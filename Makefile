.PHONY: all formal oracle julia test generate check-generated generate-docs check-docs-generated docs benchmarks benchmark-dev benchmark-hmc benchmark-report benchmark-nuts-optimization optimization-trial experiments experiment-xu21 experiment-xu21-logistic experiment-particle-gibbs-count experiment-dynamic-hmc experiment-restricted-quartic experiment-reversible-jump experiment-warmup-rwmh experiment-indefinite-adaptation experiment-indefinite-continuous-adaptation experiment-constrained-transforms experiment-ge-pg-hmc experiment-gaussian-softabs experiment-gaussian-performance

XU21_SEED ?= 2021
XU21_REPLICATES ?= 100
XU21_HORIZON ?= 2000
PG_SEED ?= 20551
PG_REPETITIONS ?= 8000
PG_COUNTS ?= 1,2,4,8
DYNAMIC_HMC_SEED ?= 3354
DYNAMIC_HMC_DRAWS ?= 10000
DYNAMIC_HMC_BURNIN ?= 1000
DYNAMIC_HMC_DIMENSION ?= 2
QUARTIC_SEED ?= 29092
QUARTIC_DRAWS ?= 20000
QUARTIC_BURNIN ?= 2000
QUARTIC_SCALE ?= 0.8
RJ_SEED ?= 24298
RJ_DRAWS ?= 40000
WARMUP_SEED ?= 44455
WARMUP_DRAWS ?= 1000
WARMUP_RETAINED ?= 20000
ADAPTIVE_BOOL_SEED ?= 7663
ADAPTIVE_BOOL_DRAWS ?= 40000
ADAPTIVE_BOOL_TAIL ?= 10000
ADAPTIVE_CONTINUOUS_SEED ?= 49175
ADAPTIVE_CONTINUOUS_DRAWS ?= 40000
ADAPTIVE_CONTINUOUS_TAIL ?= 10000
TRANSFORM_SEED ?= 68119
TRANSFORM_DRAWS ?= 30000
TRANSFORM_BURNIN ?= 3000
GE_PGHMC_SEED ?= 28184
GE_PGHMC_DRAWS ?= 30000
GE_PGHMC_BURNIN ?= 3000
SOFTABS_SEED ?= 27221
SOFTABS_DRAWS ?= 20000
SOFTABS_BURNIN ?= 2000
SOFTABS_DIMENSION ?= 2
PERFORMANCE_SEED ?= 58713
PERFORMANCE_DRAWS ?= 12000
PERFORMANCE_BURNIN ?= 2000

all: formal

formal:
	$(MAKE) -C formal build

oracle:
	cd formal && lake build mcmc_oracle

julia:
	julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'

test: formal oracle check-generated julia

generate:
	cd formal && lake build generate_ir
	formal/.lake/build/bin/generate_ir VerifiedSamplers.jl/src/Reference/Samplers.ir

check-generated:
	cd formal && lake build generate_ir
	@tmp_file=$$(mktemp); \
	trap 'rm -f "$$tmp_file"' EXIT; \
	formal/.lake/build/bin/generate_ir "$$tmp_file"; \
	cmp "$$tmp_file" VerifiedSamplers.jl/src/Reference/Samplers.ir

generate-docs:
	cd formal && lake build generate_docs
	@mkdir -p docs/generated
	formal/.lake/build/bin/generate_docs docs/generated/architecture-graphs.md
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/tools/generate_backend_docs.jl \
		docs/generated/backend-registry.md
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/tools/generate_artifact_docs.jl \
		docs/generated/reference-artifact.md

check-docs-generated:
	cd formal && lake build generate_docs
	@tmp_dir=$$(mktemp -d); \
	trap 'rm -rf "$$tmp_dir"' EXIT; \
	formal/.lake/build/bin/generate_docs "$$tmp_dir/architecture.md"; \
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/tools/generate_backend_docs.jl \
		"$$tmp_dir/backends.md"; \
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/tools/generate_artifact_docs.jl \
		"$$tmp_dir/artifact.md"; \
	cmp "$$tmp_dir/architecture.md" docs/generated/architecture-graphs.md; \
	cmp "$$tmp_dir/backends.md" docs/generated/backend-registry.md; \
	cmp "$$tmp_dir/artifact.md" docs/generated/reference-artifact.md

docs: generate-docs
	julia --project=docs -e 'using Pkg; Pkg.instantiate()'
	julia --project=docs docs/make.jl

benchmarks: benchmark-hmc benchmark-report

benchmark-dev:
	julia --project=benchmark benchmark/run.jl --dev
	julia --project=benchmark benchmark/report.jl --dev

benchmark-hmc:
	julia --project=benchmark benchmark/run.jl

benchmark-report:
	julia --project=benchmark benchmark/report.jl

benchmark-nuts-optimization:
	julia --project=benchmark benchmark/nuts_optimization.jl

# A candidate is accepted only after the complete release gate and a measured
# speedup over an explicitly supplied pre-change baseline.
optimization-trial: test
	@test -n "$(OPTIMIZATION_BASELINE_SECONDS)" || \
		(echo "set OPTIMIZATION_BASELINE_SECONDS to the pre-change median" >&2; exit 2)
	OPTIMIZATION_BASELINE_SECONDS=$(OPTIMIZATION_BASELINE_SECONDS) \
	OPTIMIZATION_MINIMUM_SPEEDUP=$${OPTIMIZATION_MINIMUM_SPEEDUP:-1.0} \
		julia --project=benchmark benchmark/nuts_optimization.jl

experiments: experiment-xu21 experiment-xu21-logistic \
	experiment-particle-gibbs-count experiment-dynamic-hmc \
	experiment-restricted-quartic experiment-reversible-jump \
	experiment-warmup-rwmh experiment-indefinite-adaptation \
	experiment-indefinite-continuous-adaptation \
	experiment-constrained-transforms \
	experiment-ge-pg-hmc experiment-gaussian-softabs \
	experiment-gaussian-performance

experiment-xu21:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/xu21_gaussian_meeting.jl \
		$(XU21_SEED) $(XU21_REPLICATES) $(XU21_HORIZON)

experiment-xu21-logistic:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/xu21_logistic_meeting.jl \
		$(XU21_SEED) $(XU21_REPLICATES) $(XU21_HORIZON)

experiment-particle-gibbs-count:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/particle_gibbs_count.jl \
		$(PG_SEED) $(PG_REPETITIONS) $(PG_COUNTS)

experiment-dynamic-hmc:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/dynamic_hmc_gaussian.jl \
		$(DYNAMIC_HMC_SEED) $(DYNAMIC_HMC_DRAWS) \
		$(DYNAMIC_HMC_BURNIN) $(DYNAMIC_HMC_DIMENSION)

experiment-restricted-quartic:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/restricted_quartic_rwmh.jl \
		$(QUARTIC_SEED) $(QUARTIC_DRAWS) $(QUARTIC_BURNIN) \
		$(QUARTIC_SCALE)

experiment-reversible-jump:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/reversible_jump.jl \
		$(RJ_SEED) $(RJ_DRAWS)

experiment-warmup-rwmh:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/warmup_rwmh.jl \
		$(WARMUP_SEED) $(WARMUP_DRAWS) $(WARMUP_RETAINED)

experiment-indefinite-adaptation:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/indefinite_adaptive_bool.jl \
		$(ADAPTIVE_BOOL_SEED) $(ADAPTIVE_BOOL_DRAWS) $(ADAPTIVE_BOOL_TAIL)

experiment-indefinite-continuous-adaptation:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/indefinite_adaptive_continuous.jl \
		$(ADAPTIVE_CONTINUOUS_SEED) $(ADAPTIVE_CONTINUOUS_DRAWS) \
		$(ADAPTIVE_CONTINUOUS_TAIL)

experiment-constrained-transforms:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/constrained_transforms.jl \
		$(TRANSFORM_SEED) $(TRANSFORM_DRAWS) $(TRANSFORM_BURNIN)

experiment-ge-pg-hmc:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/ge_pg_hmc.jl \
		$(GE_PGHMC_SEED) $(GE_PGHMC_DRAWS) $(GE_PGHMC_BURNIN)

experiment-gaussian-softabs:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/gaussian_softabs_grhmc.jl \
		$(SOFTABS_SEED) $(SOFTABS_DRAWS) $(SOFTABS_BURNIN) \
		$(SOFTABS_DIMENSION)

experiment-gaussian-performance:
	julia --project=VerifiedSamplers.jl \
		VerifiedSamplers.jl/experiments/gaussian_performance.jl \
		$(PERFORMANCE_SEED) $(PERFORMANCE_DRAWS) $(PERFORMANCE_BURNIN)
