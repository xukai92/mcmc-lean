.PHONY: all formal oracle julia test generate check-generated

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
