.PHONY: all formal julia test generate check-generated

all: formal

formal:
	$(MAKE) -C formal build

julia:
	julia --project=VerifiedSamplers.jl -e 'using Pkg; Pkg.test()'

test: formal julia

# The Lean-to-Julia emitter will replace this placeholder in the first
# executable-sampler milestone. Generation remains explicit and never runs as
# a side effect of an ordinary Lean or Julia build.
generate:
	@echo "Julia reference generator is not implemented yet."

# CI will eventually regenerate into a temporary directory and compare it with
# VerifiedSamplers.jl/src/Reference/.
check-generated:
	@echo "Generated-reference freshness check is not implemented yet."
