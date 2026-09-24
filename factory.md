# verified-samplers

## Description
Machine-checked MCMC algorithms in Lean 4 with auditable Julia reference and optimized implementations. The formal layer proves correctness properties (detailed balance, stationarity, marginal correctness); the IR compiler connects proofs to executable code.

## Scope
- formal/Mcmc/
- VerifiedSamplers.jl/src/
- docs/

## Build
cd formal && lake build

## Test
make julia

## Project Eval
- name: lean_build
  command: make formal
  parse: exit_code
  weight: 0.4
  description: Lean 4 formal proofs compile without errors
- name: julia_tests
  command: make julia
  parse: exit_code
  weight: 0.3
  description: Julia test suite passes
- name: ir_consistency
  command: make check-generated
  parse: exit_code
  weight: 0.2
  description: Generated IR matches committed Samplers.ir
- name: no_sorry
  command: make check-no-sorry
  parse: exit_code
  weight: 0.1
  description: No sorry or admit in formal proofs

## Eval Weights
- hygiene: 20
- growth: 20
- project: 60

## Target Branch
main
