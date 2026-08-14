import Mcmc.Executable.Finite.MetropolisHastings

/-!
# Typed finite sampler entry programs

These tags are the compiler inputs for the finite reference backend. Their
Lean denotations are the already verified executable functions; code
generation no longer starts from an unrelated Julia source string.
-/

namespace Mcmc.Executable.Finite

/-- Typed signatures supported by the initial finite compiler. -/
inductive Signature where
  | categorical
  | metropolisHastings

/-- Lean type denoted by a compiler entry-point signature. -/
def Signature.denote : Signature → Type
  | .categorical =>
      ∀ {n : ℕ}, NatWeights n → List DrawEvent →
        Except ExecError (Fin n × List DrawEvent)
  | .metropolisHastings =>
      ∀ {n : ℕ}, PositiveNatWeights n → NatKernelWeights n → Fin n →
        List DrawEvent → Except ExecError (Fin n × List DrawEvent)

/-- Inspectable, intrinsically signature-indexed finite sampler programs. -/
inductive Program : Signature → Type where
  | categorical : Program .categorical
  | metropolisHastings : Program .metropolisHastings

/-- Executable Lean trace denotation of a finite compiler input. -/
def Program.denote : Program signature → signature.denote
  | .categorical => replayCategorical
  | .metropolisHastings => replayMHStep

@[simp]
theorem categorical_denote {n : ℕ} (weights : NatWeights n)
    (trace : List DrawEvent) :
    Program.denote Program.categorical weights trace =
      replayCategorical weights trace :=
  rfl

@[simp]
theorem metropolisHastings_denote {n : ℕ} (target : PositiveNatWeights n)
    (proposal : NatKernelWeights n) (current : Fin n) (trace : List DrawEvent) :
    Program.denote Program.metropolisHastings target proposal current trace =
      replayMHStep target proposal current trace :=
  rfl

/-- The compiled categorical entry point is anchored to the selector whose
PMF denotation was proved exact. -/
theorem categorical_compiler_semantics {n : ℕ} (weights : NatWeights n) :
    weights.selectPMF = weights.toPMF :=
  weights.selectPMF_eq_toPMF

/-- The compiled generic MH entry point is anchored to the existing exact PMF
refinement theorem. -/
theorem metropolisHastings_compiler_semantics {n : ℕ}
    (target : PositiveNatWeights n) (proposal : NatKernelWeights n)
    (current : Fin n) :
    stepPMF target proposal current =
      (Mcmc.Finite.MetropolisHastings.kernel
        target.toNatWeights.toDistribution proposal.toKernel
        target.toDistribution_positive).rowPMF current :=
  stepPMF_refines target proposal current

end Mcmc.Executable.Finite
