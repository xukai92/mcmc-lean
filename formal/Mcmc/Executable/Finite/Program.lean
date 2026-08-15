import Mcmc.Executable.Finite.MetropolisHastings

/-!
# Typed finite sampler semantic entries

These tags name the established replay specifications and exact PMF theorems
to which the canonical command-IR interpreter is connected. They are semantic
anchors, not a second emitted artifact or public execution path.
-/

namespace Mcmc.Executable.Finite

/-- Typed signatures supported by the finite executable semantic entries. -/
inductive Signature where
  | categorical
  | metropolisHastings

/-- Lean type denoted by a finite semantic-entry signature. -/
def Signature.denote : Signature → Type
  | .categorical =>
      ∀ {n : ℕ}, NatWeights n → List DrawEvent →
        Except ExecError (Fin n × List DrawEvent)
  | .metropolisHastings =>
      ∀ {n : ℕ}, PositiveNatWeights n → NatKernelWeights n → Fin n →
        List DrawEvent → Except ExecError (Fin n × List DrawEvent)

/-- Signature-indexed names for the established finite replay specifications. -/
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

/-- The categorical semantic entry is anchored to the selector whose
PMF denotation was proved exact. -/
theorem categorical_compiler_semantics {n : ℕ} (weights : NatWeights n) :
    weights.selectPMF = weights.toPMF :=
  weights.selectPMF_eq_toPMF

/-- The generic MH semantic entry is anchored to the existing exact PMF
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
