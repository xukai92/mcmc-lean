/-!
# Portable restricted target syntax

This dependency-light syntax is shared by the generated artifact and the
verified ideal-real compiler. Rational literals avoid serializing arbitrary
Lean real values.
-/

namespace Mcmc.Executable.Continuous

inductive RestrictedArtifactExpr where
  | input
  | rational (numerator : Int) (denominator : Nat)
  | add (left right : RestrictedArtifactExpr)
  | mul (left right : RestrictedArtifactExpr)
  | neg (value : RestrictedArtifactExpr)
  | exp (value : RestrictedArtifactExpr)
deriving DecidableEq, Repr

/-- Canonical generated representation of the Gaussian restricted target. -/
def restrictedGaussianArtifact : RestrictedArtifactExpr :=
  .mul (.rational 1 2) (.mul .input .input)

end Mcmc.Executable.Continuous
