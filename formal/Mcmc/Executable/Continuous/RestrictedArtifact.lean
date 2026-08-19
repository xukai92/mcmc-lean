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
  | sin (value : RestrictedArtifactExpr)
  | cos (value : RestrictedArtifactExpr)
deriving DecidableEq, Repr

/-- Canonical generated representation of the Gaussian restricted target. -/
def restrictedGaussianArtifact : RestrictedArtifactExpr :=
  .mul (.rational 1 2) (.mul .input .input)

/-- Symbolic derivative that remains in portable rational syntax. -/
def RestrictedArtifactExpr.derivative :
    RestrictedArtifactExpr → RestrictedArtifactExpr
  | .input => .rational 1 1
  | .rational _ _ => .rational 0 1
  | .add left right => .add left.derivative right.derivative
  | .mul left right =>
      .add (.mul left.derivative right) (.mul left right.derivative)
  | .neg value => .neg value.derivative
  | .exp value => .mul (.exp value) value.derivative
  | .sin value => .mul (.cos value) value.derivative
  | .cos value => .neg (.mul (.sin value) value.derivative)

/-- Generated sinusoidally perturbed Gaussian potential `x²/2 - sin x`. -/
def restrictedSinusoidalPotentialArtifact : RestrictedArtifactExpr :=
  .add restrictedGaussianArtifact (.neg (.sin .input))

/-- Generated strongly convex polynomial potential `x⁴/4 + x²/2`. Its
nonconstant Hessian gives a position-dependent metric client without target
callback transcendental operations. -/
def restrictedQuarticPotentialArtifact : RestrictedArtifactExpr :=
  .add
    (.mul (.rational 1 4)
      (.mul (.mul .input .input) (.mul .input .input)))
    restrictedGaussianArtifact

end Mcmc.Executable.Continuous
