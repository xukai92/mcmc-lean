/-!
# Portable constrained-transform descriptors

These descriptors make coordinate conventions and Jacobians part of the
generated artifact.  Kernel correctness still comes from the measure-level
conjugation theorem; numerical implementations must refine the named scalar
operations.
-/

namespace Mcmc.Executable.ConstrainedTransformIR

inductive ScalarTransform where
  | positiveLog
  | openUnitArtanh
deriving DecidableEq, Repr

structure Descriptor where
  name : String
  transform : ScalarTransform
  constrainedType : String
  unconstrainedType : String
  forward : String
  inverse : String
  logAbsDetInverseJacobian : String
deriving DecidableEq, Repr

/-- `x > 0`, `y = log x`, `x = exp y`; the inverse Jacobian contributes `y`
to the unconstrained log density. -/
def positiveLog : Descriptor where
  name := "positive-log"
  transform := .positiveLog
  constrainedType := "positive-real"
  unconstrainedType := "real"
  forward := "log"
  inverse := "exp"
  logAbsDetInverseJacobian := "identity"

/-- `0 < x < 1`, `y = artanh(2x-1)`,
`x = (tanh(y)+1)/2`. The inverse log-Jacobian is
`log(1-tanh(y)^2)-log(2)`. -/
def openUnitArtanh : Descriptor where
  name := "open-unit-artanh"
  transform := .openUnitArtanh
  constrainedType := "open-unit-interval"
  unconstrainedType := "real"
  forward := "artanh-affine"
  inverse := "tanh-affine"
  logAbsDetInverseJacobian := "log-one-minus-tanh-sq-minus-log-two"

end Mcmc.Executable.ConstrainedTransformIR
