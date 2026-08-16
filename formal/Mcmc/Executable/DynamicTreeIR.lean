/-!
# Dynamic-tree execution descriptors

Versioned metadata for checked dynamic-trajectory builders. The descriptor
does not assert that recursive NUTS rows pass reroot certification; it records
that completed rows must use the checked-or-identity policy proved in Lean.
-/

namespace Mcmc.Executable.DynamicTreeIR

inductive Builder where
  | recursiveDoubling
deriving DecidableEq, Repr

inductive StopRule where
  | endpointUTurn
deriving DecidableEq, Repr

inductive SubtreePolicy where
  | recursiveExclusion
deriving DecidableEq, Repr

inductive FailurePolicy where
  | checkedOrIdentity
deriving DecidableEq, Repr

structure Descriptor where
  name : String
  builder : Builder
  stopRule : StopRule
  subtreePolicy : SubtreePolicy
  failurePolicy : FailurePolicy
deriving DecidableEq, Repr

/-- Portable descriptor for the root-dependent recursive builder whose full
row family is accepted only after global reroot certification. -/
def checkedRecursiveDoubling : Descriptor where
  name := "checked-recursive-doubling"
  builder := .recursiveDoubling
  stopRule := .endpointUTurn
  subtreePolicy := .recursiveExclusion
  failurePolicy := .checkedOrIdentity

end Mcmc.Executable.DynamicTreeIR
