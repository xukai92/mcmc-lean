/-!
# Portable composable-inference descriptors

Descriptors contain configuration metadata only. Kernel preservation remains a
Lean theorem premise for each named engine; runtime callbacks must be matched to
those names by the executable refinement layer.
-/

namespace Mcmc.Executable.ComposableIR

inductive Engine where
  | particleGibbs
  | hmc
  | nuts
deriving DecidableEq, Repr

structure OperatorDescriptor where
  name : String
  engine : Engine
  scope : List String
deriving DecidableEq, Repr

structure ScheduleDescriptor where
  name : String
  variables : List String
  operators : List OperatorDescriptor
deriving DecidableEq, Repr

/-- Every declared model variable occurs in at least one operator scope. -/
def ScheduleDescriptor.covers (schedule : ScheduleDescriptor) : Bool :=
  schedule.variables.all fun variableName =>
    schedule.operators.any fun operator => operator.scope.contains variableName

/-- Portable metadata for the Ge et al. PG--HMC blocked schedule. -/
def gePgHmcSchedule : ScheduleDescriptor where
  name := "ge-pg-hmc"
  variables := ["latent", "continuous"]
  operators :=
    [⟨"particle-gibbs", .particleGibbs, ["latent"]⟩,
      ⟨"hamiltonian-monte-carlo", .hmc, ["continuous"]⟩]

theorem gePgHmcSchedule_covers : gePgHmcSchedule.covers = true := by decide

end Mcmc.Executable.ComposableIR
