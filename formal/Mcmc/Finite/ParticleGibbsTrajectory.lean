import Mcmc.Finite.CollapsedConditional
import Mcmc.Finite.SequentialMonteCarlo
import Mathlib.Data.Fintype.Vector

/-!
# Trajectory-state particle Gibbs

The extended particle-history kernel is the convenient stationarity proof
space, but the Markov chain of inferential interest evolves trajectories.
This module obtains that kernel by exact conditioning on the selected
trajectory, refreshing the terminal index, and projecting back.
-/

namespace Mcmc.Finite.SequentialMonteCarlo

open MarkovKernel ParticleEstimator

variable {Sample Particle : Type*}
  [Fintype Sample] [Fintype Particle]
  [DecidableEq Sample] [DecidableEq Particle] [Nonempty Particle]

/-- Fixed-length trajectory type for a finite Feynman--Kac schedule. -/
abbrev Trajectory (steps : List (FeynmanKacStep Sample)) :=
  List.Vector Sample (steps.length + 1)

/-- Package the selected ancestral list with its already-proved length. -/
def selectedTrajectoryVector (steps : List (FeynmanKacStep Sample))
    (selected : History (Particle := Particle) steps × Particle) :
    Trajectory steps :=
  ⟨selectedTrajectory steps selected.1.1 selected.1.2 selected.2,
    selectedTrajectory_length steps selected.1.1 selected.1.2 selected.2⟩

/-- Exact normalized Feynman--Kac trajectory target, represented as the
selected-trajectory marginal of the extended particle target. -/
noncomputable def trajectoryTarget (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    Distribution (Trajectory steps) :=
  Mcmc.Finite.Conditional.statisticMarginal
    (selectedParticleTarget (Particle := Particle) initial steps hnormalizer)
    (selectedTrajectoryVector steps)

/-- The trajectory-state particle-Gibbs transition. It draws an exact
conditional particle history given the current trajectory, refreshes the
terminal index, then returns the newly selected trajectory. -/
noncomputable def trajectoryParticleGibbsKernel
    (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    MarkovKernel (Trajectory steps) :=
  Mcmc.Finite.Conditional.collapsedKernel
    (selectedParticleTarget (Particle := Particle) initial steps hnormalizer)
    (selectedTrajectoryVector steps)
    (selectedIndexRefreshKernel (Particle := Particle) steps)

/-- Exact stationarity of particle Gibbs on the trajectory state space. -/
theorem trajectoryParticleGibbsKernel_stationary
    (initial : Distribution Sample)
    (steps : List (FeynmanKacStep Sample))
    (hnormalizer : 0 < normalizingConstant initial steps) :
    (trajectoryParticleGibbsKernel (Particle := Particle)
      initial steps hnormalizer).Stationary
      (trajectoryTarget (Particle := Particle) initial steps hnormalizer) := by
  exact Mcmc.Finite.Conditional.collapsedKernel_stationary _ _ _
    (selectedIndexRefreshKernel_stationary (Particle := Particle)
      initial steps hnormalizer)

end Mcmc.Finite.SequentialMonteCarlo
