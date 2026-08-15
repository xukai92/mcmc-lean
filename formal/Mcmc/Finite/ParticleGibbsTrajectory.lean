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

/-- One explicit two-lineage history containing two prescribed trajectories.
The `false` lineage follows `current`, the `true` lineage follows `proposed`,
and every ancestry map is the identity. -/
def pairedBoolHistory :
    (steps : List (FeynmanKacStep Sample)) →
      Trajectory steps → Trajectory steps →
      History (Particle := Bool) steps
  | [], current, proposed =>
      (fun b => if b then proposed.head else current.head, ULift.up ())
  | _ :: steps, current, proposed =>
      let tail := pairedBoolHistory steps current.tail proposed.tail
      (fun b => if b then proposed.head else current.head,
        (fun b => b, tail.1, tail.2))

omit [DecidableEq Sample] in
theorem initialAncestor_pairedBoolHistory
    (steps : List (FeynmanKacStep Sample))
    (current proposed : Trajectory steps) (terminal : Bool) :
    initialAncestor steps (pairedBoolHistory steps current proposed).2 terminal =
      terminal := by
  induction steps generalizing terminal with
  | nil => rfl
  | cons step steps ih =>
      simp [pairedBoolHistory, initialAncestor,
        ih current.tail proposed.tail terminal]

omit [DecidableEq Sample] in
/-- The first lineage of `pairedBoolHistory` is the requested current path. -/
theorem selectedTrajectoryVector_pairedBoolHistory_false
    (steps : List (FeynmanKacStep Sample))
    (current proposed : Trajectory steps) :
    selectedTrajectoryVector steps
      (pairedBoolHistory steps current proposed, false) = current := by
  induction steps with
  | nil =>
      rcases current with ⟨list, hlength⟩
      cases list with
      | nil => simp at hlength
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest => simp at hlength
  | cons step steps ih =>
      apply List.Vector.toList_injective
      have htail := congrArg List.Vector.toList
        (ih current.tail proposed.tail)
      have hcons := congrArg List.Vector.toList
        (List.Vector.cons_head_tail current)
      simpa [pairedBoolHistory, selectedTrajectoryVector, selectedTrajectory,
        initialAncestor_pairedBoolHistory, List.Vector.toList] using
        (congrArg (List.cons current.head) htail).trans hcons

omit [DecidableEq Sample] in
/-- The second lineage of `pairedBoolHistory` is the requested proposed path. -/
theorem selectedTrajectoryVector_pairedBoolHistory_true
    (steps : List (FeynmanKacStep Sample))
    (current proposed : Trajectory steps) :
    selectedTrajectoryVector steps
      (pairedBoolHistory steps current proposed, true) = proposed := by
  induction steps with
  | nil =>
      rcases proposed with ⟨list, hlength⟩
      cases list with
      | nil => simp at hlength
      | cons first rest =>
          cases rest with
          | nil => rfl
          | cons second rest => simp at hlength
  | cons step steps ih =>
      apply List.Vector.toList_injective
      have htail := congrArg List.Vector.toList
        (ih current.tail proposed.tail)
      have hcons := congrArg List.Vector.toList
        (List.Vector.cons_head_tail proposed)
      simpa [pairedBoolHistory, selectedTrajectoryVector, selectedTrajectory,
        initialAncestor_pairedBoolHistory, List.Vector.toList] using
        (congrArg (List.cons proposed.head) htail).trans hcons

/-- Generic two-lineage realization using one distinguished proposed index;
all other particle indices follow the current trajectory. -/
def pairedHistoryAt (proposedIndex : Particle) :
    (steps : List (FeynmanKacStep Sample)) →
      Trajectory steps → Trajectory steps → History (Particle := Particle) steps
  | [], current, proposed =>
      (fun i => if i = proposedIndex then proposed.head else current.head,
        ULift.up ())
  | _ :: steps, current, proposed =>
      let tail := pairedHistoryAt proposedIndex steps current.tail proposed.tail
      (fun i => if i = proposedIndex then proposed.head else current.head,
        (fun i => i, tail.1, tail.2))

omit [Fintype Particle] [Nonempty Particle] [DecidableEq Sample] in
theorem initialAncestor_pairedHistoryAt (proposedIndex : Particle)
    (steps : List (FeynmanKacStep Sample))
    (current proposed : Trajectory steps) (terminal : Particle) :
    initialAncestor steps
      (pairedHistoryAt proposedIndex steps current proposed).2 terminal = terminal := by
  induction steps generalizing terminal with
  | nil => rfl
  | cons step steps ih =>
      simp [pairedHistoryAt, initialAncestor,
        ih current.tail proposed.tail terminal]

omit [Fintype Particle] [Nonempty Particle] [DecidableEq Sample] in
theorem selectedTrajectoryVector_pairedHistoryAt_current
    (currentIndex proposedIndex : Particle) (hne : currentIndex ≠ proposedIndex)
    (steps : List (FeynmanKacStep Sample))
    (current proposed : Trajectory steps) :
    selectedTrajectoryVector steps
      (pairedHistoryAt proposedIndex steps current proposed, currentIndex) =
        current := by
  induction steps with
  | nil =>
      rcases current with ⟨list, hlength⟩
      cases list with
      | nil => simp at hlength
      | cons first rest =>
          cases rest with
          | nil =>
              apply Subtype.ext
              simp [pairedHistoryAt, selectedTrajectoryVector,
                selectedTrajectory, hne]
              rfl
          | cons second rest => simp at hlength
  | cons step steps ih =>
      apply List.Vector.toList_injective
      have htail := congrArg List.Vector.toList
        (ih current.tail proposed.tail)
      have hcons := congrArg List.Vector.toList
        (List.Vector.cons_head_tail current)
      simpa [pairedHistoryAt, selectedTrajectoryVector, selectedTrajectory,
        initialAncestor_pairedHistoryAt, hne, List.Vector.toList] using
        (congrArg (List.cons current.head) htail).trans hcons

omit [Fintype Particle] [Nonempty Particle] [DecidableEq Sample] in
theorem selectedTrajectoryVector_pairedHistoryAt_proposed
    (proposedIndex : Particle) (steps : List (FeynmanKacStep Sample))
    (current proposed : Trajectory steps) :
    selectedTrajectoryVector steps
      (pairedHistoryAt proposedIndex steps current proposed, proposedIndex) =
        proposed := by
  induction steps with
  | nil =>
      rcases proposed with ⟨list, hlength⟩
      cases list with
      | nil => simp at hlength
      | cons first rest =>
          cases rest with
          | nil =>
              apply Subtype.ext
              simp [pairedHistoryAt, selectedTrajectoryVector,
                selectedTrajectory]
              rfl
          | cons second rest => simp at hlength
  | cons step steps ih =>
      apply List.Vector.toList_injective
      have htail := congrArg List.Vector.toList
        (ih current.tail proposed.tail)
      have hcons := congrArg List.Vector.toList
        (List.Vector.cons_head_tail proposed)
      simpa [pairedHistoryAt, selectedTrajectoryVector, selectedTrajectory,
        initialAncestor_pairedHistoryAt, List.Vector.toList] using
        (congrArg (List.cons proposed.head) htail).trans hcons

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
