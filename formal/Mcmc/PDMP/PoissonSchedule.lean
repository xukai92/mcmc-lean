import Mcmc.PDMP.EventSimulation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Conditional candidate times for a homogeneous Poisson clock

Conditional on exactly `n` clock candidates in a positive horizon, their
unordered timestamps are iid uniform on that horizon. This module constructs
that continuous probability law. Sorting these timestamps and coupling the
conditional laws to the Poisson count is the next path-law layer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

/-- A finite horizon with strictly positive duration. -/
structure PositiveHorizon where
  duration : NNReal
  positive : 0 < duration

/-- Continuous uniform probability measure on `(0, horizon]`. -/
noncomputable def PositiveHorizon.uniformTimeMeasure
    (horizon : PositiveHorizon) : Measure ℝ :=
  (ENNReal.ofReal (horizon.duration : ℝ))⁻¹ •
    volume.restrict (Set.Ioc 0 (horizon.duration : ℝ))

instance PositiveHorizon.uniformTimeMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) :
    IsProbabilityMeasure horizon.uniformTimeMeasure := by
  constructor
  rw [PositiveHorizon.uniformTimeMeasure, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Ioc]
  simp only [sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.2 (by exact_mod_cast horizon.positive)))
    ENNReal.ofReal_ne_top

/-- Iid unordered candidate timestamps conditional on a fixed candidate
count. -/
noncomputable def PositiveHorizon.candidateTimesMeasure
    (horizon : PositiveHorizon) (candidateCount : ℕ) :
    Measure (Fin candidateCount → ℝ) :=
  Measure.pi fun _ => horizon.uniformTimeMeasure

instance PositiveHorizon.candidateTimesMeasure.instIsProbabilityMeasure
    (horizon : PositiveHorizon) (candidateCount : ℕ) :
    IsProbabilityMeasure (horizon.candidateTimesMeasure candidateCount) := by
  unfold PositiveHorizon.candidateTimesMeasure
  infer_instance

end Mcmc.PDMP
