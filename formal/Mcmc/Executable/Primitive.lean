import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mcmc.Executable.Finite.Weights

/-!
# Typed ideal sampler primitives

This module is the common boundary between exact probability semantics and
operational replay.  A primitive is indexed by its result type, so a trace
cannot silently return a natural number where a real Gaussian value is
expected.

The real-valued primitives are *ideal*: their denotations are mathlib
measures on `ℝ`.  This does not claim that `ℝ` is an executable numeric type or
that a floating-point RNG samples these measures exactly.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace Mcmc.Executable

open ProbabilityTheory

/-- Primitive operations admitted by the initial sampler language. -/
inductive Primitive : Type → Type where
  | drawBelow (upper : ℕ) (positive : 0 < upper) : Primitive (Fin upper)
  | standardNormal : Primitive ℝ
  | uniformUnit : Primitive ℝ

/-- The ideal uniform law on the half-open unit interval. -/
noncomputable def unitUniform : Measure ℝ :=
  volume.restrict (Set.Ico 0 1)

instance unitUniform_isProbabilityMeasure : IsProbabilityMeasure unitUniform where
  measure_univ := by
    simp [unitUniform, Real.volume_Ico]

/-- The ideal unit-uniform threshold accepts a value `a ∈ [0,1]` with mass
exactly `a`. -/
theorem unitUniform_Iio {a : ℝ} (ha1 : a ≤ 1) :
    unitUniform (Set.Iio a) = ENNReal.ofReal a := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Iio]
  have hinter : Set.Iio a ∩ Set.Ico 0 1 = Set.Ico 0 a := by
    ext value
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨hvaluea, hvalue0, _hvalue1⟩
      exact ⟨hvalue0, hvaluea⟩
    · rintro ⟨hvalue0, hvaluea⟩
      exact ⟨hvaluea, hvalue0, hvaluea.trans_le ha1⟩
  rw [hinter, Real.volume_Ico]
  simp

/-- Exact denotation of a positive bounded-natural primitive. -/
noncomputable def drawBelowMeasure (upper : ℕ) (positive : 0 < upper) :
    Measure (Fin upper) :=
  (Finite.NatWeights.DrawBound.pmf ⟨upper, positive⟩).toMeasure

/-- Exact denotation of the ideal standard-normal primitive. -/
noncomputable def standardNormalMeasure : Measure ℝ :=
  gaussianReal 0 1

instance standardNormalMeasure_isProbability :
    IsProbabilityMeasure standardNormalMeasure := by
  unfold standardNormalMeasure
  infer_instance

/-- The primitive's ideal law is the same density representation consumed by
the measure-theoretic Gaussian RWMH construction. -/
theorem standardNormalMeasure_eq_withDensity :
    standardNormalMeasure = volume.withDensity (gaussianPDF 0 1) := by
  rw [standardNormalMeasure, gaussianReal_of_var_ne_zero]
  norm_num

instance drawBelowMeasure_isProbability (upper : ℕ) (positive : 0 < upper) :
    IsProbabilityMeasure (drawBelowMeasure upper positive) := by
  unfold drawBelowMeasure
  infer_instance

/-- Heterogeneous trace events. Real events are mathematical replay values,
not a serialization format for exact real-number computation. -/
inductive TraceEvent where
  | drawBelow (upper value : ℕ)
  | standardNormal (value : ℝ)
  | uniformUnit (value : ℝ)

/-- Typed replay failures at the primitive boundary. -/
inductive ReplayError where
  | exhausted
  | kindMismatch
  | boundMismatch (expected actual : ℕ)
  | outOfRangeNatural (upper value : ℕ)
  | outOfRangeUnit (value : ℝ)

/-- Successful consumption of one typed trace event. -/
structure ReplayResult (α : Type) where
  value : α
  remaining : List TraceEvent

/-- Deterministically consume one event for an ideal primitive.

This definition is noncomputable because validation of an arbitrary Lean real
uses classical order. Concrete backends instead replay their own serializable
numeric representation under a documented refinement contract. -/
noncomputable def replayPrimitive {α : Type} (primitive : Primitive α)
    (trace : List TraceEvent) : Except ReplayError (ReplayResult α) :=
  match trace with
  | [] => .error .exhausted
  | event :: rest =>
      match primitive, event with
      | .drawBelow upper _, .drawBelow actual value =>
          if actual ≠ upper then .error (.boundMismatch upper actual)
          else if h : value < upper then .ok ⟨⟨value, h⟩, rest⟩
          else .error (.outOfRangeNatural upper value)
      | .standardNormal, .standardNormal value => .ok ⟨value, rest⟩
      | .uniformUnit, .uniformUnit value =>
          if 0 ≤ value ∧ value < 1 then .ok ⟨value, rest⟩
          else .error (.outOfRangeUnit value)
      | _, _ => .error .kindMismatch

@[simp]
theorem replayPrimitive_standardNormal (value : ℝ) (rest : List TraceEvent) :
    replayPrimitive Primitive.standardNormal
        (TraceEvent.standardNormal value :: rest) = .ok ⟨value, rest⟩ :=
  rfl

@[simp]
theorem replayPrimitive_uniformUnit_of_mem {value : ℝ}
    (hvalue : 0 ≤ value ∧ value < 1) (rest : List TraceEvent) :
    replayPrimitive Primitive.uniformUnit
        (TraceEvent.uniformUnit value :: rest) = .ok ⟨value, rest⟩ := by
  simp [replayPrimitive, hvalue]

@[simp]
theorem replayPrimitive_kindMismatch (value : ℝ) (rest : List TraceEvent) :
    replayPrimitive Primitive.standardNormal
        (TraceEvent.uniformUnit value :: rest) = .error .kindMismatch :=
  rfl

end Mcmc.Executable
