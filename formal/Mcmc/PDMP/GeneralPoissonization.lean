import Mcmc.Kernel.CoupledChain
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-!
# General-state Poissonization

This module lifts the finite Poissonized semigroup construction to mathlib
Markov kernels on an arbitrary measurable state space. A Poisson-distributed
finite count selects an iterate of an embedded discrete kernel. This supplies
the bounded-clock, nonexplosive pure-jump foundation needed before adding
state-dependent PDMP event simulation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Scale every row measure of a kernel by a nonnegative extended-real
coefficient. -/
noncomputable def scaleKernel (c : ENNReal) (kernel : Kernel State State)
    [IsSFiniteKernel kernel] :
    Kernel State State :=
  Kernel.withDensity kernel fun _ _ => c

@[simp] theorem scaleKernel_apply (c : ENNReal) (kernel : Kernel State State)
    [IsSFiniteKernel kernel]
    (x : State) : scaleKernel c kernel x = c • kernel x := by
  rw [scaleKernel, Kernel.withDensity_apply _ measurable_const]
  simp

/-- Poisson mixture of all finite iterates of a general-state kernel. -/
noncomputable def generalPoissonizedKernel (transition : Kernel State State)
    [IsMarkovKernel transition]
    (r : NNReal) : Kernel State State :=
  Kernel.sum fun n : ℕ =>
    scaleKernel (poissonMeasure r {n}) (transition ^ n)

private theorem tsum_poissonMeasure_singleton (r : NNReal) :
    ∑' n : ℕ, poissonMeasure r {n} = 1 := by
  rw [← measure_iUnion]
  · rw [show (⋃ n : ℕ, ({n} : Set ℕ)) = Set.univ by ext; simp]
    simp
  · intro i j hij
    exact Set.disjoint_singleton.2 hij
  · exact fun i => MeasurableSet.singleton i

/-- The Poisson mixture of iterates of a Markov kernel is again Markov. -/
instance generalPoissonizedKernel.instIsMarkovKernel
    (transition : Kernel State State) [IsMarkovKernel transition]
    (r : NNReal) : IsMarkovKernel (generalPoissonizedKernel transition r) where
  isProbabilityMeasure x := ⟨by
    rw [generalPoissonizedKernel, Kernel.sum_apply' _ x MeasurableSet.univ]
    simp only [scaleKernel_apply, Measure.smul_apply, measure_univ]
    simpa [smul_eq_mul] using tsum_poissonMeasure_singleton r⟩

/-- The real-time row is the exact Poisson series of discrete iterates. -/
theorem generalPoissonizedKernel_apply
    (transition : Kernel State State) [IsMarkovKernel transition]
    (r : NNReal) (x : State)
    {s : Set State} (hs : MeasurableSet s) :
    generalPoissonizedKernel transition r x s =
      ∑' n : ℕ, poissonMeasure r {n} * (transition ^ n) x s := by
  rw [generalPoissonizedKernel, Kernel.sum_apply' _ x hs]
  apply tsum_congr
  intro n
  rw [scaleKernel_apply]
  simp [Measure.smul_apply, smul_eq_mul]

private theorem invariant_pow (transition : Kernel State State)
    (target : Measure State) (hinvariant : transition.Invariant target) :
    ∀ n : ℕ, (transition ^ n).Invariant target
  | 0 => by
      change Kernel.id.Invariant target
      exact Measure.id_comp
  | n + 1 => by
      rw [pow_succ]
      exact (invariant_pow transition target hinvariant n).comp hinvariant

/-- Poissonization preserves every invariant probability measure of the
embedded general-state kernel. -/
theorem generalPoissonizedKernel_invariant
    (transition : Kernel State State) [IsMarkovKernel transition]
    (target : Measure State) [IsProbabilityMeasure target]
    (hinvariant : transition.Invariant target) (r : NNReal) :
    (generalPoissonizedKernel transition r).Invariant target := by
  unfold Kernel.Invariant
  ext s hs
  rw [Measure.bind_apply hs
    (generalPoissonizedKernel transition r).aemeasurable]
  simp_rw [generalPoissonizedKernel_apply transition r _ hs]
  rw [MeasureTheory.lintegral_tsum]
  · have hpow : ∀ n : ℕ,
        ∫⁻ x, (transition ^ n) x s ∂target = target s := by
      intro n
      rw [← Measure.bind_apply hs (transition ^ n).aemeasurable,
        (invariant_pow transition target hinvariant n).def]
    rw [show (∑' n : ℕ, ∫⁻ x,
        poissonMeasure r {n} * (transition ^ n) x s ∂target) =
        ∑' n : ℕ, poissonMeasure r {n} * target s by
      apply tsum_congr
      intro n
      rw [MeasureTheory.lintegral_const_mul _
        (Kernel.measurable_coe (transition ^ n) hs), hpow n]]
    rw [ENNReal.tsum_mul_right]
    rw [tsum_poissonMeasure_singleton, one_mul]
  · intro n
    exact (measurable_const.mul
      (Kernel.measurable_coe (transition ^ n) hs)).aemeasurable

/-- A Poisson clock is nonexplosive on every finite horizon in the basic
sense that its event-count law is supported on finite natural numbers. -/
theorem poisson_count_finite_ae (r : NNReal) :
    ∀ᵐ n ∂poissonMeasure r, ∃ bound : ℕ, n ≤ bound := by
  filter_upwards [] with n
  exact ⟨n, le_rfl⟩

end Mcmc.PDMP
