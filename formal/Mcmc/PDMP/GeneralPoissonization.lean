import Mcmc.Kernel.CoupledChain
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Group.IntegralConvolution
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

/-- The Poisson series can equivalently be read as a Lebesgue integral over
the event count. -/
theorem generalPoissonizedKernel_apply_eq_lintegral
    (transition : Kernel State State) [IsMarkovKernel transition]
    (r : NNReal) (x : State) {s : Set State} (hs : MeasurableSet s) :
    generalPoissonizedKernel transition r x s =
      ∫⁻ n, (transition ^ n) x s ∂poissonMeasure r := by
  rw [generalPoissonizedKernel_apply transition r x hs,
    MeasureTheory.lintegral_countable']
  apply tsum_congr
  intro n
  exact mul_comm _ _

private theorem lintegral_generalPoissonizedKernel
    (transition : Kernel State State) [IsMarkovKernel transition]
    (r : NNReal) (x : State) (f : State → ENNReal) :
    ∫⁻ y, f y ∂generalPoissonizedKernel transition r x =
      ∫⁻ n, ∫⁻ y, f y ∂(transition ^ n) x ∂poissonMeasure r := by
  rw [generalPoissonizedKernel, Kernel.sum_apply,
    MeasureTheory.lintegral_sum_measure]
  simp_rw [scaleKernel_apply, MeasureTheory.lintegral_smul_measure]
  rw [MeasureTheory.lintegral_countable']
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  rw [mul_comm]

/-- Chapman--Kolmogorov law for the general-state Poisson mixture. Independent
Poisson event counts add, while kernel powers compose by addition of their
indices. -/
theorem generalPoissonizedKernel_add
    (transition : Kernel State State) [IsMarkovKernel transition]
    (r s : NNReal) :
    generalPoissonizedKernel transition (r + s) =
      generalPoissonizedKernel transition s ∘ₖ
        generalPoissonizedKernel transition r := by
  ext x a ha
  rw [Kernel.comp_apply' _ _ _ ha,
    generalPoissonizedKernel_apply_eq_lintegral transition (r + s) x ha]
  rw [lintegral_generalPoissonizedKernel transition r x
    (fun y ↦ generalPoissonizedKernel transition s y a)]
  simp_rw [generalPoissonizedKernel_apply_eq_lintegral transition s _ ha]
  have hinner (m : ℕ) :
      ∫⁻ y, ∫⁻ n, (transition ^ n) y a ∂poissonMeasure s
          ∂(transition ^ m) x =
        ∫⁻ n, (transition ^ (m + n)) x a ∂poissonMeasure s := by
    have hcount (y : State) :
        ∫⁻ n, (transition ^ n) y a ∂poissonMeasure s =
          ∑' n, (transition ^ n) y a * poissonMeasure s {n} :=
      MeasureTheory.lintegral_countable' _
    simp_rw [hcount]
    rw [MeasureTheory.lintegral_tsum]
    · rw [MeasureTheory.lintegral_countable']
      apply tsum_congr
      intro n
      rw [MeasureTheory.lintegral_mul_const _
        (Kernel.measurable_coe (transition ^ n) ha),
        ← Kernel.pow_add_apply_eq_lintegral transition m n x ha]
    · intro n
      exact ((Kernel.measurable_coe (transition ^ n) ha).mul_const _).aemeasurable
  simp_rw [hinner]
  rw [← Measure.lintegral_conv
      (f := fun n : ℕ ↦ (transition ^ n) x a) (by fun_prop),
    poissonMeasure_conv_poissonMeasure]

/-- At zero clock intensity no embedded transition occurs. -/
@[simp] theorem generalPoissonizedKernel_zero
    (transition : Kernel State State) [IsMarkovKernel transition] :
    generalPoissonizedKernel transition 0 = Kernel.id := by
  ext x s hs
  rw [generalPoissonizedKernel_apply transition 0 x hs,
    tsum_eq_single 0]
  · have hone : (1 : Kernel State State) = Kernel.id := rfl
    simpa [poissonMeasure_singleton] using
      congrArg (fun kernel : Kernel State State => kernel x s) hone
  · intro n hn
    simp [poissonMeasure_singleton, zero_pow hn]

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
