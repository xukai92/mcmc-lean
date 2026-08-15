import Mcmc.PDMP.Uniformization
import Mcmc.Finite.Combinators
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic

/-!
# Poissonized finite jump chains

Uniformization turns a bounded-rate continuous-time jump process into a
discrete kernel `P`. At elapsed clock intensity `r`, its transition kernel is
the expectation of `Pⁿ` when `n` has the Poisson law with parameter `r`.
This file constructs that exact real-time kernel and proves stationarity.

The Chapman--Kolmogorov law and a path-space càdlàg process remain subsequent
layers; no general-state PDMP nonexplosion or convergence claim is made here.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Mcmc.PDMP

open Mcmc.Finite MarkovKernel

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- The `n`-step iterate of a finite Markov kernel. -/
def kernelIterate (transition : MarkovKernel State) : ℕ → MarkovKernel State
  | 0 => identity
  | n + 1 => comp transition (kernelIterate transition n)

@[simp] theorem kernelIterate_zero (transition : MarkovKernel State) :
    kernelIterate transition 0 = identity := rfl

@[simp] theorem kernelIterate_succ (transition : MarkovKernel State) (n : ℕ) :
    kernelIterate transition (n + 1) =
      comp transition (kernelIterate transition n) := rfl

/-- Additive iteration law, in the composition convention where `first` is
applied before `second`. -/
theorem kernelIterate_add (transition : MarkovKernel State) (m n : ℕ) :
    kernelIterate transition (m + n) =
      comp (kernelIterate transition n) (kernelIterate transition m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, kernelIterate_succ, ih, comp_assoc,
        kernelIterate_succ]

/-- Every iterate preserves every stationary distribution of the one-step
kernel. -/
theorem kernelIterate_stationary (transition : MarkovKernel State)
    (target : Distribution State) (hstationary : transition.Stationary target)
    (n : ℕ) : (kernelIterate transition n).Stationary target := by
  induction n with
  | zero => exact identity_stationary target
  | succ n ih => exact comp_stationary _ _ target ih hstationary

omit [DecidableEq State] in
theorem kernel_prob_le_one (transition : MarkovKernel State) (x y : State) :
    transition.prob x y ≤ 1 := by
  rw [← transition.sum_prob x]
  exact Finset.single_le_sum (fun z _ => transition.nonneg x z)
    (Finset.mem_univ y)

private theorem iterate_prob_integrable (transition : MarkovKernel State)
    (r : NNReal) (x y : State) :
    Integrable (fun n : ℕ => (kernelIterate transition n).prob x y)
      (poissonMeasure r) := by
  refine Integrable.mono' (integrable_const (μ := poissonMeasure r) (1 : ℝ))
    Measurable.of_discrete.aestronglyMeasurable ?_
  exact ae_of_all _ fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      ((kernelIterate transition n).nonneg x y)]
    exact kernel_prob_le_one _ _ _

/-- Exact transition kernel after a Poisson-distributed number of steps. -/
noncomputable def poissonizedKernel (transition : MarkovKernel State)
    (r : NNReal) : MarkovKernel State where
  prob x y := ∫ n : ℕ, (kernelIterate transition n).prob x y ∂poissonMeasure r
  nonneg x y := integral_nonneg_of_ae <| ae_of_all _ fun n =>
    (kernelIterate transition n).nonneg x y
  sum_prob x := by
    rw [← integral_finsetSum Finset.univ (fun y _ =>
      iterate_prob_integrable transition r x y)]
    simp_rw [(kernelIterate transition _).sum_prob]
    simp

/-- Explicit Poisson-series formula for the real-time transition matrix. -/
theorem poissonizedKernel_prob_eq_tsum (transition : MarkovKernel State)
    (r : NNReal) (x y : State) :
    (poissonizedKernel transition r).prob x y =
      ∑' n : ℕ, Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial *
        (kernelIterate transition n).prob x y := by
  change (∫ n : ℕ, (kernelIterate transition n).prob x y ∂poissonMeasure r) = _
  simpa [smul_eq_mul] using
    (integral_poissonMeasure r
      (fun n : ℕ => (kernelIterate transition n).prob x y))

/-- At zero elapsed intensity no event occurs. -/
@[simp] theorem poissonizedKernel_zero (transition : MarkovKernel State) :
    poissonizedKernel transition 0 = identity := by
  apply MarkovKernel.ext
  funext x y
  rw [poissonizedKernel_prob_eq_tsum]
  rw [tsum_eq_single 0]
  · simp [kernelIterate]
  · intro n hn
    norm_num [zero_pow hn]

/-- Poissonization preserves stationarity because every discrete iterate
preserves the target. -/
theorem poissonizedKernel_stationary (transition : MarkovKernel State)
    (target : Distribution State) (hstationary : transition.Stationary target)
    (r : NNReal) : (poissonizedKernel transition r).Stationary target := by
  intro y
  change (∑ x, target.mass x *
      ∫ n : ℕ, (kernelIterate transition n).prob x y ∂poissonMeasure r) = _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum Finset.univ (fun x _ =>
    (iterate_prob_integrable transition r x y).const_mul (target.mass x))]
  simp_rw [kernelIterate_stationary transition target hstationary _ y]
  simp

/-- Real-time kernel of a bounded finite-rate generator obtained by first
uniformizing at rate `Λ` and then using Poisson intensity `Λt`. -/
noncomputable def FiniteRateGenerator.timeKernel
    (rates : FiniteRateGenerator State) (Λ : ℝ) (hΛ : 0 < Λ)
    (hbound : ∀ x, rates.exitRate x ≤ Λ) (t : NNReal) : MarkovKernel State :=
  poissonizedKernel (rates.uniformizedKernel Λ hΛ hbound)
    ⟨Λ * t, mul_nonneg (le_of_lt hΛ) t.2⟩

/-- Rate reversibility implies stationarity of every Poissonized real-time
kernel. -/
theorem FiniteRateGenerator.timeKernel_stationary
    (rates : FiniteRateGenerator State) (target : Distribution State)
    (hrev : rates.Reversible target) (Λ : ℝ) (hΛ : 0 < Λ)
    (hbound : ∀ x, rates.exitRate x ≤ Λ) (t : NNReal) :
    (rates.timeKernel Λ hΛ hbound t).Stationary target :=
  poissonizedKernel_stationary _ target
    (rates.uniformizedKernel_stationary target hrev Λ hΛ hbound) _

@[simp] theorem FiniteRateGenerator.timeKernel_zero
    (rates : FiniteRateGenerator State) (Λ : ℝ) (hΛ : 0 < Λ)
    (hbound : ∀ x, rates.exitRate x ≤ Λ) :
    rates.timeKernel Λ hΛ hbound 0 = identity := by
  unfold FiniteRateGenerator.timeKernel
  let r : NNReal := ⟨Λ * (0 : NNReal), mul_nonneg (le_of_lt hΛ) (0 : NNReal).2⟩
  have hr : r = 0 := by
    apply Subtype.ext
    simp [r]
  change poissonizedKernel (rates.uniformizedKernel Λ hΛ hbound) r = identity
  rw [hr, poissonizedKernel_zero]

end Mcmc.PDMP
