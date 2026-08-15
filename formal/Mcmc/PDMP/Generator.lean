import Mcmc.Kernel.AuxiliaryGibbs
import Mcmc.Finite.MarkovKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Piecewise-deterministic Markov-process foundations

PDMP correctness is naturally stated through an infinitesimal generator, not
through a discrete-time transition kernel.  This module therefore starts a
separate architecture.  It records generator invariance on an explicit test
class, rate-biased jump-flux balance for general-state kernels, and the exact
finite-rate detailed-balance calculation used by finite velocity-switching
clients.

No process-existence or semigroup theorem is inferred from a generator
identity alone.  Those analytic obligations remain explicit for continuous
BPS or Zig-Zag clients.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace Mcmc.PDMP

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Infinitesimal invariance of a generator on a declared class of test
functions. Integrability is part of the certificate. -/
def GeneratorInvariant (target : Measure State)
    (generator : (State → ℝ) → State → ℝ)
    (Test : Set (State → ℝ)) : Prop :=
  ∀ f ∈ Test, Integrable (generator f) target ∧
    (∫ x, generator f x ∂target) = 0

/-- Pointwise sum of two generator components. -/
def generatorSum
    (first second : (State → ℝ) → State → ℝ) :
    (State → ℝ) → State → ℝ :=
  fun f x => first f x + second f x

/-- Separately balanced integrable generator components have a balanced sum. -/
theorem GeneratorInvariant.add
    {target : Measure State} {first second : (State → ℝ) → State → ℝ}
    {Test : Set (State → ℝ)}
    (hfirst : GeneratorInvariant target first Test)
    (hsecond : GeneratorInvariant target second Test) :
    GeneratorInvariant target (generatorSum first second) Test := by
  intro f hf
  obtain ⟨hfi, hfb⟩ := hfirst f hf
  obtain ⟨hsi, hsb⟩ := hsecond f hf
  refine ⟨hfi.add hsi, ?_⟩
  change (∫ x, first f x + second f x ∂target) = 0
  rw [integral_add hfi hsi, hfb, hsb, add_zero]

/-- State-dependent event rate and post-event Markov kernel. -/
structure JumpMechanism (State : Type*) [MeasurableSpace State] where
  rate : State → ENNReal
  measurable_rate : Measurable rate
  jump : Kernel State State
  isMarkov : IsMarkovKernel jump := by infer_instance

attribute [instance] JumpMechanism.isMarkov

/-- Event-time law obtained by biasing a base law by the event rate. -/
noncomputable def JumpMechanism.eventMeasure
    (mechanism : JumpMechanism State) (target : Measure State) : Measure State :=
  target.withDensity mechanism.rate

/-- Incoming and outgoing event fluxes balance when the jump kernel preserves
the rate-biased event measure. -/
def JumpMechanism.HasBalancedFlux
    (mechanism : JumpMechanism State) (target : Measure State) : Prop :=
  mechanism.jump.Invariant (mechanism.eventMeasure target)

/-- Balanced jump flux gives equality of post-event and pre-event expectations
for every nonnegative measurable observable. -/
theorem JumpMechanism.lintegral_postJump_eq
    (mechanism : JumpMechanism State) (target : Measure State)
    (hflux : mechanism.HasBalancedFlux target)
    (f : State → ENNReal) (hf : Measurable f) :
    ∫⁻ x, (∫⁻ y, f y ∂mechanism.jump x)
        ∂mechanism.eventMeasure target =
      ∫⁻ x, f x ∂mechanism.eventMeasure target := by
  rw [← Measure.lintegral_bind mechanism.jump.aemeasurable hf.aemeasurable]
  rw [hflux]

section FiniteRates

variable {FiniteState : Type*} [Fintype FiniteState]

/-- Finite-state continuous-time rate matrix represented by its off-diagonal
rates. The diagonal convention is absorbed by the difference `f(y)-f(x)`. -/
structure FiniteRateGenerator (FiniteState : Type*) [Fintype FiniteState] where
  rate : FiniteState → FiniteState → ℝ
  nonneg : ∀ x y, 0 ≤ rate x y

/-- Continuous-time generator associated with finite jump rates. -/
def FiniteRateGenerator.apply (rates : FiniteRateGenerator FiniteState)
    (f : FiniteState → ℝ) (x : FiniteState) : ℝ :=
  ∑ y, rates.rate x y * (f y - f x)

/-- Detailed balance for continuous-time rates. -/
def FiniteRateGenerator.Reversible
    (rates : FiniteRateGenerator FiniteState)
    (target : Mcmc.Finite.MarkovKernel.Distribution FiniteState) : Prop :=
  ∀ x y, target.mass x * rates.rate x y =
    target.mass y * rates.rate y x

/-- Rate detailed balance implies the finite generator has target mean zero.
This is the infinitesimal stationarity equation for a finite CTMC. -/
theorem FiniteRateGenerator.sum_mass_mul_apply_eq_zero
    (rates : FiniteRateGenerator FiniteState)
    (target : Mcmc.Finite.MarkovKernel.Distribution FiniteState)
    (hrev : rates.Reversible target) (f : FiniteState → ℝ) :
    ∑ x, target.mass x * rates.apply f x = 0 := by
  simp only [FiniteRateGenerator.apply, Finset.mul_sum]
  have hswap :
      (∑ x, ∑ y, target.mass x *
        (rates.rate x y * (f y - f x))) =
      ∑ x, ∑ y, target.mass y *
        (rates.rate y x * (f x - f y)) := by
    rw [Finset.sum_comm]
  have hneg :
      (∑ x, ∑ y, target.mass x *
        (rates.rate x y * (f y - f x))) =
      -(∑ x, ∑ y, target.mass x *
        (rates.rate x y * (f y - f x))) := by
    calc
      _ = ∑ x, ∑ y, target.mass y *
          (rates.rate y x * (f x - f y)) := hswap
      _ = ∑ x, ∑ y, -(target.mass x *
          (rates.rate x y * (f y - f x))) := by
        apply Finset.sum_congr rfl
        intro x _hx
        apply Finset.sum_congr rfl
        intro y _hy
        calc
          target.mass y * (rates.rate y x * (f x - f y)) =
              (target.mass y * rates.rate y x) * (f x - f y) := by ring
          _ = (target.mass x * rates.rate x y) * (f x - f y) := by
            rw [hrev y x]
          _ = -(target.mass x * (rates.rate x y * (f y - f x))) := by ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hzero :
      (∑ x, ∑ y, target.mass x *
        (rates.rate x y * (f y - f x))) = 0 := by linarith
  exact hzero

end FiniteRates

end Mcmc.PDMP
