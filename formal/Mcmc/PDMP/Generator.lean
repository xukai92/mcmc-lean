import Mcmc.Kernel.AuxiliaryGibbs
import Mcmc.Finite.MarkovKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.ODE.Gronwall
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

/-- Differential form of the Dynkin--Gronwall estimate.  If the expected
Lyapunov value has derivative at most `-rate * value + allowance`, then its
positive-time value is bounded by the exact exponentially decaying affine
envelope.  Concrete PDMP clients only need to establish the expectation
derivative identity; the analytic comparison is handled here. -/
theorem expectation_le_exp_decay_add_of_hasDerivAt
    (expectation derivative : ℝ → ℝ) (rate allowance horizon : ℝ)
    (hrate : 0 < rate) (hhorizon : 0 ≤ horizon)
    (hcontinuous : ContinuousOn expectation (Set.Icc 0 horizon))
    (hderiv : ∀ time ∈ Set.Ico (0 : ℝ) horizon,
      HasDerivWithinAt expectation (derivative time) (Set.Ici time) time)
    (hbound : ∀ time ∈ Set.Ico (0 : ℝ) horizon,
      derivative time ≤ -rate * expectation time + allowance) :
    expectation horizon ≤
      Real.exp (-rate * horizon) * expectation 0 +
        allowance / rate * (1 - Real.exp (-rate * horizon)) := by
  have hcomparison := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := horizon) (f := expectation) (f' := derivative)
    hcontinuous
    (fun time htime r hr => (hderiv time htime).liminf_right_slope_le hr)
    (le_refl (expectation 0))
    hbound
    horizon ⟨hhorizon, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hrate.ne')]
    at hcomparison
  simp only [sub_zero] at hcomparison
  calc
    expectation horizon ≤
        expectation 0 * Real.exp (-rate * horizon) +
          allowance / (-rate) * (Real.exp (-rate * horizon) - 1) := hcomparison
    _ = Real.exp (-rate * horizon) * expectation 0 +
          allowance / rate * (1 - Real.exp (-rate * horizon)) := by
      field_simp
      ring

/-- Kernel-facing Dynkin--Gronwall transfer.  A pointwise affine generator
drift inequality becomes an exact positive-time expectation bound once the
kernel family supplies the Dynkin derivative identity and the required
integrability.  This theorem deliberately does not infer Dynkin's formula from
a symbolic generator. -/
theorem kernel_expectation_le_exp_decay_add_of_dynkin
    (semigroup : ℝ → Kernel State State)
    (observable generatorValue : State → ℝ)
    (rate allowance horizon : ℝ)
    (hmarkov : ∀ time : ℝ, IsMarkovKernel (semigroup time))
    (hrate : 0 < rate) (hhorizon : 0 ≤ horizon)
    (hobservable : ∀ time : ℝ, ∀ state : State,
      Integrable observable (semigroup time state))
    (hgenerator : ∀ time : ℝ, ∀ state : State,
      Integrable generatorValue (semigroup time state))
    (hzero : ∀ state : State,
      (∫ next, observable next ∂semigroup 0 state) = observable state)
    (hcontinuous : ∀ state : State,
      ContinuousOn
        (fun elapsed => ∫ next, observable next ∂semigroup elapsed state)
        (Set.Icc 0 horizon))
    (hdynkin : ∀ state : State, ∀ time ∈ Set.Ico (0 : ℝ) horizon,
      HasDerivWithinAt
        (fun elapsed => ∫ next, observable next ∂semigroup elapsed state)
        (∫ next, generatorValue next ∂semigroup time state)
        (Set.Ici time) time)
    (hdrift : ∀ state : State,
      generatorValue state ≤ -rate * observable state + allowance)
    (state : State) :
    (∫ next, observable next ∂semigroup horizon state) ≤
      Real.exp (-rate * horizon) * observable state +
        allowance / rate * (1 - Real.exp (-rate * horizon)) := by
  let expectation : ℝ → ℝ := fun time =>
    ∫ next, observable next ∂semigroup time state
  let derivative : ℝ → ℝ := fun time =>
    ∫ next, generatorValue next ∂semigroup time state
  have hderivative : ∀ time ∈ Set.Ico (0 : ℝ) horizon,
      HasDerivWithinAt expectation (derivative time) (Set.Ici time) time :=
    fun time htime => hdynkin state time htime
  have hbound : ∀ time ∈ Set.Ico (0 : ℝ) horizon,
      derivative time ≤ -rate * expectation time + allowance := by
    intro time _
    letI : IsMarkovKernel (semigroup time) := hmarkov time
    have hright : Integrable
        (fun next => -rate * observable next + allowance)
        (semigroup time state) :=
      (hobservable time state).const_mul (-rate) |>.add (integrable_const _)
    have hintegral := integral_mono (hgenerator time state) hright
      hdrift
    dsimp [derivative, expectation]
    calc
      (∫ next, generatorValue next ∂semigroup time state) ≤
          ∫ next, -rate * observable next + allowance
            ∂semigroup time state := hintegral
      _ = -rate * (∫ next, observable next ∂semigroup time state) +
          allowance := by
        rw [integral_add, integral_const_mul, integral_const]
        · simp
        · exact (hobservable time state).const_mul (-rate)
        · exact integrable_const _
  have hcomparison := expectation_le_exp_decay_add_of_hasDerivAt
    expectation derivative rate allowance horizon hrate hhorizon
    (hcontinuous state) hderivative hbound
  simpa [expectation, hzero state] using hcomparison

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

/-- Generator contribution of an independent constant-rate Markov refresh.
At a refresh event the state is replaced according to `refresh x`; the
holding-rate factor is kept real because this is a signed generator term. -/
noncomputable def constantRateKernelGenerator
    (rate : ℝ) (refresh : Kernel State State)
    (f : State → ℝ) (x : State) : ℝ :=
  rate * ((∫ y, f y ∂refresh x) - f x)

/-- Integrability of the refreshed expectation and the observable implies
integrability of the constant-rate refresh generator. -/
theorem integrable_constantRateKernelGenerator
    (rate : ℝ) (refresh : Kernel State State) (f : State → ℝ)
    (target : Measure State)
    (hpost : Integrable (fun x ↦ ∫ y, f y ∂refresh x) target)
    (hf : Integrable f target) :
    Integrable (constantRateKernelGenerator rate refresh f) target := by
  exact (hpost.sub hf).const_mul rate

/-- A refresh component has zero target mean whenever its post-refresh
expectation has the same target mean as the original observable.  This lemma
deliberately exposes the Fubini/invariance equality needed by a concrete
kernel rather than silently inferring it from a pointwise statement. -/
theorem integral_constantRateKernelGenerator_eq_zero
    (rate : ℝ) (refresh : Kernel State State) (f : State → ℝ)
    (target : Measure State)
    (hpost : Integrable (fun x ↦ ∫ y, f y ∂refresh x) target)
    (hf : Integrable f target)
    (hmean : (∫ x, ∫ y, f y ∂refresh x ∂target) =
      ∫ x, f x ∂target) :
    (∫ x, constantRateKernelGenerator rate refresh f x ∂target) = 0 := by
  unfold constantRateKernelGenerator
  rw [integral_const_mul, integral_sub hpost hf, hmean, sub_self, mul_zero]

/-- A family of observables whose refresh expectations are integrable and
target-balanced gives a generator-invariant constant-rate refresh component. -/
theorem generatorInvariant_constantRateKernel
    (rate : ℝ) (refresh : Kernel State State) (target : Measure State)
    (Test : Set (State → ℝ))
    (hpost : ∀ f ∈ Test,
      Integrable (fun x ↦ ∫ y, f y ∂refresh x) target)
    (hf : ∀ f ∈ Test, Integrable f target)
    (hmean : ∀ f ∈ Test,
      (∫ x, ∫ y, f y ∂refresh x ∂target) =
        ∫ x, f x ∂target) :
    GeneratorInvariant target
      (constantRateKernelGenerator rate refresh) Test := by
  intro f hftest
  exact ⟨integrable_constantRateKernelGenerator rate refresh f target
      (hpost f hftest) (hf f hftest),
    integral_constantRateKernelGenerator_eq_zero rate refresh f target
      (hpost f hftest) (hf f hftest) (hmean f hftest)⟩

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
