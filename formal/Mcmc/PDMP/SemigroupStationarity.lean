import Mcmc.PDMP.Generator
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Probability.Kernel.Invariance

/-!
# From forward equations to stationary PDMP kernels

Generator cancellation alone does not imply stationarity. This module records
the missing analytic bridge in a form usable by a constructed transition
family: transported mass of every measurable set must solve the forward
equation. If those real-valued masses are differentiable on nonnegative time
and have zero derivative, they are constant, hence the target is invariant at
every time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory CompactlySupported

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Real mass of a measurable event after transporting `target` through the
kernel at a nonnegative time. -/
noncomputable def transportedRealMass
    (transition : NNReal → Kernel State State) (target : Measure State)
    (event : Set State) (time : ℝ) : ℝ :=
  ((transition (Real.toNNReal time)) ∘ₘ target).real event

/-- The setwise analytic obligation between infinitesimal balance and actual
stationarity. It is deliberately stronger than a generator identity: clients
must justify differentiation of their constructed path-law semigroup. -/
structure SetwiseForwardStationarityCertificate
    (transition : NNReal → Kernel State State) (target : Measure State) : Prop where
  zero : transition 0 = Kernel.id
  differentiable : ∀ event, MeasurableSet event →
    DifferentiableOn ℝ
      (transportedRealMass transition target event) (Set.Ici 0)
  fderivWithin_eq_zero : ∀ event, MeasurableSet event → ∀ time ∈ Set.Ici (0 : ℝ),
    fderivWithin ℝ (transportedRealMass transition target event)
      (Set.Ici 0) time = 0

/-- A setwise forward certificate proves invariance of every transition in
the family. No convergence claim follows. -/
theorem SetwiseForwardStationarityCertificate.invariant
    (transition : NNReal → Kernel State State) (target : Measure State)
    [IsFiniteMeasure target] [∀ time, IsMarkovKernel (transition time)]
    (certificate : SetwiseForwardStationarityCertificate transition target)
    (time : NNReal) :
    (transition time).Invariant target := by
  rw [Kernel.Invariant]
  apply Measure.ext
  intro event hevent
  have hconstant :=
    (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero
      (certificate.differentiable event hevent)
      (certificate.fderivWithin_eq_zero event hevent)
      (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show (time : ℝ) ∈ Set.Ici 0 from time.coe_nonneg)
  have hreal : ((transition time) ∘ₘ target).real event = target.real event := by
    have hconstant' := hconstant.symm
    unfold transportedRealMass at hconstant'
    rw [Real.toNNReal_zero, certificate.zero, Measure.id_comp] at hconstant'
    simpa only [Real.toNNReal_coe] using hconstant'
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

/-- The same certificate packages stationarity for the entire nonnegative-time
family. -/
theorem SetwiseForwardStationarityCertificate.invariant_all
    (transition : NNReal → Kernel State State) (target : Measure State)
    [IsFiniteMeasure target] [∀ time, IsMarkovKernel (transition time)]
    (certificate : SetwiseForwardStationarityCertificate transition target) :
    ∀ time, (transition time).Invariant target :=
  certificate.invariant transition target

/-! ### Compact-test forward equations -/

section CompactTests

variable [TopologicalSpace State] [BorelSpace State]
  [LocallyCompactSpace State] [T2Space State]

/-- Expectation of a compactly supported continuous test after transporting
the target through a nonnegative-time kernel family. -/
noncomputable def transportedCompactExpectation
    (transition : NNReal → Kernel State State) (target : Measure State)
    (test : C_c(State, ℝ)) (time : ℝ) : ℝ :=
  ∫ state, test state ∂((transition (Real.toNNReal time)) ∘ₘ target)

/-- A forward-equation certificate on compactly supported continuous tests.
This is often more natural for generator arguments than measurable-set
indicators, while still determining regular measures. -/
structure CompactTestForwardStationarityCertificate
    (transition : NNReal → Kernel State State) (target : Measure State) : Prop where
  zero : transition 0 = Kernel.id
  differentiable : ∀ test : C_c(State, ℝ),
    DifferentiableOn ℝ
      (transportedCompactExpectation transition target test) (Set.Ici 0)
  fderivWithin_eq_zero : ∀ test : C_c(State, ℝ), ∀ time ∈ Set.Ici (0 : ℝ),
    fderivWithin ℝ
      (transportedCompactExpectation transition target test)
      (Set.Ici 0) time = 0

/-- Compact-test forward equations imply target invariance for every fixed
time. The conclusion follows from the Riesz measure-determination theorem,
not from an unproved promotion of generator balance. -/
theorem CompactTestForwardStationarityCertificate.invariant
    (transition : NNReal → Kernel State State) (target : Measure State)
    [IsFiniteMeasure target] [∀ time, IsMarkovKernel (transition time)]
    [target.Regular] [∀ time, ((transition time) ∘ₘ target).Regular]
    (certificate : CompactTestForwardStationarityCertificate transition target)
    (time : NNReal) :
    (transition time).Invariant target := by
  rw [Kernel.Invariant]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro test
  have hconstant :=
    (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero
      (certificate.differentiable test)
      (certificate.fderivWithin_eq_zero test)
      (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show (time : ℝ) ∈ Set.Ici 0 from time.coe_nonneg)
  have hconstant' := hconstant.symm
  unfold transportedCompactExpectation at hconstant'
  rw [Real.toNNReal_zero, certificate.zero, Measure.id_comp] at hconstant'
  simpa only [Real.toNNReal_coe] using hconstant'

/-- A compact-test certificate proves invariance of the whole family. -/
theorem CompactTestForwardStationarityCertificate.invariant_all
    (transition : NNReal → Kernel State State) (target : Measure State)
    [IsFiniteMeasure target] [∀ time, IsMarkovKernel (transition time)]
    [target.Regular] [∀ time, ((transition time) ∘ₘ target).Regular]
    (certificate : CompactTestForwardStationarityCertificate transition target) :
    ∀ time, (transition time).Invariant target :=
  certificate.invariant transition target

/-! ### Weak-forward uniqueness -/

/-- Expectation of a supplied test observable along a measure-valued curve. -/
noncomputable def weakCurveExpectation
    {Test : Type*} (observe : Test → State → ℝ)
    (curve : NNReal → Measure State) (test : Test)
    (time : ℝ) : ℝ :=
  ∫ state, observe test state ∂curve (Real.toNNReal time)

/-- A probability-measure-valued curve solves the weak forward equation for
`generator` on a chosen test domain when observable expectations differentiate
to generator expectations. Requiring probability marginals is essential for
the process interpretation and later supplies finiteness/regularity facts. -/
structure CompactTestWeakForwardSolution
    {Test : Type*} (observe generator : Test → State → ℝ)
    (initial : Measure State) (curve : NNReal → Measure State) : Prop where
  initial_eq : curve 0 = initial
  probability : ∀ time, IsProbabilityMeasure (curve time)
  generator_integrable : ∀ test time,
    Integrable (generator test) (curve time)
  differentiable : ∀ test,
    DifferentiableOn ℝ (weakCurveExpectation observe curve test) (Set.Ici 0)
  forward : ∀ test time, time ∈ Set.Ici (0 : ℝ) →
    (fderivWithin ℝ (weakCurveExpectation observe curve test)
      (Set.Ici 0) time) 1 =
      ∫ state, generator test state ∂curve (Real.toNNReal time)

/-- Uniqueness of the compact-test weak forward equation for a constructed
transition family. This is the substantive process-level theorem needed to
upgrade infinitesimal generator balance to stationarity. -/
structure CompactTestWeakForwardUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ) : Prop where
  unique : ∀ (initial : Measure State) (curve : NNReal → Measure State),
    CompactTestWeakForwardSolution observe generator initial curve →
    ∀ time, curve time = (transition time) ∘ₘ initial

/-- Target-specific weak-forward uniqueness. This is strictly the obligation
needed for stationarity: every weak solution starting from `target` must agree
with the constructed transported target curve. It does not demand global
well-posedness from arbitrary initial measures. -/
structure CompactTestTargetWeakForwardUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ) (target : Measure State) : Prop where
  unique : ∀ (curve : NNReal → Measure State),
    CompactTestWeakForwardSolution observe generator target curve →
    ∀ time, curve time = (transition time) ∘ₘ target

omit [TopologicalSpace State] [BorelSpace State]
    [LocallyCompactSpace State] [T2Space State] in
/-- Global weak-forward uniqueness implies its target-specific form. -/
theorem CompactTestWeakForwardUniqueness.forTarget
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ)
    (uniqueness : CompactTestWeakForwardUniqueness transition observe generator)
    (target : Measure State) :
    CompactTestTargetWeakForwardUniqueness transition observe generator target where
  unique curve solution time := uniqueness.unique target curve solution time

/-- A test family determines measures when equality of all its expectations
forces equality of the underlying measures. This is logically separate from
uniqueness of the scalar weak equations. -/
structure CompactTestExpectationDetermining
    {Test : Type*} (observe : Test → State → ℝ) : Prop where
  eq_of_expectations : ∀ (left right : Measure State),
    (∀ test, (∫ state, observe test state ∂left) =
      ∫ state, observe test state ∂right) → left = right

/-- The natural measure-determination notion for the locally compact
weak-forward setting: compactly supported continuous functions determine
regular measures. Unlike `CompactTestExpectationDetermining`, this does not
make an unnecessarily global claim about nonregular measures. -/
structure CompactTestRegularExpectationDetermining
    {Test : Type*} (observe : Test → State → ℝ) : Prop where
  eq_of_expectations : ∀ (left right : Measure State),
    left.Regular → right.Regular →
    (∀ test, (∫ state, observe test state ∂left) =
      ∫ state, observe test state ∂right) → left = right

/-- The finite regular variant needed by probability-valued weak-forward
curves. Unlike the unrestricted regular certificate, it asks for determination
only where both measures are finite, exactly matching Markov marginals. -/
structure CompactTestFiniteRegularExpectationDetermining
    {Test : Type*} (observe : Test → State → ℝ) : Prop where
  eq_of_expectations : ∀ (left right : Measure State),
    left.Regular → right.Regular →
    IsFiniteMeasure left → IsFiniteMeasure right →
    (∀ test, (∫ state, observe test state ∂left) =
      ∫ state, observe test state ∂right) → left = right

/-- A test family is determining for regular measures whenever it represents
every compactly supported continuous real function. This discharges the
measure-theoretic half of weak-forward uniqueness; proving scalar uniqueness
for the represented generator domain remains separate. -/
theorem compactTestRegularExpectationDetermining_of_represents_compactlySupported
    {Test : Type*} (observe : Test → State → ℝ)
    (represent : ∀ function : C_c(State, ℝ), ∃ test,
      observe test = fun state => function state) :
    CompactTestRegularExpectationDetermining observe where
  eq_of_expectations left right hleft hright heq := by
    letI : left.Regular := hleft
    letI : right.Regular := hright
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro function
    obtain ⟨test, htest⟩ := represent function
    simpa [htest] using heq test

omit [BorelSpace State] [LocallyCompactSpace State] [T2Space State] in
/-- The older all-measures determination certificate implies the natural
regular-measure certificate. -/
theorem CompactTestExpectationDetermining.toRegular
    {Test : Type*} (observe : Test → State → ℝ)
    (determining : CompactTestExpectationDetermining observe) :
    CompactTestRegularExpectationDetermining observe where
  eq_of_expectations left right _ _ :=
    determining.eq_of_expectations left right

/-- Scalar-expectation form of weak-forward uniqueness. It asks that every
weak solution agree with the constructed transition curve on the supplied
test family, but does not by itself identify the measures. -/
structure CompactTestWeakExpectationUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ) : Prop where
  unique_expectation :
    ∀ (initial : Measure State) (curve : NNReal → Measure State),
      CompactTestWeakForwardSolution observe generator initial curve →
      ∀ time test,
        (∫ state, observe test state ∂curve time) =
          ∫ state, observe test state ∂((transition time) ∘ₘ initial)

/-- Target-started scalar-expectation uniqueness. This is the scalar ODE
obligation actually needed by a stationarity proof. -/
structure CompactTestTargetWeakExpectationUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ) (target : Measure State) : Prop where
  unique_expectation :
    ∀ (curve : NNReal → Measure State),
      CompactTestWeakForwardSolution observe generator target curve →
      ∀ time test,
        (∫ state, observe test state ∂curve time) =
          ∫ state, observe test state ∂((transition time) ∘ₘ target)

omit [TopologicalSpace State] [BorelSpace State]
    [LocallyCompactSpace State] [T2Space State] in
/-- Scalar weak-equation uniqueness plus a measure-determining test family
yields full weak-forward uniqueness. -/
theorem CompactTestWeakExpectationUniqueness.toWeakForwardUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ)
    (scalar : CompactTestWeakExpectationUniqueness transition observe generator)
    (determining : CompactTestExpectationDetermining observe) :
    CompactTestWeakForwardUniqueness transition observe generator where
  unique initial curve solution time :=
    determining.eq_of_expectations (curve time) ((transition time) ∘ₘ initial)
      (fun test => scalar.unique_expectation initial curve solution time test)

omit [TopologicalSpace State] [BorelSpace State]
    [LocallyCompactSpace State] [T2Space State] in
/-- Target-started scalar expectation uniqueness plus measure determination
yields the minimal target-specific weak-forward uniqueness theorem. -/
theorem CompactTestTargetWeakExpectationUniqueness.toTargetWeakForwardUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ) (target : Measure State)
    (scalar : CompactTestTargetWeakExpectationUniqueness
      transition observe generator target)
    (determining : CompactTestExpectationDetermining observe) :
    CompactTestTargetWeakForwardUniqueness
      transition observe generator target where
  unique curve solution time :=
    determining.eq_of_expectations (curve time) ((transition time) ∘ₘ target)
      (fun test => scalar.unique_expectation curve solution time test)

omit [BorelSpace State] [LocallyCompactSpace State] [T2Space State] in
/-- Regular-measure version of the target-started scalar-to-measure upgrade.
It avoids the stronger requirement that the test family determine arbitrary
nonregular measures. The two regularity premises expose exactly what is needed
for the candidate weak solution and the constructed transition curve. -/
theorem CompactTestTargetWeakExpectationUniqueness.toTargetWeakForwardUniqueness_of_regular
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ) (target : Measure State)
    (scalar : CompactTestTargetWeakExpectationUniqueness
      transition observe generator target)
    (determining : CompactTestRegularExpectationDetermining observe)
    (hcurve : ∀ (curve : NNReal → Measure State),
      CompactTestWeakForwardSolution observe generator target curve →
      ∀ time, (curve time).Regular)
    (htransport : ∀ time, ((transition time) ∘ₘ target).Regular) :
    CompactTestTargetWeakForwardUniqueness
      transition observe generator target where
  unique curve solution time :=
    determining.eq_of_expectations (curve time) ((transition time) ∘ₘ target)
      (hcurve curve solution time) (htransport time)
      (fun test => scalar.unique_expectation curve solution time test)

omit [BorelSpace State] [LocallyCompactSpace State] [T2Space State] in
/-- Finite-regular version of the target-started scalar-to-measure upgrade.
Probability laws supply the two finiteness witnesses automatically. -/
theorem CompactTestTargetWeakExpectationUniqueness.toTargetWeakForwardUniqueness_of_finiteRegular
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ) (target : Measure State)
    [IsProbabilityMeasure target]
    [∀ time, IsMarkovKernel (transition time)]
    (scalar : CompactTestTargetWeakExpectationUniqueness
      transition observe generator target)
    (determining : CompactTestFiniteRegularExpectationDetermining observe)
    (hcurve : ∀ (curve : NNReal → Measure State),
      CompactTestWeakForwardSolution observe generator target curve →
      ∀ time, (curve time).Regular)
    (htransport : ∀ time, ((transition time) ∘ₘ target).Regular) :
    CompactTestTargetWeakForwardUniqueness
      transition observe generator target where
  unique curve solution time := by
    letI : IsProbabilityMeasure (curve time) := solution.probability time
    letI : IsProbabilityMeasure ((transition time) ∘ₘ target) := by
      infer_instance
    exact determining.eq_of_expectations
      (curve time) ((transition time) ∘ₘ target)
      (hcurve curve solution time) (htransport time)
      (by infer_instance) (by infer_instance)
      (fun test => scalar.unique_expectation curve solution time test)

omit [TopologicalSpace State] [BorelSpace State]
    [LocallyCompactSpace State] [T2Space State] in
/-- Global scalar uniqueness implies target-started scalar uniqueness. -/
theorem CompactTestWeakExpectationUniqueness.forTarget
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ)
    (scalar : CompactTestWeakExpectationUniqueness transition observe generator)
    (target : Measure State) :
    CompactTestTargetWeakExpectationUniqueness
      transition observe generator target where
  unique_expectation curve solution time test :=
    scalar.unique_expectation target curve solution time test

omit [TopologicalSpace State] [BorelSpace State]
  [LocallyCompactSpace State] [T2Space State] in
/-- Generator balance makes the constant target curve a weak-forward
solution. This theorem performs no process-law uniqueness step. -/
theorem compactTestWeakForwardSolution_const
    {Test : Type*} (observe generator : Test → State → ℝ)
    (target : Measure State) [IsProbabilityMeasure target]
    (hintegrable : ∀ test, Integrable (generator test) target)
    (hbalance : ∀ test, (∫ state, generator test state ∂target) = 0) :
    CompactTestWeakForwardSolution observe generator target (fun _ => target) where
  initial_eq := rfl
  probability := fun _ => inferInstance
  generator_integrable := fun test _ => hintegrable test
  differentiable := by
    intro test
    unfold weakCurveExpectation
    simp
  forward := by
    intro test time htime
    unfold weakCurveExpectation
    rw [hbalance test]
    simp

omit [TopologicalSpace State] [BorelSpace State]
  [LocallyCompactSpace State] [T2Space State] in
/-- Weak-forward uniqueness plus generator balance proves invariance of the
constructed transition family. This explicitly records the uniqueness theorem
that is absent from a bare generator-cancellation argument. -/
theorem invariant_of_compactTest_generatorBalance_and_weakUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ)
    (target : Measure State) [IsProbabilityMeasure target]
    (uniqueness : CompactTestWeakForwardUniqueness transition observe generator)
    (hintegrable : ∀ test, Integrable (generator test) target)
    (hbalance : ∀ test, (∫ state, generator test state ∂target) = 0)
    (time : NNReal) :
    (transition time).Invariant target := by
  rw [Kernel.Invariant]
  exact (uniqueness.unique target (fun _ => target)
    (compactTestWeakForwardSolution_const observe generator target
      hintegrable hbalance)
    time).symm

omit [TopologicalSpace State] [BorelSpace State]
  [LocallyCompactSpace State] [T2Space State] in
/-- Target-specific weak-forward uniqueness is sufficient for generator
balance to imply invariance; global uniqueness from every initial law is not
required. -/
theorem invariant_of_compactTest_generatorBalance_and_targetWeakUniqueness
    {Test : Type*}
    (transition : NNReal → Kernel State State)
    (observe generator : Test → State → ℝ)
    (target : Measure State) [IsProbabilityMeasure target]
    (uniqueness : CompactTestTargetWeakForwardUniqueness
      transition observe generator target)
    (hintegrable : ∀ test, Integrable (generator test) target)
    (hbalance : ∀ test, (∫ state, generator test state ∂target) = 0)
    (time : NNReal) :
    (transition time).Invariant target := by
  rw [Kernel.Invariant]
  exact (uniqueness.unique (fun _ => target)
    (compactTestWeakForwardSolution_const observe generator target
      hintegrable hbalance)
    time).symm

end CompactTests

end Mcmc.PDMP
