import Mcmc.PDMP.Generator
import Mathlib.Analysis.Calculus.MeanValue
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
open scoped ENNReal NNReal ProbabilityTheory

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

end Mcmc.PDMP
