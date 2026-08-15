import Mcmc.PDMP.Generator
import Mcmc.PDMP.GeneralPoissonization
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

/-!
# General-state bounded-rate uniformization

A state-dependent jump mechanism with rate bounded by a positive homogeneous
clock can be simulated at clock events: take the genuine jump with probability
`rate(x) / clockRate`, and otherwise retain the current state. This module
constructs that mathlib kernel and proves it Markov. Composing it with general
Poissonization yields the bounded-rate, nonexplosive real-time transition
kernel on arbitrary measurable state spaces.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- State-dependent probability that a homogeneous clock event is genuine. -/
noncomputable def JumpMechanism.clockAcceptance (mechanism : JumpMechanism State)
    (clockRate : NNReal) : State → ENNReal :=
  fun x => mechanism.rate x / clockRate

theorem JumpMechanism.measurable_clockAcceptance
    (mechanism : JumpMechanism State) (clockRate : NNReal) :
    Measurable (mechanism.clockAcceptance clockRate) :=
  mechanism.measurable_rate.div_const _

/-- Uniformized embedded chain: a rate-thinned genuine jump plus the unused
clock mass as a virtual self-event. -/
noncomputable def JumpMechanism.uniformizedKernel
    (mechanism : JumpMechanism State) (clockRate : NNReal) :
    Kernel State State :=
  Kernel.withDensity mechanism.jump
      (fun x _ => mechanism.clockAcceptance clockRate x) +
    Kernel.withDensity Kernel.id
      (fun x _ => 1 - mechanism.clockAcceptance clockRate x)

/-- Exact row formula for the general-state uniformized kernel. -/
theorem JumpMechanism.uniformizedKernel_apply
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (x : State) {s : Set State} (hs : MeasurableSet s) :
    mechanism.uniformizedKernel clockRate x s =
      mechanism.clockAcceptance clockRate x * mechanism.jump x s +
        (1 - mechanism.clockAcceptance clockRate x) *
          (Kernel.id : Kernel State State) x s := by
  have haccept : Measurable (Function.uncurry
      (fun x : State => fun _ : State =>
        mechanism.clockAcceptance clockRate x)) := by
    change Measurable (fun p : State × State =>
      mechanism.clockAcceptance clockRate p.1)
    exact (mechanism.measurable_clockAcceptance clockRate).comp measurable_fst
  have hrejection : Measurable (Function.uncurry
      (fun x : State => fun _ : State =>
        1 - mechanism.clockAcceptance clockRate x)) := by
    change Measurable (fun p : State × State =>
      1 - mechanism.clockAcceptance clockRate p.1)
    exact ((mechanism.measurable_clockAcceptance clockRate).const_sub 1).comp
      measurable_fst
  rw [JumpMechanism.uniformizedKernel, Kernel.add_apply,
    Measure.add_apply, Kernel.withDensity_apply _ haccept,
    Kernel.withDensity_apply _ hrejection]
  simp only [withDensity_apply _ hs, lintegral_const]
  simp

/-- A rate bound ensures every clock-acceptance probability is at most one. -/
theorem JumpMechanism.clockAcceptance_le_one
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate) (x : State) :
    mechanism.clockAcceptance clockRate x ≤ 1 := by
  unfold JumpMechanism.clockAcceptance
  apply ENNReal.div_le_of_le_mul
  simpa using hbound x

/-- Bounded-rate general-state uniformization is a Markov kernel. -/
theorem JumpMechanism.uniformizedKernel_isMarkov
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (_hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate) :
    IsMarkovKernel (mechanism.uniformizedKernel clockRate) := by
  constructor
  intro x
  constructor
  rw [mechanism.uniformizedKernel_apply clockRate x MeasurableSet.univ]
  simp only [measure_univ, mul_one]
  have hle := mechanism.clockAcceptance_le_one clockRate hbound x
  exact add_tsub_cancel_of_le hle

/-- Real-time bounded-clock transition kernel for a general jump mechanism. -/
noncomputable def JumpMechanism.timeKernel
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (time : NNReal) : Kernel State State :=
  letI := mechanism.uniformizedKernel_isMarkov clockRate hclock hbound
  generalPoissonizedKernel (mechanism.uniformizedKernel clockRate)
    (clockRate * time)

/-- The bounded-clock real-time transition is Markov. -/
theorem JumpMechanism.timeKernel_isMarkov
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (time : NNReal) :
    IsMarkovKernel (mechanism.timeKernel clockRate hclock hbound time) := by
  letI := mechanism.uniformizedKernel_isMarkov clockRate hclock hbound
  unfold JumpMechanism.timeKernel
  infer_instance

/-- Any invariant target of the embedded uniformized chain is invariant at
every real time. Balanced-flux clients discharge the embedded premise. -/
theorem JumpMechanism.timeKernel_invariant
    (mechanism : JumpMechanism State) (clockRate : NNReal)
    (hclock : 0 < clockRate)
    (hbound : ∀ x, mechanism.rate x ≤ clockRate)
    (target : Measure State) [IsProbabilityMeasure target]
    (hinvariant : (mechanism.uniformizedKernel clockRate).Invariant target)
    (time : NNReal) :
    (mechanism.timeKernel clockRate hclock hbound time).Invariant target := by
  letI := mechanism.uniformizedKernel_isMarkov clockRate hclock hbound
  unfold JumpMechanism.timeKernel
  exact generalPoissonizedKernel_invariant _ target hinvariant _

/-- The event count used by every bounded-clock time kernel is almost surely
finite on a finite horizon. -/
theorem JumpMechanism.timeKernel_eventCount_finite_ae
    (_mechanism : JumpMechanism State) (clockRate time : NNReal) :
    ∀ᵐ n ∂poissonMeasure (clockRate * time), ∃ bound : ℕ, n ≤ bound :=
  poisson_count_finite_ae _

end Mcmc.PDMP
