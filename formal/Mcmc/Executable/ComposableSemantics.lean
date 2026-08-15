import Mcmc.Executable.ComposableIR
import Mcmc.Kernel.ComposableInference

/-!
# Semantic bindings for composable-inference descriptors

The portable IR contains names and scopes, while correctness lives in
measure-kernel semantics.  This module binds the two without pretending that a
name alone proves a runtime callback correct.  A bound operator carries its
actual full-state Markov kernel and target-invariance proof; schedules execute
those kernels in descriptor order.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace Mcmc.Executable.ComposableSemantics

open ProbabilityTheory
open Mcmc.Kernel.ComposableInference

variable {State : Type*} [MeasurableSpace State]

/-- Semantic implementation of one portable descriptor. -/
structure BoundOperator (target : Measure State) where
  descriptor : ComposableIR.OperatorDescriptor
  operator : ScopedOperator (Variable := String) target
  scope_eq : operator.scope = {name | name ∈ descriptor.scope}

/-- Erase proofs and kernels back to portable metadata. -/
def BoundOperator.toDescriptor {target : Measure State}
    (operator : BoundOperator target) : ComposableIR.OperatorDescriptor :=
  operator.descriptor

/-- A descriptor schedule together with an ordered semantic implementation of
every operator. -/
structure BoundSchedule (target : Measure State) where
  descriptor : ComposableIR.ScheduleDescriptor
  operators : List (BoundOperator target)
  descriptors_eq : operators.map BoundOperator.toDescriptor =
    descriptor.operators

/-- Execute the kernels certified by a bound schedule. -/
noncomputable def BoundSchedule.kernel {target : Measure State}
    (schedule : BoundSchedule target) : Kernel State State :=
  Mcmc.Kernel.ComposableInference.schedule target
    (schedule.operators.map BoundOperator.operator)

instance BoundSchedule.kernel.instIsMarkovKernel {target : Measure State}
    (schedule : BoundSchedule target) : IsMarkovKernel schedule.kernel := by
  unfold BoundSchedule.kernel
  infer_instance

/-- Semantic schedule execution preserves the common target. -/
theorem BoundSchedule.kernel_invariant {target : Measure State}
    (schedule : BoundSchedule target) : schedule.kernel.Invariant target := by
  exact schedule_invariant target
    (schedule.operators.map BoundOperator.operator)

/-- Binding preserves descriptor order exactly; there is no name-based
reordering at the semantic boundary. -/
theorem BoundSchedule.operator_descriptors {target : Measure State}
    (schedule : BoundSchedule target) :
    schedule.operators.map BoundOperator.toDescriptor =
      schedule.descriptor.operators :=
  schedule.descriptors_eq

end Mcmc.Executable.ComposableSemantics
