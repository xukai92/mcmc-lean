import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import McmcLean.Kernel.Coupling

/-!
# Finite-time laws of coupled Markov chains

This module connects coupled transition kernels to the laws of the chains at
a fixed time. Starting from a coupled initial measure and iterating a coupled
kernel, the resulting joint law has exactly the laws of the two marginal
chains as its coordinate marginals.

Full path-space laws will use mathlib's Ionescu--Tulcea construction; the
finite-time statements here are the marginal invariants that construction
must preserve.
-/

open MeasureTheory
open scoped ProbabilityTheory

namespace McmcLean
namespace Kernel

open ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Algorithm-1 initialization for a lagged paired Markov state. Starting
from `(X₀,Y₀)`, draw `X₁` from `transition X₀` and retain `Y₀`, producing the
initial paired state `(X₁,Y₀)`. -/
noncomputable def laggedInitialMeasure
    (initialCoupling : Measure (α × α))
    (transition : ProbabilityTheory.Kernel α α) : Measure (α × α) :=
  Measure.bind initialCoupling
    (independentCoupling transition ProbabilityTheory.Kernel.id)

instance laggedInitialMeasure.instIsProbabilityMeasure
    (initialCoupling : Measure (α × α)) [IsProbabilityMeasure initialCoupling]
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    IsProbabilityMeasure (laggedInitialMeasure initialCoupling transition) := by
  unfold laggedInitialMeasure
  infer_instance

/-- The lagged initial law has marginals `π₀K` and `π₀`, exactly matching
Algorithm 1 after its separate first-chain update. -/
theorem laggedInitialMeasure_isMeasureCoupling
    (initialCoupling : Measure (α × α)) (initial : Measure α)
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition]
    (hinitial : IsMeasureCoupling initialCoupling initial initial) :
    IsMeasureCoupling (laggedInitialMeasure initialCoupling transition)
      (Measure.bind initial transition) initial := by
  unfold laggedInitialMeasure
  have hlift := independentCoupling_isCoupling transition
    (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel α α)
  have h := compMeasure_isMeasureCoupling initialCoupling initial initial
    (independentCoupling transition
      (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel α α))
    transition (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel α α)
    hinitial hlift
  simpa using h

/-- The distribution after `n` applications of a homogeneous transition
kernel. -/
noncomputable def lawAtTime
    (initial : Measure α) (transition : ProbabilityTheory.Kernel α α) (n : ℕ) :
    Measure α :=
  (transition ^ n : ProbabilityTheory.Kernel α α) ∘ₘ initial

@[simp]
theorem lawAtTime_zero
    (initial : Measure α) (transition : ProbabilityTheory.Kernel α α) :
    lawAtTime initial transition 0 = initial := by
  have hone : (1 : ProbabilityTheory.Kernel α α) = ProbabilityTheory.Kernel.id := rfl
  rw [lawAtTime, pow_zero, hone, Measure.id_comp]

/-- The time-`n+1` law is obtained by applying the transition once to the
time-`n` law. -/
theorem lawAtTime_succ
    (initial : Measure α) (transition : ProbabilityTheory.Kernel α α) (n : ℕ) :
    lawAtTime initial transition (n + 1) = transition ∘ₘ lawAtTime initial transition n := by
  rw [lawAtTime, lawAtTime, pow_succ']
  exact Measure.comp_assoc.symm

/-- Starting from an invariant law leaves every finite-time marginal equal
to that law. -/
theorem lawAtTime_eq_of_invariant
    (initial : Measure α) (transition : ProbabilityTheory.Kernel α α)
    (hinvariant : transition.Invariant initial) (n : ℕ) :
    lawAtTime initial transition n = initial := by
  induction n with
  | zero => exact lawAtTime_zero initial transition
  | succ n ih =>
      rw [lawAtTime_succ, ih]
      exact hinvariant

/-- Starting from a point mass, the finite-time law is the corresponding
kernel power evaluated at that point. -/
@[simp]
theorem lawAtTime_dirac
    (x : α) (transition : ProbabilityTheory.Kernel α α) (n : ℕ) :
    lawAtTime (Measure.dirac x) transition n = (transition ^ n) x := by
  unfold lawAtTime
  exact Measure.dirac_bind (ProbabilityTheory.Kernel.measurable _) x

/-- Powers of a Markov kernel remain Markov kernels. -/
instance pow.instIsMarkovKernel
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] (n : ℕ) :
    IsMarkovKernel (transition ^ n) := by
  induction n with
  | zero =>
      change IsMarkovKernel
        (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel α α)
      infer_instance
  | succ n ih =>
      rw [pow_succ]
      change IsMarkovKernel ((transition ^ n) ∘ₖ transition)
      infer_instance

/-- A probability initial law evolved by a Markov kernel remains a
probability measure at every finite time. -/
instance lawAtTime.instIsProbabilityMeasure
    (initial : Measure α) [IsProbabilityMeasure initial]
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition]
    (n : ℕ) :
    IsProbabilityMeasure (lawAtTime initial transition n) := by
  unfold lawAtTime
  infer_instance

/-- The time-`n` law of a coupled chain couples the time-`n` laws of its two
marginal chains. -/
theorem lawAtTime_isMeasureCoupling
    (initial : Measure (α × β))
    (leftInitial : Measure α) (rightInitial : Measure β)
    (coupled : ProbabilityTheory.Kernel (α × β) (α × β))
    (left : ProbabilityTheory.Kernel α α)
    (right : ProbabilityTheory.Kernel β β)
    (hInitial : IsMeasureCoupling initial leftInitial rightInitial)
    (hCoupled : IsCoupling coupled left right) (n : ℕ) :
    IsMeasureCoupling (lawAtTime initial coupled n)
      (lawAtTime leftInitial left n) (lawAtTime rightInitial right n) := by
  unfold lawAtTime
  exact compMeasure_isMeasureCoupling initial leftInitial rightInitial
    (coupled ^ n) (left ^ n) (right ^ n) hInitial
    (pow_isCoupling coupled left right hCoupled n)

/-- Turn a homogeneous transition kernel into the history-dependent family
expected by mathlib's Ionescu--Tulcea construction. At stage `n`, the next
transition depends only on the latest entry of the history. -/
noncomputable def homogeneousNext
    (transition : ProbabilityTheory.Kernel α α) (n : ℕ) :
    ProbabilityTheory.Kernel ((i : Finset.Iic n) → α) α :=
  let latest : Finset.Iic n := ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  transition.comap (fun history => history latest) (measurable_pi_apply latest)

instance homogeneousNext.instIsMarkovKernel
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] (n : ℕ) :
    IsMarkovKernel (homogeneousNext transition n) := by
  unfold homogeneousNext
  infer_instance

/-- Regard a starting point as the complete history through time zero. -/
def initialHistory (x : α) : (i : Finset.Iic 0) → α :=
  fun _ => x

/-- The time-zero history embedding is measurable. -/
theorem measurable_initialHistory :
    Measurable (initialHistory : α → (i : Finset.Iic 0) → α) := by
  exact measurable_pi_lambda _ fun _ => measurable_id

/-- The infinite path kernel of a homogeneous Markov transition, conditional
on its time-zero state. This is the Ionescu--Tulcea law on `ℕ → α`. -/
noncomputable def pathKernel
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    ProbabilityTheory.Kernel α (ℕ → α) := by
  letI : ∀ n, IsMarkovKernel (homogeneousNext transition n) := fun n =>
    homogeneousNext.instIsMarkovKernel transition n
  exact (ProbabilityTheory.Kernel.traj (homogeneousNext transition) 0).comap
    initialHistory measurable_initialHistory

instance pathKernel.instIsMarkovKernel
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    IsMarkovKernel (pathKernel transition) := by
  unfold pathKernel
  infer_instance

/-- The final state in a finite history through time `n`. -/
def terminalHistory (n : ℕ) (history : (i : Finset.Iic n) → α) : α :=
  history ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- Reading the final state of a finite history is measurable. -/
theorem measurable_terminalHistory (n : ℕ) : Measurable (terminalHistory (α := α) n) :=
  measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)

/-- The state-at-time-`n` kernel obtained from the finite Ionescu--Tulcea
history, conditional on a point at time zero. -/
noncomputable def finiteStateKernel
    (transition : ProbabilityTheory.Kernel α α) (n : ℕ) :
    ProbabilityTheory.Kernel α α :=
  ((ProbabilityTheory.Kernel.partialTraj (X := fun _ => α)
      (homogeneousNext transition) 0 n).map
    (terminalHistory (α := α) n)).comap
      (initialHistory (α := α)) measurable_initialHistory

@[simp]
theorem finiteStateKernel_zero
    (transition : ProbabilityTheory.Kernel α α) :
    finiteStateKernel transition 0 = ProbabilityTheory.Kernel.id := by
  rw [finiteStateKernel, ProbabilityTheory.Kernel.partialTraj_zero]
  ext x s hs
  rw [ProbabilityTheory.Kernel.comap_apply,
    ProbabilityTheory.Kernel.map_apply _ (measurable_terminalHistory 0),
    ProbabilityTheory.Kernel.deterministic_apply,
    Measure.map_dirac' (measurable_terminalHistory 0),
    ProbabilityTheory.Kernel.id_apply]
  rfl

/-- Finite path marginals obey the ordinary homogeneous Markov recurrence. -/
theorem finiteStateKernel_succ
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition]
    (n : ℕ) :
    finiteStateKernel transition (n + 1) =
      transition ∘ₖ finiteStateKernel transition n := by
  rw [finiteStateKernel, ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
    (Nat.zero_le n), ProbabilityTheory.Kernel.map_comp]
  change
    (((ProbabilityTheory.Kernel.partialTraj (X := fun _ => α)
      (homogeneousNext transition) n
      (n + 1)).map (fun x => x ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) ∘ₖ
      ProbabilityTheory.Kernel.partialTraj (X := fun _ => α)
        (homogeneousNext transition) 0 n).comap
        (initialHistory (α := α)) measurable_initialHistory) = _
  rw [ProbabilityTheory.Kernel.map_partialTraj_succ_self]
  ext x s hs
  simp only [ProbabilityTheory.Kernel.comap_apply,
    ProbabilityTheory.Kernel.comp_apply' _ _ _ hs]
  rw [finiteStateKernel, ProbabilityTheory.Kernel.comap_apply,
    ProbabilityTheory.Kernel.map_apply _ (measurable_terminalHistory n),
    MeasureTheory.lintegral_map
      (ProbabilityTheory.Kernel.measurable_coe transition hs)
      (measurable_terminalHistory n)]
  simp only [homogeneousNext, ProbabilityTheory.Kernel.comap_apply,
    terminalHistory]

/-- Every finite Ionescu--Tulcea state marginal is the corresponding power of
the homogeneous transition kernel. -/
theorem finiteStateKernel_eq_pow
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition]
    (n : ℕ) :
    finiteStateKernel transition n = transition ^ n := by
  induction n with
  | zero =>
      rw [finiteStateKernel_zero, pow_zero]
      rfl
  | succ n ih =>
      rw [finiteStateKernel_succ, ih]
      change transition * transition ^ n = transition ^ (n + 1)
      exact (pow_succ' transition n).symm

/-- Every coordinate of the infinite homogeneous path kernel has exactly the
corresponding iterated transition kernel as its law. -/
theorem pathKernel_map_atTime
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition]
    (n : ℕ) :
    (pathKernel transition).map (fun path => path n) = transition ^ n := by
  letI : ∀ k, IsMarkovKernel (homogeneousNext transition k) := fun k =>
    homogeneousNext.instIsMarkovKernel transition k
  rw [pathKernel]
  rw [← ProbabilityTheory.Kernel.comap_map_comm _ measurable_initialHistory
    (measurable_pi_apply n)]
  have heval : (fun path : ℕ → α => path n) =
      terminalHistory n ∘ Preorder.frestrictLe n := rfl
  rw [heval, ProbabilityTheory.Kernel.map_comp_right _
    (Preorder.measurable_frestrictLe n) (measurable_terminalHistory n),
    ProbabilityTheory.Kernel.traj_map_frestrictLe]
  exact finiteStateKernel_eq_pow transition n

/-- The homogeneous history adapter is evaluation at the terminal history
coordinate. -/
theorem homogeneousNext_eq_terminal
    (transition : ProbabilityTheory.Kernel α α) (n : ℕ) :
    homogeneousNext transition n =
      transition.comap (terminalHistory n) (measurable_terminalHistory n) := by
  rfl

/-- As a first coordinate check on the path construction, the state at time
one has exactly the original one-step transition kernel. -/
theorem pathKernel_map_one
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    (pathKernel transition).map (fun path => path 1) = transition := by
  simpa using pathKernel_map_atTime transition 1

/-- The infinite path law obtained by first sampling the initial state and
then following the homogeneous path kernel. -/
noncomputable def pathLaw
    (initial : Measure α)
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    Measure (ℕ → α) :=
  pathKernel transition ∘ₘ initial

/-- The local homogeneous path-law wrapper is exactly mathlib's
`trajMeasure` for the homogeneous history adapter. -/
theorem pathLaw_eq_trajMeasure
    (initial : Measure α)
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    pathLaw initial transition =
      ProbabilityTheory.Kernel.trajMeasure initial (homogeneousNext transition) := by
  rw [pathLaw, pathKernel, ProbabilityTheory.Kernel.trajMeasure]
  ext s hs
  rw [Measure.bind_apply hs (ProbabilityTheory.Kernel.aemeasurable _),
    Measure.bind_apply hs (ProbabilityTheory.Kernel.aemeasurable _)]
  simp_rw [ProbabilityTheory.Kernel.comap_apply']
  rw [MeasureTheory.lintegral_map]
  · congr 1
  · exact ProbabilityTheory.Kernel.measurable_coe _ hs
  · fun_prop

/-- If a Markov kernel preserves a measurable set with probability one, then
almost every homogeneous path cannot leave that set in one step. -/
theorem pathLaw_ae_mem_succ_of_mem
    (initial : Measure α) [IsProbabilityMeasure initial]
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition]
    (S : Set α) (hS : MeasurableSet S)
    (hstay : ∀ x ∈ S, transition x S = 1) (n : ℕ) :
    ∀ᵐ path ∂pathLaw initial transition,
      path n ∈ S → path (n + 1) ∈ S := by
  let historyLaw : Measure ((i : Finset.Iic n) → α) :=
    (pathLaw initial transition).map (Preorder.frestrictLe n)
  let next := homogeneousNext transition n
  have hprop : MeasurableSet
      {z : (((i : Finset.Iic n) → α) × α) |
        terminalHistory n z.1 ∈ S → z.2 ∈ S} := by
    exact (hS.preimage ((measurable_terminalHistory n).comp measurable_fst)).imp
      (hS.preimage measurable_snd)
  have hpair : ∀ᵐ z ∂historyLaw ⊗ₘ next,
      terminalHistory n z.1 ∈ S → z.2 ∈ S := by
    apply Measure.ae_compProd_of_ae_ae hprop
    filter_upwards [] with history
    by_cases hx : terminalHistory n history ∈ S
    · have hmass : next history S = 1 := by
        exact hstay (terminalHistory n history) hx
      have hae : ∀ᵐ y ∂next history, y ∈ S := by
        apply (ae_mem_iff_measure_eq hS.nullMeasurableSet).2
        rw [measure_univ, hmass]
      exact hae.mono fun y hy _ => hy
    · exact Filter.Eventually.of_forall fun _y h => (hx h).elim
  have htraj := ProbabilityTheory.Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ => α) (μ₀ := initial) (κ := homogeneousNext transition) (a := n)
  rw [← pathLaw_eq_trajMeasure initial transition] at htraj
  change (historyLaw ⊗ₘ next) = _ at htraj
  rw [htraj] at hpair
  exact ae_of_ae_map (by fun_prop) hpair

instance pathLaw.instIsProbabilityMeasure
    (initial : Measure α) [IsProbabilityMeasure initial]
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    IsProbabilityMeasure (pathLaw initial transition) := by
  unfold pathLaw
  infer_instance

/-- The time-one coordinate of the path law is the ordinary one-step evolved
law. -/
theorem pathLaw_map_one
    (initial : Measure α)
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition] :
    (pathLaw initial transition).map (fun path => path 1) = transition ∘ₘ initial := by
  rw [pathLaw, Measure.map_comp _ _ (measurable_pi_apply 1), pathKernel_map_one]

/-- Every coordinate of the infinite path law agrees with the ordinary
finite-time law obtained by iterating the transition kernel. -/
theorem pathLaw_map_atTime
    (initial : Measure α)
    (transition : ProbabilityTheory.Kernel α α) [IsMarkovKernel transition]
    (n : ℕ) :
    (pathLaw initial transition).map (fun path => path n) =
      lawAtTime initial transition n := by
  rw [pathLaw, Measure.map_comp _ _ (measurable_pi_apply n),
    pathKernel_map_atTime, lawAtTime]

end Kernel
end McmcLean
