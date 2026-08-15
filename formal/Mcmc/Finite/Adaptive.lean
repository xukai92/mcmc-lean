import Mcmc.Finite.Combinators
import Mathlib.Tactic

/-!
# A finite adaptive-kernel boundary

State-dependent selection from a family of Markov kernels is again a Markov
kernel.  The example below records an important adaptive-MCMC warning: even
when every frozen member preserves the same target, selecting the member from
the current state need not preserve that target.
-/

open scoped BigOperators

namespace Mcmc.Finite

/-- Select a transition kernel as a function of the current state. -/
def selectByState {State Parameter : Type*} [Fintype State]
    (choose : State → Parameter) (family : Parameter → MarkovKernel State) :
    MarkovKernel State where
  prob x y := (family (choose x)).prob x y
  nonneg x y := (family (choose x)).nonneg x y
  sum_prob x := (family (choose x)).sum_prob x

namespace Nonhomogeneous

open MarkovKernel

variable {State : Type*} [Fintype State]

/-- Evolve a law through a predetermined finite sequence of kernels. This is
nonhomogeneous Markov evolution, not state- or history-dependent adaptation. -/
def evolveSchedule : Distribution State → List (MarkovKernel State) → Distribution State
  | law, [] => law
  | law, kernel :: kernels => evolveSchedule (law.evolve kernel) kernels

/-- The law at time `n` under a predetermined time-indexed kernel schedule. -/
def lawAt (initial : Distribution State) (schedule : ℕ → MarkovKernel State) :
    ℕ → Distribution State
  | 0 => initial
  | n + 1 => (lawAt initial schedule n).evolve (schedule n)

/-- If every kernel in a predetermined schedule preserves the same target,
starting at that target leaves the law unchanged after the whole schedule. -/
theorem evolveSchedule_eq_of_stationary (target : Distribution State)
    (kernels : List (MarkovKernel State))
    (hstationary : ∀ kernel ∈ kernels, kernel.Stationary target) :
    evolveSchedule target kernels = target := by
  induction kernels with
  | nil => rfl
  | cons kernel kernels ih =>
      rw [evolveSchedule, (hstationary kernel (by simp)).evolve_eq]
      exact ih (fun later hlater => hstationary later (by simp [hlater]))

/-- Time-indexed form: common stationarity preserves the target at every
finite time under a predetermined nonhomogeneous schedule. -/
theorem lawAt_eq_of_stationary (target : Distribution State)
    (schedule : ℕ → MarkovKernel State)
    (hstationary : ∀ n, (schedule n).Stationary target) (n : ℕ) :
    lawAt target schedule n = target := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [lawAt, ih, (hstationary n).evolve_eq]

/-- Total-variation distance between two kernel rows on a finite state space. -/
noncomputable def rowTotalVariation (first second : MarkovKernel State)
    (x : State) : ℝ :=
  (∑ y, |first.prob x y - second.prob x y|) / 2

theorem rowTotalVariation_nonneg (first second : MarkovKernel State) (x : State) :
    0 ≤ rowTotalVariation first second x := by
  exact div_nonneg (Finset.sum_nonneg fun y _ => abs_nonneg _) (by norm_num)

theorem rowTotalVariation_symm (first second : MarkovKernel State) (x : State) :
    rowTotalVariation first second x = rowTotalVariation second first x := by
  unfold rowTotalVariation
  apply congrArg (fun z : ℝ => z / 2)
  apply Finset.sum_congr rfl
  intro y _
  rw [abs_sub_comm]

theorem rowTotalVariation_le_one (first second : MarkovKernel State) (x : State) :
    rowTotalVariation first second x ≤ 1 := by
  unfold rowTotalVariation
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    ∑ y, |first.prob x y - second.prob x y| ≤
        ∑ y, (first.prob x y + second.prob x y) := by
      apply Finset.sum_le_sum
      intro y _
      exact abs_sub_le_iff.mpr ⟨by
        linarith [first.nonneg x y, second.nonneg x y], by
        linarith [first.nonneg x y, second.nonneg x y]⟩
    _ = 2 := by
      rw [Finset.sum_add_distrib, first.sum_prob, second.sum_prob]
      norm_num
    _ = 1 * 2 := by norm_num

@[simp] theorem rowTotalVariation_self (kernel : MarkovKernel State) (x : State) :
    rowTotalVariation kernel kernel x = 0 := by
  simp [rowTotalVariation]

/-- Uniform finite-state row-TV bound between two kernels. -/
def KernelDistanceLE (first second : MarkovKernel State) (ε : ℝ) : Prop :=
  ∀ x, rowTotalVariation first second x ≤ ε

theorem kernelDistanceLE_symm {first second : MarkovKernel State} {ε : ℝ}
    (h : KernelDistanceLE first second ε) : KernelDistanceLE second first ε := by
  intro x
  rw [rowTotalVariation_symm]
  exact h x

/-- Deterministic diminishing adaptation for a predetermined kernel schedule.
Roberts--Rosenthal diminishing adaptation for a random adaptive process instead
requires convergence in probability; this definition is its deterministic
finite-state precursor. -/
def DiminishingSchedule (schedule : ℕ → MarkovKernel State) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
    KernelDistanceLE (schedule (n + 1)) (schedule n) ε

/-- A frozen kernel schedule is diminishing. This does not by itself prove
ergodicity or convergence from arbitrary initial laws. -/
theorem diminishingSchedule_const (kernel : MarkovKernel State) :
    DiminishingSchedule (fun _ => kernel) := by
  intro ε hε
  refine ⟨0, fun n _ x => ?_⟩
  simpa using le_of_lt hε

end Nonhomogeneous

namespace AdaptiveCounterexample

/-- The uniform distribution on two states. -/
noncomputable def uniformBool : MarkovKernel.Distribution Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  sum_mass := by norm_num

/-- A frozen kernel that leaves its input unchanged. -/
def stay : MarkovKernel Bool := MarkovKernel.identity

/-- A frozen kernel that flips its input. -/
def flip : MarkovKernel Bool where
  prob x y := if y = !x then 1 else 0
  nonneg x y := by split_ifs <;> norm_num
  sum_prob x := by cases x <;> simp

theorem stay_stationary : stay.Stationary uniformBool := by
  exact MarkovKernel.identity_stationary uniformBool

theorem flip_stationary : flip.Stationary uniformBool := by
  intro y
  cases y <;> norm_num [uniformBool, flip]

/-- At `false` choose the identity kernel; at `true` choose the flip kernel. -/
def selected : MarkovKernel Bool :=
  selectByState (fun x => x) (fun useFlip => if useFlip then flip else stay)

/-- State-dependent selection can destroy a common stationary distribution.
Both rows of `selected` send all mass to `false`. -/
theorem selected_not_stationary : ¬ selected.Stationary uniformBool := by
  intro h
  have htrue := h true
  norm_num [selected, selectByState, uniformBool, stay, flip,
    MarkovKernel.identity] at htrue

end AdaptiveCounterexample
end Mcmc.Finite
