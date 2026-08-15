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

namespace RandomAdaptation

open MarkovKernel Nonhomogeneous

variable {State Parameter : Type*} [Fintype State] [Fintype Parameter]

/-- Finite random adaptive process. The current parameter selects a state
kernel; after the next state is sampled, a conditional law selects the next
parameter. The parameter may encode any fixed finite adaptation memory. -/
structure Process (State Parameter : Type*) [Fintype State] [Fintype Parameter] where
  kernel : Parameter → MarkovKernel State
  update : State → Parameter → State → Distribution Parameter

/-- Homogeneous augmented-state kernel associated with a random adaptive
process. -/
def Process.augmentedKernel (process : Process State Parameter) :
    MarkovKernel (State × Parameter) where
  prob current next := (process.kernel current.2).prob current.1 next.1 *
    (process.update current.1 current.2 next.1).mass next.2
  nonneg current next := mul_nonneg
    ((process.kernel current.2).nonneg current.1 next.1)
    ((process.update current.1 current.2 next.1).nonneg next.2)
  sum_prob current := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,
      (process.update current.1 current.2 _).sum_mass, mul_one]
    exact (process.kernel current.2).sum_prob current.1

/-- Probability, under the current augmented law and one adaptive transition,
that the next selected state kernel differs from the current one by more than
`ε` in at least one row. -/
noncomputable def changeProbability [DecidableEq State]
    (process : Process State Parameter) (law : Distribution (State × Parameter))
    (ε : ℝ) : ℝ :=
  ∑ current, law.mass current *
    ∑ next, process.augmentedKernel.prob current next *
      (if ∃ x, ε < rowTotalVariation
        (process.kernel next.2) (process.kernel current.2) x then 1 else 0)

theorem changeProbability_nonneg [DecidableEq State]
    (process : Process State Parameter) (law : Distribution (State × Parameter))
    (ε : ℝ) : 0 ≤ changeProbability process law ε := by
  unfold changeProbability
  apply Finset.sum_nonneg
  intro current _
  apply mul_nonneg (law.nonneg current)
  apply Finset.sum_nonneg
  intro next _
  apply mul_nonneg (process.augmentedKernel.nonneg current next)
  split_ifs <;> norm_num

theorem changeProbability_le_one [DecidableEq State]
    (process : Process State Parameter) (law : Distribution (State × Parameter))
    (ε : ℝ) : changeProbability process law ε ≤ 1 := by
  unfold changeProbability
  calc
    ∑ current, law.mass current *
        ∑ next, process.augmentedKernel.prob current next *
          (if ∃ x, ε < rowTotalVariation
            (process.kernel next.2) (process.kernel current.2) x then 1 else 0) ≤
      ∑ current, law.mass current * 1 := by
        apply Finset.sum_le_sum
        intro current _
        apply mul_le_mul_of_nonneg_left _ (law.nonneg current)
        calc
          ∑ next, process.augmentedKernel.prob current next *
              (if ∃ x, ε < rowTotalVariation
                (process.kernel next.2) (process.kernel current.2) x then 1 else 0) ≤
            ∑ next, process.augmentedKernel.prob current next * 1 := by
              apply Finset.sum_le_sum
              intro next _
              apply mul_le_mul_of_nonneg_left _
                (process.augmentedKernel.nonneg current next)
              split_ifs <;> norm_num
          _ = 1 := by simp [process.augmentedKernel.sum_prob current]
    _ = 1 := by simpa using law.sum_mass

/-- Finite Markovian form of Roberts--Rosenthal Diminishing Adaptation:
successive selected kernels become close in probability under the actual
augmented process law. -/
def DiminishingAdaptation [DecidableEq State]
    (process : Process State Parameter) (initial : Distribution (State × Parameter)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n, N ≤ n →
    changeProbability process
      (Nonhomogeneous.lawAt initial (fun _ => process.augmentedKernel) n) ε ≤ δ

/-- If every parameter selects the same frozen state kernel, arbitrary random
parameter updates satisfy Diminishing Adaptation. This still gives no
containment or convergence theorem. -/
theorem diminishingAdaptation_of_kernel_const [DecidableEq State]
    (process : Process State Parameter) (kernel : MarkovKernel State)
    (hkernel : ∀ parameter, process.kernel parameter = kernel)
    (initial : Distribution (State × Parameter)) :
    DiminishingAdaptation process initial := by
  intro ε hε δ hδ
  refine ⟨0, fun n _ => ?_⟩
  have hzero : changeProbability process
      (Nonhomogeneous.lawAt initial (fun _ => process.augmentedKernel) n) ε = 0 := by
    unfold changeProbability
    apply Finset.sum_eq_zero
    intro current _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro next _
    apply mul_eq_zero_of_right
    have hnot : ¬ ∃ x, ε < rowTotalVariation
        (process.kernel next.2) (process.kernel current.2) x := by
      rintro ⟨x, hx⟩
      rw [hkernel next.2, hkernel current.2, rowTotalVariation_self] at hx
      linarith
    simp [hnot]
  rw [hzero]
  exact le_of_lt hδ

end RandomAdaptation

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
