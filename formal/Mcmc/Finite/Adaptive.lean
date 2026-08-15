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

/-- Point mass at a finite state. -/
def pointMass [DecidableEq State] (x : State) : Distribution State where
  mass y := if y = x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  sum_mass := by simp

/-- Homogeneous iteration of one finite kernel. -/
def iterateLaw (initial : Distribution State) (kernel : MarkovKernel State) :
    ℕ → Distribution State
  | 0 => initial
  | n + 1 => (iterateLaw initial kernel n).evolve kernel

/-- Total-variation distance between finite distributions. -/
noncomputable def distributionTotalVariation (first second : Distribution State) : ℝ :=
  (∑ x, |first.mass x - second.mass x|) / 2

theorem distributionTotalVariation_nonneg (first second : Distribution State) :
    0 ≤ distributionTotalVariation first second := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _) (by norm_num)

theorem distributionTotalVariation_symm (first second : Distribution State) :
    distributionTotalVariation first second = distributionTotalVariation second first := by
  unfold distributionTotalVariation
  apply congrArg (fun z : ℝ => z / 2)
  apply Finset.sum_congr rfl
  intro x _
  rw [abs_sub_comm]

@[simp] theorem distributionTotalVariation_self (law : Distribution State) :
    distributionTotalVariation law law = 0 := by
  simp [distributionTotalVariation]

theorem distributionTotalVariation_triangle (first second third : Distribution State) :
    distributionTotalVariation first third ≤
      distributionTotalVariation first second +
        distributionTotalVariation second third := by
  unfold distributionTotalVariation
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  calc
    |first.mass x - third.mass x| =
        |(first.mass x - second.mass x) + (second.mass x - third.mass x)| := by
      congr 1
      ring
    _ ≤ |first.mass x - second.mass x| + |second.mass x - third.mass x| :=
      abs_add_le _ _

theorem distributionTotalVariation_le_one (first second : Distribution State) :
    distributionTotalVariation first second ≤ 1 := by
  unfold distributionTotalVariation
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  calc
    ∑ x, |first.mass x - second.mass x| ≤
        ∑ x, (first.mass x + second.mass x) := by
      apply Finset.sum_le_sum
      intro x _
      exact abs_sub_le_iff.mpr ⟨by
        linarith [first.nonneg x, second.nonneg x], by
        linarith [first.nonneg x, second.nonneg x]⟩
    _ = 2 := by
      rw [Finset.sum_add_distrib, first.sum_mass, second.sum_mass]
      norm_num
    _ = 1 * 2 := by norm_num

/-- Applying a common Markov kernel contracts finite total variation. -/
theorem distributionTotalVariation_evolve_le (first second : Distribution State)
    (kernel : MarkovKernel State) :
    distributionTotalVariation (first.evolve kernel) (second.evolve kernel) ≤
      distributionTotalVariation first second := by
  unfold distributionTotalVariation
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    ∑ y, |(first.evolve kernel).mass y - (second.evolve kernel).mass y| ≤
        ∑ y, ∑ x, |first.mass x - second.mass x| * kernel.prob x y := by
      apply Finset.sum_le_sum
      intro y _
      rw [Distribution.evolve_mass, Distribution.evolve_mass,
        ← Finset.sum_sub_distrib]
      calc
        |∑ x, (first.mass x * kernel.prob x y -
          second.mass x * kernel.prob x y)| =
            |∑ x, (first.mass x - second.mass x) * kernel.prob x y| := by
              apply congrArg abs
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ ≤ ∑ x, |(first.mass x - second.mass x) * kernel.prob x y| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x, |first.mass x - second.mass x| * kernel.prob x y := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg (kernel.nonneg x y)]
    _ = ∑ x, ∑ y, |first.mass x - second.mass x| * kernel.prob x y := by
      rw [Finset.sum_comm]
    _ = ∑ x, |first.mass x - second.mass x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum, kernel.sum_prob, mul_one]

/-- Changing the kernel for a fixed input law is bounded by the law-weighted
row total variation. -/
theorem distributionTotalVariation_evolve_kernel_le (law : Distribution State)
    (first second : MarkovKernel State) :
    distributionTotalVariation (law.evolve first) (law.evolve second) ≤
      ∑ x, law.mass x * rowTotalVariation first second x := by
  unfold distributionTotalVariation rowTotalVariation
  rw [show (∑ x, law.mass x * ((∑ y, |first.prob x y - second.prob x y|) / 2)) =
      (∑ x, law.mass x * ∑ y, |first.prob x y - second.prob x y|) / 2 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    ∑ y, |(law.evolve first).mass y - (law.evolve second).mass y| ≤
        ∑ y, ∑ x, law.mass x * |first.prob x y - second.prob x y| := by
      apply Finset.sum_le_sum
      intro y _
      rw [Distribution.evolve_mass, Distribution.evolve_mass,
        ← Finset.sum_sub_distrib]
      calc
        |∑ x, (law.mass x * first.prob x y - law.mass x * second.prob x y)| =
            |∑ x, law.mass x * (first.prob x y - second.prob x y)| := by
              apply congrArg abs
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ ≤ ∑ x, |law.mass x * (first.prob x y - second.prob x y)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x, law.mass x * |first.prob x y - second.prob x y| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_of_nonneg (law.nonneg x)]
    _ = ∑ x, law.mass x * ∑ y, |first.prob x y - second.prob x y| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]

/-- Uniform row-TV control gives the corresponding one-step perturbation
bound for every input law. -/
theorem distributionTotalVariation_evolve_kernel_le_of_distance
    (law : Distribution State) (first second : MarkovKernel State) (ε : ℝ)
    (hdistance : KernelDistanceLE first second ε) :
    distributionTotalVariation (law.evolve first) (law.evolve second) ≤ ε := by
  calc
    distributionTotalVariation (law.evolve first) (law.evolve second) ≤
        ∑ x, law.mass x * rowTotalVariation first second x :=
      distributionTotalVariation_evolve_kernel_le law first second
    _ ≤ ∑ x, law.mass x * ε := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hdistance x) (law.nonneg x)
    _ = ε := by rw [← Finset.sum_mul, law.sum_mass, one_mul]

/-- Finite-window perturbation estimate: laws driven by two predetermined
kernel schedules differ by at most the sum of their uniform row-TV changes. -/
theorem lawAt_schedule_comparison (initial : Distribution State)
    (first second : ℕ → MarkovKernel State) (ε : ℕ → ℝ)
    (hdistance : ∀ k, KernelDistanceLE (first k) (second k) (ε k)) (n : ℕ) :
    distributionTotalVariation (lawAt initial first n) (lawAt initial second n) ≤
      ∑ k ∈ Finset.range n, ε k := by
  induction n with
  | zero => simp [lawAt]
  | succ n ih =>
      rw [lawAt, lawAt]
      calc
        distributionTotalVariation
            ((lawAt initial first n).evolve (first n))
            ((lawAt initial second n).evolve (second n)) ≤
          distributionTotalVariation
              ((lawAt initial first n).evolve (first n))
              ((lawAt initial second n).evolve (first n)) +
            distributionTotalVariation
              ((lawAt initial second n).evolve (first n))
              ((lawAt initial second n).evolve (second n)) :=
          distributionTotalVariation_triangle _ _ _
        _ ≤ distributionTotalVariation (lawAt initial first n)
              (lawAt initial second n) + ε n :=
          add_le_add
            (distributionTotalVariation_evolve_le _ _ _)
            (distributionTotalVariation_evolve_kernel_le_of_distance
              (lawAt initial second n) (first n) (second n) (ε n) (hdistance n))
        _ ≤ (∑ k ∈ Finset.range n, ε k) + ε n := add_le_add ih le_rfl
        _ = ∑ k ∈ Finset.range (n + 1), ε k := by
          rw [Finset.sum_range_succ]

/-- A kernel is within `ε` of its target by a given horizon, uniformly over
finite starting states. -/
def MixesWithin [DecidableEq State] (kernel : MarkovKernel State)
    (target : Distribution State) (steps : ℕ) (ε : ℝ) : Prop :=
  ∀ x, distributionTotalVariation (iterateLaw (pointMass x) kernel steps) target ≤ ε

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

/-- Probability that the kernel currently selected by the adaptive process has
not reached `ε` total-variation accuracy by `steps`, from the current state. -/
noncomputable def mixingFailureProbability [DecidableEq State]
    (process : Process State Parameter) (target : Distribution State)
    (law : Distribution (State × Parameter)) (steps : ℕ) (ε : ℝ) : ℝ :=
  ∑ current, law.mass current *
    (if ε < distributionTotalVariation
      (iterateLaw (pointMass current.1) (process.kernel current.2) steps) target
      then 1 else 0)

theorem mixingFailureProbability_nonneg [DecidableEq State]
    (process : Process State Parameter) (target : Distribution State)
    (law : Distribution (State × Parameter)) (steps : ℕ) (ε : ℝ) :
    0 ≤ mixingFailureProbability process target law steps ε := by
  unfold mixingFailureProbability
  apply Finset.sum_nonneg
  intro current _
  apply mul_nonneg (law.nonneg current)
  split_ifs <;> norm_num

theorem mixingFailureProbability_le_one [DecidableEq State]
    (process : Process State Parameter) (target : Distribution State)
    (law : Distribution (State × Parameter)) (steps : ℕ) (ε : ℝ) :
    mixingFailureProbability process target law steps ε ≤ 1 := by
  unfold mixingFailureProbability
  calc
    ∑ current, law.mass current *
        (if ε < distributionTotalVariation
          (iterateLaw (pointMass current.1) (process.kernel current.2) steps) target
          then 1 else 0) ≤ ∑ current, law.mass current * 1 := by
      apply Finset.sum_le_sum
      intro current _
      apply mul_le_mul_of_nonneg_left _ (law.nonneg current)
      split_ifs <;> norm_num
    _ = 1 := by simpa using law.sum_mass

/-- Finite Containment: along the adaptive process, the horizon needed for the
currently selected kernel to reach any fixed TV tolerance is bounded in
probability. -/
def Containment [DecidableEq State] (process : Process State Parameter)
    (target : Distribution State) (initial : Distribution (State × Parameter)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ steps : ℕ, ∀ n,
    mixingFailureProbability process target
      (Nonhomogeneous.lawAt initial (fun _ => process.augmentedKernel) n)
      steps ε ≤ δ

/-- Simultaneous uniform mixing of every parameter kernel implies Containment
for every initial augmented law. -/
theorem containment_of_simultaneous_uniform_mixing [DecidableEq State]
    (process : Process State Parameter) (target : Distribution State)
    (hmix : ∀ ε : ℝ, 0 < ε → ∃ steps : ℕ, ∀ parameter,
      MixesWithin (process.kernel parameter) target steps ε)
    (initial : Distribution (State × Parameter)) :
    Containment process target initial := by
  intro ε hε δ hδ
  obtain ⟨steps, hsteps⟩ := hmix ε hε
  refine ⟨steps, fun n => ?_⟩
  have hzero : mixingFailureProbability process target
      (Nonhomogeneous.lawAt initial (fun _ => process.augmentedKernel) n)
      steps ε = 0 := by
    unfold mixingFailureProbability
    apply Finset.sum_eq_zero
    intro current _
    apply mul_eq_zero_of_right
    have hnot : ¬ ε < distributionTotalVariation
        (iterateLaw (pointMass current.1) (process.kernel current.2) steps) target :=
      not_lt_of_ge (hsteps current.2 current.1)
    simp [hnot]
  rw [hzero]
  exact le_of_lt hδ

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
