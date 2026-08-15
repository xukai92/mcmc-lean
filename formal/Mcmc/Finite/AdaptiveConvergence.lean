import Mcmc.Finite.Adaptive

/-!
# Finite adaptive-MCMC convergence

This module carries out the finite Roberts--Rosenthal comparison argument.
An anchored process remembers the parameter selected at the beginning of a
finite window.  Its adaptive and frozen transition kernels share the same
parameter-update mechanism but use, respectively, the current and anchored
state kernels.  This makes their row-TV discrepancy exactly controllable by
the accumulated kernel variation.
-/

open scoped BigOperators

namespace Mcmc.Finite.RandomAdaptation

open MarkovKernel Nonhomogeneous

variable {State Parameter : Type*} [Fintype State] [Fintype Parameter]
  [DecidableEq Parameter]

/-- Augmented state carrying the adaptive state/parameter and the parameter
frozen at the beginning of the comparison window. -/
abbrev AnchoredState (State Parameter : Type*) := (State × Parameter) × Parameter

/-- Lift an augmented law to the diagonal anchor `anchor = parameter`. -/
noncomputable def anchorInitial (law : Distribution (State × Parameter)) :
    Distribution (AnchoredState State Parameter) where
  mass current := if current.2 = current.1.2 then law.mass current.1 else 0
  nonneg current := by
    split_ifs
    · exact law.nonneg current.1
    · exact le_rfl
  sum_mass := by
    classical
    rw [Fintype.sum_prod_type]
    calc
      ∑ current : State × Parameter, ∑ anchor : Parameter,
          (if anchor = current.2 then law.mass current else 0) =
          ∑ current : State × Parameter, law.mass current := by
        apply Finset.sum_congr rfl
        intro current _
        simp
      _ = 1 := law.sum_mass

/-- The anchored version of the actual adaptive transition.  The remembered
anchor is unchanged. -/
noncomputable def anchoredAdaptiveKernel (process : Process State Parameter) :
    MarkovKernel (AnchoredState State Parameter) where
  prob current next := process.augmentedKernel.prob current.1 next.1 *
    (if next.2 = current.2 then 1 else 0)
  nonneg current next := mul_nonneg
    (process.augmentedKernel.nonneg current.1 next.1) (by split_ifs <;> norm_num)
  sum_prob current := by
    classical
    rw [Fintype.sum_prod_type]
    calc
      ∑ next : State × Parameter, ∑ anchor : Parameter,
          process.augmentedKernel.prob current.1 next *
            (if anchor = current.2 then 1 else 0) =
          ∑ next : State × Parameter, process.augmentedKernel.prob current.1 next := by
        apply Finset.sum_congr rfl
        intro next _
        simp
      _ = 1 := process.augmentedKernel.sum_prob current.1

/-- Frozen comparison transition.  It evolves the state with the anchored
kernel while retaining the actual parameter-update rule and fixed anchor. -/
noncomputable def anchoredFrozenKernel (process : Process State Parameter) :
    MarkovKernel (AnchoredState State Parameter) where
  prob current next :=
    (process.kernel current.2).prob current.1.1 next.1.1 *
      (process.update current.1.1 current.1.2 next.1.1).mass next.1.2 *
      (if next.2 = current.2 then 1 else 0)
  nonneg current next := mul_nonneg
    (mul_nonneg ((process.kernel current.2).nonneg current.1.1 next.1.1)
      ((process.update current.1.1 current.1.2 next.1.1).nonneg next.1.2))
    (by split_ifs <;> norm_num)
  sum_prob current := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ next : State × Parameter, ∑ anchor : Parameter,
          (process.kernel current.2).prob current.1.1 next.1 *
            (process.update current.1.1 current.1.2 next.1).mass next.2 *
            (if anchor = current.2 then 1 else 0) =
          ∑ next : State × Parameter,
            (process.kernel current.2).prob current.1.1 next.1 *
              (process.update current.1.1 current.1.2 next.1).mass next.2 := by
        apply Finset.sum_congr rfl
        intro next _
        simp
      _ = 1 := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum,
          (process.update current.1.1 current.1.2 _).sum_mass, mul_one]
        exact (process.kernel current.2).sum_prob current.1.1

/-- Marginalize an anchored law to its current adaptive state and parameter. -/
def currentMarginal (law : Distribution (AnchoredState State Parameter)) :
    Distribution (State × Parameter) where
  mass current := ∑ anchor, law.mass (current, anchor)
  nonneg current := Finset.sum_nonneg fun anchor _ => law.nonneg (current, anchor)
  sum_mass := by
    simpa only [Fintype.sum_prod_type] using law.sum_mass

/-- State marginal of an anchored law. -/
def anchoredStateMarginal (law : Distribution (AnchoredState State Parameter)) :
    Distribution State where
  mass x := ∑ parameter, ∑ anchor, law.mass ((x, parameter), anchor)
  nonneg x := Finset.sum_nonneg fun parameter _ =>
    Finset.sum_nonneg fun anchor _ => law.nonneg ((x, parameter), anchor)
  sum_mass := by
    simpa only [Fintype.sum_prod_type] using law.sum_mass

/-- Marginal retaining the physical state and frozen anchor while forgetting
the currently adapted parameter. -/
def anchorMarginal (law : Distribution (AnchoredState State Parameter)) :
    Distribution (State × Parameter) where
  mass anchored := ∑ parameter, law.mass ((anchored.1, parameter), anchored.2)
  nonneg anchored := Finset.sum_nonneg fun parameter _ =>
    law.nonneg ((anchored.1, parameter), anchored.2)
  sum_mass := by
    calc
      ∑ anchored : State × Parameter, ∑ parameter,
          law.mass ((anchored.1, parameter), anchored.2) =
          ∑ x : State, ∑ parameter, ∑ anchor,
            law.mass ((x, parameter), anchor) := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = 1 := by
        simpa only [Fintype.sum_prod_type] using law.sum_mass

/-- Homogeneous state/anchor kernel which keeps the selected anchor fixed and
uses its state kernel. -/
noncomputable def frozenParameterKernel (process : Process State Parameter) :
    MarkovKernel (State × Parameter) where
  prob current next := (process.kernel current.2).prob current.1 next.1 *
    (if next.2 = current.2 then 1 else 0)
  nonneg current next := mul_nonneg
    ((process.kernel current.2).nonneg current.1 next.1)
    (by split_ifs <;> norm_num)
  sum_prob current := by
    rw [Fintype.sum_prod_type]
    calc
      ∑ nextState, ∑ nextParameter,
          (process.kernel current.2).prob current.1 nextState *
            (if nextParameter = current.2 then 1 else 0) =
          ∑ nextState, (process.kernel current.2).prob current.1 nextState := by
        apply Finset.sum_congr rfl
        intro nextState _
        simp
      _ = 1 := (process.kernel current.2).sum_prob current.1

@[simp] theorem currentMarginal_anchorInitial
    (law : Distribution (State × Parameter)) :
    currentMarginal (anchorInitial law) = law := by
  classical
  apply Distribution.ext
  funext current
  simp [currentMarginal, anchorInitial]

@[simp] theorem anchoredStateMarginal_anchorInitial
    (law : Distribution (State × Parameter)) :
    anchoredStateMarginal (anchorInitial law) = stateMarginal law := by
  classical
  apply Distribution.ext
  funext x
  simp [anchoredStateMarginal, anchorInitial, stateMarginal]

@[simp] theorem anchorMarginal_anchorInitial
    (law : Distribution (State × Parameter)) :
    anchorMarginal (anchorInitial law) = law := by
  classical
  apply Distribution.ext
  funext current
  simp [anchorMarginal, anchorInitial]

omit [DecidableEq Parameter] in
theorem anchoredStateMarginal_eq_stateMarginal_currentMarginal
    (law : Distribution (AnchoredState State Parameter)) :
    anchoredStateMarginal law = stateMarginal (currentMarginal law) := by
  apply Distribution.ext
  funext x
  simp only [anchoredStateMarginal, stateMarginal, currentMarginal]

/-- The current-coordinate marginal of the anchored adaptive transition is
exactly the original augmented adaptive transition. -/
theorem currentMarginal_evolve_anchoredAdaptiveKernel
    (process : Process State Parameter)
    (law : Distribution (AnchoredState State Parameter)) :
    currentMarginal (law.evolve (anchoredAdaptiveKernel process)) =
      (currentMarginal law).evolve process.augmentedKernel := by
  classical
  apply Distribution.ext
  funext next
  change (∑ nextAnchor,
      ∑ current : AnchoredState State Parameter,
        law.mass current *
          (process.augmentedKernel.prob current.1 next *
            (if nextAnchor = current.2 then 1 else 0))) =
    ∑ current : State × Parameter,
      (∑ anchor, law.mass (current, anchor)) *
        process.augmentedKernel.prob current next
  rw [Finset.sum_comm]
  calc
    ∑ current : AnchoredState State Parameter, ∑ nextAnchor,
        law.mass current *
          (process.augmentedKernel.prob current.1 next *
            (if nextAnchor = current.2 then 1 else 0)) =
        ∑ current : AnchoredState State Parameter,
          law.mass current * process.augmentedKernel.prob current.1 next := by
      apply Finset.sum_congr rfl
      intro current _
      rw [show (∑ nextAnchor,
          law.mass current *
            (process.augmentedKernel.prob current.1 next *
              (if nextAnchor = current.2 then 1 else 0))) =
          law.mass current * process.augmentedKernel.prob current.1 next by
        simp]
    _ = ∑ current : State × Parameter,
        (∑ anchor, law.mass (current, anchor)) *
          process.augmentedKernel.prob current next := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro current _
      rw [Finset.sum_mul]

/-- Iterating the anchored adaptive kernel and then forgetting the anchor is
the same as iterating the original augmented process. -/
theorem currentMarginal_iterate_anchoredAdaptiveKernel
    (process : Process State Parameter)
    (law : Distribution (State × Parameter)) (steps : ℕ) :
    currentMarginal
        (iterateLaw (anchorInitial law) (anchoredAdaptiveKernel process) steps) =
      iterateLaw law process.augmentedKernel steps := by
  induction steps with
  | zero => simp [iterateLaw]
  | succ steps ih =>
      rw [iterateLaw, iterateLaw,
        currentMarginal_evolve_anchoredAdaptiveKernel, ih]

/-- The state/anchor marginal of one frozen anchored transition evolves with
the homogeneous frozen-parameter kernel. -/
theorem anchorMarginal_evolve_anchoredFrozenKernel
    (process : Process State Parameter)
    (law : Distribution (AnchoredState State Parameter)) :
    anchorMarginal (law.evolve (anchoredFrozenKernel process)) =
      (anchorMarginal law).evolve (frozenParameterKernel process) := by
  classical
  apply Distribution.ext
  funext next
  change (∑ nextParameter,
      ∑ current : AnchoredState State Parameter,
        law.mass current *
          ((process.kernel current.2).prob current.1.1 next.1 *
            (process.update current.1.1 current.1.2 next.1).mass nextParameter *
            (if next.2 = current.2 then 1 else 0))) =
    ∑ current : State × Parameter,
      (∑ parameter, law.mass ((current.1, parameter), current.2)) *
        ((process.kernel current.2).prob current.1 next.1 *
          (if next.2 = current.2 then 1 else 0))
  rw [Finset.sum_comm]
  calc
    ∑ current : AnchoredState State Parameter, ∑ nextParameter,
        law.mass current *
          ((process.kernel current.2).prob current.1.1 next.1 *
            (process.update current.1.1 current.1.2 next.1).mass nextParameter *
            (if next.2 = current.2 then 1 else 0)) =
        ∑ current : AnchoredState State Parameter,
          law.mass current *
            ((process.kernel current.2).prob current.1.1 next.1 *
              (if next.2 = current.2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro current _
      rw [show (∑ nextParameter,
          law.mass current *
            ((process.kernel current.2).prob current.1.1 next.1 *
              (process.update current.1.1 current.1.2 next.1).mass nextParameter *
              (if next.2 = current.2 then 1 else 0))) =
          law.mass current *
            ((process.kernel current.2).prob current.1.1 next.1 *
              (if next.2 = current.2 then 1 else 0)) by
        rw [show (∑ nextParameter,
            law.mass current *
              ((process.kernel current.2).prob current.1.1 next.1 *
                (process.update current.1.1 current.1.2 next.1).mass nextParameter *
                (if next.2 = current.2 then 1 else 0))) =
            (law.mass current *
              ((process.kernel current.2).prob current.1.1 next.1 *
                (if next.2 = current.2 then 1 else 0))) *
              ∑ nextParameter,
                (process.update current.1.1 current.1.2 next.1).mass nextParameter by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro nextParameter _
          ring,
          (process.update current.1.1 current.1.2 next.1).sum_mass, mul_one]]
    _ = ∑ current : State × Parameter,
        (∑ parameter, law.mass ((current.1, parameter), current.2)) *
          ((process.kernel current.2).prob current.1 next.1 *
            (if next.2 = current.2 then 1 else 0)) := by
      rw [show (∑ current : AnchoredState State Parameter,
          law.mass current *
            ((process.kernel current.2).prob current.1.1 next.1 *
              (if next.2 = current.2 then 1 else 0))) =
          ∑ anchored : State × Parameter, ∑ parameter,
            law.mass ((anchored.1, parameter), anchored.2) *
              ((process.kernel anchored.2).prob anchored.1 next.1 *
                (if next.2 = anchored.2 then 1 else 0)) by
        simp only [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]]
      apply Finset.sum_congr rfl
      intro current _
      rw [Finset.sum_mul]

theorem anchorMarginal_iterate_anchoredFrozenKernel
    (process : Process State Parameter)
    (law : Distribution (State × Parameter)) (steps : ℕ) :
    anchorMarginal
        (iterateLaw (anchorInitial law) (anchoredFrozenKernel process) steps) =
      iterateLaw law (frozenParameterKernel process) steps := by
  induction steps with
  | zero => simp [iterateLaw]
  | succ steps ih =>
      rw [iterateLaw, iterateLaw,
        anchorMarginal_evolve_anchoredFrozenKernel, ih]

/-- Closed form for the frozen state/parameter evolution: the parameter is
fixed and each initial state evolves under the kernel it selected. -/
theorem iterate_frozenParameterKernel_mass
    [DecidableEq State]
    (process : Process State Parameter)
    (law : Distribution (State × Parameter)) (steps : ℕ)
    (y : State) (parameter : Parameter) :
    (iterateLaw law (frozenParameterKernel process) steps).mass (y, parameter) =
      ∑ x, law.mass (x, parameter) *
        (iterateLaw (pointMass x) (process.kernel parameter) steps).mass y := by
  induction steps generalizing y with
  | zero =>
      simp [iterateLaw, pointMass]
  | succ steps ih =>
      rw [iterateLaw, Distribution.evolve_mass]
      change (∑ current : State × Parameter,
        (iterateLaw law (frozenParameterKernel process) steps).mass current *
          ((process.kernel current.2).prob current.1 y *
            (if parameter = current.2 then 1 else 0))) = _
      rw [Fintype.sum_prod_type]
      simp
      simp_rw [ih]
      rw [show (∑ currentState, (∑ x, law.mass (x, parameter) *
          (iterateLaw (pointMass x) (process.kernel parameter) steps).mass currentState) *
          (process.kernel parameter).prob currentState y) =
          ∑ x, law.mass (x, parameter) *
            ∑ currentState,
              (iterateLaw (pointMass x)
                (process.kernel parameter) steps).mass currentState *
                (process.kernel parameter).prob currentState y by
        calc
          _ = ∑ currentState, ∑ x,
              law.mass (x, parameter) *
                (iterateLaw (pointMass x)
                  (process.kernel parameter) steps).mass currentState *
                (process.kernel parameter).prob currentState y := by
            apply Finset.sum_congr rfl
            intro currentState _
            rw [Finset.sum_mul]
          _ = ∑ x, ∑ currentState,
              law.mass (x, parameter) *
                (iterateLaw (pointMass x)
                  (process.kernel parameter) steps).mass currentState *
                (process.kernel parameter).prob currentState y :=
            Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro currentState _
            ring]
      simp_rw [← Distribution.evolve_mass]
      rfl

/-- The state projection of the frozen anchored chain is exactly the
previously defined frozen-window mixture. -/
theorem anchoredFrozen_stateMarginal_eq_frozenWindowLaw
    [DecidableEq State] (process : Process State Parameter)
    (law : Distribution (State × Parameter)) (steps : ℕ) :
    anchoredStateMarginal
        (iterateLaw (anchorInitial law) (anchoredFrozenKernel process) steps) =
      frozenWindowLaw process law steps := by
  have hanchor := anchorMarginal_iterate_anchoredFrozenKernel process law steps
  apply Distribution.ext
  funext y
  change (∑ parameter, ∑ anchor,
      (iterateLaw (anchorInitial law)
        (anchoredFrozenKernel process) steps).mass ((y, parameter), anchor)) =
    ∑ current, law.mass current *
      (iterateLaw (pointMass current.1)
        (process.kernel current.2) steps).mass y
  rw [Finset.sum_comm]
  change (∑ anchor, (anchorMarginal
      (iterateLaw (anchorInitial law)
        (anchoredFrozenKernel process) steps)).mass (y, anchor)) = _
  rw [hanchor]
  simp_rw [iterate_frozenParameterKernel_mass process law steps]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Expected aggregate distance between the currently selected kernel and the
kernel remembered at the start of the window. -/
noncomputable def anchoredVariation (process : Process State Parameter)
    (law : Distribution (AnchoredState State Parameter)) : ℝ :=
  ∑ current, law.mass current *
    Mcmc.Finite.Nonhomogeneous.kernelVariation
      (process.kernel current.1.2) (process.kernel current.2)

/-- The row-TV discrepancy between the adaptive and frozen anchored kernels
is the row discrepancy between their selected state kernels.  Parameter
updates and the fixed-anchor coordinate integrate out exactly. -/
theorem rowTotalVariation_anchored_kernels
    (process : Process State Parameter)
    (current : AnchoredState State Parameter) :
    rowTotalVariation (anchoredAdaptiveKernel process)
        (anchoredFrozenKernel process) current =
      rowTotalVariation (process.kernel current.1.2)
        (process.kernel current.2) current.1.1 := by
  classical
  unfold rowTotalVariation anchoredAdaptiveKernel anchoredFrozenKernel
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  congr 1
  calc
    ∑ nextState, ∑ nextParameter, ∑ nextAnchor,
        |((process.kernel current.1.2).prob current.1.1 nextState *
              (process.update current.1.1 current.1.2 nextState).mass nextParameter) *
            (if nextAnchor = current.2 then 1 else 0) -
          (process.kernel current.2).prob current.1.1 nextState *
              (process.update current.1.1 current.1.2 nextState).mass nextParameter *
            (if nextAnchor = current.2 then 1 else 0)| =
        ∑ nextState, ∑ nextParameter,
          |(process.kernel current.1.2).prob current.1.1 nextState -
              (process.kernel current.2).prob current.1.1 nextState| *
            (process.update current.1.1 current.1.2 nextState).mass nextParameter := by
      apply Finset.sum_congr rfl
      intro nextState _
      apply Finset.sum_congr rfl
      intro nextParameter _
      have hpoint (nextAnchor : Parameter) :
          |((process.kernel current.1.2).prob current.1.1 nextState *
                (process.update current.1.1 current.1.2 nextState).mass nextParameter) *
              (if nextAnchor = current.2 then 1 else 0) -
            (process.kernel current.2).prob current.1.1 nextState *
                (process.update current.1.1 current.1.2 nextState).mass nextParameter *
              (if nextAnchor = current.2 then 1 else 0)| =
          if nextAnchor = current.2 then
            |(process.kernel current.1.2).prob current.1.1 nextState -
                (process.kernel current.2).prob current.1.1 nextState| *
              (process.update current.1.1 current.1.2 nextState).mass nextParameter
          else 0 := by
        by_cases hanchor : nextAnchor = current.2
        · simp only [hanchor, if_true, mul_one]
          rw [show
            (process.kernel current.1.2).prob current.1.1 nextState *
                  (process.update current.1.1 current.1.2 nextState).mass nextParameter -
                (process.kernel current.2).prob current.1.1 nextState *
                  (process.update current.1.1 current.1.2 nextState).mass nextParameter =
              ((process.kernel current.1.2).prob current.1.1 nextState -
                (process.kernel current.2).prob current.1.1 nextState) *
                  (process.update current.1.1 current.1.2 nextState).mass nextParameter by ring,
            abs_mul,
            abs_of_nonneg
              ((process.update current.1.1 current.1.2 nextState).nonneg nextParameter)]
        · simp [hanchor]
      simp_rw [hpoint]
      simp
    _ = ∑ nextState,
        |(process.kernel current.1.2).prob current.1.1 nextState -
          (process.kernel current.2).prob current.1.1 nextState| := by
      apply Finset.sum_congr rfl
      intro nextState _
      rw [← Finset.mul_sum,
        (process.update current.1.1 current.1.2 nextState).sum_mass, mul_one]

theorem rowTotalVariation_anchored_le_kernelVariation
    (process : Process State Parameter)
    (current : AnchoredState State Parameter) :
    rowTotalVariation (anchoredAdaptiveKernel process)
        (anchoredFrozenKernel process) current ≤
      Mcmc.Finite.Nonhomogeneous.kernelVariation
        (process.kernel current.1.2) (process.kernel current.2) := by
  rw [rowTotalVariation_anchored_kernels]
  exact Mcmc.Finite.Nonhomogeneous.rowTotalVariation_le_kernelVariation _ _ _

/-- One adaptive transition increases expected distance from the window's
anchor by at most the expected variation of the newly selected kernel from
the preceding selected kernel. -/
theorem anchoredVariation_evolve_le
    (process : Process State Parameter)
    (law : Distribution (AnchoredState State Parameter)) :
    anchoredVariation process
        (law.evolve (anchoredAdaptiveKernel process)) ≤
      anchoredVariation process law +
        expectedKernelVariation process (currentMarginal law) := by
  classical
  unfold anchoredVariation expectedKernelVariation currentMarginal
  simp_rw [Distribution.evolve_mass]
  change (∑ next : AnchoredState State Parameter,
      (∑ current : AnchoredState State Parameter,
        law.mass current *
          (process.augmentedKernel.prob current.1 next.1 *
            (if next.2 = current.2 then 1 else 0))) *
        Mcmc.Finite.Nonhomogeneous.kernelVariation
          (process.kernel next.1.2) (process.kernel next.2)) ≤ _
  rw [show (∑ next : AnchoredState State Parameter,
      (∑ current : AnchoredState State Parameter,
        law.mass current *
          (process.augmentedKernel.prob current.1 next.1 *
            (if next.2 = current.2 then 1 else 0))) *
        Mcmc.Finite.Nonhomogeneous.kernelVariation
          (process.kernel next.1.2) (process.kernel next.2)) =
      ∑ current : AnchoredState State Parameter, law.mass current *
        ∑ next : State × Parameter,
          process.augmentedKernel.prob current.1 next *
            Mcmc.Finite.Nonhomogeneous.kernelVariation
              (process.kernel next.2) (process.kernel current.2) by
    calc
      _ = ∑ next : AnchoredState State Parameter,
          ∑ current : AnchoredState State Parameter,
            law.mass current *
              (process.augmentedKernel.prob current.1 next.1 *
                (if next.2 = current.2 then 1 else 0)) *
              Mcmc.Finite.Nonhomogeneous.kernelVariation
                (process.kernel next.1.2) (process.kernel next.2) := by
        apply Finset.sum_congr rfl
        intro next _
        rw [Finset.sum_mul]
      _ = ∑ current : AnchoredState State Parameter,
          ∑ next : AnchoredState State Parameter,
            law.mass current *
              (process.augmentedKernel.prob current.1 next.1 *
                (if next.2 = current.2 then 1 else 0)) *
              Mcmc.Finite.Nonhomogeneous.kernelVariation
                (process.kernel next.1.2) (process.kernel next.2) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro current _
        rw [Fintype.sum_prod_type]
        rw [show (∑ next : State × Parameter, ∑ anchor : Parameter,
            law.mass current *
              (process.augmentedKernel.prob current.1 next *
                (if anchor = current.2 then 1 else 0)) *
              Mcmc.Finite.Nonhomogeneous.kernelVariation
                (process.kernel next.2) (process.kernel anchor)) =
            law.mass current * ∑ next : State × Parameter,
              process.augmentedKernel.prob current.1 next *
                Mcmc.Finite.Nonhomogeneous.kernelVariation
                  (process.kernel next.2) (process.kernel current.2) by
          calc
            _ = ∑ next : State × Parameter,
                law.mass current *
                  (process.augmentedKernel.prob current.1 next *
                    Mcmc.Finite.Nonhomogeneous.kernelVariation
                      (process.kernel next.2) (process.kernel current.2)) := by
              apply Finset.sum_congr rfl
              intro next _
              simp
              ring
            _ = _ := by rw [Finset.mul_sum]]]
  calc
    _ ≤ ∑ current : AnchoredState State Parameter, law.mass current *
        ∑ next : State × Parameter,
          process.augmentedKernel.prob current.1 next *
            (Mcmc.Finite.Nonhomogeneous.kernelVariation
                (process.kernel next.2) (process.kernel current.1.2) +
              Mcmc.Finite.Nonhomogeneous.kernelVariation
                (process.kernel current.1.2) (process.kernel current.2)) := by
      apply Finset.sum_le_sum
      intro current _
      apply mul_le_mul_of_nonneg_left _ (law.nonneg current)
      apply Finset.sum_le_sum
      intro next _
      exact mul_le_mul_of_nonneg_left
        (Mcmc.Finite.Nonhomogeneous.kernelVariation_triangle _ _ _)
        (process.augmentedKernel.nonneg current.1 next)
    _ = anchoredVariation process law +
        expectedKernelVariation process (currentMarginal law) := by
      unfold anchoredVariation expectedKernelVariation currentMarginal
      simp_rw [mul_add]
      rw [show (∑ current : AnchoredState State Parameter,
          law.mass current *
            ∑ next : State × Parameter,
              (process.augmentedKernel.prob current.1 next *
                  Mcmc.Finite.Nonhomogeneous.kernelVariation
                    (process.kernel next.2) (process.kernel current.1.2) +
                process.augmentedKernel.prob current.1 next *
                  Mcmc.Finite.Nonhomogeneous.kernelVariation
                    (process.kernel current.1.2) (process.kernel current.2))) =
          ∑ current : State × Parameter,
              (∑ anchor, law.mass (current, anchor)) *
                ∑ next, process.augmentedKernel.prob current next *
                  Mcmc.Finite.Nonhomogeneous.kernelVariation
                    (process.kernel next.2) (process.kernel current.2) +
            ∑ current : AnchoredState State Parameter,
              law.mass current *
                Mcmc.Finite.Nonhomogeneous.kernelVariation
                  (process.kernel current.1.2) (process.kernel current.2) by
        simp_rw [Finset.sum_add_distrib, mul_add]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro current _
          rw [Finset.sum_mul]
        · apply Finset.sum_congr rfl
          intro current _
          rw [show (∑ next,
              process.augmentedKernel.prob current.1 next *
                Mcmc.Finite.Nonhomogeneous.kernelVariation
                  (process.kernel current.1.2) (process.kernel current.2)) =
              Mcmc.Finite.Nonhomogeneous.kernelVariation
                (process.kernel current.1.2) (process.kernel current.2) by
            rw [← Finset.sum_mul, process.augmentedKernel.sum_prob, one_mul]]]
      ring

@[simp] theorem anchoredVariation_anchorInitial
    (process : Process State Parameter)
    (law : Distribution (State × Parameter)) :
    anchoredVariation process (anchorInitial law) = 0 := by
  classical
  unfold anchoredVariation anchorInitial
  change (∑ current : AnchoredState State Parameter,
    (if current.2 = current.1.2 then law.mass current.1 else 0) *
      Mcmc.Finite.Nonhomogeneous.kernelVariation
        (process.kernel current.1.2) (process.kernel current.2)) = 0
  apply Finset.sum_eq_zero
  intro current _
  split_ifs with hanchor
  · rw [hanchor]
    simp [Mcmc.Finite.Nonhomogeneous.kernelVariation]
  · simp

/-- Accumulated distance from the initial window kernel is bounded by the sum
of expected successive-kernel variations. -/
theorem anchoredVariation_iterate_le_sum
    (process : Process State Parameter)
    (law : Distribution (State × Parameter)) (steps : ℕ) :
    anchoredVariation process
        (iterateLaw (anchorInitial law) (anchoredAdaptiveKernel process) steps) ≤
      ∑ j ∈ Finset.range steps,
        expectedKernelVariation process
          (iterateLaw law process.augmentedKernel j) := by
  induction steps with
  | zero => simp [iterateLaw]
  | succ steps ih =>
      rw [iterateLaw]
      calc
        anchoredVariation process
            ((iterateLaw (anchorInitial law)
              (anchoredAdaptiveKernel process) steps).evolve
                (anchoredAdaptiveKernel process)) ≤
            anchoredVariation process
                (iterateLaw (anchorInitial law)
                  (anchoredAdaptiveKernel process) steps) +
              expectedKernelVariation process
                (currentMarginal
                  (iterateLaw (anchorInitial law)
                    (anchoredAdaptiveKernel process) steps)) :=
          anchoredVariation_evolve_le process _
        _ ≤ (∑ j ∈ Finset.range steps,
              expectedKernelVariation process
                (iterateLaw law process.augmentedKernel j)) +
            expectedKernelVariation process
              (iterateLaw law process.augmentedKernel steps) := by
          rw [currentMarginal_iterate_anchoredAdaptiveKernel]
          exact add_le_add ih le_rfl
        _ = ∑ j ∈ Finset.range (steps + 1),
              expectedKernelVariation process
                (iterateLaw law process.augmentedKernel j) := by
          rw [Finset.sum_range_succ]

/-- One hybrid comparison step: evolve the first law adaptively and the
second with the frozen kernel. -/
theorem anchored_evolve_totalVariation_le
    (process : Process State Parameter)
    (adaptive frozen : Distribution (AnchoredState State Parameter)) :
    distributionTotalVariation
        (adaptive.evolve (anchoredAdaptiveKernel process))
        (frozen.evolve (anchoredFrozenKernel process)) ≤
      anchoredVariation process adaptive +
        distributionTotalVariation adaptive frozen := by
  calc
    distributionTotalVariation
        (adaptive.evolve (anchoredAdaptiveKernel process))
        (frozen.evolve (anchoredFrozenKernel process)) ≤
      distributionTotalVariation
          (adaptive.evolve (anchoredAdaptiveKernel process))
          (adaptive.evolve (anchoredFrozenKernel process)) +
        distributionTotalVariation
          (adaptive.evolve (anchoredFrozenKernel process))
          (frozen.evolve (anchoredFrozenKernel process)) :=
      distributionTotalVariation_triangle _ _ _
    _ ≤ (∑ current, adaptive.mass current *
          rowTotalVariation (anchoredAdaptiveKernel process)
            (anchoredFrozenKernel process) current) +
        distributionTotalVariation adaptive frozen :=
      add_le_add
        (distributionTotalVariation_evolve_kernel_le adaptive
          (anchoredAdaptiveKernel process) (anchoredFrozenKernel process))
        (distributionTotalVariation_evolve_le adaptive frozen
          (anchoredFrozenKernel process))
    _ ≤ anchoredVariation process adaptive +
        distributionTotalVariation adaptive frozen := by
      apply add_le_add _ le_rfl
      unfold anchoredVariation
      apply Finset.sum_le_sum
      intro current _
      exact mul_le_mul_of_nonneg_left
        (rowTotalVariation_anchored_le_kernelVariation process current)
        (adaptive.nonneg current)

/-- The actual and frozen anchored window laws differ by at most the sum of
the expected distances of the selected kernels from the window anchor. -/
theorem anchored_window_totalVariation_le_sum
    (process : Process State Parameter)
    (law : Distribution (State × Parameter)) (steps : ℕ) :
    distributionTotalVariation
        (iterateLaw (anchorInitial law) (anchoredAdaptiveKernel process) steps)
        (iterateLaw (anchorInitial law) (anchoredFrozenKernel process) steps) ≤
      ∑ k ∈ Finset.range steps,
        anchoredVariation process
          (iterateLaw (anchorInitial law)
            (anchoredAdaptiveKernel process) k) := by
  induction steps with
  | zero => simp [iterateLaw]
  | succ steps ih =>
      rw [iterateLaw, iterateLaw]
      calc
        _ ≤ anchoredVariation process
              (iterateLaw (anchorInitial law)
                (anchoredAdaptiveKernel process) steps) +
            distributionTotalVariation
              (iterateLaw (anchorInitial law)
                (anchoredAdaptiveKernel process) steps)
              (iterateLaw (anchorInitial law)
                (anchoredFrozenKernel process) steps) :=
          anchored_evolve_totalVariation_le process _ _
        _ ≤ anchoredVariation process
              (iterateLaw (anchorInitial law)
                (anchoredAdaptiveKernel process) steps) +
            ∑ k ∈ Finset.range steps,
              anchoredVariation process
                (iterateLaw (anchorInitial law)
                  (anchoredAdaptiveKernel process) k) :=
          add_le_add le_rfl ih
        _ = ∑ k ∈ Finset.range (steps + 1),
              anchoredVariation process
                (iterateLaw (anchorInitial law)
                  (anchoredAdaptiveKernel process) k) := by
          rw [Finset.sum_range_succ]
          ring

theorem iterateLaw_eq_lawAt_const (law : Distribution State)
    (kernel : MarkovKernel State) (steps : ℕ) :
    iterateLaw law kernel steps =
      Nonhomogeneous.lawAt law (fun _ => kernel) steps := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [iterateLaw, Nonhomogeneous.lawAt, ih]

theorem lawAt_const_add (law : Distribution State)
    (kernel : MarkovKernel State) (n steps : ℕ) :
    Nonhomogeneous.lawAt law (fun _ => kernel) (n + steps) =
      iterateLaw (Nonhomogeneous.lawAt law (fun _ => kernel) n) kernel steps := by
  induction steps with
  | zero => simp [iterateLaw]
  | succ steps ih =>
      rw [Nat.add_succ, Nonhomogeneous.lawAt, ih, iterateLaw]

omit [DecidableEq Parameter] in
theorem anchoredStateMarginal_totalVariation_le
    (first second : Distribution (AnchoredState State Parameter)) :
    distributionTotalVariation
        (anchoredStateMarginal first) (anchoredStateMarginal second) ≤
      distributionTotalVariation first second := by
  unfold distributionTotalVariation anchoredStateMarginal
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    ∑ x, |(∑ parameter, ∑ anchor, first.mass ((x, parameter), anchor)) -
        ∑ parameter, ∑ anchor, second.mass ((x, parameter), anchor)| =
        ∑ x, |∑ parameter, ∑ anchor,
          (first.mass ((x, parameter), anchor) -
            second.mass ((x, parameter), anchor))| := by
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg abs
      calc
        (∑ parameter, ∑ anchor, first.mass ((x, parameter), anchor)) -
            ∑ parameter, ∑ anchor, second.mass ((x, parameter), anchor) =
            ∑ parameter, ((∑ anchor, first.mass ((x, parameter), anchor)) -
              ∑ anchor, second.mass ((x, parameter), anchor)) := by
          rw [Finset.sum_sub_distrib]
        _ = ∑ parameter, ∑ anchor,
            (first.mass ((x, parameter), anchor) -
              second.mass ((x, parameter), anchor)) := by
          apply Finset.sum_congr rfl
          intro parameter _
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x, ∑ parameter, ∑ anchor,
        |first.mass ((x, parameter), anchor) -
          second.mass ((x, parameter), anchor)| := by
      apply Finset.sum_le_sum
      intro x _
      calc
        |∑ parameter, ∑ anchor,
            (first.mass ((x, parameter), anchor) -
              second.mass ((x, parameter), anchor))| ≤
            ∑ parameter, |∑ anchor,
              (first.mass ((x, parameter), anchor) -
                second.mass ((x, parameter), anchor))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ parameter, ∑ anchor,
            |first.mass ((x, parameter), anchor) -
              second.mass ((x, parameter), anchor)| := by
          apply Finset.sum_le_sum
          intro parameter _
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ current : AnchoredState State Parameter,
        |first.mass current - second.mass current| := by
      simp only [Fintype.sum_prod_type]

/-- Quantitative finite-window comparison.  If every successive-kernel change
probability over the window is at most `δ` at row tolerance `η`, the adaptive
state law differs from the frozen-window law by at most a quadratic finite
window bound. -/
theorem adaptive_frozenWindow_totalVariation_le
    [DecidableEq State]
    (process : Process State Parameter)
    (law : Distribution (State × Parameter)) (steps : ℕ)
    (η δ : ℝ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hchange : ∀ j, j < steps →
      changeProbability process
        (iterateLaw law process.augmentedKernel j) η ≤ δ) :
    distributionTotalVariation
        (stateMarginal (iterateLaw law process.augmentedKernel steps))
        (frozenWindowLaw process law steps) ≤
      (steps : ℝ) * (steps : ℝ) * Fintype.card State * (η + δ) := by
  let adaptiveLaw :=
    iterateLaw (anchorInitial law) (anchoredAdaptiveKernel process) steps
  let frozenLaw :=
    iterateLaw (anchorInitial law) (anchoredFrozenKernel process) steps
  have hadaptive : anchoredStateMarginal adaptiveLaw =
      stateMarginal (iterateLaw law process.augmentedKernel steps) := by
    rw [anchoredStateMarginal_eq_stateMarginal_currentMarginal,
      currentMarginal_iterate_anchoredAdaptiveKernel]
  have hfrozen : anchoredStateMarginal frozenLaw =
      frozenWindowLaw process law steps := by
    exact anchoredFrozen_stateMarginal_eq_frozenWindowLaw process law steps
  rw [← hadaptive, ← hfrozen]
  calc
    distributionTotalVariation
        (anchoredStateMarginal adaptiveLaw)
        (anchoredStateMarginal frozenLaw) ≤
      distributionTotalVariation adaptiveLaw frozenLaw :=
        anchoredStateMarginal_totalVariation_le adaptiveLaw frozenLaw
    _ ≤ ∑ k ∈ Finset.range steps,
        anchoredVariation process
          (iterateLaw (anchorInitial law)
            (anchoredAdaptiveKernel process) k) :=
      anchored_window_totalVariation_le_sum process law steps
    _ ≤ ∑ k ∈ Finset.range steps,
        ∑ j ∈ Finset.range k,
          expectedKernelVariation process
            (iterateLaw law process.augmentedKernel j) := by
      apply Finset.sum_le_sum
      intro k _
      exact anchoredVariation_iterate_le_sum process law k
    _ ≤ ∑ k ∈ Finset.range steps,
        ∑ _j ∈ Finset.range k,
          (Fintype.card State : ℝ) * (η + δ) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      exact le_trans
        (expectedKernelVariation_le process
          (iterateLaw law process.augmentedKernel j) η hη)
        (mul_le_mul_of_nonneg_left (by
          linarith [hchange j
            (lt_trans (Finset.mem_range.mp hj) (Finset.mem_range.mp hk))])
          (by positivity))
    _ ≤ ∑ _k ∈ Finset.range steps,
        (steps : ℝ) * ((Fintype.card State : ℝ) * (η + δ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hk))
      · exact mul_nonneg (by positivity) (add_nonneg hη hδ)
    _ = (steps : ℝ) * (steps : ℝ) * Fintype.card State * (η + δ) := by
      simp
      ring

/-- Total-variation convergence of the state marginal of a finite adaptive
process.  This is convergence of deterministic marginal laws, not an
almost-sure statement about sample paths and not a quantitative mixing rate. -/
def ConvergesInTotalVariation [DecidableEq State]
    (process : Process State Parameter) (target : Distribution State)
    (initial : Distribution (State × Parameter)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
    distributionTotalVariation (stateLawAt process initial n) target ≤ ε

/-- Finite Roberts--Rosenthal theorem: Diminishing Adaptation and Containment
imply convergence in total variation of the adaptive state marginal. -/
theorem convergesInTotalVariation_of_diminishingAdaptation_containment
    [DecidableEq State] [Nonempty State]
    (process : Process State Parameter) (target : Distribution State)
    (initial : Distribution (State × Parameter))
    (hdiminishing : DiminishingAdaptation process initial)
    (hcontainment : Containment process target initial) :
    ConvergesInTotalVariation process target initial := by
  intro ε hε
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨steps, hfrozen⟩ :=
    containment_frozenWindowLaw process target initial hcontainment
      (ε / 4) hquarter (ε / 4) hquarter
  let C : ℝ := (steps + 1 : ℕ) * (steps + 1 : ℕ) * Fintype.card State
  have hcard : (0 : ℝ) < Fintype.card State := by
    exact_mod_cast Fintype.card_pos
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let r : ℝ := ε / (8 * C)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  obtain ⟨N, hN⟩ := hdiminishing r hr r hr
  refine ⟨N + steps, fun t ht => ?_⟩
  let n := t - steps
  have hsteps : steps ≤ t := le_trans (Nat.le_add_left steps N) ht
  have hn : N ≤ n := by
    dsimp [n]
    exact Nat.le_sub_of_add_le ht
  have ht_eq : n + steps = t := by
    dsimp [n]
    exact Nat.sub_add_cancel hsteps
  let lawN := Nonhomogeneous.lawAt initial
    (fun _ => process.augmentedKernel) n
  have hchange : ∀ j, j < steps →
      changeProbability process
        (iterateLaw lawN process.augmentedKernel j) r ≤ r := by
    intro j hj
    rw [show iterateLaw lawN process.augmentedKernel j =
        Nonhomogeneous.lawAt initial (fun _ => process.augmentedKernel) (n + j) by
      symm
      exact lawAt_const_add initial process.augmentedKernel n j]
    exact hN (n + j) (le_trans hn (Nat.le_add_right n j))
  have hcompare := adaptive_frozenWindow_totalVariation_le
    process lawN steps r r (le_of_lt hr) (le_of_lt hr) hchange
  have hcoefficient :
      (steps : ℝ) * (steps : ℝ) * Fintype.card State ≤ C := by
    dsimp [C]
    have hs : (0 : ℝ) ≤ steps := by positivity
    have hsle : (steps : ℝ) ≤ (steps + 1 : ℕ) := by exact_mod_cast Nat.le_succ steps
    exact mul_le_mul_of_nonneg_right
      (mul_self_le_mul_self hs hsle) (le_of_lt hcard)
  have hcomparisonQuarter :
      (steps : ℝ) * (steps : ℝ) * Fintype.card State * (r + r) ≤ ε / 4 := by
    calc
      _ ≤ C * (r + r) :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
      _ = ε / 4 := by
        dsimp [r]
        field_simp
        ring
  have hactualFrozen :
      distributionTotalVariation
          (stateMarginal (iterateLaw lawN process.augmentedKernel steps))
          (frozenWindowLaw process lawN steps) ≤ ε / 4 :=
    le_trans hcompare hcomparisonQuarter
  have hfrozenTarget :
      distributionTotalVariation
          (frozenWindowLaw process lawN steps) target ≤ ε / 2 := by
    dsimp [lawN]
    have := hfrozen n
    linarith
  have hactualTarget := distributionTotalVariation_triangle
    (stateMarginal (iterateLaw lawN process.augmentedKernel steps))
    (frozenWindowLaw process lawN steps) target
  have hbound :
      distributionTotalVariation
          (stateMarginal (iterateLaw lawN process.augmentedKernel steps)) target ≤ ε := by
    linarith
  rw [← ht_eq]
  unfold stateLawAt
  rw [lawAt_const_add]
  exact hbound

end Mcmc.Finite.RandomAdaptation
