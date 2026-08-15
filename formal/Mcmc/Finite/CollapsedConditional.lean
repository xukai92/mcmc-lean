import Mcmc.Finite.Conditional
import Mcmc.Finite.Dynamics

/-!
# Collapsed conditional kernels

This module constructs the Markov kernel induced on a finite statistic by:

1. drawing the extended state from its exact conditional law given the
   current statistic;
2. applying a target-invariant extended-state kernel; and
3. projecting back to the statistic.

It is the finite algebraic counterpart of lift--evolve--project and supplies
the correct trajectory-state interface for particle Gibbs.
-/

open scoped BigOperators

namespace Mcmc.Finite.Conditional

open MarkovKernel

variable {Extended Statistic : Type*}
  [Fintype Extended] [DecidableEq Extended]
  [Fintype Statistic] [DecidableEq Statistic]

/-- The pushforward target of a finite statistic. -/
noncomputable def statisticMarginal (target : Distribution Extended)
    (statistic : Extended → Statistic) : Distribution Statistic :=
  Distribution.map target statistic

omit [DecidableEq Extended] in
theorem statisticMarginal_mass (target : Distribution Extended)
    (statistic : Extended → Statistic) (s : Statistic) :
    (statisticMarginal target statistic).mass s =
      fiberMass target statistic s := by
  unfold statisticMarginal Distribution.map Distribution.bind fiberMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : statistic x = s
  · simp [h]
  · simp [h, Ne.symm h]

/-- Total conditional row. A zero-mass statistic fiber uses an arbitrary
point mass; the marginal gives that row coefficient zero. -/
noncomputable def conditionalRow (target : Distribution Extended)
    (statistic : Extended → Statistic) (s : Statistic) :
    Distribution Extended :=
  if h : 0 < fiberMass target statistic s then
    fiberLaw target statistic s h
  else target

/-- Averaging the exact conditional rows against the statistic marginal
reconstructs the extended target. -/
theorem bind_statisticMarginal_conditionalRow
    (target : Distribution Extended) (statistic : Extended → Statistic) :
    Distribution.bind (statisticMarginal target statistic)
      (conditionalRow target statistic) = target := by
  apply Distribution.ext
  funext x
  rw [Distribution.bind_mass]
  rw [Finset.sum_eq_single (statistic x)]
  · rw [statisticMarginal_mass]
    by_cases hfiber : 0 < fiberMass target statistic (statistic x)
    · simp [conditionalRow, hfiber, fiberLaw]
      field_simp
    · have hmass : target.mass x = 0 := by
        apply le_antisymm
        · apply le_of_not_gt
          intro hx
          exact hfiber (fiberMass_pos_of_mass_pos target statistic x hx)
        · exact target.nonneg x
      have hzero : fiberMass target statistic (statistic x) = 0 :=
        le_antisymm (not_lt.mp hfiber)
          (fiberMass_nonneg target statistic (statistic x))
      simp [conditionalRow, hmass, hzero]
  · intro s _ hs
    by_cases hfiber : 0 < fiberMass target statistic s
    · have hstat : statistic x ≠ s := fun h => hs h.symm
      simp [conditionalRow, hfiber, fiberLaw, hstat]
    · rw [statisticMarginal_mass]
      have hzero : fiberMass target statistic s = 0 :=
        le_antisymm (not_lt.mp hfiber) (fiberMass_nonneg target statistic s)
      simp [hzero]
  · simp

/-- Turn a family of finite distributions into a Markov kernel. -/
def kernelOfRows (rows : Statistic → Distribution Statistic) :
    MarkovKernel Statistic where
  prob x y := (rows x).mass y
  nonneg x y := (rows x).nonneg y
  sum_prob x := (rows x).sum_mass

omit [DecidableEq Extended] [DecidableEq Statistic] in
private theorem bind_evolve (law : Distribution Statistic)
    (lift : Statistic → Distribution Extended) (evolve : MarkovKernel Extended) :
    Distribution.bind law (fun s => (lift s).evolve evolve) =
      (Distribution.bind law lift).evolve evolve := by
  apply Distribution.ext
  funext y
  simp only [Distribution.bind_mass, Distribution.evolve_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

omit [DecidableEq Extended] [DecidableEq Statistic] in
private theorem bind_map {Output : Type*} [Fintype Output] [DecidableEq Output]
    (law : Distribution Statistic) (next : Statistic → Distribution Extended)
    (f : Extended → Output) :
    Distribution.bind law (fun s => Distribution.map (next s) f) =
      Distribution.map (Distribution.bind law next) f := by
  apply Distribution.ext
  funext y
  unfold Distribution.map
  simp only [Distribution.bind_mass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Condition on a statistic, evolve the extended state, and project back to
the statistic. -/
noncomputable def collapsedKernel (target : Distribution Extended)
    (statistic : Extended → Statistic) (evolve : MarkovKernel Extended) :
    MarkovKernel Statistic :=
  kernelOfRows fun s =>
    Distribution.map ((conditionalRow target statistic s).evolve evolve)
      statistic

/-- A positive extended-state edge between the current and proposed fibers
gives a positive edge of the collapsed kernel. This witness form is useful
when the extended evolution is sparse, as in particle Gibbs. -/
theorem collapsedKernel_prob_pos_of_witness
    (target : Distribution Extended) (statistic : Extended → Statistic)
    (evolve : MarkovKernel Extended)
    (current proposed : Statistic) (liftCurrent liftProposed : Extended)
    (hcurrent : statistic liftCurrent = current)
    (hproposed : statistic liftProposed = proposed)
    (htarget : 0 < target.mass liftCurrent)
    (hevolve : 0 < evolve.prob liftCurrent liftProposed) :
    0 < (collapsedKernel target statistic evolve).prob current proposed := by
  have hfiber : 0 < fiberMass target statistic current := by
    rw [← hcurrent]
    exact fiberMass_pos_of_mass_pos target statistic liftCurrent
      htarget
  have hconditional :
      0 < (conditionalRow target statistic current).mass liftCurrent := by
    simp [conditionalRow, hfiber, fiberLaw, hcurrent, htarget]
  have hevolved :
      0 < ((conditionalRow target statistic current).evolve evolve).mass
        liftProposed := by
    rw [Distribution.evolve_mass]
    refine lt_of_lt_of_le
      (mul_pos hconditional hevolve) ?_
    exact Finset.single_le_sum
      (fun x _ => mul_nonneg
        ((conditionalRow target statistic current).nonneg x)
        (evolve.nonneg x liftProposed)) (Finset.mem_univ liftCurrent)
  change 0 < (Distribution.map
    ((conditionalRow target statistic current).evolve evolve)
    statistic).mass proposed
  unfold Distribution.map
  rw [Distribution.bind_mass]
  change 0 < ∑ x,
    ((conditionalRow target statistic current).evolve evolve).mass x *
      (if proposed = statistic x then 1 else 0)
  have hterm : 0 <
      ((conditionalRow target statistic current).evolve evolve).mass
          liftProposed *
        (if proposed = statistic liftProposed then 1 else 0) := by
    simpa [hproposed.symm] using hevolved
  exact hterm.trans_le (Finset.single_le_sum
    (fun x _ => show 0 ≤
        ((conditionalRow target statistic current).evolve evolve).mass x *
          (if proposed = statistic x then 1 else 0) from
      mul_nonneg
        (((conditionalRow target statistic current).evolve evolve).nonneg x)
        (by by_cases h : proposed = statistic x <;> simp [h]))
    (Finset.mem_univ liftProposed))

/-- A collapsed kernel has full support when the extended target and evolution
have full support and every statistic value has an extended representative.
This supplies a reusable route from an exact lift--evolve--project
construction to finite-state Doeblin convergence. -/
theorem collapsedKernel_prob_pos
    (target : Distribution Extended) (statistic : Extended → Statistic)
    (evolve : MarkovKernel Extended)
    (htarget : ∀ x, 0 < target.mass x)
    (hevolve : ∀ x y, 0 < evolve.prob x y)
    (hsurjective : Function.Surjective statistic)
    (current proposed : Statistic) :
    0 < (collapsedKernel target statistic evolve).prob current proposed := by
  obtain ⟨liftCurrent, hcurrent⟩ := hsurjective current
  obtain ⟨liftProposed, hproposed⟩ := hsurjective proposed
  exact collapsedKernel_prob_pos_of_witness target statistic evolve
    current proposed liftCurrent liftProposed hcurrent hproposed
    (htarget liftCurrent) (hevolve liftCurrent liftProposed)

/-- The collapsed statistic kernel preserves the statistic marginal whenever
the extended evolution preserves the extended target. -/
theorem collapsedKernel_stationary (target : Distribution Extended)
    (statistic : Extended → Statistic) (evolve : MarkovKernel Extended)
    (hevolve : evolve.Stationary target) :
    (collapsedKernel target statistic evolve).Stationary
      (statisticMarginal target statistic) := by
  intro proposed
  change (∑ current,
    (statisticMarginal target statistic).mass current *
      (Distribution.map
        ((conditionalRow target statistic current).evolve evolve)
        statistic).mass proposed) = _
  have hbind := bind_statisticMarginal_conditionalRow target statistic
  have hevolved :
      (Distribution.bind (statisticMarginal target statistic)
        (conditionalRow target statistic)).evolve evolve = target := by
    rw [hbind]
    exact hevolve.evolve_eq
  have htotal :
      Distribution.bind (statisticMarginal target statistic)
        (fun current =>
          Distribution.map
            ((conditionalRow target statistic current).evolve evolve)
            statistic) =
        statisticMarginal target statistic := by
    rw [bind_map]
    rw [bind_evolve]
    rw [hevolved]
    rfl
  exact congrFun (congrArg Distribution.mass htotal) proposed

end Mcmc.Finite.Conditional
