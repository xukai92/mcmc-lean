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
