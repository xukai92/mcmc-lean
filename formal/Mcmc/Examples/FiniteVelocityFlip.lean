import Mcmc.PDMP.Uniformization

/-!
# Symmetric finite velocity-switching generator

This is the jump component shared by elementary Zig-Zag-style models: two
velocity signs switch at a common nonnegative rate.  It is a finite CTMC
client of the separate PDMP generator architecture, not yet a construction of
the continuous position process.
-/

namespace Mcmc.Examples.FiniteVelocityFlip

open Mcmc.PDMP Mcmc.Finite.MarkovKernel

noncomputable def velocityTarget : Distribution Bool where
  mass _ := 1 / 2
  nonneg _ := by norm_num
  sum_mass := by norm_num [Fintype.sum_bool]

noncomputable def rates (switchRate : ℝ) (hnonneg : 0 ≤ switchRate) :
    FiniteRateGenerator Bool where
  rate current proposed := if current = proposed then 0 else switchRate
  nonneg current proposed := by
    split <;> positivity

theorem rates_reversible (switchRate : ℝ) (hnonneg : 0 ≤ switchRate) :
    (rates switchRate hnonneg).Reversible velocityTarget := by
  intro current proposed
  cases current <;> cases proposed <;>
    simp [rates, velocityTarget]

theorem exitRate_eq (switchRate : ℝ) (hnonneg : 0 ≤ switchRate)
    (velocity : Bool) :
    (rates switchRate hnonneg).exitRate velocity = switchRate := by
  cases velocity <;>
    simp [FiniteRateGenerator.exitRate, rates]

/-- Uniformizing at the exact switch rate produces the deterministic embedded
velocity-flip chain. -/
noncomputable def flipKernel (switchRate : ℝ) (hpositive : 0 < switchRate) :
    Mcmc.Finite.MarkovKernel Bool :=
  (rates switchRate (le_of_lt hpositive)).uniformizedKernel switchRate hpositive
    (fun velocity => by rw [exitRate_eq])

theorem flipKernel_stationary (switchRate : ℝ) (hpositive : 0 < switchRate) :
    (flipKernel switchRate hpositive).Stationary velocityTarget := by
  exact FiniteRateGenerator.uniformizedKernel_stationary
    (rates switchRate (le_of_lt hpositive)) velocityTarget
    (rates_reversible switchRate (le_of_lt hpositive)) switchRate hpositive
    (fun velocity => by rw [exitRate_eq])

@[simp] theorem flipKernel_prob_not (switchRate : ℝ)
    (hpositive : 0 < switchRate) (velocity : Bool) :
    (flipKernel switchRate hpositive).prob velocity (!velocity) = 1 := by
  unfold flipKernel
  rw [FiniteRateGenerator.uniformizedKernel_prob_ne]
  · simp [rates, hpositive.ne']
  · cases velocity <;> decide

/-- The symmetric velocity-flip generator has zero expectation under the
uniform velocity target for every observable. -/
theorem generator_mean_zero (switchRate : ℝ) (hnonneg : 0 ≤ switchRate)
    (f : Bool → ℝ) :
    ∑ velocity, velocityTarget.mass velocity *
      (rates switchRate hnonneg).apply f velocity = 0 :=
  FiniteRateGenerator.sum_mass_mul_apply_eq_zero
    (rates switchRate hnonneg) velocityTarget
    (rates_reversible switchRate hnonneg) f

end Mcmc.Examples.FiniteVelocityFlip
