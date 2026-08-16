import Mcmc.Finite.ParticleEstimator
import Mathlib.Tactic

/-!
# Exact finite-particle variance foundations

The iid particle estimator has genuinely independent distinct coordinates.
This module proves the corresponding finite second-moment identity for the
centered particle sum, the algebraic core of the usual inverse-particle-count
mean-square error. No asymptotic independence or central-limit theorem is
assumed.
-/

open scoped BigOperators

namespace Mcmc.Finite.ParticleEstimator

open MarkovKernel

variable {Sample Particle : Type*}
  [Fintype Sample] [Fintype Particle]
  [DecidableEq Sample] [DecidableEq Particle] [Nonempty Particle]

/-- Expectation of a real observable under a finite distribution. -/
noncomputable def finiteExpectation (law : Distribution Sample)
    (score : Sample → ℝ) : ℝ :=
  ∑ x, law.mass x * score x

/-- Centered second moment of one particle. -/
noncomputable def finiteVariance (law : Distribution Sample)
    (score : Sample → ℝ) : ℝ :=
  ∑ x, law.mass x * (score x - finiteExpectation law score) ^ 2

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Distinct coordinates of the iid product law factorize. -/
theorem iidPopulation_two_coordinate_expectation
    (law : Distribution Sample) (first second : Sample → ℝ)
    {i j : Particle} (hij : i ≠ j) :
    ∑ samples, (iidPopulation law).mass samples *
        (first (samples i) * second (samples j)) =
      (∑ x, law.mass x * first x) *
        (∑ y, law.mass y * second y) := by
  classical
  calc
    ∑ samples, (iidPopulation law).mass samples *
          (first (samples i) * second (samples j)) =
        ∑ samples : Particle → Sample,
          ∏ k, if k = i then law.mass (samples k) * first (samples k)
            else if k = j then law.mass (samples k) * second (samples k)
            else law.mass (samples k) := by
      apply Finset.sum_congr rfl
      intro samples _
      change (∏ k, law.mass (samples k)) *
          (first (samples i) * second (samples j)) = _
      have hfactor :
          (∏ k, if k = i then first (samples k)
            else if k = j then second (samples k) else 1) =
          first (samples i) * second (samples j) := by
        rw [Fintype.prod_eq_mul_prod_compl i]
        simp only [if_pos]
        rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
          (show j ∈ ({i} : Finset Particle)ᶜ by simp [hij.symm])]
        have hrest : ∏ k ∈ (({i} : Finset Particle)ᶜ \ {j}),
            (if k = i then first (samples k)
              else if k = j then second (samples k) else 1) = 1 := by
          apply Finset.prod_eq_one
          intro k hk
          have hki : k ≠ i := by
            simpa using (Finset.mem_sdiff.mp hk).1
          have hkj : k ≠ j := by
            simpa using (Finset.mem_sdiff.mp hk).2
          simp [hki, hkj]
        rw [hrest]
        simp [hij.symm]
      calc
        _ = (∏ k, law.mass (samples k)) *
            (∏ k, if k = i then first (samples k)
              else if k = j then second (samples k) else 1) := by rw [hfactor]
        _ = ∏ k, law.mass (samples k) *
            (if k = i then first (samples k)
              else if k = j then second (samples k) else 1) := by
            rw [Finset.prod_mul_distrib]
        _ = _ := by
          apply Finset.prod_congr rfl
          intro k _
          by_cases hki : k = i
          · simp [hki]
          · by_cases hkj : k = j <;> simp [hki, hkj]
    _ = ∏ k : Particle,
          ∑ x, if k = i then law.mass x * first x
            else if k = j then law.mass x * second x else law.mass x := by
      exact (Fintype.prod_sum
        (f := fun k : Particle => fun x : Sample =>
          if k = i then law.mass x * first x
          else if k = j then law.mass x * second x else law.mass x)).symm
    _ = (∑ x, law.mass x * first x) *
          (∑ y, law.mass y * second y) := by
      let A := ∑ x, law.mass x * first x
      let B := ∑ y, law.mass y * second y
      have hsum (k : Particle) :
          (∑ x, if k = i then law.mass x * first x
            else if k = j then law.mass x * second x else law.mass x) =
          if k = i then A else if k = j then B else 1 := by
        by_cases hki : k = i
        · simp [hki, A]
        · by_cases hkj : k = j
          · simp [hkj, hij.symm, B]
          · simp [hki, hkj, law.sum_mass]
      simp_rw [hsum]
      change (∏ k, if k = i then A else if k = j then B else 1) = A * B
      rw [Fintype.prod_eq_mul_prod_compl i]
      simp only [if_pos]
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
        (show j ∈ ({i} : Finset Particle)ᶜ by simp [hij.symm])]
      have hrest : ∏ k ∈ (({i} : Finset Particle)ᶜ \ {j}),
          (if k = i then A else if k = j then B else 1) = 1 := by
        apply Finset.prod_eq_one
        intro k hk
        have hki : k ≠ i := by simpa using (Finset.mem_sdiff.mp hk).1
        have hkj : k ≠ j := by simpa using (Finset.mem_sdiff.mp hk).2
        simp [hki, hkj]
      rw [hrest]
      simp [hij.symm]

omit [DecidableEq Sample] in
theorem finiteExpectation_centered (law : Distribution Sample)
    (score : Sample → ℝ) :
    ∑ x, law.mass x * (score x - finiteExpectation law score) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp [finiteExpectation, law.sum_mass]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- The expected squared centered particle sum is exactly particle count
times the one-particle variance. -/
theorem iidPopulation_centered_sum_sq_expectation
    (law : Distribution Sample) (score : Sample → ℝ) :
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
        (∑ i, (score (samples i) - finiteExpectation law score)) ^ 2 =
      Fintype.card Particle * finiteVariance law score := by
  classical
  let centered : Sample → ℝ :=
    fun x => score x - finiteExpectation law score
  have hcentered : ∑ x, law.mass x * centered x = 0 :=
    finiteExpectation_centered law score
  have hpair (i j : Particle) :
      ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
          (centered (samples i) * centered (samples j)) =
        if i = j then finiteVariance law score else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [if_true]
      have hsq (x : Sample) : centered x * centered x = centered x ^ 2 := by
        rw [pow_two]
      simp_rw [hsq]
      simpa only [finiteVariance, centered] using
        iidPopulation_coordinate_expectation law (fun x => centered x ^ 2) i
    · simp only [if_neg hij]
      rw [iidPopulation_two_coordinate_expectation law centered centered hij,
        hcentered, zero_mul]
  dsimp only [centered] at hcentered hpair ⊢
  change ∑ samples : Particle → Sample,
      (iidPopulation law).mass samples * (∑ i, centered (samples i)) ^ 2 = _
  calc
    _ = ∑ samples : Particle → Sample, ∑ i, ∑ j,
          (iidPopulation law).mass samples *
            (centered (samples i) * centered (samples j)) := by
      apply Finset.sum_congr rfl
      intro samples _
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ samples : Particle → Sample,
          (iidPopulation law).mass samples *
            (centered (samples i) * centered (samples j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, if i = j then finiteVariance law score else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpair i j
    _ = Fintype.card Particle * finiteVariance law score := by simp

omit [DecidableEq Sample] in
/-- Exact inverse-count mean-square error of the iid particle average. -/
theorem iidPopulation_particleAverage_mse
    (law : Distribution Sample) (score : Sample → ℝ) :
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
        (particleAverage score samples - finiteExpectation law score) ^ 2 =
      finiteVariance law score / Fintype.card Particle := by
  classical
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have havg (samples : Particle → Sample) :
      particleAverage score samples - finiteExpectation law score =
        (∑ i, (score (samples i) - finiteExpectation law score)) /
          Fintype.card Particle := by
    unfold particleAverage
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.card_univ]
    field_simp
  simp_rw [havg, div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div,
    iidPopulation_centered_sum_sq_expectation law score]
  field_simp

end Mcmc.Finite.ParticleEstimator
