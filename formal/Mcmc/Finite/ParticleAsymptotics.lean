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
theorem finiteVariance_nonneg (law : Distribution Sample)
    (score : Sample → ℝ) : 0 ≤ finiteVariance law score := by
  unfold finiteVariance
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (law.nonneg x) (sq_nonneg _)

omit [DecidableEq Sample] in
theorem finiteExpectation_centered (law : Distribution Sample)
    (score : Sample → ℝ) :
    ∑ x, law.mass x * (score x - finiteExpectation law score) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp [finiteExpectation, law.sum_mass]

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

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Distinct coordinates also factorize for an independent, non-identically
distributed population. This is the conditional covariance lemma needed for
sequential resample--propagate variance analysis. -/
theorem independentPopulation_two_coordinate_expectation
    (law : Particle → Distribution Sample) (first second : Sample → ℝ)
    {i j : Particle} (hij : i ≠ j) :
    ∑ samples, (independentPopulation law).mass samples *
        (first (samples i) * second (samples j)) =
      (∑ x, (law i).mass x * first x) *
        (∑ y, (law j).mass y * second y) := by
  classical
  calc
    ∑ samples, (independentPopulation law).mass samples *
          (first (samples i) * second (samples j)) =
        ∑ samples : Particle → Sample,
          ∏ k, if k = i then (law k).mass (samples k) * first (samples k)
            else if k = j then (law k).mass (samples k) * second (samples k)
            else (law k).mass (samples k) := by
      apply Finset.sum_congr rfl
      intro samples _
      change (∏ k, (law k).mass (samples k)) *
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
          have hki : k ≠ i := by simpa using (Finset.mem_sdiff.mp hk).1
          have hkj : k ≠ j := by simpa using (Finset.mem_sdiff.mp hk).2
          simp [hki, hkj]
        rw [hrest]
        simp [hij.symm]
      calc
        _ = (∏ k, (law k).mass (samples k)) *
            (∏ k, if k = i then first (samples k)
              else if k = j then second (samples k) else 1) := by rw [hfactor]
        _ = ∏ k, (law k).mass (samples k) *
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
          ∑ x, if k = i then (law k).mass x * first x
            else if k = j then (law k).mass x * second x
            else (law k).mass x := by
      exact (Fintype.prod_sum
        (f := fun k : Particle => fun x : Sample =>
          if k = i then (law k).mass x * first x
          else if k = j then (law k).mass x * second x
          else (law k).mass x)).symm
    _ = (∑ x, (law i).mass x * first x) *
          (∑ y, (law j).mass y * second y) := by
      let A := ∑ x, (law i).mass x * first x
      let B := ∑ y, (law j).mass y * second y
      have hsum (k : Particle) :
          (∑ x, if k = i then (law k).mass x * first x
            else if k = j then (law k).mass x * second x
            else (law k).mass x) =
          if k = i then A else if k = j then B else 1 := by
        by_cases hki : k = i
        · subst k
          simp [A]
        · by_cases hkj : k = j
          · subst k
            simp [hki, B]
          · simp [hki, hkj, Distribution.sum_mass]
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

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Conditional centered second moment for a heterogeneous independent
population: cross-coordinate covariances vanish exactly. -/
theorem independentPopulation_centered_sum_sq_expectation
    (law : Particle → Distribution Sample) (score : Sample → ℝ) :
    ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
        (∑ i, (score (samples i) - finiteExpectation (law i) score)) ^ 2 =
      ∑ i, finiteVariance (law i) score := by
  classical
  have hpair (i j : Particle) :
      ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
          ((score (samples i) - finiteExpectation (law i) score) *
            (score (samples j) - finiteExpectation (law j) score)) =
        if i = j then finiteVariance (law i) score else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [if_true]
      simp_rw [show ∀ x : Sample,
        (score x - finiteExpectation (law i) score) *
          (score x - finiteExpectation (law i) score) =
        (score x - finiteExpectation (law i) score) ^ 2 by
          intro x; rw [pow_two]]
      simpa only [finiteVariance] using
        independentPopulation_coordinate_expectation law
          (fun x => (score x - finiteExpectation (law i) score) ^ 2) i
    · simp only [if_neg hij]
      rw [independentPopulation_two_coordinate_expectation law
        (fun x => score x - finiteExpectation (law i) score)
        (fun x => score x - finiteExpectation (law j) score) hij,
        finiteExpectation_centered, finiteExpectation_centered, zero_mul]
  calc
    _ = ∑ samples : Particle → Sample, ∑ i, ∑ j,
          (independentPopulation law).mass samples *
            ((score (samples i) - finiteExpectation (law i) score) *
              (score (samples j) - finiteExpectation (law j) score)) := by
      apply Finset.sum_congr rfl
      intro samples _
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ samples : Particle → Sample,
          (independentPopulation law).mass samples *
            ((score (samples i) - finiteExpectation (law i) score) *
              (score (samples j) - finiteExpectation (law j) score)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, if i = j then finiteVariance (law i) score else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpair i j
    _ = ∑ i, finiteVariance (law i) score := by simp

/-- The conditional empirical mean for heterogeneous independent particles. -/
noncomputable def independentPopulationMean
    (law : Particle → Distribution Sample) (score : Sample → ℝ) : ℝ :=
  (∑ i, finiteExpectation (law i) score) / Fintype.card Particle

omit [DecidableEq Sample] in
/-- Exact conditional MSE of a heterogeneous independent population average.
This is the variance recurrence input for each SMC propagation stage. -/
theorem independentPopulation_particleAverage_mse
    (law : Particle → Distribution Sample) (score : Sample → ℝ) :
    ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
        (particleAverage score samples - independentPopulationMean law score) ^ 2 =
      (∑ i, finiteVariance (law i) score) /
        (Fintype.card Particle : ℝ) ^ 2 := by
  classical
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have havg (samples : Particle → Sample) :
      particleAverage score samples - independentPopulationMean law score =
        (∑ i, (score (samples i) - finiteExpectation (law i) score)) /
          Fintype.card Particle := by
    unfold particleAverage independentPopulationMean
    rw [Finset.sum_sub_distrib]
    ring
  simp_rw [havg, div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div,
    independentPopulation_centered_sum_sq_expectation law score]

omit [DecidableEq Sample] [Nonempty Particle] in
theorem independentPopulation_particleAverage_centered_expectation
    (law : Particle → Distribution Sample) (score : Sample → ℝ) :
    ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
      (particleAverage score samples - independentPopulationMean law score) = 0 := by
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [independentPopulation_particleAverage_expectation]
  rw [← Finset.sum_mul]
  simp [independentPopulationMean, finiteExpectation,
    (independentPopulation law).sum_mass]

omit [DecidableEq Sample] in
/-- Bias--variance decomposition around an arbitrary scalar reference for a
heterogeneous independent population. -/
theorem independentPopulation_particleAverage_sq_expectation
    (law : Particle → Distribution Sample) (score : Sample → ℝ)
    (reference : ℝ) :
    ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
        (particleAverage score samples - reference) ^ 2 =
      (∑ i, finiteVariance (law i) score) /
          (Fintype.card Particle : ℝ) ^ 2 +
        (independentPopulationMean law score - reference) ^ 2 := by
  have hcentered :=
    independentPopulation_particleAverage_centered_expectation law score
  have hmiddle :
      (∑ samples : Particle → Sample,
        (independentPopulation law).mass samples *
          (2 * (particleAverage score samples -
            independentPopulationMean law score) *
              (independentPopulationMean law score - reference))) =
        2 * (independentPopulationMean law score - reference) *
          (∑ samples : Particle → Sample,
            (independentPopulation law).mass samples *
              (particleAverage score samples -
                independentPopulationMean law score)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro samples _
    ring
  have hconstant :
      (∑ samples : Particle → Sample,
        (independentPopulation law).mass samples *
          (independentPopulationMean law score - reference) ^ 2) =
        (independentPopulationMean law score - reference) ^ 2 := by
    rw [← Finset.sum_mul, (independentPopulation law).sum_mass, one_mul]
  calc
    _ = ∑ samples : Particle → Sample,
        (independentPopulation law).mass samples *
          ((particleAverage score samples - independentPopulationMean law score) ^ 2 +
            2 * (particleAverage score samples -
              independentPopulationMean law score) *
                (independentPopulationMean law score - reference) +
            (independentPopulationMean law score - reference) ^ 2) := by
      apply Finset.sum_congr rfl
      intro samples _
      congr 1
      ring
    _ = (∑ samples : Particle → Sample,
          (independentPopulation law).mass samples *
            (particleAverage score samples -
              independentPopulationMean law score) ^ 2) +
        2 * (independentPopulationMean law score - reference) *
          (∑ samples : Particle → Sample,
            (independentPopulation law).mass samples *
              (particleAverage score samples -
                independentPopulationMean law score)) +
        (independentPopulationMean law score - reference) ^ 2 := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        hmiddle, hconstant]
    _ = _ := by
      rw [independentPopulation_particleAverage_mse, hcentered]
      simp

omit [DecidableEq Sample] in
/-- Exact one-step resample--propagate MSE. The two `1/N` terms are the
average conditional propagation variance and the multinomial-ancestry
variance of the propagated conditional mean. -/
theorem resamplePropagate_particleAverage_mse
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) (score : Sample → ℝ) :
    let transitionMean : Particle → ℝ := fun i =>
      finiteExpectation (rowDistribution transition (particles i)) score
    let transitionVariance : Particle → ℝ := fun i =>
      finiteVariance (rowDistribution transition (particles i)) score
    ∑ ancestors : Particle → Particle,
        (multinomialResampling weights).mass ancestors *
          (∑ next : Particle → Sample,
            (propagatedPopulation transition particles ancestors).mass next *
              (particleAverage score next -
                finiteExpectation weights transitionMean) ^ 2) =
      (finiteExpectation weights transitionVariance +
        finiteVariance weights transitionMean) / Fintype.card Particle := by
  dsimp only
  let transitionMean : Particle → ℝ := fun i =>
    finiteExpectation (rowDistribution transition (particles i)) score
  let transitionVariance : Particle → ℝ := fun i =>
    finiteVariance (rowDistribution transition (particles i)) score
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hconditional (ancestors : Particle → Particle) :
      (∑ next : Particle → Sample,
        (propagatedPopulation transition particles ancestors).mass next *
          (particleAverage score next -
            finiteExpectation weights transitionMean) ^ 2) =
        (∑ j, transitionVariance (ancestors j)) /
            (Fintype.card Particle : ℝ) ^ 2 +
          (particleAverage transitionMean ancestors -
            finiteExpectation weights transitionMean) ^ 2 := by
    simpa [propagatedPopulation, independentPopulationMean,
      particleAverage, transitionMean, transitionVariance] using
      independentPopulation_particleAverage_sq_expectation
        (fun j => rowDistribution transition (particles (ancestors j)))
        score (finiteExpectation weights transitionMean)
  have hvarianceTerm :
      (∑ ancestors : Particle → Particle,
        (multinomialResampling weights).mass ancestors *
          ((∑ j, transitionVariance (ancestors j)) /
            (Fintype.card Particle : ℝ) ^ 2)) =
        finiteExpectation weights transitionVariance /
          Fintype.card Particle := by
    have hrearrange (ancestors : Particle → Particle) :
        (∑ j, transitionVariance (ancestors j)) /
            (Fintype.card Particle : ℝ) ^ 2 =
          particleAverage transitionVariance ancestors /
            Fintype.card Particle := by
      unfold particleAverage
      field_simp
    simp_rw [hrearrange, ← mul_div_assoc]
    rw [← Finset.sum_div, multinomialResampling,
      iidPopulation_particleAverage_expectation weights transitionVariance]
    rfl
  have hmeanTerm :
      (∑ ancestors : Particle → Particle,
        (multinomialResampling weights).mass ancestors *
          (particleAverage transitionMean ancestors -
            finiteExpectation weights transitionMean) ^ 2) =
        finiteVariance weights transitionMean / Fintype.card Particle := by
    have hmean : independentPopulationMean
        (fun _ : Particle => weights) transitionMean =
        finiteExpectation weights transitionMean := by
      unfold independentPopulationMean
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hmse := independentPopulation_particleAverage_mse
      (fun _ : Particle => weights) transitionMean
    rw [hmean] at hmse
    change (∑ ancestors : Particle → Particle,
      (independentPopulation (fun _ : Particle => weights)).mass ancestors *
        (particleAverage transitionMean ancestors -
          finiteExpectation weights transitionMean) ^ 2) = _
    rw [hmse]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  change (∑ ancestors : Particle → Particle,
      (multinomialResampling weights).mass ancestors *
        (∑ next : Particle → Sample,
          (propagatedPopulation transition particles ancestors).mass next *
            (particleAverage score next -
              finiteExpectation weights transitionMean) ^ 2)) =
    (finiteExpectation weights transitionVariance +
      finiteVariance weights transitionMean) / Fintype.card Particle
  simp_rw [hconditional, mul_add]
  rw [Finset.sum_add_distrib, hvarianceTerm, hmeanTerm]
  ring

omit [DecidableEq Sample] in
/-- A directly checkable one-step `O(1/N)` bound for bootstrap
resample--propagate. -/
theorem resamplePropagate_particleAverage_mse_le
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) (score : Sample → ℝ)
    {propagationVariance ancestryVariance : ℝ}
    (hpropagation : ∀ i,
      finiteVariance (rowDistribution transition (particles i)) score ≤
        propagationVariance)
    (hancestry : finiteVariance weights (fun i =>
      finiteExpectation (rowDistribution transition (particles i)) score) ≤
        ancestryVariance) :
    let transitionMean : Particle → ℝ := fun i =>
      finiteExpectation (rowDistribution transition (particles i)) score
    ∑ ancestors : Particle → Particle,
        (multinomialResampling weights).mass ancestors *
          (∑ next : Particle → Sample,
            (propagatedPopulation transition particles ancestors).mass next *
              (particleAverage score next -
                finiteExpectation weights transitionMean) ^ 2) ≤
      (propagationVariance + ancestryVariance) / Fintype.card Particle := by
  dsimp only
  rw [resamplePropagate_particleAverage_mse]
  have hpropagationMean :
      finiteExpectation weights (fun i =>
        finiteVariance (rowDistribution transition (particles i)) score) ≤
          propagationVariance := by
    unfold finiteExpectation
    calc
      _ ≤ ∑ i, weights.mass i * propagationVariance := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hpropagation i) (weights.nonneg i)
      _ = propagationVariance := by
        rw [← Finset.sum_mul, weights.sum_mass, one_mul]
  exact div_le_div_of_nonneg_right
    (add_le_add hpropagationMean hancestry)
    (by positivity)

omit [DecidableEq Sample] in
/-- A common coordinate-variance bound gives the usual conditional `V/N`
MSE bound even when the independently propagated particles are heterogeneous. -/
theorem independentPopulation_particleAverage_mse_le
    (law : Particle → Distribution Sample) (score : Sample → ℝ)
    {varianceBound : ℝ}
    (hvariance : ∀ i, finiteVariance (law i) score ≤ varianceBound) :
    ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
        (particleAverage score samples - independentPopulationMean law score) ^ 2 ≤
      varianceBound / Fintype.card Particle := by
  rw [independentPopulation_particleAverage_mse]
  have hsum : (∑ i, finiteVariance (law i) score) ≤
      ∑ _i : Particle, varianceBound :=
    Finset.sum_le_sum fun i _ => hvariance i
  calc
    (∑ i, finiteVariance (law i) score) /
          (Fintype.card Particle : ℝ) ^ 2 ≤
        (∑ _i : Particle, varianceBound) /
          (Fintype.card Particle : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = varianceBound / Fintype.card Particle := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp

/-- Conditional MSE for a particle-count-indexed heterogeneous population. -/
noncomputable def independentPopulationMSEByExtra
    (law : ∀ extra : ℕ, Fin (extra + 1) → Distribution Sample)
    (score : Sample → ℝ) (extra : ℕ) : ℝ :=
  ∑ samples : Fin (extra + 1) → Sample,
    (independentPopulation (law extra)).mass samples *
      (particleAverage score samples -
        independentPopulationMean (law extra) score) ^ 2

omit [DecidableEq Sample] [Nonempty Particle] in
/-- A uniformly variance-bounded triangular array of independent finite
particles is mean-square consistent around its count-specific mean. -/
theorem independentPopulationMSEByExtra_tendsto_zero
    (law : ∀ extra : ℕ, Fin (extra + 1) → Distribution Sample)
    (score : Sample → ℝ) {varianceBound : ℝ}
    (hvariance : ∀ extra i,
      finiteVariance (law extra i) score ≤ varianceBound) :
    Filter.Tendsto (independentPopulationMSEByExtra law score)
      Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto
      (fun extra : ℕ => varianceBound / ((extra : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1
        tendsto_natCast_atTop_atTop)
  apply squeeze_zero
    (g := fun extra : ℕ => varianceBound / ((extra : ℝ) + 1))
  · intro extra
    unfold independentPopulationMSEByExtra
    apply Finset.sum_nonneg
    intro samples _
    exact mul_nonneg ((independentPopulation (law extra)).nonneg samples)
      (sq_nonneg _)
  · intro extra
    unfold independentPopulationMSEByExtra
    simpa using independentPopulation_particleAverage_mse_le
      (law extra) score (hvariance extra)
  · exact hupper

/-- Count-indexed deviation probability for a heterogeneous independent
population, centered at its own average coordinate expectation. -/
noncomputable def independentPopulationDeviationProbability
    (law : ∀ extra : ℕ, Fin (extra + 1) → Distribution Sample)
    (score : Sample → ℝ) (extra : ℕ) (tolerance : ℝ) : ℝ :=
  ∑ samples : Fin (extra + 1) → Sample,
    (independentPopulation (law extra)).mass samples *
      if tolerance ≤ |particleAverage score samples -
          independentPopulationMean (law extra) score|
      then 1 else 0

omit [DecidableEq Sample] [Nonempty Particle] in
theorem independentPopulationDeviationProbability_nonneg
    (law : ∀ extra : ℕ, Fin (extra + 1) → Distribution Sample)
    (score : Sample → ℝ) (extra : ℕ) (tolerance : ℝ) :
    0 ≤ independentPopulationDeviationProbability law score extra tolerance := by
  unfold independentPopulationDeviationProbability
  apply Finset.sum_nonneg
  intro samples _
  split
  · simpa using (independentPopulation (law extra)).nonneg samples
  · simp

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Finite conditional Chebyshev bound for a heterogeneous population. -/
theorem independentPopulationDeviationProbability_le
    (law : ∀ extra : ℕ, Fin (extra + 1) → Distribution Sample)
    (score : Sample → ℝ) (extra : ℕ) {tolerance varianceBound : ℝ}
    (htolerance : 0 < tolerance)
    (hvariance : ∀ i, finiteVariance (law extra i) score ≤ varianceBound) :
    independentPopulationDeviationProbability law score extra tolerance ≤
      varianceBound / ((extra + 1 : ℕ) : ℝ) / tolerance ^ 2 := by
  unfold independentPopulationDeviationProbability
  calc
    _ ≤ ∑ samples : Fin (extra + 1) → Sample,
        (independentPopulation (law extra)).mass samples *
          (particleAverage score samples -
            independentPopulationMean (law extra) score) ^ 2 /
              tolerance ^ 2 := by
      apply Finset.sum_le_sum
      intro samples _
      by_cases hbad : tolerance ≤ |particleAverage score samples -
          independentPopulationMean (law extra) score|
      · simp only [hbad, if_true]
        have hsquare : tolerance ^ 2 ≤
            (particleAverage score samples -
              independentPopulationMean (law extra) score) ^ 2 := by
          nlinarith [sq_nonneg
            (|particleAverage score samples -
                independentPopulationMean (law extra) score| - tolerance),
            sq_abs (particleAverage score samples -
              independentPopulationMean (law extra) score)]
        have hmass := (independentPopulation (law extra)).nonneg samples
        rw [le_div_iff₀ (sq_pos_of_pos htolerance)]
        nlinarith
      · simp only [hbad, if_false, mul_zero]
        exact div_nonneg
          (mul_nonneg ((independentPopulation (law extra)).nonneg samples)
            (sq_nonneg _))
          (sq_nonneg _)
    _ = independentPopulationMSEByExtra law score extra / tolerance ^ 2 := by
      unfold independentPopulationMSEByExtra
      rw [Finset.sum_div]
    _ ≤ _ := by
      gcongr
      unfold independentPopulationMSEByExtra
      simpa using independentPopulation_particleAverage_mse_le
        (law extra) score hvariance

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Uniformly variance-bounded heterogeneous finite populations converge in
probability around their count-specific coordinate-mean averages. -/
theorem independentPopulationDeviationProbability_tendsto_zero
    (law : ∀ extra : ℕ, Fin (extra + 1) → Distribution Sample)
    (score : Sample → ℝ) {tolerance varianceBound : ℝ}
    (htolerance : 0 < tolerance)
    (hvariance : ∀ extra i,
      finiteVariance (law extra i) score ≤ varianceBound) :
    Filter.Tendsto (fun extra =>
      independentPopulationDeviationProbability law score extra tolerance)
      Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto
      (fun extra : ℕ => varianceBound / ((extra : ℝ) + 1) / tolerance ^ 2)
      Filter.atTop (nhds 0) := by
    have hratio : Filter.Tendsto
        (fun extra : ℕ => varianceBound / ((extra : ℝ) + 1))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop)
    simpa using hratio.div_const (tolerance ^ 2)
  apply squeeze_zero
    (g := fun extra : ℕ => varianceBound / ((extra : ℝ) + 1) / tolerance ^ 2)
  · exact fun extra =>
      independentPopulationDeviationProbability_nonneg law score extra tolerance
  · intro extra
    simpa using independentPopulationDeviationProbability_le law score extra
      htolerance (hvariance extra)
  · exact hupper

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

/-- Mean-square error indexed by `extra + 1` iid particles, so every index
has a nonempty particle type. -/
noncomputable def iidParticleAverageMSEByExtra
    (law : Distribution Sample) (score : Sample → ℝ) (extra : ℕ) : ℝ :=
  ∑ samples : Fin (extra + 1) → Sample,
    (iidPopulation law).mass samples *
      (particleAverage score samples - finiteExpectation law score) ^ 2

omit [DecidableEq Sample] [Nonempty Particle] in
theorem iidParticleAverageMSEByExtra_eq
    (law : Distribution Sample) (score : Sample → ℝ) (extra : ℕ) :
    iidParticleAverageMSEByExtra law score extra =
      finiteVariance law score / (extra + 1) := by
  unfold iidParticleAverageMSEByExtra
  rw [iidPopulation_particleAverage_mse]
  simp

omit [DecidableEq Sample] [Nonempty Particle] in
/-- The iid empirical average is mean-square consistent as the explicit
particle count tends to infinity. -/
theorem iidParticleAverageMSEByExtra_tendsto_zero
    (law : Distribution Sample) (score : Sample → ℝ) :
    Filter.Tendsto (iidParticleAverageMSEByExtra law score)
      Filter.atTop (nhds 0) := by
  have hden : Filter.Tendsto (fun extra : ℕ => (extra : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_natCast_atTop_atTop
  have hratio : Filter.Tendsto
      (fun extra : ℕ => finiteVariance law score / ((extra : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  apply hratio.congr'
  filter_upwards [] with extra
  rw [iidParticleAverageMSEByExtra_eq]

/-- Exact finite probability that the iid particle average deviates from its
expectation by at least `tolerance`. -/
noncomputable def iidParticleDeviationProbability
    (law : Distribution Sample) (score : Sample → ℝ)
    (extra : ℕ) (tolerance : ℝ) : ℝ :=
  ∑ samples : Fin (extra + 1) → Sample,
    (iidPopulation law).mass samples *
      if tolerance ≤
          |particleAverage score samples - finiteExpectation law score|
      then 1 else 0

omit [DecidableEq Sample] [Nonempty Particle] in
theorem iidParticleDeviationProbability_nonneg
    (law : Distribution Sample) (score : Sample → ℝ)
    (extra : ℕ) (tolerance : ℝ) :
    0 ≤ iidParticleDeviationProbability law score extra tolerance := by
  unfold iidParticleDeviationProbability
  apply Finset.sum_nonneg
  intro samples _
  split
  · simpa using (iidPopulation law).nonneg samples
  · simp

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Finite Chebyshev bound derived from the exact particle-average MSE. -/
theorem iidParticleDeviationProbability_le
    (law : Distribution Sample) (score : Sample → ℝ)
    (extra : ℕ) {tolerance : ℝ} (htolerance : 0 < tolerance) :
    iidParticleDeviationProbability law score extra tolerance ≤
      finiteVariance law score / ((extra + 1 : ℕ) : ℝ) /
        tolerance ^ 2 := by
  unfold iidParticleDeviationProbability
  calc
    _ ≤ ∑ samples : Fin (extra + 1) → Sample,
        (iidPopulation law).mass samples *
          (particleAverage score samples - finiteExpectation law score) ^ 2 /
            tolerance ^ 2 := by
      apply Finset.sum_le_sum
      intro samples _
      by_cases hbad : tolerance ≤
          |particleAverage score samples - finiteExpectation law score|
      · simp only [hbad, if_true]
        have hsquare : tolerance ^ 2 ≤
            (particleAverage score samples - finiteExpectation law score) ^ 2 := by
          nlinarith [sq_nonneg
            (|particleAverage score samples - finiteExpectation law score| -
              tolerance), sq_abs
            (particleAverage score samples - finiteExpectation law score)]
        have hmass := (iidPopulation law).nonneg samples
        rw [le_div_iff₀ (sq_pos_of_pos htolerance)]
        nlinarith
      · simp only [hbad, if_false, mul_zero]
        exact div_nonneg
          (mul_nonneg ((iidPopulation law).nonneg samples) (sq_nonneg _))
          (sq_nonneg _)
    _ = iidParticleAverageMSEByExtra law score extra / tolerance ^ 2 := by
      unfold iidParticleAverageMSEByExtra
      rw [Finset.sum_div]
    _ = _ := by
      rw [iidParticleAverageMSEByExtra_eq]
      norm_num

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Count-indexed convergence in probability of the finite iid particle
average. -/
theorem iidParticleDeviationProbability_tendsto_zero
    (law : Distribution Sample) (score : Sample → ℝ)
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    Filter.Tendsto
      (fun extra => iidParticleDeviationProbability law score extra tolerance)
      Filter.atTop (nhds 0) := by
  have hupper : Filter.Tendsto
      (fun extra => iidParticleAverageMSEByExtra law score extra / tolerance ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using (iidParticleAverageMSEByExtra_tendsto_zero law score).div_const
      (tolerance ^ 2)
  apply squeeze_zero
    (g := fun extra => iidParticleAverageMSEByExtra law score extra /
      tolerance ^ 2)
  · exact fun extra =>
      iidParticleDeviationProbability_nonneg law score extra tolerance
  · intro extra
    convert iidParticleDeviationProbability_le law score extra htolerance using 1
    rw [iidParticleAverageMSEByExtra_eq]
    norm_num
  · exact hupper

end Mcmc.Finite.ParticleEstimator
