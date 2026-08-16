import Mcmc.Finite.ParticleEstimator
import Mcmc.Finite.Dynamics
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

/-- Finite expectation under a bind is the iterated finite expectation. -/
theorem finiteExpectation_bind
    {Outer Inner : Type*} [Fintype Outer] [Fintype Inner]
    (law : Distribution Outer) (next : Outer → Distribution Inner)
    (score : Inner → ℝ) :
    finiteExpectation (Distribution.bind law next) score =
      ∑ x, law.mass x * finiteExpectation (next x) score := by
  unfold finiteExpectation
  simp only [Distribution.bind_mass]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  simp only [mul_assoc]

/-- Every finite probability distribution gives positive mass to some state. -/
theorem distribution_exists_mass_pos
    {State : Type*} [Fintype State] (law : Distribution State) :
    ∃ x, 0 < law.mass x := by
  by_contra h
  push Not at h
  have hzero : ∀ x, law.mass x = 0 := fun x =>
    le_antisymm (h x) (law.nonneg x)
  have : ∑ x, law.mass x = 0 := by simp [hzero]
  linarith [law.sum_mass]

/-- A strictly positive score has strictly positive finite expectation under
every finite probability law. -/
theorem finiteExpectation_pos
    {State : Type*} [Fintype State]
    (law : Distribution State) (score : State → ℝ)
    (hscore : ∀ x, 0 < score x) :
    0 < finiteExpectation law score := by
  obtain ⟨x, hx⟩ := distribution_exists_mass_pos law
  unfold finiteExpectation
  exact (mul_pos hx (hscore x)).trans_le
    (Finset.single_le_sum
      (fun y _ => mul_nonneg (law.nonneg y) (hscore y).le)
      (Finset.mem_univ x))

/-- Minimum of a real function on a nonempty finite type. -/
noncomputable def finiteFunctionMinimum
    {State : Type*} [Fintype State] [Nonempty State] (score : State → ℝ) : ℝ :=
  (Finset.univ.image score).min' (Finset.univ_nonempty.image score)

theorem finiteFunctionMinimum_le
    {State : Type*} [Fintype State] [Nonempty State]
    (score : State → ℝ) (x : State) :
    finiteFunctionMinimum score ≤ score x := by
  unfold finiteFunctionMinimum
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

theorem finiteFunctionMinimum_pos
    {State : Type*} [Fintype State] [Nonempty State]
    (score : State → ℝ) (hscore : ∀ x, 0 < score x) :
    0 < finiteFunctionMinimum score := by
  unfold finiteFunctionMinimum
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp
    ((Finset.univ.image score).min'_mem (Finset.univ_nonempty.image score))
  rw [← hx]
  exact hscore x

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- Every empirical average is at least the finite minimum of its score. -/
theorem finiteFunctionMinimum_le_particleAverage
    [Nonempty Sample] (score : Sample → ℝ) (particles : Particle → Sample) :
    finiteFunctionMinimum score ≤ particleAverage score particles := by
  unfold particleAverage
  have hcard : (0 : ℝ) < Fintype.card Particle := by positivity
  rw [le_div_iff₀ hcard]
  calc
    finiteFunctionMinimum score * Fintype.card Particle =
        ∑ _i : Particle, finiteFunctionMinimum score := by
          simp [mul_comm]
    _ ≤ ∑ i, score (particles i) :=
      Finset.sum_le_sum fun i _ => finiteFunctionMinimum_le score (particles i)

/-- Maximum absolute value of a real function on a nonempty finite type. -/
noncomputable def finiteFunctionAbsMaximum
    {State : Type*} [Fintype State] [Nonempty State] (score : State → ℝ) : ℝ :=
  (Finset.univ.image fun x => |score x|).max'
    (Finset.univ_nonempty.image fun x => |score x|)

theorem abs_le_finiteFunctionAbsMaximum
    {State : Type*} [Fintype State] [Nonempty State]
    (score : State → ℝ) (x : State) :
    |score x| ≤ finiteFunctionAbsMaximum score := by
  unfold finiteFunctionAbsMaximum
  have hmem : |score x| ∈
      (Finset.univ.image fun y : State => |score y|) :=
    Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  exact Finset.le_max' _ _ hmem

theorem finiteFunctionAbsMaximum_nonneg
    {State : Type*} [Fintype State] [Nonempty State]
    (score : State → ℝ) : 0 ≤ finiteFunctionAbsMaximum score :=
  (abs_nonneg (score (Classical.choice ‹Nonempty State›))).trans
    (abs_le_finiteFunctionAbsMaximum score _)

/-- Expectation of a finite observable is bounded by its finite sup norm. -/
theorem abs_finiteExpectation_le
    {State : Type*} [Fintype State] [Nonempty State]
    (law : Distribution State) (score : State → ℝ) :
    |finiteExpectation law score| ≤ finiteFunctionAbsMaximum score := by
  unfold finiteExpectation
  calc
    |∑ x, law.mass x * score x| ≤ ∑ x, |law.mass x * score x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, law.mass x * |score x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (law.nonneg x)]
    _ ≤ ∑ x, law.mass x * finiteFunctionAbsMaximum score := by
      exact Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (abs_le_finiteFunctionAbsMaximum score x)
          (law.nonneg x)
    _ = finiteFunctionAbsMaximum score := by
      rw [← Finset.sum_mul, law.sum_mass, one_mul]

/-- Centered second moment of one particle. -/
noncomputable def finiteVariance (law : Distribution Sample)
    (score : Sample → ℝ) : ℝ :=
  ∑ x, law.mass x * (score x - finiteExpectation law score) ^ 2

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Uniform finite-state variance bound in terms of the observable sup norm. -/
theorem finiteVariance_le_four_mul_absMaximum_sq
    [Nonempty Sample] (law : Distribution Sample) (score : Sample → ℝ) :
    finiteVariance law score ≤ 4 * finiteFunctionAbsMaximum score ^ 2 := by
  let bound := finiteFunctionAbsMaximum score
  have hbound0 : 0 ≤ bound := finiteFunctionAbsMaximum_nonneg score
  have hmean : |finiteExpectation law score| ≤ bound :=
    abs_finiteExpectation_le law score
  have hpoint (x : Sample) :
      (score x - finiteExpectation law score) ^ 2 ≤ 4 * bound ^ 2 := by
    have hdev : |score x - finiteExpectation law score| ≤ 2 * bound := by
      calc
        |score x - finiteExpectation law score| ≤
            |score x| + |finiteExpectation law score| := abs_sub _ _
        _ ≤ bound + bound := add_le_add
          (abs_le_finiteFunctionAbsMaximum score x) hmean
        _ = 2 * bound := by ring
    have habs0 : 0 ≤ |score x - finiteExpectation law score| := abs_nonneg _
    rw [← sq_abs]
    nlinarith
  unfold finiteVariance
  calc
    _ ≤ ∑ x, law.mass x * (4 * bound ^ 2) := by
      exact Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hpoint x) (law.nonneg x)
    _ = 4 * bound ^ 2 := by
      rw [← Finset.sum_mul, law.sum_mass, one_mul]

omit [DecidableEq Sample] [Nonempty Particle] in
theorem abs_finiteExpectation_le_of_abs_le
    (law : Distribution Sample) (score : Sample → ℝ) {bound : ℝ}
    (hbound : ∀ x, |score x| ≤ bound) :
    |finiteExpectation law score| ≤ bound := by
  unfold finiteExpectation
  calc
    |∑ x, law.mass x * score x| ≤ ∑ x, |law.mass x * score x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, law.mass x * |score x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (law.nonneg x)]
    _ ≤ ∑ x, law.mass x * bound :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hbound x) (law.nonneg x)
    _ = bound := by rw [← Finset.sum_mul, law.sum_mass, one_mul]

omit [DecidableEq Sample] [Nonempty Particle] in
theorem finiteVariance_le_of_abs_le
    (law : Distribution Sample) (score : Sample → ℝ) {bound : ℝ}
    (hbound0 : 0 ≤ bound) (hbound : ∀ x, |score x| ≤ bound) :
    finiteVariance law score ≤ 4 * bound ^ 2 := by
  have hmean := abs_finiteExpectation_le_of_abs_le law score hbound
  have hpoint (x : Sample) :
      (score x - finiteExpectation law score) ^ 2 ≤ 4 * bound ^ 2 := by
    have hdev : |score x - finiteExpectation law score| ≤ 2 * bound := by
      calc
        |score x - finiteExpectation law score| ≤
            |score x| + |finiteExpectation law score| := abs_sub _ _
        _ ≤ bound + bound := add_le_add (hbound x) hmean
        _ = 2 * bound := by ring
    have habs0 : 0 ≤ |score x - finiteExpectation law score| := abs_nonneg _
    rw [← sq_abs]
    nlinarith
  unfold finiteVariance
  calc
    _ ≤ ∑ x, law.mass x * (4 * bound ^ 2) :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (hpoint x) (law.nonneg x)
    _ = 4 * bound ^ 2 := by
      rw [← Finset.sum_mul, law.sum_mass, one_mul]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Bias--variance decomposition for an arbitrary finite distribution. -/
theorem finite_sq_error_eq_variance_add_bias
    (law : Distribution Sample) (score : Sample → ℝ) (reference : ℝ) :
    ∑ x, law.mass x * (score x - reference) ^ 2 =
      finiteVariance law score +
        (finiteExpectation law score - reference) ^ 2 := by
  let mean := finiteExpectation law score
  have hcenter : ∑ x, law.mass x * (score x - mean) = 0 := by
    calc
      ∑ x, law.mass x * (score x - mean) =
          (∑ x, law.mass x * score x) -
            ∑ x, law.mass x * mean := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
      _ = mean - mean := by
        rw [show (∑ x, law.mass x * score x) = mean by rfl]
        rw [← Finset.sum_mul, law.sum_mass, one_mul]
      _ = 0 := sub_self mean
  change ∑ x, law.mass x * (score x - reference) ^ 2 =
    (∑ x, law.mass x * (score x - mean) ^ 2) + (mean - reference) ^ 2
  have hcross :
      (∑ x, law.mass x * (2 * (score x - mean) * (mean - reference))) =
        2 * (mean - reference) *
          (∑ x, law.mass x * (score x - mean)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hconstant :
      (∑ x, law.mass x * (mean - reference) ^ 2) =
        (mean - reference) ^ 2 * (∑ x, law.mass x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    ∑ x, law.mass x * (score x - reference) ^ 2 =
      ∑ x, law.mass x *
        ((score x - mean) ^ 2 +
          2 * (score x - mean) * (mean - reference) +
          (mean - reference) ^ 2) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = (∑ x, law.mass x * (score x - mean) ^ 2) +
        2 * (mean - reference) *
          (∑ x, law.mass x * (score x - mean)) +
        (mean - reference) ^ 2 * (∑ x, law.mass x) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [hcross, hconstant]
    _ = _ := by rw [hcenter, law.sum_mass]; ring

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
/-- Joint law of multinomial ancestors and the subsequently propagated
population for one bootstrap particle-filter stage. -/
noncomputable def resamplePropagateLaw
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) :
    Distribution ((Particle → Particle) × (Particle → Sample)) where
  mass outcome := (multinomialResampling weights).mass outcome.1 *
    (propagatedPopulation transition particles outcome.1).mass outcome.2
  nonneg outcome := mul_nonneg
    ((multinomialResampling weights).nonneg outcome.1)
    ((propagatedPopulation transition particles outcome.1).nonneg outcome.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,
      (propagatedPopulation transition particles _).sum_mass, mul_one]
    exact (multinomialResampling weights).sum_mass

/-- Marginal law of the next population after one bootstrap SMC stage. -/
noncomputable def bootstrapPopulationUpdate
    (step : FeynmanKacStep Sample) (particles : Particle → Sample) :
    Distribution (Particle → Sample) :=
  Distribution.bind
    (multinomialResampling
      (normalizedPotentialWeights step.potential step.potential_pos particles))
    (propagatedPopulation step.transition particles)

/-- Run a finite time-inhomogeneous bootstrap schedule from an arbitrary
incoming population law. -/
noncomputable def bootstrapPopulationLawFrom
    (current : Distribution (Particle → Sample)) :
    List (FeynmanKacStep Sample) → Distribution (Particle → Sample)
  | [] => current
  | step :: steps =>
      bootstrapPopulationLawFrom
        (Distribution.bind current (bootstrapPopulationUpdate step)) steps

/-- Population law of the actual bootstrap particle filter initialized iid. -/
noncomputable def bootstrapPopulationLaw
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample)) :
    Distribution (Particle → Sample) :=
  bootstrapPopulationLawFrom (iidPopulation (Particle := Particle) initial) steps

/-- Normalize a strictly positive potential against a finite probability law. -/
noncomputable def potentialReweight
    (law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) : Distribution Sample where
  mass x := law.mass x * potential x / finiteExpectation law potential
  nonneg x := div_nonneg (mul_nonneg (law.nonneg x) (hpotential x).le)
    (finiteExpectation_pos law potential hpotential).le
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (finiteExpectation_pos law potential hpotential))

/-- Exact normalized one-particle Feynman--Kac update corresponding to one
bootstrap particle stage. -/
noncomputable def bootstrapTargetUpdate
    (law : Distribution Sample) (step : FeynmanKacStep Sample) :
    Distribution Sample :=
  (potentialReweight law step.potential step.potential_pos).evolve step.transition

/-- Exact normalized filtering law after a finite time-inhomogeneous schedule. -/
noncomputable def bootstrapTargetLawFrom
    (current : Distribution Sample) :
    List (FeynmanKacStep Sample) → Distribution Sample
  | [] => current
  | step :: steps =>
      bootstrapTargetLawFrom (bootstrapTargetUpdate current step) steps

noncomputable def bootstrapTargetLaw
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample)) :
    Distribution Sample :=
  bootstrapTargetLawFrom initial steps

omit [DecidableEq Sample] in
/-- Reweighted expectation is the exact potential-weighted ratio. -/
theorem potentialReweight_expectation
    (law : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (score : Sample → ℝ) :
    finiteExpectation (potentialReweight law potential hpotential) score =
      finiteExpectation law (fun x => potential x * score x) /
        finiteExpectation law potential := by
  change (∑ x, (law.mass x * potential x /
      finiteExpectation law potential) * score x) =
    finiteExpectation law (fun x => potential x * score x) /
      finiteExpectation law potential
  calc
    _ = ∑ x, (law.mass x * (potential x * score x)) /
        finiteExpectation law potential := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = _ := by
      rw [← Finset.sum_div]
      rfl

omit [DecidableEq Sample] in
/-- Exact target expectation after one normalized Feynman--Kac update. -/
theorem bootstrapTargetUpdate_expectation
    (law : Distribution Sample) (step : FeynmanKacStep Sample)
    (score : Sample → ℝ) :
    finiteExpectation (bootstrapTargetUpdate law step) score =
      finiteExpectation law (fun x => step.potential x *
          finiteExpectation (rowDistribution step.transition x) score) /
        finiteExpectation law step.potential := by
  unfold bootstrapTargetUpdate
  unfold finiteExpectation
  simp only [MarkovKernel.Distribution.evolve_mass]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  change (∑ x,
      (potentialReweight law step.potential step.potential_pos).mass x *
        finiteExpectation (rowDistribution step.transition x) score) = _
  simpa [finiteExpectation] using
    potentialReweight_expectation law step.potential step.potential_pos
      (fun x => finiteExpectation (rowDistribution step.transition x) score)

omit [DecidableEq Sample] in
theorem bootstrapTargetLawFrom_append
    (current : Distribution Sample) (left right : List (FeynmanKacStep Sample)) :
    bootstrapTargetLawFrom current (left ++ right) =
      bootstrapTargetLawFrom (bootstrapTargetLawFrom current left) right := by
  induction left generalizing current with
  | nil => rfl
  | cons step left ih =>
      simp only [List.cons_append, bootstrapTargetLawFrom]
      exact ih (bootstrapTargetUpdate current step)

omit [DecidableEq Sample] in
theorem bootstrapTargetLaw_append_singleton
    (initial : Distribution Sample) (priorSteps : List (FeynmanKacStep Sample))
    (step : FeynmanKacStep Sample) :
    bootstrapTargetLaw initial (priorSteps ++ [step]) =
      bootstrapTargetUpdate (bootstrapTargetLaw initial priorSteps) step := by
  unfold bootstrapTargetLaw
  rw [bootstrapTargetLawFrom_append]
  rfl

omit [DecidableEq Sample] in
/-- The exact target expectation after appending one schedule stage is the
ratio used as the reference in the population MSE induction. -/
theorem bootstrapTargetLaw_append_singleton_expectation
    (initial : Distribution Sample) (priorSteps : List (FeynmanKacStep Sample))
    (step : FeynmanKacStep Sample) (score : Sample → ℝ) :
    finiteExpectation (bootstrapTargetLaw initial (priorSteps ++ [step])) score =
      finiteExpectation (bootstrapTargetLaw initial priorSteps)
          (fun x => step.potential x *
            finiteExpectation (rowDistribution step.transition x) score) /
        finiteExpectation (bootstrapTargetLaw initial priorSteps)
          step.potential := by
  rw [bootstrapTargetLaw_append_singleton]
  exact bootstrapTargetUpdate_expectation _ _ _

omit [DecidableEq Sample] in
@[simp] theorem bootstrapPopulationLawFrom_nil
    (current : Distribution (Particle → Sample)) :
    bootstrapPopulationLawFrom current [] = current := rfl

omit [DecidableEq Sample] in
@[simp] theorem bootstrapPopulationLawFrom_cons
    (current : Distribution (Particle → Sample))
    (step : FeynmanKacStep Sample) (steps : List (FeynmanKacStep Sample)) :
    bootstrapPopulationLawFrom current (step :: steps) =
      bootstrapPopulationLawFrom
        (Distribution.bind current (bootstrapPopulationUpdate step)) steps := rfl

omit [DecidableEq Sample] in
/-- Bootstrap schedule execution composes exactly across list concatenation. -/
theorem bootstrapPopulationLawFrom_append
    (current : Distribution (Particle → Sample))
    (left right : List (FeynmanKacStep Sample)) :
    bootstrapPopulationLawFrom current (left ++ right) =
      bootstrapPopulationLawFrom (bootstrapPopulationLawFrom current left) right := by
  induction left generalizing current with
  | nil => rfl
  | cons step left ih =>
      simp only [List.cons_append, bootstrapPopulationLawFrom_cons]
      exact ih (Distribution.bind current (bootstrapPopulationUpdate step))

omit [DecidableEq Sample] in
/-- Appending one stage evolves the preceding prefix population law by that
stage's bootstrap update. -/
theorem bootstrapPopulationLaw_append_singleton
    (initial : Distribution Sample) (priorSteps : List (FeynmanKacStep Sample))
    (step : FeynmanKacStep Sample) :
    bootstrapPopulationLaw (Particle := Particle) initial (priorSteps ++ [step]) =
      Distribution.bind (bootstrapPopulationLaw initial priorSteps)
        (bootstrapPopulationUpdate step) := by
  unfold bootstrapPopulationLaw
  rw [bootstrapPopulationLawFrom_append]
  rfl

omit [DecidableEq Sample] in
/-- The expectation of a next-population score unfolds to the exact nested
resample--propagate expectation used by the stage MSE theorem. -/
theorem bootstrapPopulationUpdate_expectation
    (step : FeynmanKacStep Sample) (particles : Particle → Sample)
    (score : (Particle → Sample) → ℝ) :
    finiteExpectation (bootstrapPopulationUpdate step particles) score =
      ∑ ancestors,
        (multinomialResampling
          (normalizedPotentialWeights step.potential step.potential_pos
            particles)).mass ancestors *
          finiteExpectation
            (propagatedPopulation step.transition particles ancestors) score := by
  unfold bootstrapPopulationUpdate
  exact finiteExpectation_bind _ _ score

omit [DecidableEq Sample] in
/-- The next-population marginal and the explicit joint ancestor/population
law give the same expectation for every population score. -/
theorem bootstrapPopulationUpdate_expectation_eq_joint
    (step : FeynmanKacStep Sample) (particles : Particle → Sample)
    (score : (Particle → Sample) → ℝ) :
    finiteExpectation (bootstrapPopulationUpdate step particles) score =
      finiteExpectation
        (resamplePropagateLaw
          (normalizedPotentialWeights step.potential step.potential_pos particles)
          particles step.transition)
        (fun outcome => score outcome.2) := by
  rw [bootstrapPopulationUpdate_expectation]
  unfold finiteExpectation resamplePropagateLaw
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  simp only [mul_assoc]

omit [DecidableEq Sample] in
/-- Appending one concrete bootstrap stage unfolds the MSE of its population
law to the integrated explicit stage law. -/
theorem bootstrapPopulationLaw_append_singleton_sq_error
    (initial : Distribution Sample) (priorSteps : List (FeynmanKacStep Sample))
    (step : FeynmanKacStep Sample) (score : Sample → ℝ) (reference : ℝ) :
    finiteExpectation
        (bootstrapPopulationLaw (Particle := Particle) initial
          (priorSteps ++ [step]))
        (fun particles => (particleAverage score particles - reference) ^ 2) =
      ∑ particles : Particle → Sample,
        (bootstrapPopulationLaw (Particle := Particle) initial priorSteps).mass particles *
        (∑ outcome : (Particle → Particle) × (Particle → Sample),
          (resamplePropagateLaw
            (normalizedPotentialWeights step.potential step.potential_pos particles)
            particles step.transition).mass outcome *
            (particleAverage score outcome.2 - reference) ^ 2) := by
  rw [bootstrapPopulationLaw_append_singleton]
  rw [finiteExpectation_bind]
  apply Finset.sum_congr rfl
  intro particles _
  rw [bootstrapPopulationUpdate_expectation_eq_joint]
  rfl

omit [DecidableEq Sample] in
/-- The one-step joint law has the normalized weighted transition mean. -/
theorem resamplePropagateLaw_particleAverage_expectation
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) (score : Sample → ℝ) :
    finiteExpectation (resamplePropagateLaw weights particles transition)
        (fun outcome => particleAverage score outcome.2) =
      finiteExpectation weights (fun i =>
        finiteExpectation (rowDistribution transition (particles i)) score) := by
  unfold finiteExpectation resamplePropagateLaw
  rw [Fintype.sum_prod_type]
  have h := resamplePropagate_particleAverage_expectation
    weights particles transition score
  simp_rw [Finset.mul_sum] at h
  simp_rw [Finset.mul_sum]
  simpa [rowDistribution, mul_assoc] using h

omit [DecidableEq Sample] in
/-- For bootstrap weights, the one-stage conditional mean is the explicit
self-normalized empirical Feynman--Kac ratio. -/
theorem resamplePropagateLaw_normalized_expectation
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (transition : MarkovKernel Sample)
    (score : Sample → ℝ) :
    finiteExpectation
        (resamplePropagateLaw
          (normalizedPotentialWeights potential hpotential particles)
          particles transition)
        (fun outcome => particleAverage score outcome.2) =
      particleAverage (fun x => potential x *
          finiteExpectation (rowDistribution transition x) score) particles /
        particleAverage potential particles := by
  rw [resamplePropagateLaw_particleAverage_expectation]
  unfold finiteExpectation
  exact finiteExpectation_normalizedPotentialWeights potential hpotential
    particles (fun x => finiteExpectation (rowDistribution transition x) score)

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
/-- Variance of the empirical average under the explicit joint one-stage law.
This packages the nested exact MSE identity as an ordinary finite-distribution
statement suitable for repeated bias--variance decomposition. -/
theorem resamplePropagateLaw_particleAverage_variance
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) (score : Sample → ℝ) :
    finiteVariance (resamplePropagateLaw weights particles transition)
        (fun outcome => particleAverage score outcome.2) =
      (finiteExpectation weights (fun i =>
          finiteVariance (rowDistribution transition (particles i)) score) +
        finiteVariance weights (fun i =>
          finiteExpectation (rowDistribution transition (particles i)) score)) /
        Fintype.card Particle := by
  unfold finiteVariance
  rw [resamplePropagateLaw_particleAverage_expectation]
  unfold resamplePropagateLaw
  rw [Fintype.sum_prod_type]
  have h := resamplePropagate_particleAverage_mse
    weights particles transition score
  simp_rw [Finset.mul_sum] at h
  simpa [finiteVariance, mul_assoc] using h

omit [DecidableEq Sample] in
/-- Exact one-stage error around an arbitrary deterministic reference: fresh
particle variance contributes `1/N`, while the squared error of the normalized
weighted transition mean is carried to the next stage. -/
theorem resamplePropagateLaw_particleAverage_sq_error
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) (score : Sample → ℝ) (reference : ℝ) :
    ∑ outcome,
        (resamplePropagateLaw weights particles transition).mass outcome *
          (particleAverage score outcome.2 - reference) ^ 2 =
      (finiteExpectation weights (fun i =>
          finiteVariance (rowDistribution transition (particles i)) score) +
        finiteVariance weights (fun i =>
          finiteExpectation (rowDistribution transition (particles i)) score)) /
          Fintype.card Particle +
        (finiteExpectation weights (fun i =>
          finiteExpectation (rowDistribution transition (particles i)) score) -
            reference) ^ 2 := by
  rw [finite_sq_error_eq_variance_add_bias]
  rw [resamplePropagateLaw_particleAverage_variance,
    resamplePropagateLaw_particleAverage_expectation]

omit [DecidableEq Sample] in
/-- Bootstrap specialization of the exact one-stage recurrence. The carried
bias is now visibly a self-normalized empirical ratio, ready for
`normalized_ratio_mse_le`; the remaining term is fresh `1/N` variance. -/
theorem bootstrapStage_particleAverage_sq_error
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (transition : MarkovKernel Sample)
    (score : Sample → ℝ) (reference : ℝ) :
    ∑ outcome,
        (resamplePropagateLaw
          (normalizedPotentialWeights potential hpotential particles)
          particles transition).mass outcome *
          (particleAverage score outcome.2 - reference) ^ 2 =
      (finiteExpectation
          (normalizedPotentialWeights potential hpotential particles)
          (fun i => finiteVariance
            (rowDistribution transition (particles i)) score) +
        finiteVariance
          (normalizedPotentialWeights potential hpotential particles)
          (fun i => finiteExpectation
            (rowDistribution transition (particles i)) score)) /
          Fintype.card Particle +
        (particleAverage (fun x => potential x *
            finiteExpectation (rowDistribution transition x) score) particles /
          particleAverage potential particles - reference) ^ 2 := by
  have hmean :
      finiteExpectation
          (normalizedPotentialWeights potential hpotential particles)
          (fun i => finiteExpectation
            (rowDistribution transition (particles i)) score) =
        particleAverage (fun x => potential x *
            finiteExpectation (rowDistribution transition x) score) particles /
          particleAverage potential particles := by
    unfold finiteExpectation
    exact finiteExpectation_normalizedPotentialWeights potential hpotential
      particles (fun x => finiteExpectation (rowDistribution transition x) score)
  rw [resamplePropagateLaw_particleAverage_sq_error]
  rw [hmean]

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- A universal finite-state bound for the fresh one-stage variance term. -/
theorem bootstrapStage_freshVariance_le
    [Nonempty Sample]
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (transition : MarkovKernel Sample)
    (score : Sample → ℝ) :
    finiteExpectation
        (normalizedPotentialWeights potential hpotential particles)
        (fun i => finiteVariance
          (rowDistribution transition (particles i)) score) +
      finiteVariance
        (normalizedPotentialWeights potential hpotential particles)
        (fun i => finiteExpectation
          (rowDistribution transition (particles i)) score) ≤
      8 * finiteFunctionAbsMaximum score ^ 2 := by
  let bound := finiteFunctionAbsMaximum score
  have hbound0 : 0 ≤ bound := finiteFunctionAbsMaximum_nonneg score
  have hrow (x : Sample) :
      finiteVariance (rowDistribution transition x) score ≤ 4 * bound ^ 2 :=
    finiteVariance_le_four_mul_absMaximum_sq _ _
  have hfirst :
      finiteExpectation
          (normalizedPotentialWeights potential hpotential particles)
          (fun i => finiteVariance
            (rowDistribution transition (particles i)) score) ≤
        4 * bound ^ 2 := by
    unfold finiteExpectation
    calc
      _ ≤ ∑ i,
          (normalizedPotentialWeights potential hpotential particles).mass i *
            (4 * bound ^ 2) := Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hrow (particles i))
                ((normalizedPotentialWeights potential hpotential particles).nonneg i)
      _ = 4 * bound ^ 2 := by
        rw [← Finset.sum_mul,
          (normalizedPotentialWeights potential hpotential particles).sum_mass,
          one_mul]
  have htransitionMean (i : Particle) :
      |finiteExpectation (rowDistribution transition (particles i)) score| ≤
        bound := abs_finiteExpectation_le _ _
  have hsecond :
      finiteVariance
          (normalizedPotentialWeights potential hpotential particles)
          (fun i => finiteExpectation
            (rowDistribution transition (particles i)) score) ≤
        4 * bound ^ 2 :=
    finiteVariance_le_of_abs_le _ _ hbound0 htransitionMean
  dsimp [bound] at hfirst hsecond ⊢
  linarith

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

section NormalizedWeightPerturbation

/-- Deterministic perturbation bound for a self-normalized particle estimate.
It separates numerator error from denominator error and makes the necessary
positive lower bound on the computed normalizer explicit.  This is the
nonlinear algebraic step needed when iterating the one-step particle MSE
identity through a normalized Feynman--Kac update. -/
theorem abs_normalized_ratio_sub_le
    {numerator approximateNumerator denominator approximateDenominator
      numeratorError denominatorError observableBound lower : ℝ}
    (hdenominator : denominator ≠ 0)
    (hlower : 0 < lower)
    (happroxDenominator : lower ≤ approximateDenominator)
    (hnumerator : |approximateNumerator - numerator| ≤ numeratorError)
    (hdenominatorError : |approximateDenominator - denominator| ≤
      denominatorError)
    (hobservable : |numerator / denominator| ≤ observableBound)
    (hnumeratorError : 0 ≤ numeratorError)
    (hdenominatorErrorNonneg : 0 ≤ denominatorError)
    (hobservableNonneg : 0 ≤ observableBound) :
    |approximateNumerator / approximateDenominator -
        numerator / denominator| ≤
      numeratorError / lower +
        observableBound * denominatorError / lower := by
  have happroxPos : 0 < approximateDenominator :=
    lt_of_lt_of_le hlower happroxDenominator
  have happroxNe : approximateDenominator ≠ 0 := ne_of_gt happroxPos
  have hsplit :
      approximateNumerator / approximateDenominator -
          numerator / denominator =
        (approximateNumerator - numerator) / approximateDenominator +
          (numerator / denominator) *
            ((denominator - approximateDenominator) /
              approximateDenominator) := by
    field_simp
    ring
  have hfirst :
      |(approximateNumerator - numerator) / approximateDenominator| ≤
        numeratorError / lower := by
    rw [abs_div, abs_of_pos happroxPos]
    exact div_le_div₀ hnumeratorError hnumerator hlower happroxDenominator
  have hnormalizer :
      |(denominator - approximateDenominator) /
          approximateDenominator| ≤ denominatorError / lower := by
    rw [abs_div, abs_of_pos happroxPos, abs_sub_comm]
    exact div_le_div₀ hdenominatorErrorNonneg hdenominatorError
      hlower happroxDenominator
  have hsecond :
      |(numerator / denominator) *
          ((denominator - approximateDenominator) /
            approximateDenominator)| ≤
        observableBound * denominatorError / lower := by
    rw [abs_mul]
    calc
      |numerator / denominator| *
          |(denominator - approximateDenominator) /
            approximateDenominator| ≤
        observableBound * (denominatorError / lower) :=
          mul_le_mul hobservable hnormalizer (abs_nonneg _) hobservableNonneg
      _ = observableBound * denominatorError / lower := by ring
  rw [hsplit]
  calc
    |(approximateNumerator - numerator) / approximateDenominator +
        (numerator / denominator) *
          ((denominator - approximateDenominator) /
            approximateDenominator)| ≤
      |(approximateNumerator - numerator) / approximateDenominator| +
        |(numerator / denominator) *
          ((denominator - approximateDenominator) /
            approximateDenominator)| := abs_add_le _ _
    _ ≤ numeratorError / lower +
        observableBound * denominatorError / lower := add_le_add hfirst hsecond

/-- Squared-error form of `abs_normalized_ratio_sub_le`. It is arranged for
direct integration against a finite particle law: numerator and denominator
mean-square errors enter additively, at the price of the standard factor two.
-/
theorem sq_normalized_ratio_sub_le
    {numerator approximateNumerator denominator approximateDenominator
      observableBound lower : ℝ}
    (hdenominator : denominator ≠ 0)
    (hlower : 0 < lower)
    (happroxDenominator : lower ≤ approximateDenominator)
    (hobservable : |numerator / denominator| ≤ observableBound)
    (hobservableNonneg : 0 ≤ observableBound) :
    (approximateNumerator / approximateDenominator -
        numerator / denominator) ^ 2 ≤
      2 * ((approximateNumerator - numerator) ^ 2 +
        observableBound ^ 2 *
          (approximateDenominator - denominator) ^ 2) / lower ^ 2 := by
  let x := |approximateNumerator - numerator| / lower
  let y := observableBound * |approximateDenominator - denominator| / lower
  have hbound :
      |approximateNumerator / approximateDenominator -
          numerator / denominator| ≤ x + y := by
    exact abs_normalized_ratio_sub_le hdenominator hlower happroxDenominator
      (le_refl _) (le_refl _) hobservable (abs_nonneg _) (abs_nonneg _)
      hobservableNonneg
  have hx : 0 ≤ x := div_nonneg (abs_nonneg _) hlower.le
  have hy : 0 ≤ y := by positivity
  have hsq :
      |approximateNumerator / approximateDenominator -
          numerator / denominator| ^ 2 ≤ (x + y) ^ 2 := by
    nlinarith [abs_nonneg (approximateNumerator / approximateDenominator -
      numerator / denominator)]
  have htwo : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x - y)]
  calc
    (approximateNumerator / approximateDenominator -
        numerator / denominator) ^ 2 =
      |approximateNumerator / approximateDenominator -
        numerator / denominator| ^ 2 := by rw [sq_abs]
    _ ≤ (x + y) ^ 2 := hsq
    _ ≤ 2 * (x ^ 2 + y ^ 2) := htwo
    _ = 2 * ((approximateNumerator - numerator) ^ 2 +
        observableBound ^ 2 *
          (approximateDenominator - denominator) ^ 2) / lower ^ 2 := by
      dsimp [x, y]
      field_simp [ne_of_gt hlower]
      all_goals simp only [sq_abs]

/-- Finite-law integration of the squared normalized-ratio bound. This turns
separate numerator and normalizer MSE estimates into the one-step nonlinear
MSE estimate needed by a full-horizon particle induction. -/
theorem normalized_ratio_mse_le
    {Approximation : Type*} [Fintype Approximation]
    (law : Distribution Approximation)
    (approximateNumerator approximateDenominator : Approximation → ℝ)
    {numerator denominator observableBound lower numeratorMSE denominatorMSE : ℝ}
    (hdenominator : denominator ≠ 0)
    (hlower : 0 < lower)
    (happroxDenominator : ∀ z, lower ≤ approximateDenominator z)
    (hobservable : |numerator / denominator| ≤ observableBound)
    (hobservableNonneg : 0 ≤ observableBound)
    (hnumeratorMSE :
      ∑ z, law.mass z * (approximateNumerator z - numerator) ^ 2 ≤ numeratorMSE)
    (hdenominatorMSE :
      ∑ z, law.mass z * (approximateDenominator z - denominator) ^ 2 ≤
        denominatorMSE) :
    ∑ z, law.mass z *
        (approximateNumerator z / approximateDenominator z -
          numerator / denominator) ^ 2 ≤
      2 * (numeratorMSE + observableBound ^ 2 * denominatorMSE) / lower ^ 2 := by
  calc
    ∑ z, law.mass z *
        (approximateNumerator z / approximateDenominator z -
          numerator / denominator) ^ 2 ≤
      ∑ z, law.mass z *
        (2 * ((approximateNumerator z - numerator) ^ 2 +
          observableBound ^ 2 *
            (approximateDenominator z - denominator) ^ 2) / lower ^ 2) := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left
        (sq_normalized_ratio_sub_le hdenominator hlower
          (happroxDenominator z) hobservable hobservableNonneg)
        (law.nonneg z)
    _ = 2 * ((∑ z, law.mass z *
          (approximateNumerator z - numerator) ^ 2) +
        observableBound ^ 2 * (∑ z, law.mass z *
          (approximateDenominator z - denominator) ^ 2)) / lower ^ 2 := by
      calc
        ∑ z, law.mass z *
            (2 * ((approximateNumerator z - numerator) ^ 2 +
              observableBound ^ 2 *
                (approximateDenominator z - denominator) ^ 2) / lower ^ 2) =
          ∑ z, (2 / lower ^ 2) *
            (law.mass z * (approximateNumerator z - numerator) ^ 2 +
              observableBound ^ 2 * law.mass z *
                (approximateDenominator z - denominator) ^ 2) := by
            apply Finset.sum_congr rfl
            intro z _
            ring
        _ = _ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring
    _ ≤ 2 * (numeratorMSE + observableBound ^ 2 * denominatorMSE) /
        lower ^ 2 := by
      have hlowerSq : 0 < lower ^ 2 := sq_pos_of_pos hlower
      gcongr

omit [DecidableEq Sample] in
/-- Integrated one-stage bootstrap MSE bound. It combines the exact fresh
`1/N` resample--propagate variance with the nonlinear normalized-ratio MSE of
the incoming population. -/
theorem bootstrapStage_mse_le
    (currentLaw : Distribution (Particle → Sample))
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample) (score : Sample → ℝ)
    {numerator denominator observableBound lower
      freshVariance numeratorMSE denominatorMSE : ℝ}
    (hdenominator : denominator ≠ 0)
    (hlower : 0 < lower)
    (hparticleLower : ∀ particles : Particle → Sample,
      lower ≤ particleAverage potential particles)
    (hobservable : |numerator / denominator| ≤ observableBound)
    (hobservableNonneg : 0 ≤ observableBound)
    (hfresh : ∀ particles : Particle → Sample,
      finiteExpectation
          (normalizedPotentialWeights potential hpotential particles)
          (fun i => finiteVariance
            (rowDistribution transition (particles i)) score) +
        finiteVariance
          (normalizedPotentialWeights potential hpotential particles)
          (fun i => finiteExpectation
            (rowDistribution transition (particles i)) score) ≤ freshVariance)
    (hnumeratorMSE :
      ∑ particles, currentLaw.mass particles *
        (particleAverage (fun x => potential x *
            finiteExpectation (rowDistribution transition x) score) particles -
          numerator) ^ 2 ≤ numeratorMSE)
    (hdenominatorMSE :
      ∑ particles, currentLaw.mass particles *
        (particleAverage potential particles - denominator) ^ 2 ≤
          denominatorMSE) :
    ∑ particles, currentLaw.mass particles *
        (∑ outcome,
          (resamplePropagateLaw
            (normalizedPotentialWeights potential hpotential particles)
            particles transition).mass outcome *
            (particleAverage score outcome.2 - numerator / denominator) ^ 2) ≤
      freshVariance / Fintype.card Particle +
        2 * (numeratorMSE + observableBound ^ 2 * denominatorMSE) /
          lower ^ 2 := by
  let approximateNumerator : (Particle → Sample) → ℝ := fun particles =>
    particleAverage (fun x => potential x *
      finiteExpectation (rowDistribution transition x) score) particles
  let approximateDenominator : (Particle → Sample) → ℝ := fun particles =>
    particleAverage potential particles
  have hratio := normalized_ratio_mse_le currentLaw approximateNumerator
    approximateDenominator hdenominator hlower hparticleLower hobservable
    hobservableNonneg hnumeratorMSE hdenominatorMSE
  have hfreshMean :
      ∑ particles, currentLaw.mass particles *
        (finiteExpectation
            (normalizedPotentialWeights potential hpotential particles)
            (fun i => finiteVariance
              (rowDistribution transition (particles i)) score) +
          finiteVariance
            (normalizedPotentialWeights potential hpotential particles)
            (fun i => finiteExpectation
              (rowDistribution transition (particles i)) score)) ≤
        freshVariance := by
    calc
      _ ≤ ∑ particles, currentLaw.mass particles * freshVariance := by
        apply Finset.sum_le_sum
        intro particles _
        exact mul_le_mul_of_nonneg_left (hfresh particles)
          (currentLaw.nonneg particles)
      _ = freshVariance := by
        rw [← Finset.sum_mul, currentLaw.sum_mass, one_mul]
  calc
    ∑ particles, currentLaw.mass particles *
        (∑ outcome,
          (resamplePropagateLaw
            (normalizedPotentialWeights potential hpotential particles)
            particles transition).mass outcome *
            (particleAverage score outcome.2 - numerator / denominator) ^ 2) =
      ∑ particles, currentLaw.mass particles *
        (((finiteExpectation
              (normalizedPotentialWeights potential hpotential particles)
              (fun i => finiteVariance
                (rowDistribution transition (particles i)) score) +
            finiteVariance
              (normalizedPotentialWeights potential hpotential particles)
              (fun i => finiteExpectation
                (rowDistribution transition (particles i)) score)) /
              Fintype.card Particle) +
          (approximateNumerator particles / approximateDenominator particles -
            numerator / denominator) ^ 2) := by
              apply Finset.sum_congr rfl
              intro particles _
              rw [bootstrapStage_particleAverage_sq_error]
    _ = (∑ particles, currentLaw.mass particles *
          (finiteExpectation
              (normalizedPotentialWeights potential hpotential particles)
              (fun i => finiteVariance
                (rowDistribution transition (particles i)) score) +
            finiteVariance
              (normalizedPotentialWeights potential hpotential particles)
              (fun i => finiteExpectation
                (rowDistribution transition (particles i)) score))) /
            Fintype.card Particle +
        ∑ particles, currentLaw.mass particles *
          (approximateNumerator particles / approximateDenominator particles -
            numerator / denominator) ^ 2 := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib, Finset.sum_div]
              apply congrArg₂ (· + ·) ?_ rfl
              apply Finset.sum_congr rfl
              intro particles _
              ring
    _ ≤ freshVariance / Fintype.card Particle +
        2 * (numeratorMSE + observableBound ^ 2 * denominatorMSE) /
          lower ^ 2 := add_le_add
            (div_le_div_of_nonneg_right hfreshMean (by positivity)) hratio

omit [DecidableEq Sample] in
/-- Concrete prefix-law corollary of `bootstrapStage_mse_le`. This is the
induction step for the actual recursively generated bootstrap SMC process. -/
theorem bootstrapPopulationLaw_append_singleton_mse_le
    (initial : Distribution Sample) (priorSteps : List (FeynmanKacStep Sample))
    (step : FeynmanKacStep Sample) (score : Sample → ℝ)
    {numerator denominator observableBound lower
      freshVariance numeratorMSE denominatorMSE : ℝ}
    (hdenominator : denominator ≠ 0)
    (hlower : 0 < lower)
    (hparticleLower : ∀ particles : Particle → Sample,
      lower ≤ particleAverage step.potential particles)
    (hobservable : |numerator / denominator| ≤ observableBound)
    (hobservableNonneg : 0 ≤ observableBound)
    (hfresh : ∀ particles : Particle → Sample,
      finiteExpectation
          (normalizedPotentialWeights step.potential step.potential_pos particles)
          (fun i => finiteVariance
            (rowDistribution step.transition (particles i)) score) +
        finiteVariance
          (normalizedPotentialWeights step.potential step.potential_pos particles)
          (fun i => finiteExpectation
            (rowDistribution step.transition (particles i)) score) ≤ freshVariance)
    (hnumeratorMSE :
      ∑ particles,
        (bootstrapPopulationLaw (Particle := Particle) initial priorSteps).mass
            particles *
          (particleAverage (fun x => step.potential x *
              finiteExpectation (rowDistribution step.transition x) score)
              particles - numerator) ^ 2 ≤ numeratorMSE)
    (hdenominatorMSE :
      ∑ particles,
        (bootstrapPopulationLaw (Particle := Particle) initial priorSteps).mass
            particles *
          (particleAverage step.potential particles - denominator) ^ 2 ≤
        denominatorMSE) :
    finiteExpectation
        (bootstrapPopulationLaw (Particle := Particle) initial
          (priorSteps ++ [step]))
        (fun particles =>
          (particleAverage score particles - numerator / denominator) ^ 2) ≤
      freshVariance / Fintype.card Particle +
        2 * (numeratorMSE + observableBound ^ 2 * denominatorMSE) /
          lower ^ 2 := by
  rw [bootstrapPopulationLaw_append_singleton_sq_error]
  exact bootstrapStage_mse_le
    (bootstrapPopulationLaw (Particle := Particle) initial priorSteps)
    step.potential step.potential_pos step.transition score hdenominator hlower
    hparticleLower hobservable hobservableNonneg hfresh hnumeratorMSE
    hdenominatorMSE

omit [DecidableEq Sample] in
/-- Induction step centered at the actual normalized Feynman--Kac target law.
The two incoming MSE premises are precisely the induction hypotheses for the
weighted transition score and for the potential. -/
theorem bootstrapPopulationLaw_append_singleton_target_mse_le
    (initial : Distribution Sample) (priorSteps : List (FeynmanKacStep Sample))
    (step : FeynmanKacStep Sample) (score : Sample → ℝ)
    {observableBound lower freshVariance numeratorMSE denominatorMSE : ℝ}
    (hlower : 0 < lower)
    (hparticleLower : ∀ particles : Particle → Sample,
      lower ≤ particleAverage step.potential particles)
    (hobservable :
      |finiteExpectation (bootstrapTargetLaw initial (priorSteps ++ [step]))
          score| ≤ observableBound)
    (hobservableNonneg : 0 ≤ observableBound)
    (hfresh : ∀ particles : Particle → Sample,
      finiteExpectation
          (normalizedPotentialWeights step.potential step.potential_pos particles)
          (fun i => finiteVariance
            (rowDistribution step.transition (particles i)) score) +
        finiteVariance
          (normalizedPotentialWeights step.potential step.potential_pos particles)
          (fun i => finiteExpectation
            (rowDistribution step.transition (particles i)) score) ≤ freshVariance)
    (hnumeratorMSE :
      ∑ particles,
        (bootstrapPopulationLaw (Particle := Particle) initial priorSteps).mass
            particles *
          (particleAverage (fun x => step.potential x *
              finiteExpectation (rowDistribution step.transition x) score)
              particles -
            finiteExpectation (bootstrapTargetLaw initial priorSteps)
              (fun x => step.potential x *
                finiteExpectation (rowDistribution step.transition x) score)) ^ 2 ≤
        numeratorMSE)
    (hdenominatorMSE :
      ∑ particles,
        (bootstrapPopulationLaw (Particle := Particle) initial priorSteps).mass
            particles *
          (particleAverage step.potential particles -
            finiteExpectation (bootstrapTargetLaw initial priorSteps)
              step.potential) ^ 2 ≤ denominatorMSE) :
    finiteExpectation
        (bootstrapPopulationLaw (Particle := Particle) initial
          (priorSteps ++ [step]))
        (fun particles =>
          (particleAverage score particles -
            finiteExpectation
              (bootstrapTargetLaw initial (priorSteps ++ [step])) score) ^ 2) ≤
      freshVariance / Fintype.card Particle +
        2 * (numeratorMSE + observableBound ^ 2 * denominatorMSE) /
          lower ^ 2 := by
  let priorTarget := bootstrapTargetLaw initial priorSteps
  let numerator := finiteExpectation priorTarget (fun x => step.potential x *
    finiteExpectation (rowDistribution step.transition x) score)
  let denominator := finiteExpectation priorTarget step.potential
  have hdenominator : denominator ≠ 0 := ne_of_gt
    (finiteExpectation_pos priorTarget step.potential step.potential_pos)
  have htarget :
      finiteExpectation (bootstrapTargetLaw initial (priorSteps ++ [step])) score =
        numerator / denominator := by
    exact bootstrapTargetLaw_append_singleton_expectation initial priorSteps
      step score
  rw [htarget] at hobservable ⊢
  exact bootstrapPopulationLaw_append_singleton_mse_le initial priorSteps step
    score hdenominator hlower hparticleLower hobservable hobservableNonneg
    hfresh hnumeratorMSE hdenominatorMSE

omit [DecidableEq Sample] in
/-- Fully finite-state version of the actual bootstrap induction step. The
positive potential floor, target-observable bound, and fresh stage variance
are constructed automatically from finite extrema. -/
theorem bootstrapPopulationLaw_append_singleton_target_mse_le_finiteBounds
    [Nonempty Sample]
    (initial : Distribution Sample) (priorSteps : List (FeynmanKacStep Sample))
    (step : FeynmanKacStep Sample) (score : Sample → ℝ)
    {numeratorMSE denominatorMSE : ℝ}
    (hnumeratorMSE :
      ∑ particles,
        (bootstrapPopulationLaw (Particle := Particle) initial priorSteps).mass
            particles *
          (particleAverage (fun x => step.potential x *
              finiteExpectation (rowDistribution step.transition x) score)
              particles -
            finiteExpectation (bootstrapTargetLaw initial priorSteps)
              (fun x => step.potential x *
                finiteExpectation (rowDistribution step.transition x) score)) ^ 2 ≤
        numeratorMSE)
    (hdenominatorMSE :
      ∑ particles,
        (bootstrapPopulationLaw (Particle := Particle) initial priorSteps).mass
            particles *
          (particleAverage step.potential particles -
            finiteExpectation (bootstrapTargetLaw initial priorSteps)
              step.potential) ^ 2 ≤ denominatorMSE) :
    finiteExpectation
        (bootstrapPopulationLaw (Particle := Particle) initial
          (priorSteps ++ [step]))
        (fun particles =>
          (particleAverage score particles -
            finiteExpectation
              (bootstrapTargetLaw initial (priorSteps ++ [step])) score) ^ 2) ≤
      (8 * finiteFunctionAbsMaximum score ^ 2) /
          Fintype.card Particle +
        2 * (numeratorMSE + finiteFunctionAbsMaximum score ^ 2 * denominatorMSE) /
          finiteFunctionMinimum step.potential ^ 2 := by
  apply bootstrapPopulationLaw_append_singleton_target_mse_le
    initial priorSteps step score
  · exact finiteFunctionMinimum_pos step.potential step.potential_pos
  · exact fun particles =>
      finiteFunctionMinimum_le_particleAverage step.potential particles
  · exact abs_finiteExpectation_le _ _
  · exact finiteFunctionAbsMaximum_nonneg score
  · exact fun particles => bootstrapStage_freshVariance_le
      step.potential step.potential_pos particles step.transition score
  · exact hnumeratorMSE
  · exact hdenominatorMSE

/-- Count-independent coefficient transformer for one finite bootstrap stage.
If the incoming MSE for every observable is `budget observable / N`, this is
the coefficient delivered for the outgoing observable. -/
noncomputable def bootstrapMSEBudgetStep [Nonempty Sample]
    (budget : (Sample → ℝ) → ℝ) (step : FeynmanKacStep Sample)
    (score : Sample → ℝ) : ℝ :=
  8 * finiteFunctionAbsMaximum score ^ 2 +
    2 * (budget (fun x => step.potential x *
        finiteExpectation (rowDistribution step.transition x) score) +
      finiteFunctionAbsMaximum score ^ 2 * budget step.potential) /
        finiteFunctionMinimum step.potential ^ 2

/-- Fold the observable-indexed MSE coefficient through a concrete schedule. -/
noncomputable def bootstrapMSEBudgetFrom [Nonempty Sample]
    (budget : (Sample → ℝ) → ℝ) :
    List (FeynmanKacStep Sample) → (Sample → ℝ) → ℝ
  | [], score => budget score
  | step :: steps, score =>
      bootstrapMSEBudgetFrom (bootstrapMSEBudgetStep budget step) steps score

omit [DecidableEq Sample] in
/-- One arbitrary incoming population/target pair advances the universal
inverse-count MSE budget by `bootstrapMSEBudgetStep`. -/
theorem bootstrapPopulationUpdate_target_mse_le_budget
    [Nonempty Sample]
    (currentPopulation : Distribution (Particle → Sample))
    (currentTarget : Distribution Sample)
    (budget : (Sample → ℝ) → ℝ)
    (hincoming : ∀ score : Sample → ℝ,
      finiteExpectation currentPopulation (fun particles =>
        (particleAverage score particles -
          finiteExpectation currentTarget score) ^ 2) ≤
        budget score / Fintype.card Particle)
    (step : FeynmanKacStep Sample) (score : Sample → ℝ) :
    finiteExpectation
        (Distribution.bind currentPopulation (bootstrapPopulationUpdate step))
        (fun particles =>
          (particleAverage score particles -
            finiteExpectation (bootstrapTargetUpdate currentTarget step) score) ^ 2) ≤
      bootstrapMSEBudgetStep budget step score / Fintype.card Particle := by
  let numeratorScore : Sample → ℝ := fun x => step.potential x *
    finiteExpectation (rowDistribution step.transition x) score
  let numerator := finiteExpectation currentTarget numeratorScore
  let denominator := finiteExpectation currentTarget step.potential
  let bound := finiteFunctionAbsMaximum score
  let lower := finiteFunctionMinimum step.potential
  have hdenominator : denominator ≠ 0 := ne_of_gt
    (finiteExpectation_pos currentTarget step.potential step.potential_pos)
  have hlower : 0 < lower :=
    finiteFunctionMinimum_pos step.potential step.potential_pos
  have htarget :
      finiteExpectation (bootstrapTargetUpdate currentTarget step) score =
        numerator / denominator := by
    exact bootstrapTargetUpdate_expectation currentTarget step score
  have hstage := bootstrapStage_mse_le currentPopulation step.potential
    step.potential_pos step.transition score hdenominator hlower
    (fun particles => finiteFunctionMinimum_le_particleAverage
      step.potential particles)
    (by simpa [bound, htarget] using
      abs_finiteExpectation_le (bootstrapTargetUpdate currentTarget step) score)
    (finiteFunctionAbsMaximum_nonneg score)
    (fun particles => bootstrapStage_freshVariance_le step.potential
      step.potential_pos particles step.transition score)
    (hincoming numeratorScore) (hincoming step.potential)
  have hlaw :
      finiteExpectation
          (Distribution.bind currentPopulation (bootstrapPopulationUpdate step))
          (fun particles =>
            (particleAverage score particles - numerator / denominator) ^ 2) =
        ∑ particles, currentPopulation.mass particles *
          (∑ outcome,
            (resamplePropagateLaw
              (normalizedPotentialWeights step.potential step.potential_pos
                particles) particles step.transition).mass outcome *
              (particleAverage score outcome.2 - numerator / denominator) ^ 2) := by
    rw [finiteExpectation_bind]
    apply Finset.sum_congr rfl
    intro particles _
    rw [bootstrapPopulationUpdate_expectation_eq_joint]
    rfl
  rw [htarget]
  rw [hlaw]
  refine hstage.trans_eq ?_
  unfold bootstrapMSEBudgetStep
  dsimp [bound, lower, numeratorScore]
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

omit [DecidableEq Sample] in
/-- Universal inverse-count MSE induction over an arbitrary finite bootstrap
schedule, starting from any population/target pair with an observable-indexed
incoming budget. -/
theorem bootstrapPopulationLawFrom_target_mse_le_budget
    [Nonempty Sample]
    (currentPopulation : Distribution (Particle → Sample))
    (currentTarget : Distribution Sample)
    (budget : (Sample → ℝ) → ℝ)
    (hincoming : ∀ score : Sample → ℝ,
      finiteExpectation currentPopulation (fun particles =>
        (particleAverage score particles -
          finiteExpectation currentTarget score) ^ 2) ≤
        budget score / Fintype.card Particle)
    (steps : List (FeynmanKacStep Sample)) (score : Sample → ℝ) :
    finiteExpectation (bootstrapPopulationLawFrom currentPopulation steps)
        (fun particles =>
          (particleAverage score particles -
            finiteExpectation (bootstrapTargetLawFrom currentTarget steps) score) ^ 2) ≤
      bootstrapMSEBudgetFrom budget steps score / Fintype.card Particle := by
  induction steps generalizing currentPopulation currentTarget budget with
  | nil => exact hincoming score
  | cons step steps ih =>
      apply ih
      exact fun nextScore =>
        bootstrapPopulationUpdate_target_mse_le_budget currentPopulation
          currentTarget budget hincoming step nextScore

omit [DecidableEq Sample] in
/-- Iid initialization supplies the exact universal base budget. -/
theorem iidPopulation_target_mse_eq_variance_div_count
    (initial : Distribution Sample) (score : Sample → ℝ) :
    finiteExpectation (iidPopulation (Particle := Particle) initial)
        (fun particles =>
          (particleAverage score particles -
            finiteExpectation initial score) ^ 2) =
      finiteVariance initial score / Fintype.card Particle := by
  unfold finiteExpectation
  exact iidPopulation_particleAverage_mse initial score

omit [DecidableEq Sample] in
/-- Full fixed-horizon `O(1/N)` MSE theorem for the actual finite bootstrap
particle filter and its exact normalized Feynman--Kac target. -/
theorem bootstrapPopulationLaw_target_mse_le
    [Nonempty Sample]
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) :
    finiteExpectation
        (bootstrapPopulationLaw (Particle := Particle) initial steps)
        (fun particles =>
          (particleAverage score particles -
            finiteExpectation (bootstrapTargetLaw initial steps) score) ^ 2) ≤
      bootstrapMSEBudgetFrom (finiteVariance initial) steps score /
        Fintype.card Particle := by
  apply bootstrapPopulationLawFrom_target_mse_le_budget
  intro baseScore
  exact (iidPopulation_target_mse_eq_variance_div_count initial baseScore).le

/-- Count-indexed MSE of the actual bootstrap particle filter. -/
noncomputable def bootstrapPopulationMSEByExtra
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) (extra : ℕ) : ℝ :=
  finiteExpectation
    (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial steps)
    (fun particles =>
      (particleAverage score particles -
        finiteExpectation (bootstrapTargetLaw initial steps) score) ^ 2)

omit [DecidableEq Sample] in
theorem bootstrapPopulationMSEByExtra_nonneg
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) (extra : ℕ) :
    0 ≤ bootstrapPopulationMSEByExtra initial steps score extra := by
  unfold bootstrapPopulationMSEByExtra finiteExpectation
  exact Finset.sum_nonneg fun particles _ => mul_nonneg
    ((bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial steps).nonneg
      particles) (sq_nonneg _)

omit [DecidableEq Sample] in
theorem bootstrapPopulationMSEByExtra_le
    [Nonempty Sample]
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) (extra : ℕ) :
    bootstrapPopulationMSEByExtra initial steps score extra ≤
      bootstrapMSEBudgetFrom (finiteVariance initial) steps score /
        ((extra : ℝ) + 1) := by
  unfold bootstrapPopulationMSEByExtra
  simpa using bootstrapPopulationLaw_target_mse_le
    (Particle := Fin (extra + 1)) initial steps score

omit [DecidableEq Sample] in
/-- Fixed-horizon mean-square consistency of the actual finite bootstrap
particle filter as its particle count tends to infinity. -/
theorem bootstrapPopulationMSEByExtra_tendsto_zero
    [Nonempty Sample]
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) :
    Filter.Tendsto (bootstrapPopulationMSEByExtra initial steps score)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
    (g := fun extra : ℕ =>
      bootstrapMSEBudgetFrom (finiteVariance initial) steps score /
        ((extra : ℝ) + 1))
  · exact fun extra => bootstrapPopulationMSEByExtra_nonneg
      initial steps score extra
  · exact fun extra => bootstrapPopulationMSEByExtra_le
      initial steps score extra
  · exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1
        tendsto_natCast_atTop_atTop)

/-- Deviation probability of the actual count-indexed bootstrap empirical
average from its exact normalized Feynman--Kac expectation. -/
noncomputable def bootstrapPopulationDeviationProbability
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) (extra : ℕ) (tolerance : ℝ) : ℝ :=
  ∑ particles : Fin (extra + 1) → Sample,
    (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial steps).mass
        particles *
      if tolerance ≤ |particleAverage score particles -
          finiteExpectation (bootstrapTargetLaw initial steps) score|
      then 1 else 0

omit [DecidableEq Sample] in
theorem bootstrapPopulationDeviationProbability_nonneg
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) (extra : ℕ) (tolerance : ℝ) :
    0 ≤ bootstrapPopulationDeviationProbability initial steps score extra
      tolerance := by
  unfold bootstrapPopulationDeviationProbability
  apply Finset.sum_nonneg
  intro particles _
  split
  · simpa using
      (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial steps).nonneg
        particles
  · simp

omit [DecidableEq Sample] in
theorem bootstrapPopulationDeviationProbability_le
    [Nonempty Sample]
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) (extra : ℕ) {tolerance : ℝ}
    (htolerance : 0 < tolerance) :
    bootstrapPopulationDeviationProbability initial steps score extra tolerance ≤
      bootstrapMSEBudgetFrom (finiteVariance initial) steps score /
        ((extra : ℝ) + 1) / tolerance ^ 2 := by
  unfold bootstrapPopulationDeviationProbability
  calc
    _ ≤ ∑ particles : Fin (extra + 1) → Sample,
        (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial steps).mass
            particles *
          (particleAverage score particles -
            finiteExpectation (bootstrapTargetLaw initial steps) score) ^ 2 /
              tolerance ^ 2 := by
      apply Finset.sum_le_sum
      intro particles _
      by_cases hbad : tolerance ≤ |particleAverage score particles -
          finiteExpectation (bootstrapTargetLaw initial steps) score|
      · simp only [hbad, if_true]
        have hsquare : tolerance ^ 2 ≤
            (particleAverage score particles -
              finiteExpectation (bootstrapTargetLaw initial steps) score) ^ 2 := by
          nlinarith [sq_nonneg
            (|particleAverage score particles -
              finiteExpectation (bootstrapTargetLaw initial steps) score| -
                tolerance),
            sq_abs (particleAverage score particles -
              finiteExpectation (bootstrapTargetLaw initial steps) score)]
        have hmass :=
          (bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial steps).nonneg
            particles
        rw [le_div_iff₀ (sq_pos_of_pos htolerance)]
        nlinarith
      · simp only [hbad, if_false, mul_zero]
        exact div_nonneg (mul_nonneg
          ((bootstrapPopulationLaw (Particle := Fin (extra + 1)) initial steps).nonneg
            particles) (sq_nonneg _)) (sq_nonneg _)
    _ = bootstrapPopulationMSEByExtra initial steps score extra /
        tolerance ^ 2 := by
      unfold bootstrapPopulationMSEByExtra finiteExpectation
      rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      (bootstrapPopulationMSEByExtra_le initial steps score extra)
      (sq_nonneg _)

omit [DecidableEq Sample] in
/-- Fixed-horizon convergence in probability of the actual bootstrap
particle-filter empirical average. -/
theorem bootstrapPopulationDeviationProbability_tendsto_zero
    [Nonempty Sample]
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (score : Sample → ℝ) {tolerance : ℝ} (htolerance : 0 < tolerance) :
    Filter.Tendsto
      (fun extra => bootstrapPopulationDeviationProbability
        initial steps score extra tolerance)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
    (g := fun extra : ℕ =>
      bootstrapMSEBudgetFrom (finiteVariance initial) steps score /
        ((extra : ℝ) + 1) / tolerance ^ 2)
  · exact fun extra => bootstrapPopulationDeviationProbability_nonneg
      initial steps score extra tolerance
  · exact fun extra => bootstrapPopulationDeviationProbability_le
      initial steps score extra htolerance
  · have hbase : Filter.Tendsto
        (fun extra : ℕ =>
          bootstrapMSEBudgetFrom (finiteVariance initial) steps score /
            ((extra : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (Filter.tendsto_atTop_add_const_right Filter.atTop 1
          tendsto_natCast_atTop_atTop)
    simpa using hbase.div_const (tolerance ^ 2)

end NormalizedWeightPerturbation

section SequentialErrorRecursion

/-- Exact deterministic budget generated by a time-inhomogeneous affine error
recurrence. `rate n` and `noise n` may vary with the Feynman--Kac stage. -/
noncomputable def sequentialErrorBudget
    (rate noise : ℕ → ℝ) (initial : ℝ) : ℕ → ℝ
  | 0 => initial
  | n + 1 => rate n * sequentialErrorBudget rate noise initial n + noise n

/-- A stagewise affine error estimate is bounded by its recursively generated
time-inhomogeneous budget. -/
theorem sequential_error_le_budget
    (error rate noise : ℕ → ℝ) {initial : ℝ}
    (hrate : ∀ n, 0 ≤ rate n)
    (hinitial : error 0 ≤ initial)
    (hstep : ∀ n, error (n + 1) ≤ rate n * error n + noise n) :
    ∀ n, error n ≤ sequentialErrorBudget rate noise initial n := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      rw [sequentialErrorBudget]
      calc
        error (n + 1) ≤ rate n * error n + noise n := hstep n
        _ ≤ rate n * sequentialErrorBudget rate noise initial n + noise n := by
          exact add_le_add (mul_le_mul_of_nonneg_left ih (hrate n)) (le_refl _)

/-- Fixed-horizon inverse-particle-count propagation. If the initial MSE and
every stage's fresh Monte Carlo noise are bounded by count-independent
coefficients divided by `N`, then the full time-inhomogeneous recurrence is
bounded by the recursively generated coefficient divided by `N`. -/
theorem sequential_error_le_inverse_count
    (error : ℕ → ℕ → ℝ) (rate noiseCoefficient : ℕ → ℝ)
    {initialCoefficient : ℝ}
    (hrate : ∀ n, 0 ≤ rate n)
    (hinitial : ∀ extra,
      error extra 0 ≤ initialCoefficient / ((extra : ℝ) + 1))
    (hstep : ∀ extra n,
      error extra (n + 1) ≤ rate n * error extra n +
        noiseCoefficient n / ((extra : ℝ) + 1)) :
    ∀ extra n, error extra n ≤
      sequentialErrorBudget rate noiseCoefficient initialCoefficient n /
        ((extra : ℝ) + 1) := by
  intro extra n
  have hdenom : (0 : ℝ) < (extra : ℝ) + 1 := by positivity
  induction n with
  | zero => exact hinitial extra
  | succ n ih =>
      rw [sequentialErrorBudget]
      calc
        error extra (n + 1) ≤ rate n * error extra n +
            noiseCoefficient n / ((extra : ℝ) + 1) := hstep extra n
        _ ≤ rate n *
              (sequentialErrorBudget rate noiseCoefficient initialCoefficient n /
                ((extra : ℝ) + 1)) +
            noiseCoefficient n / ((extra : ℝ) + 1) := by
              exact add_le_add (mul_le_mul_of_nonneg_left ih (hrate n))
                (le_refl _)
        _ = (rate n *
              sequentialErrorBudget rate noiseCoefficient initialCoefficient n +
            noiseCoefficient n) / ((extra : ℝ) + 1) := by ring

/-- At every fixed horizon, the preceding inverse-count budget tends to zero
as the concrete particle count `N = extra + 1` tends to infinity. -/
theorem sequentialErrorBudget_div_count_tendsto_zero
    (rate noiseCoefficient : ℕ → ℝ) (initialCoefficient : ℝ) (horizon : ℕ) :
    Filter.Tendsto
      (fun extra : ℕ =>
        sequentialErrorBudget rate noiseCoefficient initialCoefficient horizon /
          ((extra : ℝ) + 1))
      Filter.atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop
    (Filter.tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_natCast_atTop_atTop)

/-- Fixed-horizon mean-square consistency follows from nonnegativity and the
stagewise inverse-count recurrence. This theorem is deliberately abstract in
the stage constants so concrete SMC models must still prove their normalized
one-step estimates. -/
theorem sequential_error_tendsto_zero_of_inverse_count
    (error : ℕ → ℕ → ℝ) (rate noiseCoefficient : ℕ → ℝ)
    {initialCoefficient : ℝ}
    (hnonneg : ∀ extra n, 0 ≤ error extra n)
    (hrate : ∀ n, 0 ≤ rate n)
    (hinitial : ∀ extra,
      error extra 0 ≤ initialCoefficient / ((extra : ℝ) + 1))
    (hstep : ∀ extra n,
      error extra (n + 1) ≤ rate n * error extra n +
        noiseCoefficient n / ((extra : ℝ) + 1))
    (horizon : ℕ) :
    Filter.Tendsto (fun extra => error extra horizon)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
    (g := fun extra : ℕ =>
      sequentialErrorBudget rate noiseCoefficient initialCoefficient horizon /
        ((extra : ℝ) + 1))
  · exact fun extra => hnonneg extra horizon
  · exact fun extra => sequential_error_le_inverse_count error rate
      noiseCoefficient hrate hinitial hstep extra horizon
  · exact sequentialErrorBudget_div_count_tendsto_zero rate noiseCoefficient
      initialCoefficient horizon

/-- Iteration of a one-step affine particle-error estimate.  At every fixed
horizon this retains an explicit inverse-particle-count noise term; obtaining
uniform-in-time consistency additionally requires a strict contraction or a
separate stability theorem. -/
theorem sequential_error_le_geometric_sum
    (error : ℕ → ℝ) {rate initialError noise : ℝ}
    (hrate : 0 ≤ rate)
    (hinitial : error 0 ≤ initialError)
    (hstep : ∀ n, error (n + 1) ≤ rate * error n + noise) :
    ∀ n, error n ≤
      rate ^ n * initialError + noise * ∑ k ∈ Finset.range n, rate ^ k := by
  intro n
  induction n with
  | zero => simpa using hinitial
  | succ n ih =>
      calc
        error (n + 1) ≤ rate * error n + noise := hstep n
        _ ≤ rate *
              (rate ^ n * initialError +
                noise * ∑ k ∈ Finset.range n, rate ^ k) + noise := by
            gcongr
        _ = rate ^ (n + 1) * initialError +
              noise * ∑ k ∈ Finset.range (n + 1), rate ^ k := by
            rw [Finset.sum_range_succ']
            simp only [pow_zero, pow_succ']
            rw [← Finset.mul_sum]
            ring

end SequentialErrorRecursion

end Mcmc.Finite.ParticleEstimator
