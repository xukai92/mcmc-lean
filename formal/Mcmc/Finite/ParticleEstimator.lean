import Mcmc.Finite.PseudoMarginal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite iid particle estimators

This module supplies the first particle layer below pseudo-marginal MH.  An
iid cloud of any positive finite size averages nonnegative unit-mean weights;
Lean proves that the average remains nonnegative and unbiased, then packages
it as the estimator required by finite pseudo-marginal MH.

This is finite particle importance sampling.  Sequential propagation,
resampling, ancestry, and conditional SMC are deliberately later layers.
-/

open scoped BigOperators

namespace Mcmc.Finite.ParticleEstimator

open MarkovKernel PseudoMarginal

variable {State Sample Particle : Type*}
  [Fintype State] [Fintype Sample] [Fintype Particle]
  [DecidableEq State] [DecidableEq Sample] [DecidableEq Particle]
  [Nonempty Particle]

/-- Independent population drawn from a common finite distribution. -/
def iidPopulation (law : Distribution Sample) : Distribution (Particle → Sample) where
  mass samples := ∏ i, law.mass (samples i)
  nonneg samples := Finset.prod_nonneg fun i _ => law.nonneg (samples i)
  sum_mass := by
    rw [← Fintype.prod_sum]
    simp [law.sum_mass]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- An iid population has full support when its one-particle law does. -/
theorem iidPopulation_mass_pos (law : Distribution Sample)
    (hpos : ∀ x, 0 < law.mass x) (samples : Particle → Sample) :
    0 < (iidPopulation law).mass samples := by
  exact Finset.prod_pos fun i _ => hpos (samples i)

/-- Arithmetic mean of particle weights. -/
noncomputable def particleAverage (score : Sample → ℝ)
    (samples : Particle → Sample) : ℝ :=
  (∑ i, score (samples i)) / Fintype.card Particle

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Particle] in
theorem particleAverage_nonneg
    {score : Sample → ℝ} (hscore : ∀ s, 0 ≤ score s)
    (samples : Particle → Sample) :
    0 ≤ particleAverage score samples := by
  unfold particleAverage
  exact div_nonneg (Finset.sum_nonneg fun i _ => hscore (samples i)) (by positivity)

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Particle] in
/-- The empirical average of a pointwise positive score is positive for a
nonempty particle type. -/
theorem particleAverage_pos {score : Sample → ℝ} (hscore : ∀ s, 0 < score s)
    (samples : Particle → Sample) :
    0 < particleAverage score samples := by
  unfold particleAverage
  exact div_pos
    (Finset.sum_pos (fun i _ => hscore (samples i)) Finset.univ_nonempty)
    (by positivity)

omit [DecidableEq Sample] [Nonempty Particle] in
/-- One coordinate of an iid population has the original weighted
expectation. -/
theorem iidPopulation_coordinate_expectation
    (law : Distribution Sample) (score : Sample → ℝ)
    (i : Particle) :
    ∑ samples, (iidPopulation law).mass samples * score (samples i) =
      ∑ s, law.mass s * score s := by
  classical
  calc
    ∑ samples, (iidPopulation law).mass samples * score (samples i) =
        ∑ samples : Particle → Sample,
          ∏ j, if j = i then law.mass (samples j) * score (samples j)
          else law.mass (samples j) := by
      apply Finset.sum_congr rfl
      intro samples _
      rw [iidPopulation]
      calc
        (∏ j, law.mass (samples j)) * score (samples i) =
            ∏ j, law.mass (samples j) * (if j = i then score (samples i) else 1) := by
          rw [Finset.prod_mul_distrib]
          simp
        _ = ∏ j, if j = i then law.mass (samples j) * score (samples j)
              else law.mass (samples j) := by
          apply Finset.prod_congr rfl
          intro j _
          by_cases hji : j = i <;> simp [hji]
    _ = ∏ j : Particle, ∑ s, if j = i then law.mass s * score s
          else law.mass s := by
      exact (Fintype.prod_sum
        (f := fun j : Particle => fun s : Sample =>
          if j = i then law.mass s * score s else law.mass s)).symm
    _ = ∑ s, law.mass s * score s := by
      simp [law.sum_mass]

omit [DecidableEq Sample] in
/-- The expected empirical average of an iid population equals the
single-particle expectation. -/
theorem iidPopulation_particleAverage_expectation
    (law : Distribution Sample) (score : Sample → ℝ) :
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
        particleAverage score samples =
      ∑ s, law.mass s * score s := by
  classical
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold particleAverage
  calc
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
          ((∑ i, score (samples i)) / Fintype.card Particle) =
        (∑ i, ∑ samples : Particle → Sample,
          (iidPopulation law).mass samples *
          score (samples i)) / Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ _i : Particle, ∑ s, law.mass s * score s) /
        Fintype.card Particle := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [iidPopulation_coordinate_expectation law score i]
    _ = ∑ s, law.mass s * score s := by
      simp [hcard]

omit [DecidableEq Sample] in
/-- The average of iid nonnegative unit-mean scores is again unit mean. -/
theorem iidPopulation_particleAverage_unbiased
    (law : Distribution Sample) (score : Sample → ℝ)
    (hunbiased : ∑ s, law.mass s * score s = 1) :
    ∑ samples : Particle → Sample, (iidPopulation law).mass samples *
        particleAverage score samples = 1 := by
  rw [iidPopulation_particleAverage_expectation law score, hunbiased]

/-- Multinomial resampling draws each new ancestor independently from the
normalized weights. -/
def multinomialResampling (weights : Distribution Particle) :
    Distribution (Particle → Particle) :=
  iidPopulation weights

omit [Fintype Sample] [DecidableEq Sample] [Nonempty Particle] in
/-- Multinomial resampling has full support when every categorical weight is
positive. -/
theorem multinomialResampling_mass_pos (weights : Distribution Particle)
    (hpos : ∀ i, 0 < weights.mass i) (ancestors : Particle → Particle) :
    0 < (multinomialResampling weights).mass ancestors :=
  iidPopulation_mass_pos weights hpos ancestors

omit [Fintype Sample] [DecidableEq Sample] in
/-- Conditional unbiasedness of multinomial resampling: the expected average
of any observable over the resampled population equals its current weighted
empirical average. -/
theorem multinomialResampling_unbiased
    (weights : Distribution Particle) (particles : Particle → Sample)
    (observable : Sample → ℝ) :
    ∑ ancestors, (multinomialResampling weights).mass ancestors *
        particleAverage (fun i => observable (particles i)) ancestors =
      ∑ i, weights.mass i * observable (particles i) := by
  exact iidPopulation_particleAverage_expectation weights
    (fun i => observable (particles i))

/-- Independent, not necessarily identically distributed, finite population.
This is the conditional propagation law after ancestor indices are fixed. -/
def independentPopulation (law : Particle → Distribution Sample) :
    Distribution (Particle → Sample) where
  mass samples := ∏ i, (law i).mass (samples i)
  nonneg samples := Finset.prod_nonneg fun i _ => (law i).nonneg (samples i)
  sum_mass := by
    rw [← Fintype.prod_sum]
    simp [Distribution.sum_mass]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- A coordinate-wise independent population has full support when every
coordinate law does. -/
theorem independentPopulation_mass_pos (law : Particle → Distribution Sample)
    (hpos : ∀ i x, 0 < (law i).mass x) (samples : Particle → Sample) :
    0 < (independentPopulation law).mass samples := by
  exact Finset.prod_pos fun i _ => hpos i (samples i)

/-- Point mass as an elementary finite distribution. -/
def pointDistribution (value : Sample) : Distribution Sample where
  mass sample := if sample = value then 1 else 0
  nonneg sample := by split <;> norm_num
  sum_mass := by simp

/-- Independent population with one distinguished coordinate forced to a
specified value. All other coordinates retain their supplied laws. This is
the elementary initialization/propagation law used by conditional SMC. -/
def forcedIndependentPopulation (law : Particle → Distribution Sample)
    (retained : Particle) (value : Sample) : Distribution (Particle → Sample) :=
  independentPopulation fun i =>
    if i = retained then pointDistribution value else law i

omit [Nonempty Particle] in
theorem forcedIndependentPopulation_incompatible_zero
    (law : Particle → Distribution Sample) (retained : Particle) (value : Sample)
    (samples : Particle → Sample) (h : samples retained ≠ value) :
    (forcedIndependentPopulation law retained value).mass samples = 0 := by
  unfold forcedIndependentPopulation independentPopulation
  apply Finset.prod_eq_zero (Finset.mem_univ retained)
  simp [pointDistribution, h]

omit [Nonempty Particle] in
/-- The forced coordinate equals the retained value almost surely. -/
theorem forcedIndependentPopulation_coordinate_probability
    (law : Particle → Distribution Sample) (retained : Particle) (value : Sample) :
    ∑ samples, (forcedIndependentPopulation law retained value).mass samples *
      (if samples retained = value then 1 else 0) = 1 := by
  rw [show (∑ samples, (forcedIndependentPopulation law retained value).mass samples *
      (if samples retained = value then 1 else 0)) =
      ∑ samples, (forcedIndependentPopulation law retained value).mass samples by
    apply Finset.sum_congr rfl
    intro samples _
    by_cases h : samples retained = value
    · simp [h]
    · rw [forcedIndependentPopulation_incompatible_zero law retained value samples h]
      simp]
  exact (forcedIndependentPopulation law retained value).sum_mass

omit [Nonempty Particle] in
/-- Conditioning an independent product on one positive-mass coordinate is
exactly the forced-coordinate product law. -/
theorem forcedIndependentPopulation_mass_eq_div
    (law : Particle → Distribution Sample) (retained : Particle) (value : Sample)
    (hvalue : 0 < (law retained).mass value)
    (samples : Particle → Sample) :
    (forcedIndependentPopulation law retained value).mass samples =
      if samples retained = value then
        (independentPopulation law).mass samples / (law retained).mass value
      else 0 := by
  classical
  by_cases hsample : samples retained = value
  · simp only [hsample, if_true]
    unfold forcedIndependentPopulation independentPopulation pointDistribution
    change (∏ i, (if i = retained then
        { mass := fun sample => if sample = value then 1 else 0
          nonneg := fun sample => by split <;> norm_num
          sum_mass := by simp : Distribution Sample }
        else law i).mass (samples i)) =
      (∏ i, (law i).mass (samples i)) / (law retained).mass value
    let f : Particle → ℝ := fun i => (law i).mass (samples i)
    have hfull := Finset.mul_prod_erase Finset.univ f
      (Finset.mem_univ retained)
    have hforced :
        (∏ i, (if i = retained then
          { mass := fun sample => if sample = value then 1 else 0
            nonneg := fun sample => by split <;> norm_num
            sum_mass := by simp : Distribution Sample }
          else law i).mass (samples i)) =
        ∏ i ∈ Finset.univ.erase retained, f i := by
      rw [← Finset.prod_erase Finset.univ (a := retained)]
      · apply Finset.prod_congr rfl
        intro i hi
        have hir : i ≠ retained := (Finset.mem_erase.mp hi).1
        simp [hir, f]
      · simp [hsample]
    rw [hforced]
    dsimp only [f] at hfull
    rw [← hfull]
    field_simp
    simp [f, hsample, mul_comm]
  · rw [forcedIndependentPopulation_incompatible_zero law retained value samples hsample]
    simp [hsample]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Each coordinate of an independently propagated population has its
specified transition law. -/
theorem independentPopulation_coordinate_expectation
    (law : Particle → Distribution Sample) (score : Sample → ℝ)
    (i : Particle) :
    ∑ samples, (independentPopulation law).mass samples * score (samples i) =
      ∑ s, (law i).mass s * score s := by
  classical
  calc
    ∑ samples, (independentPopulation law).mass samples * score (samples i) =
        ∑ samples : Particle → Sample,
          ∏ j, if j = i then (law j).mass (samples j) * score (samples j)
          else (law j).mass (samples j) := by
      apply Finset.sum_congr rfl
      intro samples _
      rw [independentPopulation]
      calc
        (∏ j, (law j).mass (samples j)) * score (samples i) =
            ∏ j, (law j).mass (samples j) *
              (if j = i then score (samples i) else 1) := by
          rw [Finset.prod_mul_distrib]
          simp
        _ = ∏ j, if j = i then (law j).mass (samples j) * score (samples j)
              else (law j).mass (samples j) := by
          apply Finset.prod_congr rfl
          intro j _
          by_cases hji : j = i <;> simp [hji]
    _ = ∏ j : Particle, ∑ s, if j = i then (law j).mass s * score s
          else (law j).mass s := by
      exact (Fintype.prod_sum
        (f := fun j : Particle => fun s : Sample =>
          if j = i then (law j).mass s * score s else (law j).mass s)).symm
    _ = ∑ s, (law i).mass s * score s := by
      simp [Distribution.sum_mass]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Expected empirical average after independent heterogeneous propagation. -/
theorem independentPopulation_particleAverage_expectation
    (law : Particle → Distribution Sample) (score : Sample → ℝ) :
    ∑ samples, (independentPopulation law).mass samples *
        particleAverage score samples =
      (∑ i, ∑ s, (law i).mass s * score s) / Fintype.card Particle := by
  classical
  unfold particleAverage
  calc
    ∑ samples : Particle → Sample, (independentPopulation law).mass samples *
          ((∑ i, score (samples i)) / Fintype.card Particle) =
        (∑ i, ∑ samples : Particle → Sample,
          (independentPopulation law).mass samples * score (samples i)) /
            Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ i, ∑ s, (law i).mass s * score s) /
          Fintype.card Particle := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [independentPopulation_coordinate_expectation law score i]

omit [Nonempty Particle] in
/-- A forced independent population has the supplied marginal away from the
retained coordinate and a point mass at the retained value on that coordinate.
This is the local expectation identity needed to analyze conditional SMC
without selecting one particular population history. -/
theorem forcedIndependentPopulation_coordinate_expectation
    (law : Particle → Distribution Sample) (retained : Particle)
    (value : Sample) (score : Sample → ℝ) (i : Particle) :
    ∑ samples, (forcedIndependentPopulation law retained value).mass samples *
        score (samples i) =
      if i = retained then score value
      else ∑ s, (law i).mass s * score s := by
  classical
  unfold forcedIndependentPopulation
  rw [independentPopulation_coordinate_expectation]
  by_cases hi : i = retained
  · subst i
    simp [pointDistribution]
  · simp [hi]

omit [Nonempty Particle] in
/-- Exact expected empirical average of a conditionally independent cloud
with one forced coordinate. The formula retains the full heterogeneous sum,
so it applies both to conditional resampling and conditional propagation. -/
theorem forcedIndependentPopulation_particleAverage_expectation
    (law : Particle → Distribution Sample) (retained : Particle)
    (value : Sample) (score : Sample → ℝ) :
    ∑ samples, (forcedIndependentPopulation law retained value).mass samples *
        particleAverage score samples =
      (∑ i, if i = retained then score value
        else ∑ s, (law i).mass s * score s) / Fintype.card Particle := by
  classical
  unfold particleAverage
  calc
    ∑ samples : Particle → Sample,
          (forcedIndependentPopulation law retained value).mass samples *
            ((∑ i, score (samples i)) / Fintype.card Particle) =
        (∑ i, ∑ samples : Particle → Sample,
          (forcedIndependentPopulation law retained value).mass samples *
            score (samples i)) / Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ i, if i = retained then score value
          else ∑ s, (law i).mass s * score s) /
            Fintype.card Particle := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [forcedIndependentPopulation_coordinate_expectation]

omit [Nonempty Particle] in
/-- A count-explicit lower bound for a forced cloud: every unforced marginal
contributes its common lower bound, while the retained coordinate contributes
only the assumed nonnegative forced score. Keeping the finite sum explicit
avoids any cardinal-subtraction side condition and is convenient for recursive
conditional-SMC estimates. -/
theorem forcedIndependentPopulation_particleAverage_expectation_ge
    (law : Particle → Distribution Sample) (retained : Particle)
    (value : Sample) (score : Sample → ℝ) (lower : ℝ)
    (hvalue : 0 ≤ score value)
    (hlower : ∀ i, i ≠ retained →
      lower ≤ ∑ s, (law i).mass s * score s) :
    (∑ i : Particle, if i = retained then 0 else lower) /
        Fintype.card Particle ≤
      ∑ samples,
        (forcedIndependentPopulation law retained value).mass samples *
          particleAverage score samples := by
  rw [forcedIndependentPopulation_particleAverage_expectation]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = retained
  · simp [hi, hvalue]
  · simpa [hi] using hlower i hi

omit [Nonempty Particle] in
/-- The explicit unforced-coordinate sum is exactly `N - 1` copies of its
common contribution. This is the cardinal arithmetic behind the numerator in
conditional-SMC aggregate bounds. -/
theorem sum_unforced_constant (retained : Particle) (value : ℝ) :
    (∑ i : Particle, if i = retained then 0 else value) =
      (Fintype.card Particle - 1 : ℕ) * value := by
  classical
  letI : Nonempty Particle := ⟨retained⟩
  have hcard : 1 ≤ Fintype.card Particle :=
    Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  calc
    (∑ i : Particle, if i = retained then 0 else value) =
        ∑ i : Particle, (value - if i = retained then value else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = retained <;> simp [hi]
    _ = (Fintype.card Particle : ℝ) * value - value := by
      rw [Finset.sum_sub_distrib]
      simp
    _ = (Fintype.card Particle - 1 : ℕ) * value := by
      rw [Nat.cast_sub hcard]
      push_cast
      ring

omit [Nonempty Particle] in
/-- Cardinal form of the common-marginal forced-cloud lower bound. -/
theorem forcedIndependentPopulation_particleAverage_expectation_ge_card
    (law : Particle → Distribution Sample) (retained : Particle)
    (value : Sample) (score : Sample → ℝ) (lower : ℝ)
    (hvalue : 0 ≤ score value)
    (hlower : ∀ i, i ≠ retained →
      lower ≤ ∑ s, (law i).mass s * score s) :
    ((Fintype.card Particle - 1 : ℕ) * lower) /
        Fintype.card Particle ≤
      ∑ samples,
        (forcedIndependentPopulation law retained value).mass samples *
          particleAverage score samples := by
  rw [← sum_unforced_constant retained lower]
  exact forcedIndependentPopulation_particleAverage_expectation_ge
    law retained value score lower hvalue hlower

/-- Coordinate-dependent empirical average. Conditional genealogy arguments
need this variant because whether a child extends the proposed path depends on
its own sampled ancestor. -/
noncomputable def indexedParticleAverage (score : Particle → Sample → ℝ)
    (samples : Particle → Sample) : ℝ :=
  (∑ i, score i (samples i)) / Fintype.card Particle

omit [Nonempty Particle] in
/-- Exact expectation of a coordinate-dependent empirical average under a
cloud with one forced coordinate. -/
theorem forcedIndependentPopulation_indexedParticleAverage_expectation
    (law : Particle → Distribution Sample) (retained : Particle)
    (value : Sample) (score : Particle → Sample → ℝ) :
    ∑ samples, (forcedIndependentPopulation law retained value).mass samples *
        indexedParticleAverage score samples =
      (∑ i, if i = retained then score i value
        else ∑ s, (law i).mass s * score i s) / Fintype.card Particle := by
  classical
  unfold indexedParticleAverage
  calc
    ∑ samples : Particle → Sample,
          (forcedIndependentPopulation law retained value).mass samples *
            ((∑ i, score i (samples i)) / Fintype.card Particle) =
        (∑ i, ∑ samples : Particle → Sample,
          (forcedIndependentPopulation law retained value).mass samples *
            score i (samples i)) / Fintype.card Particle := by
      simp_rw [div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ i, if i = retained then score i value
          else ∑ s, (law i).mass s * score i s) /
            Fintype.card Particle := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [forcedIndependentPopulation_coordinate_expectation]

omit [Nonempty Particle] in
/-- Lower-bound form of the indexed forced-cloud expectation. -/
theorem forcedIndependentPopulation_indexedParticleAverage_expectation_ge
    (law : Particle → Distribution Sample) (retained : Particle)
    (value : Sample) (score : Particle → Sample → ℝ)
    (lower : Particle → ℝ)
    (hvalue : 0 ≤ score retained value)
    (hlower : ∀ i, i ≠ retained →
      lower i ≤ ∑ s, (law i).mass s * score i s) :
    (∑ i : Particle, if i = retained then 0 else lower i) /
        Fintype.card Particle ≤
      ∑ samples,
        (forcedIndependentPopulation law retained value).mass samples *
          indexedParticleAverage score samples := by
  rw [forcedIndependentPopulation_indexedParticleAverage_expectation]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = retained
  · subst i
    simp [hvalue]
  · simpa [hi] using hlower i hi

/-- A row of a finite Markov kernel as a finite distribution. -/
def rowDistribution (transition : MarkovKernel Sample) (x : Sample) :
    Distribution Sample where
  mass y := transition.prob x y
  nonneg y := transition.nonneg x y
  sum_mass := transition.sum_prob x

/-- Fraction of children that both descend from a marked parent and land at a
prescribed next state. Iterating this observable tracks how many complete
genealogies realize a proposed trajectory. -/
noncomputable def lineageExtensionFraction (marked : Particle → Prop)
    [DecidablePred marked] (desired : Sample) (ancestors : Particle → Particle)
    (next : Particle → Sample) : ℝ :=
  indexedParticleAverage
    (fun i y => if marked (ancestors i) ∧ y = desired then 1 else 0) next

omit [Nonempty Particle] in
/-- Exact conditional expectation of the extended-lineage fraction after
propagation with one forced child. -/
theorem forcedPropagation_lineageExtensionFraction_expectation
    (transition : MarkovKernel Sample) (particles : Particle → Sample)
    (ancestors : Particle → Particle) (nextRetained : Particle)
    (nextState desired : Sample) (marked : Particle → Prop)
    [DecidablePred marked] :
    ∑ next,
      (forcedIndependentPopulation
        (fun i => rowDistribution transition (particles (ancestors i)))
        nextRetained nextState).mass next *
          lineageExtensionFraction marked desired ancestors next =
      (∑ i, if i = nextRetained then
          (if marked (ancestors i) ∧ nextState = desired then 1 else 0)
        else if marked (ancestors i) then
          transition.prob (particles (ancestors i)) desired else 0) /
        Fintype.card Particle := by
  unfold lineageExtensionFraction
  rw [forcedIndependentPopulation_indexedParticleAverage_expectation]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = nextRetained
  · simp [hi]
  · simp only [hi, if_false]
    by_cases hmarked : marked (ancestors i)
    · simp [hmarked, rowDistribution]
    · simp [hmarked]

/-- Contribution of only the unforced children to the conditional expected
extended-lineage fraction. -/
noncomputable def unforcedLineageExtensionFraction
    (transition : MarkovKernel Sample) (particles : Particle → Sample)
    (marked : Particle → Prop) [DecidablePred marked] (desired : Sample)
    (nextRetained : Particle) (ancestors : Particle → Particle) : ℝ :=
  (∑ i, if i = nextRetained then 0
    else if marked (ancestors i) then
      transition.prob (particles (ancestors i)) desired else 0) /
    Fintype.card Particle

omit [Nonempty Particle] in
/-- Dropping the single forced child's nonnegative contribution leaves a
valid lower bound on the conditional propagation expectation. This is the
one-step inequality that can safely be integrated over forced resampling. -/
theorem forcedPropagation_lineageExtensionFraction_ge_unforced
    (transition : MarkovKernel Sample) (particles : Particle → Sample)
    (ancestors : Particle → Particle) (nextRetained : Particle)
    (nextState desired : Sample) (marked : Particle → Prop)
    [DecidablePred marked] :
    unforcedLineageExtensionFraction transition particles marked desired
        nextRetained ancestors ≤
      ∑ next,
        (forcedIndependentPopulation
          (fun i => rowDistribution transition (particles (ancestors i)))
          nextRetained nextState).mass next *
            lineageExtensionFraction marked desired ancestors next := by
  rw [forcedPropagation_lineageExtensionFraction_expectation]
  unfold unforcedLineageExtensionFraction
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i = nextRetained
  · subst i
    simp only [if_true]
    split <;> norm_num
  · simp [hi]

omit [DecidableEq Sample] [Nonempty Particle] in
/-- Forced multinomial resampling integrates the unforced contribution
exactly. Every one of the `N - 1` ordinary children sees the same weighted
parental extension probability. -/
theorem forcedResampling_unforcedLineageExtensionFraction_expectation
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (retained nextRetained : Particle)
    (marked : Particle → Prop) [DecidablePred marked] (desired : Sample) :
    ∑ ancestors,
      (forcedIndependentPopulation (fun _ : Particle => weights)
        nextRetained retained).mass ancestors *
          unforcedLineageExtensionFraction transition particles marked desired
            nextRetained ancestors =
      ((Fintype.card Particle - 1 : ℕ) *
        (∑ parent, weights.mass parent *
          (if marked parent then
            transition.prob (particles parent) desired else 0))) /
        Fintype.card Particle := by
  let score : Particle → Particle → ℝ := fun i parent =>
    if i = nextRetained then 0
    else if marked parent then transition.prob (particles parent) desired else 0
  have h := forcedIndependentPopulation_indexedParticleAverage_expectation
    (law := fun _ : Particle => weights) nextRetained retained score
  calc
    ∑ ancestors,
        (forcedIndependentPopulation (fun _ : Particle => weights)
          nextRetained retained).mass ancestors *
            unforcedLineageExtensionFraction transition particles marked desired
              nextRetained ancestors =
        ∑ ancestors,
          (forcedIndependentPopulation (fun _ : Particle => weights)
            nextRetained retained).mass ancestors *
              indexedParticleAverage score ancestors := by rfl
    _ = (∑ i, if i = nextRetained then score i retained
          else ∑ s, weights.mass s * score i s) /
            Fintype.card Particle := h
    _ = ((Fintype.card Particle - 1 : ℕ) *
          (∑ parent, weights.mass parent *
            (if marked parent then
              transition.prob (particles parent) desired else 0))) /
          Fintype.card Particle := by
      congr 1
      let extensionMass := ∑ parent, weights.mass parent *
        (if marked parent then
          transition.prob (particles parent) desired else 0)
      have hsum :
          (∑ i, if i = nextRetained then score i retained
            else ∑ s, weights.mass s * score i s) =
          ∑ i : Particle, if i = nextRetained then 0 else extensionMass := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = nextRetained
        · simp [hi, score]
        · simp [hi, score, extensionMass]
      rw [hsum]
      exact sum_unforced_constant nextRetained extensionMass

omit [Nonempty Particle] in
/-- One complete forced resample--propagate stage preserves at least the
`(N - 1) / N` share of the weighted probability of extending a marked
genealogy. This is an aggregate expectation theorem, not a single-history
bound, and its count factor tends to one. -/
theorem forcedResamplePropagate_lineageExtensionFraction_ge
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (retained nextRetained : Particle)
    (nextState desired : Sample) (marked : Particle → Prop)
    [DecidablePred marked] :
    ((Fintype.card Particle - 1 : ℕ) *
        (∑ parent, weights.mass parent *
          (if marked parent then
            transition.prob (particles parent) desired else 0))) /
        Fintype.card Particle ≤
      ∑ ancestors,
        (forcedIndependentPopulation (fun _ : Particle => weights)
          nextRetained retained).mass ancestors *
          ∑ next,
            (forcedIndependentPopulation
              (fun i => rowDistribution transition (particles (ancestors i)))
              nextRetained nextState).mass next *
                lineageExtensionFraction marked desired ancestors next := by
  rw [← forcedResampling_unforcedLineageExtensionFraction_expectation
    weights transition particles retained nextRetained marked desired]
  apply Finset.sum_le_sum
  intro ancestors _
  apply mul_le_mul_of_nonneg_left
  · exact forcedPropagation_lineageExtensionFraction_ge_unforced
      transition particles ancestors nextRetained nextState desired marked
  · exact (forcedIndependentPopulation (fun _ : Particle => weights)
      nextRetained retained).nonneg ancestors

/-- Conditional propagation law after a vector of ancestor indices has been
drawn. -/
def propagatedPopulation (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (ancestors : Particle → Particle) :
    Distribution (Particle → Sample) :=
  independentPopulation fun j => rowDistribution transition (particles (ancestors j))

omit [DecidableEq Sample] [Nonempty Particle] in
/-- A propagated population has full support when the transition matrix does. -/
theorem propagatedPopulation_mass_pos (transition : MarkovKernel Sample)
    (hpos : ∀ x y, 0 < transition.prob x y)
    (particles : Particle → Sample) (ancestors : Particle → Particle)
    (next : Particle → Sample) :
    0 < (propagatedPopulation transition particles ancestors).mass next := by
  apply independentPopulation_mass_pos
  intro i x
  exact hpos _ x

omit [DecidableEq Sample] in
/-- One-step bootstrap resample--propagate identity.  Conditional expectation
of the next empirical average is the current normalized weighted average of
the transition expectation. -/
theorem resamplePropagate_particleAverage_expectation
    (weights : Distribution Particle) (particles : Particle → Sample)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ) :
    ∑ ancestors, (multinomialResampling weights).mass ancestors *
        (∑ next, (propagatedPopulation transition particles ancestors).mass next *
          particleAverage observable next) =
      ∑ i, weights.mass i *
        (∑ y, transition.prob (particles i) y * observable y) := by
  simp_rw [propagatedPopulation,
    independentPopulation_particleAverage_expectation]
  change ∑ ancestors, (multinomialResampling weights).mass ancestors *
      particleAverage
        (fun i => ∑ y, transition.prob (particles i) y * observable y)
        ancestors = _
  exact multinomialResampling_unbiased weights particles
    (fun x => ∑ y, transition.prob x y * observable y)

/-- Normalized empirical potential weights. Strict positivity is a convenient
finite prerequisite; support-sensitive zero handling can be added separately. -/
noncomputable def normalizedPotentialWeights
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) : Distribution Particle where
  mass i := potential (particles i) / ∑ j, potential (particles j)
  nonneg i := div_nonneg (le_of_lt (hpotential _))
    (Finset.sum_nonneg fun j _ => le_of_lt (hpotential (particles j)))
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos
      (fun j _ => hpotential (particles j)) Finset.univ_nonempty))

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Particle] in
/-- Strictly positive potentials give every ancestor index positive
resampling weight. -/
theorem normalizedPotentialWeights_mass_pos
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (i : Particle) :
    0 < (normalizedPotentialWeights potential hpotential particles).mass i := by
  unfold normalizedPotentialWeights
  exact div_pos (hpotential _) (Finset.sum_pos
    (fun j _ => hpotential (particles j)) Finset.univ_nonempty)

/-- One multiplicative oscillation constant for a strictly positive finite
potential. This is the primitive model quantity entering count-uniform
particle-Gibbs resampling estimates. -/
structure PotentialOscillationBound (potential : Sample → ℝ) (bound : ℝ) : Prop where
  bound_pos : 0 < bound
  le_mul : ∀ x y, potential x ≤ bound * potential y

/-- Total potential carried by all particles except one retained coordinate. -/
noncomputable def unforcedPotentialSum (potential : Sample → ℝ)
    {Particle : Type*} [Fintype Particle] [DecidableEq Particle]
    (particles : Particle → Sample) (retained : Particle) : ℝ :=
  ∑ i, if i = retained then 0 else potential (particles i)

omit [Nonempty Particle] in
/-- Exact first moment of an unforced empirical sum.  A cloud with one fixed
coordinate has `N - 1` ordinary coordinates, so averaging any score over the
cloud law gives exactly `N - 1` copies of its one-particle expectation.  This
is the linear input to the self-normalized ordinary-cloud comparison needed
by the aggregate particle-Gibbs induction. -/
theorem forcedIndependentPopulation_unforcedSum_expectation
    (law : Distribution Sample) (retained : Particle) (value : Sample)
    (score : Sample → ℝ) :
    (∑ particles,
        (forcedIndependentPopulation (fun _ : Particle => law) retained value).mass
            particles *
          (∑ i : Particle, if i = retained then 0 else score (particles i))) =
      (Fintype.card Particle - 1 : ℕ) *
        (∑ x, law.mass x * score x) := by
  classical
  calc
    (∑ particles,
        (forcedIndependentPopulation (fun _ : Particle => law) retained value).mass
            particles *
          (∑ i : Particle, if i = retained then 0 else score (particles i))) =
        ∑ i : Particle, ∑ particles,
          (forcedIndependentPopulation (fun _ : Particle => law) retained value).mass
              particles *
            (if i = retained then 0 else score (particles i)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i : Particle, if i = retained then 0
          else ∑ x, law.mass x * score x := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = retained
      · simp [hi]
      · simp only [hi, if_false]
        rw [forcedIndependentPopulation_coordinate_expectation
          (fun _ : Particle => law) retained value score i]
        simp [hi]
    _ = (Fintype.card Particle - 1 : ℕ) *
          (∑ x, law.mass x * score x) :=
      sum_unforced_constant retained _

omit [Nonempty Particle] in
/-- The preceding generic identity specialized to the ordinary-particle
potential normalizer used by conditional SMC. -/
theorem forcedIndependentPopulation_unforcedPotentialSum_expectation
    (law : Distribution Sample) (retained : Particle) (value : Sample)
    (potential : Sample → ℝ) :
    (∑ particles,
        (forcedIndependentPopulation (fun _ : Particle => law) retained value).mass
            particles *
          unforcedPotentialSum potential particles retained) =
      (Fintype.card Particle - 1 : ℕ) *
        (∑ x, law.mass x * potential x) := by
  exact forcedIndependentPopulation_unforcedSum_expectation
    law retained value potential

omit [Fintype Sample] [DecidableEq Sample] in
/-- Summing the oscillation comparison over every unforced coordinate bounds
the retained potential by the aggregate ordinary-particle potential. For
`N = extra + 1`, exactly `extra` comparisons are accumulated. -/
theorem retainedPotential_mul_extra_le_bound_mul_unforcedPotentialSum
    (potential : Sample → ℝ) (bound : ℝ)
    (certificate : PotentialOscillationBound potential bound)
    (extra : ℕ) (particles : Fin (extra + 1) → Sample)
    (retained : Fin (extra + 1)) :
    (extra : ℝ) * potential (particles retained) ≤
      bound * unforcedPotentialSum potential particles retained := by
  calc
    (extra : ℝ) * potential (particles retained) =
        ∑ i : Fin (extra + 1),
          if i = retained then 0 else potential (particles retained) := by
      rw [sum_unforced_constant]
      simp
    _ ≤ ∑ i : Fin (extra + 1),
          if i = retained then 0 else bound * potential (particles i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i = retained
      · simp [hi]
      · simpa [hi] using certificate.le_mul (particles retained) (particles i)
    _ = bound * unforcedPotentialSum potential particles retained := by
      unfold unforcedPotentialSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = retained <;> simp [hi]

omit [Fintype Sample] [DecidableEq Sample] in
/-- The complete potential normalizer is the retained term plus the unforced
sum. -/
theorem sum_potential_eq_retained_add_unforcedPotentialSum
    (potential : Sample → ℝ) {Particle : Type*}
    [Fintype Particle] [DecidableEq Particle]
    (particles : Particle → Sample) (retained : Particle) :
    (∑ i, potential (particles i)) =
      potential (particles retained) +
        unforcedPotentialSum potential particles retained := by
  unfold unforcedPotentialSum
  calc
    (∑ i, potential (particles i)) =
        ∑ i, ((if i = retained then potential (particles retained) else 0) +
          (if i = retained then 0 else potential (particles i))) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = retained <;> simp [hi]
    _ = (∑ i, if i = retained then potential (particles retained) else 0) +
        ∑ i, if i = retained then 0 else potential (particles i) := by
      rw [Finset.sum_add_distrib]
    _ = potential (particles retained) +
        ∑ i, if i = retained then 0 else potential (particles i) := by simp

omit [Fintype Sample] [DecidableEq Sample] in
/-- Oscillation converts the full normalization denominator into the standard
particle-Gibbs penalty: the retained particle enlarges the ordinary-particle
sum by at most the factor `(extra + bound) / extra`. -/
theorem sum_potential_le_penalty_mul_unforcedPotentialSum
    (potential : Sample → ℝ) (bound : ℝ)
    (certificate : PotentialOscillationBound potential bound)
    (extra : ℕ) (hextra : 0 < extra)
    (particles : Fin (extra + 1) → Sample)
    (retained : Fin (extra + 1)) :
    (∑ i, potential (particles i)) ≤
      ((extra : ℝ) + bound) / extra *
        unforcedPotentialSum potential particles retained := by
  have hextraReal : 0 < (extra : ℝ) := by exact_mod_cast hextra
  have hretained :=
    retainedPotential_mul_extra_le_bound_mul_unforcedPotentialSum
      potential bound certificate extra particles retained
  rw [sum_potential_eq_retained_add_unforcedPotentialSum]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hextraReal).2
  nlinarith

omit [Fintype Sample] [DecidableEq Sample] in
/-- With at least one ordinary particle and positive potentials, the unforced
normalizer is strictly positive. -/
theorem unforcedPotentialSum_pos
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (extra : ℕ) (hextra : 0 < extra)
    (particles : Fin (extra + 1) → Sample)
    (retained : Fin (extra + 1)) :
    0 < unforcedPotentialSum potential particles retained := by
  obtain ⟨ordinary, hordinary⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card (Fin (extra + 1)) by simp; omega) retained
  unfold unforcedPotentialSum
  apply Finset.sum_pos'
  · intro i _
    by_cases hi : i = retained
    · simp [hi]
    · simpa [hi] using (hpotential (particles i)).le
  · refine ⟨ordinary, Finset.mem_univ ordinary, ?_⟩
    simp [hordinary, hpotential]

/-- Algebraic denominator-comparison lemma underlying the sharp PG factor. -/
theorem penalty_ratio_mul_div_le_div
    {extra bound unforcedDenominator fullDenominator
      unforcedNumerator fullNumerator : ℝ}
    (hextra : 0 < extra) (hbound : 0 < bound)
    (hunforcedDenominator : 0 < unforcedDenominator)
    (hfullDenominator : 0 < fullDenominator)
    (hunforcedNumerator : 0 ≤ unforcedNumerator)
    (hnumerator : unforcedNumerator ≤ fullNumerator)
    (hdenominator : fullDenominator ≤
      (extra + bound) / extra * unforcedDenominator) :
    extra / (extra + bound) *
        (unforcedNumerator / unforcedDenominator) ≤
      fullNumerator / fullDenominator := by
  apply (le_div_iff₀ hfullDenominator).2
  calc
    extra / (extra + bound) *
          (unforcedNumerator / unforcedDenominator) * fullDenominator ≤
        extra / (extra + bound) *
          (unforcedNumerator / unforcedDenominator) *
            ((extra + bound) / extra * unforcedDenominator) := by
      apply mul_le_mul_of_nonneg_left hdenominator
      positivity
    _ = unforcedNumerator := by field_simp
    _ ≤ fullNumerator := hnumerator

/-- Unnormalized marked transition mass contributed by ordinary (unforced)
particles. -/
noncomputable def unforcedPotentialTransitionMass
    (potential : Sample → ℝ) (transition : MarkovKernel Sample)
    {Particle : Type*} [Fintype Particle] [DecidableEq Particle]
    (particles : Particle → Sample) (retained : Particle)
    (marked : Particle → Prop) [DecidablePred marked]
    (desired : Sample) : ℝ :=
  ∑ i, if i = retained then 0 else
    potential (particles i) *
      (if marked i then transition.prob (particles i) desired else 0)

omit [DecidableEq Sample] in
/-- Sharp deterministic resampling comparison. Normalizing with the retained
particle loses only `extra / (extra + bound)` relative to normalizing the
ordinary particles among themselves. -/
theorem normalizedPotentialWeights_markedTransition_ge_unforced
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample) (bound : ℝ)
    (certificate : PotentialOscillationBound potential bound)
    (extra : ℕ) (hextra : 0 < extra)
    (particles : Fin (extra + 1) → Sample)
    (retained : Fin (extra + 1))
    (marked : Fin (extra + 1) → Prop) [DecidablePred marked]
    (desired : Sample) :
    (extra : ℝ) / ((extra : ℝ) + bound) *
        (unforcedPotentialTransitionMass potential transition particles retained
          marked desired /
          unforcedPotentialSum potential particles retained) ≤
      ∑ parent,
        (normalizedPotentialWeights potential hpotential particles).mass parent *
          (if marked parent then
            transition.prob (particles parent) desired else 0) := by
  let unforcedNumerator := unforcedPotentialTransitionMass potential transition
    particles retained marked desired
  let fullNumerator := ∑ parent,
    potential (particles parent) *
      (if marked parent then transition.prob (particles parent) desired else 0)
  let unforcedDenominator := unforcedPotentialSum potential particles retained
  let fullDenominator := ∑ i, potential (particles i)
  have hextraReal : 0 < (extra : ℝ) := by exact_mod_cast hextra
  have hfullDenominator : 0 < fullDenominator := by
    dsimp only [fullDenominator]
    exact Finset.sum_pos (fun i _ => hpotential (particles i)) Finset.univ_nonempty
  have hunforcedDenominator : 0 < unforcedDenominator := by
    exact unforcedPotentialSum_pos potential hpotential extra hextra particles retained
  have hunforcedNumerator : 0 ≤ unforcedNumerator := by
    dsimp only [unforcedNumerator, unforcedPotentialTransitionMass]
    apply Finset.sum_nonneg
    intro i _
    by_cases hi : i = retained
    · simp [hi]
    · simp only [hi, if_false]
      by_cases hm : marked i
      · simp only [hm, if_true]
        exact mul_nonneg (hpotential _).le (transition.nonneg _ _)
      · simp [hm]
  have hnumerator : unforcedNumerator ≤ fullNumerator := by
    dsimp only [unforcedNumerator, fullNumerator,
      unforcedPotentialTransitionMass]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = retained
    · simp only [hi, if_true]
      by_cases hm : marked retained
      · simp only [hm, if_true]
        exact mul_nonneg (hpotential _).le (transition.nonneg _ _)
      · simp [hm]
    · simp [hi]
  have hdenominator : fullDenominator ≤
      ((extra : ℝ) + bound) / extra * unforcedDenominator := by
    exact sum_potential_le_penalty_mul_unforcedPotentialSum
      potential bound certificate extra hextra particles retained
  have halgebra := penalty_ratio_mul_div_le_div
    hextraReal certificate.bound_pos hunforcedDenominator hfullDenominator
    hunforcedNumerator hnumerator hdenominator
  change (extra : ℝ) / ((extra : ℝ) + bound) *
      (unforcedNumerator / unforcedDenominator) ≤ _
  calc
    _ ≤ fullNumerator / fullDenominator := halgebra
    _ = ∑ parent,
        (normalizedPotentialWeights potential hpotential particles).mass parent *
          (if marked parent then
            transition.prob (particles parent) desired else 0) := by
      dsimp only [fullNumerator, fullDenominator]
      unfold normalizedPotentialWeights
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro parent _
      ring

/-- Combined sharp one-stage conditional-SMC comparison. The first factor is
the ordinary-child share and the second is the retained-normalizer penalty;
later path-label recursion cancels the intermediate ordinary-cloud
normalization rather than accumulating a crude `1 / bound` loss. -/
theorem forcedResamplePropagate_lineageExtensionFraction_ge_sharpUnforced
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample) (bound : ℝ)
    (certificate : PotentialOscillationBound potential bound)
    (extra : ℕ) (hextra : 0 < extra)
    (particles : Fin (extra + 1) → Sample)
    (retained nextRetained : Fin (extra + 1))
    (nextState desired : Sample)
    (marked : Fin (extra + 1) → Prop) [DecidablePred marked] :
    (extra : ℝ) / (extra + 1) *
        ((extra : ℝ) / ((extra : ℝ) + bound) *
          (unforcedPotentialTransitionMass potential transition particles
              retained marked desired /
            unforcedPotentialSum potential particles retained)) ≤
      ∑ ancestors,
        (forcedIndependentPopulation
          (fun _ : Fin (extra + 1) =>
            normalizedPotentialWeights potential hpotential particles)
          nextRetained retained).mass ancestors *
          ∑ next,
            (forcedIndependentPopulation
              (fun i => rowDistribution transition (particles (ancestors i)))
              nextRetained nextState).mass next *
                lineageExtensionFraction marked desired ancestors next := by
  let weightedExtension := ∑ parent,
    (normalizedPotentialWeights potential hpotential particles).mass parent *
      (if marked parent then transition.prob (particles parent) desired else 0)
  have hsharp := normalizedPotentialWeights_markedTransition_ge_unforced
    potential hpotential transition bound certificate extra hextra particles
      retained marked desired
  have hstage := forcedResamplePropagate_lineageExtensionFraction_ge
    (normalizedPotentialWeights potential hpotential particles)
    transition particles retained nextRetained nextState desired marked
  calc
    (extra : ℝ) / (extra + 1) *
          ((extra : ℝ) / ((extra : ℝ) + bound) *
            (unforcedPotentialTransitionMass potential transition particles
                retained marked desired /
              unforcedPotentialSum potential particles retained)) ≤
        (extra : ℝ) / (extra + 1) * weightedExtension := by
      apply mul_le_mul_of_nonneg_left hsharp
      positivity
    _ = ((Fintype.card (Fin (extra + 1)) - 1 : ℕ) * weightedExtension) /
          Fintype.card (Fin (extra + 1)) := by
      simp [weightedExtension]
      ring
    _ ≤ _ := hstage

/-- Explicit finite oscillation constant, chosen as the sum of every ordered
potential ratio. It is conservative but depends only on the model, never on
the particle count. -/
noncomputable def finitePotentialOscillationConstant
    (potential : Sample → ℝ) : ℝ :=
  ∑ x, ∑ y, potential x / potential y

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- Strict positivity on a nonempty finite state space automatically supplies
a count-independent oscillation certificate. -/
theorem finitePotentialOscillationBound
    [Nonempty Sample] (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) :
    PotentialOscillationBound potential
      (finitePotentialOscillationConstant potential) := by
  constructor
  · unfold finitePotentialOscillationConstant
    apply Finset.sum_pos
    · intro x _hx
      apply Finset.sum_pos
      · intro y _hy
        exact div_pos (hpotential x) (hpotential y)
      · exact Finset.univ_nonempty
    · exact Finset.univ_nonempty
  · intro x y
    have hratio : potential x / potential y ≤
        finitePotentialOscillationConstant potential := by
      unfold finitePotentialOscillationConstant
      exact (Finset.single_le_sum
        (fun x' _ => Finset.sum_nonneg fun y' _ =>
          div_nonneg (hpotential x').le (hpotential y').le)
        (Finset.mem_univ x)).trans' <|
          Finset.single_le_sum
            (fun y' _ => div_nonneg (hpotential x).le (hpotential y').le)
            (Finset.mem_univ y)
    have hy := hpotential y
    calc
      potential x = (potential x / potential y) * potential y := by
        field_simp
      _ ≤ finitePotentialOscillationConstant potential * potential y :=
        mul_le_mul_of_nonneg_right hratio hy.le

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- Every positive finite oscillation constant is at least one. -/
theorem one_le_finitePotentialOscillationConstant
    [Nonempty Sample] (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) :
    1 ≤ finitePotentialOscillationConstant potential := by
  let x : Sample := Classical.choice inferInstance
  have hcompare := (finitePotentialOscillationBound potential hpotential).le_mul x x
  have hx := hpotential x
  nlinarith

/-- Conservative candidate particle-Gibbs penalty for one potential slice.
Besides the
retained-particle denominator cost, the second copy of the oscillation bound
accounts for comparison of the self-normalized ordinary cloud with the exact
normalized Feynman--Kac target. Positivity is proved below; establishing the
full recursive minorization with this candidate remains a separate theorem. -/
noncomputable def finitePotentialParticleGibbsCandidatePenalty
    (potential : Sample → ℝ) : ℝ :=
  2 * finitePotentialOscillationConstant potential - 1

omit [DecidableEq Sample] [DecidableEq Particle] in
theorem finitePotentialParticleGibbsCandidatePenalty_pos
    [Nonempty Sample] (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) :
    0 < finitePotentialParticleGibbsCandidatePenalty potential := by
  unfold finitePotentialParticleGibbsCandidatePenalty
  linarith [one_le_finitePotentialOscillationConstant potential hpotential]

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Particle] in
/-- A potential oscillation bound gives a particle-count-uniform lower bound
on every normalized ancestor weight: `wᵢ ≥ 1 / (N B)`. -/
theorem normalizedPotentialWeights_mass_ge_inv_card_mul
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    {bound : ℝ} (hoscillation : PotentialOscillationBound potential bound)
    (particles : Particle → Sample) (i : Particle) :
    1 / ((Fintype.card Particle : ℝ) * bound) ≤
      (normalizedPotentialWeights potential hpotential particles).mass i := by
  unfold normalizedPotentialWeights
  have hsumPos : 0 < ∑ j, potential (particles j) :=
    Finset.sum_pos (fun j _ => hpotential _) Finset.univ_nonempty
  have hcardPos : 0 < (Fintype.card Particle : ℝ) := by positivity
  have hdenominatorPos :
      0 < (Fintype.card Particle : ℝ) * bound :=
    mul_pos hcardPos hoscillation.bound_pos
  rw [div_le_div_iff₀ hdenominatorPos hsumPos]
  calc
    1 * (∑ j, potential (particles j)) ≤
        1 * (∑ _j : Particle, bound * potential (particles i)) := by
      gcongr with j
      exact hoscillation.le_mul _ _
    _ = potential (particles i) *
        ((Fintype.card Particle : ℝ) * bound) := by
      simp
      ring

omit [DecidableEq Sample] [DecidableEq Particle] in
/-- Fully primitive finite-state specialization of the normalized resampling
weight bound. Its constant is independent of the particle type. -/
theorem normalizedPotentialWeights_mass_ge_finiteOscillation
    [Nonempty Sample]
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (i : Particle) :
    1 / ((Fintype.card Particle : ℝ) *
        finitePotentialOscillationConstant potential) ≤
      (normalizedPotentialWeights potential hpotential particles).mass i :=
  normalizedPotentialWeights_mass_ge_inv_card_mul potential hpotential
    (finitePotentialOscillationBound potential hpotential) particles i

omit [Fintype Sample] [DecidableEq Sample] [DecidableEq Particle] in
/-- Expectation under normalized empirical potential weights is exactly the
ratio of the weighted and unweighted particle averages. -/
theorem finiteExpectation_normalizedPotentialWeights
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (score : Sample → ℝ) :
    (∑ i,
      (normalizedPotentialWeights potential hpotential particles).mass i *
        score (particles i)) =
      particleAverage (fun x => potential x * score x) particles /
        particleAverage potential particles := by
  unfold normalizedPotentialWeights particleAverage
  have hsum : (∑ j, potential (particles j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => hpotential (particles j))
      Finset.univ_nonempty)
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [show (∑ i, potential (particles i) /
      (∑ j, potential (particles j)) * score (particles i)) =
      (∑ i, potential (particles i) * score (particles i)) /
        (∑ j, potential (particles j)) by
    calc
      _ = ∑ i, (potential (particles i) * score (particles i)) /
          (∑ j, potential (particles j)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by rw [Finset.sum_div]]
  field_simp

omit [DecidableEq Sample] in
/-- Multiplying the normalized resample--propagate expectation by the current
average potential cancels the empirical normalizer. This is the local
Feynman--Kac identity used in the multi-time induction. -/
theorem weighted_resamplePropagate_identity
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (particles : Particle → Sample) (transition : MarkovKernel Sample)
    (observable : Sample → ℝ) :
    particleAverage potential particles *
        (∑ ancestors,
          (multinomialResampling
            (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
          (∑ next, (propagatedPopulation transition particles ancestors).mass next *
            particleAverage observable next)) =
      particleAverage
        (fun x => potential x *
          ∑ y, transition.prob x y * observable y) particles := by
  rw [resamplePropagate_particleAverage_expectation]
  unfold particleAverage normalizedPotentialWeights
  have hsum : (∑ j, potential (particles j)) ≠ 0 :=
    ne_of_gt (Finset.sum_pos (fun j _ => hpotential (particles j))
      Finset.univ_nonempty)
  have hcard : (Fintype.card Particle : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ((∑ i, potential (particles i)) / Fintype.card Particle) *
      (∑ i, (potential (particles i) / ∑ j, potential (particles j)) *
        ∑ y, transition.prob (particles i) y * observable y) =
    (∑ i, potential (particles i) *
      ∑ y, transition.prob (particles i) y * observable y) /
        Fintype.card Particle
  field_simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- One-particle unnormalized Feynman--Kac transform. -/
noncomputable def feynmanKacTransform (potential : Sample → ℝ)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ) : Sample → ℝ :=
  fun x => potential x * ∑ y, transition.prob x y * observable y

/-- Particle Feynman--Kac transform: multiply the conditional expectation
after multinomial resample--propagate by the current average potential. -/
noncomputable def particleFeynmanKacTransform
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample)
    (observable : (Particle → Sample) → ℝ) : (Particle → Sample) → ℝ :=
  fun particles => particleAverage potential particles *
    ∑ ancestors,
      (multinomialResampling
        (normalizedPotentialWeights potential hpotential particles)).mass ancestors *
      ∑ next, (propagatedPopulation transition particles ancestors).mass next *
        observable next

omit [DecidableEq Sample] in
/-- The particle transform maps an empirical average to the empirical average
of the exact one-particle Feynman--Kac transform. -/
theorem particleFeynmanKacTransform_particleAverage
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ)
    (particles : Particle → Sample) :
    particleFeynmanKacTransform potential hpotential transition
        (particleAverage observable) particles =
      particleAverage (feynmanKacTransform potential transition observable)
        particles := by
  exact weighted_resamplePropagate_identity potential hpotential particles
    transition observable

omit [DecidableEq Sample] in
/-- Arbitrary finite-horizon Feynman--Kac identity, conditional on the initial
particle cloud. Iteration expands to the usual product of successive average
potentials and nested resample--propagate expectations. -/
theorem particleFeynmanKacTransform_iterate
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (transition : MarkovKernel Sample) (observable : Sample → ℝ)
    (n : ℕ) (particles : Particle → Sample) :
    (particleFeynmanKacTransform potential hpotential transition)^[n]
        (particleAverage observable) particles =
      particleAverage ((feynmanKacTransform potential transition)^[n] observable)
        particles := by
  induction n generalizing observable with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hmap :
          particleFeynmanKacTransform potential hpotential transition
              (particleAverage (Particle := Particle) observable) =
            particleAverage (Particle := Particle)
              (feynmanKacTransform potential transition observable) := by
        funext cloud
        exact particleFeynmanKacTransform_particleAverage potential hpotential
          transition observable cloud
      rw [hmap]
      exact ih (feynmanKacTransform potential transition observable)

omit [DecidableEq Sample] in
/-- After an iid initial cloud, the finite-horizon particle normalizing
estimator has exactly the corresponding one-particle Feynman--Kac expectation. -/
theorem iid_particleFeynmanKacTransform_iterate_expectation
    (initial : Distribution Sample) (potential : Sample → ℝ)
    (hpotential : ∀ x, 0 < potential x) (transition : MarkovKernel Sample)
    (observable : Sample → ℝ) (n : ℕ) :
    ∑ particles, (iidPopulation (Particle := Particle) initial).mass particles *
        ((particleFeynmanKacTransform potential hpotential transition)^[n]
          (particleAverage observable) particles) =
      ∑ x, initial.mass x *
        ((feynmanKacTransform potential transition)^[n] observable) x := by
  simp_rw [particleFeynmanKacTransform_iterate potential hpotential transition
    observable n]
  exact iidPopulation_particleAverage_expectation initial _

/-- One time step of a finite, possibly time-inhomogeneous Feynman--Kac
model. Strictly positive potentials make multinomial normalization total. -/
structure FeynmanKacStep (Sample : Type*) [Fintype Sample] where
  potential : Sample → ℝ
  potential_pos : ∀ x, 0 < potential x
  transition : MarkovKernel Sample

/-- Backward composition of a time-varying sequence of exact one-particle
Feynman--Kac transforms. -/
noncomputable def feynmanKacSequence :
    List (FeynmanKacStep Sample) → (Sample → ℝ) → Sample → ℝ
  | [], observable => observable
  | step :: steps, observable =>
      feynmanKacTransform step.potential step.transition
        (feynmanKacSequence steps observable)

/-- Matching time-varying particle transform, expressed as nested conditional
resample--propagate expectations. -/
noncomputable def particleFeynmanKacSequence :
    List (FeynmanKacStep Sample) →
      ((Particle → Sample) → ℝ) → (Particle → Sample) → ℝ
  | [], observable => observable
  | step :: steps, observable =>
      particleFeynmanKacTransform step.potential step.potential_pos
        step.transition (particleFeynmanKacSequence steps observable)

omit [DecidableEq Sample] in
/-- Time-inhomogeneous finite-horizon SMC expectation identity, conditional on
the initial cloud. -/
theorem particleFeynmanKacSequence_particleAverage
    (steps : List (FeynmanKacStep Sample)) (observable : Sample → ℝ) :
    particleFeynmanKacSequence (Particle := Particle) steps
        (particleAverage observable) =
      particleAverage (feynmanKacSequence steps observable) := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      rw [particleFeynmanKacSequence, feynmanKacSequence, ih]
      funext particles
      exact particleFeynmanKacTransform_particleAverage step.potential
        step.potential_pos step.transition _ particles

omit [DecidableEq Sample] in
/-- An iid initial population turns the time-inhomogeneous particle sequence
into exactly the corresponding one-particle Feynman--Kac expectation. -/
theorem iid_particleFeynmanKacSequence_expectation
    (initial : Distribution Sample) (steps : List (FeynmanKacStep Sample))
    (observable : Sample → ℝ) :
    ∑ particles, (iidPopulation (Particle := Particle) initial).mass particles *
        particleFeynmanKacSequence (Particle := Particle) steps
          (particleAverage observable) particles =
      ∑ x, initial.mass x * feynmanKacSequence steps observable x := by
  rw [particleFeynmanKacSequence_particleAverage steps observable]
  exact iidPopulation_particleAverage_expectation initial _

/-- Lift a state-indexed one-particle unbiased score into a finite iid particle
estimator usable by pseudo-marginal MH. -/
noncomputable def estimator
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1) :
    Estimator State (Particle → Sample) where
  law x := iidPopulation (law x)
  value x samples := particleAverage (score x) samples
  nonneg x samples := particleAverage_nonneg (hscore x) samples
  unbiased x := iidPopulation_particleAverage_unbiased
    (law x) (score x) (hunbiased x)

/-- Particle importance pseudo-marginal MH: propose a state and draw a fresh
iid cloud at the proposal, retaining the current cloud on rejection. -/
noncomputable def particleIndependentMH
    (target : Distribution State)
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1)
    (proposal : MarkovKernel State) :
    MarkovKernel (State × (Particle → Sample)) :=
  PseudoMarginal.kernel target
    (estimator (Particle := Particle) law score hscore hunbiased) proposal

/-- Exact stationarity of particle importance MH on its extended state. -/
theorem particleIndependentMH_stationary
    (target : Distribution State)
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1)
    (proposal : MarkovKernel State) :
    (particleIndependentMH (Particle := Particle) target law score hscore
      hunbiased proposal).Stationary
      (PseudoMarginal.extendedTarget target
        (estimator (Particle := Particle) law score hscore hunbiased)) :=
  PseudoMarginal.stationary target
    (estimator (Particle := Particle) law score hscore hunbiased) proposal

omit [DecidableEq State] [DecidableEq Sample] in
/-- The stationary state marginal of particle importance MH is exactly the
desired target for every positive finite particle count. -/
theorem particleIndependentMH_state_marginal
    (target : Distribution State)
    (law : State → Distribution Sample)
    (score : State → Sample → ℝ)
    (hscore : ∀ x s, 0 ≤ score x s)
    (hunbiased : ∀ x, ∑ s, (law x).mass s * score x s = 1)
    (x : State) :
    ∑ cloud, (PseudoMarginal.extendedTarget target
      (estimator (Particle := Particle) law score hscore hunbiased)).mass
        (x, cloud) = target.mass x :=
  PseudoMarginal.state_marginal target
    (estimator (Particle := Particle) law score hscore hunbiased) x

end Mcmc.Finite.ParticleEstimator
