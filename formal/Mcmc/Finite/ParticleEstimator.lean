import Mcmc.Finite.PseudoMarginal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
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

/-- Finite-distribution Jensen inequality for the reciprocal. This form keeps
the probability weights explicit and is the nonlinear ingredient in
leave-one-out bounds for self-normalized particle systems. -/
theorem one_div_expectation_le_expectation_one_div
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : Distribution α) (denominator : α → ℝ)
    (hdenominator : ∀ x, 0 < denominator x) :
    1 / (∑ x, law.mass x * denominator x) ≤
      ∑ x, law.mass x * (1 / denominator x) := by
  have hjensen :=
    (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn.map_sum_le
      (t := Finset.univ) (w := law.mass) (p := denominator)
      (fun x _ => law.nonneg x) law.sum_mass
      (fun x _ => hdenominator x)
  simpa [one_div, zpow_neg_one, smul_eq_mul] using hjensen

/-- A deterministic upper bound on a positive random denominator turns the
reciprocal Jensen inequality into the lower bound used by leave-one-out
arguments. -/
theorem one_div_upper_le_expectation_one_div
    {α : Type*} [Fintype α] [DecidableEq α]
    (law : Distribution α) (denominator : α → ℝ) (upper : ℝ)
    (hdenominator : ∀ x, 0 < denominator x)
    (hmean : 0 < ∑ x, law.mass x * denominator x)
    (hupper : (∑ x, law.mass x * denominator x) ≤ upper) :
    1 / upper ≤ ∑ x, law.mass x * (1 / denominator x) := by
  exact (one_div_le_one_div_of_le hmean hupper).trans
    (one_div_expectation_le_expectation_one_div law denominator hdenominator)

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

omit [Nonempty Particle] in
/-- Product Fubini: independently sample parents and then conditionally
independent children coordinatewise, or independently sample directly from
each coordinate's bound law. -/
theorem independentPopulation_bind_eq_independentPopulation_bind
    {Parent Child : Type*} [Fintype Parent] [Fintype Child]
    [DecidableEq Parent] [DecidableEq Child]
    (parentLaw : Particle → Distribution Parent)
    (childLaw : Particle → Parent → Distribution Child) :
    Distribution.bind (independentPopulation parentLaw) (fun parents =>
      independentPopulation (fun i => childLaw i (parents i))) =
      independentPopulation (fun i =>
        Distribution.bind (parentLaw i) (childLaw i)) := by
  apply Distribution.ext
  funext children
  unfold Distribution.bind independentPopulation
  change (∑ parents : Particle → Parent,
      (∏ i, (parentLaw i).mass (parents i)) *
        ∏ i, (childLaw i (parents i)).mass (children i)) =
    ∏ i, ∑ parent,
      (parentLaw i).mass parent * (childLaw i parent).mass (children i)
  calc
    (∑ parents : Particle → Parent,
        (∏ i, (parentLaw i).mass (parents i)) *
          ∏ i, (childLaw i (parents i)).mass (children i)) =
      ∑ parents : Particle → Parent, ∏ i,
        ((parentLaw i).mass (parents i) *
          (childLaw i (parents i)).mass (children i)) := by
        apply Finset.sum_congr rfl
        intro parents _
        rw [Finset.prod_mul_distrib]
    _ = _ := (Fintype.prod_sum
      (f := fun i : Particle => fun parent : Parent =>
        (parentLaw i).mass parent *
          (childLaw i parent).mass (children i))).symm

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

/-- Mapping a point mass gives the point mass of the image. -/
theorem map_pointDistribution {Output : Type*} [Fintype Output]
    [DecidableEq Output] (value : Sample) (transform : Sample → Output) :
    Distribution.map (pointDistribution value) transform =
      pointDistribution (transform value) := by
  apply Distribution.ext
  funext output
  simp only [Distribution.map, Distribution.bind_mass, pointDistribution]
  rw [Finset.sum_eq_single value]
  · simp
  · intro other _ hother
    simp [hother]
  · simp

omit [Nonempty Particle] in
/-- An independent population of coordinate point masses is the point mass
of the complete coordinate vector. -/
theorem independentPopulation_pointDistribution
    (value : Particle → Sample) :
    independentPopulation (fun i => pointDistribution (value i)) =
      pointDistribution value := by
  classical
  apply Distribution.ext
  funext samples
  unfold independentPopulation pointDistribution
  change (∏ j : Particle, if samples j = value j then 1 else 0) =
    (if samples = value then 1 else 0)
  by_cases h : samples = value
  · subst samples
    simp
  · have hexists : ∃ i, samples i ≠ value i := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    obtain ⟨i, hi⟩ := hexists
    simp only [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

omit [Nonempty Particle] in
/-- Coordinatewise deterministic maps commute with independent-population
sampling. -/
theorem map_independentPopulation_coordinatewise
    {Output : Type*} [Fintype Output] [DecidableEq Output]
    (law : Particle → Distribution Sample) (transform : Particle → Sample → Output) :
    Distribution.map (independentPopulation law)
        (fun samples i => transform i (samples i)) =
      independentPopulation (fun i => Distribution.map (law i) (transform i)) := by
  unfold Distribution.map
  calc
    Distribution.bind (independentPopulation law) (fun samples =>
        pointDistribution (fun i => transform i (samples i))) =
      Distribution.bind (independentPopulation law) (fun samples =>
        independentPopulation (fun i =>
          pointDistribution (transform i (samples i)))) := by
            congr 1
            funext samples
            exact (independentPopulation_pointDistribution
              (fun i => transform i (samples i))).symm
    _ = independentPopulation (fun i =>
        Distribution.bind (law i) (fun sample =>
          pointDistribution (transform i sample))) :=
      independentPopulation_bind_eq_independentPopulation_bind law
        (fun i sample => pointDistribution (transform i sample))

/-- Independent population with one distinguished coordinate forced to a
specified value. All other coordinates retain their supplied laws. This is
the elementary initialization/propagation law used by conditional SMC. -/
def forcedIndependentPopulation (law : Particle → Distribution Sample)
    (retained : Particle) (value : Sample) : Distribution (Particle → Sample) :=
  independentPopulation fun i =>
    if i = retained then pointDistribution value else law i

/-- Independent population with two named coordinates forced. When the
coordinates are distinct, this is the conditional remainder law obtained by
fixing both a retained particle and one selected ordinary particle. -/
def doublyForcedIndependentPopulation (law : Particle → Distribution Sample)
    (first : Particle) (firstValue : Sample)
    (second : Particle) (secondValue : Sample) :
    Distribution (Particle → Sample) :=
  independentPopulation fun i =>
    if i = first then pointDistribution firstValue
    else if i = second then pointDistribution secondValue
    else law i

omit [Nonempty Particle] in
/-- Sampling one coordinate and then forcing it to the sampled value rebuilds
the original independent product law. -/
theorem bind_forcedIndependentPopulation_eq_independentPopulation
    (law : Particle → Distribution Sample) (selected : Particle) :
    Distribution.bind (law selected) (fun value =>
      forcedIndependentPopulation law selected value) =
      independentPopulation law := by
  classical
  apply Distribution.ext
  funext samples
  simp only [Distribution.bind_mass]
  rw [Finset.sum_eq_single (samples selected)]
  · unfold forcedIndependentPopulation independentPopulation
    change (law selected).mass (samples selected) *
        (∏ i, (if i = selected then pointDistribution (samples selected)
          else law i).mass (samples i)) =
      ∏ i, (law i).mass (samples i)
    let f : Particle → ℝ := fun i => (law i).mass (samples i)
    have hfull := Finset.mul_prod_erase Finset.univ f
      (Finset.mem_univ selected)
    have hforced :
        (∏ i, (if i = selected then pointDistribution (samples selected)
          else law i).mass (samples i)) =
          ∏ i ∈ Finset.univ.erase selected, f i := by
      rw [← Finset.prod_erase Finset.univ (a := selected)]
      · apply Finset.prod_congr rfl
        intro i hi
        have hne : i ≠ selected := (Finset.mem_erase.mp hi).1
        simp [hne, f]
      · simp [pointDistribution]
    rw [hforced]
    simpa [f] using hfull
  · intro other _ hother
    apply mul_eq_zero_of_right
    unfold forcedIndependentPopulation independentPopulation
    apply Finset.prod_eq_zero (Finset.mem_univ selected)
    simp [pointDistribution, Ne.symm hother]
  · simp

omit [Nonempty Particle] in
/-- Disintegrating a one-coordinate-forced product at any distinct ordinary
coordinate gives the corresponding two-coordinate-forced product. -/
theorem forcedIndependentPopulation_bind_doublyForced
    (law : Particle → Distribution Sample)
    (retained selected : Particle) (hneq : retained ≠ selected)
    (retainedValue : Sample) :
    Distribution.bind (law selected) (fun selectedValue =>
      doublyForcedIndependentPopulation law retained retainedValue
        selected selectedValue) =
      forcedIndependentPopulation law retained retainedValue := by
  let retainedLaw : Particle → Distribution Sample := fun i =>
    if i = retained then pointDistribution retainedValue else law i
  have hselected : retainedLaw selected = law selected := by
    simp [retainedLaw, Ne.symm hneq]
  have hdouble (selectedValue : Sample) :
      forcedIndependentPopulation retainedLaw selected selectedValue =
        doublyForcedIndependentPopulation law retained retainedValue
          selected selectedValue := by
    apply Distribution.ext
    funext samples
    unfold forcedIndependentPopulation doublyForcedIndependentPopulation
    unfold independentPopulation
    apply Finset.prod_congr rfl
    intro i _
    by_cases hfirst : i = retained
    · subst i
      simp [hneq, retainedLaw]
    · by_cases hsecond : i = selected <;>
        simp [hfirst, hsecond, retainedLaw, Ne.symm hneq]
  calc
    Distribution.bind (law selected) (fun selectedValue =>
        doublyForcedIndependentPopulation law retained retainedValue
          selected selectedValue) =
      Distribution.bind (retainedLaw selected) (fun selectedValue =>
        forcedIndependentPopulation retainedLaw selected selectedValue) := by
          rw [hselected]
          congr 1
          funext selectedValue
          exact (hdouble selectedValue).symm
    _ = independentPopulation retainedLaw :=
      bind_forcedIndependentPopulation_eq_independentPopulation retainedLaw selected
    _ = forcedIndependentPopulation law retained retainedValue := rfl

omit [Nonempty Particle] in
/-- A two-coordinate-forced product has zero mass away from either prescribed
coordinate value. -/
theorem doublyForcedIndependentPopulation_incompatible_zero
    (law : Particle → Distribution Sample)
    (first : Particle) (firstValue : Sample)
    (second : Particle) (secondValue : Sample) (hneq : first ≠ second)
    (samples : Particle → Sample)
    (hincompatible : samples first ≠ firstValue ∨
      samples second ≠ secondValue) :
    (doublyForcedIndependentPopulation law first firstValue second secondValue).mass
        samples = 0 := by
  unfold doublyForcedIndependentPopulation independentPopulation
  rcases hincompatible with hfirst | hsecond
  · apply Finset.prod_eq_zero (Finset.mem_univ first)
    simp [pointDistribution, hfirst]
  · apply Finset.prod_eq_zero (Finset.mem_univ second)
    simp [pointDistribution, Ne.symm hneq, hsecond]

omit [Nonempty Particle] in
/-- Expectations under a two-coordinate-forced product may replace an
observable by any expression agreeing on compatible populations. -/
theorem doublyForcedIndependentPopulation_expectation_congr
    (law : Particle → Distribution Sample)
    (first : Particle) (firstValue : Sample)
    (second : Particle) (secondValue : Sample) (hneq : first ≠ second)
    (left right : (Particle → Sample) → ℝ)
    (hagrees : ∀ samples, samples first = firstValue →
      samples second = secondValue → left samples = right samples) :
    (∑ samples,
      (doublyForcedIndependentPopulation law first firstValue second secondValue).mass
          samples * left samples) =
      ∑ samples,
        (doublyForcedIndependentPopulation law first firstValue second secondValue).mass
          samples * right samples := by
  apply Finset.sum_congr rfl
  intro samples _
  by_cases hfirst : samples first = firstValue
  · by_cases hsecond : samples second = secondValue
    · rw [hagrees samples hfirst hsecond]
    · rw [doublyForcedIndependentPopulation_incompatible_zero
        law first firstValue second secondValue hneq samples (Or.inr hsecond)]
      simp
  · rw [doublyForcedIndependentPopulation_incompatible_zero
      law first firstValue second secondValue hneq samples (Or.inl hfirst)]
    simp

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

omit [Nonempty Particle] in
/-- Under a two-coordinate-forced product law, the expected score sum over
the remaining coordinates is exactly the sum of their original marginal
expectations. Keeping the exclusions explicit avoids premature cardinal
arithmetic and is the form consumed by the leave-one-out PG proof. -/
theorem doublyForcedIndependentPopulation_remainder_expectation
    (law : Particle → Distribution Sample)
    (first : Particle) (firstValue : Sample)
    (second : Particle) (secondValue : Sample)
    (score : Sample → ℝ) :
    (∑ samples,
        (doublyForcedIndependentPopulation law first firstValue second secondValue).mass
            samples *
          (∑ i : Particle,
            if i = first ∨ i = second then 0 else score (samples i))) =
      ∑ i : Particle, if i = first ∨ i = second then 0
        else ∑ x, (law i).mass x * score x := by
  classical
  calc
    (∑ samples,
        (doublyForcedIndependentPopulation law first firstValue second secondValue).mass
            samples *
          (∑ i : Particle,
            if i = first ∨ i = second then 0 else score (samples i))) =
        ∑ i : Particle, ∑ samples,
          (doublyForcedIndependentPopulation law first firstValue second secondValue).mass
              samples *
            (if i = first ∨ i = second then 0 else score (samples i)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ i : Particle, if i = first ∨ i = second then 0
          else ∑ x, (law i).mass x * score x := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i = first ∨ i = second
      · simp [hi]
      · simp only [hi, if_false]
        unfold doublyForcedIndependentPopulation
        rw [independentPopulation_coordinate_expectation]
        have hfirst : i ≠ first := fun h => hi (Or.inl h)
        have hsecond : i ≠ second := fun h => hi (Or.inr h)
        simp [hfirst, hsecond]

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

/-- With `extra + 1` total particles, excluding two distinct coordinates
leaves exactly `extra - 1` copies of a constant. -/
theorem sum_excluding_pair_constant (extra : ℕ) (hextra : 0 < extra)
    (first second : Fin (extra + 1)) (hneq : first ≠ second) (value : ℝ) :
    (∑ i : Fin (extra + 1),
      if i = first ∨ i = second then 0 else value) =
      (extra - 1 : ℕ) * value := by
  calc
    (∑ i : Fin (extra + 1),
        if i = first ∨ i = second then 0 else value) =
      ∑ i : Fin (extra + 1), (
        value - (if i = first then value else 0) -
          (if i = second then value else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hfirst : i = first
      · simp [hfirst, hneq]
      · by_cases hsecond : i = second <;> simp [hfirst, hsecond, Ne.symm hneq]
    _ = (extra + 1 : ℕ) * value - value - value := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp
    _ = (extra - 1 : ℕ) * value := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hextra))]
      push_cast
      ring

/-- Split a finite sum into two distinct named coordinates and the remaining
coordinates. -/
theorem sum_eq_pair_add_remainder {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℝ) (first second : α) (hneq : first ≠ second) :
    (∑ i, score i) = score first + score second +
      ∑ i, if i = first ∨ i = second then 0 else score i := by
  calc
    (∑ i, score i) = ∑ i,
        ((if i = first then score first else 0) +
          (if i = second then score second else 0) +
          (if i = first ∨ i = second then 0 else score i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hfirst : i = first
      · subst i
        simp [hneq]
      · by_cases hsecond : i = second
        · subst i
          simp [hfirst]
        · simp [hfirst, hsecond]
    _ = score first + score second +
        ∑ i, if i = first ∨ i = second then 0 else score i := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp

/-- Common-law specialization of the two-coordinate remainder identity for
`extra + 1` particles. -/
theorem doublyForcedIndependentPopulation_remainder_expectation_fin
    (law : Distribution Sample) (extra : ℕ) (hextra : 0 < extra)
    (first second : Fin (extra + 1)) (hneq : first ≠ second)
    (firstValue secondValue : Sample) (score : Sample → ℝ) :
    (∑ samples,
        (doublyForcedIndependentPopulation
          (fun _ : Fin (extra + 1) => law)
          first firstValue second secondValue).mass samples *
          (∑ i : Fin (extra + 1),
            if i = first ∨ i = second then 0 else score (samples i))) =
      (extra - 1 : ℕ) * (∑ x, law.mass x * score x) := by
  rw [doublyForcedIndependentPopulation_remainder_expectation]
  simpa using sum_excluding_pair_constant extra hextra first second hneq
    (∑ x, law.mass x * score x)

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

omit [Nonempty Particle] in
/-- Every ordinary child of a forced resample--propagate stage has exactly the
same joint `(updated label, state)` marginal: first draw its parent from the
normalized weights, then propagate from that parent's state. This is the
coordinate-level precursor of the joint-population disintegration used by the
recursive PG induction. -/
theorem forcedResamplePropagate_label_coordinate_expectation
    {Label : Type*} (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label)
    (retained nextRetained : Particle) (nextState : Sample)
    (i : Particle) (hi : i ≠ nextRetained)
    (observable : Label → Sample → ℝ) :
    (∑ ancestors,
      (forcedIndependentPopulation (fun _ : Particle => weights)
        nextRetained retained).mass ancestors *
        ∑ next,
          (forcedIndependentPopulation
            (fun j => rowDistribution transition (particles (ancestors j)))
            nextRetained nextState).mass next *
            observable (extend (labels (ancestors i)) (next i)) (next i)) =
      ∑ parent, weights.mass parent *
        ∑ y, transition.prob (particles parent) y *
          observable (extend (labels parent) y) y := by
  let childScore : Particle → ℝ := fun parent =>
    ∑ y, transition.prob (particles parent) y *
      observable (extend (labels parent) y) y
  have hinner (ancestors : Particle → Particle) :
      (∑ next,
        (forcedIndependentPopulation
          (fun j => rowDistribution transition (particles (ancestors j)))
          nextRetained nextState).mass next *
          observable (extend (labels (ancestors i)) (next i)) (next i)) =
        childScore (ancestors i) := by
    rw [forcedIndependentPopulation_coordinate_expectation
      (fun j => rowDistribution transition (particles (ancestors j)))
      nextRetained nextState
      (fun y => observable (extend (labels (ancestors i)) y) y) i]
    simp only [hi, if_false]
    rfl
  simp_rw [hinner]
  rw [forcedIndependentPopulation_coordinate_expectation]
  simp [hi, childScore]

/-- Joint law of one ordinary labeled child after resampling and propagation. -/
def resamplePropagateLabelDistribution {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label) :
    Distribution (Label × Sample) :=
  Distribution.bind weights fun parent =>
    Distribution.map (rowDistribution transition (particles parent)) fun y =>
      (extend (labels parent) y, y)

/-- Joint labeled population for one forced resample--propagate stage. The
retained child is fixed; every ordinary child independently samples a parent
and propagated state. -/
def forcedResamplePropagateLabelPopulation {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label)
    (retained nextRetained : Particle) (nextState : Sample) :
    Distribution (Particle → (Label × Sample)) :=
  Distribution.bind
    (forcedIndependentPopulation (fun _ : Particle => weights)
      nextRetained retained) fun ancestors =>
    independentPopulation fun i =>
      if i = nextRetained then
        pointDistribution (extend (labels retained) nextState, nextState)
      else
        Distribution.map
          (rowDistribution transition (particles (ancestors i))) fun y =>
            (extend (labels (ancestors i)) y, y)

/-- The same forced labeled stage represented in the original two-step form:
draw ancestors, draw propagated states, then pair each state with its updated
label. -/
def forcedResamplePropagateLabelPopulationViaStates {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label)
    (retained nextRetained : Particle) (nextState : Sample) :
    Distribution (Particle → (Label × Sample)) :=
  Distribution.bind
    (forcedIndependentPopulation (fun _ : Particle => weights)
      nextRetained retained) fun ancestors =>
    Distribution.map
      (forcedIndependentPopulation
        (fun i => rowDistribution transition (particles (ancestors i)))
        nextRetained nextState) fun next i =>
          (extend (labels (ancestors i)) (next i), next i)

omit [Nonempty Particle] in
/-- The two-step ancestor/state representation and the packaged joint-child
population have exactly the same law. -/
theorem forcedResamplePropagateLabelPopulationViaStates_eq
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label)
    (retained nextRetained : Particle) (nextState : Sample) :
    forcedResamplePropagateLabelPopulationViaStates extend weights transition
        particles labels retained nextRetained nextState =
      forcedResamplePropagateLabelPopulation extend weights transition
        particles labels retained nextRetained nextState := by
  apply Distribution.ext
  funext children
  unfold forcedResamplePropagateLabelPopulationViaStates
  unfold forcedResamplePropagateLabelPopulation
  simp only [Distribution.bind_mass]
  apply Finset.sum_congr rfl
  intro ancestors _
  by_cases hancestor : ancestors nextRetained = retained
  · congr 1
    unfold forcedIndependentPopulation
    let stateLaw : Particle → Distribution Sample := fun i =>
      if i = nextRetained then pointDistribution nextState
      else rowDistribution transition (particles (ancestors i))
    let transform : Particle → Sample → (Label × Sample) := fun i y =>
      (extend (labels (ancestors i)) y, y)
    change (Distribution.map (independentPopulation stateLaw)
      (fun next i => transform i (next i))).mass children = _
    rw [map_independentPopulation_coordinatewise stateLaw transform]
    unfold independentPopulation
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i = nextRetained
    · subst i
      simp only [stateLaw, transform, if_true, hancestor]
      rw [map_pointDistribution]
    · simp [hi, stateLaw, transform]
  · rw [forcedIndependentPopulation_incompatible_zero
      (fun _ : Particle => weights) nextRetained retained ancestors hancestor]
    simp

omit [Nonempty Particle] in
/-- Expectation bridge from the nested ancestor/state sums used by the SMC
suffix recursion to the packaged joint-child population. -/
theorem forcedResamplePropagateLabelPopulation_expectation
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label)
    (retained nextRetained : Particle) (nextState : Sample)
    (observable : (Particle → (Label × Sample)) → ℝ) :
    (∑ ancestors,
      (forcedIndependentPopulation (fun _ : Particle => weights)
        nextRetained retained).mass ancestors *
        ∑ next,
          (forcedIndependentPopulation
            (fun i => rowDistribution transition (particles (ancestors i)))
            nextRetained nextState).mass next *
            observable (fun i =>
              (extend (labels (ancestors i)) (next i), next i))) =
      ∑ children,
        (forcedResamplePropagateLabelPopulation extend weights transition particles labels
          retained nextRetained nextState).mass children * observable children := by
  rw [← forcedResamplePropagateLabelPopulationViaStates_eq]
  unfold forcedResamplePropagateLabelPopulationViaStates
  rw [Distribution.bind_expectation]
  apply Finset.sum_congr rfl
  intro ancestors _
  rw [Distribution.map_expectation]

omit [Nonempty Particle] in
/-- The forced joint labeled population is exactly an independent population
with one forced coordinate and a common ordinary-child law. -/
theorem forcedResamplePropagateLabelPopulation_eq_forcedIndependent
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label)
    (retained nextRetained : Particle) (nextState : Sample) :
    forcedResamplePropagateLabelPopulation extend weights transition particles labels
        retained nextRetained nextState =
      forcedIndependentPopulation
        (fun _ : Particle =>
          resamplePropagateLabelDistribution extend weights transition particles labels)
        nextRetained (extend (labels retained) nextState, nextState) := by
  unfold forcedResamplePropagateLabelPopulation
  let parentLaw : Particle → Distribution Particle := fun i =>
    if i = nextRetained then pointDistribution retained else weights
  let childLaw : Particle → Particle → Distribution (Label × Sample) :=
    fun i parent =>
      if i = nextRetained then
        pointDistribution (extend (labels retained) nextState, nextState)
      else Distribution.map
        (rowDistribution transition (particles parent)) fun y =>
          (extend (labels parent) y, y)
  change Distribution.bind (independentPopulation parentLaw) (fun ancestors =>
      independentPopulation (fun i => childLaw i (ancestors i))) = _
  rw [independentPopulation_bind_eq_independentPopulation_bind]
  unfold forcedIndependentPopulation
  apply Distribution.ext
  funext children
  unfold independentPopulation
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i = nextRetained
  · subst i
    simp [parentLaw, childLaw, pointDistribution]
  · change (Distribution.bind (parentLaw i) (childLaw i)).mass (children i) = _
    simp only [parentLaw, childLaw, hi, if_false]
    rfl

omit [DecidableEq Particle] [Nonempty Particle] in
/-- Expectations under the joint ordinary-child law are the familiar
resample-then-propagate double sum. -/
theorem resamplePropagateLabelDistribution_expectation {Label : Type*}
    [Fintype Label] [DecidableEq Label]
    (extend : Label → Sample → Label)
    (weights : Distribution Particle) (transition : MarkovKernel Sample)
    (particles : Particle → Sample) (labels : Particle → Label)
    (observable : Label → Sample → ℝ) :
    (∑ child,
      (resamplePropagateLabelDistribution extend weights transition particles labels).mass
          child * observable child.1 child.2) =
      ∑ parent, weights.mass parent *
        ∑ y, transition.prob (particles parent) y *
          observable (extend (labels parent) y) y := by
  unfold resamplePropagateLabelDistribution
  rw [Distribution.bind_expectation]
  apply Finset.sum_congr rfl
  intro parent _
  rw [Distribution.map_expectation]
  rfl

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

omit [DecidableEq Sample] [DecidableEq Particle] [Nonempty Particle] in
/-- An oscillation certificate bounds every point value by `bound` times the
mean under any probability law. This replaces a supremum in the finite
leave-one-out argument and remains valid for an arbitrary retained state. -/
theorem PotentialOscillationBound.le_bound_mul_expectation
    (potential : Sample → ℝ) (bound : ℝ)
    (certificate : PotentialOscillationBound potential bound)
    (law : Distribution Sample) (x : Sample) :
    potential x ≤ bound * ∑ y, law.mass y * potential y := by
  calc
    potential x = ∑ y, law.mass y * potential x := by
      rw [← Finset.sum_mul, law.sum_mass, one_mul]
    _ ≤ ∑ y, law.mass y * (bound * potential y) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (certificate.le_mul x y) (law.nonneg y)
    _ = bound * ∑ y, law.mass y * potential y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

omit [DecidableEq Sample] [DecidableEq Particle] [Nonempty Particle] in
/-- Leave-one-out reciprocal bound with two distinguished potential terms.
One term is the selected ordinary particle and the other is the retained
particle. If the remaining denominator has mean `others * μ(G)`, oscillation
bounds each distinguished term by `B * μ(G)`, producing the characteristic
`others + 2B` denominator. -/
theorem leaveOneOut_reciprocal_lower_bound
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (bound : ℝ) (certificate : PotentialOscillationBound potential bound)
    (samplingLaw : Distribution Sample) (selected retained : Sample)
    (remainderLaw : Distribution Ω) (remainder : Ω → ℝ)
    (others : ℕ) (hremainder : ∀ ω, 0 ≤ remainder ω)
    (hremainderMean :
      (∑ ω, remainderLaw.mass ω * remainder ω) =
        (others : ℝ) * ∑ x, samplingLaw.mass x * potential x) :
    1 / (((others : ℝ) + 2 * bound) *
        (∑ x, samplingLaw.mass x * potential x)) ≤
      ∑ ω, remainderLaw.mass ω *
        (1 / (potential selected + potential retained + remainder ω)) := by
  let meanPotential := ∑ x, samplingLaw.mass x * potential x
  let denominator := fun ω =>
    potential selected + potential retained + remainder ω
  have hdenominator : ∀ ω, 0 < denominator ω := by
    intro ω
    dsimp only [denominator]
    exact add_pos_of_pos_of_nonneg
      (add_pos (hpotential selected) (hpotential retained)) (hremainder ω)
  have hmeanEq :
      (∑ ω, remainderLaw.mass ω * denominator ω) =
        potential selected + potential retained + (others : ℝ) * meanPotential := by
    dsimp only [denominator]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [remainderLaw.sum_mass, one_mul, one_mul, hremainderMean]
  have hmean : 0 < ∑ ω, remainderLaw.mass ω * denominator ω := by
    rw [hmeanEq]
    exact add_pos_of_pos_of_nonneg
      (add_pos (hpotential selected) (hpotential retained))
      (mul_nonneg (Nat.cast_nonneg others) (Finset.sum_nonneg fun x _ =>
        mul_nonneg (samplingLaw.nonneg x) (hpotential x).le))
  have hselected : potential selected ≤ bound * meanPotential :=
    certificate.le_bound_mul_expectation potential bound samplingLaw selected
  have hretained : potential retained ≤ bound * meanPotential :=
    certificate.le_bound_mul_expectation potential bound samplingLaw retained
  have hmeanPotential : 0 ≤ meanPotential := by
    dsimp only [meanPotential]
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (samplingLaw.nonneg x) (hpotential x).le
  have hmeanUpper :
      (∑ ω, remainderLaw.mass ω * denominator ω) ≤
        ((others : ℝ) + 2 * bound) * meanPotential := by
    rw [hmeanEq]
    nlinarith
  exact one_div_upper_le_expectation_one_div remainderLaw denominator
    (((others : ℝ) + 2 * bound) * meanPotential)
    hdenominator hmean hmeanUpper

/-- Concrete two-coordinate forced-cloud instance of the leave-one-out
reciprocal estimate. For `extra + 1` total particles, the remainder contains
`extra - 1` independent draws. -/
theorem doublyForced_reciprocal_totalPotential_lower_bound
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (bound : ℝ) (certificate : PotentialOscillationBound potential bound)
    (law : Distribution Sample) (extra : ℕ) (hextra : 0 < extra)
    (retained selected : Fin (extra + 1)) (hneq : retained ≠ selected)
    (retainedValue selectedValue : Sample) :
    1 / (((extra - 1 : ℕ) : ℝ) + 2 * bound) /
        (∑ x, law.mass x * potential x) ≤
      ∑ particles,
        (doublyForcedIndependentPopulation
          (fun _ : Fin (extra + 1) => law)
          retained retainedValue selected selectedValue).mass particles *
          (1 / (potential selectedValue + potential retainedValue +
            ∑ i : Fin (extra + 1),
              if i = retained ∨ i = selected then 0
              else potential (particles i))) := by
  have h := leaveOneOut_reciprocal_lower_bound
    potential hpotential bound certificate law selectedValue retainedValue
    (doublyForcedIndependentPopulation
      (fun _ : Fin (extra + 1) => law)
      retained retainedValue selected selectedValue)
    (fun particles => ∑ i : Fin (extra + 1),
      if i = retained ∨ i = selected then 0 else potential (particles i))
    (extra - 1)
    (fun particles => Finset.sum_nonneg fun i _ => by
      by_cases hi : i = retained ∨ i = selected
      · simp [hi]
      · simpa [hi] using (hpotential (particles i)).le)
    (doublyForcedIndependentPopulation_remainder_expectation_fin
      law extra hextra retained selected hneq retainedValue selectedValue potential)
  simpa [div_eq_mul_inv, mul_assoc, mul_comm] using h

/-- One ordinary coordinate's contribution to a forced cloud dominates its
one-particle weighted expectation divided by the leave-one-out denominator. -/
theorem forcedIndependentPopulation_selectedNormalizedScore_lower_bound
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (bound : ℝ) (certificate : PotentialOscillationBound potential bound)
    (law : Distribution Sample) (extra : ℕ) (hextra : 0 < extra)
    (retained selected : Fin (extra + 1)) (hneq : retained ≠ selected)
    (retainedValue : Sample) (score : Sample → ℝ)
    (hscore : ∀ x, 0 ≤ score x) :
    (1 / ((((extra - 1 : ℕ) : ℝ) + 2 * bound) *
        (∑ x, law.mass x * potential x))) *
      (∑ x, law.mass x * (potential x * score x)) ≤
      ∑ particles,
        (forcedIndependentPopulation (fun _ : Fin (extra + 1) => law)
          retained retainedValue).mass particles *
          (potential (particles selected) * score (particles selected) /
            ∑ i, potential (particles i)) := by
  let upper := (((extra - 1 : ℕ) : ℝ) + 2 * bound) *
    (∑ x, law.mass x * potential x)
  have hdisintegrate := forcedIndependentPopulation_bind_doublyForced
    (fun _ : Fin (extra + 1) => law) retained selected hneq retainedValue
  rw [← hdisintegrate, Distribution.bind_expectation]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro selectedValue _
  calc
    1 / ((((extra - 1 : ℕ) : ℝ) + 2 * bound) *
          (∑ x, law.mass x * potential x)) *
        (law.mass selectedValue *
          (potential selectedValue * score selectedValue)) =
        law.mass selectedValue *
          (1 / ((((extra - 1 : ℕ) : ℝ) + 2 * bound) *
              (∑ x, law.mass x * potential x)) *
            (potential selectedValue * score selectedValue)) := by ring
    _ ≤ law.mass selectedValue *
        ∑ particles,
          (doublyForcedIndependentPopulation
            (fun _ : Fin (extra + 1) => law)
            retained retainedValue selected selectedValue).mass particles *
            (potential (particles selected) * score (particles selected) /
              ∑ i, potential (particles i)) := by
      apply mul_le_mul_of_nonneg_left
      · have hreciprocal := doublyForced_reciprocal_totalPotential_lower_bound
          potential hpotential bound certificate law extra hextra retained selected
          hneq retainedValue selectedValue
        have hscaled := mul_le_mul_of_nonneg_left hreciprocal
          (mul_nonneg (hpotential selectedValue).le (hscore selectedValue))
        have heq :
            (∑ particles,
              (doublyForcedIndependentPopulation
                (fun _ : Fin (extra + 1) => law)
                retained retainedValue selected selectedValue).mass particles *
                (potential (particles selected) * score (particles selected) /
                  ∑ i, potential (particles i))) =
              potential selectedValue * score selectedValue *
                ∑ particles,
                  (doublyForcedIndependentPopulation
                    (fun _ : Fin (extra + 1) => law)
                    retained retainedValue selected selectedValue).mass particles *
                    (1 / (potential selectedValue + potential retainedValue +
                      ∑ i : Fin (extra + 1),
                        if i = retained ∨ i = selected then 0
                        else potential (particles i))) := by
          calc
            (∑ particles,
                (doublyForcedIndependentPopulation
                  (fun _ : Fin (extra + 1) => law)
                  retained retainedValue selected selectedValue).mass particles *
                  (potential (particles selected) * score (particles selected) /
                    ∑ i, potential (particles i))) =
              ∑ particles,
                (doublyForcedIndependentPopulation
                  (fun _ : Fin (extra + 1) => law)
                  retained retainedValue selected selectedValue).mass particles *
                  (potential selectedValue * score selectedValue *
                    (1 / (potential selectedValue + potential retainedValue +
                      ∑ i : Fin (extra + 1),
                        if i = retained ∨ i = selected then 0
                        else potential (particles i)))) := by
              apply doublyForcedIndependentPopulation_expectation_congr
                (fun _ : Fin (extra + 1) => law)
                retained retainedValue selected selectedValue hneq
              intro particles hretained hselected
              rw [sum_eq_pair_add_remainder
                (fun i => potential (particles i)) selected retained (Ne.symm hneq)]
              rw [hselected, hretained]
              have hremainder :
                  (∑ i : Fin (extra + 1),
                    if i = selected ∨ i = retained then 0
                    else potential (particles i)) =
                  ∑ i : Fin (extra + 1),
                    if i = retained ∨ i = selected then 0
                    else potential (particles i) := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases hi : i = selected ∨ i = retained
                · have hi' : i = retained ∨ i = selected := hi.elim Or.inr Or.inl
                  simp [hi, hi']
                · have hi' : ¬(i = retained ∨ i = selected) := by
                    intro h
                    exact hi (h.elim Or.inr Or.inl)
                  simp [hi, hi']
              rw [hremainder]
              ring
            _ = potential selectedValue * score selectedValue *
                ∑ particles,
                  (doublyForcedIndependentPopulation
                    (fun _ : Fin (extra + 1) => law)
                    retained retainedValue selected selectedValue).mass particles *
                    (1 / (potential selectedValue + potential retainedValue +
                      ∑ i : Fin (extra + 1),
                        if i = retained ∨ i = selected then 0
                        else potential (particles i))) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro particles _
              ring
        rw [heq]
        simpa [upper, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hscaled
      · exact law.nonneg selectedValue

/-- Summing the selected-coordinate leave-one-out estimate over all ordinary
particles gives the sharp self-normalized forced-cloud comparison. -/
theorem forcedIndependentPopulation_unforcedNormalizedScore_lower_bound
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (bound : ℝ) (certificate : PotentialOscillationBound potential bound)
    (law : Distribution Sample) (extra : ℕ) (hextra : 0 < extra)
    (retained : Fin (extra + 1)) (retainedValue : Sample)
    (score : Sample → ℝ) (hscore : ∀ x, 0 ≤ score x) :
    (extra : ℝ) *
        (1 / (((((extra - 1 : ℕ) : ℝ) + 2 * bound) *
          (∑ x, law.mass x * potential x))) *
          (∑ x, law.mass x * (potential x * score x))) ≤
      ∑ particles,
        (forcedIndependentPopulation (fun _ : Fin (extra + 1) => law)
          retained retainedValue).mass particles *
          ((∑ i : Fin (extra + 1),
              if i = retained then 0
              else potential (particles i) * score (particles i)) /
            ∑ i, potential (particles i)) := by
  let contribution := fun selected : Fin (extra + 1) =>
    ∑ particles,
      (forcedIndependentPopulation (fun _ : Fin (extra + 1) => law)
        retained retainedValue).mass particles *
        (potential (particles selected) * score (particles selected) /
          ∑ i, potential (particles i))
  let lower := 1 / (((((extra - 1 : ℕ) : ℝ) + 2 * bound) *
    (∑ x, law.mass x * potential x))) *
    (∑ x, law.mass x * (potential x * score x))
  calc
    (extra : ℝ) * lower =
        ∑ selected : Fin (extra + 1),
          if selected = retained then 0 else lower := by
      rw [sum_unforced_constant]
      simp
    _ ≤ ∑ selected : Fin (extra + 1),
          if selected = retained then 0 else contribution selected := by
      apply Finset.sum_le_sum
      intro selected _
      by_cases hselected : selected = retained
      · simp [hselected]
      · simp only [hselected, if_false]
        exact forcedIndependentPopulation_selectedNormalizedScore_lower_bound
          potential hpotential bound certificate law extra hextra retained selected
          (Ne.symm hselected) retainedValue score hscore
    _ = ∑ particles,
        (forcedIndependentPopulation (fun _ : Fin (extra + 1) => law)
          retained retainedValue).mass particles *
          ((∑ i : Fin (extra + 1),
              if i = retained then 0
              else potential (particles i) * score (particles i)) /
            ∑ i, potential (particles i)) := by
      calc
        (∑ selected : Fin (extra + 1),
            if selected = retained then 0 else contribution selected) =
          ∑ selected : Fin (extra + 1), ∑ particles,
            (forcedIndependentPopulation (fun _ : Fin (extra + 1) => law)
              retained retainedValue).mass particles *
              (if selected = retained then 0 else
                potential (particles selected) * score (particles selected) /
                  ∑ i, potential (particles i)) := by
            apply Finset.sum_congr rfl
            intro selected _
            by_cases hselected : selected = retained <;>
              simp [hselected, contribution]
        _ = ∑ particles, ∑ selected : Fin (extra + 1),
            (forcedIndependentPopulation (fun _ : Fin (extra + 1) => law)
              retained retainedValue).mass particles *
              (if selected = retained then 0 else
                potential (particles selected) * score (particles selected) /
                  ∑ i, potential (particles i)) := by
            rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro particles _
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro selected _
          by_cases hselected : selected = retained <;> simp [hselected]

/-- Ratio form of the aggregate ordinary-cloud comparison. Its coefficient is
`extra / (extra - 1 + 2B)`, equivalently
`extra / (extra + (2B - 1))`, which is the candidate PG stage factor. -/
theorem forcedIndependentPopulation_normalizedTargetScore_lower_bound
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (bound : ℝ) (certificate : PotentialOscillationBound potential bound)
    (law : Distribution Sample) (extra : ℕ) (hextra : 0 < extra)
    (retained : Fin (extra + 1)) (retainedValue : Sample)
    (score : Sample → ℝ) (hscore : ∀ x, 0 ≤ score x) :
    (extra : ℝ) / (((extra - 1 : ℕ) : ℝ) + 2 * bound) *
        ((∑ x, law.mass x * (potential x * score x)) /
          ∑ x, law.mass x * potential x) ≤
      ∑ particles,
        (forcedIndependentPopulation (fun _ : Fin (extra + 1) => law)
          retained retainedValue).mass particles *
          ((∑ i : Fin (extra + 1),
              if i = retained then 0
              else potential (particles i) * score (particles i)) /
            ∑ i, potential (particles i)) := by
  have hbase := forcedIndependentPopulation_unforcedNormalizedScore_lower_bound
    potential hpotential bound certificate law extra hextra retained retainedValue
    score hscore
  have hfactor : 0 < (((extra - 1 : ℕ) : ℝ) + 2 * bound) := by
    have : 0 ≤ (((extra - 1 : ℕ) : ℝ)) := Nat.cast_nonneg _
    linarith [certificate.bound_pos]
  have hexpectation : 0 < ∑ x, law.mass x * potential x := by
    have hexists : ∃ x, 0 < law.mass x := by
      by_contra h
      push Not at h
      have hzero : ∀ x, law.mass x = 0 := fun x =>
        le_antisymm (h x) (law.nonneg x)
      have : ∑ x, law.mass x = 0 := by simp [hzero]
      linarith [law.sum_mass]
    obtain ⟨x, hx⟩ := hexists
    apply Finset.sum_pos'
    · intro y _
      exact mul_nonneg (law.nonneg y) (hpotential y).le
    · exact ⟨x, Finset.mem_univ x, mul_pos hx (hpotential x)⟩
  convert hbase using 1
  field_simp

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

/-- Normalize a strictly positive potential against an arbitrary finite
probability distribution. -/
noncomputable def positivePotentialReweight {α : Type*}
    [Fintype α] [DecidableEq α]
    (law : Distribution α) (potential : α → ℝ)
    (hpotential : ∀ x, 0 < potential x) : Distribution α where
  mass x := law.mass x * potential x / ∑ y, law.mass y * potential y
  nonneg x := div_nonneg (mul_nonneg (law.nonneg x) (hpotential x).le)
    (Finset.sum_nonneg fun y _ => mul_nonneg (law.nonneg y) (hpotential y).le)
  sum_mass := by
    rw [← Finset.sum_div]
    apply div_self
    intro hzero
    have hmassZero : ∀ x, law.mass x = 0 := by
      intro x
      by_contra hx
      have hxpos : 0 < law.mass x := lt_of_le_of_ne (law.nonneg x) (Ne.symm hx)
      have hsumPos : 0 < ∑ y, law.mass y * potential y := by
        apply Finset.sum_pos'
        · intro y _
          exact mul_nonneg (law.nonneg y) (hpotential y).le
        · exact ⟨x, Finset.mem_univ x, mul_pos hxpos (hpotential x)⟩
      exact (ne_of_gt hsumPos) hzero
    have : ∑ x, law.mass x = 0 := by simp [hmassZero]
    linarith [law.sum_mass]

/-- Expectation under a positive-potential reweighting is the corresponding
normalized weighted expectation. -/
theorem positivePotentialReweight_expectation {α : Type*}
    [Fintype α] [DecidableEq α]
    (law : Distribution α) (potential : α → ℝ)
    (hpotential : ∀ x, 0 < potential x) (score : α → ℝ) :
    (∑ x, (positivePotentialReweight law potential hpotential).mass x * score x) =
      (∑ x, law.mass x * (potential x * score x)) /
        ∑ x, law.mass x * potential x := by
  unfold positivePotentialReweight
  change (∑ x, (law.mass x * potential x /
      ∑ y, law.mass y * potential y) * score x) = _
  calc
    _ = ∑ x, (law.mass x * (potential x * score x)) /
        ∑ y, law.mass y * potential y := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [Finset.sum_div]

omit [Fintype Sample] [DecidableEq Sample] in
/-- A state-potential oscillation certificate lifts unchanged to joint
`(label,state)` values. -/
theorem PotentialOscillationBound.snd {Label : Type*}
    (potential : Sample → ℝ) (bound : ℝ)
    (certificate : PotentialOscillationBound potential bound) :
    PotentialOscillationBound (fun z : Label × Sample => potential z.2) bound := by
  exact ⟨certificate.bound_pos, fun x y => certificate.le_mul x.2 y.2⟩

/-- Joint-label form of the sharp forced-cloud comparison. -/
theorem forcedJointPopulation_normalizedTargetScore_lower_bound
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (potential : Sample → ℝ) (hpotential : ∀ x, 0 < potential x)
    (bound : ℝ) (certificate : PotentialOscillationBound potential bound)
    (law : Distribution (Label × Sample)) (extra : ℕ) (hextra : 0 < extra)
    (retained : Fin (extra + 1)) (retainedValue : Label × Sample)
    (score : Label × Sample → ℝ) (hscore : ∀ x, 0 ≤ score x) :
    (extra : ℝ) / (((extra - 1 : ℕ) : ℝ) + 2 * bound) *
        (∑ x,
          (positivePotentialReweight law (fun z => potential z.2)
            (fun z => hpotential z.2)).mass x * score x) ≤
      ∑ particles,
        (forcedIndependentPopulation
          (fun _ : Fin (extra + 1) => law) retained retainedValue).mass particles *
          ((∑ i : Fin (extra + 1),
              if i = retained then 0
              else potential (particles i).2 * score (particles i)) /
            ∑ i, potential (particles i).2) := by
  rw [positivePotentialReweight_expectation]
  exact forcedIndependentPopulation_normalizedTargetScore_lower_bound
    (fun z : Label × Sample => potential z.2) (fun z => hpotential z.2)
    bound certificate.snd law extra hextra retained retainedValue score hscore

/-- Exact normalized Feynman--Kac update of a joint `(label,state)` law. -/
noncomputable def labeledFeynmanKacStepDistribution {Label : Type*}
    [Fintype Label] [DecidableEq Label] [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) (step : FeynmanKacStep Sample)
    (law : Distribution (Label × Sample)) : Distribution (Label × Sample) :=
  resamplePropagateLabelDistribution extend
    (positivePotentialReweight law (fun z : Label × Sample => step.potential z.2)
      (fun z => step.potential_pos z.2))
    step.transition (fun z => z.2) (fun z => z.1)

omit [Nonempty Particle] in
/-- Expectation under the exact labeled Feynman--Kac update is the normalized
potential-weighted transition expectation. -/
theorem labeledFeynmanKacStepDistribution_expectation {Label : Type*}
    [Fintype Label] [DecidableEq Label] [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) (step : FeynmanKacStep Sample)
    (law : Distribution (Label × Sample)) (observable : Label → Sample → ℝ) :
    (∑ child,
      (labeledFeynmanKacStepDistribution extend step law).mass child *
        observable child.1 child.2) =
      (∑ parent, law.mass parent *
        (step.potential parent.2 *
          ∑ y, step.transition.prob parent.2 y *
            observable (extend parent.1 y) y)) /
        ∑ parent, law.mass parent * step.potential parent.2 := by
  unfold labeledFeynmanKacStepDistribution
  rw [resamplePropagateLabelDistribution_expectation]
  unfold positivePotentialReweight
  change (∑ parent,
      (law.mass parent * step.potential parent.2 /
        ∑ z, law.mass z * step.potential z.2) *
        ∑ y, step.transition.prob parent.2 y *
          observable (extend parent.1 y) y) = _
  calc
    _ = ∑ parent,
        (law.mass parent *
          (step.potential parent.2 *
            ∑ y, step.transition.prob parent.2 y *
              observable (extend parent.1 y) y)) /
          ∑ z, law.mass z * step.potential z.2 := by
      apply Finset.sum_congr rfl
      intro parent _
      ring
    _ = _ := by rw [Finset.sum_div]

/-- Iterated exact normalized labeled Feynman--Kac law. -/
noncomputable def labeledFeynmanKacLawFrom {Label : Type*}
    [Fintype Label] [DecidableEq Label] [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) :
    Distribution (Label × Sample) → List (FeynmanKacStep Sample) →
      Distribution (Label × Sample)
  | law, [] => law
  | law, step :: steps =>
      labeledFeynmanKacLawFrom extend
        (labeledFeynmanKacStepDistribution extend step law) steps

@[simp] theorem labeledFeynmanKacLawFrom_nil {Label : Type*}
    [Fintype Label] [DecidableEq Label] [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample)) :
    labeledFeynmanKacLawFrom extend law [] = law := rfl

@[simp] theorem labeledFeynmanKacLawFrom_cons {Label : Type*}
    [Fintype Label] [DecidableEq Label] [Nonempty Label] [Nonempty Sample]
    (extend : Label → Sample → Label) (law : Distribution (Label × Sample))
    (step : FeynmanKacStep Sample) (steps : List (FeynmanKacStep Sample)) :
    labeledFeynmanKacLawFrom extend law (step :: steps) =
      labeledFeynmanKacLawFrom extend
        (labeledFeynmanKacStepDistribution extend step law) steps := rfl


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
