import McmcLean.Hamiltonian.QuadraticGaussian
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Regularized logistic-regression potentials

This module begins a validated applied target for the Xu et al. coupling
theory.  It first establishes the scalar calculus and global Lipschitz facts
for softplus and the logistic sigmoid.  The finite-data potential and its
Hamiltonian assumptions are built on these lemmas below.
-/

namespace McmcLean.Hamiltonian

open MeasureTheory

/-- Numerically conventional softplus, used as the negative log likelihood
of one logistic observation after composing with its signed linear score. -/
noncomputable def softplus (z : ℝ) : ℝ := Real.log (1 + Real.exp z)

/-- Logistic sigmoid in the form which is the derivative of `softplus`. -/
noncomputable def logisticSigmoid (z : ℝ) : ℝ :=
  Real.exp z / (1 + Real.exp z)

theorem hasDerivAt_softplus (z : ℝ) :
    HasDerivAt softplus (logisticSigmoid z) z := by
  change HasDerivAt (fun z : ℝ => Real.log (1 + Real.exp z))
    (Real.exp z / (1 + Real.exp z)) z
  have hinner : HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp z) z := by
    simpa only [add_zero] using (Real.hasDerivAt_exp z).const_add 1
  exact hinner.log (ne_of_gt (show 0 < 1 + Real.exp z by positivity))

theorem contDiff_softplus : ContDiff ℝ 2 softplus := by
  unfold softplus
  exact (contDiff_const.add Real.contDiff_exp).log (fun z => by positivity)

theorem softplus_nonneg (z : ℝ) : 0 ≤ softplus z := by
  unfold softplus
  exact Real.log_nonneg (by linarith [Real.exp_pos z])

theorem softplus_deriv (z : ℝ) : deriv softplus z = logisticSigmoid z :=
  (hasDerivAt_softplus z).deriv

theorem differentiable_softplus : Differentiable ℝ softplus :=
  fun z => (hasDerivAt_softplus z).differentiableAt

theorem hasDerivAt_logisticSigmoid (z : ℝ) :
    HasDerivAt logisticSigmoid
      (Real.exp z / (1 + Real.exp z) ^ 2) z := by
  change HasDerivAt (Real.exp / fun z : ℝ => 1 + Real.exp z)
    (Real.exp z / (1 + Real.exp z) ^ 2) z
  have hdenom : 1 + Real.exp z ≠ 0 := ne_of_gt (by positivity)
  have hinner : HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp z) z := by
    simpa only [add_zero] using (Real.hasDerivAt_exp z).const_add 1
  have h := (Real.hasDerivAt_exp z).div
    hinner hdenom
  apply h.congr_deriv
  field_simp
  ring

theorem logisticSigmoid_deriv (z : ℝ) :
    deriv logisticSigmoid z = Real.exp z / (1 + Real.exp z) ^ 2 :=
  (hasDerivAt_logisticSigmoid z).deriv

theorem logisticSigmoid_nonneg (z : ℝ) : 0 ≤ logisticSigmoid z := by
  unfold logisticSigmoid
  positivity

theorem logisticSigmoid_le_one (z : ℝ) : logisticSigmoid z ≤ 1 := by
  unfold logisticSigmoid
  apply (div_le_one (by positivity)).2
  linarith [Real.exp_pos z]

theorem lipschitzWith_softplus : LipschitzWith 1 softplus := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_softplus
  intro z
  rw [← NNReal.coe_le_coe]
  change ‖deriv softplus z‖ ≤ (1 : ℝ)
  rw [softplus_deriv, Real.norm_eq_abs,
    abs_of_nonneg (logisticSigmoid_nonneg z)]
  exact logisticSigmoid_le_one z

theorem abs_softplus_sub_le (x y : ℝ) :
    |softplus x - softplus y| ≤ |x - y| := by
  simpa only [Real.dist_eq, NNReal.smul_def, NNReal.coe_one, one_mul] using
    lipschitzWith_softplus.dist_le_mul x y

theorem logisticSigmoid_deriv_nonneg (z : ℝ) :
    0 ≤ deriv logisticSigmoid z := by
  rw [logisticSigmoid_deriv]
  positivity

theorem logisticSigmoid_deriv_le_one (z : ℝ) :
    deriv logisticSigmoid z ≤ 1 := by
  rw [logisticSigmoid_deriv]
  have he : 0 < Real.exp z := Real.exp_pos z
  apply (div_le_one (sq_pos_of_pos (by positivity))).2
  nlinarith [sq_nonneg (Real.exp z)]

theorem differentiable_logisticSigmoid : Differentiable ℝ logisticSigmoid :=
  fun z => (hasDerivAt_logisticSigmoid z).differentiableAt

theorem monotone_logisticSigmoid : Monotone logisticSigmoid :=
  monotone_of_deriv_nonneg differentiable_logisticSigmoid
    logisticSigmoid_deriv_nonneg

theorem lipschitzWith_logisticSigmoid :
    LipschitzWith 1 logisticSigmoid := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_logisticSigmoid
  intro z
  rw [← NNReal.coe_le_coe]
  change ‖deriv logisticSigmoid z‖ ≤ (1 : ℝ)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (logisticSigmoid_deriv_nonneg z)]
  exact logisticSigmoid_deriv_le_one z

theorem abs_logisticSigmoid_sub_le (x y : ℝ) :
    |logisticSigmoid x - logisticSigmoid y| ≤ |x - y| := by
  simpa only [Real.dist_eq, NNReal.smul_def, NNReal.coe_one, one_mul] using
    lipschitzWith_logisticSigmoid.dist_le_mul x y

/-- A generic capped exponential with a strictly negative quadratic tail is
uniformly controlled by the square root of its nonnegative offset.  This
rescales the scalar standard-quadratic estimate already used for Gaussian
HMC drift. -/
theorem min_one_exp_sub_quadratic_mul_one_add_le
    {offset coefficient radius : ℝ}
    (hoffset : 0 ≤ offset) (hcoefficient : 0 < coefficient)
    (hradius : 0 ≤ radius) :
    min 1 (Real.exp (offset - coefficient * radius ^ 2)) * (1 + radius) ≤
      (1 + 1 / (2 * Real.sqrt coefficient)) *
        (16 + 2 * Real.sqrt (2 * offset)) := by
  let d := 2 * Real.sqrt coefficient
  have hsqrtPos : 0 < Real.sqrt coefficient := Real.sqrt_pos.2 hcoefficient
  have hdPos : 0 < d := by dsimp only [d]; positivity
  have hdSq : d ^ 2 = 4 * coefficient := by
    dsimp only [d]
    rw [mul_pow, Real.sq_sqrt hcoefficient.le]
    ring
  have hsqrtSq : (Real.sqrt (2 * offset)) ^ 2 = 2 * offset :=
    Real.sq_sqrt (mul_nonneg (by norm_num) hoffset)
  have hbase := min_one_exp_standardQuadratic_defect_mul_one_add_abs_le
    (d * radius) (Real.sqrt (2 * offset))
  rw [abs_of_nonneg (mul_nonneg hdPos.le hradius),
    abs_of_nonneg (Real.sqrt_nonneg _)] at hbase
  have hexponent :
      (Real.sqrt (2 * offset)) ^ 2 / 2 - (d * radius) ^ 2 / 4 =
        offset - coefficient * radius ^ 2 := by
    rw [hsqrtSq, mul_pow, hdSq]
    ring
  rw [hexponent] at hbase
  have hfactor :
      1 + radius ≤ (1 + 1 / d) * (1 + d * radius) := by
    have hinv : 0 ≤ 1 / d := by positivity
    have hdr : 0 ≤ d * radius := mul_nonneg hdPos.le hradius
    field_simp
    nlinarith
  have hretention :
      0 ≤ min 1 (Real.exp (offset - coefficient * radius ^ 2)) := by
    positivity
  calc
    min 1 (Real.exp (offset - coefficient * radius ^ 2)) * (1 + radius) ≤
        min 1 (Real.exp (offset - coefficient * radius ^ 2)) *
          ((1 + 1 / d) * (1 + d * radius)) :=
      mul_le_mul_of_nonneg_left hfactor hretention
    _ = (1 + 1 / d) *
        (min 1 (Real.exp (offset - coefficient * radius ^ 2)) *
          (1 + d * radius)) := by ring
    _ ≤ (1 + 1 / d) * (16 + 2 * Real.sqrt (2 * offset)) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by rfl

/-- Square root of a quadratic-plus-linear momentum envelope grows at most
linearly in the momentum radius. -/
theorem sqrt_two_mul_add_mul_add_sq_le
    {constant linear radius : ℝ}
    (hconstant : 0 ≤ constant) (hlinear : 0 ≤ linear)
    (hradius : 0 ≤ radius) :
    Real.sqrt (2 * (constant + linear * radius + radius ^ 2)) ≤
      Real.sqrt (2 * constant) + linear + 3 * radius := by
  have hsum : 0 ≤ constant + linear * radius + radius ^ 2 := by positivity
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hsqrtSq : (Real.sqrt (2 * constant)) ^ 2 = 2 * constant :=
      Real.sq_sqrt (mul_nonneg (by norm_num) hconstant)
    have hsqrt0 : 0 ≤ Real.sqrt (2 * constant) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (linear - radius),
      mul_nonneg hsqrt0 hlinear, mul_nonneg hsqrt0 hradius]

section FiniteData

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Signed linear predictor used by one binary logistic observation. Labels
are allowed to be arbitrary reals; the conventional case is `label = ±1`. -/
noncomputable def logisticScore
    (feature : κ → Position ι) (label : κ → ℝ)
    (q : Position ι) (k : κ) : ℝ :=
  -label k * euclideanInner (feature k) q

/-- Finite negative log likelihood for binary logistic regression. -/
noncomputable def logisticNegativeLogLikelihood
    (feature : κ → Position ι) (label : κ → ℝ)
    (q : Position ι) : ℝ :=
  ∑ k, softplus (logisticScore feature label q k)

/-- `L²`-regularized logistic negative log posterior, up to an additive
normalizing constant. -/
noncomputable def regularizedLogisticPotential
    (feature : κ → Position ι) (label : κ → ℝ) (regularization : ℝ)
    (q : Position ι) : ℝ :=
  logisticNegativeLogLikelihood feature label q +
    regularization * kineticEnergy q

/-- Gradient contribution of one logistic observation. -/
noncomputable def logisticGradientContribution
    (feature : Position ι) (label : ℝ) (q : Position ι) : Position ι :=
  (-label * logisticSigmoid (-label * euclideanInner feature q)) • feature

/-- Exact gradient used by leapfrog for the regularized logistic target. -/
noncomputable def regularizedLogisticGradient
    (feature : κ → Position ι) (label : κ → ℝ) (regularization : ℝ)
    (q : Position ι) : Position ι :=
  regularization • q + ∑ k,
    logisticGradientContribution (feature k) (label k) q

omit [Fintype κ] in
theorem contDiff_logisticScore
    (feature : κ → Position ι) (label : κ → ℝ) (k : κ) :
    ContDiff ℝ 2 (fun q => logisticScore feature label q k) := by
  unfold logisticScore euclideanInner
  exact contDiff_const.mul
    (ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i))

theorem contDiff_logisticNegativeLogLikelihood
    (feature : κ → Position ι) (label : κ → ℝ) :
    ContDiff ℝ 2 (logisticNegativeLogLikelihood feature label) := by
  unfold logisticNegativeLogLikelihood
  exact ContDiff.sum fun k _ =>
    contDiff_softplus.comp (contDiff_logisticScore feature label k)

theorem contDiff_regularizedLogisticPotential
    (feature : κ → Position ι) (label : κ → ℝ) (regularization : ℝ) :
    ContDiff ℝ 2
      (regularizedLogisticPotential feature label regularization) := by
  unfold regularizedLogisticPotential
  exact (contDiff_logisticNegativeLogLikelihood feature label).add
    (contDiff_const.mul contDiff_standardQuadraticPotential)

omit [Fintype κ] in
/-- Directional derivative of one signed linear score. -/
theorem hasDerivAt_logisticScore_line
    (feature : κ → Position ι) (label : κ → ℝ)
    (q h : Position ι) (k : κ) :
    HasDerivAt
      (fun t : ℝ => logisticScore feature label (q + t • h) k)
      (-label k * euclideanInner (feature k) h) 0 := by
  unfold logisticScore euclideanInner
  have hsum : HasDerivAt
      (fun t : ℝ => ∑ i, feature k i * (q i + t * h i))
      (∑ i, feature k i * h i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id 0).mul_const (h i)).const_add (q i)).const_mul
        (feature k i)
  exact hsum.const_mul (-label k)

/-- The supplied finite-data gradient is exactly the Fréchet derivative of
the regularized logistic potential. -/
theorem fderiv_regularizedLogisticPotential_apply
    (feature : κ → Position ι) (label : κ → ℝ) (regularization : ℝ)
    (q h : Position ι) :
    fderiv ℝ (regularizedLogisticPotential feature label regularization) q h =
      euclideanInner
        (regularizedLogisticGradient feature label regularization q) h := by
  let line : ℝ → Position ι := fun t => q + t • h
  have hline : HasDerivAt line h 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    change HasDerivAt (fun t : ℝ => q i + t * h i) (h i) 0
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id 0).mul_const (h i)).const_add (q i)
  have hfromFDeriv : HasDerivAt
      (fun t => regularizedLogisticPotential feature label regularization (line t))
      (fderiv ℝ (regularizedLogisticPotential feature label regularization) q h) 0 := by
    have hdifferentiable :=
      (contDiff_regularizedLogisticPotential feature label regularization).differentiable
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hlinezero : line 0 = q := by simp [line]
    have houter := (hdifferentiable q).hasFDerivAt
    rw [← hlinezero] at houter
    have hcomp := houter.comp_hasDerivAt 0 hline
    rw [hlinezero] at hcomp
    change HasDerivAt
      ((regularizedLogisticPotential feature label regularization) ∘ line)
      (fderiv ℝ (regularizedLogisticPotential feature label regularization) q h) 0
    exact hcomp
  have hlikelihood : HasDerivAt
      (fun t => logisticNegativeLogLikelihood feature label (line t))
      (∑ k, (-label k *
        logisticSigmoid (logisticScore feature label q k)) *
          euclideanInner (feature k) h) 0 := by
    unfold logisticNegativeLogLikelihood
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hasDerivAt_softplus
        (logisticScore feature label (q + (0 : ℝ) • h) k)).comp 0
        (hasDerivAt_logisticScore_line feature label q h k)
    apply hsum.congr_deriv
    apply Finset.sum_congr rfl
    intro k _
    simp only [zero_smul, add_zero]
    ring
  have hquadratic : HasDerivAt
      (fun t => regularization * kineticEnergy (line t))
      (regularization * euclideanInner q h) 0 := by
    have hbase : HasDerivAt
        (fun t => standardQuadraticPotential (line t))
        (euclideanInner q h) 0 := by
      have hdiff := contDiff_standardQuadraticPotential.differentiable
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0) q
      have hlinezero : line 0 = q := by simp [line]
      have hout := hdiff.hasFDerivAt
      rw [← hlinezero] at hout
      have hc := hout.comp_hasDerivAt 0 hline
      rw [hlinezero, fderiv_standardQuadraticPotential_apply] at hc
      exact hc
    exact hbase.const_mul regularization
  have hdirect := hlikelihood.add hquadratic
  apply hfromFDeriv.unique
  apply hdirect.congr_deriv
  unfold regularizedLogisticGradient logisticGradientContribution
    logisticScore euclideanInner
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  rw [add_comm]
  congr 1
  · simp only [mul_assoc]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- Euclidean triangle inequality for a finite sum. -/
theorem euclideanNorm_finset_sum_le
    {α : Type*} (s : Finset α) (f : α → Position ι) :
    euclideanNorm (∑ a ∈ s, f a) ≤ ∑ a ∈ s, euclideanNorm (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (euclideanNorm_add_le (f a) (∑ x ∈ s, f x)).trans
        (by gcongr)

/-- A finite constant controlling the full likelihood force. -/
noncomputable def logisticForceBound
    (feature : κ → Position ι) (label : κ → ℝ) : ℝ :=
  ∑ k, |label k| * euclideanNorm (feature k)

theorem logisticForceBound_nonneg
    (feature : κ → Position ι) (label : κ → ℝ) :
    0 ≤ logisticForceBound feature label := by
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg _) (euclideanNorm_nonneg _)

/-- The entire logistic likelihood force is uniformly bounded, independently
of position. This is the bounded perturbation of the quadratic force used by
the forthcoming HMC drift estimate. -/
theorem euclideanNorm_logisticLikelihoodGradient_le
    (feature : κ → Position ι) (label : κ → ℝ) (q : Position ι) :
    euclideanNorm
        (∑ k, logisticGradientContribution (feature k) (label k) q) ≤
      logisticForceBound feature label := by
  calc
    _ ≤ ∑ k, euclideanNorm
        (logisticGradientContribution (feature k) (label k) q) := by
      simpa using
        (euclideanNorm_finset_sum_le (ι := ι) Finset.univ fun k =>
          logisticGradientContribution (feature k) (label k) q)
    _ ≤ logisticForceBound feature label := by
      unfold logisticForceBound
      apply Finset.sum_le_sum
      intro k _
      unfold logisticGradientContribution
      rw [euclideanNorm_smul, abs_mul, abs_neg]
      rw [abs_of_nonneg (logisticSigmoid_nonneg _)]
      have hsig := mul_le_mul_of_nonneg_left
        (logisticSigmoid_le_one
          (-label k * euclideanInner (feature k) q)) (abs_nonneg (label k))
      simpa only [mul_one] using mul_le_mul_of_nonneg_right hsig
        (euclideanNorm_nonneg (feature k))

/-- The regularized force differs from its linear quadratic part by at most
the finite likelihood-force constant. -/
theorem euclideanNorm_regularizedLogisticGradient_sub_linear_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : ℝ) (q : Position ι) :
    euclideanNorm
        (regularizedLogisticGradient feature label regularization q -
          regularization • q) ≤ logisticForceBound feature label := by
  have hid :
      regularizedLogisticGradient feature label regularization q -
          regularization • q =
        ∑ k, logisticGradientContribution (feature k) (label k) q := by
    unfold regularizedLogisticGradient
    abel
  rw [hid]
  exact euclideanNorm_logisticLikelihoodGradient_le feature label q

/-- The unregularized finite logistic negative log likelihood is nonnegative. -/
theorem logisticNegativeLogLikelihood_nonneg
    (feature : κ → Position ι) (label : κ → ℝ) (q : Position ι) :
    0 ≤ logisticNegativeLogLikelihood feature label q := by
  unfold logisticNegativeLogLikelihood
  exact Finset.sum_nonneg fun k _ => softplus_nonneg _

/-- Positive `L²` regularization gives an explicit quadratic coercive lower
bound for the applied potential. -/
theorem regularizedLogisticPotential_coercive
    (feature : κ → Position ι) (label : κ → ℝ)
    {regularization : ℝ} (_hregularization : 0 ≤ regularization)
    (q : Position ι) :
    regularization * kineticEnergy q ≤
      regularizedLogisticPotential feature label regularization q := by
  unfold regularizedLogisticPotential
  exact le_add_of_nonneg_left
    (logisticNegativeLogLikelihood_nonneg feature label q)

omit [Fintype κ] in
/-- One signed linear score is Lipschitz in the Euclidean position norm. -/
theorem abs_logisticScore_sub_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (q₁ q₂ : Position ι) (k : κ) :
    |logisticScore feature label q₁ k -
        logisticScore feature label q₂ k| ≤
      |label k| * euclideanNorm (feature k) *
        euclideanNorm (q₁ - q₂) := by
  unfold logisticScore
  have hinner :
      euclideanInner (feature k) q₁ - euclideanInner (feature k) q₂ =
        euclideanInner (feature k) (q₁ - q₂) := by
    unfold euclideanInner
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  rw [← mul_sub, abs_mul, abs_neg, hinner]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (abs_euclideanInner_le_norm_mul_norm (feature k) (q₁ - q₂))
    (abs_nonneg (label k))

/-- The full logistic negative log likelihood is globally Lipschitz with the
same finite force constant. -/
theorem abs_logisticNegativeLogLikelihood_sub_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (q₁ q₂ : Position ι) :
    |logisticNegativeLogLikelihood feature label q₁ -
        logisticNegativeLogLikelihood feature label q₂| ≤
      logisticForceBound feature label * euclideanNorm (q₁ - q₂) := by
  unfold logisticNegativeLogLikelihood
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k, (softplus (logisticScore feature label q₁ k) -
        softplus (logisticScore feature label q₂ k))| ≤
      ∑ k, |softplus (logisticScore feature label q₁ k) -
        softplus (logisticScore feature label q₂ k)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (|label k| * euclideanNorm (feature k)) *
        euclideanNorm (q₁ - q₂) := by
      apply Finset.sum_le_sum
      intro k _
      exact (abs_softplus_sub_le _ _).trans
        (abs_logisticScore_sub_le feature label q₁ q₂ k)
    _ = logisticForceBound feature label *
        euclideanNorm (q₁ - q₂) := by
      unfold logisticForceBound
      rw [Finset.sum_mul]

/-- Linear growth of the likelihood around the origin, used to compare the
regularized target with its coercive quadratic part. -/
theorem logisticNegativeLogLikelihood_le_origin_add
    (feature : κ → Position ι) (label : κ → ℝ) (q : Position ι) :
    logisticNegativeLogLikelihood feature label q ≤
      logisticNegativeLogLikelihood feature label 0 +
        logisticForceBound feature label * euclideanNorm q := by
  have habs := abs_logisticNegativeLogLikelihood_sub_le
    feature label q 0
  have hdiff :
      logisticNegativeLogLikelihood feature label q -
          logisticNegativeLogLikelihood feature label 0 ≤
        |logisticNegativeLogLikelihood feature label q -
          logisticNegativeLogLikelihood feature label 0| := le_abs_self _
  calc
    logisticNegativeLogLikelihood feature label q =
        logisticNegativeLogLikelihood feature label 0 +
          (logisticNegativeLogLikelihood feature label q -
            logisticNegativeLogLikelihood feature label 0) := by ring
    _ ≤ logisticNegativeLogLikelihood feature label 0 +
        logisticForceBound feature label * euclideanNorm q := by
      simpa only [sub_zero, add_comm] using add_le_add_left (hdiff.trans habs)
        (logisticNegativeLogLikelihood feature label 0)

/-- At the quadratic-cancellation parameter `ε² λ = 2`, one leapfrog
position update loses its incoming linear position term. Only refreshed
momentum and the uniformly bounded likelihood force remain. -/
theorem regularizedLogistic_leapfrog_fst_of_sq_mul_regularization_eq_two
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    (leapfrog (regularizedLogisticGradient feature label regularization)
      ε (q, p)).1 =
      ε • p - (ε ^ 2 / 2) •
        (∑ k, logisticGradientContribution (feature k) (label k) q) := by
  unfold leapfrog halfKick drift regularizedLogisticGradient
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul]
  have hq : q i * (ε ^ 2 * regularization) = q i * 2 :=
    congrArg (fun x : ℝ => q i * x) hcancel
  nlinarith

/-- Consequently the special one-step proposal position has a norm envelope
independent of the incoming position. -/
theorem euclideanNorm_regularizedLogistic_leapfrog_fst_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    euclideanNorm
        (leapfrog (regularizedLogisticGradient feature label regularization)
          ε (q, p)).1 ≤
      |ε| * euclideanNorm p +
        |ε ^ 2 / 2| * logisticForceBound feature label := by
  rw [regularizedLogistic_leapfrog_fst_of_sq_mul_regularization_eq_two
    feature label regularization ε hcancel q p]
  apply (euclideanNorm_sub_le _ _).trans
  rw [euclideanNorm_smul, euclideanNorm_smul]
  gcongr
  exact euclideanNorm_logisticLikelihoodGradient_le feature label q

/-- At the same cancellation parameter, the momentum update also simplifies:
the incoming momentum and the likelihood force at the incoming position
cancel exactly. -/
theorem regularizedLogistic_leapfrog_snd_of_sq_mul_regularization_eq_two
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    (leapfrog (regularizedLogisticGradient feature label regularization)
      ε (q, p)).2 =
      (-(ε * regularization / 2)) • q - (ε / 2) •
        (∑ k, logisticGradientContribution (feature k) (label k)
          ((leapfrog
            (regularizedLogisticGradient feature label regularization)
            ε (q, p)).1)) := by
  have hqnext :=
    regularizedLogistic_leapfrog_fst_of_sq_mul_regularization_eq_two
      feature label regularization ε hcancel q p
  unfold leapfrog halfKick drift regularizedLogisticGradient
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul] at hqnext ⊢
  have hp : p i * (ε ^ 2 * regularization) = p i * 2 :=
    congrArg (fun x : ℝ => p i * x) hcancel
  have hb :
      (∑ k, logisticGradientContribution (feature k) (label k) q i) *
          (ε ^ 2 * regularization) =
        (∑ k, logisticGradientContribution (feature k) (label k) q i) * 2 :=
    congrArg (fun x : ℝ =>
      (∑ k, logisticGradientContribution (feature k) (label k) q i) * x)
      hcancel
  have hqScaled :
      (ε * regularization * q i) * (ε ^ 2 * regularization) =
        (ε * regularization * q i) * 2 :=
    congrArg (fun x : ℝ => (ε * regularization * q i) * x) hcancel
  have hbScaled :
      (ε * (∑ k, logisticGradientContribution (feature k) (label k) q i)) *
          (ε ^ 2 * regularization) =
        (ε * (∑ k, logisticGradientContribution (feature k) (label k) q i)) * 2 :=
    congrArg (fun x : ℝ =>
      (ε * (∑ k, logisticGradientContribution (feature k) (label k) q i)) * x)
      hcancel
  ring_nf
  nlinarith

/-- The special one-step momentum has a sharp linear-in-position envelope
plus the same bounded likelihood-force allowance. -/
theorem euclideanNorm_regularizedLogistic_leapfrog_snd_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    euclideanNorm
        (leapfrog (regularizedLogisticGradient feature label regularization)
          ε (q, p)).2 ≤
      |ε * regularization / 2| * euclideanNorm q +
        |ε / 2| * logisticForceBound feature label := by
  rw [regularizedLogistic_leapfrog_snd_of_sq_mul_regularization_eq_two
    feature label regularization ε hcancel q p]
  apply (euclideanNorm_sub_le _ _).trans
  rw [euclideanNorm_smul, euclideanNorm_smul, abs_neg]
  gcongr
  exact euclideanNorm_logisticLikelihoodGradient_le feature label _

/-- A weighted two-term square estimate tuned to retain a strict fraction of
the incoming quadratic potential in the logistic HMC energy calculation. -/
theorem squaredEuclideanNorm_sub_le_three_halves_three
    (x y : Position ι) :
    squaredEuclideanNorm (x - y) ≤
      (3 / 2 : ℝ) * squaredEuclideanNorm x +
        3 * squaredEuclideanNorm y := by
  unfold squaredEuclideanNorm euclideanInner
  simp only [Pi.sub_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (x i + 2 * y i)]

/-- At the cancellation step size, the endpoint momentum energy retains only
`3/8` of the incoming quadratic position energy, up to the bounded logistic
force.  The missing `1/8` is the strict coercive margin used below. -/
theorem kineticEnergy_regularizedLogistic_leapfrog_snd_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hregularization : 0 ≤ regularization)
    (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    kineticEnergy
        (leapfrog (regularizedLogisticGradient feature label regularization)
          ε (q, p)).2 ≤
      (3 * regularization / 8) * squaredEuclideanNorm q +
        (3 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2 := by
  rw [regularizedLogistic_leapfrog_snd_of_sq_mul_regularization_eq_two
    feature label regularization ε hcancel q p]
  let b := ∑ k, logisticGradientContribution (feature k) (label k)
    ((leapfrog (regularizedLogisticGradient feature label regularization)
      ε (q, p)).1)
  have hbNorm : euclideanNorm b ≤ logisticForceBound feature label := by
    dsimp only [b]
    exact euclideanNorm_logisticLikelihoodGradient_le feature label _
  have hbSq : squaredEuclideanNorm b ≤ logisticForceBound feature label ^ 2 := by
    rw [← euclideanNorm_sq]
    exact (sq_le_sq₀ (euclideanNorm_nonneg b)
      (logisticForceBound_nonneg feature label)).2 hbNorm
  have hsquare := squaredEuclideanNorm_sub_le_three_halves_three
    ((-(ε * regularization / 2)) • q) ((ε / 2) • b)
  rw [squaredEuclideanNorm_smul, squaredEuclideanNorm_smul] at hsquare
  have hkinetic (x : Momentum ι) :
      kineticEnergy x = (1 / 2 : ℝ) * squaredEuclideanNorm x := by
    unfold kineticEnergy squaredEuclideanNorm euclideanInner
    simp only [pow_two]
  change kineticEnergy
      ((-(ε * regularization / 2)) • q - (ε / 2) • b) ≤ _
  rw [hkinetic]
  have hcoef : ε ^ 2 * regularization ^ 2 = 2 * regularization := by
    nlinarith
  calc
    (1 / 2 : ℝ) * squaredEuclideanNorm
        ((-(ε * regularization / 2)) • q - (ε / 2) • b) ≤
      (1 / 2 : ℝ) * ((3 / 2 : ℝ) * (-(ε * regularization / 2)) ^ 2 *
        squaredEuclideanNorm q + 3 * (ε / 2) ^ 2 *
          squaredEuclideanNorm b) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using hsquare)
        (by norm_num)
    _ = (3 * regularization / 8) * squaredEuclideanNorm q +
        (3 * ε ^ 2 / 8) * squaredEuclideanNorm b := by
      rw [show (-(ε * regularization / 2)) ^ 2 =
          ε ^ 2 * regularization ^ 2 / 4 by ring,
        show (ε / 2) ^ 2 = ε ^ 2 / 4 by ring, hcoef]
      ring
    _ ≤ (3 * regularization / 8) * squaredEuclideanNorm q +
        (3 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2 := by
      have hcoefficient : 0 ≤ (3 * ε ^ 2 / 8 : ℝ) := by positivity
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbSq hcoefficient)

/-- A sharp one-step Hamiltonian-defect envelope for the concrete
regularized-logistic target.  At `ε² λ = 2`, the proposal endpoint is
independent of the incoming position, while the retained term
`-(λ/8) ‖q‖²` drives the acceptance probability of staying at a remote
current position to zero. -/
theorem regularizedLogistic_energy_leapfrog_sub_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hregularization : 0 ≤ regularization)
    (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    energy (regularizedLogisticPotential feature label regularization)
        (leapfrog (regularizedLogisticGradient feature label regularization)
          ε (q, p)) -
      energy (regularizedLogisticPotential feature label regularization)
        (q, p) ≤
      logisticNegativeLogLikelihood feature label 0 +
        logisticForceBound feature label *
          euclideanNorm
            (leapfrog
              (regularizedLogisticGradient feature label regularization)
              ε (q, p)).1 +
        (regularization / 2) *
          squaredEuclideanNorm
            (leapfrog
              (regularizedLogisticGradient feature label regularization)
              ε (q, p)).1 -
        (regularization / 8) * squaredEuclideanNorm q +
        (3 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2 -
        kineticEnergy p := by
  let qNext :=
    (leapfrog (regularizedLogisticGradient feature label regularization)
      ε (q, p)).1
  have hnllNext := logisticNegativeLogLikelihood_le_origin_add
    feature label qNext
  have hnllCurrent := logisticNegativeLogLikelihood_nonneg feature label q
  have hpNext := kineticEnergy_regularizedLogistic_leapfrog_snd_le
    feature label regularization ε hregularization hcancel q p
  unfold energy regularizedLogisticPotential
  change
    logisticNegativeLogLikelihood feature label qNext +
        regularization * kineticEnergy qNext +
        kineticEnergy
          (leapfrog (regularizedLogisticGradient feature label regularization)
            ε (q, p)).2 -
      (logisticNegativeLogLikelihood feature label q +
        regularization * kineticEnergy q + kineticEnergy p) ≤ _
  have hkinetic (x : Position ι) :
      kineticEnergy x = (1 / 2 : ℝ) * squaredEuclideanNorm x := by
    unfold kineticEnergy squaredEuclideanNorm euclideanInner
    simp only [pow_two]
  rw [hkinetic qNext, hkinetic q]
  dsimp only [qNext] at hnllNext ⊢
  nlinarith

/-- The cancellation-step proposal position has a squared-norm envelope
depending only on refreshed momentum and the uniform data-force bound. -/
theorem squaredEuclideanNorm_regularizedLogistic_leapfrog_fst_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    squaredEuclideanNorm
        (leapfrog (regularizedLogisticGradient feature label regularization)
          ε (q, p)).1 ≤
      (3 / 2 : ℝ) * ε ^ 2 * squaredEuclideanNorm p +
        3 * (ε ^ 2 / 2) ^ 2 * logisticForceBound feature label ^ 2 := by
  rw [regularizedLogistic_leapfrog_fst_of_sq_mul_regularization_eq_two
    feature label regularization ε hcancel q p]
  let b := ∑ k, logisticGradientContribution (feature k) (label k) q
  have hbNorm : euclideanNorm b ≤ logisticForceBound feature label := by
    dsimp only [b]
    exact euclideanNorm_logisticLikelihoodGradient_le feature label q
  have hbSq : squaredEuclideanNorm b ≤ logisticForceBound feature label ^ 2 := by
    rw [← euclideanNorm_sq]
    exact (sq_le_sq₀ (euclideanNorm_nonneg b)
      (logisticForceBound_nonneg feature label)).2 hbNorm
  have hsquare := squaredEuclideanNorm_sub_le_three_halves_three
    (ε • p) ((ε ^ 2 / 2) • b)
  rw [squaredEuclideanNorm_smul, squaredEuclideanNorm_smul] at hsquare
  calc
    squaredEuclideanNorm (ε • p - (ε ^ 2 / 2) • b) ≤
        (3 / 2 : ℝ) * ε ^ 2 * squaredEuclideanNorm p +
          3 * (ε ^ 2 / 2) ^ 2 * squaredEuclideanNorm b := by
      simpa only [mul_assoc] using hsquare
    _ ≤ (3 / 2 : ℝ) * ε ^ 2 * squaredEuclideanNorm p +
        3 * (ε ^ 2 / 2) ^ 2 * logisticForceBound feature label ^ 2 := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbSq (by positivity))

/-- Fully explicit cancellation-step energy envelope.  All positive terms
are functions of refreshed momentum and fixed data; dependence on the
current position is the strict coercive term `-(λ/8) ‖q‖²`. -/
theorem regularizedLogistic_energy_leapfrog_sub_le_explicit
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hregularization : 0 ≤ regularization)
    (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    energy (regularizedLogisticPotential feature label regularization)
        (leapfrog (regularizedLogisticGradient feature label regularization)
          ε (q, p)) -
      energy (regularizedLogisticPotential feature label regularization)
        (q, p) ≤
      logisticNegativeLogLikelihood feature label 0 +
        |ε| * logisticForceBound feature label * euclideanNorm p +
        squaredEuclideanNorm p +
        (13 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2 -
        (regularization / 8) * squaredEuclideanNorm q := by
  have henergy := regularizedLogistic_energy_leapfrog_sub_le feature label
    regularization ε hregularization hcancel q p
  have hqNorm := euclideanNorm_regularizedLogistic_leapfrog_fst_le
    feature label regularization ε hcancel q p
  have hqSq := squaredEuclideanNorm_regularizedLogistic_leapfrog_fst_le
    feature label regularization ε hcancel q p
  have hforce := logisticForceBound_nonneg feature label
  have hregForce : 0 ≤ regularization * logisticForceBound feature label ^ 2 :=
    mul_nonneg hregularization (sq_nonneg _)
  have habs : |ε ^ 2 / 2| = ε ^ 2 / 2 := abs_of_nonneg (by positivity)
  have hkinetic (x : Momentum ι) :
      kineticEnergy x = (1 / 2 : ℝ) * squaredEuclideanNorm x := by
    unfold kineticEnergy squaredEuclideanNorm euclideanInner
    simp only [pow_two]
  rw [hkinetic p] at henergy
  rw [habs] at hqNorm
  calc
    energy (regularizedLogisticPotential feature label regularization)
          (leapfrog
            (regularizedLogisticGradient feature label regularization)
            ε (q, p)) -
        energy (regularizedLogisticPotential feature label regularization)
          (q, p) ≤
      logisticNegativeLogLikelihood feature label 0 +
        logisticForceBound feature label *
          (|ε| * euclideanNorm p +
            ε ^ 2 / 2 * logisticForceBound feature label) +
        (regularization / 2) *
          ((3 / 2 : ℝ) * ε ^ 2 * squaredEuclideanNorm p +
            3 * (ε ^ 2 / 2) ^ 2 *
              logisticForceBound feature label ^ 2) -
        (regularization / 8) * squaredEuclideanNorm q +
        (3 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2 -
        (1 / 2 : ℝ) * squaredEuclideanNorm p := by
      refine henergy.trans ?_
      gcongr
    _ = logisticNegativeLogLikelihood feature label 0 +
        |ε| * logisticForceBound feature label * euclideanNorm p +
        squaredEuclideanNorm p +
        (13 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2 -
        (regularization / 8) * squaredEuclideanNorm q := by
      calc
        _ = logisticNegativeLogLikelihood feature label 0 +
              |ε| * logisticForceBound feature label * euclideanNorm p +
              squaredEuclideanNorm p +
              (13 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2 -
              (regularization / 8) * squaredEuclideanNorm q +
            ((3 / 4 : ℝ) * squaredEuclideanNorm p +
              (3 / 8 : ℝ) * ε ^ 2 *
                logisticForceBound feature label ^ 2) *
              (ε ^ 2 * regularization - 2) := by ring
        _ = _ := by rw [hcancel]; ring

/-- Momentum-only part of the cancellation-step energy envelope. -/
noncomputable def regularizedLogisticMomentumEnvelope
    (feature : κ → Position ι) (label : κ → ℝ) (ε : ℝ)
    (p : Momentum ι) : ℝ :=
  logisticNegativeLogLikelihood feature label 0 +
    |ε| * logisticForceBound feature label * euclideanNorm p +
    squaredEuclideanNorm p +
    (13 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2

/-- Full energy envelope, displaying the strict negative radial term. -/
noncomputable def regularizedLogisticEnergyEnvelope
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (q : Position ι) (p : Momentum ι) : ℝ :=
  regularizedLogisticMomentumEnvelope feature label ε p -
    (regularization / 8) * squaredEuclideanNorm q

theorem regularizedLogistic_energy_leapfrog_sub_le_envelope
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hregularization : 0 ≤ regularization)
    (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    energy (regularizedLogisticPotential feature label regularization)
        (leapfrog (regularizedLogisticGradient feature label regularization)
          ε (q, p)) -
      energy (regularizedLogisticPotential feature label regularization)
        (q, p) ≤
      regularizedLogisticEnergyEnvelope feature label regularization ε q p := by
  exact regularizedLogistic_energy_leapfrog_sub_le_explicit feature label
    regularization ε hregularization hcancel q p

/-- In either orientation of a two-point cancellation-step trajectory, the
probability of retaining the current index is bounded by the exponential of
the same negative-quadratic energy envelope. -/
theorem regularizedLogistic_currentIndexProbability_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hregularization : 0 ≤ regularization)
    (hcancel : ε ^ 2 * regularization = 2)
    (origin : Fin 2) (q : Position ι) (p : Momentum ι) :
    trajectoryIndexPMF
        (regularizedLogisticPotential feature label regularization)
        (offsetLeapfrogTrajectory
          (regularizedLogisticGradient feature label regularization)
          ε origin (q, p)) origin ≤
      ENNReal.ofReal (Real.exp
        (regularizedLogisticEnergyEnvelope feature label regularization ε q p)) := by
  fin_cases origin
  · let current : Fin 2 := ⟨0, by omega⟩
    let endpoint : Fin 2 := ⟨1, by omega⟩
    have hprob := trajectoryIndexPMF_le_exp_energy_sub
      (regularizedLogisticPotential feature label regularization)
      (offsetLeapfrogTrajectory
        (regularizedLogisticGradient feature label regularization)
        ε current (q, p)) current endpoint
    dsimp only [current, endpoint] at hprob ⊢
    rw [offsetLeapfrogTrajectory_origin] at hprob
    apply hprob.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact regularizedLogistic_energy_leapfrog_sub_le_envelope feature label
      regularization ε hregularization hcancel q p
  · let endpoint : Fin 2 := ⟨0, by omega⟩
    let current : Fin 2 := ⟨1, by omega⟩
    have hprob := trajectoryIndexPMF_le_exp_energy_sub
      (regularizedLogisticPotential feature label regularization)
      (offsetLeapfrogTrajectory
        (regularizedLogisticGradient feature label regularization)
        ε current (q, p)) current endpoint
    dsimp only [current, endpoint] at hprob ⊢
    rw [offsetLeapfrogTrajectory_origin] at hprob
    apply hprob.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hcancelNeg : (-ε) ^ 2 * regularization = 2 := by
      simpa only [neg_sq] using hcancel
    have henergy :=
      regularizedLogistic_energy_leapfrog_sub_le_envelope feature label
        regularization (-ε) hregularization hcancelNeg q p
    simpa [offsetLeapfrogTrajectory, signedLeapfrog, abs_neg, neg_sq,
      regularizedLogisticEnergyEnvelope,
      regularizedLogisticMomentumEnvelope] using henergy

/-- Either non-current endpoint in the randomly rooted two-point trajectory
has a position cost controlled only by refreshed momentum and the data-force
bound. -/
theorem regularizedLogistic_noncurrentEndpoint_lyapunov_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hcancel : ε ^ 2 * regularization = 2)
    (origin selected : Fin 2) (hne : selected ≠ origin)
    (q : Position ι) (p : Momentum ι) :
    standardDistanceLyapunov
        (offsetLeapfrogTrajectory
          (regularizedLogisticGradient feature label regularization)
          ε origin (q, p) selected).1 ≤
      ENNReal.ofReal
        (1 + |ε| * euclideanNorm p +
          (ε ^ 2 / 2) * logisticForceBound feature label) := by
  apply (standardDistanceLyapunov_le_ofReal_one_add_euclideanNorm _).trans
  apply ENNReal.ofReal_le_ofReal
  fin_cases origin <;> fin_cases selected
  · exact False.elim (hne rfl)
  · simp [offsetLeapfrogTrajectory, signedLeapfrog]
    have h := euclideanNorm_regularizedLogistic_leapfrog_fst_le
      feature label regularization ε hcancel q p
    rw [abs_of_nonneg (by positivity : 0 ≤ ε ^ 2 / 2)] at h
    linarith
  · simp [offsetLeapfrogTrajectory, signedLeapfrog]
    have hcancelNeg : (-ε) ^ 2 * regularization = 2 := by
      simpa only [neg_sq] using hcancel
    have h := euclideanNorm_regularizedLogistic_leapfrog_fst_le
      feature label regularization (-ε) hcancelNeg q p
    rw [abs_of_nonneg (by positivity : 0 ≤ (-ε) ^ 2 / 2)] at h
    have h' : euclideanNorm
        (leapfrog (regularizedLogisticGradient feature label regularization)
          (-ε) (q, p)).1 ≤
        |ε| * euclideanNorm p +
          ε ^ 2 / 2 * logisticForceBound feature label := by
      simpa only [abs_neg, neg_sq] using h
    linarith
  · exact False.elim (hne rfl)

/-- Conditional two-index expectation bound for one randomly rooted
cancellation-step regularized-logistic trajectory. -/
theorem regularizedLogistic_indexExpectation_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hregularization : 0 ≤ regularization)
    (hcancel : ε ^ 2 * regularization = 2)
    (origin : Fin 2) (q : Position ι) (p : Momentum ι) :
    (∑ selected : Fin 2,
      trajectoryIndexPMF
          (regularizedLogisticPotential feature label regularization)
          (offsetLeapfrogTrajectory
            (regularizedLogisticGradient feature label regularization)
            ε origin (q, p)) selected *
        standardDistanceLyapunov
          (offsetLeapfrogTrajectory
            (regularizedLogisticGradient feature label regularization)
            ε origin (q, p) selected).1) ≤
      min 1 (ENNReal.ofReal (Real.exp
          (regularizedLogisticEnergyEnvelope feature label regularization ε q p))) *
          standardDistanceLyapunov q +
        ENNReal.ofReal
          (1 + |ε| * euclideanNorm p +
            (ε ^ 2 / 2) * logisticForceBound feature label) := by
  let trajectory := offsetLeapfrogTrajectory
    (regularizedLogisticGradient feature label regularization) ε origin (q, p)
  let retention := ENNReal.ofReal (Real.exp
    (regularizedLogisticEnergyEnvelope feature label regularization ε q p))
  let endpointCost := ENNReal.ofReal
    (1 + |ε| * euclideanNorm p +
      (ε ^ 2 / 2) * logisticForceBound feature label)
  have hretain : trajectoryIndexPMF
      (regularizedLogisticPotential feature label regularization)
      trajectory origin ≤ min 1 retention := by
    apply le_min
    · exact (trajectoryIndexPMF
        (regularizedLogisticPotential feature label regularization)
        trajectory).coe_le_one origin
    · exact regularizedLogistic_currentIndexProbability_le feature label
        regularization ε hregularization hcancel origin q p
  fin_cases origin
  · rw [Fin.sum_univ_two]
    have hretain0 : trajectoryIndexPMF
        (regularizedLogisticPotential feature label regularization)
        trajectory (0 : Fin 2) ≤ min 1 retention := by
      simpa using hretain
    have hcurrent :
        trajectoryIndexPMF
            (regularizedLogisticPotential feature label regularization)
            trajectory (0 : Fin 2) *
          standardDistanceLyapunov (trajectory (0 : Fin 2)).1 ≤
        min 1 retention * standardDistanceLyapunov q := by
      rw [show trajectory (0 : Fin 2) = (q, p) by simp [trajectory]]
      simpa only [mul_comm] using mul_le_mul_right hretain0
        (standardDistanceLyapunov q)
    have hendpoint :
        trajectoryIndexPMF
            (regularizedLogisticPotential feature label regularization)
            trajectory (1 : Fin 2) *
          standardDistanceLyapunov (trajectory (1 : Fin 2)).1 ≤
        endpointCost := by
      calc
        _ ≤ 1 * standardDistanceLyapunov (trajectory (1 : Fin 2)).1 := by
          gcongr
          exact (trajectoryIndexPMF
            (regularizedLogisticPotential feature label regularization)
            trajectory).coe_le_one _
        _ ≤ endpointCost := by
          rw [one_mul]
          exact regularizedLogistic_noncurrentEndpoint_lyapunov_le
            feature label regularization ε hcancel (0 : Fin 2) (1 : Fin 2)
            (by decide) q p
    exact add_le_add hcurrent hendpoint
  · rw [Fin.sum_univ_two]
    have hretain1 : trajectoryIndexPMF
        (regularizedLogisticPotential feature label regularization)
        trajectory (1 : Fin 2) ≤ min 1 retention := by
      simpa using hretain
    have hendpoint :
        trajectoryIndexPMF
            (regularizedLogisticPotential feature label regularization)
            trajectory (0 : Fin 2) *
          standardDistanceLyapunov (trajectory (0 : Fin 2)).1 ≤
        endpointCost := by
      calc
        _ ≤ 1 * standardDistanceLyapunov (trajectory (0 : Fin 2)).1 := by
          gcongr
          exact (trajectoryIndexPMF
            (regularizedLogisticPotential feature label regularization)
            trajectory).coe_le_one _
        _ ≤ endpointCost := by
          rw [one_mul]
          exact regularizedLogistic_noncurrentEndpoint_lyapunov_le
            feature label regularization ε hcancel (1 : Fin 2) (0 : Fin 2)
            (by decide) q p
    have hcurrent :
        trajectoryIndexPMF
            (regularizedLogisticPotential feature label regularization)
            trajectory (1 : Fin 2) *
          standardDistanceLyapunov (trajectory (1 : Fin 2)).1 ≤
        min 1 retention * standardDistanceLyapunov q := by
      rw [show trajectory (1 : Fin 2) = (q, p) by simp [trajectory]]
      simpa only [mul_comm] using mul_le_mul_right hretain1
        (standardDistanceLyapunov q)
    exact (add_le_add hendpoint hcurrent).trans_eq (add_comm _ _)

/-- Uniformly averaging the two possible trajectory roots preserves the
same retention-plus-endpoint estimate. -/
theorem regularizedLogistic_originIndexExpectation_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) (hregularization : 0 ≤ regularization)
    (hcancel : ε ^ 2 * regularization = 2)
    (q : Position ι) (p : Momentum ι) :
    (∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin *
      ∑ selected : Fin 2,
        trajectoryIndexPMF
            (regularizedLogisticPotential feature label regularization)
            (offsetLeapfrogTrajectory
              (regularizedLogisticGradient feature label regularization)
              ε origin (q, p)) selected *
          standardDistanceLyapunov
            (offsetLeapfrogTrajectory
              (regularizedLogisticGradient feature label regularization)
              ε origin (q, p) selected).1) ≤
      min 1 (ENNReal.ofReal (Real.exp
          (regularizedLogisticEnergyEnvelope feature label regularization ε q p))) *
          standardDistanceLyapunov q +
        ENNReal.ofReal
          (1 + |ε| * euclideanNorm p +
            (ε ^ 2 / 2) * logisticForceBound feature label) := by
  let bound :=
    min 1 (ENNReal.ofReal (Real.exp
        (regularizedLogisticEnergyEnvelope feature label regularization ε q p))) *
        standardDistanceLyapunov q +
      ENNReal.ofReal
        (1 + |ε| * euclideanNorm p +
          (ε ^ 2 / 2) * logisticForceBound feature label)
  calc
    _ ≤ ∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin * bound := by
      apply Finset.sum_le_sum
      intro origin _
      exact mul_le_mul_right
        (regularizedLogistic_indexExpectation_le feature label regularization ε
          hregularization hcancel origin q p)
        (PMF.uniformOfFintype (Fin 2) origin)
    _ = (∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin) * bound := by
      rw [Finset.sum_mul]
    _ = bound := by
      rw [show ∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin = 1 by
        rw [show ∑ origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin =
          ∑' origin : Fin 2, PMF.uniformOfFintype (Fin 2) origin by
            rw [tsum_fintype], PMF.tsum_coe], one_mul]
/-- One logistic gradient contribution is globally Lipschitz, with the
explicit squared feature/label coefficient. -/
theorem euclideanNorm_logisticGradientContribution_sub_le
    (feature : Position ι) (label : ℝ) (q₁ q₂ : Position ι) :
    euclideanNorm
        (logisticGradientContribution feature label q₁ -
          logisticGradientContribution feature label q₂) ≤
      label ^ 2 * euclideanNorm feature ^ 2 *
        euclideanNorm (q₁ - q₂) := by
  let s₁ := -label * euclideanInner feature q₁
  let s₂ := -label * euclideanInner feature q₂
  have hscore : |s₁ - s₂| ≤
      |label| * euclideanNorm feature * euclideanNorm (q₁ - q₂) := by
    have hinner :
        euclideanInner feature q₁ - euclideanInner feature q₂ =
          euclideanInner feature (q₁ - q₂) := by
      unfold euclideanInner
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply]
      ring
    dsimp only [s₁, s₂]
    rw [← mul_sub, abs_mul, abs_neg, hinner]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (abs_euclideanInner_le_norm_mul_norm feature (q₁ - q₂))
      (abs_nonneg label)
  have hsig := abs_logisticSigmoid_sub_le s₁ s₂
  have hcoef :
      |-label * logisticSigmoid s₁ -
          (-label * logisticSigmoid s₂)| ≤
        label ^ 2 * euclideanNorm feature *
          euclideanNorm (q₁ - q₂) := by
    rw [← mul_sub, abs_mul, abs_neg]
    calc
      |label| * |logisticSigmoid s₁ - logisticSigmoid s₂| ≤
          |label| * |s₁ - s₂| :=
        mul_le_mul_of_nonneg_left hsig (abs_nonneg label)
      _ ≤ |label| *
          (|label| * euclideanNorm feature * euclideanNorm (q₁ - q₂)) :=
        mul_le_mul_of_nonneg_left hscore (abs_nonneg label)
      _ = label ^ 2 * euclideanNorm feature *
          euclideanNorm (q₁ - q₂) := by rw [← sq_abs label]; ring
  unfold logisticGradientContribution
  rw [show
      (-label * logisticSigmoid (-label * euclideanInner feature q₁)) • feature -
          (-label * logisticSigmoid (-label * euclideanInner feature q₂)) • feature =
        ((-label * logisticSigmoid s₁) -
          (-label * logisticSigmoid s₂)) • feature by
      dsimp only [s₁, s₂]
      funext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring]
  rw [euclideanNorm_smul]
  calc
    _ ≤ (label ^ 2 * euclideanNorm feature *
        euclideanNorm (q₁ - q₂)) * euclideanNorm feature :=
      mul_le_mul_of_nonneg_right hcoef (euclideanNorm_nonneg feature)
    _ = label ^ 2 * euclideanNorm feature ^ 2 *
        euclideanNorm (q₁ - q₂) := by ring

/-- Sum of the explicit per-observation gradient-Lipschitz coefficients. -/
noncomputable def logisticSmoothness
    (feature : κ → Position ι) (label : κ → ℝ) : NNReal :=
  ∑ k, ⟨label k ^ 2 * euclideanNorm (feature k) ^ 2,
    mul_nonneg (sq_nonneg _) (sq_nonneg _)⟩

@[simp]
theorem coe_logisticSmoothness
    (feature : κ → Position ι) (label : κ → ℝ) :
    (logisticSmoothness feature label : ℝ) =
      ∑ k, label k ^ 2 * euclideanNorm (feature k) ^ 2 := by
  rw [logisticSmoothness, NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- The exact logistic gradient is globally Euclidean-Lipschitz after adding
positive quadratic regularization. -/
theorem regularizedLogisticGradient_lipschitz
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (q₁ q₂ : Position ι) :
    euclideanNorm
        (regularizedLogisticGradient feature label regularization q₁ -
          regularizedLogisticGradient feature label regularization q₂) ≤
      ((regularization + logisticSmoothness feature label : NNReal) : ℝ) *
        euclideanNorm (q₁ - q₂) := by
  let d := q₁ - q₂
  have hid :
      regularizedLogisticGradient feature label regularization q₁ -
          regularizedLogisticGradient feature label regularization q₂ =
        (regularization : ℝ) • d +
          ∑ k, (logisticGradientContribution (feature k) (label k) q₁ -
            logisticGradientContribution (feature k) (label k) q₂) := by
    ext i
    simp only [regularizedLogisticGradient, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul, d]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  apply (euclideanNorm_add_le _ _).trans
  calc
    euclideanNorm ((regularization : ℝ) • d) +
        euclideanNorm (∑ k,
          (logisticGradientContribution (feature k) (label k) q₁ -
            logisticGradientContribution (feature k) (label k) q₂)) ≤
      (regularization : ℝ) * euclideanNorm d +
        ∑ k, euclideanNorm
          (logisticGradientContribution (feature k) (label k) q₁ -
            logisticGradientContribution (feature k) (label k) q₂) := by
      rw [euclideanNorm_smul, abs_of_nonneg regularization.coe_nonneg]
      gcongr
      simpa only [Finset.sum_const_zero, Finset.sum_filter] using
        (euclideanNorm_finset_sum_le (ι := ι) Finset.univ fun k =>
          logisticGradientContribution (feature k) (label k) q₁ -
            logisticGradientContribution (feature k) (label k) q₂)
    _ ≤ (regularization : ℝ) * euclideanNorm d +
        ∑ k, (label k ^ 2 * euclideanNorm (feature k) ^ 2) *
          euclideanNorm d := by
      gcongr with k
      exact euclideanNorm_logisticGradientContribution_sub_le
        (feature k) (label k) q₁ q₂
    _ = ((regularization + logisticSmoothness feature label : NNReal) : ℝ) *
        euclideanNorm (q₁ - q₂) := by
      rw [← Finset.sum_mul, NNReal.coe_add, coe_logisticSmoothness]
      dsimp only [d]
      ring

/-- The regularized finite logistic target satisfies Xu et al.'s global
regularity assumption with an explicit data-dependent constant. -/
theorem regularPotential_regularizedLogistic
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization) :
    RegularPotential
      (regularizedLogisticPotential feature label regularization)
      (regularizedLogisticGradient feature label regularization)
      (regularization + logisticSmoothness feature label) where
  beta_pos := lt_of_lt_of_le hregularization (le_add_right le_rfl)
  contDiff_two :=
    contDiff_regularizedLogisticPotential feature label regularization
  fderiv_apply :=
    fderiv_regularizedLogisticPotential_apply feature label regularization
  gradient_lipschitz :=
    regularizedLogisticGradient_lipschitz feature label regularization

/-- Drift-ready momentum-integral bound for the actual regularized-logistic
position multinomial-HMC kernel with `L = 1`. Everything remaining on the
right is a scalar radial Gaussian-momentum estimate. -/
theorem lintegral_regularizedLogistic_hmc_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (hcancel : ε ^ 2 * (regularization : ℝ) = 2)
    (q : Position ι) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂standardPositionMultinomialHMC
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticGradient feature label regularization)
        ε 1
        (contDiff_regularizedLogisticPotential feature label
          regularization).continuous.measurable
        (regularPotential_regularizedLogistic feature label regularization
          hregularization).contDiff_one_gradient.continuous.measurable q) ≤
      ∫⁻ p : Momentum ι,
        min 1 (ENNReal.ofReal (Real.exp
            (regularizedLogisticEnergyEnvelope feature label regularization ε q p))) *
            standardDistanceLyapunov q +
          ENNReal.ofReal
            (1 + |ε| * euclideanNorm p +
              (ε ^ 2 / 2) * logisticForceBound feature label)
        ∂standardMomentumMeasure := by
  rw [standardPositionMultinomialHMC]
  rw [lintegral_positionMultinomialHMC
    (regularizedLogisticPotential feature label regularization)
    (regularizedLogisticGradient feature label regularization)
    ε 1
    (contDiff_regularizedLogisticPotential feature label
      regularization).continuous.measurable
    (regularPotential_regularizedLogistic feature label regularization
      hregularization).contDiff_one_gradient.continuous.measurable
    standardMomentumMeasure standardDistanceLyapunov
    measurable_standardDistanceLyapunov]
  exact lintegral_mono fun p =>
    regularizedLogistic_originIndexExpectation_le feature label regularization ε
      regularization.coe_nonneg hcancel q p

/-- Position-independent constant in the logistic momentum energy envelope. -/
noncomputable def regularizedLogisticEnvelopeConstant
    (feature : κ → Position ι) (label : κ → ℝ) (ε : ℝ) : ℝ :=
  logisticNegativeLogLikelihood feature label 0 +
    (13 * ε ^ 2 / 8) * logisticForceBound feature label ^ 2

/-- Rescaling factor incurred when the negative quadratic energy tail has
coefficient `regularization / 8`. -/
noncomputable def regularizedLogisticRetentionScale
    (regularization : ℝ) : ℝ :=
  1 + 1 / (2 * Real.sqrt (regularization / 8))

/-- Constant part of the integrated cancellation-step drift envelope. -/
noncomputable def regularizedLogisticDriftBase
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization ε : ℝ) : ℝ :=
  regularizedLogisticRetentionScale regularization *
      (16 + 2 *
        (Real.sqrt (2 * regularizedLogisticEnvelopeConstant feature label ε) +
          |ε| * logisticForceBound feature label)) +
    1 + (ε ^ 2 / 2) * logisticForceBound feature label

/-- Coefficient of the refreshed momentum norm in the drift envelope. -/
noncomputable def regularizedLogisticDriftSlope
    (regularization ε : ℝ) : ℝ :=
  6 * regularizedLogisticRetentionScale regularization + |ε|

/-- The complete conditional logistic HMC drift integrand grows at most
linearly in refreshed momentum. -/
theorem regularizedLogistic_driftIntegrand_le
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (q : Position ι) (p : Momentum ι) :
    min 1 (ENNReal.ofReal (Real.exp
        (regularizedLogisticEnergyEnvelope feature label regularization ε q p))) *
        standardDistanceLyapunov q +
      ENNReal.ofReal
        (1 + |ε| * euclideanNorm p +
          (ε ^ 2 / 2) * logisticForceBound feature label) ≤
      ENNReal.ofReal
        (regularizedLogisticDriftBase feature label regularization ε +
          regularizedLogisticDriftSlope regularization ε * euclideanNorm p) := by
  let qr := euclideanNorm q
  let pr := euclideanNorm p
  let B := logisticForceBound feature label
  let C := regularizedLogisticEnvelopeConstant feature label ε
  let a := |ε| * B
  let c := (regularization : ℝ) / 8
  let scale := regularizedLogisticRetentionScale (regularization : ℝ)
  have hqr : 0 ≤ qr := euclideanNorm_nonneg q
  have hpr : 0 ≤ pr := euclideanNorm_nonneg p
  have hB : 0 ≤ B := logisticForceBound_nonneg feature label
  have hC : 0 ≤ C := by
    dsimp only [C, regularizedLogisticEnvelopeConstant, B]
    exact add_nonneg (logisticNegativeLogLikelihood_nonneg feature label 0)
      (mul_nonneg (by positivity) (sq_nonneg _))
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg ε) hB
  have hc : 0 < c := by dsimp only [c]; positivity
  have hscale : 0 ≤ scale := by
    dsimp only [scale, regularizedLogisticRetentionScale]
    positivity
  have henvelope :
      regularizedLogisticEnergyEnvelope feature label regularization ε q p =
        (C + a * pr + pr ^ 2) - c * qr ^ 2 := by
    dsimp only [regularizedLogisticEnergyEnvelope,
      regularizedLogisticMomentumEnvelope, C,
      regularizedLogisticEnvelopeConstant, a, c, B, pr, qr]
    rw [euclideanNorm_sq p, euclideanNorm_sq q]
    ring
  have hscalar := min_one_exp_sub_quadratic_mul_one_add_le
    (show 0 ≤ C + a * pr + pr ^ 2 by positivity) hc hqr
  have hsqrt := sqrt_two_mul_add_mul_add_sq_le hC ha hpr
  have hretentionReal :
      min 1 (Real.exp
          ((C + a * pr + pr ^ 2) - c * qr ^ 2)) * (1 + qr) ≤
        scale * (16 + 2 * (Real.sqrt (2 * C) + a + 3 * pr)) := by
    apply hscalar.trans
    dsimp only [scale, regularizedLogisticRetentionScale, c]
    apply mul_le_mul_of_nonneg_left _ hscale
    nlinarith
  have hretention :
      min 1 (ENNReal.ofReal (Real.exp
          (regularizedLogisticEnergyEnvelope feature label regularization ε q p))) *
          standardDistanceLyapunov q ≤
        ENNReal.ofReal
          (scale * (16 + 2 * (Real.sqrt (2 * C) + a + 3 * pr))) := by
    apply le_trans (by
      simpa only [mul_comm] using mul_le_mul_right
        (standardDistanceLyapunov_le_ofReal_one_add_euclideanNorm q)
        (min 1 (ENNReal.ofReal (Real.exp
          (regularizedLogisticEnergyEnvelope feature label regularization ε q p)))))
    rw [henvelope, ← ENNReal.ofReal_one, ← ENNReal.ofReal_min,
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by
      simpa only [mul_comm] using hretentionReal)
  have hendpointNonneg :
      0 ≤ 1 + |ε| * pr + (ε ^ 2 / 2) * B := by positivity
  have hretentionBoundNonneg :
      0 ≤ scale * (16 + 2 * (Real.sqrt (2 * C) + a + 3 * pr)) := by
    positivity
  calc
    _ ≤ ENNReal.ofReal
          (scale * (16 + 2 * (Real.sqrt (2 * C) + a + 3 * pr))) +
        ENNReal.ofReal (1 + |ε| * pr + (ε ^ 2 / 2) * B) :=
      add_le_add hretention le_rfl
    _ = ENNReal.ofReal
        (regularizedLogisticDriftBase feature label regularization ε +
          regularizedLogisticDriftSlope regularization ε * pr) := by
      rw [← ENNReal.ofReal_add hretentionBoundNonneg hendpointNonneg]
      apply congrArg ENNReal.ofReal
      dsimp only [regularizedLogisticDriftBase,
        regularizedLogisticDriftSlope, scale, C, a, B]
      ring
    _ = _ := rfl

theorem regularizedLogisticDriftBase_nonneg
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) :
    0 ≤ regularizedLogisticDriftBase feature label regularization ε := by
  unfold regularizedLogisticDriftBase regularizedLogisticRetentionScale
  have hB := logisticForceBound_nonneg feature label
  have hC : 0 ≤ regularizedLogisticEnvelopeConstant feature label ε := by
    unfold regularizedLogisticEnvelopeConstant
    exact add_nonneg (logisticNegativeLogLikelihood_nonneg feature label 0)
      (mul_nonneg (by positivity) (sq_nonneg _))
  positivity

theorem regularizedLogisticDriftSlope_nonneg
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) :
    0 ≤ regularizedLogisticDriftSlope regularization ε := by
  unfold regularizedLogisticDriftSlope regularizedLogisticRetentionScale
  positivity

/-- Explicit finite allowance obtained by integrating the linear radial
envelope against refreshed standard Gaussian momentum. -/
noncomputable def regularizedLogisticDriftAllowance
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (ε : ℝ) : ENNReal :=
  ENNReal.ofReal
      (regularizedLogisticDriftBase feature label regularization ε) +
    ENNReal.ofReal (regularizedLogisticDriftSlope regularization ε) *
      (∫⁻ p : Momentum ι, ENNReal.ofReal (euclideanNorm p)
        ∂standardMomentumMeasure)

theorem regularizedLogisticDriftAllowance_ne_top
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (ε : ℝ) :
    regularizedLogisticDriftAllowance feature label regularization ε ≠ ⊤ := by
  unfold regularizedLogisticDriftAllowance
  exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      lintegral_euclideanNorm_standardMomentumMeasure_ne_top⟩

/-- The conditional cancellation-step drift envelope integrates to the
explicit finite allowance, uniformly in the current position. -/
theorem regularizedLogistic_envelope_le_allowance
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (q : Position ι) :
    (∫⁻ p : Momentum ι,
      min 1 (ENNReal.ofReal (Real.exp
          (regularizedLogisticEnergyEnvelope feature label regularization ε q p))) *
          standardDistanceLyapunov q +
        ENNReal.ofReal
          (1 + |ε| * euclideanNorm p +
            (ε ^ 2 / 2) * logisticForceBound feature label)
      ∂standardMomentumMeasure) ≤
        regularizedLogisticDriftAllowance feature label regularization ε := by
  let base := regularizedLogisticDriftBase feature label regularization ε
  let slope := regularizedLogisticDriftSlope regularization ε
  have hbase : 0 ≤ base :=
    regularizedLogisticDriftBase_nonneg feature label regularization
      hregularization ε
  have hslope : 0 ≤ slope :=
    regularizedLogisticDriftSlope_nonneg regularization hregularization ε
  calc
    _ ≤ ∫⁻ p : Momentum ι,
        ENNReal.ofReal (base + slope * euclideanNorm p)
        ∂standardMomentumMeasure := by
      exact lintegral_mono fun p =>
        regularizedLogistic_driftIntegrand_le feature label regularization
          hregularization ε q p
    _ = ∫⁻ p : Momentum ι,
        ENNReal.ofReal base +
          ENNReal.ofReal slope * ENNReal.ofReal (euclideanNorm p)
        ∂standardMomentumMeasure := by
      apply lintegral_congr
      intro p
      rw [ENNReal.ofReal_add hbase
        (mul_nonneg hslope (euclideanNorm_nonneg p)),
        ENNReal.ofReal_mul hslope]
    _ = ENNReal.ofReal base + ENNReal.ofReal slope *
        (∫⁻ p : Momentum ι, ENNReal.ofReal (euclideanNorm p)
          ∂standardMomentumMeasure) := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ,
        mul_one]
      congr 1
      exact lintegral_const_mul _
        ((ENNReal.continuous_ofReal.comp continuous_euclideanNorm).measurable)
    _ = regularizedLogisticDriftAllowance feature label regularization ε := rfl

/-- Strict affine drift for the actual finite-data regularized-logistic
multinomial-HMC kernel at every cancellation parameter `ε² λ = 2`, with
`L = 1`. -/
theorem regularizedLogistic_hmc_drift
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    (ε : ℝ) (hcancel : ε ^ 2 * (regularization : ℝ) = 2)
    (q : Position ι) :
    (∫⁻ y, standardDistanceLyapunov y
      ∂standardPositionMultinomialHMC
        (regularizedLogisticPotential feature label regularization)
        (regularizedLogisticGradient feature label regularization)
        ε 1
        (contDiff_regularizedLogisticPotential feature label
          regularization).continuous.measurable
        (regularPotential_regularizedLogistic feature label regularization
          hregularization).contDiff_one_gradient.continuous.measurable q) ≤
      (1 / 2 : ENNReal) * standardDistanceLyapunov q +
        regularizedLogisticDriftAllowance feature label regularization ε := by
  have huniform := (lintegral_regularizedLogistic_hmc_le feature label
    regularization hregularization ε hcancel q).trans
      (regularizedLogistic_envelope_le_allowance feature label regularization
        hregularization ε q)
  exact huniform.trans (le_add_left le_rfl)

/-- A single logistic likelihood-gradient contribution is monotone. -/
theorem logisticGradientContribution_monotone
    (feature : Position ι) (label : ℝ) (q₁ q₂ : Position ι) :
    0 ≤ euclideanInner (q₁ - q₂)
      (logisticGradientContribution feature label q₁ -
        logisticGradientContribution feature label q₂) := by
  let t₁ := -label * euclideanInner feature q₁
  let t₂ := -label * euclideanInner feature q₂
  have hid :
      euclideanInner (q₁ - q₂)
          (logisticGradientContribution feature label q₁ -
            logisticGradientContribution feature label q₂) =
        (t₁ - t₂) * (logisticSigmoid t₁ - logisticSigmoid t₂) := by
    unfold logisticGradientContribution
    dsimp only [t₁, t₂]
    simp only [euclideanInner, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hinner :
        ∑ x, (q₁ x - q₂ x) * feature x =
          euclideanInner feature q₁ - euclideanInner feature q₂ := by
      unfold euclideanInner
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      ∑ x, (q₁ x - q₂ x) *
          ((-label * logisticSigmoid (-label * euclideanInner feature q₁)) *
              feature x -
            (-label * logisticSigmoid (-label * euclideanInner feature q₂)) *
              feature x) =
        (-label * (logisticSigmoid
            (-label * euclideanInner feature q₁) -
          logisticSigmoid (-label * euclideanInner feature q₂))) *
          ∑ x, (q₁ x - q₂ x) * feature x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = _ := by
        rw [hinner]
        unfold euclideanInner
        have hcomm1 : ∑ x, feature x * q₁ x = ∑ x, q₁ x * feature x := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        have hcomm2 : ∑ x, feature x * q₂ x = ∑ x, q₂ x * feature x := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hcomm1, hcomm2]
        ring
  rw [hid]
  by_cases hle : t₁ ≤ t₂
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hle)
      (sub_nonpos.mpr (monotone_logisticSigmoid hle))
  · have hle' : t₂ ≤ t₁ := le_of_not_ge hle
    exact mul_nonneg (sub_nonneg.mpr hle')
      (sub_nonneg.mpr (monotone_logisticSigmoid hle'))

/-- Positive quadratic regularization makes the full logistic gradient
globally strongly monotone with exactly the regularization modulus. -/
theorem regularizedLogisticGradient_strongMonotone
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (q₁ q₂ : Position ι) :
    (regularization : ℝ) * squaredEuclideanNorm (q₁ - q₂) ≤
      euclideanInner (q₁ - q₂)
        (regularizedLogisticGradient feature label regularization q₁ -
          regularizedLogisticGradient feature label regularization q₂) := by
  let d := q₁ - q₂
  have hid :
      regularizedLogisticGradient feature label regularization q₁ -
          regularizedLogisticGradient feature label regularization q₂ =
        (regularization : ℝ) • d +
          ∑ k, (logisticGradientContribution (feature k) (label k) q₁ -
            logisticGradientContribution (feature k) (label k) q₂) := by
    ext i
    simp only [regularizedLogisticGradient, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul, d]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid]
  have hsum : 0 ≤ ∑ k, euclideanInner d
      (logisticGradientContribution (feature k) (label k) q₁ -
        logisticGradientContribution (feature k) (label k) q₂) :=
    Finset.sum_nonneg fun k _ => by
      dsimp only [d]
      exact logisticGradientContribution_monotone
        (feature k) (label k) q₁ q₂
  have hexpand :
      euclideanInner (q₁ - q₂)
          ((regularization : ℝ) • d +
            ∑ k, (logisticGradientContribution (feature k) (label k) q₁ -
              logisticGradientContribution (feature k) (label k) q₂)) =
        (regularization : ℝ) * squaredEuclideanNorm (q₁ - q₂) +
          ∑ k, euclideanInner d
            (logisticGradientContribution (feature k) (label k) q₁ -
              logisticGradientContribution (feature k) (label k) q₂) := by
    unfold euclideanInner squaredEuclideanNorm
    dsimp only [d]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    apply congrArg₂ (· + ·)
    · unfold euclideanInner
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
  rw [hexpand]
  nlinarith

/-- Every positive-radius ball supplies the compact positive-volume local
strong-convexity region required by Xu et al. -/
theorem localStrongConvexity_regularizedLogistic_closedBall
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    {r : ℝ} (hr : 0 < r) :
    LocalStrongConvexity
      (regularizedLogisticGradient feature label regularization)
      (Metric.closedBall (0 : Position ι) r) regularization where
  alpha_pos := hregularization
  compact := isCompact_closedBall 0 r
  measurableSet := measurableSet_closedBall
  volume_pos := Metric.measure_closedBall_pos volume 0 hr
  strongMonotone := by
    intro q₁ _ q₂ _
    exact regularizedLogisticGradient_strongMonotone
      feature label regularization q₁ q₂

/-- The verified regularized-logistic target has a concrete positive HMC
integration window on which the implemented maximal shared-momentum coupling
enters a relaxed diagonal uniformly from any strictly smaller closed ball.
This discharges the local HMC premise of the Xu meeting theorem; the separate
global Foster--Lyapunov drift certificate remains target- and parameter-
specific. -/
theorem exists_regularizedLogistic_maximalSharedMomentum_relaxedAccessible
    (feature : κ → Position ι) (label : κ → ℝ)
    (regularization : NNReal) (hregularization : 0 < regularization)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ δ > 0,
      ∃ entry : ENNReal, 0 < entry ∧
        ∃ εbar > 0, ∀ {ε : ℝ} {L : ℕ},
          0 < ε → ε ≤ εbar →
          Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
          McmcLean.Kernel.IsRelaxedMeetingAccessibleFrom
            (maximalSharedMomentumCoupledPositionMultinomialHMC
              (regularizedLogisticPotential feature label regularization)
              (regularizedLogisticGradient feature label regularization)
              ε L
              (contDiff_regularizedLogisticPotential feature label
                regularization).continuous.measurable
              (regularPotential_regularizedLogistic feature label
                regularization hregularization).contDiff_one_gradient.continuous.measurable)
            (Metric.closedBall (0 : Position ι) r) δ 1 entry := by
  let potential := regularizedLogisticPotential feature label regularization
  let gradient := regularizedLogisticGradient feature label regularization
  let hreg : RegularPotential potential gradient
      (regularization + logisticSmoothness feature label) :=
    regularPotential_regularizedLogistic feature label regularization
      hregularization
  let S : Set (Position ι) := Metric.closedBall 0 R
  let K : Set (Position ι) := Metric.closedBall 0 r
  have hconv : LocalStrongConvexity gradient S regularization :=
    localStrongConvexity_regularizedLogistic_closedBall
      feature label regularization hregularization (lt_trans hr hrR)
  have hK : IsCompact K := isCompact_closedBall 0 r
  have hKS : K ⊆ interior S := by
    rw [show interior S = Metric.ball 0 R by
      dsimp only [S]
      exact interior_closedBall 0 (ne_of_gt (lt_trans hr hrR))]
    intro q hq
    rw [Metric.mem_ball]
    exact (Metric.mem_closedBall.mp hq).trans_lt hrR
  simpa only [potential, gradient, K, S] using
    hconv.exists_maximalSharedMomentum_isRelaxedMeetingAccessible
      hreg hK hKS hconv.compact (convex_closedBall 0 R)

end FiniteData

end McmcLean.Hamiltonian
