import Mcmc.Relativistic.ScalarSliceBounds

/-!
# Generic scalar generalized-leapfrog Jacobians

This module extracts the triangular-map calculation from the original bounded
scalar client.  It applies to arbitrary differentiable scalar coordinate
callbacks and isolates the single Hamiltonian input: equality of the two mixed
partials.
-/

namespace Mcmc.Relativistic

/-- Vertical triangular shear and its derivative matrix. -/
noncomputable def scalarVerticalShear
    (a : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, z.2 + a * F z)

noncomputable def scalarVerticalShearFDeriv
    (a : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1, 0;
      a * fderiv ℝ F z (1, 0),
      1 + a * fderiv ℝ F z (0, 1)]).toContinuousLinearMap

theorem hasFDerivAt_scalarVerticalShear
    (a : ℝ) (F : ℝ × ℝ → ℝ) (hF : Differentiable ℝ F)
    (z : ℝ × ℝ) :
    HasFDerivAt (scalarVerticalShear a F)
      (scalarVerticalShearFDeriv a F z) z := by
  unfold scalarVerticalShearFDeriv scalarVerticalShear
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! HasFDerivAt.prodMk (𝕜 := ℝ) hasFDerivAt_fst
    (hasFDerivAt_snd.add ((hF z).hasFDerivAt.const_mul a)) using 2
  · simp
  · apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨v₁, v₂⟩
    have hv : fderiv ℝ F z (v₁, v₂) =
        v₁ * fderiv ℝ F z (1, 0) +
          v₂ * fderiv ℝ F z (0, 1) := by
      have hvec : (v₁, v₂) = v₁ • (1, 0) + v₂ • (0, 1) := by
        ext <;> simp
      simpa only [map_add, map_smul, smul_eq_mul] using
        congrArg (fderiv ℝ F z) hvec
    change (a * fderiv ℝ F z (1, 0)) * v₁ +
        (1 + a * fderiv ℝ F z (0, 1)) * v₂ =
      v₂ + a * fderiv ℝ F z (v₁, v₂)
    rw [hv]
    ring

theorem det_scalarVerticalShearFDeriv
    (a : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    (scalarVerticalShearFDeriv a F z).det =
      1 + a * fderiv ℝ F z (0, 1) := by
  unfold scalarVerticalShearFDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

/-- Horizontal triangular shear and its derivative matrix. -/
noncomputable def scalarHorizontalShear
    (a : ℝ) (G : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 + a * G z, z.2)

noncomputable def scalarHorizontalShearFDeriv
    (a : ℝ) (G : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![1 + a * fderiv ℝ G z (1, 0),
      a * fderiv ℝ G z (0, 1);
      0, 1]).toContinuousLinearMap

theorem hasFDerivAt_scalarHorizontalShear
    (a : ℝ) (G : ℝ × ℝ → ℝ) (hG : Differentiable ℝ G)
    (z : ℝ × ℝ) :
    HasFDerivAt (scalarHorizontalShear a G)
      (scalarHorizontalShearFDeriv a G z) z := by
  unfold scalarHorizontalShearFDeriv scalarHorizontalShear
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! HasFDerivAt.prodMk (𝕜 := ℝ)
    (hasFDerivAt_fst.add ((hG z).hasFDerivAt.const_mul a))
    hasFDerivAt_snd using 2
  · apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨v₁, v₂⟩
    have hv : fderiv ℝ G z (v₁, v₂) =
        v₁ * fderiv ℝ G z (1, 0) +
          v₂ * fderiv ℝ G z (0, 1) := by
      have hvec : (v₁, v₂) = v₁ • (1, 0) + v₂ • (0, 1) := by
        ext <;> simp
      simpa only [map_add, map_smul, smul_eq_mul] using
        congrArg (fderiv ℝ G z) hvec
    change (1 + a * fderiv ℝ G z (1, 0)) * v₁ +
        (a * fderiv ℝ G z (0, 1)) * v₂ =
      v₁ + a * fderiv ℝ G z (v₁, v₂)
    rw [hv]
    ring
  · simp

theorem det_scalarHorizontalShearFDeriv
    (a : ℝ) (G : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    (scalarHorizontalShearFDeriv a G z).det =
      1 + a * fderiv ℝ G z (1, 0) := by
  unfold scalarHorizontalShearFDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

/-- Equality of Hamiltonian mixed partials makes the incoming and right-stage
determinants agree at the same half-step state. -/
theorem det_scalar_shears_eq_of_mixed
    (a : ℝ) (F G : ℝ × ℝ → ℝ) (z : ℝ × ℝ)
    (hmixed : fderiv ℝ F z (0, 1) = fderiv ℝ G z (1, 0)) :
    (scalarVerticalShearFDeriv a F z).det =
      (scalarHorizontalShearFDeriv a G z).det := by
  rw [det_scalarVerticalShearFDeriv,
    det_scalarHorizontalShearFDeriv, hmixed]

/-- The same equality pairs the negative horizontal and vertical stages at
the outgoing half-step state. -/
theorem det_scalar_negative_shears_eq_of_mixed
    (a : ℝ) (F G : ℝ × ℝ → ℝ) (z : ℝ × ℝ)
    (hmixed : fderiv ℝ F z (0, 1) = fderiv ℝ G z (1, 0)) :
    (scalarHorizontalShearFDeriv (-a) G z).det =
      (scalarVerticalShearFDeriv (-a) F z).det := by
  rw [det_scalarVerticalShearFDeriv,
    det_scalarHorizontalShearFDeriv, hmixed]

/-- Mixed momentum derivative of the generic scalar position callback. -/
theorem deriv_scalarGRPositionCallback_snd
    (drift scale scaleDerivative : ℝ → ℝ)
    (hscalePos : ∀ x, 0 < scale x) (q p : ℝ) :
    deriv (fun r => scalarGRPositionCallback drift scale scaleDerivative
      (q, r)) p =
      scaleDerivative q *
        (2 * scalarVelocityProfile (scale q * p) -
          scalarVelocityProfile (scale q * p) ^ 3) := by
  let s := scale q
  let x := s * p
  let inner : ℝ → ℝ := fun r => s * r
  have hs : s ≠ 0 := (hscalePos q).ne'
  have hw : HasDerivAt scalarPositionProfile
      (2 * scalarVelocityProfile x - scalarVelocityProfile x ^ 3) x := by
    rw [← deriv_scalarPositionProfile x]
    exact (differentiable_scalarPositionProfile x).hasDerivAt
  have hinner : HasDerivAt inner s p := by
    dsimp [inner]
    simpa using (hasDerivAt_id p).const_mul s
  have hcomp := hw.comp p hinner
  have hcomp' : HasDerivAt (fun r => scalarPositionProfile (s * r))
      ((2 * scalarVelocityProfile x - scalarVelocityProfile x ^ 3) * s) p := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with r
    rfl
  have hout := (hasDerivAt_const p (drift q)).add
    (hcomp'.const_mul (scaleDerivative q / s))
  have hlocal : (fun r => scalarGRPositionCallback drift scale scaleDerivative
      (q, r)) =ᶠ[nhds p]
      ((fun _ => drift q) + fun y => scaleDerivative q / s *
        scalarPositionProfile (s * y)) := by
    filter_upwards [] with r
    rfl
  rw [hlocal.deriv_eq, hout.deriv]
  dsimp [x, s]
  field_simp [(hscalePos q).ne']
  ring

/-- Mixed position derivative of the generic scalar momentum callback. -/
theorem deriv_scalarGRMomentumCallback_fst
    (scale scaleDerivative : ℝ → ℝ)
    (hscale : ∀ q, HasDerivAt scale (scaleDerivative q) q)
    (q p : ℝ) :
    deriv (fun r => scalarGRMomentumCallback scale (r, p)) q =
      scaleDerivative q *
        (scalarVelocityProfile (scale q * p) +
          (scale q * p) /
            scalarRelativisticProfile (scale q * p) ^ 3) := by
  have houter : HasDerivAt (scaledVelocityProfile p)
      (scalarVelocityProfile (scale q * p) +
        (scale q * p) /
          scalarRelativisticProfile (scale q * p) ^ 3) (scale q) := by
    rw [← deriv_scaledVelocityProfile p (scale q)]
    exact ((differentiableAt_id.mul
      (differentiable_scalarVelocityProfile.differentiableAt.comp
        (scale q) (by fun_prop))).hasDerivAt)
  have hcomp := houter.comp q (hscale q)
  rw [show (fun r => scalarGRMomentumCallback scale (r, p)) =
      scaledVelocityProfile p ∘ scale by rfl, hcomp.deriv]
  ring

/-- Equality of mixed derivatives for every differentiable positive scalar
factor. This is the Hamiltonian input to the triangular determinant pairing. -/
theorem scalarGRCallbacks_mixed_derivatives_eq
    (drift scale : ℝ → ℝ) (hscale : Differentiable ℝ scale)
    (hscalePos : ∀ x, 0 < scale x) (q p : ℝ) :
    deriv (fun r => scalarGRPositionCallback drift scale (deriv scale)
      (q, r)) p =
    deriv (fun r => scalarGRMomentumCallback scale (r, p)) q := by
  rw [deriv_scalarGRPositionCallback_snd drift scale (deriv scale)
      hscalePos,
    deriv_scalarGRMomentumCallback_fst scale (deriv scale)
      (fun x => (hscale x).hasDerivAt)]
  rw [scalarProfile_mixed_identity]

theorem fderiv_apply_snd_eq_deriv_slice
    (F : ℝ × ℝ → ℝ) (hF : Differentiable ℝ F) (q p : ℝ) :
    fderiv ℝ F (q, p) (0, 1) = deriv (fun r => F (q, r)) p := by
  have hcomp := (hF (q, p)).hasFDerivAt.comp p
    (hasFDerivAt_prodMk_right q p)
  exact hcomp.hasDerivAt.deriv.symm

theorem fderiv_apply_fst_eq_deriv_slice
    (G : ℝ × ℝ → ℝ) (hG : Differentiable ℝ G) (q p : ℝ) :
    fderiv ℝ G (q, p) (1, 0) = deriv (fun r => G (r, p)) q := by
  have hleft := HasFDerivAt.prodMk (𝕜 := ℝ)
    (hasFDerivAt_id q) (hasFDerivAt_const p q)
  have hcomp := (hG (q, p)).hasFDerivAt.comp q
    hleft
  exact hcomp.hasDerivAt.deriv.symm

/-- Fréchet-coordinate form consumed directly by the generic shear
determinant theorems. -/
theorem scalarGRCallbacks_fderiv_mixed_eq
    (drift scale : ℝ → ℝ) (hscale : Differentiable ℝ scale)
    (hscalePos : ∀ x, 0 < scale x)
    (hposition : Differentiable ℝ
      (scalarGRPositionCallback drift scale (deriv scale)))
    (hmomentum : Differentiable ℝ (scalarGRMomentumCallback scale))
    (z : ℝ × ℝ) :
    fderiv ℝ (scalarGRPositionCallback drift scale (deriv scale)) z (0, 1) =
      fderiv ℝ (scalarGRMomentumCallback scale) z (1, 0) := by
  rcases z with ⟨q, p⟩
  rw [fderiv_apply_snd_eq_deriv_slice _ hposition,
    fderiv_apply_fst_eq_deriv_slice _ hmomentum]
  exact scalarGRCallbacks_mixed_derivatives_eq drift scale hscale
    hscalePos q p

/-- Four-stage scalar generalized-leapfrog map built from two inverse
selections and the two explicit triangular transfers. -/
noncomputable def scalarGeneralizedLeapfrogStep
    (a : ℝ) (F G : ℝ × ℝ → ℝ)
    (incomingInverse leftInverse : ℝ × ℝ → ℝ × ℝ) :
    ℝ × ℝ → ℝ × ℝ :=
  scalarVerticalShear (-a) F ∘ leftInverse ∘
    scalarHorizontalShear a G ∘ incomingInverse

theorem differentiable_scalarGeneralizedLeapfrogStep
    (a : ℝ) (F G : ℝ × ℝ → ℝ)
    (incomingInverse leftInverse : ℝ × ℝ → ℝ × ℝ)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hinverse : Differentiable ℝ incomingInverse)
    (hleft : Differentiable ℝ leftInverse) :
    Differentiable ℝ (scalarGeneralizedLeapfrogStep a F G
      incomingInverse leftInverse) := by
  unfold scalarGeneralizedLeapfrogStep
  have hout : Differentiable ℝ (scalarVerticalShear (-a) F) := by
    unfold scalarVerticalShear
    fun_prop
  have hright : Differentiable ℝ (scalarHorizontalShear a G) := by
    unfold scalarHorizontalShear
    fun_prop
  exact hout.comp (hleft.comp (hright.comp hinverse))

/-- Generic inverse-stage determinant theorem. It is independent of how the
inverse selections were constructed; Banach fixed points are one client. -/
theorem det_fderiv_scalarGeneralizedLeapfrogStep_eq_one
    (a : ℝ) (F G : ℝ × ℝ → ℝ)
    (incomingInverse leftInverse : ℝ × ℝ → ℝ × ℝ)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hinverse : Differentiable ℝ incomingInverse)
    (hleft : Differentiable ℝ leftInverse)
    (hincomingLeft : Function.LeftInverse
      (scalarVerticalShear a F) incomingInverse)
    (hleftLeft : Function.LeftInverse
      (scalarHorizontalShear (-a) G) leftInverse)
    (hmixed : ∀ z,
      fderiv ℝ F z (0, 1) = fderiv ℝ G z (1, 0))
    (z : ℝ × ℝ) :
    (fderiv ℝ (scalarGeneralizedLeapfrogStep a F G
      incomingInverse leftInverse) z).det = 1 := by
  let half := incomingInverse z
  let right := scalarHorizontalShear a G half
  let next := leftInverse right
  have hincomingDiff : Differentiable ℝ (scalarVerticalShear a F) := by
    unfold scalarVerticalShear
    fun_prop
  have hrightDiff : Differentiable ℝ (scalarHorizontalShear a G) := by
    unfold scalarHorizontalShear
    fun_prop
  have hleftMapDiff : Differentiable ℝ (scalarHorizontalShear (-a) G) := by
    unfold scalarHorizontalShear
    fun_prop
  have houtDiff : Differentiable ℝ (scalarVerticalShear (-a) F) := by
    unfold scalarVerticalShear
    fun_prop
  have hinverseDet := det_fderiv_mul_det_fderiv_of_leftInverse
    (scalarVerticalShear a F) incomingInverse hincomingDiff hinverse
    hincomingLeft z
  have hleftInverseDet := det_fderiv_mul_det_fderiv_of_leftInverse
    (scalarHorizontalShear (-a) G) leftInverse hleftMapDiff hleft
    hleftLeft right
  have hhalf := (hinverse z).hasFDerivAt
  have hright := hasFDerivAt_scalarHorizontalShear a G hG half
  have hnext := (hleft right).hasFDerivAt
  have hout := hasFDerivAt_scalarVerticalShear (-a) F hF next
  have hcomp := hout.comp z (hnext.comp z (hright.comp z hhalf))
  have hdetStep :
      (fderiv ℝ (scalarGeneralizedLeapfrogStep a F G
        incomingInverse leftInverse) z).det =
      (scalarVerticalShearFDeriv (-a) F next).det *
        (fderiv ℝ leftInverse right).det *
        (scalarHorizontalShearFDeriv a G half).det *
        (fderiv ℝ incomingInverse z).det := by
    rw [show scalarGeneralizedLeapfrogStep a F G
        incomingInverse leftInverse =
      scalarVerticalShear (-a) F ∘ leftInverse ∘
        scalarHorizontalShear a G ∘ incomingInverse by rfl]
    rw [hcomp.fderiv]
    simp only [det_continuousLinearMap_comp]
    ring
  have hincomingActual :
      (fderiv ℝ (scalarVerticalShear a F) half).det =
        (scalarVerticalShearFDeriv a F half).det := by
    rw [(hasFDerivAt_scalarVerticalShear a F hF half).fderiv]
  have hleftActual :
      (fderiv ℝ (scalarHorizontalShear (-a) G) next).det =
        (scalarHorizontalShearFDeriv (-a) G next).det := by
    rw [(hasFDerivAt_scalarHorizontalShear (-a) G hG next).fderiv]
  have hrightIncoming := det_scalar_shears_eq_of_mixed
    a F G half (hmixed half)
  have houtLeft := det_scalar_negative_shears_eq_of_mixed
    a F G next (hmixed next)
  rw [hdetStep]
  rw [← houtLeft, ← hrightIncoming]
  rw [hincomingActual] at hinverseDet
  rw [hleftActual] at hleftInverseDet
  nlinarith

/-- A strict slice-contraction bound makes every incoming triangular
Jacobian nonsingular. -/
theorem det_scalarVerticalShearFDeriv_ne_zero_of_lipschitz
    (a : ℝ) (F : ℝ × ℝ → ℝ) (K : NNReal)
    (hF : Differentiable ℝ F)
    (hlip : ∀ q, LipschitzWith K (fun p => F (q, p)))
    (hstep : |a| * K < 1) (z : ℝ × ℝ) :
    (scalarVerticalShearFDeriv a F z).det ≠ 0 := by
  rcases z with ⟨q, p⟩
  rw [det_scalarVerticalShearFDeriv,
    fderiv_apply_snd_eq_deriv_slice F hF q p]
  have hd : |deriv (fun r => F (q, r)) p| ≤ K := by
    simpa [Real.norm_eq_abs] using
      norm_deriv_le_of_lipschitz (x₀ := p) (hlip q)
  have hproduct : |a * deriv (fun r => F (q, r)) p| < 1 := by
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hd (abs_nonneg a)) hstep
  intro hzero
  have : a * deriv (fun r => F (q, r)) p = -1 := by linarith
  rw [this, abs_neg, abs_one] at hproduct
  exact (lt_irrefl 1 hproduct)

/-- The corresponding strict position-slice bound makes both signs of the
horizontal triangular Jacobian nonsingular. -/
theorem det_scalarHorizontalShearFDeriv_ne_zero_of_lipschitz
    (a : ℝ) (G : ℝ × ℝ → ℝ) (K : NNReal)
    (hG : Differentiable ℝ G)
    (hlip : ∀ p, LipschitzWith K (fun q => G (q, p)))
    (hstep : |a| * K < 1) (z : ℝ × ℝ) :
    (scalarHorizontalShearFDeriv a G z).det ≠ 0 := by
  rcases z with ⟨q, p⟩
  rw [det_scalarHorizontalShearFDeriv,
    fderiv_apply_fst_eq_deriv_slice G hG q p]
  have hd : |deriv (fun r => G (r, p)) q| ≤ K := by
    simpa [Real.norm_eq_abs] using
      norm_deriv_le_of_lipschitz (x₀ := q) (hlip p)
  have hproduct : |a * deriv (fun r => G (r, p)) q| < 1 := by
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hd (abs_nonneg a)) hstep
  intro hzero
  have : a * deriv (fun r => G (r, p)) q = -1 := by linarith
  rw [this, abs_neg, abs_one] at hproduct
  exact (lt_irrefl 1 hproduct)

noncomputable def scalarSliceRate (a : ℝ) (K : NNReal) : NNReal :=
  ⟨|a| * K, mul_nonneg (abs_nonneg _) K.2⟩

noncomputable def scalarIncomingInverseUpdate
    (a : ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (r : ℝ) : ℝ :=
  z.2 - a * F (z.1, r)

theorem scalarIncomingInverseUpdate_contracting
    (a : ℝ) (F : ℝ × ℝ → ℝ) (K : NNReal)
    (hlip : ∀ q, LipschitzWith K (fun p => F (q, p)))
    (hstep : |a| * K < 1) (z : ℝ × ℝ) :
    ContractingWith (scalarSliceRate a K)
      (scalarIncomingInverseUpdate a F z) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro p r
    rw [Real.dist_eq]
    unfold scalarIncomingInverseUpdate scalarSliceRate
    rw [show (z.2 - a * F (z.1, p)) - (z.2 - a * F (z.1, r)) =
      -a * (F (z.1, p) - F (z.1, r)) by ring, abs_mul, abs_neg]
    calc
      |a| * |F (z.1, p) - F (z.1, r)| ≤
          |a| * (K * |p - r|) := by
        gcongr
        simpa [Real.dist_eq] using (hlip z.1).dist_le_mul p r
      _ = (⟨|a| * K, mul_nonneg (abs_nonneg _) K.2⟩ : NNReal) *
          |p - r| := by
        change |a| * ((K : ℝ) * |p - r|) =
          (|a| * (K : ℝ)) * |p - r|
        ring

/-- Banach-selected inverse of the incoming vertical shear. -/
noncomputable def scalarIncomingInverse
    (a : ℝ) (F : ℝ × ℝ → ℝ) (K : NNReal)
    (hlip : ∀ q, LipschitzWith K (fun p => F (q, p)))
    (hstep : |a| * K < 1) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1, (scalarIncomingInverseUpdate_contracting a F K hlip hstep z).fixedPoint
    (scalarIncomingInverseUpdate a F z))

theorem scalarVerticalShear_leftInverse_scalarIncomingInverse
    (a : ℝ) (F : ℝ × ℝ → ℝ) (K : NNReal)
    (hlip : ∀ q, LipschitzWith K (fun p => F (q, p)))
    (hstep : |a| * K < 1) :
    Function.LeftInverse (scalarVerticalShear a F)
      (scalarIncomingInverse a F K hlip hstep) := by
  intro z
  let r := (scalarIncomingInverseUpdate_contracting a F K hlip hstep z).fixedPoint
    (scalarIncomingInverseUpdate a F z)
  have hfixed :=
    (scalarIncomingInverseUpdate_contracting a F K hlip hstep z).fixedPoint_isFixedPt
  apply Prod.ext
  · rfl
  · change r + a * F (z.1, r) = z.2
    have hr : r = z.2 - a * F (z.1, r) := by
      simpa [r, scalarIncomingInverseUpdate] using hfixed.symm
    linarith

theorem continuous_scalarIncomingInverse
    (a : ℝ) (F : ℝ × ℝ → ℝ) (K : NNReal)
    (hF : Continuous F)
    (hlip : ∀ q, LipschitzWith K (fun p => F (q, p)))
    (hstep : |a| * K < 1) :
    Continuous (scalarIncomingInverse a F K hlip hstep) := by
  let update := scalarIncomingInverseUpdate a F
  have hjoint : Continuous fun z : (ℝ × ℝ) × ℝ => update z.1 z.2 := by
    unfold update scalarIncomingInverseUpdate
    exact continuous_fst.snd.sub (continuous_const.mul
      (hF.comp (continuous_fst.fst.prodMk continuous_snd)))
  have hfixed := continuous_fixedPoint_of_continuous_uniform_contracting
    (scalarSliceRate a K) hstep update hjoint
      (fun z => (scalarIncomingInverseUpdate_contracting
        a F K hlip hstep z).2)
  unfold scalarIncomingInverse
  exact continuous_fst.prodMk hfixed

noncomputable def scalarLeftInverseUpdate
    (a : ℝ) (G : ℝ × ℝ → ℝ) (y : ℝ × ℝ) (q : ℝ) : ℝ :=
  y.1 + a * G (q, y.2)

theorem scalarLeftInverseUpdate_contracting
    (a : ℝ) (G : ℝ × ℝ → ℝ) (K : NNReal)
    (hlip : ∀ p, LipschitzWith K (fun q => G (q, p)))
    (hstep : |a| * K < 1) (y : ℝ × ℝ) :
    ContractingWith (scalarSliceRate a K)
      (scalarLeftInverseUpdate a G y) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro q r
    rw [Real.dist_eq]
    unfold scalarLeftInverseUpdate scalarSliceRate
    rw [show (y.1 + a * G (q, y.2)) - (y.1 + a * G (r, y.2)) =
      a * (G (q, y.2) - G (r, y.2)) by ring, abs_mul]
    calc
      |a| * |G (q, y.2) - G (r, y.2)| ≤
          |a| * (K * |q - r|) := by
        gcongr
        simpa [Real.dist_eq] using (hlip y.2).dist_le_mul q r
      _ = (⟨|a| * K, mul_nonneg (abs_nonneg _) K.2⟩ : NNReal) *
          |q - r| := by
        change |a| * ((K : ℝ) * |q - r|) =
          (|a| * (K : ℝ)) * |q - r|
        ring

/-- Banach-selected inverse of the left horizontal shear. -/
noncomputable def scalarLeftInverse
    (a : ℝ) (G : ℝ × ℝ → ℝ) (K : NNReal)
    (hlip : ∀ p, LipschitzWith K (fun q => G (q, p)))
    (hstep : |a| * K < 1) (y : ℝ × ℝ) : ℝ × ℝ :=
  ((scalarLeftInverseUpdate_contracting a G K hlip hstep y).fixedPoint
    (scalarLeftInverseUpdate a G y), y.2)

theorem scalarHorizontalShear_leftInverse_scalarLeftInverse
    (a : ℝ) (G : ℝ × ℝ → ℝ) (K : NNReal)
    (hlip : ∀ p, LipschitzWith K (fun q => G (q, p)))
    (hstep : |a| * K < 1) :
    Function.LeftInverse (scalarHorizontalShear (-a) G)
      (scalarLeftInverse a G K hlip hstep) := by
  intro y
  let q := (scalarLeftInverseUpdate_contracting a G K hlip hstep y).fixedPoint
    (scalarLeftInverseUpdate a G y)
  have hfixed :=
    (scalarLeftInverseUpdate_contracting a G K hlip hstep y).fixedPoint_isFixedPt
  unfold scalarHorizontalShear scalarLeftInverse
  simp only [neg_mul]
  change (q - a * G (q, y.2), y.2) = y
  apply Prod.ext
  · change q - a * G (q, y.2) = y.1
    have hq : q = y.1 + a * G (q, y.2) := by
      simpa [q, scalarLeftInverseUpdate] using hfixed.symm
    linarith
  · rfl

theorem continuous_scalarLeftInverse
    (a : ℝ) (G : ℝ × ℝ → ℝ) (K : NNReal)
    (hG : Continuous G)
    (hlip : ∀ p, LipschitzWith K (fun q => G (q, p)))
    (hstep : |a| * K < 1) :
    Continuous (scalarLeftInverse a G K hlip hstep) := by
  let update := scalarLeftInverseUpdate a G
  have hjoint : Continuous fun z : (ℝ × ℝ) × ℝ => update z.1 z.2 := by
    unfold update scalarLeftInverseUpdate
    exact continuous_fst.fst.add (continuous_const.mul
      (hG.comp (continuous_snd.prodMk continuous_fst.snd)))
  have hfixed := continuous_fixedPoint_of_continuous_uniform_contracting
    (scalarSliceRate a K) hstep update hjoint
      (fun y => (scalarLeftInverseUpdate_contracting
        a G K hlip hstep y).2)
  unfold scalarLeftInverse
  exact hfixed.prodMk continuous_snd

theorem differentiable_scalarIncomingInverse
    (a : ℝ) (F : ℝ × ℝ → ℝ) (K : NNReal)
    (hF : Differentiable ℝ F)
    (hlip : ∀ q, LipschitzWith K (fun p => F (q, p)))
    (hstep : |a| * K < 1) :
    Differentiable ℝ (scalarIncomingInverse a F K hlip hstep) := by
  apply differentiable_of_continuous_leftInverse_of_det_fderiv_ne_zero
    (scalarVerticalShear a F) (scalarIncomingInverse a F K hlip hstep)
    (by unfold scalarVerticalShear; fun_prop)
    (continuous_scalarIncomingInverse a F K hF.continuous hlip hstep)
    (scalarVerticalShear_leftInverse_scalarIncomingInverse a F K hlip hstep)
  intro z
  rw [(hasFDerivAt_scalarVerticalShear a F hF z).fderiv]
  exact det_scalarVerticalShearFDeriv_ne_zero_of_lipschitz
    a F K hF hlip hstep z

theorem differentiable_scalarLeftInverse
    (a : ℝ) (G : ℝ × ℝ → ℝ) (K : NNReal)
    (hG : Differentiable ℝ G)
    (hlip : ∀ p, LipschitzWith K (fun q => G (q, p)))
    (hstep : |a| * K < 1) :
    Differentiable ℝ (scalarLeftInverse a G K hlip hstep) := by
  apply differentiable_of_continuous_leftInverse_of_det_fderiv_ne_zero
    (scalarHorizontalShear (-a) G) (scalarLeftInverse a G K hlip hstep)
    (by unfold scalarHorizontalShear; fun_prop)
    (continuous_scalarLeftInverse a G K hG.continuous hlip hstep)
    (scalarHorizontalShear_leftInverse_scalarLeftInverse a G K hlip hstep)
  intro z
  rw [(hasFDerivAt_scalarHorizontalShear (-a) G hG z).fderiv]
  apply det_scalarHorizontalShearFDeriv_ne_zero_of_lipschitz
    (-a) G K hG hlip
  · simpa only [abs_neg] using hstep

/-- Fully constructed scalar exact generalized-leapfrog step from the two
global slice-Lipschitz bounds. -/
noncomputable def scalarBanachGeneralizedLeapfrogStep
    (a : ℝ) (F G : ℝ × ℝ → ℝ) (KF KG : NNReal)
    (hlipF : ∀ q, LipschitzWith KF (fun p => F (q, p)))
    (hlipG : ∀ p, LipschitzWith KG (fun q => G (q, p)))
    (hstepF : |a| * KF < 1) (hstepG : |a| * KG < 1) :
    ℝ × ℝ → ℝ × ℝ :=
  scalarGeneralizedLeapfrogStep a F G
    (scalarIncomingInverse a F KF hlipF hstepF)
    (scalarLeftInverse a G KG hlipG hstepG)

/-- End-to-end determinant-one theorem for the Banach-selected scalar step. -/
theorem det_fderiv_scalarBanachGeneralizedLeapfrogStep_eq_one
    (a : ℝ) (F G : ℝ × ℝ → ℝ) (KF KG : NNReal)
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hlipF : ∀ q, LipschitzWith KF (fun p => F (q, p)))
    (hlipG : ∀ p, LipschitzWith KG (fun q => G (q, p)))
    (hstepF : |a| * KF < 1) (hstepG : |a| * KG < 1)
    (hmixed : ∀ z,
      fderiv ℝ F z (0, 1) = fderiv ℝ G z (1, 0))
    (z : ℝ × ℝ) :
    (fderiv ℝ (scalarBanachGeneralizedLeapfrogStep a F G KF KG
      hlipF hlipG hstepF hstepG) z).det = 1 := by
  exact det_fderiv_scalarGeneralizedLeapfrogStep_eq_one
    a F G
    (scalarIncomingInverse a F KF hlipF hstepF)
    (scalarLeftInverse a G KG hlipG hstepG)
    hF hG
    (differentiable_scalarIncomingInverse a F KF hF hlipF hstepF)
    (differentiable_scalarLeftInverse a G KG hG hlipG hstepG)
    (scalarVerticalShear_leftInverse_scalarIncomingInverse
      a F KF hlipF hstepF)
    (scalarHorizontalShear_leftInverse_scalarLeftInverse
      a G KG hlipG hstepG)
    hmixed z

end Mcmc.Relativistic
