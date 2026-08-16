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

end Mcmc.Relativistic
