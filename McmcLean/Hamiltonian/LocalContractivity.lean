import McmcLean.Hamiltonian.CoupledMultinomialHMC
import McmcLean.Hamiltonian.ExactFlow
import McmcLean.Hamiltonian.LeapfrogContraction
import McmcLean.Hamiltonian.TrajectoryWeightBounds
import McmcLean.Finite.GreedyTransportCompleteness
import McmcLean.Finite.Transport
import McmcLean.Kernel.MeetingDrift
import Mathlib.Data.Int.NatAbs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Local contractivity for coupled multinomial HMC

This module records Condition 1 of Xu, Fjelde, Sutton, and Ge (2021) with its
uniform parameter quantifiers.  It is deliberately separate from the simpler
kernel-level expected-distance consequence in `McmcLean.Kernel.MeetingDrift`.

The uniformly sampled trajectory origin represents the paper's split into
backward and forward leapfrog steps.  Quantifying over every origin is the
finite-index form of quantifying over all such splits.
-/

open scoped ENNReal
open ProbabilityTheory

namespace McmcLean.Hamiltonian

variable {ι : Type*} [Fintype ι]

/-- A parameterized choice of joint trajectory-index law. The arguments are
step size, total number of leapfrog steps, paired phase points, and the shared
index occupied by the current state. -/
abbrev TrajectoryIndexCouplingFamily (ι : Type*) [Fintype ι] :=
  (ε : ℝ) → (L : ℕ) → PhaseSpace ι × PhaseSpace ι → Fin (L + 1) →
    PMF (Fin (L + 1) × Fin (L + 1))

/-- Squared Euclidean separation of the two initial positions, as a finite
nonnegative scalar. -/
noncomputable def initialSquaredPositionDistance
    (q₁ q₂ : Position ι) : NNReal :=
  ⟨euclideanNorm (q₁ - q₂) ^ 2, sq_nonneg _⟩

/-- Euclidean separation of the two initial positions as a finite
nonnegative scalar, used by the paper's first-moment maximal-coupling route. -/
noncomputable def initialPositionDistance
    (q₁ q₂ : Position ι) : NNReal :=
  ⟨euclideanNorm (q₁ - q₂), euclideanNorm_nonneg _⟩

/-- Weighted Cauchy--Schwarz turns a second-moment contraction into a
first-moment contraction. The weights need only have total mass at most one,
as happens for the pointwise overlap of two categorical laws. -/
theorem weightedFirstMoment_le_sqrtRate
    {κ : Type*} [Fintype κ] (weight distance : κ → NNReal)
    (rate initial : NNReal)
    (hweight : ∑ i, weight i ≤ 1)
    (hsecond : ∑ i, weight i * distance i ^ 2 ≤ rate * initial ^ 2) :
    ∑ i, weight i * distance i ≤ NNReal.sqrt rate * initial := by
  calc
    ∑ i, weight i * distance i =
        ∑ i, NNReal.sqrt (weight i) *
          NNReal.sqrt (weight i * distance i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [NNReal.sqrt_mul, NNReal.sqrt_sq]
      calc
        weight i * distance i =
            (NNReal.sqrt (weight i) * NNReal.sqrt (weight i)) * distance i := by
          rw [NNReal.mul_self_sqrt]
        _ = NNReal.sqrt (weight i) *
            (NNReal.sqrt (weight i) * distance i) := by ring
    _ ≤ NNReal.sqrt (∑ i, weight i) *
          NNReal.sqrt (∑ i, weight i * distance i ^ 2) :=
      NNReal.sum_sqrt_mul_sqrt_le Finset.univ weight
        (fun i => weight i * distance i ^ 2)
    _ ≤ NNReal.sqrt 1 * NNReal.sqrt (rate * initial ^ 2) := by
      gcongr
    _ = NNReal.sqrt rate * initial := by
      simp [NNReal.sqrt_mul]

/-- Any strictly positive exact squared-distance loss below one leaves a
strictly positive numerical-error allowance while keeping the combined
aligned rate below one. -/
theorem exists_nnreal_exactRate_errorRate_sq_lt_one
    {loss : ℝ} (hloss : 0 < loss) (hlossOne : loss ≤ 1) :
    ∃ exactRate errorRate : NNReal,
      0 < errorRate ∧
      1 - loss ≤ (exactRate : ℝ) ^ 2 ∧
      ((exactRate + errorRate : NNReal) : ℝ) ^ 2 < 1 := by
  let r : ℝ := Real.sqrt (1 - loss)
  have hbase : 0 ≤ 1 - loss := sub_nonneg.mpr hlossOne
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = 1 - loss := Real.sq_sqrt hbase
  have hrlt : r < 1 := by
    nlinarith
  let exactRate : NNReal := ⟨r, hr0⟩
  let errorRate : NNReal := ⟨(1 - r) / 2, by linarith⟩
  refine ⟨exactRate, errorRate, ?_, ?_, ?_⟩
  · change 0 < (1 - r) / 2
    linarith
  · change 1 - loss ≤ r ^ 2
    exact hrsq.symm.le
  · change (r + (1 - r) / 2) ^ 2 < 1
    nlinarith

/-- On a positive integration-time window, the loss at `Tmin` supplies one
uniform exact rate and one positive numerical-error allowance for every later
time. -/
theorem exists_nnreal_exactRate_errorRate_sq_lt_one_on_window
    {κ θ Tmin : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (hTmin : 0 < Tmin)
    (hlossOne : κ * θ * Tmin ^ 2 ≤ 1) :
    ∃ exactRate errorRate : NNReal,
      0 < errorRate ∧
      (∀ t : ℝ, Tmin ≤ t →
        1 - κ * θ * t ^ 2 ≤ (exactRate : ℝ) ^ 2) ∧
      ((exactRate + errorRate : NNReal) : ℝ) ^ 2 < 1 := by
  have hloss : 0 < κ * θ * Tmin ^ 2 := by positivity
  obtain ⟨exactRate, errorRate, herror, hexact, hsum⟩ :=
    exists_nnreal_exactRate_errorRate_sq_lt_one hloss hlossOne
  refine ⟨exactRate, errorRate, herror, ?_, hsum⟩
  intro t ht
  have ht0 : 0 ≤ t := hTmin.le.trans ht
  have hsquares : Tmin ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ hTmin.le ht0).mpr ht
  have hcoeff : 0 ≤ κ * θ := mul_nonneg hκ.le hθ.le
  have hlossMono := mul_le_mul_of_nonneg_left hsquares hcoeff
  exact (sub_le_sub_left hlossMono 1).trans hexact

/-- Budget-facing version of the window rate selection, including the
canonical subunit aligned rate. -/
theorem exists_nnreal_alignedRate_lt_one_on_window
    {κ θ Tmin : ℝ} (hκ : 0 < κ) (hθ : 0 < θ) (hTmin : 0 < Tmin)
    (hlossOne : κ * θ * Tmin ^ 2 ≤ 1) :
    ∃ exactRate errorRate alignedRate : NNReal,
      0 < errorRate ∧ alignedRate < 1 ∧
      alignedRate = (exactRate + errorRate) ^ 2 ∧
      ∀ t : ℝ, Tmin ≤ t →
        1 - κ * θ * t ^ 2 ≤ (exactRate : ℝ) ^ 2 := by
  obtain ⟨exactRate, errorRate, herror, hexact, hsum⟩ :=
    exists_nnreal_exactRate_errorRate_sq_lt_one_on_window
      hκ hθ hTmin hlossOne
  let alignedRate : NNReal := (exactRate + errorRate) ^ 2
  have haligned : alignedRate < 1 := by
    apply NNReal.coe_lt_coe.mp
    simpa only [alignedRate, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one]
      using hsum
  exact ⟨exactRate, errorRate, alignedRate, herror, haligned, rfl, hexact⟩

/-- A positive band-mass floor lets the numerical allowance be reduced so
that the endpoint-band gain outweighs the whole-window excess above one. -/
theorem exists_pos_errorRate_twoRate_weighted_lt_one
    {r errorCap η : ℝ} (hr0 : 0 ≤ r) (herrorCap : 0 < errorCap)
    (hbandCap : (r + errorCap) ^ 2 < 1)
    (hη : 0 < η) :
    ∃ errorRate : ℝ, 0 < errorRate ∧ errorRate ≤ errorCap ∧
      (r + errorRate) ^ 2 < 1 ∧
      (1 + errorRate) ^ 2 -
        η * ((1 + errorRate) ^ 2 - (r + errorRate) ^ 2) < 1 := by
  have hrlt : r < 1 := by
    have hsum0 : 0 ≤ r + errorCap := by linarith
    nlinarith
  have hgap : 0 < η * (1 - r ^ 2) := by
    have : 0 < 1 - r ^ 2 := by nlinarith
    positivity
  let errorRate := min (errorCap / 2)
    (min (1 / 2) (η * (1 - r ^ 2) / 8))
  have herrorRate : 0 < errorRate := by
    dsimp [errorRate]
    exact lt_min (half_pos herrorCap)
      (lt_min (by norm_num) (div_pos hgap (by norm_num)))
  have herrorLe : errorRate ≤ errorCap :=
    (min_le_left _ _).trans (by linarith)
  have herrorOne : errorRate ≤ 1 / 2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have herrorGap : errorRate ≤ η * (1 - r ^ 2) / 8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hband : (r + errorRate) ^ 2 < 1 := by
    have hsumLe : r + errorRate ≤ r + errorCap := by linarith
    have hsum0 : 0 ≤ r + errorRate := by linarith
    nlinarith
  refine ⟨errorRate, herrorRate, herrorLe, hband, ?_⟩
  have hgain : 1 - r ^ 2 ≤
      (1 + errorRate) ^ 2 - (r + errorRate) ^ 2 := by
    nlinarith
  have hηgain := mul_le_mul_of_nonneg_left hgain hη.le
  have hexcess : (1 + errorRate) ^ 2 - 1 < η * (1 - r ^ 2) := by
    nlinarith
  nlinarith

/-- Compact-uniform numerical contraction on a genuine positive integration
window. This instantiates the exact-flow certificate, constructs the common
Euclidean envelope, chooses a numerical error allowance, and transfers the
exact squared loss to leapfrog with a uniform subunit factor. -/
theorem LocalStrongConvexity.exists_uniform_leapfrogN_contraction_on_window
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∃ Tmin > 0, ∃ Tmax > 4 * Tmin, ∃ εbar > 0,
      ∃ exactRate errorRate : NNReal,
        0 < errorRate ∧
        ((exactRate + errorRate : NNReal) : ℝ) ^ 2 < 1 ∧
        ((1 + errorRate : NNReal) : ℝ) ^ 2 -
            (4 * Real.exp 2)⁻¹ *
              (((1 + errorRate : NNReal) : ℝ) ^ 2 -
                ((exactRate + errorRate : NNReal) : ℝ) ^ 2) < 1 ∧
        (∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
          IsHamiltonianCurve gradient q₁ p₁ →
          IsHamiltonianCurve gradient q₂ p₂ →
          q₁ 0 ∈ K → q₂ 0 ∈ K →
          euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
          euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
          p₁ 0 = p₂ 0 →
          ∀ {ε : ℝ} {n : ℕ}, |ε| ≤ εbar →
            Tmin ≤ (n : ℝ) * |ε| → (n : ℝ) * |ε| ≤ Tmax →
            squaredEuclideanNorm
                ((leapfrogN gradient ε n (q₁ 0, p₁ 0)).1 -
                  (leapfrogN gradient ε n (q₂ 0, p₂ 0)).1) ≤
              ((exactRate + errorRate : NNReal) : ℝ) ^ 2 *
                squaredEuclideanNorm (q₁ 0 - q₂ 0)) ∧
        (∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
          IsHamiltonianCurve gradient q₁ p₁ →
          IsHamiltonianCurve gradient q₂ p₂ →
          q₁ 0 ∈ K → q₂ 0 ∈ K →
          euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
          euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
          p₁ 0 = p₂ 0 →
          ∀ {ε : ℝ} {n : ℕ}, |ε| ≤ εbar →
            (n : ℝ) * |ε| ≤ Tmax →
            squaredEuclideanNorm
                ((leapfrogN gradient ε n (q₁ 0, p₁ 0)).1 -
                  (leapfrogN gradient ε n (q₂ 0, p₂ 0)).1) ≤
              ((1 + errorRate : NNReal) : ℝ) ^ 2 *
                squaredEuclideanNorm (q₁ 0 - q₂ 0)) := by
  obtain ⟨_r, _hr, cert, hexactCert⟩ :=
    hconv.exists_uniform_exactFlow_contraction hreg hK hKS M₀
  obtain ⟨Tmax, hTmax, hTmaxCert, henvelope⟩ :=
    exists_pos_exactFlowUniformEuclidean_envelope
      (ι := ι) β gradient hK hKS M₀ cert.horizon_pos
  let θ : ℝ := (1 - cert.delta) ^ 2
  let c : ℝ := cert.kappa * θ
  have hθ : 0 < θ := sq_pos_of_pos (sub_pos.mpr cert.delta_lt_one)
  have hc : 0 < c := mul_pos cert.kappa_pos hθ
  let Tmin : ℝ := min (Tmax / 8) (1 / (c + 1))
  have hTmin : 0 < Tmin := by
    dsimp [Tmin]
    exact lt_min (div_pos hTmax (by norm_num))
      (div_pos zero_lt_one (by linarith))
  have hTminTmax : 4 * Tmin < Tmax := by
    have hmin : Tmin ≤ Tmax / 8 := min_le_left _ _
    linarith
  have hTminBound : Tmin ≤ 1 / (c + 1) := min_le_right _ _
  have hlossOne : cert.kappa * θ * Tmin ^ 2 ≤ 1 := by
    have hc0 : 0 ≤ c := hc.le
    have hden : 0 < c + 1 := by linarith
    have hsq : Tmin ^ 2 ≤ (1 / (c + 1)) ^ 2 :=
      (sq_le_sq₀ hTmin.le (div_nonneg zero_le_one hden.le)).mpr hTminBound
    have hmul := mul_le_mul_of_nonneg_left hsq hc0
    have hcFrac : c * (1 / (c + 1)) ^ 2 ≤ 1 := by
      field_simp
      nlinarith [sq_nonneg c]
    change c * Tmin ^ 2 ≤ 1
    exact hmul.trans hcFrac
  obtain ⟨exactRate, errorCap, herrorCap, hexactWindow, hsumCap⟩ :=
    exists_nnreal_exactRate_errorRate_sq_lt_one_on_window
      cert.kappa_pos hθ hTmin hlossOne
  let η : ℝ := (4 * Real.exp 2)⁻¹
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨errorRateReal, herrorRateReal, herrorRateLe,
      hsum, hweighted⟩ :=
    exists_pos_errorRate_twoRate_weighted_lt_one
      exactRate.coe_nonneg (by exact_mod_cast herrorCap) hsumCap hη
  let errorRate : NNReal := ⟨errorRateReal, herrorRateReal.le⟩
  have herrorRate : 0 < errorRate := by
    exact_mod_cast herrorRateReal
  have hexactRate : 0 ≤ (exactRate : ℝ) := exactRate.coe_nonneg
  obtain ⟨εbar, hεbar, hpaired⟩ :=
    hreg.exists_uniform_leapfrogN_pairedPhaseError_le_mul
      hK hScompact hSconvex hM₀ hTmax.le herrorRateReal henvelope
  refine ⟨Tmin, hTmin, Tmax, hTminTmax, εbar, hεbar,
    exactRate, errorRate, herrorRate, hsum, ?_, ?_, ?_⟩
  · change (1 + errorRateReal) ^ 2 -
      (4 * Real.exp 2)⁻¹ *
        ((1 + errorRateReal) ^ 2 -
          ((exactRate : ℝ) + errorRateReal) ^ 2) < 1
    exact hweighted
  · intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
      hmomentum ε n hε hlower horizon
    have hambient : ∀ z : PhaseSpace ι, ‖z‖ ≤ euclideanPhaseSize z := by
      intro z
      rw [Prod.norm_def]
      apply max_le
      · exact (show ‖z.1‖ ≤ euclideanNorm z.1 by
          simpa only [dist_zero_right, sub_zero] using
            dist_le_euclideanNorm_sub z.1 0) |>.trans
          (euclideanNorm_fst_le_phaseSize z)
      · have hp : ‖z.2‖ ≤ euclideanNorm z.2 := by
          simpa only [dist_zero_right, sub_zero] using
            dist_le_euclideanNorm_sub z.2 0
        unfold euclideanPhaseSize
        exact hp.trans (le_add_of_nonneg_left (euclideanNorm_nonneg _))
    have htCert : |(n : ℝ) * ε| ≤ cert.horizon := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      exact horizon.trans hTmaxCert
    have hraw := hexactCert q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂
      ((hambient _).trans hz₁) ((hambient _).trans hz₂)
      hmomentum ((n : ℝ) * ε) htCert
    have hfactor := hexactWindow ((n : ℝ) * |ε|) hlower
    have hexact : squaredEuclideanNorm
        ((exactGridPhase q₁ p₁ ε n).1 -
          (exactGridPhase q₂ p₂ ε n).1) ≤
      (exactRate : ℝ) ^ 2 * squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
      apply hraw.trans
      have hmul := mul_le_mul_of_nonneg_right hfactor
        (squaredEuclideanNorm_nonneg (q₁ 0 - q₂ 0))
      change (1 - cert.kappa * (1 - cert.delta) ^ 2 *
          ((n : ℝ) * ε) ^ 2) * squaredEuclideanNorm (q₁ 0 - q₂ 0) ≤ _
      have hsquare : ((n : ℝ) * ε) ^ 2 = ((n : ℝ) * |ε|) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]
      rw [hsquare]
      simpa only [θ] using hmul
    exact squaredEuclideanNorm_leapfrogN_le_of_exactGrid_and_pairedError
      hexactRate herrorRateReal.le hexact
      (hpaired hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum hε horizon)
  · intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
      hmomentum ε n hε horizon
    have hambient : ∀ z : PhaseSpace ι, ‖z‖ ≤ euclideanPhaseSize z := by
      intro z
      rw [Prod.norm_def]
      apply max_le
      · exact (show ‖z.1‖ ≤ euclideanNorm z.1 by
          simpa only [dist_zero_right, sub_zero] using
            dist_le_euclideanNorm_sub z.1 0) |>.trans
          (euclideanNorm_fst_le_phaseSize z)
      · have hp : ‖z.2‖ ≤ euclideanNorm z.2 := by
          simpa only [dist_zero_right, sub_zero] using
            dist_le_euclideanNorm_sub z.2 0
        unfold euclideanPhaseSize
        exact hp.trans (le_add_of_nonneg_left (euclideanNorm_nonneg _))
    have htCert : |(n : ℝ) * ε| ≤ cert.horizon := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      exact horizon.trans hTmaxCert
    have hraw := hexactCert q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂
      ((hambient _).trans hz₁) ((hambient _).trans hz₂)
      hmomentum ((n : ℝ) * ε) htCert
    have hexact : squaredEuclideanNorm
          ((exactGridPhase q₁ p₁ ε n).1 -
            (exactGridPhase q₂ p₂ ε n).1) ≤
        (1 : ℝ) ^ 2 * squaredEuclideanNorm (q₁ 0 - q₂ 0) := by
      apply hraw.trans
      have hnonneg : 0 ≤ cert.kappa * (1 - cert.delta) ^ 2 *
          ((n : ℝ) * ε) ^ 2 := by positivity
      have hcoeff : 1 - cert.kappa * (1 - cert.delta) ^ 2 *
          ((n : ℝ) * ε) ^ 2 ≤ 1 := by linarith
      have := mul_le_mul_of_nonneg_right hcoeff
        (squaredEuclideanNorm_nonneg (q₁ 0 - q₂ 0))
      simpa only [one_pow, one_mul] using this
    change squaredEuclideanNorm
        ((leapfrogN gradient ε n (q₁ 0, p₁ 0)).1 -
          (leapfrogN gradient ε n (q₂ 0, p₂ 0)).1) ≤
      (1 + errorRateReal) ^ 2 *
        squaredEuclideanNorm (q₁ 0 - q₂ 0)
    exact squaredEuclideanNorm_leapfrogN_le_of_exactGrid_and_pairedError
        (by norm_num : (0 : ℝ) ≤ 1) herrorRateReal.le hexact
        (hpaired hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum hε horizon)

/-- The compact positive-window contraction theorem also controls arbitrary
signed trajectory offsets.  Negative offsets are ordinary leapfrog iterates
with step size `-ε`, so the same absolute-step-size threshold and rate apply. -/
theorem LocalStrongConvexity.exists_uniform_signedLeapfrog_contraction_on_window
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∃ Tmin > 0, ∃ Tmax > 4 * Tmin, ∃ εbar > 0,
      ∃ exactRate errorRate : NNReal,
        0 < errorRate ∧
        ((exactRate + errorRate : NNReal) : ℝ) ^ 2 < 1 ∧
        ((1 + errorRate : NNReal) : ℝ) ^ 2 -
            (4 * Real.exp 2)⁻¹ *
              (((1 + errorRate : NNReal) : ℝ) ^ 2 -
                ((exactRate + errorRate : NNReal) : ℝ) ^ 2) < 1 ∧
        (∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
          IsHamiltonianCurve gradient q₁ p₁ →
          IsHamiltonianCurve gradient q₂ p₂ →
          q₁ 0 ∈ K → q₂ 0 ∈ K →
          euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
          euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
          p₁ 0 = p₂ 0 →
          ∀ {ε : ℝ} {k : ℤ}, |ε| ≤ εbar →
            Tmin ≤ (Int.natAbs k : ℝ) * |ε| →
            (Int.natAbs k : ℝ) * |ε| ≤ Tmax →
            squaredEuclideanNorm
                ((signedLeapfrog gradient ε k (q₁ 0, p₁ 0)).1 -
                  (signedLeapfrog gradient ε k (q₂ 0, p₂ 0)).1) ≤
              ((exactRate + errorRate : NNReal) : ℝ) ^ 2 *
                squaredEuclideanNorm (q₁ 0 - q₂ 0)) ∧
        (∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
          IsHamiltonianCurve gradient q₁ p₁ →
          IsHamiltonianCurve gradient q₂ p₂ →
          q₁ 0 ∈ K → q₂ 0 ∈ K →
          euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
          euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
          p₁ 0 = p₂ 0 →
          ∀ {ε : ℝ} {k : ℤ}, |ε| ≤ εbar →
            (Int.natAbs k : ℝ) * |ε| ≤ Tmax →
            squaredEuclideanNorm
                ((signedLeapfrog gradient ε k (q₁ 0, p₁ 0)).1 -
                  (signedLeapfrog gradient ε k (q₂ 0, p₂ 0)).1) ≤
              ((1 + errorRate : NNReal) : ℝ) ^ 2 *
                squaredEuclideanNorm (q₁ 0 - q₂ 0)) := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
      exactRate, errorRate, herrorRate, hrate, hweighted, hcontract⟩ :=
    hconv.exists_uniform_leapfrogN_contraction_on_window
      hreg hK hKS hScompact hSconvex hM₀
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
    exactRate, errorRate, herrorRate, hrate, hweighted, ?_, ?_⟩
  · intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
      hmomentum ε k hε hlower hupper
    cases k with
    | ofNat n =>
        change squaredEuclideanNorm
            ((((leapfrogPerm gradient ε) ^ n) (q₁ 0, p₁ 0)).1 -
              (((leapfrogPerm gradient ε) ^ n) (q₂ 0, p₂ 0)).1) ≤ _
        simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm, leapfrogN] using
          hcontract.1 hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum
            (ε := ε) (n := n) hε hlower hupper
    | negSucc n =>
        have hεneg : |-ε| ≤ εbar := by simpa only [abs_neg] using hε
        have hlower' : Tmin ≤ ((n + 1 : ℕ) : ℝ) * |-ε| := by
          simpa only [Int.natAbs_negSucc, abs_neg] using hlower
        have hupper' : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ Tmax := by
          simpa only [Int.natAbs_negSucc, abs_neg] using hupper
        change squaredEuclideanNorm
            (((((leapfrogPerm gradient ε) ^ (n + 1))⁻¹)
                (q₁ 0, p₁ 0)).1 -
              ((((leapfrogPerm gradient ε) ^ (n + 1))⁻¹)
                (q₂ 0, p₂ 0)).1) ≤ _
        rw [← inv_pow]
        simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm_inv, leapfrogN] using
          hcontract.1 hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum
            (ε := -ε) (n := n + 1) hεneg hlower' hupper'
  · intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
      hmomentum ε k hε hupper
    cases k with
    | ofNat n =>
        change squaredEuclideanNorm
            ((((leapfrogPerm gradient ε) ^ n) (q₁ 0, p₁ 0)).1 -
              (((leapfrogPerm gradient ε) ^ n) (q₂ 0, p₂ 0)).1) ≤ _
        simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm, leapfrogN] using
          hcontract.2 hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum
            (ε := ε) (n := n) hε hupper
    | negSucc n =>
        have hεneg : |-ε| ≤ εbar := by simpa only [abs_neg] using hε
        have hupper' : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ Tmax := by
          simpa only [Int.natAbs_negSucc, abs_neg] using hupper
        change squaredEuclideanNorm
            (((((leapfrogPerm gradient ε) ^ (n + 1))⁻¹)
                (q₁ 0, p₁ 0)).1 -
              ((((leapfrogPerm gradient ε) ^ (n + 1))⁻¹)
                (q₂ 0, p₂ 0)).1) ≤ _
        rw [← inv_pow]
        simpa only [Equiv.Perm.coe_pow, coe_leapfrogPerm_inv, leapfrogN] using
          hcontract.2 hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum
            (ε := -ε) (n := n + 1) hεneg hupper'

/-- An endpoint-band index on the longer side of an arbitrary randomized
trajectory split.  Its parameter ranges over `L / 4 + 1` indices. -/
def trajectoryInteriorBandIndex
    (L : ℕ) (origin : Fin (L + 1)) (j : Fin (L / 4 + 1)) : Fin (L + 1) :=
  if origin.val ≤ L / 2 then
    ⟨L - j.val, by omega⟩
  else
    ⟨j.val, by omega⟩

theorem trajectoryInteriorBandIndex_injective
    (L : ℕ) (origin : Fin (L + 1)) :
    Function.Injective (trajectoryInteriorBandIndex L origin) := by
  intro i j hij
  unfold trajectoryInteriorBandIndex at hij
  split at hij
  · apply Fin.ext
    simp only [Fin.mk.injEq] at hij ⊢
    omega
  · exact Fin.ext (Fin.mk.inj_iff.mp hij)

/-- A canonical band containing a fixed fraction of the indices furthest
from the current-state origin. -/
def trajectoryInteriorIndexBand
    (L : ℕ) (origin : Fin (L + 1)) : Finset (Fin (L + 1)) :=
  Finset.univ.image (trajectoryInteriorBandIndex L origin)

theorem card_trajectoryInteriorIndexBand
    (L : ℕ) (origin : Fin (L + 1)) :
    (trajectoryInteriorIndexBand L origin).card = L / 4 + 1 := by
  unfold trajectoryInteriorIndexBand
  rw [Finset.card_image_of_injective _
    (trajectoryInteriorBandIndex_injective L origin)]
  simp

/-- Every band index is between one quarter and all of the total number of
steps away from the randomized origin. -/
theorem trajectoryInteriorIndexBand_offset_bounds
    {L : ℕ} (origin : Fin (L + 1)) {i : Fin (L + 1)}
    (hi : i ∈ trajectoryInteriorIndexBand L origin) :
    L ≤ 4 * Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ∧
      Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
  rw [trajectoryInteriorIndexBand, Finset.mem_image] at hi
  rcases hi with ⟨j, hj, rfl⟩
  unfold trajectoryInteriorBandIndex
  split <;> rename_i h
  · change L ≤ 4 * Int.natAbs
        (((L - j.val : ℕ) : ℤ) - (origin.val : ℤ)) ∧
      Int.natAbs (((L - j.val : ℕ) : ℤ) - (origin.val : ℤ)) ≤ L
    rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega)]
    omega
  · change L ≤ 4 * Int.natAbs
        ((j.val : ℤ) - (origin.val : ℤ)) ∧
      Int.natAbs ((j.val : ℤ) - (origin.val : ℤ)) ≤ L
    rw [Int.natAbs_natCast_sub_natCast_of_le (by omega)]
    omega

/-- The canonical endpoint band contains at least one quarter of all
trajectory indices. -/
theorem quarter_card_le_trajectoryInteriorIndexBand
    (L : ℕ) (origin : Fin (L + 1)) :
    L + 1 ≤ 4 * (trajectoryInteriorIndexBand L origin).card := by
  rw [card_trajectoryInteriorIndexBand]
  omega

/-- A total horizon in `[4*Tmin,Tmax]` puts every endpoint-band offset in the
positive contraction window `[Tmin,Tmax]`. -/
theorem trajectoryInteriorIndexBand_physicalTime_bounds
    {L : ℕ} (origin : Fin (L + 1)) {i : Fin (L + 1)}
    (hi : i ∈ trajectoryInteriorIndexBand L origin)
    {ε Tmin Tmax : ℝ} (hε0 : 0 ≤ ε)
    (hTmin : 4 * Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ Tmax) :
    Tmin ≤
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * ε ∧
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * ε ≤ Tmax := by
  rcases trajectoryInteriorIndexBand_offset_bounds origin hi with
    ⟨hlow, hhigh⟩
  have hlowR : (L : ℝ) ≤
      4 * (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) := by
    exact_mod_cast hlow
  have hhighR :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hhigh
  constructor
  · have := mul_le_mul_of_nonneg_right hlowR hε0
    nlinarith
  · exact (mul_le_mul_of_nonneg_right hhighR hε0).trans
      (by simpa only [mul_comm] using hTmax)

/-- A signed-leapfrog contraction on `[Tmin,Tmax]` applies to every aligned
index in the canonical endpoint band once the full trajectory horizon lies
in `[4*Tmin,Tmax]`. -/
theorem trajectorySquaredPositionCost_le_on_trajectoryInteriorIndexBand
    (gradient : Position ι → Position ι)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    {Tmin Tmax εbar : ℝ} {rate : NNReal}
    (hcontract : ∀ {ε : ℝ} {k : ℤ}, |ε| ≤ εbar →
      Tmin ≤ (Int.natAbs k : ℝ) * |ε| →
      (Int.natAbs k : ℝ) * |ε| ≤ Tmax →
      squaredEuclideanNorm
          ((signedLeapfrog gradient ε k (q₁ 0, p₁ 0)).1 -
            (signedLeapfrog gradient ε k (q₂ 0, p₂ 0)).1) ≤
        (rate : ℝ) * squaredEuclideanNorm (q₁ 0 - q₂ 0))
    {L : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hεbar : ε ≤ εbar)
    (hTmin : 4 * Tmin ≤ ε * (L : ℝ))
    (hTmax : ε * (L : ℝ) ≤ Tmax)
    (origin : Fin (L + 1)) {i : Fin (L + 1)}
    (hi : i ∈ trajectoryInteriorIndexBand L origin) :
    trajectorySquaredPositionCost gradient ε
        (((q₁ 0, p₁ 0), (q₂ 0, p₂ 0))) origin i i ≤
      rate * initialSquaredPositionDistance (q₁ 0) (q₂ 0) := by
  rcases trajectoryInteriorIndexBand_physicalTime_bounds origin hi hε0
    hTmin hTmax with ⟨hlower, hupper⟩
  have hεabs : |ε| ≤ εbar := by
    rw [abs_of_nonneg hε0]
    exact hεbar
  have hlower' : Tmin ≤
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| := by
    simpa only [abs_of_nonneg hε0] using hlower
  have hupper' :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ Tmax := by
    simpa only [abs_of_nonneg hε0] using hupper
  unfold trajectorySquaredPositionCost initialSquaredPositionDistance
    offsetLeapfrogTrajectory
  apply NNReal.coe_le_coe.mp
  change squaredEuclideanNorm
      ((signedLeapfrog gradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₁ 0, p₁ 0)).1 -
        (signedLeapfrog gradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₂ 0, p₂ 0)).1) ≤
    (rate : ℝ) * euclideanNorm (q₁ 0 - q₂ 0) ^ 2
  rw [euclideanNorm_sq]
  exact hcontract hεabs hlower' hupper'

/-- A whole-window signed-leapfrog separation bound controls every aligned
trajectory index, including the unchanged current-state index. -/
theorem trajectorySquaredPositionCost_le_of_signedLeapfrog_bound
    (gradient : Position ι → Position ι)
    {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι}
    {Tmax εbar : ℝ} {rate : NNReal}
    (hbound : ∀ {ε : ℝ} {k : ℤ}, |ε| ≤ εbar →
      (Int.natAbs k : ℝ) * |ε| ≤ Tmax →
      squaredEuclideanNorm
          ((signedLeapfrog gradient ε k (q₁ 0, p₁ 0)).1 -
            (signedLeapfrog gradient ε k (q₂ 0, p₂ 0)).1) ≤
        (rate : ℝ) * squaredEuclideanNorm (q₁ 0 - q₂ 0))
    {L : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hεbar : ε ≤ εbar)
    (hTmax : ε * (L : ℝ) ≤ Tmax)
    (origin i : Fin (L + 1)) :
    trajectorySquaredPositionCost gradient ε
        (((q₁ 0, p₁ 0), (q₂ 0, p₂ 0))) origin i i ≤
      rate * initialSquaredPositionDistance (q₁ 0) (q₂ 0) := by
  have hoffset : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
    by_cases hio : i.val ≤ origin.val
    · rw [Int.natAbs_natCast_sub_natCast_of_le hio]
      omega
    · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega)]
      omega
  have hoffsetR :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hoffset
  have htime :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ Tmax := by
    rw [abs_of_nonneg hε0]
    exact (mul_le_mul_of_nonneg_right hoffsetR hε0).trans
      (by simpa only [mul_comm] using hTmax)
  have hεabs : |ε| ≤ εbar := by
    simpa only [abs_of_nonneg hε0] using hεbar
  unfold trajectorySquaredPositionCost initialSquaredPositionDistance
    offsetLeapfrogTrajectory
  apply NNReal.coe_le_coe.mp
  change squaredEuclideanNorm
      ((signedLeapfrog gradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₁ 0, p₁ 0)).1 -
        (signedLeapfrog gradient ε
          ((i.val : ℤ) - (origin.val : ℤ)) (q₂ 0, p₂ 0)).1) ≤
    (rate : ℝ) * euclideanNorm (q₁ 0 - q₂ 0) ^ 2
  rw [euclideanNorm_sq]
  exact hbound hεabs htime

/-- Compact local strong convexity supplies a uniform subunit aligned-cost
rate on a fixed-fraction endpoint band for every randomized trajectory
origin.  The lower bound here is on the total integration horizon, while the
underlying endpoint theorem is applied to each signed offset in the band. -/
theorem LocalStrongConvexity.exists_uniform_trajectoryInteriorBand_contraction
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ alignedRate : NNReal, alignedRate < 1 ∧
        ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
          IsHamiltonianCurve gradient q₁ p₁ →
          IsHamiltonianCurve gradient q₂ p₂ →
          q₁ 0 ∈ K → q₂ 0 ∈ K →
          euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
          euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
          p₁ 0 = p₂ 0 →
          ∀ {ε : ℝ} {L : ℕ}, 0 ≤ ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ (origin : Fin (L + 1)) {i : Fin (L + 1)},
              i ∈ trajectoryInteriorIndexBand L origin →
              trajectorySquaredPositionCost gradient ε
                  (((q₁ 0, p₁ 0), (q₂ 0, p₂ 0))) origin i i ≤
                alignedRate *
                  initialSquaredPositionDistance (q₁ 0) (q₂ 0) := by
  obtain ⟨T₀, hT₀, Tmax, hTmax, εbar, hεbar,
      exactRate, errorRate, herrorRate, hrate, hsigned⟩ :=
    hconv.exists_uniform_signedLeapfrog_contraction_on_window
      hreg hK hKS hScompact hSconvex hM₀
  let Tmin := 4 * T₀
  let alignedRate : NNReal := (exactRate + errorRate) ^ 2
  have hTmin : 0 < Tmin := mul_pos (by norm_num) hT₀
  have hTminMax : Tmin < Tmax := by simpa only [Tmin] using hTmax
  have haligned : alignedRate < 1 := by
    apply NNReal.coe_lt_coe.mp
    simpa only [alignedRate, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one]
      using hrate
  refine ⟨Tmin, hTmin, Tmax, hTminMax, εbar, hεbar,
    alignedRate, haligned, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
    hmomentum ε L hε0 hεbar' hfullMin hfullMax origin i hi
  apply trajectorySquaredPositionCost_le_on_trajectoryInteriorIndexBand
    gradient (Tmin := T₀) (Tmax := Tmax) (εbar := εbar)
      (rate := alignedRate) ?_ hε0 hεbar' ?_ hfullMax origin hi
  · intro ε' k hε' hlower hupper
    simpa only [alignedRate, NNReal.coe_pow, NNReal.coe_add] using
      hsigned.2.1 hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum
        hε' hlower hupper
  · simpa only [Tmin] using hfullMin

/-- The compact theorem yields the two aligned rates needed by the weighted
band argument: a subunit rate on the endpoint band and a whole-trajectory
rate arbitrarily close to one as the selected relative numerical allowance
shrinks. -/
theorem LocalStrongConvexity.exists_uniform_trajectoryAlignedTwoRateBounds
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ bandRate globalRate : NNReal,
        bandRate < 1 ∧ bandRate ≤ globalRate ∧
        ((globalRate : ℝ) - (4 * Real.exp 2)⁻¹ *
          ((globalRate : ℝ) - (bandRate : ℝ)) < 1) ∧
        ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
          IsHamiltonianCurve gradient q₁ p₁ →
          IsHamiltonianCurve gradient q₂ p₂ →
          q₁ 0 ∈ K → q₂ 0 ∈ K →
          euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
          euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
          p₁ 0 = p₂ 0 →
          ∀ {ε : ℝ} {L : ℕ}, 0 ≤ ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ (origin : Fin (L + 1)),
              (∀ i, i ∈ trajectoryInteriorIndexBand L origin →
                trajectorySquaredPositionCost gradient ε
                    (((q₁ 0, p₁ 0), (q₂ 0, p₂ 0))) origin i i ≤
                  bandRate *
                    initialSquaredPositionDistance (q₁ 0) (q₂ 0)) ∧
              (∀ i, trajectorySquaredPositionCost gradient ε
                    (((q₁ 0, p₁ 0), (q₂ 0, p₂ 0))) origin i i ≤
                  globalRate *
                    initialSquaredPositionDistance (q₁ 0) (q₂ 0)) := by
  obtain ⟨T₀, hT₀, Tmax, hTmax, εbar, hεbar,
      exactRate, errorRate, herrorRate, hrate, hsigned⟩ :=
    hconv.exists_uniform_signedLeapfrog_contraction_on_window
      hreg hK hKS hScompact hSconvex hM₀
  let Tmin := 4 * T₀
  let bandRate : NNReal := (exactRate + errorRate) ^ 2
  let globalRate : NNReal := (1 + errorRate) ^ 2
  have hTmin : 0 < Tmin := mul_pos (by norm_num) hT₀
  have hTminMax : Tmin < Tmax := by simpa only [Tmin] using hTmax
  have hbandRate : bandRate < 1 := by
    apply NNReal.coe_lt_coe.mp
    simpa only [bandRate, NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one]
      using hrate
  have hexactLe : exactRate ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    have hsum0 : 0 ≤ ((exactRate + errorRate : NNReal) : ℝ) :=
      NNReal.coe_nonneg _
    have hsumlt : ((exactRate + errorRate : NNReal) : ℝ) < 1 := by
      nlinarith
    have hexactSum : (exactRate : ℝ) ≤
        ((exactRate + errorRate : NNReal) : ℝ) := by
      push_cast
      exact le_add_of_nonneg_right errorRate.coe_nonneg
    exact hexactSum.trans hsumlt.le
  have hbandGlobal : bandRate ≤ globalRate := by
    dsimp [bandRate, globalRate]
    gcongr
  refine ⟨Tmin, hTmin, Tmax, hTminMax, εbar, hεbar,
    bandRate, globalRate, hbandRate, hbandGlobal, ?_, ?_⟩
  · simpa only [bandRate, globalRate, NNReal.coe_pow, NNReal.coe_add,
      NNReal.coe_one] using hsigned.1
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
    hmomentum ε L hε0 hεbar' hfullMin hfullMax origin
  constructor
  · intro i hi
    apply trajectorySquaredPositionCost_le_on_trajectoryInteriorIndexBand
      gradient (Tmin := T₀) (Tmax := Tmax) (εbar := εbar)
        (rate := bandRate) ?_ hε0 hεbar' ?_ hfullMax origin hi
    · intro ε' k hε' hlower hupper
      simpa only [bandRate, NNReal.coe_pow, NNReal.coe_add] using
        hsigned.2.1 hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum
          hε' hlower hupper
    · simpa only [Tmin] using hfullMin
  · intro i
    apply trajectorySquaredPositionCost_le_of_signedLeapfrog_bound
      gradient (Tmax := Tmax) (εbar := εbar) (rate := globalRate)
        ?_ hε0 hεbar' hfullMax origin i
    intro ε' k hε' hupper
    simpa only [globalRate, NNReal.coe_pow, NNReal.coe_add,
      NNReal.coe_one] using
      hsigned.2.2 hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂ hmomentum
        hε' hupper

/-- Centered energy control gives the canonical endpoint band an overlap-mass
floor independent of the trajectory length and randomized origin. -/
theorem trajectoryInteriorIndexBand_overlapMass_ge
    (potential : Position ι → ℝ) {L : ℕ}
    (trajectory₁ trajectory₂ : Fin (L + 1) → PhaseSpace ι)
    (center₁ center₂ δ : ℝ)
    (henergy₁ : ∀ i,
      |energy potential (trajectory₁ i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy potential (trajectory₂ i) - center₂| ≤ δ)
    (origin : Fin (L + 1)) :
    ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹) ≤
      ∑ i ∈ trajectoryInteriorIndexBand L origin,
        min (trajectoryIndexPMF potential trajectory₁ i)
          (trajectoryIndexPMF potential trajectory₂ i) := by
  have hband := trajectoryIndexPMF_overlap_bandMass_ge_of_centered_energy
    potential trajectory₁ trajectory₂ center₁ center₂ δ
      henergy₁ henergy₂ (trajectoryInteriorIndexBand L origin)
  apply le_trans ?_ hband
  rw [← ENNReal.ofReal_natCast
      (trajectoryInteriorIndexBand L origin).card,
    ← ENNReal.ofReal_natCast (L + 1),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg (L + 1)),
    ← ENNReal.ofReal_inv_of_pos
      (x := (((L + 1 : ℕ) : ℝ) * Real.exp (2 * δ)))
      (mul_pos (by positivity) (Real.exp_pos _)),
    ← ENNReal.ofReal_mul
      (Nat.cast_nonneg (trajectoryInteriorIndexBand L origin).card)]
  apply ENNReal.ofReal_le_ofReal
  have hcard := quarter_card_le_trajectoryInteriorIndexBand L origin
  have hexp : 0 < Real.exp (2 * δ) := Real.exp_pos _
  field_simp
  exact_mod_cast hcard

/-- Two deterministic trajectory-cost rates lift to an overlap-weighted
aligned-cost estimate.  The global rate is `σ`; the endpoint band has the
better rate `ρ`; centered energy control supplies a uniform amount of overlap
on that band and hence an explicit loss from the global budget. -/
theorem trajectoryIndexPMF_alignedSquaredCost_add_bandLoss_le
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    {L : ℕ} (ε : ℝ) (origin : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι)
    (center₁ center₂ δ : ℝ) (ρ σ : ENNReal)
    (henergy₁ : ∀ i,
      |energy potential
        (offsetLeapfrogTrajectory gradient ε origin (q₁, p) i) - center₁| ≤ δ)
    (henergy₂ : ∀ i,
      |energy potential
        (offsetLeapfrogTrajectory gradient ε origin (q₂, p) i) - center₂| ≤ δ)
    (hglobal : ∀ i,
      (trajectorySquaredPositionCost gradient ε
        (((q₁, p), (q₂, p))) origin i i : ENNReal) ≤
          σ * (initialSquaredPositionDistance q₁ q₂ : ENNReal))
    (hband : ∀ i, i ∈ trajectoryInteriorIndexBand L origin →
      (trajectorySquaredPositionCost gradient ε
        (((q₁, p), (q₂, p))) origin i i : ENNReal) ≤
          ρ * (initialSquaredPositionDistance q₁ q₂ : ENNReal))
    (hρσ : ρ ≤ σ) :
    (∑ i, min
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
        (trajectorySquaredPositionCost gradient ε
          (((q₁, p), (q₂, p))) origin i i : ENNReal)) +
      (ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹) * (σ - ρ)) *
        (initialSquaredPositionDistance q₁ q₂ : ENNReal) ≤
      σ * (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
  classical
  let trajectory₁ := offsetLeapfrogTrajectory gradient ε origin (q₁, p)
  let trajectory₂ := offsetLeapfrogTrajectory gradient ε origin (q₂, p)
  let weight : Fin (L + 1) → ENNReal := fun i =>
    min (trajectoryIndexPMF potential trajectory₁ i)
      (trajectoryIndexPMF potential trajectory₂ i)
  let cost : Fin (L + 1) → ENNReal := fun i =>
    (trajectorySquaredPositionCost gradient ε
      (((q₁, p), (q₂, p))) origin i i : ENNReal)
  let band := trajectoryInteriorIndexBand L origin
  let loss := ENNReal.ofReal ((4 * Real.exp (2 * δ))⁻¹) * (σ - ρ)
  apply McmcLean.Finite.weightedCost_add_bandLoss_le
    weight cost (fun i => i ∈ band) ρ σ loss
      (initialSquaredPositionDistance q₁ q₂ : ENNReal)
  · dsimp [weight]
    calc
      (∑ i, min (trajectoryIndexPMF potential trajectory₁ i)
          (trajectoryIndexPMF potential trajectory₂ i)) ≤
          ∑ i, trajectoryIndexPMF potential trajectory₁ i :=
        Finset.sum_le_sum fun i hi => min_le_left _ _
      _ = 1 := by
        rw [show ∑ i, trajectoryIndexPMF potential trajectory₁ i =
            ∑' i, trajectoryIndexPMF potential trajectory₁ i by
              rw [tsum_fintype], PMF.tsum_coe]
  · exact hglobal
  · intro i hi
    exact hband i hi
  · exact hρσ
  · have hmass := trajectoryInteriorIndexBand_overlapMass_ge
      potential trajectory₁ trajectory₂ center₁ center₂ δ
        henergy₁ henergy₂ origin
    have hmul := mul_le_mul_left hmass (σ - ρ)
    dsimp [loss, weight, band]
    apply le_trans (by simpa only [mul_comm] using hmul)
    rw [Finset.mul_sum]
    calc
      (∑ i ∈ trajectoryInteriorIndexBand L origin,
          (σ - ρ) * weight i) =
          ∑ i, if i ∈ trajectoryInteriorIndexBand L origin then
            weight i * (σ - ρ) else 0 := by
        rw [← Finset.sum_filter]
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        simp only [mul_comm]
      _ ≤ _ := le_rfl

/-- The fixed overlap floor used after restricting centered energy defects to
radius one. -/
noncomputable def compactTrajectoryOverlapFloor : NNReal :=
  ⟨(4 * Real.exp 2)⁻¹, by positivity⟩

theorem compactTrajectoryOverlapFloor_pos :
    0 < compactTrajectoryOverlapFloor := by
  apply NNReal.coe_pos.mp
  change 0 < (4 * Real.exp 2)⁻¹
  positivity

theorem compactTrajectoryOverlapFloor_le_one :
    compactTrajectoryOverlapFloor ≤ 1 := by
  apply NNReal.coe_le_coe.mp
  change (4 * Real.exp 2)⁻¹ ≤ (1 : ℝ)
  apply (inv_le_one₀ (by positivity)).2
  have hexp : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  nlinarith

/-- The aligned rate obtained by subtracting the guaranteed endpoint-band
gain from the whole-trajectory rate. -/
noncomputable def compactTrajectoryAlignedRate
    (bandRate globalRate : NNReal) : NNReal :=
  globalRate - compactTrajectoryOverlapFloor * (globalRate - bandRate)

theorem compactTrajectoryAlignedRate_lt_one
    {bandRate globalRate : NNReal} (hbandGlobal : bandRate ≤ globalRate)
    (hweighted : ((globalRate : ℝ) -
      (compactTrajectoryOverlapFloor : ℝ) *
        ((globalRate : ℝ) - (bandRate : ℝ))) < 1) :
    compactTrajectoryAlignedRate bandRate globalRate < 1 := by
  have hloss : compactTrajectoryOverlapFloor * (globalRate - bandRate) ≤
      globalRate := by
    calc
      compactTrajectoryOverlapFloor * (globalRate - bandRate) ≤
          1 * (globalRate - bandRate) :=
        mul_le_mul_of_nonneg_right compactTrajectoryOverlapFloor_le_one
          bot_le
      _ = globalRate - bandRate := one_mul _
      _ ≤ globalRate := tsub_le_self
  apply NNReal.coe_lt_coe.mp
  rw [compactTrajectoryAlignedRate, NNReal.coe_sub hloss,
    NNReal.coe_mul, NNReal.coe_sub hbandGlobal]
  exact hweighted

/-- The explicit two-rate estimate gives the sharp overlap-weighted aligned
budget at `compactTrajectoryAlignedRate`. -/
theorem trajectoryIndexPMF_alignedSquaredCost_le_compactRate
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    {L : ℕ} (ε : ℝ) (origin : Fin (L + 1))
    (q₁ q₂ : Position ι) (p : Momentum ι)
    (center₁ center₂ : ℝ) (bandRate globalRate : NNReal)
    (henergy₁ : ∀ i,
      |energy potential
        (offsetLeapfrogTrajectory gradient ε origin (q₁, p) i) - center₁| ≤ 1)
    (henergy₂ : ∀ i,
      |energy potential
        (offsetLeapfrogTrajectory gradient ε origin (q₂, p) i) - center₂| ≤ 1)
    (hglobal : ∀ i,
      trajectorySquaredPositionCost gradient ε
          (((q₁, p), (q₂, p))) origin i i ≤
        globalRate * initialSquaredPositionDistance q₁ q₂)
    (hband : ∀ i, i ∈ trajectoryInteriorIndexBand L origin →
      trajectorySquaredPositionCost gradient ε
          (((q₁, p), (q₂, p))) origin i i ≤
        bandRate * initialSquaredPositionDistance q₁ q₂)
    (hbandGlobal : bandRate ≤ globalRate) :
    (∑ i, min
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
        (trajectorySquaredPositionCost gradient ε
          (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
      (compactTrajectoryAlignedRate bandRate globalRate : ENNReal) *
        (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
  have hadd := trajectoryIndexPMF_alignedSquaredCost_add_bandLoss_le
    potential gradient ε origin q₁ q₂ p center₁ center₂ 1
      (bandRate : ENNReal) (globalRate : ENNReal)
      henergy₁ henergy₂ (fun i => by exact_mod_cast hglobal i)
      (fun i hi => by exact_mod_cast hband i hi) (by exact_mod_cast hbandGlobal)
  let loss : NNReal :=
    compactTrajectoryOverlapFloor * (globalRate - bandRate)
  have hloss : loss ≤ globalRate := by
    dsimp [loss]
    calc
      compactTrajectoryOverlapFloor * (globalRate - bandRate) ≤
          1 * (globalRate - bandRate) :=
        mul_le_mul_of_nonneg_right compactTrajectoryOverlapFloor_le_one
          bot_le
      _ ≤ globalRate := by simp only [one_mul]; exact tsub_le_self
  have hlossTop :
      (loss : ENNReal) *
      (initialSquaredPositionDistance q₁ q₂ : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hlossCoe : (loss : ENNReal) =
      ENNReal.ofReal ((4 * Real.exp 2)⁻¹) *
        ((globalRate : ENNReal) - (bandRate : ENNReal)) := by
    dsimp [loss]
    rw [ENNReal.coe_sub, ENNReal.coe_nnreal_eq]
    rfl
  have hadd' :
      (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
          (trajectorySquaredPositionCost gradient ε
            (((q₁, p), (q₂, p))) origin i i : ENNReal)) +
        (loss : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) ≤
        (globalRate : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
    rw [hlossCoe]
    simpa only [mul_one] using hadd
  apply (ENNReal.add_le_add_iff_right hlossTop).mp
  have hrates : compactTrajectoryAlignedRate bandRate globalRate + loss =
      globalRate := by
    dsimp [compactTrajectoryAlignedRate, loss]
    exact tsub_add_cancel_of_le hloss
  calc
    (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
          (trajectorySquaredPositionCost gradient ε
            (((q₁, p), (q₂, p))) origin i i : ENNReal)) +
        (loss : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) ≤
      (globalRate : ENNReal) *
        (initialSquaredPositionDistance q₁ q₂ : ENNReal) := hadd'
    _ = ((compactTrajectoryAlignedRate bandRate globalRate : ENNReal) +
          (loss : ENNReal)) *
        (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
      rw [← ENNReal.coe_add, hrates]
    _ = (compactTrajectoryAlignedRate bandRate globalRate : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) +
        (loss : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) := add_mul _ _ _

/-- Compact local strong convexity now closes the full overlap-weighted
aligned part of the repaired exponent-two multinomial budget.  The theorem
simultaneously selects the numerical threshold needed for contraction and for
unit centered-energy error, so its aligned rate is uniformly below one over
all trajectory lengths, origins, and bounded shared momenta in the compact
core. -/
theorem LocalStrongConvexity.exists_uniform_overlapWeightedAlignedContraction
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ alignedRate : NNReal, alignedRate < 1 ∧
        ∀ {q₁ q₂ : ℝ → Position ι} {p₁ p₂ : ℝ → Momentum ι},
          IsHamiltonianCurve gradient q₁ p₁ →
          IsHamiltonianCurve gradient q₂ p₂ →
          q₁ 0 ∈ K → q₂ 0 ∈ K →
          euclideanPhaseSize (q₁ 0, p₁ 0) ≤ M₀ →
          euclideanPhaseSize (q₂ 0, p₂ 0) ≤ M₀ →
          p₁ 0 = p₂ 0 →
          ∀ {ε : ℝ} {L : ℕ}, 0 ≤ ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ (origin : Fin (L + 1)),
              (∑ i, min
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin
                      (q₁ 0, p₁ 0)) i)
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin
                      (q₂ 0, p₂ 0)) i) *
                  (trajectorySquaredPositionCost gradient ε
                    (((q₁ 0, p₁ 0), (q₂ 0, p₂ 0))) origin i i : ENNReal)) ≤
                (alignedRate : ENNReal) *
                  (initialSquaredPositionDistance (q₁ 0) (q₂ 0) : ENNReal) := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar₀, hεbar₀,
      bandRate, globalRate, hbandRate, hbandGlobal, hweighted, hbounds⟩ :=
    hconv.exists_uniform_trajectoryAlignedTwoRateBounds
      hreg hK hKS hScompact hSconvex hM₀
  obtain ⟨C, hC, henergy⟩ :=
    abs_energy_signedLeapfrog_sub_le_of_horizon hreg
      hreg.locallyUniformQuadraticLeapfrogEnergyError (R := M₀) (T := Tmax)
  have hTmax0 : 0 < Tmax := hTmin.trans hTmax
  let energyStep : ℝ := (C * Tmax + 1)⁻¹
  have hden : 0 < C * Tmax + 1 := by
    have : 0 ≤ C * Tmax := mul_nonneg hC hTmax0.le
    linarith
  have henergyStep : 0 < energyStep := inv_pos.mpr hden
  let εbar := min εbar₀ (min 1 energyStep)
  have hεbar : 0 < εbar := by
    dsimp [εbar]
    exact lt_min hεbar₀ (lt_min zero_lt_one henergyStep)
  let alignedRate := compactTrajectoryAlignedRate bandRate globalRate
  have haligned : alignedRate < 1 := by
    apply compactTrajectoryAlignedRate_lt_one hbandGlobal
    change (globalRate : ℝ) - (4 * Real.exp 2)⁻¹ *
      ((globalRate : ℝ) - (bandRate : ℝ)) < 1
    exact hweighted
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
    alignedRate, haligned, ?_⟩
  intro q₁ q₂ p₁ p₂ hcurve₁ hcurve₂ hq₁ hq₂ hz₁ hz₂
    hmomentum ε L hε0 hεbar' hfullMin hfullMax origin
  have hεbar₀' : ε ≤ εbar₀ :=
    hεbar'.trans (min_le_left _ _)
  have hεone : |ε| ≤ 1 := by
    rw [abs_of_nonneg hε0]
    exact hεbar'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεenergy : ε ≤ energyStep :=
    hεbar'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have henergyBudget : C * Tmax * |ε| ≤ 1 := by
    rw [abs_of_nonneg hε0]
    have hCT : 0 ≤ C * Tmax := mul_nonneg hC hTmax0.le
    have hmul := mul_le_mul_of_nonneg_left hεenergy hCT
    apply hmul.trans
    dsimp [energyStep]
    rw [inv_eq_one_div]
    field_simp
    nlinarith
  obtain ⟨hband, hglobal⟩ := hbounds hcurve₁ hcurve₂ hq₁ hq₂
    hz₁ hz₂ hmomentum hε0 hεbar₀' hfullMin hfullMax origin
  have hoffsetTime : ∀ i : Fin (L + 1),
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ Tmax := by
    intro i
    have hoffset : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
      omega
    have hoffsetR :
        (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
      exact_mod_cast hoffset
    rw [abs_of_nonneg hε0]
    exact (mul_le_mul_of_nonneg_right hoffsetR hε0).trans
      (by simpa only [mul_comm] using hfullMax)
  have henergy₁ : ∀ i,
      |energy potential
        (offsetLeapfrogTrajectory gradient ε origin (q₁ 0, p₁ 0) i) -
          energy potential (q₁ 0, p₁ 0)| ≤ 1 := by
    intro i
    apply (henergy hεone
      ((i.val : ℤ) - (origin.val : ℤ)) (hoffsetTime i)
      (q₁ 0, p₁ 0) hz₁).trans
    exact henergyBudget
  have henergy₂ : ∀ i,
      |energy potential
        (offsetLeapfrogTrajectory gradient ε origin (q₂ 0, p₂ 0) i) -
          energy potential (q₂ 0, p₂ 0)| ≤ 1 := by
    intro i
    apply (henergy hεone
      ((i.val : ℤ) - (origin.val : ℤ)) (hoffsetTime i)
      (q₂ 0, p₂ 0) hz₂).trans
    exact henergyBudget
  simpa only [hmomentum, alignedRate] using
    trajectoryIndexPMF_alignedSquaredCost_le_compactRate
      potential gradient ε origin (q₁ 0) (q₂ 0) (p₁ 0)
        (energy potential (q₁ 0, p₁ 0))
        (energy potential (q₂ 0, p₁ 0)) bandRate globalRate
        henergy₁ (by simpa only [hmomentum] using henergy₂)
        (fun i => by simpa only [hmomentum] using hglobal i)
        (fun i hi => by simpa only [hmomentum] using hband i hi)
        hbandGlobal

/-- Initial-state form of the compact overlap-weighted contraction theorem.
Global exact Hamiltonian curves are constructed from `RegularPotential`, so
callers no longer need to supply classical trajectories as an assumption. -/
theorem LocalStrongConvexity.exists_uniform_overlapWeightedAlignedContraction_of_initial
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {M₀ : ℝ} (hM₀ : 0 ≤ M₀) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ alignedRate : NNReal, alignedRate < 1 ∧
        ∀ q₁ q₂ : Position ι, ∀ p : Momentum ι,
          q₁ ∈ K → q₂ ∈ K →
          euclideanPhaseSize (q₁, p) ≤ M₀ →
          euclideanPhaseSize (q₂, p) ≤ M₀ →
          ∀ {ε : ℝ} {L : ℕ}, 0 ≤ ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ (origin : Fin (L + 1)),
              (∑ i, min
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                  (trajectorySquaredPositionCost gradient ε
                    (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                (alignedRate : ENNReal) *
                  (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
      alignedRate, haligned, hbound⟩ :=
    hconv.exists_uniform_overlapWeightedAlignedContraction
      hreg hK hKS hScompact hSconvex hM₀
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
    alignedRate, haligned, ?_⟩
  intro q₁ q₂ p hq₁ hq₂ hz₁ hz₂ ε L hε0 hεbar' hTmin' hTmax' origin
  obtain ⟨qcurve₁, pcurve₁, hqcurve₁, hpcurve₁, hcurve₁⟩ :=
    hreg.exists_hamiltonianCurve q₁ p
  obtain ⟨qcurve₂, pcurve₂, hqcurve₂, hpcurve₂, hcurve₂⟩ :=
    hreg.exists_hamiltonianCurve q₂ p
  simpa only [hqcurve₁, hpcurve₁, hqcurve₂, hpcurve₂] using
    hbound hcurve₁ hcurve₂
      (by simpa only [hqcurve₁] using hq₁)
      (by simpa only [hqcurve₂] using hq₂)
      (by simpa only [hqcurve₁, hpcurve₁] using hz₁)
      (by simpa only [hqcurve₂, hpcurve₂] using hz₂)
      (by rw [hpcurve₁, hpcurve₂]) hε0 hεbar' hTmin' hTmax' origin

/-- Kinetic-cutoff form of the compact overlap-weighted contraction theorem.
Compactness bounds positions and the energy cutoff bounds the shared momentum,
so both the phase-size and global-curve premises are discharged internally. -/
theorem LocalStrongConvexity.exists_uniform_overlapWeightedAlignedContraction_of_kineticEnergy_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {k0 : ℝ} (hk0 : 0 ≤ k0) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ alignedRate : NNReal, alignedRate < 1 ∧
        ∀ q₁ q₂ : Position ι, ∀ p : Momentum ι,
          q₁ ∈ K → q₂ ∈ K → kineticEnergy p ≤ k0 →
          ∀ {ε : ℝ} {L : ℕ}, 0 ≤ ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ (origin : Fin (L + 1)),
              (∑ i, min
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                  (trajectorySquaredPositionCost gradient ε
                    (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                (alignedRate : ENNReal) *
                  (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
  obtain ⟨M₀, hM₀, hphase⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
      hK hk0
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
      alignedRate, haligned, hbound⟩ :=
    hconv.exists_uniform_overlapWeightedAlignedContraction_of_initial
      hreg hK hKS hScompact hSconvex hM₀.le
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
    alignedRate, haligned, ?_⟩
  intro q₁ q₂ p hq₁ hq₂ hp ε L hε0 hεbar' hTmin' hTmax' origin
  exact hbound q₁ q₂ p hq₁ hq₂ (hphase q₁ hq₁ p hp)
    (hphase q₂ hq₂ p hp) hε0 hεbar' hTmin' hTmax' origin

/-- Compact-uniform absolute mismatch budget. Under regularity, the product
of trajectory-index TV and one uniform cross-index squared-cost bound can be
made smaller than any prescribed positive constant. This is the quantitative
content supplied by Proposition 4.2; unlike Condition 1, its right-hand side
is not scaled by the current position separation. -/
theorem RegularPotential.exists_uniform_totalVariation_mul_squaredCost_lt
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T)
    {η : ENNReal} (hη : 0 < η) :
    ∃ εbar > 0, ∃ mismatchBound : NNReal,
      ∀ {ε : ℝ}, 0 < ε → ε < εbar →
        ∀ {L : ℕ}, ε * (L : ℝ) ≤ T →
          ∀ (origin : Fin (L + 1)), ∀ q₁ ∈ K, ∀ q₂ ∈ K,
            ∀ p : Momentum ι, kineticEnergy p ≤ k0 →
              (∀ i j, trajectorySquaredPositionCost gradient ε
                  (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
              McmcLean.Finite.totalVariation
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                  (mismatchBound : ENNReal) < η := by
  obtain ⟨M, hM, hphase⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
      hK hk0
  let R := Real.exp (leapfrogNormStabilityRate β * T) *
    (M + (2 + (β : ℝ)) * T * euclideanNorm (gradient 0))
  have hR : 0 < R := by
    dsimp [R]
    have hforcing : 0 ≤
        (2 + (β : ℝ)) * T * euclideanNorm (gradient 0) :=
      mul_nonneg (mul_nonneg (by positivity) hT) (euclideanNorm_nonneg _)
    exact mul_pos (Real.exp_pos _) (lt_of_lt_of_le hM (le_add_of_nonneg_right hforcing))
  let mismatchBound : NNReal :=
    ⟨4 * R ^ 2, (mul_pos (by norm_num) (sq_pos_of_pos hR)).le⟩
  have hboundPos : (0 : ENNReal) < (mismatchBound : ENNReal) := by
    rw [ENNReal.coe_pos]
    change (0 : ℝ) < 4 * R ^ 2
    positivity
  have hboundTop : (mismatchBound : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  let δ : ENNReal := η / (mismatchBound : ENNReal)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact ENNReal.div_pos hη.ne' hboundTop
  obtain ⟨εtv, hεtv, htv⟩ :=
    hreg.exists_uniform_offsetTrajectory_totalVariation_lt hK hk0 hT hδ
  let εbar := min εtv 1
  have hεbar : 0 < εbar := lt_min hεtv zero_lt_one
  refine ⟨εbar, hεbar, mismatchBound, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp
  have hεone : |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    exact hε.le.trans (min_le_right _ _)
  have hhor : (L : ℝ) * |ε| ≤ T := by
    rw [abs_of_pos hεpos]
    simpa only [mul_comm] using horizon
  have hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin (q₁, p) i).1 ≤ R := by
    intro i
    exact (euclideanNorm_fst_le_phaseSize _).trans
      ((offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
        hreg hεone origin i hhor (q₁, p)).trans (by
          dsimp [R]
          gcongr
          exact hphase q₁ hq₁ p hp))
  have hright : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin (q₂, p) i).1 ≤ R := by
    intro i
    exact (euclideanNorm_fst_le_phaseSize _).trans
      ((offsetLeapfrogTrajectory_euclideanPhaseSize_le_exp
        hreg hεone origin i hhor (q₂, p)).trans (by
          dsimp [R]
          gcongr
          exact hphase q₂ hq₂ p hp))
  constructor
  · intro i j
    exact trajectorySquaredPositionCost_le_of_positionNorm_le
      gradient ε (((q₁, p), (q₂, p))) origin hR.le hleft hright i j
  · have htv' := htv hεpos (hε.trans_le (min_le_left _ _)) horizon
      origin q₁ hq₁ q₂ hq₂ p hp
    calc
      McmcLean.Finite.totalVariation
            (trajectoryIndexPMF potential
              (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
            (trajectoryIndexPMF potential
              (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
            (mismatchBound : ENNReal) <
          δ * (mismatchBound : ENNReal) := by
            simpa only [mul_comm] using
              ENNReal.mul_lt_mul_right hboundPos.ne' hboundTop htv'
      _ = η := by
        dsimp [δ]
        exact ENNReal.div_mul_cancel hboundPos.ne' hboundTop

/-- Quantitative local relative consistency for signed leapfrog integration.
On bounded initial phases and a bounded integration horizon, the difference
of two centered energy defects is `O(|ε|)` times their initial phase
separation.  This is stronger and more reusable than the compact-set
epsilon--delta property below, while remaining strictly weaker than assuming
the final trajectory-weight conclusion. -/
def LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) : Prop :=
  ∀ R T : ℝ, 0 ≤ T → ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ε : ℝ}, |ε| ≤ 1 → ∀ k : ℤ,
      (Int.natAbs k : ℝ) * |ε| ≤ T →
      ∀ z₁ z₂ : PhaseSpace ι,
        euclideanPhaseSize z₁ ≤ R → euclideanPhaseSize z₂ ≤ R →
        |(energy potential (signedLeapfrog gradient ε k z₁) -
              energy potential z₁) -
            (energy potential (signedLeapfrog gradient ε k z₂) -
              energy potential z₂)| ≤
          C * |ε| *
            (euclideanNorm (z₁.1 - z₂.1) +
              euclideanNorm (z₁.2 - z₂.2))

/-- Vanishing-modulus relative consistency for signed leapfrog integration.
This is the natural qualitative target under `C²` regularity: on every
bounded phase family and horizon, the centered energy-defect map becomes
arbitrarily Lipschitz as the step size tends to zero.  It does not require the
linear `O(|ε|)` modulus available for the quadratic specialization. -/
def LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) : Prop :=
  ∀ R T : ℝ, 0 ≤ T → ∀ relativeRate : ℝ, 0 < relativeRate →
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| < εbar → ∀ k : ℤ,
      (Int.natAbs k : ℝ) * |ε| ≤ T →
      ∀ z₁ z₂ : PhaseSpace ι,
        euclideanPhaseSize z₁ ≤ R → euclideanPhaseSize z₂ ≤ R →
        |(energy potential (signedLeapfrog gradient ε k z₁) -
              energy potential z₁) -
            (energy potential (signedLeapfrog gradient ε k z₂) -
              energy potential z₂)| ≤
          relativeRate *
            (euclideanNorm (z₁.1 - z₂.1) +
              euclideanNorm (z₁.2 - z₂.2))

/-- Shared-momentum vanishing relative consistency, exactly matching the
coupled-HMC use case.  This is weaker than the arbitrary-phase criterion and
is the appropriate general-potential obligation because the two trajectories
are initialized with one common Gaussian momentum. -/
def LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyErrorOfSharedMomentum
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) : Prop :=
  ∀ R T : ℝ, 0 ≤ T → ∀ relativeRate : ℝ, 0 < relativeRate →
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| < εbar → ∀ k : ℤ,
      (Int.natAbs k : ℝ) * |ε| ≤ T →
      ∀ z₁ z₂ : PhaseSpace ι, z₁.2 = z₂.2 →
        euclideanPhaseSize z₁ ≤ R → euclideanPhaseSize z₂ ≤ R →
        |(energy potential (signedLeapfrog gradient ε k z₁) -
              energy potential z₁) -
            (energy potential (signedLeapfrog gradient ε k z₂) -
              energy potential z₂)| ≤
          relativeRate * euclideanNorm (z₁.1 - z₂.1)

/-- Centered Hamiltonian defect of one leapfrog step. -/
noncomputable def oneStepEnergyDefect
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) (z : PhaseSpace ι) : ℝ :=
  energy potential (leapfrog gradient ε z) - energy potential z

/-- At step size zero, the one-step energy defect is identically zero. -/
@[simp]
theorem oneStepEnergyDefect_zero
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    oneStepEnergyDefect potential gradient 0 = 0 := by
  funext z
  simp [oneStepEnergyDefect, leapfrog, halfKick, drift]

/-- Consequently, the phase derivative of the defect vanishes exactly at
step size zero. The remaining consistency issue is the uniform rate at which
this derivative approaches zero. -/
@[simp]
theorem fderiv_oneStepEnergyDefect_zero
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (z : PhaseSpace ι) :
    fderiv ℝ (oneStepEnergyDefect potential gradient 0) z = 0 := by
  rw [oneStepEnergyDefect_zero]
  simp

/-- Tangent of one leapfrog update when the step size, rather than the phase
point, is varied. The final term is the Hessian action contributed by the
force at the drifted position. -/
noncomputable def leapfrogStepSizeTangent
    (gradient : Position ι → Position ι) (ε : ℝ) (z : PhaseSpace ι) :
    PhaseSpace ι :=
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  let qDot := pHalf - (ε / 2) • gradient z.1
  let pDot :=
    -(1 / 2 : ℝ) • gradient z.1 -
      (1 / 2 : ℝ) • gradient qNext -
        (ε / 2) • fderiv ℝ gradient qNext qDot
  (qDot, pDot)

/-- Tangent of one leapfrog update with respect to its initial phase point. -/
noncomputable def leapfrogPhaseTangent
    (gradient : Position ι → Position ι) (ε : ℝ)
    (z v : PhaseSpace ι) : PhaseSpace ι :=
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  let dpHalf := v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1
  let dqNext := v.1 + ε • dpHalf
  let dpNext := dpHalf - (ε / 2) • fderiv ℝ gradient qNext dqNext
  (dqNext, dpNext)

/-- The affine phase-space line through `z` in direction `v` has derivative
`v`, stated with the normed-space instances used by Fréchet calculus. -/
theorem hasDerivAt_phaseLine (z v : PhaseSpace ι) :
    HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
  have hq : HasDerivAt (fun t : ℝ ↦ z.1 + t • v.1) v.1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert (hasDerivAt_const (x := (0 : ℝ)) (z.1 i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 i)) using 1
    · funext x
      rfl
    · simp
  have hp : HasDerivAt (fun t : ℝ ↦ z.2 + t • v.2) v.2 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert (hasDerivAt_const (x := (0 : ℝ)) (z.2 i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 i)) using 1
    · funext x
      rfl
    · simp
  have hphase := hq.prodMk hp
  convert hphase using 1
  funext t
  rfl

/-- The explicit phase tangent is the directional derivative of leapfrog
along every affine phase-space line. -/
theorem RegularPotential.hasDerivAt_leapfrog_phaseLine
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z v : PhaseSpace ι) :
    HasDerivAt (fun t : ℝ ↦ leapfrog gradient ε (z + t • v))
      (leapfrogPhaseTangent gradient ε z v) 0 := by
  let q : ℝ → Position ι := fun t ↦ z.1 + t • v.1
  let p : ℝ → Momentum ι := fun t ↦ z.2 + t • v.2
  have hq : HasDerivAt q v.1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    dsimp only [q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    convert (hasDerivAt_const (x := (0 : ℝ)) (z.1 i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (v.1 i)) using 1
    · funext x
      rfl
    · simp
  have hp : HasDerivAt p v.2 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    dsimp only [p, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    convert (hasDerivAt_const (x := (0 : ℝ)) (z.2 i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (v.2 i)) using 1
    · funext x
      rfl
    · simp
  let pHalf : ℝ → Momentum ι := fun t ↦ halfKick gradient ε (q t) (p t)
  have hgradientQ : HasDerivAt (gradient ∘ q)
      (fderiv ℝ gradient z.1 v.1) 0 := by
    have hcomp := (hreg.contDiff_one_gradient.differentiable (by norm_num)
      (q 0)).hasFDerivAt.comp_hasDerivAt 0 hq
    simpa [q] using hcomp
  have hpHalf : HasDerivAt pHalf
      (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1) 0 := by
    dsimp [pHalf, halfKick]
    exact hp.sub (hgradientQ.const_smul (ε / 2 : ℝ))
  let qNext : ℝ → Position ι := fun t ↦ drift ε (q t) (pHalf t)
  have hqNext : HasDerivAt qNext
      (v.1 + ε • (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1)) 0 := by
    dsimp [qNext, drift]
    exact hq.add (hpHalf.const_smul ε)
  have hgradientNext : HasDerivAt (gradient ∘ qNext)
      (fderiv ℝ gradient (qNext 0)
        (v.1 + ε • (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1))) 0 :=
    (hreg.contDiff_one_gradient.differentiable (by norm_num)
      (qNext 0)).hasFDerivAt.comp_hasDerivAt 0 hqNext
  let pNext : ℝ → Momentum ι := fun t ↦
    halfKick gradient ε (qNext t) (pHalf t)
  have hpNext : HasDerivAt pNext
      ((v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1) -
        (ε / 2) • fderiv ℝ gradient (qNext 0)
          (v.1 + ε • (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1))) 0 := by
    dsimp [pNext, halfKick]
    exact hpHalf.sub (hgradientNext.const_smul (ε / 2 : ℝ))
  have hphase := hqNext.prodMk hpNext
  dsimp [qNext, pNext, pHalf, q, p] at hphase
  convert hphase using 1
  · funext t
    simp [leapfrog, halfKick, drift]
  · simp [leapfrogPhaseTangent, halfKick, drift]

/-- Explicit action of the phase Fréchet derivative of leapfrog. -/
theorem RegularPotential.fderiv_leapfrog_apply
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z v : PhaseSpace ι) :
    fderiv ℝ (leapfrog gradient ε) z v =
      leapfrogPhaseTangent gradient ε z v := by
  have habstract := (hreg.contDiff_one_leapfrog ε).differentiable
    (by norm_num) z
  have habstract' : DifferentiableAt ℝ (leapfrog gradient ε)
      (z + (0 : ℝ) • v) := by
    simpa using habstract
  have hline := habstract'.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_phaseLine z v)
  simpa using hline.unique (hreg.hasDerivAt_leapfrog_phaseLine ε z v)

/-- Under `C²` potential regularity, the explicit tangent above is the actual
derivative of leapfrog with respect to its step-size parameter. -/
theorem RegularPotential.hasDerivAt_leapfrog_stepSize
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z : PhaseSpace ι) :
    HasDerivAt (fun t : ℝ ↦ leapfrog gradient t z)
      (leapfrogStepSizeTangent gradient ε z) ε := by
  let Q : ℝ → Position ι := fun t ↦ (leapfrog gradient t z).1
  let P : ℝ → Momentum ι := fun t ↦ (leapfrog gradient t z).2
  let qDot : Position ι :=
    halfKick gradient ε z.1 z.2 - (ε / 2) • gradient z.1
  have hQ : HasDerivAt Q qDot ε := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := ((hasDerivAt_const (x := ε) (z.1 i)).add
      ((hasDerivAt_id ε).mul
        ((hasDerivAt_const (x := ε) (z.2 i)).sub
          (((hasDerivAt_id ε).div_const 2).mul_const
            (gradient z.1 i)))))
    dsimp [Q, qDot, leapfrog, halfKick, drift] at h ⊢
    convert h using 1
    · funext x
      rfl
    · ring
  let qNext : Position ι := Q ε
  have hgradQ : HasDerivAt (fun t : ℝ ↦ gradient (Q t))
      (fderiv ℝ gradient qNext qDot) ε := by
    exact (hreg.contDiff_one_gradient.differentiable (by norm_num)
      qNext).hasFDerivAt.comp_hasDerivAt ε hQ
  have hP : HasDerivAt P
      (-(1 / 2 : ℝ) • gradient z.1 -
        (1 / 2 : ℝ) • gradient qNext -
          (ε / 2) • fderiv ℝ gradient qNext qDot) ε := by
    apply hasDerivAt_pi.mpr
    intro i
    have hfirst := ((hasDerivAt_id ε).div_const 2).mul_const
      (gradient z.1 i)
    have hgradQi := hasDerivAt_pi.mp hgradQ i
    have hsecond := ((hasDerivAt_id ε).div_const 2).mul hgradQi
    have htotal := ((hasDerivAt_const (x := ε) (z.2 i)).sub hfirst).sub hsecond
    dsimp [P, Q, qNext, qDot, leapfrog, halfKick, drift] at htotal ⊢
    convert htotal using 1
    · funext x
      rfl
    · ring
  have hphase := hQ.prodMk hP
  dsimp [Q, P] at hphase
  convert hphase using 1
  simp only [leapfrogStepSizeTangent, qDot, qNext, Q, leapfrog]

/-- Directional derivative of the Hamiltonian at a phase point, written in
the explicit Euclidean coordinates used throughout the development. -/
noncomputable def energyDirectionalDerivative
    (gradient : Position ι → Position ι)
    (z v : PhaseSpace ι) : ℝ :=
  euclideanInner (gradient z.1) v.1 + euclideanInner z.2 v.2

/-- Chain rule for the Hamiltonian along an arbitrary differentiable phase
curve. -/
theorem RegularPotential.hasDerivAt_energy_of_hasDerivAt
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {Z : ℝ → PhaseSpace ι} {V : PhaseSpace ι} {t : ℝ}
    (hZ : HasDerivAt Z V t) :
    HasDerivAt (fun s ↦ energy potential (Z s))
      (energyDirectionalDerivative gradient (Z t) V) t := by
  have hq : HasDerivAt (fun s ↦ (Z s).1) V.1 t := by
    simpa using
      ((hasDerivAt_const (x := t)
        (ContinuousLinearMap.fst ℝ (Position ι) (Momentum ι))).clm_apply hZ)
  have hp : HasDerivAt (fun s ↦ (Z s).2) V.2 t := by
    simpa using
      ((hasDerivAt_const (x := t)
        (ContinuousLinearMap.snd ℝ (Position ι) (Momentum ι))).clm_apply hZ)
  have hpotential : HasDerivAt (fun s ↦ potential (Z s).1)
      (euclideanInner (gradient (Z t).1) V.1) t := by
    have hcomp :=
      (hreg.contDiff_two.differentiable
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (Z t).1).hasFDerivAt.comp_hasDerivAt t hq
    rw [hreg.fderiv_apply] at hcomp
    exact hcomp
  have hkinetic : HasDerivAt (fun s ↦ kineticEnergy (Z s).2)
      (euclideanInner (Z t).2 V.2) t := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i hi ↦ ((hasDerivAt_pi.mp hp i).pow 2))
    have hhalf := hsum.const_mul (1 / 2 : ℝ)
    unfold kineticEnergy
    apply hhalf.congr_deriv
    simp only [euclideanInner, Finset.mul_sum]
    simp
    ring_nf
  change HasDerivAt
    ((fun s ↦ potential (Z s).1) + fun s ↦ kineticEnergy (Z s).2)
      (energyDirectionalDerivative gradient (Z t) V) t
  unfold energyDirectionalDerivative
  exact hpotential.add hkinetic

/-- Explicit action of the phase derivative of the one-step energy defect. -/
theorem RegularPotential.fderiv_oneStepEnergyDefect_apply
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z v : PhaseSpace ι) :
    fderiv ℝ (oneStepEnergyDefect potential gradient ε) z v =
      energyDirectionalDerivative gradient (leapfrog gradient ε z)
          (leapfrogPhaseTangent gradient ε z v) -
        energyDirectionalDerivative gradient z v := by
  have habstract : DifferentiableAt ℝ
      (oneStepEnergyDefect potential gradient ε) z := by
    unfold oneStepEnergyDefect
    exact ((hreg.contDiff_one_energy.comp
      (hreg.contDiff_one_leapfrog ε)).sub
        hreg.contDiff_one_energy).differentiable (by norm_num) z
  have habstract' : DifferentiableAt ℝ
      (oneStepEnergyDefect potential gradient ε) (z + (0 : ℝ) • v) := by
    simpa using habstract
  have habstractLine := habstract'.hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_phaseLine z v)
  have hafter := hreg.hasDerivAt_energy_of_hasDerivAt
    (hreg.hasDerivAt_leapfrog_phaseLine ε z v)
  have hinitial := hreg.hasDerivAt_energy_of_hasDerivAt
    (hasDerivAt_phaseLine z v)
  have hunique := habstractLine.unique (hafter.sub hinitial)
  simpa [oneStepEnergyDefect, Function.comp_apply] using hunique

/-- The derivative of the certified gradient is a symmetric Hessian in the
explicit Euclidean pairing. -/
theorem RegularPotential.euclideanInner_fderiv_gradient_comm
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (q v w : Position ι) :
    euclideanInner (fderiv ℝ gradient q v) w =
      euclideanInner (fderiv ℝ gradient q w) v := by
  have hline (u : Position ι) :
      HasDerivAt (fun t : ℝ ↦ q + t • u) u 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    convert (hasDerivAt_const (x := (0 : ℝ)) (q i)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (u i)) using 1
    · funext x
      rfl
    · simp
  let A : Position ι → Position ι →L[ℝ] ℝ := fderiv ℝ potential
  have hA : ContDiff ℝ 1 A := hreg.contDiff_two.fderiv_right (by norm_num)
  have hsecond (u r : Position ι) :
      fderiv ℝ A q u r = euclideanInner (fderiv ℝ gradient q u) r := by
    have hAdiff : DifferentiableAt ℝ A (q + (0 : ℝ) • u) := by
      simpa using hA.differentiable (by norm_num) q
    have hAline := hAdiff.hasFDerivAt.comp_hasDerivAt
      0 (hline u)
    have happly := hAline.clm_apply (hasDerivAt_const (x := (0 : ℝ)) r)
    have hgradientDiff : DifferentiableAt ℝ gradient (q + (0 : ℝ) • u) := by
      simpa using hreg.contDiff_one_gradient.differentiable (by norm_num) q
    have hgradientLine := hgradientDiff.hasFDerivAt.comp_hasDerivAt
      0 (hline u)
    have hinner := hasDerivAt_euclideanInner
      (fun i ↦ hasDerivAt_pi.mp hgradientLine i)
      (fun i ↦ hasDerivAt_const (x := (0 : ℝ)) (r i))
    simp only [Function.comp_apply, zero_smul, add_zero, map_zero] at happly hinner
    have heq : (fun t : ℝ ↦ A (q + t • u) r) =
        fun t : ℝ ↦ euclideanInner (gradient (q + t • u)) r := by
      funext t
      exact hreg.fderiv_apply _ _
    rw [heq] at happly
    have hu := happly.unique hinner
    simpa [A, euclideanInner] using hu
  have hsymm := hreg.contDiff_two.contDiffAt.isSymmSndFDerivAt
    (x := q) (by norm_num)
  have hsymm' : fderiv ℝ A q v w = fderiv ℝ A q w v := by
    simpa [A] using hsymm v w
  calc
    euclideanInner (fderiv ℝ gradient q v) w = fderiv ℝ A q v w :=
      (hsecond v w).symm
    _ = fderiv ℝ A q w v := hsymm'
    _ = euclideanInner (fderiv ℝ gradient q w) v := hsecond w v

/-- On every bounded phase family, the Hessians at the initial and drifted
leapfrog positions become uniformly close as the step size tends to zero. -/
theorem RegularPotential.exists_uniform_leapfrog_hessian_sub_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (R : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → |ε| < εbar →
      ∀ z : PhaseSpace ι, euclideanPhaseSize z ≤ R →
        ‖fderiv ℝ gradient (leapfrog gradient ε z).1 -
            fderiv ℝ gradient z.1‖ ≤ η := by
  let S : ℝ := max R 0
  let G : ℝ := (β : ℝ) * S + euclideanNorm (gradient 0)
  let P : ℝ := S + G
  let B : ℝ := S + P
  have hS : 0 ≤ S := le_max_right _ _
  have hG : 0 ≤ G := by
    dsimp [G]
    exact add_nonneg (mul_nonneg β.coe_nonneg hS)
      (euclideanNorm_nonneg _)
  have hP : 0 ≤ P := add_nonneg hS hG
  have hB : 0 ≤ B := add_nonneg hS hP
  let K : Set (Position ι) := Metric.closedBall 0 B
  have hK : IsCompact K := isCompact_closedBall 0 B
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff_le.mp
    (hreg.uniformContinuousOn_fderiv_gradient hK) η hη
  let εbar : ℝ := min 1 (δ / (P + 1))
  have hPone : 0 < P + 1 := by linarith
  have hεbar : 0 < εbar :=
    lt_min zero_lt_one (div_pos hδ hPone)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z hz
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  have hRS : R ≤ S := le_max_left _ _
  have hq : euclideanNorm z.1 ≤ S :=
    (euclideanNorm_fst_le_phaseSize z).trans (hz.trans hRS)
  have hp : euclideanNorm z.2 ≤ S := by
    unfold euclideanPhaseSize at hz
    nlinarith [euclideanNorm_nonneg z.1]
  have hg : euclideanNorm (gradient z.1) ≤ G := by
    apply (hreg.euclideanNorm_gradient_le z.1).trans
    dsimp [G]
    gcongr
  have hpHalf : euclideanNorm pHalf ≤ P := by
    dsimp [pHalf, halfKick]
    apply (euclideanNorm_sub_le z.2 ((ε / 2) • gradient z.1)).trans
    rw [euclideanNorm_smul]
    have habsHalf : |ε / 2| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg ε]
    dsimp [P]
    nlinarith [euclideanNorm_nonneg z.2, euclideanNorm_nonneg (gradient z.1)]
  have hqdiff : euclideanNorm (qNext - z.1) ≤ |ε| * P := by
    have heq : qNext - z.1 = ε • pHalf := by
      dsimp [qNext, drift]
      abel
    rw [heq, euclideanNorm_smul]
    exact mul_le_mul_of_nonneg_left hpHalf (abs_nonneg ε)
  have hqNext : euclideanNorm qNext ≤ B := by
    have htri := euclideanNorm_add_le (qNext - z.1) z.1
    have heq : qNext - z.1 + z.1 = qNext := by abel
    rw [heq] at htri
    have habsP : |ε| * P ≤ P := by
      calc
        |ε| * P ≤ 1 * P := mul_le_mul_of_nonneg_right hεone hP
        _ = P := one_mul P
    calc
      euclideanNorm qNext ≤ euclideanNorm (qNext - z.1) + euclideanNorm z.1 := htri
      _ ≤ |ε| * P + S := add_le_add hqdiff hq
      _ ≤ P + S := add_le_add habsP le_rfl
      _ = B := by dsimp [B]; ring
  have hzK : z.1 ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖z.1‖ ≤ euclideanNorm z.1 by
      simpa only [dist_zero_right, sub_zero] using
        dist_le_euclideanNorm_sub z.1 0) |>.trans (hq.trans (by
          dsimp [B]
          linarith))
  have hqNextK : qNext ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖qNext‖ ≤ euclideanNorm qNext by
      simpa only [dist_zero_right, sub_zero] using
        dist_le_euclideanNorm_sub qNext 0) |>.trans hqNext
  have hεδ : |ε| * P < δ := by
    have hquot : |ε| < δ / (P + 1) :=
      hε.trans_le (min_le_right _ _)
    have hmul : |ε| * (P + 1) < δ := (lt_div_iff₀ hPone).mp hquot
    nlinarith [abs_nonneg ε]
  have hdist : dist qNext z.1 ≤ δ :=
    (dist_le_euclideanNorm_sub qNext z.1).trans
      (hqdiff.trans hεδ.le)
  have hout := hclose qNext hqNextK z.1 hzK hdist
  simpa only [dist_eq_norm, qNext, leapfrog] using hout

/-- Dimension-explicit Euclidean bound for the Hessian action, obtained from
the global ambient operator-norm bound. -/
theorem RegularPotential.euclideanNorm_fderiv_gradient_apply_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (q u : Position ι) :
    euclideanNorm (fderiv ℝ gradient q u) ≤
      ((Fintype.card ι : ℝ) + 1) *
        ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ) *
          euclideanNorm u := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let M : ℝ := ((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have houtAmbient : ‖fderiv ℝ gradient q u‖ ≤ M * ‖u‖ :=
    (fderiv ℝ gradient q).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hreg.norm_fderiv_gradient_le_global q)
        (norm_nonneg u))
  have houtEuclidean : euclideanNorm (fderiv ℝ gradient q u) ≤
      D * ‖fderiv ℝ gradient q u‖ := by
    have h := euclideanNorm_sub_le_card_succ_mul_dist
      (fderiv ℝ gradient q u) 0
    simpa only [sub_zero, dist_zero_right, D] using h
  have hu : ‖u‖ ≤ euclideanNorm u := by
    simpa only [dist_zero_right, sub_zero] using dist_le_euclideanNorm_sub u 0
  calc
    euclideanNorm (fderiv ℝ gradient q u) ≤
        D * ‖fderiv ℝ gradient q u‖ := houtEuclidean
    _ ≤ D * (M * ‖u‖) := mul_le_mul_of_nonneg_left houtAmbient hD
    _ ≤ D * (M * euclideanNorm u) := by gcongr
    _ = D * M * euclideanNorm u := by ring

/-- On every bounded phase family, the force increment across one leapfrog
drift has a uniformly vanishing first-order linearization remainder. -/
theorem RegularPotential.exists_uniform_leapfrog_gradient_linearization_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (R : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → |ε| < εbar →
      ∀ z : PhaseSpace ι, euclideanPhaseSize z ≤ R →
        ‖(gradient (leapfrog gradient ε z).1 - gradient z.1) -
            fderiv ℝ gradient z.1 ((leapfrog gradient ε z).1 - z.1)‖ ≤
          η * ‖(leapfrog gradient ε z).1 - z.1‖ := by
  let S : ℝ := max R 0
  let G : ℝ := (β : ℝ) * S + euclideanNorm (gradient 0)
  let P : ℝ := S + G
  let B : ℝ := S + P
  have hS : 0 ≤ S := le_max_right _ _
  have hG : 0 ≤ G := by
    dsimp [G]
    exact add_nonneg (mul_nonneg β.coe_nonneg hS)
      (euclideanNorm_nonneg _)
  have hP : 0 ≤ P := add_nonneg hS hG
  let K : Set (Position ι) := Metric.closedBall 0 B
  have hK : IsCompact K := isCompact_closedBall 0 B
  have hKconvex : Convex ℝ K := convex_closedBall 0 B
  obtain ⟨δ, hδ, hlinear⟩ :=
    hreg.exists_uniform_gradient_linearization_error hK hKconvex hη
  let εbar : ℝ := min 1 (δ / (P + 1))
  have hPone : 0 < P + 1 := by linarith
  have hεbar : 0 < εbar :=
    lt_min zero_lt_one (div_pos hδ hPone)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z hz
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  have hRS : R ≤ S := le_max_left _ _
  have hq : euclideanNorm z.1 ≤ S :=
    (euclideanNorm_fst_le_phaseSize z).trans (hz.trans hRS)
  have hp : euclideanNorm z.2 ≤ S := by
    unfold euclideanPhaseSize at hz
    nlinarith [euclideanNorm_nonneg z.1]
  have hg : euclideanNorm (gradient z.1) ≤ G := by
    apply (hreg.euclideanNorm_gradient_le z.1).trans
    dsimp [G]
    gcongr
  have hpHalf : euclideanNorm pHalf ≤ P := by
    dsimp [pHalf, halfKick]
    apply (euclideanNorm_sub_le z.2 ((ε / 2) • gradient z.1)).trans
    rw [euclideanNorm_smul]
    have habsHalf : |ε / 2| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg ε]
    dsimp [P]
    nlinarith [euclideanNorm_nonneg z.2, euclideanNorm_nonneg (gradient z.1)]
  have hqdiff : euclideanNorm (qNext - z.1) ≤ |ε| * P := by
    have heq : qNext - z.1 = ε • pHalf := by
      dsimp [qNext, drift]
      abel
    rw [heq, euclideanNorm_smul]
    exact mul_le_mul_of_nonneg_left hpHalf (abs_nonneg ε)
  have hqNext : euclideanNorm qNext ≤ B := by
    have htri := euclideanNorm_add_le (qNext - z.1) z.1
    have heq : qNext - z.1 + z.1 = qNext := by abel
    rw [heq] at htri
    have habsP : |ε| * P ≤ P := by
      calc
        |ε| * P ≤ 1 * P := mul_le_mul_of_nonneg_right hεone hP
        _ = P := one_mul P
    calc
      euclideanNorm qNext ≤ euclideanNorm (qNext - z.1) + euclideanNorm z.1 := htri
      _ ≤ |ε| * P + S := add_le_add hqdiff hq
      _ ≤ P + S := add_le_add habsP le_rfl
      _ = B := by dsimp [B]; ring
  have hzK : z.1 ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖z.1‖ ≤ euclideanNorm z.1 by
      simpa only [dist_zero_right, sub_zero] using
        dist_le_euclideanNorm_sub z.1 0) |>.trans (hq.trans (by
          dsimp [B]
          linarith))
  have hqNextK : qNext ∈ K := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (show ‖qNext‖ ≤ euclideanNorm qNext by
      simpa only [dist_zero_right, sub_zero] using
        dist_le_euclideanNorm_sub qNext 0) |>.trans hqNext
  have hεδ : |ε| * P < δ := by
    have hquot : |ε| < δ / (P + 1) :=
      hε.trans_le (min_le_right _ _)
    have hmul : |ε| * (P + 1) < δ := (lt_div_iff₀ hPone).mp hquot
    nlinarith [abs_nonneg ε]
  have hdist : dist z.1 qNext ≤ δ := by
    rw [dist_comm]
    exact (dist_le_euclideanNorm_sub qNext z.1).trans
      (hqdiff.trans hεδ.le)
  have hout := hlinear z.1 hzK qNext hqNextK hdist
  simpa only [qNext, leapfrog] using hout

/-- A gradient linearization remainder together with endpoint Hessian
continuity controls the trapezoidal force increment. -/
theorem norm_leapfrog_trapezoidalForceRemainder_le
    (gradient : Position ι → Position ι) (ε η : ℝ)
    (z : PhaseSpace ι)
    (hlinear :
      ‖(gradient (leapfrog gradient ε z).1 - gradient z.1) -
          fderiv ℝ gradient z.1 ((leapfrog gradient ε z).1 - z.1)‖ ≤
        η * ‖(leapfrog gradient ε z).1 - z.1‖)
    (hhessian :
      ‖fderiv ℝ gradient (leapfrog gradient ε z).1 -
          fderiv ℝ gradient z.1‖ ≤ η) :
    let pHalf := halfKick gradient ε z.1 z.2
    ‖(gradient (leapfrog gradient ε z).1 - gradient z.1) -
        (ε / 2) •
          (fderiv ℝ gradient z.1 pHalf +
            fderiv ℝ gradient (leapfrog gradient ε z).1 pHalf)‖ ≤
      (3 / 2 : ℝ) * η * |ε| * ‖pHalf‖ := by
  let pHalf := halfKick gradient ε z.1 z.2
  let H₀ := fderiv ℝ gradient z.1
  let H₁ := fderiv ℝ gradient (leapfrog gradient ε z).1
  let forceDiff := gradient (leapfrog gradient ε z).1 - gradient z.1
  have hposition : (leapfrog gradient ε z).1 - z.1 = ε • pHalf := by
    dsimp [pHalf, leapfrog, drift]
    abel
  have hid : forceDiff - (ε / 2) • (H₀ pHalf + H₁ pHalf) =
      (forceDiff - H₀ ((leapfrog gradient ε z).1 - z.1)) +
        (ε / 2) • ((H₀ - H₁) pHalf) := by
    rw [hposition]
    simp only [map_smul, sub_apply]
    module
  change ‖forceDiff - (ε / 2) • (H₀ pHalf + H₁ pHalf)‖ ≤
    (3 / 2 : ℝ) * η * |ε| * ‖pHalf‖
  rw [hid]
  apply (norm_add_le _ _).trans
  have hfirst :
      ‖forceDiff - H₀ ((leapfrog gradient ε z).1 - z.1)‖ ≤
        η * (|ε| * ‖pHalf‖) := by
    apply hlinear.trans
    rw [hposition, norm_smul]
    rw [Real.norm_eq_abs]
  have hsecond : ‖(H₀ - H₁) pHalf‖ ≤ η * ‖pHalf‖ := by
    have hop : ‖H₀ - H₁‖ ≤ η := by
      have heq : H₀ - H₁ = -(H₁ - H₀) := by abel
      rw [heq, norm_neg]
      exact hhessian
    exact ((H₀ - H₁).le_opNorm pHalf).trans
      (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
  rw [norm_smul]
  have habsHalf : |ε / 2| = |ε| / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.norm_eq_abs, habsHalf]
  apply (add_le_add hfirst
    (mul_le_mul_of_nonneg_left hsecond (div_nonneg (abs_nonneg ε) (by norm_num)))).trans_eq
  ring

/-- The complete trapezoidal force remainder is uniformly small on bounded
phase families. -/
theorem RegularPotential.exists_uniform_leapfrog_trapezoidalForceRemainder_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (R : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → |ε| < εbar →
      ∀ z : PhaseSpace ι, euclideanPhaseSize z ≤ R →
        let pHalf := halfKick gradient ε z.1 z.2
        ‖(gradient (leapfrog gradient ε z).1 - gradient z.1) -
            (ε / 2) •
              (fderiv ℝ gradient z.1 pHalf +
                fderiv ℝ gradient (leapfrog gradient ε z).1 pHalf)‖ ≤
          (3 / 2 : ℝ) * η * |ε| * ‖pHalf‖ := by
  obtain ⟨εlinear, hεlinear, hlinear⟩ :=
    hreg.exists_uniform_leapfrog_gradient_linearization_le R hη
  obtain ⟨εhessian, hεhessian, hhessian⟩ :=
    hreg.exists_uniform_leapfrog_hessian_sub_le R hη
  let εbar := min εlinear εhessian
  have hεbar : 0 < εbar := lt_min hεlinear hεhessian
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z hz
  apply norm_leapfrog_trapezoidalForceRemainder_le gradient ε η z
  · exact hlinear hεone (hε.trans_le (min_le_left _ _)) z hz
  · exact hhessian hεone (hε.trans_le (min_le_right _ _)) z hz

/-- Exact cancellation decomposition for the phase derivative of one
leapfrog energy defect. The last three terms carry explicit powers of the
step size; the first two form the Hessian/trapezoidal cancellation. -/
theorem RegularPotential.fderiv_oneStepEnergyDefect_apply_eq
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z v : PhaseSpace ι) :
    let pHalf := halfKick gradient ε z.1 z.2
    let qNext := drift ε z.1 pHalf
    let pNext := halfKick gradient ε qNext pHalf
    let hessianInitial := fderiv ℝ gradient z.1
    let hessianNext := fderiv ℝ gradient qNext
    let dpHalf := v.2 - (ε / 2) • hessianInitial v.1
    let dqNext := v.1 + ε • dpHalf
    fderiv ℝ (oneStepEnergyDefect potential gradient ε) z v =
      euclideanInner (gradient qNext - gradient z.1) v.1 -
        (ε / 2) * euclideanInner z.2 (hessianInitial v.1) +
      (ε / 2) * euclideanInner (gradient qNext - gradient z.1) v.2 +
      (ε ^ 2 / 4) *
        euclideanInner (gradient z.1 - gradient qNext)
          (hessianInitial v.1) -
      (ε / 2) * euclideanInner pNext (hessianNext dqNext) := by
  rw [hreg.fderiv_oneStepEnergyDefect_apply]
  dsimp [energyDirectionalDerivative, leapfrogPhaseTangent,
    leapfrog, halfKick, drift]
  simp only [euclideanInner_sub_left, euclideanInner_sub_right,
    euclideanInner_add_right,
    euclideanInner_smul_left, euclideanInner_smul_right,
    euclideanInner_comm]
  ring

/-- The leading terms in the phase derivative are a trapezoidal approximation
to the force increment, plus an explicitly quadratic correction. Hessian
symmetry is what moves its action onto the momentum vectors. -/
theorem RegularPotential.leapfrogEnergyPhaseLeadingCancellation_eq
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z v : PhaseSpace ι) :
    let pHalf := halfKick gradient ε z.1 z.2
    let qNext := drift ε z.1 pHalf
    let pNext := halfKick gradient ε qNext pHalf
    let hessianInitial := fderiv ℝ gradient z.1
    let hessianNext := fderiv ℝ gradient qNext
    let dpHalf := v.2 - (ε / 2) • hessianInitial v.1
    let dqNext := v.1 + ε • dpHalf
    euclideanInner (gradient qNext - gradient z.1) v.1 -
          (ε / 2) * euclideanInner z.2 (hessianInitial v.1) -
          (ε / 2) * euclideanInner pNext (hessianNext dqNext) =
      euclideanInner
          ((gradient qNext - gradient z.1) -
            (ε / 2) • (hessianInitial z.2 + hessianNext pNext)) v.1 -
        (ε ^ 2 / 2) * euclideanInner (hessianNext pNext) dpHalf := by
  dsimp
  have hinitial : euclideanInner z.2 (fderiv ℝ gradient z.1 v.1) =
      euclideanInner (fderiv ℝ gradient z.1 z.2) v.1 := by
    rw [euclideanInner_comm]
    exact hreg.euclideanInner_fderiv_gradient_comm z.1 v.1 z.2
  let qNext := drift ε z.1 (halfKick gradient ε z.1 z.2)
  let pNext := halfKick gradient ε qNext (halfKick gradient ε z.1 z.2)
  let dpHalf := v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1
  let dqNext := v.1 + ε • dpHalf
  have hnext : euclideanInner pNext (fderiv ℝ gradient qNext dqNext) =
      euclideanInner (fderiv ℝ gradient qNext pNext) dqNext := by
    rw [euclideanInner_comm]
    exact hreg.euclideanInner_fderiv_gradient_comm qNext dqNext pNext
  rw [hinitial]
  change _ - _ * euclideanInner pNext (fderiv ℝ gradient qNext dqNext) = _
  rw [hnext]
  dsimp [qNext, pNext, dpHalf, dqNext]
  simp only [euclideanInner_sub_right,
    euclideanInner_add_right,
    euclideanInner_smul_right,
    euclideanInner_comm]
  ring

/-- Fully cancellation-normalized phase derivative. Its first term has the
uniformly vanishing trapezoidal-force coefficient; all four residual terms
carry at least `ε²`. -/
theorem RegularPotential.fderiv_oneStepEnergyDefect_apply_eq_trapezoidal
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z v : PhaseSpace ι) :
    let pHalf := halfKick gradient ε z.1 z.2
    let qNext := drift ε z.1 pHalf
    let pNext := halfKick gradient ε qNext pHalf
    let H₀ := fderiv ℝ gradient z.1
    let H₁ := fderiv ℝ gradient qNext
    let dpHalf := v.2 - (ε / 2) • H₀ v.1
    let trapezoidalForce :=
      (gradient qNext - gradient z.1) -
        (ε / 2) • (H₀ pHalf + H₁ pHalf)
    fderiv ℝ (oneStepEnergyDefect potential gradient ε) z v =
      euclideanInner trapezoidalForce v.1 +
      (ε ^ 2 / 4) * euclideanInner (H₁ (gradient qNext) -
        H₀ (gradient z.1)) v.1 -
      (ε ^ 2 / 2) * euclideanInner (H₁ pNext) dpHalf +
      (ε / 2) * euclideanInner (gradient qNext - gradient z.1) v.2 +
      (ε ^ 2 / 4) * euclideanInner
        (gradient z.1 - gradient qNext) (H₀ v.1) := by
  rw [hreg.fderiv_oneStepEnergyDefect_apply]
  dsimp [energyDirectionalDerivative, leapfrogPhaseTangent,
    leapfrog, halfKick, drift]
  have hinitial (u w : Position ι) :
      euclideanInner w (fderiv ℝ gradient z.1 u) =
        euclideanInner (fderiv ℝ gradient z.1 w) u := by
    rw [euclideanInner_comm]
    exact hreg.euclideanInner_fderiv_gradient_comm z.1 u w
  let qNext := z.1 + ε • (z.2 - (ε / 2) • gradient z.1)
  have hnext (u w : Position ι) :
      euclideanInner w (fderiv ℝ gradient qNext u) =
        euclideanInner (fderiv ℝ gradient qNext w) u := by
    rw [euclideanInner_comm]
    exact hreg.euclideanInner_fderiv_gradient_comm qNext u w
  simp only [euclideanInner_sub_left, euclideanInner_sub_right,
    euclideanInner_add_left, euclideanInner_add_right,
    euclideanInner_smul_left, euclideanInner_smul_right]
  rw [hinitial v.1 z.2]
  let dqNext := v.1 + ε • (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1)
  rw [hnext dqNext z.2, hnext dqNext (gradient z.1),
    hnext dqNext (gradient qNext)]
  dsimp [qNext, dqNext]
  simp only [euclideanInner_sub_right, euclideanInner_add_right,
    euclideanInner_smul_right, euclideanInner_comm, map_sub, map_smul]
  ring

/-- Absolute bound obtained term-by-term from the cancellation-normalized
phase derivative. -/
theorem RegularPotential.abs_fderiv_oneStepEnergyDefect_apply_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z v : PhaseSpace ι) :
    let pHalf := halfKick gradient ε z.1 z.2
    let qNext := drift ε z.1 pHalf
    let pNext := halfKick gradient ε qNext pHalf
    let H₀ := fderiv ℝ gradient z.1
    let H₁ := fderiv ℝ gradient qNext
    let dpHalf := v.2 - (ε / 2) • H₀ v.1
    let trapezoidalForce :=
      (gradient qNext - gradient z.1) -
        (ε / 2) • (H₀ pHalf + H₁ pHalf)
    |fderiv ℝ (oneStepEnergyDefect potential gradient ε) z v| ≤
      euclideanNorm trapezoidalForce * euclideanNorm v.1 +
      (|ε| ^ 2 / 4) *
        (euclideanNorm (H₁ (gradient qNext)) +
          euclideanNorm (H₀ (gradient z.1))) * euclideanNorm v.1 +
      (|ε| ^ 2 / 2) * euclideanNorm (H₁ pNext) *
        euclideanNorm dpHalf +
      (|ε| / 2) * euclideanNorm (gradient qNext - gradient z.1) *
        euclideanNorm v.2 +
      (|ε| ^ 2 / 4) * euclideanNorm (gradient qNext - gradient z.1) *
        euclideanNorm (H₀ v.1) := by
  rw [hreg.fderiv_oneStepEnergyDefect_apply_eq_trapezoidal]
  dsimp
  let a := euclideanInner
    ((gradient (leapfrog gradient ε z).1 - gradient z.1) -
      (ε / 2) •
        (fderiv ℝ gradient z.1 (halfKick gradient ε z.1 z.2) +
          fderiv ℝ gradient (leapfrog gradient ε z).1
            (halfKick gradient ε z.1 z.2))) v.1
  let b := (ε ^ 2 / 4) * euclideanInner
    (fderiv ℝ gradient (leapfrog gradient ε z).1
        (gradient (leapfrog gradient ε z).1) -
      fderiv ℝ gradient z.1 (gradient z.1)) v.1
  let c := (ε ^ 2 / 2) * euclideanInner
    (fderiv ℝ gradient (leapfrog gradient ε z).1
      (halfKick gradient ε (leapfrog gradient ε z).1
        (halfKick gradient ε z.1 z.2)))
    (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1)
  let d := (ε / 2) * euclideanInner
    (gradient (leapfrog gradient ε z).1 - gradient z.1) v.2
  let e := (ε ^ 2 / 4) * euclideanInner
    (gradient z.1 - gradient (leapfrog gradient ε z).1)
    (fderiv ℝ gradient z.1 v.1)
  change |a + b - c + d + e| ≤ _
  have habcde : |a + b - c + d + e| ≤
      |a| + |b| + |c| + |d| + |e| := by
    calc
      |a + b - c + d + e| ≤ |a + b - c + d| + |e| := abs_add_le _ _
      _ ≤ (|a + b - c| + |d|) + |e| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|a + b| + |c|) + |d|) + |e| := by
        gcongr
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (a + b) (-c)
      _ ≤ (((|a| + |b|) + |c|) + |d|) + |e| := by
        gcongr
        exact abs_add_le _ _
      _ = |a| + |b| + |c| + |d| + |e| := by ring
  apply habcde.trans
  dsimp [a, b, c, d, e]
  rw [abs_mul, abs_mul, abs_mul, abs_mul]
  simp only [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_pow]
  have ha := abs_euclideanInner_le_norm_mul_norm
    ((gradient (leapfrog gradient ε z).1 - gradient z.1) -
      (ε / 2) •
        (fderiv ℝ gradient z.1 (halfKick gradient ε z.1 z.2) +
          fderiv ℝ gradient (leapfrog gradient ε z).1
            (halfKick gradient ε z.1 z.2))) v.1
  have hb := abs_euclideanInner_le_norm_mul_norm
    (fderiv ℝ gradient (leapfrog gradient ε z).1
        (gradient (leapfrog gradient ε z).1) -
      fderiv ℝ gradient z.1 (gradient z.1)) v.1
  have hc := abs_euclideanInner_le_norm_mul_norm
    (fderiv ℝ gradient (leapfrog gradient ε z).1
      (halfKick gradient ε (leapfrog gradient ε z).1
        (halfKick gradient ε z.1 z.2)))
    (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1)
  have hd := abs_euclideanInner_le_norm_mul_norm
    (gradient (leapfrog gradient ε z).1 - gradient z.1) v.2
  have he := abs_euclideanInner_le_norm_mul_norm
    (gradient z.1 - gradient (leapfrog gradient ε z).1)
    (fderiv ℝ gradient z.1 v.1)
  have hb' : euclideanNorm
      (fderiv ℝ gradient (leapfrog gradient ε z).1
          (gradient (leapfrog gradient ε z).1) -
        fderiv ℝ gradient z.1 (gradient z.1)) ≤
      euclideanNorm (fderiv ℝ gradient (leapfrog gradient ε z).1
        (gradient (leapfrog gradient ε z).1)) +
      euclideanNorm (fderiv ℝ gradient z.1 (gradient z.1)) :=
    euclideanNorm_sub_le _ _
  have heq : euclideanNorm
      (gradient z.1 - gradient (leapfrog gradient ε z).1) =
      euclideanNorm
        (gradient (leapfrog gradient ε z).1 - gradient z.1) := by
    have hneg : gradient z.1 - gradient (leapfrog gradient ε z).1 =
        -(gradient (leapfrog gradient ε z).1 - gradient z.1) := by abel
    rw [hneg, euclideanNorm_neg]
  rw [heq] at he
  simp only [leapfrog] at ha hb hc hd he hb' ⊢
  have hcoeff2 : 0 ≤ |ε| ^ 2 / 4 := by positivity
  have hcoeff1 : 0 ≤ |ε| / 2 := by positivity
  have hA := ha
  have hB : (|ε| ^ 2 / 4) *
      |euclideanInner
        (fderiv ℝ gradient
            (drift ε z.1 (halfKick gradient ε z.1 z.2))
            (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2))) -
          fderiv ℝ gradient z.1 (gradient z.1)) v.1| ≤
      (|ε| ^ 2 / 4) *
        (euclideanNorm (fderiv ℝ gradient
            (drift ε z.1 (halfKick gradient ε z.1 z.2))
            (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)))) +
          euclideanNorm (fderiv ℝ gradient z.1 (gradient z.1))) *
        euclideanNorm v.1 := by
    have hraw := mul_le_mul_of_nonneg_left
      (hb.trans (mul_le_mul_of_nonneg_right hb' (euclideanNorm_nonneg _)))
      hcoeff2
    simpa only [mul_assoc] using hraw
  have hC : (|ε| ^ 2 / 2) *
      |euclideanInner
        (fderiv ℝ gradient
          (drift ε z.1 (halfKick gradient ε z.1 z.2))
          (halfKick gradient ε
            (drift ε z.1 (halfKick gradient ε z.1 z.2))
            (halfKick gradient ε z.1 z.2)))
        (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1)| ≤
      (|ε| ^ 2 / 2) *
        euclideanNorm (fderiv ℝ gradient
          (drift ε z.1 (halfKick gradient ε z.1 z.2))
          (halfKick gradient ε
            (drift ε z.1 (halfKick gradient ε z.1 z.2))
            (halfKick gradient ε z.1 z.2))) *
        euclideanNorm (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1) := by
    have hc0 : 0 ≤ |ε| ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
    have hraw := mul_le_mul_of_nonneg_left hc hc0
    simpa only [mul_assoc] using hraw
  have hD : (|ε| / 2) *
      |euclideanInner
        (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)) - gradient z.1)
        v.2| ≤
      (|ε| / 2) *
        euclideanNorm
          (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)) - gradient z.1) *
        euclideanNorm v.2 := by
    have hraw := mul_le_mul_of_nonneg_left hd hcoeff1
    simpa only [mul_assoc] using hraw
  have hE : (|ε| ^ 2 / 4) *
      |euclideanInner
        (gradient z.1 - gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)))
        (fderiv ℝ gradient z.1 v.1)| ≤
      (|ε| ^ 2 / 4) *
        euclideanNorm
          (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)) - gradient z.1) *
        euclideanNorm (fderiv ℝ gradient z.1 v.1) := by
    have hraw := mul_le_mul_of_nonneg_left he hcoeff2
    simpa only [mul_assoc] using hraw
  linarith

/-- The explicit Euclidean norm of the position component is controlled by
the product phase-space norm, with a deliberately coarse dimension factor. -/
theorem euclideanNorm_fst_le_card_succ_mul_phaseNorm (v : PhaseSpace ι) :
    euclideanNorm v.1 ≤ ((Fintype.card ι : ℝ) + 1) * ‖v‖ := by
  have hcoord : euclideanNorm v.1 ≤
      ((Fintype.card ι : ℝ) + 1) * ‖v.1‖ := by
    have h := euclideanNorm_sub_le_card_succ_mul_dist v.1 0
    simpa only [sub_zero, dist_zero_right] using h
  apply hcoord.trans
  gcongr
  rw [Prod.norm_def]
  exact le_max_left _ _

/-- The explicit Euclidean norm of the momentum component is controlled by
the product phase-space norm, with the same dimension factor. -/
theorem euclideanNorm_snd_le_card_succ_mul_phaseNorm (v : PhaseSpace ι) :
    euclideanNorm v.2 ≤ ((Fintype.card ι : ℝ) + 1) * ‖v‖ := by
  have hcoord : euclideanNorm v.2 ≤
      ((Fintype.card ι : ℝ) + 1) * ‖v.2‖ := by
    have h := euclideanNorm_sub_le_card_succ_mul_dist v.2 0
    simpa only [sub_zero, dist_zero_right] using h
  apply hcoord.trans
  gcongr
  rw [Prod.norm_def]
  exact le_max_right _ _

/-- Uniform linear control of the tangent half-kick.  This is the phase
geometry estimate used to turn the cancellation-normalized scalar bound into
an operator-norm bound. -/
theorem RegularPotential.euclideanNorm_tangentHalfKick_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε : ℝ} (hε : |ε| ≤ 1) (q : Position ι) (v : PhaseSpace ι) :
    euclideanNorm
        (v.2 - (ε / 2) • fderiv ℝ gradient q v.1) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (1 + (((Fintype.card ι : ℝ) + 1) *
          (((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ))) / 2) *
        ‖v‖ := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let A : ℝ := D *
    (((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A, D]; positivity
  have hv₁ := euclideanNorm_fst_le_card_succ_mul_phaseNorm v
  have hv₂ := euclideanNorm_snd_le_card_succ_mul_phaseNorm v
  have hH := hreg.euclideanNorm_fderiv_gradient_apply_le q v.1
  have habsHalf : |ε / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  apply (euclideanNorm_sub_le v.2
    ((ε / 2) • fderiv ℝ gradient q v.1)).trans
  rw [euclideanNorm_smul]
  have hH' : euclideanNorm (fderiv ℝ gradient q v.1) ≤
      A * (D * ‖v‖) := by
    apply hH.trans
    have := mul_le_mul_of_nonneg_left hv₁ hA
    simpa only [A, D, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_add,
      NNReal.coe_one, mul_assoc] using this
  have hscaled : |ε / 2| *
      euclideanNorm (fderiv ℝ gradient q v.1) ≤
      (1 / 2 : ℝ) * (A * (D * ‖v‖)) :=
    (mul_le_mul habsHalf hH' (euclideanNorm_nonneg _) (by positivity))
  calc
    euclideanNorm v.2 + |ε / 2| *
        euclideanNorm (fderiv ℝ gradient q v.1) ≤
      D * ‖v‖ + (1 / 2 : ℝ) * (A * (D * ‖v‖)) :=
        add_le_add hv₂ hscaled
    _ = D * (1 + A / 2) * ‖v‖ := by ring
    _ = ((Fintype.card ι : ℝ) + 1) *
        (1 + (((Fintype.card ι : ℝ) + 1) *
          (((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ))) / 2) *
        ‖v‖ := by rfl

/-- Once the bounded phase data are supplied, the cancellation-normalized
one-step derivative has one uniformly vanishing first-order coefficient and
an explicit quadratic remainder.  This packages the algebra needed for the
eventual operator-norm estimate. -/
theorem RegularPotential.abs_fderiv_oneStepEnergyDefect_apply_le_bounded
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {ε T G₀ G₁ Pnext F : ℝ} (z v : PhaseSpace ι)
    (hε : |ε| ≤ 1) (hT : 0 ≤ T) (hG₀ : 0 ≤ G₀) (hG₁ : 0 ≤ G₁)
    (hPnext : 0 ≤ Pnext) (hF : 0 ≤ F)
    (htrap :
      euclideanNorm
        ((gradient (leapfrog gradient ε z).1 - gradient z.1) -
          (ε / 2) •
            (fderiv ℝ gradient z.1 (halfKick gradient ε z.1 z.2) +
              fderiv ℝ gradient (leapfrog gradient ε z).1
                (halfKick gradient ε z.1 z.2))) ≤ T * |ε|)
    (hgradient₀ : euclideanNorm (gradient z.1) ≤ G₀)
    (hgradient₁ : euclideanNorm (gradient (leapfrog gradient ε z).1) ≤ G₁)
    (hpNext : euclideanNorm (leapfrog gradient ε z).2 ≤ Pnext)
    (hforce : euclideanNorm
      (gradient (leapfrog gradient ε z).1 - gradient z.1) ≤ F * |ε|) :
    let D : ℝ := (Fintype.card ι : ℝ) + 1
    let A : ℝ := D *
      (((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ))
    |fderiv ℝ (oneStepEnergyDefect potential gradient ε) z v| ≤
      |ε| *
        (T * D + |ε| *
          (A * (G₁ + G₀) * D / 4 +
            A * Pnext * (D * (1 + A / 2)) / 2 +
            F * D / 2 + F * A * D / 4)) * ‖v‖ := by
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let A : ℝ := D *
    (((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A, D]; positivity
  have habs : 0 ≤ |ε| := abs_nonneg _
  have hvnorm : 0 ≤ ‖v‖ := norm_nonneg _
  have hv₁ : euclideanNorm v.1 ≤ D * ‖v‖ := by
    simpa only [D] using euclideanNorm_fst_le_card_succ_mul_phaseNorm v
  have hv₂ : euclideanNorm v.2 ≤ D * ‖v‖ := by
    simpa only [D] using euclideanNorm_snd_le_card_succ_mul_phaseNorm v
  have hdp : euclideanNorm
      (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1) ≤
      D * (1 + A / 2) * ‖v‖ := by
    simpa only [D, A] using hreg.euclideanNorm_tangentHalfKick_le hε z.1 v
  have hH₀g₀ : euclideanNorm (fderiv ℝ gradient z.1 (gradient z.1)) ≤
      A * G₀ := by
    apply (hreg.euclideanNorm_fderiv_gradient_apply_le z.1
      (gradient z.1)).trans
    have := mul_le_mul_of_nonneg_left hgradient₀ hA
    simpa only [A, D, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_add,
      NNReal.coe_one, mul_assoc] using this
  have hH₁g₁ : euclideanNorm
      (fderiv ℝ gradient (leapfrog gradient ε z).1
        (gradient (leapfrog gradient ε z).1)) ≤ A * G₁ := by
    apply (hreg.euclideanNorm_fderiv_gradient_apply_le
      (leapfrog gradient ε z).1
      (gradient (leapfrog gradient ε z).1)).trans
    have := mul_le_mul_of_nonneg_left hgradient₁ hA
    simpa only [A, D, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_add,
      NNReal.coe_one, mul_assoc] using this
  have hH₁p : euclideanNorm
      (fderiv ℝ gradient (leapfrog gradient ε z).1
        (leapfrog gradient ε z).2) ≤ A * Pnext := by
    apply (hreg.euclideanNorm_fderiv_gradient_apply_le
      (leapfrog gradient ε z).1 (leapfrog gradient ε z).2).trans
    have := mul_le_mul_of_nonneg_left hpNext hA
    simpa only [A, D, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_add,
      NNReal.coe_one, mul_assoc] using this
  have hH₀v : euclideanNorm (fderiv ℝ gradient z.1 v.1) ≤
      A * (D * ‖v‖) := by
    apply (hreg.euclideanNorm_fderiv_gradient_apply_le z.1 v.1).trans
    have := mul_le_mul_of_nonneg_left hv₁ hA
    simpa only [A, D, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_add,
      NNReal.coe_one, mul_assoc] using this
  simp only [leapfrog] at htrap hgradient₁ hpNext hforce hH₁g₁ hH₁p
  apply (hreg.abs_fderiv_oneStepEnergyDefect_apply_le ε z v).trans
  have ht₁ : euclideanNorm
        ((gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)) - gradient z.1) -
          (ε / 2) •
            (fderiv ℝ gradient z.1 (halfKick gradient ε z.1 z.2) +
              fderiv ℝ gradient
                (drift ε z.1 (halfKick gradient ε z.1 z.2))
                (halfKick gradient ε z.1 z.2))) * euclideanNorm v.1 ≤
      (T * |ε|) * (D * ‖v‖) := by
    (gcongr; exact euclideanNorm_nonneg _)
  have ht₂ : (|ε| ^ 2 / 4) *
        (euclideanNorm
            (fderiv ℝ gradient
              (drift ε z.1 (halfKick gradient ε z.1 z.2))
              (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)))) +
          euclideanNorm (fderiv ℝ gradient z.1 (gradient z.1))) *
        euclideanNorm v.1 ≤
      (|ε| ^ 2 / 4) * (A * G₁ + A * G₀) * (D * ‖v‖) := by
    (gcongr; exact euclideanNorm_nonneg _)
  have ht₃ : (|ε| ^ 2 / 2) *
        euclideanNorm
          (fderiv ℝ gradient
            (drift ε z.1 (halfKick gradient ε z.1 z.2))
            (halfKick gradient ε
              (drift ε z.1 (halfKick gradient ε z.1 z.2))
              (halfKick gradient ε z.1 z.2))) *
        euclideanNorm
          (v.2 - (ε / 2) • fderiv ℝ gradient z.1 v.1) ≤
      (|ε| ^ 2 / 2) * (A * Pnext) *
        (D * (1 + A / 2) * ‖v‖) := by
    (gcongr; exact euclideanNorm_nonneg _)
  have ht₄ : (|ε| / 2) *
        euclideanNorm
          (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)) - gradient z.1) *
        euclideanNorm v.2 ≤
      (|ε| / 2) * (F * |ε|) * (D * ‖v‖) := by
    (gcongr; exact euclideanNorm_nonneg _)
  have ht₅ : (|ε| ^ 2 / 4) *
        euclideanNorm
          (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)) - gradient z.1) *
        euclideanNorm (fderiv ℝ gradient z.1 v.1) ≤
      (|ε| ^ 2 / 4) * (F * |ε|) * (A * (D * ‖v‖)) := by
    (gcongr; exact euclideanNorm_nonneg _)
  have ht₅' : (|ε| ^ 2 / 4) *
        euclideanNorm
          (gradient (drift ε z.1 (halfKick gradient ε z.1 z.2)) - gradient z.1) *
        euclideanNorm (fderiv ℝ gradient z.1 v.1) ≤
      (|ε| ^ 2 / 4) * F * (A * (D * ‖v‖)) := by
    apply ht₅.trans
    gcongr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hε hF
  calc
    _ ≤ (T * |ε|) * (D * ‖v‖) +
        (|ε| ^ 2 / 4) * (A * G₁ + A * G₀) * (D * ‖v‖) +
        (|ε| ^ 2 / 2) * (A * Pnext) *
          (D * (1 + A / 2) * ‖v‖) +
        (|ε| / 2) * (F * |ε|) * (D * ‖v‖) +
        (|ε| ^ 2 / 4) * F * (A * (D * ‖v‖)) := by
          linarith [ht₁, ht₂, ht₃, ht₄, ht₅']
    _ = |ε| *
        (T * D + |ε| *
          (A * (G₁ + G₀) * D / 4 +
            A * Pnext * (D * (1 + A / 2)) / 2 +
            F * D / 2 + F * A * D / 4)) * ‖v‖ := by ring

/-- Cancellation-friendly form of the Hamiltonian variation generated by
changing leapfrog's step size. The first term is a gradient linearization
remainder; every other term carries an explicit power of the step size. -/
theorem energyDirectionalDerivative_leapfrog_tangent_eq
    (gradient : Position ι → Position ι) (ε : ℝ) (z : PhaseSpace ι) :
    let pHalf := halfKick gradient ε z.1 z.2
    let qNext := drift ε z.1 pHalf
    let qDot := pHalf - (ε / 2) • gradient z.1
    let gradientDiff := gradient qNext - gradient z.1
    let hessianAction := fderiv ℝ gradient qNext qDot
    energyDirectionalDerivative gradient (leapfrog gradient ε z)
        (leapfrogStepSizeTangent gradient ε z) =
      (1 / 2 : ℝ) * euclideanInner pHalf
        (gradientDiff - ε • hessianAction) +
      (ε / 4) * euclideanInner (gradient qNext) gradientDiff +
      (ε ^ 2 / 4) * euclideanInner (gradient qNext) hessianAction := by
  dsimp [energyDirectionalDerivative, leapfrogStepSizeTangent,
    leapfrog, halfKick, drift]
  simp only [euclideanInner_sub_left, euclideanInner_sub_right,
    euclideanInner_smul_left, euclideanInner_smul_right,
    euclideanInner_comm]
  ring

/-- Differentiating the Hamiltonian along the step-size-parametrized
leapfrog update gives the Hamiltonian directional derivative applied to the
explicit leapfrog step-size tangent. -/
theorem RegularPotential.hasDerivAt_energy_leapfrog_stepSize
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z : PhaseSpace ι) :
    HasDerivAt (fun t : ℝ ↦ energy potential (leapfrog gradient t z))
      (energyDirectionalDerivative gradient (leapfrog gradient ε z)
        (leapfrogStepSizeTangent gradient ε z)) ε := by
  let L : ℝ → PhaseSpace ι := fun t ↦ leapfrog gradient t z
  let V : PhaseSpace ι := leapfrogStepSizeTangent gradient ε z
  have hL : HasDerivAt L V ε := by
    simpa only [L, V] using hreg.hasDerivAt_leapfrog_stepSize ε z
  have hq : HasDerivAt (fun t ↦ (L t).1) V.1 ε := by
    simpa using
      ((hasDerivAt_const (x := ε)
        (ContinuousLinearMap.fst ℝ (Position ι) (Momentum ι))).clm_apply hL)
  have hp : HasDerivAt (fun t ↦ (L t).2) V.2 ε := by
    simpa using
      ((hasDerivAt_const (x := ε)
        (ContinuousLinearMap.snd ℝ (Position ι) (Momentum ι))).clm_apply hL)
  have hpotential : HasDerivAt (fun t ↦ potential (L t).1)
      (euclideanInner (gradient (L ε).1) V.1) ε := by
    have hcomp :=
      (hreg.contDiff_two.differentiable
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (L ε).1).hasFDerivAt.comp_hasDerivAt ε hq
    rw [hreg.fderiv_apply] at hcomp
    exact hcomp
  have hkinetic : HasDerivAt (fun t ↦ kineticEnergy (L t).2)
      (euclideanInner (L ε).2 V.2) ε := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i hi ↦ ((hasDerivAt_pi.mp hp i).pow 2))
    have hhalf := hsum.const_mul (1 / 2 : ℝ)
    unfold kineticEnergy
    apply hhalf.congr_deriv
    simp only [euclideanInner, Finset.mul_sum]
    simp
    ring_nf
  change HasDerivAt
    ((fun t ↦ potential (L t).1) + fun t ↦ kineticEnergy (L t).2)
      (energyDirectionalDerivative gradient (L ε) V) ε
  unfold energyDirectionalDerivative
  exact hpotential.add hkinetic

/-- Arbitrary-step derivative formula for the centered one-step energy
defect. This is the integrand used when comparing two defects by the
fundamental theorem of calculus in the step-size variable. -/
theorem RegularPotential.hasDerivAt_oneStepEnergyDefect_stepSize
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z : PhaseSpace ι) :
    HasDerivAt (fun t : ℝ ↦ oneStepEnergyDefect potential gradient t z)
      (energyDirectionalDerivative gradient (leapfrog gradient ε z)
        (leapfrogStepSizeTangent gradient ε z)) ε := by
  unfold oneStepEnergyDefect
  exact (hreg.hasDerivAt_energy_leapfrog_stepSize ε z).sub_const _

/-- For a fixed phase point, the one-step defect is continuously
differentiable in the step-size parameter under `C²` potential regularity. -/
theorem RegularPotential.contDiff_one_oneStepEnergyDefect_stepSize
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z : PhaseSpace ι) :
    ContDiff ℝ 1 (fun ε : ℝ ↦ oneStepEnergyDefect potential gradient ε z) := by
  have hpotential : ContDiff ℝ 1 potential :=
    hreg.contDiff_two.of_le (by norm_num)
  have hgradient : ContDiff ℝ 1 gradient := hreg.contDiff_one_gradient
  unfold oneStepEnergyDefect energy kineticEnergy leapfrog halfKick drift
  fun_prop

/-- A paired one-step defect is exactly the step-size integral of the
difference of the two explicit Hamiltonian-variation integrands. This turns
the remaining theorem into a compact-uniform bound on a concrete expression
containing only the gradient and its first derivative. -/
theorem RegularPotential.intervalIntegral_pairedOneStepEnergyDefectDerivative
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) (z₁ z₂ : PhaseSpace ι) :
    (∫ t in (0 : ℝ)..ε,
      (energyDirectionalDerivative gradient (leapfrog gradient t z₁)
          (leapfrogStepSizeTangent gradient t z₁) -
        energyDirectionalDerivative gradient (leapfrog gradient t z₂)
          (leapfrogStepSizeTangent gradient t z₂))) =
      oneStepEnergyDefect potential gradient ε z₁ -
        oneStepEnergyDefect potential gradient ε z₂ := by
  let F : ℝ → ℝ := fun t ↦
    oneStepEnergyDefect potential gradient t z₁ -
      oneStepEnergyDefect potential gradient t z₂
  let F' : ℝ → ℝ := fun t ↦
    energyDirectionalDerivative gradient (leapfrog gradient t z₁)
        (leapfrogStepSizeTangent gradient t z₁) -
      energyDirectionalDerivative gradient (leapfrog gradient t z₂)
        (leapfrogStepSizeTangent gradient t z₂)
  have hFderiv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    exact (hreg.hasDerivAt_oneStepEnergyDefect_stepSize t z₁).sub
      (hreg.hasDerivAt_oneStepEnergyDefect_stepSize t z₂)
  have hderiv : deriv F = F' := by
    funext t
    exact (hFderiv t).deriv
  have hFcontDiff : ContDiff ℝ 1 F :=
    (hreg.contDiff_one_oneStepEnergyDefect_stepSize z₁).sub
      (hreg.contDiff_one_oneStepEnergyDefect_stepSize z₂)
  have hF'cont : Continuous F' := by
    rw [← hderiv]
    exact hFcontDiff.continuous_deriv (by norm_num)
  have hFTC := intervalIntegral.integral_deriv_eq_sub'
    (a := (0 : ℝ)) (b := ε) F hderiv
      (fun t ht ↦ (hFderiv t).differentiableAt) hF'cont.continuousOn
  simpa [F, F'] using hFTC

/-- Compact-uniform local Lipschitz control of the explicit step-size
Hamiltonian-variation integrand. Its coefficient vanishes as the step size
tends to zero. This is now the smallest outstanding `C²` calculus statement. -/
def LocallyUniformVanishingPairedStepSizeEnergyVariation
    (gradient : Position ι → Position ι) : Prop :=
  ∀ R : ℝ, ∀ relativeRate : ℝ, 0 < relativeRate →
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → |ε| < εbar →
      ∀ z₁ z₂ : PhaseSpace ι,
        euclideanPhaseSize z₁ ≤ R → euclideanPhaseSize z₂ ≤ R →
        |energyDirectionalDerivative gradient (leapfrog gradient ε z₁)
              (leapfrogStepSizeTangent gradient ε z₁) -
            energyDirectionalDerivative gradient (leapfrog gradient ε z₂)
              (leapfrogStepSizeTangent gradient ε z₂)| ≤
          relativeRate *
            (euclideanNorm (z₁.1 - z₂.1) +
              euclideanNorm (z₁.2 - z₂.2))

/-- One leapfrog step follows the Hamiltonian vector field to first order at
zero step size, so its Hamiltonian has zero first step-size derivative. This
is the algebraic cancellation underlying the remaining uniform consistency
estimate. -/
theorem RegularPotential.hasDerivAt_energy_leapfrog_zero
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z : PhaseSpace ι) :
    HasDerivAt (fun ε : ℝ ↦ energy potential (leapfrog gradient ε z)) 0 0 := by
  let Q : ℝ → Position ι := fun ε ↦ (leapfrog gradient ε z).1
  let P : ℝ → Momentum ι := fun ε ↦ (leapfrog gradient ε z).2
  have hgradient : Differentiable ℝ gradient :=
    hreg.contDiff_one_gradient.differentiable (by norm_num)
  have hQ : HasDerivAt Q z.2 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    dsimp [Q, leapfrog, halfKick, drift]
    have h := ((hasDerivAt_const (x := (0 : ℝ)) (z.1 i)).add
      ((hasDerivAt_id (0 : ℝ)).mul
        ((hasDerivAt_const (x := (0 : ℝ)) (z.2 i)).sub
          (((hasDerivAt_id (0 : ℝ)).div_const 2).mul_const
            (gradient z.1 i)))))
    convert h using 1
    · funext x
      rfl
    · norm_num
  have hP : HasDerivAt P (-gradient z.1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have hgradQ : DifferentiableAt ℝ (fun ε : ℝ ↦ gradient (Q ε) i) 0 := by
      have hcomp : DifferentiableAt ℝ (gradient ∘ Q) 0 :=
        (hgradient (Q 0)).comp 0 hQ.differentiableAt
      exact (differentiableAt_apply i (gradient (Q 0))).comp 0 hcomp
    have hfirst := ((hasDerivAt_id (0 : ℝ)).div_const 2).mul_const
      (gradient z.1 i)
    have hsecond := ((hasDerivAt_id (0 : ℝ)).div_const 2).mul
      hgradQ.hasDerivAt
    have htotal := ((hasDerivAt_const (x := (0 : ℝ)) (z.2 i)).sub hfirst).sub hsecond
    dsimp [P, Q, leapfrog, halfKick, drift] at htotal ⊢
    convert htotal using 1
    · funext x
      rfl
    · simp
      ring
  have hQ0 : Q 0 = z.1 := by
    simp [Q, leapfrog, halfKick, drift]
  have hP0 : P 0 = z.2 := by
    simp [P, leapfrog, halfKick, drift]
  have hpotential : HasDerivAt (potential ∘ Q)
      (euclideanInner (gradient z.1) z.2) 0 := by
    have hcomp :=
      (hreg.contDiff_two.differentiable
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (Q 0)).hasFDerivAt.comp_hasDerivAt 0 hQ
    rw [hreg.fderiv_apply, hQ0] at hcomp
    exact hcomp
  have hkinetic : HasDerivAt (fun ε : ℝ ↦ kineticEnergy (P ε))
      (-euclideanInner (gradient z.1) z.2) 0 := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i hi ↦ ((hasDerivAt_pi.mp hP i).pow 2))
    have hhalf := hsum.const_mul (1 / 2 : ℝ)
    unfold kineticEnergy
    apply hhalf.congr_deriv
    rw [hP0]
    dsimp [P]
    simp only [euclideanInner, Finset.mul_sum]
    simp [mul_comm]
    ring_nf
  change HasDerivAt
    ((potential ∘ Q) + fun ε : ℝ ↦ kineticEnergy (P ε)) 0 0
  exact (hpotential.add hkinetic).congr_deriv (add_neg_cancel _)

/-- The explicit arbitrary-step Hamiltonian-variation integrand vanishes at
zero step size. -/
@[simp]
theorem RegularPotential.energyDirectionalDerivative_leapfrog_tangent_zero
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z : PhaseSpace ι) :
    energyDirectionalDerivative gradient (leapfrog gradient 0 z)
      (leapfrogStepSizeTangent gradient 0 z) = 0 :=
  (hreg.hasDerivAt_energy_leapfrog_stepSize 0 z).unique
    (hreg.hasDerivAt_energy_leapfrog_zero z)

/-- The centered one-step energy defect therefore has zero first derivative
with respect to step size at zero. -/
theorem RegularPotential.hasDerivAt_oneStepEnergyDefect_zero
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z : PhaseSpace ι) :
    HasDerivAt (fun ε : ℝ ↦ oneStepEnergyDefect potential gradient ε z) 0 0 := by
  unfold oneStepEnergyDefect
  exact (hreg.hasDerivAt_energy_leapfrog_zero z).sub_const _

/-- Pointwise, the one-step Hamiltonian defect is little-o of the step size.
The unresolved general theorem needs the stronger statement after taking the
phase derivative, uniformly on bounded phase families. -/
theorem RegularPotential.isLittleO_oneStepEnergyDefect
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (z : PhaseSpace ι) :
    (fun ε : ℝ ↦ oneStepEnergyDefect potential gradient ε z) =o[nhds 0]
      (fun ε : ℝ ↦ ε) := by
  simpa using (hreg.hasDerivAt_oneStepEnergyDefect_zero z).isLittleO

/-- Derivative-level form of the remaining local calculus estimate.  The
phase derivative of the one-step defect is `o(|ε|)` uniformly on ambient
phase balls. -/
def LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) : Prop :=
  ∀ R : ℝ, ∀ relativeRate : ℝ, 0 < relativeRate →
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → |ε| < εbar →
      ∀ z : PhaseSpace ι, ‖z‖ ≤ R →
        ‖fderiv ℝ (oneStepEnergyDefect potential gradient ε) z‖ ≤
          relativeRate * |ε|

set_option maxHeartbeats 800000 in
/-- Every `C²` regular potential satisfies the locally uniform relative
one-step energy-defect estimate.  The proof uses Hessian continuity only in
the trapezoidal-force cancellation; all remaining terms have an explicit
quadratic step-size factor. -/
theorem RegularPotential.locallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β) :
    LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
      potential gradient := by
  intro R relativeRate hrelativeRate
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let S : ℝ := 2 * D * max R 0
  let G : ℝ := (β : ℝ) * S + euclideanNorm (gradient 0)
  let P : ℝ := S + G
  let G₁ : ℝ := G + (β : ℝ) * P
  let N : ℝ := P + G₁
  let F : ℝ := (β : ℝ) * P
  let A : ℝ := D *
    (((β * (Fintype.card ι + 1 : NNReal) : NNReal) : ℝ))
  let C : ℝ :=
    A * (G₁ + G) * D / 4 +
      A * N * (D * (1 + A / 2)) / 2 +
      F * D / 2 + F * A * D / 4
  let η : ℝ := relativeRate / (4 * D ^ 2 * (P + 1))
  have hD : 0 < D := by dsimp [D]; positivity
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hG : 0 ≤ G := by
    dsimp [G]
    exact add_nonneg (mul_nonneg β.coe_nonneg hS) (euclideanNorm_nonneg _)
  have hP : 0 ≤ P := add_nonneg hS hG
  have hG₁ : 0 ≤ G₁ := by
    dsimp [G₁]
    exact add_nonneg hG (mul_nonneg β.coe_nonneg hP)
  have hN : 0 ≤ N := add_nonneg hP hG₁
  have hF : 0 ≤ F := mul_nonneg β.coe_nonneg hP
  have hA : 0 ≤ A := by dsimp [A, D]; positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hPone : 0 < P + 1 := by linarith
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨εtrap, hεtrap, htrap⟩ :=
    hreg.exists_uniform_leapfrog_trapezoidalForceRemainder_le S hη
  let εquad : ℝ := relativeRate / (2 * (C + 1))
  have hεquad : 0 < εquad := by
    dsimp [εquad]
    positivity
  let εbar : ℝ := min εtrap εquad
  have hεbar : 0 < εbar := lt_min hεtrap hεquad
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z hz
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hzphase : euclideanPhaseSize z ≤ S := by
    have hq : euclideanNorm z.1 ≤ D * ‖z.1‖ := by
      have h := euclideanNorm_sub_le_card_succ_mul_dist z.1 0
      simpa only [sub_zero, dist_zero_right, D] using h
    have hp : euclideanNorm z.2 ≤ D * ‖z.2‖ := by
      have h := euclideanNorm_sub_le_card_succ_mul_dist z.2 0
      simpa only [sub_zero, dist_zero_right, D] using h
    have hqnorm : ‖z.1‖ ≤ ‖z‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    have hpnorm : ‖z.2‖ ≤ ‖z‖ := by
      rw [Prod.norm_def]
      exact le_max_right _ _
    unfold euclideanPhaseSize
    calc
      euclideanNorm z.1 + euclideanNorm z.2 ≤
          D * ‖z.1‖ + D * ‖z.2‖ := add_le_add hq hp
      _ ≤ D * ‖z‖ + D * ‖z‖ := by gcongr
      _ ≤ 2 * D * max R 0 := by
        have hzmax : ‖z‖ ≤ max R 0 := hz.trans (le_max_left _ _)
        nlinarith [hD.le]
      _ = S := rfl
  let pHalf := halfKick gradient ε z.1 z.2
  let qNext := drift ε z.1 pHalf
  let pNext := halfKick gradient ε qNext pHalf
  have hq : euclideanNorm z.1 ≤ S :=
    (euclideanNorm_fst_le_phaseSize z).trans hzphase
  have hp : euclideanNorm z.2 ≤ S := by
    unfold euclideanPhaseSize at hzphase
    nlinarith [euclideanNorm_nonneg z.1]
  have hg : euclideanNorm (gradient z.1) ≤ G := by
    apply (hreg.euclideanNorm_gradient_le z.1).trans
    dsimp [G]
    gcongr
  have hpHalf : euclideanNorm pHalf ≤ P := by
    dsimp [pHalf, halfKick]
    apply (euclideanNorm_sub_le z.2 ((ε / 2) • gradient z.1)).trans
    rw [euclideanNorm_smul]
    have habsHalf : |ε / 2| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg ε]
    dsimp [P]
    nlinarith [euclideanNorm_nonneg z.2, euclideanNorm_nonneg (gradient z.1)]
  have hqdiff : euclideanNorm (qNext - z.1) ≤ |ε| * P := by
    have heq : qNext - z.1 = ε • pHalf := by
      dsimp [qNext, drift]
      abel
    rw [heq, euclideanNorm_smul]
    exact mul_le_mul_of_nonneg_left hpHalf (abs_nonneg ε)
  have hforce : euclideanNorm (gradient qNext - gradient z.1) ≤
      F * |ε| := by
    apply (hreg.euclideanNorm_gradient_sub_le qNext z.1).trans
    dsimp [F]
    nlinarith [β.coe_nonneg, abs_nonneg ε]
  have hgNext : euclideanNorm (gradient qNext) ≤ G₁ := by
    have htri := euclideanNorm_add_le
      (gradient qNext - gradient z.1) (gradient z.1)
    have heq : gradient qNext - gradient z.1 + gradient z.1 =
        gradient qNext := by abel
    rw [heq] at htri
    have habsP : |ε| * P ≤ P := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hεone hP
    calc
      euclideanNorm (gradient qNext) ≤
          euclideanNorm (gradient qNext - gradient z.1) +
            euclideanNorm (gradient z.1) := htri
      _ ≤ F * |ε| + G := add_le_add hforce hg
      _ ≤ (β : ℝ) * P + G := by
        dsimp [F]
        have hb : (β : ℝ) * P * |ε| ≤ (β : ℝ) * P := by
          calc
          (β : ℝ) * P * |ε| = (β : ℝ) * (|ε| * P) := by ring
          _ ≤ (β : ℝ) * P :=
            mul_le_mul_of_nonneg_left habsP β.coe_nonneg
        exact add_le_add hb le_rfl
      _ = G₁ := by dsimp [G₁]; ring
  have hpNext : euclideanNorm pNext ≤ N := by
    dsimp [pNext, halfKick]
    apply (euclideanNorm_sub_le pHalf ((ε / 2) • gradient qNext)).trans
    rw [euclideanNorm_smul]
    have habsHalf : |ε / 2| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        |ε| / 2 ≤ 1 / 2 := div_le_div_of_nonneg_right hεone (by norm_num)
        _ ≤ 1 := by norm_num
    have hscaled : |ε / 2| * euclideanNorm (gradient qNext) ≤ G₁ := by
      calc
        |ε / 2| * euclideanNorm (gradient qNext) ≤
            1 * G₁ := mul_le_mul habsHalf hgNext
              (euclideanNorm_nonneg _) zero_le_one
        _ = G₁ := one_mul _
    exact (add_le_add hpHalf hscaled).trans_eq (by rfl)
  have htrapAmbient := htrap hεone
    (hε.trans_le (min_le_left _ _)) z hzphase
  let T : ℝ := D * (3 / 2 : ℝ) * η * P
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have htrapEuclidean : euclideanNorm
      ((gradient qNext - gradient z.1) -
        (ε / 2) •
          (fderiv ℝ gradient z.1 pHalf +
            fderiv ℝ gradient qNext pHalf)) ≤ T * |ε| := by
    have heuc := euclideanNorm_sub_le_card_succ_mul_dist
      ((gradient qNext - gradient z.1) -
        (ε / 2) •
          (fderiv ℝ gradient z.1 pHalf +
            fderiv ℝ gradient qNext pHalf)) 0
    simp only [sub_zero, dist_zero_right] at heuc
    apply heuc.trans
    have hpAmbient : ‖pHalf‖ ≤ P := by
      have hle : ‖pHalf‖ ≤ euclideanNorm pHalf := by
        simpa only [dist_zero_right, sub_zero] using
          dist_le_euclideanNorm_sub pHalf 0
      exact hle.trans hpHalf
    have htrapAmbient' :
        ‖(gradient qNext - gradient z.1) -
          (ε / 2) •
            (fderiv ℝ gradient z.1 pHalf +
              fderiv ℝ gradient qNext pHalf)‖ ≤
          3 / 2 * η * |ε| * ‖pHalf‖ := by
      simpa only [qNext, pHalf, leapfrog] using htrapAmbient
    apply (mul_le_mul_of_nonneg_left htrapAmbient' hD.le).trans
    have hcoef : 0 ≤ D * (3 / 2 * η * |ε|) :=
      mul_nonneg hD.le
        (mul_nonneg (mul_nonneg (by norm_num) hη.le) (abs_nonneg ε))
    have hmul := mul_le_mul_of_nonneg_left hpAmbient hcoef
    calc
      D * (3 / 2 * η * |ε| * ‖pHalf‖) =
          (D * (3 / 2 * η * |ε|)) * ‖pHalf‖ := by
            simp only [mul_assoc]
      _ ≤ (D * (3 / 2 * η * |ε|)) * P := hmul
      _ = T * |ε| := by dsimp [T]; ring
  have hlead : T * D ≤ (3 / 8 : ℝ) * relativeRate := by
    have hden : 0 < 4 * D ^ 2 * (P + 1) :=
      mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hD)) hPone
    have hcancel : η * (4 * D ^ 2 * (P + 1)) = relativeRate := by
      change (relativeRate / (4 * D ^ 2 * (P + 1))) *
        (4 * D ^ 2 * (P + 1)) = relativeRate
      exact div_mul_cancel₀ relativeRate hden.ne'
    have hPP : η * P ≤ η * (P + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hη.le
    calc
      T * D = (3 / 2 : ℝ) * D ^ 2 * (η * P) := by dsimp [T]; ring
      _ ≤ (3 / 2 : ℝ) * D ^ 2 * (η * (P + 1)) :=
        mul_le_mul_of_nonneg_left hPP
          (mul_nonneg (by norm_num) (sq_nonneg D))
      _ = (3 / 8 : ℝ) * (η * (4 * D ^ 2 * (P + 1))) := by ring
      _ = (3 / 8 : ℝ) * relativeRate := by rw [hcancel]
  have hquadCut : |ε| * C ≤ relativeRate / 2 := by
    have hsmall : |ε| < εquad := hε.trans_le (min_le_right _ _)
    dsimp [εquad] at hsmall
    have hmul := (lt_div_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < C + 1))).mp hsmall
    nlinarith [abs_nonneg ε]
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hrelativeRate.le (abs_nonneg ε))
  intro v
  rw [Real.norm_eq_abs]
  have hv := hreg.abs_fderiv_oneStepEnergyDefect_apply_le_bounded
    z v hεone hT hG hG₁ hN hF htrapEuclidean hg hgNext
    (by simpa only [pNext, qNext, pHalf, leapfrog] using hpNext)
    (by simpa only [qNext, leapfrog] using hforce)
  apply hv.trans
  dsimp only [C] at hquadCut
  dsimp only [D, A, C] at hv ⊢
  have habsNorm : 0 ≤ |ε| * ‖v‖ :=
    mul_nonneg (abs_nonneg ε) (norm_nonneg v)
  nlinarith

/-- Local one-step form of the remaining energy analysis.  On every bounded
phase family, the Lipschitz coefficient of one leapfrog energy defect,
divided by the step size, can be made arbitrarily small.  Existing phase
stability is enough to telescope this property over fixed horizons. -/
def LocallyUniformVanishingPerTimePairedOneStepEnergyError
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) : Prop :=
  ∀ R : ℝ, ∀ relativeRate : ℝ, 0 < relativeRate →
    ∃ εbar > 0, ∀ {ε : ℝ}, |ε| ≤ 1 → |ε| < εbar →
      ∀ z₁ z₂ : PhaseSpace ι,
        euclideanPhaseSize z₁ ≤ R → euclideanPhaseSize z₂ ≤ R →
        |(energy potential (leapfrog gradient ε z₁) - energy potential z₁) -
            (energy potential (leapfrog gradient ε z₂) - energy potential z₂)| ≤
          relativeRate * |ε| *
            (euclideanNorm (z₁.1 - z₂.1) +
              euclideanNorm (z₁.2 - z₂.2))

/-- Integrating a vanishing paired bound for the explicit step-size
variation proves the paired one-step energy-defect estimate. -/
theorem LocallyUniformVanishingPairedStepSizeEnergyVariation.toPaired
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (hvariation : LocallyUniformVanishingPairedStepSizeEnergyVariation
      gradient) :
    LocallyUniformVanishingPerTimePairedOneStepEnergyError
      potential gradient := by
  intro R relativeRate hrelativeRate
  obtain ⟨εbar, hεbar, hbound⟩ :=
    hvariation R relativeRate hrelativeRate
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z₁ z₂ hz₁ hz₂
  let separation : ℝ :=
    euclideanNorm (z₁.1 - z₂.1) + euclideanNorm (z₁.2 - z₂.2)
  let integrand : ℝ → ℝ := fun t ↦
    energyDirectionalDerivative gradient (leapfrog gradient t z₁)
        (leapfrogStepSizeTangent gradient t z₁) -
      energyDirectionalDerivative gradient (leapfrog gradient t z₂)
        (leapfrogStepSizeTangent gradient t z₂)
  have hintegrand : ∀ t ∈ Set.uIoc (0 : ℝ) ε,
      ‖integrand t‖ ≤ relativeRate * separation := by
    intro t ht
    have ht' : t ∈ Set.uIcc (0 : ℝ) ε := Set.uIoc_subset_uIcc ht
    have htε : |t| ≤ |ε| := by
      simpa only [sub_zero] using Set.abs_sub_left_of_mem_uIcc ht'
    have htone : |t| ≤ 1 := htε.trans hεone
    have htbar : |t| < εbar := htε.trans_lt hε
    rw [Real.norm_eq_abs]
    exact hbound htone htbar z₁ z₂ hz₁ hz₂
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const
    hintegrand
  have hidentity :=
    hreg.intervalIntegral_pairedOneStepEnergyDefectDerivative ε z₁ z₂
  rw [hidentity, Real.norm_eq_abs, sub_zero] at hintegral
  dsimp [separation] at hintegral ⊢
  apply hintegral.trans_eq
  ring

/-- Uniform smallness of the phase derivative implies the paired one-step
estimate by the mean-value theorem. -/
theorem LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv.toPaired
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (hderiv : LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
      potential gradient) :
    LocallyUniformVanishingPerTimePairedOneStepEnergyError
      potential gradient := by
  intro R relativeRate hrelativeRate
  obtain ⟨εbar, hεbar, hbound⟩ := hderiv R relativeRate hrelativeRate
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z₁ z₂ hz₁ hz₂
  have hambient (z : PhaseSpace ι) : ‖z‖ ≤ euclideanPhaseSize z := by
    rw [Prod.norm_def]
    apply max_le
    · exact (show ‖z.1‖ ≤ euclideanNorm z.1 by
        simpa only [dist_zero_right, sub_zero] using
          dist_le_euclideanNorm_sub z.1 0) |>.trans
        (euclideanNorm_fst_le_phaseSize z)
    · have hp : ‖z.2‖ ≤ euclideanNorm z.2 := by
        simpa only [dist_zero_right, sub_zero] using
          dist_le_euclideanNorm_sub z.2 0
      unfold euclideanPhaseSize
      exact hp.trans (le_add_of_nonneg_left (euclideanNorm_nonneg _))
  have hz₁ball : z₁ ∈ Metric.closedBall (0 : PhaseSpace ι) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hambient z₁).trans hz₁
  have hz₂ball : z₂ ∈ Metric.closedBall (0 : PhaseSpace ι) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hambient z₂).trans hz₂
  have hdefect : ContDiff ℝ 1 (oneStepEnergyDefect potential gradient ε) := by
    unfold oneStepEnergyDefect
    exact (hreg.contDiff_one_energy.comp
      (hreg.contDiff_one_leapfrog ε)).sub hreg.contDiff_one_energy
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le
    (f := oneStepEnergyDefect potential gradient ε)
    (s := Metric.closedBall (0 : PhaseSpace ι) R)
    (x := z₂) (y := z₁) (C := relativeRate * |ε|)
    (fun z hz => hdefect.differentiable (by norm_num) z)
    (fun z hz => hbound hεone hε z (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz))
    (convex_closedBall 0 R) hz₂ball hz₁ball
  have hphaseSub : ‖z₁ - z₂‖ ≤
      euclideanNorm (z₁.1 - z₂.1) + euclideanNorm (z₁.2 - z₂.2) := by
    rw [Prod.norm_def]
    apply max_le
    · exact (show ‖z₁.1 - z₂.1‖ ≤ euclideanNorm (z₁.1 - z₂.1) by
        have h := dist_le_euclideanNorm_sub (z₁.1 - z₂.1) 0
        simpa only [dist_zero_right, sub_zero] using h) |>.trans
        (le_add_of_nonneg_right (euclideanNorm_nonneg _))
    · exact (show ‖z₁.2 - z₂.2‖ ≤ euclideanNorm (z₁.2 - z₂.2) by
        have h := dist_le_euclideanNorm_sub (z₁.2 - z₂.2) 0
        simpa only [dist_zero_right, sub_zero] using h) |>.trans
        (le_add_of_nonneg_left (euclideanNorm_nonneg _))
  unfold oneStepEnergyDefect at hmean
  rw [Real.norm_eq_abs] at hmean
  exact hmean.trans (mul_le_mul_of_nonneg_left hphaseSub
    (mul_nonneg hrelativeRate.le (abs_nonneg ε)))

/-- Conversely, the paired one-step estimate bounds the phase derivative.
Thus, in finite-dimensional phase space, the paired and derivative-level
interfaces express the same local `o(|ε|)` content. -/
theorem LocallyUniformVanishingPerTimePairedOneStepEnergyError.toFDeriv
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hone : LocallyUniformVanishingPerTimePairedOneStepEnergyError
      potential gradient) :
    LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
      potential gradient := by
  intro R relativeRate hrelativeRate
  let D : ℝ := (Fintype.card ι : ℝ) + 1
  let localRate : ℝ := relativeRate / (2 * D)
  let phaseRadius : ℝ := 2 * D * (max R 0 + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hlocalRate : 0 < localRate :=
    div_pos hrelativeRate (mul_pos (by norm_num) hD)
  obtain ⟨εbar, hεbar, hpair⟩ := hone phaseRadius localRate hlocalRate
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεone hε z hz
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hphaseSize_of_norm (y : PhaseSpace ι) :
      euclideanPhaseSize y ≤ 2 * D * ‖y‖ := by
    have hq : euclideanNorm y.1 ≤ D * ‖y.1‖ := by
      have h := euclideanNorm_sub_le_card_succ_mul_dist y.1 0
      simpa only [sub_zero, dist_zero_right, D] using h
    have hp : euclideanNorm y.2 ≤ D * ‖y.2‖ := by
      have h := euclideanNorm_sub_le_card_succ_mul_dist y.2 0
      simpa only [sub_zero, dist_zero_right, D] using h
    have hqnorm : ‖y.1‖ ≤ ‖y‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    have hpnorm : ‖y.2‖ ≤ ‖y‖ := by
      rw [Prod.norm_def]
      exact le_max_right _ _
    unfold euclideanPhaseSize
    calc
      euclideanNorm y.1 + euclideanNorm y.2 ≤
          D * ‖y.1‖ + D * ‖y.2‖ := add_le_add hq hp
      _ ≤ D * ‖y‖ + D * ‖y‖ := by gcongr
      _ = 2 * D * ‖y‖ := by ring
  have hzphase : euclideanPhaseSize z ≤ phaseRadius := by
    apply (hphaseSize_of_norm z).trans
    dsimp [phaseRadius]
    have hzmax : ‖z‖ ≤ max R 0 + 1 := by
      calc
        ‖z‖ ≤ R := hz
        _ ≤ max R 0 := le_max_left _ _
        _ ≤ max R 0 + 1 := by linarith
    gcongr
  apply norm_fderiv_le_of_lip' ℝ
    (mul_nonneg hrelativeRate.le (abs_nonneg ε))
  filter_upwards [Metric.ball_mem_nhds z zero_lt_one] with y hy
  have hynorm : ‖y‖ ≤ max R 0 + 1 := by
    have hdist : ‖y - z‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have htri : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
      have := norm_add_le (y - z) z
      simpa only [sub_add_cancel] using this
    calc
      ‖y‖ ≤ ‖y - z‖ + ‖z‖ := htri
      _ ≤ 1 + R := by linarith
      _ ≤ max R 0 + 1 := by linarith [le_max_left R 0]
  have hyphase : euclideanPhaseSize y ≤ phaseRadius := by
    exact (hphaseSize_of_norm y).trans (by
      dsimp [phaseRadius]
      gcongr)
  have hseparation :
      euclideanNorm (y.1 - z.1) + euclideanNorm (y.2 - z.2) ≤
        2 * D * ‖y - z‖ := by
    have hq : euclideanNorm (y.1 - z.1) ≤ D * ‖y.1 - z.1‖ := by
      have h := euclideanNorm_sub_le_card_succ_mul_dist y.1 z.1
      simpa only [dist_eq_norm, D] using h
    have hp : euclideanNorm (y.2 - z.2) ≤ D * ‖y.2 - z.2‖ := by
      have h := euclideanNorm_sub_le_card_succ_mul_dist y.2 z.2
      simpa only [dist_eq_norm, D] using h
    have hqnorm : ‖y.1 - z.1‖ ≤ ‖y - z‖ := by
      rw [Prod.norm_def]
      exact le_max_left _ _
    have hpnorm : ‖y.2 - z.2‖ ≤ ‖y - z‖ := by
      rw [Prod.norm_def]
      exact le_max_right _ _
    calc
      euclideanNorm (y.1 - z.1) + euclideanNorm (y.2 - z.2) ≤
          D * ‖y.1 - z.1‖ + D * ‖y.2 - z.2‖ := add_le_add hq hp
      _ ≤ D * ‖y - z‖ + D * ‖y - z‖ := by gcongr
      _ = 2 * D * ‖y - z‖ := by ring
  have hpaired := hpair hεone hε y z hyphase hzphase
  unfold oneStepEnergyDefect
  rw [Real.norm_eq_abs]
  apply hpaired.trans
  have hcoefficient : localRate * (2 * D) = relativeRate := by
    dsimp [localRate]
    field_simp
  calc
    localRate * |ε| *
        (euclideanNorm (y.1 - z.1) + euclideanNorm (y.2 - z.2)) ≤
      localRate * |ε| * (2 * D * ‖y - z‖) := by
        gcongr
    _ = relativeRate * |ε| * ‖y - z‖ := by
      rw [← hcoefficient]
      ring

/-- Arbitrary-phase vanishing consistency specializes to shared momentum. -/
theorem LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError.toSharedMomentum
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (h : LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError
      potential gradient) :
    LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyErrorOfSharedMomentum
      potential gradient := by
  intro R T hT relativeRate hrelativeRate
  obtain ⟨εbar, hεbar, hbound⟩ := h R T hT relativeRate hrelativeRate
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε k horizon z₁ z₂ hmomentum hz₁ hz₂
  have hraw := hbound hε k horizon z₁ z₂ hz₁ hz₂
  simpa only [hmomentum, sub_self, euclideanNorm_zero, add_zero] using hraw

/-- A quantitative linear modulus supplies the qualitative vanishing modulus. -/
theorem LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError.toVanishing
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hlinear : LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError
      potential gradient) :
    LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError
      potential gradient := by
  intro R T hT relativeRate hrelativeRate
  obtain ⟨C, hC, hbound⟩ := hlinear R T hT
  let εbar := min 1 (relativeRate / (C + 1))
  have hden : 0 < C + 1 := by linarith
  have hεbar : 0 < εbar :=
    lt_min zero_lt_one (div_pos hrelativeRate hden)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε k horizon z₁ z₂ hz₁ hz₂
  have hεone : |ε| ≤ 1 := hε.le.trans (min_le_left _ _)
  have hεquot : |ε| < relativeRate / (C + 1) :=
    hε.trans_le (min_le_right _ _)
  have hscaled : C * |ε| ≤ relativeRate := by
    have hmul : |ε| * (C + 1) < relativeRate :=
      (lt_div_iff₀ hden).mp hεquot
    nlinarith [abs_nonneg ε]
  exact (hbound hεone k horizon z₁ z₂ hz₁ hz₂).trans
    (mul_le_mul_of_nonneg_right hscaled
      (add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)))

/-- A vanishing per-time one-step paired defect telescopes to signed,
fixed-horizon shared-momentum relative consistency. -/
theorem LocallyUniformVanishingPerTimePairedOneStepEnergyError.toSharedMomentumSigned
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (hone : LocallyUniformVanishingPerTimePairedOneStepEnergyError
      potential gradient) :
    LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyErrorOfSharedMomentum
      potential gradient := by
  intro R T hT relativeRate hrelativeRate
  let E := Real.exp (leapfrogNormStabilityRate β * T)
  let B := E * (R + (2 + (β : ℝ)) * T * euclideanNorm (gradient 0))
  let denom := (T + 1) * (E + 1)
  let localRate := relativeRate / denom
  have hE : 0 < E := Real.exp_pos _
  have hdenom : 0 < denom := by dsimp [denom]; positivity
  have hlocalRate : 0 < localRate := div_pos hrelativeRate hdenom
  obtain ⟨εlocal, hεlocal, hstep⟩ := hone B localRate hlocalRate
  let εbar := min 1 εlocal
  have hεbar : 0 < εbar := lt_min zero_lt_one hεlocal
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε k horizon z₁ z₂ hmomentum hz₁ hz₂
  have hεone : |ε| ≤ 1 := hε.le.trans (min_le_left _ _)
  have hεlocal' : |ε| < εlocal := hε.trans_le (min_le_right _ _)
  have hrateT : localRate * T * E ≤ relativeRate := by
    dsimp [localRate]
    rw [show relativeRate / denom * T * E =
      (relativeRate * (T * E)) / denom by ring]
    apply (div_le_iff₀ hdenom).2
    have hTE : T * E ≤ denom := by
      dsimp [denom]
      nlinarith [hE.le]
    exact mul_le_mul_of_nonneg_left hTE hrelativeRate.le
  have hpositive : ∀ (step : ℝ) (n : ℕ), |step| ≤ 1 →
      |step| < εlocal → (n : ℝ) * |step| ≤ T →
      |(energy potential (leapfrogN gradient step n z₁) - energy potential z₁) -
          (energy potential (leapfrogN gradient step n z₂) - energy potential z₂)| ≤
        relativeRate * euclideanNorm (z₁.1 - z₂.1) := by
    intro step n hstepOne hstepLocal hn
    rw [energy_leapfrogN_sub_eq_sum_step_errors,
      energy_leapfrogN_sub_eq_sum_step_errors,
      ← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    let D := euclideanNorm (z₁.1 - z₂.1) +
      euclideanNorm (z₁.2 - z₂.2)
    have hD : 0 ≤ D := by
      dsimp [D]
      exact add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)
    have hterms :
        (∑ i ∈ Finset.range n,
          |(energy potential (leapfrog gradient step
                (leapfrogN gradient step i z₁)) -
              energy potential (leapfrogN gradient step i z₁)) -
            (energy potential (leapfrog gradient step
                (leapfrogN gradient step i z₂)) -
              energy potential (leapfrogN gradient step i z₂))|) ≤
          ∑ _i ∈ Finset.range n, localRate * |step| * (E * D) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
      have hiT : (i : ℝ) * |step| ≤ T :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hin)
          (abs_nonneg step)).trans hn
      have hsize₁ := leapfrogN_euclideanPhaseSize_le_exp
        hreg hstepOne i hiT z₁
      have hsize₂ := leapfrogN_euclideanPhaseSize_le_exp
        hreg hstepOne i hiT z₂
      have hsep := leapfrogN_euclideanNorm_phaseSub_le_exp
        hreg hstepOne i hiT z₁ z₂
      have hsize₁' : euclideanPhaseSize (leapfrogN gradient step i z₁) ≤ B := by
        apply hsize₁.trans
        dsimp [B, E]
        gcongr
      have hsize₂' : euclideanPhaseSize (leapfrogN gradient step i z₂) ≤ B := by
        apply hsize₂.trans
        dsimp [B, E]
        gcongr
      exact (hstep hstepOne hstepLocal
        (leapfrogN gradient step i z₁) (leapfrogN gradient step i z₂)
        hsize₁' hsize₂').trans
          (mul_le_mul_of_nonneg_left hsep
            (mul_nonneg hlocalRate.le (abs_nonneg step)))
    apply hterms.trans
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hnscaled := mul_le_mul_of_nonneg_left hn hlocalRate.le
    have hcoef : (n : ℝ) * (localRate * |step| * (E * D)) ≤
        (localRate * T * E) * D := by
      calc
        (n : ℝ) * (localRate * |step| * (E * D)) =
            (localRate * ((n : ℝ) * |step|)) * E * D := by ring
        _ ≤ (localRate * T) * E * D := by
          gcongr
        _ = (localRate * T * E) * D := by ring
    apply hcoef.trans
    have hDshared : D = euclideanNorm (z₁.1 - z₂.1) := by
      dsimp [D]
      rw [hmomentum, sub_self, euclideanNorm_zero, add_zero]
    rw [hDshared]
    exact mul_le_mul_of_nonneg_right hrateT (euclideanNorm_nonneg _)
  cases k with
  | ofNat n =>
      exact hpositive ε n hεone hεlocal' horizon
  | negSucc n =>
      change |(energy potential (leapfrogN gradient (-ε) (n + 1) z₁) -
          energy potential z₁) -
        (energy potential (leapfrogN gradient (-ε) (n + 1) z₂) -
          energy potential z₂)| ≤ _
      have hεnegOne : |-ε| ≤ 1 := by simpa only [abs_neg] using hεone
      have hεnegLocal : |-ε| < εlocal := by simpa only [abs_neg] using hεlocal'
      have hhor : ((n + 1 : ℕ) : ℝ) * |-ε| ≤ T := by
        simpa only [Int.natAbs_negSucc, abs_neg] using horizon
      exact hpositive (-ε) (n + 1) hεnegOne hεnegLocal hhor

/-- The missing relative numerical estimate behind the paper's Lemma 4.3.
It asks that differences of the two centered leapfrog energy-defect profiles
be Lipschitz in the initial position separation, with an arbitrarily small
coefficient after reducing the step size uniformly on a compact position set,
kinetic cutoff, and integration-time window. -/
def UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (K : Set (Position ι)) (k0 T : ℝ) : Prop :=
  ∀ energyRate : NNReal, 0 < energyRate →
    ∃ εbar > 0, ∀ {ε : ℝ}, 0 < ε → ε < εbar →
      ∀ {L : ℕ}, ε * (L : ℝ) ≤ T →
        ∀ (origin : Fin (L + 1)), ∀ q₁ ∈ K, ∀ q₂ ∈ K,
          ∀ p : Momentum ι, kineticEnergy p ≤ k0 → ∀ i,
            |(energy potential
                  (offsetLeapfrogTrajectory gradient ε origin (q₁, p) i) -
                energy potential (q₁, p)) -
              (energy potential
                  (offsetLeapfrogTrajectory gradient ε origin (q₂, p) i) -
                energy potential (q₂, p))| ≤
              (energyRate : ℝ) * euclideanNorm (q₁ - q₂)

/-- A locally uniform vanishing modulus gives the compact-window relative
property after compactness and the kinetic cutoff bound the initial phases. -/
theorem LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError.onCompactWindow
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpaired : LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError
      potential gradient)
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T) :
    UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
      potential gradient K k0 T := by
  obtain ⟨R, hR, hphase⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
      hK hk0
  intro energyRate henergyRate
  obtain ⟨εbar, hεbar, hbound⟩ :=
    hpaired R T hT (energyRate : ℝ) (by exact_mod_cast henergyRate)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp i
  have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
    omega
  have hindexR :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hindex
  have hoffset :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ T := by
    rw [abs_of_pos hεpos]
    exact (mul_le_mul_of_nonneg_right hindexR hεpos.le).trans
      (by simpa only [mul_comm] using horizon)
  have hraw := hbound (by simpa only [abs_of_pos hεpos] using hε)
    ((i.val : ℤ) - (origin.val : ℤ)) hoffset
    (q₁, p) (q₂, p) (hphase q₁ hq₁ p hp) (hphase q₂ hq₂ p hp)
  simpa only [offsetLeapfrogTrajectory, sub_self, euclideanNorm_zero,
    add_zero] using hraw

/-- The shared-momentum criterion already suffices for the compact-window
property, because multinomial HMC couples both trajectories with one momentum. -/
theorem LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyErrorOfSharedMomentum.onCompactWindow
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpaired :
      LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyErrorOfSharedMomentum
        potential gradient)
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T) :
    UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
      potential gradient K k0 T := by
  obtain ⟨R, hR, hphase⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
      hK hk0
  intro energyRate henergyRate
  obtain ⟨εbar, hεbar, hbound⟩ :=
    hpaired R T hT (energyRate : ℝ) (by exact_mod_cast henergyRate)
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp i
  have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
    omega
  have hindexR :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hindex
  have hoffset :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ T := by
    rw [abs_of_pos hεpos]
    exact (mul_le_mul_of_nonneg_right hindexR hεpos.le).trans
      (by simpa only [mul_comm] using horizon)
  have hraw := hbound (by simpa only [abs_of_pos hεpos] using hε)
    ((i.val : ℤ) - (origin.val : ℤ)) hoffset
    (q₁, p) (q₂, p) rfl (hphase q₁ hq₁ p hp) (hphase q₂ hq₂ p hp)
  simpa only [offsetLeapfrogTrajectory] using hraw

/-- Quantitative signed-leapfrog relative consistency implies the compact
window epsilon--delta property used by the multinomial mismatch proof. -/
theorem LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError.onCompactWindow
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpaired : LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError
      potential gradient)
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T) :
    UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
      potential gradient K k0 T := by
  obtain ⟨R, hR, hphase⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanPhaseSize_bound_of_kineticEnergy_le
      hK hk0
  obtain ⟨C, hC, hbound⟩ := hpaired R T hT
  intro energyRate henergyRate
  let εbar : ℝ := min 1 ((energyRate : ℝ) / (C + 1))
  have hden : 0 < C + 1 := by linarith
  have hquot : 0 < (energyRate : ℝ) / (C + 1) :=
    div_pos (by exact_mod_cast henergyRate) hden
  have hεbar : 0 < εbar := lt_min zero_lt_one hquot
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp i
  have hεone : |ε| ≤ 1 := by
    rw [abs_of_pos hεpos]
    exact hε.le.trans (min_le_left _ _)
  have hindex : Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) ≤ L := by
    omega
  have hindexR :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) ≤ L := by
    exact_mod_cast hindex
  have hoffset :
      (Int.natAbs ((i.val : ℤ) - (origin.val : ℤ)) : ℝ) * |ε| ≤ T := by
    rw [abs_of_pos hεpos]
    exact (mul_le_mul_of_nonneg_right hindexR hεpos.le).trans
      (by simpa only [mul_comm] using horizon)
  have hraw := hbound hεone ((i.val : ℤ) - (origin.val : ℤ)) hoffset
    (q₁, p) (q₂, p) (hphase q₁ hq₁ p hp) (hphase q₂ hq₂ p hp)
  have hεquot : ε < (energyRate : ℝ) / (C + 1) :=
    hε.trans_le (min_le_right _ _)
  have hscaled : C * ε ≤ (energyRate : ℝ) := by
    have hmul : ε * (C + 1) < (energyRate : ℝ) :=
      (lt_div_iff₀ hden).mp hεquot
    nlinarith
  apply hraw.trans
  rw [abs_of_pos hεpos]
  simp only [sub_self, euclideanNorm_zero, add_zero]
  exact mul_le_mul_of_nonneg_right hscaled (euclideanNorm_nonneg _)

/-- A positive mismatch allowance admits a positive relative-energy rate
small enough both for TV linearization and for the final mismatch budget. -/
lemma exists_relativeEnergyRate
    (positionBound mismatchBound mismatchRate : NNReal)
    (hmismatch : 0 < mismatchRate) (hmismatchOne : mismatchRate ≤ 1) :
    ∃ energyRate : NNReal, 0 < energyRate ∧
      4 * energyRate * mismatchBound ≤ mismatchRate ∧
      energyRate * (2 * positionBound) ≤ 1 / 2 := by
  let denom : NNReal := 8 * (mismatchBound + 1) * (positionBound + 1)
  have hdenom : 0 < denom := by dsimp [denom]; positivity
  let energyRate := mismatchRate / denom
  have henergy : 0 < energyRate := div_pos hmismatch hdenom
  refine ⟨energyRate, henergy, ?_, ?_⟩
  · apply NNReal.coe_le_coe.mp
    dsimp [energyRate, denom]
    have hdenomR : 0 <
        8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1) := by
      positivity
    rw [show 4 *
        ((mismatchRate : ℝ) /
          (8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1))) *
          (mismatchBound : ℝ) =
        (4 * (mismatchRate : ℝ) * (mismatchBound : ℝ)) /
          (8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1)) by
      ring]
    apply (div_le_iff₀ hdenomR).2
    have hB : 0 ≤ (mismatchBound : ℝ) := mismatchBound.coe_nonneg
    have hQ : 0 ≤ (positionBound : ℝ) := positionBound.coe_nonneg
    have hcoef : 4 * (mismatchBound : ℝ) ≤
        8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1) := by
      nlinarith [mul_nonneg (show 0 ≤ 8 * ((mismatchBound : ℝ) + 1) by positivity)
        (show 0 ≤ (positionBound : ℝ) from hQ)]
    calc
      4 * (mismatchRate : ℝ) * (mismatchBound : ℝ) =
          (mismatchRate : ℝ) * (4 * (mismatchBound : ℝ)) := by ring
      _ ≤ (mismatchRate : ℝ) *
          (8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hcoef mismatchRate.coe_nonneg
  · apply NNReal.coe_le_coe.mp
    dsimp [energyRate, denom]
    have hdenomR : 0 <
        8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1) := by
      positivity
    rw [show
        (mismatchRate : ℝ) /
            (8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1)) *
            (2 * (positionBound : ℝ)) =
          ((mismatchRate : ℝ) * (2 * (positionBound : ℝ))) /
            (8 * ((mismatchBound : ℝ) + 1) * ((positionBound : ℝ) + 1)) by
      ring]
    apply (div_le_iff₀ hdenomR).2
    have hmr : (mismatchRate : ℝ) ≤ 1 := by exact_mod_cast hmismatchOne
    have hB : 0 ≤ (mismatchBound : ℝ) := mismatchBound.coe_nonneg
    have hQ : 0 ≤ (positionBound : ℝ) := positionBound.coe_nonneg
    nlinarith

/-- Strongest compact-uniform general-potential estimate currently implied by
Assumptions 1 and 2 alone: a subunit overlap-weighted aligned rate and an
arbitrarily small *additive* mismatch budget hold with common numerical
thresholds.  Lemma 4.3's relative Condition 1 conclusion additionally needs
this final `η` to scale with the initial separation. -/
theorem LocalStrongConvexity.exists_uniform_alignedContraction_additiveMismatch
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {k0 : ℝ} (hk0 : 0 ≤ k0)
    {η : ENNReal} (hη : 0 < η) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ alignedRate : NNReal, alignedRate < 1 ∧
        ∃ mismatchBound : NNReal,
          ∀ q₁ q₂ : Position ι, ∀ p : Momentum ι,
            q₁ ∈ K → q₂ ∈ K → kineticEnergy p ≤ k0 →
            ∀ {ε : ℝ} {L : ℕ}, 0 < ε → ε ≤ εbar →
              Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
              ∀ (origin : Fin (L + 1)),
                (∑ i, min
                    (trajectoryIndexPMF potential
                      (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                    (trajectoryIndexPMF potential
                      (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                    (trajectorySquaredPositionCost gradient ε
                      (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                    (alignedRate : ENNReal) *
                      (initialSquaredPositionDistance q₁ q₂ : ENNReal) ∧
                (∀ i j, trajectorySquaredPositionCost gradient ε
                    (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
                McmcLean.Finite.totalVariation
                    (trajectoryIndexPMF potential
                      (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                    (trajectoryIndexPMF potential
                      (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                    (mismatchBound : ENNReal) < η := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εaligned, hεaligned,
      alignedRate, haligned, halignedBound⟩ :=
    hconv.exists_uniform_overlapWeightedAlignedContraction_of_kineticEnergy_le
      hreg hK hKS hScompact hSconvex hk0
  have hTmax0 : 0 ≤ Tmax := (hTmin.trans hTmax).le
  obtain ⟨εmismatch, hεmismatch, mismatchBound, hmismatch⟩ :=
    hreg.exists_uniform_totalVariation_mul_squaredCost_lt
      hK hk0 hTmax0 hη
  let εbar := min εaligned (εmismatch / 2)
  have hεbar : 0 < εbar :=
    lt_min hεaligned (half_pos hεmismatch)
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
    alignedRate, haligned, mismatchBound, ?_⟩
  intro q₁ q₂ p hq₁ hq₂ hp ε L hεpos hεbar' hTmin' hTmax' origin
  have hεaligned' : ε ≤ εaligned :=
    hεbar'.trans (min_le_left _ _)
  have hεmismatch' : ε < εmismatch := by
    have hhalf : ε ≤ εmismatch / 2 :=
      hεbar'.trans (min_le_right _ _)
    exact hhalf.trans_lt (half_lt_self hεmismatch)
  refine ⟨halignedBound q₁ q₂ p hq₁ hq₂ hp hεpos.le hεaligned'
      hTmin' hTmax' origin, ?_⟩
  exact hmismatch hεpos hεmismatch' hTmax' origin q₁ hq₁ q₂ hq₂ p hp

@[simp]
theorem coe_initialPositionDistance
    (q₁ q₂ : Position ι) :
    (initialPositionDistance q₁ q₂ : ENNReal) =
      ENNReal.ofReal (euclideanNorm (q₁ - q₂)) := by
  rw [ENNReal.coe_nnreal_eq]
  rfl

@[simp]
theorem coe_initialSquaredPositionDistance
    (q₁ q₂ : Position ι) :
    (initialSquaredPositionDistance q₁ q₂ : ENNReal) =
      ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2) := by
  rw [ENNReal.coe_nnreal_eq]
  rfl

/-- The fixed-exponent quantitative core of Condition 1. For every positive
kinetic-energy cutoff, the step-size and integration-length thresholds work
uniformly over all smaller admissible numerical parameters, all trajectory
splits, both positions in `S`, and every shared momentum under the cutoff. -/
def XuCondition1AtExponent
    (family : TrajectoryIndexCouplingFamily ι)
    (gradient : Position ι → Position ι) (S : Set (Position ι))
    (m : ℕ) (rate : NNReal) : Prop :=
  1 ≤ m ∧
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∃ Lbar : ℕ, 1 ≤ Lbar ∧
          ∀ ε : ℝ, 0 < ε → ε < εbar →
            ∀ L : ℕ,
              ε * (L : ℝ) < εbar * (Lbar : ℝ) →
                ∀ origin : Fin (L + 1),
                  ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                    kineticEnergy p ≤ k0 →
                      McmcLean.Finite.transportCost
                          (trajectoryPositionMomentCost gradient m ε
                            (((q₁, p), (q₂, p))) origin)
                          (family ε L (((q₁, p), (q₂, p))) origin) ≤
                        (rate : ENNReal) *
                          ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ m)

/-- Condition 1 (local contractivity) from Xu et al. The exponent is chosen
once and its fixed-exponent core holds uniformly. -/
def XuCondition1
    (family : TrajectoryIndexCouplingFamily ι)
    (gradient : Position ι → Position ι) (S : Set (Position ι))
    (rate : NNReal) : Prop :=
  0 < rate ∧ rate < 1 ∧
    ∃ m : ℕ, XuCondition1AtExponent family gradient S m rate

/-- On a one-point index type every joint PMF puts unit mass on the unique
pair, so transport cost is just that pair's cost. -/
private theorem transportCost_fin_one
    (cost : Fin 1 → Fin 1 → NNReal) (joint : PMF (Fin 1 × Fin 1)) :
    McmcLean.Finite.transportCost cost joint = (cost 0 0 : ENNReal) := by
  have htotal : ∑ ij : Fin 1 × Fin 1, joint ij = 1 := by
    calc
      ∑ ij : Fin 1 × Fin 1, joint ij = ∑' ij, joint ij := by
        rw [tsum_fintype]
      _ = 1 := joint.tsum_coe
  have htotal' : ∑ i : Fin 1, ∑ j : Fin 1, joint (i, j) = 1 := by
    rw [← Finset.sum_product]
    exact htotal
  have hmass : joint (0, 0) = 1 := by simpa using htotal'
  unfold McmcLean.Finite.transportCost
  simp [hmass]

/-- The printed uniform quantifiers in Condition 1 force its rate to be at
least one whenever the contraction set contains two distinct points. Indeed,
the admissible choice `L = 0` has only the current-state index and therefore
cannot contract. This records a genuine obstruction in the published
statement rather than silently strengthening its integration-time regime. -/
theorem XuCondition1AtExponent.one_le_rate_of_distinct
    {family : TrajectoryIndexCouplingFamily ι}
    {gradient : Position ι → Position ι} {S : Set (Position ι)}
    {m : ℕ} {rate : NNReal}
    (h : XuCondition1AtExponent family gradient S m rate)
    {q₁ q₂ : Position ι} (hq₁ : q₁ ∈ S) (hq₂ : q₂ ∈ S)
    (hne : q₁ ≠ q₂) : 1 ≤ rate := by
  rcases h.2 1 zero_lt_one with
    ⟨εbar, hεbar, Lbar, hLbar, hbound⟩
  let ε := εbar / 2
  have hε0 : 0 < ε := div_pos hεbar (by norm_num)
  have hεlt : ε < εbar := by dsimp [ε]; linarith
  have hlength : ε * ((0 : ℕ) : ℝ) < εbar * (Lbar : ℝ) := by
    have hLbarPos : 0 < (Lbar : ℝ) := by exact_mod_cast hLbar
    simpa using mul_pos hεbar hLbarPos
  have hcost := hbound ε hε0 hεlt 0 hlength 0 q₁ hq₁ q₂ hq₂ 0 (by
    unfold kineticEnergy
    simp)
  rw [transportCost_fin_one] at hcost
  have hcostValue :
      (trajectoryPositionMomentCost gradient m ε
          (((q₁, (0 : Momentum ι)), (q₂, (0 : Momentum ι))))
          (0 : Fin 1) 0 0 : ENNReal) =
        ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ m) := by
    unfold trajectoryPositionMomentCost offsetLeapfrogTrajectory
    simp only [Fin.val_zero, Int.ofNat_zero, sub_self, signedLeapfrog_zero,
      ]
    rw [ENNReal.coe_nnreal_eq]
    congr 1
  rw [hcostValue] at hcost
  let d : ENNReal := ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ m)
  have hnorm : 0 < euclideanNorm (q₁ - q₂) := by
    have hsquare := squaredEuclideanNorm_pos (sub_ne_zero.mpr hne)
    rw [← euclideanNorm_sq] at hsquare
    nlinarith [euclideanNorm_nonneg (q₁ - q₂)]
  have hmpos : 0 < euclideanNorm (q₁ - q₂) ^ m :=
    pow_pos hnorm _
  have hd0 : d ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hmpos
  have hdtop : d ≠ ∞ := ENNReal.ofReal_ne_top
  change d ≤ (rate : ENNReal) * d at hcost
  have hone : (1 : ENNReal) ≤ rate := by
    rw [← ENNReal.mul_le_mul_iff_right hd0 hdtop]
    simpa only [one_mul, mul_comm] using hcost
  exact_mod_cast hone

/-- Consequently, the printed Condition 1 is inconsistent with its required
strictly subunit rate on any set containing two distinct points. -/
theorem XuCondition1.not_of_distinct
    {family : TrajectoryIndexCouplingFamily ι}
    {gradient : Position ι → Position ι} {S : Set (Position ι)}
    {rate : NNReal} {q₁ q₂ : Position ι}
    (hq₁ : q₁ ∈ S) (hq₂ : q₂ ∈ S) (hne : q₁ ≠ q₂) :
    ¬ XuCondition1 family gradient S rate := by
  intro h
  rcases h.2.2 with ⟨m, hm⟩
  have hone := hm.one_le_rate_of_distinct hq₁ hq₂ hne
  exact (not_le_of_gt h.2.1) hone

/-- A mathematically viable repair of the printed Condition 1: integration
times stay in a fixed window bounded away from zero while the leapfrog step
size decreases. This definition is explicitly not attributed verbatim to the
paper; it is the interface on which the remaining contraction analysis can be
carried out without contradicting the identity limit. -/
def XuCondition1AtExponentOnIntegrationWindow
    (family : TrajectoryIndexCouplingFamily ι)
    (gradient : Position ι → Position ι) (S : Set (Position ι))
    (m : ℕ) (rate : NNReal) (Tmin Tmax : ℝ) : Prop :=
  1 ≤ m ∧ 0 < Tmin ∧ Tmin ≤ Tmax ∧
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  McmcLean.Finite.transportCost
                      (trajectoryPositionMomentCost gradient m ε
                        (((q₁, p), (q₂, p))) origin)
                      (family ε L (((q₁, p), (q₂, p))) origin) ≤
                    (rate : ENNReal) *
                      ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ m)

/-- Full local contractivity on a positive integration-time window. -/
def XuCondition1OnIntegrationWindow
    (family : TrajectoryIndexCouplingFamily ι)
    (gradient : Position ι → Position ι) (S : Set (Position ι))
    (rate : NNReal) : Prop :=
  0 < rate ∧ rate < 1 ∧
    ∃ m : ℕ, ∃ Tmin Tmax : ℝ,
      XuCondition1AtExponentOnIntegrationWindow
        family gradient S m rate Tmin Tmax

/-- A fixed-exponent positive-window certificate supplies the repaired full
local-contractivity interface. -/
theorem XuCondition1AtExponentOnIntegrationWindow.xuCondition1OnIntegrationWindow
    {family : TrajectoryIndexCouplingFamily ι}
    {gradient : Position ι → Position ι} {S : Set (Position ι)}
    {m : ℕ} {rate : NNReal} {Tmin Tmax : ℝ}
    (h : XuCondition1AtExponentOnIntegrationWindow
      family gradient S m rate Tmin Tmax)
    (hrate0 : 0 < rate) (hrate1 : rate < 1) :
    XuCondition1OnIntegrationWindow family gradient S rate :=
  ⟨hrate0, hrate1, m, Tmin, Tmax, h⟩

/-- Any fixed-exponent certificate with a subunit positive rate supplies the
existential exponent required by Condition 1. -/
theorem XuCondition1AtExponent.xuCondition1
    {family : TrajectoryIndexCouplingFamily ι}
    {gradient : Position ι → Position ι} {S : Set (Position ι)}
    {m : ℕ} {rate : NNReal}
    (h : XuCondition1AtExponent family gradient S m rate)
    (hrate0 : 0 < rate) (hrate1 : rate < 1) :
    XuCondition1 family gradient S rate :=
  ⟨hrate0, hrate1, m, h⟩

/-- The maximal categorical coupling as a parameterized family suitable for
`XuCondition1`. -/
noncomputable def maximalTrajectoryIndexCouplingFamily
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    TrajectoryIndexCouplingFamily ι :=
  fun ε _L z origin =>
    maximalTrajectoryIndexCoupling potential gradient ε z origin

/-- The optimal-transport categorical coupling as a parameterized family
suitable for `XuCondition1`. -/
noncomputable def transportTrajectoryIndexCouplingFamily
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    TrajectoryIndexCouplingFamily ι :=
  fun ε _L z origin =>
    transportTrajectoryIndexCoupling potential gradient ε z origin

/-- Constructive transport family obtained by measurable finite argmin over
all complete greedy edge orders. Its exact global optimality is separated
below into the finite candidate-completeness hypothesis. -/
noncomputable def greedyTransportTrajectoryIndexCouplingFamily
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    TrajectoryIndexCouplingFamily ι :=
  fun ε _L z origin =>
    McmcLean.Finite.greedySelectedTransportCoupling
      (fun z => trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (fun z => trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2))
      (fun z => trajectorySquaredPositionCost gradient ε z origin) z

/-- Apply Algorithm 5 pointwise to an arbitrary parameterized candidate
trajectory-index law. -/
noncomputable def repairedTrajectoryIndexCouplingFamily
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (candidate : TrajectoryIndexCouplingFamily ι) :
    TrajectoryIndexCouplingFamily ι :=
  fun ε _L z origin =>
    repairedTrajectoryIndexCoupling potential gradient ε z origin
      (candidate ε _L z origin)

/-- Every row of a trajectory-index family has the two required multinomial
trajectory laws as marginals. -/
def IsTrajectoryIndexCouplingFamily
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι) : Prop :=
  ∀ ε L z origin,
    McmcLean.Finite.IsPMFCoupling (family ε L z origin)
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2))

/-- Every atom of a parameterized trajectory-index family varies measurably
with the paired phase point.  This is the exact regularity needed to turn the
pointwise finite laws into a mathlib `Kernel`; it is deliberately separate
from the marginal-coupling property. -/
def IsMeasurableTrajectoryIndexCouplingFamily
    (family : TrajectoryIndexCouplingFamily ι) : Prop :=
  ∀ ε L origin selected,
    Measurable fun z : PhaseSpace ι × PhaseSpace ι =>
      family ε L z origin selected

/-- Pointwise marginal repair makes any candidate family an exact
trajectory-index coupling family. -/
theorem repairedTrajectoryIndexCouplingFamily_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (candidate : TrajectoryIndexCouplingFamily ι) :
    IsTrajectoryIndexCouplingFamily potential gradient
      (repairedTrajectoryIndexCouplingFamily potential gradient candidate) := by
  intro ε L z origin
  exact repairedTrajectoryIndexCoupling_isCoupling potential gradient ε z
    origin (candidate ε L z origin)

/-- Algorithm 5 preserves measurability of a parameterized candidate family. -/
theorem repairedTrajectoryIndexCouplingFamily_isMeasurable
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (candidate : TrajectoryIndexCouplingFamily ι)
    (hcandidate : IsMeasurableTrajectoryIndexCouplingFamily candidate) :
    IsMeasurableTrajectoryIndexCouplingFamily
      (repairedTrajectoryIndexCouplingFamily potential gradient candidate) := by
  intro ε L origin selected
  unfold repairedTrajectoryIndexCouplingFamily repairedTrajectoryIndexCoupling
  apply McmcLean.Finite.measurable_maximallyMarginalRepairedCoupling_apply
  · exact fun edge => hcandidate ε L origin edge
  · intro i
    exact (measurable_trajectoryIndexProbability hpotential hgradient ε
      origin i).comp measurable_fst
  · intro j
    exact (measurable_trajectoryIndexProbability hpotential hgradient ε
      origin j).comp measurable_snd

/-- A trajectory-index family is pointwise optimal for the squared-position
transport problem.  This interface does not prescribe how ties are broken;
in particular, a future constructive measurable selector can implement it
without having to coincide with `Classical.choose`. -/
def IsOptimalTrajectoryIndexCouplingFamily
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι) : Prop :=
  IsTrajectoryIndexCouplingFamily potential gradient family ∧
    ∀ ε L z origin (joint : PMF (Fin (L + 1) × Fin (L + 1))),
      McmcLean.Finite.IsPMFCoupling joint
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) →
        McmcLean.Finite.transportCost
            (trajectorySquaredPositionCost gradient ε z origin)
            (family ε L z origin) ≤
          McmcLean.Finite.transportCost
            (trajectorySquaredPositionCost gradient ε z origin) joint

/-- The randomized-origin phase-space kernel associated with any measurable
trajectory-index coupling family. -/
noncomputable def trajectoryIndexCouplingFamilyKernel
    (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family) :
    Kernel (PhaseSpace ι × PhaseSpace ι) (PhaseSpace ι × PhaseSpace ι) :=
  coupledRandomizedMultinomialLeapfrogKernel gradient ε L
    (fun z origin => family ε L z origin) hgradient (hmeas ε L)

instance trajectoryIndexCouplingFamilyKernel_isMarkovKernel
    (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family) :
    IsMarkovKernel
      (trajectoryIndexCouplingFamilyKernel gradient family ε L hgradient
        hmeas) := by
  unfold trajectoryIndexCouplingFamilyKernel
  infer_instance

/-- A measurable family with the required pointwise marginals gives an actual
coupling of the verified randomized multinomial trajectory kernel. -/
theorem trajectoryIndexCouplingFamilyKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family)
    (hfamily : IsTrajectoryIndexCouplingFamily potential gradient family) :
    McmcLean.Kernel.IsCoupling
      (trajectoryIndexCouplingFamilyKernel gradient family ε L hgradient
        hmeas)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) := by
  unfold trajectoryIndexCouplingFamilyKernel
  apply coupledRandomizedMultinomialLeapfrogKernel_isCoupling
  exact fun z origin => hfamily ε L z origin

/-- Shared-momentum position-space HMC driven by a measurable categorical
coupling family. -/
noncomputable def trajectoryIndexCouplingFamilySharedMomentumHMC
    (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family) :
    Kernel (Position ι × Position ι) (Position ι × Position ι) :=
  coupledPositionMultinomialHMC
    (trajectoryIndexCouplingFamilyKernel gradient family ε L hgradient hmeas)
    (sharedPositionMomentumLift (standardMomentumMeasure (ι := ι)))

instance trajectoryIndexCouplingFamilySharedMomentumHMC_isMarkovKernel
    (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (ε : ℝ) (L : ℕ) (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family) :
    IsMarkovKernel
      (trajectoryIndexCouplingFamilySharedMomentumHMC gradient family ε L
        hgradient hmeas) := by
  unfold trajectoryIndexCouplingFamilySharedMomentumHMC
  infer_instance

/-- Both marginals of the family-driven shared-momentum kernel are the
verified standard position-space multinomial HMC kernel. -/
theorem trajectoryIndexCouplingFamilySharedMomentumHMC_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (ε : ℝ) (L : ℕ) (hpotential : Measurable potential)
    (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family)
    (hfamily : IsTrajectoryIndexCouplingFamily potential gradient family) :
    McmcLean.Kernel.IsCoupling
      (trajectoryIndexCouplingFamilySharedMomentumHMC gradient family ε L
        hgradient hmeas)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  unfold trajectoryIndexCouplingFamilySharedMomentumHMC
    standardPositionMultinomialHMC positionMultinomialHMC
  apply coupledPositionMultinomialHMC_isCoupling
  · exact trajectoryIndexCouplingFamilyKernel_isCoupling potential gradient
      family ε L hpotential hgradient hmeas hfamily
  · exact sharedPositionMomentumLift_isCoupling standardMomentumMeasure

/-- A measurable approximate trajectory-index solver, followed pointwise by
Algorithm 5, lifts to a coupling of the verified randomized phase-space
multinomial kernels. -/
theorem repairedTrajectoryIndexCouplingFamilyKernel_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (candidate : TrajectoryIndexCouplingFamily ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hcandidate : IsMeasurableTrajectoryIndexCouplingFamily candidate)
    (ε : ℝ) (L : ℕ) :
    McmcLean.Kernel.IsCoupling
      (trajectoryIndexCouplingFamilyKernel gradient
        (repairedTrajectoryIndexCouplingFamily potential gradient candidate)
        ε L hgradient
        (repairedTrajectoryIndexCouplingFamily_isMeasurable potential gradient
          hpotential hgradient candidate hcandidate))
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient)
      (randomizedMultinomialLeapfrogKernel potential gradient ε L
        hpotential hgradient) := by
  exact trajectoryIndexCouplingFamilyKernel_isCoupling potential gradient _ ε L
    hpotential hgradient
    (repairedTrajectoryIndexCouplingFamily_isMeasurable potential gradient
      hpotential hgradient candidate hcandidate)
    (repairedTrajectoryIndexCouplingFamily_isCoupling potential gradient candidate)

/-- The same repaired family lifts through the shared-momentum construction
to a coupling of the verified position-space multinomial HMC kernel. -/
theorem repairedTrajectoryIndexCouplingFamilySharedMomentumHMC_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (candidate : TrajectoryIndexCouplingFamily ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hcandidate : IsMeasurableTrajectoryIndexCouplingFamily candidate)
    (ε : ℝ) (L : ℕ) :
    McmcLean.Kernel.IsCoupling
      (trajectoryIndexCouplingFamilySharedMomentumHMC gradient
        (repairedTrajectoryIndexCouplingFamily potential gradient candidate)
        ε L hgradient
        (repairedTrajectoryIndexCouplingFamily_isMeasurable potential gradient
          hpotential hgradient candidate hcandidate))
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient)
      (standardPositionMultinomialHMC potential gradient ε L
        hpotential hgradient) := by
  exact trajectoryIndexCouplingFamilySharedMomentumHMC_isCoupling potential
    gradient _ ε L hpotential hgradient
    (repairedTrajectoryIndexCouplingFamily_isMeasurable potential gradient
      hpotential hgradient candidate hcandidate)
    (repairedTrajectoryIndexCouplingFamily_isCoupling potential gradient candidate)

/-- The maximal family has the required trajectory-index marginals. -/
theorem maximalTrajectoryIndexCouplingFamily_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    IsTrajectoryIndexCouplingFamily potential gradient
      (maximalTrajectoryIndexCouplingFamily potential gradient) := by
  intro ε L z origin
  exact (maximalTrajectoryIndexCoupling_isMaximal
    potential gradient ε z origin).1

/-- Measurable potentials and gradients make the maximal categorical family
an actual measurable family of finite joint laws. -/
theorem maximalTrajectoryIndexCouplingFamily_isMeasurable
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    IsMeasurableTrajectoryIndexCouplingFamily
      (maximalTrajectoryIndexCouplingFamily potential gradient) := by
  intro ε L origin selected
  exact measurable_maximalTrajectoryIndexCoupling_apply
    hpotential hgradient ε origin selected

/-- A positive-window moment certificate for any measurable trajectory-index
family is an expected output-position moment bound for the implemented
randomized-origin kernel.  This is the generic kernel-level bridge from the
paper's pointwise Condition 1 cost to a mathlib Markov kernel. -/
theorem XuCondition1AtExponentOnIntegrationWindow.coupledRandomizedMultinomialLeapfrogKernel_expectedPositionMoment
    (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (S : Set (Position ι)) (m : ℕ) (rate : NNReal) (Tmin Tmax : ℝ)
    (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family)
    (h : XuCondition1AtExponentOnIntegrationWindow
      family gradient S m rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
              kineticEnergy p ≤ k0 →
                (∫⁻ y, ENNReal.ofReal
                    (euclideanNorm (y.1.1 - y.2.1) ^ m)
                    ∂coupledRandomizedMultinomialLeapfrogKernel gradient ε L
                      (fun z origin => family ε L z origin) hgradient
                      (hmeas ε L) (((q₁, p), (q₂, p)))) ≤
                  (rate : ENNReal) *
                    ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ m) := by
  intro k0 hk0
  rcases h.2.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ p hp
  apply coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionMoment_le
  intro origin
  exact hbound ε hε0 hε L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p hp

/-- Exponent-one Condition 1 is an actual conditional expected-position-
distance contraction theorem for the randomized maximal coupled trajectory
kernel, after averaging over its shared origin. Momentum is still fixed here;
the condition's kinetic cutoff is retained explicitly for the later momentum
integration step. -/
theorem XuCondition1AtExponentOnIntegrationWindow.maximalCoupledRandomizedMultinomialLeapfrogKernel_expectedDistance
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (h : XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 1 rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
              kineticEnergy p ≤ k0 →
                (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
                    ∂maximalCoupledRandomizedMultinomialLeapfrogKernel
                      potential gradient ε L hpotential hgradient
                      (((q₁, p), (q₂, p)))) ≤
                  (rate : ENNReal) *
                    ENNReal.ofReal (euclideanNorm (q₁ - q₂)) := by
  intro k0 hk0
  rcases h.2.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ p hp
  unfold maximalCoupledRandomizedMultinomialLeapfrogKernel
  apply coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionDistance_le
  intro origin
  have hcost := hbound ε hε0 hε L hTmin hTmax origin
    q₁ hq₁ q₂ hq₂ p hp
  simpa only [maximalTrajectoryIndexCouplingFamily, pow_one] using hcost

/-- The optimal-transport family has the required trajectory-index
marginals. -/
theorem transportTrajectoryIndexCouplingFamily_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    IsTrajectoryIndexCouplingFamily potential gradient
      (transportTrajectoryIndexCouplingFamily potential gradient) := by
  intro ε L z origin
  exact transportTrajectoryIndexCoupling_isCoupling
    potential gradient ε z origin

/-- The existing classically selected family implements the abstract
pointwise-optimal interface.  Measurability is intentionally not asserted. -/
theorem transportTrajectoryIndexCouplingFamily_isOptimal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    IsOptimalTrajectoryIndexCouplingFamily potential gradient
      (transportTrajectoryIndexCouplingFamily potential gradient) := by
  refine ⟨transportTrajectoryIndexCouplingFamily_isCoupling
    potential gradient, ?_⟩
  intro ε L z origin joint hjoint
  exact transportTrajectoryIndexCoupling_minimal
    potential gradient ε z origin joint hjoint

/-- The one remaining finite combinatorial hypothesis for the constructive
greedy selector: at every trajectory input, the complete-order candidate
family contains a globally optimal squared-cost coupling. -/
def GreedyTransportTrajectoryCandidatesComplete
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) : Prop :=
  ∀ (ε : ℝ) (L : ℕ) (z : PhaseSpace ι × PhaseSpace ι)
      (origin : Fin (L + 1)),
    McmcLean.Finite.GreedyTransportCandidatesComplete
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.1))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin z.2))
      (trajectorySquaredPositionCost gradient ε z origin)

/-- The greedy finite selector has the required categorical marginals without
any optimality assumption. -/
theorem greedyTransportTrajectoryIndexCouplingFamily_isCoupling
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    IsTrajectoryIndexCouplingFamily potential gradient
      (greedyTransportTrajectoryIndexCouplingFamily potential gradient) := by
  intro ε L z origin
  unfold greedyTransportTrajectoryIndexCouplingFamily
  exact McmcLean.Finite.greedySelectedTransportCoupling_isCoupling _ _ _ z

/-- The greedy finite selector is atom-measurable under the ordinary
measurability assumptions on the potential and gradient. -/
theorem greedyTransportTrajectoryIndexCouplingFamily_isMeasurable
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    IsMeasurableTrajectoryIndexCouplingFamily
      (greedyTransportTrajectoryIndexCouplingFamily potential gradient) := by
  intro ε L origin selected
  unfold greedyTransportTrajectoryIndexCouplingFamily
  apply McmcLean.Finite.measurable_greedySelectedTransportCoupling_apply
  · intro i
    exact (measurable_trajectoryIndexProbability hpotential hgradient ε
      origin i).comp measurable_fst
  · intro j
    exact (measurable_trajectoryIndexProbability hpotential hgradient ε
      origin j).comp measurable_snd
  · intro i j
    apply Measurable.subtype_mk
    exact continuous_squaredEuclideanNorm.measurable.comp
      (((measurable_offsetLeapfrogTrajectory hgradient ε origin i).comp
          measurable_fst).fst.sub
        ((measurable_offsetLeapfrogTrajectory hgradient ε origin j).comp
          measurable_snd).fst)

/-- The constructive measurable greedy selector realizes the exact
pointwise-optimal transport interface used by the HMC theorems. -/
theorem greedyTransportTrajectoryIndexCouplingFamily_isOptimal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι) :
    IsOptimalTrajectoryIndexCouplingFamily potential gradient
      (greedyTransportTrajectoryIndexCouplingFamily potential gradient) := by
  refine ⟨greedyTransportTrajectoryIndexCouplingFamily_isCoupling
    potential gradient, ?_⟩
  intro ε L z origin joint hjoint
  unfold greedyTransportTrajectoryIndexCouplingFamily
  exact McmcLean.Finite.greedySelectedTransportCoupling_minimal _ _ _ z
    (McmcLean.Finite.greedyTransportCandidatesComplete _ _ _) joint hjoint

/-- Exponent-two positive-window contractivity for a measurably selected
optimal transport plan controls the squared position separation of the actual
randomized-origin transport kernel.  The measurability premise is kept
explicit because the current finite optimizer is selected pointwise. -/
theorem XuCondition1AtExponentOnIntegrationWindow.transportCoupledRandomizedMultinomialLeapfrogKernel_expectedSquaredDistance
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily
      (transportTrajectoryIndexCouplingFamily potential gradient))
    (h : XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
              kineticEnergy p ≤ k0 →
                (∫⁻ y, ENNReal.ofReal
                    (euclideanNorm (y.1.1 - y.2.1) ^ 2)
                    ∂transportCoupledRandomizedMultinomialLeapfrogKernel
                      potential gradient ε L hgradient (hmeas ε L)
                      (((q₁, p), (q₂, p)))) ≤
                  (rate : ENNReal) *
                    ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2) := by
  simpa only [transportCoupledRandomizedMultinomialLeapfrogKernel,
    transportTrajectoryIndexCouplingFamily] using
    (h.coupledRandomizedMultinomialLeapfrogKernel_expectedPositionMoment
      gradient (transportTrajectoryIndexCouplingFamily potential gradient)
      S 2 rate Tmin Tmax hgradient hmeas)

/-- The preceding squared-moment bound gives the paper's conditional relaxed
meeting estimate by Markov's inequality.  It applies to the implemented
transport trajectory kernel, conditional on the shared momentum cutoff. -/
theorem XuCondition1AtExponentOnIntegrationWindow.transportCoupledRandomizedMultinomialLeapfrogKernel_relaxedEntry
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily
      (transportTrajectoryIndexCouplingFamily potential gradient))
    (h : XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
              kineticEnergy p ≤ k0 →
                ∀ δ : ℝ, 0 < δ →
                  1 - ((rate : ENNReal) *
                      ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
                      ENNReal.ofReal (δ ^ 2) ≤
                    transportCoupledRandomizedMultinomialLeapfrogKernel
                      potential gradient ε L hgradient (hmeas ε L)
                      (((q₁, p), (q₂, p)))
                      (phasePositionRelaxedDiagonal δ) := by
  intro k0 hk0
  rcases h.transportCoupledRandomizedMultinomialLeapfrogKernel_expectedSquaredDistance
      potential gradient S rate Tmin Tmax hgradient hmeas k0 hk0 with
    ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ p hp δ hδ
  apply measure_phasePositionRelaxedDiagonal_ge_of_lintegral_sq_le
  exact hbound ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ p hp
  exact hδ

/-- Exponent-two transport contractivity lifts through the paper's shared
standard-Gaussian momentum refresh.  The prefactor is exactly the probability
of the kinetic-energy cutoff; the remaining factor is the conditional
squared-moment Markov bound. -/
theorem XuCondition1AtExponentOnIntegrationWindow.transportSharedMomentumCoupledPositionMultinomialHMC_relaxedEntry
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily
      (transportTrajectoryIndexCouplingFamily potential gradient))
    (h : XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ δ : ℝ, 0 < δ →
              standardMomentumMeasure (ι := ι)
                  {p | kineticEnergy p ≤ k0} *
                  (1 - ((rate : ENNReal) *
                    ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
                    ENNReal.ofReal (δ ^ 2)) ≤
                transportSharedMomentumCoupledPositionMultinomialHMC
                  potential gradient ε L hgradient (hmeas ε L) (q₁, q₂)
                  (positionEuclideanRelaxedDiagonal δ) := by
  intro k0 hk0
  rcases h.transportCoupledRandomizedMultinomialLeapfrogKernel_relaxedEntry
      potential gradient S rate Tmin Tmax hgradient hmeas k0 hk0 with
    ⟨εbar, hεbar, hconditional⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ δ hδ
  unfold transportSharedMomentumCoupledPositionMultinomialHMC
  apply coupledPositionMultinomialHMC_positionRelaxedDiagonal_ge_of_sharedMomentum
    (coupledTrajectory :=
      transportCoupledRandomizedMultinomialLeapfrogKernel
        potential gradient ε L hgradient (hmeas ε L))
    (momentumTarget := standardMomentumMeasure)
    (q := (q₁, q₂)) (cutoff := {p | kineticEnergy p ≤ k0})
    (measurable_kineticEnergy measurableSet_Iic) (δ := δ)
    (c := 1 - ((rate : ENNReal) *
      ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
      ENNReal.ofReal (δ ^ 2))
  intro p hp
  exact hconditional ε hε0 hε L hTmin hTmax
    q₁ hq₁ q₂ hq₂ p hp δ hδ

/-- Whenever the squared-distance budget is strictly smaller than the chosen
relaxed radius, the full shared-momentum transport kernel has a strictly
positive relaxed-entry constant. -/
theorem XuCondition1AtExponentOnIntegrationWindow.transportSharedMomentumCoupledPositionMultinomialHMC_relaxedEntry_pos
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hgradient : Measurable gradient)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily
      (transportTrajectoryIndexCouplingFamily potential gradient))
    (h : XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ δ : ℝ, 0 < δ →
              ((rate : ENNReal) *
                  ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
                  ENNReal.ofReal (δ ^ 2) < 1 →
                ∃ entry : ENNReal, 0 < entry ∧
                  entry ≤
                    transportSharedMomentumCoupledPositionMultinomialHMC
                      potential gradient ε L hgradient (hmeas ε L) (q₁, q₂)
                      (positionEuclideanRelaxedDiagonal δ) := by
  intro k0 hk0
  rcases h.transportSharedMomentumCoupledPositionMultinomialHMC_relaxedEntry
      potential gradient S rate Tmin Tmax hgradient hmeas k0 hk0 with
    ⟨εbar, hεbar, hentry⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ δ hδ hratio
  let ratio := ((rate : ENNReal) *
    ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
    ENNReal.ofReal (δ ^ 2)
  let entry := standardMomentumMeasure (ι := ι)
    {p | kineticEnergy p ≤ k0} * (1 - ratio)
  refine ⟨entry, ?_, ?_⟩
  · dsimp [entry]
    apply ENNReal.mul_pos
    · exact (standardMomentumMeasure_kineticEnergy_le_pos hk0).ne'
    · exact (tsub_pos_iff_lt.mpr hratio).ne'
  · dsimp [entry, ratio]
    exact hentry ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ δ hδ

/-- For exponent two, the general moment cost is exactly the squared-position
cost already used by the maximal and transport coupling bounds. -/
theorem trajectoryPositionMomentCost_two
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    (i j : Fin (L + 1)) :
    trajectoryPositionMomentCost gradient 2 ε z origin i j =
      trajectorySquaredPositionCost gradient ε z origin i j := by
  apply NNReal.eq
  exact euclideanNorm_sq _

/-- Consequently, the exponent-two expected cost in Condition 1 is the
existing transport cost used in the concrete coupling estimates. -/
theorem transportCost_trajectoryPositionMomentCost_two
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    (joint : PMF (Fin (L + 1) × Fin (L + 1))) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 2 ε z origin) joint =
      McmcLean.Finite.transportCost
        (trajectorySquaredPositionCost gradient ε z origin) joint := by
  congr 1
  funext i j
  exact trajectoryPositionMomentCost_two gradient ε z origin i j

/-- For exponent one, the moment cost is the direct Euclidean distance as an
`NNReal`; this theorem records the specialization used below. -/
theorem coe_trajectoryPositionMomentCost_one
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    (i j : Fin (L + 1)) :
    (trajectoryPositionMomentCost gradient 1 ε z origin i j : ENNReal) =
      ENNReal.ofReal (euclideanNorm
        ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
          (offsetLeapfrogTrajectory gradient ε origin z.2 j).1)) := by
  rw [ENNReal.coe_nnreal_eq]
  congr 1
  exact pow_one _

/-- Cauchy--Schwarz specialized to the categorical overlap weights used by
the maximal coupling. A weighted squared-cost bound gives the corresponding
weighted first-moment bound with square-root rate. -/
theorem overlapWeightedFirstMoment_le_sqrtRate
    {κ : Type*} [Fintype κ] (p q : PMF κ) (distance : κ → NNReal)
    (rate initial : NNReal)
    (hsecond : (∑ i, min (p i) (q i) * (distance i ^ 2 : ENNReal)) ≤
      (rate : ENNReal) * (initial ^ 2 : NNReal)) :
    (∑ i, min (p i) (q i) * (distance i : ENNReal)) ≤
      (NNReal.sqrt rate : ENNReal) * initial := by
  let weight : κ → NNReal := fun i => ENNReal.toNNReal (min (p i) (q i))
  have hfinite : ∀ i, min (p i) (q i) ≠ ∞ := by
    intro i
    exact ne_top_of_le_ne_top (p.apply_ne_top i) (min_le_left _ _)
  have hcoe : ∀ i, (weight i : ENNReal) = min (p i) (q i) := by
    intro i
    exact ENNReal.coe_toNNReal (hfinite i)
  have hweight : ∑ i, weight i ≤ 1 := by
    apply ENNReal.coe_le_coe.mp
    push_cast
    calc
      (∑ i, (weight i : ENNReal)) = ∑ i, min (p i) (q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcoe i
      _ ≤ 1 := by
        simpa only [McmcLean.Finite.overlap] using
          McmcLean.Finite.overlap_le_one p q
  have hsecondNN : ∑ i, weight i * distance i ^ 2 ≤
      rate * initial ^ 2 := by
    apply ENNReal.coe_le_coe.mp
    push_cast
    calc
      (∑ i, (weight i : ENNReal) * (distance i : ENNReal) ^ 2) =
          ∑ i, min (p i) (q i) * (distance i : ENNReal) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoe i]
      _ ≤ (rate : ENNReal) * (initial : ENNReal) ^ 2 := hsecond
  have hfirst := weightedFirstMoment_le_sqrtRate weight distance rate initial
    hweight hsecondNN
  have hfirst' := ENNReal.coe_le_coe.mpr hfirst
  push_cast at hfirst'
  simp_rw [hcoe] at hfirst'
  exact hfirst'

/-- Squaring the exponent-one trajectory cost gives the squared-position
cost used by the `W₂` analysis. -/
theorem trajectoryPositionMomentCost_one_sq
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    (i j : Fin (L + 1)) :
    trajectoryPositionMomentCost gradient 1 ε z origin i j ^ 2 =
      trajectorySquaredPositionCost gradient ε z origin i j := by
  apply NNReal.eq
  unfold trajectoryPositionMomentCost trajectorySquaredPositionCost
  simp only [NNReal.coe_pow, pow_one]
  exact euclideanNorm_sq _

/-- The squared initial distance is the square of the first-moment initial
distance. -/
theorem initialPositionDistance_sq (q₁ q₂ : Position ι) :
    initialPositionDistance q₁ q₂ ^ 2 =
      initialSquaredPositionDistance q₁ q₂ := by
  rfl

/-- The completed overlap-weighted squared aligned estimate automatically
implies its first-moment counterpart with square-root rate. -/
theorem trajectoryOverlapWeightedMomentOne_le_sqrtRate
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (q₁ q₂ : Position ι) (rate : NNReal)
    (hsecond :
      (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2) i) *
          (trajectorySquaredPositionCost gradient ε z origin i i : ENNReal)) ≤
        (rate : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal)) :
      (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2) i) *
          (trajectoryPositionMomentCost gradient 1 ε z origin i i : ENNReal)) ≤
        (NNReal.sqrt rate : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) := by
  apply overlapWeightedFirstMoment_le_sqrtRate
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.1))
    (trajectoryIndexPMF potential
      (offsetLeapfrogTrajectory gradient ε origin z.2))
    (fun i => trajectoryPositionMomentCost gradient 1 ε z origin i i)
    rate (initialPositionDistance q₁ q₂)
  convert hsecond using 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    rw [← ENNReal.coe_pow,
      trajectoryPositionMomentCost_one_sq]
  · rw [initialPositionDistance_sq]

/-- A squared overlap-weighted aligned contraction yields the corresponding
first-moment contraction, with the square root of the squared-cost rate. -/
theorem LocalStrongConvexity.exists_uniform_overlapWeightedMomentOneContraction_of_kineticEnergy_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {k0 : ℝ} (hk0 : 0 ≤ k0) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ alignedRate : NNReal, alignedRate < 1 ∧
        ∀ q₁ q₂ : Position ι, ∀ p : Momentum ι,
          q₁ ∈ K → q₂ ∈ K → kineticEnergy p ≤ k0 →
          ∀ {ε : ℝ} {L : ℕ}, 0 ≤ ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ (origin : Fin (L + 1)),
              (∑ i, min
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                  (trajectoryPositionMomentCost gradient 1 ε
                    (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                (alignedRate : ENNReal) *
                  (initialPositionDistance q₁ q₂ : ENNReal) := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
      squaredRate, hsquaredRate, hbound⟩ :=
    hconv.exists_uniform_overlapWeightedAlignedContraction_of_kineticEnergy_le
      hreg hK hKS hScompact hSconvex hk0
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
    NNReal.sqrt squaredRate, ?_, ?_⟩
  · rw [← NNReal.sqrt_one, NNReal.sqrt_lt_sqrt]
    exact hsquaredRate
  · intro q₁ q₂ p hq₁ hq₂ hp ε L hε0 hεbar' hTmin' hTmax' origin
    exact trajectoryOverlapWeightedMomentOne_le_sqrtRate
      potential gradient ε (((q₁, p), (q₂, p))) origin q₁ q₂ squaredRate
      (hbound q₁ q₂ p hq₁ hq₂ hp hε0 hεbar' hTmin' hTmax' origin)

/-- At the trajectory's current-state index, aligned exponent-one cost is
exactly the initial position distance. -/
theorem trajectoryPositionMomentCost_one_origin_eq
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (q₁ q₂ : Position ι) (p : Momentum ι) (origin : Fin (L + 1)) :
    trajectoryPositionMomentCost gradient 1 ε
        (((q₁, p), (q₂, p))) origin origin origin =
      initialPositionDistance q₁ q₂ := by
  apply NNReal.eq
  unfold trajectoryPositionMomentCost initialPositionDistance
  simp [offsetLeapfrogTrajectory]

/-- Consequently, a uniform per-index aligned bound forces its rate to be at
least one on distinct starts. This explains why the overlap-weighted sharp
budget below is necessary for a genuinely contractive result. -/
theorem one_le_alignedRate_of_trajectoryMomentCost_one
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    {q₁ q₂ : Position ι} (p : Momentum ι) (origin : Fin (L + 1))
    {alignedRate : NNReal} (hne : q₁ ≠ q₂)
    (hbound : ∀ i, trajectoryPositionMomentCost gradient 1 ε
      (((q₁, p), (q₂, p))) origin i i ≤
        alignedRate * initialPositionDistance q₁ q₂) :
    1 ≤ alignedRate := by
  have h := hbound origin
  rw [trajectoryPositionMomentCost_one_origin_eq] at h
  have hd : 0 < initialPositionDistance q₁ q₂ := by
    change 0 < euclideanNorm (q₁ - q₂)
    have hsquare := squaredEuclideanNorm_pos (sub_ne_zero.mpr hne)
    rw [← euclideanNorm_sq] at hsquare
    nlinarith [euclideanNorm_nonneg (q₁ - q₂)]
  exact (le_mul_iff_one_le_left hd).mp h

/-- At the current-state index, aligned squared cost is exactly the initial
squared position distance. -/
theorem trajectorySquaredPositionCost_origin_eq
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (q₁ q₂ : Position ι) (p : Momentum ι) (origin : Fin (L + 1)) :
    trajectorySquaredPositionCost gradient ε
        (((q₁, p), (q₂, p))) origin origin origin =
      initialSquaredPositionDistance q₁ q₂ := by
  apply NNReal.eq
  unfold trajectorySquaredPositionCost initialSquaredPositionDistance
  simp [offsetLeapfrogTrajectory, euclideanNorm_sq]

/-- The same obstruction holds at exponent two: a per-index aligned squared
bound on distinct starts necessarily has rate at least one. -/
theorem one_le_alignedRate_of_trajectorySquaredPositionCost
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    {q₁ q₂ : Position ι} (p : Momentum ι) (origin : Fin (L + 1))
    {alignedRate : NNReal} (hne : q₁ ≠ q₂)
    (hbound : ∀ i, trajectorySquaredPositionCost gradient ε
      (((q₁, p), (q₂, p))) origin i i ≤
        alignedRate * initialSquaredPositionDistance q₁ q₂) :
    1 ≤ alignedRate := by
  have h := hbound origin
  rw [trajectorySquaredPositionCost_origin_eq] at h
  have hd : 0 < initialSquaredPositionDistance q₁ q₂ := by
    change 0 < euclideanNorm (q₁ - q₂) ^ 2
    rw [euclideanNorm_sq]
    exact squaredEuclideanNorm_pos (sub_ne_zero.mpr hne)
  exact (le_mul_iff_one_le_left hd).mp h

/-- Exact-reference contraction plus relative approximation errors gives the
aligned exponent-one trajectory-cost bound required by the maximal-coupling
budget.  The reference positions may be supplied by exact Hamiltonian flows
at the selected trajectory time. -/
theorem trajectoryPositionMomentCost_one_le_of_reference
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin i : Fin (L + 1))
    (y₁ y₂ q₁ q₂ : Position ι) (ρ δ₁ δ₂ : NNReal)
    (href : euclideanNorm (y₁ - y₂) ≤
      (ρ : ℝ) * euclideanNorm (q₁ - q₂))
    (herr₁ : euclideanNorm
        ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 - y₁) ≤
      (δ₁ : ℝ) * euclideanNorm (q₁ - q₂))
    (herr₂ : euclideanNorm
        ((offsetLeapfrogTrajectory gradient ε origin z.2 i).1 - y₂) ≤
      (δ₂ : ℝ) * euclideanNorm (q₁ - q₂)) :
    trajectoryPositionMomentCost gradient 1 ε z origin i i ≤
      (ρ + δ₁ + δ₂) * initialPositionDistance q₁ q₂ := by
  apply NNReal.coe_le_coe.mp
  change euclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) ^ 1 ≤
    (((ρ + δ₁ + δ₂) * initialPositionDistance q₁ q₂ : NNReal) : ℝ)
  rw [pow_one]
  push_cast
  exact euclideanNorm_relativeContraction_le_of_reference href herr₁ herr₂

/-- The sharper aligned trajectory bound obtained from relative-displacement
error.  This is the budget-facing form expected from a coupled
leapfrog-versus-exact-flow estimate. -/
theorem trajectoryPositionMomentCost_one_le_of_displacementError
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin i : Fin (L + 1))
    (y₁ y₂ q₁ q₂ : Position ι) (ρ δ : NNReal)
    (href : euclideanNorm (y₁ - y₂) ≤
      (ρ : ℝ) * euclideanNorm (q₁ - q₂))
    (herror : euclideanNorm
        (((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
            (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) -
          (y₁ - y₂)) ≤
      (δ : ℝ) * euclideanNorm (q₁ - q₂)) :
    trajectoryPositionMomentCost gradient 1 ε z origin i i ≤
      (ρ + δ) * initialPositionDistance q₁ q₂ := by
  apply NNReal.coe_le_coe.mp
  change euclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) ^ 1 ≤
    (((ρ + δ) * initialPositionDistance q₁ q₂ : NNReal) : ℝ)
  rw [pow_one]
  push_cast
  exact euclideanNorm_relativeContraction_le_of_displacementError href herror

/-- Exact squared contraction and a relative displacement error give the
aligned exponent-two cost bound used by both maximal and transport coupling
budgets. -/
theorem trajectorySquaredPositionCost_le_of_displacementError
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin i : Fin (L + 1))
    (y₁ y₂ q₁ q₂ : Position ι) (ρ δ : NNReal)
    (href : squaredEuclideanNorm (y₁ - y₂) ≤
      (ρ : ℝ) ^ 2 * squaredEuclideanNorm (q₁ - q₂))
    (herror : euclideanNorm
        (((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
            (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) -
          (y₁ - y₂)) ≤
      (δ : ℝ) * euclideanNorm (q₁ - q₂)) :
    trajectorySquaredPositionCost gradient ε z origin i i ≤
      (ρ + δ) ^ 2 * initialSquaredPositionDistance q₁ q₂ := by
  apply NNReal.coe_le_coe.mp
  change squaredEuclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) ≤
    ((((ρ + δ) ^ 2 * initialSquaredPositionDistance q₁ q₂ : NNReal) : ℝ))
  push_cast
  rw [show (initialSquaredPositionDistance q₁ q₂ : ℝ) =
      squaredEuclideanNorm (q₁ - q₂) by
    exact euclideanNorm_sq (q₁ - q₂)]
  exact squaredEuclideanNorm_relativeContraction_le_of_displacementError
    ρ.coe_nonneg δ.coe_nonneg href herror

/-- Budget-facing composition of exact Hamiltonian contraction with a
relative leapfrog displacement error. Local strong convexity supplies the
exact reference bound; only the uniform trajectory estimates and numerical
error remain as premises. -/
theorem trajectorySquaredPositionCost_le_of_exactFlowMargin
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin i : Fin (L + 1))
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    (q₁ q₂ : Position ι)
    (qExact₁ qExact₂ : ℝ → Position ι)
    (pExact₁ pExact₂ : ℝ → Momentum ι)
    (hcurve₁ : IsHamiltonianCurve gradient qExact₁ pExact₁)
    (hcurve₂ : IsHamiltonianCurve gradient qExact₂ pExact₂)
    {κ θ t : ℝ} (hκ : 0 ≤ κ) (ht : 0 ≤ t)
    (hq₁ : qExact₁ 0 = q₁) (hq₂ : qExact₂ 0 = q₂)
    (hp : pExact₁ 0 = pExact₂ 0)
    (hregion : ∀ s ∈ Set.Icc (0 : ℝ) t,
      qExact₁ s ∈ S ∧ qExact₂ s ∈ S)
    (hmomentum : ∀ s ∈ Set.Icc (0 : ℝ) t,
      squaredEuclideanNorm (pExact₁ s - pExact₂ s) ≤
        (α - κ) * squaredEuclideanNorm (qExact₁ s - qExact₂ s))
    (hseparation : ∀ s ∈ Set.Icc (0 : ℝ) t,
      θ * squaredEuclideanNorm (qExact₁ 0 - qExact₂ 0) ≤
        squaredEuclideanNorm (qExact₁ s - qExact₂ s))
    (ρ δ : NNReal) (hrate : 1 - κ * θ * t ^ 2 ≤ (ρ : ℝ) ^ 2)
    (herror : euclideanNorm
        (((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
            (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) -
          (qExact₁ t - qExact₂ t)) ≤
      (δ : ℝ) * euclideanNorm (q₁ - q₂)) :
    trajectorySquaredPositionCost gradient ε z origin i i ≤
      (ρ + δ) ^ 2 * initialSquaredPositionDistance q₁ q₂ := by
  apply trajectorySquaredPositionCost_le_of_displacementError
    gradient ε z origin i (qExact₁ t) (qExact₂ t) q₁ q₂ ρ δ
  · have hexact := hconv.squaredEuclideanSeparation_le_mul
      hcurve₁ hcurve₂ hκ ht hp hregion hmomentum hseparation
    rw [hq₁, hq₂] at hexact
    exact hexact.trans (mul_le_mul_of_nonneg_right hrate
      (squaredEuclideanNorm_nonneg (q₁ - q₂)))
  · exact herror

/-- Budget-facing two-sided composition in which regularity derives the
relative-momentum estimate. The remaining exact-flow premises are position
containment and multiplicative upper/lower separation bounds. -/
theorem trajectorySquaredPositionCost_le_of_exactFlowPositionBounds
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin i : Fin (L + 1))
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    (q₁ q₂ : Position ι)
    (qExact₁ qExact₂ : ℝ → Position ι)
    (pExact₁ pExact₂ : ℝ → Momentum ι)
    (hcurve₁ : IsHamiltonianCurve gradient qExact₁ pExact₁)
    (hcurve₂ : IsHamiltonianCurve gradient qExact₂ pExact₂)
    {A κ θ t : ℝ} (hA : 0 ≤ A) (hκ : 0 ≤ κ) (hθ : 0 < θ)
    (hq₁ : qExact₁ 0 = q₁) (hq₂ : qExact₂ 0 = q₂)
    (hp : pExact₁ 0 = pExact₂ 0)
    (hbudget :
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 ≤
        (α - κ) * θ)
    (hregion : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      qExact₁ s ∈ S ∧ qExact₂ s ∈ S)
    (hupper : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      euclideanNorm (qExact₁ s - qExact₂ s) ≤
        A * euclideanNorm (qExact₁ 0 - qExact₂ 0))
    (hlower : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      θ * squaredEuclideanNorm (qExact₁ 0 - qExact₂ 0) ≤
        squaredEuclideanNorm (qExact₁ s - qExact₂ s))
    (ρ δ : NNReal) (hrate : 1 - κ * θ * t ^ 2 ≤ (ρ : ℝ) ^ 2)
    (herror : euclideanNorm
        (((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
            (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) -
          (qExact₁ t - qExact₂ t)) ≤
      (δ : ℝ) * euclideanNorm (q₁ - q₂)) :
    trajectorySquaredPositionCost gradient ε z origin i i ≤
      (ρ + δ) ^ 2 * initialSquaredPositionDistance q₁ q₂ := by
  apply trajectorySquaredPositionCost_le_of_displacementError
    gradient ε z origin i (qExact₁ t) (qExact₂ t) q₁ q₂ ρ δ
  · have hexact := hconv.squaredEuclideanSeparation_le_mul_of_positionBounds
      hreg hcurve₁ hcurve₂ hA hκ hθ hp hbudget hregion hupper hlower
    rw [hq₁, hq₂] at hexact
    exact hexact.trans (mul_le_mul_of_nonneg_right hrate
      (squaredEuclideanNorm_nonneg (q₁ - q₂)))
  · exact herror

/-- Fully reduced exact-flow contribution to the aligned trajectory budget.
Global regularity derives relative momentum, and the displacement budget
derives lower separation, so callers only provide uniform upper separation
and containment in the strong-convexity region. -/
theorem trajectorySquaredPositionCost_le_of_exactFlowUpperBound
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin i : Fin (L + 1))
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    (q₁ q₂ : Position ι)
    (qExact₁ qExact₂ : ℝ → Position ι)
    (pExact₁ pExact₂ : ℝ → Momentum ι)
    (hcurve₁ : IsHamiltonianCurve gradient qExact₁ pExact₁)
    (hcurve₂ : IsHamiltonianCurve gradient qExact₂ pExact₂)
    {A δ κ t : ℝ} (hA : 0 ≤ A) (hδ : δ < 1) (hκ : 0 ≤ κ)
    (hq₁ : qExact₁ 0 = q₁) (hq₂ : qExact₂ 0 = q₂)
    (hp : pExact₁ 0 = pExact₂ 0)
    (hdisplacementBudget :
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) * A * |t| ^ 2 ≤ δ)
    (hmomentumBudget :
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) * A * |t|) ^ 2 ≤
        (α - κ) * (1 - δ) ^ 2)
    (hregion : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      qExact₁ s ∈ S ∧ qExact₂ s ∈ S)
    (hupper : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      euclideanNorm (qExact₁ s - qExact₂ s) ≤
        A * euclideanNorm (qExact₁ 0 - qExact₂ 0))
    (ρ errorRate : NNReal)
    (hrate : 1 - κ * (1 - δ) ^ 2 * t ^ 2 ≤ (ρ : ℝ) ^ 2)
    (herror : euclideanNorm
        (((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
            (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) -
          (qExact₁ t - qExact₂ t)) ≤
      (errorRate : ℝ) * euclideanNorm (q₁ - q₂)) :
    trajectorySquaredPositionCost gradient ε z origin i i ≤
      (ρ + errorRate) ^ 2 * initialSquaredPositionDistance q₁ q₂ := by
  apply trajectorySquaredPositionCost_le_of_displacementError
    gradient ε z origin i (qExact₁ t) (qExact₂ t) q₁ q₂ ρ errorRate
  · have hexact := hconv.squaredEuclideanSeparation_le_mul_of_upperBound
      hreg hcurve₁ hcurve₂ hA hδ hκ hp hdisplacementBudget
        hmomentumBudget hregion hupper
    rw [hq₁, hq₂] at hexact
    exact hexact.trans (mul_le_mul_of_nonneg_right hrate
      (squaredEuclideanNorm_nonneg (q₁ - q₂)))
  · exact herror

/-- Aligned numerical trajectory-cost bound with all exact-flow
relative-motion estimates discharged. The only remaining geometric exact-flow
premise is containment in the local strong-convexity region. -/
theorem trajectorySquaredPositionCost_le_of_exactFlowRegion
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin i : Fin (L + 1))
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    (q₁ q₂ : Position ι)
    (qExact₁ qExact₂ : ℝ → Position ι)
    (pExact₁ pExact₂ : ℝ → Momentum ι)
    (hcurve₁ : IsHamiltonianCurve gradient qExact₁ pExact₁)
    (hcurve₂ : IsHamiltonianCurve gradient qExact₂ pExact₂)
    {δ κ t : ℝ} (hδ : δ < 1) (hκ : 0 ≤ κ)
    (hq₁ : qExact₁ 0 = q₁) (hq₂ : qExact₂ 0 = q₂)
    (hp : pExact₁ 0 = pExact₂ 0)
    (hdisplacementBudget :
      ((Fintype.card ι : ℝ) + 1) ^ 2 * (β : ℝ) *
          exactFlowPositionStabilityFactor (ι := ι) β t * |t| ^ 2 ≤ δ)
    (hmomentumBudget :
      (((Fintype.card ι : ℝ) + 1) * (β : ℝ) *
          exactFlowPositionStabilityFactor (ι := ι) β t * |t|) ^ 2 ≤
        (α - κ) * (1 - δ) ^ 2)
    (hregion : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      qExact₁ s ∈ S ∧ qExact₂ s ∈ S)
    (ρ errorRate : NNReal)
    (hrate : 1 - κ * (1 - δ) ^ 2 * t ^ 2 ≤ (ρ : ℝ) ^ 2)
    (herror : euclideanNorm
        (((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
            (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) -
          (qExact₁ t - qExact₂ t)) ≤
      (errorRate : ℝ) * euclideanNorm (q₁ - q₂)) :
    trajectorySquaredPositionCost gradient ε z origin i i ≤
      (ρ + errorRate) ^ 2 * initialSquaredPositionDistance q₁ q₂ := by
  apply trajectorySquaredPositionCost_le_of_displacementError
    gradient ε z origin i (qExact₁ t) (qExact₂ t) q₁ q₂ ρ errorRate
  · have hexact := hconv.squaredEuclideanSeparation_le_mul_of_region
      hreg hcurve₁ hcurve₂ hδ hκ hp hdisplacementBudget
        hmomentumBudget hregion
    rw [hq₁, hq₂] at hexact
    exact hexact.trans (mul_le_mul_of_nonneg_right hrate
      (squaredEuclideanNorm_nonneg (q₁ - q₂)))
  · exact herror

/-- A common Euclidean position ball gives the exponent-one off-diagonal
bound `2R` used in the maximal-coupling argument. -/
theorem trajectoryPositionMomentCost_one_le_of_positionNorm_le
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (z : PhaseSpace ι × PhaseSpace ι) (origin : Fin (L + 1))
    {R : ℝ} (hR : 0 ≤ R)
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (i j : Fin (L + 1)) :
    trajectoryPositionMomentCost gradient 1 ε z origin i j ≤
      ⟨2 * R, by positivity⟩ := by
  apply NNReal.coe_le_coe.mp
  change euclideanNorm
      ((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1) ^ 1 ≤ 2 * R
  rw [pow_one]
  exact (euclideanNorm_sub_le _ _).trans (by
    linarith [hleft i, hright j])

/-- Aligned points of two identical offset trajectories have zero squared
position cost. -/
@[simp]
theorem trajectorySquaredPositionCost_same_start_aligned
    (gradient : Position ι → Position ι) (ε : ℝ) {L : ℕ}
    (q : Position ι) (p : Momentum ι) (origin i : Fin (L + 1)) :
    trajectorySquaredPositionCost gradient ε
      (((q, p), (q, p))) origin i i = 0 := by
  apply NNReal.eq
  change squaredEuclideanNorm (_ - _) = 0
  rw [sub_self]
  exact squaredEuclideanNorm_eq_zero.mpr rfl

/-- Identical offset trajectories induce zero total-variation mismatch. -/
@[simp]
theorem trajectoryIndexPMF_totalVariation_same_start
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (q : Position ι) (p : Momentum ι)
    (origin : Fin (L + 1)) :
    McmcLean.Finite.totalVariation
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin (q, p)))
      (trajectoryIndexPMF potential
        (offsetLeapfrogTrajectory gradient ε origin (q, p))) = 0 := by
  exact McmcLean.Finite.totalVariation_self _

/-- At coincident starts with shared momentum, maximal trajectory coupling has
exactly zero exponent-two position cost. -/
theorem maximalTrajectoryIndexCoupling_moment_two_same_start
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (q : Position ι) (p : Momentum ι)
    (origin : Fin (L + 1)) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 2 ε
          (((q, p), (q, p))) origin)
        (maximalTrajectoryIndexCoupling potential gradient ε
          (((q, p), (q, p))) origin) = 0 := by
  rw [transportCost_trajectoryPositionMomentCost_two]
  unfold maximalTrajectoryIndexCoupling
  rw [McmcLean.Finite.maximalCoupling_self]
  apply McmcLean.Finite.transportCost_diagonalCoupling_eq_zero
  exact trajectorySquaredPositionCost_same_start_aligned gradient ε q p origin

/-- Squared-cost optimality gives the same zero-cost boundary result for the
transport trajectory coupling. -/
theorem transportTrajectoryIndexCoupling_moment_two_same_start
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (q : Position ι) (p : Momentum ι)
    (origin : Fin (L + 1)) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 2 ε
          (((q, p), (q, p))) origin)
        (transportTrajectoryIndexCoupling potential gradient ε
          (((q, p), (q, p))) origin) = 0 := by
  apply le_antisymm
  · rw [transportCost_trajectoryPositionMomentCost_two]
    exact (transportTrajectoryIndexCoupling_cost_le_maximal
      potential gradient ε (((q, p), (q, p))) origin).trans_eq
        (by
          rw [← transportCost_trajectoryPositionMomentCost_two]
          exact maximalTrajectoryIndexCoupling_moment_two_same_start
            potential gradient ε q p origin)
  · exact bot_le

/-- Squared-cost optimality makes exponent-two local contractivity transfer
from the maximal trajectory-index coupling to the transport coupling, with
the same rate and uniform numerical thresholds. -/
theorem transport_xuCondition1AtExponent_two_of_maximal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal)
    (hmax : XuCondition1AtExponent
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate) :
    XuCondition1AtExponent
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate := by
  refine ⟨hmax.1, ?_⟩
  intro k0 hk0
  rcases hmax.2 k0 hk0 with ⟨εbar, hεbar, Lbar, hLbar, hbound⟩
  refine ⟨εbar, hεbar, Lbar, hLbar, ?_⟩
  intro ε hε0 hε L hlength origin q₁ hq₁ q₂ hq₂ p hp
  have hmaxBound := hbound ε hε0 hε L hlength origin
    q₁ hq₁ q₂ hq₂ p hp
  rw [transportCost_trajectoryPositionMomentCost_two] at hmaxBound ⊢
  exact (transportTrajectoryIndexCoupling_cost_le_maximal
    potential gradient ε (((q₁, p), (q₂, p))) origin).trans hmaxBound

/-- Squared-cost optimality also transfers the repaired positive-window
exponent-two condition from maximal to transport coupling. -/
theorem optimalTrajectoryIndexCouplingFamily_xuCondition1AtExponentOnIntegrationWindow_two_of_maximal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (hoptimal : IsOptimalTrajectoryIndexCouplingFamily
      potential gradient family)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hmax : XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    XuCondition1AtExponentOnIntegrationWindow
      family gradient S 2 rate Tmin Tmax := by
  refine ⟨hmax.1, hmax.2.1, hmax.2.2.1, ?_⟩
  intro k0 hk0
  rcases hmax.2.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p hp
  have hmaxBound := hbound ε hε0 hε L hTmin hTmax origin
    q₁ hq₁ q₂ hq₂ p hp
  rw [transportCost_trajectoryPositionMomentCost_two] at hmaxBound ⊢
  exact (hoptimal.2 ε L (((q₁, p), (q₂, p))) origin
    (maximalTrajectoryIndexCoupling potential gradient ε
      (((q₁, p), (q₂, p))) origin)
    (maximalTrajectoryIndexCoupling_isMaximal potential gradient ε
      (((q₁, p), (q₂, p))) origin).1).trans hmaxBound

/-- Any measurable pointwise-optimal selector—not specifically the legacy
`Classical.choose` selector—therefore yields the full shared-momentum
position-kernel relaxed-entry estimate.  This is the executable theorem
surface that a constructive finite selector must instantiate. -/
theorem optimalTrajectoryIndexCouplingFamilySharedMomentumHMC_relaxedEntry
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (family : TrajectoryIndexCouplingFamily ι)
    (hoptimal : IsOptimalTrajectoryIndexCouplingFamily
      potential gradient family)
    (hmeas : IsMeasurableTrajectoryIndexCouplingFamily family)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hgradient : Measurable gradient)
    (hmax : XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ δ : ℝ, 0 < δ →
              standardMomentumMeasure (ι := ι)
                  {p | kineticEnergy p ≤ k0} *
                  (1 - ((rate : ENNReal) *
                    ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
                    ENNReal.ofReal (δ ^ 2)) ≤
                trajectoryIndexCouplingFamilySharedMomentumHMC
                  gradient family ε L hgradient hmeas (q₁, q₂)
                  (positionEuclideanRelaxedDiagonal δ) := by
  have hcondition :=
    optimalTrajectoryIndexCouplingFamily_xuCondition1AtExponentOnIntegrationWindow_two_of_maximal
      potential gradient family hoptimal S rate Tmin Tmax hmax
  rcases hcondition.coupledRandomizedMultinomialLeapfrogKernel_expectedPositionMoment
      gradient family S 2 rate Tmin Tmax hgradient hmeas with hmoment
  intro k0 hk0
  rcases hmoment k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ δ hδ
  unfold trajectoryIndexCouplingFamilySharedMomentumHMC
  apply coupledPositionMultinomialHMC_positionRelaxedDiagonal_ge_of_sharedMomentum
    (coupledTrajectory := trajectoryIndexCouplingFamilyKernel
      gradient family ε L hgradient hmeas)
    (momentumTarget := standardMomentumMeasure)
    (q := (q₁, q₂)) (cutoff := {p | kineticEnergy p ≤ k0})
    (measurable_kineticEnergy measurableSet_Iic) (δ := δ)
    (c := 1 - ((rate : ENNReal) *
      ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
      ENNReal.ofReal (δ ^ 2))
  intro p hp
  apply measure_phasePositionRelaxedDiagonal_ge_of_lintegral_sq_le
  · unfold trajectoryIndexCouplingFamilyKernel
    exact hbound ε hε0 hε L hTmin hTmax q₁ hq₁ q₂ hq₂ p hp
  · exact hδ

/-- The constructive greedy selector itself has the full shared-momentum
transport-HMC relaxed-entry bound. -/
theorem greedyTransportTrajectoryIndexCouplingFamilySharedMomentumHMC_relaxedEntry
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hmax : XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ δ : ℝ, 0 < δ →
              standardMomentumMeasure (ι := ι)
                  {p | kineticEnergy p ≤ k0} *
                  (1 - ((rate : ENNReal) *
                    ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)) /
                    ENNReal.ofReal (δ ^ 2)) ≤
                trajectoryIndexCouplingFamilySharedMomentumHMC gradient
                  (greedyTransportTrajectoryIndexCouplingFamily
                    potential gradient)
                  ε L hgradient
                  (greedyTransportTrajectoryIndexCouplingFamily_isMeasurable
                    potential gradient hpotential hgradient)
                  (q₁, q₂) (positionEuclideanRelaxedDiagonal δ) :=
  optimalTrajectoryIndexCouplingFamilySharedMomentumHMC_relaxedEntry
    potential gradient
    (greedyTransportTrajectoryIndexCouplingFamily potential gradient)
    (greedyTransportTrajectoryIndexCouplingFamily_isOptimal
      potential gradient)
    (greedyTransportTrajectoryIndexCouplingFamily_isMeasurable
      potential gradient hpotential hgradient)
    S rate Tmin Tmax hgradient hmax

/-- Squared-cost optimality also transfers the repaired positive-window
exponent-two condition from maximal to the legacy classically selected
transport coupling. -/
theorem transport_xuCondition1AtExponentOnIntegrationWindow_two_of_maximal
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal) (Tmin Tmax : ℝ)
    (hmax : XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax) :
    XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate Tmin Tmax := by
  refine ⟨hmax.1, hmax.2.1, hmax.2.2.1, ?_⟩
  intro k0 hk0
  rcases hmax.2.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p hp
  have hmaxBound := hbound ε hε0 hε L hTmin hTmax origin
    q₁ hq₁ q₂ hq₂ p hp
  rw [transportCost_trajectoryPositionMomentCost_two] at hmaxBound ⊢
  exact (transportTrajectoryIndexCoupling_cost_le_maximal
    potential gradient ε (((q₁, p), (q₂, p))) origin).trans hmaxBound

/-- Hence a positive subunit exponent-two Condition 1 certificate for the
maximal coupling gives the full Condition 1 statement for the transport
coupling. -/
theorem transport_xuCondition1_of_maximal_exponent_two
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) {rate : NNReal}
    (hmax : XuCondition1AtExponent
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate)
    (hrate0 : 0 < rate) (hrate1 : rate < 1) :
    XuCondition1 (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S rate :=
  (transport_xuCondition1AtExponent_two_of_maximal
    potential gradient S rate hmax).xuCondition1 hrate0 hrate1

/-- The existing aligned-cost plus total-variation estimate discharges the
exponent-two Condition 1 inequality for the maximal coupling whenever its two
error terms fit inside the requested contraction budget. -/
theorem maximalTrajectoryIndexCoupling_moment_two_le
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound mismatchBound : NNReal)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound)
    (hmismatch : ∀ i j, i ≠ j →
      trajectorySquaredPositionCost gradient ε z origin i j ≤ mismatchBound)
    (budget : ENNReal)
    (hbudget : (diagonalBound : ENNReal) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) ≤ budget) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 2 ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      budget := by
  rw [transportCost_trajectoryPositionMomentCost_two]
  exact (maximalTrajectoryIndexCoupling_cost_le_add_totalVariation_mul
    potential gradient ε z origin diagonalBound mismatchBound
      hdiagonal hmismatch).trans hbudget

/-- For exponent one, maximal coupling gives the paper's first-moment
decomposition: aligned trajectory distance plus total variation times an
off-diagonal distance bound. -/
theorem maximalTrajectoryIndexCoupling_moment_one_le
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound mismatchBound : NNReal)
    (hdiagonal : ∀ i,
      trajectoryPositionMomentCost gradient 1 ε z origin i i ≤ diagonalBound)
    (hmismatch : ∀ i j, i ≠ j →
      trajectoryPositionMomentCost gradient 1 ε z origin i j ≤ mismatchBound)
    (budget : ENNReal)
    (hbudget : (diagonalBound : ENNReal) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) ≤ budget) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 1 ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      budget := by
  exact ((maximalTrajectoryIndexCoupling_isMaximal
    potential gradient ε z origin).transportCost_le_add_totalVariation_mul
      (trajectoryPositionMomentCost gradient 1 ε z origin)
      diagonalBound mismatchBound hdiagonal hmismatch).trans hbudget

/-- Sharp exponent-one maximal-coupling decomposition.  Unlike the uniform
diagonal bound above, this retains the overlap-weighted aligned cost.  This is
essential because the trajectory's current-state index has contraction factor
exactly one even when the averaged aligned selection contracts. -/
theorem maximalTrajectoryIndexCoupling_moment_one_le_overlap
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (mismatchBound : NNReal)
    (hmismatch : ∀ i j, i ≠ j →
      trajectoryPositionMomentCost gradient 1 ε z origin i j ≤ mismatchBound) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 1 ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2) i) *
          (trajectoryPositionMomentCost gradient 1 ε z origin i i : ENNReal)) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) := by
  unfold maximalTrajectoryIndexCoupling
  exact McmcLean.Finite.maximalCoupling_transportCost_le_diagonal_add_totalVariation_mul
    _ _ _ mismatchBound hmismatch

/-- The concrete exponent-one maximal-coupling estimate when both finite
trajectories stay in a common position ball. -/
theorem maximalTrajectoryIndexCoupling_moment_one_le_of_positionNorm_le
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound : NNReal)
    {R : ℝ} (hR : 0 ≤ R)
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (hdiagonal : ∀ i,
      trajectoryPositionMomentCost gradient 1 ε z origin i i ≤ diagonalBound) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 1 ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      (diagonalBound : ENNReal) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          ENNReal.ofNNReal (⟨2 * R, by positivity⟩ : NNReal) := by
  apply maximalTrajectoryIndexCoupling_moment_one_le potential gradient ε z
    origin diagonalBound ⟨2 * R, by positivity⟩ hdiagonal
  · intro i j hij
    exact trajectoryPositionMomentCost_one_le_of_positionNorm_le
      gradient ε z origin hR hleft hright i j
  · exact le_rfl

/-- A small Hamiltonian discrepancy proportional to initial position
separation gives the relative TV-mismatch term required by the exponent-one
maximal-coupling budget.  The scalar condition accounts for the chosen
off-diagonal cost bound. -/
theorem trajectoryIndexPMF_totalVariation_mul_le_of_relative_energy
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (q₁ q₂ : Position ι)
    (radius energyRate mismatchBound mismatchRate : NNReal)
    (hradiusSmall : (radius : ℝ) ≤ 1 / 2)
    (henergy : ∀ i,
      |energy potential (offsetLeapfrogTrajectory gradient ε origin z.1 i) -
        energy potential (offsetLeapfrogTrajectory gradient ε origin z.2 i)| ≤
          (radius : ℝ))
    (hrelative : radius ≤ energyRate * initialPositionDistance q₁ q₂)
    (hrates : 4 * energyRate * mismatchBound ≤ mismatchRate) :
    McmcLean.Finite.totalVariation
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.1))
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.2)) *
        (mismatchBound : ENNReal) ≤
      (mismatchRate : ENNReal) *
        (initialPositionDistance q₁ q₂ : ENNReal) := by
  have htv := trajectoryIndexPMF_totalVariation_le_four_mul_of_abs_energy_sub_le
    potential
    (offsetLeapfrogTrajectory gradient ε origin z.1)
    (offsetLeapfrogTrajectory gradient ε origin z.2)
    radius.coe_nonneg hradiusSmall henergy
  have hradius : 4 * radius ≤
      4 * (energyRate * initialPositionDistance q₁ q₂) :=
    mul_le_mul_right hrelative 4
  calc
    McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) ≤
        ENNReal.ofReal (4 * (radius : ℝ)) *
          (mismatchBound : ENNReal) := by
      simpa only [mul_comm] using
        mul_le_mul_right htv (mismatchBound : ENNReal)
    _ = ((4 * radius : NNReal) : ENNReal) *
          (mismatchBound : ENNReal) := by
      congr 1
      rw [ENNReal.coe_nnreal_eq]
      congr 1
    _ ≤ ((4 * (energyRate * initialPositionDistance q₁ q₂) : NNReal) :
          ENNReal) * (mismatchBound : ENNReal) :=
      by
        simpa only [mul_comm] using
          mul_le_mul_right (ENNReal.coe_le_coe.mpr hradius)
            (mismatchBound : ENNReal)
    _ = ((4 * energyRate * mismatchBound : NNReal) : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) := by
      push_cast
      ring
    _ ≤ (mismatchRate : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) :=
      by
        simpa only [mul_comm] using
          mul_le_mul_right (ENNReal.coe_le_coe.mpr hrates)
            (initialPositionDistance q₁ q₂ : ENNReal)

/-- Baseline-canceling version of the relative TV-mismatch bridge.  It only
requires the two centered energy-defect profiles to be relatively close,
which is the natural numerical estimate for trajectories with different
initial Hamiltonians. -/
theorem trajectoryIndexPMF_totalVariation_mul_le_of_relative_centeredEnergy
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (q₁ q₂ : Position ι)
    (center₁ center₂ : ℝ)
    (radius energyRate mismatchBound mismatchRate : NNReal)
    (hradiusSmall : (radius : ℝ) ≤ 1 / 2)
    (hdefect : ∀ i,
      |(energy potential (offsetLeapfrogTrajectory gradient ε origin z.1 i) -
          center₁) -
        (energy potential (offsetLeapfrogTrajectory gradient ε origin z.2 i) -
          center₂)| ≤ (radius : ℝ))
    (hrelative : radius ≤ energyRate * initialPositionDistance q₁ q₂)
    (hrates : 4 * energyRate * mismatchBound ≤ mismatchRate) :
    McmcLean.Finite.totalVariation
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.1))
        (trajectoryIndexPMF potential
          (offsetLeapfrogTrajectory gradient ε origin z.2)) *
        (mismatchBound : ENNReal) ≤
      (mismatchRate : ENNReal) *
        (initialPositionDistance q₁ q₂ : ENNReal) := by
  have htv :=
    trajectoryIndexPMF_totalVariation_le_four_mul_of_centeredDifference
      potential
      (offsetLeapfrogTrajectory gradient ε origin z.1)
      (offsetLeapfrogTrajectory gradient ε origin z.2)
      center₁ center₂ radius.coe_nonneg hradiusSmall hdefect
  have hradius : 4 * radius ≤
      4 * (energyRate * initialPositionDistance q₁ q₂) :=
    mul_le_mul_right hrelative 4
  calc
    McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) ≤
        ENNReal.ofReal (4 * (radius : ℝ)) *
          (mismatchBound : ENNReal) := by
      simpa only [mul_comm] using
        mul_le_mul_right htv (mismatchBound : ENNReal)
    _ = ((4 * radius : NNReal) : ENNReal) *
          (mismatchBound : ENNReal) := by
      congr 1
      rw [ENNReal.coe_nnreal_eq]
      congr 1
    _ ≤ ((4 * (energyRate * initialPositionDistance q₁ q₂) : NNReal) :
          ENNReal) * (mismatchBound : ENNReal) := by
      simpa only [mul_comm] using
        mul_le_mul_right (ENNReal.coe_le_coe.mpr hradius)
          (mismatchBound : ENNReal)
    _ = ((4 * energyRate * mismatchBound : NNReal) : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) := by
      push_cast
      ring
    _ ≤ (mismatchRate : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) := by
      simpa only [mul_comm] using
        mul_le_mul_right (ENNReal.coe_le_coe.mpr hrates)
          (initialPositionDistance q₁ q₂ : ENNReal)

/-- The relative centered-energy property closes the TV-weighted mismatch
term with any prescribed positive rate at most one. -/
theorem UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow.exists_uniform_relativeMismatchBudget
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T)
    (hrelative : UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
      potential gradient K k0 T)
    (mismatchRate : NNReal) (hmismatch : 0 < mismatchRate)
    (hmismatchOne : mismatchRate ≤ 1) :
    ∃ εbar > 0, ∃ mismatchBound : NNReal,
      ∀ {ε : ℝ}, 0 < ε → ε < εbar →
        ∀ {L : ℕ}, ε * (L : ℝ) ≤ T →
          ∀ (origin : Fin (L + 1)), ∀ q₁ ∈ K, ∀ q₂ ∈ K,
            ∀ p : Momentum ι, kineticEnergy p ≤ k0 →
              (∀ i j, trajectorySquaredPositionCost gradient ε
                (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
              McmcLean.Finite.totalVariation
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                  (mismatchBound : ENNReal) ≤
                (mismatchRate : ENNReal) *
                  (initialPositionDistance q₁ q₂ : ENNReal) := by
  obtain ⟨R, hR, hposition⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanNorm_bound hK
  let positionBound : NNReal := ⟨R, hR.le⟩
  obtain ⟨εcost, hεcost, mismatchBound, hcost⟩ :=
    hreg.exists_uniform_totalVariation_mul_squaredCost_lt
      hK hk0 hT (show (0 : ENNReal) < 1 by simp)
  obtain ⟨energyRate, henergyRate, hrates, hradius⟩ :=
    exists_relativeEnergyRate positionBound mismatchBound mismatchRate
      hmismatch hmismatchOne
  obtain ⟨εenergy, hεenergy, henergy⟩ :=
    hrelative energyRate henergyRate
  let εbar := min (εcost / 2) (εenergy / 2)
  have hεbar : 0 < εbar :=
    lt_min (half_pos hεcost) (half_pos hεenergy)
  refine ⟨εbar, hεbar, mismatchBound, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp
  have hεcost' : ε < εcost :=
    (hε.trans_le (min_le_left _ _)).trans (half_lt_self hεcost)
  have hεenergy' : ε < εenergy :=
    (hε.trans_le (min_le_right _ _)).trans (half_lt_self hεenergy)
  have hcost' := hcost hεpos hεcost' horizon origin
    q₁ hq₁ q₂ hq₂ p hp
  refine ⟨hcost'.1, ?_⟩
  let d := initialPositionDistance q₁ q₂
  let radius := energyRate * d
  have hd : d ≤ 2 * positionBound := by
    apply NNReal.coe_le_coe.mp
    change euclideanNorm (q₁ - q₂) ≤ 2 * R
    exact (euclideanNorm_sub_le q₁ q₂).trans (by
      have h₁ := hposition q₁ hq₁
      have h₂ := hposition q₂ hq₂
      linarith)
  have hradiusSmall : radius ≤ 1 / 2 := by
    exact (mul_le_mul_right hd energyRate).trans hradius
  have hdefect : ∀ i,
      |(energy potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p) i) -
          energy potential (q₁, p)) -
        (energy potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p) i) -
          energy potential (q₂, p))| ≤ (radius : ℝ) := by
    intro i
    change _ ≤ (energyRate : ℝ) * euclideanNorm (q₁ - q₂)
    exact henergy hεpos hεenergy' horizon origin q₁ hq₁ q₂ hq₂ p hp i
  exact trajectoryIndexPMF_totalVariation_mul_le_of_relative_centeredEnergy
    potential gradient ε (((q₁, p), (q₂, p))) origin q₁ q₂
    (energy potential (q₁, p)) (energy potential (q₂, p))
    radius energyRate mismatchBound mismatchRate
    (by exact_mod_cast hradiusSmall) hdefect le_rfl hrates

/-- First-moment form of the relative mismatch budget.  The uniform
cross-trajectory distance bound is the square root of the corresponding
squared-cost bound. -/
theorem UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow.exists_uniform_relativeMomentOneMismatchBudget
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {k0 T : ℝ} (hk0 : 0 ≤ k0) (hT : 0 ≤ T)
    (hrelative : UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
      potential gradient K k0 T)
    (mismatchRate : NNReal) (hmismatch : 0 < mismatchRate)
    (hmismatchOne : mismatchRate ≤ 1) :
    ∃ εbar > 0, ∃ mismatchBound : NNReal,
      ∀ {ε : ℝ}, 0 < ε → ε < εbar →
        ∀ {L : ℕ}, ε * (L : ℝ) ≤ T →
          ∀ (origin : Fin (L + 1)), ∀ q₁ ∈ K, ∀ q₂ ∈ K,
            ∀ p : Momentum ι, kineticEnergy p ≤ k0 →
              (∀ i j, trajectoryPositionMomentCost gradient 1 ε
                (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
              McmcLean.Finite.totalVariation
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                  (trajectoryIndexPMF potential
                    (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                  (mismatchBound : ENNReal) ≤
                (mismatchRate : ENNReal) *
                  (initialPositionDistance q₁ q₂ : ENNReal) := by
  obtain ⟨R, hR, hposition⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanNorm_bound hK
  let positionBound : NNReal := ⟨R, hR.le⟩
  obtain ⟨εcost, hεcost, squaredBound, hcost⟩ :=
    hreg.exists_uniform_totalVariation_mul_squaredCost_lt
      hK hk0 hT (show (0 : ENNReal) < 1 by simp)
  let mismatchBound := NNReal.sqrt squaredBound
  obtain ⟨energyRate, henergyRate, hrates, hradius⟩ :=
    exists_relativeEnergyRate positionBound mismatchBound mismatchRate
      hmismatch hmismatchOne
  obtain ⟨εenergy, hεenergy, henergy⟩ :=
    hrelative energyRate henergyRate
  let εbar := min (εcost / 2) (εenergy / 2)
  have hεbar : 0 < εbar :=
    lt_min (half_pos hεcost) (half_pos hεenergy)
  refine ⟨εbar, hεbar, mismatchBound, ?_⟩
  intro ε hεpos hε L horizon origin q₁ hq₁ q₂ hq₂ p hp
  have hεcost' : ε < εcost :=
    (hε.trans_le (min_le_left _ _)).trans (half_lt_self hεcost)
  have hεenergy' : ε < εenergy :=
    (hε.trans_le (min_le_right _ _)).trans (half_lt_self hεenergy)
  have hcost' := hcost hεpos hεcost' horizon origin
    q₁ hq₁ q₂ hq₂ p hp
  constructor
  · intro i j
    apply NNReal.le_sqrt_iff_sq_le.mpr
    rw [trajectoryPositionMomentCost_one_sq]
    exact hcost'.1 i j
  · let d := initialPositionDistance q₁ q₂
    let radius := energyRate * d
    have hd : d ≤ 2 * positionBound := by
      apply NNReal.coe_le_coe.mp
      change euclideanNorm (q₁ - q₂) ≤ 2 * R
      exact (euclideanNorm_sub_le q₁ q₂).trans (by
        have h₁ := hposition q₁ hq₁
        have h₂ := hposition q₂ hq₂
        linarith)
    have hradiusSmall : radius ≤ 1 / 2 :=
      (mul_le_mul_right hd energyRate).trans hradius
    have hdefect : ∀ i,
        |(energy potential
              (offsetLeapfrogTrajectory gradient ε origin (q₁, p) i) -
            energy potential (q₁, p)) -
          (energy potential
              (offsetLeapfrogTrajectory gradient ε origin (q₂, p) i) -
            energy potential (q₂, p))| ≤ (radius : ℝ) := by
      intro i
      change _ ≤ (energyRate : ℝ) * euclideanNorm (q₁ - q₂)
      exact henergy hεpos hεenergy' horizon origin q₁ hq₁ q₂ hq₂ p hp i
    exact trajectoryIndexPMF_totalVariation_mul_le_of_relative_centeredEnergy
      potential gradient ε (((q₁, p), (q₂, p))) origin q₁ q₂
      (energy potential (q₁, p)) (energy potential (q₂, p))
      radius energyRate mismatchBound mismatchRate
      (by exact_mod_cast hradiusSmall) hdefect le_rfl hrates

/-- Fixed-kinetic-cutoff exponent-one local contractivity for the maximal
multinomial trajectory-index coupling.  Uniformity over all kinetic cutoffs
requires a further quantifier-management step; this theorem records the full
analytic assembly at each fixed cutoff. -/
theorem LocalStrongConvexity.exists_maximalTrajectoryIndexCoupling_moment_one_contraction_of_kineticEnergy_le
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {k0 : ℝ} (hk0 : 0 ≤ k0)
    (hrelative : ∀ T : ℝ, 0 ≤ T →
      UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
        potential gradient K k0 T) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ rate : NNReal, rate < 1 ∧
        ∀ q₁ q₂ : Position ι, ∀ p : Momentum ι,
          q₁ ∈ K → q₂ ∈ K → kineticEnergy p ≤ k0 →
          ∀ {ε : ℝ} {L : ℕ}, 0 < ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ (origin : Fin (L + 1)),
              McmcLean.Finite.transportCost
                  (trajectoryPositionMomentCost gradient 1 ε
                    (((q₁, p), (q₂, p))) origin)
                  (maximalTrajectoryIndexCoupling potential gradient ε
                    (((q₁, p), (q₂, p))) origin) ≤
                (rate : ENNReal) *
                  (initialPositionDistance q₁ q₂ : ENNReal) := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εaligned, hεaligned,
      alignedRate, halignedRate, haligned⟩ :=
    hconv.exists_uniform_overlapWeightedMomentOneContraction_of_kineticEnergy_le
      hreg hK hKS hScompact hSconvex hk0
  let mismatchRate : NNReal := (1 - alignedRate) / 2
  have hmismatchPos : 0 < mismatchRate := by
    dsimp [mismatchRate]
    exact div_pos (tsub_pos_iff_lt.mpr halignedRate) (by norm_num)
  have hmismatchOne : mismatchRate ≤ 1 := by
    dsimp [mismatchRate]
    exact (div_le_self (by positivity : (0 : NNReal) ≤ 1 - alignedRate)
      (by norm_num : (1 : NNReal) ≤ 2)).trans tsub_le_self
  have hrates : alignedRate + mismatchRate < 1 := by
    have hcancel : alignedRate + (1 - alignedRate) = 1 :=
      add_tsub_cancel_of_le halignedRate.le
    dsimp [mismatchRate]
    calc
      alignedRate + (1 - alignedRate) / 2 <
          alignedRate + (1 - alignedRate) := by
        simpa only [add_comm] using add_lt_add_left
          (div_lt_self (tsub_pos_iff_lt.mpr halignedRate)
            (by norm_num : (1 : NNReal) < 2)) alignedRate
      _ = 1 := hcancel
  have hTmax0 : 0 ≤ Tmax := (hTmin.trans hTmax).le
  obtain ⟨εmismatch, hεmismatch, mismatchBound, hmismatch⟩ :=
    (hrelative Tmax hTmax0).exists_uniform_relativeMomentOneMismatchBudget
      hreg hK hk0 hTmax0 mismatchRate hmismatchPos hmismatchOne
  let εbar := min εaligned (εmismatch / 2)
  have hεbar : 0 < εbar :=
    lt_min hεaligned (half_pos hεmismatch)
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
    alignedRate + mismatchRate, hrates, ?_⟩
  intro q₁ q₂ p hq₁ hq₂ hp ε L hεpos hεbar' hTmin' hTmax' origin
  have hεaligned' : ε ≤ εaligned :=
    hεbar'.trans (min_le_left _ _)
  have hεmismatch' : ε < εmismatch :=
    (hεbar'.trans (min_le_right _ _)).trans_lt
      (half_lt_self hεmismatch)
  have haligned' := haligned q₁ q₂ p hq₁ hq₂ hp hεpos.le
    hεaligned' hTmin' hTmax' origin
  obtain ⟨hcross, htv⟩ := hmismatch hεpos hεmismatch' hTmax'
    origin q₁ hq₁ q₂ hq₂ p hp
  apply (maximalTrajectoryIndexCoupling_moment_one_le_overlap
    potential gradient ε (((q₁, p), (q₂, p))) origin mismatchBound
      (fun i j _ => hcross i j)).trans
  calc
    (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
          (trajectoryPositionMomentCost gradient 1 ε
            (((q₁, p), (q₂, p))) origin i i : ENNReal)) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
          (mismatchBound : ENNReal) ≤
        (alignedRate : ENNReal) *
            (initialPositionDistance q₁ q₂ : ENNReal) +
          (mismatchRate : ENNReal) *
            (initialPositionDistance q₁ q₂ : ENNReal) :=
      add_le_add haligned' htv
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
        (initialPositionDistance q₁ q₂ : ENNReal) := by
      push_cast
      ring

/-- Assumptions 1 and 2 close the fixed-cutoff maximal-coupling contraction
without an additional numerical-analysis premise.  The relative centered
energy estimate is supplied by the general `C²` one-step theorem. -/
theorem LocalStrongConvexity.exists_maximalTrajectoryIndexCoupling_moment_one_contraction_of_regularPotential
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {k0 : ℝ} (hk0 : 0 ≤ k0) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ rate : NNReal, rate < 1 ∧
        ∀ q₁ q₂ : Position ι, ∀ p : Momentum ι,
          q₁ ∈ K → q₂ ∈ K → kineticEnergy p ≤ k0 →
          ∀ {ε : ℝ} {L : ℕ}, 0 < ε → ε ≤ εbar →
            Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ origin : Fin (L + 1),
              McmcLean.Finite.transportCost
                  (trajectoryPositionMomentCost gradient 1 ε
                    (((q₁, p), (q₂, p))) origin)
                  (maximalTrajectoryIndexCoupling potential gradient ε
                    (((q₁, p), (q₂, p))) origin) ≤
                (rate : ENNReal) *
                  (initialPositionDistance q₁ q₂ : ENNReal) := by
  apply hconv.exists_maximalTrajectoryIndexCoupling_moment_one_contraction_of_kineticEnergy_le
    hreg hK hKS hScompact hSconvex hk0
  intro T hT
  exact (((hreg.locallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
      |>.toPaired hreg).toSharedMomentumSigned hreg).onCompactWindow
        hK hk0 hT)

/-- Kernel-level fixed-cutoff contraction for the implemented randomized-
origin maximal multinomial coupling. -/
theorem LocalStrongConvexity.exists_maximalCoupledRandomizedMultinomialLeapfrogKernel_expectedDistance
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) {k0 : ℝ} (hk0 : 0 ≤ k0)
    (hpotential : Measurable potential) (hgradient : Measurable gradient) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ εbar > 0,
      ∃ rate : NNReal, rate < 1 ∧
        ∀ {ε : ℝ} {L : ℕ}, 0 < ε → ε ≤ εbar →
          Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
          ∀ q₁ ∈ K, ∀ q₂ ∈ K, ∀ p : Momentum ι,
            kineticEnergy p ≤ k0 →
              (∫⁻ y, ENNReal.ofReal
                  (euclideanNorm (y.1.1 - y.2.1))
                ∂maximalCoupledRandomizedMultinomialLeapfrogKernel
                  potential gradient ε L hpotential hgradient
                  (((q₁, p), (q₂, p)))) ≤
                (rate : ENNReal) *
                  ENNReal.ofReal (euclideanNorm (q₁ - q₂)) := by
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
      rate, hrate, hbound⟩ :=
    hconv.exists_maximalTrajectoryIndexCoupling_moment_one_contraction_of_regularPotential
      hreg hK hKS hScompact hSconvex hk0
  refine ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar, rate, hrate, ?_⟩
  intro ε L hεpos hεbar' hTmin' hTmax' q₁ hq₁ q₂ hq₂ p hp
  unfold maximalCoupledRandomizedMultinomialLeapfrogKernel
  apply coupledRandomizedMultinomialLeapfrogKernel_lintegral_positionDistance_le
  intro origin
  simpa only [pow_one, coe_initialPositionDistance] using
    hbound q₁ q₂ p hq₁ hq₂ hp hεpos hεbar' hTmin' hTmax' origin

/-- Assumptions 1 and 2 give one positive integration window on which the
implemented shared-momentum maximal HMC coupling reaches a relaxed diagonal
from the compact core with uniformly positive probability.  Only the single
positive-mass cutoff `K(p) ≤ 1` needed by the downstream meeting argument is
selected. -/
theorem LocalStrongConvexity.exists_maximalSharedMomentum_isRelaxedMeetingAccessible
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) :
    ∃ Tmin > 0, ∃ Tmax > Tmin, ∃ δ > 0,
      ∃ entry : ENNReal, 0 < entry ∧
        ∃ εbar > 0, ∀ {ε : ℝ} {L : ℕ},
          0 < ε → ε ≤ εbar →
          Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
          McmcLean.Kernel.IsRelaxedMeetingAccessibleFrom
            (maximalSharedMomentumCoupledPositionMultinomialHMC
              potential gradient ε L
              hreg.contDiff_two.continuous.measurable
              hreg.contDiff_one_gradient.continuous.measurable)
            K δ 1 entry := by
  let hpotential : Measurable potential :=
    hreg.contDiff_two.continuous.measurable
  let hgradient : Measurable gradient :=
    hreg.contDiff_one_gradient.continuous.measurable
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
      rate, hrate, hbound⟩ :=
    hconv.exists_maximalCoupledRandomizedMultinomialLeapfrogKernel_expectedDistance
      hreg hK hKS hScompact hSconvex (k0 := 1) (by norm_num)
        hpotential hgradient
  obtain ⟨R, hR, hposition⟩ :=
    McmcLean.Hamiltonian.IsCompact.exists_euclideanNorm_bound hK
  let D : ℝ := 2 * R
  let δ : ℝ := 2 * D
  let cutoff : Set (Momentum ι) := {p | kineticEnergy p ≤ 1}
  let mass : ENNReal := standardMomentumMeasure (ι := ι) cutoff
  let entry : ENNReal := mass * (1 / 2)
  have hD : 0 < D := mul_pos (by norm_num) hR
  have hδ : 0 < δ := mul_pos (by norm_num) hD
  have hcutoff : MeasurableSet cutoff := by
    dsimp [cutoff]
    exact measurable_kineticEnergy measurableSet_Iic
  have hmass : 0 < mass := by
    dsimp [mass, cutoff]
    exact standardMomentumMeasure_kineticEnergy_le_pos (by norm_num)
  have hentry : 0 < entry := by
    dsimp [entry]
    exact ENNReal.mul_pos hmass.ne' (by norm_num)
  refine ⟨Tmin, hTmin, Tmax, hTmax, δ, hδ,
    entry, hentry, εbar, hεbar, ?_⟩
  intro ε L hεpos hεbar' hTmin' hTmax'
  unfold McmcLean.Kernel.IsRelaxedMeetingAccessibleFrom
    McmcLean.Kernel.IsUniformlyAccessibleFrom
  intro q hq
  rw [pow_one]
  have hkernelEntry : entry ≤
      maximalSharedMomentumCoupledPositionMultinomialHMC
        potential gradient ε L hpotential hgradient q
        (positionEuclideanRelaxedDiagonal δ) := by
    dsimp [entry, mass]
    unfold maximalSharedMomentumCoupledPositionMultinomialHMC
    apply coupledPositionMultinomialHMC_positionRelaxedDiagonal_ge_of_sharedMomentum
      (coupledTrajectory :=
        maximalCoupledRandomizedMultinomialLeapfrogKernel
          potential gradient ε L hpotential hgradient)
      (momentumTarget := standardMomentumMeasure)
      (q := q) (cutoff := cutoff) hcutoff (δ := δ)
      (c := (1 / 2 : ENNReal))
    intro p hp
    have hpEnergy : kineticEnergy p ≤ 1 := hp
    have hdist : euclideanNorm (q.1 - q.2) ≤ D := by
      apply (euclideanNorm_sub_le q.1 q.2).trans
      dsimp [D]
      linarith [hposition q.1 hq.1, hposition q.2 hq.2]
    have hexpect := hbound hεpos hεbar' hTmin' hTmax'
      q.1 hq.1 q.2 hq.2 p hpEnergy
    have hexpectD :
        (∫⁻ y, ENNReal.ofReal (euclideanNorm (y.1.1 - y.2.1))
          ∂maximalCoupledRandomizedMultinomialLeapfrogKernel
            potential gradient ε L hpotential hgradient
            (((q.1, p), (q.2, p)))) ≤ ENNReal.ofReal D := by
      apply hexpect.trans
      calc
        (rate : ENNReal) * ENNReal.ofReal (euclideanNorm (q.1 - q.2)) ≤
            ENNReal.ofReal (euclideanNorm (q.1 - q.2)) := by
          exact mul_le_of_le_one_left (by positivity)
            (ENNReal.coe_le_coe.mpr hrate.le)
        _ ≤ ENNReal.ofReal D := ENNReal.ofReal_le_ofReal hdist
    have hhalf : (1 / 2 : ENNReal) ≤
        1 - ENNReal.ofReal D / ENNReal.ofReal δ := by
      have hδeq : ENNReal.ofReal δ = 2 * ENNReal.ofReal D := by
        dsimp [δ]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hD0 : ENNReal.ofReal D ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr hD
      have hDtop : ENNReal.ofReal D ≠ ⊤ := ENNReal.ofReal_ne_top
      have hden0 : (2 : ENNReal) * ENNReal.ofReal D ≠ 0 :=
        mul_ne_zero (by norm_num) hD0
      have hdenTop : (2 : ENNReal) * ENNReal.ofReal D ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) hDtop
      have hratio : ENNReal.ofReal D /
          (2 * ENNReal.ofReal D) = (1 / 2 : ENNReal) := by
        symm
        apply (ENNReal.eq_div_iff hden0 hdenTop).2
        simpa only [one_div, mul_comm] using
          (ENNReal.mul_inv_cancel_right
            (a := ENNReal.ofReal D) (b := (2 : ENNReal))
            (by norm_num) (by norm_num))
      rw [hδeq, hratio]
      norm_num
    apply hhalf.trans
    exact measure_phasePositionRelaxedDiagonal_ge_of_lintegral_le
      _ _ hexpectD hδ
  apply hkernelEntry.trans
  apply MeasureTheory.measure_mono
  intro y hy
  have hy' : euclideanNorm (y.1 - y.2) < δ := by
    simpa only [positionEuclideanRelaxedDiagonal, Set.mem_setOf_eq] using hy
  exact (dist_le_euclideanNorm_sub y.1 y.2).trans hy'.le

/-- Pointwise closure of the paper's exponent-one maximal-coupling argument.
Exact reference contraction, relative-displacement leapfrog error, common-ball
containment, and relative Hamiltonian discrepancy combine into one expected
distance contraction bound. -/
theorem maximalTrajectoryIndexCoupling_moment_one_le_of_reference_energy
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (q₁ q₂ : Position ι)
    (y₁ y₂ : Fin (L + 1) → Position ι)
    (exactRate errorRate energyRadius energyRate mismatchBound mismatchRate :
      NNReal)
    {R : ℝ} (hR : 0 ≤ R)
    (href : ∀ i, euclideanNorm (y₁ i - y₂ i) ≤
      (exactRate : ℝ) * euclideanNorm (q₁ - q₂))
    (hdisplacement : ∀ i, euclideanNorm
        (((offsetLeapfrogTrajectory gradient ε origin z.1 i).1 -
            (offsetLeapfrogTrajectory gradient ε origin z.2 i).1) -
          (y₁ i - y₂ i)) ≤
      (errorRate : ℝ) * euclideanNorm (q₁ - q₂))
    (hleft : ∀ i,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.1 i).1 ≤ R)
    (hright : ∀ j,
      euclideanNorm
        (offsetLeapfrogTrajectory gradient ε origin z.2 j).1 ≤ R)
    (htwoR : 2 * R ≤ (mismatchBound : ℝ))
    (henergySmall : (energyRadius : ℝ) ≤ 1 / 2)
    (henergy : ∀ i,
      |energy potential (offsetLeapfrogTrajectory gradient ε origin z.1 i) -
        energy potential (offsetLeapfrogTrajectory gradient ε origin z.2 i)| ≤
          (energyRadius : ℝ))
    (henergyRelative : energyRadius ≤
      energyRate * initialPositionDistance q₁ q₂)
    (hrates : 4 * energyRate * mismatchBound ≤ mismatchRate) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 1 ε z origin)
        (maximalTrajectoryIndexCoupling potential gradient ε z origin) ≤
      ((exactRate + errorRate + mismatchRate : NNReal) : ENNReal) *
        (initialPositionDistance q₁ q₂ : ENNReal) := by
  let d := initialPositionDistance q₁ q₂
  apply maximalTrajectoryIndexCoupling_moment_one_le potential gradient ε z
    origin ((exactRate + errorRate) * d) mismatchBound
  · intro i
    exact trajectoryPositionMomentCost_one_le_of_displacementError
      gradient ε z origin i (y₁ i) (y₂ i) q₁ q₂ exactRate errorRate
        (href i) (hdisplacement i)
  · intro i j hij
    apply (trajectoryPositionMomentCost_one_le_of_positionNorm_le
      gradient ε z origin hR hleft hright i j).trans
    exact_mod_cast htwoR
  · have htv :
        McmcLean.Finite.totalVariation
            (trajectoryIndexPMF potential
              (offsetLeapfrogTrajectory gradient ε origin z.1))
            (trajectoryIndexPMF potential
              (offsetLeapfrogTrajectory gradient ε origin z.2)) *
            (mismatchBound : ENNReal) ≤
          (mismatchRate : ENNReal) * (d : ENNReal) := by
      exact trajectoryIndexPMF_totalVariation_mul_le_of_relative_energy
        potential gradient ε z origin q₁ q₂ energyRadius energyRate
          mismatchBound mismatchRate henergySmall henergy henergyRelative hrates
    calc
      (((exactRate + errorRate) * d : NNReal) : ENNReal) +
          McmcLean.Finite.totalVariation
            (trajectoryIndexPMF potential
              (offsetLeapfrogTrajectory gradient ε origin z.1))
            (trajectoryIndexPMF potential
              (offsetLeapfrogTrajectory gradient ε origin z.2)) *
            (mismatchBound : ENNReal) ≤
        (((exactRate + errorRate) * d : NNReal) : ENNReal) +
          (mismatchRate : ENNReal) * (d : ENNReal) :=
        add_le_add le_rfl htv
      _ = ((exactRate + errorRate + mismatchRate : NNReal) : ENNReal) *
          (d : ENNReal) := by
        push_cast
        ring

/-- The transport trajectory coupling satisfies the same exponent-two
Condition 1 inequality under the same explicit contraction budget. -/
theorem transportTrajectoryIndexCoupling_moment_two_le
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (z : PhaseSpace ι × PhaseSpace ι)
    (origin : Fin (L + 1)) (diagonalBound mismatchBound : NNReal)
    (hdiagonal : ∀ i,
      trajectorySquaredPositionCost gradient ε z origin i i ≤ diagonalBound)
    (hmismatch : ∀ i j, i ≠ j →
      trajectorySquaredPositionCost gradient ε z origin i j ≤ mismatchBound)
    (budget : ENNReal)
    (hbudget : (diagonalBound : ENNReal) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.1))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin z.2)) *
          (mismatchBound : ENNReal) ≤ budget) :
    McmcLean.Finite.transportCost
        (trajectoryPositionMomentCost gradient 2 ε z origin)
        (transportTrajectoryIndexCoupling potential gradient ε z origin) ≤
      budget := by
  rw [transportCost_trajectoryPositionMomentCost_two]
  exact (transportTrajectoryIndexCoupling_cost_le_add_totalVariation_mul
    potential gradient ε z origin diagonalBound mismatchBound
      hdiagonal hmismatch).trans hbudget

/-- Uniform analytic budgets sufficient for the maximal coupling's
exponent-two Condition 1. The predicate separates the three obligations used
in the paper's proof: aligned contraction, off-diagonal boundedness, and a
small total-variation mismatch contribution. -/
def XuMaximalMomentTwoBudget
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal) : Prop :=
  ∀ k0 : ℝ, 0 < k0 →
    ∃ εbar : ℝ, 0 < εbar ∧
      ∃ Lbar : ℕ, 1 ≤ Lbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, ε * (L : ℝ) < εbar * (Lbar : ℝ) →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  ∃ diagonalBound mismatchBound : NNReal,
                    (∀ i, trajectorySquaredPositionCost gradient ε
                      (((q₁, p), (q₂, p))) origin i i ≤ diagonalBound) ∧
                    (∀ i j, i ≠ j →
                      trajectorySquaredPositionCost gradient ε
                        (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
                    (diagonalBound : ENNReal) +
                        McmcLean.Finite.totalVariation
                          (trajectoryIndexPMF potential
                            (offsetLeapfrogTrajectory gradient ε origin
                              (q₁, p)))
                          (trajectoryIndexPMF potential
                            (offsetLeapfrogTrajectory gradient ε origin
                              (q₂, p))) *
                          (mismatchBound : ENNReal) ≤
                      (rate : ENNReal) *
                        ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2)

/-- A sharper sufficient certificate whose two error contributions scale
with the initial squared separation. This relative form handles arbitrarily
close starting positions, including the zero-separation boundary where an
absolute error allowance could not prove Condition 1. -/
def XuRelativeMomentTwoBudget
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (alignedRate mismatchRate : NNReal) : Prop :=
  ∀ k0 : ℝ, 0 < k0 →
    ∃ εbar : ℝ, 0 < εbar ∧
      ∃ Lbar : ℕ, 1 ≤ Lbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, ε * (L : ℝ) < εbar * (Lbar : ℝ) →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  ∃ mismatchBound : NNReal,
                    (∀ i, trajectorySquaredPositionCost gradient ε
                      (((q₁, p), (q₂, p))) origin i i ≤
                        alignedRate * initialSquaredPositionDistance q₁ q₂) ∧
                    (∀ i j, i ≠ j →
                      trajectorySquaredPositionCost gradient ε
                        (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
                    McmcLean.Finite.totalVariation
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                        (mismatchBound : ENNReal) ≤
                      (mismatchRate : ENNReal) *
                        (initialSquaredPositionDistance q₁ q₂ : ENNReal)

/-- Relative aligned and mismatch rates add to the requested total rate,
yielding the uniform maximal-family budget. -/
theorem XuRelativeMomentTwoBudget.xuMaximalMomentTwoBudget
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) {alignedRate mismatchRate rate : NNReal}
    (h : XuRelativeMomentTwoBudget potential gradient S
      alignedRate mismatchRate)
    (hrates : alignedRate + mismatchRate ≤ rate) :
    XuMaximalMomentTwoBudget potential gradient S rate := by
  intro k0 hk0
  rcases h k0 hk0 with ⟨εbar, hεbar, Lbar, hLbar, hbound⟩
  refine ⟨εbar, hεbar, Lbar, hLbar, ?_⟩
  intro ε hε0 hε L hlength origin q₁ hq₁ q₂ hq₂ p hp
  rcases hbound ε hε0 hε L hlength origin q₁ hq₁ q₂ hq₂ p hp with
    ⟨mismatchBound, hdiagonal, hmismatch, htv⟩
  refine ⟨alignedRate * initialSquaredPositionDistance q₁ q₂,
    mismatchBound, hdiagonal, hmismatch, ?_⟩
  calc
    ((alignedRate * initialSquaredPositionDistance q₁ q₂ : NNReal) : ENNReal) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
          (mismatchBound : ENNReal) ≤
        ((alignedRate * initialSquaredPositionDistance q₁ q₂ : NNReal) :
            ENNReal) +
          (mismatchRate : ENNReal) *
            (initialSquaredPositionDistance q₁ q₂ : ENNReal) :=
      add_le_add le_rfl htv
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
      push_cast
      ring
    _ ≤ (rate : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
      exact mul_le_mul_left (ENNReal.coe_le_coe.mpr hrates) _
    _ = (rate : ENNReal) *
          ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2) := by
      rw [coe_initialSquaredPositionDistance]

/-- The aligned/mismatch/TV budget is sufficient for exponent-two Condition 1
of the maximal trajectory-index coupling. -/
theorem XuMaximalMomentTwoBudget.maximal_xuCondition1AtExponent_two
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal)
    (h : XuMaximalMomentTwoBudget potential gradient S rate) :
    XuCondition1AtExponent
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate := by
  refine ⟨by omega, ?_⟩
  intro k0 hk0
  rcases h k0 hk0 with ⟨εbar, hεbar, Lbar, hLbar, hbound⟩
  refine ⟨εbar, hεbar, Lbar, hLbar, ?_⟩
  intro ε hε0 hε L hlength origin q₁ hq₁ q₂ hq₂ p hp
  rcases hbound ε hε0 hε L hlength origin q₁ hq₁ q₂ hq₂ p hp with
    ⟨diagonalBound, mismatchBound, hdiagonal, hmismatch, hbudget⟩
  exact maximalTrajectoryIndexCoupling_moment_two_le
    potential gradient ε (((q₁, p), (q₂, p))) origin
      diagonalBound mismatchBound hdiagonal hmismatch _ hbudget

/-- The same uniform analytic budget proves exponent-two Condition 1 for the
transport trajectory-index coupling by squared-cost optimality. -/
theorem XuMaximalMomentTwoBudget.transport_xuCondition1AtExponent_two
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (rate : NNReal)
    (h : XuMaximalMomentTwoBudget potential gradient S rate) :
    XuCondition1AtExponent
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 rate :=
  transport_xuCondition1AtExponent_two_of_maximal potential gradient S rate
    (h.maximal_xuCondition1AtExponent_two potential gradient S rate)

/-- With a positive subunit rate, one maximal-family analytic budget proves
the paper's full Condition 1 for both proposed categorical couplings. -/
theorem XuMaximalMomentTwoBudget.xuCondition1_maximal_and_transport
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) {rate : NNReal}
    (h : XuMaximalMomentTwoBudget potential gradient S rate)
    (hrate0 : 0 < rate) (hrate1 : rate < 1) :
    XuCondition1 (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient S rate ∧
      XuCondition1 (transportTrajectoryIndexCouplingFamily potential gradient)
        gradient S rate := by
  exact ⟨XuCondition1AtExponent.xuCondition1
      (h.maximal_xuCondition1AtExponent_two potential gradient S rate)
      hrate0 hrate1,
    XuCondition1AtExponent.xuCondition1
      (h.transport_xuCondition1AtExponent_two potential gradient S rate)
      hrate0 hrate1⟩

/-- If the aligned rate is positive and the sum of aligned and mismatch rates
is subunit, the relative certificate gives full Condition 1 for both proposed
couplings at their canonical summed rate. -/
theorem XuRelativeMomentTwoBudget.xuCondition1_maximal_and_transport
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) {alignedRate mismatchRate : NNReal}
    (h : XuRelativeMomentTwoBudget potential gradient S
      alignedRate mismatchRate)
    (haligned : 0 < alignedRate)
    (hrate : alignedRate + mismatchRate < 1) :
    XuCondition1 (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient S (alignedRate + mismatchRate) ∧
      XuCondition1 (transportTrajectoryIndexCouplingFamily potential gradient)
        gradient S (alignedRate + mismatchRate) := by
  apply XuMaximalMomentTwoBudget.xuCondition1_maximal_and_transport
    potential gradient S
    (h.xuMaximalMomentTwoBudget potential gradient S le_rfl)
  · exact haligned.trans_le (le_add_right le_rfl)
  · exact hrate

/-- Non-vacuous relative contraction budget on an integration-time window
bounded away from zero. It separates aligned contraction from the
TV-weighted off-diagonal contribution exactly as the earlier verbatim budget,
but uses the repaired numerical quantifiers. -/
def XuRelativeMomentTwoBudgetOnIntegrationWindow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    (alignedRate mismatchRate : NNReal) : Prop :=
  0 < Tmin ∧ Tmin ≤ Tmax ∧
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  ∃ mismatchBound : NNReal,
                    (∀ i, trajectorySquaredPositionCost gradient ε
                      (((q₁, p), (q₂, p))) origin i i ≤
                        alignedRate * initialSquaredPositionDistance q₁ q₂) ∧
                    (∀ i j, i ≠ j →
                      trajectorySquaredPositionCost gradient ε
                        (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
                    McmcLean.Finite.totalVariation
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                        (mismatchBound : ENNReal) ≤
                      (mismatchRate : ENNReal) *
                        (initialSquaredPositionDistance q₁ q₂ : ENNReal)

/-- The positive-window relative budget for the maximal coupling argument as
it is used at exponent one: aligned distances contract linearly in the
initial separation, and the total-variation mismatch contribution has the
same linear scaling. -/
def XuRelativeMomentOneMaximalBudgetOnIntegrationWindow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    (alignedRate mismatchRate : NNReal) : Prop :=
  0 < Tmin ∧ Tmin ≤ Tmax ∧
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  ∃ mismatchBound : NNReal,
                    (∀ i, trajectoryPositionMomentCost gradient 1 ε
                      (((q₁, p), (q₂, p))) origin i i ≤
                        alignedRate * initialPositionDistance q₁ q₂) ∧
                    (∀ i j, i ≠ j →
                      trajectoryPositionMomentCost gradient 1 ε
                        (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
                    McmcLean.Finite.totalVariation
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                        (mismatchBound : ENNReal) ≤
                      (mismatchRate : ENNReal) *
                        (initialPositionDistance q₁ q₂ : ENNReal)

/-- Faithful exponent-two budget retaining the overlap-weighted aligned
squared cost. Unlike a uniform per-index bound, this permits the unchanged
current-state index while still allowing a subunit expected-cost rate. -/
def XuSharpRelativeMomentTwoBudgetOnIntegrationWindow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    (alignedRate mismatchRate : NNReal) : Prop :=
  0 < Tmin ∧ Tmin ≤ Tmax ∧
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  ∃ mismatchBound : NNReal,
                    (∑ i, min
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                        (trajectorySquaredPositionCost gradient ε
                          (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                      (alignedRate : ENNReal) *
                        (initialSquaredPositionDistance q₁ q₂ : ENNReal) ∧
                    (∀ i j, i ≠ j →
                      trajectorySquaredPositionCost gradient ε
                        (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
                    McmcLean.Finite.totalVariation
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                        (mismatchBound : ENNReal) ≤
                      (mismatchRate : ENNReal) *
                        (initialSquaredPositionDistance q₁ q₂ : ENNReal)

/-- The cutoff-uniform aligned half of repaired exponent-one Condition 1.
Unlike the fixed-cutoff theorem above, the integration window and aligned
rate are outside the kinetic-cutoff quantifier; only the numerical step-size
threshold may shrink as the cutoff grows. -/
def UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ) (alignedRate : NNReal) : Prop :=
  0 < Tmin ∧ Tmin ≤ Tmax ∧ alignedRate < 1 ∧
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  (∑ i, min
                      (trajectoryIndexPMF potential
                        (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                      (trajectoryIndexPMF potential
                        (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                      (trajectoryPositionMomentCost gradient 1 ε
                        (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                    (alignedRate : ENNReal) *
                      (initialPositionDistance q₁ q₂ : ENNReal)

/-- The cutoff-wise positive-window certificate supplied by local strong
convexity.  In contrast to the stronger uniform interface above, the window,
rate, and numerical threshold may all depend on the kinetic cutoff.  This is
the quantifier order directly supported by compact phase-space arguments. -/
def CutoffWiseOverlapWeightedMomentOneContractionOnIntegrationWindow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) : Prop :=
  ∀ k0 : ℝ, 0 ≤ k0 →
    ∃ Tmin > 0, ∃ Tmax ≥ Tmin, ∃ εbar > 0,
      ∃ alignedRate : NNReal, alignedRate < 1 ∧
        ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
          kineticEnergy p ≤ k0 →
            ∀ ε : ℝ, 0 ≤ ε → ε ≤ εbar →
              ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) →
                ε * (L : ℝ) ≤ Tmax →
                  ∀ origin : Fin (L + 1),
                    (∑ i, min
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                        (trajectoryPositionMomentCost gradient 1 ε
                          (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                      (alignedRate : ENNReal) *
                        (initialPositionDistance q₁ q₂ : ENNReal)

/-- Compact local strong convexity proves the cutoff-wise aligned
first-moment certificate.  This packages the existing fixed-cutoff theorem
with the precise quantifier order it supports. -/
theorem LocalStrongConvexity.cutoffWiseOverlapWeightedMomentOneContractionOnIntegrationWindow
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {S : Set (Position ι)} {α : ℝ}
    (hconv : LocalStrongConvexity gradient S α)
    {K : Set (Position ι)} (hK : IsCompact K)
    (hKS : K ⊆ interior S) (hScompact : IsCompact S)
    (hSconvex : Convex ℝ S) :
    CutoffWiseOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K := by
  intro k0 hk0
  obtain ⟨Tmin, hTmin, Tmax, hTmax, εbar, hεbar,
      alignedRate, haligned, hbound⟩ :=
    hconv.exists_uniform_overlapWeightedMomentOneContraction_of_kineticEnergy_le
      hreg hK hKS hScompact hSconvex hk0
  refine ⟨Tmin, hTmin, Tmax, hTmax.le, εbar, hεbar,
    alignedRate, haligned, ?_⟩
  intro q₁ hq₁ q₂ hq₂ p hp ε hε0 hεbar' L hTmin' hTmax' origin
  exact hbound q₁ q₂ p hq₁ hq₂ hp hε0 hεbar' hTmin' hTmax' origin

/-- The cutoff-uniform certificate is strictly stronger than the cutoff-wise
one.  Shrinking its strict step-size threshold by one half reconciles the two
endpoint conventions. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.toCutoffWise
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {S : Set (Position ι)} {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (h : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate) :
    CutoffWiseOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient S := by
  intro k0 hk0
  obtain ⟨εstrict, hεstrict, hbound⟩ := h.2.2.2 (k0 + 1) (by linarith)
  let εbar := εstrict / 2
  have hεbar : 0 < εbar := half_pos hεstrict
  refine ⟨Tmin, h.1, Tmax, h.2.1, εbar, hεbar,
    alignedRate, h.2.2.1, ?_⟩
  intro q₁ hq₁ q₂ hq₂ p hp ε hε0 hεbar' L hTmin hTmax origin
  have hεpos : 0 < ε := by
    by_contra hnot
    have hεzero : ε = 0 := le_antisymm (le_of_not_gt hnot) hε0
    subst ε
    norm_num at hTmin
    exact (not_lt_of_ge hTmin) h.1
  have hεlt : ε < εstrict := by
    calc
      ε ≤ εbar := hεbar'
      _ < εstrict := by dsimp [εbar]; linarith
  apply hbound ε hεpos hεlt L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p
  exact hp.trans (by linarith)

/-- Faithful first-moment maximal-coupling budget retaining the
overlap-weighted aligned cost.  This is strictly sharper than requiring every
aligned index to contract, which is impossible below rate one at the
current-state index. -/
def XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    (alignedRate mismatchRate : NNReal) : Prop :=
  0 < Tmin ∧ Tmin ≤ Tmax ∧
    ∀ k0 : ℝ, 0 < k0 →
      ∃ εbar : ℝ, 0 < εbar ∧
        ∀ ε : ℝ, 0 < ε → ε < εbar →
          ∀ L : ℕ, Tmin ≤ ε * (L : ℝ) → ε * (L : ℝ) ≤ Tmax →
            ∀ origin : Fin (L + 1),
              ∀ q₁ ∈ S, ∀ q₂ ∈ S, ∀ p : Momentum ι,
                kineticEnergy p ≤ k0 →
                  ∃ mismatchBound : NNReal,
                    (∑ i, min
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
                        (trajectoryPositionMomentCost gradient 1 ε
                          (((q₁, p), (q₂, p))) origin i i : ENNReal)) ≤
                      (alignedRate : ENNReal) *
                        (initialPositionDistance q₁ q₂ : ENNReal) ∧
                    (∀ i j, i ≠ j →
                      trajectoryPositionMomentCost gradient 1 ε
                        (((q₁, p), (q₂, p))) origin i j ≤ mismatchBound) ∧
                    McmcLean.Finite.totalVariation
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
                        (trajectoryIndexPMF potential
                          (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
                        (mismatchBound : ENNReal) ≤
                      (mismatchRate : ENNReal) *
                        (initialPositionDistance q₁ q₂ : ENNReal)

/-- The sharp overlap-weighted squared budget proves exponent-two
positive-window contractivity for maximal coupling. -/
theorem XuSharpRelativeMomentTwoBudgetOnIntegrationWindow.maximalCondition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuSharpRelativeMomentTwoBudgetOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate mismatchRate) :
    XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 (alignedRate + mismatchRate) Tmin Tmax := by
  refine ⟨by omega, h.1, h.2.1, ?_⟩
  intro k0 hk0
  rcases h.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p hp
  rcases hbound ε hε0 hε L hTmin hTmax origin
      q₁ hq₁ q₂ hq₂ p hp with
    ⟨mismatchBound, haligned, hmismatch, htv⟩
  rw [transportCost_trajectoryPositionMomentCost_two]
  apply (maximalTrajectoryIndexCoupling_cost_le_weightedDiagonal_add_tv
    potential gradient ε (((q₁, p), (q₂, p))) origin mismatchBound
      hmismatch).trans
  calc
    (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
          (trajectorySquaredPositionCost gradient ε
            (((q₁, p), (q₂, p))) origin i i : ENNReal)) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
          (mismatchBound : ENNReal) ≤
      (alignedRate : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) +
        (mismatchRate : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) :=
      add_le_add haligned htv
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
        ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2) := by
      rw [← coe_initialSquaredPositionDistance]
      push_cast
      ring

/-- Squared-cost optimality transfers the sharp exponent-two condition to
the measurable optimal-transport trajectory coupling. -/
theorem XuSharpRelativeMomentTwoBudgetOnIntegrationWindow.transportCondition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuSharpRelativeMomentTwoBudgetOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate mismatchRate) :
    XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 (alignedRate + mismatchRate) Tmin Tmax :=
  transport_xuCondition1AtExponentOnIntegrationWindow_two_of_maximal
    potential gradient S (alignedRate + mismatchRate) Tmin Tmax
      (h.maximalCondition potential gradient S Tmin Tmax)

/-- A positive aligned rate and subunit total sharp squared budget give full
positive-window Condition 1 for both categorical coupling constructions. -/
theorem XuSharpRelativeMomentTwoBudgetOnIntegrationWindow.conditions
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuSharpRelativeMomentTwoBudgetOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate mismatchRate)
    (haligned : 0 < alignedRate)
    (hrate : alignedRate + mismatchRate < 1) :
    XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient S (alignedRate + mismatchRate) ∧
      XuCondition1OnIntegrationWindow
        (transportTrajectoryIndexCouplingFamily potential gradient)
        gradient S (alignedRate + mismatchRate) := by
  have hpositive : 0 < alignedRate + mismatchRate :=
    haligned.trans_le (le_add_right le_rfl)
  exact ⟨(h.maximalCondition potential gradient S Tmin Tmax)
      |>.xuCondition1OnIntegrationWindow hpositive hrate,
    (h.transportCondition potential gradient S Tmin Tmax)
      |>.xuCondition1OnIntegrationWindow hpositive hrate⟩

/-- The sharp overlap-weighted budget proves exponent-one positive-window
contractivity for maximal coupling. -/
theorem XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow.maximalCondition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate mismatchRate) :
    XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 1 (alignedRate + mismatchRate) Tmin Tmax := by
  refine ⟨by omega, h.1, h.2.1, ?_⟩
  intro k0 hk0
  rcases h.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p hp
  rcases hbound ε hε0 hε L hTmin hTmax origin
      q₁ hq₁ q₂ hq₂ p hp with
    ⟨mismatchBound, haligned, hmismatch, htv⟩
  apply (maximalTrajectoryIndexCoupling_moment_one_le_overlap
    potential gradient ε (((q₁, p), (q₂, p))) origin mismatchBound
      hmismatch).trans
  calc
    (∑ i, min
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)) i)
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p)) i) *
          (trajectoryPositionMomentCost gradient 1 ε
            (((q₁, p), (q₂, p))) origin i i : ENNReal)) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
          (mismatchBound : ENNReal) ≤
      (alignedRate : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) +
        (mismatchRate : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) :=
      add_le_add haligned htv
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
        ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 1) := by
      rw [pow_one, ← coe_initialPositionDistance]
      push_cast
      ring

/-- A positive aligned rate and subunit summed sharp budget give the repaired
full maximal-coupling Condition 1 interface. -/
theorem XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow.condition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate mismatchRate)
    (haligned : 0 < alignedRate)
    (hrate : alignedRate + mismatchRate < 1) :
    XuCondition1OnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S (alignedRate + mismatchRate) :=
  (h.maximalCondition potential gradient S Tmin Tmax).xuCondition1OnIntegrationWindow
    (haligned.trans_le (le_add_right le_rfl)) hrate

/-- A cutoff-uniform aligned certificate and the relative centered-energy
estimate close repaired exponent-one Condition 1.  This theorem isolates the
only two analytic inputs from the already verified maximal-coupling algebra. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate)
    (hrelative : ∀ k0 : ℝ, 0 < k0 →
      UniformRelativeCenteredLeapfrogEnergyErrorOnCompactWindow
        potential gradient K k0 Tmax) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) := by
  let mismatchRate : NNReal := (1 - alignedRate) / 2
  have hmismatchPos : 0 < mismatchRate := by
    dsimp [mismatchRate]
    exact div_pos (tsub_pos_iff_lt.mpr haligned.2.2.1) (by norm_num)
  have hmismatchOne : mismatchRate ≤ 1 := by
    dsimp [mismatchRate]
    exact (div_le_self (by positivity : (0 : NNReal) ≤ 1 - alignedRate)
      (by norm_num : (1 : NNReal) ≤ 2)).trans tsub_le_self
  have hrates : alignedRate + mismatchRate < 1 := by
    have hcancel : alignedRate + (1 - alignedRate) = 1 :=
      add_tsub_cancel_of_le haligned.2.2.1.le
    dsimp [mismatchRate]
    calc
      alignedRate + (1 - alignedRate) / 2 <
          alignedRate + (1 - alignedRate) := by
        simpa only [add_comm] using add_lt_add_left
          (div_lt_self (tsub_pos_iff_lt.mpr haligned.2.2.1)
            (by norm_num : (1 : NNReal) < 2)) alignedRate
      _ = 1 := hcancel
  have hTmax0 : 0 ≤ Tmax := haligned.1.le.trans haligned.2.1
  have hbudget : XuSharpRelativeMomentOneMaximalBudgetOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate mismatchRate := by
    refine ⟨haligned.1, haligned.2.1, ?_⟩
    intro k0 hk0
    obtain ⟨εaligned, hεaligned, halignedBound⟩ :=
      haligned.2.2.2 k0 hk0
    obtain ⟨εmismatch, hεmismatch, mismatchBound, hmismatchBound⟩ :=
      (hrelative k0 hk0).exists_uniform_relativeMomentOneMismatchBudget
        hreg hK hk0.le hTmax0 mismatchRate hmismatchPos hmismatchOne
    let εbar := min εaligned (εmismatch / 2)
    have hεbar : 0 < εbar :=
      lt_min hεaligned (half_pos hεmismatch)
    refine ⟨εbar, hεbar, ?_⟩
    intro ε hεpos hε L hTmin' hTmax' origin q₁ hq₁ q₂ hq₂ p hp
    have hεaligned' : ε < εaligned :=
      hε.trans_le (min_le_left _ _)
    have hεmismatch' : ε < εmismatch :=
      (hε.trans_le (min_le_right _ _)).trans (half_lt_self hεmismatch)
    have ha := halignedBound ε hεpos hεaligned' L hTmin' hTmax'
      origin q₁ hq₁ q₂ hq₂ p hp
    obtain ⟨hcross, htv⟩ := hmismatchBound hεpos hεmismatch' hTmax'
      origin q₁ hq₁ q₂ hq₂ p hp
    exact ⟨mismatchBound, ha, (fun i j _ => hcross i j), htv⟩
  refine ⟨mismatchRate, hmismatchPos, hrates, ?_⟩
  exact (hbudget.maximalCondition potential gradient K Tmin Tmax)
    |>.xuCondition1OnIntegrationWindow
      (hmismatchPos.trans_le (le_add_left le_rfl)) hrates

/-- A shared-momentum vanishing signed-leapfrog modulus is sufficient for
repaired maximal-coupling Condition 1. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_sharedMomentumVanishingSignedEnergyError
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate)
    (hpaired :
      LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyErrorOfSharedMomentum
        potential gradient) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) := by
  apply haligned.exists_maximalCondition hreg hK
  intro k0 hk0
  exact hpaired.onCompactWindow hK hk0.le
    (haligned.1.le.trans haligned.2.1)

/-- The local one-step paired energy estimate is therefore sufficient,
together with the aligned certificate, for repaired maximal Condition 1. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_oneStepEnergyError
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate)
    (hone : LocallyUniformVanishingPerTimePairedOneStepEnergyError
      potential gradient) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) :=
  haligned.exists_maximalCondition_of_sharedMomentumVanishingSignedEnergyError
    hreg hK (hone.toSharedMomentumSigned hreg)

/-- The derivative-level one-step criterion is sufficient for repaired
maximal-coupling Condition 1.  This isolates the remaining numerical-analysis
obligation as uniform `o(|ε|)` control of the phase derivative of one
leapfrog energy defect. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_oneStepEnergyDefectFDeriv
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate)
    (hderiv : LocallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv
      potential gradient) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) :=
  haligned.exists_maximalCondition_of_oneStepEnergyError
    hreg hK (hderiv.toPaired hreg)

/-- For a regular potential, the aligned overlap-weighted contraction
certificate is now the only analytic premise needed here: the relative
leapfrog energy-error part follows from `C²` regularity. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_regularPotential
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) :=
  haligned.exists_maximalCondition_of_oneStepEnergyDefectFDeriv
    hreg hK hreg.locallyUniformVanishingPerTimeOneStepEnergyDefectFDeriv

/-- The explicit step-size Hamiltonian-variation criterion is sufficient for
repaired maximal-coupling Condition 1. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_stepSizeEnergyVariation
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate)
    (hvariation : LocallyUniformVanishingPairedStepSizeEnergyVariation
      gradient) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) :=
  haligned.exists_maximalCondition_of_oneStepEnergyError
    hreg hK (hvariation.toPaired hreg)

/-- A vanishing signed-leapfrog relative modulus is sufficient for repaired
maximal-coupling Condition 1. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_vanishingSignedEnergyError
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate)
    (hpaired : LocallyUniformVanishingRelativeCenteredSignedLeapfrogEnergyError
      potential gradient) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) := by
  exact haligned.exists_maximalCondition_of_sharedMomentumVanishingSignedEnergyError
    hreg hK hpaired.toSharedMomentum

/-- Quantitative signed-leapfrog relative consistency is a direct sufficient
numerical hypothesis for the repaired maximal-coupling Condition 1 theorem. -/
theorem UniformOverlapWeightedMomentOneContractionOnIntegrationWindow.exists_maximalCondition_of_signedEnergyError
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    {β : NNReal} (hreg : RegularPotential potential gradient β)
    {K : Set (Position ι)} (hK : IsCompact K)
    {Tmin Tmax : ℝ} {alignedRate : NNReal}
    (haligned : UniformOverlapWeightedMomentOneContractionOnIntegrationWindow
      potential gradient K Tmin Tmax alignedRate)
    (hpaired : LocallyUniformLinearRelativeCenteredSignedLeapfrogEnergyError
      potential gradient) :
    ∃ mismatchRate : NNReal, 0 < mismatchRate ∧
      alignedRate + mismatchRate < 1 ∧
      XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient K (alignedRate + mismatchRate) := by
  exact haligned.exists_maximalCondition_of_vanishingSignedEnergyError
    hreg hK hpaired.toVanishing

/-- The exponent-one relative budget proves positive-window contractivity for
the maximal trajectory-index coupling at the sum of its two rates. -/
theorem XuRelativeMomentOneMaximalBudgetOnIntegrationWindow.maximalCondition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuRelativeMomentOneMaximalBudgetOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate mismatchRate) :
    XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 1 (alignedRate + mismatchRate) Tmin Tmax := by
  refine ⟨by omega, h.1, h.2.1, ?_⟩
  intro k0 hk0
  rcases h.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p hp
  rcases hbound ε hε0 hε L hTmin hTmax origin
      q₁ hq₁ q₂ hq₂ p hp with
    ⟨mismatchBound, hdiagonal, hmismatch, htv⟩
  apply maximalTrajectoryIndexCoupling_moment_one_le potential gradient ε
    (((q₁, p), (q₂, p))) origin
    (alignedRate * initialPositionDistance q₁ q₂) mismatchBound
    hdiagonal hmismatch _
  calc
    ((alignedRate * initialPositionDistance q₁ q₂ : NNReal) : ENNReal) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
          (mismatchBound : ENNReal) ≤
      ((alignedRate * initialPositionDistance q₁ q₂ : NNReal) : ENNReal) +
        (mismatchRate : ENNReal) *
          (initialPositionDistance q₁ q₂ : ENNReal) :=
      add_le_add le_rfl htv
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
        (initialPositionDistance q₁ q₂ : ENNReal) := by
      push_cast
      ring
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
        ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 1) := by
      rw [pow_one, coe_initialPositionDistance]

/-- A positive aligned rate and subunit total rate turn the exponent-one
maximal-coupling certificate into the repaired full Condition 1 interface. -/
theorem XuRelativeMomentOneMaximalBudgetOnIntegrationWindow.condition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuRelativeMomentOneMaximalBudgetOnIntegrationWindow
      potential gradient S Tmin Tmax alignedRate mismatchRate)
    (haligned : 0 < alignedRate)
    (hrate : alignedRate + mismatchRate < 1) :
    XuCondition1OnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S (alignedRate + mismatchRate) := by
  apply XuCondition1AtExponentOnIntegrationWindow.xuCondition1OnIntegrationWindow
    (h.maximalCondition potential gradient S Tmin Tmax)
  · exact haligned.trans_le (le_add_right le_rfl)
  · exact hrate

/-- The repaired relative budget proves exponent-two positive-window
contractivity for maximal coupling at the sum of its two rates. -/
theorem XuRelativeMomentTwoBudgetOnIntegrationWindow.maximalCondition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuRelativeMomentTwoBudgetOnIntegrationWindow potential gradient S
      Tmin Tmax alignedRate mismatchRate) :
    XuCondition1AtExponentOnIntegrationWindow
      (maximalTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 (alignedRate + mismatchRate) Tmin Tmax := by
  refine ⟨by omega, h.1, h.2.1, ?_⟩
  intro k0 hk0
  rcases h.2.2 k0 hk0 with ⟨εbar, hεbar, hbound⟩
  refine ⟨εbar, hεbar, ?_⟩
  intro ε hε0 hε L hTmin hTmax origin q₁ hq₁ q₂ hq₂ p hp
  rcases hbound ε hε0 hε L hTmin hTmax origin
      q₁ hq₁ q₂ hq₂ p hp with
    ⟨mismatchBound, hdiagonal, hmismatch, htv⟩
  apply maximalTrajectoryIndexCoupling_moment_two_le potential gradient ε
    (((q₁, p), (q₂, p))) origin
    (alignedRate * initialSquaredPositionDistance q₁ q₂) mismatchBound
    hdiagonal hmismatch _
  calc
    ((alignedRate * initialSquaredPositionDistance q₁ q₂ : NNReal) : ENNReal) +
        McmcLean.Finite.totalVariation
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₁, p)))
          (trajectoryIndexPMF potential
            (offsetLeapfrogTrajectory gradient ε origin (q₂, p))) *
          (mismatchBound : ENNReal) ≤
      ((alignedRate * initialSquaredPositionDistance q₁ q₂ : NNReal) : ENNReal) +
        (mismatchRate : ENNReal) *
          (initialSquaredPositionDistance q₁ q₂ : ENNReal) :=
      add_le_add le_rfl htv
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
        (initialSquaredPositionDistance q₁ q₂ : ENNReal) := by
      push_cast
      ring
    _ = ((alignedRate + mismatchRate : NNReal) : ENNReal) *
        ENNReal.ofReal (euclideanNorm (q₁ - q₂) ^ 2) := by
      rw [coe_initialSquaredPositionDistance]

/-- The same repaired budget proves exponent-two positive-window
contractivity for the optimal-transport coupling. -/
theorem XuRelativeMomentTwoBudgetOnIntegrationWindow.transportCondition
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuRelativeMomentTwoBudgetOnIntegrationWindow potential gradient S
      Tmin Tmax alignedRate mismatchRate) :
    XuCondition1AtExponentOnIntegrationWindow
      (transportTrajectoryIndexCouplingFamily potential gradient)
      gradient S 2 (alignedRate + mismatchRate) Tmin Tmax :=
  transport_xuCondition1AtExponentOnIntegrationWindow_two_of_maximal
    potential gradient S (alignedRate + mismatchRate) Tmin Tmax
      (h.maximalCondition potential gradient S Tmin Tmax)

/-- A positive aligned rate and subunit total repaired budget give full
positive-window Condition 1 for both categorical coupling constructions. -/
theorem XuRelativeMomentTwoBudgetOnIntegrationWindow.conditions
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (S : Set (Position ι)) (Tmin Tmax : ℝ)
    {alignedRate mismatchRate : NNReal}
    (h : XuRelativeMomentTwoBudgetOnIntegrationWindow potential gradient S
      Tmin Tmax alignedRate mismatchRate)
    (haligned : 0 < alignedRate)
    (hrate : alignedRate + mismatchRate < 1) :
    XuCondition1OnIntegrationWindow
        (maximalTrajectoryIndexCouplingFamily potential gradient)
        gradient S (alignedRate + mismatchRate) ∧
      XuCondition1OnIntegrationWindow
        (transportTrajectoryIndexCouplingFamily potential gradient)
        gradient S (alignedRate + mismatchRate) := by
  have hpositive : 0 < alignedRate + mismatchRate :=
    haligned.trans_le (le_add_right le_rfl)
  exact ⟨XuCondition1AtExponentOnIntegrationWindow.xuCondition1OnIntegrationWindow
        (h.maximalCondition potential gradient S Tmin Tmax) hpositive hrate,
    XuCondition1AtExponentOnIntegrationWindow.xuCondition1OnIntegrationWindow
        (h.transportCondition potential gradient S Tmin Tmax) hpositive hrate⟩

end McmcLean.Hamiltonian
