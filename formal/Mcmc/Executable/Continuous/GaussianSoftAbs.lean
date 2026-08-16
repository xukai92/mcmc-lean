import Mcmc.Executable.Continuous.SeparableGeneralizedLeapfrog
import Mcmc.Relativistic.SoftAbsKernel

/-!
# Executable Gaussian diagonal-SoftAbs GR-HMC client

The standard Gaussian potential has constant Hessian diagonal `1`. Applying
SoftAbs therefore gives a genuine, non-identity diagonal SoftAbs metric that
is constant in position. The generalized implicit equations collapse to the
explicit separable metric leapfrog, whose measurability, uniqueness,
reversibility, and exact phase-volume preservation are already certified.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian Mcmc.Relativistic MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Standard centered Gaussian potential, up to its normalization constant. -/
noncomputable def gaussianSoftAbsPotential (q : Position ι) : ℝ :=
  (1 / 2 : ℝ) * squaredEuclideanNorm q

/-- Its exact Hessian diagonal. -/
def gaussianHessianDiagonal (_q : Position ι) (_i : ι) : ℝ := 1

omit [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianSoftAbsPotential :
    Measurable (gaussianSoftAbsPotential : Position ι → ℝ) := by
  exact (continuous_const.mul continuous_squaredEuclideanNorm).measurable

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianHessianDiagonal (i : ι) :
    Measurable fun q : Position ι => gaussianHessianDiagonal q i :=
  measurable_const

/-- The concrete Gaussian SoftAbs metric (`α=1`). -/
noncomputable abbrev gaussianSoftAbsMetric : FactoredRiemannianMetric ι :=
  diagonalSoftAbsMetric 1 (by norm_num) gaussianHessianDiagonal

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsEigenvalue_gt_one (q : Position ι) (i : ι) :
    1 < diagonalSoftAbsEigenvalue 1 gaussianHessianDiagonal q i := by
  change 1 < softAbs 1 1
  simp only [softAbs, one_ne_zero, if_false, one_mul, one_div]
  rw [one_lt_inv₀ (real_tanh_pos (by norm_num))]
  exact Real.tanh_lt_one 1

/-- Relativistic velocity for the constant Gaussian SoftAbs metric. -/
noncomputable def gaussianSoftAbsVelocity (p : Momentum ι) : Position ι :=
  riemannianRelativisticVelocity gaussianSoftAbsMetric 1 1 0 p

omit [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsVelocity_eq (q : Position ι) (p : Momentum ι) :
    riemannianRelativisticVelocity gaussianSoftAbsMetric 1 1 q p =
      gaussianSoftAbsVelocity p := by
  rfl

omit [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianSoftAbsVelocity :
    Measurable (gaussianSoftAbsVelocity : Momentum ι → Position ι) := by
  unfold gaussianSoftAbsVelocity riemannianRelativisticVelocity
    generalRelativisticVelocity generalRelativisticMass relativisticMass
    gaussianSoftAbsMetric gaussianHessianDiagonal diagonalSoftAbsMetric
    diagonalSoftAbsFactor diagonalSoftAbsInverseMetric diagonalMomentumMap
    squaredEuclideanNorm euclideanInner
  fun_prop

omit [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsVelocity_odd (p : Momentum ι) :
    gaussianSoftAbsVelocity (-p) = -gaussianSoftAbsVelocity p := by
  unfold gaussianSoftAbsVelocity riemannianRelativisticVelocity
    generalRelativisticVelocity generalRelativisticMass
  have hfactor :
      (gaussianSoftAbsMetric.factor (0 : Position ι)).toLinearMap (-p) =
        -(gaussianSoftAbsMetric.factor (0 : Position ι)).toLinearMap p := by
    exact map_neg _ p
  have hinverse : gaussianSoftAbsMetric.inverseMetric (0 : Position ι) (-p) =
      -gaussianSoftAbsMetric.inverseMetric (0 : Position ι) p := by
    exact map_neg _ p
  rw [hfactor, relativisticMass_neg, hinverse]
  module

/-- Constant-metric package consumed by the explicit leapfrog theorem. -/
noncomputable def gaussianSoftAbsConstantMetric : ConstantMetric ι where
  velocity := gaussianSoftAbsVelocity
  measurable_velocity := measurable_gaussianSoftAbsVelocity
  velocity_odd := gaussianSoftAbsVelocity_odd

/-- The actual Gaussian force callback. -/
def gaussianSoftAbsGradient (q : Position ι) : Momentum ι := q

omit [Fintype ι] [Nonempty ι] in
/-- The supplied diagonal is the actual coordinate Hessian of the Gaussian
potential, not an unrelated metric callback. -/
theorem gaussianHessianDiagonal_eq_fderiv_gradient
    (q : Position ι) (i : ι) :
    gaussianHessianDiagonal q i =
      fderiv ℝ (fun r : Position ι => gaussianSoftAbsGradient r i) q
        (Pi.single i 1) := by
  unfold gaussianHessianDiagonal gaussianSoftAbsGradient
  rw [(hasFDerivAt_apply i q).fderiv]
  simp

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] in
theorem measurable_gaussianSoftAbsGradient :
    Measurable (gaussianSoftAbsGradient : Position ι → Momentum ι) :=
  measurable_id

/-- Fully certified generalized-leapfrog selection for the Gaussian
diagonal-SoftAbs Hamiltonian. -/
noncomputable def gaussianSoftAbsSelection :
    GeneralizedLeapfrogSelection
      (separablePositionDerivative
        (gaussianSoftAbsGradient : Position ι → Momentum ι))
      (separableMomentumDerivative
        (gaussianSoftAbsVelocity : Momentum ι → Position ι)) :=
  separableGeneralizedLeapfrogSelection
    (gaussianSoftAbsVelocity : Momentum ι → Position ι)
    (gaussianSoftAbsGradient : Position ι → Momentum ι)

omit [Nonempty ι] [DecidableEq ι] in
theorem gaussianSoftAbsSelection_valid :
    (gaussianSoftAbsSelection (ι := ι)).IsValid := by
  exact separableGeneralizedLeapfrogSelection_valid
    (gaussianSoftAbsConstantMetric (ι := ι))
    (gaussianSoftAbsGradient (ι := ι))
    (measurable_gaussianSoftAbsGradient (ι := ι))

omit [Nonempty ι] [DecidableEq ι] in
/-- Exact one-step algebra for the concrete Gaussian SoftAbs solver.  The
relativistic velocity is evaluated at the force-kicked half momentum; this is
the nonquadratic term that a bare-kernel drift proof must control. -/
theorem gaussianSoftAbsSelection_step_eq (ε : ℝ) (z : PhaseSpace ι) :
    (gaussianSoftAbsSelection (ι := ι)).step ε z =
      let pHalf := z.2 - (ε / 2) • z.1
      let qNext := z.1 + ε • gaussianSoftAbsVelocity pHalf
      (qNext, pHalf - (ε / 2) • qNext) := by
  rfl

omit [Nonempty ι] [DecidableEq ι] in
/-- Position component of one concrete Gaussian SoftAbs generalized-leapfrog
step. -/
theorem gaussianSoftAbsSelection_step_fst (ε : ℝ) (z : PhaseSpace ι) :
    ((gaussianSoftAbsSelection (ι := ι)).step ε z).1 =
      z.1 + ε • gaussianSoftAbsVelocity (z.2 - (ε / 2) • z.1) := by
  rw [gaussianSoftAbsSelection_step_eq]

/-- End-to-end exact position invariance for endpoint-Metropolis GR-HMC on
the Gaussian target with its actual diagonal SoftAbs Hessian metric. -/
theorem gaussianSoftAbs_endpointGRHMC_invariant (ε : ℝ) :
    (positionEndpointMetropolisGRHMC (gaussianSoftAbsPotential (ι := ι))
      (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num)
      (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        1 (by norm_num) (gaussianHessianDiagonal (ι := ι)) 1 1
        (by norm_num) (by norm_num)
        (measurable_gaussianHessianDiagonal (ι := ι)))
      ε).Invariant
      (generalRelativisticPositionTarget (gaussianSoftAbsPotential (ι := ι))
        1 1 (by norm_num) (by norm_num)) := by
  exact diagonalSoftAbs_positionEndpointMetropolisGRHMC_invariant
    (measurable_gaussianSoftAbsPotential (ι := ι)) 1 (by norm_num)
    (gaussianHessianDiagonal (ι := ι))
    (measurable_gaussianHessianDiagonal (ι := ι))
    1 1 (by norm_num) (by norm_num)
    (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid ε

/-- End-to-end exact position invariance for multinomial GR-HMC on the same
Gaussian diagonal-SoftAbs client. -/
theorem gaussianSoftAbs_multinomialGRHMC_invariant (ε : ℝ) (L : ℕ) :
    (positionMultinomialGRHMC (gaussianSoftAbsPotential (ι := ι))
      (gaussianSoftAbsMetric (ι := ι)) 1 1 (by norm_num) (by norm_num)
      (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid
      (measurable_diagonalSoftAbs_generalRelativisticHamiltonian
        (gaussianSoftAbsPotential (ι := ι))
        (measurable_gaussianSoftAbsPotential (ι := ι))
        1 (by norm_num) (gaussianHessianDiagonal (ι := ι))
        (measurable_gaussianHessianDiagonal (ι := ι)) 1 1)
      (diagonalSoftAbs_isMeasurableRiemannianMomentumFamily
        1 (by norm_num) (gaussianHessianDiagonal (ι := ι)) 1 1
        (by norm_num) (by norm_num)
        (measurable_gaussianHessianDiagonal (ι := ι)))
      ε L).Invariant
      (generalRelativisticPositionTarget (gaussianSoftAbsPotential (ι := ι))
        1 1 (by norm_num) (by norm_num)) := by
  exact diagonalSoftAbs_positionMultinomialGRHMC_invariant
    (measurable_gaussianSoftAbsPotential (ι := ι)) 1 (by norm_num)
    (gaussianHessianDiagonal (ι := ι))
    (measurable_gaussianHessianDiagonal (ι := ι))
    1 1 (by norm_num) (by norm_num)
    (gaussianSoftAbsSelection (ι := ι)) gaussianSoftAbsSelection_valid ε L

end Mcmc.Executable.Continuous
