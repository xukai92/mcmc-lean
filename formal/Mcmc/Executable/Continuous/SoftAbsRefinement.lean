import Mcmc.Executable.Continuous.RestrictedRefinement
import Mcmc.Relativistic.SoftAbs

/-!
# Guarded numerical refinement for diagonal SoftAbs metrics

The target expression language stays total. SoftAbs metric evaluation uses
positive-domain operations (`sqrt`, reciprocal, and `log`), so this module
keeps their local backend guarantees and positivity guards explicit and
composes them into the three quantities consumed by GR-HMC.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Relativistic

/-- Operation-local numerical contract for one scalar SoftAbs metric entry.
Each transport theorem includes both local backend error and argument error;
the backend or a platform-specific refinement layer supplies those facts. -/
structure SoftAbsPrimitiveBackend where
  softAbs : ℝ → ℝ → ℝ
  sqrt : ℝ → ℝ
  inv : ℝ → ℝ
  log : ℝ → ℝ
  softAbsError : ℝ → ℝ → ℝ → ℝ → ℝ
  sqrtError : ℝ → ℝ → ℝ → ℝ
  invError : ℝ → ℝ → ℝ → ℝ
  logError : ℝ → ℝ → ℝ → ℝ
  softAbs_bound : ∀ α computed ideal error,
    0 < α → Approximates computed ideal error →
      Approximates (softAbs α computed) (Mcmc.Relativistic.softAbs α ideal)
        (softAbsError α computed ideal error)
  sqrt_bound : ∀ computed ideal error,
    0 < computed → 0 < ideal → Approximates computed ideal error →
      Approximates (sqrt computed) (Real.sqrt ideal)
        (sqrtError computed ideal error)
  inv_bound : ∀ computed ideal error,
    computed ≠ 0 → ideal ≠ 0 → Approximates computed ideal error →
      Approximates (inv computed) ideal⁻¹ (invError computed ideal error)
  log_bound : ∀ computed ideal error,
    0 < computed → 0 < ideal → Approximates computed ideal error →
      Approximates (log computed) (Real.log ideal)
        (logError computed ideal error)

/-- End-to-end numerical witness for one diagonal SoftAbs eigenvalue, its
inverse-square-root factor, and its log-determinant contribution. -/
structure SoftAbsMetricEntryCertificate (α idealHessian : ℝ) where
  computedHessian : ℝ
  computedEigenvalue : ℝ
  computedSqrt : ℝ
  computedFactor : ℝ
  computedLogDet : ℝ
  hessianError : ℝ
  eigenvalueError : ℝ
  sqrtError : ℝ
  factorError : ℝ
  logDetError : ℝ
  hessian_bound : Approximates computedHessian idealHessian hessianError
  eigenvalue_bound : Approximates computedEigenvalue
    (Mcmc.Relativistic.softAbs α idealHessian) eigenvalueError
  factor_bound : Approximates computedFactor
    (Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ factorError
  logDet_bound : Approximates computedLogDet
    (Real.log (Mcmc.Relativistic.softAbs α idealHessian)) logDetError

/-- Compose guarded operation certificates into the metric-entry witness. -/
noncomputable def SoftAbsPrimitiveBackend.metricEntryCertificate
    (backend : SoftAbsPrimitiveBackend) {α computedHessian idealHessian hessianError : ℝ}
    (hα : 0 < α)
    (hhessian : Approximates computedHessian idealHessian hessianError)
    (heigenComputed : 0 < backend.softAbs α computedHessian)
    (hsqrtComputed : 0 < backend.sqrt (backend.softAbs α computedHessian)) :
    SoftAbsMetricEntryCertificate α idealHessian := by
  let idealEigenvalue := Mcmc.Relativistic.softAbs α idealHessian
  let computedEigenvalue := backend.softAbs α computedHessian
  let eigenvalueError := backend.softAbsError α computedHessian
    idealHessian hessianError
  have hidealEigenvalue : 0 < idealEigenvalue := softAbs_pos α hα idealHessian
  have heigen : Approximates computedEigenvalue idealEigenvalue eigenvalueError :=
    backend.softAbs_bound α computedHessian idealHessian hessianError hα hhessian
  let computedSqrt := backend.sqrt computedEigenvalue
  let sqrtError := backend.sqrtError computedEigenvalue idealEigenvalue eigenvalueError
  have hsqrt : Approximates computedSqrt (Real.sqrt idealEigenvalue) sqrtError :=
    backend.sqrt_bound computedEigenvalue idealEigenvalue eigenvalueError
      heigenComputed hidealEigenvalue heigen
  let computedFactor := backend.inv computedSqrt
  let factorError := backend.invError computedSqrt
    (Real.sqrt idealEigenvalue) sqrtError
  have hidealSqrt : Real.sqrt idealEigenvalue ≠ 0 :=
    (Real.sqrt_pos.2 hidealEigenvalue).ne'
  have hfactor : Approximates computedFactor (Real.sqrt idealEigenvalue)⁻¹
      factorError :=
    backend.inv_bound computedSqrt (Real.sqrt idealEigenvalue) sqrtError
      hsqrtComputed.ne' hidealSqrt hsqrt
  let computedLogDet := backend.log computedEigenvalue
  let logDetError := backend.logError computedEigenvalue idealEigenvalue eigenvalueError
  have hlog : Approximates computedLogDet (Real.log idealEigenvalue) logDetError :=
    backend.log_bound computedEigenvalue idealEigenvalue eigenvalueError
      heigenComputed hidealEigenvalue heigen
  exact {
    computedHessian := computedHessian
    computedEigenvalue := computedEigenvalue
    computedSqrt := computedSqrt
    computedFactor := computedFactor
    computedLogDet := computedLogDet
    hessianError := hessianError
    eigenvalueError := eigenvalueError
    sqrtError := sqrtError
    factorError := factorError
    logDetError := logDetError
    hessian_bound := hhessian
    eigenvalue_bound := heigen
    factor_bound := hfactor
    logDet_bound := hlog }

/-- End-to-end generated-target bridge for the scalar sinusoidal SoftAbs
client. The restricted backend evaluates the generated second derivative;
the metric backend then transports that Hessian bound through SoftAbs and its
derived positive-domain operations. -/
noncomputable def restrictedSinusoidalSoftAbsMetricEntryCertificate
    (targetBackend : RestrictedBackend)
    (metricBackend : SoftAbsPrimitiveBackend)
    {computedInput idealInput inputError : ℝ}
    (hinput : Approximates computedInput idealInput inputError)
    (heigenComputed : 0 < metricBackend.softAbs 1
      (restrictedSinusoidalPotentialArtifact.derivative.derivative.backendEval
        targetBackend computedInput))
    (hsqrtComputed : 0 < metricBackend.sqrt (metricBackend.softAbs 1
      (restrictedSinusoidalPotentialArtifact.derivative.derivative.backendEval
        targetBackend computedInput))) :
    SoftAbsMetricEntryCertificate 1 (1 + Real.sin idealInput) := by
  let hessianExpression :=
    restrictedSinusoidalPotentialArtifact.derivative.derivative
  have hhessian : Approximates
      (hessianExpression.backendEval targetBackend computedInput)
      (1 + Real.sin idealInput)
      (hessianExpression.accumulatedError targetBackend computedInput
        idealInput inputError) := by
    have h := hessianExpression.backendEval_approximates targetBackend hinput
    rw [restrictedSinusoidalPotentialArtifact_secondDerivative_eval] at h
    exact h
  exact metricBackend.metricEntryCertificate (α := 1)
    (computedHessian := hessianExpression.backendEval targetBackend computedInput)
    (idealHessian := 1 + Real.sin idealInput)
    (hessianError := hessianExpression.accumulatedError targetBackend
      computedInput idealInput inputError)
    (by norm_num) hhessian heigenComputed hsqrtComputed

/-- Coordinatewise guarded certificates for a finite diagonal SoftAbs metric.
The aggregate log determinant is the sum of the certified scalar entries. -/
structure SoftAbsDiagonalMetricCertificate (ι : Type*) [Fintype ι]
    (α : ℝ) (idealHessian : ι → ℝ) where
  entry : ∀ i, SoftAbsMetricEntryCertificate α (idealHessian i)

namespace SoftAbsDiagonalMetricCertificate

variable {ι : Type*} [Fintype ι] {α : ℝ} {idealHessian : ι → ℝ}

noncomputable def computedLogDet
    (certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) : ℝ :=
  ∑ i, (certificate.entry i).computedLogDet

noncomputable def idealLogDet
    (_certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) : ℝ :=
  ∑ i, Real.log (Mcmc.Relativistic.softAbs α (idealHessian i))

noncomputable def logDetError
    (certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) : ℝ :=
  ∑ i, (certificate.entry i).logDetError

/-- Scalar log-determinant errors compose into the diagonal metric's complete
log-determinant error bound. -/
theorem logDet_bound
    (certificate : SoftAbsDiagonalMetricCertificate ι α idealHessian) :
    Approximates certificate.computedLogDet certificate.idealLogDet
      certificate.logDetError := by
  classical
  unfold computedLogDet idealLogDet logDetError
  exact Approximates.sum Finset.univ
    (fun i => (certificate.entry i).computedLogDet)
    (fun i => Real.log (Mcmc.Relativistic.softAbs α (idealHessian i)))
    (fun i => (certificate.entry i).logDetError)
    (fun i _ => (certificate.entry i).logDet_bound)

end SoftAbsDiagonalMetricCertificate

section ScalarHamiltonian

/-- A certified diagonal factor entry transports a certified scalar momentum.
This is the first missing connection from metric evaluation to the kinetic
energy actually used by GR-HMC. -/
theorem SoftAbsMetricEntryCertificate.factorMomentum_bound
    {α idealHessian computedMomentum idealMomentum momentumError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hmomentum : Approximates computedMomentum idealMomentum momentumError) :
    Approximates
      (certificate.computedFactor * computedMomentum)
      ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
        idealMomentum)
      (certificate.factorError * |computedMomentum| +
        |(Real.sqrt
          (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError) :=
  certificate.factor_bound.mul hmomentum

/-- Squaring the transformed momentum preserves a fully explicit absolute
error bound. -/
theorem SoftAbsMetricEntryCertificate.transformedMomentumSq_bound
    {α idealHessian computedMomentum idealMomentum momentumError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hmomentum : Approximates computedMomentum idealMomentum momentumError) :
    let computed := certificate.computedFactor * computedMomentum
    let ideal := (Real.sqrt
      (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ * idealMomentum
    let error := certificate.factorError * |computedMomentum| +
      |(Real.sqrt
        (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError
    Approximates (computed * computed) (ideal * ideal)
      (error * |computed| + |ideal| * error) := by
  dsimp only
  let h := certificate.factorMomentum_bound hmomentum
  exact h.mul h

/-- For unit rest mass and unit speed, the scalar relativistic radicand is
`1 + (A(q)p)²`.  A guarded backend square root therefore yields a certified
kinetic term. -/
theorem SoftAbsPrimitiveBackend.scalarUnitKinetic_bound
    (backend : SoftAbsPrimitiveBackend)
    {α idealHessian computedMomentum idealMomentum momentumError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hmomentum : Approximates computedMomentum idealMomentum momentumError)
    (hcomputedRadicand : 0 <
      (certificate.computedFactor * computedMomentum) ^ 2 + 1) :
    let computedTransformed := certificate.computedFactor * computedMomentum
    let idealTransformed := (Real.sqrt
      (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ * idealMomentum
    let transformedError := certificate.factorError * |computedMomentum| +
      |(Real.sqrt
        (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError
    let radicandError := transformedError * |computedTransformed| +
      |idealTransformed| * transformedError
    Approximates
      (backend.sqrt (computedTransformed ^ 2 + 1))
      (Real.sqrt (idealTransformed ^ 2 + 1))
      (backend.sqrtError (computedTransformed ^ 2 + 1)
        (idealTransformed ^ 2 + 1) radicandError) := by
  dsimp only
  have hsquare := certificate.transformedMomentumSq_bound hmomentum
  simp only [pow_two]
  have hradicand : Approximates
      ((certificate.computedFactor * computedMomentum) *
          (certificate.computedFactor * computedMomentum) + 1)
      (((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) *
        ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) + 1)
      ((certificate.factorError * |computedMomentum| +
          |(Real.sqrt
            (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| * momentumError) *
          |certificate.computedFactor * computedMomentum| +
        |(Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum| *
          (certificate.factorError * |computedMomentum| +
            |(Real.sqrt
              (Mcmc.Relativistic.softAbs α idealHessian))⁻¹| *
                momentumError)) := by
    simpa using hsquare.add (Approximates.refl 1)
  have hcomputed : 0 <
      (certificate.computedFactor * computedMomentum) *
          (certificate.computedFactor * computedMomentum) + 1 := by
    simpa [pow_two] using hcomputedRadicand
  have hideal : 0 <
      ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) *
        ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
          idealMomentum) + 1 := by
    nlinarith [sq_nonneg
      ((Real.sqrt (Mcmc.Relativistic.softAbs α idealHessian))⁻¹ *
        idealMomentum)]
  exact backend.sqrt_bound _ _ _ hcomputed hideal hradicand

/-- Compose potential, unit-parameter relativistic kinetic energy, and the
SoftAbs log-determinant contribution into the scalar GR Hamiltonian value.
The square-root approximation may come from
`SoftAbsPrimitiveBackend.scalarUnitKinetic_bound`. -/
theorem scalarUnitSoftAbsHamiltonian_bound
    {α idealHessian computedPotential idealPotential potentialError
      computedKinetic idealKinetic kineticError : ℝ}
    (certificate : SoftAbsMetricEntryCertificate α idealHessian)
    (hpotential : Approximates computedPotential idealPotential potentialError)
    (hkinetic : Approximates computedKinetic idealKinetic kineticError) :
    Approximates
      (computedPotential + computedKinetic +
        (1 / 2 : ℝ) * certificate.computedLogDet)
      (idealPotential + idealKinetic +
        (1 / 2 : ℝ) *
          Real.log (Mcmc.Relativistic.softAbs α idealHessian))
      (potentialError + kineticError +
        (0 * |certificate.computedLogDet| +
          |(1 / 2 : ℝ)| * certificate.logDetError)) := by
  exact (hpotential.add hkinetic).add
    ((Approximates.refl (1 / 2 : ℝ)).mul certificate.logDet_bound)

end ScalarHamiltonian

end Mcmc.Executable.Continuous
