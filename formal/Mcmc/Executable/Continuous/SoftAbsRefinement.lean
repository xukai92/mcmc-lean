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

end Mcmc.Executable.Continuous
