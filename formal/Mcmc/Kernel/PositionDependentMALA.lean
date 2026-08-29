import Mcmc.Kernel.GaussianRandomWalk

/-!
# Position-dependent Metropolis-adjusted Langevin foundations

This module separates the drift convention of position-dependent MALA from
the generic density-MH correctness argument. The primary drift is appropriate
for a target density with respect to Lebesgue measure: half the inverse-metric
score plus half the row divergence of the inverse metric.

The proposal-density record deliberately requires measurability and
normalization. A dense or structured Gaussian client must discharge those
facts for the same mean and covariance used by its forward/reverse Hastings
ratio; merely supplying matrix callbacks is not enough.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory BigOperators

namespace Mcmc.Kernel

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- Matrix-vector action for an inverse metric represented by its entries. -/
def inverseMetricAction (inverseMetric : (ι → ℝ) → ι → ι → ℝ)
    (q v : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, inverseMetric q i j * v j

/-- Row divergence `Σ_j ∂_j A_ij(q)` of an inverse metric `A(q)`. The
derivative callback is indexed as `derivative q j i k = ∂_j A_ik(q)`. -/
def inverseMetricDivergence
    (derivative : (ι → ℝ) → ι → ι → ι → ℝ)
    (q : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, derivative q j i j

/-- Derivative of `A = G⁻¹` obtained from `∂A = -A (∂G) A`.
The metric derivative is indexed as `metricDerivative q j a b = ∂_j G_ab`. -/
def inverseMetricDerivativeFromMetric
    (inverseMetric : (ι → ℝ) → ι → ι → ℝ)
    (metricDerivative : (ι → ℝ) → ι → ι → ι → ℝ)
    (q : ι → ℝ) (j i k : ι) : ℝ :=
  -∑ a, ∑ b, inverseMetric q i a * metricDerivative q j a b *
    inverseMetric q b k

/-- Lebesgue-correct position-dependent Langevin drift
`(A(q) ∇logπ(q) + div A(q)) / 2`. -/
noncomputable def positionDependentMalaDrift
    (inverseMetric : (ι → ℝ) → ι → ι → ℝ)
    (derivative : (ι → ℝ) → ι → ι → ι → ℝ)
    (score : (ι → ℝ) → ι → ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  (inverseMetricAction inverseMetric q (score q) i +
    inverseMetricDivergence derivative q i) / 2

/-- Simplified manifold-MALA drift. With the actual asymmetric proposal
density it remains a valid MH proposal, but it omits the diffusion divergence
correction. -/
noncomputable def simplifiedPositionDependentMalaDrift
    (inverseMetric : (ι → ℝ) → ι → ι → ℝ)
    (score : (ι → ℝ) → ι → ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  inverseMetricAction inverseMetric q (score q) i / 2

/-- Euler proposal mean for time increment `variance = ε²`. -/
noncomputable def positionDependentMalaMean (variance : ℝ)
    (inverseMetric : (ι → ℝ) → ι → ι → ℝ)
    (derivative : (ι → ℝ) → ι → ι → ι → ℝ)
    (score : (ι → ℝ) → ι → ℝ) (q : ι → ℝ) (i : ι) : ℝ :=
  q i + variance * positionDependentMalaDrift
    inverseMetric derivative score q i

theorem positionDependentMalaDrift_eq_simplified_of_zero_divergence
    (inverseMetric : (ι → ℝ) → ι → ι → ℝ)
    (derivative : (ι → ℝ) → ι → ι → ι → ℝ)
    (score : (ι → ℝ) → ι → ℝ)
    (hzero : ∀ q i, inverseMetricDivergence derivative q i = 0) :
    positionDependentMalaDrift inverseMetric derivative score =
      simplifiedPositionDependentMalaDrift inverseMetric score := by
  funext q i
  simp [positionDependentMalaDrift, simplifiedPositionDependentMalaDrift,
    hzero q i]

/-- The corrected position-dependent drift reduces to ordinary Euclidean MALA
for the identity inverse metric and a zero metric derivative. -/
theorem positionDependentMalaDrift_identity
    [DecidableEq ι] (score : (ι → ℝ) → ι → ℝ) (q : ι → ℝ) (i : ι) :
    positionDependentMalaDrift
      (fun _ row column => if row = column then 1 else 0)
      (fun _ _ _ _ => 0) score q i = score q i / 2 := by
  simp [positionDependentMalaDrift, inverseMetricAction,
    inverseMetricDivergence]

/-- Quadratic form of a position-dependent precision/metric matrix. -/
def metricQuadratic (metric : (ι → ℝ) → ι → ι → ℝ)
    (q residual : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, residual i * metric q i j * residual j

/-- Dense Gaussian PMALA proposal density with mean `mean(q)`, covariance
`ε² G(q)⁻¹`, and Lebesgue reference measure. `logDetMetric` denotes
`log det G(q)`. -/
noncomputable def densePmalaProposalDensity (stepSize : ℝ)
    (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ) (q proposed : ι → ℝ) : ENNReal :=
  let residual := proposed - mean q
  ENNReal.ofReal (Real.exp (
    (logDetMetric q) / 2 -
    (Fintype.card ι : ℝ) * Real.log stepSize -
    (Fintype.card ι : ℝ) * Real.log (2 * Real.pi) / 2 -
    metricQuadratic metric q residual / (2 * stepSize ^ 2)))

/-- A position-dependent proposal density together with exactly the analytic
facts required by density-based MH. Gaussian clients must prove these fields
for their state-dependent mean and covariance. -/
structure PositionDependentProposalDensity
    (State : Type*) [MeasurableSpace State] (reference : Measure State) where
  density : State → State → ENNReal
  measurable_uncurry : Measurable (Function.uncurry density)
  normalized : ∀ x, ∫⁻ y, density x y ∂reference = 1

/-- Concrete dense Gaussian proposal record after analytic measurability and
normalization have been proved for the supplied metric client. -/
noncomputable def densePmalaProposal
    (stepSize : ℝ) (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize mean metric logDetMetric q proposed
        ∂volume = 1) :
    PositionDependentProposalDensity (ι → ℝ) volume where
  density := densePmalaProposalDensity stepSize mean metric logDetMetric
  measurable_uncurry := hmeasurable
  normalized := hnormalized

variable {State : Type*} [MeasurableSpace State]

/-- Metropolis completion of a normalized position-dependent proposal. -/
noncomputable def positionDependentMALA
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal)
    (proposal : PositionDependentProposalDensity State reference) :
    Kernel State State :=
  densityMetropolisHastings reference weight proposal.density
    proposal.measurable_uncurry proposal.normalized

theorem positionDependentMALA_isMarkov
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (hweight : Measurable weight)
    (proposal : PositionDependentProposalDensity State reference) :
    IsMarkovKernel (positionDependentMALA reference weight proposal) := by
  exact densityMetropolisHastings_isMarkov reference weight proposal.density
    hweight proposal.measurable_uncurry proposal.normalized

theorem positionDependentMALA_isReversible
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (hweight : Measurable weight)
    (proposal : PositionDependentProposalDensity State reference)
    (hfinite : ∀ x y, forwardDensityFlow weight proposal.density x y ≠ ∞) :
    (positionDependentMALA reference weight proposal).IsReversible
      (densityTarget reference weight) := by
  exact densityMetropolisHastings_isReversible reference weight
    proposal.density hweight proposal.measurable_uncurry proposal.normalized
    hfinite

theorem positionDependentMALA_invariant
    (reference : Measure State) [SFinite reference]
    (weight : State → ENNReal) (hweight : Measurable weight)
    (proposal : PositionDependentProposalDensity State reference)
    (hfinite : ∀ x y, forwardDensityFlow weight proposal.density x y ≠ ∞) :
    (positionDependentMALA reference weight proposal).Invariant
      (densityTarget reference weight) := by
  exact densityMetropolisHastings_invariant reference weight proposal.density
    hweight proposal.measurable_uncurry proposal.normalized hfinite

/-- Dense Gaussian PMALA kernel for a concrete mean, metric, and log
determinant whose density obligations have been discharged. -/
noncomputable def densePMALA (weight : (ι → ℝ) → ENNReal)
    (stepSize : ℝ) (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize mean metric logDetMetric q proposed
        ∂volume = 1) : Kernel (ι → ℝ) (ι → ℝ) :=
  positionDependentMALA volume weight
    (densePmalaProposal stepSize mean metric logDetMetric
      hmeasurable hnormalized)

theorem densePMALA_isMarkov (weight : (ι → ℝ) → ENNReal)
    (stepSize : ℝ) (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ) (hweight : Measurable weight)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize mean metric logDetMetric q proposed
        ∂volume = 1) :
    IsMarkovKernel (densePMALA weight stepSize mean metric logDetMetric
      hmeasurable hnormalized) := by
  exact positionDependentMALA_isMarkov volume weight hweight
    (densePmalaProposal stepSize mean metric logDetMetric
      hmeasurable hnormalized)

theorem densePMALA_isReversible (weight : (ι → ℝ) → ENNReal)
    (stepSize : ℝ) (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ) (hweight : Measurable weight)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize mean metric logDetMetric q proposed
        ∂volume = 1)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (densePmalaProposalDensity stepSize mean metric logDetMetric) x y ≠ ∞) :
    (densePMALA weight stepSize mean metric logDetMetric
      hmeasurable hnormalized).IsReversible (densityTarget volume weight) := by
  exact positionDependentMALA_isReversible volume weight hweight
    (densePmalaProposal stepSize mean metric logDetMetric
      hmeasurable hnormalized) hfinite

theorem densePMALA_invariant (weight : (ι → ℝ) → ENNReal)
    (stepSize : ℝ) (mean : (ι → ℝ) → ι → ℝ)
    (metric : (ι → ℝ) → ι → ι → ℝ)
    (logDetMetric : (ι → ℝ) → ℝ)
    (hweight : Measurable weight)
    (hmeasurable : Measurable (Function.uncurry
      (densePmalaProposalDensity stepSize mean metric logDetMetric)))
    (hnormalized : ∀ q, ∫⁻ proposed,
      densePmalaProposalDensity stepSize mean metric logDetMetric q proposed
        ∂volume = 1)
    (hfinite : ∀ x y, forwardDensityFlow weight
      (densePmalaProposalDensity stepSize mean metric logDetMetric) x y ≠ ∞) :
    (densePMALA weight stepSize mean metric logDetMetric
      hmeasurable hnormalized).Invariant (densityTarget volume weight) := by
  exact positionDependentMALA_invariant volume weight hweight
    (densePmalaProposal stepSize mean metric logDetMetric
      hmeasurable hnormalized) hfinite

end Mcmc.Kernel
