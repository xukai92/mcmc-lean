import Mcmc.Executable.Continuous.HMC

/-!
# Constant-metric endpoint HMC

Exact finite-dimensional foundations for diagonal and dense constant mass
matrices. The proofs use only that velocity is measurable and odd; matrix
positive-definiteness is needed separately to construct its Gaussian momentum
law and is checked by the Julia public API.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Hamiltonian MeasureTheory

variable {ι : Type*} [Fintype ι]

def metricDrift (velocity : Momentum ι → Position ι) (ε : ℝ)
    (q : Position ι) (p : Momentum ι) : Position ι :=
  q + ε • velocity p

noncomputable def metricLeapfrog (velocity : Momentum ι → Position ι)
    (gradient : Position ι → Momentum ι) (ε : ℝ) (z : PhaseSpace ι) :
    PhaseSpace ι :=
  let pHalf := z.2 - (ε / 2) • gradient z.1
  let qNext := metricDrift velocity ε z.1 pHalf
  (qNext, pHalf - (ε / 2) • gradient qNext)

noncomputable def metricLeapfrogN (velocity : Momentum ι → Position ι)
    (gradient : Position ι → Momentum ι) (ε : ℝ) : Nat → PhaseSpace ι → PhaseSpace ι
  | 0, z => z
  | n + 1, z => metricLeapfrog velocity gradient ε
      (metricLeapfrogN velocity gradient ε n z)

noncomputable def metricDriftPhase (velocity : Momentum ι → Position ι)
    (ε : ℝ) (z : PhaseSpace ι) : PhaseSpace ι :=
  (metricDrift velocity ε z.1 z.2, z.2)

omit [Fintype ι] in theorem measurable_metricDriftPhase {velocity : Momentum ι → Position ι}
    (hvelocity : Measurable velocity) (ε : ℝ) :
    Measurable (metricDriftPhase velocity ε) := by
  unfold metricDriftPhase metricDrift
  fun_prop

theorem measurePreserving_metricDriftPhase
    {velocity : Momentum ι → Position ι} (hvelocity : Measurable velocity)
    (ε : ℝ) :
    MeasurePreserving (metricDriftPhase velocity ε) phaseVolume phaseVolume := by
  let shear : Momentum ι × Position ι → Momentum ι × Position ι :=
    fun z => (z.1, z.2 + ε • velocity z.1)
  have hshear : MeasurePreserving shear
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι)))
      ((volume : Measure (Momentum ι)).prod (volume : Measure (Position ι))) := by
    exact (MeasurePreserving.id (volume : Measure (Momentum ι))).skew_product
      (g := fun p q => q + ε • velocity p) (by fun_prop)
      (ae_of_all _ fun p =>
        map_add_right_eq_self (volume : Measure (Position ι)) (ε • velocity p))
  have h := (Measure.measurePreserving_swap (μ := (volume : Measure (Momentum ι)))
    (ν := (volume : Measure (Position ι)))).comp
      (hshear.comp Measure.measurePreserving_swap)
  apply h.congr (measurable_metricDriftPhase hvelocity ε)
  filter_upwards [] with z
  rfl

theorem measurePreserving_metricLeapfrog
    {velocity : Momentum ι → Position ι} {gradient : Position ι → Momentum ι}
    (hvelocity : Measurable velocity) (hgradient : Measurable gradient) (ε : ℝ) :
    MeasurePreserving (metricLeapfrog velocity gradient ε) phaseVolume phaseVolume := by
  change MeasurePreserving
    (Mcmc.Hamiltonian.kickPhase gradient ε ∘ metricDriftPhase velocity ε ∘
      Mcmc.Hamiltonian.kickPhase gradient ε) phaseVolume phaseVolume
  exact (measurePreserving_kickPhase hgradient ε).comp
    ((measurePreserving_metricDriftPhase hvelocity ε).comp
      (measurePreserving_kickPhase hgradient ε))

theorem measurePreserving_metricLeapfrogN
    {velocity : Momentum ι → Position ι} {gradient : Position ι → Momentum ι}
    (hvelocity : Measurable velocity) (hgradient : Measurable gradient)
    (ε : ℝ) (steps : Nat) :
    MeasurePreserving (metricLeapfrogN velocity gradient ε steps)
      phaseVolume phaseVolume := by
  induction steps with
  | zero => exact MeasurePreserving.id _
  | succ steps ih =>
      exact (measurePreserving_metricLeapfrog hvelocity hgradient ε).comp ih

/-- A dense constant inverse-mass operator is represented abstractly as a
measurable odd linear velocity map; matrix multiplication is one instance. -/
structure ConstantMetric (ι : Type*) [Fintype ι] where
  velocity : Momentum ι → Position ι
  measurable_velocity : Measurable velocity
  velocity_odd : ∀ p, velocity (-p) = -velocity p

/-- Diagonal inverse-mass velocity, covering the executable diagonal metric. -/
def diagonalVelocity (inverseMass : ι → ℝ) (p : Momentum ι) : Position ι :=
  fun i => inverseMass i * p i

omit [Fintype ι] in theorem measurable_diagonalVelocity (inverseMass : ι → ℝ) :
    Measurable (diagonalVelocity inverseMass) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_const.mul (measurable_pi_apply i)

omit [Fintype ι] in theorem diagonalVelocity_odd (inverseMass : ι → ℝ) (p : Momentum ι) :
    diagonalVelocity inverseMass (-p) = -diagonalVelocity inverseMass p := by
  funext i
  simp [diagonalVelocity]

def diagonalMetric (inverseMass : ι → ℝ) : ConstantMetric ι where
  velocity := diagonalVelocity inverseMass
  measurable_velocity := measurable_diagonalVelocity inverseMass
  velocity_odd := diagonalVelocity_odd inverseMass

/-- Dense inverse-mass matrix-vector multiplication. -/
noncomputable def denseVelocity (inverseMass : ι → ι → ℝ)
    (p : Momentum ι) : Position ι :=
  fun i => ∑ j, inverseMass i j * p j

theorem measurable_denseVelocity (inverseMass : ι → ι → ℝ) :
    Measurable (denseVelocity inverseMass) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ fun j _ =>
    measurable_const.mul (measurable_pi_apply j)

theorem denseVelocity_odd (inverseMass : ι → ι → ℝ)
    (p : Momentum ι) :
    denseVelocity inverseMass (-p) = -denseVelocity inverseMass p := by
  funext i
  simp [denseVelocity]

noncomputable def denseMetric (inverseMass : ι → ι → ℝ) : ConstantMetric ι where
  velocity := denseVelocity inverseMass
  measurable_velocity := measurable_denseVelocity inverseMass
  velocity_odd := denseVelocity_odd inverseMass

end Mcmc.Executable.Continuous
