import Mcmc.Relativistic.FixedPointIteration
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A concrete momentum-even position-dependent implicit solver

This module supplies a smooth scalar nonseparable Hamiltonian

`H(q,p) = a q √(1+p²)`.

It has the relativistic square-root momentum profile, is even under momentum
negation, and makes both generalized-leapfrog equations implicit.  Both
fixed-point maps are proved contractive under the explicit condition
`|εa/2| < 1`, yielding an exact, unique Banach-selected solve and convergent
finite iterations.

The Hamiltonian is a solver test model rather than a normalized statistical
target or a globally positive Riemannian kinetic energy.  Volume preservation
of the exact selected phase map remains a separate obligation.
-/

namespace Mcmc.Relativistic

open Mcmc.Hamiltonian MeasureTheory Filter Topology

/-- Scalar relativistic square-root profile. -/
noncomputable def scalarRelativisticProfile (p : ℝ) : ℝ :=
  Real.sqrt (1 + p ^ 2)

theorem scalarRelativisticProfile_pos (p : ℝ) :
    0 < scalarRelativisticProfile p := by
  unfold scalarRelativisticProfile
  positivity

@[simp] theorem scalarRelativisticProfile_neg (p : ℝ) :
    scalarRelativisticProfile (-p) = scalarRelativisticProfile p := by
  simp [scalarRelativisticProfile]

theorem deriv_scalarRelativisticProfile (p : ℝ) :
    deriv scalarRelativisticProfile p =
      p / scalarRelativisticProfile p := by
  have hnonzero : 1 + p ^ 2 ≠ 0 := by positivity
  have hderiv := (((hasDerivAt_id p).pow 2).const_add 1).sqrt hnonzero
  unfold scalarRelativisticProfile
  rw [show deriv (fun x : ℝ => Real.sqrt (1 + x ^ 2)) p =
      (2 * p) / (2 * Real.sqrt (1 + p ^ 2)) by
    convert hderiv.deriv using 1 <;> simp]
  have hsqrt : Real.sqrt (1 + p ^ 2) ≠ 0 :=
    ne_of_gt (scalarRelativisticProfile_pos p)
  field_simp [hsqrt]

theorem abs_div_scalarRelativisticProfile_le_one (p : ℝ) :
    |p / scalarRelativisticProfile p| ≤ 1 := by
  rw [abs_div, abs_of_pos (scalarRelativisticProfile_pos p),
    div_le_one (scalarRelativisticProfile_pos p)]
  unfold scalarRelativisticProfile
  rw [← (sq_le_sq₀ (abs_nonneg p) (Real.sqrt_nonneg _))]
  rw [sq_abs, Real.sq_sqrt (by positivity)]
  linarith

/-- The relativistic profile is globally one-Lipschitz. -/
theorem scalarRelativisticProfile_lipschitz :
    LipschitzWith 1 scalarRelativisticProfile := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro p
    unfold scalarRelativisticProfile
    apply HasDerivAt.differentiableAt
    apply HasDerivAt.sqrt ((((hasDerivAt_id p).pow 2).const_add 1))
    change 1 + p ^ 2 ≠ 0
    positivity
  · intro p
    rw [deriv_scalarRelativisticProfile]
    change |p / scalarRelativisticProfile p| ≤ 1
    exact abs_div_scalarRelativisticProfile_le_one p

/-- Smooth momentum-even nonseparable Hamiltonian used by the concrete
solver. -/
noncomputable def linearRelativisticHamiltonian (a : ℝ)
    (z : PhaseSpace Unit) : ℝ :=
  a * z.fst Unit.unit * scalarRelativisticProfile (z.snd Unit.unit)

@[simp] theorem linearRelativisticHamiltonian_momentumFlip
    (a : ℝ) (z : PhaseSpace Unit) :
    linearRelativisticHamiltonian a (momentumFlip z) =
      linearRelativisticHamiltonian a z := by
  simp [linearRelativisticHamiltonian, momentumFlip]

/-- `∂H/∂q = a √(1+p²)`. -/
noncomputable def linearRelativisticPositionDerivative (a : ℝ) :
    PhaseSpace Unit → Position Unit :=
  fun z _ => a * scalarRelativisticProfile (z.snd Unit.unit)

/-- `∂H/∂p = a q p / √(1+p²)`. -/
noncomputable def linearRelativisticMomentumDerivative (a : ℝ) :
    PhaseSpace Unit → Position Unit :=
  fun z _ => a * z.fst Unit.unit *
    (z.snd Unit.unit / scalarRelativisticProfile (z.snd Unit.unit))

@[simp] theorem linearRelativisticPositionDerivative_flip
    (a : ℝ) (z : PhaseSpace Unit) :
    linearRelativisticPositionDerivative a (momentumFlip z) =
      linearRelativisticPositionDerivative a z := by
  ext i
  simp [linearRelativisticPositionDerivative, momentumFlip]

@[simp] theorem linearRelativisticMomentumDerivative_flip
    (a : ℝ) (z : PhaseSpace Unit) :
    linearRelativisticMomentumDerivative a (momentumFlip z) =
      -linearRelativisticMomentumDerivative a z := by
  ext i
  simp [linearRelativisticMomentumDerivative, momentumFlip]
  ring

/-- The supplied position derivative is the actual derivative of the
Hamiltonian in its scalar position coordinate. -/
theorem hasDerivAt_linearRelativisticHamiltonian_position
    (a q p : ℝ) :
    HasDerivAt (fun x => a * x * scalarRelativisticProfile p)
      (a * scalarRelativisticProfile p) q := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (hasDerivAt_id q).mul_const (a * scalarRelativisticProfile p)

/-- The supplied momentum derivative is the actual derivative of the
Hamiltonian in its scalar momentum coordinate. -/
theorem hasDerivAt_linearRelativisticHamiltonian_momentum
    (a q p : ℝ) :
    HasDerivAt (fun x => a * q * scalarRelativisticProfile x)
      (a * q * (p / scalarRelativisticProfile p)) p := by
  have hdiff : HasDerivAt scalarRelativisticProfile
      (p / scalarRelativisticProfile p) p := by
    rw [← deriv_scalarRelativisticProfile]
    unfold scalarRelativisticProfile
    apply DifferentiableAt.hasDerivAt
    apply HasDerivAt.differentiableAt
    apply HasDerivAt.sqrt ((((hasDerivAt_id p).pow 2).const_add 1))
    change 1 + p ^ 2 ≠ 0
    positivity
  exact hdiff.const_mul (a * q)

/-- Sup norm on the one-coordinate function space. -/
theorem norm_pi_unit (x : Unit → ℝ) : ‖x‖ = |x Unit.unit| := by
  rw [Pi.norm_def]
  simp [Real.norm_eq_abs]

/-- Exact common contraction rate for the two implicit maps. -/
noncomputable def linearRelativisticFixedPointRate (a ε : ℝ) : NNReal :=
  ⟨|ε / 2 * a|, abs_nonneg _⟩

theorem linearRelativistic_halfMomentum_contracting (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace Unit) :
    ContractingWith (linearRelativisticFixedPointRate a ε)
      (halfMomentumFixedPointUpdate
        (linearRelativisticPositionDerivative a) ε z) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [dist_eq_norm, dist_eq_norm, norm_pi_unit, norm_pi_unit]
    change |(z.snd Unit.unit - ε / 2 *
        (a * scalarRelativisticProfile (p Unit.unit))) -
      (z.snd Unit.unit - ε / 2 *
        (a * scalarRelativisticProfile (q Unit.unit)))| ≤
      |ε / 2 * a| * |p Unit.unit - q Unit.unit|
    calc
      _ = |-(ε / 2 * a) *
          (scalarRelativisticProfile (p Unit.unit) -
            scalarRelativisticProfile (q Unit.unit))| := by
        congr 1
        ring
      _ = |ε / 2 * a| *
          |scalarRelativisticProfile (p Unit.unit) -
            scalarRelativisticProfile (q Unit.unit)| := by
        rw [abs_mul, abs_neg]
      _ ≤ |ε / 2 * a| * |p Unit.unit - q Unit.unit| := by
        have hlip := scalarRelativisticProfile_lipschitz.dist_le_mul
          (p Unit.unit) (q Unit.unit)
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.dist_eq] using hlip) (abs_nonneg _)

theorem linearRelativistic_nextPosition_contracting (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (q : Position Unit)
    (p : Momentum Unit) :
    ContractingWith (linearRelativisticFixedPointRate a ε)
      (positionFixedPointUpdate
        (linearRelativisticMomentumDerivative a) ε q p) := by
  constructor
  · exact hstep
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, norm_pi_unit, norm_pi_unit]
    simp only [positionFixedPointUpdate,
      linearRelativisticMomentumDerivative, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Pi.sub_apply]
    change |(q Unit.unit + ε / 2 *
        (a * q Unit.unit *
            (p Unit.unit / scalarRelativisticProfile (p Unit.unit)) +
          a * x Unit.unit *
            (p Unit.unit / scalarRelativisticProfile (p Unit.unit)))) -
      (q Unit.unit + ε / 2 *
        (a * q Unit.unit *
            (p Unit.unit / scalarRelativisticProfile (p Unit.unit)) +
          a * y Unit.unit *
            (p Unit.unit / scalarRelativisticProfile (p Unit.unit))))| ≤
      |ε / 2 * a| * |x Unit.unit - y Unit.unit|
    calc
      _ = |ε / 2 * a| *
          |p Unit.unit / scalarRelativisticProfile (p Unit.unit)| *
          |x Unit.unit - y Unit.unit| := by
        rw [← abs_mul, ← abs_mul]
        congr 1
        ring
      _ ≤ |ε / 2 * a| * 1 * |x Unit.unit - y Unit.unit| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (abs_div_scalarRelativisticProfile_le_one _) (abs_nonneg _))
          (abs_nonneg _)
      _ = _ := by ring

/-- Concrete exact fixed-step solver for the smooth momentum-even
position-dependent Hamiltonian. -/
noncomputable def linearRelativisticContractiveSolverAt (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) :
    ContractiveGeneralizedLeapfrogSolverAt
      (linearRelativisticPositionDerivative a)
      (linearRelativisticMomentumDerivative a) ε where
  halfRate _ := linearRelativisticFixedPointRate a ε
  halfContracting := linearRelativistic_halfMomentum_contracting a ε hstep
  positionRate _ _ := linearRelativisticFixedPointRate a ε
  positionContracting := linearRelativistic_nextPosition_contracting a ε hstep

/-- The practical half-momentum iteration converges to the exact solve. -/
theorem linearRelativistic_finiteHalfMomentum_tendsto (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace Unit) :
    Tendsto (fun n => finiteHalfMomentum
      (linearRelativisticPositionDerivative a) n ε z) atTop
      (𝓝 ((linearRelativisticContractiveSolverAt a ε hstep).halfMomentum z)) := by
  let solver := linearRelativisticContractiveSolverAt a ε hstep
  change Tendsto _ _ (𝓝 ((solver.halfContracting z).fixedPoint
    (halfMomentumFixedPointUpdate
      (linearRelativisticPositionDerivative a) ε z)))
  exact finiteHalfMomentum_tendsto_fixedPoint
    (linearRelativisticPositionDerivative a) (solver.halfRate z) ε z
    (solver.halfContracting z)

/-- With the exact half momentum fixed, the practical position iteration also
converges to the exact solve. -/
theorem linearRelativistic_finiteNextPosition_tendsto (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace Unit) :
    let solver := linearRelativisticContractiveSolverAt a ε hstep
    Tendsto (fun n => finiteNextPosition
      (linearRelativisticMomentumDerivative a) n ε z.1
        (solver.halfMomentum z)) atTop (𝓝 (solver.nextPosition z)) := by
  dsimp only
  let solver := linearRelativisticContractiveSolverAt a ε hstep
  change Tendsto _ _ (𝓝 ((solver.positionContracting z.1
    (solver.halfMomentum z)).fixedPoint
      (positionFixedPointUpdate (linearRelativisticMomentumDerivative a) ε
        z.1 (solver.halfMomentum z))))
  exact finiteNextPosition_tendsto_fixedPoint
    (linearRelativisticMomentumDerivative a)
    (solver.positionRate z.1 (solver.halfMomentum z)) ε z.1
    (solver.halfMomentum z)
    (solver.positionContracting z.1 (solver.halfMomentum z))

theorem measurable_linearRelativisticPositionDerivative (a : ℝ) :
    Measurable (linearRelativisticPositionDerivative a) := by
  unfold linearRelativisticPositionDerivative scalarRelativisticProfile
  fun_prop

theorem measurable_linearRelativisticMomentumDerivative (a : ℝ) :
    Measurable (linearRelativisticMomentumDerivative a) := by
  unfold linearRelativisticMomentumDerivative scalarRelativisticProfile
  fun_prop

/-- The exact Banach-selected fixed-step phase map is measurable. The proof
uses the measurable finite iterations and their pointwise convergence to the
exact fixed points. -/
theorem measurable_linearRelativisticContractiveSolverAt_step (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) :
    Measurable (linearRelativisticContractiveSolverAt a ε hstep).step := by
  let solver := linearRelativisticContractiveSolverAt a ε hstep
  have hhalf : Measurable solver.halfMomentum := by
    refine measurable_of_tendsto_metrizable
      (f := fun n z => finiteHalfMomentum
        (linearRelativisticPositionDerivative a) n ε z)
      (g := solver.halfMomentum) ?_ ?_
    · intro n
      exact measurable_finiteHalfMomentum
        (measurable_linearRelativisticPositionDerivative a) n ε
    · rw [tendsto_pi_nhds]
      intro z
      exact linearRelativistic_finiteHalfMomentum_tendsto a ε hstep z
  have hnext : Measurable solver.nextPosition := by
    refine measurable_of_tendsto_metrizable
      (f := fun n z => finiteNextPosition
        (linearRelativisticMomentumDerivative a) n ε z.1
          (solver.halfMomentum z))
      (g := solver.nextPosition) ?_ ?_
    · intro n
      exact (measurable_finiteNextPosition
        (measurable_linearRelativisticMomentumDerivative a) n ε).comp
          (measurable_fst.prodMk hhalf)
    · rw [tendsto_pi_nhds]
      intro z
      exact linearRelativistic_finiteNextPosition_tendsto a ε hstep z
  change Measurable fun z =>
    (solver.nextPosition z, solver.halfMomentum z - (ε / 2) •
      linearRelativisticPositionDerivative a
        (solver.nextPosition z, solver.halfMomentum z))
  exact hnext.prodMk (hhalf.sub
    ((measurable_const : Measurable (fun _ : PhaseSpace Unit => ε / 2)).smul
    ((measurable_linearRelativisticPositionDerivative a).comp
      (hnext.prodMk hhalf))))

/-- Momentum parity plus uniqueness makes the exact fixed-step solve
time-reversible across the certified `ε` and `-ε` solvers. -/
theorem linearRelativisticContractiveSolverAt_reversible (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) (z : PhaseSpace Unit) :
    let forward := linearRelativisticContractiveSolverAt a ε hstep
    let hbackward : |(-ε) / 2 * a| < 1 := by
      simpa [neg_div] using hstep
    let backward := linearRelativisticContractiveSolverAt a (-ε) hbackward
    momentumFlip (forward.step (momentumFlip z)) = backward.step z := by
  dsimp only
  let hbackward : |(-ε) / 2 * a| < 1 := by
    simpa [neg_div] using hstep
  let forward := linearRelativisticContractiveSolverAt a ε hstep
  let backward := linearRelativisticContractiveSolverAt a (-ε) hbackward
  let pHalf := forward.halfMomentum (momentumFlip z)
  have hforward := forward.satisfies (momentumFlip z)
  have hreverse : GeneralizedLeapfrogEquations
      (linearRelativisticPositionDerivative a)
      (linearRelativisticMomentumDerivative a) (-ε) z (-pHalf)
      (momentumFlip (forward.step (momentumFlip z))) := by
    rcases hforward with ⟨hp, hq, hpNext⟩
    constructor
    · ext i
      have hi := congrFun hp i
      simp [pHalf, momentumFlip, linearRelativisticPositionDerivative] at hi ⊢
      linarith
    constructor
    · ext i
      have hi := congrFun hq i
      simp [pHalf, momentumFlip, linearRelativisticMomentumDerivative] at hi ⊢
      ring_nf at hi ⊢
      exact hi
    · ext i
      have hi := congrFun hpNext i
      simp [pHalf, momentumFlip, linearRelativisticPositionDerivative] at hi ⊢
      linarith
  exact (backward.unique z (-pHalf)
    (momentumFlip (forward.step (momentumFlip z))) hreverse).2

/-- The remaining analytic data needed to promote the concrete exact solve
from a reversible measurable integrator to a phase-volume-preserving one. The
determinant field is the precise theorem suggested by the executable
finite-difference regression; it is not inferred from that regression. -/
structure LinearRelativisticJacobianCertificate (a ε : ℝ)
    (hstep : |ε / 2 * a| < 1) : Prop where
  differentiable : Differentiable ℝ
    (linearRelativisticContractiveSolverAt a ε hstep).step
  absDetOne : ∀ z,
    |(fderiv ℝ (linearRelativisticContractiveSolverAt a ε hstep).step z).det| = 1

/-- A unit-Jacobian certificate closes the exact phase-volume obligation by
the finite-dimensional change-of-variables theorem. Bijectivity is derived,
not assumed, from the unique opposite-step solve. -/
theorem LinearRelativisticJacobianCertificate.volumePreserving
    {a ε : ℝ} {hstep : |ε / 2 * a| < 1}
    (certificate : LinearRelativisticJacobianCertificate a ε hstep) :
    MeasurePreserving
      (linearRelativisticContractiveSolverAt a ε hstep).step
      (phaseVolume : Measure (PhaseSpace Unit)) phaseVolume := by
  let hbackward : |(-ε) / 2 * a| < 1 := by
    simpa [neg_div] using hstep
  let forward := linearRelativisticContractiveSolverAt a ε hstep
  let backward := linearRelativisticContractiveSolverAt a (-ε) hbackward
  letI : Measure.IsAddHaarMeasure
      (phaseVolume : Measure (PhaseSpace Unit)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  exact measurePreserving_of_bijective_differentiable_abs_det_one
    (phaseVolume : Measure (PhaseSpace Unit)) forward.step certificate.differentiable
    (forward.step_bijective backward) certificate.absDetOne

end Mcmc.Relativistic
