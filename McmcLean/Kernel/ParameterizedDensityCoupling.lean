import McmcLean.Kernel.DensityCoupling
import McmcLean.Kernel.MetropolisHastings

/-!
# Measurable maximal couplings of parameterized densities

This module packages the common-density/residual construction as a Markov
kernel.  It is the reusable bridge from a jointly measurable family of
probability densities to a measurable maximal proposal coupling.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace McmcLean.Kernel

open ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

section

variable (reference : Measure State) [SFinite reference]
variable (density : State → State → ENNReal)

/-- Common density of two rows in a parameterized density family. -/
noncomputable def parameterizedCommonDensity
    (current : State × State) (z : State) : ENNReal :=
  min (density current.1 z) (density current.2 z)

/-- Common mass of two rows in a parameterized density family. -/
noncomputable def parameterizedOverlap (current : State × State) : ENNReal :=
  ∫⁻ z, parameterizedCommonDensity density current z ∂reference

theorem measurable_parameterizedOverlap
    (hmeas : Measurable (Function.uncurry density)) :
    Measurable (parameterizedOverlap reference density) := by
  apply Measurable.lintegral_prod_right
  exact (hmeas.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).min
    (hmeas.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- Left residual density after removing the common part. -/
noncomputable def parameterizedLeftResidualDensity
    (current : State × State) (z : State) : ENNReal :=
  density current.1 z - parameterizedCommonDensity density current z

/-- Right residual density after removing the common part. -/
noncomputable def parameterizedRightResidualDensity
    (current : State × State) (z : State) : ENNReal :=
  density current.2 z - parameterizedCommonDensity density current z

theorem measurable_uncurry_parameterizedCommonDensity
    (hmeas : Measurable (Function.uncurry density)) :
    Measurable (Function.uncurry (parameterizedCommonDensity density)) := by
  exact (hmeas.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).min
    (hmeas.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem measurable_uncurry_parameterizedLeftResidualDensity
    (hmeas : Measurable (Function.uncurry density)) :
    Measurable (Function.uncurry
      (parameterizedLeftResidualDensity density)) := by
  exact (hmeas.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
    (measurable_uncurry_parameterizedCommonDensity density hmeas)

theorem measurable_uncurry_parameterizedRightResidualDensity
    (hmeas : Measurable (Function.uncurry density)) :
    Measurable (Function.uncurry
      (parameterizedRightResidualDensity density)) := by
  exact (hmeas.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)).sub
    (measurable_uncurry_parameterizedCommonDensity density hmeas)

/-- Common mass, mapped onto the diagonal. -/
noncomputable def parameterizedCommonKernel
    (_hmeas : Measurable (Function.uncurry density)) :
    Kernel (State × State) (State × State) :=
  Kernel.map
    ((Kernel.const (State × State) reference).withDensity
      (parameterizedCommonDensity density))
    (fun z => (z, z))

/-- Left residual subkernel. -/
noncomputable def parameterizedLeftResidualKernel
    (_hmeas : Measurable (Function.uncurry density)) :
    Kernel (State × State) State :=
  (Kernel.const (State × State) reference).withDensity
    (parameterizedLeftResidualDensity density)

/-- Right residual subkernel. -/
noncomputable def parameterizedRightResidualKernel
    (_hmeas : Measurable (Function.uncurry density)) :
    Kernel (State × State) State :=
  (Kernel.const (State × State) reference).withDensity
    (parameterizedRightResidualDensity density)

theorem parameterizedLeftResidualKernel_isSFinite
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞) :
    IsSFiniteKernel
      (parameterizedLeftResidualKernel reference density hmeas) := by
  unfold parameterizedLeftResidualKernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro current z
  exact ne_top_of_le_ne_top (hfinite current.1 z) tsub_le_self

theorem parameterizedRightResidualKernel_isSFinite
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞) :
    IsSFiniteKernel
      (parameterizedRightResidualKernel reference density hmeas) := by
  unfold parameterizedRightResidualKernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro current z
  exact ne_top_of_le_ne_top (hfinite current.2 z) tsub_le_self

/-- Independently coupled residual subkernels. -/
noncomputable def parameterizedResidualProductKernel
    (hmeas : Measurable (Function.uncurry density))
    (_hfinite : ∀ x z, density x z ≠ ∞) :
    Kernel (State × State) (State × State) := by
  letI := parameterizedLeftResidualKernel_isSFinite reference density hmeas _hfinite
  exact parameterizedLeftResidualKernel reference density hmeas ×ₖ
    parameterizedRightResidualKernel reference density hmeas

theorem parameterizedResidualProductKernel_isSFinite
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞) :
    IsSFiniteKernel
      (parameterizedResidualProductKernel reference density hmeas hfinite) := by
  unfold parameterizedResidualProductKernel
  letI := parameterizedLeftResidualKernel_isSFinite reference density hmeas hfinite
  letI := parameterizedRightResidualKernel_isSFinite reference density hmeas hfinite
  infer_instance

/-- Residual product normalized by its missing common mass. -/
noncomputable def parameterizedScaledResidualKernel
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞) :
    Kernel (State × State) (State × State) := by
  letI := parameterizedResidualProductKernel_isSFinite reference density hmeas hfinite
  exact (parameterizedResidualProductKernel reference density hmeas hfinite).withDensity
    (fun current _ => (1 - parameterizedOverlap reference density current)⁻¹)

/-- Measurable maximal coupling kernel of a parameterized density family. -/
noncomputable def parameterizedMaximalCouplingKernel
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞) :
    Kernel (State × State) (State × State) :=
  parameterizedCommonKernel reference density hmeas +
    parameterizedScaledResidualKernel reference density hmeas hfinite

theorem parameterizedCommonKernel_apply
    (hmeas : Measurable (Function.uncurry density))
    (current : State × State) :
    parameterizedCommonKernel reference density hmeas current =
      (commonDensityMeasure reference (density current.1)
        (density current.2)).map (fun z => (z, z)) := by
  have hdiag : Measurable (fun z : State => (z, z)) :=
    measurable_id.prodMk measurable_id
  rw [parameterizedCommonKernel, Kernel.map_apply _ hdiag,
    Kernel.withDensity_apply _
      (measurable_uncurry_parameterizedCommonDensity density hmeas),
    Kernel.const_apply]
  rfl

theorem parameterizedLeftResidualKernel_apply
    (hmeas : Measurable (Function.uncurry density))
    (current : State × State) :
    parameterizedLeftResidualKernel reference density hmeas current =
      leftResidualDensityMeasure reference (density current.1)
        (density current.2) := by
  rw [parameterizedLeftResidualKernel, Kernel.withDensity_apply _
    (measurable_uncurry_parameterizedLeftResidualDensity density hmeas),
    Kernel.const_apply]
  rfl

theorem parameterizedRightResidualKernel_apply
    (hmeas : Measurable (Function.uncurry density))
    (current : State × State) :
    parameterizedRightResidualKernel reference density hmeas current =
      rightResidualDensityMeasure reference (density current.1)
        (density current.2) := by
  rw [parameterizedRightResidualKernel, Kernel.withDensity_apply _
    (measurable_uncurry_parameterizedRightResidualDensity density hmeas),
    Kernel.const_apply]
  rfl

theorem parameterizedScaledResidualKernel_apply
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞)
    (current : State × State) :
    parameterizedScaledResidualKernel reference density hmeas hfinite current =
      (1 - parameterizedOverlap reference density current)⁻¹ •
        ((leftResidualDensityMeasure reference (density current.1)
          (density current.2)).prod
    (rightResidualDensityMeasure reference (density current.1)
          (density current.2))) := by
  letI := parameterizedLeftResidualKernel_isSFinite reference density hmeas hfinite
  letI := parameterizedRightResidualKernel_isSFinite reference density hmeas hfinite
  rw [parameterizedScaledResidualKernel, Kernel.withDensity_apply]
  · rw [withDensity_const, parameterizedResidualProductKernel,
      Kernel.prod_apply, parameterizedLeftResidualKernel_apply,
      parameterizedRightResidualKernel_apply]
  · exact (measurable_const.sub
      ((measurable_parameterizedOverlap reference density hmeas).comp
        measurable_fst)).inv

theorem parameterizedMaximalCouplingKernel_apply
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞)
    (hnorm : ∀ x, ∫⁻ z, density x z ∂reference = 1)
    (current : State × State) :
    parameterizedMaximalCouplingKernel reference density hmeas hfinite current =
      maximalDensityCoupling reference (density current.1)
        (density current.2) := by
  rw [parameterizedMaximalCouplingKernel, Kernel.coe_add, Pi.add_apply,
    parameterizedCommonKernel_apply,
    parameterizedScaledResidualKernel_apply reference density hmeas hfinite]
  rw [maximalDensityCoupling]
  split_ifs with hoverlap
  · have hoverlap' : parameterizedOverlap reference density current = 1 := by
      simpa [parameterizedOverlap, parameterizedCommonDensity, densityOverlap]
        using hoverlap
    have hleftZero : leftResidualDensityMeasure reference
        (density current.1) (density current.2) = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [leftResidualDensityMeasure_apply_univ reference
        (Measurable.of_uncurry_left hmeas)
        (Measurable.of_uncurry_left hmeas) (hnorm current.1)]
      change 1 - parameterizedOverlap reference density current = 0
      rw [hoverlap', tsub_self]
    rw [hoverlap', tsub_self, ENNReal.inv_zero, hleftZero,
      Measure.zero_prod, smul_zero, add_zero]
  · rfl

theorem parameterizedMaximalCouplingKernel_isMarkov
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞)
    (hnorm : ∀ x, ∫⁻ z, density x z ∂reference = 1) :
    IsMarkovKernel
      (parameterizedMaximalCouplingKernel reference density hmeas hfinite) := by
  constructor
  intro current
  rw [parameterizedMaximalCouplingKernel_apply reference density hmeas hfinite hnorm]
  exact maximalDensityCoupling_isProbability reference
    (Measurable.of_uncurry_left hmeas) (Measurable.of_uncurry_left hmeas)
    (hnorm current.1) (hnorm current.2)

theorem parameterizedMaximalCouplingKernel_isCoupling
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞)
    (hnorm : ∀ x, ∫⁻ z, density x z ∂reference = 1) :
    IsCoupling
      (parameterizedMaximalCouplingKernel reference density hmeas hfinite)
      (densityProposal reference density) (densityProposal reference density) := by
  constructor
  · ext current s hs
    rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply,
      parameterizedMaximalCouplingKernel_apply reference density hmeas hfinite hnorm]
    have hrow := maximalDensityCoupling_fst reference
      (Measurable.of_uncurry_left hmeas) (Measurable.of_uncurry_left hmeas)
      (hnorm current.1) (hnorm current.2)
    calc
      maximalDensityCoupling reference (density current.1)
          (density current.2) (Prod.fst ⁻¹' s) =
          (maximalDensityCoupling reference (density current.1)
            (density current.2)).fst s := (Measure.fst_apply hs).symm
      _ = reference.withDensity (density current.1) s :=
        congrArg (fun μ : Measure State => μ s) hrow
      _ = (densityProposal reference density current.1) s := by
        rw [densityProposal, Kernel.withDensity_apply _ hmeas,
          Kernel.const_apply]
  · ext current s hs
    rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply,
      parameterizedMaximalCouplingKernel_apply reference density hmeas hfinite hnorm]
    have hrow := maximalDensityCoupling_snd reference
      (Measurable.of_uncurry_left hmeas) (Measurable.of_uncurry_left hmeas)
      (hnorm current.1) (hnorm current.2)
    calc
      maximalDensityCoupling reference (density current.1)
          (density current.2) (Prod.snd ⁻¹' s) =
          (maximalDensityCoupling reference (density current.1)
            (density current.2)).snd s := (Measure.snd_apply hs).symm
      _ = reference.withDensity (density current.2) s :=
        congrArg (fun μ : Measure State => μ s) hrow
      _ = (densityProposal reference density current.2) s := by
        rw [densityProposal, Kernel.withDensity_apply _ hmeas,
          Kernel.const_apply]

theorem parameterizedMaximalCouplingKernel_diagonal_pos [MeasurableEq State]
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞)
    (hnorm : ∀ x, ∫⁻ z, density x z ∂reference = 1)
    (hreference : 0 < reference Set.univ)
    (hpos : ∀ x z, 0 < density x z) (current : State × State) :
    0 < parameterizedMaximalCouplingKernel reference density hmeas hfinite current
      (Set.diagonal State) := by
  rw [parameterizedMaximalCouplingKernel_apply reference density hmeas hfinite hnorm]
  apply maximalDensityCoupling_diagonal_pos reference
  apply densityOverlap_pos reference
  · exact Measurable.of_uncurry_left hmeas
  · exact Measurable.of_uncurry_left hmeas
  · exact hreference
  · exact hpos current.1
  · exact hpos current.2

/-- A common density floor on one measurable output region quantitatively
lower-bounds the diagonal mass of the parameterized maximal coupling. -/
theorem densityFloor_mul_measure_le_parameterizedMaximalCouplingKernel_diagonal
    [MeasurableEq State]
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞)
    (hnorm : ∀ x, ∫⁻ z, density x z ∂reference = 1)
    (current : State × State) {A : Set State} (hA : MeasurableSet A)
    (floor : ENNReal)
    (hleft : ∀ z ∈ A, floor ≤ density current.1 z)
    (hright : ∀ z ∈ A, floor ≤ density current.2 z) :
    floor * reference A ≤
      parameterizedMaximalCouplingKernel reference density hmeas hfinite
        current (Set.diagonal State) := by
  rw [parameterizedMaximalCouplingKernel_apply reference density hmeas
    hfinite hnorm]
  exact (densityFloor_mul_measure_le_densityOverlap reference hA floor
    hleft hright).trans
      (densityOverlap_le_maximalDensityCoupling_diagonal reference _ _)

/-- Localized form: the common density floor on `A` lower-bounds the maximal
coupling's mass on the portion of the diagonal over `A`. -/
theorem densityFloor_mul_measure_le_parameterizedMaximalCouplingKernel_diagonalOver
    [MeasurableEq State]
    (hmeas : Measurable (Function.uncurry density))
    (hfinite : ∀ x z, density x z ≠ ∞)
    (hnorm : ∀ x, ∫⁻ z, density x z ∂reference = 1)
    (current : State × State) {A : Set State} (hA : MeasurableSet A)
    (floor : ENNReal)
    (hleft : ∀ z ∈ A, floor ≤ density current.1 z)
    (hright : ∀ z ∈ A, floor ≤ density current.2 z) :
    floor * reference A ≤
      parameterizedMaximalCouplingKernel reference density hmeas hfinite
        current (diagonalOver A) := by
  rw [parameterizedMaximalCouplingKernel_apply reference density hmeas
    hfinite hnorm]
  exact densityFloor_mul_measure_le_maximalDensityCoupling_diagonalOver
    reference hA floor hleft hright

end

end McmcLean.Kernel
