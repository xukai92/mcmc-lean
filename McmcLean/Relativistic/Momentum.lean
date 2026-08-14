import McmcLean.Relativistic.Kinetic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Radial law for relativistic momentum

For a radially symmetric density on a `d`-dimensional Euclidean space, polar
change of variables contributes the Jacobian `r^(d - 1)`.  This module records
the resulting unnormalized radial weight for relativistic momentum.

Xu and Ge derive the factor `r` in two dimensions in their Equation (10), then
reuse it in the printed arbitrary-dimensional Algorithm 1.  We prove that the
printed factor agrees with the dimension-dependent law in dimension two and
give a concrete dimension-three point where it does not agree.

The subsequent measure layer will combine this weight with mathlib's
`Measure.toSphere` and `Measure.volumeIoiPow` polar decomposition.
-/

namespace McmcLean.Relativistic

open MeasureTheory Metric Set
open McmcLean.Hamiltonian
open scoped ENNReal

/-- Radial form of the relativistic kinetic energy. -/
noncomputable def radialRelativisticKineticEnergy
    (m c r : ℝ) : ℝ :=
  m * c ^ 2 * Real.sqrt (r ^ 2 / (m ^ 2 * c ^ 2) + 1)

/-- Unnormalized radial density in dimension `d`, including the polar Jacobian
`r^(d - 1)`. -/
noncomputable def relativisticRadialWeight
    (d : ℕ) (m c r : ℝ) : ℝ :=
  Real.exp (-radialRelativisticKineticEnergy m c r) * r ^ (d - 1)

/-- The radial weight printed in Equation (10), derived there for dimension
two. -/
noncomputable def printedRelativisticRadialWeight
    (m c r : ℝ) : ℝ :=
  Real.exp (-radialRelativisticKineticEnergy m c r) * r

/-- The paper's printed radial factor is the correct polar Jacobian in two
dimensions. -/
theorem relativisticRadialWeight_two
    (m c r : ℝ) :
    relativisticRadialWeight 2 m c r =
      printedRelativisticRadialWeight m c r := by
  simp [relativisticRadialWeight, printedRelativisticRadialWeight]

/-- At radius two in dimension three, the correct radial weight differs from
the two-dimensional weight reused by the printed Algorithm 1. -/
theorem relativisticRadialWeight_three_at_two_ne_printed
    (m c : ℝ) :
    relativisticRadialWeight 3 m c 2 ≠
      printedRelativisticRadialWeight m c 2 := by
  simp only [relativisticRadialWeight, printedRelativisticRadialWeight,
    Nat.reduceSubDiff, pow_two]
  have hexp : 0 < Real.exp (-radialRelativisticKineticEnergy m c 2) :=
    Real.exp_pos _
  nlinarith

/-- The relativistic radial weight is nonnegative at nonnegative radii. -/
theorem relativisticRadialWeight_nonneg
    (d : ℕ) (m c r : ℝ) (hr : 0 ≤ r) :
    0 ≤ relativisticRadialWeight d m c r := by
  exact mul_nonneg (Real.exp_pos _).le (pow_nonneg hr _)

theorem continuous_relativisticRadialWeight
    (d : ℕ) (m c : ℝ) :
    Continuous (relativisticRadialWeight d m c) := by
  unfold relativisticRadialWeight radialRelativisticKineticEnergy
  fun_prop

/-- Relativistic radial energy grows at least linearly, with slope `c`, on
positive radii. -/
theorem c_mul_lt_radialRelativisticKineticEnergy
    (m c r : ℝ) (hm : 0 < m) (hc : 0 < c) (hr : 0 ≤ r) :
    c * r < radialRelativisticKineticEnergy m c r := by
  let p : Momentum Unit := fun _ => r
  have hmass := euclideanNorm_div_lt_relativisticMass m c p hm hc
  have hsq : squaredEuclideanNorm p = r ^ 2 := by
    simp [p, squaredEuclideanNorm, euclideanInner]
    ring
  have hnorm : euclideanNorm p = r := by
    rw [euclideanNorm, hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
  rw [hnorm] at hmass
  have hmul := mul_lt_mul_of_pos_left hmass (sq_pos_of_pos hc)
  have hc0 : c ≠ 0 := ne_of_gt hc
  have henergy :
      c ^ 2 * relativisticMass m c p =
        radialRelativisticKineticEnergy m c r := by
    simp [relativisticMass, radialRelativisticKineticEnergy, hsq]
    ring
  calc
    c * r = c ^ 2 * (r / c) := by field_simp [hc.ne']
    _ < c ^ 2 * relativisticMass m c p := hmul
    _ = radialRelativisticKineticEnergy m c r := henergy

/-- The corrected dimension-dependent radial density is integrable on the
positive ray for positive physical parameters. -/
theorem integrableOn_relativisticRadialWeight
    (d : ℕ) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    IntegrableOn (relativisticRadialWeight d m c) (Ioi 0) := by
  let n := d - 1
  have hcomparison : IntegrableOn
      (fun r : ℝ => r ^ n * Real.exp (-c * r)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (n : ℝ)) (p := (1 : ℝ)) (b := c)
      (by exact_mod_cast (show (-1 : ℤ) < n from by omega))
      (by norm_num) hc
    simpa [Real.rpow_natCast, Real.rpow_one] using h
  apply hcomparison.mono'
  · exact (continuous_relativisticRadialWeight d m c).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 ≤ r := hr.le
    rw [Real.norm_eq_abs,
      abs_of_nonneg (relativisticRadialWeight_nonneg d m c r hr0)]
    unfold relativisticRadialWeight
    rw [show d - 1 = n by rfl]
    have henergy := c_mul_lt_radialRelativisticKineticEnergy m c r hm hc hr0
    have hexp :
        Real.exp (-radialRelativisticKineticEnergy m c r) ≤
          Real.exp (-c * r) := by
      apply Real.exp_le_exp.mpr
      linarith
    nlinarith [pow_nonneg hr0 n]

/-- Boltzmann factor associated with the radial relativistic kinetic energy. -/
noncomputable def relativisticBoltzmannWeight
    (m c r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-radialRelativisticKineticEnergy m c r))

/-- Evaluating the radial energy at the project's Euclidean norm recovers the
special-relativistic kinetic energy exactly. -/
theorem radialRelativisticKineticEnergy_euclideanNorm
    {ι : Type*} [Fintype ι] (m c : ℝ) (p : Momentum ι) :
    radialRelativisticKineticEnergy m c (euclideanNorm p) =
      relativisticKineticEnergy m c p := by
  unfold radialRelativisticKineticEnergy relativisticKineticEnergy
  rw [euclideanNorm_sq]

theorem relativisticBoltzmannWeight_pos (m c r : ℝ) :
    0 < relativisticBoltzmannWeight m c r := by
  rw [relativisticBoltzmannWeight, ENNReal.ofReal_pos]
  exact Real.exp_pos _

theorem continuous_relativisticBoltzmannWeight (m c : ℝ) :
    Continuous (relativisticBoltzmannWeight m c) := by
  unfold relativisticBoltzmannWeight radialRelativisticKineticEnergy
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

/-- The corrected radial base measure.  Mathlib's `volumeIoiPow (d - 1)`
already contains the polar Jacobian `r^(d-1)`; the additional density is only
the relativistic Boltzmann factor. -/
noncomputable def relativisticRadiusMeasure
    (d : ℕ) (m c : ℝ) : Measure (Ioi (0 : ℝ)) :=
  (Measure.volumeIoiPow (d - 1)).withDensity
    (fun r => relativisticBoltzmannWeight m c r.1)

/-- Expanded density of the corrected radius law with respect to Lebesgue
measure on the positive ray.  This theorem makes the `r^(d-1)` Jacobian
explicit. -/
theorem relativisticRadiusMeasure_eq_withDensity
    (d : ℕ) (m c : ℝ) :
    relativisticRadiusMeasure d m c =
      (Measure.comap Subtype.val volume).withDensity
        (fun r : Ioi (0 : ℝ) =>
          ENNReal.ofReal (r.1 ^ (d - 1)) *
            relativisticBoltzmannWeight m c r.1) := by
  rw [relativisticRadiusMeasure, Measure.volumeIoiPow]
  symm
  apply withDensity_mul
  · exact ENNReal.continuous_ofReal.measurable.comp (by fun_prop)
  · exact (continuous_relativisticBoltzmannWeight m c).measurable.comp
      continuous_subtype_val.measurable

/-- Reconstruct a nonzero vector from a unit direction and positive radius. -/
def polarSynthesis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    sphere (0 : E) 1 × Ioi (0 : ℝ) → E :=
  fun ur => ur.2.1 • ur.1.1

theorem continuous_polarSynthesis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (polarSynthesis : sphere (0 : E) 1 × Ioi (0 : ℝ) → E) := by
  unfold polarSynthesis
  fun_prop

theorem norm_polarSynthesis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ur : sphere (0 : E) 1 × Ioi (0 : ℝ)) :
    ‖polarSynthesis ur‖ = ur.2.1 := by
  rw [polarSynthesis, norm_smul, Real.norm_eq_abs, abs_of_pos ur.2.2]
  have hu : ‖ur.1.1‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using ur.1.2
  rw [hu, mul_one]

/-- Transporting a pulled-back density through a measurable map is the same as
transporting the base measure and then applying the target-side density. -/
theorem map_withDensity_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (μ : Measure α) (g : β → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f =
      (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs,
    withDensity_apply _ (hs.preimage hf),
    withDensity_apply _ hs,
    Measure.restrict_map hf hs,
    lintegral_map hg hf]
  rfl

/-- Unnormalized corrected polar sampler measure.  Its direction is the Haar
surface measure induced by ambient volume, and its radius uses the
dimension-dependent polar measure. -/
noncomputable def relativisticPolarMomentumMeasure
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (m c : ℝ) : Measure E :=
  ((volume.toSphere).prod
    (relativisticRadiusMeasure (Module.finrank ℝ E) m c)).map polarSynthesis

/-- Unnormalized Cartesian relativistic momentum measure.  This is the target
against which the corrected polar sampler will be proved correct. -/
noncomputable def relativisticCartesianMomentumMeasure
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (m c : ℝ) : Measure E :=
  volume.withDensity
    (fun p => relativisticBoltzmannWeight m c ‖p‖)

/-- The real-valued Cartesian Boltzmann factor is integrable against any
finite-dimensional additive Haar volume when `m,c>0`. -/
theorem integrable_relativisticCartesianBoltzmann
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] [Nontrivial E]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Integrable
      (fun p : E => Real.exp
        (-radialRelativisticKineticEnergy m c ‖p‖)) volume := by
  apply (integrable_fun_norm_addHaar (volume : Measure E)
    (f := fun r : ℝ =>
      Real.exp (-radialRelativisticKineticEnergy m c r))).2
  convert integrableOn_relativisticRadialWeight
      (Module.finrank ℝ E) m c hm hc using 1
  funext r
  rw [smul_eq_mul, relativisticRadialWeight, mul_comm]

/-- The unnormalized Cartesian relativistic momentum measure has finite total
mass for positive physical parameters. -/
theorem isFiniteMeasure_relativisticCartesianMomentumMeasure
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] [Nontrivial E]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    IsFiniteMeasure (relativisticCartesianMomentumMeasure E m c) := by
  unfold relativisticCartesianMomentumMeasure relativisticBoltzmannWeight
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    (integrable_relativisticCartesianBoltzmann E m c hm hc).aestronglyMeasurable
    (ae_of_all _ fun p => (Real.exp_pos _).le)).2
  exact integrable_relativisticCartesianBoltzmann E m c hm hc

/-- The unnormalized Cartesian relativistic momentum measure is nonzero. -/
theorem relativisticCartesianMomentumMeasure_ne_zero
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] [Nontrivial E]
    (m c : ℝ) :
    relativisticCartesianMomentumMeasure E m c ≠ 0 := by
  unfold relativisticCartesianMomentumMeasure
  intro hzero
  have hzero := (withDensity_eq_zero_iff
    ((continuous_relativisticBoltzmannWeight m c).measurable.comp
      continuous_norm.measurable).aemeasurable).mp hzero
  haveI : (ae (volume : Measure E)).NeBot := inferInstance
  obtain ⟨p, hp⟩ := hzero.exists
  exact (relativisticBoltzmannWeight_pos m c ‖p‖).ne' hp

/-- Normalized isotropic relativistic momentum probability measure. -/
noncomputable def relativisticMomentumProbability
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] [Nontrivial E]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) : ProbabilityMeasure E := by
  letI : IsFiniteMeasure (relativisticCartesianMomentumMeasure E m c) :=
    isFiniteMeasure_relativisticCartesianMomentumMeasure E m c hm hc
  let μ : FiniteMeasure E :=
    ⟨relativisticCartesianMomentumMeasure E m c, inferInstance⟩
  exact μ.normalize

/-- The normalized probability is the inverse-total-mass scaling of the
unnormalized Cartesian momentum measure. -/
theorem relativisticMomentumProbability_toMeasure
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] [Nontrivial E]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    ((relativisticMomentumProbability E m c hm hc : ProbabilityMeasure E) :
        Measure E) =
      (FiniteMeasure.mass
        (⟨relativisticCartesianMomentumMeasure E m c,
          isFiniteMeasure_relativisticCartesianMomentumMeasure E m c hm hc⟩ :
          FiniteMeasure E))⁻¹ •
        relativisticCartesianMomentumMeasure E m c := by
  letI : IsFiniteMeasure (relativisticCartesianMomentumMeasure E m c) :=
    isFiniteMeasure_relativisticCartesianMomentumMeasure E m c hm hc
  let μ : FiniteMeasure E :=
    ⟨relativisticCartesianMomentumMeasure E m c, inferInstance⟩
  change (μ.normalize : Measure E) = μ.mass⁻¹ • (μ : Measure E)
  exact μ.toMeasure_normalize_eq_of_nonzero
    (by
      intro h
      exact relativisticCartesianMomentumMeasure_ne_zero E m c
        (congrArg ((↑) : FiniteMeasure E → Measure E) h))

/-- On the polar product space, the corrected sampler is precisely the Haar
sphere/radial base measure tilted by the relativistic Boltzmann factor. -/
theorem relativisticPolarPairMeasure_eq_withDensity
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (m c : ℝ) :
    (volume : Measure E).toSphere.prod
        (relativisticRadiusMeasure (Module.finrank ℝ E) m c) =
      ((volume : Measure E).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))).withDensity
        (fun ur => relativisticBoltzmannWeight m c ur.2.1) := by
  rw [relativisticRadiusMeasure]
  apply prod_withDensity_right
  exact (continuous_relativisticBoltzmannWeight m c).measurable.comp
    continuous_subtype_val.measurable

set_option maxHeartbeats 800000 in
/-- Correctness target for the polar sampler: under an additive Haar ambient
volume, polar synthesis produces exactly the Cartesian relativistic momentum
measure. -/
theorem relativisticPolarMomentumMeasure_eq_cartesian
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] [Nontrivial E]
    (m c : ℝ) :
    relativisticPolarMomentumMeasure E m c =
      relativisticCartesianMomentumMeasure E m c := by
  let e := (homeomorphUnitSphereProd E).toMeasurableEquiv
  let source : Measure ({0}ᶜ : Set E) := Measure.comap Subtype.val volume
  let target : Measure (sphere (0 : E) 1 × Ioi (0 : ℝ)) :=
    (volume : Measure E).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ E - 1))
  let g : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ :=
    fun ur => relativisticBoltzmannWeight m c ur.2.1
  have hg : Measurable g :=
    (continuous_relativisticBoltzmannWeight m c).measurable.comp
      (continuous_subtype_val.comp continuous_snd).measurable
  have he : Measure.map e source = target := by
    exact volume.measurePreserving_homeomorphUnitSphereProd.map_eq
  have hweighted :
      (source.withDensity (g ∘ e)).map e = target.withDensity g := by
    rw [map_withDensity_comp e source g e.measurable hg, he]
  rw [relativisticPolarMomentumMeasure,
    relativisticPolarPairMeasure_eq_withDensity E m c]
  change Measure.map polarSynthesis (target.withDensity g) = _
  rw [← hweighted, Measure.map_map
    (continuous_polarSynthesis (E := E)).measurable e.measurable]
  have hsynth : polarSynthesis ∘ e =
      ((↑) : ({0}ᶜ : Set E) → E) := by
    funext x
    have hx : ‖(x : E)‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact x.2
    change polarSynthesis ((homeomorphUnitSphereProd E) x) = (x : E)
    simp [polarSynthesis, hx]
  rw [hsynth]
  let cartesianDensity : E → ℝ≥0∞ :=
    fun p => relativisticBoltzmannWeight m c ‖p‖
  have hcart : Measurable cartesianDensity :=
    (continuous_relativisticBoltzmannWeight m c).measurable.comp
      continuous_norm.measurable
  have hpull : g ∘ e = cartesianDensity ∘
      ((↑) : ({0}ᶜ : Set E) → E) := by
    funext x
    simp [g, e, cartesianDensity]
  rw [hpull, map_withDensity_comp _ source cartesianDensity
    measurable_subtype_coe hcart]
  rw [show Measure.map ((↑) : ({0}ᶜ : Set E) → E) source =
      volume.restrict ({0}ᶜ : Set E) by
    exact map_comap_subtype_coe (measurableSet_singleton 0).compl volume]
  have hrestrict : volume.restrict ({0}ᶜ : Set E) = volume := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    simp
  rw [hrestrict]
  rfl

/-! ## Euclidean momentum coordinates

`Momentum ι = ι → ℝ` carries mathlib's product/sup norm, whereas the HMC
Hamiltonian uses `euclideanNorm`.  Consequently the generic ambient-norm
radial measure above must be constructed first on `EuclideanSpace ℝ ι` and
then transported to `Momentum ι`.  Using the ambient norm of `Momentum ι`
directly would give the wrong law in dimension greater than one. -/

/-- The canonical coordinate map from Euclidean `L²` space to the project's
function-valued momentum representation. -/
noncomputable def euclideanMomentumEquiv (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ ι ≃L[ℝ] Momentum ι :=
  EuclideanSpace.equiv ι ℝ

theorem euclideanNorm_euclideanMomentumEquiv
    {ι : Type*} [Fintype ι] (p : EuclideanSpace ℝ ι) :
    euclideanNorm (euclideanMomentumEquiv ι p) = ‖p‖ := by
  rw [euclideanNorm, EuclideanSpace.norm_eq]
  congr 1
  simp [squaredEuclideanNorm, euclideanInner, euclideanMomentumEquiv,
    pow_two]

/-- Correct unnormalized isotropic relativistic law in the momentum
coordinates used by the Hamiltonian. -/
noncomputable def euclideanRelativisticMomentumMeasure
    (ι : Type*) [Fintype ι] (m c : ℝ) : Measure (Momentum ι) :=
  volume.withDensity
    (fun p => relativisticBoltzmannWeight m c (euclideanNorm p))

/-- Transporting the ambient radial law from Euclidean `L²` coordinates gives
exactly the Hamiltonian's Euclidean momentum density. -/
theorem map_euclideanRelativisticMomentumMeasure
    (ι : Type*) [Fintype ι] (m c : ℝ) :
    (relativisticCartesianMomentumMeasure (EuclideanSpace ℝ ι) m c).map
        (euclideanMomentumEquiv ι) =
      euclideanRelativisticMomentumMeasure ι m c := by
  let f : EuclideanSpace ℝ ι → Momentum ι := euclideanMomentumEquiv ι
  let g : Momentum ι → ℝ≥0∞ :=
    fun p => relativisticBoltzmannWeight m c (euclideanNorm p)
  have hf : Measurable f := (euclideanMomentumEquiv ι).continuous.measurable
  have hg : Measurable g :=
    (continuous_relativisticBoltzmannWeight m c).measurable.comp
      continuous_euclideanNorm.measurable
  have hdensity :
      (fun p : EuclideanSpace ℝ ι =>
        relativisticBoltzmannWeight m c ‖p‖) = g ∘ f := by
    funext p
    change relativisticBoltzmannWeight m c ‖p‖ =
      relativisticBoltzmannWeight m c
        (euclideanNorm (euclideanMomentumEquiv ι p))
    rw [euclideanNorm_euclideanMomentumEquiv]
  unfold relativisticCartesianMomentumMeasure
  rw [hdensity, map_withDensity_comp f volume g hf hg]
  have hvolume : Measure.map f volume =
      (volume : Measure (Momentum ι)) := by
    exact (PiLp.volume_preserving_ofLp ι).map_eq
  rw [hvolume]
  rfl

/-- Corrected polar sampler in the project's momentum coordinates. -/
noncomputable def euclideanRelativisticPolarMomentumMeasure
    (ι : Type*) [Fintype ι] (m c : ℝ) : Measure (Momentum ι) :=
  (relativisticPolarMomentumMeasure (EuclideanSpace ℝ ι) m c).map
    (euclideanMomentumEquiv ι)

theorem euclideanRelativisticPolarMomentumMeasure_eq
    (ι : Type*) [Fintype ι] [Nonempty ι] (m c : ℝ) :
    euclideanRelativisticPolarMomentumMeasure ι m c =
      euclideanRelativisticMomentumMeasure ι m c := by
  rw [euclideanRelativisticPolarMomentumMeasure,
    relativisticPolarMomentumMeasure_eq_cartesian,
    map_euclideanRelativisticMomentumMeasure]

/-- Normalized Euclidean relativistic momentum probability, transported from
the corresponding normalized law on `EuclideanSpace`. -/
noncomputable def euclideanRelativisticMomentumProbability
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    ProbabilityMeasure (Momentum ι) :=
  (relativisticMomentumProbability (EuclideanSpace ℝ ι) m c hm hc).map
    (euclideanMomentumEquiv ι).continuous.measurable.aemeasurable

/-- Total mass (momentum partition function) of the corrected Euclidean
relativistic law. -/
noncomputable def euclideanRelativisticMomentumPartition
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) : NNReal :=
  FiniteMeasure.mass
    (⟨relativisticCartesianMomentumMeasure (EuclideanSpace ℝ ι) m c,
      isFiniteMeasure_relativisticCartesianMomentumMeasure
        (EuclideanSpace ℝ ι) m c hm hc⟩ :
      FiniteMeasure (EuclideanSpace ℝ ι))

theorem euclideanRelativisticMomentumPartition_ne_zero
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    euclideanRelativisticMomentumPartition ι m c hm hc ≠ 0 := by
  rw [euclideanRelativisticMomentumPartition,
    FiniteMeasure.mass_nonzero_iff]
  intro h
  exact (relativisticCartesianMomentumMeasure_ne_zero
    (EuclideanSpace ℝ ι) m c)
      (congrArg ((↑) : FiniteMeasure (EuclideanSpace ℝ ι) →
        Measure (EuclideanSpace ℝ ι)) h)

/-- The normalized corrected law is inverse-partition scaling of its
unnormalized Euclidean density. -/
theorem euclideanRelativisticMomentumProbability_toMeasure
    (ι : Type*) [Fintype ι] [Nonempty ι]
    (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    (euclideanRelativisticMomentumProbability ι m c hm hc :
      Measure (Momentum ι)) =
      ((euclideanRelativisticMomentumPartition ι m c hm hc)⁻¹ : NNReal) •
        euclideanRelativisticMomentumMeasure ι m c := by
  have hmap := map_euclideanRelativisticMomentumMeasure ι m c
  rw [euclideanRelativisticMomentumProbability,
    ProbabilityMeasure.toMeasure_map,
    relativisticMomentumProbability_toMeasure,
    Measure.map_smul, hmap]
  rfl

/-- The Cartesian relativistic density is symmetric under momentum flip. -/
theorem relativisticCartesianDensity_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m c : ℝ) (p : E) :
    relativisticBoltzmannWeight m c ‖-p‖ =
      relativisticBoltzmannWeight m c ‖p‖ := by
  rw [norm_neg]

end McmcLean.Relativistic
