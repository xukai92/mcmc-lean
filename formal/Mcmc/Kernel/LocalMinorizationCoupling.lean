import Mcmc.Kernel.GeneralConvergence
import Mcmc.Kernel.ParameterMixture

/-!
# Couplings from local minorization

This module converts a minorization available only on a measurable state set
into global kernel infrastructure.  The first step replaces rows outside the
set by the minorizing probability law, turning the local certificate into an
ordinary Doeblin certificate without changing any row inside the set.
-/

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.Kernel

/-- Convergence along every residue class modulo a positive skeleton length
implies convergence of the unthinned sequence. -/
theorem tendsto_of_tendsto_skeleton_residues
    {X : Type*} [TopologicalSpace X] {f : ℕ → X} {x : X}
    (steps : ℕ) (hsteps : 0 < steps)
    (hresidue : ∀ r : Fin steps,
      Filter.Tendsto (fun n => f (steps * n + r.1))
        Filter.atTop (nhds x)) :
    Filter.Tendsto f Filter.atTop (nhds x) := by
  rw [Filter.tendsto_def]
  intro s hs
  have hall : ∀ᶠ n in Filter.atTop, ∀ r : Fin steps,
      f (steps * n + r.1) ∈ s := by
    rw [Filter.eventually_all]
    intro r
    exact (hresidue r).eventually hs
  have hdiv : Filter.Tendsto (fun n : ℕ => n / steps)
      Filter.atTop Filter.atTop := by
    show Filter.map (fun n : ℕ => n / steps) Filter.atTop ≤ Filter.atTop
    rw [Filter.map_div_atTop_eq_nat steps hsteps]
  filter_upwards [hdiv.eventually hall] with n hn
  have hmod : n % steps < steps := Nat.mod_lt n hsteps
  have := hn ⟨n % steps, hmod⟩
  have hdecompose : steps * (n / steps) + n % steps = n :=
    Nat.div_add_mod n steps
  simpa [hdecompose] using this

open ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- Postcomposition by a nonnegative kernel is monotone in its input measure.
This elementary fact is useful when propagating a local submeasure through
the remaining stages of a sampler. -/
theorem measure_comp_mono {source target : Type*}
    [MeasurableSpace source] [MeasurableSpace target]
    (transition : Kernel source target)
    {first second : Measure source} [SFinite first] [SFinite second]
    (hmeasure : first ≤ second) :
    transition ∘ₘ first ≤ transition ∘ₘ second := by
  apply Measure.le_iff.mpr
  intro event hevent
  rw [Measure.bind_apply hevent transition.aemeasurable,
    Measure.bind_apply hevent transition.aemeasurable]
  exact lintegral_mono' hmeasure le_rfl

/-- A transition locally minorizes `reference` on `D`. -/
def LocallyMinorizes (transition : Kernel α α) (D : Set α)
    (ε : ENNReal) (reference : Measure α) : Prop :=
  ∀ x ∈ D, ∀ s, MeasurableSet s → ε * reference s ≤ transition x s

/-- A pointwise minorization on a measurable parameter region survives
independent parameter averaging. Its coefficient is multiplied by the mass
of that region. This is the generic bridge from a uniform fixed-schedule
bound to a continuously randomized schedule kernel. -/
theorem independentParameterMixture_locallyMinorizes_on
    {Parameter : Type*} [MeasurableSpace Parameter]
    (family : Kernel (α × Parameter) α)
    (parameterLaw : Measure Parameter) [SFinite parameterLaw]
    (D : Set α) (A : Set Parameter) (hA : MeasurableSet A)
    (floor : ENNReal) (reference : Measure α)
    (hminor : ∀ x ∈ D, ∀ parameter ∈ A, ∀ event,
      MeasurableSet event →
        floor * reference event ≤ family (x, parameter) event) :
    LocallyMinorizes
      (independentParameterMixture family parameterLaw) D
      (parameterLaw A * floor) reference := by
  intro x hx event hevent
  unfold independentParameterMixture
  rw [Kernel.comp_apply]
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.bind_apply hevent family.aemeasurable]
  rw [MeasureTheory.lintegral_map
    (Kernel.measurable_coe family hevent)
    (by fun_prop : Measurable (Prod.mk x))]
  calc
    (parameterLaw A * floor) * reference event =
        ∫⁻ _parameter in A, floor * reference event ∂parameterLaw := by
      rw [setLIntegral_const]
      ring
    _ ≤ ∫⁻ parameter in A, family (x, parameter) event ∂parameterLaw := by
      apply setLIntegral_mono' hA
      intro parameter hparameter
      exact hminor x hx parameter hparameter event hevent
    _ ≤ ∫⁻ parameter, family (x, parameter) event ∂parameterLaw := by
      exact lintegral_mono' (Measure.restrict_le_self) le_rfl

/-- A pointwise lower bound on a transition density over `D × C` gives a
local minorization by the reference measure restricted to `C`. -/
theorem locallyMinorizes_restrict_of_density_lower_bound
    (transition : Kernel α α) (reference : Measure α)
    (density : α → α → ENNReal)
    (D C : Set α) (hC : MeasurableSet C) (floor : ENNReal)
    (happly : ∀ x event, MeasurableSet event →
      transition x event = ∫⁻ y in event, density x y ∂reference)
    (hlower : ∀ x ∈ D, ∀ y ∈ C, floor ≤ density x y) :
    LocallyMinorizes transition D floor (reference.restrict C) := by
  intro x hx event hevent
  rw [Measure.restrict_apply hevent, happly x event hevent]
  calc
    floor * reference (event ∩ C) =
        ∫⁻ _y in event ∩ C, floor ∂reference := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ y in event ∩ C, density x y ∂reference := by
      apply setLIntegral_mono' (hevent.inter hC)
      intro y hy
      exact hlower x hx y hy.2
    _ ≤ ∫⁻ y in event, density x y ∂reference := by
      apply lintegral_mono'
      · exact Measure.restrict_mono Set.inter_subset_left le_rfl
      · exact le_rfl

/-- A jointly continuous density that is positive on a nonempty compact
rectangle supplies a strictly positive local-minorization coefficient. -/
theorem exists_pos_locallyMinorizes_restrict_of_continuous_density
    [TopologicalSpace α]
    (transition : Kernel α α) (reference : Measure α)
    (density : α → α → ENNReal)
    (D C : Set α) (hDcompact : IsCompact D) (hCcompact : IsCompact C)
    (hDnonempty : D.Nonempty) (hCnonempty : C.Nonempty)
    (hC : MeasurableSet C)
    (hdensity : Continuous (fun pair : α × α => density pair.1 pair.2))
    (hpositive : ∀ x ∈ D, ∀ y ∈ C, 0 < density x y)
    (happly : ∀ x event, MeasurableSet event →
      transition x event = ∫⁻ y in event, density x y ∂reference) :
    ∃ floor : ENNReal, 0 < floor ∧
      LocallyMinorizes transition D floor (reference.restrict C) := by
  have hcompact : IsCompact (D ×ˢ C) := hDcompact.prod hCcompact
  have hnonempty : (D ×ˢ C).Nonempty := hDnonempty.prod hCnonempty
  obtain ⟨floor, hfloor, hlower⟩ := exists_pos_le_on_compact
    hcompact hnonempty hdensity (by
      intro pair hpair
      exact hpositive pair.1 hpair.1 pair.2 hpair.2)
  refine ⟨floor, hfloor, ?_⟩
  apply locallyMinorizes_restrict_of_density_lower_bound
    transition reference density D C hC floor
  · exact happly
  · intro x hx y hy
    exact hlower (x, y) ⟨hx, hy⟩

/-- Uniform finite-step accessibility between two regions for an arbitrary
single-state kernel. -/
def SingleChainAccessibleFrom (transition : Kernel α α)
    (start target : Set α) (steps : ℕ) (bound : ENNReal) : Prop :=
  ∀ x ∈ start, bound ≤ (transition ^ steps) x target

/-- One-step accessibility is just a row-wise event lower bound. -/
theorem isUniformlyAccessibleFrom_one
    (transition : Kernel α α) {start target : Set α}
    {bound : ENNReal}
    (h : ∀ x ∈ start, bound ≤ transition x target) :
    SingleChainAccessibleFrom transition start target 1 bound := by
  intro x hx
  simpa only [pow_one] using h x hx

/-- Single-chain accessibility composes by Chapman--Kolmogorov. -/
theorem SingleChainAccessibleFrom.comp
    (transition : Kernel α α)
    {start middle target : Set α}
    (hmiddle : MeasurableSet middle) (htarget : MeasurableSet target)
    {firstSteps secondSteps : ℕ} {firstBound secondBound : ENNReal}
    (hfirst : SingleChainAccessibleFrom transition start middle
      firstSteps firstBound)
    (hsecond : SingleChainAccessibleFrom transition middle target
      secondSteps secondBound) :
    SingleChainAccessibleFrom transition start target
      (firstSteps + secondSteps) (secondBound * firstBound) := by
  intro x hx
  rw [Kernel.pow_add_apply_eq_lintegral transition firstSteps secondSteps x
    htarget]
  calc
    secondBound * firstBound ≤
        secondBound * (transition ^ firstSteps) x middle := by
      simpa only [mul_comm] using
        (mul_le_mul_right (hfirst x hx) secondBound)
    _ = ∫⁻ _y in middle, secondBound
          ∂((transition ^ firstSteps) x) := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ y in middle, (transition ^ secondSteps) y target
          ∂((transition ^ firstSteps) x) := by
      exact setLIntegral_mono' hmiddle fun y hy => hsecond y hy
    _ ≤ ∫⁻ y, (transition ^ secondSteps) y target
          ∂((transition ^ firstSteps) x) :=
      setLIntegral_le_lintegral middle _

/-- Iterating a uniform one-step bound along a measurable sequence of
corridor sets yields the corresponding power bound. The sets may depend on
the initial state; only the per-step constant is shared. -/
theorem bound_pow_le_apply_of_measurable_corridor
    (transition : Kernel α α) [IsMarkovKernel transition]
    (sets : ℕ → Set α) (hmeasurable : ∀ i, MeasurableSet (sets i))
    (bound : ENNReal) (x : α) (hx : x ∈ sets 0) (n : ℕ)
    (hstep : ∀ i < n, ∀ y ∈ sets i,
      bound ≤ transition y (sets (i + 1))) :
    bound ^ n ≤ (transition ^ n) x (sets n) := by
  induction n with
  | zero =>
      simp only [pow_zero]
      have hone : (1 : Kernel α α) = Kernel.id := rfl
      rw [hone]
      rw [Kernel.id_apply]
      simp [hx]
  | succ n ih =>
      have ih' := ih (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))
      rw [Kernel.pow_succ_apply_eq_lintegral transition n x
        (hmeasurable (n + 1))]
      calc
        bound ^ (n + 1) = bound * bound ^ n := by
          rw [pow_succ]
          ac_rfl
        _ ≤ bound * (transition ^ n) x (sets n) := by
          gcongr
        _ = ∫⁻ _y in sets n, bound ∂((transition ^ n) x) := by
          rw [setLIntegral_const]
        _ ≤ ∫⁻ y in sets n, transition y (sets (n + 1))
              ∂((transition ^ n) x) := by
          exact setLIntegral_mono' (hmeasurable n) fun y hy =>
            hstep n (Nat.lt_succ_self n) y hy
        _ ≤ ∫⁻ y, transition y (sets (n + 1))
              ∂((transition ^ n) x) :=
          setLIntegral_le_lintegral (sets n) _

/-- Allowance accumulated by iterating `Pv ≤ rate · v + allowance`. -/
noncomputable def affineDriftAccumulatedAllowance
    (rate allowance : ENNReal) : ℕ → ENNReal
  | 0 => 0
  | n + 1 => affineDriftAccumulatedAllowance rate allowance n +
      rate ^ n * allowance

theorem affineDriftAccumulatedAllowance_ne_top
    {rate allowance : ENNReal} (hrate : rate ≠ ∞)
    (hallowance : allowance ≠ ∞) :
    ∀ n, affineDriftAccumulatedAllowance rate allowance n ≠ ∞ := by
  intro n
  induction n with
  | zero => simp [affineDriftAccumulatedAllowance]
  | succ n ih =>
      rw [affineDriftAccumulatedAllowance]
      exact ENNReal.add_ne_top.2
        ⟨ih, ENNReal.mul_ne_top (ENNReal.pow_ne_top hrate) hallowance⟩

theorem affineDriftAccumulatedAllowance_eq_sum
    (rate allowance : ENNReal) : ∀ n,
    affineDriftAccumulatedAllowance rate allowance n =
      ∑ i ∈ Finset.range n, rate ^ i * allowance := by
  intro n
  induction n with
  | zero => simp [affineDriftAccumulatedAllowance]
  | succ n ih =>
      rw [affineDriftAccumulatedAllowance, Finset.sum_range_succ, ih]

/-- Every finite accumulated drift allowance is bounded by the infinite
geometric allowance, uniformly in the skeleton length. -/
theorem affineDriftAccumulatedAllowance_le_geometric
    (rate allowance : ENNReal) (n : ℕ) :
    affineDriftAccumulatedAllowance rate allowance n ≤
      (1 - rate)⁻¹ * allowance := by
  rw [affineDriftAccumulatedAllowance_eq_sum]
  calc
    (∑ i ∈ Finset.range n, rate ^ i * allowance) ≤
        ∑' i : ℕ, rate ^ i * allowance :=
      ENNReal.sum_le_tsum (Finset.range n)
    _ = (∑' i : ℕ, rate ^ i) * allowance := by
      rw [ENNReal.tsum_mul_right]
    _ = (1 - rate)⁻¹ * allowance := by
      rw [ENNReal.tsum_geometric]

/-- A strict finite affine rate and finite allowance admit a finite positive
paired-sublevel threshold that absorbs the doubled allowance. -/
theorem exists_affineDrift_paired_budget_threshold
    {rate allowance : ENNReal} (hrate : rate < 1)
    (hrateTop : rate ≠ ∞) (hallowanceTop : allowance ≠ ∞) :
    ∃ threshold : ENNReal, threshold ≠ 0 ∧ threshold ≠ ∞ ∧
      rate * threshold + (allowance + allowance) < threshold := by
  have hrateReal : rate.toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal hrateTop ENNReal.one_ne_top).2 hrate
  let gap : ℝ := 1 - rate.toReal
  have hgap : 0 < gap := sub_pos.mpr hrateReal
  let T : ℝ := 2 * allowance.toReal / gap + 1
  have hT : 0 < T := by
    dsimp [T]
    positivity
  let threshold : ENNReal := ENNReal.ofReal T
  have hthreshold0 : threshold ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hT).ne'
  have hthresholdTop : threshold ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨threshold, hthreshold0, hthresholdTop, ?_⟩
  have hallowanceAddTop : allowance + allowance ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hallowanceTop, hallowanceTop⟩
  have hrateMulTop : rate * threshold ≠ ∞ :=
    ENNReal.mul_ne_top hrateTop hthresholdTop
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.add_ne_top.2 ⟨hrateMulTop, hallowanceAddTop⟩)
    hthresholdTop).1
  rw [ENNReal.toReal_add hrateMulTop hallowanceAddTop,
    ENNReal.toReal_mul, ENNReal.toReal_add hallowanceTop hallowanceTop,
    ENNReal.toReal_ofReal hT.le]
  dsimp [T, gap]
  have hgapEq : (1 - rate.toReal) *
      (2 * allowance.toReal / (1 - rate.toReal)) =
      2 * allowance.toReal := by
    rw [div_eq_mul_inv]
    calc
      (1 - rate.toReal) *
          (2 * allowance.toReal * (1 - rate.toReal)⁻¹) =
          2 * allowance.toReal *
            ((1 - rate.toReal) * (1 - rate.toReal)⁻¹) := by ring
      _ = 2 * allowance.toReal := by
        rw [mul_inv_cancel₀ hgap.ne', mul_one]
  nlinarith

theorem ennreal_pow_le_self_of_le_one
    {r : ENNReal} (hr : r ≤ 1) {n : ℕ} (hn : 0 < n) :
    r ^ n ≤ r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hpow : ∀ m : ℕ, r ^ m ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        calc
          r ^ m * r ≤ 1 * 1 := by gcongr
          _ = 1 := mul_one 1
  rw [pow_succ]
  simpa only [one_mul, mul_one, mul_comm] using mul_le_mul_right (hpow k) r

/-- An affine one-chain drift certificate lifts to every kernel power with
the expected powered rate and accumulated allowance. -/
theorem HasAffineDrift.pow
    (transition : Kernel α α) [IsMarkovKernel transition]
    {v : α → ENNReal} {rate allowance : ENNReal}
    (hdrift : HasAffineDrift transition v rate allowance) (n : ℕ) :
    HasAffineDrift (transition ^ n) v (rate ^ n)
      (affineDriftAccumulatedAllowance rate allowance n) := by
  refine ⟨hdrift.1, ?_⟩
  induction n with
  | zero =>
      intro x
      simp only [pow_zero, affineDriftAccumulatedAllowance]
      have hone : (1 : Kernel α α) = Kernel.id := rfl
      rw [hone, Kernel.id_apply, lintegral_dirac' x hdrift.1]
      simp
  | succ n ih =>
      intro x
      rw [pow_succ]
      change (∫⁻ z, v z ∂((transition ^ n) ∘ₖ transition) x) ≤ _
      rw [Kernel.lintegral_comp _ _ _ hdrift.1]
      calc
        (∫⁻ y, ∫⁻ z, v z ∂(transition ^ n) y ∂transition x) ≤
            ∫⁻ y, rate ^ n * v y +
              affineDriftAccumulatedAllowance rate allowance n
              ∂transition x := by
          exact lintegral_mono ih
        _ = rate ^ n * (∫⁻ y, v y ∂transition x) +
            affineDriftAccumulatedAllowance rate allowance n := by
          have hscaled : Measurable (fun y => rate ^ n * v y) :=
            measurable_const.mul hdrift.1
          rw [lintegral_add_left hscaled,
            lintegral_const_mul _ hdrift.1, lintegral_const,
            measure_univ, mul_one]
        _ ≤ rate ^ n * (rate * v x + allowance) +
            affineDriftAccumulatedAllowance rate allowance n := by
          gcongr
          exact hdrift.2 x
        _ = rate ^ (n + 1) * v x +
            affineDriftAccumulatedAllowance rate allowance (n + 1) := by
          simp only [affineDriftAccumulatedAllowance, pow_succ]
          ring

/-- Invariance is preserved by every kernel power. -/
theorem invariant_pow
    {transition : Kernel α α} {target : Measure α}
    (hinvariant : transition.Invariant target) :
    ∀ n : ℕ, (transition ^ n).Invariant target := by
  intro n
  induction n with
  | zero =>
      have hone : (1 : Kernel α α) = Kernel.id := rfl
      rw [pow_zero, hone]
      rw [ProbabilityTheory.Kernel.Invariant, Measure.id_comp]
  | succ n ih =>
      rw [pow_succ]
      exact ih.comp hinvariant

/-- Normalize a finite positive restriction of a measure. -/
noncomputable def normalizedRestriction
    (μ : Measure α) (A : Set α) : Measure α :=
  (μ A)⁻¹ • μ.restrict A

theorem normalizedRestriction_isProbabilityMeasure
    (μ : Measure α) {A : Set α}
    (hApos : 0 < μ A) (hAtop : μ A ≠ ∞) :
    IsProbabilityMeasure (normalizedRestriction μ A) := by
  constructor
  rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply
    MeasurableSet.univ, Set.univ_inter]
  exact ENNReal.inv_mul_cancel hApos.ne' hAtop

theorem normalizedRestriction_apply
    (μ : Measure α) {A s : Set α} (hs : MeasurableSet s) :
    normalizedRestriction μ A s = (μ A)⁻¹ * μ (s ∩ A) := by
  rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply hs,
    smul_eq_mul]

/-- A lower density bound against `μ` on one finite positive output region
is exactly a local minorization by its normalized restriction. -/
theorem locallyMinorizes_normalizedRestriction_of_densityFloor
    (transition : Kernel α α) (D : Set α) (μ : Measure α)
    {A : Set α}
    (hApos : 0 < μ A) (hAtop : μ A ≠ ∞) (floor : ENNReal)
    (hfloor : ∀ x ∈ D, ∀ s, MeasurableSet s →
      floor * μ (s ∩ A) ≤ transition x s) :
    LocallyMinorizes transition D (floor * μ A)
      (normalizedRestriction μ A) := by
  intro x hx s hs
  rw [normalizedRestriction_apply μ hs]
  rw [show floor * μ A * ((μ A)⁻¹ * μ (s ∩ A)) =
      floor * (μ A * (μ A)⁻¹) * μ (s ∩ A) by ac_rfl,
    ENNReal.mul_inv_cancel hApos.ne' hAtop, mul_one]
  exact hfloor x hx s hs

/-- A positive ENNReal local-minorization coefficient can be shrunk to a
strictly interior NNReal mixture coefficient, as required by residual
coupling constructions. -/
theorem LocallyMinorizes.exists_pos_nnreal_coefficient
    (transition : Kernel α α) [IsMarkovKernel transition] (D : Set α)
    (reference : Measure α) [IsProbabilityMeasure reference]
    {coefficient : ENNReal} (hcoefficient : 0 < coefficient)
    (hDne : D.Nonempty)
    (hlocal : LocallyMinorizes transition D coefficient reference) :
    ∃ p : Set.Icc (0 : NNReal) 1,
      0 < p.1 ∧ p.1 < 1 ∧
      LocallyMinorizes transition D (p.1 : ENNReal) reference := by
  obtain ⟨x, hx⟩ := hDne
  have hleOne : coefficient ≤ 1 := by
    have h := hlocal x hx Set.univ MeasurableSet.univ
    simpa using h
  have htop : coefficient ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hleOne
  let pval : NNReal := coefficient.toNNReal / 2
  have hpvalPos : 0 < pval := by
    dsimp [pval]
    exact div_pos (ENNReal.toNNReal_pos hcoefficient.ne' htop) (by norm_num)
  have hpvalLt : pval < 1 := by
    have hcoe : coefficient.toNNReal ≤ 1 := by
      exact (ENNReal.toNNReal_le_toNNReal htop ENNReal.one_ne_top).2 hleOne
    dsimp [pval]
    calc
      coefficient.toNNReal / 2 ≤ 1 / 2 := by gcongr
      _ < 1 := by norm_num
  let p : Set.Icc (0 : NNReal) 1 :=
    ⟨pval, hpvalPos.le, hpvalLt.le⟩
  refine ⟨p, hpvalPos, hpvalLt, ?_⟩
  intro y hy s hs
  have hpLe : ((p.1 : NNReal) : ENNReal) ≤ coefficient := by
    change ((coefficient.toNNReal / 2 : NNReal) : ENNReal) ≤ coefficient
    have hpvalLe : coefficient.toNNReal / 2 ≤ coefficient.toNNReal := by
      calc
        coefficient.toNNReal / 2 ≤ coefficient.toNNReal / 1 := by
          gcongr
          norm_num
        _ = coefficient.toNNReal := div_one _
    calc
      ((coefficient.toNNReal / 2 : NNReal) : ENNReal) ≤
          (coefficient.toNNReal : ENNReal) := by
        exact_mod_cast hpvalLe
      _ ≤ coefficient := ENNReal.coe_toNNReal_le_self
  calc
    (p.1 : ENNReal) * reference s ≤ coefficient * reference s := by
      gcongr
    _ ≤ transition y s := hlocal y hy s hs

section OneDimensionalChangeOfVariables

/-- A source density floor and an upper Jacobian bound imply an output
density floor for an injective one-dimensional transformation. The theorem
uses image-volume control directly, so clients need not construct an inverse
or its derivative. -/
theorem mul_volume_le_map_of_sourceFloor_of_image_le
    (source : Measure ℝ) (f : ℝ → ℝ)
    (hf : MeasurableEmbedding f) {P S : Set ℝ}
    (hS : MeasurableSet S) (hSP : S ⊆ f '' P)
    (sourceFloor jacobianBound outputFloor : ENNReal)
    (hsource : ∀ T, MeasurableSet T → T ⊆ P →
      sourceFloor * volume T ≤ source T)
    (himage : ∀ T, MeasurableSet T →
      volume (f '' T) ≤ jacobianBound * volume T)
    (hcoefficient : outputFloor * jacobianBound ≤ sourceFloor) :
    outputFloor * volume S ≤ Measure.map f source S := by
  let T := f ⁻¹' S
  have hT : MeasurableSet T := hf.measurable hS
  have hTP : T ⊆ P := by
    intro x hx
    obtain ⟨y, hyP, hy⟩ := hSP hx
    exact (hf.injective hy).symm ▸ hyP
  have himageEq : f '' T = S := by
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact hx
    · intro z hz
      obtain ⟨x, hxP, rfl⟩ := hSP hz
      exact ⟨x, hz, rfl⟩
  rw [Measure.map_apply hf.measurable hS]
  calc
    outputFloor * volume S = outputFloor * volume (f '' T) := by
      rw [himageEq]
    _ ≤ outputFloor * (jacobianBound * volume T) := by
      gcongr
      exact himage T hT
    _ = (outputFloor * jacobianBound) * volume T := by ring
    _ ≤ sourceFloor * volume T := by gcongr
    _ ≤ source T := hsource T hT hTP

end OneDimensionalChangeOfVariables

/-- Replace rows outside `D` by the reference probability law.  On `D` this
is definitionally the original transition. -/
noncomputable def localizedMinorizationKernel
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) : Kernel α α := by
  classical
  exact Kernel.piecewise hD transition (Kernel.const α reference)

instance localizedMinorizationKernel.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference] :
    IsMarkovKernel (localizedMinorizationKernel transition D hD reference) := by
  classical
  unfold localizedMinorizationKernel
  infer_instance

@[simp]
theorem localizedMinorizationKernel_apply_of_mem
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) {x : α} (hx : x ∈ D) :
    localizedMinorizationKernel transition D hD reference x = transition x := by
  classical
  change (if x ∈ D then transition x else reference) = transition x
  rw [if_pos hx]

@[simp]
theorem localizedMinorizationKernel_apply_of_not_mem
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) {x : α} (hx : x ∉ D) :
    localizedMinorizationKernel transition D hD reference x = reference := by
  classical
  change (if x ∈ D then transition x else reference) = reference
  rw [if_neg hx]

/-- Local minorization becomes global after replacing the irrelevant rows.
-/
theorem localizedMinorizationKernel_uniformlyMinorizes
    (transition : Kernel α α) (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) (ε : Set.Icc (0 : NNReal) 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    UniformlyMinorizes
      (localizedMinorizationKernel transition D hD reference) ε.1 reference := by
  intro x s hs
  by_cases hx : x ∈ D
  · rw [localizedMinorizationKernel_apply_of_mem transition D hD reference hx]
    exact hlocal x hx s hs
  · rw [localizedMinorizationKernel_apply_of_not_mem transition D hD reference hx]
    exact mul_le_of_le_one_left (bot_le : 0 ≤ reference s)
      (show (ε.1 : ENNReal) ≤ 1 by exact_mod_cast ε.2.2)

/-- The globalized kernel has the standard residual decomposition, while its
rows on `D` are still exactly the original transition rows. -/
theorem mixture_localizedResidual_apply_of_mem
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference)
    {x : α} (hx : x ∈ D) :
    mixture ε (Kernel.const α reference)
        (minorizationResidual
          (localizedMinorizationKernel transition D hD reference)
          reference ε hε
          (localizedMinorizationKernel_uniformlyMinorizes
            transition D hD reference ε hlocal)) x =
      transition x := by
  have hdecomp := congrArg (fun K : Kernel α α => K x)
    (mixture_minorizationResidual_eq
      (localizedMinorizationKernel transition D hD reference)
      reference ε hε
      (localizedMinorizationKernel_uniformlyMinorizes
        transition D hD reference ε hlocal))
  simpa [localizedMinorizationKernel_apply_of_mem
    transition D hD reference hx] using hdecomp

/-- The common reference draw copied onto both output coordinates. -/
noncomputable def diagonalReferenceCoupling
    (reference : Measure α) : Kernel (α × α) (α × α) :=
  synchronousCoupling (Kernel.const α reference)

instance diagonalReferenceCoupling.instIsMarkovKernel
    (reference : Measure α) [IsProbabilityMeasure reference] :
    IsMarkovKernel (diagonalReferenceCoupling reference) := by
  unfold diagonalReferenceCoupling
  infer_instance

theorem diagonalReferenceCoupling_isCoupling
    (reference : Measure α) [IsProbabilityMeasure reference] :
    IsCoupling (diagonalReferenceCoupling reference)
      (Kernel.const α reference) (Kernel.const α reference) := by
  constructor
  · ext current s hs
    rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply]
    change ((Kernel.const (α × α) reference).map diagonalMap current)
      (Prod.fst ⁻¹' s) = reference s
    rw [Kernel.map_apply' _ measurable_diagonalMap current (measurable_fst hs),
      Kernel.const_apply]
    rfl
  · ext current s hs
    rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply]
    change ((Kernel.const (α × α) reference).map diagonalMap current)
      (Prod.snd ⁻¹' s) = reference s
    rw [Kernel.map_apply' _ measurable_diagonalMap current (measurable_snd hs),
      Kernel.const_apply]
    rfl

/-- Coupling supplied by the common local-minorization component and
independent residuals of the globalized transition. -/
noncomputable def localizedMinorizationCoreCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    Kernel (α × α) (α × α) :=
  let localized := localizedMinorizationKernel transition D hD reference
  let hglobal := localizedMinorizationKernel_uniformlyMinorizes
    transition D hD reference ε hlocal
  let residual := minorizationResidual localized reference ε hε hglobal
  mixture ε (diagonalReferenceCoupling reference)
    (independentCoupling residual residual)

instance localizedMinorizationCoreCoupling.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsMarkovKernel (localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal) := by
  unfold localizedMinorizationCoreCoupling
  infer_instance

/-- Both marginals of the core coupling are the residual decomposition of
the globalized transition. -/
theorem localizedMinorizationCoreCoupling_isCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    let localized := localizedMinorizationKernel transition D hD reference
    let hglobal := localizedMinorizationKernel_uniformlyMinorizes
      transition D hD reference ε hlocal
    let residual := minorizationResidual localized reference ε hε hglobal
    IsCoupling (localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal)
      (mixture ε (Kernel.const α reference) residual)
      (mixture ε (Kernel.const α reference) residual) := by
  dsimp
  apply mixture_isCoupling
  · exact diagonalReferenceCoupling_isCoupling reference
  · exact independentCoupling_isCoupling _ _

/-- The core coupling uses its common component with probability `ε`, hence
has at least `ε` diagonal mass at every input pair. -/
theorem coe_le_localizedMinorizationCoreCoupling_diagonal
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference)
    (current : α × α) :
    (ε.1 : ENNReal) ≤ localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal current (Set.diagonal α) := by
  calc
    (ε.1 : ENNReal) = (ε.1 : ENNReal) *
        diagonalReferenceCoupling reference current (Set.diagonal α) := by
      have hdiag : diagonalReferenceCoupling reference current
          (Set.diagonal α) = 1 := by
        unfold diagonalReferenceCoupling synchronousCoupling
        rw [Kernel.map_apply' _ measurable_diagonalMap current
          measurableSet_diagonal, Kernel.comap_apply, Kernel.const_apply]
        have hpre : diagonalMap ⁻¹' Set.diagonal α = Set.univ := by
          ext y
          simp [diagonalMap]
        rw [hpre, measure_univ]
      rw [hdiag, mul_one]
    _ ≤ _ := by
      exact mixture_apply_first_le ε _ _ current measurableSet_diagonal

/-- Use the common-component coupling when both inputs lie in `D`, and the
ordinary independent coupling elsewhere. -/
noncomputable def localMinorizationCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    Kernel (α × α) (α × α) := by
  classical
  exact Kernel.piecewise (hD.prod hD)
    (localizedMinorizationCoreCoupling
      transition D hD reference ε hε hlocal)
    (independentCoupling transition transition)

instance localMinorizationCoupling.instIsMarkovKernel
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsMarkovKernel (localMinorizationCoupling
      transition D hD reference ε hε hlocal) := by
  classical
  unfold localMinorizationCoupling
  infer_instance

theorem localMinorizationCoupling_isCoupling
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsCoupling (localMinorizationCoupling
      transition D hD reference ε hε hlocal) transition transition := by
  classical
  let core := localizedMinorizationCoreCoupling
    transition D hD reference ε hε hlocal
  let localized := localizedMinorizationKernel transition D hD reference
  let hglobal := localizedMinorizationKernel_uniformlyMinorizes
    transition D hD reference ε hlocal
  let residual := minorizationResidual localized reference ε hε hglobal
  have hcore : IsCoupling core
      (mixture ε (Kernel.const α reference) residual)
      (mixture ε (Kernel.const α reference) residual) :=
    localizedMinorizationCoreCoupling_isCoupling
      transition D hD reference ε hε hlocal
  have hindependent := independentCoupling_isCoupling transition transition
  constructor
  · ext current s hs
    rw [Kernel.fst_apply' _ _ hs, Kernel.comap_apply,
      localMinorizationCoupling, Kernel.piecewise_apply']
    split_ifs with hcurrent
    · rw [← Kernel.fst_apply' core current hs, hcore.fst_apply]
      have hx : current.1 ∈ D := hcurrent.1
      exact congrArg (fun μ : Measure α => μ s)
        (mixture_localizedResidual_apply_of_mem
          transition D hD reference ε hε hlocal hx)
    · rw [← Kernel.fst_apply' (independentCoupling transition transition)
          current hs,
        hindependent.fst_apply]
  · ext current s hs
    rw [Kernel.snd_apply' _ _ hs, Kernel.comap_apply,
      localMinorizationCoupling, Kernel.piecewise_apply']
    split_ifs with hcurrent
    · rw [← Kernel.snd_apply' core current hs, hcore.snd_apply]
      have hx : current.2 ∈ D := hcurrent.2
      exact congrArg (fun μ : Measure α => μ s)
        (mixture_localizedResidual_apply_of_mem
          transition D hD reference ε hε hlocal hx)
    · rw [← Kernel.snd_apply' (independentCoupling transition transition)
          current hs,
        hindependent.snd_apply]

/-- On `D × D`, the local-minorization coupling has diagonal mass at least
the minorization coefficient. -/
theorem localMinorizationCoupling_isExactMeetingSmallSet
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsExactMeetingSmallSet
      (localMinorizationCoupling transition D hD reference ε hε hlocal)
      (D ×ˢ D) ε.1 := by
  intro current hcurrent
  classical
  rw [localMinorizationCoupling, Kernel.piecewise_apply', if_pos hcurrent]
  exact coe_le_localizedMinorizationCoreCoupling_diagonal
    transition D hD reference ε hε hlocal current

/-- Sticky version used by meeting-time arguments. -/
noncomputable def faithfulLocalMinorizationCoupling
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    Kernel (α × α) (α × α) :=
  stickyCoupling transition
    (localMinorizationCoupling transition D hD reference ε hε hlocal)

instance faithfulLocalMinorizationCoupling.instIsMarkovKernel
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsMarkovKernel (faithfulLocalMinorizationCoupling
      transition D hD reference ε hε hlocal) := by
  unfold faithfulLocalMinorizationCoupling
  infer_instance

theorem faithfulLocalMinorizationCoupling_isCoupling
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsCoupling (faithfulLocalMinorizationCoupling
      transition D hD reference ε hε hlocal) transition transition := by
  apply stickyCoupling_isCoupling
  exact localMinorizationCoupling_isCoupling
    transition D hD reference ε hε hlocal

theorem faithfulLocalMinorizationCoupling_isFaithful
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsFaithful (faithfulLocalMinorizationCoupling
      transition D hD reference ε hε hlocal) := by
  exact stickyCoupling_isFaithful transition _

theorem faithfulLocalMinorizationCoupling_isExactMeetingSmallSet
    [MeasurableEq α]
    (transition : Kernel α α) [IsMarkovKernel transition]
    (D : Set α) (hD : MeasurableSet D)
    (reference : Measure α) [IsProbabilityMeasure reference]
    (ε : Set.Icc (0 : NNReal) 1) (hε : ε.1 < 1)
    (hlocal : LocallyMinorizes transition D ε.1 reference) :
    IsExactMeetingSmallSet
      (faithfulLocalMinorizationCoupling
        transition D hD reference ε hε hlocal)
      (D ×ˢ D) ε.1 := by
  apply stickyCoupling_isExactMeetingSmallSet
  exact localMinorizationCoupling_isExactMeetingSmallSet
    transition D hD reference ε hε hlocal

end Mcmc.Kernel
