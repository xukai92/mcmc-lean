import Mcmc.Hamiltonian.DynamicMultinomial
import Mcmc.Hamiltonian.Invariance
import Mcmc.Finite.CertifiedDynamicTree

/-!
# Invariance of certified dynamic multinomial trajectories

This module lifts the pointwise reroot theorem for a dynamic candidate mask to
measure-level detailed balance.  It is the continuous-state correctness
interface intended for checked NUTS trees: executable tree construction may be
arbitrary, but its completed candidate mask must be measurable, root retaining,
row-reroot invariant at admitted candidates, and pairwise membership symmetric.
-/

open MeasureTheory
open scoped BigOperators ENNReal ProbabilityTheory

namespace Mcmc.Hamiltonian

open ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- A globally checked family of finite candidate rows expressed in orbit
coordinates.  `orbitCovariant` states that rebuilding after moving the phase
point and changing the distinguished origin addresses the same physical
trajectory rows. -/
structure CertifiedTrajectoryCandidateRows
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ) where
  rows : PhaseSpace ι → Fin (L + 1) → Finset (Fin (L + 1))
  checks : ∀ z, Mcmc.Finite.MarkovKernel.CertifiedDynamicTree.Checks (rows z)
  orbitCovariant : ∀ z origin selected,
    rows (offsetLeapfrogTrajectory gradient ε origin z selected) selected =
      rows z selected

/-- Raw orbit-coordinate rows before applying the executable global checker.
The covariance requirement covers every possible distinguished root, so the
check result cannot change merely because the same orbit is rerooted. -/
structure RawTrajectoryCandidateRows
    (gradient : Position ι → Position ι) (ε : ℝ) (L : ℕ) where
  rows : PhaseSpace ι → Fin (L + 1) → Finset (Fin (L + 1))
  orbitCovariant : ∀ (z : PhaseSpace ι) (origin selected root : Fin (L + 1)),
    rows (offsetLeapfrogTrajectory gradient ε origin z selected) root = rows z root

/-- Executable checked-or-identity sanitization of a complete row family. -/
def RawTrajectoryCandidateRows.checkedRows
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (raw : RawTrajectoryCandidateRows gradient ε L)
    (z : PhaseSpace ι) (root : Fin (L + 1)) : Finset (Fin (L + 1)) :=
  if Mcmc.Finite.MarkovKernel.CertifiedDynamicTree.check (raw.rows z) then
    raw.rows z root
  else {root}

omit [Fintype ι] in
theorem RawTrajectoryCandidateRows.checkedRows_checks
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (raw : RawTrajectoryCandidateRows gradient ε L) (z : PhaseSpace ι) :
    Mcmc.Finite.MarkovKernel.CertifiedDynamicTree.Checks (raw.checkedRows z) := by
  classical
  by_cases hcheck :
      Mcmc.Finite.MarkovKernel.CertifiedDynamicTree.check (raw.rows z) = true
  · have hchecks :=
      (Mcmc.Finite.MarkovKernel.CertifiedDynamicTree.check_eq_true_iff
        (raw.rows z)).mp hcheck
    have heq : raw.checkedRows z = raw.rows z := by
      funext root
      simp [RawTrajectoryCandidateRows.checkedRows, hcheck]
    rw [heq]
    exact hchecks
  · have hfalse :
        Mcmc.Finite.MarkovKernel.CertifiedDynamicTree.check (raw.rows z) = false :=
      Bool.eq_false_of_not_eq_true hcheck
    have heq : raw.checkedRows z = fun root => {root} := by
      funext root
      simp [RawTrajectoryCandidateRows.checkedRows, hfalse]
    rw [heq]
    constructor
    · intro root
      simp
    · intro root leaf hleaf
      simp_all

omit [Fintype ι] in
theorem RawTrajectoryCandidateRows.checkedRows_orbitCovariant
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (raw : RawTrajectoryCandidateRows gradient ε L) :
    ∀ (z : PhaseSpace ι) (origin selected root : Fin (L + 1)),
      raw.checkedRows (offsetLeapfrogTrajectory gradient ε origin z selected) root =
        raw.checkedRows z root := by
  classical
  intro z origin selected root
  have hrows : raw.rows (offsetLeapfrogTrajectory gradient ε origin z selected) =
      raw.rows z := by
    funext candidateRoot
    exact raw.orbitCovariant z origin selected candidateRoot
  simp [RawTrajectoryCandidateRows.checkedRows, hrows]

/-- Every orbit-covariant raw builder becomes a proof-bearing continuous
candidate certificate after the executable checked-or-identity wrapper. -/
def RawTrajectoryCandidateRows.toCertified
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (raw : RawTrajectoryCandidateRows gradient ε L) :
    CertifiedTrajectoryCandidateRows gradient ε L where
  rows := raw.checkedRows
  checks := raw.checkedRows_checks
  orbitCovariant := fun z origin selected =>
    raw.checkedRows_orbitCovariant z origin selected selected

/-- Boolean mask decoded from proof-bearing checked orbit rows. -/
def CertifiedTrajectoryCandidateRows.mask
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (certificate : CertifiedTrajectoryCandidateRows gradient ε L) :
    TrajectoryCandidateMask ι L :=
  fun z origin selected => decide (selected ∈ certificate.rows z origin)

omit [Fintype ι] in
theorem CertifiedTrajectoryCandidateRows.mask_root
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (certificate : CertifiedTrajectoryCandidateRows gradient ε L) :
    ∀ z origin, certificate.mask z origin origin = true := by
  intro z origin
  simp [CertifiedTrajectoryCandidateRows.mask, (certificate.checks z).1 origin]

omit [Fintype ι] in
theorem CertifiedTrajectoryCandidateRows.mask_reroot
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (certificate : CertifiedTrajectoryCandidateRows gradient ε L) :
    ∀ z origin selected, certificate.mask z origin selected = true →
      ∀ i, certificate.mask
          (offsetLeapfrogTrajectory gradient ε origin z selected) selected i =
        certificate.mask z origin i := by
  intro z origin selected hselected i
  have hmem : selected ∈ certificate.rows z origin := by
    simpa [CertifiedTrajectoryCandidateRows.mask] using hselected
  have hrows := (certificate.checks z).2 origin selected hmem
  apply Bool.decide_congr
  rw [certificate.orbitCovariant z origin selected, hrows]

omit [Fintype ι] in
theorem CertifiedTrajectoryCandidateRows.mask_pair
    {gradient : Position ι → Position ι} {ε : ℝ} {L : ℕ}
    (certificate : CertifiedTrajectoryCandidateRows gradient ε L) :
    ∀ z origin selected,
      certificate.mask
          (offsetLeapfrogTrajectory gradient ε origin z selected) selected origin =
        certificate.mask z origin selected := by
  intro z origin selected
  apply Bool.decide_congr
  rw [certificate.orbitCovariant z origin selected]
  constructor
  · intro horigin
    have hrows := (certificate.checks z).2 selected origin horigin
    rw [hrows]
    exact (certificate.checks z).1 selected
  · intro hselected
    have hrows := (certificate.checks z).2 origin selected hselected
    rw [hrows]
    exact (certificate.checks z).1 origin

/-- Measurability of every Boolean candidate decision. -/
def MeasurableTrajectoryCandidateMask {L : ℕ}
    (mask : TrajectoryCandidateMask ι L) : Prop :=
  ∀ origin selected, Measurable fun z => mask z origin selected

theorem measurable_dynamicTrajectoryWeight
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} {mask : TrajectoryCandidateMask ι L}
    (hmask : MeasurableTrajectoryCandidateMask mask)
    (origin selected : Fin (L + 1)) :
    Measurable fun z =>
      dynamicTrajectoryWeight potential gradient ε mask z origin selected := by
  unfold dynamicTrajectoryWeight
  apply Measurable.ite
  · exact (hmask origin selected) (measurableSet_singleton true)
  · exact (measurable_boltzmannWeight hpotential).comp
      (measurable_offsetLeapfrogTrajectory hgradient ε origin selected)
  · exact measurable_const

theorem measurable_dynamicTrajectoryIndexProbability
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} {mask : TrajectoryCandidateMask ι L}
    (hmask : MeasurableTrajectoryCandidateMask mask)
    (hroot : ∀ z origin, mask z origin origin = true)
    (origin selected : Fin (L + 1)) :
    Measurable fun z =>
      dynamicTrajectoryIndexPMF potential gradient ε mask hroot z origin selected := by
  simp only [dynamicTrajectoryIndexPMF_apply, dynamicTrajectoryNormalizer]
  apply Measurable.mul
  · exact measurable_dynamicTrajectoryWeight hpotential hgradient ε hmask origin selected
  · apply Measurable.inv
    apply Finset.measurable_sum
    intro i hi
    exact measurable_dynamicTrajectoryWeight hpotential hgradient ε hmask origin i

/-- One ordered origin/selected component of the dynamic transition. -/
noncomputable def dynamicTrajectoryIndexComponentKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (origin selected : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hmask : MeasurableTrajectoryCandidateMask mask) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) where
  toFun z :=
    (dynamicTrajectoryIndexPMF potential gradient ε mask hroot z origin selected) •
      Measure.dirac (offsetLeapfrogTrajectory gradient ε origin z selected)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    exact (measurable_dynamicTrajectoryIndexProbability hpotential hgradient ε hmask
      hroot origin selected).mul
        (measurable_const.indicator
          (measurable_offsetLeapfrogTrajectory hgradient ε origin selected hs))

/-- Fixed-origin dynamic multinomial transition. -/
noncomputable def dynamicOffsetMultinomialKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (origin : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hmask : MeasurableTrajectoryCandidateMask mask) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) where
  toFun z := ∑ selected,
    dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
      origin selected hpotential hgradient hmask z
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply]
    exact Finset.measurable_sum _ fun selected hselected =>
      (dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
        origin selected hpotential hgradient hmask).measurable_coe hs

instance dynamicOffsetMultinomialKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (origin : Fin (L + 1))
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hmask : MeasurableTrajectoryCandidateMask mask) :
    IsMarkovKernel (dynamicOffsetMultinomialKernel potential gradient ε mask hroot
      origin hpotential hgradient hmask) where
  isProbabilityMeasure z := by
    constructor
    rw [dynamicOffsetMultinomialKernel]
    change (∑ selected : Fin (L + 1),
      dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
        origin selected hpotential hgradient hmask z) Set.univ = 1
    rw [Measure.finsetSum_apply]
    change (∑ selected : Fin (L + 1),
      ((dynamicTrajectoryIndexPMF potential gradient ε mask hroot z origin selected) •
        Measure.dirac (offsetLeapfrogTrajectory gradient ε origin z selected)) Set.univ) = 1
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    exact (tsum_fintype _).symm.trans
      (PMF.tsum_coe (dynamicTrajectoryIndexPMF potential gradient ε mask hroot z origin))

/-- Uniform mixture over possible trajectory origins. -/
noncomputable def randomizedDynamicMultinomialKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hmask : MeasurableTrajectoryCandidateMask mask) :
    Kernel (PhaseSpace ι) (PhaseSpace ι) where
  toFun z := ∑ origin,
    PMF.uniformOfFintype (Fin (L + 1)) origin •
      dynamicOffsetMultinomialKernel potential gradient ε mask hroot origin
        hpotential hgradient hmask z
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ fun origin horigin => measurable_const.mul
      ((dynamicOffsetMultinomialKernel potential gradient ε mask hroot origin
        hpotential hgradient hmask).measurable_coe hs)

instance randomizedDynamicMultinomialKernel_isMarkovKernel
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hmask : MeasurableTrajectoryCandidateMask mask) :
    IsMarkovKernel (randomizedDynamicMultinomialKernel potential gradient ε mask hroot
      hpotential hgradient hmask) where
  isProbabilityMeasure z := by
    constructor
    rw [randomizedDynamicMultinomialKernel]
    change (∑ origin : Fin (L + 1),
      PMF.uniformOfFintype (Fin (L + 1)) origin •
        dynamicOffsetMultinomialKernel potential gradient ε mask hroot origin
          hpotential hgradient hmask z) Set.univ = 1
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact (tsum_fintype _).symm.trans (PMF.tsum_coe _)

/-- Target-weighted probability flow for one dynamic ordered pair. -/
noncomputable def dynamicTrajectorySelectionFlow
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (origin selected : Fin (L + 1)) (z : PhaseSpace ι) : ℝ≥0∞ :=
  boltzmannWeight potential z *
    dynamicTrajectoryIndexPMF potential gradient ε mask hroot z origin selected

theorem measurable_dynamicTrajectorySelectionFlow
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} {mask : TrajectoryCandidateMask ι L}
    (hmask : MeasurableTrajectoryCandidateMask mask)
    (hroot : ∀ z origin, mask z origin origin = true)
    (origin selected : Fin (L + 1)) :
    Measurable (dynamicTrajectorySelectionFlow potential gradient ε mask hroot
      origin selected) :=
  (measurable_boltzmannWeight hpotential).mul
    (measurable_dynamicTrajectoryIndexProbability hpotential hgradient ε hmask
      hroot origin selected)

theorem dynamicTrajectoryIndexComponentKernel_balance
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hmask : MeasurableTrajectoryCandidateMask mask)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hreroot : ∀ z origin selected, mask z origin selected = true →
      ∀ i, mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected i =
        mask z origin i)
    (hpair : ∀ z origin selected,
      mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected origin =
        mask z origin selected)
    (origin selected : Fin (L + 1))
    {A B : Set (PhaseSpace ι)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ z in A,
        dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
          origin selected hpotential hgradient hmask z B ∂phaseBoltzmannTarget potential =
      ∫⁻ z in B,
        dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
          selected origin hpotential hgradient hmask z A ∂phaseBoltzmannTarget potential := by
  unfold phaseBoltzmannTarget
  rw [setLIntegral_withDensity_eq_setLIntegral_mul phaseVolume
      (measurable_boltzmannWeight hpotential)
      ((dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
        origin selected hpotential hgradient hmask).measurable_coe hB) hA]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul phaseVolume
      (measurable_boltzmannWeight hpotential)
      ((dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
        selected origin hpotential hgradient hmask).measurable_coe hA) hB]
  rw [← lintegral_indicator hA, ← lintegral_indicator hB]
  let T : PhaseSpace ι → PhaseSpace ι :=
    fun z => offsetLeapfrogTrajectory gradient ε origin z selected
  let reverseIntegrand : PhaseSpace ι → ℝ≥0∞ := fun z =>
    (B ∩ (fun z => offsetLeapfrogTrajectory gradient ε selected z origin) ⁻¹' A).indicator
      (dynamicTrajectorySelectionFlow potential gradient ε mask hroot selected origin) z
  have hreverse : Measurable reverseIntegrand := by
    unfold reverseIntegrand
    apply Measurable.indicator
    · exact measurable_dynamicTrajectorySelectionFlow hpotential hgradient ε hmask hroot
        selected origin
    · exact hB.inter (measurable_offsetLeapfrogTrajectory hgradient ε selected origin hA)
  calc
    _ = ∫⁻ z, (A ∩ (fun z =>
          offsetLeapfrogTrajectory gradient ε origin z selected) ⁻¹' B).indicator
            (dynamicTrajectorySelectionFlow potential gradient ε mask hroot origin selected) z
          ∂phaseVolume := by
        apply lintegral_congr
        intro z
        by_cases hzA : z ∈ A <;>
          by_cases hzB : offsetLeapfrogTrajectory gradient ε origin z selected ∈ B <;>
            simp [dynamicTrajectoryIndexComponentKernel, dynamicTrajectorySelectionFlow,
              Set.indicator, hzA, hzB, Measure.dirac_apply' _ hB]
    _ = ∫⁻ z, reverseIntegrand z ∂phaseVolume := by
        rw [← (measurePreserving_offsetLeapfrogTrajectory hgradient ε origin selected).lintegral_comp
          hreverse]
        apply lintegral_congr
        intro z
        have hback : offsetLeapfrogTrajectory gradient ε selected
            (offsetLeapfrogTrajectory gradient ε origin z selected) origin = z := by
          rw [offsetLeapfrogTrajectory_reroot, offsetLeapfrogTrajectory_origin]
        have hflow := boltzmann_dynamicTrajectoryIndexPMF_flow_reroot
          potential gradient ε mask hroot hreroot hpair z origin selected
        unfold reverseIntegrand dynamicTrajectorySelectionFlow
        by_cases hzA : z ∈ A
        · by_cases hzB : offsetLeapfrogTrajectory gradient ε origin z selected ∈ B
          · simp only [Set.mem_inter_iff, Set.mem_preimage, hzA, hzB, and_self,
              Set.indicator_of_mem, hback]
            exact hflow
          · simp [Set.indicator, hzA, hzB]
        · simp [Set.indicator, hzA, hback]
    _ = _ := by
        apply lintegral_congr
        intro z
        unfold reverseIntegrand
        by_cases hzB : z ∈ B <;>
          by_cases hzA : offsetLeapfrogTrajectory gradient ε selected z origin ∈ A <;>
            simp [dynamicTrajectoryIndexComponentKernel, dynamicTrajectorySelectionFlow,
              Set.indicator, hzA, hzB, Measure.dirac_apply' _ hA]

theorem randomizedDynamicMultinomialKernel_apply_set_eq_components
    (potential : Position ι → ℝ) (gradient : Position ι → Position ι)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (hmask : MeasurableTrajectoryCandidateMask mask)
    (z : PhaseSpace ι) (s : Set (PhaseSpace ι)) (_hs : MeasurableSet s) :
    randomizedDynamicMultinomialKernel potential gradient ε mask hroot
        hpotential hgradient hmask z s =
      ∑ origin : Fin (L + 1), PMF.uniformOfFintype (Fin (L + 1)) origin *
        ∑ selected : Fin (L + 1),
          dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
            origin selected hpotential hgradient hmask z s := by
  change (∑ origin : Fin (L + 1),
    PMF.uniformOfFintype (Fin (L + 1)) origin •
      dynamicOffsetMultinomialKernel potential gradient ε mask hroot origin
        hpotential hgradient hmask z) s = _
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro origin horigin
  rw [Measure.smul_apply, smul_eq_mul]
  congr 1
  change (∑ selected : Fin (L + 1),
    dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
      origin selected hpotential hgradient hmask z) s = _
  rw [Measure.finsetSum_apply]

private theorem randomizedDynamicMultinomialKernel_flow_sum
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hmask : MeasurableTrajectoryCandidateMask mask)
    {A B : Set (PhaseSpace ι)} (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ z in A, randomizedDynamicMultinomialKernel potential gradient ε mask hroot
        hpotential hgradient hmask z B ∂phaseBoltzmannTarget potential =
      ∑ origin : Fin (L + 1), PMF.uniformOfFintype (Fin (L + 1)) origin *
        ∑ selected : Fin (L + 1), ∫⁻ z in A,
          dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
            origin selected hpotential hgradient hmask z B
            ∂phaseBoltzmannTarget potential := by
  simp_rw [randomizedDynamicMultinomialKernel_apply_set_eq_components
    potential gradient ε mask hroot hpotential hgradient hmask _ B hB]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro origin horigin
    rw [lintegral_const_mul _ (Finset.measurable_sum _ fun selected hselected =>
      (dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
        origin selected hpotential hgradient hmask).measurable_coe hB)]
    rw [lintegral_finsetSum _ fun selected hselected =>
      (dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
        origin selected hpotential hgradient hmask).measurable_coe hB]
  · intro origin horigin
    exact measurable_const.mul (Finset.measurable_sum _ fun selected hselected =>
      (dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
        origin selected hpotential hgradient hmask).measurable_coe hB)

/-- A certified dynamic multinomial trajectory transition satisfies detailed
balance with respect to the phase-space Boltzmann measure. -/
theorem randomizedDynamicMultinomialKernel_isReversible
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hmask : MeasurableTrajectoryCandidateMask mask)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hreroot : ∀ z origin selected, mask z origin selected = true →
      ∀ i, mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected i =
        mask z origin i)
    (hpair : ∀ z origin selected,
      mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected origin =
        mask z origin selected) :
    (randomizedDynamicMultinomialKernel potential gradient ε mask hroot
      hpotential hgradient hmask).IsReversible (phaseBoltzmannTarget potential) := by
  intro A B hA hB
  rw [randomizedDynamicMultinomialKernel_flow_sum hpotential hgradient ε mask
    hroot hmask hA hB]
  rw [randomizedDynamicMultinomialKernel_flow_sum hpotential hgradient ε mask
    hroot hmask hB hA]
  trans ∑ origin : Fin (L + 1), PMF.uniformOfFintype (Fin (L + 1)) origin *
      ∑ selected : Fin (L + 1), ∫⁻ z in B,
        dynamicTrajectoryIndexComponentKernel potential gradient ε mask hroot
          selected origin hpotential hgradient hmask z A ∂phaseBoltzmannTarget potential
  · apply Finset.sum_congr rfl
    intro origin horigin
    congr 1
    apply Finset.sum_congr rfl
    intro selected hselected
    exact dynamicTrajectoryIndexComponentKernel_balance hpotential hgradient ε mask hmask
      hroot hreroot hpair origin selected hA hB
  · simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]

/-- Detailed balance gives invariance of the certified dynamic transition. -/
theorem randomizedDynamicMultinomialKernel_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ} (mask : TrajectoryCandidateMask ι L)
    (hmask : MeasurableTrajectoryCandidateMask mask)
    (hroot : ∀ z origin, mask z origin origin = true)
    (hreroot : ∀ z origin selected, mask z origin selected = true →
      ∀ i, mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected i =
        mask z origin i)
    (hpair : ∀ z origin selected,
      mask (offsetLeapfrogTrajectory gradient ε origin z selected) selected origin =
        mask z origin selected) :
    (randomizedDynamicMultinomialKernel potential gradient ε mask hroot
      hpotential hgradient hmask).Invariant (phaseBoltzmannTarget potential) :=
  (randomizedDynamicMultinomialKernel_isReversible hpotential hgradient ε mask hmask
    hroot hreroot hpair).invariant

/-- The checked-row interface discharges all algebraic NUTS obligations.  Only
measurability of the concrete row builder remains an analytic input. -/
theorem CertifiedTrajectoryCandidateRows.randomizedKernel_invariant
    {potential : Position ι → ℝ} {gradient : Position ι → Position ι}
    (hpotential : Measurable potential) (hgradient : Measurable gradient)
    (ε : ℝ) {L : ℕ}
    (certificate : CertifiedTrajectoryCandidateRows gradient ε L)
    (hmask : MeasurableTrajectoryCandidateMask certificate.mask) :
    (randomizedDynamicMultinomialKernel potential gradient ε certificate.mask
      certificate.mask_root hpotential hgradient hmask).Invariant
        (phaseBoltzmannTarget potential) :=
  randomizedDynamicMultinomialKernel_invariant hpotential hgradient ε certificate.mask
    hmask certificate.mask_root certificate.mask_reroot certificate.mask_pair

end Mcmc.Hamiltonian
