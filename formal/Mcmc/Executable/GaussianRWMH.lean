import Mcmc.Executable.IR
import Mcmc.Kernel.RandomWalkMetropolisHastings

/-!
# Executable Gaussian RWMH boundary

This module connects the first real-valued IR program to the exact Gaussian
proposal measure.  Acceptance is kept as the next explicit boundary: a target
log-density must first be represented in the pure expression language before
the complete proposal/accept/reject program can be emitted.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Executable

open ProbabilityTheory
open IR

/-- Pure body of the standard-Gaussian proposal program. -/
def standardGaussianProposalBody (current : ℝ) : Program [.real] .real :=
  .ret (.add (.real current) (.var .here))

/-- Draw ideal standard-normal noise and translate it by the current scalar
state. This is inspectable syntax, not an embedded Lean sampling function. -/
def standardGaussianProposalProgram (current : ℝ) : Program [] .real :=
  .sample .standardNormal (standardGaussianProposalBody current)

@[simp]
theorem standardGaussianProposalProgram_replay (current noise : ℝ)
    (rest : List Event) :
    Program.replay (standardGaussianProposalProgram current) PUnit.unit
        (Event.standardNormal noise :: rest) =
      .ok ⟨current + noise, rest⟩ :=
  rfl

/-- Translating the ideal standard-normal primitive gives the exact Gaussian
proposal measure with mean at the current state. -/
theorem map_standardNormalMeasure_add (current : ℝ) :
    standardNormalMeasure.map (fun noise => current + noise) =
      gaussianReal current 1 := by
  rw [standardNormalMeasure, gaussianReal_map_const_add]
  simp

/-- The kernel interpretation of the proposal syntax has that translated
Gaussian law. -/
theorem standardGaussianProposalProgram_measure (current : ℝ) :
    (standardGaussianProposalProgram current).measure = gaussianReal current 1 := by
  letI : IsProbabilityMeasure Prim.standardNormal.measure :=
    Prim.isProbabilityMeasure .standardNormal
  letI : IsMarkovKernel (standardGaussianProposalBody current).kernel :=
    (standardGaussianProposalBody current).isMarkovKernel
  rw [← map_standardNormalMeasure_add current]
  ext set hset
  rw [Program.measure, standardGaussianProposalProgram, Program.kernel,
    Kernel.snd_apply' _ _ hset,
    Kernel.compProd_apply (measurable_snd hset)]
  simp [standardGaussianProposalBody, Prim.measure, standardNormalMeasure, Program.kernel,
    Kernel.comap_apply, Kernel.deterministic_apply]
  rw [Measure.map_apply (by fun_prop) hset]
  change (∫⁻ noise : ℝ,
    ((fun value : ℝ => current + value) ⁻¹' set).indicator 1 noise
      ∂gaussianReal 0 1) = _
  rw [lintegral_indicator_one]
  exact hset.preimage (by fun_prop)

/-- The proposal row used by the existing density-based RWMH kernel is the
same translated Gaussian measure. -/
theorem scalarStandardGaussianProposal_row (current : ℝ) :
    Mcmc.Kernel.densityProposal volume
        (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 1)) current =
      gaussianReal current 1 := by
  ext set hset
  rw [Mcmc.Kernel.densityProposal_apply volume
    (Mcmc.Kernel.measurable_uncurry_randomWalkProposalDensity
      (measurable_gaussianPDF 0 1)) current hset]
  rw [gaussianReal_apply current (by norm_num) set]
  apply setLIntegral_congr_fun hset
  intro value _
  simp only [Mcmc.Kernel.randomWalkProposalDensity, gaussianPDF]
  rw [gaussianPDFReal_sub]
  simp

/-- Proposal-level refinement theorem: the IR program and the proposal row of
the verified standard-Gaussian RWMH kernel denote exactly the same measure. -/
theorem standardGaussianProposalProgram_refines_rwmh (current : ℝ) :
    (standardGaussianProposalProgram current).measure =
      Mcmc.Kernel.densityProposal volume
        (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 1)) current := by
  rw [standardGaussianProposalProgram_measure,
    scalarStandardGaussianProposal_row]

/-- Real acceptance threshold for unit-variance Gaussian RWMH targeting the
unnormalized standard-Gaussian weight. -/
noncomputable def standardGaussianAcceptance (current proposed : ℝ) : ℝ :=
  Real.exp (min 0 ((current * current - proposed * proposed) * (1 / 2)))

theorem standardGaussianAcceptance_pos (current proposed : ℝ) :
    0 < standardGaussianAcceptance current proposed := by
  exact Real.exp_pos _

theorem standardGaussianAcceptance_le_one (current proposed : ℝ) :
    standardGaussianAcceptance current proposed ≤ 1 := by
  rw [standardGaussianAcceptance, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (min_le_left _ _)

/-- Exact unit-uniform accept/reject integral. -/
theorem lintegral_unitUniform_acceptReject (a proposed current : ℝ)
    (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) (set : Set ℝ) :
    (∫⁻ uniform, set.indicator 1
        (if uniform < a then proposed else current) ∂unitUniform) =
      ENNReal.ofReal a * set.indicator 1 proposed +
        (1 - ENNReal.ofReal a) * set.indicator 1 current := by
  classical
  by_cases hproposed : proposed ∈ set
  · by_cases hcurrent : current ∈ set
    · have hfun : (fun uniform : ℝ => set.indicator 1
          (if uniform < a then proposed else current)) =
          (fun _ : ℝ => (1 : ENNReal)) := by
        funext uniform
        by_cases hu : uniform < a <;>
          simp [Set.indicator, hu, hproposed, hcurrent]
      rw [hfun]
      have haenn : ENNReal.ofReal a ≤ 1 := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha1
      simp only [lintegral_one, measure_univ, Set.indicator_of_mem hproposed,
        Set.indicator_of_mem hcurrent, Pi.one_apply, mul_one]
      exact (add_tsub_cancel_of_le haenn).symm
    · have hfun : (fun uniform : ℝ => set.indicator 1
          (if uniform < a then proposed else current)) =
          (Set.Iio a).indicator (fun _ : ℝ => (1 : ENNReal)) := by
        funext uniform
        by_cases hu : uniform < a <;>
          simp [Set.indicator, hu, hproposed, hcurrent]
      rw [hfun, lintegral_indicator_fun_one measurableSet_Iio,
        unitUniform_Iio ha1]
      simp [Set.indicator, hproposed, hcurrent]
  · by_cases hcurrent : current ∈ set
    · have hfun : (fun uniform : ℝ => set.indicator 1
          (if uniform < a then proposed else current)) =
          (Set.Iio a)ᶜ.indicator (fun _ : ℝ => (1 : ENNReal)) := by
        funext uniform
        by_cases hu : uniform < a <;>
          simp [Set.indicator, hu, hproposed, hcurrent]
      rw [hfun, lintegral_indicator_fun_one measurableSet_Iio.compl]
      rw [measure_compl measurableSet_Iio (measure_ne_top unitUniform (Set.Iio a))]
      rw [unitUniform_Iio ha1]
      simp [Set.indicator, hproposed, hcurrent]
    · have hfun : (fun uniform : ℝ => set.indicator 1
          (if uniform < a then proposed else current)) =
          (fun _ : ℝ => (0 : ENNReal)) := by
        funext uniform
        by_cases hu : uniform < a <;>
          simp [Set.indicator, hu, hproposed, hcurrent]
      rw [hfun]
      simp [Set.indicator, hproposed, hcurrent]

/-- Unnormalized standard-Gaussian target weight used by the exact RWMH
kernel. -/
noncomputable def standardGaussianWeight (value : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(value * value) / 2))

theorem measurable_standardGaussianWeight : Measurable standardGaussianWeight := by
  unfold standardGaussianWeight
  fun_prop

theorem standardGaussianWeight_ne_zero (value : ℝ) :
    standardGaussianWeight value ≠ 0 := by
  simp [standardGaussianWeight, ENNReal.ofReal_eq_zero, Real.exp_pos]

theorem standardGaussianWeight_ne_top (value : ℝ) :
    standardGaussianWeight value ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- The real threshold used by the IR is exactly the zero-safe density
acceptance probability of the existing RWMH construction. -/
theorem ofReal_standardGaussianAcceptance_eq_densityAcceptance
    (current proposed : ℝ) :
    ENNReal.ofReal (standardGaussianAcceptance current proposed) =
      Mcmc.Kernel.densityAcceptance standardGaussianWeight
        (Mcmc.Kernel.randomWalkProposalDensity (gaussianPDF 0 1))
        current proposed := by
  rw [Mcmc.Kernel.randomWalk_densityAcceptance_eq_min_weight_div
    standardGaussianWeight (gaussianPDF 0 1)
    (fun z => by
      simp [gaussianPDF, gaussianPDFReal])
    standardGaussianWeight_ne_zero
    (fun z => (gaussianPDF_pos 0 (by norm_num) z).ne')
    (fun _ => gaussianPDF_ne_top)]
  rw [standardGaussianWeight, standardGaussianWeight]
  rw [← ENNReal.ofReal_min]
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
  apply congrArg ENNReal.ofReal
  unfold standardGaussianAcceptance
  let currentExponent : ℝ := -(current * current) / 2
  let proposedExponent : ℝ := -(proposed * proposed) / 2
  have hratio :
      (current * current - proposed * proposed) * (1 / 2) =
        proposedExponent - currentExponent := by
    dsimp [currentExponent, proposedExponent]
    ring
  rw [hratio]
  by_cases horder : currentExponent ≤ proposedExponent
  · have hexp : Real.exp currentExponent ≤ Real.exp proposedExponent :=
      Real.exp_le_exp.mpr horder
    rw [min_eq_left (sub_nonneg.mpr horder), Real.exp_zero,
      min_eq_left hexp, div_self (Real.exp_ne_zero _)]
  · have hreverse : proposedExponent ≤ currentExponent := le_of_not_ge horder
    have hexp : Real.exp proposedExponent ≤ Real.exp currentExponent :=
      Real.exp_le_exp.mpr hreverse
    rw [min_eq_right (sub_nonpos.mpr hreverse), min_eq_right hexp,
      Real.exp_sub]

/-- Body after proposal noise and the proposed position have been bound. -/
noncomputable def standardGaussianRwmhAcceptBody (current : ℝ) : Program
    [.real, .real, .real] .real :=
  let uniform : Expr [.real, .real, .real] .real := .var .here
  let proposed : Expr [.real, .real, .real] .real := .var (.there .here)
  let logRatio := .mul
    (.sub (.mul (.real current) (.real current)) (.mul proposed proposed))
    (.real (1 / 2))
  let threshold := .exp (.min (.real 0) logRatio)
  .ret (.ite (.lt uniform threshold) proposed (.real current))

/-- Complete ideal-real standard-Gaussian RWMH syntax for a standard-Gaussian
target. The first draw is proposal noise and the second is the MH uniform. -/
noncomputable def standardGaussianRwmhAfterProposal (current : ℝ) :
    Program [.real, .real] .real :=
  .sample .uniformUnit (standardGaussianRwmhAcceptBody current)

noncomputable def standardGaussianRwmhAfterNoise (current : ℝ) :
    Program [.real] .real :=
  .letE (.add (.real current) (.var .here))
    (standardGaussianRwmhAfterProposal current)

noncomputable def standardGaussianRwmhProgram (current : ℝ) : Program [] .real :=
  .sample .standardNormal (standardGaussianRwmhAfterNoise current)

/-- Trace-level behavior of the complete program. -/
theorem standardGaussianRwmhProgram_replay (current noise uniform : ℝ)
    (hunit : 0 ≤ uniform ∧ uniform < 1) (rest : List Event) :
    Program.replay (standardGaussianRwmhProgram current) PUnit.unit
        (Event.standardNormal noise :: Event.uniformUnit uniform :: rest) =
      .ok ⟨if uniform < standardGaussianAcceptance current (current + noise)
        then current + noise else current, rest⟩ := by
  simp [standardGaussianRwmhProgram, standardGaussianRwmhAcceptBody,
    standardGaussianRwmhAfterNoise, standardGaussianRwmhAfterProposal,
    Program.replay, Prim.replay, hunit, Expr.eval, Var.get,
    standardGaussianAcceptance]

/-- The existing exact scalar standard-Gaussian RWMH kernel specialized to
the same target and unit-variance proposal as the IR program. -/
noncomputable def scalarStandardGaussianRwmhKernel : Kernel ℝ ℝ :=
  Mcmc.Kernel.randomWalkMetropolisHastings volume standardGaussianWeight
    (gaussianPDF 0 1) (measurable_gaussianPDF 0 1)
    (lintegral_gaussianPDF_eq_one 0 (by norm_num))

/-- The density representation consumed by scalar Gaussian RWMH is exactly
the ideal standard-normal primitive law. -/
theorem standardNormalMeasure_eq_rwmh_noise :
    standardNormalMeasure =
      volume.withDensity (gaussianPDF 0 1) :=
  standardNormalMeasure_eq_withDensity

end Mcmc.Executable
