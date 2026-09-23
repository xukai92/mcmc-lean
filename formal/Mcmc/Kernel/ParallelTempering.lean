import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mcmc.Kernel.MetropolisHastings
import Mcmc.Kernel.DetailedBalance
import Mcmc.Kernel.DeterministicMetropolis

/-!
# General-state K-temperature parallel tempering

This module formalizes the kernel theory for parallel tempering (replica exchange)
MCMC with an arbitrary number K of temperature levels in the general
(measure-theoretic) setting.

## Main definitions

* `productTarget`: K-fold product target measure via `Measure.pi`
* `swapCoord`: coordinate swap via composition with `Equiv.swap`
* `productWeight`: product of per-coordinate density weights
* `pairSwapKernel`: deterministic Metropolis kernel for adjacent coordinate swap
* `liftCoord`: lift a single-coordinate kernel to the product space
* `withinTemp`: sequential within-temperature updates
* `evenSwapKernel` / `oddSwapKernel`: compose pair swaps for even/odd rounds
* `seoSwapKernel`: 50-50 mixture of even and odd swap kernels
* `seoKernel` / `deoKernel`: stochastic and deterministic even-odd compositions

## Main results

* `swapCoord_involutive`: swapping twice returns to the original
* `measurable_swapCoord`: the coordinate swap is measurable
* `swapCoord_measurePreserving`: swap preserves the uniform product reference
* `pairSwapKernel_isReversible`: pair swap satisfies detailed balance (Theorem 2)
* `cold_marginal`: first coordinate marginal recovers π₁

## Roadmap

* **Within-temperature invariance**: if each Kᵢ preserves πᵢ, the
  within-temperature composition preserves the product target.

* **SEO/DEO invariance**: follows from within-temperature invariance and
  pair swap invariance via `Kernel.Invariant.comp`.

* **SEO reversibility**: the stochastic swap (convex combination of reversible
  kernels) is reversible via `isReversible_add`, but composition with
  within-temperature updates requires separate treatment.

* **DEO non-reversibility**: DEO is NOT reversible for K ≥ 3 in general.
  The deterministic even→odd ordering creates directed flow (Syed et al. 2022).

* **Pi-withDensity identity**: the bridge
  `Measure.pi (fun k => μ.withDensity (f k)) =
    (Measure.pi (fun _ => μ)).withDensity (fun x => ∏ k, f k (x k))`
  connects `productTarget` to `productDensityTarget`.

## References

* Syed, S., Bouchard-Côté, A., Deligiannidis, G., & Doucet, A. (2022).
  Non-reversible parallel tempering: A scalable highly parallel MCMC scheme.
  *JRSS-B*, 84(2), 321-350.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace Mcmc.Kernel.ParallelTempering

variable {S : Type*} [MeasurableSpace S]
variable {K : ℕ}

/-! ### Product target and weight -/

/-- Product target for K temperatures: Π = π₁ ⊗ ... ⊗ πₖ. -/
noncomputable def productTarget (π : Fin K → Measure S) :
    Measure (Fin K → S) :=
  Measure.pi π

/-- Product of per-coordinate density weights. -/
noncomputable def productWeight (weight : Fin K → S → ENNReal)
    (x : Fin K → S) : ENNReal :=
  ∏ k : Fin K, weight k (x k)

/-- Product density target as withDensity on the uniform product reference.
This form connects directly to the deterministic Metropolis reversibility
theorem. -/
noncomputable def productDensityTarget (reference : Measure S)
    (weight : Fin K → S → ENNReal) : Measure (Fin K → S) :=
  (Measure.pi (fun _ : Fin K => reference)).withDensity (productWeight weight)

/-! ### Coordinate swap -/

/-- Swap coordinates i and j in the product state by composing with
`Equiv.swap`. When i = j this is the identity. -/
def swapCoord (i j : Fin K) (x : Fin K → S) : Fin K → S :=
  x ∘ Equiv.swap i j

/-! ### Elementary properties -/

omit [MeasurableSpace S] in
/-- Swapping coordinates i and j twice returns to the original state. -/
theorem swapCoord_involutive (i j : Fin K) :
    Function.Involutive (swapCoord (S := S) (K := K) i j) := by
  intro x; ext k
  simp [swapCoord, Function.comp, Equiv.swap_apply_self]

/-- The coordinate swap is measurable. -/
theorem measurable_swapCoord (i j : Fin K) :
    Measurable (swapCoord (S := S) (K := K) i j) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (Equiv.swap i j k)

/-- The product weight function is measurable. -/
theorem measurable_productWeight
    {weight : Fin K → S → ENNReal}
    (hweight : ∀ k, Measurable (weight k)) :
    Measurable (productWeight weight) :=
  Finset.measurable_prod _ fun k _ => (hweight k).comp (measurable_pi_apply k)

omit [MeasurableSpace S] in
/-- The product weight is nonzero when each coordinate weight is. -/
theorem productWeight_pos
    {weight : Fin K → S → ENNReal}
    (hpos : ∀ x : Fin K → S, ∀ k, weight k (x k) ≠ 0)
    (x : Fin K → S) :
    productWeight weight x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => hpos x k

omit [MeasurableSpace S] in
/-- The product weight is finite when each coordinate weight is. -/
theorem productWeight_ne_top
    {weight : Fin K → S → ENNReal}
    (hfin : ∀ x : Fin K → S, ∀ k, weight k (x k) ≠ ⊤)
    (x : Fin K → S) :
    productWeight weight x ≠ ⊤ :=
  (ENNReal.prod_lt_top fun k _ => lt_top_iff_ne_top.mpr (hfin x k)).ne

/-! ### Measure preservation -/

omit [MeasurableSpace S] in
/-- Preimage of a univ-pi set under `swapCoord` is a univ-pi set with
permuted index sets. -/
theorem swapCoord_preimage_pi (i j : Fin K) (s : Fin K → Set S) :
    swapCoord i j ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (s ∘ Equiv.swap i j) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    swapCoord, Function.comp]
  constructor
  · intro h k
    simpa [Equiv.swap_apply_self] using h (Equiv.swap i j k)
  · intro h k
    simpa [Equiv.swap_apply_self] using h (Equiv.swap i j k)

/-- Swapping coordinates preserves the uniform product reference measure. -/
theorem swapCoord_measurePreserving (i j : Fin K)
    (μ : Measure S) [SigmaFinite μ] :
    MeasurePreserving (swapCoord i j)
      (Measure.pi (fun _ : Fin K => μ))
      (Measure.pi (fun _ : Fin K => μ)) := by
  refine ⟨measurable_swapCoord i j, ?_⟩
  symm; apply Measure.pi_eq; intro s hs
  rw [Measure.map_apply (measurable_swapCoord i j)
        (.pi Set.countable_univ fun k _ => hs k),
      swapCoord_preimage_pi]
  change (Measure.pi fun _ : Fin K => μ)
    (Set.pi Set.univ fun k => s (Equiv.swap i j k)) = _
  rw [Measure.pi_pi]
  exact Equiv.prod_comp (Equiv.swap i j) (fun k => μ (s k))

/-! ### Pair swap kernel -/

/-- Pairwise swap kernel for adjacent temperatures (i, i+1).
Applies the deterministic Metropolis construction: propose swapping
coordinates i and i+1, accept with the standard min-ratio criterion
using the product weight. -/
noncomputable def pairSwapKernel
    (weight : Fin K → S → ENNReal)
    (i : Fin K) (hi : i.val + 1 < K) :
    Kernel (Fin K → S) (Fin K → S) :=
  let j : Fin K := ⟨i.val + 1, hi⟩
  deterministicMetropolis (productWeight weight) (swapCoord i j)
    (measurable_swapCoord i j)

/-- The pair swap kernel is a Markov kernel. -/
theorem pairSwapKernel_isMarkov
    {weight : Fin K → S → ENNReal}
    (hweight : ∀ k, Measurable (weight k))
    (i : Fin K) (hi : i.val + 1 < K) :
    IsMarkovKernel (pairSwapKernel weight i hi) :=
  deterministicMetropolis_isMarkov (productWeight weight)
    (swapCoord i ⟨i.val + 1, hi⟩) (measurable_productWeight hweight)
    (measurable_swapCoord i ⟨i.val + 1, hi⟩)

/-- The pairwise swap kernel for adjacent temperatures (i, i+1) satisfies
detailed balance w.r.t. the product density target.

The swap proposal is a deterministic transposition (an involution) preserving
the product reference measure, so the symmetric-flow acceptance criterion
yields detailed balance via `deterministicMetropolis_isReversible`. -/
theorem pairSwapKernel_isReversible
    (reference : Measure S) [SigmaFinite reference]
    {weight : Fin K → S → ENNReal}
    (hweight : ∀ k, Measurable (weight k))
    (i : Fin K) (hi : i.val + 1 < K)
    (hpos : ∀ x : Fin K → S, ∀ k, weight k (x k) ≠ 0)
    (hfin : ∀ x : Fin K → S, ∀ k, weight k (x k) ≠ ⊤) :
    (pairSwapKernel weight i hi).IsReversible
      (productDensityTarget reference weight) := by
  let j : Fin K := ⟨i.val + 1, hi⟩
  show (deterministicMetropolis (productWeight weight) (swapCoord i j)
    (measurable_swapCoord i j)).IsReversible
      ((Measure.pi (fun _ : Fin K => reference)).withDensity (productWeight weight))
  exact deterministicMetropolis_isReversible
    (Measure.pi (fun _ : Fin K => reference))
    (productWeight weight) (swapCoord i j) (measurable_swapCoord i j)
    (measurable_productWeight hweight)
    (productWeight_pos hpos) (productWeight_ne_top hfin)
    (swapCoord_involutive i j)
    (swapCoord_measurePreserving i j reference)

/-- The pairwise swap kernel preserves the product density target. -/
theorem pairSwapKernel_invariant
    (reference : Measure S) [SigmaFinite reference]
    {weight : Fin K → S → ENNReal}
    (hweight : ∀ k, Measurable (weight k))
    (i : Fin K) (hi : i.val + 1 < K)
    (hpos : ∀ x : Fin K → S, ∀ k, weight k (x k) ≠ 0)
    (hfin : ∀ x : Fin K → S, ∀ k, weight k (x k) ≠ ⊤) :
    (pairSwapKernel weight i hi).Invariant
      (productDensityTarget reference weight) := by
  letI := pairSwapKernel_isMarkov hweight i hi
  exact (pairSwapKernel_isReversible reference hweight i hi hpos hfin).invariant

/-! ### Lifted single-coordinate kernel -/

/-- Within-temperature exploration: apply kernel κ to coordinate i,
leaving all other coordinates unchanged. -/
noncomputable def liftCoord (i : Fin K)
    (κ : Kernel S S) [IsSFiniteKernel κ] :
    Kernel (Fin K → S) (Fin K → S) where
  toFun x := (κ (x i)).map (Function.update x i)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    let κ' := κ.comap (fun z : Fin K → S => z i) (measurable_pi_apply i)
    have step : ∀ x, ((κ (x i)).map (Function.update x i)) s =
        ∫⁻ y, s.indicator 1 (Function.update x i y) ∂κ' x := by
      intro x
      rw [Measure.map_apply (measurable_update x) hs]
      change κ (x i) (Function.update x i ⁻¹' s) =
        ∫⁻ y, s.indicator 1 (Function.update x i y) ∂κ (x i)
      rw [← lintegral_indicator_one (hs.preimage (measurable_update x))]
      refine lintegral_congr fun y => ?_
      by_cases h : Function.update x i y ∈ s
      · rw [Set.indicator_of_mem (Set.mem_preimage.mpr h), Set.indicator_of_mem h,
            Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem (mt Set.mem_preimage.mp h), Set.indicator_of_notMem h]
    simp_rw [step]
    exact ((measurable_one.indicator hs).comp measurable_update').lintegral_kernel_prod_right'

/-- Sequential within-temperature updates across all K temperatures. -/
noncomputable def withinTemp
    (kernels : Fin K → Kernel S S) [∀ k, IsSFiniteKernel (kernels k)] :
    Kernel (Fin K → S) (Fin K → S) :=
  (List.finRange K).foldr (fun k acc => liftCoord k (kernels k) ∘ₖ acc) Kernel.id

/-! ### Even and odd swap kernels -/

/-- Compose all even-pair swap kernels (pairs (0,1), (2,3), ...).
Non-overlapping pairs commute, so sequential composition equals parallel. -/
noncomputable def evenSwapKernel
    (weight : Fin K → S → ENNReal) :
    Kernel (Fin K → S) (Fin K → S) :=
  (List.finRange K).foldr
    (fun i acc =>
      if h : i.val % 2 = 0 ∧ i.val + 1 < K
      then pairSwapKernel weight i h.2 ∘ₖ acc
      else acc)
    Kernel.id

/-- Compose all odd-pair swap kernels (pairs (1,2), (3,4), ...). -/
noncomputable def oddSwapKernel
    (weight : Fin K → S → ENNReal) :
    Kernel (Fin K → S) (Fin K → S) :=
  (List.finRange K).foldr
    (fun i acc =>
      if h : i.val % 2 = 1 ∧ i.val + 1 < K
      then pairSwapKernel weight i h.2 ∘ₖ acc
      else acc)
    Kernel.id

/-- Even pair starting indices: {i : Fin K | i.val % 2 = 0 ∧ i.val + 1 < K}. -/
def evenPairIndices : List (Fin K) :=
  (List.finRange K).filter fun i => decide (i.val % 2 = 0 ∧ i.val + 1 < K)

/-- Odd pair starting indices: {i : Fin K | i.val % 2 = 1 ∧ i.val + 1 < K}. -/
def oddPairIndices : List (Fin K) :=
  (List.finRange K).filter fun i => decide (i.val % 2 = 1 ∧ i.val + 1 < K)

/-! ### SEO and DEO kernels -/

/-- Stochastic even-odd swap kernel: 50-50 mixture of even and odd swap
rounds. The mixture is a convex combination at the measure level. -/
noncomputable def seoSwapKernel
    (weight : Fin K → S → ENNReal) :
    Kernel (Fin K → S) (Fin K → S) where
  toFun x :=
    (1 / 2 : ENNReal) • evenSwapKernel weight x +
    (1 / 2 : ENNReal) • oddSwapKernel weight x
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    show Measurable fun x =>
      ((1 / 2 : ENNReal) • evenSwapKernel weight x +
       (1 / 2 : ENNReal) • oddSwapKernel weight x) s
    simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    exact (measurable_const.mul ((evenSwapKernel weight).measurable_coe hs)).add
      (measurable_const.mul ((oddSwapKernel weight).measurable_coe hs))

/-- SEO (Stochastic Even-Odd) kernel: 50-50 mixture of even and odd swap
rounds, composed with within-temperature updates. -/
noncomputable def seoKernel
    (weight : Fin K → S → ENNReal)
    (kernels : Fin K → Kernel S S) [∀ k, IsSFiniteKernel (kernels k)] :
    Kernel (Fin K → S) (Fin K → S) :=
  seoSwapKernel weight ∘ₖ withinTemp kernels

/-- DEO (Deterministic Even-Odd) kernel: even-swap → odd-swap in fixed
order, composed with within-temperature updates. -/
noncomputable def deoKernel
    (weight : Fin K → S → ENNReal)
    (kernels : Fin K → Kernel S S) [∀ k, IsSFiniteKernel (kernels k)] :
    Kernel (Fin K → S) (Fin K → S) :=
  oddSwapKernel weight ∘ₖ (evenSwapKernel weight ∘ₖ withinTemp kernels)

/-! ### Cold marginal -/

/-- The first coordinate marginal of the product target recovers the
cold-temperature target π₁. -/
theorem cold_marginal
    (π : Fin K → Measure S) (h0 : 0 < K)
    [∀ k, SigmaFinite (π k)]
    [∀ k, IsProbabilityMeasure (π k)] :
    (productTarget π).map (· ⟨0, h0⟩) = π ⟨0, h0⟩ := by
  classical
  change (Measure.pi π).map (Function.eval ⟨0, h0⟩) = π ⟨0, h0⟩
  rw [Measure.pi_map_eval,
    show ∏ j ∈ Finset.univ.erase ⟨0, h0⟩, π j Set.univ = 1 from
      Finset.prod_eq_one fun _ _ => measure_univ,
    one_smul]

end Mcmc.Kernel.ParallelTempering
