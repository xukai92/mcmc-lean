import Mcmc.Finite.MeasureKernel
import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Finite kernels as stochastic matrices

This file connects the elementary finite Markov-kernel interface to mathlib's
row-stochastic matrices.  Matrix-based dynamics can therefore reuse mathlib's
matrix powers, irreducibility, and primitivity infrastructure while the
one-step Metropolis--Hastings proof remains in the elementary finite layer.
-/

open scoped BigOperators ENNReal Matrix

namespace Mcmc.Finite
namespace MarkovKernel

variable {State : Type*} [Fintype State]

/-- The transition matrix underlying an elementary finite Markov kernel. -/
def toMatrix (P : MarkovKernel State) : Matrix State State ℝ :=
  P.prob

@[simp]
theorem toMatrix_apply (P : MarkovKernel State) (x y : State) :
    P.toMatrix x y = P.prob x y :=
  rfl

theorem toMatrix_mem_rowStochastic [DecidableEq State] (P : MarkovKernel State) :
    P.toMatrix ∈ Matrix.rowStochastic ℝ State := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  exact ⟨P.nonneg, P.sum_prob⟩

/-- An elementary finite kernel bundled as a mathlib row-stochastic matrix. -/
def toRowStochastic [DecidableEq State] (P : MarkovKernel State) :
    Matrix.rowStochastic ℝ State :=
  ⟨P.toMatrix, P.toMatrix_mem_rowStochastic⟩

@[simp]
theorem toRowStochastic_apply [DecidableEq State] (P : MarkovKernel State) (x y : State) :
    P.toRowStochastic.1 x y = P.prob x y :=
  rfl

/-- A mathlib row-stochastic matrix as an elementary finite Markov kernel. -/
def ofRowStochastic [DecidableEq State] (P : Matrix.rowStochastic ℝ State) :
    MarkovKernel State where
  prob := P.1
  nonneg _ _ := Matrix.nonneg_of_mem_rowStochastic P.property
  sum_prob x := Matrix.sum_row_of_mem_rowStochastic P.property x

@[simp]
theorem ofRowStochastic_apply [DecidableEq State] (P : Matrix.rowStochastic ℝ State)
    (x y : State) :
    (ofRowStochastic P).prob x y = P.1 x y :=
  rfl

@[simp]
theorem ofRowStochastic_toRowStochastic [DecidableEq State] (P : MarkovKernel State) :
    ofRowStochastic P.toRowStochastic = P := by
  cases P
  rfl

@[simp]
theorem toRowStochastic_ofRowStochastic [DecidableEq State]
    (P : Matrix.rowStochastic ℝ State) :
    (ofRowStochastic P).toRowStochastic = P := by
  apply Subtype.ext
  rfl

/-- Elementary finite Markov kernels are equivalent to mathlib row-stochastic
matrices over the reals. -/
def equivRowStochastic [DecidableEq State] :
    MarkovKernel State ≃ Matrix.rowStochastic ℝ State where
  toFun := toRowStochastic
  invFun := ofRowStochastic
  left_inv := fun P => ofRowStochastic_toRowStochastic (State := State) P
  right_inv := fun P => toRowStochastic_ofRowStochastic (State := State) P

/-- Local stationarity is exactly the usual stationary row-vector equation. -/
theorem stationary_iff_vecMul [DecidableEq State] (P : MarkovKernel State)
    (π : Distribution State) :
    P.Stationary π ↔ π.mass ᵥ* P.toMatrix = π.mass := by
  simp only [Stationary, Matrix.vecMul, dotProduct, toMatrix, funext_iff]

/-- The matrix and measure-kernel views agree on every one-step transition. -/
theorem toMeasureKernel_apply_singleton_eq_toMatrix [MeasurableSpace State]
    [MeasurableSingletonClass State] (P : MarkovKernel State) (x y : State) :
    P.toMeasureKernel x {y} = ENNReal.ofReal (P.toMatrix x y) := by
  simpa only [toMatrix_apply] using P.toMeasureKernel_apply_singleton x y

end MarkovKernel
end Mcmc.Finite
