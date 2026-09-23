import Mcmc.Kernel.ActiveSketchSMMALA

/-!
# Active-Sketch sMMALA concrete instantiation

A 2-dimensional identity-sketch example demonstrating `activeSketchMetric_posDef`.
The sketch `S(x)ₖᵢ = δₖᵢ` gives `SᵀS = I`, so `G(x) = I + λI = (1+λ)I`,
which is trivially positive definite for `λ > 0`.
-/

namespace Mcmc.Examples.ActiveSketchSMMALA

open Mcmc.Kernel

/-- Identity sketch for `Fin 2`: `S(x)ₖᵢ = δₖᵢ`. -/
noncomputable def exampleSketch : (Fin 2 → ℝ) → Fin 2 → Fin 2 → ℝ :=
  fun _x _k i => if i = _k then 1 else 0

theorem exampleMetric_posDef (reg : ℝ) (hreg : 0 < reg) (x : Fin 2 → ℝ) :
    (Matrix.of (activeSketchMetric exampleSketch reg x)).PosDef :=
  activeSketchMetric_posDef exampleSketch reg hreg x

end Mcmc.Examples.ActiveSketchSMMALA
