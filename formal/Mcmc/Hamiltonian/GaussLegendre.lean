import Mcmc.Hamiltonian.ParallelIntegrators

/-!
# Two-stage Gauss--Legendre integration

This file records the exact two-stage collocation equations, verifies their
symplectic Runge--Kutta coefficient identity, and proves the algebra underlying
time reversal. A runtime nonlinear solver must still certify the stage
equations (or use a defined fallback); a residual tolerance alone is not this
exact mathematical method.
-/

namespace Mcmc.Hamiltonian.GaussLegendre

noncomputable section

def radius : ℝ := Real.sqrt 3 / 6
def a11 : ℝ := 1 / 4
def a12 : ℝ := 1 / 4 - radius
def a21 : ℝ := 1 / 4 + radius
def a22 : ℝ := 1 / 4
def b1 : ℝ := 1 / 2
def b2 : ℝ := 1 / 2

/-- The Butcher coefficients satisfy the Runge--Kutta symplecticity equations
`bᵢ aᵢⱼ + bⱼ aⱼᵢ = bᵢ bⱼ`. -/
theorem symplectic_coefficients (i j : Fin 2) :
    let a : Fin 2 → Fin 2 → ℝ := fun i j =>
      if i = 0 then (if j = 0 then a11 else a12)
      else (if j = 0 then a21 else a22)
    let b : Fin 2 → ℝ := fun _ => 1 / 2
    b i * a i j + b j * a j i = b i * b j := by
  fin_cases i <;> fin_cases j <;>
    simp [a11, a12, a21, a22, radius] <;> ring

abbrev State (n : ℕ) := Fin n → ℝ

/-- Exact stage witness for one two-stage Gauss--Legendre step. -/
structure Stages {n : ℕ} (field : State n → State n)
    (stepSize : ℝ) (initial : State n) where
  first : State n
  second : State n
  first_eq : first = field (initial + stepSize • (a11 • first + a12 • second))
  second_eq : second = field (initial + stepSize • (a21 • first + a22 • second))

def endpoint {n : ℕ} {field : State n → State n} {stepSize : ℝ}
    {initial : State n} (stages : Stages field stepSize initial) : State n :=
  initial + stepSize • (b1 • stages.first + b2 • stages.second)

/-- Reversing a step swaps its two collocation stages. -/
def reverseStages {n : ℕ} {field : State n → State n} {stepSize : ℝ}
    {initial : State n} (stages : Stages field stepSize initial) :
    Stages field (-stepSize) (endpoint stages) := by
  refine ⟨stages.second, stages.first, ?_, ?_⟩
  · calc
      stages.second = field
          (initial + stepSize • (a21 • stages.first + a22 • stages.second)) :=
        stages.second_eq
      _ = field (endpoint stages + (-stepSize) •
          (a11 • stages.second + a12 • stages.first)) := by
        congr 1
        funext i
        simp [endpoint, a11, a12, a21, a22, b1, b2, radius]
        ring
  · calc
      stages.first = field
          (initial + stepSize • (a11 • stages.first + a12 • stages.second)) :=
        stages.first_eq
      _ = field (endpoint stages + (-stepSize) •
          (a21 • stages.second + a22 • stages.first)) := by
        congr 1
        funext i
        simp [endpoint, a11, a12, a21, a22, b1, b2, radius]
        ring

theorem reverse_endpoint {n : ℕ} {field : State n → State n} {stepSize : ℝ}
    {initial : State n} (stages : Stages field stepSize initial) :
    endpoint (reverseStages stages) = initial := by
  funext i
  simp [endpoint, reverseStages, b1, b2]
  ring

/-- An exact stage solver. Uniqueness makes the reverse solve choose the
swapped witness constructed by `reverseStages`; it is an explicit obligation,
not an assumption hidden in a residual tolerance. -/
structure ExactStageSolver {n : ℕ} (field : State n → State n) where
  solve : (stepSize : ℝ) → (initial : State n) → Stages field stepSize initial
  unique : ∀ {stepSize initial} (candidate : Stages field stepSize initial),
    candidate.first = (solve stepSize initial).first ∧
      candidate.second = (solve stepSize initial).second

def exactStep {n : ℕ} {field : State n → State n}
    (solver : ExactStageSolver field) (stepSize : ℝ) (initial : State n) :
    State n :=
  endpoint (solver.solve stepSize initial)

theorem endpoint_eq_of_stage_eq {n : ℕ} {field : State n → State n}
    {stepSize : ℝ} {initial : State n}
    {left right : Stages field stepSize initial}
    (hfirst : left.first = right.first)
    (hsecond : left.second = right.second) :
    endpoint left = endpoint right := by
  simp [endpoint, hfirst, hsecond]

/-- Exact GL2 with a unique stage solution is self-adjoint: a negative step
from the endpoint returns to the initial state. -/
theorem exactStep_neg_comp {n : ℕ} {field : State n → State n}
    (solver : ExactStageSolver field) (stepSize : ℝ) (initial : State n) :
    exactStep solver (-stepSize) (exactStep solver stepSize initial) = initial := by
  let forward := solver.solve stepSize initial
  have selected := solver.unique (reverseStages forward)
  calc
    exactStep solver (-stepSize) (exactStep solver stepSize initial) =
        endpoint (reverseStages forward) := by
      apply endpoint_eq_of_stage_eq
      · exact selected.1.symm
      · exact selected.2.symm
    _ = initial := reverse_endpoint forward

end

end Mcmc.Hamiltonian.GaussLegendre
