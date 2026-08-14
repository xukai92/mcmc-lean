/-!
# Backend-neutral typed finite command IR

This IR describes finite sampler control flow without Julia syntax or indexing
conventions. Array indices are zero-based, matching Lean `Fin` values and trace
semantics. Backends are responsible for lowering that convention explicitly.
-/

namespace Mcmc.Executable.Finite.CompilerIR

inductive Ty where
  | source | nat | bool | natVector | natMatrix

structure Var (type : Ty) where
  name : String

inductive Expr : Ty → Type
  | var (value : Var type) : Expr type
  | nat (value : Nat) : Expr .nat
  | vector (values : List Nat) : Expr .natVector
  | matrix (rows : List (List Nat)) : Expr .natMatrix
  | add (left right : Expr .nat) : Expr .nat
  | sub (left right : Expr .nat) : Expr .nat
  | mul (left right : Expr .nat) : Expr .nat
  | min (left right : Expr .nat) : Expr .nat
  | length (value : Expr .natVector) : Expr .nat
  | rowCount (value : Expr .natMatrix) : Expr .nat
  | total (value : Expr .natVector) : Expr .nat
  | index (value : Expr .natVector) (index : Expr .nat) : Expr .nat
  | row (value : Expr .natMatrix) (index : Expr .nat) : Expr .natVector
  | lt (left right : Expr .nat) : Expr .bool
  | le (left right : Expr .nat) : Expr .bool
  | eq (left right : Expr .nat) : Expr .bool
  | and (left right : Expr .bool) : Expr .bool
  | allNonnegative (value : Expr .natVector) : Expr .bool
  | allPositive (value : Expr .natVector) : Expr .bool
  | allRowsLength (value : Expr .natMatrix) (size : Expr .nat) : Expr .bool
  | allRowsNonnegativePositive (value : Expr .natMatrix) : Expr .bool
  | toExactVector (value : Expr .natVector) : Expr .natVector
  | toExactMatrix (value : Expr .natMatrix) : Expr .natMatrix
  | categorical (source : Expr .source) (weights : Expr .natVector) : Expr .nat

inductive Failure where
  | argument (message : String)
  | dimension (message : String)
  | internal (message : String)

inductive Stmt where
  | letE (destination : Var type) (value : Expr type)
  | guard (condition : Expr .bool) (failure : Failure)
  | drawBelow (destination : Var .nat) (source : Expr .source) (upper : Expr .nat)
  | forVector (index weight : Var .nat) (vector : Var .natVector) (body : List Stmt)
  | ifThen (condition : Expr .bool) (body : List Stmt)
  | subtractAssign (destination : Var .nat) (value : Expr .nat)
  | return (value : Expr .nat)
  | fail (failure : Failure)

structure Input where
  type : Ty
  name : String

structure Program where
  name : String
  inputs : List Input
  body : List Stmt

private def source : Var .source := ⟨"source"⟩
private def weights : Var .natVector := ⟨"weights"⟩
private def target : Var .natVector := ⟨"target"⟩
private def proposal : Var .natMatrix := ⟨"proposal"⟩
private def current : Var .nat := ⟨"current"⟩

/-- Cumulative categorical selection in backend-neutral control flow. -/
def categoricalProgram : Program where
  name := "categorical_index!"
  inputs := [⟨.source, source.name⟩, ⟨.natVector, weights.name⟩]
  body :=
    let exactWeights : Var .natVector := ⟨"exact_weights"⟩
    let total : Var .nat := ⟨"total"⟩
    let draw : Var .nat := ⟨"draw"⟩
    let index : Var .nat := ⟨"index"⟩
    let weight : Var .nat := ⟨"weight"⟩
    [.letE exactWeights (.toExactVector (.var weights)),
      .guard (.allNonnegative (.var exactWeights))
        (.argument "weights must be nonnegative"),
      .letE total (.total (.var exactWeights)),
      .guard (.lt (.nat 0) (.var total))
        (.argument "weights must have positive total"),
      .drawBelow draw (.var source) (.var total),
      .forVector index weight exactWeights [
        .ifThen (.lt (.var draw) (.var weight)) [.return (.var index)],
        .subtractAssign draw (.var weight)],
      .fail (.internal "draw_below! violated its range contract")]

/-- Generic exact finite MH control flow. -/
def metropolisHastingsProgram : Program where
  name := "finite_mh_step!"
  inputs := [⟨.source, source.name⟩, ⟨.natVector, target.name⟩,
    ⟨.natMatrix, proposal.name⟩, ⟨.nat, current.name⟩]
  body :=
    let targetWeights : Var .natVector := ⟨"target_weights"⟩
    let rows : Var .natMatrix := ⟨"rows"⟩
    let stateCount : Var .nat := ⟨"state_count"⟩
    let proposed : Var .nat := ⟨"proposed"⟩
    let currentTotal : Var .nat := ⟨"current_total"⟩
    let proposedTotal : Var .nat := ⟨"proposed_total"⟩
    let forward : Var .nat := ⟨"forward"⟩
    let reverse : Var .nat := ⟨"reverse"⟩
    let upper : Var .nat := ⟨"upper"⟩
    let threshold : Var .nat := ⟨"threshold"⟩
    let draw : Var .nat := ⟨"draw"⟩
    [.letE targetWeights (.toExactVector (.var target)),
      .guard (.allPositive (.var targetWeights))
        (.argument "target weights must be positive"),
      .letE stateCount (.length (.var targetWeights)),
      .guard (.eq (.rowCount (.var proposal)) (.var stateCount))
        (.dimension "proposal row count"),
      .guard (.and (.le (.nat 0) (.var current))
        (.lt (.var current) (.var stateCount)))
        (.argument "current state is out of range"),
      .letE rows (.toExactMatrix (.var proposal)),
      .guard (.allRowsLength (.var rows) (.var stateCount))
        (.dimension "proposal column count"),
      .guard (.allRowsNonnegativePositive (.var rows))
        (.argument "proposal rows need nonnegative weights and positive totals"),
      .letE proposed (.categorical (.var source) (.row (.var rows) (.var current))),
      .ifThen (.eq (.var proposed) (.var current)) [.return (.var current)],
      .letE currentTotal (.total (.row (.var rows) (.var current))),
      .letE proposedTotal (.total (.row (.var rows) (.var proposed))),
      .letE forward (.index (.row (.var rows) (.var current)) (.var proposed)),
      .letE reverse (.index (.row (.var rows) (.var proposed)) (.var current)),
      .letE upper (.mul (.mul (.index (.var targetWeights) (.var current))
        (.var forward)) (.var proposedTotal)),
      .letE threshold (.min (.var upper)
        (.mul (.mul (.index (.var targetWeights) (.var proposed)) (.var reverse))
          (.var currentTotal))),
      .drawBelow draw (.var source) (.var upper),
      .ifThen (.lt (.var draw) (.var threshold)) [.return (.var proposed)],
      .return (.var current)]

/-- Concrete literals used by the backend's thin two-state wrapper. -/
def twoStateTarget : Expr .natVector := .vector [1, 3]
def twoStateProposal : Expr .natMatrix := .matrix [[1, 1], [1, 1]]

end Mcmc.Executable.Finite.CompilerIR
