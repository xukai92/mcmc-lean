/-!
# Documentation graphs

Typed graph descriptions used to generate diagrams for the public documentation.
Keeping the nodes and edges in Lean makes changes to the documented architecture
part of the compiled formal source tree.
-/

namespace Mcmc.Docs

/-- A node in a generated documentation graph. -/
structure GraphNode where
  id : String
  label : String
  deriving Repr

/-- A directed edge in a generated documentation graph. -/
structure GraphEdge where
  source : String
  target : String
  label : Option String := none
  dashed : Bool := false
  deriving Repr

/-- A Mermaid flowchart whose structure is maintained in Lean. -/
structure Graph where
  title : String
  direction : String := "TB"
  nodes : List GraphNode
  edges : List GraphEdge
  note : String
  deriving Repr

private def escapeLabel (value : String) : String :=
  value.replace "\"" "&quot;"

private def renderNode (node : GraphNode) : String :=
  s!"  {node.id}[\"{escapeLabel node.label}\"]"

private def renderEdge (edge : GraphEdge) : String :=
  let arrow := if edge.dashed then "-.->" else "-->"
  match edge.label with
  | none => s!"  {edge.source} {arrow} {edge.target}"
  | some label => s!"  {edge.source} {arrow}|{escapeLabel label}| {edge.target}"

/-- Render one graph as a Markdown section containing Mermaid source. -/
def Graph.render (graph : Graph) : String :=
  String.intercalate "\n" <|
    [s!"## {graph.title}", "", "```mermaid", s!"flowchart {graph.direction}"] ++
    graph.nodes.map renderNode ++ graph.edges.map renderEdge ++
    ["```", "", graph.note]

/-- The measure-theoretic and algorithmic dependency layers. -/
def formalizationGraph : Graph where
  title := "Formalization dependency graph"
  nodes := [
    ⟨"measure", "mathlib Measure and integration"⟩,
    ⟨"kernel", "ProbabilityTheory.Kernel"⟩,
    ⟨"finite", "Finite probability and transport"⟩,
    ⟨"smc", "Finite Feynman--Kac and explicit SMC histories"⟩,
    ⟨"pmcmc", "PIMH, PMMH, conditional SMC, and particle Gibbs"⟩,
    ⟨"pgRate", "Positive-horizon PG convergence and count-indexed rates"⟩,
    ⟨"trace", "Finite assume/observe posterior semantics"⟩,
    ⟨"composable", "Scoped composable inference operators"⟩,
    ⟨"ge18", "Ge et al. 2018 Turing core"⟩,
    ⟨"transform", "Constrained-coordinate measure equivalences"⟩,
    ⟨"mh", "General-state Metropolis--Hastings"⟩,
    ⟨"rwmh", "Gaussian RWMH and coupling"⟩,
    ⟨"dynamics", "Hamiltonian dynamics and leapfrog"⟩,
    ⟨"implicit", "Fixed-step exact implicit solver"⟩,
    ⟨"hmc", "Multinomial HMC and coupling"⟩,
    ⟨"meeting", "Meeting, drift, and tail bounds"⟩,
    ⟨"xu21", "Xu et al. 2021 results"⟩,
    ⟨"relativistic", "Relativistic and Riemannian HMC"⟩,
    ⟨"xu24", "Xu and Ge 2024 results"⟩]
  edges := [
    ⟨"measure", "kernel", none, false⟩,
    ⟨"kernel", "mh", none, false⟩,
    ⟨"finite", "hmc", some "trajectory-index laws", false⟩,
    ⟨"finite", "smc", none, false⟩,
    ⟨"smc", "pmcmc", some "selected-path extended target", false⟩,
    ⟨"pmcmc", "pgRate", some "full support or explicit minorization", false⟩,
    ⟨"finite", "trace", some "normalized factor semantics", false⟩,
    ⟨"trace", "composable", some "common posterior target", false⟩,
    ⟨"pmcmc", "composable", some "PG component", false⟩,
    ⟨"mh", "rwmh", none, false⟩,
    ⟨"dynamics", "hmc", none, false⟩,
    ⟨"kernel", "hmc", none, false⟩,
    ⟨"hmc", "composable", some "HMC component", false⟩,
    ⟨"composable", "ge18", some "scheduled stationarity", false⟩,
    ⟨"kernel", "transform", some "kernel conjugation", false⟩,
    ⟨"transform", "ge18", some "positive-real runtime convention", false⟩,
    ⟨"rwmh", "meeting", none, false⟩,
    ⟨"hmc", "meeting", none, false⟩,
    ⟨"meeting", "xu21", none, false⟩,
    ⟨"dynamics", "relativistic", none, false⟩,
    ⟨"dynamics", "implicit", some "generalized-leapfrog equations", false⟩,
    ⟨"implicit", "relativistic", some "existence, uniqueness, reversal", false⟩,
    ⟨"kernel", "relativistic", none, false⟩,
    ⟨"relativistic", "xu24", none, false⟩]
  note := "Arrows show definition or theorem dependencies. The finite layer remains useful inside general-state HMC because trajectory-index selection is finite."

/-- The executable assurance chain and its explicitly deferred numerical link. -/
def executableGraph : Graph where
  title := "Executable assurance graph"
  direction := "LR"
  nodes := [
    ⟨"ideal", "Ideal real-valued sampler semantics"⟩,
    ⟨"typed", "Typed sampler IR in Lean"⟩,
    ⟨"oracle", "Exact Lean IR interpreter oracle"⟩,
    ⟨"serialized", "Versioned serialized IR"⟩,
    ⟨"reference", "Julia Reference interpreter"⟩,
    ⟨"optimized", "Julia Optimized implementation"⟩,
    ⟨"bounds", "Backend-independent error and margin certificates"⟩,
    ⟨"float", "Floating-point execution"⟩]
  edges := [
    ⟨"ideal", "typed", some "proved refinement", false⟩,
    ⟨"typed", "oracle", some "exact interpreter theorem", false⟩,
    ⟨"typed", "serialized", some "Lean generator", false⟩,
    ⟨"serialized", "reference", some "direct interpretation", false⟩,
    ⟨"reference", "optimized", some "differential tests", false⟩,
    ⟨"ideal", "bounds", some "proved bounded refinement", false⟩,
    ⟨"bounds", "float", some "platform-local operation bounds", true⟩,
    ⟨"optimized", "float", some "executes as", false⟩]
  note := "Solid arrows are implemented generation, proved refinement, or tested conformance links as labeled. The exact Lean interpreter satisfies its refinement contract. The dashed arrow isolates the remaining platform-specific libm, rounding, and RNG evidence needed to instantiate the proved bounded certificates for Float64."

/-- Complete generated Markdown page for the documentation site. -/
def renderGraphs : String :=
  String.intercalate "\n\n" [
    "# Lean-generated architecture graphs",
    "<!-- Generated by formal/Mcmc/GenerateDocs.lean; do not edit manually. -->",
    "The graph data below is defined and typechecked in `Mcmc.Docs.Graph`.",
    formalizationGraph.render,
    executableGraph.render]

end Mcmc.Docs
