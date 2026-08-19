/-!
# Sampler assurance registry

Typed documentation data for the maintained sampler golden paths.  The facets
are deliberately independent: a proved mathematical or ideal-execution result
does not silently upgrade Julia, floating-point, callback, or RNG behavior.

This registry records existing evidence only.  It is not an algorithm API and
does not add mathematical claims.
-/

namespace Mcmc.Docs

/-- Kind of evidence supporting one sampler layer. -/
inductive EvidenceKind where
  | proved
  | generated
  | tested
  | documentedBoundary
  deriving Repr, DecidableEq

/-- Evidence for one independently auditable sampler facet. -/
structure EvidenceFacet where
  kind : EvidenceKind
  evidence : String
  note : String
  deriving Repr

/-- Evidence carried by one maintained sampler path.

The fields are not collapsed into a single maturity badge because their trust
boundaries differ. -/
structure SamplerAssurance where
  sampler : String
  mathematics : EvidenceFacet
  executable : EvidenceFacet
  artifact : EvidenceFacet
  reference : EvidenceFacet
  publicRuntime : EvidenceFacet
  optimized : EvidenceFacet
  deriving Repr

private def EvidenceKind.label : EvidenceKind → String
  | .proved => "proved"
  | .generated => "generated/checkable"
  | .tested => "tested"
  | .documentedBoundary => "documented boundary"

private def escapeCell (value : String) : String :=
  value.replace "|" "\\|" |>.replace "\n" " "

private def EvidenceFacet.render (facet : EvidenceFacet) : String :=
  escapeCell s!"**{facet.kind.label}:** `{facet.evidence}` — {facet.note}"

private def SamplerAssurance.render (entry : SamplerAssurance) : String :=
  String.intercalate " | " [
    entry.sampler,
    entry.mathematics.render,
    entry.executable.render,
    entry.artifact.render,
    entry.reference.render,
    entry.publicRuntime.render,
    entry.optimized.render]

/-- Current end-to-end golden paths.  This deliberately begins with the two
existing paths used to validate the contributor workflow; it is not an
exhaustive algorithm-coverage table. -/
def samplerAssuranceRegistry : List SamplerAssurance := [
  { sampler := "Scalar Gaussian RWMH"
    mathematics := {
      kind := .proved
      evidence := "gaussianRandomWalkMetropolisHastings_invariant"
      note := "Markov, reversibility, and invariance theorems are checked." }
    executable := {
      kind := .proved
      evidence := "gaussianRwmhProgramKernel_refines"
      note := "Exact kernel equality and deterministic trace replay are checked." }
    artifact := {
      kind := .generated
      evidence := "gaussian_rwmh_step!"
      note := "Lean emits the canonical declaration; regeneration is checked." }
    reference := {
      kind := .tested
      evidence := "Reference.gaussian_rwmh_step!"
      note := "Julia parsing, replay, and validation are test-supported." }
    publicRuntime := {
      kind := .tested
      evidence := "GaussianRWMH"
      note := "Seeded API and statistical regressions exercise Reference." }
    optimized := {
      kind := .tested
      evidence := "Optimized.gaussian_rwmh_step!"
      note := "The independent implementation has deterministic differential tests." } },
  { sampler := "Scalar fixed-step endpoint HMC"
    mathematics := {
      kind := .proved
      evidence := "endpointHmcNPositionKernel_invariant"
      note := "The refreshed/projected exact endpoint kernel preserves its target under the stated factorization." }
    executable := {
      kind := .documentedBoundary
      evidence := "runScalarHmc_refines"
      note := "Trace replay and integrator correspondence are proved; no single theorem equates the full command kernel to the position kernel." }
    artifact := {
      kind := .generated
      evidence := "scalar_hmc_step!"
      note := "Lean emits the canonical declaration; regeneration is checked." }
    reference := {
      kind := .tested
      evidence := "Reference.scalar_hmc_step!"
      note := "Julia parsing, replay, callbacks, and validation are test-supported." }
    publicRuntime := {
      kind := .tested
      evidence := "ScalarHMC"
      note := "Seeded API and moment regressions exercise Reference." }
    optimized := {
      kind := .tested
      evidence := "Optimized.scalar_hmc_step!"
      note := "The independent implementation has deterministic differential tests." } }]

/-- Render the assurance registry as a generated Markdown section. -/
def renderSamplerAssuranceRegistry : String :=
  String.intercalate "\n" <|
    ["## Sampler assurance registry", "",
     "This generated registry records the two existing golden paths. Facets are independent: `proved` applies only to the named Lean result, while Julia paths remain test-supported unless stated otherwise.", "",
     "| Sampler | Mathematics | Executable semantics | Artifact | Julia Reference | Public runtime | Optimized |",
     "|---|---|---|---|---|---|---|"] ++
    samplerAssuranceRegistry.map (fun entry => s!"| {entry.render} |")

end Mcmc.Docs
