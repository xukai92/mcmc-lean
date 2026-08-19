import Mcmc.Executable.Finite.CompilerIR
import Mcmc.Executable.Continuous.CompilerIR
import Mcmc.Executable.Continuous.MetricCompilerIR
import Mcmc.Executable.Continuous.MultinomialCompilerIR
import Mcmc.Executable.Continuous.CoupledXu21
import Mcmc.Executable.Continuous.RelativisticCompilerIR
import Mcmc.Executable.Continuous.RestrictedArtifact
import Mcmc.Executable.ComposableIR
import Mcmc.Executable.ConstrainedTransformIR
import Mcmc.Executable.DynamicTreeIR

/-!
# Versioned textual format for sampler IR

The artifact is data, not Julia source. Its deliberately small S-expression
format is consumed by the maintained Julia reference interpreter.
-/

namespace Mcmc.Executable.IRFormat

open Finite.CompilerIR

def version : Nat := 19

private def quote (value : String) : String :=
  let escapedBackslash := value.replace "\\" "\\\\"
  let escapedQuote := escapedBackslash.replace "\"" "\\\""
  let escapedNewline := escapedQuote.replace "\n" "\\n"
  "\"" ++ escapedNewline ++ "\""

private def tyRender : Ty → String
  | .source => "source"
  | .nat => "nat"
  | .bool => "bool"
  | .natVector => "nat-vector"
  | .natMatrix => "nat-matrix"

private def list (items : List String) : String :=
  "(" ++ String.intercalate " " items ++ ")"

private def exprRender : {type : Ty} → Expr type → String
  | type, .var value => list ["var", tyRender type, quote value.name]
  | _, .nat value => list ["nat", toString value]
  | _, .vector values => list ("vector" :: values.map toString)
  | _, .matrix rows => list ("matrix" :: rows.map fun row =>
      list ("row" :: row.map toString))
  | _, .add left right => list ["add", exprRender left, exprRender right]
  | _, .sub left right => list ["sub", exprRender left, exprRender right]
  | _, .mul left right => list ["mul", exprRender left, exprRender right]
  | _, .min left right => list ["min", exprRender left, exprRender right]
  | _, .length value => list ["length", exprRender value]
  | _, .rowCount value => list ["row-count", exprRender value]
  | _, .total value => list ["total", exprRender value]
  | _, .index value index => list ["index", exprRender value, exprRender index]
  | _, .row value index => list ["row-at", exprRender value, exprRender index]
  | _, .lt left right => list ["lt", exprRender left, exprRender right]
  | _, .le left right => list ["le", exprRender left, exprRender right]
  | _, .eq left right => list ["eq", exprRender left, exprRender right]
  | _, .and left right => list ["and", exprRender left, exprRender right]
  | _, .allNonnegative value => list ["all-nonnegative", exprRender value]
  | _, .allPositive value => list ["all-positive", exprRender value]
  | _, .allRowsLength value size =>
      list ["all-rows-length", exprRender value, exprRender size]
  | _, .allRowsNonnegativePositive value =>
      list ["all-rows-nonnegative-positive", exprRender value]
  | _, .toExactVector value => list ["to-exact-vector", exprRender value]
  | _, .toExactMatrix value => list ["to-exact-matrix", exprRender value]
  | _, .categorical source weights =>
      list ["categorical", exprRender source, exprRender weights]

private def failureRender : Failure → String
  | .argument message => list ["argument", quote message]
  | .dimension message => list ["dimension", quote message]
  | .internal message => list ["internal", quote message]

private def stmtRender : Stmt → String
  | .letE destination value =>
      list ["let", quote destination.name, exprRender value]
  | .guard condition failure =>
      list ["guard", exprRender condition, failureRender failure]
  | .drawBelow destination source upper =>
      list ["draw-below", quote destination.name, exprRender source, exprRender upper]
  | .ifThen condition body =>
      list ["if", exprRender condition, list ("body" :: body.map stmtRender)]
  | .return value => list ["return", exprRender value]
  | .fail failure => list ["fail", failureRender failure]

private def Input.render (input : Input) : String :=
  list ["input", tyRender input.type, quote input.name]

/-- Render one typed finite command-IR program in the artifact format. -/
def finiteProgramRender (program : Program) : String :=
  list ["program", quote program.name,
    list ("inputs" :: program.inputs.map Input.render),
    list ("body" :: program.body.map stmtRender)]

private def continuousTyRender :
    Continuous.CompilerIR.Ty → String
  | .real => "real"
  | .bool => "bool"
  | .nat => "nat"
  | .realVector => "real-vector"

private def continuousExprRender : {type : Continuous.CompilerIR.Ty} →
    Continuous.CompilerIR.Expr type → String
  | type, .var value => list ["var", continuousTyRender type, quote value.name]
  | _, .real value => list ["real", toString value]
  | _, .nat value => list ["nat", toString value]
  | _, .add left right =>
      list ["add", continuousExprRender left, continuousExprRender right]
  | _, .sub left right =>
      list ["sub-real", continuousExprRender left, continuousExprRender right]
  | _, .mul left right =>
      list ["mul", continuousExprRender left, continuousExprRender right]
  | _, .div left right =>
      list ["div-real", continuousExprRender left, continuousExprRender right]
  | _, .exp value => list ["exp", continuousExprRender value]
  | _, .min left right =>
      list ["min", continuousExprRender left, continuousExprRender right]
  | _, .lt left right =>
      list ["lt", continuousExprRender left, continuousExprRender right]
  | _, .logDensity value => list ["log-density", continuousExprRender value]
  | _, .gradient value => list ["gradient", continuousExprRender value]
  | _, .leapfrogPosition stepSize steps position momentum =>
      list ["leapfrog-position", continuousExprRender stepSize,
        continuousExprRender steps, continuousExprRender position,
        continuousExprRender momentum]
  | _, .leapfrogMomentum stepSize steps position momentum =>
      list ["leapfrog-momentum", continuousExprRender stepSize,
        continuousExprRender steps, continuousExprRender position,
        continuousExprRender momentum]
  | _, .vectorLogDensity value =>
      list ["vector-log-density", continuousExprRender value]
  | _, .vectorGradient value =>
      list ["vector-gradient", continuousExprRender value]
  | _, .vectorLeapfrogPosition stepSize steps position momentum =>
      list ["vector-leapfrog-position", continuousExprRender stepSize,
        continuousExprRender steps, continuousExprRender position,
        continuousExprRender momentum]
  | _, .vectorLeapfrogMomentum stepSize steps position momentum =>
      list ["vector-leapfrog-momentum", continuousExprRender stepSize,
        continuousExprRender steps, continuousExprRender position,
        continuousExprRender momentum]
  | _, .squaredNorm value =>
      list ["squared-norm", continuousExprRender value]

private def continuousStmtRender : Continuous.CompilerIR.Stmt → String
  | .letE destination value =>
      list ["let", quote destination.name, continuousExprRender value]
  | .sampleStandardNormal destination =>
      list ["sample-standard-normal", quote destination.name]
  | .sampleUniformUnit destination =>
      list ["sample-uniform-unit", quote destination.name]
  | .sampleStandardNormalVector destination dimension =>
      list ["sample-standard-normal-vector", quote destination.name,
        continuousExprRender dimension]
  | .ifThen condition body =>
      list ["if", continuousExprRender condition,
        list ("body" :: body.map continuousStmtRender)]
  | .return value => list ["return", continuousExprRender value]
  | .returnVector value => list ["return", continuousExprRender value]

/-- Serialize one typed scalar/vector continuous command program. This is
public so the independent artifact parser can state declaration-level
round-trip checks without duplicating the serializer. -/
def continuousProgramRender
    (program : Continuous.CompilerIR.Program) : String :=
  let inputs :=
    [list ["input", "source", quote program.sourceInput],
      list ["input", "log-density", quote program.logDensityInput]] ++
      (match program.gradientInput with
      | none => []
      | some name => [list ["input", "gradient", quote name]]) ++
      program.realInputs.map (fun name => list ["input", "real", quote name]) ++
      program.natInputs.map (fun name => list ["input", "nat", quote name]) ++
      program.vectorInputs.map (fun name =>
        list ["input", "real-vector", quote name])
  list ["program", quote program.name, list ("inputs" :: inputs),
    list ("body" :: program.body.map continuousStmtRender)]

private def restrictedExprRender :
    Mcmc.Executable.Continuous.RestrictedArtifactExpr → String
  | .input => list ["input"]
  | .rational numerator denominator =>
      list ["rational", toString numerator, toString denominator]
  | .add left right =>
      list ["add", restrictedExprRender left, restrictedExprRender right]
  | .mul left right =>
      list ["mul", restrictedExprRender left, restrictedExprRender right]
  | .neg value => list ["neg", restrictedExprRender value]
  | .exp value => list ["exp", restrictedExprRender value]
  | .sin value => list ["sin", restrictedExprRender value]
  | .cos value => list ["cos", restrictedExprRender value]

private def restrictedTargetRender (name : String)
    (expression : Mcmc.Executable.Continuous.RestrictedArtifactExpr) : String :=
  list ["target", quote name, restrictedExprRender expression]

private def engineRender : ComposableIR.Engine → String
  | .particleGibbs => "particle-gibbs"
  | .hmc => "hmc"
  | .nuts => "nuts"

private def operatorDescriptorRender
    (operator : ComposableIR.OperatorDescriptor) : String :=
  list ["operator", quote operator.name, engineRender operator.engine,
    list ("scope" :: operator.scope.map quote)]

private def scheduleDescriptorRender
    (schedule : ComposableIR.ScheduleDescriptor) : String :=
  list ["schedule", quote schedule.name,
    list ("variables" :: schedule.variables.map quote),
    list ("operators" :: schedule.operators.map operatorDescriptorRender)]

private def scalarTransformRender :
    ConstrainedTransformIR.ScalarTransform → String
  | .positiveLog => "positive-log"
  | .openUnitArtanh => "open-unit-artanh"

private def transformDescriptorRender
    (descriptor : ConstrainedTransformIR.Descriptor) : String :=
  list ["transform", quote descriptor.name,
    scalarTransformRender descriptor.transform,
    quote descriptor.constrainedType, quote descriptor.unconstrainedType,
    quote descriptor.forward, quote descriptor.inverse,
    quote descriptor.logAbsDetInverseJacobian]

private def dynamicTreeBuilderRender :
    DynamicTreeIR.Builder → String
  | .recursiveDoubling => "recursive-doubling"

private def dynamicTreeTracePolicyRender :
    DynamicTreeIR.TracePolicy → String
  | .fairDirectionBits => "fair-direction-bits"

private def dynamicTreeRootEncodingRender :
    DynamicTreeIR.RootEncoding → String
  | .lsbFirstGrowRightZero => "lsb-first-grow-right-zero"

private def dynamicTreeStopRuleRender :
    DynamicTreeIR.StopRule → String
  | .endpointUTurn => "endpoint-uturn"

private def dynamicTreeSubtreePolicyRender :
    DynamicTreeIR.SubtreePolicy → String
  | .recursiveExclusion => "recursive-exclusion"

private def dynamicTreeFailurePolicyRender :
    DynamicTreeIR.FailurePolicy → String
  | .checkedOrIdentity => "checked-or-identity"

private def dynamicTreeSelectionPolicyRender :
    DynamicTreeIR.SelectionPolicy → String
  | .eligibleCountStreaming => "eligible-count-streaming"

private def dynamicTreeDescriptorRender
    (descriptor : DynamicTreeIR.Descriptor) : String :=
  list ["dynamic-tree", quote descriptor.name,
    dynamicTreeBuilderRender descriptor.builder,
    dynamicTreeTracePolicyRender descriptor.tracePolicy,
    dynamicTreeRootEncodingRender descriptor.rootEncoding,
    dynamicTreeStopRuleRender descriptor.stopRule,
    dynamicTreeSubtreePolicyRender descriptor.subtreePolicy,
    dynamicTreeSelectionPolicyRender descriptor.selectionPolicy,
    dynamicTreeFailurePolicyRender descriptor.failurePolicy]

/-- Serialize all reference entry programs with a format version. -/
def render : String :=
  list (["verified-samplers-ir", toString version,
    finiteProgramRender categoricalProgram,
    finiteProgramRender metropolisHastingsProgram,
    continuousProgramRender Continuous.CompilerIR.gaussianRwmhProgram,
    continuousProgramRender Continuous.CompilerIR.scalarHmcProgram,
    continuousProgramRender Continuous.CompilerIR.vectorHmcProgram,
    Continuous.MetricCompilerIR.diagonalHmcProgram.render,
    Continuous.MetricCompilerIR.denseHmcProgram.render,
    Continuous.MetricCompilerIR.diagonalMultinomialHmcProgram.render,
    Continuous.MetricCompilerIR.denseMultinomialHmcProgram.render,
    Continuous.MultinomialCompilerIR.program.render,
    Continuous.RelativisticCompilerIR.program.render,
    Continuous.RelativisticCompilerIR.certifiedPositionDependentProgram.render,
    restrictedTargetRender "restricted-gaussian-potential"
      Mcmc.Executable.Continuous.restrictedGaussianArtifact,
    restrictedTargetRender "restricted-sinusoidal-potential"
      Mcmc.Executable.Continuous.restrictedSinusoidalPotentialArtifact,
    restrictedTargetRender "restricted-quartic-potential"
      Mcmc.Executable.Continuous.restrictedQuarticPotentialArtifact,
    scheduleDescriptorRender ComposableIR.gePgHmcSchedule,
    transformDescriptorRender ConstrainedTransformIR.positiveLog,
    transformDescriptorRender ConstrainedTransformIR.openUnitArtanh] ++
    [dynamicTreeDescriptorRender DynamicTreeIR.checkedRecursiveDoubling] ++
    Continuous.CoupledXu21.renderedPrograms) ++ "\n"

end Mcmc.Executable.IRFormat
