import Mcmc.PDMP.PoissonSchedule
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic

/-!
# Integrating scheduled PDMP execution

This module gives the first fully integrated fixed-horizon path-law client: a
single conditional candidate time is sampled from its continuous law, the
process flows to that time, applies bounded thinning, and flows through the
remaining horizon. Keeping the sampled time in the augmented state makes every
step a standard mathlib kernel composition.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Mcmc.PDMP

variable {State : Type*} [MeasurableSpace State]

/-- Deterministically flow to the timestamp while retaining it. -/
noncomputable def ThinnedFlowSimulator.flowToTimestamp
    (simulator : ThinnedFlowSimulator State) :
    Kernel (State × NNReal) (State × NNReal) :=
  Kernel.deterministic
    (fun p => (simulator.semiflow.flow p.2 p.1, p.2))
    (simulator.semiflow.jointly_measurable_flow.comp
      (measurable_snd.prodMk measurable_fst) |>.prodMk measurable_snd)

instance ThinnedFlowSimulator.flowToTimestamp.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) :
    IsMarkovKernel simulator.flowToTimestamp := by
  unfold ThinnedFlowSimulator.flowToTimestamp
  infer_instance

/-- Apply the accepted/virtual event to the state while retaining its
timestamp. -/
noncomputable def ThinnedFlowSimulator.jumpKeepTimestamp
    (simulator : ThinnedFlowSimulator State) :
    Kernel (State × NNReal) (State × NNReal) :=
  Kernel.prod
    (Kernel.prodMkRight NNReal
      (simulator.mechanism.uniformizedKernel simulator.clock.rate))
    (Kernel.deterministic Prod.snd measurable_snd)

instance ThinnedFlowSimulator.jumpKeepTimestamp.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) :
    IsMarkovKernel simulator.jumpKeepTimestamp := by
  letI : IsMarkovKernel
      (simulator.mechanism.uniformizedKernel simulator.clock.rate) :=
    simulator.mechanism.uniformizedKernel_isMarkov simulator.clock.rate
      simulator.clock.positive simulator.rate_le_clock
  unfold ThinnedFlowSimulator.jumpKeepTimestamp
  infer_instance

/-- Flow from a retained timestamp through the residual horizon. -/
noncomputable def ThinnedFlowSimulator.flowResidual
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    Kernel (State × NNReal) State :=
  Kernel.deterministic
    (fun p => simulator.semiflow.flow (horizon - p.2) p.1)
    (simulator.semiflow.jointly_measurable_flow.comp
      ((measurable_const.sub measurable_snd).prodMk measurable_fst))

instance ThinnedFlowSimulator.flowResidual.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    IsMarkovKernel (simulator.flowResidual horizon) := by
  unfold ThinnedFlowSimulator.flowResidual
  infer_instance

/-- Execute one supplied candidate timestamp inside a fixed horizon. -/
noncomputable def ThinnedFlowSimulator.oneTimestampKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    Kernel (State × NNReal) State :=
  simulator.flowResidual horizon ∘ₖ
    (simulator.jumpKeepTimestamp ∘ₖ simulator.flowToTimestamp)

instance ThinnedFlowSimulator.oneTimestampKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal) :
    IsMarkovKernel (simulator.oneTimestampKernel horizon) := by
  unfold ThinnedFlowSimulator.oneTimestampKernel
  infer_instance

/-- Sample one timestamp from an arbitrary probability law and execute its
fixed-horizon flow/thinning path. -/
noncomputable def ThinnedFlowSimulator.oneRandomTimestampKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (timestampLaw : Measure NNReal) : Kernel State State :=
  simulator.oneTimestampKernel horizon ∘ₖ
    Kernel.prod Kernel.id (Kernel.const State timestampLaw)

instance ThinnedFlowSimulator.oneRandomTimestampKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : NNReal)
    (timestampLaw : Measure NNReal) [IsProbabilityMeasure timestampLaw] :
    IsMarkovKernel
      (simulator.oneRandomTimestampKernel horizon timestampLaw) := by
  unfold ThinnedFlowSimulator.oneRandomTimestampKernel
  infer_instance

/-- Fully integrated execution conditional on exactly one homogeneous-clock
candidate in a positive horizon. Its timestamp has the standard continuous
uniform conditional law. -/
noncomputable def ThinnedFlowSimulator.oneConditionalCandidateKernel
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon) :
    Kernel State State :=
  simulator.oneRandomTimestampKernel horizon.duration
    horizon.uniformNNRealTimeMeasure

instance ThinnedFlowSimulator.oneConditionalCandidateKernel.instIsMarkovKernel
    (simulator : ThinnedFlowSimulator State) (horizon : PositiveHorizon) :
    IsMarkovKernel (simulator.oneConditionalCandidateKernel horizon) := by
  unfold ThinnedFlowSimulator.oneConditionalCandidateKernel
  infer_instance

end Mcmc.PDMP
