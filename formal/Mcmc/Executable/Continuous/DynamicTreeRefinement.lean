import Mcmc.Executable.Continuous.BoundedRWMH
import Mcmc.Finite.CertifiedDynamicTree

/-!
# Bounded decision refinement for dynamic NUTS trees

This module certifies the discontinuous Boolean decisions used by a
finite-precision dynamic-tree builder. It does not claim that Float64 phase
points equal ideal-real phase points. Instead, callers supply absolute error
bounds for the scalar comparisons. A decision is certified only when its
computed value lies strictly outside the corresponding uncertainty band.
-/

namespace Mcmc.Executable.Continuous

open Mcmc.Finite.MarkovKernel

/-- A comparison with zero whose computed value is separated from the entire
absolute-error uncertainty interval. -/
structure SeparatedZeroCertificate where
  computed : ℝ
  ideal : ℝ
  error : ℝ
  bound : Approximates computed ideal error
  separated : computed < -error ∨ error < computed

/-- Boolean sign decision made by the numerical implementation. -/
noncomputable def SeparatedZeroCertificate.computedNegative
    (certificate : SeparatedZeroCertificate) : Bool :=
  decide (certificate.computed < 0)

/-- Ideal-real sign decision consumed by the mathematical tree. -/
noncomputable def SeparatedZeroCertificate.idealNegative
    (certificate : SeparatedZeroCertificate) : Bool :=
  decide (certificate.ideal < 0)

/-- Separation from zero makes the computed and ideal sign decisions equal.
Equality cases are intentionally uncertifiable. -/
theorem SeparatedZeroCertificate.computedNegative_eq_idealNegative
    (certificate : SeparatedZeroCertificate) :
    certificate.computedNegative = certificate.idealNegative := by
  have herror := certificate.bound.nonneg
  have habs := certificate.bound
  rw [Approximates] at habs
  have hinterval := abs_le.mp habs
  rcases certificate.separated with hnegative | hpositive
  · have hcomputed : certificate.computed < 0 := by linarith
    have hideal : certificate.ideal < 0 := by linarith
    simp [SeparatedZeroCertificate.computedNegative,
      SeparatedZeroCertificate.idealNegative, hcomputed, hideal]
  · have hcomputed : ¬ certificate.computed < 0 := by linarith
    have hideal : ¬ certificate.ideal < 0 := by linarith
    simp [SeparatedZeroCertificate.computedNegative,
      SeparatedZeroCertificate.idealNegative, hcomputed, hideal]

/-- Two-sided scalar comparison certificate. This is the form used for slice
eligibility and divergence thresholds: errors from both operands add before
the computed difference is tested for strict separation from zero. -/
structure SeparatedComparisonCertificate where
  computedLeft : ℝ
  idealLeft : ℝ
  computedRight : ℝ
  idealRight : ℝ
  leftError : ℝ
  rightError : ℝ
  leftBound : Approximates computedLeft idealLeft leftError
  rightBound : Approximates computedRight idealRight rightError
  separated :
    computedLeft - computedRight < -(leftError + rightError) ∨
      leftError + rightError < computedLeft - computedRight

noncomputable def SeparatedComparisonCertificate.differenceCertificate
    (certificate : SeparatedComparisonCertificate) :
    SeparatedZeroCertificate where
  computed := certificate.computedLeft - certificate.computedRight
  ideal := certificate.idealLeft - certificate.idealRight
  error := certificate.leftError + certificate.rightError
  bound := certificate.leftBound.sub certificate.rightBound
  separated := certificate.separated

noncomputable def SeparatedComparisonCertificate.computedLess
    (certificate : SeparatedComparisonCertificate) : Bool :=
  decide (certificate.computedLeft < certificate.computedRight)

noncomputable def SeparatedComparisonCertificate.idealLess
    (certificate : SeparatedComparisonCertificate) : Bool :=
  decide (certificate.idealLeft < certificate.idealRight)

/-- A separated bounded comparison produces exactly the ideal-real Boolean. -/
theorem SeparatedComparisonCertificate.computedLess_eq_idealLess
    (certificate : SeparatedComparisonCertificate) :
    certificate.computedLess = certificate.idealLess := by
  change decide (certificate.computedLeft < certificate.computedRight) =
    decide (certificate.idealLeft < certificate.idealRight)
  have h := certificate.differenceCertificate.computedNegative_eq_idealNegative
  change decide (certificate.computedLeft - certificate.computedRight < 0) =
    decide (certificate.idealLeft - certificate.idealRight < 0) at h
  simpa only [sub_lt_zero] using h

/-- Pair of certified endpoint dot products used by the vector U-turn rule. -/
structure UTurnDecisionCertificate where
  leftMomentum : SeparatedZeroCertificate
  rightMomentum : SeparatedZeroCertificate

noncomputable def UTurnDecisionCertificate.computedTurns
    (certificate : UTurnDecisionCertificate) : Bool :=
  certificate.leftMomentum.computedNegative ||
    certificate.rightMomentum.computedNegative

noncomputable def UTurnDecisionCertificate.idealTurns
    (certificate : UTurnDecisionCertificate) : Bool :=
  certificate.leftMomentum.idealNegative ||
    certificate.rightMomentum.idealNegative

/-- Both endpoint sign certificates compose into the exact ideal U-turn bit. -/
theorem UTurnDecisionCertificate.computedTurns_eq_idealTurns
    (certificate : UTurnDecisionCertificate) :
    certificate.computedTurns = certificate.idealTurns := by
  simp only [UTurnDecisionCertificate.computedTurns,
    UTurnDecisionCertificate.idealTurns,
    certificate.leftMomentum.computedNegative_eq_idealNegative,
    certificate.rightMomentum.computedNegative_eq_idealNegative]

/-- Tree-local certificate proposition: only decisions actually visited by
this completed recursive tree need witnesses. -/
def RecursivePhaseTree.DecisionsAgree
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool) :
    RecursivePhaseTree Phase → Prop
  | .leaf phase => computedLeaf phase = idealLeaf phase
  | .node left right =>
      DecisionsAgree computedLeaf idealLeaf computedTurns idealTurns left ∧
        DecisionsAgree computedLeaf idealLeaf computedTurns idealTurns right ∧
        computedTurns left.leftmost right.rightmost =
          idealTurns left.leftmost right.rightmost

/-- A tree-local collection of certified primitive decisions suffices to
reproduce the exact ideal recursive flag tree. -/
theorem RecursivePhaseTree.toBuildFlagTree_eq_of_decisionsAgree
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool)
    (tree : RecursivePhaseTree Phase)
    (hagrees : Mcmc.Executable.Continuous.RecursivePhaseTree.DecisionsAgree
      computedLeaf idealLeaf computedTurns idealTurns tree) :
    tree.toBuildFlagTree computedLeaf computedTurns =
      tree.toBuildFlagTree idealLeaf idealTurns := by
  induction tree with
  | leaf phase =>
      simpa [RecursivePhaseTree.toBuildFlagTree,
        RecursivePhaseTree.DecisionsAgree] using hagrees
  | node left right ihLeft ihRight =>
      rcases hagrees with ⟨hleft, hright, hroot⟩
      simp [RecursivePhaseTree.toBuildFlagTree, ihLeft hleft, ihRight hright,
        hroot]

/-- Pointwise equality of certified leaf and endpoint decisions lifts through
the entire recursive `BuildTree` Boolean trace. -/
theorem RecursivePhaseTree.toBuildFlagTree_eq_of_decisions_eq
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool)
    (hleaf : ∀ phase, computedLeaf phase = idealLeaf phase)
    (hturns : ∀ left right, computedTurns left right = idealTurns left right)
    (tree : RecursivePhaseTree Phase) :
    tree.toBuildFlagTree computedLeaf computedTurns =
      tree.toBuildFlagTree idealLeaf idealTurns := by
  apply Mcmc.Executable.Continuous.RecursivePhaseTree.toBuildFlagTree_eq_of_decisionsAgree
    computedLeaf idealLeaf computedTurns idealTurns tree
  induction tree with
  | leaf phase => exact hleaf phase
  | node left right ihLeft ihRight =>
      exact ⟨ihLeft, ihRight, hturns left.leftmost right.rightmost⟩

/-- Consequently the numerical and ideal recursive continuation decisions are
identical whenever every primitive Boolean decision is certified. -/
theorem RecursivePhaseTree.continues_eq_of_decisions_eq
    {Phase : Type*}
    (computedLeaf idealLeaf : Phase → Bool)
    (computedTurns idealTurns : Phase → Phase → Bool)
    (hleaf : ∀ phase, computedLeaf phase = idealLeaf phase)
    (hturns : ∀ left right, computedTurns left right = idealTurns left right)
    (tree : RecursivePhaseTree Phase) :
    (tree.toBuildFlagTree computedLeaf computedTurns).continues =
      (tree.toBuildFlagTree idealLeaf idealTurns).continues := by
  exact congrArg NUTSBuildFlagTree.continues
    (Mcmc.Executable.Continuous.RecursivePhaseTree.toBuildFlagTree_eq_of_decisions_eq
      computedLeaf idealLeaf computedTurns idealTurns hleaf hturns tree)

end Mcmc.Executable.Continuous
