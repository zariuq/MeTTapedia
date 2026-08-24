import Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension

/-!
# Checked inference as a displayed native realization

A generic inference checker, an independent proof-relevant interpretation,
and a native calculus have three different carriers.  This module gives their
weakest common waist without identifying them:

* a checked derivation retains its exact authored proof tree;
* independent semantics assigns evidence to that derivation;
* a native realization projects the evidence to a calculus-specific artifact;
* the graph of that projection retains both the evidence and the artifact.

The artifact projection is not assumed faithful.  Faithfulness is an earned
capability, characterized exactly as injectivity of the graph projection.  A
negative canary proves why retaining the graph matters: two semantic witnesses
may produce the same native artifact while remaining distinct in the retained
realization.

The construction is deliberately independent of Prime syntax.  A Prime
instance chooses intrinsically typed contextual terms as its artifacts; a
different NIK-hosted language may choose its own maximal native calculus.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension

universe uGoal uEvidence uArtifact

/-! ## A native projection and its retained graph -/

/-- A calculus-specific realization of a proof-relevant evidence family.
No injectivity premise is imposed: a native artifact may be an intentionally
lossy projection of retained semantic evidence. -/
structure NativeRealization (Goal : Type uGoal)
    (Evidence : Goal → Type uEvidence) where
  Artifact : Goal → Type uArtifact
  realize : ∀ goal, Evidence goal → Artifact goal

namespace NativeRealization

variable {Goal : Type uGoal} {Evidence : Goal → Type uEvidence}
    (realization : NativeRealization Goal Evidence)

/-- The graph of native realization.  Evidence remains a first-class field;
the equality witnesses that the accompanying artifact is its declared native
projection. -/
structure Graph (goal : Goal) where
  evidence : Evidence goal
  artifact : realization.Artifact goal
  agrees : artifact = realization.realize goal evidence

namespace Graph

variable {realization}

/-- Every semantic witness has a canonical point in the retained graph. -/
def embed {goal : Goal} (evidence : Evidence goal) :
    realization.Graph goal where
  evidence := evidence
  artifact := realization.realize goal evidence
  agrees := rfl

@[simp] theorem embed_evidence {goal : Goal} (evidence : Evidence goal) :
    (embed (realization := realization) evidence).evidence = evidence :=
  rfl

@[simp] theorem embed_artifact {goal : Goal} (evidence : Evidence goal) :
    (embed (realization := realization) evidence).artifact =
      realization.realize goal evidence :=
  rfl

/-- Equality in the retained graph is determined by retained evidence; the
artifact and agreement proof then follow from the graph law. -/
@[ext] theorem ext {goal : Goal}
    {first second : realization.Graph goal}
    (evidence : first.evidence = second.evidence) : first = second := by
  cases first with
  | mk firstEvidence firstArtifact firstAgreement =>
    cases second with
    | mk secondEvidence secondArtifact secondAgreement =>
      dsimp at evidence
      subst secondEvidence
      cases firstAgreement
      cases secondAgreement
      rfl

/-- The retained embedding never identifies semantic witnesses, regardless
of whether the artifact projection is faithful. -/
theorem embed_injective {goal : Goal} :
    Function.Injective (embed (realization := realization) (goal := goal)) := by
  intro first second equality
  exact congrArg Graph.evidence equality

end Graph

/-- Artifact faithfulness is a capability of a particular native
realization, not a default property of checked semantics. -/
def ArtifactFaithful : Prop :=
  ∀ goal, Function.Injective (realization.realize goal)

/-- Equivalent graph-level formulation: the artifact projection is
injective exactly when native realization retains the full evidence fibre. -/
theorem artifactFaithful_iff_graphProjectionInjective :
    realization.ArtifactFaithful ↔
      ∀ goal,
        Function.Injective
          (fun point : realization.Graph goal => point.artifact) := by
  constructor
  · intro faithful goal first second artifacts
    apply Graph.ext
    apply faithful goal
    calc
      realization.realize goal first.evidence = first.artifact :=
        first.agrees.symm
      _ = second.artifact := artifacts
      _ = realization.realize goal second.evidence := second.agrees
  · intro graphFaithful goal first second artifacts
    have artifactEquality :
        (Graph.embed (realization := realization) first).artifact =
          (Graph.embed (realization := realization) second).artifact :=
      artifacts
    have graphEquality := graphFaithful goal artifactEquality
    exact congrArg Graph.evidence graphEquality

/-! ## Negative canary: artifact equality need not be evidence equality -/

namespace ProjectionCanary

def CanaryEvidence (_ : Unit) := Bool

def collapsing : NativeRealization Unit CanaryEvidence where
  Artifact := fun _ => Unit
  realize := fun _ _ => ()

def first : collapsing.Graph () :=
  Graph.embed (realization := collapsing) false

def second : collapsing.Graph () :=
  Graph.embed (realization := collapsing) true

theorem retained_points_distinct : first ≠ second := by
  intro equality
  have evidenceEquality := congrArg Graph.evidence equality
  simp [first, second] at evidenceEquality

theorem projected_artifacts_equal : first.artifact = second.artifact :=
  rfl

theorem artifact_projection_not_faithful :
    ¬ collapsing.ArtifactFaithful := by
  intro faithful
  have impossible : false = true := @faithful () false true rfl
  exact Bool.false_ne_true impossible

end ProjectionCanary

end NativeRealization

/-! ## The checked-to-native waist -/

/-- One validated inference presentation equipped independently with
proof-relevant semantics and a displayed native realization for a named goal
family. -/
structure CheckedNativeWaist (presentation : ValidatedPresentation) where
  Meaning : Pattern → Type uEvidence
  semantics : PresentationSemantics presentation Meaning
  Goal : Type uGoal
  surface : Goal → Pattern
  native : NativeRealization.{uGoal, uEvidence, uArtifact} Goal
    (fun goal => Meaning (surface goal))

namespace CheckedNativeWaist

variable {presentation : ValidatedPresentation}
    (waist : CheckedNativeWaist presentation)

/-- A checked derivation in one supported goal fibre. -/
structure CheckedProgram (goal : waist.Goal) : Type where
  checked : Derivation presentation (waist.surface goal)

namespace CheckedProgram

variable {waist}

/-- Independent semantic evidence produced from the exact checked tree. -/
def evidence {goal : waist.Goal} (program : waist.CheckedProgram goal) :
    waist.Meaning (waist.surface goal) :=
  waist.semantics.interpret program.checked

/-- The complete retained native graph point. -/
def realized {goal : waist.Goal} (program : waist.CheckedProgram goal) :
    waist.native.Graph goal :=
  NativeRealization.Graph.embed (realization := waist.native) program.evidence

/-- The native artifact projection.  Consumers that require proof identity
must retain `realized`, not only this projection. -/
def artifact {goal : waist.Goal} (program : waist.CheckedProgram goal) :
    waist.native.Artifact goal :=
  program.realized.artifact

@[simp] theorem realized_evidence {goal : waist.Goal}
    (program : waist.CheckedProgram goal) :
    program.realized.evidence = program.evidence :=
  rfl

@[simp] theorem artifact_eq_realize {goal : waist.Goal}
    (program : waist.CheckedProgram goal) :
    program.artifact = waist.native.realize goal program.evidence :=
  rfl

/-- Even a lossy artifact cannot erase evidence from the retained graph. -/
theorem evidence_eq_of_realized_eq {goal : waist.Goal}
    (first second : waist.CheckedProgram goal)
    (equal : first.realized = second.realized) :
    first.evidence = second.evidence :=
  congrArg NativeRealization.Graph.evidence equal

/-- When a native realization earns artifact faithfulness, equality of hot
artifacts is sufficient to recover equality of semantic evidence. -/
theorem evidence_eq_of_artifact_eq
    (faithful : waist.native.ArtifactFaithful)
    {goal : waist.Goal} (first second : waist.CheckedProgram goal)
    (equal : first.artifact = second.artifact) :
    first.evidence = second.evidence := by
  apply faithful goal
  simpa only [artifact_eq_realize] using equal

end CheckedProgram

/-- A checked externally supplied proof with its exact raw erasure. -/
structure CheckedRawProgram (goal : waist.Goal) (raw : RawProof) : Type where
  checked : Derivation presentation (waist.surface goal)
  erases : checked.erase = raw

namespace CheckedRawProgram

variable {waist}

def toChecked {goal : waist.Goal} {raw : RawProof}
    (program : waist.CheckedRawProgram goal raw) :
    waist.CheckedProgram goal :=
  ⟨program.checked⟩

@[simp] theorem toChecked_erase {goal : waist.Goal} {raw : RawProof}
    (program : waist.CheckedRawProgram goal raw) :
    program.toChecked.checked.erase = raw :=
  program.erases

end CheckedRawProgram

/-- Generic raw checking is exact for the retained waist: acceptance is
equivalent to an exact-erasing checked program.  The native layer adds no new
proofs and rejects no checked proofs in its declared goal family. -/
theorem checkRaw_iff_nonempty
    (goal : waist.Goal) (raw : RawProof) :
    checkRaw presentation (waist.surface goal) raw = true ↔
      Nonempty (waist.CheckedRawProgram goal raw) := by
  constructor
  · intro accepted
    rcases (G2_checkRaw_iff_exists_derivation_erases_to.mp accepted) with
      ⟨derivation, erases⟩
    exact ⟨⟨derivation, erases⟩⟩
  · rintro ⟨program⟩
    rw [← program.erases]
    exact checkRaw_erase program.checked

#print axioms NativeRealization.Graph.embed_injective
#print axioms NativeRealization.artifactFaithful_iff_graphProjectionInjective
#print axioms NativeRealization.ProjectionCanary.retained_points_distinct
#print axioms NativeRealization.ProjectionCanary.projected_artifacts_equal
#print axioms NativeRealization.ProjectionCanary.artifact_projection_not_faithful
#print axioms CheckedProgram.evidence_eq_of_realized_eq
#print axioms CheckedProgram.evidence_eq_of_artifact_eq
#print axioms checkRaw_iff_nonempty

end CheckedNativeWaist
end Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
