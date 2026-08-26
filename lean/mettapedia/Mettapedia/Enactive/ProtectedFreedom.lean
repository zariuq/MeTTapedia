import Mettapedia.Enactive.CompletionFibre
import Mettapedia.Evidence.SourceScoped

/-!
# Protected semantic and executable freedom

Completion freedom, uncertainty, and executable choice are different
mathematical objects:

* semantic freedom is the typed family of correct compatible completions;
* epistemic latitude is an observer fibre, containing states that the current
  view does not distinguish; and
* executable freedom is a semantic completion equipped with retained source,
  authority, realizability, and revision-currentness evidence.

The first notion follows Michael Timothy Bennett's completion semantics.  The
separation from observer-relative variety follows the process and
perspectival analyses of David Weinbaum, Francis Heylighen, and Viktoras
Veitas.  The receipt-indexed executable refinement is a project-original
bridge to proof-backed self-modification and native execution.

No cardinality is installed as the definition of freedom.  The finite canary
at the end shows why: maximizing unconstrained completion count can select an
ignorant policy that still permits a declared unsafe completion.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.ProtectedFreedom

open Mettapedia.Cybernetics
open Mettapedia.Evidence
open Mettapedia.Enactive

universe uWorld uState uView uFreedom uSource uRevision uAuthority uEvidence
  uProof uIndex uFamily

/-! ## Three orthogonal fibres -/

/-- Correct compatible refinements retained with their completion witness. -/
abbrev SemanticFreedom {World : Type uWorld}
    {layer : AbstractionLayer World} (policy : Aspect layer) : Type uWorld :=
  Completion.Fibre policy

/-- Possibilities retained because the selected observer identifies them. -/
abbrev EpistemicLatitude {State : Type uState} {View : Type uView}
    (observer : Observer State View) (view : View) : Type uState :=
  observer.Fibre view

/-- The evidence disciplines required to turn one semantic possibility into
an executable choice.  Authorization and realizability remain separate
proof-relevant families. -/
structure ExecutionDiscipline (Freedom : Type uFreedom) where
  Source : Type uSource
  Revision : Type uRevision
  Authority : Type uAuthority
  sourceDecidable : DecidableEq Source
  Authorized : Freedom -> Authority -> Type uEvidence
  Realizable : Freedom -> Type uEvidence

attribute [instance] ExecutionDiscipline.sourceDecidable

/-- A proof-relevant execution receipt issued at one exact revision.  Source
occurrences are retained rather than reconstructed from the semantic target. -/
structure IssuedReceipt {Freedom : Type uFreedom}
    (discipline : ExecutionDiscipline.{uFreedom, uSource, uRevision,
      uAuthority, uEvidence} Freedom)
    (choice : Freedom) where
  authority : discipline.Authority
  sources : Finset discipline.Source
  issuedAt : discipline.Revision
  authorized : discipline.Authorized choice authority
  realizable : discipline.Realizable choice

instance {Freedom : Type uFreedom}
    {discipline : ExecutionDiscipline.{uFreedom, uSource, uRevision,
      uAuthority, uEvidence} Freedom} {choice : Freedom} :
    SourceScoped (IssuedReceipt discipline choice) discipline.Source where
  sourceScope := IssuedReceipt.sources

/-- Currentness compares the retained issuance revision with the live one.
It is not derivable from authorization or realizability. -/
def IssuedReceipt.CurrentAt {Freedom : Type uFreedom}
    {discipline : ExecutionDiscipline.{uFreedom, uSource, uRevision,
      uAuthority, uEvidence} Freedom} {choice : Freedom}
    (receipt : IssuedReceipt discipline choice)
    (currentRevision : discipline.Revision) : Prop :=
  receipt.issuedAt = currentRevision

/-- Executable freedom is semantic freedom plus an exact current receipt.
The nested sigma retains which completion and which evidence licensed it. -/
abbrev ExecutableFreedom {Freedom : Type uFreedom}
    (discipline : ExecutionDiscipline.{uFreedom, uSource, uRevision,
      uAuthority, uEvidence} Freedom)
    (currentRevision : discipline.Revision) : Type _ :=
  Sigma fun choice : Freedom =>
    Sigma fun receipt : IssuedReceipt discipline choice =>
      PLift (receipt.CurrentAt currentRevision)

/-- Forget execution evidence without changing the selected semantic choice. -/
def ExecutableFreedom.semanticChoice {Freedom : Type uFreedom}
    {discipline : ExecutionDiscipline.{uFreedom, uSource, uRevision,
      uAuthority, uEvidence} Freedom}
    {currentRevision : discipline.Revision}
    (executable : ExecutableFreedom discipline currentRevision) : Freedom :=
  executable.1

/-- A stale issued receipt cannot license execution at the candidate
revision.  This obstruction does not refute the semantic choice. -/
theorem IssuedReceipt.not_currentAt_of_stale {Freedom : Type uFreedom}
    {discipline : ExecutionDiscipline.{uFreedom, uSource, uRevision,
      uAuthority, uEvidence} Freedom} {choice : Freedom}
    (receipt : IssuedReceipt discipline choice)
    {candidateRevision : discipline.Revision}
    (stale : receipt.issuedAt ≠ candidateRevision) :
    Not (receipt.CurrentAt candidateRevision) :=
  stale

/-! ## Proof-backed completion-preserving modification -/

/-- A proof-backed policy weakening.  The new policy adds no constraint not
already imposed by the old policy.  This is a sufficient, deliberately
non-universal class of completion-preserving modifications. -/
structure ProofBackedWeakening {World : Type uWorld}
    {layer : AbstractionLayer World} (oldPolicy newPolicy : Aspect layer)
    (Proof : Type uProof) where
  proof : Proof
  weakens : newPolicy <= oldPolicy

namespace ProofBackedWeakening

variable {World : Type uWorld} {layer : AbstractionLayer World}
variable {oldPolicy newPolicy : Aspect layer} {Proof : Type uProof}

/-- Transport an old semantic completion through policy weakening. -/
def mapCompletion (modification : ProofBackedWeakening oldPolicy newPolicy Proof) :
    SemanticFreedom oldPolicy -> SemanticFreedom newPolicy :=
  Completion.Fibre.contravariantEmbedding modification.weakens

/-- Completion transport preserves the exact target aspect, not only its
finite cardinal readout. -/
@[simp] theorem mapCompletion_target
    (modification : ProofBackedWeakening oldPolicy newPolicy Proof)
    (completion : SemanticFreedom oldPolicy) :
    (modification.mapCompletion completion).target = completion.target :=
  rfl

/-- Every protected target that was an old completion remains the same target
after a proof-backed weakening. -/
theorem preserves_protected_completion
    (modification : ProofBackedWeakening oldPolicy newPolicy Proof)
    (Protected : Set (Aspect layer))
    (completion : SemanticFreedom oldPolicy)
    (isProtected : completion.target ∈ Protected) :
    (modification.mapCompletion completion).target ∈ Protected := by
  simpa using isProtected

end ProofBackedWeakening

/-! ## A common protected-family transport interface -/

/-- Transport of informative fibres over a selected protected index family.
The fibres may carry completion proofs, observations, or other evidence; they
are not reduced to truth values or cardinalities. -/
structure ProtectedFamilyMap {Index : Type uIndex} (protectedIndices : Set Index)
    (Before After : Index -> Type uFamily) where
  map : forall index, index ∈ protectedIndices -> Before index -> After index

/-- The proof fibre witnessing that `target` completes `policy`. -/
abbrev CompletionAt {World : Type uWorld} {layer : AbstractionLayer World}
    (policy target : Aspect layer) : Type :=
  PLift (policy <= target)

/-- A proof-backed weakening induces one protected-family map on completion
fibres.  This packages the preceding pointwise theorem without losing the
target index. -/
def ProofBackedWeakening.protectedFamilyMap
    {World : Type uWorld} {layer : AbstractionLayer World}
    {oldPolicy newPolicy : Aspect layer} {Proof : Type uProof}
    (modification : ProofBackedWeakening oldPolicy newPolicy Proof)
    (Protected : Set (Aspect layer)) :
    ProtectedFamilyMap Protected (CompletionAt oldPolicy)
      (CompletionAt newPolicy) where
  map := by
    intro target _ oldCompletion
    exact ⟨modification.weakens.trans oldCompletion.down⟩

/-- A proof-backed weakening together with the source-scoped receipt that
currently licenses its proof.  The receipt is additional evidence; the order
theorem above remains the reason completions are preserved. -/
structure CurrentProofBackedWeakening {World : Type uWorld}
    {layer : AbstractionLayer World} (oldPolicy newPolicy : Aspect layer)
    (Proof : Type uProof)
    (discipline : ExecutionDiscipline.{uProof, uSource, uRevision,
      uAuthority, uEvidence} Proof)
    (currentRevision : discipline.Revision) where
  modification : ProofBackedWeakening oldPolicy newPolicy Proof
  receipt : IssuedReceipt discipline modification.proof
  current : receipt.CurrentAt currentRevision

namespace CurrentProofBackedWeakening

variable {World : Type uWorld} {layer : AbstractionLayer World}
variable {oldPolicy newPolicy : Aspect layer} {Proof : Type uProof}
variable {discipline : ExecutionDiscipline.{uProof, uSource, uRevision,
  uAuthority, uEvidence} Proof}
variable {currentRevision : discipline.Revision}

/-- Current proof evidence and semantic preservation are returned together,
without treating either one as derivable from the other. -/
theorem preserves_protected_completion
    (admitted : CurrentProofBackedWeakening oldPolicy newPolicy Proof
      discipline currentRevision)
    (Protected : Set (Aspect layer))
    (completion : SemanticFreedom oldPolicy)
    (isProtected : completion.target ∈ Protected) :
    (admitted.modification.mapCompletion completion).target ∈ Protected ∧
      admitted.receipt.CurrentAt currentRevision :=
  ⟨admitted.modification.preserves_protected_completion Protected completion
    isProtected, admitted.current⟩

end CurrentProofBackedWeakening

/-! ## Observer-level preservation interface -/

/-- Exact preservation of a selected family of observations.  This is the
common interface used downstream to connect completion preservation with
existing dynamic-individuation protected-goal theorems. -/
def ProtectedObservationAgreement {Goal : Type*} {Value : Type*}
    (protectedGoals : Set Goal) (before after : Goal -> Value) : Prop :=
  forall goal, goal ∈ protectedGoals -> before goal = after goal

/-- The singleton fibre retaining the exact value observed at one goal. -/
abbrev ObservationFibre {Goal : Type uIndex} {Value : Type uFamily}
    (observe : Goal -> Value) (goal : Goal) : Type uFamily :=
  {value : Value // observe goal = value}

/-- Exact protected observation agreement transports the informative value
fibres without changing the retained values. -/
def protectedObservationFamilyMap
    {Goal : Type uIndex} {Value : Type uFamily}
    {protectedGoals : Set Goal} {before after : Goal -> Value}
    (agreement : ProtectedObservationAgreement protectedGoals before after) :
    ProtectedFamilyMap protectedGoals (ObservationFibre before)
      (ObservationFibre after) where
  map := by
    intro goal protectedGoal observed
    exact ⟨observed.1,
      (agreement goal protectedGoal).symm.trans observed.2⟩

/-! ## Positive and negative controls -/

namespace Canary

/-- A coarse view can retain two epistemic possibilities without altering
any semantic completion family. -/
def constantObserver : Observer Bool Unit where
  observe := fun _ => ()

def hiddenFalse : EpistemicLatitude constantObserver () := ⟨false, rfl⟩
def hiddenTrue : EpistemicLatitude constantObserver () := ⟨true, rfl⟩

theorem hidden_states_remain_distinct : hiddenFalse ≠ hiddenTrue := by
  intro equal
  have : false = true := congrArg Subtype.val equal
  contradiction

def receiptDiscipline : ExecutionDiscipline Unit where
  Source := Fin 2
  Revision := Bool
  Authority := Unit
  sourceDecidable := inferInstance
  Authorized := fun _ _ => Unit
  Realizable := fun _ => Unit

def issuedAtFalse : IssuedReceipt receiptDiscipline () where
  authority := ()
  sources := by
    change Finset (Fin 2)
    exact {0}
  issuedAt := false
  authorized := ()
  realizable := ()

theorem issuedAtFalse_current : issuedAtFalse.CurrentAt false :=
  by simp [IssuedReceipt.CurrentAt, issuedAtFalse, receiptDiscipline]

theorem issuedAtFalse_stale_at_true :
    Not (issuedAtFalse.CurrentAt true) := by
  simp [IssuedReceipt.CurrentAt, issuedAtFalse, receiptDiscipline]

open Mettapedia.Enactive.Finite

abbrev oldPolicy : Aspect Finite.Canary.boolLayer.toAbstract :=
  Finite.Canary.trueStatement.toAbstract

abbrev weakenedPolicy : Aspect Finite.Canary.boolLayer.toAbstract :=
  Finite.Canary.emptyStatement.toAbstract

def proofBackedWeakening :
    ProofBackedWeakening oldPolicy weakenedPolicy Unit where
  proof := ()
  weakens := Finite.Canary.empty_completes_to_true_abstractly

def currentProofBackedWeakening :
    CurrentProofBackedWeakening oldPolicy weakenedPolicy Unit
      receiptDiscipline false where
  modification := proofBackedWeakening
  receipt := issuedAtFalse
  current := issuedAtFalse_current

def protectedOldCompletion : SemanticFreedom oldPolicy :=
  ⟨oldPolicy, le_rfl⟩

/-- Positive control: a genuinely source-scoped, current proof-backed
weakening preserves the exact protected completion target. -/
theorem current_weakening_preserves_old_completion :
    (currentProofBackedWeakening.modification.mapCompletion
      protectedOldCompletion).target ∈ ({oldPolicy} : Set _) ∧
      currentProofBackedWeakening.receipt.CurrentAt false := by
  have isProtected :
      protectedOldCompletion.target ∈ ({oldPolicy} : Set _) := by
    change oldPolicy ∈ ({oldPolicy} : Set _)
    simp
  exact currentProofBackedWeakening.preserves_protected_completion
    {oldPolicy} protectedOldCompletion isProtected

def falseStatement : Finite.Canary.boolLayer.Statement :=
  ⟨{Finite.Canary.falseFact}, by decide⟩

/-- The ignorant policy has strictly more completions than the safe policy,
but one of those extra completions is the declared unsafe false statement. -/
theorem unconstrained_weakness_prefers_policy_with_unsafe_completion :
    Finite.Canary.boolLayer.weakness Finite.Canary.trueStatement <
        Finite.Canary.boolLayer.weakness Finite.Canary.emptyStatement ∧
      falseStatement ∈
        Finite.Canary.boolLayer.extension Finite.Canary.emptyStatement ∧
      falseStatement ∉
        Finite.Canary.boolLayer.extension Finite.Canary.trueStatement := by
  decide

end Canary

end Mettapedia.Enactive.ProtectedFreedom

#print axioms Mettapedia.Enactive.ProtectedFreedom.ProofBackedWeakening.preserves_protected_completion
#print axioms Mettapedia.Enactive.ProtectedFreedom.ProofBackedWeakening.protectedFamilyMap
#print axioms Mettapedia.Enactive.ProtectedFreedom.CurrentProofBackedWeakening.preserves_protected_completion
#print axioms Mettapedia.Enactive.ProtectedFreedom.Canary.current_weakening_preserves_old_completion
#print axioms Mettapedia.Enactive.ProtectedFreedom.Canary.unconstrained_weakness_prefers_policy_with_unsafe_completion
