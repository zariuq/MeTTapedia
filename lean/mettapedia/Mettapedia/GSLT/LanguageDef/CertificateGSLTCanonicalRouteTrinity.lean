import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily
import Mettapedia.Computability.ComputationalTrinity

/-!
# A scoped computational trinity for completed certificate routes

The operational face stores actual completed search routes with their final
ordered premise-use ledgers. Its representation carries a certificate of
route canonicality. Every completed route of the pending-first machine
satisfies that certificate, as proved by `canonicalCompleteRoute_eq`; the
certificate therefore filters out no completed routes. Contextual substitution
is the separately established route-receipt action, which reconstructs,
substitutes, and runs the proof. Scheduling or failed search branches of a
different execution machine are not represented here.

The intensional face stores authored open derivations. Its natural comparison
with the canonical operational face is invertible. The extensional face keeps
only the goal and ledger, so its observation may still forget a rule choice.
None of this supplies an authored Prime dependent type former or a general
execution decision procedure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.Computability.ComputationalTrinity
open OpenSearchMachine

/-- One canonical operational answer retains its goal, exact final ledger,
and proof-relevant sequence of rule and assumption steps. -/
def CanonicalRouteAnswer
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) : Type :=
  Σ goal : Pattern,
    { receipt : Σ ledger : List (Fin context.judgments.length),
        Route (Step definition context.judgments)
          ⟨[goal], []⟩ ⟨[], ledger⟩ //
      canonicalCompleteRoute receipt.2 = receipt.2 }

/-- The canonicality certificate excludes no completed machine route.
This equivalence keeps the actual goal, ledger, and route unchanged. -/
def completedRouteAnswerEquiv
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) :
    (Σ goal : Pattern, Σ ledger : List (Fin context.judgments.length),
      Route (Step definition context.judgments)
        ⟨[goal], []⟩ ⟨[], ledger⟩) ≃
      CanonicalRouteAnswer definition context where
  toFun answer := ⟨answer.1, ⟨answer.2,
    canonicalCompleteRoute_eq answer.2.2⟩⟩
  invFun answer := ⟨answer.1, answer.2.val⟩
  left_inv := by rintro ⟨goal, receipt⟩; rfl
  right_inv := by rintro ⟨goal, ⟨receipt, fixed⟩⟩; rfl

def proofOfCanonicalRoute
    {definition : ValidatedCalculusLanguageDef}
    {context : ClassifyingContext definition}
    (answer : CanonicalRouteAnswer definition context) :
    (derivationTotalFace definition).obj (Opposite.op context) :=
  ⟨answer.1, derivationOfCompleteRoute answer.2.val.2⟩

def canonicalRouteOfProof
    {definition : ValidatedCalculusLanguageDef}
    {context : ClassifyingContext definition}
    (answer : (derivationTotalFace definition).obj (Opposite.op context)) :
    CanonicalRouteAnswer definition context :=
  ⟨answer.1, ⟨completeRouteReceipt answer.2,
    canonicalCompleteRoute_runToCompletion answer.2⟩⟩

/-- The completed operational routes and authored proof face agree
objectwise without identifying their representation types. -/
def canonicalRouteProofEquiv
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) :
    CanonicalRouteAnswer definition context ≃
      (derivationTotalFace definition).obj (Opposite.op context) where
  toFun := proofOfCanonicalRoute
  invFun := canonicalRouteOfProof
  left_inv := by
    rintro ⟨goal, ⟨receipt, fixed⟩⟩
    dsimp [canonicalRouteOfProof, proofOfCanonicalRoute]
    exact congrArg (Sigma.mk goal)
      (Subtype.ext (completeRouteReceipt_reconstruct_of_fixed receipt fixed))
  right_inv := by
    rintro ⟨goal, derivation⟩
    exact congrArg (Sigma.mk goal)
      (derivationOfCompleteRoute_runToCompletion derivation)

/-- Contextual substitution of canonical routes is the genuine operational
receipt action; it stays canonical and satisfies identity and composition. -/
def canonicalRouteFace (definition : ValidatedCalculusLanguageDef) :
    Face (ClassifyingContext definition) where
  obj context := CanonicalRouteAnswer definition context.unop
  map substitution := TypeCat.ofHom fun answer =>
    ⟨answer.1,
      ⟨mapCompleteRouteReceipt substitution.unop answer.2.val,
        mapCompleteRouteReceipt_fixed substitution.unop answer.2.val⟩⟩
  map_id context := by
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, ⟨receipt, fixed⟩⟩
    exact congrArg (Sigma.mk goal)
      (Subtype.ext (mapCompleteRouteReceipt_id receipt))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, ⟨receipt, fixed⟩⟩
    exact congrArg (Sigma.mk goal)
      (Subtype.ext
        (mapCompleteRouteReceipt_comp first.unop second.unop receipt).symm)

/-- Reconstructing after contextual substitution equals substituting the
reconstructed proof. This is the naturality square of the operational-to-
intensional comparison. -/
theorem proofOfCanonicalRoute_reindex
    (definition : ValidatedCalculusLanguageDef)
    {source target : (ClassifyingContext definition)ᵒᵖ}
    (substitution : source ⟶ target)
    (answer : (canonicalRouteFace definition).obj source) :
    proofOfCanonicalRoute
        ((canonicalRouteFace definition).map substitution answer) =
      (derivationTotalFace definition).map substitution
        (proofOfCanonicalRoute answer) := by
  exact congrArg (Sigma.mk answer.1)
    (mapCompleteRouteReceipt_reconstruct substitution.unop answer.2.val)

/-- Completed operational routes and authored open proofs are naturally
isomorphic. The canonicality field imposes no further restriction, by
`completedRouteAnswerEquiv`. -/
def canonicalRouteProofIso
    (definition : ValidatedCalculusLanguageDef) :
    canonicalRouteFace definition ≅ derivationTotalFace definition := by
  refine NatIso.ofComponents
    (fun context =>
      (canonicalRouteProofEquiv definition context.unop).toIso)
    ?_
  intro source target substitution
  apply ConcreteCategory.hom_ext
  intro answer
  exact proofOfCanonicalRoute_reindex definition substitution answer

/-- The semantic total of the proof-relevant displayed family and the
completed operational-route presheaf agree naturally through their exact
comparisons with the authored proof face. -/
def exactDerivationTotalRouteIso
    (definition : ValidatedCalculusLanguageDef) :
    Mettapedia.TypeTheory.DisplayedPresheafComprehension.totalSpace
        (exactDerivationDisplayedFamily definition) ≅
      canonicalRouteFace definition :=
  exactDerivationTotalIso definition ≪≫ (canonicalRouteProofIso definition).symm

/-- The spatial observation forgets the proof tree while retaining the
unchanged goal and exact ordered premise-use ledger. -/
def canonicalRouteObservation
    (definition : ValidatedCalculusLanguageDef) :
    canonicalRouteFace definition ⟶ goalLedgerFace definition :=
  (canonicalRouteProofIso definition).hom ≫
    derivationToGoalLedger definition

/-- A concrete contextual comparison of the three faces. Exactness is not
claimed: goal-and-ledger observation may identify distinct rule proofs. -/
def canonicalRouteComparison
    (definition : ValidatedCalculusLanguageDef) :
    Comparison (ClassifyingContext definition) where
  program := canonicalRouteFace definition
  logic := derivationTotalFace definition
  space := goalLedgerFace definition
  programToLogic := (canonicalRouteProofIso definition).hom
  logicToSpace := derivationToGoalLedger definition
  programToSpace := canonicalRouteObservation definition
  coherence := rfl

/-- The actual closure-modal completion predicate at one contextual goal
and exact ordered discharge ledger. -/
def ExactCompletionSupport
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (answer : Pattern × List (Fin context.judgments.length)) : Prop :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
    (OpenSearchModalAdequacy.theory definition context.judgments).closure
    (fun candidate => candidate =
      (⟨[], answer.2⟩ : OpenSearchMachine.State context.judgments))
    ⟨[answer.1], []⟩

/-- Contextual modal support is a subpresheaf of goal-and-ledger data.
Transport uses the proved exact-completion law, not an assumed invariance
of arbitrary modal predicates. -/
def completionSupportFace (definition : ValidatedCalculusLanguageDef) :
    Face (ClassifyingContext definition) where
  obj context := { answer : Pattern × List (Fin context.unop.judgments.length) //
    ExactCompletionSupport definition context.unop answer }
  map substitution := TypeCat.ofHom fun answer =>
    ⟨(answer.1.1, mapLedger substitution.unop answer.1.2),
      exactCompletionDiamond_reindex definition substitution.unop
        answer.1.1 answer.1.2 answer.2⟩
  map_id context := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨goal, ledger⟩, completion⟩
    apply Subtype.ext
    exact congrArg (fun uses => (goal, uses))
      (mapLedger_id definition context.unop.judgments ledger)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨goal, ledger⟩, completion⟩
    apply Subtype.ext
    exact congrArg (fun uses => (goal, uses))
      (mapLedger_comp first.unop second.unop ledger)

/-- An authored proof yields the closure-modal completion support for its
actual ordered premise-use ledger; proof identity is forgotten only here. -/
def derivationToCompletionSupport
    (definition : ValidatedCalculusLanguageDef) :
    derivationTotalFace definition ⟶ completionSupportFace definition where
  app context := TypeCat.ofHom fun answer =>
    ⟨(answer.1, holeOccurrences answer.2),
      (exactDerivationFibre_nonempty_iff_closureDiamond definition
        context.unop answer.1 (holeOccurrences answer.2)).mp
        ⟨⟨answer.2, rfl⟩⟩⟩
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, derivation⟩
    apply Subtype.ext
    exact congrArg (fun uses => (goal, uses))
      (holeOccurrences_bind derivation substitution.unop)

/-- Forgetting modal support gives the previously defined goal-and-ledger
observation, with no choice of representative proof. -/
def forgetCompletionSupport
    (definition : ValidatedCalculusLanguageDef) :
    completionSupportFace definition ⟶ goalLedgerFace definition where
  app _ := TypeCat.ofHom Subtype.val
  naturality := by
    intro source target substitution
    apply ConcreteCategory.hom_ext
    intro answer
    rfl

theorem derivationToCompletionSupport_forget
    (definition : ValidatedCalculusLanguageDef) :
    derivationToCompletionSupport definition ≫
        forgetCompletionSupport definition =
      derivationToGoalLedger definition := by
  ext context answer
  rfl

/-- The same operational/intensional comparison now reaches the actual
OSLF closure-modal completion support, rather than only its data index. -/
def canonicalRouteModalComparison
    (definition : ValidatedCalculusLanguageDef) :
    Comparison (ClassifyingContext definition) where
  program := canonicalRouteFace definition
  logic := derivationTotalFace definition
  space := completionSupportFace definition
  programToLogic := (canonicalRouteProofIso definition).hom
  logicToSpace := derivationToCompletionSupport definition
  programToSpace := (canonicalRouteProofIso definition).hom ≫
    derivationToCompletionSupport definition
  coherence := rfl

theorem canonicalRouteModalComparison_forget
    (definition : ValidatedCalculusLanguageDef) :
    (canonicalRouteModalComparison definition).programToSpace ≫
        forgetCompletionSupport definition =
      (canonicalRouteComparison definition).programToSpace := by
  change ((canonicalRouteProofIso definition).hom ≫
      derivationToCompletionSupport definition) ≫
        forgetCompletionSupport definition =
      (canonicalRouteProofIso definition).hom ≫
        derivationToGoalLedger definition
  rw [Category.assoc, derivationToCompletionSupport_forget]

end Mettapedia.GSLT.LanguageDef.CertificateGSLT

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.canonicalRouteProofEquiv
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.completedRouteAnswerEquiv
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.canonicalRouteFace
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.proofOfCanonicalRoute_reindex
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.canonicalRouteProofIso
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.exactDerivationTotalRouteIso
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.canonicalRouteComparison
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.completionSupportFace
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.derivationToCompletionSupport
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.derivationToCompletionSupport_forget
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.canonicalRouteModalComparison
#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.canonicalRouteModalComparison_forget
