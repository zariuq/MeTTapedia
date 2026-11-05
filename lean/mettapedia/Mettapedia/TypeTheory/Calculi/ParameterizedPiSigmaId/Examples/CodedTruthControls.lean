import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedTruthProofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.AnnotatedPredicatePolymorphism

/-!
# Retained truth-code proofs and a distinct-code refusal

The two set axioms remain hypotheses of the generated proofs. A separate
actual-set interpretation satisfies them and rejects a truth code of an
equation between two distinct sets. This does not install those hypotheses
as native axioms or identify intensional source identity with set equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.CodedTruthControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open TowerInterpretation CodedHOL
open HOL.Embedding

abbrev Constants := Symbol Nat
abbrev core : SetComprehensionProofs.Core Constants := Symbol.core
def left : ClosedTerm Constants object := .const (.head 0)
def right : ClosedTerm Constants object := .const (.head 1)
def witness : ClosedTerm Constants object := .const (.head 2)

abbrev basis : List (ClosedFormula Constants) :=
  [SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.powerLaw,
   SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw]

def reflexiveClaim : ClosedFormula Constants :=
  memberAt (.const (.core .empty)) (SetComprehensionProofs.truthCode core (.eq left left))

def reflexiveProof : ProofSyntax Constants basis reflexiveClaim :=
  SetComprehensionProofs.identityIntro core left (.hyp (Δ := basis) 0) (.hyp (Δ := basis) 1)

theorem reflexiveProof_free : reflexiveProof.FunctionExtensionalityFree :=
  SetComprehensionProofs.truthIntro_free core (.eq left left) (.hyp (Δ := basis) 0) (.hyp (Δ := basis) 1) (.eqRefl left)
    trivial trivial trivial

def equalityClaim : ClosedFormula Constants :=
  memberAt witness (SetComprehensionProofs.truthCode core (.eq left right))

abbrev reflectionBasis : List (ClosedFormula Constants) :=
  [SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.separationLaw, equalityClaim]

def reflectionProof : ProofSyntax Constants reflectionBasis (.eq left right) :=
  SetComprehensionProofs.identityReflect core left right witness (.hyp (Δ := reflectionBasis) 0) (.hyp (Δ := reflectionBasis) 1)

theorem reflectionProof_free : reflectionProof.FunctionExtensionalityFree :=
  SetComprehensionProofs.truthReflect_free core (.eq left right) witness (.hyp (Δ := reflectionBasis) 0) (.hyp (Δ := reflectionBasis) 1)
    trivial trivial

def function : ClosedTerm Constants (object ⇒ object) :=
  .app (.const .application) (.const (.head 3))

def transportClaim : ClosedFormula Constants := .eq (.app function left) (.app function right)
def transportProof : ProofSyntax Constants reflectionBasis transportClaim :=
  .eqAppArg function reflectionProof

theorem transportProof_free : transportProof.FunctionExtensionalityFree := reflectionProof_free

abbrev sourceStatement : Presentation.TypedEquality.Annotated.CStatement Nat :=
  .typing .nil (.refl (.head 0)) (.id (.head 1) (.head 0) (.head 0))

theorem sourceStatement_derivable :
    Presentation.TypedEquality.Annotated.CDerivable AnnotatedPredicatePolymorphism.church sourceStatement :=
  .reflIntro (.headType rfl)

def sourceClaim : ClosedFormula Constants :=
  TruthProofs.expand (judgmentAt sourceStatement Fin.elim0)

def sourceProof : ProofSyntax Constants basis sourceClaim :=
  TruthProofs.reflexivityJudgment .nil (.head 1) (.head 0) Fin.elim0
    (.hyp (Δ := basis) 0) (.hyp (Δ := basis) 1)

theorem sourceProof_free : sourceProof.FunctionExtensionalityFree :=
  TruthProofs.reflexivityJudgment_free .nil (.head 1) (.head 0) Fin.elim0
    (.hyp (Δ := basis) 0) (.hyp (Δ := basis) 1) trivial trivial

def heads (index : Nat) : ZFSet.{0} := if index = 1 then {∅} else ∅
def constants (_ : Presentation.DeclName) : ZFSet.{0} := ∅
noncomputable abbrev actualModel := model heads constants

theorem basis_valid : ∀ formula ∈ basis, actualModel.models formula := by
  intro formula present
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · intro a _ b _
    change ZFSet.{0} at a b
    change (b ∈ ZFSet.powerset a → ∀ x : ZFSet, True → x ∈ b → x ∈ a) ∧
      ((∀ x : ZFSet, True → x ∈ b → x ∈ a) → b ∈ ZFSet.powerset a)
    exact ⟨fun h x _ hx => ZFSet.mem_powerset.mp h hx,
      fun h => ZFSet.mem_powerset.mpr (fun x hx => h x trivial hx)⟩
  · intro a _ predicate _ x _
    change ZFSet.{0} at a x
    change ZFSet.{0} → ULift.{1} Prop at predicate
    change (x ∈ ZFSet.sep (fun y => (predicate y).down) a → x ∈ a ∧ (predicate x).down) ∧
      (x ∈ a ∧ (predicate x).down → x ∈ ZFSet.sep (fun y => (predicate y).down) a)
    exact ⟨(ZFSet.mem_sep (p := fun y => (predicate y).down)).mp,
      (ZFSet.mem_sep (p := fun y => (predicate y).down)).mpr⟩

theorem unequal : (∅ : ZFSet.{0}) ≠ {∅} := by
  intro same
  have member : (∅ : ZFSet.{0}) ∈ ({∅} : ZFSet) := ZFSet.mem_singleton.mpr rfl
  rw [← same] at member
  exact ZFSet.notMem_empty _ member

theorem rejects_distinct_codes : ¬ actualModel.models equalityClaim := by
  change ¬ ((∅ : ZFSet.{0}) ∈ ZFSet.sep (fun _ => (∅ : ZFSet.{0}) = {∅})
    (ZFSet.powerset ∅))
  exact fun proof => unequal (ZFSet.mem_sep.mp proof).2

theorem no_distinct_identity_proof : ¬ Nonempty (ProofSyntax Constants basis equalityClaim) := by
  rintro ⟨proof⟩
  apply rejects_distinct_codes
  exact HOL.Soundness.extDerivation_sound proof.erase
    (actualModel.functionsRespectEqv_of_fullDomains
      (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) basis_valid

theorem expansion_preserves_claim :
    actualModel.denote (TruthProofs.expand reflexiveClaim) (fun index => nomatch index) =
      actualModel.denote reflexiveClaim (fun index => nomatch index) :=
  TruthProofs.denote_expand heads constants reflexiveClaim _

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.CodedTruthControls
