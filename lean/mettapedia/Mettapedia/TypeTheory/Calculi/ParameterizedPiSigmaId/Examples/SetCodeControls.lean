import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeTypingProofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.AnnotatedPredicatePolymorphism

/-!
# Source application receipts and a wrong product definition

The positive source derivation applies identity to a reflexivity witness.
Its actual premise receipts feed the generic application producer. A separate
model control rejects a product body that always returns the empty set.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open TowerInterpretation CodedHOL
open HOL.Embedding
open SetComprehensionProofs SetMembershipProofs
namespace Source
def carrier {n : Nat} : CTm Nat n := .id (.head 1) (.head 0) (.head 0)
def identity : CTm Nat 0 := .lam carrier (.var 0)
def argument : CTm Nat 0 := .refl (.head 0)
def functionType : CTm Nat 0 := .pi carrier carrier
def statement : CStatement Nat := .typing .nil (.app identity argument) (CTm.inst0 argument carrier)
abbrev church := AnnotatedPredicatePolymorphism.church

theorem carrier_typed {n : Nat} {context : CCtx Nat n} : CTyped church context carrier (.head 2) :=
  .idForm (.headType rfl) (by change 0 < 2; decide) (.headType rfl) (.headType rfl)

theorem identity_typed : CTyped church .nil identity functionType :=
  .lamIntro carrier_typed (by change 0 < 2; decide)
    (.piForm carrier_typed (by change 0 < 2; decide) carrier_typed (by change 0 < 2; decide) rfl)
    (by change 0 < 2; decide) (.var 0)

theorem argument_typed : CTyped church .nil argument carrier := .reflIntro (.headType rfl)
theorem derivation : CDerivable church statement := .appElim identity_typed argument_typed
end Source

abbrev Constants := SetCode.PrimitiveSymbol Nat
abbrev core : Core Constants := SetCode.core
abbrev epsilon : ClosedTerm Constants (SelectionProofs.Selection object) := SetCode.epsilon
abbrev basis : List (ClosedFormula Constants) :=
  [lawAt core ZFSetHenkinInterpretation.emptyLaw,lawAt core ZFSetHenkinInterpretation.powerLaw,
   lawAt core ZFSetHenkinInterpretation.separationLaw,lawAt core ZFSetHenkinInterpretation.replacementLaw,
   SelectionProofs.principle epsilon,lawAt core ZFSetHenkinInterpretation.unionLaw,
   lawAt core ZFSetHenkinInterpretation.extensionality]

def sets : SetTraceProofs.Laws core epsilon basis where
  pairing := {empty := .hyp 0,power := .hyp 1,separation := .hyp 2,replacement := .hyp 3,selection := .hyp 4}
  union := .hyp 5
  extensionality := .hyp 6

theorem sets_free : sets.Free := ⟨⟨trivial,trivial,trivial,trivial,trivial⟩,trivial,trivial⟩

abbrev bound : Fin 0 → ClosedTerm Constants object := fun index => SetCode.expand (Fin.elim0 index)
def code (source : CTm Nat 0) : ClosedTerm Constants object := AnnotatedCodedReading.readAt SetCode.operations bound source
def carrier := code Source.carrier
def family : ClosedTerm Constants (object ⇒ object) := .lam (HOL.weaken carrier)
def identityFunction : ClosedTerm Constants (object ⇒ object) := .lam (.var .vz)

def body : ProofSyntax Constants basis (SetTraceProductProofs.pointwise core carrier family identityFunction) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let premise : Formula Constants [object] := member core (.var .vz) (HOL.weaken carrier)
  let localAssumptions := premise :: weakenHyps (σ := object) basis
  have functionBeta : ProofSyntax Constants localAssumptions
      (.eq (.app (HOL.weaken identityFunction) (.var .vz)) (.var .vz)) := .beta (.var .vz) (.var .vz)
  have familyBeta : ProofSyntax Constants localAssumptions
      (.eq (.app (HOL.weaken family) (.var .vz)) (HOL.weaken carrier)) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta (.var .vz) (HOL.weaken (HOL.weaken carrier)))
    rw [instantiate_weaken]
    rfl
  exact transportValue core _ (.eqSymm functionBeta) (transportBound core _ (.eqSymm familyBeta) (.hyp 0))

theorem body_free : body.FunctionExtensionalityFree := by
  unfold body
  apply transportValue_free
  · trivial
  · apply transportBound_free
    · simp [ProofSyntax.FunctionExtensionalityFree]
    · trivial

def functionReceipt : ProofSyntax Constants basis
    (member core (code Source.identity) (code Source.functionType)) := by
  have typed := SetTraceProductProofs.abstractionTyped core epsilon carrier family identityFunction sets body
  have abstractionBeta : ProofSyntax Constants basis (.eq (code Source.identity)
      (SetTraceProofs.abstraction core epsilon carrier identityFunction)) :=
    SetCodeOperators.binaryBeta core epsilon .abstraction carrier identityFunction
  have productBeta : ProofSyntax Constants basis (.eq (code Source.functionType)
      (SetTraceProductProofs.product core epsilon carrier family)) :=
    SetCodeOperators.binaryBeta core epsilon .product carrier family
  exact transportBound core _ (.eqSymm productBeta)
    (transportValue core _ (.eqSymm abstractionBeta) typed)

theorem functionReceipt_free : functionReceipt.FunctionExtensionalityFree := by
  unfold functionReceipt
  apply transportBound_free
  · exact SetCodeOperators.binaryBeta_free core epsilon .product _ _
  · apply transportValue_free
    · exact SetCodeOperators.binaryBeta_free core epsilon .abstraction _ _
    · exact SetTraceProductProofs.abstractionTyped_free core epsilon carrier family identityFunction sets body sets_free body_free

def argumentReceipt : ProofSyntax Constants basis (member core (code Source.argument) carrier) :=
  SetCode.TypingProofs.reflexivityAt (.head 1) (.head 0) bound sets.pairing.power sets.pairing.separation

theorem argumentReceipt_free : argumentReceipt.FunctionExtensionalityFree :=
  SetCode.TypingProofs.reflexivityAt_free (.head 1) (.head 0) bound sets.pairing.power sets.pairing.separation trivial trivial

def closedJudgment {value type : CTm Nat 0} (proof : ProofSyntax Constants basis (member core (code value) (code type))) :
    ProofSyntax Constants basis (SetCode.expand (judgmentAt (.typing .nil value type) Fin.elim0)) :=
  ProofSyntax.castIndices rfl (SetCode.TypingProofs.expanded_typing .nil value type Fin.elim0).symm
    (.impI (proof.prepend .top))

theorem closedJudgment_free {value type : CTm Nat 0} (proof : ProofSyntax Constants basis (member core (code value) (code type)))
    (free : proof.FunctionExtensionalityFree) : (closedJudgment proof).FunctionExtensionalityFree := by
  unfold closedJudgment
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ProofSyntax.functionExtensionalityFree_mono (ProofSyntax.OccurrenceMap.prepend .top) proof).mpr free

def functionJudgment := closedJudgment functionReceipt
def argumentJudgment := closedJudgment argumentReceipt
def applicationReceipt := SetCode.TypingProofs.applicationJudgment .nil Source.identity Source.argument
  Source.carrier Source.carrier Fin.elim0 sets functionJudgment argumentJudgment

theorem applicationReceipt_free : applicationReceipt.FunctionExtensionalityFree :=
  SetCode.TypingProofs.applicationJudgment_free .nil Source.identity Source.argument Source.carrier Source.carrier Fin.elim0
    sets functionJudgment argumentJudgment sets_free
    (closedJudgment_free functionReceipt functionReceipt_free)
    (closedJudgment_free argumentReceipt argumentReceipt_free)

def heads (_ : Nat) : ZFSet.{0} := ∅
def constants (_ : DeclName) : ZFSet.{0} := ∅
noncomputable abbrev actualModel := SetCode.model heads constants

theorem basis_valid : Soundness.SatisfiesHyps (Γ := []) actualModel (fun index => nomatch index) basis := by
  have same : basis = (ZFSetTraceProofInterpretation.basis []).map
      (HOL.mapConst (SetCode.PrimitiveSymbol.set (Head := Nat))) := rfl
  intro formula present
  rw [same] at present
  obtain ⟨original,admitted,rfl⟩ := List.mem_map.mp present
  rw [SetCode.denote_choiceMap]
  exact ZFSetTraceProofInterpretation.basis_valid.{0} (Γ := []) (fun index => nomatch index) original admitted

theorem actual_application :
    (actualModel.denote (SetCode.expand (judgmentAt (Γ := []) Source.statement Fin.elim0)) (fun index => nomatch index)).down :=
  Soundness.extDerivation_sound applicationReceipt.erase
    (actualModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) basis_valid

def sourceProduct : ClosedTerm (CodedHOL.Symbol Nat) object :=
  .app (.app (.const .product) (.const (.core .empty))) (.lam (.const (.core .empty)))

def wrongImages : {type : Ty Unit} → CodedHOL.Symbol Nat type → ClosedTerm Constants type
  | _, .product => .lam (.lam (.const (.set (.core .empty))))
  | _, symbol => SetCode.images symbol

theorem correctProduct_containsEmpty : (∅ : ZFSet.{0}) ∈
    (show ZFSet.{0} from actualModel.denote (SetCode.expand sourceProduct) (fun index => nomatch index)) := by
  rw [SetCode.denote_expand]
  change (∅ : ZFSet.{0}) ∈ ZFSetTraceProducts.tracePiSet ∅ (fun _ => ∅)
  rw [ZFSetTraceProductProofInterpretation.tracePiSet_eq_bounded,ZFSet.mem_sep,ZFSet.mem_powerset]
  exact ⟨ZFSet.empty_subset _,fun point absent => False.elim (ZFSet.notMem_empty point absent)⟩

theorem wrongProduct_refused : actualModel.denote (SetCode.expand sourceProduct) (fun index => nomatch index) ≠
    actualModel.denote (HOL.substConst wrongImages sourceProduct) (fun index => nomatch index) := by
  intro equal
  have present : (∅ : ZFSet.{0}) ∈
      (show ZFSet.{0} from actualModel.denote (HOL.substConst wrongImages sourceProduct) (fun index => nomatch index)) := by
    rw [← equal]
    exact correctProduct_containsEmpty
  change (∅ : ZFSet.{0}) ∈ ∅ at present
  exact ZFSet.notMem_empty _ present

theorem no_wrongProduct_equality : ¬ Nonempty (ProofSyntax Constants basis
    (.eq (SetCode.expand sourceProduct) (HOL.substConst wrongImages sourceProduct))) := by
  rintro ⟨proof⟩
  exact wrongProduct_refused (Soundness.extDerivation_sound proof.erase
    (actualModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) basis_valid)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeControls
