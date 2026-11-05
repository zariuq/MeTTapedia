import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedCodedConstantSubstitution
import Mettapedia.Logic.HOL.Embedding.ZFSetCodeOperatorsInterpretation
import Mettapedia.Logic.HOL.SetCodeConstantMap

/-!
# Expanding the coded source operations to primitive set syntax

The target signature has set primitives, the explicit selector, head codes
and declaration codes. All eight derived code operations are closed lambda
bodies. The independently chosen source model is their actual reduct;
expansion preserves every source HOL term and generated judgment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open HOL.Embedding
universe u

inductive PrimitiveSymbol (Head : Type) : Ty Unit → Type where
  | set {type : Ty Unit} (symbol : ZFSetHenkinInterpretation.ChoiceSymbol type) : PrimitiveSymbol Head type
  | head (name : Head) : PrimitiveSymbol Head object
  | constant (name : DeclName) : PrimitiveSymbol Head object

variable {Head : Type}

def core : SetComprehensionProofs.Core (PrimitiveSymbol Head) := fun symbol => .set (.core symbol)
def epsilon : ClosedTerm (PrimitiveSymbol Head) (SelectionProofs.Selection object) := .const (.set .epsilon)

def body {type : Ty Unit} (operator : SetCodeOperators.Operator type) : ClosedTerm (PrimitiveSymbol Head) type :=
  SetCodeOperators.body core epsilon operator

def images : {type : Ty Unit} → CodedHOL.Symbol Head type → ClosedTerm (PrimitiveSymbol Head) type
  | _, .core symbol => .const (.set (.core symbol))
  | _, .head name => .const (.head name)
  | _, .constant name => .const (.constant name)
  | _, .product => body .product
  | _, .sum => body .sum
  | _, .abstraction => body .abstraction
  | _, .application => body .application
  | _, .pair => body .pair
  | _, .first => body .first
  | _, .second => body .second
  | _, .truth => body .truth

def expand {Γ : Ctx Unit} {type : Ty Unit} (term : Term (CodedHOL.Symbol Head) Γ type) := HOL.substConst images term

def operations : AnnotatedCodedReading.Operations Head (PrimitiveSymbol Head) object :=
  CodedHOL.operations.mapDefinitions images

theorem expand_readAt {n : Nat} {Γ : Ctx Unit} (source : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    expand (AnnotatedCodedReading.readAt CodedHOL.operations bound source) =
      AnnotatedCodedReading.readAt operations (fun index => expand (bound index)) source :=
  AnnotatedCodedReading.readAt_substConst CodedHOL.operations images source bound

theorem expand_subst {Γ Ξ : Ctx Unit} {type : Ty Unit} (theta : Subst (CodedHOL.Symbol Head) Γ Ξ)
    (term : Term (CodedHOL.Symbol Head) Γ type) : expand (HOL.subst theta term) =
      HOL.subst (fun index => expand (theta index)) (expand term) :=
  (HOL.substConst_subst images theta term).symm

theorem body_choiceMap {type : Ty Unit} (operator : SetCodeOperators.Operator type) :
    body (Head := Head) operator = HOL.mapConst PrimitiveSymbol.set
      (SetCodeOperators.body ZFSetPairingProofInterpretation.core ZFSetPairingProofInterpretation.epsilon operator) := by
  exact (SetCodeConstantMap.map_body ZFSetPairingProofInterpretation.core PrimitiveSymbol.set
    ZFSetPairingProofInterpretation.epsilon operator).symm

noncomputable def denoteSymbol (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    {type : Ty Unit} → PrimitiveSymbol Head type → Ty.denote.{0,u+1} ZFSetHenkinInterpretation.carrier.{u} type
  | _, .set symbol => ZFSetHenkinInterpretation.choiceDenote symbol
  | _, .head name => heads name
  | _, .constant name => constants name

noncomputable abbrev model (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    HenkinModel.{0,0,u+1} Unit (PrimitiveSymbol Head) :=
  HenkinModel.standard ZFSetHenkinInterpretation.carrier (denoteSymbol heads constants)

variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

def choiceImages {type : Ty Unit} (symbol : ZFSetHenkinInterpretation.ChoiceSymbol type) :
    ClosedTerm (PrimitiveSymbol Head) type := .const (.set symbol)

theorem choice_reduct : (model heads constants).constantSubstitutionReduct choiceImages =
    ZFSetHenkinInterpretation.choiceModel.{u} := by
  apply HenkinModel.ext_data rfl
  · rfl
  · apply heq_of_eq
    funext type symbol
    cases symbol <;> rfl

theorem denote_choiceMap {Γ : Ctx Unit} {type : Ty Unit}
    (term : Term ZFSetHenkinInterpretation.ChoiceSymbol Γ type) (valuation : (model heads constants).Valuation Γ) :
    (model heads constants).denote (HOL.mapConst PrimitiveSymbol.set term) valuation =
      ZFSetHenkinInterpretation.choiceModel.{u}.denote term valuation := by
  have equality := HenkinModel.denote_substConst choiceImages (model heads constants) term valuation
  have denotations : HEq @((model heads constants).constantSubstitutionReduct choiceImages).denote
      @(ZFSetHenkinInterpretation.choiceModel.{u}).denote := by rw [choice_reduct heads constants]
  have compared := congrFun (congrFun (congrFun (congrFun (eq_of_heq denotations) Γ) type) term) valuation
  have mapped := HOL.substConst_constant_images (PrimitiveSymbol.set (Head := Head)) term
  exact (congrArg (fun output => (model heads constants).denote output valuation) mapped).symm.trans
    (equality.trans compared)

theorem denote_body {type : Ty Unit} (operator : SetCodeOperators.Operator type) :
    (model heads constants).denote (body operator) (fun index => nomatch index) =
      ZFSetCodeOperatorsInterpretation.meaning operator := by
  rw [body_choiceMap,denote_choiceMap]
  exact ZFSetCodeOperatorsInterpretation.body_meaning operator

theorem images_agree {type : Ty Unit} (symbol : CodedHOL.Symbol Head type) :
    (model heads constants).denote (images symbol) (fun index => nomatch index) =
      (CodedHOL.model heads constants).constDen symbol := by
  cases symbol with
  | core symbol => rfl
  | head name => rfl
  | constant name => rfl
  | product => exact denote_body heads constants .product
  | sum => exact denote_body heads constants .sum
  | abstraction => exact denote_body heads constants .abstraction
  | application => exact denote_body heads constants .application
  | pair => exact denote_body heads constants .pair
  | first => exact denote_body heads constants .first
  | second => exact denote_body heads constants .second
  | truth => exact denote_body heads constants .truth

theorem model_reduct : CodedHOL.model heads constants = (model heads constants).constantSubstitutionReduct images :=
  HenkinModel.eq_constantSubstitutionReduct_of_agreement images (CodedHOL.model heads constants) (model heads constants)
    rfl HEq.rfl (fun symbol => heq_of_eq ((images_agree heads constants symbol).symm.trans
      (HenkinModel.denote_closed_valuation_eq (model heads constants) (images symbol) _ _)))

theorem denote_expand {Γ : Ctx Unit} {type : Ty Unit} (term : Term (CodedHOL.Symbol Head) Γ type)
    (valuation : (model heads constants).Valuation Γ) :
    (model heads constants).denote (expand term) valuation = (CodedHOL.model heads constants).denote term valuation := by
  have denotations : HEq @((model heads constants).constantSubstitutionReduct images).denote
      @(CodedHOL.model heads constants).denote := by rw [← model_reduct heads constants]
  exact (HenkinModel.denote_substConst images (model heads constants) term valuation).trans
    (congrFun (congrFun (congrFun (congrFun (eq_of_heq denotations) Γ) type) term) valuation)

theorem denote_expand_readAt {n : Nat} {Γ : Ctx Unit} (source : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (valuation : (model heads constants).Valuation Γ) :
    (model heads constants).denote (expand (AnnotatedCodedReading.readAt CodedHOL.operations bound source)) valuation =
      ev heads constants source (fun index => (CodedHOL.model heads constants).denote (bound index) valuation) :=
  (denote_expand heads constants _ valuation).trans (CodedHOL.denote_readAt heads constants source bound valuation)

theorem expanded_judgment_holds {R : Rules Head} {P : ChurchRules R}
    (interpretation : SetModel heads constants P) {statement : CStatement Head} (derivation : CDerivable P statement)
    {Γ : Ctx Unit} (bound : Fin (statementArity statement) → Term (CodedHOL.Symbol Head) Γ object)
    (valuation : (model heads constants).Valuation Γ) :
    ((model heads constants).denote (expand (judgmentAt statement bound)) valuation).down := by
  rw [denote_expand heads constants]
  exact CodedHOL.judgmentAt_holds heads constants interpretation derivation bound valuation

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode
