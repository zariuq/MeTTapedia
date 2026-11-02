import Mettapedia.Logic.HOL.IndexedConstructorInduction
import Mettapedia.TypeTheory.RecursiveSpace
import Mettapedia.Logic.HOL.Soundness

/-!
# Data-field controls for retained indexed constructor cases

The constructor has one proposition-valued field and returns that field as
its index. The supplied child condition reads the field from the actual
payload. The case proof uses that condition; it cannot manufacture the field
from the unrestricted shape guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorInductionControls
open FiniteConstructorEncoding IndexedConstructorGuards CurriedPredicates

inductive Base where | number | space
abbrev number : Ty Base := .base .number
abbrev space : Ty Base := .base .space
def fields : List (List (Ty Base)) := [[.prop]]
abbrev payload : Ty Base := payloadType fields

inductive Symbol : Ty Base → Type
  | numeral : Nat → Symbol number
  | bottom : Symbol space
  | construct : Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)

def only : Fin fields.length := ⟨0, by decide⟩

@[reducible] def inventory {Γ : Ctx Base} : ConstructorPrograms Symbol Γ where
  fields := fields
  number := number
  index := .prop
  numeral := fun value => .const (.numeral value)
  allowed := Fin.cases (.lam .top) (fun impossible => Fin.elim0 impossible)
  result := Fin.cases (.lam (.var .vz)) (fun impossible => Fin.elim0 impossible)

def reader {Γ : Ctx Base} : Term Symbol Γ (payload ⇒ .prop) :=
  .lam (.app (.var .vz) (.lam (.var .vz)))

@[simp] theorem reader_subst {Γ Ξ : Ctx Base} (images : Subst Symbol Γ Ξ) :
    HOL.subst images reader = reader := rfl

def property {Γ : Ctx Base} : Term Symbol Γ (space ⇒ .prop ⇒ .prop) :=
  .lam (.lam (.var .vz))

variable {Γ : Ctx Base} {assumptions : List (Formula Symbol Γ)}

def reader_beta (point : Formula Symbol Γ) : ProofSyntax Symbol assumptions
    (.eq (.app reader (encode fields only (point, PUnit.unit))) point) := by
  have first : ProofSyntax Symbol assumptions (.eq
      (.app reader (encode fields only (point, PUnit.unit)))
      (.app (encode fields only (point, PUnit.unit)) (.lam (.var .vz)))) :=
    .beta (encode fields only (point, PUnit.unit)) (.app (.var .vz) (.lam (.var .vz)))
  have second : ProofSyntax Symbol assumptions (.eq
      (.app (encode fields only (point, PUnit.unit)) (.lam (.var .vz)))
      (.app (.lam (.var .vz)) point)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.beta (.lam (.var .vz)) (.app (.var .vz) (weaken point)))
    simp only [fields, only, encode, applyArguments, weakenArguments, ignoreHandlers,
      instantiate, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]
  exact .eqTrans first (.eqTrans second (.beta point (.var .vz)))

theorem reader_beta_free (point : Formula Symbol Γ) :
    (reader_beta (assumptions := assumptions) point).FunctionExtensionalityFree := by
  unfold reader_beta
  refine ⟨True.intro, ?_, True.intro⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

def property_beta (value : Term Symbol Γ space) (index : Formula Symbol Γ) :
    ProofSyntax Symbol assumptions (.eq (.app (.app property value) index) index) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2 (.var .vz) value index)
  simp only [property, instantiate, HOL.subst, Subst.single, Subst.lift]

theorem property_beta_free (value : Term Symbol Γ space) (index : Formula Symbol Γ) :
    (property_beta (assumptions := assumptions) value index).FunctionExtensionalityFree := by
  unfold property_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

def cases (construct : Term Symbol Γ (number ⇒ payload ⇒ (number ⇒ space) ⇒ space))
    (children : Term Symbol Γ (number ⇒ space)) :
    inventory.IndexedCases construct children reader property assumptions := by
  intro Ξ images occurrence arguments
  have same : occurrence = only := Fin.ext (by
    change occurrence.val = 0
    have bound : occurrence.val < 1 := occurrence.isLt
    omega)
  subst occurrence
  rcases arguments with ⟨point, ⟨⟩⟩
  let hypotheses : List (Formula Symbol Ξ) :=
    applyArguments _ ((inventory.subst images).allowed only) (point, PUnit.unit) ::
      .app (HOL.subst images reader) (encode fields only (point, PUnit.unit)) ::
      assumptions.map (HOL.subst images)
  have supplied : ProofSyntax Symbol hypotheses
      (.app reader (encode fields only (point, PUnit.unit))) := by
    apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp (Const := Symbol) (Δ := hypotheses) 1)
    simp [hypotheses, List.get_eq_getElem]
  have fieldProof := ProofSyntax.impE (ProofSyntax.eqPropEL (reader_beta point)) supplied
  have resultProof : ProofSyntax Symbol hypotheses (.app (.lam (.var .vz)) point) :=
    .impE (.eqPropER (.beta point (.var .vz))) fieldProof
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.impE (ProofSyntax.eqPropER (property_beta
      ((inventory.subst images).constructorValue (HOL.subst images construct) only
        (point, PUnit.unit) (HOL.subst images children)) (.app (.lam (.var .vz)) point))) resultProof)
  simp [inventory, ConstructorPrograms.subst, only, fields,
    property, HOL.subst, Subst.lift, applyFields]

def constructor : ClosedTerm Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space) := .const .construct
def children : ClosedTerm Symbol (number ⇒ space) := .lam (.const .bottom)
def topPayload : ClosedTerm Symbol payload := encode fields only (.top, PUnit.unit)
def topValue : ClosedTerm Symbol space := inventory.constructorValue constructor only (.top, PUnit.unit) children
def injectivity : ClosedFormula Symbol := ConstructorInjectivity.statement constructor

def topShape : ProofSyntax Symbol assumptions (.app (.app inventory.shapeProgram (.const (.numeral 0)))
    (encode fields only (.top, PUnit.unit))) := by
  apply ProofSyntax.impE (ProofSyntax.eqPropER (inventory.shapeProgram_beta _ _))
  apply ConstructorDataPredicates.introduce fields (inventory.shapeCondition (.const (.numeral 0))) only
    (.top, PUnit.unit)
  apply conjoin_intro [.prop] (.top, PUnit.unit)
  · exact .impE (.eqPropER (.beta .top .top)) .topI
  · exact constant_intro [.prop] (.top, PUnit.unit) (.eqRefl (.const (Symbol.numeral 0)))

def lifted : ProofSyntax Symbol [injectivity]
    (.app (IndexedPredicateInduction.lift (inventory.rootProgram constructor) property) topValue) :=
  inventory.constructorCases_lift constructor (.const (.numeral 0)) topPayload children reader property
    (cases constructor children) (.hyp 0) topShape
    (.impE (.eqPropER (reader_beta .top)) .topI)

def wrongRoot : ClosedFormula Symbol := inventory.rootIndex constructor topValue .bot

def wrongIndexRefused : ProofSyntax Symbol [injectivity] (.not wrongRoot) := by
  apply ProofSyntax.notI
  have root : ProofSyntax Symbol [wrongRoot, injectivity]
      (.app (.app (inventory.rootProgram constructor) topValue) .bot) :=
    .impE (.eqPropER (inventory.rootProgram_beta constructor topValue .bot)) (.hyp 0)
  have output := IndexedPredicateInduction.eliminate (inventory.rootProgram constructor) property topValue .bot
    (lifted.prepend wrongRoot) root
  exact .impE (.eqPropEL (property_beta topValue .bot)) output

theorem cases_free (construct : Term Symbol Γ (number ⇒ payload ⇒ (number ⇒ space) ⇒ space))
    (children : Term Symbol Γ (number ⇒ space))
    {Ξ : Ctx Base} (images : Subst Symbol Γ Ξ) (occurrence : Fin fields.length)
    (arguments : Arguments Symbol Ξ (fields.get occurrence)) :
    (cases (assumptions := assumptions) construct children images occurrence arguments).FunctionExtensionalityFree := by
  have same : occurrence = only := Fin.ext (by
    change occurrence.val = 0
    have bound : occurrence.val < 1 := occurrence.isLt
    omega)
  subst occurrence
  rcases arguments with ⟨point, ⟨⟩⟩
  unfold cases
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨property_beta_free _ _, True.intro, reader_beta_free _,
    (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro⟩

theorem topShape_free : (topShape (assumptions := assumptions)).FunctionExtensionalityFree := by
  unfold topShape
  refine ⟨inventory.shapeProgram_beta_free _ _, ?_⟩
  apply ConstructorDataPredicates.introduce_free
  apply conjoin_intro_free
  · trivial
  · exact constant_intro_free _ _ _ True.intro

theorem lifted_free : lifted.FunctionExtensionalityFree := by
  unfold lifted
  apply ConstructorPrograms.constructorCases_lift_free
  · exact cases_free constructor children
  · trivial
  · exact topShape_free
  · exact ⟨reader_beta_free _, True.intro⟩

theorem wrongIndexRefused_free : wrongIndexRefused.FunctionExtensionalityFree := by
  unfold wrongIndexRefused
  refine ⟨property_beta_free _ _, ?_⟩
  apply IndexedPredicateInduction.eliminate_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr lifted_free
  · exact ⟨inventory.rootProgram_beta_free _ _ _, True.intro⟩

abbrev Payload := (ULift.{1} Prop → ULift.{1} Prop) → ULift.{1} Prop

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .space => Mettapedia.TypeTheory.RecursiveSpace.Tree Payload

@[reducible] def model : HenkinModel.{0,0,0} Base Symbol := .standard carrier
  (fun symbol => match symbol with
    | .numeral value => .up value
    | .bottom => Mettapedia.TypeTheory.RecursiveSpace.bottom
    | .construct => fun tag data descendants =>
        Mettapedia.TypeTheory.RecursiveSpace.construct tag.down data (fun n => descendants (.up n)))

theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

theorem injectivity_valid : model.models injectivity := by
  intro firstTag _ firstData _ firstChildren _ secondTag _ secondData _ secondChildren _
  change (Mettapedia.TypeTheory.RecursiveSpace.construct firstTag.down firstData
      (fun n => firstChildren (.up n)) =
    Mettapedia.TypeTheory.RecursiveSpace.construct secondTag.down secondData
      (fun n => secondChildren (.up n))) ↔
    model.Eqv number firstTag secondTag ∧
      (model.Eqv payload firstData secondData ∧
        model.Eqv (number ⇒ space) firstChildren secondChildren)
  simp only [model.eqv_iff_eq_of_fullDomains full]
  constructor
  · intro same
    obtain ⟨tags, data, descendants⟩ :=
      (Mettapedia.TypeTheory.RecursiveSpace.construct_injective _ _ _ _ _ _).mp same
    exact ⟨congrArg ULift.up tags, data, funext fun n => congrFun descendants n.down⟩
  · rintro ⟨tags, data, descendants⟩
    cases tags
    cases data
    cases descendants
    rfl

theorem wrongIndexRefused_valid : ¬ model.models wrongRoot := by
  have implication : model.models (.imp injectivity (.not wrongRoot)) :=
    Soundness.extTheorem_sound (.impI wrongIndexRefused.erase) model
      (model.functionsRespectEqv_of_fullDomains full)
  exact (HenkinModel.models_not model).mp
    ((HenkinModel.models_imp model).mp implication injectivity_valid)

def falseCaseGuard : ClosedFormula Symbol :=
  applyArguments [.prop] (inventory.allowed only) (.bot, PUnit.unit)

def falseCaseTarget : ClosedFormula Symbol :=
  .app (.app property (inventory.constructorValue constructor only (.bot, PUnit.unit) children))
    (applyFields [.prop] (inventory.result only) (.bot, PUnit.unit))

theorem child_condition_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Symbol [falseCaseGuard] falseCaseTarget) := by
  rintro ⟨proof⟩
  have result := Soundness.extTheorem_sound (ProofSyntax.impI proof).erase model
    (model.functionsRespectEqv_of_fullDomains full)
  change True → False at result
  exact result True.intro

@[reducible] def collapsedModel : HenkinModel.{0,0,0} Base Symbol := .standard carrier
  (fun symbol => match symbol with
    | .numeral value => .up value
    | .bottom => Mettapedia.TypeTheory.RecursiveSpace.bottom
    | .construct => fun _ _ _ => Mettapedia.TypeTheory.RecursiveSpace.bottom)

theorem collapsed_full : collapsedModel.FullDomains := HenkinModel.fullDomains_standard _ _

theorem collapsed_wrongRoot_valid : collapsedModel.models wrongRoot := by
  apply Or.inl
  refine ⟨ULift.up False, True.intro, ?_⟩
  exact ⟨True.intro, Iff.rfl,
    ⟨(fun _ => Mettapedia.TypeTheory.RecursiveSpace.bottom), True.intro, rfl⟩⟩

theorem injectivity_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Symbol [] (.not wrongRoot)) := by
  rintro ⟨proof⟩
  have excluded := Soundness.extTheorem_sound proof.erase collapsedModel
    (collapsedModel.functionsRespectEqv_of_fullDomains collapsed_full)
  exact (HenkinModel.models_not collapsedModel).mp excluded collapsed_wrongRoot_valid

#print axioms reader_beta
#print axioms reader_beta_free
#print axioms property_beta
#print axioms property_beta_free
#print axioms cases
#print axioms topShape
#print axioms lifted
#print axioms wrongIndexRefused
#print axioms cases_free
#print axioms topShape_free
#print axioms lifted_free
#print axioms wrongIndexRefused_free
#print axioms injectivity_valid
#print axioms wrongIndexRefused_valid
#print axioms child_condition_cannot_be_dropped
#print axioms collapsed_wrongRoot_valid
#print axioms injectivity_cannot_be_dropped

end Mettapedia.Logic.HOL.IndexedConstructorInductionControls
