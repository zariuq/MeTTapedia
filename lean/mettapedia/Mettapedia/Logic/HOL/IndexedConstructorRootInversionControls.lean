import Mettapedia.Logic.HOL.IndexedConstructorRootInversion
import Mettapedia.TypeTheory.RecursiveSpace
import Mettapedia.Logic.HOL.Soundness

/-!
# Positive and separating controls for retained root-index inversion

Two nullary constructors have different proposition-valued result indices.
The original root producer supplies the first root. Retained inversion
refuses the other index under the explicit constructor-injectivity theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedConstructorRootInversionControls
open FiniteConstructorEncoding IndexedConstructorGuards

inductive Base where | number | space
abbrev number : Ty Base := .base .number
abbrev space : Ty Base := .base .space
def fields : List (List (Ty Base)) := [[], []]
abbrev payload : Ty Base := payloadType fields

inductive Symbol : Ty Base → Type
  | numeral : Nat → Symbol number
  | bottom : Symbol space
  | construct : Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)

def nullaryPrograms (left right : ClosedFormula Symbol) :
    (occurrence : Fin fields.length) → Term Symbol [] (handlerType (fields.get occurrence)) := by
  rintro ⟨value, bound⟩
  cases value with
  | zero => exact left
  | succ value =>
      cases value with
      | zero => exact right
      | succ value => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 value) bound)

@[reducible] def inventory : ConstructorPrograms Symbol [] where
  fields := fields
  number := number
  index := .prop
  numeral := fun value => .const (.numeral value)
  allowed := nullaryPrograms .top .top
  result := by
    rintro ⟨value, bound⟩
    cases value with
    | zero => exact .bot
    | succ value =>
        cases value with
        | zero => exact .top
        | succ value => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 value) bound)

def constructor : ClosedTerm Symbol (number ⇒ payload ⇒ (number ⇒ space) ⇒ space) := .const .construct
def children : ClosedTerm Symbol (number ⇒ space) := .lam (.const .bottom)
def first : Fin fields.length := ⟨0, by decide⟩
def second : Fin fields.length := ⟨1, by decide⟩
def value : ClosedTerm Symbol space := inventory.constructorValue constructor first PUnit.unit children
def injectivity : ClosedFormula Symbol := ConstructorInjectivity.statement constructor
def wrongRoot : ClosedFormula Symbol := inventory.rootIndex constructor value .top

def producedRoot : ProofSyntax Symbol [] (inventory.rootIndex constructor value .bot) :=
  inventory.rootIndex_intro constructor first PUnit.unit children .bot .topI (.eqRefl .bot)

theorem producedRoot_free : producedRoot.FunctionExtensionalityFree :=
  inventory.rootIndex_intro_free constructor first PUnit.unit children .bot .topI (.eqRefl .bot)
    True.intro True.intro

def wrongIndexRefused : ProofSyntax Symbol [injectivity] (.not wrongRoot) := by
  apply ProofSyntax.notI
  have impossible := inventory.rootIndex_result constructor first PUnit.unit children .top
    (ProofSyntax.hyp (Const := Symbol) (Δ := [wrongRoot, injectivity]) 1)
    (ProofSyntax.hyp (Const := Symbol) (Δ := [wrongRoot, injectivity]) 0)
  exact .impE (.eqPropER impossible) .topI

theorem wrongIndexRefused_free : wrongIndexRefused.FunctionExtensionalityFree := by
  unfold wrongIndexRefused
  change _ ∧ True
  constructor
  · exact inventory.rootIndex_result_free constructor first PUnit.unit children .top
      (ProofSyntax.hyp (Const := Symbol) (Δ := [wrongRoot, injectivity]) 1)
      (ProofSyntax.hyp (Const := Symbol) (Δ := [wrongRoot, injectivity]) 0) True.intro True.intro
  · trivial

abbrev Payload := ULift.{1} Prop → ULift.{1} Prop → ULift.{1} Prop

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .space => Mettapedia.TypeTheory.RecursiveSpace.Tree Payload

@[reducible] def model : HenkinModel.{0,0,0} Base Symbol := .standard carrier
  (fun symbol => match symbol with
    | .numeral value => .up value
    | .bottom => Mettapedia.TypeTheory.RecursiveSpace.bottom
    | .construct => fun tag data children =>
        Mettapedia.TypeTheory.RecursiveSpace.construct tag.down data (fun n => children (.up n)))

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
    obtain ⟨tags, data, children⟩ :=
      (Mettapedia.TypeTheory.RecursiveSpace.construct_injective _ _ _ _ _ _).mp same
    exact ⟨congrArg ULift.up tags, data, funext fun n => congrFun children n.down⟩
  · rintro ⟨tags, data, children⟩
    cases tags
    cases data
    cases children
    rfl

theorem wrongIndexRefused_valid : ¬ model.models wrongRoot := by
  have implication : model.models (.imp injectivity (.not wrongRoot)) :=
    Soundness.extTheorem_sound (.impI wrongIndexRefused.erase) model
      (model.functionsRespectEqv_of_fullDomains full)
  exact (HenkinModel.models_not model).mp
    ((HenkinModel.models_imp model).mp implication injectivity_valid)

/-- Collapsing constructor values destroys the primitive injectivity law. -/
@[reducible] def collapsedModel : HenkinModel.{0,0,0} Base Symbol := .standard carrier
  (fun symbol => match symbol with
    | .numeral value => .up value
    | .bottom => Mettapedia.TypeTheory.RecursiveSpace.bottom
    | .construct => fun _ _ _ => Mettapedia.TypeTheory.RecursiveSpace.bottom)

theorem collapsed_full : collapsedModel.FullDomains := HenkinModel.fullDomains_standard _ _

theorem collapsed_wrongRoot_valid : collapsedModel.models wrongRoot := by
  apply Or.inr
  apply Or.inl
  exact ⟨True.intro, Iff.rfl,
    ⟨(fun _ => Mettapedia.TypeTheory.RecursiveSpace.bottom), True.intro, rfl⟩⟩

theorem injectivity_cannot_be_dropped :
    ¬ Nonempty (ProofSyntax Symbol [] (.not wrongRoot)) := by
  rintro ⟨proof⟩
  have excluded := Soundness.extTheorem_sound proof.erase collapsedModel
    (collapsedModel.functionsRespectEqv_of_fullDomains collapsed_full)
  exact (HenkinModel.models_not collapsedModel).mp excluded collapsed_wrongRoot_valid

#print axioms producedRoot
#print axioms producedRoot_free
#print axioms wrongIndexRefused
#print axioms wrongIndexRefused_free
#print axioms injectivity_valid
#print axioms wrongIndexRefused_valid
#print axioms collapsed_wrongRoot_valid
#print axioms injectivity_cannot_be_dropped

end Mettapedia.Logic.HOL.IndexedConstructorRootInversionControls
