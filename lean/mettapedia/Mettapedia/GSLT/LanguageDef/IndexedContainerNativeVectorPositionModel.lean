import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorInactivePadding
import Mettapedia.Logic.HOL.HOLLightStandardTheory

/-!
# Independent natural/Boolean/list model of the source position reading

The parameter assignment realizes the actual zero, successor, vector
constructors/projections and the two distinct array selection instances.
Other parameters receive typed inhabitants. This is a semantic control of
the source terms, not an executable replacement for the generated programs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionModel
open Mettapedia.Logic
open Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original parameter)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open FiniteConstructorEncoding CurriedPredicates OrderedPositionPrograms

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .vector => ULift.{1} (List Bool)
  | .evidence => ULift.{1} Unit

def inhabitant : (type : Base) → carrier type
  | .number => ULift.up 0
  | .element => ULift.up false
  | .vector => ULift.up []
  | .evidence => ULift.up ()

def defaultValue : (type : Ty Base) → Ty.denote.{0,0} carrier type
  | .base type => inhabitant type
  | .prop => ULift.up False
  | .arr _ result => fun _ => defaultValue result

abbrev Assignment := {type : Ty Base} → Const type → Ty.denote.{0,0} carrier type

def assign {type : Ty Base} (name : Nat) (value : Ty.denote.{0,0} carrier type) (previous : Assignment) : Assignment :=
  fun {other} symbol => match symbol with
    | .parameter actual _ =>
        if actual = name then
          if same : other = type then same.symm ▸ value else previous symbol
        else previous symbol

def elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)) := parameter 12 _
def arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)) := parameter 13 _
def ops := arrayOperations elementSelection arraySelection

noncomputable def meaning : Assignment :=
  assign 0 (type := N) (ULift.up 0)
    (assign 1 (type := N ⇒ N) (fun n => ULift.up (n.down + 1))
      (assign 2 (type := V) (ULift.up [])
        (assign 3 (type := N ⇒ E ⇒ V ⇒ V) (fun _ head tail => ULift.up (head.down :: tail.down))
          (assign 4 (type := V ⇒ E) (fun vector => ULift.up (vector.down.headD false))
            (assign 5 (type := V ⇒ V) (fun vector => ULift.up vector.down.tail)
              (assign 12 (type := SelectionProofs.Selection (N ⇒ E))
                (HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ E))
                (assign 13 (type := SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E))
                  (HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ V ⇒ N ⇒ E))
                  (assign 20 (type := E) (ULift.up true) (fun {type} _ => defaultValue type)))))))))

noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carrier meaning
def values : model.Valuation [] := fun entry => nomatch entry

theorem zero_denote : model.denote original.zero values = ULift.up 0 := rfl
theorem successor_denote (n : Nat) : model.denote original.successor values (ULift.up n) = ULift.up (n + 1) := rfl

theorem numeral_denote (n : Nat) : model.denote (numeral [] n) values = ULift.up n := by
  induction n with
  | zero => rfl
  | succ n previous =>
      change ULift.up ((model.denote (numeral [] n) values).down + 1) = ULift.up (n + 1)
      rw [previous]

theorem induction_holds : model.models (NaturalRecursionProofs.inductionPrinciple original.zero original.successor) := by
  intro predicate _ clauses n _
  rcases n with ⟨n⟩
  induction n with
  | zero => exact clauses.1
  | succ n previous => exact clauses.2 (ULift.up n) trivial (previous trivial)

theorem separation_holds : model.models (NaturalNumeralProofs.separation original.zero original.successor) := by
  intro n _ same
  have impossible : n.down + 1 = (0:Nat) := congrArg ULift.down same
  exact Nat.noConfusion impossible

theorem elementSelection_holds : model.models (SelectionProofs.principle elementSelection) := by
  intro predicate _ witness _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (N ⇒ E) predicate ⟨witness,present⟩

theorem arraySelection_holds : model.models (SelectionProofs.principle arraySelection) := by
  intro predicate _ witness _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (N ⇒ V ⇒ N ⇒ E) predicate ⟨witness,present⟩

theorem elementRecursion_holds : model.models (ops.recursionLaw E) := by
  intro initial _ step _
  let result : ULift.{1} Nat → ULift.{1} Bool :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨result,trivial,?_,?_⟩
  · rfl
  · intro n _; rfl

theorem arrayRecursion_holds : model.models (ops.recursionLaw (V ⇒ N ⇒ E)) := by
  intro initial _ step _
  let result : ULift.{1} Nat → (ULift.{1} (List Bool) → ULift.{1} Nat → ULift.{1} Bool) :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨result,trivial,?_,?_⟩
  · intro vector _ position _; rfl
  · intro n _ vector _ position _; rfl

theorem head_holds : model.models ops.headLaw := by
  intro n _ head _ tail _
  rfl

theorem tail_holds : model.models ops.tailLaw := by
  intro n _ head _ tail _
  rfl

theorem primitive_assumptions_realizable : Soundness.SatisfiesHyps model values (ops.assumptions []) := by
  intro formula present
  simp only [VectorChildArrays.Operations.assumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl
  · exact elementSelection_holds
  · exact elementRecursion_holds
  · exact arraySelection_holds
  · exact arrayRecursion_holds
  · exact head_holds
  · exact tail_holds

def payload : ClosedTerm Const (E ⇒ .prop) := .lam .top
def tag : ClosedTerm Const E := parameter 21 _

def encodedArguments (length shape : Nat) := sourceArguments payload (numeral [] length) tag (numeral [] shape)
def inventory := constructors payload
def positionPrograms := IndexedConstructorGuards.PositionPrograms.ofSegments inventory original.zero original.successor (plans payload)
noncomputable def encodedFields (length shape : Nat) : inventory.Data model :=
  ⟨occurrence payload,denoteArguments model _ (encodedArguments length shape) values⟩

theorem sourceAllowed_iff (length shape : Nat) :
    (model.denote (sourceAllowed payload (numeral [] length) tag (numeral [] shape)) values).down ↔ shape = 0 := by
  change (True ∧ (True ∧ ((model.denote (numeral [] shape) values = ULift.up 0) ∧ True))) ↔ shape = 0
  rw [numeral_denote]
  simp only [true_and,and_true]
  exact ⟨fun same => congrArg ULift.down same,fun same => congrArg ULift.up same⟩

theorem dataAllowed_iff (length shape : Nat) : inventory.dataAllowed model values (encodedFields length shape) ↔ shape = 0 := by
  change (True ∧ (True ∧ ((model.denote (numeral [] shape) values = ULift.up 0) ∧ True))) ↔ shape = 0
  rw [numeral_denote]
  simp only [true_and,and_true]
  exact ⟨fun same => congrArg ULift.down same,fun same => congrArg ULift.up same⟩

theorem fields_evaluate (length shape : Nat) :
    evaluateFields model Equiv.ulift.symm _ values (encodedFields length shape).2 (plans payload (encodedFields length shape).1) =
      [(1,ULift.up True),(length,ULift.up True),(1,ULift.up True)] := by
  change [(1,ULift.up True),((model.denote (numeral [] length) values).down,ULift.up True),(1,ULift.up True)] = _
  rw [numeral_denote]

theorem related_iff (length shape slot : Nat) (target : ULift Prop) :
    positionPrograms.related model values (encodedFields length shape) (ULift.up slot) target ↔
      (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
        [(1,ULift.up True),(length,ULift.up True),(1,ULift.up True)])[slot]? = some target := by
  have comparison := IndexedConstructorGuards.PositionPrograms.ofSegments_related inventory original.zero original.successor
    (plans payload) model Equiv.ulift.symm (HenkinModel.fullDomains_standard _ _) values zero_denote successor_denote
    values (encodedFields length shape) (ULift.up slot) target
  change positionPrograms.related model values (encodedFields length shape) (ULift.up slot) target ↔
    (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
      (evaluateFields model Equiv.ulift.symm _ values (encodedFields length shape).2
        (plans payload (encodedFields length shape).1)))[slot]? = some target at comparison
  apply comparison.trans
  rw [fields_evaluate]
  rfl

theorem sourceActivity_data (length shape slot : Nat) :
    (model.denote (sourceActivity payload (numeral [] length) tag (numeral [] shape)) values (ULift.up slot)).down ↔
      inventory.dataAllowed model values (encodedFields length shape) ∧
        ∃ target, positionPrograms.related model values (encodedFields length shape) (ULift.up slot) target := by
  have interpretation := positionPrograms.activeProgram_denote model (HenkinModel.fullDomains_standard _ _) values
    (model.denote (encode inventory.fields (occurrence payload) (encodedArguments length shape)) values) (ULift.up slot)
  change (model.denote (sourceActivity payload (numeral [] length) tag (numeral [] shape)) values (ULift.up slot)).down ↔ _ at interpretation
  apply interpretation.trans
  rw [encode_denote]
  constructor
  · rintro ⟨data,valid,same⟩
    have equal : encodedFields length shape = data := Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective _ _ same
    exact equal.symm ▸ valid
  · intro valid
    exact ⟨encodedFields length shape,valid,rfl⟩

theorem sourceActivity_iff (length shape slot : Nat) :
    (model.denote (sourceActivity payload (numeral [] length) tag (numeral [] shape)) values (ULift.up slot)).down ↔
      shape = 0 ∧ slot < length + 2 := by
  rw [sourceActivity_data,dataAllowed_iff]
  apply and_congr Iff.rfl
  change (∃ target : ULift.{1} Prop,
    positionPrograms.related model values (encodedFields length shape) (ULift.up slot) target) ↔ slot < length + 2
  simp only [related_iff]
  rw [Mettapedia.TypeTheory.OrderedPositionSegments.active_iff]
  rw [Mettapedia.TypeTheory.OrderedPositionSegments.length_flatten]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

theorem normal_shape_inactive : ¬ (model.denote (sourceActivity payload (numeral [] 2) tag (numeral [] 0)) values (ULift.up 4)).down := by
  rw [sourceActivity_iff]
  decide

theorem forged_shape_inactive_everywhere (slot : Nat) :
    ¬ (model.denote (sourceActivity payload (numeral [] 2) tag (numeral [] 9)) values (ULift.up slot)).down := by
  rw [sourceActivity_iff]
  simp

#print axioms induction_holds
#print axioms primitive_assumptions_realizable
#print axioms sourceActivity_iff
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionModel
