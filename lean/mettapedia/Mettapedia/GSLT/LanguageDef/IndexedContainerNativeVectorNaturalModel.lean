import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorAdmission
import Mettapedia.Logic.HOL.FiniteConstructorNaturalRealization
import Mettapedia.Logic.HOL.HOLLightStandardTheory

/-!
# A natural-valued meaning for the original mixed-vector constructor

Number and element carriers are lifted naturals. The complete source payload
data and the active child list are encoded by the existing natural realization.
The original constructor symbol receives this actual function. Selection and
source payload predicates retain their own typed parameters. Constants outside
the displayed interpretation receive typed defaults; no whole-theory model is
claimed for those parameters.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalModel
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original parameter)
open FiniteConstructorEncoding

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Nat
  | .vector => ULift.{1} (List Nat)
  | .evidence => ULift.{1} Unit
def inhabitant : (type : Base) → carrier type
  | .number => .up 0
  | .element => .up 0
  | .vector => .up []
  | .evidence => .up ()
def defaultValue : (type : Ty Base) → Ty.denote.{0,0} carrier type
  | .base type => inhabitant type
  | .prop => .up False
  | .arr _ result => fun _ => defaultValue result
abbrev Assignment := {type : Ty Base} → Const type → Ty.denote.{0,0} carrier type
def assign {type : Ty Base} (name : Nat) (value : Ty.denote.{0,0} carrier type) (previous : Assignment) : Assignment :=
  fun {other} symbol => match symbol with
    | .parameter actual _ => if actual = name then
        if same : other = type then same.symm ▸ value else previous symbol
      else previous symbol

def basisMeaning : Assignment :=
  assign 0 (type := N) (.up 0)
    (assign 1 (type := N ⇒ N) (fun n => .up (n.down+1)) (fun {type} _ => defaultValue type))
def basis : HenkinModel.{0,0,0} Base Const := .standard carrier basisMeaning
abbrev fields : List (List (Ty Base)) := [[N,E,N]]
abbrev Raw := Ty.denote.{0,0} carrier (payloadType fields)
abbrev SourceData := Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote.{0,0} carrier) fields

def dataEquiv : SourceData ≃ ULift.{1} Nat × ULift.{1} Nat × ULift.{1} Nat where
  toFun := by
    rintro ⟨occurrence,data⟩
    have same : occurrence = ⟨0,by decide⟩ := Fin.eq_zero occurrence
    cases same
    exact (data.1,data.2.1,data.2.2.1)
  invFun := fun data => ⟨⟨0,by decide⟩,data.1,data.2.1,data.2.2,PUnit.unit⟩
  left_inv := by
    rintro ⟨occurrence,data⟩
    have same : occurrence = ⟨0,by decide⟩ := Fin.eq_zero occurrence
    cases same
    rfl
  right_inv := fun _ => rfl
instance : Encodable SourceData := Encodable.ofEquiv (ULift.{1} Nat × ULift.{1} Nat × ULift.{1} Nat) dataEquiv
instance : Encodable (Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote.{0,0} basis.Carrier) fields) := by
  change Encodable SourceData
  infer_instance
def arity (data : SourceData) : Nat := (dataEquiv data).1.down + 2

noncomputable def constructorMeaning (tag : ULift.{1} Nat) (payload : Raw)
    (children : ULift.{1} Nat → ULift.{1} Nat) : ULift.{1} Nat :=
  .up (FiniteConstructorEncoding.NaturalRealization.construct.{0,0,0} basis fields arity tag.down payload
    (fun slot => (children (.up slot)).down))

def constructor : ClosedTerm Const (N ⇒ payloadType fields ⇒ (N ⇒ E) ⇒ E) := parameter 25 _
def payloadSelection : ClosedTerm Const (SelectionProofs.Selection (payloadType fields)) := parameter 27 _
def childrenSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)) := parameter 28 _
def bottom : ClosedTerm Const E := parameter 26 _
def payloadPredicate : ClosedTerm Const (E ⇒ .prop) := parameter 20 _

noncomputable def meaning (predicate : Nat → Prop) : Assignment :=
  assign 25 (type := N ⇒ payloadType fields ⇒ (N ⇒ E) ⇒ E) constructorMeaning
    (assign 27 (type := SelectionProofs.Selection (payloadType fields))
      (HOLLightStandardTheory.selectionOperation carrier inhabitant (payloadType fields))
      (assign 28 (type := SelectionProofs.Selection (N ⇒ E))
        (HOLLightStandardTheory.selectionOperation carrier inhabitant (N ⇒ E))
        (assign 26 (type := E) (.up 0)
          (assign 20 (type := E ⇒ .prop) (fun value => .up (predicate value.down)) basisMeaning))))
noncomputable def model (predicate : Nat → Prop) : HenkinModel.{0,0,0} Base Const := .standard carrier (meaning predicate)
def values (predicate : Nat → Prop) : (model predicate).Valuation [] := fun index => nomatch index
theorem full (predicate : Nat → Prop) : (model predicate).FullDomains := HenkinModel.fullDomains_standard _ _

theorem zero_denote (predicate : Nat → Prop) : (model predicate).denote original.zero (values predicate) = .up 0 := rfl
theorem successor_denote (predicate : Nat → Prop) (n : Nat) :
    (model predicate).denote original.successor (values predicate) (.up n) = .up (n+1) := rfl
theorem constructor_denote (predicate : Nat → Prop) (tag : ULift.{1} Nat) (payload : Raw)
    (children : ULift.{1} Nat → ULift.{1} Nat) :
    (model predicate).denote constructor (values predicate) tag payload children = constructorMeaning tag payload children := rfl
theorem bottom_denote (predicate : Nat → Prop) : (model predicate).denote bottom (values predicate) = .up 0 := rfl

theorem payloadSelection_holds (predicate : Nat → Prop) : (model predicate).models (SelectionProofs.principle payloadSelection) := by
  intro question _ witness _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (payloadType fields) question ⟨witness,present⟩
theorem childrenSelection_holds (predicate : Nat → Prop) : (model predicate).models (SelectionProofs.principle childrenSelection) := by
  intro question _ witness _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant (N ⇒ E) question ⟨witness,present⟩

#print axioms constructor_denote
#print axioms childrenSelection_holds
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalModel
