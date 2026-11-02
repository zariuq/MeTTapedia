import Mettapedia.Languages.Datalog.FactInput
import Mettapedia.Languages.Datalog.StaticTyping

/-! Whole fact-file reading preserves and reflects independent record
framing, typed field meanings, order and duplicates. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.FactInput

theorem rows_exact (relation : QualifiedName) (types : List AttributeType)
    (lines : List (List Char)) (facts : List GroundFact) :
    lines.mapM (fun line => (readFields? types (fields line)).map (GroundFact.mk relation)) = some facts ↔
      List.Forall₂ (fun line fact => fact.relation = relation ∧ FieldsMeaning types (fields line) fact.values) lines facts := by
  induction lines generalizing facts with
  | nil => cases facts <;> simp
  | cons line lines ih =>
    rw [List.mapM_cons]
    constructor
    · intro read
      obtain ⟨head, headRead, rest⟩ := Option.bind_eq_some_iff.mp read
      obtain ⟨tail, tailRead, same⟩ := Option.bind_eq_some_iff.mp rest
      cases Option.some.inj same
      obtain ⟨values, fieldsRead, same⟩ := Option.map_eq_some_iff.mp headRead
      subst head
      exact .cons ⟨rfl, readFields_sound _ _ _ fieldsRead⟩ ((ih tail).mp tailRead)
    · intro meaning
      cases meaning with
      | cons head tail =>
        obtain ⟨relationEq, valuesMeaning⟩ := head
        have headRead := readFields_complete valuesMeaning
        have tailRead := (ih _).mpr tail
        simp only [headRead, Option.map_some, tailRead]
        cases relationEq
        rfl

theorem read_exact (relation : QualifiedName) (types : List AttributeType) (input : String)
    (facts : List GroundFact) : read? relation types input = some facts ↔ Meaning relation types input facts := by
  have rows : read? relation types input =
      (Mettapedia.Util.DelimitedRecords.decode '\n' input.toList).mapM
        (fun line => (readFields? types (fields line)).map (GroundFact.mk relation)) := by
    unfold read?
    congr 1
    funext line
    cases readFields? types (fields line) <;> rfl
  rw [rows, rows_exact]
  constructor
  · intro meaning
    exact ⟨_, Mettapedia.Util.DelimitedRecords.decode_sound _ _, meaning⟩
  · rintro ⟨lines, framed, meaning⟩
    rw [Mettapedia.Util.DelimitedRecords.decode_complete framed]
    exact meaning

theorem FieldMeaning.typed {kind : AttributeType} {text : String} {value : Value}
    (meaning : FieldMeaning kind text value) : value.type = kind ∧ value.fits64 = true := by
  cases meaning with
  | symbol => exact ⟨rfl, rfl⟩
  | number _ width => exact ⟨rfl, width⟩
  | unsigned _ width => exact ⟨rfl, width⟩

theorem FieldsMeaning.typed {types : List AttributeType} {fields : List String} {values : List Value}
    (meaning : FieldsMeaning types fields values) :
    values.map Value.type = types ∧ ∀ value ∈ values, value.fits64 = true := by
  induction meaning with
  | nil => simp
  | cons head tail ih =>
    exact ⟨by simp only [List.map_cons, head.typed.1, ih.1],
      fun value member => (List.mem_cons.mp member).elim (fun same => same ▸ head.typed.2) (ih.2 value)⟩

theorem FieldsMeaning.valueTypes {types : List AttributeType} {fields : List String} {values : List Value}
    (meaning : FieldsMeaning types fields values) : List.Forall₂ StaticTyping.ValueTyped values types := by
  induction meaning with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.typed ih

theorem read_typed (signature : StaticTyping.Signature) (relation : QualifiedName) (types : List AttributeType)
    (declared : signature relation = some types) (input : String) (facts : List GroundFact)
    (read : read? relation types input = some facts) : ∀ fact ∈ facts, StaticTyping.FactTyped signature fact := by
  obtain ⟨lines, framed, meaning⟩ := (read_exact relation types input facts).mp read
  clear read framed
  induction meaning with
  | nil => simp
  | @cons line fact lines facts head tail ih =>
    intro value member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨types, head.1 ▸ declared, head.2.valueTypes⟩
    · exact ih value later

end Mettapedia.Languages.Datalog.FactInput
