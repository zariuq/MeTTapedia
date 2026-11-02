import Mettapedia.Languages.Datalog.IRCodec

/-! Successful scalar and vector decoding recovers the original canonical
IR payload. These are the reverse laws complementing encode/decode round trips. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Datalog.IRCodec

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

theorem atom_inverse (source : Pattern) (text : String) (read : atom? source = some text) : atom text = source := by
  unfold atom? at read
  split at read
  · cases Option.some.inj read
    rfl
  · cases read

theorem mapM_inverse {α β : Type} (encode : α → β) (decode : β → Option α)
    (inverse : ∀ source value, decode source = some value → encode value = source)
    (sources : List β) (values : List α) (read : sources.mapM decode = some values) : values.map encode = sources := by
  induction sources generalizing values with
  | nil => cases Option.some.inj read; rfl
  | cons source sources ih =>
    rw [List.mapM_cons] at read
    change ((decode source).bind fun first => (sources.mapM decode).bind fun rest => some (first :: rest)) = some values at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨first,headRead,rest,tailRead,rfl⟩ := read
    simp only [List.map_cons,inverse source first headRead,ih rest tailRead]

theorem vector_inverse {α : Type} (encode : α → Pattern) (decode : Pattern → Option α)
    (inverse : ∀ source value, decode source = some value → encode value = source)
    (source : Pattern) (values : List α) (read : vector? decode source = some values) : vector encode values = source := by
  unfold vector? at read
  split at read
  · rename_i sources
    simp only [vector,mapM_inverse encode decode inverse sources values read]
  · cases read

theorem integer_inverse (text : String) (value : Int) (read : integer? text = some value) : value.repr = text := by
  change (text.toInt?.bind fun number => if number.repr == text then some number else none) = some value at read
  obtain ⟨number,_,accepted⟩ := Option.bind_eq_some_iff.mp read
  split at accepted
  · rename_i good
    have same : number = value := Option.some.inj accepted
    exact same ▸ beq_iff_eq.mp good
  · cases accepted

theorem natural_inverse (text : String) (value : Nat) (read : natural? text = some value) : value.repr = text := by
  change (text.toNat?.bind fun number => if number.repr == text then some number else none) = some value at read
  obtain ⟨number,_,accepted⟩ := Option.bind_eq_some_iff.mp read
  split at accepted
  · rename_i good
    have same : number = value := Option.some.inj accepted
    exact same ▸ beq_iff_eq.mp good
  · cases accepted

theorem value_inverse (source : Pattern) (output : Value) (read : value? source = some output) : value output = source := by
  unfold value? at read
  split at read
  · rename_i payload
    obtain ⟨text,parsed,rfl⟩ := Option.map_eq_some_iff.mp read
    simp only [value,atom_inverse payload text parsed]
  · rename_i payload
    change ((atom? payload).bind fun text => (integer? text).bind fun number => some (Value.number number)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨text,textRead,number,parsed,rfl⟩ := read
    have leaf : atom number.repr = payload := (congrArg atom (integer_inverse text number parsed)).trans (atom_inverse payload text textRead)
    simp only [value,leaf]
  · rename_i payload
    change ((atom? payload).bind fun text => (natural? text).bind fun number => some (Value.unsigned number)) = some output at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨text,textRead,number,parsed,rfl⟩ := read
    have leaf : atom number.repr = payload := (congrArg atom (natural_inverse text number parsed)).trans (atom_inverse payload text textRead)
    simp only [value,leaf]
  · rename_i payload
    change ((atom? payload).bind fun text => (natural? text).bind fun word =>
      if word < 2 ^ 64 then some (Value.floating (UInt64.ofNat word)) else none) = some output at read
    simp only [Option.bind_eq_some_iff] at read
    obtain ⟨text,textRead,word,parsed,accepted⟩ := read
    split at accepted
    · rename_i inside
      cases Option.some.inj accepted
      have leaf : atom word.repr = payload := (congrArg atom (natural_inverse text word parsed)).trans (atom_inverse payload text textRead)
      simp only [value,UInt64.toNat_ofNat',Nat.mod_eq_of_lt inside,leaf]
    · cases accepted
  · cases read

#print axioms vector_inverse
#print axioms value_inverse

end Mettapedia.Languages.Datalog.IRCodec
