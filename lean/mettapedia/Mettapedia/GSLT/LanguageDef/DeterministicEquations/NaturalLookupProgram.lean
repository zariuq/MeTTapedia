import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListData
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# Authored natural-key table lookup

The first matching row supplies its value. Values remain inert data, including
call-shaped expressions. The host supplies list views and natural comparison;
lookup and ordered selection are performed by equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeNaturalTable {α : Type} (encode : α → Term) (entries : List (Nat × α)) : Term :=
  .list (entries.map fun (key, value) => .list [natural key, encode value])

def encodeLookupResult : Option Term → Term
  | none => .sym "None"
  | some value => .expr [.sym "Some", value]

def naturalLookupProgram : Program := [
  ⟨"table-get", "nik:nat-table-get", [.var "entries", .var "key"],
    .expr [.sym "nik:table-view", .expr [.sym "nik:list-view", .var "entries"], .var "key"]⟩,
  ⟨"table-empty", "nik:table-view", [.sym "List:Nil", .var "key"], .sym "None"⟩,
  ⟨"table-cons", "nik:table-view",
    [.expr [.sym "List:Cons", .list [.var "first", .var "value"], .var "rest"], .var "key"],
    .expr [.sym "nik:table-equal", .expr [.sym "nik:nat-eq", .var "key", .var "first"],
      .var "value", .var "rest", .var "key"]⟩,
  ⟨"table-found", "nik:table-equal", [.sym "True", .var "value", .var "rest", .var "key"],
    .expr [.sym "Some", .var "value"]⟩,
  ⟨"table-next", "nik:table-equal", [.sym "False", .var "value", .var "rest", .var "key"],
    .expr [.sym "nik:nat-table-get", .var "rest", .var "key"]⟩]

theorem naturalLookupProgram_leftLinear : LeftLinear naturalLookupProgram := by
  simp [LeftLinear, naturalLookupProgram, patternVarsList, patternVars]

private theorem lookup_start {α : Type} (encode : α → Term) (entries : List (Nat × α))
    (key : Nat) (result : Term)
    (next : Applies naturalLookupProgram computationalHost "nik:table-view"
      [listView (entries.map fun (key, value) => .list [natural key, encode value]), natural key] result) :
    Applies naturalLookupProgram computationalHost "nik:nat-table-get" [encodeNaturalTable encode entries, natural key]
      result := by
  refine Applies.equation (equation := naturalLookupProgram[0])
    (environment := [("entries", encodeNaturalTable encode entries), ("key", natural key)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil)) next
  exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil)
    (.primitive (by rfl) (computationalHost_list_view _))

private theorem lookup_cons {α : Type} (encode : α → Term) (first key : Nat) (value : α)
    (rest : List (Nat × α)) (result : Term)
    (next : Applies naturalLookupProgram computationalHost "nik:table-equal"
      [boolean (decide (key = first)), encode value, encodeNaturalTable encode rest, natural key] result) :
    Applies naturalLookupProgram computationalHost "nik:table-view"
      [listView (((first, value) :: rest).map fun (key, value) => .list [natural key, encode value]), natural key]
      result := by
  refine Applies.equation (equation := naturalLookupProgram[2])
    (environment := [("first", natural first), ("value", encode value),
      ("rest", encodeNaturalTable encode rest), ("key", natural key)]) (by rfl) (by rfl) ?_
  refine Evaluates.call (by simp [Special])
    (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))) next
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
    (.primitive (by rfl) (computationalHost_binary (operation := .equal) rfl _ _ (by decide) (by decide)))

private theorem lookup_next {α : Type} (encode : α → Term) (key : Nat) (value : α)
    (rest : List (Nat × α)) (result : Term)
    (next : Applies naturalLookupProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable encode rest, natural key] result) :
    Applies naturalLookupProgram computationalHost "nik:table-equal"
      [.sym "False", encode value, encodeNaturalTable encode rest, natural key] result := by
  refine Applies.equation (equation := naturalLookupProgram[4])
    (environment := [("value", encode value), ("rest", encodeNaturalTable encode rest), ("key", natural key)])
    (by rfl) (by rfl) ?_
  exact Evaluates.call (by simp [Special])
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) next

theorem natural_lookup_computes {α : Type} (encode : α → Term) (entries : List (Nat × α)) (key : Nat) :
    Applies naturalLookupProgram computationalHost "nik:nat-table-get" [encodeNaturalTable encode entries, natural key]
      (encodeLookupResult ((entries.lookup key).map encode)) := by
  induction entries with
  | nil => exact lookup_start encode [] key _ ⟨1, rfl⟩
  | cons entry rest ih =>
      obtain ⟨first, value⟩ := entry
      apply lookup_start
      apply lookup_cons
      by_cases same : key = first
      · subst key
        simp only [List.lookup, beq_self_eq_true, ↓reduceIte, decide_true, Option.map_some, boolean]
        exact ⟨2, rfl⟩
      · have different : (key == first) = false := by simp [same]
        simpa [same, List.lookup, different, boolean] using lookup_next encode key value rest _ ih

theorem natural_lookup_result_exact {α : Type} (encode : α → Term) (entries : List (Nat × α))
    (key : Nat) (result : Term) :
    Applies naturalLookupProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable encode entries, natural key] result ↔
      result = encodeLookupResult ((entries.lookup key).map encode) := by
  constructor
  · exact fun run => run.deterministic (natural_lookup_computes encode entries key)
  · rintro rfl; exact natural_lookup_computes encode entries key

namespace NaturalLookupControls

theorem first_matching_row_wins :
    Applies naturalLookupProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable id [(0, .sym "first"), (0, .sym "second")], natural 0]
      (encodeLookupResult (some (.sym "first"))) := natural_lookup_computes id _ _

theorem later_row_cannot_replace_first_match :
    ¬ Applies naturalLookupProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable id [(0, .sym "first"), (0, .sym "second")], natural 0]
      (encodeLookupResult (some (.sym "second"))) := by
  intro run
  have impossible := run.deterministic first_matching_row_wins
  simp [encodeLookupResult] at impossible

theorem stored_calls_are_not_executed :
    Applies naturalLookupProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable id [(1, .expr [.sym "nik:nat-eq", .sym "wrong", natural 0])], natural 1]
      (encodeLookupResult (some (.expr [.sym "nik:nat-eq", .sym "wrong", natural 0]))) :=
  natural_lookup_computes id _ _

theorem absent_key_has_no_value :
    Applies naturalLookupProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable id [(1, .sym "value")], natural 0] (.sym "None") :=
  natural_lookup_computes id _ _

theorem keys_do_not_wrap :
    Applies naturalLookupProgram computationalHost "nik:nat-table-get"
      [encodeNaturalTable id [(0, .sym "wrapped")], natural 18446744073709551616] (.sym "None") :=
  natural_lookup_computes id _ _

end NaturalLookupControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
