import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaBindingCorrespondence

/-! # Binding and refusal controls for the emitted MeTTa patterns -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Controls

open Mettapedia.Languages.MeTTa.HE (Bindings simpleMatch)

/-- A guest variable is quoted data even when its spelling is a target name. -/
theorem guest_variable_is_data (sourceName : String) (first : Nat) :
    simpleMatch (pattern (.var sourceName) first).1.1
      (MeTTaData.encode (.var (freshName first))) Bindings.empty
      (sizeOf (Term.var sourceName) + 2) =
        some (Bindings.empty.assign (freshName first)
          (MeTTaData.encode (.var (freshName first)))) := by
  rw [pattern_matches _ _ _ _ _ (by omega) (FreshFrom.empty first)]
  rfl

/-- The raw equation IR records each occurrence and reads the first one;
fresh target variables preserve that convention without adding an equality. -/
theorem repeated_occurrences_keep_source_lookup (firstValue secondValue : Term) :
    let source := [Term.var "x", .var "x"]
    let values := [firstValue, secondValue]
    let result := extendMatch 0 [("x", firstValue), ("x", secondValue)] Bindings.empty
    simpleMatch (patterns source 0).1.1 (MeTTaData.encodeItems values) Bindings.empty
        (sizeOf source + 2) = some result ∧
      lookupRenamed (patterns source 0).1.2 result "x" = some (MeTTaData.encode firstValue) := by
  dsimp only
  constructor
  · rw [patterns_match _ _ _ _ _ (by omega) (FreshFrom.empty 0)]
    rfl
  · simpa [Env.lookup] using
      patterns_binding_lookup [.var "x", .var "x"] [firstValue, secondValue]
        [("x", firstValue), ("x", secondValue)] rfl 0 Bindings.empty (FreshFrom.empty 0) "x"

/-- Constructor tags are semantic: a list never matches an expression. -/
theorem list_expression_mismatch (source values : List Term) (first fuel : Nat)
    (enough : sizeOf (Term.list source) + 2 ≤ fuel) :
    simpleMatch (pattern (.list source) first).1.1 (MeTTaData.encode (.expr values))
      Bindings.empty fuel = none := by
  apply (pattern_refusal_iff _ _ _ _ _ enough (FreshFrom.empty first)).mpr
  rfl

/-- Wrong arity is a refusal at every fuel above the structural bound. -/
theorem argument_arity_mismatch (source values : List Term) (first fuel : Nat)
    (enough : sizeOf source + 2 ≤ fuel) (wrong : source.length ≠ values.length) :
    simpleMatch (patterns source first).1.1 (MeTTaData.encodeItems values)
      Bindings.empty fuel = none := by
  apply (patterns_refusal_iff _ _ _ _ _ enough (FreshFrom.empty first)).mpr
  cases matched : matchTerms source values with
  | none => rfl
  | some environment => exact False.elim (wrong (matchTerms_length matched))

/-- Exhaustion alone cannot witness a semantic refusal. -/
theorem exhausted_match_can_have_a_source_witness :
    matchTerm (.var "x") (.sym "a") = some [("x", .sym "a")] ∧
      simpleMatch (pattern (.var "x") 0).1.1 (MeTTaData.encode (.sym "a"))
        Bindings.empty 0 = none := ⟨rfl, rfl⟩

/-- Reusing an occupied target name would reject a valid source match. -/
theorem target_name_capture_changes_matching :
    matchTerm (.var "x") (.sym "a") = some [("x", .sym "a")] ∧
      simpleMatch (pattern (.var "x") 0).1.1 (MeTTaData.encode (.sym "a"))
        (Bindings.empty.assign (freshName 0) (MeTTaData.encode (.sym "b"))) 2 = none := by
  constructor <;> rfl

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Controls
