import Mettapedia.Languages.VibeITP.Presentation.InstantiationSignature

/-!
# Postorder instantiation controls

These controls exercise raw operations and the separate statement guards.
Raw arity/list mismatches are included without asserting that they are valid
physical checker inputs. Completed refusals, malformed data and exhaustion
are separate observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation.Controls

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => instantiationProgram
local notation "H" => computationalHost

private def F : Spec.SymId := .fresh 13
private def binder : Spec.SymId := .fresh 14
private def other : Spec.SymId := .fresh 15
private def unary : SignatureTable := [(F, ⟨.fvar, [0]⟩)]
private def underBinder : SignatureTable := [(F, ⟨.fvar, [0]⟩), (binder, ⟨.constant, [1]⟩)]
private def nullary : SignatureTable := [(F, ⟨.fvar, []⟩)]
private def replacementBinder : SignatureTable := [(F, ⟨.fvar, []⟩), (binder, ⟨.constant, [1]⟩)]

theorem declared_free_variable_is_detected :
    Applies P H "vibe:is-fvar" [encodeTable unary, encodeSymbol F] (boolean true) :=
  isFvar_computes unary F

theorem unknown_symbol_is_not_free :
    Applies P H "vibe:is-fvar" [encodeTable [], encodeSymbol F] (boolean false) :=
  isFvar_computes [] F

theorem nested_occurrence_is_detected :
    Applies P H "vibe:has-fvar" [encodeTable underBinder, encode (.app binder [.app F [.lit [42]]])]
      (boolean true) := hasFvar_computes underBinder (.app binder [.app F [.lit [42]]])

theorem first_declaration_controls_occurrence :
    Applies P H "vibe:is-fvar" [encodeTable [(F, ⟨.constant, []⟩), (F, ⟨.fvar, []⟩)], encodeSymbol F]
      (boolean false) := isFvar_computes _ F

theorem nested_targets_are_processed_before_parent :
    Applies P H "vibe:instantiate" [encodeTable unary, encodeSymbol F, encode (.bvar 0),
      encode (.app F [.app F [.lit [42]]])] (encodeResult (some (.lit [42]))) :=
  instantiation_computes unary F (.bvar 0) (.app F [.app F [.lit [42]]])

theorem returned_replacement_is_not_instantiated_again :
    Applies P H "vibe:instantiate" [encodeTable unary, encodeSymbol F, encode (.app F [.bvar 0]),
      encode (.app F [.lit [42]])] (encodeResult (some (.app F [.lit [42]]))) :=
  instantiation_computes unary F (.app F [.bvar 0]) (.app F [.lit [42]])

theorem repeated_children_retain_order_and_multiplicity :
    Applies P H "vibe:instantiate" [encodeTable [(F, ⟨.fvar, [0]⟩), (binder, ⟨.constant, [0, 0]⟩)],
      encodeSymbol F, encode (.bvar 0), encode (.app binder [.app F [.lit [1]], .app F [.lit [2]]])]
      (encodeResult (some (.app binder [.lit [1], .lit [2]]))) :=
  instantiation_computes _ F (.bvar 0) (.app binder [.app F [.lit [1]], .app F [.lit [2]]])

theorem bound_argument_remains_bound :
    Applies P H "vibe:instantiate" [encodeTable underBinder, encodeSymbol F, encode (.bvar 0),
      encode (.app binder [.app F [.bvar 0]])] (encodeResult (some (.app binder [.bvar 0]))) :=
  instantiation_computes underBinder F (.bvar 0) (.app binder [.app F [.bvar 0]])

theorem raw_open_value_shifts_under_binder :
    Applies P H "vibe:inst-go" [encodeTable [(F, ⟨.fvar, []⟩), (binder, ⟨.constant, [1]⟩)],
      encodeSymbol F, natural 0, encode (.bvar 0), natural 0, encode (.app binder [.app F []])]
      (encodeResult (some (.app binder [.bvar 1]))) :=
  instGo_computes _ F 0 (.bvar 0) 0 (.app binder [.app F []])

theorem capturing_raw_result_is_refused :
    ¬ Applies P H "vibe:inst-go" [encodeTable [(F, ⟨.fvar, []⟩), (binder, ⟨.constant, [1]⟩)],
      encodeSymbol F, natural 0, encode (.bvar 0), natural 0, encode (.app binder [.app F []])]
      (encodeResult (some (.app binder [.bvar 0]))) := by
  rw [instGo_accepts_iff]
  decide

theorem other_lower_head_is_preserved :
    Applies P H "vibe:instantiate" [encodeTable [(F, ⟨.fvar, []⟩), (.fresh 12, ⟨.fvar, []⟩)],
      encodeSymbol F, encode (.lit [42]), encode (.app (.fresh 12) [])]
      (encodeResult (some (.app (.fresh 12) []))) :=
  instantiation_computes _ F (.lit [42]) (.app (.fresh 12) [])

theorem other_higher_head_is_preserved :
    Applies P H "vibe:instantiate" [encodeTable [(F, ⟨.fvar, []⟩), (other, ⟨.fvar, []⟩)],
      encodeSymbol F, encode (.lit [42]), encode (.app other [])]
      (encodeResult (some (.app other []))) := instantiation_computes _ F (.lit [42]) (.app other [])

theorem large_fresh_identity_has_no_word_cap :
    Applies P H "vibe:instantiate" [encodeTable [(.fresh 18446744073709551629, ⟨.fvar, []⟩)],
      encodeSymbol (.fresh 18446744073709551629), encode (.lit [42]), encode (.app (.fresh 18446744073709551629) [])]
      (encodeResult (some (.lit [42]))) :=
  instantiation_computes _ (.fresh 18446744073709551629) (.lit [42]) (.app (.fresh 18446744073709551629) [])

theorem builtin_and_fresh_identities_are_distinct :
    Applies P H "vibe:instantiate" [encodeTable [(F, ⟨.fvar, []⟩), (.builtin .impl, ⟨.constant, []⟩)],
      encodeSymbol F, encode (.lit [42]), encode (.app (.builtin .impl) [])]
      (encodeResult (some (.app (.builtin .impl) []))) :=
  instantiation_computes _ F (.lit [42]) (.app (.builtin .impl) [])

theorem raw_literal_does_not_inspect_offset :
    Applies P H "vibe:inst-go" [encodeTable [], encodeSymbol F, natural Spec.wordBound,
      encode (.bvar Spec.wordBound), natural Spec.wordBound, encode (.lit [0, 255, 42])]
      (encodeResult (some (.lit [0, 255, 42]))) :=
  instGo_computes [] F Spec.wordBound (.bvar Spec.wordBound) Spec.wordBound (.lit [0, 255, 42])

theorem raw_bound_variable_does_not_inspect_offset :
    Applies P H "vibe:inst-go" [encodeTable [], encodeSymbol F, natural Spec.wordBound,
      encode (.bvar Spec.wordBound), natural Spec.wordBound, encode (.bvar Spec.wordBound)]
      (encodeResult (some (.bvar Spec.wordBound))) :=
  instGo_computes [] F Spec.wordBound (.bvar Spec.wordBound) Spec.wordBound (.bvar Spec.wordBound)

theorem no_free_variables_prunes_binder_overflow :
    Applies P H "vibe:inst-go" [encodeTable [(binder, ⟨.constant, [Spec.wordBound]⟩)],
      encodeSymbol F, natural 0, encode (.bvar Spec.wordBound), natural Spec.wordBound,
      encode (.app binder [.bvar Spec.wordBound])]
      (encodeResult (some (.app binder [.bvar Spec.wordBound]))) :=
  instGo_computes _ F 0 (.bvar Spec.wordBound) Spec.wordBound (.app binder [.bvar Spec.wordBound])

theorem traversed_binder_overflow_refuses :
    Applies P H "vibe:instantiate" [encodeTable [(F, ⟨.fvar, []⟩), (binder, ⟨.constant, [Spec.wordBound]⟩)],
      encodeSymbol F, encode (.lit [42]), encode (.app binder [.app F []])] (encodeResult none) :=
  instantiation_computes _ F (.lit [42]) (.app binder [.app F []])

theorem shifted_value_overflow_refuses :
    Applies P H "vibe:inst-go" [encodeTable nullary, encodeSymbol F, natural 0,
      encode (.bvar (Spec.wordBound - 2)), natural 1, encode (.app F [])] (encodeResult none) :=
  instGo_computes nullary F 0 (.bvar (Spec.wordBound - 2)) 1 (.app F [])

theorem later_child_overflow_refuses_entire_application :
    Applies P H "vibe:instantiate" [encodeTable [(F, ⟨.fvar, []⟩), (binder, ⟨.constant, [0, Spec.wordBound]⟩)],
      encodeSymbol F, encode (.lit [42]), encode (.app binder [.app F [], .app F []])]
      (encodeResult none) := instantiation_computes _ F (.lit [42]) (.app binder [.app F [], .app F []])

theorem unknown_target_declaration_refuses_statement :
    Applies P H "vibe:instantiate" [encodeTable [], encodeSymbol F, encode (.lit [42]), encode (.lit [1])]
      (encodeResult none) := instantiation_computes [] F (.lit [42]) (.lit [1])

theorem constant_target_declaration_refuses_statement :
    Applies P H "vibe:instantiate" [encodeTable [(F, ⟨.constant, []⟩)], encodeSymbol F,
      encode (.lit [42]), encode (.app F [])] (encodeResult none) :=
  instantiation_computes _ F (.lit [42]) (.app F [])

theorem value_exceeding_arity_refuses_statement :
    Applies P H "vibe:instantiate" [encodeTable unary, encodeSymbol F, encode (.bvar 1),
      encode (.app F [.lit [42]])] (encodeResult none) :=
  instantiation_computes unary F (.bvar 1) (.app F [.lit [42]])

theorem open_result_refuses_statement :
    Applies P H "vibe:instantiate" [encodeTable unary, encodeSymbol F, encode (.bvar 0), encode (.bvar 0)]
      (encodeResult none) := instantiation_computes unary F (.bvar 0) (.bvar 0)

theorem closed_statement_without_occurrences_is_accepted :
    Applies P H "vibe:instantiate" [encodeTable nullary, encodeSymbol F, encode (.lit [42]), encode (.lit [1])]
      (encodeResult (some (.lit [1]))) := instantiation_computes nullary F (.lit [42]) (.lit [1])

theorem raw_missing_argument_uses_substitution_default :
    Applies P H "vibe:inst-go" [encodeTable [(F, ⟨.fvar, [0, 0]⟩)], encodeSymbol F, natural 2,
      encode (.bvar 0), natural 0, encode (.app F [.lit [42]])] (encodeResult (some (.bvar 0))) :=
  instGo_computes _ F 2 (.bvar 0) 0 (.app F [.lit [42]])

theorem raw_extra_arguments_do_not_change_explicit_arity :
    Applies P H "vibe:inst-go" [encodeTable unary, encodeSymbol F, natural 1, encode (.bvar 0), natural 0,
      encode (.app F [.lit [1], .lit [2]])] (encodeResult (some (.lit [1]))) :=
  instGo_computes unary F 1 (.bvar 0) 0 (.app F [.lit [1], .lit [2]])

theorem replacement_head_is_included_in_snapshot :
    Applies P H "vibe:instantiate"
      [encodeTable (instantiationSnapshot (signatureOf replacementBinder) F (.app binder [.bvar 0]) (.app F [])),
        encodeSymbol F, encode (.app binder [.bvar 0]), encode (.app F [])]
      (encodeResult (some (.app binder [.bvar 0]))) :=
  instantiation_computes_for_signature (signatureOf replacementBinder) F (.app binder [.bvar 0]) (.app F [])

theorem source_only_snapshot_refuses_valid_replacement :
    Spec.instantiateStatement (signatureOf (snapshot (signatureOf replacementBinder) (.app F []))) F
      (.app binder [.bvar 0]) (.app F []) = none ∧
    Spec.instantiateStatement (signatureOf replacementBinder) F (.app binder [.bvar 0]) (.app F []) =
      some (.app binder [.bvar 0]) := by
  constructor <;> rfl

theorem target_declaration_is_needed_without_occurrences :
    Spec.instantiateStatement (signatureOf (tableFor (signatureOf nullary) [])) F (.lit [42]) (.lit [1]) = none ∧
    Spec.instantiateStatement (signatureOf (instantiationSnapshot (signatureOf nullary) F (.lit [42]) (.lit [1])))
      F (.lit [42]) (.lit [1]) = some (.lit [1]) := by
  constructor <;> rfl

theorem invented_statement_result_is_refused (table : SignatureTable) (symbol : Spec.SymId)
    (value statement : Spec.Term) (claimed : Term)
    (different : claimed ≠ encodeResult (Spec.instantiateStatement (signatureOf table) symbol value statement)) :
    ¬ Applies P H "vibe:instantiate" [encodeTable table, encodeSymbol symbol, encode value, encode statement] claimed := by
  rw [instantiation_result_exact]
  exact different

theorem invented_raw_result_is_refused (table : SignatureTable) (symbol : Spec.SymId) (arity offset : Nat)
    (value source : Spec.Term) (claimed : Term)
    (different : claimed ≠ encodeResult (Spec.instGo (signatureOf table) symbol arity value offset source)) :
    ¬ Applies P H "vibe:inst-go"
      [encodeTable table, encodeSymbol symbol, natural arity, encode value, natural offset, encode source] claimed := by
  rw [instGo_result_exact]
  exact different

theorem no_fuel_is_exhaustion :
    apply P H 0 "vibe:instantiate" [encodeTable nullary, encodeSymbol F, encode (.lit [42]), encode (.app F [])] =
      .exhausted := rfl

theorem malformed_argument_list_faults :
    apply P H 3 "vibe:inst-args" [encodeTable [], encodeSymbol F, natural 0,
      encode (.lit [42]), natural 0, encodeBinders [], .sym "wrong"] = .failure := rfl

private theorem call_failure {environment : Env} {head : String} {arguments values : List Term}
    (ordinary : ¬ Special head arguments)
    (children : List.Forall₂ (Evaluates P H environment) arguments values)
    (failed : ∃ fuel, apply P H fuel head values = .failure) :
    ∃ fuel, eval P H fuel environment (.expr (.sym head :: arguments)) = .failure := by
  obtain ⟨n, children⟩ := evaluates_items children
  obtain ⟨m, failed⟩ := failed
  have stable : ∀ more, m ≤ more → apply P H more head values = .failure := by
    intro more enough
    exact (apply_le enough (by rw [failed]; intro equal; cases equal)).trans failed
  refine ⟨max n m + 1, ?_⟩
  rw [eval, evalStep_head ordinary]
  change (match evalItems P H (max n m) environment arguments with
    | .values values => apply P H (max n m) head values
    | .stop outcome => outcome) = _
  rw [children _ (Nat.le_max_left _ _)]
  change apply P H (max n m) head values = .failure
  exact stable _ (Nat.le_max_right _ _)

private theorem call_first_failure {environment : Env} {head : String} {first : Term} {rest : List Term}
    (ordinary : ¬ Special head (first :: rest))
    (failed : ∃ fuel, eval P H fuel environment first = .failure) :
    ∃ fuel, eval P H fuel environment (.expr (.sym head :: first :: rest)) = .failure := by
  obtain ⟨fuel, failed⟩ := failed
  refine ⟨fuel + 1, ?_⟩
  rw [eval, evalStep_head ordinary]
  change (match evalItems P H fuel environment (first :: rest) with
    | .values values => apply P H fuel head values
    | .stop outcome => outcome) = _
  simp only [evalItems, evalItemsWith, failed]

theorem malformed_scalar_arity_faults :
    ∃ fuel, apply P H fuel "vibe:inst-arity" [.sym "wrong", encodeTable [], encodeSymbol F,
      encode (.lit [42]), encode (.lit [1])] = .failure := by
  let environment : Env := [("arity", .sym "wrong"), ("table", encodeTable []), ("F", encodeSymbol F),
    ("value", encode (.lit [42])), ("statement", encode (.lit [1]))]
  have depth : Evaluates P H environment (.expr [.sym "vibe:depth", .var "table", .var "value"]) (natural 0) := by
    refine Evaluates.call (by simp [Special])
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ?_
    exact reuse_substitution_call (by decide +kernel) (ComputationalSubstitution.depth_computes_in_substitution [] (.lit [42]))
  have faulted : (H).primitive "nik:nat-le" [natural 0, .sym "wrong"] = .fault := by
    rw [computationalHost_arithmetic _ _ (by decide) (by decide)]
    exact naturalArithmeticHost_non_natural (operation := .le) rfl _ _ (.inr rfl)
  have operation : ∃ fuel, apply P H fuel "nik:nat-le" [natural 0, .sym "wrong"] = .failure := by
    have undefined : (P).defines "nik:nat-le" = false := rfl
    have undefinedAt : (P).definesAt "nik:nat-le" 2 = false := rfl
    refine ⟨0, ?_⟩
    change applyWith P H (eval P H 0) _ _ = _
    simp only [applyWith, List.length_cons, List.length_nil, undefinedAt, undefined,
      Bool.false_eq_true, ↓reduceIte, faulted]
  have guard : ∃ fuel, eval P H fuel environment
      (.expr [.sym "nik:nat-le", .expr [.sym "vibe:depth", .var "table", .var "value"], .var "arity"]) = .failure :=
    call_failure (by simp [Special]) (.cons depth (.cons (.variable (by rfl)) .nil)) operation
  have body := call_first_failure (head := "vibe:inst-value-depth")
    (rest := [.var "table", .var "F", .var "arity", .var "value", .var "statement"])
    (by simp [Special]) guard
  obtain ⟨fuel, bodyFailed⟩ := body
  refine ⟨fuel, ?_⟩
  have defined : (P).definesAt "vibe:inst-arity" 5 = true := rfl
  have selected : (P).select "vibe:inst-arity"
      [.sym "wrong", encodeTable [], encodeSymbol F, encode (.lit [42]), encode (.lit [1])] =
      some (instantiationEquations[40], environment) := rfl
  change applyWith P H (eval P H fuel) _ _ = _
  simp only [applyWith, List.length_cons, List.length_nil, defined, ↓reduceIte, selected]
  exact bodyFailed

end Mettapedia.Languages.VibeITP.Presentation.ComputationalInstantiation.Controls
