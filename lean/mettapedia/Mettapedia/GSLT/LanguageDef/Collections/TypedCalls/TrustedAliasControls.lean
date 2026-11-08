import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ContractBindingFacts

/-!
# An aliased constructor head and a discharged result guard

The existing two-way source evaluator changes an open head through an ANY
argument's alias. The existing polymorphic pair protocol rejects the changed
result, even in a functional declaration space. A caller which consumes the
result and returns a fixed literal exposes omission of that guard.

The paired argument boundary isolates the only guarded argument; the other
alias is captured in the source environment. This is not a full compilation
theorem for the native two-argument reproducer. The native regression is
checked separately against the implementation's reference routes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedAliasControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open UnifyingRegions ContractBindingFacts
open Controls (decls decls_functional num sym gOne eff_gOne pair_rejects_declared_head)

def changed : Atom := .expression [sym "inc", num 1]

def record (argument : Atom) : Substitution := fun name =>
  if name = "source-a" then argument
  else if name = "source-b" then .var "g" else .var name

def facts : Facts := [("source-a", ⟨false, true⟩), ("source-b", ⟨false, false⟩)]
def pattern : Pat := .var "source-b"
def flags : ValueFlags := ⟨⟨true, false⟩, false⟩
def source : Expr := .letE pattern (.const (sym "inc")) (.var "source-a")

theorem initially_valid_facts : Sound decls (record gOne) facts := by
  intro entry member
  simp only [facts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨by simp, fun _ => Controls.gOne_uninterp⟩
  · simp [ContractBindingFacts.Holds]

theorem one_declaration_per_subject : Functional decls := decls_functional

theorem native_flags_allow_binding : nativeAllows decls facts pattern flags = true := by
  decide +kernel

theorem current_dependencies_refuse_binding :
    observedClaims facts (record gOne) pattern (sym "inc") = false := by decide +kernel

/-- Both source names participate in the actual unifier; the saved first
argument's head changes when the second name is bound. -/
theorem actual_source_changes_head :
    (evalUnifying (fun _ _ => 0) (fun _ => 0) source (record gOne)).map observe = {changed} := by
  cbv

def sourceBody (_ : List Atom → Multiset Atom) (args : List Atom) : Multiset Atom :=
  match args with
  | [argument] =>
      (evalUnifying (fun _ _ => 0) (fun _ => 0) source (record argument)).map observe
  | _ => 0

theorem source_body_at_argument (oracle : List Atom → Multiset Atom) :
    sourceBody oracle [gOne] = {changed} := actual_source_changes_head

theorem unguarded_version_returns : versionRun sourceBody 1 [gOne] = {changed} := by
  exact source_body_at_argument _

theorem result_guard_rejects_changed_head (grounded : String → Bool) :
    protocolRun decls grounded sourceBody pairRow 1 [gOne] = 0 := by
  change chainCall decls (metatype grounded)
    (sourceBody (protocolRun decls grounded sourceBody pairRow 0)) pairRow [gOne] = 0
  rw [chainCall_congr (body' := fun _ => {changed}) _ _ (source_body_at_argument _)]
  exact (pair_rejects_declared_head grounded).2

/-- The source-level declared-head change remains visible even if a caller
ignores the value and only observes whether its continuation runs. -/
def consumeResult (answers : Multiset Atom) : Multiset Atom := answers.bind fun _ => {num 1}

theorem nested_discharge_exposes_missing_guard (grounded : String → Bool) :
    consumeResult (versionRun sourceBody 1 [gOne]) = {num 1} ∧
      consumeResult (protocolRun decls grounded sourceBody pairRow 1 [gOne]) = 0 := by
  rw [unguarded_version_returns, result_guard_rejects_changed_head]
  simp [consumeResult]

theorem functional_space_does_not_make_discharge_safe (grounded : String → Bool) :
    Functional decls ∧ nativeAllows decls facts pattern flags = true ∧
      consumeResult (versionRun sourceBody 1 [gOne]) ≠
        consumeResult (protocolRun decls grounded sourceBody pairRow 1 [gOne]) := by
  refine ⟨decls_functional, native_flags_allow_binding, ?_⟩
  obtain ⟨unchecked, checked⟩ := nested_discharge_exposes_missing_guard grounded
  rw [unchecked, checked]
  exact Multiset.singleton_ne_zero _

def cleanSource : Expr := .letE pattern (.const (sym "foo")) (.var "source-a")

def cleanBody (_ : List Atom → Multiset Atom) (args : List Atom) : Multiset Atom :=
  match args with
  | [argument] =>
      (evalUnifying (fun _ _ => 0) (fun _ => 0) cleanSource (record argument)).map observe
  | _ => 0

theorem clean_alias_source (oracle : List Atom → Multiset Atom) :
    cleanBody oracle [gOne] = {.expression [sym "foo", num 1]} := by cbv

/-- Aliasing itself is not the failure: filling the open head with an
undeclared symbol preserves the pair guard and its sole occurrence. -/
theorem clean_alias_protocol_agrees (grounded : String → Bool) :
    versionRun cleanBody 1 [gOne] = {.expression [sym "foo", num 1]} ∧
      protocolRun decls grounded cleanBody pairRow 1 [gOne] = {.expression [sym "foo", num 1]} := by
  refine ⟨clean_alias_source _, ?_⟩
  change chainCall decls (metatype grounded)
    (cleanBody (protocolRun decls grounded cleanBody pairRow 0)) pairRow [gOne] = _
  rw [chainCall_congr (body' := fun _ => {.expression [sym "foo", num 1]}) _ _ (clean_alias_source _)]
  exact (Controls.pair_accepts_instance grounded).1

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedAliasControls
