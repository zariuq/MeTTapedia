import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeFrame
import Mettapedia.Languages.MeTTa.HE.EqualityClosure

/-!
# A second fresh arrow range joins the retained private class

After selecting a private result variable at a concrete range, the operator
cast can query a second fresh arrow instance. Its source match records an
equality between the two private names. This module constructs that match,
merge, model and selected frame while retaining every incoming constraint.
The whole standard-if arrow is covered, not only an isolated variable match.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Eval Spec.Eval.Completed

theorem fresh_not_in_equalities (bindings : Bindings) (name : String)
    (fresh : name ∉ specBindingVars bindings) : name ∉ bindings.eqVarsInOrder := by
  rw [EqualityClosure.mem_eqVarsInOrder_iff]
  intro member
  exact fresh (List.mem_append_right _ member)

theorem extended_private_facts (before : Bindings) (name : String) (expected : Atom)
    (fresh : name ∉ specBindingVars before) :
    (HEFreshRangeFrame.extend before name expected).lookup name = some expected ∧
      name ∉ (HEFreshRangeFrame.extend before name expected).eqVarsInOrder := by
  constructor
  · rw [← HEFreshRangeFrame.assign_eq_extend before name expected fresh]
    exact lookup_assign_of_lookup_none before name expected (HEFreshRangeFrame.fresh_lookup before name fresh)
  · exact fresh_not_in_equalities before name fresh

theorem assigned_in_support (bindings : Bindings) (name : String) (value : Atom)
    (assigned : bindings.lookup name = some value) : name ∈ specBindingVars bindings := by
  obtain ⟨pre, post, same, _⟩ := List.lookup_eq_some_iff.mp assigned
  have member : (name, value) ∈ bindings.assignments := by rw [same]; simp
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨(name, value), member, by simp⟩)

theorem alias_class_singleton (bindings : Bindings) (left right : String) (value : Atom)
    (isolated : left ∉ bindings.eqVarsInOrder) (assigned : bindings.lookup left = some value)
    (fresh : right ∉ specBindingVars bindings) :
    (bindings.addEquality left right).classValues left = [value] := by
  have different : left ≠ right := by
    intro same
    exact fresh (same ▸ assigned_in_support bindings left value assigned)
  exact EqualityClosure.classValues_addEquality_of_fresh isolated
    (fresh_not_in_equalities bindings right fresh) different assigned
    (HEFreshRangeFrame.fresh_lookup bindings right fresh)

theorem alias_merge (bindings : Bindings) (left right : String) (value : Atom)
    (isolated : left ∉ bindings.eqVarsInOrder) (assigned : bindings.lookup left = some value)
    (fresh : right ∉ specBindingVars bindings) :
    MergeRel equalityGroundedSemantic bindings (Bindings.empty.addEquality left right)
      (bindings.addEquality left right) := by
  apply MergeRel.mk (order := [.equality left right])
  · simp [constraints, Bindings.empty, Bindings.addEquality, List.eraseDups_cons]
  · exact .equality (.consistent (alias_class_singleton bindings left right value isolated assigned fresh)
      (by simp [ValuesAgree])) .nil

theorem alias_model (before : Frame) (left right : String)
    (fresh : right ∉ specBindingVars before.bindings) :
    ∃ valuation, TypeBindingSatisfied valuation (before.bindings.addEquality left right) := by
  obtain ⟨valuation, model⟩ := before.certified.satisfiable
  let extended : String → Atom := Function.update valuation right (valuation left)
  have preserved : TypeBindingSatisfied extended before.bindings := by
    apply (specTypeBindingSatisfied_congr_of_bindingVars
      (left := valuation) (right := extended) (bindings := before.bindings) ?_).mp model
    intro name member
    have different : name ≠ right := by intro same; exact fresh (same ▸ member)
    simp [extended, Function.update_of_ne different]
  refine ⟨extended, preserved.1, ?_⟩
  intro a b member
  rcases List.mem_append.mp member with old | added
  · exact preserved.2 a b old
  · cases List.mem_singleton.mp added
    by_cases same : left = right
    · simp [same]
    · simp [extended, Function.update_of_ne same]

def arrowWith (spine : List String) (name : String) : Atom :=
  .expression (spine.map Atom.symbol ++ [.var name])

theorem empty_alias_merge (left right : String) :
    MergeRel equalityGroundedSemantic Bindings.empty (Bindings.empty.addEquality left right)
      (Bindings.empty.addEquality left right) := by
  apply MergeRel.mk (order := [.equality left right])
  · simp [constraints, Bindings.empty, Bindings.addEquality, List.eraseDups_cons]
  · apply MergeConstraintsRel.equality (next := Bindings.empty.addEquality left right)
    · apply AddVarEqualityRel.consistent (values := [])
      · simp [Bindings.classValues, Bindings.empty, Bindings.addEquality, Bindings.lookup]
      · trivial
    · exact .nil

theorem arrow_match (spine : List String) (left right : String) :
    MatchRel equalityGroundedSemantic (arrowWith spine left) (arrowWith spine right)
      (Bindings.empty.addEquality left right) := by
  apply MatchRel.expression
  · induction spine with
    | nil =>
        exact .cons (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
          (empty_alias_merge left right) .nil
    | cons head spine ih =>
        exact .cons (.symSym head semanticLoopFree_empty)
          (.mk (by simp [constraints, Bindings.empty]) .nil) ih
  · exact semanticLoopFree_of_assignments_nil rfl

theorem arrow_source_match (spine : List String) (bindings : Bindings) (left right : String) (value : Atom)
    (isolated : left ∉ bindings.eqVarsInOrder) (assigned : bindings.lookup left = some value)
    (fresh : right ∉ specBindingVars bindings) :
    TypeMatchRel (arrowWith spine left) (arrowWith spine right) bindings
      (bindings.addEquality left right) :=
  .structural (by simp [arrowWith, Atom.undefinedType]) (by simp [arrowWith, Atom.atomType])
    (by simp [arrowWith, Atom.undefinedType]) (by simp [arrowWith, Atom.atomType])
    (arrow_match spine left right) (alias_merge bindings left right value isolated assigned fresh)

theorem forced_alias_read (after : Frame) (before : Bindings) (left right : String) (value : Atom)
    (closed : TypeSubst.typeVars value = []) (assigned : before.lookup left = some value)
    (bindings : after.bindings = before.addEquality left right) (policy : Policy) :
    (after.read policy (.var left)).erase = value ∧ (after.read policy (.var right)).erase = value := by
  obtain ⟨pre, post, layout, _⟩ := List.lookup_eq_some_iff.mp assigned
  have stored : (left, value) ∈ before.assignments := by rw [layout]; simp
  have forced (which : String) (side : which = left ∨ which = right) :
      (Entry.Value.eraseEnvironment after.environment).apply (.var which) = value := by
    apply after.certified.forced_read
    intro valuation model
    rw [bindings] at model
    have leftEq : valuation left = value := by
      simpa [applyTypeValuation_of_typeVars_eq_nil _ _ closed] using model.1 left value stored
    have aliasEq := model.2 left right (List.mem_append_right _ (by simp))
    rcases side with rfl | rfl
    · simpa only [applyTypeValuation] using leftEq
    · simpa only [applyTypeValuation] using aliasEq.symm.trans leftEq
  constructor
  · simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using forced left (Or.inl rfl)
  · simpa only [Frame.read, Entry.Value.erase_substitute_environment, Entry.Value.erase] using forced right (Or.inr rfl)

/-- The full operator-arrow cast earns its contextual frame from the
source match and fresh model extension, preserving the caller record. -/
theorem arrow_alias_frame (policy : Policy) (before : Frame) (spine : List String)
    (left right : String) (value : Atom) (closed : TypeSubst.typeVars value = [])
    (isolated : left ∉ before.bindings.eqVarsInOrder) (assigned : before.bindings.lookup left = some value)
    (fresh : right ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      after.bindings = before.bindings.addEquality left right ∧
      Frame.TypeRenewRel policy (arrowWith spine left) (arrowWith spine right) before after ∧
      ∀ readingPolicy : Policy,
        (after.read readingPolicy (.var left)).erase = value ∧
        (after.read readingPolicy (.var right)).erase = value := by
  have matched := arrow_source_match spine before.bindings left right value isolated assigned fresh
  have model := alias_model before left right fresh
  have policyMatch : policy.matching.Rel (arrowWith spine left) (arrowWith spine right)
      before.bindings (before.bindings.addEquality left right) := by
    cases chosen : policy.matching with
    | raw => exact matched
    | finite => exact ⟨matched, model⟩
  obtain ⟨after, bindings, renewed⟩ := Frame.TypeRenewRel.of_modelled_match before policyMatch model
  exact ⟨after, bindings, renewed, forced_alias_read after before.bindings left right value closed assigned bindings⟩

theorem if_number_alias_frame (policy : Policy) (before : Frame) (left right : String)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some (.symbol "Number"))
    (fresh : right ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      after.bindings = before.bindings.addEquality left right ∧
      Frame.TypeRenewRel policy (arrowWith ["->", "Bool", "Atom", "Atom"] left)
        (arrowWith ["->", "Bool", "Atom", "Atom"] right) before after ∧
      ∀ readingPolicy : Policy,
        after.read readingPolicy (.var left) = .symbol "Number" ∧
        after.read readingPolicy (.var right) = .symbol "Number" := by
  obtain ⟨after, bindings, renewed, read⟩ := arrow_alias_frame policy before ["->", "Bool", "Atom", "Atom"]
    left right (.symbol "Number") rfl isolated assigned fresh
  exact ⟨after, bindings, renewed, fun readingPolicy =>
    ⟨HEFreshRangeFrame.symbol_of_erase _ _ (read readingPolicy).1,
      HEFreshRangeFrame.symbol_of_erase _ _ (read readingPolicy).2⟩⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias
