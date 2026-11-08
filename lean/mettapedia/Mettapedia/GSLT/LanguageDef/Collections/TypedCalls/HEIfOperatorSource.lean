import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias

/-!
# The actual standard-if operator cast after schematic selection

The selected result variable is already constrained by the caller. The
operator's subsequent type lookup introduces a second fresh arrow instance;
the source cast joins its result variable to the retained private class.
This derives the reached frame from matching and its model, rather than
assuming that operator evaluation leaves the selected record unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfOperatorSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Bindings.ScopeObservation
open HEIfSourceSelection (signature)

def castScope (scope : List String) (live : List Atom) (before : Frame) (left : String) : List String :=
  invocationTypeScope
    (invocationTypeScope scope live (.symbol "if") (signature left).functionType before.bindings)
    [] (.symbol "if") (signature left).functionType before.bindings

theorem source_of_query {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (left right : String)
    (queried : environment.lookup
      (invocationTypeScope scope live (.symbol "if") (signature left).functionType before.bindings)
      (environment.view world label) before.bindings (.symbol "if") (signature left).functionType [(signature right).functionType])
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some (.symbol "Number"))
    (fresh : right ∉ castScope scope live before left) :
    ∃ after : Frame,
      Stateful.AtomRel environment label world live scope (.symbol "if") (signature left).functionType before
        [(.symbol "if", after)] world (policy := policy) ∧
      after.bindings = before.bindings.addEquality left right ∧
      ∀ readingPolicy,
        after.read readingPolicy (.var left) = .symbol "Number" ∧
        after.read readingPolicy (.var right) = .symbol "Number" := by
  have bindingFresh : right ∉ specBindingVars before.bindings := by
    intro present
    exact fresh (by simp [castScope, invocationTypeScope, present])
  have sourceMatch : TypeMatchRel (signature left).functionType (signature right).functionType
      before.bindings (before.bindings.addEquality left right) := by
    simpa [signature, HEFreshRangeAlias.arrowWith, CompletedDelivery.arrowType, Atom.atomType] using
      HEFreshRangeAlias.arrow_source_match ["->", "Bool", "Atom", "Atom"] before.bindings
        left right (.symbol "Number") isolated assigned bindingFresh
  have model := HEFreshRangeAlias.alias_model before left right bindingFresh
  have policyMatch : policy.matching.Rel (signature left).functionType (signature right).functionType
      before.bindings (before.bindings.addEquality left right) := by
    cases matching : policy.matching with
    | raw => exact sourceMatch
    | finite => exact ⟨sourceMatch, model⟩
  obtain ⟨after, bindings, renewed⟩ := Frame.CastRenewRel.of_modelled_source_match
    (policy := policy) before (earlier := []) (later := []) queried rfl
    (by simp) policyMatch model
  have afterMatch : policy.matching.Rel (signature left).functionType (signature right).functionType
      before.bindings after.bindings := by rw [bindings]; exact policyMatch
  have readSymbol : before.read policy (.symbol "if") = .symbol "if" := by
    simp [Frame.read, Entry.Value.substitute]
  have evaluated : Stateful.AtomRel environment label world live scope (.symbol "if")
      (signature left).functionType before [(.symbol "if", after)] world (policy := policy) := by
    apply Stateful.AtomRel.cast (raw := [(.symbol "if", after.bindings)])
    · rw [readSymbol]
      apply Entry.Rel.cast (metaType := Atom.symbolType)
      · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · simpa only [Entry.Value.erase] using MetaTypeRel.symbol "if"
      · simp [signature, CompletedDelivery.arrowType, Atom.atomType, Atom.symbolType, Atom.variableType]
      · exact Or.inl ⟨"if", by simp [Entry.Value.erase]⟩
      · simp [Entry.Value.erase, Atom.unit]
    · rw [readSymbol]
      simp only [Entry.Value.erase]
      exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) afterMatch
    · rw [readSymbol]
      exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase],
        by simpa only [Entry.Value.erase] using renewed, by simp [Entry.Value.erase]⟩ .nil
  refine ⟨after, evaluated, bindings, ?_⟩
  intro readingPolicy
  have reads := HEFreshRangeAlias.forced_alias_read after before.bindings left right (.symbol "Number")
    rfl assigned bindings readingPolicy
  exact ⟨HEFreshRangeFrame.symbol_of_erase _ _ reads.1, HEFreshRangeFrame.symbol_of_erase _ _ reads.2⟩

theorem source {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (left right : String)
    (declared : getAtomTypes (environment.view world label) (.symbol "if") = [(signature "t").functionType])
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some (.symbol "Number"))
    (fresh : right ∉ castScope scope live before left) :
    ∃ after : Frame,
      Stateful.AtomRel environment label world live scope (.symbol "if") (signature left).functionType before
        [(.symbol "if", after)] world (policy := policy) ∧
      after.bindings = before.bindings.addEquality left right ∧
      ∀ readingPolicy,
        after.read readingPolicy (.var left) = .symbol "Number" ∧
        after.read readingPolicy (.var right) = .symbol "Number" := by
  apply source_of_query environment policy label world live scope before left right
  · rw [lookup]
    exact HEIfSourceSelection.signature_lookup _ _ before _ right declared fresh
  · exact isolated
  · exact assigned
  · exact fresh

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfOperatorSource
