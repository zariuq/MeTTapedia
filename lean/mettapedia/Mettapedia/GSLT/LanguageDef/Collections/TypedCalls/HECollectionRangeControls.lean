import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionRange

/-! Controls for the extended-space inferred range endpoint. Type-service
completion, source result multiplicity and program-world retention are
checked separately rather than conflated into one answer observation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionRangeControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open RetainedTypePayloads (ExternalView)
open TypeReadSupply (Supply)
open HECollectionWorld (World environment)

theorem new_square_declaration_changes_read (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (external : ExternalView) (supply : Supply) (depth : Nat) :
    (NativeTypeScopedReads.evaluate ops HECollectionTypeReadPrimitives.source external (depth + 1)
      (.infer true (.symbol "sq")) supply).1 = some (.types [CollectionStdlibSource.squareType]) ∧
    (NativeTypeScopedReads.evaluate ops HERangeTypeReadPrimitives.source external (depth + 1)
      (.infer true (.symbol "sq")) supply).1 = some (.types [ops.undefined]) := by
  constructor
  · apply HECollectionTypeReadPrimitives.closed_symbol
    · rw [HECollectionTypeReadPrimitives.declarations_eq]; rfl
    · rfl
  · exact congrArg Prod.fst (HERangeTypeReadPrimitives.undeclared_symbol_read ops external depth supply "sq" (by
      rw [HERangeTypeReadPrimitives.declarations_eq]; rfl))

theorem closure_is_not_known_empty (external : ExternalView) (supply : Supply) :
    let packet := HECollectionTypeReadPrimitives.source
    (ScopedSubtypeReads.completeTypes external packet.rows packet.subtypeFresh packet.alpha 0 [.symbol "Number"] supply).1 = none ∧
    (ScopedSubtypeReads.completeTypes external packet.rows packet.subtypeFresh packet.alpha 1 [.symbol "Number"] supply).1 =
      some [.symbol "Number"] := ⟨rfl, HECollectionTypeReadPrimitives.closure external _ supply⟩

theorem cross_zero (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom) (saved : List Frame) :
    let policy := Policy.unchangedPreservingReady .preserve
    let current := environment minimal policy external active primitive subtypes
    ∃ rows, Stateful.AtomRel current HECollectionSpaceExtension.space ((), saved) [] []
      (HERangeUntypedEntry.rangeCall (-1) 2) (.symbol "Number") Controls.argumentAliasFrame rows ((), saved) (policy := policy) ∧
      rows.map Prod.fst = [.grounded (.int (-1)), .grounded (.int 0), .grounded (.int 1), .symbol "Empty"] := by
  dsimp only
  obtain ⟨rows, run, _, seen⟩ := HECollectionRange.source minimal (.unchangedPreservingReady .preserve) external active primitive subtypes
    ((), saved) (.unchangedPreservingReady .preserve) Controls.argumentAliasFrame [] [] (-1) 2 (.symbol "Number") (Or.inl rfl)
  exact ⟨rows, run, by simpa [HERangeSourceAdequacy.values, List.range_succ] using seen⟩

theorem descending_is_terminal_empty (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom) (world : World) (before : Frame) :
    let policy := Policy.unchangedPreservingReady .preserve
    let current := environment minimal policy external active primitive subtypes
    ∃ rows, Stateful.AtomRel current HECollectionSpaceExtension.space world [] []
      (HERangeUntypedEntry.rangeCall 5 2) Atom.undefinedType before rows world (policy := policy) ∧
      rows.map Prod.fst = [.symbol "Empty"] ∧ rows ≠ [] := by
  dsimp only
  obtain ⟨rows, run, _, seen⟩ := HECollectionRange.source minimal (.unchangedPreservingReady .preserve) external active primitive subtypes
    world (.unchangedPreservingReady .preserve) before [] [] 5 2 Atom.undefinedType (Or.inr rfl)
  have shape : rows.map Prod.fst = [.symbol "Empty"] := by simpa [HERangeSourceAdequacy.values] using seen
  exact ⟨rows, run, shape, by intro empty; simp [empty] at shape⟩

theorem duplicate_superpose (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (world : World) (policy : Policy) (before : Frame) (value : Int) :
    let current := environment minimal policy external active primitive subtypes
    Stateful.AtomRel current HECollectionSpaceExtension.space world [] []
      (HERangeSuperposeSource.call [.grounded (.int value), .grounded (.int value)]) Atom.undefinedType before
      [(.grounded (.int value), before), (.grounded (.int value), before)] world (policy := policy) := by
  dsimp only
  have child : ¬FunctionPending policy (.grounded (.int value)) ∧
      (Entry.Value.grounded (.int value)).erase ≠ Atom.notReducible ∧
      ¬IsEmptyOrErrorRel (Entry.Value.grounded (.int value)).erase ∧
      Stateful.AtomRel (environment minimal policy external active primitive subtypes) HECollectionSpaceExtension.space world [] []
        (.grounded (.int value)) Atom.undefinedType before [(.grounded (.int value), before)] world (policy := policy) :=
    ⟨by simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase], by simp [Entry.Value.erase, Atom.notReducible],
      by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty],
      HECollectionArithmetic.number_undefined minimal policy external active primitive subtypes world policy [] [] before value⟩
  have run := HECollectionSuperpose.source minimal policy external active primitive subtypes world policy before [] []
    [.grounded (.int value), .grounded (.int value)] [[(.grounded (.int value), before)], [(.grounded (.int value), before)]]
    Atom.undefinedType (by decide) (by decide)
    (by simp [Entry.Value.erase, TypeSubst.typeVarsList, TypeSubst.typeVars]) (by simp) (.cons child (.cons child .nil))
    (by intro row member; simp at member; subst row; exact .number value)
  simpa using run

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionRangeControls
