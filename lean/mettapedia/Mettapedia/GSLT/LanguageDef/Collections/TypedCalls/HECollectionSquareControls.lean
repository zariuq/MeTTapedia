import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareCapture
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldWorldServices

/-! Controls for the composed square/range child and its actual capture.
Equal squares retain both occurrences; source typing is not inferred from
those results, and final Empty is removed only at capture. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment snapshots)

theorem cross_zero_duplicates (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom) (world : World) :
    let policy := Policy.unchangedPreservingReady .preserve
    ∃ rows, Stateful.AtomRel (environment minimal policy external active primitive subtypes) HECollectionSpaceExtension.space world [] []
      (HECollectionSquareRange.call (-1) 2) Atom.undefinedType Controls.argumentAliasFrame rows world (policy := policy) ∧
      rows.map Prod.fst = [.grounded (.int 1), .grounded (.int 0), .grounded (.int 1), .symbol "Empty"] := by
  dsimp only
  obtain ⟨rows, run, _, seen⟩ := HECollectionSquareRange.source minimal (.unchangedPreservingReady .preserve) external active primitive subtypes
    world (.unchangedPreservingReady .preserve) Controls.argumentAliasFrame [] [] (-1) 2 Atom.undefinedType (Or.inr rfl)
  exact ⟨rows, run, by simpa [HECollectionSquareRange.squares, List.range_succ] using seen⟩

theorem empty_range_returns_terminal_empty (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom) (world : World) (before : Frame) :
    let policy := Policy.unchangedPreservingReady .preserve
    ∃ rows, Stateful.AtomRel (environment minimal policy external active primitive subtypes) HECollectionSpaceExtension.space world [] []
      (HECollectionSquareRange.call 2 2) Atom.undefinedType before rows world (policy := policy) ∧
      rows.map Prod.fst = [.symbol "Empty"] := by
  dsimp only
  obtain ⟨rows, run, _, seen⟩ := HECollectionSquareRange.source minimal (.unchangedPreservingReady .preserve) external active primitive subtypes
    world (.unchangedPreservingReady .preserve) before [] [] 2 2 Atom.undefinedType (Or.inr rfl)
  exact ⟨rows, run, by simpa [HECollectionSquareRange.squares] using seen⟩

theorem capture_keeps_both_ones (minimal : Minimal.Services) (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom) (world : World) :
    let policy := Policy.unchangedPreservingReady .preserve
    ∃ after pairs rows,
      Stateful.MinimalRel (environment minimal policy external active primitive subtypes) HECollectionSpaceExtension.space world [] [] none
        (HECollectionSquareCapture.operand minimal (-1) 2) Controls.argumentAliasFrame
        [(.expression .active pairs, Controls.argumentAliasFrame)] after (policy := policy) ∧
      List.Forall₂ (StoredPairRel snapshots HECollectionSpaceExtension.space after) rows pairs ∧
      rows.map Prod.fst = [.grounded (.int 1), .grounded (.int 0), .grounded (.int 1)] ∧ pairs.length = 3 := by
  dsimp only
  obtain ⟨after, pairs, rows, run, stored, seen, _, count, _⟩ :=
    HECollectionSquareCapture.source minimal (.unchangedPreservingReady .preserve) external active primitive subtypes world
      (.unchangedPreservingReady .preserve) Controls.argumentAliasFrame [] [] none (-1) 2
  exact ⟨after, pairs, rows, run, stored, by simpa [HECollectionSquareRange.squares, List.range_succ] using seen, count⟩

theorem raw_range_type_is_not_its_numeric_results (external : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (supply : TypeReadSupply.Supply) (lower upper : Int) :
    (NativeTypeScopedReads.evaluate (HECollectionInferredQueries.currentOps external active primitive subtypes)
      HECollectionTypeReadPrimitives.source external 2
      (.infer true (.expression [.symbol "range", .grounded (.int lower), .grounded (.int upper)])) supply).1 ≠
      some (.types [.symbol "Number"]) := by
  rw [HECollectionTypeReadApplications.range_type]
  simp [HECollectionInferredQueries.currentOps, TypeScopeMatcher.currentOps, TypeScopeMatcher.ops, Atom.undefinedType]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareControls
