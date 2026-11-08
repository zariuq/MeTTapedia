import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareRange

/-! The standard collapse child is executed and captured, rather than
supplied as a result array. Every saved pair restores its actual reached
frame; only final Empty occurrences are removed. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareCapture

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment snapshots)
open HECollectionSquareRange (squares)

def operand (minimal : Minimal.Services) (lower upper : Int) : Entry.Value :=
  .expression .active [.symbol "collapse-bind", .expression .active [.symbol "metta",
    HECollectionSquareRange.call lower upper, .symbol "%Undefined%",
    .grounded (minimal.contextPayload HECollectionSpaceExtension.space)]]

theorem surviving_values (lower : Int) (count : Nat) (rows : List Result)
    (seen : rows.map Prod.fst = squares lower count ++ [.symbol "Empty"]) :
    (survivingRows rows).map Prod.fst = squares lower count := by
  rw [HERangeSourceAdequacy.surviving_readout, seen, List.filter_append]
  have kept : (squares lower count).filter (fun value => value.erase != Atom.empty) = squares lower count := by
    apply List.filter_eq_self.mpr
    intro value member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    simp [Entry.Value.erase, Atom.empty]
  rw [kept]
  simp [Entry.Value.erase, Atom.empty]

theorem source (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (lower upper : Int) :
    let current := environment minimal nativePolicy external active primitive subtypes
    ∃ after pairs rows,
      Stateful.MinimalRel current HECollectionSpaceExtension.space world live scope caller (operand minimal lower upper)
        before [(.expression .active pairs, before)] after (policy := policy) ∧
      List.Forall₂ (StoredPairRel snapshots HECollectionSpaceExtension.space after) rows pairs ∧
      rows.map Prod.fst = squares lower (upper - lower).toNat ∧
      (∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) ∧ pairs.length = (upper - lower).toNat ∧ after.1 = world.1 := by
  let current := environment minimal nativePolicy external active primitive subtypes
  obtain ⟨children, evaluated, numeric, seen⟩ := HECollectionSquareRange.source minimal nativePolicy external active primitive subtypes
    world policy before live scope lower upper Atom.undefinedType (Or.inr rfl)
  obtain ⟨packed, after, captured⟩ := CaptureRowsRel.total snapshots (SnapshotServices.appendModel_total Space Unit)
    HECollectionSpaceExtension.space world children []
  obtain ⟨pairs, shape, stored⟩ := captured.encoded (SnapshotServices.appendModel_laws Space Unit)
  have same : packed = .expression .active pairs := by simpa only [List.reverse_nil, List.nil_append] using shape
  subst packed
  have observed := surviving_values lower (upper - lower).toNat children seen
  refine ⟨after, pairs, survivingRows children, ?_, stored, observed, ?_, ?_, captured.appendModel_preserves_base⟩
  · refine Stateful.MinimalRel.collapseBind (world1 := world) rfl ?_ captured
    apply Stateful.MinimalRel.metta
    simpa only [Entry.Value.erase, Atom.undefinedType] using evaluated
  · intro row member
    have fromChild : row ∈ children := (List.mem_filter.mp member).1
    rcases row with ⟨value, frame⟩
    cases numeric (value, frame) fromChild <;> simp [Entry.Value.erase, TypeSubst.typeVars]
  · have size := congrArg List.length observed
    have sameLength : (survivingRows children).length = (upper - lower).toNat := by simpa [squares] using size
    exact stored.length_eq.symm.trans sameLength

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareCapture
