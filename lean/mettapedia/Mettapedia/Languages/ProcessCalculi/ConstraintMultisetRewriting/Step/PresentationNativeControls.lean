import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationNativePreparation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativePublicationControls
import Mathlib.Data.Nat.Pairing

/-! # Identical prepared syntax can have different admitted publications

The existing conditional-template execution supplies two real firings with
different publication recipes. Both have exactly the same physical prepared
views and scalar bundle. Thus the bundle cannot replace the full candidate.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeControls

open Mettapedia.OSLF
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Interface
open ContextualConditionalTemplateControls

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

abbrev state := templateState locals inners before
abbrev target := SchemaPreparation.TargetSignature bank captures

def encodeHead : Binding.CommonABT.Head target → Payloads.Head
  | ⟨_, .inl .pair⟩ => .symbol 0
  | ⟨_, .inl (.literal number)⟩ => .symbol (number + 1)
  | ⟨_, .inr (.mk (.inl ⟨_, .inl impossible⟩))⟩ => nomatch impossible
  | ⟨_, .inr (.mk (.inl ⟨scope, .inr (name, ())⟩))⟩ => .hole (Nat.pair 0 (Nat.pair scope name))
  | ⟨_, .inr (.mk (.inr ()))⟩ => .hole (Nat.pair 1 0)

def decodeHead : Payloads.Head → Option (Binding.CommonABT.Head target)
  | .symbol 0 => some ⟨(), .inl .pair⟩
  | .symbol (number + 1) => some ⟨(), .inl (.literal number)⟩
  | .hole code => match Nat.unpair code with
    | (0, privateCode) => some ⟨(), .inr (.mk (.inl
        (ScopedVar.at (Nat.unpair privateCode).1 (.inr ((Nat.unpair privateCode).2, ())))))⟩
    | (1, 0) => some ⟨(), .inr (.mk (.inr ()))⟩
    | _ => none
  | _ => none

theorem head_roundtrip (head : Binding.CommonABT.Head target) : decodeHead (encodeHead head) = some head := by
  match head with
  | ⟨sort, .inl original⟩ => cases sort; cases original <;> rfl
  | ⟨_, .inr (.mk (.inl ⟨_, .inl impossible⟩))⟩ => nomatch impossible
  | ⟨_, .inr (.mk (.inl ⟨scope, .inr (name, ())⟩))⟩ =>
      simp [encodeHead, decodeHead, Nat.unpair_pair, ScopedVar.at]
      apply ContextualFamily.Operator.key_injective
      simp [ContextualFamily.Operator.key, Nat.unpair_pair]
  | ⟨_, .inr (.mk (.inr ()))⟩ => simp [encodeHead, decodeHead, Nat.unpair_pair]

def headCode : Intrinsic.HeadPresentation target where
  key := ⟨"tcalc.conditional-template-controls", 1⟩
  view := encodeHead
  expand := decodeHead
  expand_view := head_roundtrip

theorem same_prepared_source_different_publications (fuel : Nat) :
    ∃ (f g : NativeFiring state) (admittedF : f.Realized) (admittedG : g.Realized)
      (physical : SchemaPreparation.Views Payloads.Term),
      NativePreparation.prepare? (s := state) headCode f = some physical ∧
      NativePreparation.prepare? (s := state) headCode g = some physical ∧
      SchemaPreparation.readSourceViews? bank captures headCode [] () (SchemaPreparation.printViews physical) =
        some (SchemaPreparation.viewsOf bank captures f.prepared) ∧
      (native (S := base) (O := Nat) (Γ := []) (sort := ())).result f admittedF ≠
        (native (S := base) (O := Nat) (Γ := []) (sort := ())).result g admittedG := by
  obtain ⟨f, g, admittedF, admittedG, rule, selection, _, _, _, _, different⟩ :=
    PublicationControls.native_result_depends_on_recipes fuel
  obtain ⟨physical, computed, _⟩ := NativePreparation.prepare_unique (s := state) headCode f
  refine ⟨f, g, admittedF, admittedG, physical, computed, ?_,
    NativePreparation.source_readback (s := state) headCode f computed, different⟩
  rw [← NativePreparation.preparation_congr (s := state) headCode rule selection]
  exact computed

#print axioms head_roundtrip
#print axioms same_prepared_source_different_publications

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.NativeControls
