import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSchemaPreparation
import Mathlib.Data.Nat.Pairing

/-! # Repeated schema reads retain private identities and shared captures

The same physical occurrence is selected twice. The existing reservation
gives its two uses different scopes, and the executable opening/readback
route preserves that distinction. A shared value remains the positive twin.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SchemaControls

open Mettapedia.OSLF
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.Parsing
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Logic.LP (ScopedVar)

abbrev base : Signature where
  Srt := Unit
  Op _ := Nat
  arity _ := []

abbrev locals : Nat → MetaArity base := fun _ => ([(), ()], ())
abbrev captures : Nat → MetaArity base := fun _ => ([(), ()], ())
abbrev target := SchemaPreparation.TargetSignature locals captures

def encodeHead : Binding.CommonABT.Head target → Payloads.Head
  | ⟨_, .inl original⟩ => .symbol original
  | ⟨_, .inr (.mk (.inl name))⟩ => .hole (Nat.pair 0 (Nat.pair name.scope name.name))
  | ⟨_, .inr (.mk (.inr name))⟩ => .hole (Nat.pair 1 name)

def decodeHead : Payloads.Head → Option (Binding.CommonABT.Head target)
  | .symbol original => some ⟨(), .inl original⟩
  | .hole code => match Nat.unpair code with
    | (0, localCode) => some ⟨(), .inr (.mk (.inl (ScopedVar.at (Nat.unpair localCode).1 (Nat.unpair localCode).2)))⟩
    | (1, name) => some ⟨(), .inr (.mk (.inr name))⟩
    | _ => none
  | _ => none

theorem head_roundtrip (head : Binding.CommonABT.Head target) : decodeHead (encodeHead head) = some head := by
  match head with
  | ⟨sort, .inl original⟩ => cases sort; rfl
  | ⟨_, .inr (.mk (.inl ⟨scope, name⟩))⟩ =>
      simp [encodeHead, decodeHead, Nat.unpair_pair, ScopedVar.at]
      apply ContextualFamily.Operator.key_injective
      simp [ContextualFamily.Operator.key, Nat.unpair_pair]
  | ⟨_, .inr (.mk (.inr name))⟩ => simp [encodeHead, decodeHead, Nat.unpair_pair]

def code : Intrinsic.HeadPresentation target where
  key := ⟨"tcalc.contextual-schema-controls", 1⟩
  view := encodeHead
  expand := decodeHead
  expand_view := head_roundtrip

def privateBody : Term (signature base (ContextualSelectionViews.source locals captures)) [(), ()] () :=
  generator (ContextualSelectionViews.source locals captures) (.inl 7)

def sharedValue : Term (signature base captures) [(), ()] () := generator captures 7
def privateRow : ContextualStoredRows.Row locals captures [(), ()] () := .schema privateBody
def sharedRow : ContextualStoredRows.Row locals captures [(), ()] () := .shared sharedValue

def occupied : Finset Nat := {0, 1}
def selection : Selection Nat := ⟨[], [9, 9], []⟩
def first : Fin selection.read.length := ⟨0, by decide⟩
def second : Fin selection.read.length := ⟨1, by decide⟩

def useScope (port : Fin selection.read.length) : Nat :=
  ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection port)

theorem same_physical_occurrence : selection.read.get first = selection.read.get second := rfl

theorem distinct_use_scopes : useScope first ≠ useScope second := by
  apply ContextualActivationScopes.different_ports_have_different_scopes
  intro equal
  have same := ContextualActivationScopes.readPort_injective selection equal
  have impossible := congrArg Fin.val same
  exact Nat.zero_ne_one impossible

theorem scopes_are_fresh (port : Fin selection.read.length) : useScope port ∉ occupied :=
  ContextualActivationScopes.at_fresh occupied _

def opened (row : ContextualStoredRows.Row locals captures [(), ()] ()) (port : Fin selection.read.length) :=
  (ContextualABTPreparation.readAt locals captures occupied selection (fun _ => row) port).map
    (SchemaPreparation.encodePhysical locals captures code)

theorem private_views_distinct : opened privateRow first ≠ opened privateRow second := by
  change SchemaPreparation.openRow? locals captures code (useScope first) (.schema privateBody) ≠
    SchemaPreparation.openRow? locals captures code (useScope second) (.schema privateBody)
  apply SchemaPreparation.private_local_separates_encoded_uses locals captures code distinct_use_scopes
    privateBody privateBody 7
  have exactSupport := ContextualFamily.support_generator (S := base)
    (source := ContextualSelectionViews.source locals captures) (Sum.inl 7)
  rw [show ContextualFamily.support (S := base)
    (source := ContextualSelectionViews.source locals captures) privateBody = [Sum.inl 7] from exactSupport]
  exact List.mem_singleton_self _

theorem shared_views_agree : opened sharedRow first = opened sharedRow second :=
  SchemaPreparation.shared_value_unchanged locals captures code _ _ sharedValue

def rule : RuleInstance (Term (signature base (ContextualSelectionViews.source locals captures)) [(), ()] ()) :=
  ⟨[], [privateBody, privateBody], [], [], []⟩

theorem selected_schema_has_source_readback (port : Fin selection.read.length) :
    ∃ physical, opened privateRow port = some physical ∧
      Intrinsic.readSource? code [(), ()] () (Source.termInput physical) =
        some ((ContextualActivatedStep.prepared locals captures occupied selection rule (fun _ => privateRow)).read port) := by
  have computed := SchemaPreparation.openRow_exact locals captures code (useScope port) privateRow
  refine ⟨_, computed, ?_⟩
  exact SchemaPreparation.selected_read_source locals captures code occupied selection rule
    (fun _ => privateRow) port computed

theorem shared_value_does_not_identify_its_opening :
    ¬ ∃ recover : Option Payloads.Term → Nat,
      ∀ scope, recover (SchemaPreparation.openRow? locals captures code scope sharedRow) = scope :=
  SchemaPreparation.value_cannot_recover_scope locals captures code sharedValue

theorem quotation_is_not_implicitly_opened (handle : Nat) :
    Intrinsic.read? code [(), ()] () (.node (.quotedRule handle) .nil) = none := rfl

#print axioms head_roundtrip
#print axioms private_views_distinct
#print axioms shared_views_agree
#print axioms selected_schema_has_source_readback
#print axioms shared_value_does_not_identify_its_opening

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.SchemaControls
