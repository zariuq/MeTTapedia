import Mettapedia.OSLF.Syntax.FiniteRuleSearch
import Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWire

/-!
# Serialized proof production and exact independent replay

The producer selects rules and constructs their evidence. The separate decoder
accepts only a complete tree with the specified ordered premise judgments.
A serialized success replays to the exact produced tree, not merely another
proof with the same conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleSearch.Labelled

open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire

universe u v w
variable {Label : Type w}
variable {J : Type u} (F : FinitePresentation.{0,u,v} Unit (fun _ => J))
variable (candidates : (j : J) → Candidates F j) (codec : ShapeCodec F Label)

def produceWire (fuel : Nat) (j : J) : Option (Wire Label) :=
  match search F candidates fuel j with
  | .established tree => some (encode F codec tree)
  | _ => none

variable [DecidableEq J]

/-- The same proof history returned by search is recovered by independent
wire checking, including all rule identities and ordered premise children. -/
theorem produceWire_replays (fuel : Nat) (j : J) (wire : Wire Label)
    (produced : produceWire F candidates codec fuel j = some wire) :
    ∃ tree : F.Derivation () j,
      search F candidates fuel j = .established tree ∧
      decodeAt F codec j wire = some tree := by
  cases result : search F candidates fuel j with
  | established tree =>
      simp only [produceWire, result, Option.some.injEq] at produced
      subst wire
      exact ⟨tree, rfl, decodeAt_encode F codec tree⟩
  | refuted impossible => simp only [produceWire, result] at produced; cases produced
  | incomplete => simp only [produceWire, result] at produced; cases produced

theorem produceWire_checked (fuel : Nat) (j : J) (wire : Wire Label)
    (produced : produceWire F candidates codec fuel j = some wire) :
    check F codec j wire = true := by
  rcases produceWire_replays F candidates codec fuel j wire produced with ⟨tree, _, replay⟩
  simp only [check, replay, Option.isSome_some]

/-- A failed replay cannot be a serialized success of this producer at any
budget. Rejection of a wire does not reject its proposed typing judgment. -/
theorem rejected_not_produced (j : J) (wire : Wire Label)
    (rejected : check F codec j wire = false) (fuel : Nat) :
    produceWire F candidates codec fuel j ≠ some wire := by
  intro produced
  have accepted := produceWire_checked F candidates codec fuel j wire produced
  rw [rejected] at accepted
  cases accepted

#print axioms produceWire_replays

end Mettapedia.OSLF.Binding.FiniteRuleSearch.Labelled
