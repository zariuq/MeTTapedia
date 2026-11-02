import Mettapedia.Machines.CMemory.Borrowing

/-!
# Executable uniform-origin summaries

An unknown-index shared reference read needs every possible element to name
the same referent footprint, or to be null. This scan retains nullability and
refuses conflicting origins. Its soundness theorem derives the universal
element contract from acceptance of the scan; it does not assume that contract.
Owning, exclusive and opaque-authority fields are excluded by the frontend
before this shared-origin operation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Resources.UniformOrigins

open Mettapedia.Machines.CMemory.Borrowing

structure Input where
  origin : Option Region
  nullable : Bool
  deriving DecidableEq, Repr

structure Summary where
  chosen : Option Region
  nullable : Bool
  deriving DecidableEq, Repr

def Covers (summary : Summary) (input : Input) : Prop :=
  (∀ region, input.origin = some region → summary.chosen = some region) ∧
  (input.origin = none ∨ input.nullable = true → summary.nullable = true)

def Extends (before after : Summary) : Prop :=
  (∀ region, before.chosen = some region → after.chosen = some region) ∧
  (before.nullable = true → after.nullable = true)

def merge (summary : Summary) (input : Input) : Option Summary :=
  match input.origin with
  | none => some { summary with nullable := true }
  | some region =>
    match summary.chosen with
    | none => some ⟨some region, summary.nullable || input.nullable⟩
    | some old => if old = region then
        some { summary with nullable := summary.nullable || input.nullable } else none

def scan (summary : Summary) : List Input → Option Summary
  | [] => some summary
  | input :: rest => (merge summary input).bind fun next => scan next rest

def summarize (inputs : List Input) : Option Summary := scan ⟨none, false⟩ inputs

theorem extends_refl (summary : Summary) : Extends summary summary :=
  ⟨fun _ same => same, fun same => same⟩

theorem extends_trans {a b c : Summary} (ab : Extends a b) (bc : Extends b c) :
    Extends a c := ⟨fun region old => bc.1 region (ab.1 region old), fun old => bc.2 (ab.2 old)⟩

theorem covers_of_extends {a b : Summary} (extension : Extends a b) {input : Input}
    (covered : Covers a input) : Covers b input :=
  ⟨fun region origin => extension.1 region (covered.1 region origin),
    fun nullable => extension.2 (covered.2 nullable)⟩

theorem merge_sound (before after : Summary) (input : Input)
    (accepted : merge before input = some after) : Extends before after ∧ Covers after input := by
  cases before with
  | mk chosen nullable =>
    cases input with
    | mk origin possibleNull =>
      cases origin with
      | none =>
        simp only [merge, Option.some.injEq] at accepted
        subst after
        simp [Extends, Covers]
      | some region =>
        cases chosen with
        | none =>
          simp only [merge, Option.some.injEq] at accepted
          subst after
          simp [Extends, Covers]
          exact ⟨Or.inl, Or.inr⟩
        | some old =>
          by_cases same : old = region
          · simp only [merge, same, ↓reduceIte, Option.some.injEq] at accepted
            subst after
            simp [Extends, Covers, same]
            exact ⟨Or.inl, Or.inr⟩
          · simp [merge, same] at accepted

theorem scan_sound (before after : Summary) (inputs : List Input)
    (accepted : scan before inputs = some after) :
    Extends before after ∧ ∀ input ∈ inputs, Covers after input := by
  induction inputs generalizing before with
  | nil =>
    have same : before = after := Option.some.inj accepted
    subst before
    exact ⟨extends_refl after, by simp⟩
  | cons input rest ih =>
    unfold scan at accepted
    cases merged : merge before input with
    | none => simp [merged] at accepted
    | some next =>
      have tail : scan next rest = some after := by simpa [merged] using accepted
      obtain ⟨advance, covers⟩ := merge_sound before next input merged
      obtain ⟨further, remaining⟩ := ih next tail
      refine ⟨extends_trans advance further, ?_⟩
      intro observed member
      rcases List.mem_cons.mp member with rfl | member
      · exact covers_of_extends further covers
      · exact remaining observed member

theorem admitted_elements_have_common_origin (inputs : List Input) (summary : Summary)
    (accepted : summarize inputs = some summary) :
    ∀ input ∈ inputs, Covers summary input := (scan_sound _ _ _ accepted).2

def x : Region := ⟨3, 0, 8⟩
def y : Region := ⟨4, 0, 8⟩

theorem shared_same_origin_accepted :
    summarize [⟨some x, false⟩, ⟨some x, false⟩] = some ⟨some x, false⟩ := by decide
theorem nullable_origin_retained :
    summarize [⟨some x, false⟩, ⟨none, false⟩] = some ⟨some x, true⟩ := by decide
theorem different_origins_refused : summarize [⟨some x, false⟩, ⟨some y, false⟩] = none := by decide
theorem possible_null_not_forgotten :
    summarize [⟨some x, true⟩, ⟨some x, false⟩] = some ⟨some x, true⟩ := by decide

#print axioms merge_sound
#print axioms scan_sound
#print axioms admitted_elements_have_common_origin

end Mettapedia.Machines.Resources.UniformOrigins
