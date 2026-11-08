import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEShownSlotReturn

/-!
# Register origins emitted by ordinary equation patterns

The pattern walk allocates one fresh contiguous register block at each
expression, then walks its fields from left to right. A first variable
occurrence binds its local slot; repeated occurrences compare against it.
This is the ordinary atom/constructor branch of native match-op emission.
Dialect-specific pattern views and logical-list carriers retain their own
admission and representation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotOrigins

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval
open Mettapedia.Machines

inductive Op where
  | atom (source : Nat) (literal : Atom)
  | expr (source first length : Nat)
  | bind (source slot : Nat)
  | same (source slot : Nat)
  deriving DecidableEq, Repr

structure Emitted where
  code : List Op
  next : Nat
  seen : List Nat
  deriving DecidableEq, Repr

mutual
/-- The native variable/atom/expression emission cases, with the current
fresh-register frontier and previously bound slots threaded explicitly. -/
def emit (slots : String → Option Nat) (pattern : Atom) (source next : Nat) (seen : List Nat) : Option Emitted :=
  match pattern with
  | .var name => (slots name).map fun slot =>
      if slot ∈ seen then ⟨[.same source slot], next, seen⟩
      else ⟨[.bind source slot], next, slot :: seen⟩
  | .expression fields =>
      (emitFields slots fields next (next + fields.length) seen).map fun rest =>
        ⟨.expr source next fields.length :: rest.code, rest.next, rest.seen⟩
  | literal => some ⟨[.atom source literal], next, seen⟩
termination_by sizeOf pattern

def emitFields (slots : String → Option Nat) (fields : List Atom) (source next : Nat)
    (seen : List Nat) : Option Emitted :=
  match fields with
  | [] => some ⟨[], next, seen⟩
  | field :: fields =>
      (emit slots field source next seen).bind fun first =>
        (emitFields slots fields (source + 1) first.next first.seen).map fun rest =>
          ⟨first.code ++ rest.code, rest.next, rest.seen⟩
termination_by sizeOf fields
end

/-- Root registers are precisely the authored argument positions. -/
def compile (slots : String → Option Nat) (patterns : List Atom) : Option Emitted :=
  emitFields slots patterns 0 patterns.length []

/-- Every EXPR allocates at the current frontier, never over an existing
argument or field register. Other operations read already allocated slots. -/
inductive Allocated : Nat → List Op → Nat → Prop where
  | nil (next : Nat) : Allocated next [] next
  | atom {next source literal rest final} : source < next → Allocated next rest final →
      Allocated next (.atom source literal :: rest) final
  | bind {next source slot rest final} : source < next → Allocated next rest final →
      Allocated next (.bind source slot :: rest) final
  | same {next source slot rest final} : source < next → Allocated next rest final →
      Allocated next (.same source slot :: rest) final
  | expr {next source length rest final} : source < next → Allocated (next + length) rest final →
      Allocated next (.expr source next length :: rest) final

theorem Allocated.monotone {start final : Nat} {code : List Op} (allocated : Allocated start code final) :
    start ≤ final := by
  induction allocated with
  | nil => exact Nat.le_refl _
  | atom _ _ ih | bind _ _ ih | same _ _ ih => exact ih
  | expr _ _ ih => omega

theorem Allocated.append {start middle final : Nat} {first rest : List Op}
    (left : Allocated start first middle) (right : Allocated middle rest final) :
    Allocated start (first ++ rest) final := by
  induction left with
  | nil => exact right
  | atom source _ ih => exact .atom source (ih right)
  | bind source _ ih => exact .bind source (ih right)
  | same source _ ih => exact .same source (ih right)
  | expr source _ ih => exact .expr source (ih right)

mutual
theorem emitted_allocated (slots : String → Option Nat) (pattern : Atom)
    (source next : Nat) (seen : List Nat) (output : Emitted)
    (valid : source < next) (emitted : emit slots pattern source next seen = some output) :
    Allocated next output.code output.next := by
  cases pattern with
  | symbol name =>
      simp only [emit, Option.some.injEq] at emitted
      cases emitted
      exact .atom valid (.nil _)
  | grounded value =>
      simp only [emit, Option.some.injEq] at emitted
      cases emitted
      exact .atom valid (.nil _)
  | var name =>
      simp only [emit, Option.map_eq_some_iff] at emitted
      obtain ⟨slot, _, emitted⟩ := emitted
      split at emitted
      · cases emitted; exact .same valid (.nil _)
      · cases emitted; exact .bind valid (.nil _)
  | expression fields =>
      simp only [emit, Option.map_eq_some_iff] at emitted
      obtain ⟨rest, generated, rfl⟩ := emitted
      exact .expr valid (fields_allocated slots fields next (next + fields.length) seen rest (by omega) generated)
termination_by sizeOf pattern

theorem fields_allocated (slots : String → Option Nat) (fields : List Atom)
    (source next : Nat) (seen : List Nat) (output : Emitted)
    (valid : source + fields.length ≤ next)
    (emitted : emitFields slots fields source next seen = some output) :
    Allocated next output.code output.next := by
  cases fields with
  | nil =>
      simp only [emitFields, Option.some.injEq] at emitted
      cases emitted
      exact .nil _
  | cons field fields =>
      simp only [emitFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at emitted
      obtain ⟨first, firstRun, rest, restRun, rfl⟩ := emitted
      have firstAllocated := emitted_allocated slots field source next seen first
        (by simp only [List.length_cons] at valid; omega) firstRun
      have restAllocated := fields_allocated slots fields (source + 1) first.next first.seen rest
        (by have := firstAllocated.monotone; simp only [List.length_cons] at valid; omega) restRun
      exact firstAllocated.append restAllocated
termination_by sizeOf fields
end

theorem compiled_allocated (slots : String → Option Nat) (patterns : List Atom) (output : Emitted)
    (emitted : compile slots patterns = some output) : Allocated patterns.length output.code output.next :=
  fields_allocated slots patterns 0 patterns.length [] output (by omega) emitted

def boundSlots : List Op → List Nat := List.filterMap fun
  | .bind _ slot => some slot
  | _ => none

/-- Facts about the compiler's actual seen-slot state. -/
structure BindingFacts (before : List Nat) (code : List Op) (after : List Nat) : Prop where
  fresh : ∀ slot ∈ boundSlots code, slot ∉ before
  unique : (boundSlots code).Nodup
  kept : before ⊆ after
  written : boundSlots code ⊆ after

theorem BindingFacts.nil (seen : List Nat) : BindingFacts seen [] seen := by
  refine ⟨?_, by simp [boundSlots], fun _ member => member, ?_⟩ <;> simp [boundSlots]

theorem BindingFacts.append {before middle after : List Nat} {first rest : List Op}
    (left : BindingFacts before first middle) (right : BindingFacts middle rest after) :
    BindingFacts before (first ++ rest) after := by
  have split : boundSlots (first ++ rest) = boundSlots first ++ boundSlots rest := by
    simp [boundSlots]
  refine ⟨?_, ?_, fun _ member => right.kept (left.kept member), ?_⟩
  · rw [split]
    intro slot member
    rcases List.mem_append.mp member with first | later
    · exact left.fresh slot first
    · exact fun present => right.fresh slot later (left.kept present)
  · rw [split]
    apply List.nodup_append.mpr
    refine ⟨left.unique, right.unique, ?_⟩
    intro slot first other later same
    subst other
    exact right.fresh slot later (left.written first)
  · rw [split]
    intro slot member
    rcases List.mem_append.mp member with first | later
    · exact right.kept (left.written first)
    · exact right.written later

mutual
theorem emitted_binding_facts (slots : String → Option Nat) (pattern : Atom)
    (source next : Nat) (seen : List Nat) (output : Emitted)
    (emitted : emit slots pattern source next seen = some output) :
    BindingFacts seen output.code output.seen := by
  cases pattern with
  | symbol name =>
      simp only [emit, Option.some.injEq] at emitted
      cases emitted
      exact ⟨by simp [boundSlots], by simp [boundSlots], fun _ member => member, by simp [boundSlots]⟩
  | grounded value =>
      simp only [emit, Option.some.injEq] at emitted
      cases emitted
      exact ⟨by simp [boundSlots], by simp [boundSlots], fun _ member => member, by simp [boundSlots]⟩
  | var name =>
      simp only [emit, Option.map_eq_some_iff] at emitted
      obtain ⟨slot, _, emitted⟩ := emitted
      split at emitted
      next present =>
        cases emitted
        exact ⟨by simp [boundSlots], by simp [boundSlots], fun _ member => member, by simp [boundSlots]⟩
      next fresh =>
        cases emitted
        exact ⟨by simpa [boundSlots] using fresh, by simp [boundSlots],
          fun _ member => List.mem_cons_of_mem _ member, by simp [boundSlots]⟩
  | expression fields =>
      simp only [emit, Option.map_eq_some_iff] at emitted
      obtain ⟨rest, generated, rfl⟩ := emitted
      have facts := fields_binding_facts slots fields next (next + fields.length) seen rest generated
      exact ⟨facts.fresh, facts.unique, facts.kept, facts.written⟩
termination_by sizeOf pattern

theorem fields_binding_facts (slots : String → Option Nat) (fields : List Atom)
    (source next : Nat) (seen : List Nat) (output : Emitted)
    (emitted : emitFields slots fields source next seen = some output) :
    BindingFacts seen output.code output.seen := by
  cases fields with
  | nil =>
      simp only [emitFields, Option.some.injEq] at emitted
      cases emitted
      exact BindingFacts.nil seen
  | cons field fields =>
      simp only [emitFields, Option.bind_eq_some_iff, Option.map_eq_some_iff] at emitted
      obtain ⟨first, firstRun, rest, restRun, rfl⟩ := emitted
      exact (emitted_binding_facts slots field source next seen first firstRun).append
        (fields_binding_facts slots fields (source + 1) first.next first.seen rest restRun)
termination_by sizeOf fields
end

theorem compiled_bindings_unique (slots : String → Option Nat) (patterns : List Atom) (output : Emitted)
    (emitted : compile slots patterns = some output) : (boundSlots output.code).Nodup :=
  (fields_binding_facts slots patterns 0 patterns.length [] output emitted).unique

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotOrigins
