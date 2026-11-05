import Mathlib.Tactic

/-!
# A space file's general terms: nested fields and a fact's variables

A file fact may hold nested terms and variables.  A variable's name means
nothing outside its fact; what the fact says is which of its places hold
the same variable.  The file therefore writes each variable as a slot
number, numbered by first occurrence in the fact, and reading the fact back
makes one fresh variable per slot.

This file proves, over terms of symbols, variables and applications:
* `decode_encode`: reading an encoded fact back gives the fact with its
  variables renamed by `rename`, an injective renaming; so the fact is
  recovered up to the renaming of its variables;
* `shared_reads_back_shared`: two places of a fact hold the same variable
  exactly when the read-back fact's places do;
* `encode_alpha_invariant`: two facts that differ only by an injective
  renaming of their variables are written as the same record, so a file
  holds a fact once whatever its variables were called.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SpaceFileTerms

/-- Terms: symbols, variables (by name), and binary applications (an
expression's argument list is a chain of them). -/
inductive Tm
  | sym (s : Nat)
  | var (x : Nat)
  | app (f : Tm) (a : Tm)
  deriving DecidableEq

/-- The variables of a term in order of first occurrence, each once. -/
def varsOf : Tm → List Nat
  | .sym _ => []
  | .var x => [x]
  | .app f a => (varsOf f ++ varsOf a).dedup

/-- Renaming the variables of a term. -/
def rename (r : Nat → Nat) : Tm → Tm
  | .sym s => .sym s
  | .var x => .var (r x)
  | .app f a => .app (rename r f) (rename r a)

/-- A slot table: the variables in slot order. -/
abbrev Slots := List Nat

/-- Writing a term against a slot table: each variable becomes its slot. -/
def encodeWith (slots : Slots) : Tm → Tm
  | .sym s => .sym s
  | .var x => .var (slots.idxOf x)
  | .app f a => .app (encodeWith slots f) (encodeWith slots a)

/-- A fact's record: its term with each variable replaced by its slot,
slots numbered by first occurrence. -/
def encode (t : Tm) : Tm := encodeWith (varsOf t) t

/-- The renaming encoding performs on a term's variables. -/
def slotOf (t : Tm) (x : Nat) : Nat := (varsOf t).idxOf x

theorem encodeWith_eq_rename (slots : Slots) (t : Tm) :
    encodeWith slots t = rename (fun x => slots.idxOf x) t := by
  induction t with
  | sym s => rfl
  | var x => rfl
  | app f a ihf iha => simp [encodeWith, rename, ihf, iha]

/-- Reading back: the record is the fact under the slot renaming. -/
theorem decode_encode (t : Tm) : encode t = rename (slotOf t) t := by
  unfold encode slotOf
  exact encodeWith_eq_rename _ t

/-- The slot renaming is injective on the term's variables, so two places
hold the same variable exactly when they hold the same slot. -/
theorem shared_reads_back_shared (t : Tm) (x y : Nat) (hx : x ∈ varsOf t) :
    slotOf t x = slotOf t y ↔ x = y := by
  unfold slotOf
  exact List.idxOf_inj hx

theorem rename_rename (f g : Nat → Nat) (t : Tm) :
    rename f (rename g t) = rename (f ∘ g) t := by
  induction t with
  | sym s => rfl
  | var x => rfl
  | app a b iha ihb => simp [rename, iha, ihb]

theorem rename_congr (f g : Nat → Nat) (t : Tm) (h : ∀ x ∈ varsOf t, f x = g x) :
    rename f t = rename g t := by
  induction t with
  | sym s => rfl
  | var x => simp [rename, h x (by simp [varsOf])]
  | app a b iha ihb =>
      simp only [rename]
      rw [iha (fun x hx => h x (by simp [varsOf, List.mem_dedup, hx])),
          ihb (fun x hx => h x (by simp [varsOf, List.mem_dedup, hx]))]

theorem varsOf_rename (r : Nat → Nat) (hr : Function.Injective r) (t : Tm) :
    varsOf (rename r t) = (varsOf t).map r := by
  induction t with
  | sym s => rfl
  | var x => rfl
  | app a b iha ihb =>
      simp only [varsOf, rename, iha, ihb, ← List.map_append]
      exact List.dedup_map_of_injective hr _

theorem idxOf_map_injective (r : Nat → Nat) (hr : Function.Injective r)
    (l : List Nat) (x : Nat) : (l.map r).idxOf (r x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : y = x
      · subst h; simp [List.idxOf_cons_self]
      · have : r y ≠ r x := fun e => h (hr e)
        simp [List.idxOf_cons_ne _ h, List.idxOf_cons_ne _ this, ih]

/-- Facts that differ by an injective renaming of their variables are
written as the same record. -/
theorem encode_alpha_invariant (r : Nat → Nat) (hr : Function.Injective r) (t : Tm) :
    encode (rename r t) = encode t := by
  rw [decode_encode, decode_encode, rename_rename]
  apply rename_congr
  intro x _
  simp only [Function.comp, slotOf, varsOf_rename r hr t, idxOf_map_injective r hr]

end Mettapedia.Machines.SpaceFileTerms
