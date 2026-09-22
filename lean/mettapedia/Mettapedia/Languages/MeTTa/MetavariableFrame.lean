import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Metavariables as slots in a finite frame

A unification variable is a slot in the finite context that created it:
an equation's authored inventory, or the inventory of a goal the machine
manufactured.  Lookup is an index.  Object-level binders remain the ABT
(`idx k`); this module is only the substitution's domain.

The named substitution of `SubstitutionAlgebra` is recovered by spelling
each slot, provided the inventory names are unique.  Epoch-stamped dense
slots for compiled equation heads already exist in
`CompiledPlanEpochSlotCompilation`; this object is the same carrier for
every manufactured term, so both sides of a unification index.

References: explicit substitutions (Abadi, Cardelli, Curien, Lévy);
contextual metavariables (Nanevski, Pfenning, Pientka); Vampire banks
generalised to one bank per goal.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MetavariableFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-- Finite variable inventory of one activation or manufactured goal. -/
abbrev Frame := List Var

/-- A metavariable is a slot of its frame, not a global name. -/
abbrev Slot (φ : Frame) := Fin φ.length

/-- Environment for one frame: a value per slot. -/
abbrev FrameEnv (φ : Frame) := Slot φ → Option Atom

/-- Index lookup. -/
def lookup {φ : Frame} (env : FrameEnv φ) (slot : Slot φ) : Option Atom :=
  env slot

/-- Spell a slot as the named variable `SubstitutionAlgebra` uses. -/
def nameOf {φ : Frame} (slot : Slot φ) : Var :=
  φ.get slot

/-- First index of a name in a frame, if any. -/
def indexOf : Frame → Var → Option Nat
  | [], _ => none
  | w :: rest, v =>
      if w = v then some 0
      else (indexOf rest v).map (· + 1)

theorem indexOf_lt {φ : Frame} {v : Var} {i : Nat}
    (h : indexOf φ v = some i) : i < φ.length := by
  induction φ generalizing i with
  | nil => simp [indexOf] at h
  | cons w rest ih =>
      simp only [indexOf] at h
      split at h
      · next _ =>
          simp at h
          subst i
          exact Nat.succ_pos _
      · next _ =>
          cases hmap : indexOf rest v with
          | none => simp [hmap] at h
          | some j =>
              simp [hmap] at h
              subst i
              exact Nat.succ_lt_succ (ih hmap)

/-- Named substitution denoted by a frame environment.  Names outside the
inventory are unbound. -/
def denote {φ : Frame} (env : FrameEnv φ) : Subst :=
  fun v =>
    match h : indexOf φ v with
    | some i => env ⟨i, indexOf_lt h⟩
    | none => none

@[simp] theorem lookup_eq {φ : Frame} (env : FrameEnv φ) (slot : Slot φ) :
    lookup env slot = env slot := rfl

theorem indexOf_get {φ : Frame} (unique : φ.Nodup) (slot : Slot φ) :
    indexOf φ (nameOf slot) = some slot.val := by
  induction φ with
  | nil => exact slot.elim0
  | cons w rest ih =>
      have unique_rest : rest.Nodup := (List.nodup_cons.mp unique).2
      have w_fresh : w ∉ rest := (List.nodup_cons.mp unique).1
      match slot with
      | ⟨0, _⟩ =>
          simp [indexOf, nameOf, List.get]
      | ⟨n + 1, hn⟩ =>
          have hn' : n < rest.length := Nat.succ_lt_succ_iff.mp hn
          have w_ne : w ≠ rest.get ⟨n, hn'⟩ := by
            intro h
            exact w_fresh (h ▸ List.get_mem rest ⟨n, hn'⟩)
          have name_tail :
              nameOf (φ := w :: rest) ⟨n + 1, hn⟩ =
                rest.get ⟨n, hn'⟩ := by
            simp [nameOf, List.get]
          simp only [indexOf, name_tail]
          rw [if_neg w_ne]
          change Option.map (fun x => x + 1)
              (indexOf rest (nameOf (φ := rest) ⟨n, hn'⟩)) =
            some (n + 1)
          rw [ih unique_rest ⟨n, hn'⟩]
          rfl

/-- A slot's name, looked up through the denoted substitution, is the
slot's value.  This is the index-not-name law. -/
theorem denote_nameOf {φ : Frame} (unique : φ.Nodup)
    (env : FrameEnv φ) (slot : Slot φ) :
    denote env (nameOf slot) = lookup env slot := by
  unfold denote lookup
  split
  · next i hi =>
      have same := indexOf_get unique slot
      simp [same] at hi
      subst i
      rfl
  · next hnone =>
      have same := indexOf_get unique slot
      simp [same] at hnone

end Mettapedia.Languages.MeTTa.MetavariableFrame
