import Mettapedia.Machines.StoredIdUnification

/-!
# Free-frame shortcuts and reversible frame counters

An active binding trail determines which frames have any bound cell. Zero
count for a frame implies its variables remain unchanged by the composed
substitution. A term from that frame cannot contain a target variable from
another frame, so its occurs test can be skipped. Both conditions matter.

The counter cache is maintained across append and rollback; a counter that
does not represent the active trail does not justify the shortcut. This is a
logical binding-trail model, not a native frame allocator or overflow proof.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoredIdFrameConditions

open ShapeStore ShapeScopedUnification StoredIdViews StoredIdUnification
open Mettapedia.Logic.LP

variable {α Var Id : Type} [DecidableEq Var]

def frameCount (frame : Nat) (bindings : List (Binding Var Id)) : Nat :=
  (bindings.filter (fun b => b.1.scope == frame)).length

omit [DecidableEq Var] in
theorem frameCount_zero (frame : Nat) (bindings : List (Binding Var Id)) :
    frameCount frame bindings = 0 ↔ ∀ b ∈ bindings, b.1.scope ≠ frame := by
  simp [frameCount, List.filter_eq_nil_iff]

omit [DecidableEq Var] in
theorem frameCount_append (frame : Nat) (first second : List (Binding Var Id)) :
    frameCount frame (first ++ second) = frameCount frame first + frameCount frame second := by
  simp [frameCount]

theorem free_frame_fixed (reader : Reader α Var Id) (frame : Nat)
    (bindings : List (Binding Var Id)) (free : frameCount frame bindings = 0) (v : Var) :
    bindingsMeaning reader bindings (ScopedVar.at frame v) = .var (ScopedVar.at frame v) := by
  have absent := (frameCount_zero frame bindings).mp free
  induction bindings with
  | nil => rfl
  | cons b rest ih =>
      have different : ScopedVar.at frame v ≠ b.1 := by
        intro same
        have scopes := congrArg ScopedVar.scope same
        exact absent b (by simp) scopes.symm
      have tailFree : frameCount frame rest = 0 :=
        (frameCount_zero frame rest).mpr (fun x hx => absent x (List.mem_cons_of_mem _ hx))
      have tailAbsent : ∀ b ∈ rest, b.1.scope ≠ frame :=
        fun x hx => absent x (List.mem_cons_of_mem _ hx)
      simp only [bindingsMeaning, Subst.comp, Subst.single, if_neg different, Subst.applyTerm_var]
      exact ih tailFree tailAbsent

omit [DecidableEq Var] in
theorem encode_fixed (θ : Mettapedia.Logic.LP.Subst (signature α Var)) (frame : Nat)
    (fixed : ∀ v, θ (ScopedVar.at frame v) = .var (ScopedVar.at frame v))
    (t : OpenTerm α Var) : θ.applyTerm (encode frame t) = encode frame t := by
  induction t with
  | atom a => cases a <;> simp [encode, fixed]
  | node l r ihl ihr => simp [encode, apply_pair, ihl, ihr]

theorem foreign_frame_not_occurs (frame : Nat) (target : ScopedVar Var)
    (different : target.scope ≠ frame) (t : OpenTerm α Var) :
    (encode frame t).occursIn target = false := by
  induction t with
  | atom a =>
      cases a with
      | inl a => rfl
      | inr v =>
          have unequal : target ≠ ScopedVar.at frame v := by
            intro equal
            exact different (congrArg ScopedVar.scope equal)
          simp [encode, Term.occursIn, unequal]
  | node l r ihl ihr => simp [encode, occurs_pair, ihl, ihr]

/-- The omitted walk is justified by both the current binding context and
the distinction between the target's frame and the stored term's frame. -/
theorem skip_occurs_for_free_foreign_frame (reader : Reader α Var Id)
    (bindings : List (Binding Var Id)) (frame : Nat) (target : ScopedVar Var)
    (free : frameCount frame bindings = 0) (different : target.scope ≠ frame)
    (t : OpenTerm α Var) :
    ((bindingsMeaning reader bindings).applyTerm (encode frame t)).occursIn target = false := by
  rw [encode_fixed _ frame (free_frame_fixed reader frame bindings free) t]
  exact foreign_frame_not_occurs frame target different t

@[ext] structure Trail (Var Id : Type) where
  bindings : List (Binding Var Id)
  counts : Nat → Nat

abbrev Trail.Valid (trail : Trail Var Id) : Prop :=
  ∀ frame, trail.counts frame = frameCount frame trail.bindings

def push (trail : Trail Var Id) (binding : Binding Var Id) : Trail Var Id :=
  ⟨trail.bindings ++ [binding],
    Function.update trail.counts binding.1.scope (trail.counts binding.1.scope + 1)⟩

def rollback (mark : Nat) (trail : Trail Var Id) : Trail Var Id :=
  ⟨trail.bindings.take mark,
    fun frame => trail.counts frame - frameCount frame (trail.bindings.drop mark)⟩

omit [DecidableEq Var] in
theorem push_valid (trail : Trail Var Id) (valid : trail.Valid) (binding : Binding Var Id) :
    (push trail binding).Valid := by
  intro frame
  by_cases same : frame = binding.1.scope
  · subst frame
    simp [push, frameCount, valid]
  · simp [push, Function.update_of_ne same, frameCount, valid, Ne.symm same]

omit [DecidableEq Var] in
theorem rollback_valid (trail : Trail Var Id) (valid : trail.Valid) (mark : Nat) :
    (rollback mark trail).Valid := by
  intro frame
  have split := frameCount_append frame (trail.bindings.take mark) (trail.bindings.drop mark)
  rw [List.take_append_drop] at split
  change trail.counts frame - frameCount frame (trail.bindings.drop mark) =
    frameCount frame (trail.bindings.take mark)
  rw [valid, split]
  omega

omit [DecidableEq Var] in
theorem rollback_restores (before after : Trail Var Id) (validBefore : before.Valid)
    (validAfter : after.Valid) (added : List (Binding Var Id))
    (extendsTrail : after.bindings = before.bindings ++ added) :
    rollback before.bindings.length after = before := by
  have equalBindings : (rollback before.bindings.length after).bindings = before.bindings := by
    simp [rollback, extendsTrail]
  have equalCounts : (rollback before.bindings.length after).counts = before.counts := by
    funext frame
    rw [rollback_valid after validAfter, equalBindings, validBefore]
  exact Trail.ext equalBindings equalCounts

namespace Controls

open StoredIdViews.Controls (reader)

def redirect : List (Binding Nat Nat) := [(⟨1, 0⟩, .cell ⟨0, 0⟩)]

theorem distinct_frames_alone_are_insufficient :
    Term.occursIn (σ := signature Bool Nat) ⟨0, 0⟩
      ((bindingsMeaning reader redirect).applyTerm
        (encode 1 (.atom (.inr (0 : Nat))))) = true := by
  decide

theorem no_bindings_alone_is_insufficient :
    Term.occursIn (σ := signature Bool Nat) ⟨1, 0⟩
      (encode 1 (.node (.atom (.inr (0 : Nat))) (.atom (.inl false)))) = true := by decide

def staleCounter : Trail Nat Nat := ⟨redirect, fun _ => 0⟩

theorem stale_zero_counter_is_invalid : ¬ staleCounter.Valid := by
  intro valid
  have wrong := valid 1
  change 0 = 1 at wrong
  omega

end Controls

#print axioms skip_occurs_for_free_foreign_frame
#print axioms push_valid
#print axioms rollback_valid
#print axioms rollback_restores

end Mettapedia.Machines.StoredIdFrameConditions
