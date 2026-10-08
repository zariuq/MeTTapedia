import Mettapedia.Logic.LP.DirectionalMatching
import Mettapedia.Logic.LP.StructuralTestRenaming

/-!
# Lossless scope transport for directional matching

One coordinate map is applied to the entire constraint batch. It cannot
freshen two occurrences of an intentional alias independently. Theorems use
the existing first-order representation, not an encoding of higher-order
binders. A native frame/graph transport must establish the stated left inverse.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.DirectionalMatching

open UnificationRenaming

universe u v
variable {σ : LPSignature.{u, u, v, u}} [DecidableEq σ.vars]

theorem mem_subjectVars_renamed (f : σ.vars → σ.vars)
    (pairs : List (Term σ × Term σ)) (name : σ.vars) :
    name ∈ subjectVars (equations f pairs) ↔
      ∃ original ∈ subjectVars pairs, name = f original := by
  constructor
  · intro member
    obtain ⟨pair, present, inVars⟩ := (mem_subjectVars _ name).mp member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp present
    obtain ⟨old, inTerm, equal⟩ := StructuralTestRenaming.mem_freeVars_rename.mp inVars
    exact ⟨old, (mem_subjectVars _ old).mpr ⟨original, included, inTerm⟩, equal⟩
  · rintro ⟨original, present, rfl⟩
    obtain ⟨pair, included, inVars⟩ := (mem_subjectVars _ original).mp present
    exact (mem_subjectVars _ _).mpr
      ⟨(rename f pair.1, rename f pair.2), List.mem_map.mpr ⟨pair, included, rfl⟩,
        StructuralTestRenaming.mem_freeVars_rename.mpr ⟨original, inVars, rfl⟩⟩

theorem push_fixes_subjects (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (pairs : List (Term σ × Term σ))
    (answer : Subst σ)
    (fixed : RigidUnification.Fixes (fun name => name ∈ subjectVars pairs) answer) :
    RigidUnification.Fixes (fun name => name ∈ subjectVars (equations f pairs))
      (push f g answer) := by
  intro name member
  obtain ⟨original, present, rfl⟩ := (mem_subjectVars_renamed f pairs name).mp member
  simp only [push, inverse original, fixed original present, rename_var]

theorem pull_fixes_subjects (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (pairs : List (Term σ × Term σ))
    (answer : Subst σ)
    (fixed : RigidUnification.Fixes
      (fun name => name ∈ subjectVars (equations f pairs)) answer) :
    RigidUnification.Fixes (fun name => name ∈ subjectVars pairs) (pull f g answer) := by
  intro name member
  have present : f name ∈ subjectVars (equations f pairs) :=
    (mem_subjectVars_renamed f pairs (f name)).mpr ⟨name, member, rfl⟩
  simp only [pull, fixed (f name) present, rename_var, inverse name]

omit [DecidableEq σ.vars] in
theorem push_matches (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (pairs : List (Term σ × Term σ))
    (answer : Subst σ) (matched : Matches answer pairs) :
    Matches (push f g answer) (equations f pairs) := by
  intro pair member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rw [push_apply f g inverse, matched original present]

omit [DecidableEq σ.vars] in
theorem pull_matches (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (pairs : List (Term σ × Term σ))
    (answer : Subst σ) (matched : Matches answer (equations f pairs)) :
    Matches (pull f g answer) pairs := by
  intro pair member
  rw [pull_apply, matched (rename f pair.1, rename f pair.2)
    (List.mem_map.mpr ⟨pair, member, rfl⟩), rename_leftInverse f g inverse]

theorem permitted_matching_rename_iff (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (pairs : List (Term σ × Term σ)) :
    (∃ answer, RigidUnification.Fixes
      (fun name => name ∈ subjectVars (equations f pairs)) answer ∧
        Matches answer (equations f pairs)) ↔
    ∃ answer, RigidUnification.Fixes (fun name => name ∈ subjectVars pairs) answer ∧
      Matches answer pairs := by
  constructor
  · rintro ⟨answer, fixed, matched⟩
    exact ⟨pull f g answer, pull_fixes_subjects f g inverse pairs answer fixed,
      pull_matches f g inverse pairs answer matched⟩
  · rintro ⟨answer, fixed, matched⟩
    exact ⟨push f g answer, push_fixes_subjects f g inverse pairs answer fixed,
      push_matches f g inverse pairs answer matched⟩

theorem matchMany_rename_rejection [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (pairs : List (Term σ × Term σ)) :
    matchMany (equations f pairs) = none ↔ matchMany pairs = none := by
  rw [matchMany_none_iff, matchMany_none_iff,
    permitted_matching_rename_iff f g inverse]

/-- Two independently chosen representatives give the same image on every
observed pattern variable after transporting the scope back. -/
theorem matchMany_rename_images [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (f g : σ.vars → σ.vars)
    (inverse : Function.LeftInverse g f) (pairs : List (Term σ × Term σ))
    (before after : Subst σ)
    (first : matchMany pairs = some before)
    (second : matchMany (equations f pairs) = some after)
    (pair : Term σ × Term σ) (member : pair ∈ pairs) :
    ∀ name ∈ pair.1.freeVars, before name = (pull f g after) name := by
  exact matching_images_unique (matchMany_sound pairs before first).2
    (pull_matches f g inverse pairs after (matchMany_sound _ _ second).2) member

end Mettapedia.Logic.LP.DirectionalMatching

#print axioms Mettapedia.Logic.LP.DirectionalMatching.matchMany_rename_rejection
#print axioms Mettapedia.Logic.LP.DirectionalMatching.matchMany_rename_images
