import Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming

/-!
# Combining independently renamed terms with disjoint supports

Per-term variants need not preserve sharing across a list. They do preserve
the whole list when both lists have disjoint variable supports between terms.
The global maps are constructed by joining the actual component maps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def Apart (first second : Atom) : Prop :=
  ∀ name ∈ atomFreeVars first, name ∉ atomFreeVars second

def onSupport (support : List String) (inside outside : String → String) : String → String :=
  fun name => if name ∈ support then inside name else outside name

theorem rename_on_support (term : Atom) (inside outside : String → String) :
    rename (onSupport (atomFreeVars term) inside outside) term = rename inside term := by
  apply (equal_iff_on_variables _ _ term).mpr
  intro name present
  simp only [onSupport,if_pos present]

theorem rename_outside_support (first second : Atom) (inside outside : String → String)
    (apart : Apart first second) :
    rename (onSupport (atomFreeVars first) inside outside) second = rename outside second := by
  apply (equal_iff_on_variables _ _ second).mpr
  intro name present
  have missing : name ∉ atomFreeVars first := fun inside => apart name inside present
  simp only [onSupport,if_neg missing]

theorem Variant.cons {first second : Atom} {left right : List Atom}
    (head : Variant first second) (tail : Variant (.expression left) (.expression right))
    (leftApart : Apart first (.expression left)) (rightApart : Apart second (.expression right)) :
    Variant (.expression (first :: left)) (.expression (second :: right)) := by
  obtain ⟨forwardHead,backwardHead,headForward,headBackward⟩ := head
  obtain ⟨forwardTail,backwardTail,tailForward,tailBackward⟩ := tail
  refine ⟨onSupport (atomFreeVars first) forwardHead forwardTail,
    onSupport (atomFreeVars second) backwardHead backwardTail,?_,?_⟩
  · have top := (rename_on_support first forwardHead forwardTail).trans headForward
    have bottom := (rename_outside_support first (.expression left) forwardHead forwardTail leftApart).trans tailForward
    exact congrArg Atom.expression (congrArg₂ List.cons top (Atom.expression.inj bottom))
  · have top := (rename_on_support second backwardHead backwardTail).trans headBackward
    have bottom := (rename_outside_support second (.expression right) backwardHead backwardTail rightApart).trans tailBackward
    exact congrArg Atom.expression (congrArg₂ List.cons top (Atom.expression.inj bottom))

theorem apart_expression_iff (first : Atom) (rest : List Atom) :
    Apart first (.expression rest) ↔ ∀ second ∈ rest, Apart first second := by
  simp only [Apart,variables_expression,not_exists,not_and]
  aesop

/-- Separate occurrence copies make per-branch maps compatible. Neither
pointwise variants nor the absence of sharing on only one side is enough. -/
theorem joint_variant_of_separated {first second : List Atom}
    (corresponding : List.Forall₂ Variant first second)
    (leftSeparated : first.Pairwise Apart) (rightSeparated : second.Pairwise Apart) :
    Variant (.expression first) (.expression second) := by
  induction corresponding with
  | nil => exact Variant.refl _
  | @cons first second left right head tail ih =>
      obtain ⟨leftTop,leftTail⟩ := List.pairwise_cons.mp leftSeparated
      obtain ⟨rightTop,rightTail⟩ := List.pairwise_cons.mp rightSeparated
      exact head.cons (ih leftTail rightTail)
        ((apart_expression_iff first left).mpr leftTop)
        ((apart_expression_iff second right).mpr rightTop)

theorem variants_symm {first second : List Atom} (same : List.Forall₂ Variant first second) :
    List.Forall₂ Variant second first := by
  induction same with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.symm ih

theorem variants_trans {first second third : List Atom}
    (left : List.Forall₂ Variant first second) (right : List.Forall₂ Variant second third) :
    List.Forall₂ Variant first third := by
  induction left generalizing third with
  | nil => cases right; exact .nil
  | cons head tail ih =>
      cases right with
      | cons following rest => exact .cons (head.trans following) (ih rest)

end Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming
