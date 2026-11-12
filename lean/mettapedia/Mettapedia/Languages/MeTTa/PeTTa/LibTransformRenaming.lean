import Mettapedia.Languages.MeTTa.PeTTa.LibTransformAbsent

/-!
# Fresh variables for each firing

The model starts every firing from no bindings: the variables of a transform's patterns are
the firing's own. The step keeps what its firings told as knowledge, so in one run the rule
instance of each firing must be written with variables that the knowledge before it does
not mention. This module supplies that renaming and its laws.

* `tag n x`: the variable `x` of firing `n`, with a decoder (`untag_tag`). Different
  firings never share a tagged name.
* `rename n`: an atom with every variable tagged `n` (`vars_rename`).
* `withLocal ρ n σ`: the solution `ρ` with the variables tagged `n` solved as `σ` solves
  them. It agrees with `ρ` on every atom whose variables carry smaller tags
  (`subst_withLocal_of_tagsBelow`), and it solves the renamed pattern as `σ` solved the
  pattern (`subst_withLocal_rename`).
* `untagged ρ n`: what the solution `ρ` says about firing `n`'s own variables;
  `subst_untagged_of_rename`: if `ρ` makes a renamed pattern equal to a ground atom, then
  `untagged ρ n` makes the pattern equal to it.

Negative example: `Controls.untagged_name_has_no_tag` (a name that does not start as a
tag does decodes to nothing).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open Mettapedia.Languages.MeTTa (SubstitutionAlgebra.subst SubstitutionAlgebra.vars)

/-! ## Tagged names -/

/-- `n` marks, an end mark, then the name's characters. -/
def tagChars (n : Nat) (xs : List Char) : List Char := List.replicate n 'a' ++ 'b' :: xs

/-- The tag and the name of a tagged list of characters. -/
def untagChars : List Char → Option (Nat × List Char)
  | [] => none
  | c :: cs =>
      if c = 'b' then some (0, cs)
      else if c = 'a' then (untagChars cs).map fun r => (r.1 + 1, r.2)
      else none

theorem untagChars_tagChars (n : Nat) (xs : List Char) :
    untagChars (tagChars n xs) = some (n, xs) := by
  induction n with
  | zero => simp [tagChars, untagChars]
  | succ n ih =>
      have step : tagChars (n + 1) xs = 'a' :: tagChars n xs := by
        simp [tagChars, List.replicate_succ]
      rw [step]
      simp [untagChars, ih]

/-- The variable `x` of firing `n`. -/
def tag (n : Nat) (x : String) : String := String.ofList (tagChars n x.toList)

/-- The firing and the variable of a tagged name. -/
def untag (v : String) : Option (Nat × String) :=
  (untagChars v.toList).map fun r => (r.1, String.ofList r.2)

theorem untag_tag (n : Nat) (x : String) : untag (tag n x) = some (n, x) := by
  simp [untag, tag, untagChars_tagChars]

/-- Tagged names of different firings differ, and so do different names of one firing. -/
theorem tag_injective {n m : Nat} {x y : String} (same : tag n x = tag m y) : n = m ∧ x = y := by
  have decoded := congrArg untag same
  rw [untag_tag, untag_tag] at decoded
  simpa using decoded

/-! ## Renaming an atom -/

/-- The atom with every variable tagged `n`. -/
def rename (n : Nat) : Atom → Atom
  | .var v => .var (tag n v)
  | .symbol s => .symbol s
  | .grounded g => .grounded g
  | .expression es => .expression (renameList n es)
where
  renameList (n : Nat) : List Atom → List Atom
    | [] => []
    | a :: as => rename n a :: renameList n as

/-- The variables of a renamed atom are the atom's variables, tagged. -/
theorem vars_rename (n : Nat) : ∀ a : Atom,
    SubstitutionAlgebra.vars (rename n a) = (SubstitutionAlgebra.vars a).map (tag n)
  | .var _ => rfl
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es => by
      simp only [rename, SubstitutionAlgebra.vars]
      exact list es
where
  list : ∀ es : List Atom,
      SubstitutionAlgebra.vars.varsList (rename.renameList n es) =
        (SubstitutionAlgebra.vars.varsList es).map (tag n)
    | [] => rfl
    | a :: as => by
        simp only [rename.renameList, SubstitutionAlgebra.vars.varsList, vars_rename n a,
          list as, List.map_append]

/-! ## Solutions -/

/-- What a solution says about firing `n`'s own variables. -/
def untagged (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (n : Nat) :
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst :=
  fun x => ρ (tag n x)

/-- The solution `ρ`, with the variables tagged `n` solved as `σ` solves them. -/
def withLocal (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (n : Nat)
    (σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) :
    Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst :=
  fun v => match untag v with
    | some (m, x) => if m = n then σ x else ρ v
    | none => ρ v

theorem withLocal_tag (ρ σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst)
    (n : Nat) (x : String) : withLocal ρ n σ (tag n x) = σ x := by
  simp [withLocal, untag_tag]

/-- Every variable of the atom carries a tag below `n`. -/
def TagsBelow (n : Nat) (a : Atom) : Prop :=
  ∀ v ∈ SubstitutionAlgebra.vars a, ∃ m x, m < n ∧ v = tag m x

theorem tagsBelow_of_ground (n : Nat) {a : Atom} (ground : isGroundAtom a = true) :
    TagsBelow n a := by
  intro v member
  rw [vars_of_ground a ground] at member
  exact absurd member List.not_mem_nil

theorem tagsBelow_rename (n : Nat) (a : Atom) : TagsBelow (n + 1) (rename n a) := by
  intro v member
  rw [vars_rename] at member
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp member
  exact ⟨n, x, Nat.lt_succ_self n, rfl⟩

theorem TagsBelow.mono {n m : Nat} {a : Atom} (below : TagsBelow n a) (le : n ≤ m) :
    TagsBelow m a := fun v member =>
  let ⟨k, x, lt, same⟩ := below v member
  ⟨k, x, Nat.lt_of_lt_of_le lt le, same⟩

/-- **The local solution does not disturb earlier knowledge.** On an atom whose variables
carry tags below `n`, the solution extended at tag `n` substitutes as the solution did. -/
theorem subst_withLocal_of_tagsBelow
    (ρ σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) {n : Nat} {a : Atom}
    (below : TagsBelow n a) :
    SubstitutionAlgebra.subst (withLocal ρ n σ) a = SubstitutionAlgebra.subst ρ a := by
  refine Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_congr_on_vars _ _ a ?_
  intro v member
  obtain ⟨m, x, lt, rfl⟩ := below v member
  have different : m ≠ n := Nat.ne_of_lt lt
  simp [withLocal, untag_tag, different]

/-- **The extended solution solves the renamed pattern as the local one solved the
pattern**, when the instance is ground. -/
theorem subst_withLocal_rename
    (ρ σ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (n : Nat) :
    ∀ (p b : Atom), SubstitutionAlgebra.subst σ p = b → isGroundAtom b = true →
      SubstitutionAlgebra.subst (withLocal ρ n σ) (rename n p) = b
  | .var x, b, solved, ground => by
      simp only [SubstitutionAlgebra.subst] at solved
      simp only [rename, SubstitutionAlgebra.subst, withLocal_tag]
      cases bound : σ x with
      | none =>
          rw [bound] at solved
          simp only [Option.getD_none] at solved
          rw [← solved] at ground
          simp [isGroundAtom] at ground
      | some value =>
          rw [bound] at solved
          simpa using solved
  | .symbol _, _, solved, _ => solved
  | .grounded _, _, solved, _ => solved
  | .expression es, b, solved, ground => by
      simp only [SubstitutionAlgebra.subst] at solved
      subst solved
      simp only [isGroundAtom] at ground
      simp only [rename, SubstitutionAlgebra.subst]
      rw [list es ground]
where
  list : ∀ es : List Atom,
      isGroundAtom.isGroundList (SubstitutionAlgebra.subst.substList σ es) = true →
      SubstitutionAlgebra.subst.substList (withLocal ρ n σ) (rename.renameList n es) =
        SubstitutionAlgebra.subst.substList σ es
    | [], _ => rfl
    | e :: es, ground => by
        simp only [SubstitutionAlgebra.subst.substList, isGroundAtom.isGroundList,
          Bool.and_eq_true] at ground
        simp only [rename.renameList, SubstitutionAlgebra.subst.substList,
          subst_withLocal_rename ρ σ n e _ rfl ground.1, list es ground.2]

/-- **A solution of a renamed pattern is, untagged, a solution of the pattern**, when the
instance is ground. -/
theorem subst_untagged_of_rename
    (ρ : Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst) (n : Nat) :
    ∀ (p b : Atom), SubstitutionAlgebra.subst ρ (rename n p) = b → isGroundAtom b = true →
      SubstitutionAlgebra.subst (untagged ρ n) p = b
  | .var x, b, solved, ground => by
      simp only [rename, SubstitutionAlgebra.subst] at solved
      simp only [SubstitutionAlgebra.subst, untagged]
      cases bound : ρ (tag n x) with
      | none =>
          rw [bound] at solved
          simp only [Option.getD_none] at solved
          rw [← solved] at ground
          simp [isGroundAtom] at ground
      | some value =>
          rw [bound] at solved
          simpa using solved
  | .symbol _, _, solved, _ => solved
  | .grounded _, _, solved, _ => solved
  | .expression es, b, solved, ground => by
      simp only [rename, SubstitutionAlgebra.subst] at solved
      subst solved
      simp only [isGroundAtom] at ground
      simp only [SubstitutionAlgebra.subst]
      rw [list es ground]
where
  list : ∀ es : List Atom,
      isGroundAtom.isGroundList
        (SubstitutionAlgebra.subst.substList ρ (rename.renameList n es)) = true →
      SubstitutionAlgebra.subst.substList (untagged ρ n) es =
        SubstitutionAlgebra.subst.substList ρ (rename.renameList n es)
    | [], _ => rfl
    | e :: es, ground => by
        simp only [rename.renameList, SubstitutionAlgebra.subst.substList,
          isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [rename.renameList, SubstitutionAlgebra.subst.substList,
          subst_untagged_of_rename ρ n e _ rfl ground.1, list es ground.2]

namespace Controls

/-- A name that does not start as a tag does decodes to nothing. -/
theorem untagged_name_has_no_tag : untag "x" = none := by decide

/-- The first firing's `x` and the second firing's `x` are different names. -/
theorem tags_differ : tag 0 "x" ≠ tag 1 "x" := fun same => by
  have := (tag_injective same).1
  omega

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
