import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationInstance

/-!
# Unfolding replicated components of a block

A replicated component `!X` of a block stands for unboundedly many copies of `X`. Unfolding it puts one copy of `X`,
its block in canonical form, beside the block's components, the copy's restrictions innermost (`Prenex.unfoldWith`):
`X`'s free variables already read the block's restrictions and the names outside, so only the block's own components
move past the copy's restrictions. The unfoldings of a block are reached by unfolding replicated components, of the
block or of copies unfolded before (`Unfolds`), and those within a number of unfoldings are listed (`unfoldings`).

A redex of a process may take copies of replicated molecules, so the canonical form of a process holds the redex only
after unfolding; these are the forms a step of the canonical form is read from.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)

variable {block : ReplicationBlock}

/-- **One copy of a block beside a block**: the copy's restrictions innermost, the block's components past them. The
copy's free variables read the block's restrictions and the names outside. -/
def Prenex.unfoldWith (form copy : Prenex) : Prenex :=
  ⟨copy.count + form.count, form.components.map (liftBVars 0 copy.count) ++ copy.components⟩

/-- **The unfoldings of a block**: the block, and an unfolding of a replicated component of an unfolding, one copy of
its argument beside it, the copy's block in canonical form. -/
inductive Unfolds (block : ReplicationBlock) : Prenex → Prenex → Prop
  | refl (form : Prenex) : Unfolds block form form
  | step {form next : Prenex} {argument : Pattern} : Unfolds block form next →
      Pattern.apply block.replicate [argument] ∈ next.components →
      Unfolds block form (next.unfoldWith (normal block (decompose block.toBlock argument)))

/-- The unfoldings of a block within a number of unfoldings. -/
inductive UnfoldsWithin (block : ReplicationBlock) : Nat → Prenex → Prenex → Prop
  | refl (depth : Nat) (form : Prenex) : UnfoldsWithin block depth form form
  | step {depth : Nat} {form next : Prenex} {argument : Pattern} :
      Pattern.apply block.replicate [argument] ∈ form.components →
      UnfoldsWithin block depth (form.unfoldWith (normal block (decompose block.toBlock argument))) next →
      UnfoldsWithin block (depth + 1) form next

/-- **The unfoldings of a block within a number of unfoldings, listed.** -/
def unfoldings (block : ReplicationBlock) : Nat → Prenex → List Prenex
  | 0, form => [form]
  | depth + 1, form => form :: (form.components.filterMap (replicatedArgument block)).flatMap fun argument =>
      unfoldings block depth (form.unfoldWith (normal block (decompose block.toBlock argument)))

theorem mem_replicatedArgument {component argument : Pattern} :
    replicatedArgument block component = some argument ↔ component = .apply block.replicate [argument] := by
  constructor
  · intro found
    match component, found with
    | .apply label [argument'], found =>
        simp only [replicatedArgument] at found
        split_ifs at found with isReplicate
        · cases found
          rw [isReplicate]
  · rintro rfl
    simp [replicatedArgument]

theorem UnfoldsWithin.mono {depth depth' : Nat} {form next : Prenex} (within : UnfoldsWithin block depth form next)
    (more : depth ≤ depth') : UnfoldsWithin block depth' form next := by
  induction within generalizing depth' with
  | refl => exact .refl _ _
  | @step depth form next argument member _ recurse =>
      obtain ⟨depth'', rfl⟩ : ∃ smaller, depth' = smaller + 1 := ⟨depth' - 1, by omega⟩
      exact .step member (recurse (by omega))

/-- **The list holds exactly the unfoldings within its number of unfoldings.** -/
theorem mem_unfoldings : ∀ (depth : Nat) (form next : Prenex),
    next ∈ unfoldings block depth form ↔ UnfoldsWithin block depth form next
  | 0, form, next => by
      constructor
      · intro member
        simp only [unfoldings, List.mem_singleton] at member
        subst member
        exact .refl _ _
      · intro within
        cases within with
        | refl => simp [unfoldings]
  | depth + 1, form, next => by
      simp only [unfoldings, List.mem_cons, List.mem_flatMap, List.mem_filterMap]
      constructor
      · rintro (rfl | ⟨argument, ⟨component, member, found⟩, inner⟩)
        · exact .refl _ _
        · rw [mem_replicatedArgument] at found
          subst found
          exact .step member ((mem_unfoldings depth _ next).mp inner)
      · intro within
        cases within with
        | refl => exact .inl rfl
        | step member rest =>
            exact .inr ⟨_, ⟨_, member, mem_replicatedArgument.mpr rfl⟩, (mem_unfoldings depth _ next).mpr rest⟩

/-- Unfolding first and then further is an unfolding. -/
theorem Unfolds.prepend {form next : Prenex} {argument : Pattern}
    (rest : Unfolds block (form.unfoldWith (normal block (decompose block.toBlock argument))) next)
    (member : Pattern.apply block.replicate [argument] ∈ form.components) : Unfolds block form next := by
  induction rest with
  | refl => exact .step (.refl _) member
  | step _ inner recurse => exact .step recurse inner

/-- An unfolding within a number of unfoldings is an unfolding. -/
theorem UnfoldsWithin.unfolds {depth : Nat} {form next : Prenex} (within : UnfoldsWithin block depth form next) :
    Unfolds block form next := by
  induction within with
  | refl => exact .refl _
  | step member _ recurse => exact recurse.prepend member

/-- Unfolding once more after an unfolding within a number of unfoldings. -/
theorem UnfoldsWithin.snoc {depth : Nat} {form next : Prenex} {argument : Pattern}
    (within : UnfoldsWithin block depth form next) (member : Pattern.apply block.replicate [argument] ∈ next.components) :
    UnfoldsWithin block (depth + 1) form (next.unfoldWith (normal block (decompose block.toBlock argument))) := by
  induction within with
  | refl depth form => exact .step member (.refl _ _)
  | step first _ recurse => exact .step first (recurse member)

/-- **Every unfolding is within some number of unfoldings.** -/
theorem Unfolds.within {form next : Prenex} (unfolds : Unfolds block form next) :
    ∃ depth, UnfoldsWithin block depth form next := by
  induction unfolds with
  | refl => exact ⟨0, .refl _ _⟩
  | step _ member recurse =>
      obtain ⟨depth, within⟩ := recurse
      exact ⟨depth + 1, within.snoc member⟩

/-! ## Unfolding renamed, and nested -/

theorem liftIndex_liftIndex (first second : Nat) (relabel : Nat → Nat) :
    liftIndex first (liftIndex second relabel) = liftIndex (first + second) relabel := by
  funext index
  simp only [liftIndex, Nat.sub_sub]
  split_ifs <;> omega

theorem liftBVars_liftBVars (first second : Nat) (pattern : Pattern) :
    liftBVars 0 first (liftBVars 0 second pattern) = liftBVars 0 (first + second) pattern := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false]
  omega

/-- **Renaming outside an unfolded block** renames the block and the copy, the copy past the block's restrictions. -/
theorem unfoldWith_renameOuter (form copy : Prenex) (relabel : Nat → Nat) :
    (form.unfoldWith copy).renameOuter relabel =
      (form.renameOuter relabel).unfoldWith (copy.renameOuter (liftIndex form.count relabel)) := by
  obtain ⟨count, components⟩ := form
  obtain ⟨copies, copyComponents⟩ := copy
  simp only [Prenex.unfoldWith, Prenex.renameOuter, List.map_append, List.map_map, Prenex.mk.injEq, true_and]
  congr 1
  · refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp]
    refine rename_liftBVars_zero copies (fun index => ?_) component
    simp only [liftIndex]
    by_cases below : index < count
    · rw [if_pos (by omega), if_pos below]
    · rw [if_neg (by omega), if_neg below, show index + copies - (copies + count) = index - count by omega]
      omega
  · rw [liftIndex_liftIndex]

/-- **Unfolding a copy inside a block** is unfolding the block further. -/
theorem unfoldWith_unfoldWith (form copy inner : Prenex) :
    (form.unfoldWith copy).unfoldWith inner = form.unfoldWith (copy.unfoldWith inner) := by
  obtain ⟨count, components⟩ := form
  obtain ⟨copies, copyComponents⟩ := copy
  obtain ⟨inners, innerComponents⟩ := inner
  simp only [Prenex.unfoldWith, List.map_append, List.map_map, List.append_assoc, Prenex.mk.injEq]
  refine ⟨by omega, ?_⟩
  congr 1
  refine List.map_congr_left fun component _ => ?_
  simp only [Function.comp]
  rw [liftBVars_liftBVars]

/-- **Unfoldings of a copy are unfoldings of the block holding it.** -/
theorem Unfolds.unfoldWith {copy next : Prenex} (unfolds : Unfolds block copy next) (form : Prenex) :
    Unfolds block (form.unfoldWith copy) (form.unfoldWith next) := by
  induction unfolds with
  | refl => exact .refl _
  | @step next argument _ member recurse =>
      rw [← unfoldWith_unfoldWith]
      exact .step recurse (List.mem_append_right _ member)

/-- **Unfoldings compose.** -/
theorem Unfolds.trans {first second third : Prenex} (head : Unfolds block first second)
    (tail : Unfolds block second third) : Unfolds block first third := by
  induction tail with
  | refl => exact head
  | step _ member recurse => exact .step recurse member

/-- **Unfoldings within some number of unfoldings compose**, within their sum. -/
theorem UnfoldsWithin.trans {first second third : Prenex} {depth depth' : Nat}
    (head : UnfoldsWithin block depth first second) (tail : UnfoldsWithin block depth' second third) :
    UnfoldsWithin block (depth + depth') first third := by
  induction head with
  | refl depth form => exact tail.mono (by omega)
  | @step depth form next argument member _ recurse =>
      rw [show depth + 1 + depth' = (depth + depth') + 1 by omega]
      exact .step member (recurse tail)

/-- **Unfoldings of a copy within some number of unfoldings are unfoldings of the block holding it**, within as
many. -/
theorem UnfoldsWithin.unfoldWith {copy next : Prenex} {depth : Nat} (within : UnfoldsWithin block depth copy next)
    (form : Prenex) : UnfoldsWithin block depth (form.unfoldWith copy) (form.unfoldWith next) := by
  induction within with
  | refl depth copy => exact .refl _ _
  | @step depth copy next argument member _ recurse =>
      refine .step (List.mem_append_right _ member) ?_
      rw [unfoldWith_unfoldWith]
      exact recurse

/-- One unfolding of a replicated component. -/
theorem UnfoldsWithin.single {form : Prenex} {argument : Pattern}
    (member : Pattern.apply block.replicate [argument] ∈ form.components) :
    UnfoldsWithin block 1 form (form.unfoldWith (normal block (decompose block.toBlock argument))) :=
  .step member (.refl _ _)

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
