import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups

/-!
# Removing copy groups around protected components

Some components of a block may be protected, as the components a redex takes are. Copy groups that avoid them can be
removed one by one until every copy group left meets them (`exists_removesAvoiding`).

Such a removal survives replacing protected components by others that mention only restrictions the replaced ones
mention, as what a redex leaves does: a copy group avoiding the replaced components is linked to none of them, so to
none of their replacements (`IsCopy.replace`, `RemovesAvoiding.replace`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups

open Finset

variable {ι : Type} [DecidableEq ι]

namespace System

variable (system : System ι)

/-- **Removing copy groups that avoid some components**, one by one. -/
inductive RemovesAvoiding (avoid : Finset ι) : Finset ι → Finset ι → Prop
  | refl {live : Finset ι} : RemovesAvoiding avoid live live
  | step {live rest : Finset ι} {p : ι} {copied : Finset ι} : system.IsCopy live p copied → Disjoint copied avoid →
      RemovesAvoiding avoid (live \ copied) rest → RemovesAvoiding avoid live rest

variable {system}

theorem RemovesAvoiding.removes {avoid live rest : Finset ι} (removes : system.RemovesAvoiding avoid live rest) :
    system.Removes live rest := by
  induction removes with
  | refl => exact .refl
  | step isCopy _ _ recurse => exact .step isCopy recurse

theorem RemovesAvoiding.subset {avoid live rest : Finset ι} (removes : system.RemovesAvoiding avoid live rest) :
    rest ⊆ live := by
  induction removes with
  | refl => exact Finset.Subset.refl _
  | step _ _ _ recurse => exact recurse.trans Finset.sdiff_subset

/-- **The avoided components stay.** -/
theorem RemovesAvoiding.keeps {avoid live rest : Finset ι} (removes : system.RemovesAvoiding avoid live rest) :
    live ∩ avoid ⊆ rest := by
  induction removes with
  | refl => exact Finset.inter_subset_left
  | @step live rest p copied _ disjoint _ recurse =>
      intro member inBoth
      obtain ⟨inLive, inAvoid⟩ := Finset.mem_inter.mp inBoth
      refine recurse (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨inLive, fun inCopied => ?_⟩, inAvoid⟩)
      exact Finset.disjoint_left.mp disjoint inCopied inAvoid

/-- **Removing copy groups that avoid some components until every copy group left meets them.** -/
theorem exists_removesAvoiding (avoid : Finset ι) : ∀ (live : Finset ι),
    ∃ rest, system.RemovesAvoiding avoid live rest ∧ ∀ p group, system.IsCopy rest p group → ¬ Disjoint group avoid := by
  intro live
  induction live using Finset.strongInduction with
  | H live recurse =>
      classical
      by_cases some : ∃ p group, system.IsCopy live p group ∧ Disjoint group avoid
      · obtain ⟨p, group, isCopy, disjoint⟩ := some
        obtain ⟨member, inGroup⟩ := isCopy.isGroup.nonempty
        have groupLive : group ⊆ live := fun element inGroup =>
          (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2
        have smaller : live \ group ⊂ live :=
          Finset.sdiff_ssubset groupLive ⟨member, inGroup⟩
        obtain ⟨rest, removes, maximal⟩ := recurse (live \ group) smaller
        exact ⟨rest, .step isCopy disjoint removes, maximal⟩
      · push Not at some
        exact ⟨live, .refl, fun p group isCopy disjoint => some p group isCopy disjoint⟩

/-- **A copy group avoiding some components stays one when they are replaced** by components mentioning only
restrictions that they or some kept components it avoids mention: a link to a new component would be a link to a
replaced or kept one, which the group does not hold. -/
theorem IsCopy.replace {common old new keep : Finset ι} {p : ι} {copied : Finset ι}
    (isCopy : system.IsCopy (common ∪ old) p copied) (avoids : Disjoint copied (old ∪ keep)) (pCommon : p ∈ common)
    (keepCommon : keep ⊆ common)
    (newMentions : ∀ element ∈ new, ∀ restriction ∈ system.mentions element,
      ∃ original ∈ old ∪ keep, restriction ∈ system.mentions original) :
    system.IsCopy (common ∪ new) p copied where
  isLive := Finset.mem_union_left _ pCommon
  isReplicated := isCopy.isReplicated
  isCopy := isCopy.isCopy
  isGroup := by
    have groupCommon : copied ⊆ common := by
      intro member inCopied
      have inLive := (Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).2
      rcases Finset.mem_union.mp inLive with inCommon | inOld
      · exact inCommon
      · exact absurd (Finset.mem_union_left _ inOld) (Finset.disjoint_left.mp avoids inCopied)
    refine ⟨fun member inCopied => ?_, isCopy.isGroup.nonempty, isCopy.isGroup.linked, ?_⟩
    · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).1,
        Finset.mem_union_left _ (groupCommon inCopied)⟩
    · intro first inFirst second inLive link
      obtain ⟨notP, inUnion⟩ := Finset.mem_erase.mp inLive
      rcases Finset.mem_union.mp inUnion with inCommon | inNew
      · exact isCopy.isGroup.closed first inFirst second
          (Finset.mem_erase.mpr ⟨notP, Finset.mem_union_left _ inCommon⟩) link
      · obtain ⟨restriction, mentioned, mentioned', notMentioned⟩ := link
        obtain ⟨original, inOriginal, mentionedOriginal⟩ := newMentions second inNew restriction mentioned'
        have originalLive : original ∈ common ∪ old := by
          rcases Finset.mem_union.mp inOriginal with inOld | inKeep
          · exact Finset.mem_union_right _ inOld
          · exact Finset.mem_union_left _ (keepCommon inKeep)
        have originalNotP : original ≠ p := fun same => notMentioned (same ▸ mentionedOriginal)
        have originalHeld := isCopy.isGroup.closed first inFirst original
          (Finset.mem_erase.mpr ⟨originalNotP, originalLive⟩) ⟨restriction, mentioned, mentionedOriginal, notMentioned⟩
        exact absurd inOriginal (Finset.disjoint_left.mp avoids originalHeld)

/-- **A removal avoiding some components survives replacing them**, by components mentioning only restrictions the
replaced or kept avoided ones mention: the components kept beside the replaced ones are kept beside their
replacements. -/
theorem RemovesAvoiding.replace {avoid live rest : Finset ι} (removes : system.RemovesAvoiding avoid live rest) :
    ∀ {common old new keep : Finset ι}, live = common ∪ old → Disjoint common old → Disjoint common new →
      old ⊆ avoid → keep ⊆ avoid → keep ⊆ common → (∀ q ∈ old, ¬ system.replicated q) →
      (∀ element ∈ new, ∀ restriction ∈ system.mentions element,
        ∃ original ∈ old ∪ keep, restriction ∈ system.mentions original) →
      ∃ common', common' ⊆ common ∧ rest = common' ∪ old ∧ system.Removes (common ∪ new) (common' ∪ new) := by
  induction removes with
  | refl =>
      intro common old new keep liveIs _ _ _ _ _ _ _
      exact ⟨common, Finset.Subset.refl _, liveIs, .refl⟩
  | @step live rest p copied isCopy disjoint _ recurse =>
      intro common old new keep liveIs commonOld commonNew oldAvoid keepAvoid keepCommon oldPlain newMentions
      subst liveIs
      have avoidsBoth : Disjoint copied (old ∪ keep) :=
        disjoint.mono_right (Finset.union_subset oldAvoid keepAvoid)
      have avoidsOld : Disjoint copied old := avoidsBoth.mono_right Finset.subset_union_left
      have copiedCommon : copied ⊆ common := by
        intro member inCopied
        have inLive := (Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).2
        rcases Finset.mem_union.mp inLive with inCommon | inOld
        · exact inCommon
        · exact absurd inOld (Finset.disjoint_left.mp avoidsOld inCopied)
      have pNotOld : p ∉ old := fun inOld => oldPlain p inOld isCopy.isReplicated
      have pCommon : p ∈ common := by
        rcases Finset.mem_union.mp isCopy.isLive with inCommon | inOld
        · exact inCommon
        · exact absurd inOld pNotOld
      have replaced := IsCopy.replace (new := new) isCopy avoidsBoth pCommon keepCommon newMentions
      have liveRest : (common ∪ old) \ copied = (common \ copied) ∪ old := by
        ext member
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨inCommon | inOld, notCopied⟩
          · exact .inl ⟨inCommon, notCopied⟩
          · exact .inr inOld
        · rintro (⟨inCommon, notCopied⟩ | inOld)
          · exact ⟨.inl inCommon, notCopied⟩
          · exact ⟨.inr inOld, Finset.disjoint_right.mp avoidsOld inOld⟩
      have newRest : (common ∪ new) \ copied = (common \ copied) ∪ new := by
        ext member
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨inCommon | inNew, notCopied⟩
          · exact .inl ⟨inCommon, notCopied⟩
          · exact .inr inNew
        · rintro (⟨inCommon, notCopied⟩ | inNew)
          · exact ⟨.inl inCommon, notCopied⟩
          · exact ⟨.inr inNew, fun inCopied => Finset.disjoint_left.mp commonNew (copiedCommon inCopied) inNew⟩
      have keepRest : keep ⊆ common \ copied := fun member inKeep =>
        Finset.mem_sdiff.mpr ⟨keepCommon inKeep, fun inCopied =>
          Finset.disjoint_left.mp avoidsBoth inCopied (Finset.mem_union_right _ inKeep)⟩
      obtain ⟨common', inside, restIs, rest⟩ := recurse liveRest
        (Finset.disjoint_of_subset_left Finset.sdiff_subset commonOld)
        (Finset.disjoint_of_subset_left Finset.sdiff_subset commonNew) oldAvoid keepAvoid keepRest oldPlain newMentions
      refine ⟨common', inside.trans Finset.sdiff_subset, restIs, .step replaced ?_⟩
      rw [newRest]
      exact rest

end System

section Iso

variable {κ : Type} [DecidableEq κ] {system : System ι} {other : System κ} {map : ι → κ} {relabel : Nat → Nat}

/-- **Removing copy groups carries across an isomorphism.** -/
theorem System.Iso.removes {live rest : Finset ι} (removes : system.Removes live rest) :
    System.Iso system other live map relabel → other.Removes (live.image map) (rest.image map) := by
  induction removes with
  | refl => exact fun _ => .refl
  | @step live rest p copied isCopy _ recurse =>
      intro iso
      have copiedLive : copied ⊆ live := fun member inCopied =>
        (Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).2
      refine .step ((iso.isCopy_iff isCopy.isLive copiedLive).mpr isCopy) ?_
      rw [← iso.image_sdiff (Finset.Subset.refl _) copiedLive]
      exact recurse (iso.mono Finset.sdiff_subset)

end Iso

namespace System

end System

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups
