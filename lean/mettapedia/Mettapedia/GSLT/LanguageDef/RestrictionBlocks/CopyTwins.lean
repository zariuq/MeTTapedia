import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups
import Mathlib.Data.Finset.Max

/-!
# Twin replicated components

Two distinct replicated components that mention the same restrictions, copy the same groups, and leave a copy group
holding both a copy or not when one of them is dropped from it are **twins** (`Twins`). One twin is in a copy group
exactly when the other is (`Twins.mem_copies_iff`), and removing one twin removes just it from the copies
(`Twins.copies_erase`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups

variable {ι : Type} [DecidableEq ι]

namespace System

variable {system : System ι}

/-- **A pair of alike replicated components** among some live components: distinct, both replicated, mentioning
the same restrictions. -/
structure TwinPair (live : Finset ι) (d e : ι) : Prop where
  dLive : d ∈ live
  eLive : e ∈ live
  different : d ≠ e
  dReplicated : system.replicated d
  eReplicated : system.replicated e
  sameMentions : system.mentions d = system.mentions e

/-- **Twin replicated components**: an alike pair copying the same groups, a copy group holding both being a copy
or not without `d`. -/
structure Twins (live : Finset ι) (d e : ι) : Prop extends system.TwinPair live d e where
  sameCopies : ∀ group ⊆ live, d ∉ group → e ∉ group → (system.copy group d ↔ system.copy group e)
  dropOne : ∀ p ∈ live, p ≠ d → p ≠ e → ∀ group ⊆ live, p ∉ group → d ∈ group → e ∈ group →
    (system.copy group p ↔ system.copy (group.erase d) p)

variable {live : Finset ι} {d e : ι}

omit [DecidableEq ι] in
theorem TwinPair.symm (pair : system.TwinPair live d e) : system.TwinPair live e d :=
  ⟨pair.eLive, pair.dLive, pair.different.symm, pair.eReplicated, pair.dReplicated, pair.sameMentions.symm⟩

/-- The twin `e` in place of the twin `d`. -/
def swapTwin (d e : ι) (member : ι) : ι := if member = d then e else member

theorem swapTwin_of_ne {member : ι} (different : member ≠ d) : swapTwin d e member = member := if_neg different

theorem TwinPair.mentions_swap (twins : system.TwinPair live d e) (member : ι) :
    system.mentions (swapTwin d e member) = system.mentions member := by
  unfold swapTwin
  split_ifs with isD
  · rw [isD, twins.sameMentions]
  · rfl

/-- **A path through the twin `d` passes through `e` instead.** -/
theorem TwinPair.linkedIn_swap (twins : system.TwinPair live d e) {p : ι} {set target : Finset ι}
    (into : ∀ member ∈ set, member ≠ d → member ∈ target) (eIn : e ∈ target) {first second : ι}
    (linked : system.LinkedIn p set first second) :
    system.LinkedIn p target (swapTwin d e first) (swapTwin d e second) := by
  have swapIn : ∀ member ∈ set, swapTwin d e member ∈ target := by
    intro member inSet
    unfold swapTwin
    split_ifs with isD
    · exact eIn
    · exact into member inSet isD
  induction linked with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step reached =>
      obtain ⟨inFirst, inSecond, link⟩ := step
      obtain ⟨restriction, inMiddle, inLast, notP⟩ := link
      refine reached.tail ⟨swapIn _ inFirst, swapIn _ inSecond, restriction, ?_, ?_, notP⟩
      · rw [twins.mentions_swap]; exact inMiddle
      · rw [twins.mentions_swap]; exact inLast

/-- A group holding a component that links to nothing is that component alone. -/
theorem IsGroup.eq_singleton {p member : ι} {group : Finset ι} (isGroup : system.IsGroup live p group)
    (inGroup : member ∈ group) (alone : ∀ other, ¬ system.LinkFor p member other) : group = {member} := by
  ext other
  simp only [Finset.mem_singleton]
  constructor
  · intro inOther
    rcases Relation.ReflTransGen.cases_head (isGroup.linked member inGroup other inOther) with same | ⟨_, ⟨-, -, link⟩, -⟩
    · exact same.symm
    · exact absurd link (alone _)
  · rintro rfl
    exact inGroup

omit [DecidableEq ι] in
/-- `d` links for `e` to nothing. -/
theorem TwinPair.alone_d (twins : system.TwinPair live d e) (other : ι) : ¬ system.LinkFor e d other := by
  rintro ⟨restriction, inD, -, notE⟩
  rw [twins.sameMentions] at inD
  exact notE inD

omit [DecidableEq ι] in
/-- `e` links for `d` to nothing. -/
theorem TwinPair.alone_e (twins : system.TwinPair live d e) (other : ι) : ¬ system.LinkFor d e other := by
  rintro ⟨restriction, inE, -, notD⟩
  rw [← twins.sameMentions] at inE
  exact notD inE

/-- A group of a component among the live ones, not holding `d`, is a group among the others. -/
theorem IsGroup.erase_of_not_mem {p : ι} {group : Finset ι} (isGroup : system.IsGroup live p group)
    (notD : d ∉ group) : system.IsGroup (live.erase d) p group where
  subset := fun member inGroup => by
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (isGroup.subset inGroup)
    exact Finset.mem_erase.mpr ⟨different, Finset.mem_erase.mpr ⟨fun same => notD (same ▸ inGroup), inLive⟩⟩
  nonempty := isGroup.nonempty
  linked := isGroup.linked
  closed := fun first inFirst second inSecond link => by
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp inSecond
    exact isGroup.closed first inFirst second (Finset.mem_erase.mpr ⟨different, (Finset.mem_erase.mp inLive).2⟩) link

/-- A group among the others from which nothing links to `d` is a group among all. -/
theorem IsGroup.of_erase {p : ι} {group : Finset ι} (isGroup : system.IsGroup (live.erase d) p group)
    (apart : ∀ first ∈ group, ¬ system.LinkFor p first d) : system.IsGroup live p group where
  subset := fun member inGroup => by
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (isGroup.subset inGroup)
    exact Finset.mem_erase.mpr ⟨different, (Finset.mem_erase.mp inLive).2⟩
  nonempty := isGroup.nonempty
  linked := isGroup.linked
  closed := fun first inFirst second inSecond link => by
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp inSecond
    by_cases isD : second = d
    · subst isD
      exact absurd link (apart first inFirst)
    · exact isGroup.closed first inFirst second
        (Finset.mem_erase.mpr ⟨different, Finset.mem_erase.mpr ⟨isD, inLive⟩⟩) link

/-- **A group holding `d` and something else holds `e`**, unless it is a group of `e`. -/
theorem TwinPair.mem_of_mem (twins : system.TwinPair live d e) {p : ι} (pE : p ≠ e) {group : Finset ι}
    (isGroup : system.IsGroup live p group) (dIn : d ∈ group) {other : ι} (otherIn : other ∈ group)
    (otherD : other ≠ d) : e ∈ group := by
  obtain ⟨middle, middleIn, link⟩ : ∃ middle ∈ group, system.LinkFor p middle d := by
    rcases Relation.ReflTransGen.cases_tail (isGroup.linked other otherIn d dIn) with same | ⟨middle, -, middleIn, -, link⟩
    · exact absurd same.symm otherD
    · exact ⟨middle, middleIn, link⟩
  refine isGroup.closed middle middleIn e (Finset.mem_erase.mpr ⟨fun same => pE same.symm, twins.eLive⟩) ?_
  obtain ⟨restriction, inMiddle, inD, notP⟩ := link
  rw [twins.sameMentions] at inD
  exact ⟨restriction, inMiddle, inD, notP⟩

/-- A group holding `d` and something else, with `e`, is a group without `d` among the others. -/
theorem TwinPair.erase_group (twins : system.TwinPair live d e) {p : ι} {group : Finset ι}
    (isGroup : system.IsGroup live p group) (eIn : e ∈ group) : system.IsGroup (live.erase d) p (group.erase d) where
  subset := fun member inGroup => by
    obtain ⟨memberD, inGroup'⟩ := Finset.mem_erase.mp inGroup
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (isGroup.subset inGroup')
    exact Finset.mem_erase.mpr ⟨different, Finset.mem_erase.mpr ⟨memberD, inLive⟩⟩
  nonempty := ⟨e, Finset.mem_erase.mpr ⟨twins.different.symm, eIn⟩⟩
  linked := fun first inFirst second inSecond => by
    obtain ⟨firstD, firstIn⟩ := Finset.mem_erase.mp inFirst
    obtain ⟨secondD, secondIn⟩ := Finset.mem_erase.mp inSecond
    have swapped := twins.linkedIn_swap (target := group.erase d) (fun member inGroup memberD =>
      Finset.mem_erase.mpr ⟨memberD, inGroup⟩) (Finset.mem_erase.mpr ⟨twins.different.symm, eIn⟩)
      (isGroup.linked first firstIn second secondIn)
    rwa [swapTwin_of_ne firstD, swapTwin_of_ne secondD] at swapped
  closed := fun first inFirst second inSecond link => by
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp inSecond
    obtain ⟨secondD, secondLive⟩ := Finset.mem_erase.mp inLive
    exact Finset.mem_erase.mpr ⟨secondD, isGroup.closed first (Finset.mem_erase.mp inFirst).2 second
      (Finset.mem_erase.mpr ⟨different, secondLive⟩) link⟩

/-- **A copy group holding one of an alike pair holds the other.** -/
theorem TwinPair.mem_of_copy {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole)
    (pair : system.TwinPair live d e) {q : ι} {group : Finset ι} (isCopy : system.IsCopy live q group)
    (dIn : d ∈ group) : e ∈ group := by
  by_cases qE : q = e
  · subst qE
    have single := isCopy.isGroup.eq_singleton dIn pair.alone_d
    exact absurd (single ▸ isCopy.isCopy) (laws.notLone d (inside pair.dLive) q (inside pair.eLive) pair.different
      pair.dReplicated pair.eReplicated pair.sameMentions.le)
  · by_cases alone : group = {d}
    · -- alone, `d` mentions only what `q` mentions, so it is no copy of `q`
      have within : system.mentions d ⊆ system.mentions q := by
        intro restriction inD
        by_contra notQ
        have inE : restriction ∈ system.mentions e := by rw [← pair.sameMentions]; exact inD
        have inGroup := isCopy.isGroup.closed d dIn e
          (Finset.mem_erase.mpr ⟨fun same => qE same.symm, pair.eLive⟩) ⟨restriction, inD, inE, notQ⟩
        rw [alone, Finset.mem_singleton] at inGroup
        exact pair.different inGroup.symm
      exact absurd (alone ▸ isCopy.isCopy) (laws.notLone d (inside pair.dLive) q (inside isCopy.isLive)
        (fun same => isCopy.isGroup.not_mem (same ▸ dIn)) pair.dReplicated isCopy.isReplicated within)
    · obtain ⟨other, otherIn, otherD⟩ : ∃ other ∈ group, other ≠ d := by
        by_contra none
        push Not at none
        exact alone (Finset.eq_singleton_iff_unique_mem.mpr ⟨dIn, none⟩)
      exact pair.mem_of_mem qE isCopy.isGroup dIn otherIn otherD

/-- **One of an alike pair is in a copy group exactly when the other is.** -/
theorem TwinPair.mem_copies_iff {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole)
    (pair : system.TwinPair live d e) : d ∈ system.copies live ↔ e ∈ system.copies live := by
  rw [system.mem_copies, system.mem_copies]
  constructor
  · rintro ⟨-, q, group, isCopy, dIn⟩
    exact ⟨pair.eLive, q, group, isCopy, pair.mem_of_copy laws inside isCopy dIn⟩
  · rintro ⟨-, q, group, isCopy, eIn⟩
    exact ⟨pair.dLive, q, group, isCopy, pair.symm.mem_of_copy laws inside isCopy eIn⟩

/-- **Removing one twin removes just it from the copies.** -/
theorem Twins.copies_erase {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole)
    (twins : system.Twins live d e) : system.copies (live.erase d) = (system.copies live).erase d := by
  have pair := twins.toTwinPair
  have eRest : e ∈ live.erase d := Finset.mem_erase.mpr ⟨pair.different.symm, pair.eLive⟩
  ext member
  rw [Finset.mem_erase, system.mem_copies, system.mem_copies]
  constructor
  · rintro ⟨inRest, q, group, isCopy, inGroup⟩
    obtain ⟨memberD, memberLive⟩ := Finset.mem_erase.mp inRest
    obtain ⟨qD, qLive⟩ := Finset.mem_erase.mp isCopy.isLive
    refine ⟨memberD, memberLive, ?_⟩
    by_cases qE : q = e
    · subst qE
      refine ⟨q, group, ⟨qLive, isCopy.isReplicated, isCopy.isGroup.of_erase fun first _ link => ?_,
        isCopy.isCopy⟩, inGroup⟩
      obtain ⟨restriction, -, inD, notE⟩ := link
      rw [pair.sameMentions] at inD
      exact notE inD
    · have memberQ : member ≠ q := (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).1
      obtain ⟨full, fullGroup, memberIn⟩ := IsGroup.exists_of_mem (system := system)
        (Finset.mem_erase.mpr ⟨memberQ, memberLive⟩)
      -- the group among the others is the group among all, without `d`
      have restInFull : group ⊆ full := fun other inOther =>
        fullGroup.reach memberIn ((isCopy.isGroup.linked member inGroup other inOther).mono fun element inElement =>
          by
            obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (isCopy.isGroup.subset inElement)
            exact Finset.mem_erase.mpr ⟨different, (Finset.mem_erase.mp inLive).2⟩)
      have fullInRest : ∀ other ∈ full, other ≠ d → other ∈ group := by
        intro other inOther otherD
        have swapped := pair.linkedIn_swap (target := (live.erase d).erase q)
          (fun element inElement elementD => by
            obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (fullGroup.subset inElement)
            exact Finset.mem_erase.mpr ⟨different, Finset.mem_erase.mpr ⟨elementD, inLive⟩⟩)
          (Finset.mem_erase.mpr ⟨fun same => qE same.symm, eRest⟩) (fullGroup.linked member memberIn other inOther)
        rw [swapTwin_of_ne memberD, swapTwin_of_ne otherD] at swapped
        exact isCopy.isGroup.reach inGroup swapped
      have dNot : d ∉ group := fun dIn => (Finset.mem_erase.mp (Finset.mem_erase.mp
        (isCopy.isGroup.subset dIn)).2).1 rfl
      refine ⟨q, full, ⟨qLive, isCopy.isReplicated, fullGroup, ?_⟩, memberIn⟩
      by_cases dIn : d ∈ full
      · have eIn := pair.mem_of_mem qE fullGroup dIn memberIn memberD
        have restIs : full.erase d = group := by
          ext other
          rw [Finset.mem_erase]
          exact ⟨fun ⟨otherD, inFull⟩ => fullInRest other inFull otherD,
            fun inRest' => ⟨fun same => dNot (same ▸ inRest'), restInFull inRest'⟩⟩
        rw [twins.dropOne q qLive qD qE full (fun other inFull => (Finset.mem_erase.mp (fullGroup.subset inFull)).2)
          fullGroup.not_mem dIn eIn, restIs]
        exact isCopy.isCopy
      · have same : full = group := Finset.Subset.antisymm
          (fun other inFull => fullInRest other inFull fun same => dIn (same ▸ inFull)) restInFull
        rw [same]
        exact isCopy.isCopy
  · rintro ⟨memberD, memberLive, q, group, isCopy, inGroup⟩
    refine ⟨Finset.mem_erase.mpr ⟨memberD, memberLive⟩, ?_⟩
    have groupLive : group ⊆ live := fun other inOther => (Finset.mem_erase.mp (isCopy.isGroup.subset inOther)).2
    by_cases qD : q = d
    · subst qD
      -- a copy group of `d` holds neither twin, and is one of `e` among the others
      have eNot : e ∉ group := fun eIn => by
        have single := isCopy.isGroup.eq_singleton eIn pair.alone_e
        exact laws.notLone e (inside pair.eLive) q (inside pair.dLive) pair.different.symm pair.eReplicated
          pair.dReplicated pair.sameMentions.ge (single ▸ isCopy.isCopy)
      have dNot : q ∉ group := isCopy.isGroup.not_mem
      have asE : system.IsGroup (live.erase q) e group := by
        refine ⟨fun other inOther => ?_, isCopy.isGroup.nonempty, fun first inFirst second inSecond => ?_,
          fun first inFirst second inSecond link => ?_⟩
        · obtain ⟨otherD, otherLive⟩ := Finset.mem_erase.mp (isCopy.isGroup.subset inOther)
          exact Finset.mem_erase.mpr ⟨fun same => eNot (same ▸ inOther), Finset.mem_erase.mpr ⟨otherD, otherLive⟩⟩
        · have linked := isCopy.isGroup.linked first inFirst second inSecond
          unfold LinkedIn LinkFor at linked ⊢
          rwa [← pair.sameMentions]
        · obtain ⟨different, inLive⟩ := Finset.mem_erase.mp inSecond
          obtain ⟨secondD, secondLive⟩ := Finset.mem_erase.mp inLive
          unfold LinkFor at link
          rw [← pair.sameMentions] at link
          exact isCopy.isGroup.closed first inFirst second (Finset.mem_erase.mpr ⟨secondD, secondLive⟩) link
      exact ⟨e, group, ⟨eRest, pair.eReplicated, asE, (twins.sameCopies group groupLive dNot eNot).mp isCopy.isCopy⟩,
        inGroup⟩
    · have qLive : q ∈ live.erase d := Finset.mem_erase.mpr ⟨qD, isCopy.isLive⟩
      by_cases dIn : d ∈ group
      · by_cases qE : q = e
        · subst qE
          have single := isCopy.isGroup.eq_singleton dIn pair.alone_d
          exact absurd (single ▸ isCopy.isCopy) (laws.notLone d (inside pair.dLive) q (inside pair.eLive)
            pair.different pair.dReplicated pair.eReplicated pair.sameMentions.le)
        · have eIn := pair.mem_of_mem qE isCopy.isGroup dIn inGroup memberD
          exact ⟨q, group.erase d, ⟨qLive, isCopy.isReplicated, pair.erase_group isCopy.isGroup eIn,
            (twins.dropOne q isCopy.isLive qD qE group groupLive isCopy.isGroup.not_mem dIn eIn).mp isCopy.isCopy⟩,
            Finset.mem_erase.mpr ⟨memberD, inGroup⟩⟩
      · exact ⟨q, group, ⟨qLive, isCopy.isReplicated, isCopy.isGroup.erase_of_not_mem dIn, isCopy.isCopy⟩, inGroup⟩

/-- **Absorption without one twin ends where absorption with both does, without it.** -/
theorem Twins.absorbs_erase {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole)
    (twins : system.Twins live d e) {final : Finset ι} (absorbs : system.Absorbs (live.erase d) final) :
    final = (live \ system.copies live).erase d := by
  rw [absorbs.eq laws ((Finset.erase_subset d live).trans inside), twins.copies_erase laws inside]
  ext member
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  tauto

/-- **Absorption leaves something of a nonempty set of components**: the highest replicated component a copy group
needs is in none, since what holds it would be higher still. -/
theorem exists_not_copy {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole)
    (nonempty : live.Nonempty) : ∃ member ∈ live, member ∉ system.copies live := by
  classical
  by_contra allCopies
  push Not at allCopies
  obtain ⟨start, startLive⟩ := nonempty
  obtain ⟨-, absorber, group, isCopy, -⟩ := system.mem_copies.mp (allCopies start startLive)
  set replicatedLive := live.filter system.replicated
  have absorberIn : absorber ∈ replicatedLive := Finset.mem_filter.mpr ⟨isCopy.isLive, isCopy.isReplicated⟩
  obtain ⟨highest, highestIn, highestMax⟩ :=
    replicatedLive.exists_max_image system.height ⟨absorber, absorberIn⟩
  obtain ⟨highestLive, highestReplicated⟩ := Finset.mem_filter.mp highestIn
  obtain ⟨-, holder, held, holderCopy, inHeld⟩ := system.mem_copies.mp (allCopies highest highestLive)
  have lower := laws.lower held (fun member inGroup => inside (Finset.mem_erase.mp
    (holderCopy.isGroup.subset inGroup)).2) holder (inside holderCopy.isLive) holderCopy.isGroup.not_mem highest
    holderCopy.isReplicated holderCopy.isCopy inHeld highestReplicated
  have notHigher := highestMax holder (Finset.mem_filter.mpr ⟨holderCopy.isLive, holderCopy.isReplicated⟩)
  omega

end System

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups
