import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-!
# Copy groups

The combinatorics of absorption, `!P | P = !P`, over any components. Components mention restrictions; some are
replicated. For a replicated component `p`, the other components are linked through the restrictions `p` does not
mention (`LinkFor`); a **group** of `p` is a class of this linking (`IsGroup`), and a **copy group** is a group that
is a copy of `p`'s argument (`IsCopy`, by a predicate `copy` given with the system).

Under four laws of the copy predicate (`Laws`) — a copy mentions every restriction its replicated component mentions;
a lone replicated component is never a copy; a replicated component held by a copy is lower than the one it copies;
a copy keeps or loses that status when a copy inside it is absorbed — removing a copy group removes exactly itself
from the copy groups (`removed_copies`). So every way of removing copy groups until none is left removes the same
components: those of some copy group (`copies`), and absorption has one result.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups

open Finset

variable {ι : Type} [DecidableEq ι]

/-- **A system of components for absorption**: the restrictions each component mentions, which are replicated,
when a set of components is a copy of a replicated component's argument, and a height of replicated components. -/
structure System (ι : Type) where
  mentions : ι → Finset Nat
  replicated : ι → Prop
  copy : Finset ι → ι → Prop
  height : ι → Nat

namespace System

variable (system : System ι)

/-- Two components are linked for `p` when they share a restriction `p` does not mention. -/
def LinkFor (p first second : ι) : Prop :=
  ∃ restriction ∈ system.mentions first, restriction ∈ system.mentions second ∧ restriction ∉ system.mentions p

/-- Linked inside a set, for `p`. -/
def LinkedIn (p : ι) (set : Finset ι) : ι → ι → Prop :=
  Relation.ReflTransGen fun first second => first ∈ set ∧ second ∈ set ∧ system.LinkFor p first second

/-- **A group of `p` among the components `live`**: components other than `p`, linked inside, and closed under
linking for `p`. -/
structure IsGroup (live : Finset ι) (p : ι) (group : Finset ι) : Prop where
  subset : group ⊆ live.erase p
  nonempty : group.Nonempty
  linked : ∀ first ∈ group, ∀ second ∈ group, system.LinkedIn p group first second
  closed : ∀ first ∈ group, ∀ second ∈ live.erase p, system.LinkFor p first second → second ∈ group

/-- **A copy group**: a group of a live replicated component that is a copy of its argument. -/
structure IsCopy (live : Finset ι) (p : ι) (group : Finset ι) : Prop where
  isLive : p ∈ live
  isReplicated : system.replicated p
  isGroup : system.IsGroup live p group
  isCopy : system.copy group p

/-- **The laws of a copy predicate on some components.** -/
structure Laws (whole : Finset ι) : Prop where
  /-- A copy mentions every restriction its replicated component mentions. -/
  free : ∀ group ⊆ whole, ∀ p ∈ whole, p ∉ group → system.replicated p → system.copy group p →
    ∀ restriction ∈ system.mentions p, ∃ member ∈ group, restriction ∈ system.mentions member
  /-- A replicated component mentioning only restrictions another one mentions is not a copy of it alone. -/
  notLone : ∀ q ∈ whole, ∀ p ∈ whole, q ≠ p → system.replicated q → system.replicated p →
    system.mentions q ⊆ system.mentions p → ¬ system.copy {q} p
  /-- A replicated component held by a copy is lower than the replicated component it copies. -/
  lower : ∀ group ⊆ whole, ∀ p ∈ whole, p ∉ group → ∀ q, system.replicated p → system.copy group p → q ∈ group →
    system.replicated q → system.height q < system.height p
  /-- **Absorbing a copy inside a group keeps the group a copy or not.** -/
  inner : ∀ live ⊆ whole, ∀ p group q outer, system.IsCopy live p group → q ∈ live → system.replicated q →
    system.IsGroup live q outer → q ≠ p → group ⊆ outer → p ∈ outer →
    (system.copy outer q ↔ system.copy (outer \ group) q)

variable {system}

omit [DecidableEq ι] in
theorem LinkFor.symm {p first second : ι} (link : system.LinkFor p first second) : system.LinkFor p second first :=
  let ⟨restriction, inFirst, inSecond, notP⟩ := link
  ⟨restriction, inSecond, inFirst, notP⟩

omit [DecidableEq ι] in
theorem LinkedIn.mono {p : ι} {set set' : Finset ι} (subset : set ⊆ set') {first second : ι}
    (linked : system.LinkedIn p set first second) : system.LinkedIn p set' first second := by
  induction linked with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step reached =>
      obtain ⟨inFirst, inSecond, link⟩ := step
      exact reached.tail ⟨subset inFirst, subset inSecond, link⟩

omit [DecidableEq ι] in
theorem LinkedIn.symm {p : ι} {set : Finset ι} {first second : ι} (linked : system.LinkedIn p set first second) :
    system.LinkedIn p set second first := by
  induction linked with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step reached =>
      obtain ⟨inFirst, inSecond, link⟩ := step
      exact Relation.ReflTransGen.head ⟨inSecond, inFirst, link.symm⟩ reached

/-- **A group holds everything linked to its members among the live components.** -/
theorem IsGroup.reach {live : Finset ι} {p : ι} {group : Finset ι} (isGroup : system.IsGroup live p group)
    {first second : ι} (inGroup : first ∈ group) (linked : system.LinkedIn p (live.erase p) first second) :
    second ∈ group := by
  induction linked with
  | refl => exact inGroup
  | tail _ step reached =>
      obtain ⟨-, inLive, link⟩ := step
      exact isGroup.closed _ reached _ inLive link

/-- **Two groups of one component sharing a member are one group.** -/
theorem IsGroup.eq_of_mem {live : Finset ι} {p : ι} {first second : Finset ι} (firstGroup : system.IsGroup live p first)
    (secondGroup : system.IsGroup live p second) {member : ι} (inFirst : member ∈ first) (inSecond : member ∈ second) :
    first = second := by
  ext other
  constructor
  · intro inOther
    exact secondGroup.reach inSecond ((firstGroup.linked member inFirst other inOther).mono firstGroup.subset)
  · intro inOther
    exact firstGroup.reach inFirst ((secondGroup.linked member inSecond other inOther).mono secondGroup.subset)

theorem IsGroup.not_mem {live : Finset ι} {p : ι} {group : Finset ι} (isGroup : system.IsGroup live p group) :
    p ∉ group := fun inGroup => (Finset.mem_erase.mp (isGroup.subset inGroup)).1 rfl

/-! ## Removing a copy group -/

section Removal

variable {live : Finset ι} {p : ι} {copied : Finset ι}

/-- The replicated component of a copy group stays live once the copy group is removed. -/
theorem IsCopy.live_rest (isCopy : system.IsCopy live p copied) : p ∈ live \ copied :=
  Finset.mem_sdiff.mpr ⟨isCopy.isLive, isCopy.isGroup.not_mem⟩

/-- **A copy group of `p` is linked for any other live component it does not hold**: a link between its members
uses a restriction `p` does not mention, which the other component does not mention either, or it would be in the
copy group. -/
theorem IsCopy.link_for {q : ι} (isCopy : system.IsCopy live p copied) (qLive : q ∈ live) (qOther : q ≠ p)
    (notHeld : q ∉ copied) {first second : ι} (link : system.LinkFor p first second) (inFirst : first ∈ copied) :
    system.LinkFor q first second := by
  obtain ⟨restriction, mentioned, mentioned', notP⟩ := link
  refine ⟨restriction, mentioned, mentioned', fun inQ => notHeld ?_⟩
  exact isCopy.isGroup.closed first inFirst q (Finset.mem_erase.mpr ⟨qOther, qLive⟩)
    ⟨restriction, mentioned, inQ, notP⟩

/-- **Leaving a copy group inside another group reaches its replicated component**: a link out of the copy group goes
through a restriction its replicated component mentions, or to that component. -/
theorem IsCopy.exit_holds {q : ι} {outer : Finset ι} (isCopy : system.IsCopy live p copied) (qOther : q ≠ p)
    (outerGroup : system.IsGroup live q outer) {member : ι} (inOuter : member ∈ outer) (inCopied : member ∈ copied)
    (notInside : ¬ outer ⊆ copied) : p ∈ outer := by
  obtain ⟨outside, inOutside, notCopied⟩ := Finset.not_subset.mp notInside
  have leaves : ∀ last, system.LinkedIn q outer member last → last ∉ copied → p ∈ outer := by
    intro last linked notIn
    induction linked with
    | refl => exact absurd inCopied notIn
    | @tail middle next _ step reached =>
        obtain ⟨inMiddle, inNext, link⟩ := step
        by_cases middleCopied : middle ∈ copied
        · by_cases isP : next = p
          · exact isP ▸ inNext
          · obtain ⟨restriction, mentioned, mentioned', notQ⟩ := link
            by_cases mentionedByP : restriction ∈ system.mentions p
            · exact outerGroup.closed middle inMiddle p
                (Finset.mem_erase.mpr ⟨qOther.symm, isCopy.isLive⟩) ⟨restriction, mentioned, mentionedByP, notQ⟩
            · exact absurd (isCopy.isGroup.closed middle middleCopied next
                (Finset.mem_erase.mpr ⟨isP, (Finset.mem_erase.mp (outerGroup.subset inNext)).2⟩)
                ⟨restriction, mentioned, mentioned', mentionedByP⟩) notIn
        · exact reached middleCopied
  exact leaves outside (outerGroup.linked member inOuter outside inOutside) notCopied

/-- **A group meeting a copy group it does not lie in holds the copy group and its replicated component.** -/
theorem IsCopy.meets {q : ι} {outer : Finset ι} (isCopy : system.IsCopy live p copied) (qLive : q ∈ live \ copied)
    (qOther : q ≠ p) (outerGroup : system.IsGroup live q outer) {member : ι} (inBoth : member ∈ outer ∩ copied)
    (notInside : ¬ outer ⊆ copied) : p ∈ outer ∧ copied ⊆ outer := by
  obtain ⟨qInLive, qNotHeld⟩ := Finset.mem_sdiff.mp qLive
  obtain ⟨inOuter, inCopied⟩ := Finset.mem_inter.mp inBoth
  have relink : ∀ last, system.LinkedIn p copied member last → system.LinkedIn q (live.erase q) member last := by
    intro last path
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ step reached =>
        obtain ⟨inFirst, inSecond, link⟩ := step
        refine reached.tail ⟨?_, ?_, isCopy.link_for qInLive qOther qNotHeld link inFirst⟩
        · exact Finset.mem_erase.mpr ⟨fun equal => qNotHeld (equal ▸ inFirst),
            (Finset.mem_erase.mp (isCopy.isGroup.subset inFirst)).2⟩
        · exact Finset.mem_erase.mpr ⟨fun equal => qNotHeld (equal ▸ inSecond),
            (Finset.mem_erase.mp (isCopy.isGroup.subset inSecond)).2⟩
  exact ⟨isCopy.exit_holds qOther outerGroup inOuter inCopied notInside, fun other inOther =>
    outerGroup.reach inOuter (relink other (isCopy.isGroup.linked member inCopied other inOther))⟩

/-- **A group holding a copy group and its replicated component is still a group without the copy group.** -/
theorem IsCopy.group_rest {q : ι} {outer : Finset ι} (isCopy : system.IsCopy live p copied) (qOther : q ≠ p)
    (outerGroup : system.IsGroup live q outer) (pIn : p ∈ outer) :
    system.IsGroup (live \ copied) q (outer \ copied) := by
  have pRest : p ∈ outer \ copied := Finset.mem_sdiff.mpr ⟨pIn, isCopy.isGroup.not_mem⟩
  -- every member of the rest is linked to `p` inside the rest
  have toP : ∀ other ∈ outer \ copied, system.LinkedIn q (outer \ copied) p other := by
    intro other inOther
    obtain ⟨inOuter, notCopied⟩ := Finset.mem_sdiff.mp inOther
    have path := outerGroup.linked p pIn other inOuter
    have general : ∀ last, system.LinkedIn q outer p last → last ∉ copied →
        system.LinkedIn q (outer \ copied) p last := by
      intro last linked notIn
      induction linked with
      | refl => exact Relation.ReflTransGen.refl
      | @tail middle next _ step reached =>
          obtain ⟨inMiddle, inNext, link⟩ := step
          have nextRest : next ∈ outer \ copied := Finset.mem_sdiff.mpr ⟨inNext, notIn⟩
          by_cases middleCopied : middle ∈ copied
          · -- leaving the copy group: the restriction is mentioned by `p`, or the next component is `p`
            by_cases isP : next = p
            · subst isP
              exact Relation.ReflTransGen.refl
            · obtain ⟨restriction, mentioned, mentioned', notQ⟩ := link
              by_cases mentionedByP : restriction ∈ system.mentions p
              · exact Relation.ReflTransGen.single ⟨pRest, nextRest, restriction, mentionedByP, mentioned', notQ⟩
              · exact absurd (isCopy.isGroup.closed middle middleCopied next
                  (Finset.mem_erase.mpr ⟨isP, (Finset.mem_erase.mp (outerGroup.subset inNext)).2⟩)
                  ⟨restriction, mentioned, mentioned', mentionedByP⟩) notIn
          · exact (reached middleCopied).tail ⟨Finset.mem_sdiff.mpr ⟨inMiddle, middleCopied⟩, nextRest, link⟩
    exact general other path notCopied
  refine ⟨?_, ⟨p, pRest⟩, ?_, ?_⟩
  · intro other inOther
    obtain ⟨inOuter, notCopied⟩ := Finset.mem_sdiff.mp inOther
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (outerGroup.subset inOuter)
    exact Finset.mem_erase.mpr ⟨different, Finset.mem_sdiff.mpr ⟨inLive, notCopied⟩⟩
  · intro first inFirst second inSecond
    exact (toP first inFirst).symm.trans (toP second inSecond)
  · intro first inFirst second inSecond link
    obtain ⟨different, inRest⟩ := Finset.mem_erase.mp inSecond
    obtain ⟨inLive, notCopied⟩ := Finset.mem_sdiff.mp inRest
    exact Finset.mem_sdiff.mpr ⟨outerGroup.closed first (Finset.mem_sdiff.mp inFirst).1 second
      (Finset.mem_erase.mpr ⟨different, inLive⟩) link, notCopied⟩

/-- **A group missing a copy group stays a group without it.** -/
theorem IsGroup.rest_of_disjoint {q : ι} {outer : Finset ι} (outerGroup : system.IsGroup live q outer)
    (disjoint : Disjoint outer copied) : system.IsGroup (live \ copied) q outer := by
  refine ⟨?_, outerGroup.nonempty, outerGroup.linked, ?_⟩
  · intro other inOther
    obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (outerGroup.subset inOther)
    exact Finset.mem_erase.mpr ⟨different, Finset.mem_sdiff.mpr ⟨inLive,
      Finset.disjoint_left.mp disjoint inOther⟩⟩
  · intro first inFirst second inSecond link
    obtain ⟨different, inRest⟩ := Finset.mem_erase.mp inSecond
    exact outerGroup.closed first inFirst second
      (Finset.mem_erase.mpr ⟨different, (Finset.mem_sdiff.mp inRest).1⟩) link

/-- **Every group without a copy group comes from a group with it.** -/
theorem IsGroup.from_rest {q : ι} {rest : Finset ι} (restGroup : system.IsGroup (live \ copied) q rest)
    {outer : Finset ι} (outerGroup : system.IsGroup live q outer) {member : ι} (inRest : member ∈ rest)
    (inOuter : member ∈ outer) : rest ⊆ outer := by
  intro other inOther
  exact outerGroup.reach inOuter ((restGroup.linked member inRest other inOther).mono fun element inElement =>
    by
      obtain ⟨different, inLive⟩ := Finset.mem_erase.mp (restGroup.subset inElement)
      exact Finset.mem_erase.mpr ⟨different, (Finset.mem_sdiff.mp inLive).1⟩)

/-- **The group of a component among the others**: everything linked to it. -/
theorem IsGroup.exists_of_mem {q member : ι} (inLive : member ∈ live.erase q) :
    ∃ group, system.IsGroup live q group ∧ member ∈ group := by
  classical
  let group := (live.erase q).filter fun other => system.LinkedIn q (live.erase q) member other
  have reachable : ∀ other, other ∈ group ↔ other ∈ live.erase q ∧ system.LinkedIn q (live.erase q) member other :=
    fun other => Finset.mem_filter
  -- a path from the member stays among the members of the group
  have stays : ∀ last, system.LinkedIn q (live.erase q) member last → system.LinkedIn q group member last := by
    intro last path
    induction path with
    | refl => exact Relation.ReflTransGen.refl
    | @tail middle next before step reached =>
        obtain ⟨inMiddle, inNext, link⟩ := step
        exact reached.tail ⟨(reachable middle).mpr ⟨inMiddle, before⟩,
          (reachable next).mpr ⟨inNext, before.tail ⟨inMiddle, inNext, link⟩⟩, link⟩
  refine ⟨group, ⟨fun other inOther => ((reachable other).mp inOther).1, ⟨member, (reachable member).mpr
    ⟨inLive, Relation.ReflTransGen.refl⟩⟩, ?_, ?_⟩, (reachable member).mpr ⟨inLive, Relation.ReflTransGen.refl⟩⟩
  · intro first inFirst second inSecond
    exact (stays first ((reachable first).mp inFirst).2).symm.trans (stays second ((reachable second).mp inSecond).2)
  · intro first inFirst second inSecond link
    obtain ⟨firstLive, firstReached⟩ := (reachable first).mp inFirst
    exact (reachable second).mpr ⟨inSecond, firstReached.tail ⟨firstLive, inSecond, link⟩⟩

/-- **A copy group of a component held by a copy group lies inside it**: the held copy mentions a restriction only
the holding copy group uses, and leaving the holding copy group would hold its replicated component, making each
replicated component lower than the other. -/
theorem IsCopy.held_inside {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole) {q : ι}
    {other : Finset ι} (isCopy : system.IsCopy live p copied) (qHeld : q ∈ copied)
    (otherCopy : system.IsCopy live q other) : other ⊆ copied := by
  have qOther : q ≠ p := fun equal => isCopy.isGroup.not_mem (equal ▸ qHeld)
  have copiedWhole : copied ⊆ whole := fun member inCopied =>
    inside (Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).2
  have otherWhole : other ⊆ whole := fun member inOther =>
    inside (Finset.mem_erase.mp (otherCopy.isGroup.subset inOther)).2
  have pWhole := inside isCopy.isLive
  have qWhole := inside otherCopy.isLive
  -- `q` mentions a restriction `p` does not; otherwise `q` alone would be the holding copy group
  obtain ⟨restriction, mentionedByQ, notP⟩ : ∃ restriction ∈ system.mentions q,
      restriction ∉ system.mentions p := by
    by_contra none
    have within : system.mentions q ⊆ system.mentions p := fun restriction mentioned =>
      by_contra fun notMentioned => none ⟨restriction, mentioned, notMentioned⟩
    have single : copied = {q} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨qHeld, fun other inOther => ?_⟩
      rcases Relation.ReflTransGen.cases_head (isCopy.isGroup.linked q qHeld other inOther) with
        equal | ⟨next, step, _⟩
      · exact equal.symm
      · obtain ⟨-, -, restriction', mentioned, -, notMentioned⟩ := step
        exact absurd (within mentioned) notMentioned
    exact laws.notLone q qWhole p pWhole qOther otherCopy.isReplicated isCopy.isReplicated within
      (single ▸ isCopy.isCopy)
  -- the copy of `q` mentions that restriction, through a member that the holding copy group holds
  obtain ⟨member, inOther, mentionedByMember⟩ := laws.free other otherWhole q qWhole otherCopy.isGroup.not_mem
    otherCopy.isReplicated otherCopy.isCopy restriction mentionedByQ
  have memberLive := Finset.mem_erase.mp (otherCopy.isGroup.subset inOther)
  have memberNotP : member ≠ p := fun equal => notP (equal ▸ mentionedByMember)
  have memberCopied : member ∈ copied := isCopy.isGroup.closed q qHeld member
    (Finset.mem_erase.mpr ⟨memberNotP, memberLive.2⟩) ⟨restriction, mentionedByQ, mentionedByMember, notP⟩
  by_contra notInside
  have pHeld := isCopy.exit_holds qOther otherCopy.isGroup inOther memberCopied notInside
  exact absurd (laws.lower copied copiedWhole p pWhole isCopy.isGroup.not_mem q isCopy.isReplicated isCopy.isCopy
      qHeld otherCopy.isReplicated)
    (Nat.lt_asymm (laws.lower other otherWhole q qWhole otherCopy.isGroup.not_mem p otherCopy.isReplicated
      otherCopy.isCopy pHeld isCopy.isReplicated))

/-- **A copy group not inside the removed one stays a copy group without it.** -/
theorem IsCopy.rest_copy {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole) {q : ι}
    {outer : Finset ι} (isCopy : system.IsCopy live p copied)
    (outerCopy : system.IsCopy live q outer) (notInside : ¬ outer ⊆ copied) :
    system.IsCopy (live \ copied) q (outer \ copied) := by
  have qRest : q ∈ live \ copied := Finset.mem_sdiff.mpr ⟨outerCopy.isLive, fun qHeld =>
    notInside (isCopy.held_inside laws inside qHeld outerCopy)⟩
  by_cases meet : (outer ∩ copied).Nonempty
  · obtain ⟨member, inBoth⟩ := meet
    by_cases same : q = p
    · subst same
      exact absurd (outerCopy.isGroup.eq_of_mem isCopy.isGroup (Finset.mem_inter.mp inBoth).1
        (Finset.mem_inter.mp inBoth).2 ▸ Finset.Subset.refl outer) notInside
    obtain ⟨pIn, -⟩ := isCopy.meets qRest same outerCopy.isGroup inBoth notInside
    exact ⟨qRest, outerCopy.isReplicated, isCopy.group_rest same outerCopy.isGroup pIn,
      (laws.inner live inside p copied q outer isCopy outerCopy.isLive outerCopy.isReplicated outerCopy.isGroup same
        (isCopy.meets qRest same outerCopy.isGroup inBoth notInside).2 pIn).mp outerCopy.isCopy⟩
  · have disjoint : Disjoint outer copied := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp meet)
    rw [Finset.sdiff_eq_self_of_disjoint disjoint]
    exact ⟨qRest, outerCopy.isReplicated, outerCopy.isGroup.rest_of_disjoint disjoint, outerCopy.isCopy⟩

/-- **Every copy group without the removed one comes from a copy group with it.** -/
theorem IsCopy.from_rest {whole : Finset ι} (laws : system.Laws whole) (inside : live ⊆ whole) {q : ι}
    {rest : Finset ι} (isCopy : system.IsCopy live p copied)
    (restCopy : system.IsCopy (live \ copied) q rest) :
    ∃ outer, system.IsCopy live q outer ∧ rest = outer \ copied := by
  obtain ⟨qLive, qNotHeld⟩ := Finset.mem_sdiff.mp restCopy.isLive
  obtain ⟨member, inRest⟩ := restCopy.isGroup.nonempty
  have memberRest := Finset.mem_erase.mp (restCopy.isGroup.subset inRest)
  obtain ⟨memberLive, memberNotCopied⟩ := Finset.mem_sdiff.mp memberRest.2
  obtain ⟨outer, outerGroup, inOuter⟩ := IsGroup.exists_of_mem (system := system)
    (Finset.mem_erase.mpr ⟨memberRest.1, memberLive⟩)
  have notInside : ¬ outer ⊆ copied := fun inside => memberNotCopied (inside inOuter)
  by_cases meet : (outer ∩ copied).Nonempty
  · obtain ⟨shared, inBoth⟩ := meet
    by_cases same : q = p
    · subst same
      exact absurd (outerGroup.eq_of_mem isCopy.isGroup (Finset.mem_inter.mp inBoth).1
        (Finset.mem_inter.mp inBoth).2 ▸ inOuter) memberNotCopied
    obtain ⟨pIn, outerInside⟩ := isCopy.meets restCopy.isLive same outerGroup inBoth notInside
    have restGroup := isCopy.group_rest same outerGroup pIn
    have equal : rest = outer \ copied := restCopy.isGroup.eq_of_mem restGroup inRest
      (Finset.mem_sdiff.mpr ⟨inOuter, memberNotCopied⟩)
    refine ⟨outer, ⟨qLive, restCopy.isReplicated, outerGroup, ?_⟩, equal⟩
    exact (laws.inner live inside p copied q outer isCopy qLive restCopy.isReplicated outerGroup same outerInside
      pIn).mpr
      (equal ▸ restCopy.isCopy)
  · have disjoint : Disjoint outer copied := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp meet)
    have equal : rest = outer := restCopy.isGroup.eq_of_mem (outerGroup.rest_of_disjoint disjoint) inRest inOuter
    refine ⟨outer, ⟨qLive, restCopy.isReplicated, outerGroup, equal ▸ restCopy.isCopy⟩, ?_⟩
    rw [Finset.sdiff_eq_self_of_disjoint disjoint, equal]

end Removal

/-! ## The components absorption removes -/

/-- **The components of some copy group.** -/
noncomputable def copies (live : Finset ι) : Finset ι := by
  classical
  exact live.filter fun member => ∃ q group, system.IsCopy live q group ∧ member ∈ group

theorem mem_copies {live : Finset ι} {member : ι} :
    member ∈ system.copies live ↔ member ∈ live ∧ ∃ q group, system.IsCopy live q group ∧ member ∈ group := by
  classical
  unfold copies
  simp only [Finset.mem_filter]

theorem IsCopy.subset_copies {live : Finset ι} {p : ι} {copied : Finset ι} (isCopy : system.IsCopy live p copied) :
    copied ⊆ system.copies live := fun _ inCopied =>
  system.mem_copies.mpr ⟨(Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).2, p, copied, isCopy, inCopied⟩

/-- **Removing a copy group removes exactly itself from the copies.** -/
theorem removed_copies {whole : Finset ι} (laws : system.Laws whole) {live : Finset ι}
    (inside : live ⊆ whole) {p : ι} {copied : Finset ι} (isCopy : system.IsCopy live p copied) : system.copies (live \ copied) = system.copies live \ copied := by
  ext member
  rw [Finset.mem_sdiff, system.mem_copies, system.mem_copies, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨inLive, notCopied⟩, q, rest, restCopy, inRest⟩
    obtain ⟨outer, outerCopy, rfl⟩ := isCopy.from_rest laws inside restCopy
    exact ⟨⟨inLive, q, outer, outerCopy, (Finset.mem_sdiff.mp inRest).1⟩, notCopied⟩
  · rintro ⟨⟨inLive, q, outer, outerCopy, inOuter⟩, notCopied⟩
    exact ⟨⟨inLive, notCopied⟩, q, outer \ copied, isCopy.rest_copy laws inside outerCopy fun within =>
      notCopied (within inOuter), Finset.mem_sdiff.mpr ⟨inOuter, notCopied⟩⟩

/-- **Absorbing until no copy group is left**: removing copy groups one by one. -/
inductive Absorbs : Finset ι → Finset ι → Prop
  | done {live : Finset ι} : (∀ p group, ¬ system.IsCopy live p group) → Absorbs live live
  | step {live final : Finset ι} {p : ι} {copied : Finset ι} : system.IsCopy live p copied →
      Absorbs (live \ copied) final → Absorbs live final

/-- **Removing copy groups one by one**, not necessarily until none is left. -/
inductive Removes : Finset ι → Finset ι → Prop
  | refl {live : Finset ι} : Removes live live
  | step {live rest : Finset ι} {p : ι} {copied : Finset ι} : system.IsCopy live p copied →
      Removes (live \ copied) rest → Removes live rest

/-- Removing some copy groups and then absorbing is absorbing. -/
theorem Removes.absorbs {live rest final : Finset ι} (removes : system.Removes live rest)
    (absorbs : system.Absorbs rest final) : system.Absorbs live final := by
  induction removes with
  | refl => exact absorbs
  | step isCopy _ recurse => exact .step isCopy (recurse absorbs)

/-- **Absorption has one result**: every way of removing copy groups until none is left removes the copies. -/
theorem Absorbs.eq {whole : Finset ι} (laws : system.Laws whole) {live final : Finset ι}
    (inside : live ⊆ whole) (absorbs : system.Absorbs live final) : final = live \ system.copies live := by
  induction absorbs with
  | @done live none =>
      have empty : system.copies live = ∅ := by
        ext member
        simp only [system.mem_copies, Finset.notMem_empty, iff_false, not_and, not_exists]
        intro _ q group isCopy
        exact absurd isCopy (none q group)
      rw [empty, Finset.sdiff_empty]
  | @step live final p copied isCopy _ reached =>
      rw [reached (Finset.sdiff_subset.trans inside), removed_copies laws inside isCopy]
      ext member
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨inLive, notCopied⟩, notRest⟩
        exact ⟨inLive, fun inCopies => notRest ⟨inCopies, notCopied⟩⟩
      · rintro ⟨inLive, notCopies⟩
        exact ⟨⟨inLive, fun inCopied => notCopies (isCopy.subset_copies inCopied)⟩, fun ⟨inCopies, _⟩ =>
          notCopies inCopies⟩

/-! ## Isomorphic systems -/

section Iso

variable {κ : Type} [DecidableEq κ]

/-- **An isomorphism of absorption systems** on live components: a map of components injective on them, and an
injective map of restrictions, carrying mentions, replication and copies. -/
structure Iso (system : System ι) (other : System κ) (live : Finset ι) (map : ι → κ) (relabel : Nat → Nat) :
    Prop where
  injective : ∀ first ∈ live, ∀ second ∈ live, map first = map second → first = second
  relabelInjective : Function.Injective relabel
  mentions : ∀ member ∈ live, other.mentions (map member) = (system.mentions member).image relabel
  replicated : ∀ member ∈ live, other.replicated (map member) ↔ system.replicated member
  copy : ∀ group ⊆ live, ∀ p ∈ live, system.replicated p → p ∉ group →
    (other.copy (group.image map) (map p) ↔ system.copy group p)
  height : ∀ member ∈ live, system.replicated member → other.height (map member) = system.height member

variable {system : System ι} {other : System κ} {live : Finset ι} {map : ι → κ} {relabel : Nat → Nat}

omit [DecidableEq ι] in
theorem Iso.linkFor (iso : Iso system other live map relabel) {p first second : ι} (pLive : p ∈ live)
    (firstLive : first ∈ live) (secondLive : second ∈ live) :
    other.LinkFor (map p) (map first) (map second) ↔ system.LinkFor p first second := by
  simp only [LinkFor, iso.mentions _ pLive, iso.mentions _ firstLive, iso.mentions _ secondLive, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨restriction, inFirst, rfl⟩, ⟨other', inSecond, same⟩, notP⟩
    have equal : other' = restriction := iso.relabelInjective same
    exact ⟨restriction, inFirst, equal ▸ inSecond, fun inP => notP ⟨restriction, inP, rfl⟩⟩
  · rintro ⟨restriction, inFirst, inSecond, notP⟩
    refine ⟨relabel restriction, ⟨restriction, inFirst, rfl⟩, ⟨restriction, inSecond, rfl⟩, ?_⟩
    rintro ⟨other', inP, same⟩
    have equal : other' = restriction := iso.relabelInjective same
    exact notP (equal ▸ inP)

omit [DecidableEq ι] in
theorem Iso.mono (iso : Iso system other live map relabel) {smaller : Finset ι} (subset : smaller ⊆ live) :
    Iso system other smaller map relabel where
  injective := fun first inFirst second inSecond => iso.injective first (subset inFirst) second (subset inSecond)
  relabelInjective := iso.relabelInjective
  mentions := fun member inMember => iso.mentions member (subset inMember)
  replicated := fun member inMember => iso.replicated member (subset inMember)
  copy := fun group inside p pLive replicated notIn => iso.copy group (inside.trans subset) p (subset pLive)
    replicated notIn
  height := fun member inMember => iso.height member (subset inMember)

omit [DecidableEq ι] in
theorem Iso.mem_image (iso : Iso system other live map relabel) {set : Finset ι} (subset : set ⊆ live)
    {member : ι} (memberLive : member ∈ live) : map member ∈ set.image map ↔ member ∈ set := by
  constructor
  · intro inImage
    obtain ⟨original, inSet, same⟩ := Finset.mem_image.mp inImage
    rwa [← iso.injective original (subset inSet) member memberLive same]
  · intro inSet
    exact Finset.mem_image_of_mem map inSet

theorem Iso.image_erase (iso : Iso system other live map relabel) {p : ι} (pLive : p ∈ live) :
    (live.erase p).image map = (live.image map).erase (map p) := by
  ext target
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨original, ⟨different, inLive⟩, rfl⟩
    exact ⟨fun same => different (iso.injective original inLive p pLive same), original, inLive, rfl⟩
  · rintro ⟨different, original, inLive, rfl⟩
    exact ⟨original, ⟨fun same => different (same ▸ rfl), inLive⟩, rfl⟩

omit [DecidableEq ι] in
/-- **Linked inside a set, through the isomorphism.** -/
theorem Iso.linkedIn (iso : Iso system other live map relabel) {p : ι} (pLive : p ∈ live) {set : Finset ι}
    (subset : set ⊆ live) {first second : ι} (linked : system.LinkedIn p set first second) :
    other.LinkedIn (map p) (set.image map) (map first) (map second) := by
  induction linked with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step reached =>
      obtain ⟨inFirst, inSecond, link⟩ := step
      exact reached.tail ⟨Finset.mem_image_of_mem map inFirst, Finset.mem_image_of_mem map inSecond,
        (iso.linkFor pLive (subset inFirst) (subset inSecond)).mpr link⟩

omit [DecidableEq ι] in
/-- Linked inside an image, back through the isomorphism. -/
theorem Iso.linkedIn_back (iso : Iso system other live map relabel) {p : ι} (pLive : p ∈ live) {set : Finset ι}
    (subset : set ⊆ live) {first : ι} (firstIn : first ∈ set) :
    ∀ target, other.LinkedIn (map p) (set.image map) (map first) target →
      ∃ last ∈ set, map last = target ∧ system.LinkedIn p set first last := by
  intro target linked
  induction linked with
  | refl => exact ⟨first, firstIn, rfl, Relation.ReflTransGen.refl⟩
  | @tail middle next _ step reached =>
      obtain ⟨last, lastIn, rfl, linkedLast⟩ := reached
      obtain ⟨-, inNext, link⟩ := step
      obtain ⟨original, originalIn, rfl⟩ := Finset.mem_image.mp inNext
      exact ⟨original, originalIn, rfl, linkedLast.tail ⟨lastIn, originalIn,
        (iso.linkFor pLive (subset lastIn) (subset originalIn)).mp link⟩⟩

/-- **Groups correspond through the isomorphism.** -/
theorem Iso.isGroup_iff (iso : Iso system other live map relabel) {p : ι} (pLive : p ∈ live) {group : Finset ι}
    (subset : group ⊆ live) :
    other.IsGroup (live.image map) (map p) (group.image map) ↔ system.IsGroup live p group := by
  constructor
  · intro isGroup
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro member inGroup
      have imageIn := isGroup.subset (Finset.mem_image_of_mem map inGroup)
      rw [← iso.image_erase pLive] at imageIn
      exact (iso.mem_image (Finset.erase_subset p live) (subset inGroup)).mp imageIn
    · obtain ⟨target, inImage⟩ := isGroup.nonempty
      obtain ⟨original, inGroup, -⟩ := Finset.mem_image.mp inImage
      exact ⟨original, inGroup⟩
    · intro first inFirst second inSecond
      obtain ⟨last, lastIn, same, linked⟩ := iso.linkedIn_back pLive subset inFirst (map second)
        (isGroup.linked _ (Finset.mem_image_of_mem map inFirst) _ (Finset.mem_image_of_mem map inSecond))
      rwa [← iso.injective last (subset lastIn) second (subset inSecond) same]
    · intro first inFirst second inSecond link
      have secondLive := Finset.mem_erase.mp inSecond
      have imageIn : map second ∈ (live.image map).erase (map p) := by
        rw [← iso.image_erase pLive]
        exact Finset.mem_image_of_mem map inSecond
      have reached := isGroup.closed _ (Finset.mem_image_of_mem map inFirst) _ imageIn
        ((iso.linkFor pLive (subset inFirst) secondLive.2).mpr link)
      exact (iso.mem_image subset secondLive.2).mp reached
  · intro isGroup
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro target inImage
      obtain ⟨original, inGroup, rfl⟩ := Finset.mem_image.mp inImage
      rw [← iso.image_erase pLive]
      exact Finset.mem_image_of_mem map (isGroup.subset inGroup)
    · obtain ⟨member, inGroup⟩ := isGroup.nonempty
      exact ⟨map member, Finset.mem_image_of_mem map inGroup⟩
    · intro first inFirst second inSecond
      obtain ⟨first', inFirst', rfl⟩ := Finset.mem_image.mp inFirst
      obtain ⟨second', inSecond', rfl⟩ := Finset.mem_image.mp inSecond
      exact iso.linkedIn pLive subset (isGroup.linked first' inFirst' second' inSecond')
    · intro first inFirst target inTarget link
      obtain ⟨first', inFirst', rfl⟩ := Finset.mem_image.mp inFirst
      rw [← iso.image_erase pLive] at inTarget
      obtain ⟨second', inSecond', rfl⟩ := Finset.mem_image.mp inTarget
      have secondLive := Finset.mem_erase.mp inSecond'
      exact Finset.mem_image_of_mem map (isGroup.closed first' inFirst' second' inSecond'
        ((iso.linkFor pLive (subset inFirst') secondLive.2).mp link))

/-- **Copy groups correspond through the isomorphism.** -/
theorem Iso.isCopy_iff (iso : Iso system other live map relabel) {p : ι} (pLive : p ∈ live) {group : Finset ι}
    (subset : group ⊆ live) :
    other.IsCopy (live.image map) (map p) (group.image map) ↔ system.IsCopy live p group := by
  constructor
  · intro isCopy
    have isGroup := (iso.isGroup_iff pLive subset).mp isCopy.isGroup
    have replicated := (iso.replicated p pLive).mp isCopy.isReplicated
    exact ⟨pLive, replicated, isGroup, (iso.copy group subset p pLive replicated isGroup.not_mem).mp isCopy.isCopy⟩
  · intro isCopy
    exact ⟨Finset.mem_image_of_mem map pLive, (iso.replicated p pLive).mpr isCopy.isReplicated,
      (iso.isGroup_iff pLive subset).mpr isCopy.isGroup,
      (iso.copy group subset p pLive isCopy.isReplicated isCopy.isGroup.not_mem).mpr isCopy.isCopy⟩

/-- **The copies correspond through the isomorphism.** -/
theorem Iso.copies (iso : Iso system other live map relabel) :
    other.copies (live.image map) = (system.copies live).image map := by
  ext target
  constructor
  · intro inCopies
    obtain ⟨inImage, q', group', isCopy', inGroup'⟩ := other.mem_copies.mp inCopies
    obtain ⟨member, memberLive, rfl⟩ := Finset.mem_image.mp inImage
    obtain ⟨q, qLive, rfl⟩ := Finset.mem_image.mp isCopy'.isLive
    have groupInLive : ∀ target ∈ group', ∃ original ∈ live, map original = target := by
      intro target inTarget
      have inErased := isCopy'.isGroup.subset inTarget
      rw [← iso.image_erase qLive] at inErased
      obtain ⟨original, inOriginal, same⟩ := Finset.mem_image.mp inErased
      exact ⟨original, (Finset.mem_erase.mp inOriginal).2, same⟩
    classical
    set preimage := live.filter fun original => map original ∈ group'
    have imageIs : preimage.image map = group' := by
      ext target
      simp only [Finset.mem_image, Finset.mem_filter, preimage]
      constructor
      · rintro ⟨original, ⟨-, inGroup⟩, rfl⟩
        exact inGroup
      · intro inTarget
        obtain ⟨original, inOriginal, rfl⟩ := groupInLive target inTarget
        exact ⟨original, ⟨inOriginal, inTarget⟩, rfl⟩
    have preimageLive : preimage ⊆ live := Finset.filter_subset _ _
    rw [← imageIs] at isCopy' inGroup'
    have isCopy := (iso.isCopy_iff qLive preimageLive).mp isCopy'
    exact Finset.mem_image.mpr ⟨member, system.mem_copies.mpr ⟨memberLive, q, preimage, isCopy,
      (iso.mem_image preimageLive memberLive).mp inGroup'⟩, rfl⟩
  · intro inImage
    obtain ⟨member, inCopies, rfl⟩ := Finset.mem_image.mp inImage
    obtain ⟨memberLive, q, group, isCopy, inGroup⟩ := system.mem_copies.mp inCopies
    have groupLive : group ⊆ live := fun element inElement =>
      (Finset.mem_erase.mp (isCopy.isGroup.subset inElement)).2
    exact other.mem_copies.mpr ⟨Finset.mem_image_of_mem map memberLive, map q, group.image map,
      (iso.isCopy_iff isCopy.isLive groupLive).mpr isCopy, Finset.mem_image_of_mem map inGroup⟩

omit [DecidableEq ι] in
/-- **A set of images of live components is the image of its preimage.** -/
theorem preimage_of_image {set : Finset κ} (inside : set ⊆ live.image map) :
    ∃ original ⊆ live, original.image map = set := by
  classical
  refine ⟨live.filter fun member => map member ∈ set, Finset.filter_subset _ _, ?_⟩
  ext target
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨member, ⟨-, inSet⟩, rfl⟩
    exact inSet
  · intro inSet
    obtain ⟨member, memberLive, rfl⟩ := Finset.mem_image.mp (inside inSet)
    exact ⟨member, ⟨memberLive, inSet⟩, rfl⟩

theorem Iso.image_sdiff (iso : Iso system other live map relabel) {first second : Finset ι} (firstLive : first ⊆ live)
    (secondLive : second ⊆ live) : (first \ second).image map = first.image map \ second.image map := by
  ext target
  simp only [Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨member, ⟨inFirst, notSecond⟩, rfl⟩
    refine ⟨⟨member, inFirst, rfl⟩, ?_⟩
    rintro ⟨other', inSecond, same⟩
    exact notSecond (iso.injective other' (secondLive inSecond) member (firstLive inFirst) same ▸ inSecond)
  · rintro ⟨⟨member, inFirst, rfl⟩, notSecond⟩
    exact ⟨member, ⟨inFirst, fun inSecond => notSecond ⟨member, inSecond, rfl⟩⟩, rfl⟩

/-- **The laws carry across an isomorphism.** -/
theorem Iso.laws (iso : Iso system other live map relabel) (laws : system.Laws live) :
    other.Laws (live.image map) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro group' inside p' pIn notIn replicated copied restriction' mentioned
    obtain ⟨group, groupLive, rfl⟩ := preimage_of_image inside
    obtain ⟨p, pLive, rfl⟩ := Finset.mem_image.mp pIn
    rw [iso.mentions p pLive] at mentioned
    obtain ⟨restriction, mentionedByP, rfl⟩ := Finset.mem_image.mp mentioned
    have pNot : p ∉ group := fun inGroup => notIn (Finset.mem_image_of_mem map inGroup)
    have pReplicated := (iso.replicated p pLive).mp replicated
    obtain ⟨member, inGroup, mentionedByMember⟩ := laws.free group groupLive p pLive pNot pReplicated
      ((iso.copy group groupLive p pLive pReplicated pNot).mp copied) restriction mentionedByP
    refine ⟨map member, Finset.mem_image_of_mem map inGroup, ?_⟩
    rw [iso.mentions member (groupLive inGroup)]
    exact Finset.mem_image_of_mem relabel mentionedByMember
  · intro q' qIn p' pIn different qReplicated pReplicated within copied
    obtain ⟨q, qLive, rfl⟩ := Finset.mem_image.mp qIn
    obtain ⟨p, pLive, rfl⟩ := Finset.mem_image.mp pIn
    have singleLive : ({q} : Finset ι) ⊆ live := Finset.singleton_subset_iff.mpr qLive
    rw [show ({map q} : Finset κ) = ({q} : Finset ι).image map from by simp] at copied
    have qp : q ≠ p := fun same => different (by rw [same])
    have pReplicated' := (iso.replicated p pLive).mp pReplicated
    refine laws.notLone q qLive p pLive qp ((iso.replicated q qLive).mp qReplicated) pReplicated' ?_
      ((iso.copy {q} singleLive p pLive pReplicated' (by simpa using qp.symm)).mp copied)
    intro restriction mentioned
    have imageIn : relabel restriction ∈ other.mentions (map p) := by
      apply within
      rw [iso.mentions q qLive]
      exact Finset.mem_image_of_mem relabel mentioned
    rw [iso.mentions p pLive] at imageIn
    obtain ⟨original, inP, same⟩ := Finset.mem_image.mp imageIn
    rwa [← iso.relabelInjective same]
  · intro group' inside p' pIn notIn q' replicated copied qIn qReplicated
    obtain ⟨group, groupLive, rfl⟩ := preimage_of_image inside
    obtain ⟨p, pLive, rfl⟩ := Finset.mem_image.mp pIn
    obtain ⟨q, inGroup, rfl⟩ := Finset.mem_image.mp qIn
    have pNot : p ∉ group := fun inGroup => notIn (Finset.mem_image_of_mem map inGroup)
    have pReplicated := (iso.replicated p pLive).mp replicated
    have qReplicated' := (iso.replicated q (groupLive inGroup)).mp qReplicated
    rw [iso.height p pLive pReplicated, iso.height q (groupLive inGroup) qReplicated']
    exact laws.lower group groupLive p pLive pNot q pReplicated
      ((iso.copy group groupLive p pLive pReplicated pNot).mp copied) inGroup qReplicated'
  · intro smaller' inside p' group' q' outer' isCopy' qIn qReplicated isGroup' different groupInside pIn
    obtain ⟨smaller, smallerLive, rfl⟩ := preimage_of_image inside
    have smallIso := iso.mono smallerLive
    obtain ⟨p, pSmall, rfl⟩ := Finset.mem_image.mp isCopy'.isLive
    obtain ⟨q, qSmall, rfl⟩ := Finset.mem_image.mp qIn
    have groupInSmaller : group' ⊆ smaller.image map := fun target inTarget =>
      (Finset.mem_erase.mp (isCopy'.isGroup.subset inTarget)).2
    have outerInSmaller : outer' ⊆ smaller.image map := fun target inTarget =>
      (Finset.mem_erase.mp (isGroup'.subset inTarget)).2
    obtain ⟨group, groupSmall, rfl⟩ := preimage_of_image groupInSmaller
    obtain ⟨outer, outerSmall, rfl⟩ := preimage_of_image outerInSmaller
    have isCopy := (smallIso.isCopy_iff pSmall groupSmall).mp isCopy'
    have isGroup := (smallIso.isGroup_iff qSmall outerSmall).mp isGroup'
    have qp : q ≠ p := fun equal => different (by rw [equal])
    have inside' : group ⊆ outer := fun member inGroup => (smallIso.mem_image outerSmall (groupSmall inGroup)).mp
      (groupInside (Finset.mem_image_of_mem map inGroup))
    have pOuter : p ∈ outer := (smallIso.mem_image outerSmall pSmall).mp pIn
    have qReplicated' := (iso.replicated q (smallerLive qSmall)).mp qReplicated
    have rest := laws.inner smaller smallerLive p group q outer isCopy qSmall qReplicated' isGroup qp inside' pOuter
    have outerLive := outerSmall.trans smallerLive
    have restLive : outer \ group ⊆ live := Finset.sdiff_subset.trans outerLive
    have qNot : q ∉ outer := isGroup.not_mem
    rw [iso.copy outer outerLive q (smallerLive qSmall) qReplicated' qNot, ← smallIso.image_sdiff outerSmall groupSmall,
      iso.copy (outer \ group) restLive q (smallerLive qSmall) qReplicated' fun inRest => qNot (Finset.mem_sdiff.mp inRest).1]
    exact rest

/-- **A complete removal sequence on the image comes from one on the original.** -/
theorem Iso.absorbs {final' : Finset κ} {image : Finset κ} (absorbs : other.Absorbs image final') :
    ∀ {live : Finset ι}, Iso system other live map relabel → live.image map = image →
      ∃ final ⊆ live, system.Absorbs live final ∧ final' = final.image map := by
  induction absorbs with
  | @done image none =>
      intro live iso imageIs
      refine ⟨live, Finset.Subset.refl _, .done fun p group isCopy => ?_, imageIs.symm⟩
      have groupLive : group ⊆ live := fun member inGroup => (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2
      exact none (map p) (group.image map) (imageIs ▸ (iso.isCopy_iff isCopy.isLive groupLive).mpr isCopy)
  | @step image final' p' copied' isCopy' _ reached =>
      intro live iso imageIs
      subst imageIs
      obtain ⟨p, pLive, rfl⟩ := Finset.mem_image.mp isCopy'.isLive
      have copiedInImage : copied' ⊆ live.image map := fun target inTarget =>
        (Finset.mem_erase.mp (isCopy'.isGroup.subset inTarget)).2
      obtain ⟨copied, copiedLive, rfl⟩ := preimage_of_image copiedInImage
      have isCopy := (iso.isCopy_iff pLive copiedLive).mp isCopy'
      obtain ⟨final, finalInside, absorbs, finalIs⟩ := reached (iso.mono Finset.sdiff_subset)
        (iso.image_sdiff (Finset.Subset.refl _) copiedLive)
      exact ⟨final, finalInside.trans Finset.sdiff_subset, .step isCopy absorbs, finalIs⟩

/-- **Absorption on the image ends at the image of the original's end**, under the original's laws. -/
theorem Iso.absorbs_eq (iso : Iso system other live map relabel) {whole : Finset ι} (laws : system.Laws whole)
    (inside : live ⊆ whole) {final' : Finset κ} (absorbs : other.Absorbs (live.image map) final') :
    final' = (live \ system.copies live).image map := by
  obtain ⟨final, -, original, rfl⟩ := iso.absorbs absorbs rfl
  rw [original.eq laws inside]

section Trans

variable {μ : Type} [DecidableEq μ] {third : System μ} {map' : κ → μ} {relabel' : Nat → Nat}

omit [DecidableEq ι] in
/-- **Isomorphisms compose.** -/
theorem Iso.trans (iso : Iso system other live map relabel) (iso' : Iso other third (live.image map) map' relabel') :
    Iso system third live (map' ∘ map) (relabel' ∘ relabel) where
  injective := fun first inFirst second inSecond same =>
    iso.injective first inFirst second inSecond
      (iso'.injective _ (Finset.mem_image_of_mem map inFirst) _ (Finset.mem_image_of_mem map inSecond) same)
  relabelInjective := iso'.relabelInjective.comp iso.relabelInjective
  mentions := fun member inMember => by
    rw [Function.comp_apply, iso'.mentions _ (Finset.mem_image_of_mem map inMember), iso.mentions member inMember,
      Finset.image_image]
  replicated := fun member inMember => by
    rw [Function.comp_apply, iso'.replicated _ (Finset.mem_image_of_mem map inMember)]
    exact iso.replicated member inMember
  copy := fun group inside p pIn replicated notIn => by
    rw [← Finset.image_image, Function.comp_apply,
      iso'.copy _ (Finset.image_subset_image inside) _ (Finset.mem_image_of_mem map pIn)
        ((iso.replicated p pIn).mpr replicated) fun inImage => notIn ((iso.mem_image inside pIn).mp inImage)]
    exact iso.copy group inside p pIn replicated notIn
  height := fun member inMember replicated => by
    rw [Function.comp_apply, iso'.height _ (Finset.mem_image_of_mem map inMember)
      ((iso.replicated member inMember).mpr replicated)]
    exact iso.height member inMember replicated

end Trans

end Iso

end System

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks.CopyGroups
