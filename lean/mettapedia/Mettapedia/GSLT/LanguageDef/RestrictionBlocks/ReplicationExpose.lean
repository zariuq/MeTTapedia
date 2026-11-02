import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationAlign

/-!
# Exposing a redex in an unfolding of the canonical form

The components a redex takes may be absorbed in the canonical form of a block, into copies of replicated
components. They come back in an unfolding of the canonical form (`exposure`). Components carry a role (`Role`): the
**parts** of the redex, **anchors** (replicated components that must stay exposed, so that their copies can be
unfolded), and the **others**. A block **exposes** its parts and anchors within some number of unfoldings
(`Exposes`) when an unfolding of its canonical form within that many unfoldings holds the parts, read alike under a
renaming, and the anchors among its other components, and every context of the parts and anchors reads beside the
block's other components as it reads, renamed, beside the unfolding's other components.

Every block exposes its parts and anchors (`exposes`), by induction on its components:

- copy groups avoiding the parts and anchors are removed (`remove_avoiding`): a removed group is a copy group also
  beside any context of the parts and anchors, so the context reads the same;
- a block without copy groups exposes them in its canonical form (`exposes_base`);
- otherwise a copy group meets them, and is unfolded from its replicated component (`exposes_step`): the block
  without the group, its replicated component made an anchor, exposes its parts and anchors; unfolding the replicated
  component puts the canonical form of its copy beside them, which is that of the group's own block, and that block
  exposes the group's parts and anchors within the copy. The contexts align through both (`step_alignment`): the
  group's own restrictions are read as names past every name used and closed again.

Each part costs at most a ceiling on the heights of the replicated components, the size of their arguments'
canonical forms (`weight`): a copy group holds only lower replicated components, and unfolding it is paid by the
parts and anchors it holds (`step_weights`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex freeIn_apply)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

variable {block : ReplicationBlock}

/-! ## Components with roles -/

/-- **What a component is to an exposure**: a part of a redex, an anchor kept exposed, or another component. -/
inductive Role
  | part
  | anchor
  | other
  deriving DecidableEq

/-- The component with its role at a place, inaction past the end. -/
def taggedAt (block : ReplicationBlock) (tagged : List (Pattern × Role)) (place : Nat) : Pattern × Role :=
  tagged.getD place (.apply block.unit [], .other)

/-- The parts. -/
def partsOf (tagged : List (Pattern × Role)) : List Pattern :=
  (tagged.filter fun item => decide (item.2 = .part)).map Prod.fst

/-- The anchors. -/
def anchorsOf (tagged : List (Pattern × Role)) : List Pattern :=
  (tagged.filter fun item => decide (item.2 = .anchor)).map Prod.fst

/-- The components other than the parts. -/
def othersOf (tagged : List (Pattern × Role)) : List Pattern :=
  (tagged.filter fun item => decide (item.2 ≠ .part)).map Prod.fst

/-- **A restriction attached to the parts and anchors**: some part or anchor mentions it. -/
def Attached (tagged : List (Pattern × Role)) (index : Nat) : Prop :=
  ∃ held ∈ partsOf tagged ++ anchorsOf tagged, mentions index held = true

/-- The height of a replicated component: the size of its argument's canonical form. -/
def height (block : ReplicationBlock) (component : Pattern) : Nat :=
  size (canonicalOf block (argumentOf? component))

/-- **What exposing a component costs in unfoldings**, below a ceiling on the heights: a part at most the ceiling, an
anchor at most the heights between its own and the ceiling, another component nothing. -/
def weight (block : ReplicationBlock) (ceiling : Nat) (item : Pattern × Role) : Nat :=
  match item.2 with
  | .part => ceiling
  | .anchor => ceiling - 1 - height block item.1
  | .other => 0

/-- **A block exposes its parts and anchors within some number of unfoldings**: an unfolding of its canonical form
within that many unfoldings holds the parts, read alike under a renaming, beside its other components, among which
the anchors are read alike; the renaming keeps the names outside past the unfolding's restrictions and the
restrictions the parts and anchors mention apart and below them; and every context of the parts and anchors reads
beside the block's other components as it reads, renamed, beside the unfolding's other components. -/
def Exposes (block : ReplicationBlock) (count : Nat) (tagged : List (Pattern × Role)) (depth : Nat) : Prop :=
  ∃ (unfolded : Prenex) (relabel : Nat → Nat) (exposed rest : List Pattern),
    UnfoldsWithin block depth (normal block ⟨count, tagged.map Prod.fst⟩) unfolded ∧
    unfolded.components.Perm (exposed ++ rest) ∧
    List.Forall₂ (fun shown part => AlikeR block shown (rename relabel part)) exposed (partsOf tagged) ∧
    (∀ anchor ∈ anchorsOf tagged, ∃ shown ∈ rest, AlikeR block shown (rename relabel anchor)) ∧
    (∀ index, relabel (count + index) = unfolded.count + index) ∧
    (∀ index < count, Attached tagged index → relabel index < unfolded.count) ∧
    (∀ first < count, ∀ second < count, Attached tagged first → Attached tagged second →
      relabel first = relabel second → first = second) ∧
    ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ context, ∀ index < count, mentions index component = true → Attached tagged index) →
      normal block ⟨count, othersOf tagged ++ context⟩ =
        normal block ⟨unfolded.count, rest ++ context.map (rename relabel)⟩

theorem taggedAt_lt {tagged : List (Pattern × Role)} {place : Nat} (inside : place < tagged.length) :
    taggedAt block tagged place = tagged[place] :=
  List.getD_eq_getElem _ _ inside

theorem map_taggedAt_range (tagged : List (Pattern × Role)) :
    (List.range tagged.length).map (taggedAt block tagged) = tagged := by
  apply List.ext_getElem
  · simp
  · intro place inside _
    rw [List.getElem_map, List.getElem_range]
    exact taggedAt_lt (by simpa using inside)

theorem placeValue_fst (tagged : List (Pattern × Role)) (place : Nat) :
    placeValue block (tagged.map Prod.fst) place = (taggedAt block tagged place).1 := by
  unfold placeValue taggedAt
  exact List.getD_map tagged (.apply block.unit [], .other) Prod.fst

theorem restrictTo_tagged (count : Nat) (tagged : List (Pattern × Role)) (kept : List Nat) :
    restrictTo block ⟨count, tagged.map Prod.fst⟩ kept = ⟨count, (kept.map (taggedAt block tagged)).map Prod.fst⟩ := by
  simp only [restrictTo, List.map_map, Prenex.mk.injEq, true_and]
  exact List.map_congr_left fun place _ => placeValue_fst tagged place

theorem mem_partsOf {tagged : List (Pattern × Role)} {component : Pattern} :
    component ∈ partsOf tagged ↔ (component, Role.part) ∈ tagged := by
  simp only [partsOf, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨component', role⟩, ⟨member, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨_, ⟨member, rfl⟩, rfl⟩

theorem mem_anchorsOf {tagged : List (Pattern × Role)} {component : Pattern} :
    component ∈ anchorsOf tagged ↔ (component, Role.anchor) ∈ tagged := by
  simp only [anchorsOf, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨component', role⟩, ⟨member, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨_, ⟨member, rfl⟩, rfl⟩

theorem partsOf_perm {first second : List (Pattern × Role)} (permutation : first.Perm second) :
    (partsOf first).Perm (partsOf second) :=
  (permutation.filter _).map _

theorem anchorsOf_perm {first second : List (Pattern × Role)} (permutation : first.Perm second) :
    (anchorsOf first).Perm (anchorsOf second) :=
  (permutation.filter _).map _

theorem othersOf_perm {first second : List (Pattern × Role)} (permutation : first.Perm second) :
    (othersOf first).Perm (othersOf second) :=
  (permutation.filter _).map _

theorem partsOf_append (first second : List (Pattern × Role)) :
    partsOf (first ++ second) = partsOf first ++ partsOf second := by
  simp [partsOf, List.filter_append]

theorem anchorsOf_append (first second : List (Pattern × Role)) :
    anchorsOf (first ++ second) = anchorsOf first ++ anchorsOf second := by
  simp [anchorsOf, List.filter_append]

theorem othersOf_append (first second : List (Pattern × Role)) :
    othersOf (first ++ second) = othersOf first ++ othersOf second := by
  simp [othersOf, List.filter_append]

/-- The components other than the parts at some places, from those places. -/
theorem othersOf_places (tagged : List (Pattern × Role)) (places : List Nat) :
    othersOf (places.map (taggedAt block tagged)) =
      (places.filter fun place => decide ((taggedAt block tagged place).2 ≠ .part)).map
        fun place => (taggedAt block tagged place).1 := by
  simp only [othersOf, List.filter_map, List.map_map]
  rfl

/-! ## Related lists in another order -/

/-- **Related lists stay related in any order of the second**, the first reordered alike. -/
theorem forall₂_exists_perm {α β : Type} {relation : α → β → Prop} {first : List α} {second second' : List β}
    (related : List.Forall₂ relation first second) (permutation : second.Perm second') :
    ∃ first', first.Perm first' ∧ List.Forall₂ relation first' second' := by
  induction permutation generalizing first with
  | nil =>
      cases related
      exact ⟨[], List.Perm.refl _, .nil⟩
  | cons head _ recurse =>
      cases related with
      | cons headRelated tailRelated =>
          obtain ⟨tail', tailPerm, tailRelated'⟩ := recurse tailRelated
          exact ⟨_, tailPerm.cons _, .cons headRelated tailRelated'⟩
  | swap x y rest =>
      cases related with
      | cons yRelated tailRelated =>
          cases tailRelated with
          | cons xRelated restRelated =>
              exact ⟨_, List.Perm.swap _ _ _, .cons xRelated (.cons yRelated restRelated)⟩
  | trans _ _ firstRecurse secondRecurse =>
      obtain ⟨middle, firstPerm, middleRelated⟩ := firstRecurse related
      obtain ⟨last, secondPerm, lastRelated⟩ := secondRecurse middleRelated
      exact ⟨last, firstPerm.trans secondPerm, lastRelated⟩

/-! ## The restrictions a copy group owns -/

section Owned

variable {form : Prenex} {p : Nat} {group : Finset Nat}

theorem mem_ownOf {index : Nat} : index ∈ ownOf block form p group ↔
    index < form.count ∧ mentions index (placeValue block form.components p) = false ∧
      ∃ place ∈ group, mentions index (placeValue block form.components place) = true := by
  unfold ownOf
  rw [mem_restrictionsOf_iff]
  simp only [Finset.mem_sort]

theorem ownOf_nodup : (ownOf block form p group).Nodup := restrictionsOf_nodup _ _ _ _

theorem ownOf_lt {index : Nat} (member : index ∈ ownOf block form p group) : index < form.count :=
  (mem_ownOf.mp member).1

/-- **What a group's components mention past its own restrictions, its replicated component mentions.** -/
theorem mentions_of_group {place index : Nat} (inGroup : place ∈ group) (below : index < form.count)
    (notOwn : index ∉ ownOf block form p group)
    (mentioned : mentions index (placeValue block form.components place) = true) :
    mentions index (placeValue block form.components p) = true := by
  by_contra notMentioned
  exact notOwn (mem_ownOf.mpr ⟨below, by simpa using notMentioned, place, inGroup, mentioned⟩)

/-- **The replicated component mentions none of its copy group's own restrictions.** -/
theorem not_mentions_own_p {index : Nat} (own : index ∈ ownOf block form p group) :
    mentions index (placeValue block form.components p) = false :=
  (mem_ownOf.mp own).2.1

/-- **No live component outside a copy group and its replicated component mentions the group's own
restrictions**: it would be linked to the group. -/
theorem not_mentions_own {live : Finset Nat} (isCopy : (blockSystem block form).IsCopy live p group)
    {place index : Nat} (inLive : place ∈ live) (notGroup : place ∉ group) (notP : place ≠ p)
    (own : index ∈ ownOf block form p group) :
    mentions index (placeValue block form.components place) = false := by
  obtain ⟨below, notP', member, inGroup, memberMentions⟩ := mem_ownOf.mp own
  by_contra mentioned
  have link : (blockSystem block form).LinkFor p member place := by
    refine ⟨index, ?_, ?_, ?_⟩ <;>
      simp only [blockSystem, absorptionSystem, List.mem_toFinset, mem_usedRestrictions]
    · exact ⟨below, memberMentions⟩
    · exact ⟨below, by simpa using mentioned⟩
    · rintro ⟨-, mentionedP⟩
      rw [notP'] at mentionedP
      exact Bool.false_ne_true mentionedP
  exact notGroup (isCopy.isGroup.closed member inGroup place (Finset.mem_erase.mpr ⟨notP, inLive⟩) link)

end Owned

/-! ## Heights under renamings -/

theorem argumentOf_rename (relabel : Nat → Nat) : ∀ pattern : Pattern,
    argumentOf? (rename relabel pattern) = rename relabel (argumentOf? pattern)
  | .apply label [argument] => by simp [rename_apply, argumentOf?]
  | .apply label [] => by simp [rename_apply, argumentOf?]
  | .apply label (first :: second :: rest) => by simp [rename_apply, argumentOf?]
  | .bvar index => rfl
  | .fvar name => rfl
  | .lambda binder body => by simp [argumentOf?, rename_lambda]
  | .multiLambda arity binders body => by simp [argumentOf?, rename_multiLambda]
  | .subst body replacement => by simp [argumentOf?, rename_subst]
  | .collection kind elements rest => by simp [argumentOf?, rename_collection]

/-- **A renaming injective on a component's free names keeps its height.** -/
theorem height_rename_on (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {component : Pattern} {relabel : Nat → Nat}
    (injectiveOn : ∀ first second, FreeIn first component → FreeIn second component → relabel first = relabel second →
      first = second) :
    height block (rename relabel component) = height block component := by
  classical
  obtain ⟨relabel', injective, agree⟩ := exists_injective_on [component] relabel (fun index => FreeIn index component)
    (fun pattern member index free => by
      rw [List.mem_singleton] at member
      subst member
      exact free) injectiveOn
  unfold height
  rw [← agree component (List.mem_singleton_self _), argumentOf_rename]
  exact (below_all fresh restrictFresh (size (argumentOf? component) + 1)).sized _ (Nat.lt_succ_self _) relabel'
    injective

theorem fst_perm_parts_others (tagged : List (Pattern × Role)) :
    (tagged.map Prod.fst).Perm (partsOf tagged ++ othersOf tagged) := by
  unfold partsOf othersOf
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  have split := List.filter_append_perm (fun item : Pattern × Role => decide (item.2 = .part)) tagged
  have same : (tagged.filter fun item : Pattern × Role => !decide (item.2 = .part)) =
      tagged.filter fun item => decide (item.2 ≠ .part) := by
    apply List.filter_congr
    intro item _
    simp
  rw [same] at split
  exact split.symm

theorem mem_othersOf_of_anchor {tagged : List (Pattern × Role)} {anchor : Pattern} (member : anchor ∈ anchorsOf tagged) :
    anchor ∈ othersOf tagged := by
  have inTagged := mem_anchorsOf.mp member
  simp only [othersOf, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨_, ⟨inTagged, by simp⟩, rfl⟩

theorem mem_fst_of_parts_anchors {tagged : List (Pattern × Role)} {held : Pattern}
    (member : held ∈ partsOf tagged ++ anchorsOf tagged) : held ∈ tagged.map Prod.fst := by
  rcases List.mem_append.mp member with inParts | inAnchors
  · exact List.mem_map.mpr ⟨_, mem_partsOf.mp inParts, rfl⟩
  · exact List.mem_map.mpr ⟨_, mem_anchorsOf.mp inAnchors, rfl⟩

theorem attached_used {count : Nat} {tagged : List (Pattern × Role)} {index : Nat} (attached : Attached tagged index)
    (below : index < count) : index ∈ usedOf ⟨count, tagged.map Prod.fst⟩ := by
  obtain ⟨held, member, mentioned⟩ := attached
  exact List.mem_filter.mpr ⟨List.mem_range.mpr below, List.any_eq_true.mpr
    ⟨held, mem_fst_of_parts_anchors member, mentioned⟩⟩

/-- **Exposure carries to a block with the same canonical form, parts and anchors**, whose other components read as
the block's beside every context. -/
theorem Exposes.transfer {count : Nat} {tagged tagged' : List (Pattern × Role)} {depth depth' : Nat}
    (exposes : Exposes block count tagged depth)
    (sameNormal : normal block ⟨count, tagged.map Prod.fst⟩ = normal block ⟨count, tagged'.map Prod.fst⟩)
    (sameParts : partsOf tagged = partsOf tagged') (sameAnchors : anchorsOf tagged = anchorsOf tagged')
    (sameOthers : ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ context, ∀ index < count, mentions index component = true → Attached tagged' index) →
      normal block ⟨count, othersOf tagged ++ context⟩ = normal block ⟨count, othersOf tagged' ++ context⟩)
    (more : depth ≤ depth') : Exposes block count tagged' depth' := by
  obtain ⟨unfolded, relabel, exposed, rest, unfolds, permutation, partsRelated, anchorsShown, outer, below, injective,
    aligned⟩ := exposes
  have sameAttached : ∀ index, Attached tagged index ↔ Attached tagged' index := by
    intro index
    simp only [Attached, sameParts, sameAnchors]
  refine ⟨unfolded, relabel, exposed, rest, ?_, permutation, sameParts ▸ partsRelated, sameAnchors ▸ anchorsShown,
    outer, fun index inside attached => below index inside ((sameAttached index).mpr attached),
    fun first firstInside second secondInside firstAttached secondAttached same => injective first firstInside second
      secondInside ((sameAttached first).mpr firstAttached) ((sameAttached second).mpr secondAttached) same, ?_⟩
  · rw [← sameNormal]
    exact unfolds.mono more
  · intro context contextAtomic attached
    rw [← sameOthers context contextAtomic attached]
    exact aligned context contextAtomic fun component member index inside mentioned =>
      (sameAttached index).mpr (attached component member index inside mentioned)

/-! ## Unfoldings of blocks of atoms -/

/-- **Unfolding a block of atoms gives a block of atoms.** -/
theorem UnfoldsWithin.atomic (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)
    {depth : Nat} {form unfolded : Prenex} (unfolds : UnfoldsWithin block depth form unfolded) :
    form.Atomic block.toBlock → unfolded.Atomic block.toBlock := by
  induction unfolds with
  | refl => exact id
  | @step depth form next argument member _ recurse =>
      intro atomic
      apply recurse
      intro component inUnfolded
      simp only [Prenex.unfoldWith, List.mem_append, List.mem_map] at inUnfolded
      rcases inUnfolded with ⟨original, inForm, rfl⟩ | inCopy
      · rw [liftBVars_eq_rename]
        exact atomic_rename (atomic original inForm) _
      · exact normal_atomic fresh restrictFresh (decompose_atomic _) component inCopy

/-- Renamings agreeing on the free names of some patterns rename them alike. -/
theorem map_rename_congr {patterns : List Pattern} {first second : Nat → Nat}
    (agree : ∀ pattern ∈ patterns, ∀ index, FreeIn index pattern → first index = second index) :
    patterns.map (rename first) = patterns.map (rename second) :=
  List.map_congr_left fun pattern member => rename_congr pattern (agree pattern member)

theorem taggedAt_mem {tagged : List (Pattern × Role)} {place : Nat} (inside : place < tagged.length) :
    taggedAt block tagged place ∈ tagged := by
  rw [taggedAt_lt inside]
  exact List.getElem_mem inside

theorem taggedAt_fst_mem {tagged : List (Pattern × Role)} {place : Nat} (inside : place < tagged.length) :
    (taggedAt block tagged place).1 ∈ tagged.map Prod.fst :=
  List.mem_map_of_mem (taggedAt_mem inside)

/-- A part or anchor at some place. -/
theorem exists_place_of_held {tagged : List (Pattern × Role)} {held : Pattern}
    (member : held ∈ partsOf tagged ++ anchorsOf tagged) :
    ∃ place < tagged.length, (taggedAt block tagged place).1 = held ∧ (taggedAt block tagged place).2 ≠ .other := by
  rcases List.mem_append.mp member with inParts | inAnchors
  · obtain ⟨place, inside, found⟩ := List.getElem_of_mem (mem_partsOf.mp inParts)
    exact ⟨place, inside, by rw [taggedAt_lt inside, found], by rw [taggedAt_lt inside, found]; simp⟩
  · obtain ⟨place, inside, found⟩ := List.getElem_of_mem (mem_anchorsOf.mp inAnchors)
    exact ⟨place, inside, by rw [taggedAt_lt inside, found], by rw [taggedAt_lt inside, found]; simp⟩

/-- A part or anchor of the components at some places. -/
theorem held_of_place {tagged : List (Pattern × Role)} {places : List Nat} {place : Nat} (member : place ∈ places)
    (role : (taggedAt block tagged place).2 ≠ .other) :
    (taggedAt block tagged place).1 ∈ partsOf (places.map (taggedAt block tagged)) ++
      anchorsOf (places.map (taggedAt block tagged)) := by
  have inMapped : taggedAt block tagged place ∈ places.map (taggedAt block tagged) := List.mem_map_of_mem member
  cases roleIs : (taggedAt block tagged place).2 with
  | part =>
      exact List.mem_append_left _ (mem_partsOf.mpr (by rw [← roleIs]; exact inMapped))
  | anchor =>
      exact List.mem_append_right _ (mem_anchorsOf.mpr (by rw [← roleIs]; exact inMapped))
  | other => exact absurd roleIs role

/-! ## Removing copy groups that avoid the parts and anchors -/

/-- Removing copy groups carries across a system that agrees on the components. -/
theorem removesAvoiding_iso {system other : CopyGroups.System Nat} {avoid live rest : Finset Nat}
    (removes : system.RemovesAvoiding avoid live rest) :
    ∀ {relabel : Nat → Nat}, CopyGroups.System.Iso system other live id relabel →
      other.RemovesAvoiding avoid live rest := by
  induction removes with
  | refl => exact fun _ => .refl
  | @step live rest p copied isCopy disjoint _ recurse =>
      intro relabel iso
      have copiedLive : copied ⊆ live := fun member inCopied =>
        (Finset.mem_erase.mp (isCopy.isGroup.subset inCopied)).2
      have transported := (iso.isCopy_iff isCopy.isLive copiedLive).mpr isCopy
      rw [Finset.image_id, Finset.image_id] at transported
      exact .step transported disjoint (recurse (iso.mono Finset.sdiff_subset))

section Removal

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **Copy groups avoiding the parts and anchors are removed** until every copy group left meets them. The canonical
form of the block stays, and so does that of the other components beside any context of the parts and anchors: a
removed group is a copy group there too. -/
theorem remove_avoiding {count : Nat} {tagged : List (Pattern × Role)}
    (atomic : (Prenex.mk count (tagged.map Prod.fst)).Atomic block.toBlock)
    (plain : ∀ item ∈ tagged, item.2 = .part → isReplicated block item.1 = false) :
    ∃ live : Finset Nat, live ⊆ (List.range tagged.length).toFinset ∧
      (∀ place < tagged.length, (taggedAt block tagged place).2 ≠ .other → place ∈ live) ∧
      (blockSystem block ⟨count, tagged.map Prod.fst⟩).Removes (List.range tagged.length).toFinset live ∧
      (∀ p group, (blockSystem block ⟨count, tagged.map Prod.fst⟩).IsCopy live p group →
        ∃ place ∈ group, (taggedAt block tagged place).2 ≠ .other) ∧
      ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
        (∀ component ∈ context, ∀ index < count, mentions index component = true → Attached tagged index) →
        normal block ⟨count, othersOf (((List.range tagged.length).filter (· ∈ live)).map (taggedAt block tagged)) ++
          context⟩ = normal block ⟨count, othersOf tagged ++ context⟩ := by
  classical
  set length := tagged.length with lengthIs
  set system := blockSystem block ⟨count, tagged.map Prod.fst⟩ with systemIs
  set avoid := ((List.range length).filter fun place => decide ((taggedAt block tagged place).2 ≠ .other)).toFinset
    with avoidIs
  obtain ⟨live, removes, maximal⟩ := system.exists_removesAvoiding avoid (List.range length).toFinset
  refine ⟨live, removes.subset, ?_, removes.removes, ?_, ?_⟩
  · intro place inside notOther
    refine removes.keeps (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr (List.mem_range.mpr inside), ?_⟩)
    simp only [avoidIs, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨inside, notOther⟩
  · intro p group isCopy
    obtain ⟨place, inGroup, inAvoid⟩ := Finset.not_disjoint_iff.mp (maximal p group isCopy)
    simp only [avoidIs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at inAvoid
    exact ⟨place, inGroup, inAvoid.2⟩
  · intro context contextAtomic attached
    -- the removal, beside the context
    set bigForm : Prenex := ⟨count, tagged.map Prod.fst ++ context⟩ with bigFormIs
    have placesIs : (places (⟨count, tagged.map Prod.fst⟩ : Prenex)).toFinset = (List.range length).toFinset := by
      simp [places, lengthIs]
    have iso := append_iso (block := block) count (tagged.map Prod.fst) context
    rw [placesIs] at iso
    have removesBig := removesAvoiding_iso removes iso
    set partPlaces := (List.range length).filter fun place => decide ((taggedAt block tagged place).2 = .part)
      with partPlacesIs
    set commonPlaces := (List.range length).filter fun place => decide ((taggedAt block tagged place).2 ≠ .part)
      with commonPlacesIs
    set keepPlaces := (List.range length).filter fun place => decide ((taggedAt block tagged place).2 = .anchor)
      with keepPlacesIs
    set newPlaces := (List.range context.length).map (length + ·) with newPlacesIs
    have liveIs : (List.range length).toFinset = commonPlaces.toFinset ∪ partPlaces.toFinset := by
      ext place
      simp only [List.mem_toFinset, List.mem_range, Finset.mem_union, commonPlacesIs, partPlacesIs,
        List.mem_filter, decide_eq_true_eq]
      constructor
      · intro inside
        by_cases isPart : (taggedAt block tagged place).2 = .part
        · exact .inr ⟨inside, isPart⟩
        · exact .inl ⟨inside, isPart⟩
      · rintro (⟨inside, _⟩ | ⟨inside, _⟩) <;> exact inside
    have bigAtomic : bigForm.Atomic block.toBlock := by
      intro component member
      rcases List.mem_append.mp member with inTagged | inContext
      · exact atomic component inTagged
      · exact contextAtomic component inContext
    obtain ⟨common', inside', restIs, removesNew⟩ := removesBig.replace (common := commonPlaces.toFinset)
      (old := partPlaces.toFinset) (new := newPlaces.toFinset) (keep := keepPlaces.toFinset) liveIs
      (by
        refine Finset.disjoint_left.mpr fun place inCommon inParts => ?_
        simp only [commonPlacesIs, partPlacesIs, List.mem_toFinset, List.mem_filter,
          decide_eq_true_eq] at inCommon inParts
        exact inCommon.2 inParts.2)
      (by
        refine Finset.disjoint_left.mpr fun place inCommon inNew => ?_
        simp only [commonPlacesIs, newPlacesIs, List.mem_toFinset, List.mem_filter, List.mem_map,
          List.mem_range] at inCommon inNew
        obtain ⟨offset, _, rfl⟩ := inNew
        omega)
      (by
        intro place member
        simp only [partPlacesIs, avoidIs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at member ⊢
        exact ⟨member.1, by rw [member.2]; decide⟩)
      (by
        intro place member
        simp only [keepPlacesIs, avoidIs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at member ⊢
        exact ⟨member.1, by rw [member.2]; decide⟩)
      (by
        intro place member
        simp only [keepPlacesIs, commonPlacesIs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at member ⊢
        exact ⟨member.1, by rw [member.2]; decide⟩)
      (by
        intro place member replicated
        simp only [partPlacesIs, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at member
        have inside : place < tagged.length := member.1
        have flat := plain tagged[place] (List.getElem_mem inside)
          (by rw [← taggedAt_lt (block := block) inside]; exact member.2)
        simp only [blockSystem, absorptionSystem] at replicated
        rw [placeValue_append_left (by simpa using inside), placeValue_fst, taggedAt_lt inside, flat] at replicated
        exact Bool.false_ne_true replicated)
      (by
        intro place inNew restriction mentioned
        simp only [newPlacesIs, List.mem_toFinset, List.mem_map, List.mem_range] at inNew
        obtain ⟨offset, offsetInside, rfl⟩ := inNew
        simp only [blockSystem, absorptionSystem, List.mem_toFinset, mem_usedRestrictions] at mentioned
        rw [show length + offset = (tagged.map Prod.fst).length + offset by simp [lengthIs],
          placeValue_append_right offsetInside] at mentioned
        obtain ⟨below, mentionedHere⟩ := mentioned
        have inContext : placeValue block context offset ∈ context := placeValue_mem offsetInside
        obtain ⟨held, inHeld, heldMentions⟩ := attached _ inContext restriction below mentionedHere
        -- the part or anchor at its place
        have heldPlace : ∃ place < length, (taggedAt block tagged place).1 = held ∧
            ((taggedAt block tagged place).2 = .part ∨ (taggedAt block tagged place).2 = .anchor) := by
          rcases List.mem_append.mp inHeld with inParts | inAnchors
          · obtain ⟨place, inside, found⟩ := List.getElem_of_mem (mem_partsOf.mp inParts)
            exact ⟨place, inside, by rw [taggedAt_lt inside, found], .inl (by rw [taggedAt_lt inside, found])⟩
          · obtain ⟨place, inside, found⟩ := List.getElem_of_mem (mem_anchorsOf.mp inAnchors)
            exact ⟨place, inside, by rw [taggedAt_lt inside, found], .inr (by rw [taggedAt_lt inside, found])⟩
        obtain ⟨place, inside, heldIs, role⟩ := heldPlace
        refine ⟨place, ?_, ?_⟩
        · rcases role with isPart | isAnchor
          · exact Finset.mem_union_left _ (by
              simp only [partPlacesIs, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
              exact ⟨inside, isPart⟩)
          · exact Finset.mem_union_right _ (by
              simp only [keepPlacesIs, List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
              exact ⟨inside, isAnchor⟩)
        · simp only [blockSystem, absorptionSystem, List.mem_toFinset, mem_usedRestrictions]
          rw [placeValue_append_left (by simpa using inside), placeValue_fst, heldIs]
          exact ⟨below, heldMentions⟩)
    -- the kept other components, by their places
    set keptPlaces := commonPlaces.filter (· ∈ live) with keptPlacesIs
    have keptToFinset : keptPlaces.toFinset = common' := by
      ext place
      simp only [keptPlacesIs, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨inCommon, inLive⟩
        rw [restIs] at inLive
        rcases Finset.mem_union.mp inLive with inCommon' | inParts
        · exact inCommon'
        · simp only [commonPlacesIs, partPlacesIs, List.mem_toFinset, List.mem_filter,
            decide_eq_true_eq] at inCommon inParts
          exact absurd inParts.2 inCommon.2
      · intro inCommon'
        exact ⟨List.mem_toFinset.mp (inside' inCommon'), by rw [restIs]; exact Finset.mem_union_left _ inCommon'⟩
    have commonNodup : commonPlaces.Nodup := List.nodup_range.filter _
    have newNodup : newPlaces.Nodup := (List.nodup_range).map fun first second same => by omega
    have commonNewApart : ∀ a ∈ commonPlaces, ∀ b ∈ newPlaces, a ≠ b := by
      intro a inCommon b inNew same
      simp only [commonPlacesIs, newPlacesIs, List.mem_filter, List.mem_map, List.mem_range] at inCommon inNew
      obtain ⟨offset, _, rfl⟩ := inNew
      omega
    have bigLength : bigForm.components.length = length + context.length := by simp [bigFormIs, lengthIs]
    have commonInside : ∀ place ∈ commonPlaces, place < length := fun place member =>
      List.mem_range.mp (List.mem_filter.mp member).1
    have newInside : ∀ place ∈ newPlaces, length ≤ place ∧ place < length + context.length := by
      intro place member
      simp only [newPlacesIs, List.mem_map, List.mem_range] at member
      obtain ⟨offset, inside, rfl⟩ := member
      omega
    have restricted := normal_restrict_from fresh restrictFresh bigAtomic (live := commonPlaces ++ newPlaces)
      (kept := keptPlaces ++ newPlaces)
      (List.nodup_append.mpr ⟨commonNodup, newNodup, commonNewApart⟩)
      (by
        intro place member
        rw [bigLength]
        rcases List.mem_append.mp member with inCommon | inNew
        · have := commonInside place inCommon
          omega
        · exact (newInside place inNew).2)
      (List.nodup_append.mpr ⟨commonNodup.sublist List.filter_sublist, newNodup, fun a inKept b inNew =>
        commonNewApart a (List.filter_sublist.subset inKept) b inNew⟩)
      (by
        intro place member
        rcases List.mem_append.mp member with inKept | inNew
        · exact List.mem_append_left _ (List.filter_sublist.subset inKept)
        · exact List.mem_append_right _ inNew)
      (by
        rw [List.toFinset_append, List.toFinset_append, keptToFinset]
        exact removesNew)
    -- the restricted blocks
    have valueLeft : ∀ place < length, placeValue block bigForm.components place = (taggedAt block tagged place).1 := by
      intro place inside
      rw [bigFormIs, placeValue_append_left (by simpa using inside), placeValue_fst]
    have valueNew : newPlaces.map (placeValue block bigForm.components) = context := by
      apply List.ext_getElem
      · simp [newPlacesIs]
      · intro position inside _
        simp only [newPlacesIs, List.getElem_map, List.getElem_range]
        rw [bigFormIs, show length + position = (tagged.map Prod.fst).length + position by simp [lengthIs],
          placeValue_append_right (by simpa [newPlacesIs] using inside)]
        exact List.getD_eq_getElem _ _ _
    have commonValues : commonPlaces.map (placeValue block bigForm.components) = othersOf tagged := by
      conv_rhs => rw [← map_taggedAt_range (block := block) tagged]
      rw [othersOf_places]
      exact List.map_congr_left fun place member => valueLeft place (commonInside place member)
    have keptValues : keptPlaces.map (placeValue block bigForm.components) =
        othersOf (((List.range length).filter (· ∈ live)).map (taggedAt block tagged)) := by
      rw [othersOf_places, List.filter_filter, keptPlacesIs, commonPlacesIs, List.filter_filter]
      have sameFilter : ((List.range length).filter fun place =>
            decide (place ∈ live) && decide ((taggedAt block tagged place).2 ≠ .part)) =
          (List.range length).filter fun place =>
            decide ((taggedAt block tagged place).2 ≠ .part) && decide (place ∈ live) := by
        apply List.filter_congr
        intro place _
        exact Bool.and_comm _ _
      rw [sameFilter]
      exact List.map_congr_left fun place member =>
        valueLeft place (List.mem_range.mp (List.mem_filter.mp member).1)
    simp only [restrictTo, List.map_append, valueNew, commonValues, keptValues] at restricted
    exact restricted

/-- **A block without copy groups exposes its parts and anchors in its canonical form.** -/
theorem exposes_base {count : Nat} {tagged : List (Pattern × Role)}
    (atomic : (Prenex.mk count (tagged.map Prod.fst)).Atomic block.toBlock)
    (plain : ∀ item ∈ tagged, item.2 = .part → isReplicated block item.1 = false)
    (none : ∀ p group, ¬ (blockSystem block ⟨count, tagged.map Prod.fst⟩).IsCopy
      (places ⟨count, tagged.map Prod.fst⟩).toFinset p group) (depth : Nat) :
    Exposes block count tagged depth := by
  obtain ⟨relabel, restUnfolded, componentsPerm, othersIn, outer, below, injective, aligned⟩ :=
    exposure_base fresh restrictFresh (fst_perm_parts_others tagged) atomic
      (fun part member => plain _ (mem_partsOf.mp member) rfl) none
  refine ⟨normal block ⟨count, tagged.map Prod.fst⟩, relabel,
    (partsOf tagged).map fun part => recanon block (rename relabel part), restUnfolded, .refl depth _,
    componentsPerm, ?_, ?_, outer, ?_, ?_, ?_⟩
  · rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun part _ => (alike_recanon_all fresh restrictFresh _).symm
  · intro anchor member
    exact ⟨_, othersIn anchor (mem_othersOf_of_anchor member), (alike_recanon_all fresh restrictFresh _).symm⟩
  · intro index inside attached
    exact below index (attached_used attached inside)
  · intro first firstInside second secondInside firstAttached secondAttached same
    exact injective first (attached_used firstAttached firstInside) second (attached_used secondAttached secondInside)
      same
  · intro context contextAtomic attached
    exact aligned context contextAtomic fun component member index inside mentioned =>
      attached_used (attached component member index inside mentioned) inside

end Removal

/-! ## Roles of components at places, renamed -/

/-- **The components of some roles at some places, read through another reading of the places** that agrees on the
roles and renames the components. -/
theorem roleFilter_map_places (keep : Role → Bool) {places : List Nat} {first second : Nat → Pattern × Role}
    {relabel : Pattern → Pattern} (sameRole : ∀ place ∈ places, keep (first place).2 = keep (second place).2)
    (sameComponent : ∀ place ∈ places, (first place).1 = relabel (second place).1) :
    ((places.map first).filter fun item => keep item.2).map Prod.fst =
      (((places.map second).filter fun item => keep item.2).map Prod.fst).map relabel := by
  rw [List.filter_map, List.filter_map, List.map_map, List.map_map, List.map_map]
  have filterSame : (places.filter ((fun item : Pattern × Role => keep item.2) ∘ first)) =
      places.filter ((fun item : Pattern × Role => keep item.2) ∘ second) :=
    List.filter_congr fun place member => sameRole place member
  rw [filterSame]
  exact List.map_congr_left fun place member =>
    sameComponent place (List.mem_of_mem_filter member)

theorem partsOf_map_places {places : List Nat} {first second : Nat → Pattern × Role} {relabel : Pattern → Pattern}
    (sameRole : ∀ place ∈ places, ((first place).2 = .part ↔ (second place).2 = .part))
    (sameComponent : ∀ place ∈ places, (first place).1 = relabel (second place).1) :
    partsOf (places.map first) = (partsOf (places.map second)).map relabel :=
  roleFilter_map_places (fun role => decide (role = .part))
    (fun place member => by simp only [decide_eq_decide]; exact sameRole place member) sameComponent

theorem othersOf_map_places {places : List Nat} {first second : Nat → Pattern × Role} {relabel : Pattern → Pattern}
    (sameRole : ∀ place ∈ places, ((first place).2 = .part ↔ (second place).2 = .part))
    (sameComponent : ∀ place ∈ places, (first place).1 = relabel (second place).1) :
    othersOf (places.map first) = (othersOf (places.map second)).map relabel :=
  roleFilter_map_places (fun role => decide (role ≠ .part))
    (fun place member => by simp only [decide_eq_decide, ne_eq]; exact not_congr (sameRole place member))
    sameComponent

theorem forall₂_imp_mem_right {α β : Type} {relation relation' : α → β → Prop} {first : List α} {second : List β}
    (related : List.Forall₂ relation first second)
    (imp : ∀ a b, b ∈ second → relation a b → relation' a b) : List.Forall₂ relation' first second := by
  induction related with
  | nil => exact .nil
  | cons head _ recurse =>
      exact .cons (imp _ _ List.mem_cons_self head)
        (recurse fun a b member holds => imp a b (List.mem_cons_of_mem _ member) holds)

theorem mem_partsOf_places {tagged : List (Pattern × Role)} {places : List Nat} {part : Pattern}
    (member : part ∈ partsOf (places.map (taggedAt block tagged))) :
    ∃ place ∈ places, taggedAt block tagged place = (part, .part) := by
  obtain ⟨place, inPlaces, found⟩ := List.mem_map.mp (mem_partsOf.mp member)
  exact ⟨place, inPlaces, found⟩

/-! ## What unfolding a copy group costs -/

/-- **Unfolding a copy group costs one unfolding, paid by the parts and anchors the group holds**: each is exposed
below the replicated component's height instead of the ceiling, and the replicated component, made an anchor,
costs at most what is left. -/
theorem step_weights {ceiling top : Nat} {tagged : List (Pattern × Role)} {rest group : List Nat} {q : Nat}
    {restItem groupItem : Nat → Pattern × Role}
    (permutation : (rest ++ group).Perm (List.range tagged.length)) (restNodup : rest.Nodup) (qIn : q ∈ rest)
    (restSame : ∀ place ∈ rest, place ≠ q →
      weight block ceiling (restItem place) = weight block ceiling (taggedAt block tagged place))
    (qWeight : weight block ceiling (restItem q) = ceiling - 1 - top)
    (groupSame : ∀ place ∈ group, weight block top (groupItem place) = weight block top (taggedAt block tagged place))
    (topLow : top < ceiling)
    (lower : ∀ place ∈ group, (taggedAt block tagged place).2 = .anchor →
      height block (taggedAt block tagged place).1 < top)
    (meets : ∃ place ∈ group, (taggedAt block tagged place).2 ≠ .other) :
    ((rest.map restItem).map (weight block ceiling)).sum + 1 + ((group.map groupItem).map (weight block top)).sum ≤
      (tagged.map (weight block ceiling)).sum := by
  have total : (tagged.map (weight block ceiling)).sum =
      (rest.map fun place => weight block ceiling (taggedAt block tagged place)).sum +
        (group.map fun place => weight block ceiling (taggedAt block tagged place)).sum := by
    have mapped := (permutation.map (fun place => weight block ceiling (taggedAt block tagged place))).sum_eq
    rw [List.map_append, List.sum_append] at mapped
    rw [mapped]
    conv_lhs => rw [← map_taggedAt_range (block := block) tagged, List.map_map]
    rfl
  have restWeight : ((rest.map restItem).map (weight block ceiling)).sum ≤
      (rest.map fun place => weight block ceiling (taggedAt block tagged place)).sum + (ceiling - 1 - top) := by
    have qPerm := List.perm_cons_erase qIn
    have notQ : ∀ place ∈ rest.erase q, place ≠ q := fun place member same => by
      subst same
      exact (List.Nodup.not_mem_erase restNodup) member
    rw [List.map_map, (qPerm.map _).sum_eq, (qPerm.map _).sum_eq, List.map_cons, List.map_cons, List.sum_cons,
      List.sum_cons]
    have sameRest : ((rest.erase q).map (weight block ceiling ∘ restItem)).sum =
        ((rest.erase q).map fun place => weight block ceiling (taggedAt block tagged place)).sum := by
      congr 1
      exact List.map_congr_left fun place member =>
        restSame place (List.mem_of_mem_erase member) (notQ place member)
    rw [sameRest]
    simp only [Function.comp_apply, qWeight]
    omega
  have groupWeight : ((group.map groupItem).map (weight block top)).sum =
      (group.map fun place => weight block top (taggedAt block tagged place)).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun place member => groupSame place member
  have groupSurplus : (group.map fun place => weight block top (taggedAt block tagged place)).sum + (ceiling - top) ≤
      (group.map fun place => weight block ceiling (taggedAt block tagged place)).sum := by
    obtain ⟨met, metIn, metRole⟩ := meets
    have metPerm := List.perm_cons_erase metIn
    rw [(metPerm.map _).sum_eq, (metPerm.map _).sum_eq, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have restLe : ((group.erase met).map fun place => weight block top (taggedAt block tagged place)).sum ≤
        ((group.erase met).map fun place => weight block ceiling (taggedAt block tagged place)).sum := by
      apply List.sum_le_sum
      intro place _
      simp only [weight]
      split <;> omega
    have metLe : weight block top (taggedAt block tagged met) + (ceiling - top) ≤
        weight block ceiling (taggedAt block tagged met) := by
      cases roleIs : (taggedAt block tagged met).2 with
      | part =>
          simp only [weight, roleIs]
          omega
      | anchor =>
          have := lower met metIn roleIs
          simp only [weight, roleIs]
          omega
      | other => exact absurd roleIs metRole
    omega
  rw [total, groupWeight]
  omega

/-! ## Unfolding a copy group -/

section Step

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **The other components beside a context read as in the unfolding**, through the two exposures: the block without
the group reads the group's other components and the context with the group's own restrictions as names outside,
past every name used; those are moved first and closed again; the unfolding's restrictions are then moved past the
group's own, and the group's block reads the rest of the unfolding and the context with the unfolding's
restrictions as names outside. -/
theorem step_alignment {count : Nat} {own : List Nat} (ownNodup : own.Nodup) (ownBelow : ∀ index ∈ own, index < count)
    {othersRest othersGroup context rest₁ restG : List Pattern} {relabel₁ relabelG rho : Nat → Nat}
    {unfolded₁ unfoldedG : Nat} {attached₁ attachedG : Nat → Prop}
    (restAtomic : ∀ component ∈ othersRest, decompose block.toBlock component = Prenex.atom component)
    (groupAtomic : ∀ component ∈ othersGroup, decompose block.toBlock component = Prenex.atom component)
    (contextAtomic : ∀ component ∈ context, decompose block.toBlock component = Prenex.atom component)
    (rest₁Atomic : ∀ component ∈ rest₁, decompose block.toBlock component = Prenex.atom component)
    (restGAtomic : ∀ component ∈ restG, decompose block.toBlock component = Prenex.atom component)
    (restFree : ∀ component ∈ othersRest, ∀ index, FreeIn index component → index < count → index ∉ own)
    (groupAttached : ∀ component ∈ othersGroup, ∀ index, FreeIn index component → index < count → index ∉ own →
      attached₁ (Prenex.groupIndex count (outsideOf count own) index))
    (contextAttached : ∀ component ∈ context, ∀ index, FreeIn index component → index < count →
      (index ∈ own ∧ attachedG (own.idxOf index)) ∨
        (index ∉ own ∧ attached₁ (Prenex.groupIndex count (outsideOf count own) index)))
    (outer₁ : ∀ index, relabel₁ ((outsideOf count own).length + index) = unfolded₁ + index)
    (below₁ : ∀ index < (outsideOf count own).length, attached₁ index → relabel₁ index < unfolded₁)
    (aligned₁ : ∀ extra : List Pattern, (∀ component ∈ extra, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ extra, ∀ index < (outsideOf count own).length, mentions index component = true →
        attached₁ index) →
      normal block ⟨(outsideOf count own).length,
          othersRest.map (rename (Prenex.groupIndex count (outsideOf count own))) ++ extra⟩ =
        normal block ⟨unfolded₁, rest₁ ++ extra.map (rename relabel₁)⟩)
    (rhoOwn : ∀ index ∈ own, rho index = own.idxOf index)
    (rhoOutside : ∀ index < count, index ∉ own →
      rho index = relabel₁ (Prenex.groupIndex count (outsideOf count own) index) + own.length)
    (rhoAbove : ∀ index, count ≤ index → rho index = unfolded₁ + (index - count) + own.length)
    (outerG : ∀ index, relabelG (own.length + index) = unfoldedG + index)
    (alignedG : ∀ extra : List Pattern, (∀ component ∈ extra, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ extra, ∀ index < own.length, mentions index component = true → attachedG index) →
      normal block ⟨own.length, othersGroup.map (rename rho) ++ extra⟩ =
        normal block ⟨unfoldedG, restG ++ extra.map (rename relabelG)⟩) :
    normal block ⟨count, othersRest ++ othersGroup ++ context⟩ =
      normal block ⟨unfoldedG + unfolded₁,
        (rest₁.map (rename (shiftAbove 0 unfoldedG)) ++ restG) ++ context.map (rename (relabelG ∘ rho))⟩ := by
  classical
  set outside := outsideOf count own with outsideIs
  set inner := outside.length with innerIs
  set gi := Prenex.groupIndex count outside with giIs
  have outsideLength : inner = count - own.length := outsideOf_length ownNodup ownBelow
  have ownLe : own.length ≤ count := length_le_of_inside ownNodup ownBelow
  have giInside : ∀ index < count, gi index = outside.idxOf index := fun index below => groupIndex_below below
  have giBelow : ∀ index < count, index ∉ own → gi index < inner := fun index below notOwn => by
    rw [giInside index below]
    exact List.idxOf_lt_length_of_mem (mem_outsideOf.mpr ⟨below, notOwn⟩)
  have giAbove : ∀ index, count ≤ index → gi index = inner + (index - count) := fun index above => by
    rw [giIs, groupIndex_above above]
    omega
  have renamedAtomic : ∀ (patterns : List Pattern) (relabel : Nat → Nat),
      (∀ component ∈ patterns, decompose block.toBlock component = Prenex.atom component) →
      ∀ component ∈ patterns.map (rename relabel), decompose block.toBlock component = Prenex.atom component := by
    intro patterns relabel atomic component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    exact atomic_rename (atomic original inOriginal) relabel
  have appendAtomic : ∀ first second : List Pattern,
      (∀ component ∈ first, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ second, decompose block.toBlock component = Prenex.atom component) →
      ∀ component ∈ first ++ second, decompose block.toBlock component = Prenex.atom component := by
    intro first second firstAtomic secondAtomic component member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact firstAtomic component inFirst
    · exact secondAtomic component inSecond
  -- a bound past every name used
  obtain ⟨bound, bounded⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
    (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le)
    (othersRest ++ othersGroup ++ context ++ rest₁) fun pattern _ => exists_freeBound pattern
  have boundRest : ∀ component ∈ othersRest, ∀ index, FreeIn index component → index < bound :=
    fun component member => bounded component (by simp [member])
  have boundGroup : ∀ component ∈ othersGroup, ∀ index, FreeIn index component → index < bound :=
    fun component member => bounded component (by simp [member])
  have boundContext : ∀ component ∈ context, ∀ index, FreeIn index component → index < bound :=
    fun component member => bounded component (by simp [member])
  have boundRest₁ : ∀ component ∈ rest₁, ∀ index, FreeIn index component → index < bound :=
    fun component member => bounded component (by simp [member])
  -- the renamings
  set high : Nat → Nat := fun index =>
    if index < count then (if index ∈ own then inner + bound + own.idxOf index else gi index)
    else inner + (index - count) with highIs
  set close : Nat → Nat := fun index =>
    if index < bound then own.length + index else if index < bound + own.length then index - bound else index
    with closeIs
  set mixed : Nat → Nat := fun index =>
    if index < count then (if index ∈ own then inner + own.idxOf index else gi index) else index with mixedIs
  set swap : Nat → Nat := fun index =>
    if index < unfolded₁ then own.length + index else if index < unfolded₁ + own.length then index - unfolded₁
    else index with swapIs
  have closeInjective : Function.Injective close := by
    intro first second same
    simp only [closeIs] at same
    split_ifs at same <;> omega
  -- the group's other components and the context, with the group's own restrictions past every name used
  set extra₁ := (othersGroup ++ context).map (rename high) with extra₁Is
  have extra₁Atomic := renamedAtomic _ high (appendAtomic _ _ groupAtomic contextAtomic)
  have extra₁Attached : ∀ component ∈ extra₁, ∀ index < inner, mentions index component = true →
      attached₁ index := by
    intro component member index below mentioned
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [mentions_iff, freeIn_rename] at mentioned
    obtain ⟨name, free, maps⟩ := mentioned
    simp only [highIs] at maps
    by_cases nameBelow : name < count
    · by_cases inOwn : name ∈ own
      · rw [if_pos nameBelow, if_pos inOwn] at maps
        omega
      · rw [if_pos nameBelow, if_neg inOwn] at maps
        subst maps
        rcases List.mem_append.mp inOriginal with inGroup | inContext
        · exact groupAttached original inGroup name free nameBelow inOwn
        · rcases contextAttached original inContext name free nameBelow with ⟨isOwn, _⟩ | ⟨_, attached⟩
          · exact absurd isOwn inOwn
          · exact attached
    · rw [if_neg nameBelow] at maps
      omega
  have restRenamedAtomic := renamedAtomic _ gi restAtomic
  have firstEq := aligned₁ extra₁ extra₁Atomic extra₁Attached
  set first : Prenex := ⟨inner, othersRest.map (rename gi) ++ extra₁⟩ with firstIs
  set second : Prenex := ⟨unfolded₁, rest₁ ++ extra₁.map (rename relabel₁)⟩ with secondIs
  have firstAtomic : first.Atomic block.toBlock := appendAtomic _ _ restRenamedAtomic extra₁Atomic
  have secondAtomic : second.Atomic block.toBlock :=
    appendAtomic _ _ rest₁Atomic (renamedAtomic _ relabel₁ extra₁Atomic)
  -- moving the group's own restrictions first, past every name used, and closing them again
  have movedEq : normal block (first.renameOuter close) = normal block (second.renameOuter close) := by
    rw [← normal_renameOuter_normal fresh restrictFresh firstAtomic closeInjective, firstEq,
      normal_renameOuter_normal fresh restrictFresh secondAtomic closeInjective]
  have closedEq := normal_add_congr fresh restrictFresh (renameOuter_atomic firstAtomic close)
    (renameOuter_atomic secondAtomic close) movedEq own.length
  have mixedComponents : (othersRest ++ othersGroup ++ context).map (rename mixed) =
      (first.renameOuter close).components := by
    simp only [firstIs, Prenex.renameOuter, extra₁Is, List.map_append, List.map_map, List.append_assoc]
    congr 1
    · refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, rename_comp]
      apply rename_congr
      intro index free
      simp only [Function.comp_apply, mixedIs, liftIndex]
      by_cases below : index < count
      · have notOwn := restFree component member index free below
        rw [if_pos below, if_neg notOwn, if_pos (giBelow index below notOwn)]
      · rw [if_neg below, giAbove index (by omega), if_neg (by omega)]
        have := boundRest component member index free
        simp only [closeIs]
        rw [if_pos (by omega)]
        omega
    · congr 1 <;> refine List.map_congr_left fun component member => ?_ <;>
        simp only [Function.comp_apply, rename_comp] <;> apply rename_congr <;> intro index free <;>
        simp only [Function.comp_apply, mixedIs, highIs, liftIndex]
      · have := boundGroup component member index free
        by_cases below : index < count
        · by_cases inOwn : index ∈ own
          · have := List.idxOf_lt_length_of_mem inOwn
            rw [if_pos below, if_pos inOwn, if_pos below, if_pos inOwn, if_neg (by omega)]
            simp only [closeIs]
            rw [if_neg (by omega), if_pos (by omega)]
            omega
          · rw [if_pos below, if_neg inOwn, if_pos below, if_neg inOwn, if_pos (giBelow index below inOwn)]
        · rw [if_neg below, if_neg below, if_neg (by omega)]
          simp only [closeIs]
          rw [if_pos (by omega)]
          omega
      · have := boundContext component member index free
        by_cases below : index < count
        · by_cases inOwn : index ∈ own
          · have := List.idxOf_lt_length_of_mem inOwn
            rw [if_pos below, if_pos inOwn, if_pos below, if_pos inOwn, if_neg (by omega)]
            simp only [closeIs]
            rw [if_neg (by omega), if_pos (by omega)]
            omega
          · rw [if_pos below, if_neg inOwn, if_pos below, if_neg inOwn, if_pos (giBelow index below inOwn)]
        · rw [if_neg below, if_neg below, if_neg (by omega)]
          simp only [closeIs]
          rw [if_pos (by omega)]
          omega
  -- the block, the group's own restrictions moved past the others
  have mixedEq : normal block ⟨count, othersRest ++ othersGroup ++ context⟩ =
      normal block ⟨inner + own.length, (first.renameOuter close).components⟩ := by
    have xAtomic : (Prenex.mk count (othersRest ++ othersGroup ++ context)).Atomic block.toBlock :=
      appendAtomic _ _ (appendAtomic _ _ restAtomic groupAtomic) contextAtomic
    rw [← mixedComponents, show inner + own.length = count by omega]
    refine (normal_rename_used fresh restrictFresh xAtomic ?_ ?_ ?_).symm
    · intro a inA b inB same
      have aBelow : a < count := List.mem_range.mp (List.mem_filter.mp inA).1
      have bBelow : b < count := List.mem_range.mp (List.mem_filter.mp inB).1
      simp only [mixedIs, if_pos aBelow, if_pos bBelow] at same
      by_cases aOwn : a ∈ own <;> by_cases bOwn : b ∈ own <;> simp only [aOwn, bOwn, if_true, if_false] at same
      · exact (List.idxOf_inj aOwn).mp (by omega)
      · have := giBelow b bBelow bOwn
        omega
      · have := giBelow a aBelow aOwn
        omega
      · rw [giInside a aBelow, giInside b bBelow] at same
        exact (List.idxOf_inj (mem_outsideOf.mpr ⟨aBelow, aOwn⟩)).mp same
    · intro index member
      have below : index < count := List.mem_range.mp (List.mem_filter.mp member).1
      simp only [mixedIs, if_pos below]
      split_ifs with inOwn
      · have := List.idxOf_lt_length_of_mem inOwn
        omega
      · have := giBelow index below inOwn
        omega
    · intro index
      simp only [mixedIs, if_neg (by omega : ¬ (count + index < count))]
  -- the unfolding's restrictions moved past the group's own
  set moved := (second.renameOuter close).components with movedIs
  have movedAtomic : (Prenex.mk (unfolded₁ + own.length) moved).Atomic block.toBlock :=
    renameOuter_atomic secondAtomic close
  have swapEq : normal block ⟨unfolded₁ + own.length, moved⟩ =
      normal block ⟨own.length + unfolded₁, moved.map (rename swap)⟩ := by
    refine (normal_rename_used fresh restrictFresh movedAtomic ?_ ?_ ?_).symm
    · intro a inA b inB same
      have aBelow : a < unfolded₁ + own.length := List.mem_range.mp (List.mem_filter.mp inA).1
      have bBelow : b < unfolded₁ + own.length := List.mem_range.mp (List.mem_filter.mp inB).1
      simp only [swapIs] at same
      split_ifs at same <;> omega
    · intro index member
      have below : index < unfolded₁ + own.length := List.mem_range.mp (List.mem_filter.mp member).1
      simp only [swapIs]
      split_ifs <;> omega
    · intro index
      simp only [swapIs]
      split_ifs <;> omega
  have mapsTo : ∀ index, index < bound → (index < count → index ∉ own → attached₁ (gi index)) →
      swap (liftIndex unfolded₁ close (relabel₁ (high index))) = rho index := by
    intro index belowBound attachedIf
    by_cases below : index < count
    · by_cases inOwn : index ∈ own
      · have idxBelow := List.idxOf_lt_length_of_mem inOwn
        have highIs' : high index = inner + (bound + own.idxOf index) := by
          simp only [highIs, if_pos below, if_pos inOwn]
          omega
        rw [highIs', outer₁, rhoOwn index inOwn]
        simp only [liftIndex, closeIs, swapIs]
        split_ifs <;> omega
      · have highIs' : high index = gi index := by simp only [highIs, if_pos below, if_neg inOwn]
        have small := below₁ (gi index) (giBelow index below inOwn) (attachedIf below inOwn)
        rw [highIs', rhoOutside index below inOwn]
        simp only [liftIndex, swapIs]
        split_ifs
        omega
    · have highIs' : high index = inner + (index - count) := by simp only [highIs, if_neg below]
      rw [highIs', outer₁, rhoAbove index (by omega)]
      simp only [liftIndex, closeIs, swapIs]
      split_ifs <;> omega
  have swappedComponents : moved.map (rename swap) =
      rest₁.map (rename (shiftAbove 0 own.length)) ++ (othersGroup ++ context).map (rename rho) := by
    rw [movedIs, secondIs]
    simp only [Prenex.renameOuter]
    rw [List.map_append, List.map_append]
    congr 1
    · rw [List.map_map]
      refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, rename_comp]
      apply rename_congr
      intro index free
      have := boundRest₁ component member index free
      simp only [Function.comp_apply, liftIndex, closeIs, swapIs, shiftAbove, Nat.not_lt_zero, if_false]
      split_ifs <;> omega
    · rw [extra₁Is, List.map_map, List.map_map, List.map_map]
      refine List.map_congr_left fun component member => ?_
      simp only [Function.comp_apply, rename_comp]
      apply rename_congr
      intro index free
      simp only [Function.comp_apply]
      rcases List.mem_append.mp member with inGroup | inContext
      · exact mapsTo index (boundGroup component inGroup index free) fun below notOwn =>
          groupAttached component inGroup index free below notOwn
      · refine mapsTo index (boundContext component inContext index free) fun below notOwn => ?_
        rcases contextAttached component inContext index free below with ⟨isOwn, _⟩ | ⟨_, attached⟩
        · exact absurd isOwn notOwn
        · exact attached
  -- the group's block reads the rest of the unfolding and the context
  set extraG := rest₁.map (rename (shiftAbove 0 own.length)) ++ context.map (rename rho) with extraGIs
  have extraGAtomic := appendAtomic _ _ (renamedAtomic _ (shiftAbove 0 own.length) rest₁Atomic)
    (renamedAtomic _ rho contextAtomic)
  have extraGAttached : ∀ component ∈ extraG, ∀ index < own.length, mentions index component = true →
      attachedG index := by
    intro component member index below mentioned
    rcases List.mem_append.mp member with inRest | inContext
    · obtain ⟨original, _, rfl⟩ := List.mem_map.mp inRest
      rw [mentions_iff, freeIn_rename] at mentioned
      obtain ⟨name, _, maps⟩ := mentioned
      simp only [shiftAbove, Nat.not_lt_zero, if_false] at maps
      omega
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inContext
      rw [mentions_iff, freeIn_rename] at mentioned
      obtain ⟨name, free, maps⟩ := mentioned
      by_cases nameBelow : name < count
      · rcases contextAttached original inOriginal name free nameBelow with ⟨inOwn, attached⟩ | ⟨notOwn, _⟩
        · rw [rhoOwn name inOwn] at maps
          rw [← maps]
          exact attached
        · rw [rhoOutside name nameBelow notOwn] at maps
          omega
      · rw [rhoAbove name (by omega)] at maps
        omega
  have groupEq := alignedG extraG extraGAtomic extraGAttached
  have groupFirstAtomic : (Prenex.mk own.length (othersGroup.map (rename rho) ++ extraG)).Atomic block.toBlock :=
    appendAtomic _ _ (renamedAtomic _ rho groupAtomic) extraGAtomic
  have groupSecondAtomic : (Prenex.mk unfoldedG (restG ++ extraG.map (rename relabelG))).Atomic block.toBlock :=
    appendAtomic _ _ restGAtomic (renamedAtomic _ relabelG extraGAtomic)
  have groupClosed := normal_add_congr fresh restrictFresh groupFirstAtomic groupSecondAtomic groupEq unfolded₁
  have extraGRenamed : extraG.map (rename relabelG) =
      rest₁.map (rename (shiftAbove 0 unfoldedG)) ++ context.map (rename (relabelG ∘ rho)) := by
    rw [extraGIs, List.map_append, List.map_map, List.map_map]
    congr 1
    · refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp_apply, rename_comp]
      apply rename_congr
      intro index _
      simp only [Function.comp_apply, shiftAbove, Nat.not_lt_zero, if_false]
      rw [Nat.add_comm, outerG]
      omega
    · refine List.map_congr_left fun component _ => ?_
      simp only [Function.comp_apply, rename_comp]
  have swappedAtomic : (Prenex.mk (own.length + unfolded₁)
      (rest₁.map (rename (shiftAbove 0 own.length)) ++ (othersGroup ++ context).map (rename rho))).Atomic
        block.toBlock :=
    appendAtomic _ _ (renamedAtomic _ _ rest₁Atomic) (renamedAtomic _ _ (appendAtomic _ _ groupAtomic contextAtomic))
  have lastAtomic : (Prenex.mk (unfoldedG + unfolded₁) (restG ++ (rest₁.map (rename (shiftAbove 0 unfoldedG)) ++
      context.map (rename (relabelG ∘ rho))))).Atomic block.toBlock :=
    appendAtomic _ _ restGAtomic (appendAtomic _ _ (renamedAtomic _ _ rest₁Atomic) (renamedAtomic _ _ contextAtomic))
  calc normal block ⟨count, othersRest ++ othersGroup ++ context⟩
      = normal block ⟨inner + own.length, (first.renameOuter close).components⟩ := mixedEq
    _ = normal block ⟨unfolded₁ + own.length, moved⟩ := closedEq
    _ = normal block ⟨own.length + unfolded₁, moved.map (rename swap)⟩ := swapEq
    _ = normal block ⟨own.length + unfolded₁, othersGroup.map (rename rho) ++ extraG⟩ := by
        rw [swappedComponents]
        refine normal_perm fresh restrictFresh ?_ swappedAtomic
        rw [List.map_append, extraGIs]
        simpa [List.append_assoc] using
          (List.perm_append_comm (l₁ := rest₁.map (rename (shiftAbove 0 own.length)))
            (l₂ := othersGroup.map (rename rho))).append_right (context.map (rename rho))
    _ = normal block ⟨unfoldedG + unfolded₁, restG ++ extraG.map (rename relabelG)⟩ := groupClosed
    _ = normal block ⟨unfoldedG + unfolded₁, (rest₁.map (rename (shiftAbove 0 unfoldedG)) ++ restG) ++
          context.map (rename (relabelG ∘ rho))⟩ := by
        rw [extraGRenamed]
        refine normal_perm fresh restrictFresh ?_ lastAtomic
        simpa [List.append_assoc] using
          (List.perm_append_comm (l₁ := restG) (l₂ := rest₁.map (rename (shiftAbove 0 unfoldedG)))).append_right
            (context.map (rename (relabelG ∘ rho)))

/-- **A copy group meeting the parts and anchors is unfolded from its replicated component.** The block without the
group, the replicated component made an anchor and the group's own restrictions dropped, exposes its parts and
anchors; unfolding the replicated component puts the canonical form of its copy beside them, and the group's own
block, whose canonical form that is, exposes the group's parts and anchors within the copy. -/
theorem exposes_step {count ceiling : Nat} {tagged : List (Pattern × Role)}
    (recurse : ∀ {count' ceiling' : Nat} {tagged' : List (Pattern × Role)}, tagged'.length < tagged.length →
      (Prenex.mk count' (tagged'.map Prod.fst)).Atomic block.toBlock →
      (∀ item ∈ tagged', item.2 = .part → isReplicated block item.1 = false) →
      (∀ item ∈ tagged', item.2 = .anchor → isReplicated block item.1 = true) →
      (∀ item ∈ tagged', isReplicated block item.1 = true → height block item.1 < ceiling') →
      Exposes block count' tagged' ((tagged'.map (weight block ceiling')).sum))
    (atomic : (Prenex.mk count (tagged.map Prod.fst)).Atomic block.toBlock)
    (plain : ∀ item ∈ tagged, item.2 = .part → isReplicated block item.1 = false)
    (anchored : ∀ item ∈ tagged, item.2 = .anchor → isReplicated block item.1 = true)
    (low : ∀ item ∈ tagged, isReplicated block item.1 = true → height block item.1 < ceiling)
    {q : Nat} {group : Finset Nat}
    (isCopy : (blockSystem block ⟨count, tagged.map Prod.fst⟩).IsCopy
      (places ⟨count, tagged.map Prod.fst⟩).toFinset q group)
    (meets : ∃ place ∈ group, (taggedAt block tagged place).2 ≠ .other) :
    Exposes block count tagged ((tagged.map (weight block ceiling)).sum) := by
  classical
  /- The block and the copy group. -/
  have valueIs : ∀ place, placeValue block (tagged.map Prod.fst) place = (taggedAt block tagged place).1 :=
    placeValue_fst tagged
  have inPlaces : ∀ place ∈ (places (⟨count, tagged.map Prod.fst⟩ : Prenex)).toFinset, place < tagged.length := by
    intro place member
    simpa [places] using member
  have placesIs : (places (⟨count, tagged.map Prod.fst⟩ : Prenex)).toFinset = (List.range tagged.length).toFinset := by
    simp [places]
  have qInside : q < tagged.length := inPlaces q isCopy.isLive
  have groupInside : ∀ place ∈ group, place < tagged.length := fun place member =>
    inPlaces place (Finset.mem_erase.mp (isCopy.isGroup.subset member)).2
  have qNotGroup : q ∉ group := fun member => (Finset.mem_erase.mp (isCopy.isGroup.subset member)).1 rfl
  have qReplicated : isReplicated block (taggedAt block tagged q).1 = true := by
    have replicated := isCopy.isReplicated
    simp only [blockSystem, absorptionSystem] at replicated
    rwa [valueIs] at replicated
  obtain ⟨argument, qIs⟩ := replicated_shape qReplicated
  have qNotPart : (taggedAt block tagged q).2 ≠ .part := fun isPart => by
    rw [plain _ (taggedAt_mem qInside) isPart] at qReplicated
    exact Bool.false_ne_true qReplicated
  /- The restrictions the group owns, and the others in their order. -/
  set own := ownOf block ⟨count, tagged.map Prod.fst⟩ q group with ownIs
  have ownNodup : own.Nodup := ownOf_nodup
  have ownBelow : ∀ index ∈ own, index < count := fun index member => ownOf_lt member
  have ownLe : own.length ≤ count := length_le_of_inside ownNodup ownBelow
  set outside := outsideOf count own with outsideIs
  have outsideLength : outside.length = count - own.length := outsideOf_length ownNodup ownBelow
  set gi := Prenex.groupIndex count outside with giIs
  have giInside : ∀ index < count, gi index = outside.idxOf index := fun index below => groupIndex_below below
  have giBelow : ∀ index < count, index ∉ own → gi index < outside.length := fun index below notOwn => by
    rw [giInside index below]
    exact List.idxOf_lt_length_of_mem (mem_outsideOf.mpr ⟨below, notOwn⟩)
  have giOuter : ∀ index, gi (count + index) = outside.length + index := fun index => by
    rw [giIs, groupIndex_above (by omega)]
    omega
  have giAbove : ∀ index, count ≤ index → gi index = outside.length + (index - count) := fun index above => by
    have := giOuter (index - count)
    rwa [show count + (index - count) = index by omega] at this
  have giInjective : ∀ first second, (first < count → first ∉ own) → (second < count → second ∉ own) →
      gi first = gi second → first = second := by
    intro first second firstOk secondOk same
    by_cases firstBelow : first < count <;> by_cases secondBelow : second < count
    · rw [giInside first firstBelow, giInside second secondBelow] at same
      exact (List.idxOf_inj (mem_outsideOf.mpr ⟨firstBelow, firstOk firstBelow⟩)).mp same
    · have := giBelow first firstBelow (firstOk firstBelow)
      rw [giAbove second (by omega)] at same
      omega
    · have := giBelow second secondBelow (secondOk secondBelow)
      rw [giAbove first (by omega)] at same
      omega
    · rw [giAbove first (by omega), giAbove second (by omega)] at same
      omega
  /- What mentions the group's own restrictions. -/
  have qOwnFree : ∀ index ∈ own, mentions index (taggedAt block tagged q).1 = false := fun index member => by
    rw [← valueIs]
    exact not_mentions_own_p member
  have outsideOwnFree : ∀ place < tagged.length, place ∉ group → ∀ index ∈ own,
      mentions index (taggedAt block tagged place).1 = false := by
    intro place inside notGroup index member
    by_cases isQ : place = q
    · subst isQ
      exact qOwnFree index member
    · rw [← valueIs]
      exact not_mentions_own isCopy (by simpa [places] using inside) notGroup isQ member
  have groupToQ : ∀ place ∈ group, ∀ index < count, index ∉ own →
      mentions index (taggedAt block tagged place).1 = true → mentions index (taggedAt block tagged q).1 = true := by
    intro place inGroup index below notOwn mentioned
    rw [← valueIs] at mentioned ⊢
    exact mentions_of_group inGroup below notOwn mentioned
  have freeNotOwn : ∀ place < tagged.length, place ∉ group → ∀ index,
      FreeIn index (taggedAt block tagged place).1 → index < count → index ∉ own := by
    intro place inside notGroup index free _ inOwn
    have notMentioned := outsideOwnFree place inside notGroup index inOwn
    rw [(mentions_iff _ _).mpr free] at notMentioned
    exact absurd notMentioned (by decide)
  /- The block without the group. -/
  set outList := (List.range tagged.length).filter (· ∉ group) with outListIs
  have outListNodup : outList.Nodup := List.nodup_range.filter _
  have mem_outList : ∀ place, place ∈ outList ↔ place < tagged.length ∧ place ∉ group := by
    intro place
    simp [outListIs]
  set restTagged := outList.map fun place => (rename gi (taggedAt block tagged place).1,
    if place = q then Role.anchor else (taggedAt block tagged place).2) with restTaggedIs
  have mem_restTagged : ∀ item, item ∈ restTagged ↔ ∃ place ∈ outList, (rename gi (taggedAt block tagged place).1,
      if place = q then Role.anchor else (taggedAt block tagged place).2) = item := by
    intro item
    simp only [restTaggedIs, List.mem_map]
  have restFst : restTagged.map Prod.fst = (outList.map (placeValue block (tagged.map Prod.fst))).map (rename gi) := by
    simp only [restTaggedIs, List.map_map]
    exact List.map_congr_left fun place _ => by simp [valueIs]
  have giOnOut : ∀ place ∈ outList, ∀ first second, FreeIn first (taggedAt block tagged place).1 →
      FreeIn second (taggedAt block tagged place).1 → gi first = gi second → first = second := by
    intro place inOut first second firstFree secondFree same
    obtain ⟨inside, notGroup⟩ := (mem_outList place).mp inOut
    exact giInjective first second (freeNotOwn place inside notGroup first firstFree)
      (freeNotOwn place inside notGroup second secondFree) same
  have restNormal : normal block ⟨outside.length, restTagged.map Prod.fst⟩ =
      normal block ⟨count, tagged.map Prod.fst⟩ := by
    have restrictedAtomic : (restrictTo block ⟨count, tagged.map Prod.fst⟩ outList).Atomic block.toBlock :=
      restrictTo_atomic atomic fun place member => by simpa using ((mem_outList place).mp member).1
    have usedNotOwn : ∀ index ∈ usedOf ⟨count, outList.map (placeValue block (tagged.map Prod.fst))⟩,
        index < count ∧ index ∉ own := by
      intro index member
      obtain ⟨inside, mentionedAny⟩ := List.mem_filter.mp member
      obtain ⟨component, inComponents, mentioned⟩ := List.any_eq_true.mp mentionedAny
      obtain ⟨place, inOut, rfl⟩ := List.mem_map.mp inComponents
      obtain ⟨placeInside, notGroup⟩ := (mem_outList place).mp inOut
      refine ⟨List.mem_range.mp inside, fun inOwn => ?_⟩
      rw [valueIs, outsideOwnFree place placeInside notGroup index inOwn] at mentioned
      exact Bool.false_ne_true mentioned
    rw [restFst]
    calc normal block ⟨outside.length, (outList.map (placeValue block (tagged.map Prod.fst))).map (rename gi)⟩
        = normal block (restrictTo block ⟨count, tagged.map Prod.fst⟩ outList) := by
          refine normal_rename_used fresh restrictFresh restrictedAtomic ?_ ?_ giOuter
          · intro first inFirst second inSecond same
            exact giInjective first second (fun _ => (usedNotOwn first inFirst).2)
              (fun _ => (usedNotOwn second inSecond).2) same
          · intro index member
            exact giBelow index (usedNotOwn index member).1 (usedNotOwn index member).2
      _ = normal block (restrictTo block ⟨count, tagged.map Prod.fst⟩ (List.range tagged.length)) := by
          refine normal_restrict_from fresh restrictFresh atomic List.nodup_range (by simp) outListNodup
            (fun place member => List.mem_range.mpr ((mem_outList place).mp member).1) ?_
          have removed : (List.range tagged.length).toFinset \ group = outList.toFinset := by
            ext place
            simp [outListIs]
          rw [← removed]
          exact .step (p := q) (copied := group) (by rw [← placesIs]; exact isCopy) .refl
      _ = normal block ⟨count, tagged.map Prod.fst⟩ := by
          rw [restrictTo_tagged, map_taggedAt_range]
  have restShorter : restTagged.length < tagged.length := by
    rw [restTaggedIs, List.length_map, outListIs]
    obtain ⟨member, inGroup⟩ := isCopy.isGroup.nonempty
    have shorter : ((List.range tagged.length).filter (· ∉ group)).length < (List.range tagged.length).length :=
      List.length_filter_lt_length_iff_exists.mpr
        ⟨member, List.mem_range.mpr (groupInside member inGroup), by simp [inGroup]⟩
    simpa using shorter
  have restAtomic : (Prenex.mk outside.length (restTagged.map Prod.fst)).Atomic block.toBlock := by
    intro component member
    rw [restFst] at member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    obtain ⟨place, inOut, rfl⟩ := List.mem_map.mp inOriginal
    rw [valueIs]
    exact atomic_rename (atomic _ (taggedAt_fst_mem ((mem_outList place).mp inOut).1)) gi
  have restPlain : ∀ item ∈ restTagged, item.2 = .part → isReplicated block item.1 = false := by
    intro item member isPart
    obtain ⟨place, inOut, rfl⟩ := (mem_restTagged item).mp member
    by_cases isQ : place = q
    · simp [isQ] at isPart
    · simp only [isQ, if_false] at isPart ⊢
      rw [isReplicated_rename]
      exact plain _ (taggedAt_mem ((mem_outList place).mp inOut).1) isPart
  have restAnchored : ∀ item ∈ restTagged, item.2 = .anchor → isReplicated block item.1 = true := by
    intro item member isAnchor
    obtain ⟨place, inOut, rfl⟩ := (mem_restTagged item).mp member
    simp only [isReplicated_rename]
    by_cases isQ : place = q
    · subst isQ
      exact qReplicated
    · simp only [isQ, if_false] at isAnchor
      exact anchored _ (taggedAt_mem ((mem_outList place).mp inOut).1) isAnchor
  have restLow : ∀ item ∈ restTagged, isReplicated block item.1 = true → height block item.1 < ceiling := by
    intro item member replicated
    obtain ⟨place, inOut, rfl⟩ := (mem_restTagged item).mp member
    simp only [isReplicated_rename] at replicated ⊢
    rw [height_rename_on fresh restrictFresh (giOnOut place inOut)]
    exact low _ (taggedAt_mem ((mem_outList place).mp inOut).1) replicated
  obtain ⟨unfolded₁, relabel₁, exposed₁, rest₁, unfolds₁, perm₁, parts₁, anchors₁, outer₁, below₁, injective₁,
    aligned₁⟩ := recurse restShorter restAtomic restPlain restAnchored restLow
  /- The replicated component, exposed. -/
  have qInOut : q ∈ outList := (mem_outList q).mpr ⟨qInside, qNotGroup⟩
  have qAnchor : rename gi (taggedAt block tagged q).1 ∈ anchorsOf restTagged :=
    mem_anchorsOf.mpr ((mem_restTagged _).mpr ⟨q, qInOut, by simp⟩)
  have attachedByQ : ∀ index < count, mentions index (taggedAt block tagged q).1 = true →
      Attached restTagged (gi index) := by
    intro index _ mentioned
    refine ⟨_, List.mem_append_right _ qAnchor, ?_⟩
    rw [mentions_iff, freeIn_rename]
    exact ⟨index, (mentions_iff _ _).mp mentioned, rfl⟩
  obtain ⟨shown, shownIn, shownAlike⟩ := anchors₁ _ qAnchor
  have renamedQ : rename relabel₁ (rename gi (taggedAt block tagged q).1) =
      .apply block.replicate [rename relabel₁ (rename gi argument)] := by
    rw [qIs, rename_apply, rename_apply]
    rfl
  have shownReplicated : isReplicated block shown = true := by
    rw [shownAlike.2.1, renamedQ]
    simp [isReplicated]
  obtain ⟨copyArgument, shownIs⟩ := replicated_shape shownReplicated
  have copyNormal : normal block (decompose block.toBlock copyArgument) =
      normal block (decompose block.toBlock (rename relabel₁ (rename gi argument))) := by
    have same := shownAlike.2.2.2 shownReplicated id Function.injective_id
    rw [shownIs, renamedQ, rename_id, rename_id] at same
    simp only [argumentOf?] at same
    unfold canonicalOf at same
    exact toPattern_injective (normal_atomic fresh restrictFresh (decompose_atomic _))
      (normal_atomic fresh restrictFresh (decompose_atomic _)) same
  have relabel₁On : ∀ first second, (first < outside.length → Attached restTagged first) →
      (second < outside.length → Attached restTagged second) → relabel₁ first = relabel₁ second → first = second := by
    intro first second firstOk secondOk same
    have outerAt : ∀ index, outside.length ≤ index → relabel₁ index = unfolded₁.count + (index - outside.length) :=
      fun index above => by
        have := outer₁ (index - outside.length)
        rwa [show outside.length + (index - outside.length) = index by omega] at this
    by_cases firstBelow : first < outside.length <;> by_cases secondBelow : second < outside.length
    · exact injective₁ first firstBelow second secondBelow (firstOk firstBelow) (secondOk secondBelow) same
    · have := below₁ first firstBelow (firstOk firstBelow)
      rw [outerAt second (by omega)] at same
      omega
    · have := below₁ second secondBelow (secondOk secondBelow)
      rw [outerAt first (by omega)] at same
      omega
    · rw [outerAt first (by omega), outerAt second (by omega)] at same
      omega
  /- The group's own block, in the frame of the unfolding. -/
  set rho := liftIndex own.length relabel₁ ∘ Prenex.permute count (splitOrder count outside own) with rhoIs
  have rhoOwn : ∀ index ∈ own, rho index = own.idxOf index := fun index member => by
    simp only [rhoIs, Function.comp_apply]
    rw [permute_split_inside member (ownBelow index member)]
    simp only [liftIndex, if_pos (List.idxOf_lt_length_of_mem member)]
  have rhoOutside : ∀ index < count, index ∉ own → rho index = relabel₁ (gi index) + own.length :=
    fun index below notOwn => by
      simp only [rhoIs, Function.comp_apply]
      rw [permute_split_outside notOwn below, giInside index below]
      simp only [liftIndex]
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
  have rhoAbove : ∀ index, count ≤ index → rho index = unfolded₁.count + (index - count) + own.length :=
    fun index above => by
      simp only [rhoIs, Function.comp_apply]
      rw [permute_split_above above]
      simp only [liftIndex]
      rw [if_neg (by omega), show index - own.length = outside.length + (index - count) by omega, outer₁]
  set groupPlaces := group.sort (· ≤ ·) with groupPlacesIs
  have groupPlacesNodup : groupPlaces.Nodup := Finset.sort_nodup _ _
  have mem_groupPlaces : ∀ place, place ∈ groupPlaces ↔ place ∈ group := fun place => Finset.mem_sort _
  set groupTagged := groupPlaces.map fun place => (rename rho (taggedAt block tagged place).1,
    (taggedAt block tagged place).2) with groupTaggedIs
  have mem_groupTagged : ∀ item, item ∈ groupTagged ↔ ∃ place ∈ groupPlaces,
      (rename rho (taggedAt block tagged place).1, (taggedAt block tagged place).2) = item := by
    intro item
    simp only [groupTaggedIs, List.mem_map]
  have groupBlockIs : (Prenex.mk own.length (groupTagged.map Prod.fst)) =
      (groupBlock block ⟨count, tagged.map Prod.fst⟩ q group).renameOuter relabel₁ := by
    simp only [groupBlock, copyBlock, Prenex.renameOuter, groupTaggedIs, List.map_map, Prenex.mk.injEq]
    refine ⟨rfl, List.map_congr_left fun place _ => ?_⟩
    simp only [Function.comp_apply, rename_comp, valueIs, rhoIs]
    rfl
  have groupBlockAtomic : (groupBlock block ⟨count, tagged.map Prod.fst⟩ q group).Atomic block.toBlock := by
    intro component member
    simp only [groupBlock, copyBlock, List.map_map, List.mem_map, Function.comp_apply] at member
    obtain ⟨place, inSorted, rfl⟩ := member
    rw [valueIs]
    exact atomic_rename (atomic _ (taggedAt_fst_mem (groupInside place ((mem_groupPlaces place).mp inSorted)))) _
  have groupFree : ∀ index, (groupBlock block ⟨count, tagged.map Prod.fst⟩ q group).FreePast index →
      index < outside.length → Attached restTagged index := by
    rintro index ⟨component, member, free⟩ below
    simp only [groupBlock, copyBlock, List.map_map, List.mem_map, Function.comp_apply] at member free
    rw [← ownIs] at member free
    rw [← outsideIs] at member
    obtain ⟨place, inSorted, rfl⟩ := member
    rw [freeIn_rename] at free
    obtain ⟨original, originalFree, maps⟩ := free
    have inGroup := (mem_groupPlaces place).mp inSorted
    by_cases originalBelow : original < count
    · by_cases inOwn : original ∈ own
      · rw [permute_split_inside inOwn originalBelow] at maps
        have := List.idxOf_lt_length_of_mem inOwn
        omega
      · rw [permute_split_outside inOwn originalBelow, ← outsideIs] at maps
        have indexIs : index = gi original := by
          rw [giInside original originalBelow]
          omega
        rw [indexIs]
        rw [valueIs] at originalFree
        exact attachedByQ original originalBelow (groupToQ place inGroup original originalBelow inOwn
          ((mentions_iff _ _).mpr originalFree))
    · rw [permute_split_above (by omega)] at maps
      omega
  have argumentFree : ∀ index, (decompose block.toBlock (rename gi argument)).FreePast index →
      index < outside.length → Attached restTagged index := by
    intro index past below
    have free := (freeIn_decompose (block := block.toBlock) _ index).mpr past
    rw [freeIn_rename] at free
    obtain ⟨original, originalFree, rfl⟩ := free
    by_cases originalBelow : original < count
    · have mentioned : mentions original (taggedAt block tagged q).1 = true := by
        rw [qIs, mentions_iff, freeIn_apply]
        exact ⟨argument, List.mem_singleton_self _, originalFree⟩
      exact attachedByQ original originalBelow mentioned
    · rw [giAbove original (by omega)] at below
      omega
  have argumentIs : argumentOf? (placeValue block (tagged.map Prod.fst) q) = argument := by
    rw [valueIs, qIs]
    rfl
  have groupNormal : normal block ⟨own.length, groupTagged.map Prod.fst⟩ =
      normal block (decompose block.toBlock copyArgument) := by
    rw [groupBlockIs, ← normal_renameOuter_normal_on fresh restrictFresh groupBlockAtomic
      (fun first second firstPast secondPast same => relabel₁On first second (groupFree first firstPast)
        (groupFree second secondPast) same),
      normal_groupBlock fresh restrictFresh atomic (Finset.Subset.refl _) isCopy, argumentIs,
      normal_renameOuter_normal_on fresh restrictFresh (decompose_atomic _)
        (fun first second firstPast secondPast same => relabel₁On first second (argumentFree first firstPast)
          (argumentFree second secondPast) same),
      ← decompose_renameOuter, copyNormal]
  /- The names of the group's components, in the frame of the unfolding. -/
  have groupNames : ∀ place ∈ group, ∀ index, FreeIn index (taggedAt block tagged place).1 →
      (index < count ∧ index ∈ own) ∨ (index < count ∧ index ∉ own ∧ Attached restTagged (gi index)) ∨
        count ≤ index := by
    intro place inGroup index free
    by_cases below : index < count
    · by_cases inOwn : index ∈ own
      · exact .inl ⟨below, inOwn⟩
      · exact .inr (.inl ⟨below, inOwn, attachedByQ index below
          (groupToQ place inGroup index below inOwn ((mentions_iff _ _).mpr free))⟩)
    · exact .inr (.inr (by omega))
  have rhoInjective : ∀ first second,
      ((first < count ∧ first ∈ own) ∨ (first < count ∧ first ∉ own ∧ Attached restTagged (gi first)) ∨
        count ≤ first) →
      ((second < count ∧ second ∈ own) ∨ (second < count ∧ second ∉ own ∧ Attached restTagged (gi second)) ∨
        count ≤ second) →
      rho first = rho second → first = second := by
    intro first second firstKind secondKind same
    have ownRange : ∀ index ∈ own, rho index < own.length := fun index member => by
      rw [rhoOwn index member]
      exact List.idxOf_lt_length_of_mem member
    have outsideRange : ∀ index < count, index ∉ own → Attached restTagged (gi index) →
        own.length ≤ rho index ∧ rho index < unfolded₁.count + own.length := fun index below notOwn attached => by
      rw [rhoOutside index below notOwn]
      have := below₁ (gi index) (giBelow index below notOwn) attached
      omega
    have aboveRange : ∀ index, count ≤ index → unfolded₁.count + own.length ≤ rho index := fun index above => by
      rw [rhoAbove index above]
      omega
    rcases firstKind with ⟨firstBelow, firstOwn⟩ | ⟨firstBelow, firstNotOwn, firstAttached⟩ | firstAbove <;>
      rcases secondKind with ⟨secondBelow, secondOwn⟩ | ⟨secondBelow, secondNotOwn, secondAttached⟩ | secondAbove
    · rw [rhoOwn first firstOwn, rhoOwn second secondOwn] at same
      exact (List.idxOf_inj firstOwn).mp same
    · have := ownRange first firstOwn
      have := outsideRange second secondBelow secondNotOwn secondAttached
      omega
    · have := ownRange first firstOwn
      have := aboveRange second secondAbove
      omega
    · have := outsideRange first firstBelow firstNotOwn firstAttached
      have := ownRange second secondOwn
      omega
    · rw [rhoOutside first firstBelow firstNotOwn, rhoOutside second secondBelow secondNotOwn] at same
      have := injective₁ (gi first) (giBelow first firstBelow firstNotOwn) (gi second)
        (giBelow second secondBelow secondNotOwn) firstAttached secondAttached (by omega)
      exact giInjective first second (fun _ => firstNotOwn) (fun _ => secondNotOwn) this
    · have := outsideRange first firstBelow firstNotOwn firstAttached
      have := aboveRange second secondAbove
      omega
    · have := aboveRange first firstAbove
      have := ownRange second secondOwn
      omega
    · have := aboveRange first firstAbove
      have := outsideRange second secondBelow secondNotOwn secondAttached
      omega
    · rw [rhoAbove first firstAbove, rhoAbove second secondAbove] at same
      omega
  /- The group's block exposes its parts and anchors. -/
  have groupShorter : groupTagged.length < tagged.length := by
    rw [groupTaggedIs, List.length_map, groupPlacesIs, Finset.length_sort]
    have inside : group ⊆ (List.range tagged.length).toFinset.erase q := fun place member =>
      Finset.mem_erase.mpr ⟨fun same => qNotGroup (same ▸ member),
        List.mem_toFinset.mpr (List.mem_range.mpr (groupInside place member))⟩
    have := Finset.card_le_card inside
    rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr (List.mem_range.mpr qInside)),
      List.toFinset_card_of_nodup List.nodup_range, List.length_range] at this
    omega
  have groupAtomic : (Prenex.mk own.length (groupTagged.map Prod.fst)).Atomic block.toBlock := by
    intro component member
    simp only [groupTaggedIs, List.map_map, List.mem_map, Function.comp_apply] at member
    obtain ⟨place, inSorted, rfl⟩ := member
    exact atomic_rename (atomic _ (taggedAt_fst_mem (groupInside place ((mem_groupPlaces place).mp inSorted)))) _
  have groupPlain : ∀ item ∈ groupTagged, item.2 = .part → isReplicated block item.1 = false := by
    intro item member isPart
    obtain ⟨place, inSorted, rfl⟩ := (mem_groupTagged item).mp member
    rw [isReplicated_rename]
    exact plain _ (taggedAt_mem (groupInside place ((mem_groupPlaces place).mp inSorted))) isPart
  have groupAnchored : ∀ item ∈ groupTagged, item.2 = .anchor → isReplicated block item.1 = true := by
    intro item member isAnchor
    obtain ⟨place, inSorted, rfl⟩ := (mem_groupTagged item).mp member
    rw [isReplicated_rename]
    exact anchored _ (taggedAt_mem (groupInside place ((mem_groupPlaces place).mp inSorted))) isAnchor
  have lowerLaw : ∀ place ∈ group, isReplicated block (taggedAt block tagged place).1 = true →
      height block (taggedAt block tagged place).1 < height block (taggedAt block tagged q).1 := by
    intro place inGroup replicated
    have test : CopyTest block (canonicalOf block) count (placeValue block (tagged.map Prod.fst) q)
        (asGroup (allowedFor count (placeValue block (tagged.map Prod.fst) q)) count
          (placeValue block (tagged.map Prod.fst)) (group.sort (· ≤ ·))) := isCopy.isCopy
    obtain ⟨-, -, smaller, -⟩ := test
    have member : placeValue block (tagged.map Prod.fst) place ∈
        (asGroup (allowedFor count (placeValue block (tagged.map Prod.fst) q)) count
          (placeValue block (tagged.map Prod.fst)) (group.sort (· ≤ ·))).components :=
      List.mem_map_of_mem ((Finset.mem_sort _).mpr inGroup)
    have result := smaller _ member (by rw [valueIs]; exact replicated)
    unfold height
    rw [valueIs, valueIs] at result
    exact result
  have groupLow : ∀ item ∈ groupTagged, isReplicated block item.1 = true →
      height block item.1 < height block (taggedAt block tagged q).1 := by
    intro item member replicated
    obtain ⟨place, inSorted, rfl⟩ := (mem_groupTagged item).mp member
    have inGroup := (mem_groupPlaces place).mp inSorted
    simp only [isReplicated_rename] at replicated ⊢
    rw [height_rename_on fresh restrictFresh fun first second firstFree secondFree same =>
      rhoInjective first second (groupNames place inGroup first firstFree) (groupNames place inGroup second secondFree)
        same]
    exact lowerLaw place inGroup replicated
  obtain ⟨unfoldedG, relabelG, exposedG, restG, unfoldsG, permG, partsG, anchorsG, outerG, belowG, injectiveG,
    alignedG⟩ := recurse groupShorter groupAtomic groupPlain groupAnchored groupLow
  /- The unfolding: the block without the group, the replicated component unfolded, the group within the copy. -/
  have shownMember : Pattern.apply block.replicate [copyArgument] ∈ unfolded₁.components := by
    rw [← shownIs]
    exact perm₁.symm.subset (List.mem_append_right _ shownIn)
  have unfolds : UnfoldsWithin block ((restTagged.map (weight block ceiling)).sum + 1 +
      (groupTagged.map (weight block (height block (taggedAt block tagged q).1))).sum)
      (normal block ⟨count, tagged.map Prod.fst⟩) (unfolded₁.unfoldWith unfoldedG) := by
    rw [← restNormal]
    have single := UnfoldsWithin.single (block := block) shownMember
    rw [← groupNormal] at single
    exact (unfolds₁.trans single).trans (unfoldsG.unfoldWith unfolded₁)
  /- The places: those outside the group and those in it. -/
  have placesPerm : (outList ++ groupPlaces).Perm (List.range tagged.length) := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_append.mpr ⟨outListNodup, groupPlacesNodup, ?_⟩)
      List.nodup_range).mpr fun place => ?_
    · intro first inOut second inGroup same
      subst same
      exact ((mem_outList first).mp inOut).2 ((mem_groupPlaces first).mp inGroup)
    · simp only [List.mem_append, mem_outList, mem_groupPlaces, List.mem_range]
      constructor
      · rintro (⟨inside, _⟩ | inGroup)
        · exact inside
        · exact groupInside place inGroup
      · intro inside
        by_cases inGroup : place ∈ group
        · exact .inr inGroup
        · exact .inl ⟨inside, inGroup⟩
  have taggedPerm : ((outList ++ groupPlaces).map (taggedAt block tagged)).Perm tagged := by
    have := placesPerm.map (taggedAt block tagged)
    rwa [map_taggedAt_range] at this
  /- The weights. -/
  have qLow : height block (taggedAt block tagged q).1 < ceiling := low _ (taggedAt_mem qInside) qReplicated
  have weights := step_weights (block := block) (ceiling := ceiling) (top := height block (taggedAt block tagged q).1)
    (q := q) (restItem := fun place => (rename gi (taggedAt block tagged place).1,
      if place = q then Role.anchor else (taggedAt block tagged place).2))
    (groupItem := fun place => (rename rho (taggedAt block tagged place).1, (taggedAt block tagged place).2))
    placesPerm outListNodup qInOut
    (fun place inOut notQ => by
      simp only [if_neg notQ]
      cases roleIs : (taggedAt block tagged place).2 with
      | part => simp only [weight, roleIs]
      | anchor =>
          simp only [weight, roleIs]
          rw [height_rename_on fresh restrictFresh (giOnOut place inOut)]
      | other => simp only [weight, roleIs])
    (by
      simp only [weight, ↓reduceIte]
      rw [height_rename_on fresh restrictFresh (giOnOut q qInOut)])
    (fun place member => by
      have inGroup := (mem_groupPlaces place).mp member
      cases roleIs : (taggedAt block tagged place).2 with
      | part => simp only [weight, roleIs]
      | anchor =>
          simp only [weight, roleIs]
          rw [height_rename_on fresh restrictFresh fun first second firstFree secondFree same =>
            rhoInjective first second (groupNames place inGroup first firstFree)
              (groupNames place inGroup second secondFree) same]
      | other => simp only [weight, roleIs])
    qLow
    (fun place member isAnchor => lowerLaw place ((mem_groupPlaces place).mp member)
      (anchored _ (taggedAt_mem (groupInside place ((mem_groupPlaces place).mp member))) isAnchor))
    (by
      obtain ⟨met, metIn, metRole⟩ := meets
      exact ⟨met, (mem_groupPlaces met).mpr metIn, metRole⟩)
  have unfoldsWithin := unfolds.mono weights
  /- How the unfolding reads the block's names. -/
  set relabel := relabelG ∘ rho with relabelIs
  have relabelRest : ∀ index, (index < count → index ∉ own ∧ Attached restTagged (gi index)) →
      relabel index = relabel₁ (gi index) + unfoldedG.count := by
    intro index ok
    simp only [relabelIs, Function.comp_apply]
    by_cases below : index < count
    · obtain ⟨notOwn, _⟩ := ok below
      rw [rhoOutside index below notOwn, Nat.add_comm, outerG]
      omega
    · rw [rhoAbove index (by omega), giAbove index (by omega), outer₁,
        show unfolded₁.count + (index - count) + own.length = own.length + (unfolded₁.count + (index - count)) by omega,
        outerG]
      omega
  have restHeld : ∀ place ∈ outList, (taggedAt block tagged place).2 ≠ .other →
      rename gi (taggedAt block tagged place).1 ∈ partsOf restTagged ++ anchorsOf restTagged := by
    intro place inOut role
    by_cases isQ : place = q
    · subst isQ
      exact List.mem_append_right _ qAnchor
    · cases roleIs : (taggedAt block tagged place).2 with
      | part =>
          exact List.mem_append_left _ (mem_partsOf.mpr ((mem_restTagged _).mpr ⟨place, inOut, by simp [isQ, roleIs]⟩))
      | anchor =>
          exact List.mem_append_right _
            (mem_anchorsOf.mpr ((mem_restTagged _).mpr ⟨place, inOut, by simp [isQ, roleIs]⟩))
      | other => exact absurd roleIs role
  have restNames : ∀ place ∈ outList, (taggedAt block tagged place).2 ≠ .other → ∀ index,
      FreeIn index (taggedAt block tagged place).1 → index < count → index ∉ own ∧ Attached restTagged (gi index) := by
    intro place inOut role index free below
    refine ⟨freeNotOwn place ((mem_outList place).mp inOut).1 ((mem_outList place).mp inOut).2 index free below,
      _, restHeld place inOut role, ?_⟩
    rw [mentions_iff, freeIn_rename]
    exact ⟨index, free, rfl⟩
  have shiftInjective : ∀ shift, Function.Injective (shiftAbove 0 shift) := fun shift first second same => by
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at same
    omega
  have restAlike : ∀ place ∈ outList, (taggedAt block tagged place).2 ≠ .other → ∀ shown₁,
      AlikeR block shown₁ (rename relabel₁ (rename gi (taggedAt block tagged place).1)) →
      AlikeR block (rename (shiftAbove 0 unfoldedG.count) shown₁) (rename relabel (taggedAt block tagged place).1) := by
    intro place inOut role shown₁ alike
    have lifted := alike.rename (shiftInjective unfoldedG.count)
    rw [rename_comp, rename_comp] at lifted
    have same : rename relabel (taggedAt block tagged place).1 =
        rename (shiftAbove 0 unfoldedG.count ∘ relabel₁ ∘ gi) (taggedAt block tagged place).1 := by
      apply rename_congr
      intro index free
      simp only [Function.comp_apply, shiftAbove, Nat.not_lt_zero, if_false]
      exact relabelRest index (restNames place inOut role index free)
    rw [same]
    exact lifted
  have groupHeld : ∀ place ∈ group, (taggedAt block tagged place).2 ≠ .other →
      rename rho (taggedAt block tagged place).1 ∈ partsOf groupTagged ++ anchorsOf groupTagged := by
    intro place inGroup role
    have inSorted := (mem_groupPlaces place).mpr inGroup
    cases roleIs : (taggedAt block tagged place).2 with
    | part =>
        exact List.mem_append_left _ (mem_partsOf.mpr ((mem_groupTagged _).mpr ⟨place, inSorted, by simp [roleIs]⟩))
    | anchor =>
        exact List.mem_append_right _
          (mem_anchorsOf.mpr ((mem_groupTagged _).mpr ⟨place, inSorted, by simp [roleIs]⟩))
    | other => exact absurd roleIs role
  have attachedSplit : ∀ index < count, Attached tagged index →
      (index ∈ own ∧ Attached groupTagged (own.idxOf index)) ∨ (index ∉ own ∧ Attached restTagged (gi index)) := by
    intro index below attached
    obtain ⟨held, member, mentioned⟩ := attached
    obtain ⟨place, inside, heldIs, role⟩ := exists_place_of_held (block := block) member
    subst heldIs
    by_cases inOwn : index ∈ own
    · have inGroup : place ∈ group := by
        by_contra notGroup
        rw [outsideOwnFree place inside notGroup index inOwn] at mentioned
        exact Bool.false_ne_true mentioned
      refine .inl ⟨inOwn, _, groupHeld place inGroup role, ?_⟩
      rw [mentions_iff, freeIn_rename]
      exact ⟨index, (mentions_iff _ _).mp mentioned, rhoOwn index inOwn⟩
    · refine .inr ⟨inOwn, ?_⟩
      by_cases inGroup : place ∈ group
      · exact attachedByQ index below (groupToQ place inGroup index below inOwn mentioned)
      · refine ⟨_, restHeld place ((mem_outList place).mpr ⟨inside, inGroup⟩) role, ?_⟩
        rw [mentions_iff, freeIn_rename]
        exact ⟨index, (mentions_iff _ _).mp mentioned, rfl⟩
  /- The parts, exposed. -/
  have restParts : partsOf restTagged = (partsOf (outList.map (taggedAt block tagged))).map (rename gi) := by
    rw [restTaggedIs]
    refine partsOf_map_places (fun place _ => ?_) (fun place _ => rfl)
    by_cases isQ : place = q
    · subst isQ
      simp only [↓reduceIte]
      exact ⟨fun isPart => absurd isPart (by decide), fun isPart => absurd isPart qNotPart⟩
    · simp only [if_neg isQ]
  have groupParts : partsOf groupTagged = (partsOf (groupPlaces.map (taggedAt block tagged))).map (rename rho) := by
    rw [groupTaggedIs]
    exact partsOf_map_places (fun place _ => Iff.rfl) (fun place _ => rfl)
  have partsRelated : List.Forall₂ (fun shown part => AlikeR block shown (rename relabel part))
      (exposed₁.map (rename (shiftAbove 0 unfoldedG.count)) ++ exposedG)
      (partsOf (outList.map (taggedAt block tagged)) ++ partsOf (groupPlaces.map (taggedAt block tagged))) := by
    refine List.rel_append ?_ ?_
    · rw [restParts, List.forall₂_map_right_iff] at parts₁
      rw [List.forall₂_map_left_iff]
      refine forall₂_imp_mem_right parts₁ fun shown part member alike => ?_
      obtain ⟨place, inOut, found⟩ := mem_partsOf_places (block := block) member
      have partIs : part = (taggedAt block tagged place).1 := by rw [found]
      have role : (taggedAt block tagged place).2 ≠ .other := by rw [found]; simp
      rw [partIs] at alike ⊢
      exact restAlike place inOut role shown alike
    · rw [groupParts, List.forall₂_map_right_iff] at partsG
      exact partsG.imp fun shown part alike => by rwa [rename_comp] at alike
  have partsPerm : (partsOf (outList.map (taggedAt block tagged)) ++
      partsOf (groupPlaces.map (taggedAt block tagged))).Perm (partsOf tagged) := by
    rw [← partsOf_append, ← List.map_append]
    exact partsOf_perm taggedPerm
  obtain ⟨exposed, exposedPerm, exposedRelated⟩ := forall₂_exists_perm partsRelated partsPerm
  /- The anchors, among the rest. -/
  have anchorsShown : ∀ anchor ∈ anchorsOf tagged,
      ∃ shown ∈ rest₁.map (rename (shiftAbove 0 unfoldedG.count)) ++ restG, AlikeR block shown (rename relabel anchor) := by
    intro anchor member
    obtain ⟨place, inside, found⟩ := List.getElem_of_mem (mem_anchorsOf.mp member)
    have atPlace : taggedAt block tagged place = (anchor, .anchor) := by rw [taggedAt_lt inside, found]
    by_cases inGroup : place ∈ group
    · have inG : rename rho anchor ∈ anchorsOf groupTagged :=
        mem_anchorsOf.mpr ((mem_groupTagged _).mpr ⟨place, (mem_groupPlaces place).mpr inGroup, by rw [atPlace]⟩)
      obtain ⟨shownG, inRestG, alikeG⟩ := anchorsG _ inG
      refine ⟨shownG, List.mem_append_right _ inRestG, ?_⟩
      rwa [rename_comp] at alikeG
    · have inOut : place ∈ outList := (mem_outList place).mpr ⟨inside, inGroup⟩
      have role : (taggedAt block tagged place).2 ≠ .other := by rw [atPlace]; simp
      have inRest : rename gi anchor ∈ anchorsOf restTagged := by
        refine mem_anchorsOf.mpr ((mem_restTagged _).mpr ⟨place, inOut, ?_⟩)
        by_cases isQ : place = q
        · simp only [if_pos isQ, atPlace]
        · simp only [if_neg isQ, atPlace]
      obtain ⟨shown₁, inRest₁, alike₁⟩ := anchors₁ _ inRest
      refine ⟨_, List.mem_append_left _ (List.mem_map_of_mem inRest₁), ?_⟩
      have alike := restAlike place inOut role shown₁ (by rw [atPlace]; exact alike₁)
      rwa [atPlace] at alike
  /- The names outside, and the restrictions the parts and anchors mention. -/
  have relabelOwn : ∀ index ∈ own, relabel index = relabelG (own.idxOf index) := fun index member => by
    simp only [relabelIs, Function.comp_apply, rhoOwn index member]
  have outerAll : ∀ index, relabel (count + index) = (unfolded₁.unfoldWith unfoldedG).count + index := by
    intro index
    rw [relabelRest (count + index) fun below => absurd below (by omega), giOuter, outer₁]
    simp only [Prenex.unfoldWith]
    omega
  have belowAll : ∀ index < count, Attached tagged index →
      relabel index < (unfolded₁.unfoldWith unfoldedG).count := by
    intro index below attached
    simp only [Prenex.unfoldWith]
    rcases attachedSplit index below attached with ⟨inOwn, attachedG⟩ | ⟨notOwn, attachedRest⟩
    · have := belowG (own.idxOf index) (List.idxOf_lt_length_of_mem inOwn) attachedG
      rw [relabelOwn index inOwn]
      omega
    · rw [relabelRest index fun _ => ⟨notOwn, attachedRest⟩]
      have := below₁ (gi index) (giBelow index below notOwn) attachedRest
      omega
  have injectiveAll : ∀ first < count, ∀ second < count, Attached tagged first → Attached tagged second →
      relabel first = relabel second → first = second := by
    intro first firstBelow second secondBelow firstAttached secondAttached same
    rcases attachedSplit first firstBelow firstAttached with ⟨firstOwn, firstG⟩ | ⟨firstNotOwn, firstRest⟩ <;>
      rcases attachedSplit second secondBelow secondAttached with ⟨secondOwn, secondG⟩ | ⟨secondNotOwn, secondRest⟩
    · rw [relabelOwn first firstOwn, relabelOwn second secondOwn] at same
      exact (List.idxOf_inj firstOwn).mp (injectiveG (own.idxOf first) (List.idxOf_lt_length_of_mem firstOwn)
        (own.idxOf second) (List.idxOf_lt_length_of_mem secondOwn) firstG secondG same)
    · have := belowG (own.idxOf first) (List.idxOf_lt_length_of_mem firstOwn) firstG
      rw [relabelOwn first firstOwn, relabelRest second fun _ => ⟨secondNotOwn, secondRest⟩] at same
      omega
    · have := belowG (own.idxOf second) (List.idxOf_lt_length_of_mem secondOwn) secondG
      rw [relabelRest first fun _ => ⟨firstNotOwn, firstRest⟩, relabelOwn second secondOwn] at same
      omega
    · rw [relabelRest first fun _ => ⟨firstNotOwn, firstRest⟩,
        relabelRest second fun _ => ⟨secondNotOwn, secondRest⟩] at same
      have sameRest := injective₁ (gi first) (giBelow first firstBelow firstNotOwn) (gi second)
        (giBelow second secondBelow secondNotOwn) firstRest secondRest (by omega)
      exact giInjective first second (fun _ => firstNotOwn) (fun _ => secondNotOwn) sameRest
  /- Every context reads alike. -/
  have unfolded₁Atomic : unfolded₁.Atomic block.toBlock :=
    unfolds₁.atomic fresh restrictFresh (normal_atomic fresh restrictFresh restAtomic)
  have unfoldedGAtomic : unfoldedG.Atomic block.toBlock :=
    unfoldsG.atomic fresh restrictFresh (normal_atomic fresh restrictFresh groupAtomic)
  have mem_othersPlaces : ∀ (places : List Nat) (component : Pattern),
      component ∈ othersOf (places.map (taggedAt block tagged)) → ∃ place ∈ places,
        (taggedAt block tagged place).1 = component := by
    intro places component member
    simp only [othersOf, List.mem_map, List.mem_filter] at member
    obtain ⟨item, ⟨⟨place, inPlaces, rfl⟩, _⟩, rfl⟩ := member
    exact ⟨place, inPlaces, rfl⟩
  have alignedAll : ∀ context : List Pattern,
      (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ context, ∀ index < count, mentions index component = true → Attached tagged index) →
      normal block ⟨count, othersOf tagged ++ context⟩ =
        normal block ⟨(unfolded₁.unfoldWith unfoldedG).count,
          (rest₁.map (rename (shiftAbove 0 unfoldedG.count)) ++ restG) ++ context.map (rename relabel)⟩ := by
    intro context contextAtomic attached
    have othersPerm : (othersOf (outList.map (taggedAt block tagged)) ++
        othersOf (groupPlaces.map (taggedAt block tagged))).Perm (othersOf tagged) := by
      rw [← othersOf_append, ← List.map_append]
      exact othersOf_perm taggedPerm
    have restOthers : othersOf restTagged =
        (othersOf (outList.map (taggedAt block tagged))).map (rename gi) := by
      rw [restTaggedIs]
      refine othersOf_map_places (fun place _ => ?_) (fun place _ => rfl)
      by_cases isQ : place = q
      · subst isQ
        simp only [↓reduceIte]
        exact ⟨fun isPart => absurd isPart (by decide), fun isPart => absurd isPart qNotPart⟩
      · simp only [if_neg isQ]
    have groupOthers : othersOf groupTagged =
        (othersOf (groupPlaces.map (taggedAt block tagged))).map (rename rho) := by
      rw [groupTaggedIs]
      exact othersOf_map_places (fun place _ => Iff.rfl) (fun place _ => rfl)
    have aligned := step_alignment (block := block) fresh restrictFresh ownNodup ownBelow
      (othersRest := othersOf (outList.map (taggedAt block tagged)))
      (othersGroup := othersOf (groupPlaces.map (taggedAt block tagged))) (context := context)
      (rest₁ := rest₁) (restG := restG) (relabel₁ := relabel₁) (relabelG := relabelG) (rho := rho)
      (unfolded₁ := unfolded₁.count) (unfoldedG := unfoldedG.count)
      (attached₁ := Attached restTagged) (attachedG := Attached groupTagged)
      (fun component member => by
        obtain ⟨place, inOut, rfl⟩ := mem_othersPlaces _ _ member
        exact atomic _ (taggedAt_fst_mem ((mem_outList place).mp inOut).1))
      (fun component member => by
        obtain ⟨place, inSorted, rfl⟩ := mem_othersPlaces _ _ member
        exact atomic _ (taggedAt_fst_mem (groupInside place ((mem_groupPlaces place).mp inSorted))))
      contextAtomic
      (fun component member => unfolded₁Atomic component (perm₁.symm.subset (List.mem_append_right _ member)))
      (fun component member => unfoldedGAtomic component (permG.symm.subset (List.mem_append_right _ member)))
      (fun component member index free below => by
        obtain ⟨place, inOut, rfl⟩ := mem_othersPlaces _ _ member
        exact freeNotOwn place ((mem_outList place).mp inOut).1 ((mem_outList place).mp inOut).2 index free below)
      (fun component member index free below notOwn => by
        obtain ⟨place, inSorted, rfl⟩ := mem_othersPlaces _ _ member
        exact attachedByQ index below (groupToQ place ((mem_groupPlaces place).mp inSorted) index below notOwn
          ((mentions_iff _ _).mpr free)))
      (fun component member index free below =>
        attachedSplit index below (attached component member index below ((mentions_iff _ _).mpr free)))
      outer₁ below₁
      (fun extra extraAtomic extraAttached => by
        rw [← restOthers]
        exact aligned₁ extra extraAtomic extraAttached)
      rhoOwn rhoOutside rhoAbove outerG
      (fun extra extraAtomic extraAttached => by
        rw [← groupOthers]
        exact alignedG extra extraAtomic extraAttached)
    have othersAtomic : (Prenex.mk count (othersOf tagged ++ context)).Atomic block.toBlock := by
      intro component member
      rcases List.mem_append.mp member with inOthers | inContext
      · simp only [othersOf, List.mem_map, List.mem_filter] at inOthers
        obtain ⟨item, ⟨inTagged, _⟩, rfl⟩ := inOthers
        exact atomic _ (List.mem_map_of_mem inTagged)
      · exact contextAtomic component inContext
    rw [normal_perm fresh restrictFresh (othersPerm.symm.append_right context) othersAtomic]
    rw [aligned]
    rfl
  /- The unfolding's components. -/
  have componentsPerm : (unfolded₁.unfoldWith unfoldedG).components.Perm
      (exposed ++ (rest₁.map (rename (shiftAbove 0 unfoldedG.count)) ++ restG)) := by
    have liftIs : liftBVars 0 unfoldedG.count = rename (shiftAbove 0 unfoldedG.count) :=
      funext (liftBVars_eq_rename 0 unfoldedG.count)
    simp only [Prenex.unfoldWith, liftIs]
    have first := perm₁.map (rename (shiftAbove 0 unfoldedG.count))
    rw [List.map_append] at first
    refine (first.append permG).trans ?_
    refine List.Perm.trans ?_ ((exposedPerm.append_right _))
    rw [List.perm_iff_count]
    intro component
    simp only [List.count_append]
    omega
  exact ⟨unfolded₁.unfoldWith unfoldedG, relabel, exposed, rest₁.map (rename (shiftAbove 0 unfoldedG.count)) ++ restG,
    unfoldsWithin, componentsPerm, exposedRelated, anchorsShown, outerAll, belowAll, injectiveAll, alignedAll⟩

end Step

/-! ## Exposure -/

/-- The components of some roles at the live places are those of the block, when every component of those roles is
live. -/
theorem roleFilter_live (keep : Role → Bool) {tagged : List (Pattern × Role)} {live : Finset Nat}
    (inLive : ∀ place < tagged.length, keep (taggedAt block tagged place).2 = true → place ∈ live) :
    ((((List.range tagged.length).filter (· ∈ live)).map (taggedAt block tagged)).filter fun item => keep item.2) =
      tagged.filter fun item => keep item.2 := by
  classical
  conv_rhs => rw [← map_taggedAt_range (block := block) tagged]
  rw [List.filter_map, List.filter_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro place member
  have inside := List.mem_range.mp member
  simp only [Function.comp_apply]
  cases kept : keep (taggedAt block tagged place).2
  · simp
  · simp [inLive place inside kept]

section Exposure

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **Every block exposes its parts and anchors in an unfolding of its canonical form**, within what they cost below a
ceiling on the heights of its replicated components: copy groups avoiding them are removed, and a copy group meeting
them is unfolded from its replicated component. -/
theorem exposes : ∀ (bound : Nat) {count ceiling : Nat} {tagged : List (Pattern × Role)}, tagged.length ≤ bound →
    (Prenex.mk count (tagged.map Prod.fst)).Atomic block.toBlock →
    (∀ item ∈ tagged, item.2 = .part → isReplicated block item.1 = false) →
    (∀ item ∈ tagged, item.2 = .anchor → isReplicated block item.1 = true) →
    (∀ item ∈ tagged, isReplicated block item.1 = true → height block item.1 < ceiling) →
    Exposes block count tagged ((tagged.map (weight block ceiling)).sum)
  | 0, count, ceiling, tagged, short, atomic, plain, _, _ => by
      have empty : tagged = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst empty
      exact exposes_base fresh restrictFresh atomic plain (fun p group isCopy => by
        have := isCopy.isLive
        simp [places] at this) _
  | bound + 1, count, ceiling, tagged, short, atomic, plain, anchored, low => by
      classical
      obtain ⟨live, liveInside, keeps, removes, maximal, sameOthers⟩ := remove_avoiding fresh restrictFresh atomic plain
      have placesIs : (places (⟨count, tagged.map Prod.fst⟩ : Prenex)).toFinset =
          (List.range tagged.length).toFinset := by
        simp [places]
      by_cases everything : live = (List.range tagged.length).toFinset
      · subst everything
        by_cases some : ∃ p group, (blockSystem block ⟨count, tagged.map Prod.fst⟩).IsCopy
            (List.range tagged.length).toFinset p group
        · obtain ⟨q, group, isCopy⟩ := some
          exact exposes_step fresh restrictFresh
            (fun shorter atomic' plain' anchored' low' => exposes bound (by omega) atomic' plain' anchored' low')
            atomic plain anchored low (by rw [placesIs]; exact isCopy) (maximal q group isCopy)
        · push Not at some
          exact exposes_base fresh restrictFresh atomic plain (fun p group isCopy => some p group (by
            rw [← placesIs]; exact isCopy)) _
      · -- some copy groups were removed: a shorter block with the same canonical form, parts and anchors
        set kept := (List.range tagged.length).filter (· ∈ live) with keptIs
        set tagged₀ := kept.map (taggedAt block tagged) with tagged₀Is
        have keptInside : ∀ place ∈ kept, place < tagged.length := fun place member =>
          List.mem_range.mp (List.mem_filter.mp member).1
        have memTagged₀ : ∀ item ∈ tagged₀, item ∈ tagged := by
          intro item member
          obtain ⟨place, inKept, rfl⟩ := List.mem_map.mp member
          exact taggedAt_mem (keptInside place inKept)
        have shorter : tagged₀.length < tagged.length := by
          rw [tagged₀Is, List.length_map, keptIs]
          obtain ⟨missing, inRange, notLive⟩ : ∃ place ∈ (List.range tagged.length).toFinset, place ∉ live := by
            by_contra none
            push Not at none
            exact everything (Finset.Subset.antisymm liveInside none)
          have fewer : ((List.range tagged.length).filter (· ∈ live)).length < (List.range tagged.length).length :=
            List.length_filter_lt_length_iff_exists.mpr ⟨missing, List.mem_toFinset.mp inRange, by simpa using notLive⟩
          simpa using fewer
        have atomic₀ : (Prenex.mk count (tagged₀.map Prod.fst)).Atomic block.toBlock := by
          intro component member
          obtain ⟨item, inTagged₀, rfl⟩ := List.mem_map.mp member
          exact atomic _ (List.mem_map_of_mem (memTagged₀ item inTagged₀))
        have exposes₀ := exposes bound (by omega) atomic₀ (fun item member => plain item (memTagged₀ item member))
          (fun item member => anchored item (memTagged₀ item member))
          (fun item member => low item (memTagged₀ item member))
        have sameNormal : normal block ⟨count, tagged₀.map Prod.fst⟩ = normal block ⟨count, tagged.map Prod.fst⟩ := by
          have restricted := normal_restrict_from fresh restrictFresh atomic (live := List.range tagged.length)
            (kept := kept) List.nodup_range (by simp) (List.nodup_range.filter _)
            (fun place member => (List.mem_filter.mp member).1)
            (by rw [keptIs, filter_toFinset liveInside]; exact removes)
          rw [restrictTo_tagged, restrictTo_tagged, map_taggedAt_range] at restricted
          exact restricted
        have sameParts : partsOf tagged₀ = partsOf tagged := by
          unfold partsOf
          rw [tagged₀Is, keptIs, roleFilter_live (fun role => decide (role = .part)) fun place inside isPart =>
            keeps place inside (by simp only [decide_eq_true_eq] at isPart; rw [isPart]; decide)]
        have sameAnchors : anchorsOf tagged₀ = anchorsOf tagged := by
          unfold anchorsOf
          rw [tagged₀Is, keptIs, roleFilter_live (fun role => decide (role = .anchor)) fun place inside isAnchor =>
            keeps place inside (by simp only [decide_eq_true_eq] at isAnchor; rw [isAnchor]; decide)]
        have sameWeight : (tagged₀.map (weight block ceiling)).sum = (tagged.map (weight block ceiling)).sum := by
          have split := List.filter_append_perm (fun place => decide (place ∈ live)) (List.range tagged.length)
          have summed := (split.map fun place => weight block ceiling (taggedAt block tagged place)).sum_eq
          rw [List.map_append, List.sum_append] at summed
          have removedZero : (((List.range tagged.length).filter fun place => !decide (place ∈ live)).map
              fun place => weight block ceiling (taggedAt block tagged place)).sum = 0 := by
            apply List.sum_eq_zero
            intro weightValue member
            obtain ⟨place, inRemoved, rfl⟩ := List.mem_map.mp member
            obtain ⟨inRange, notLive⟩ := List.mem_filter.mp inRemoved
            have isOther : (taggedAt block tagged place).2 = .other := by
              by_contra notOther
              exact (by simpa using notLive : place ∉ live) (keeps place (List.mem_range.mp inRange) notOther)
            simp only [weight, isOther]
          rw [removedZero, Nat.add_zero] at summed
          rw [tagged₀Is, List.map_map, keptIs]
          conv_rhs => rw [← map_taggedAt_range (block := block) tagged, List.map_map]
          exact summed
        exact exposes₀.transfer sameNormal sameParts sameAnchors (fun context contextAtomic attached =>
          sameOthers context contextAtomic attached) (le_of_eq sameWeight)

/-- **The parts of a redex in a block are exposed in an unfolding of the block's canonical form**, within as many
unfoldings as the parts times a ceiling on the heights of the block's replicated components: read alike under a
renaming, beside the unfolding's other components, which read every context of the parts as the block's other
components do. -/
theorem exposure {count ceiling : Nat} {parts others : List Pattern}
    (atomic : (Prenex.mk count (parts ++ others)).Atomic block.toBlock)
    (plain : ∀ part ∈ parts, isReplicated block part = false)
    (low : ∀ component ∈ parts ++ others, isReplicated block component = true → height block component < ceiling) :
    ∃ (unfolded : Prenex) (relabel : Nat → Nat) (exposed rest : List Pattern),
      UnfoldsWithin block (parts.length * ceiling) (normal block ⟨count, parts ++ others⟩) unfolded ∧
      unfolded.components.Perm (exposed ++ rest) ∧
      List.Forall₂ (fun shown part => AlikeR block shown (rename relabel part)) exposed parts ∧
      (∀ index, relabel (count + index) = unfolded.count + index) ∧
      (∀ index < count, (∃ part ∈ parts, mentions index part = true) → relabel index < unfolded.count) ∧
      (∀ first < count, ∀ second < count, (∃ part ∈ parts, mentions first part = true) →
        (∃ part ∈ parts, mentions second part = true) → relabel first = relabel second → first = second) ∧
      ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
        (∀ component ∈ context, ∀ index < count, mentions index component = true →
          ∃ part ∈ parts, mentions index part = true) →
        normal block ⟨count, others ++ context⟩ = normal block ⟨unfolded.count, rest ++ context.map (rename relabel)⟩ := by
  set tagged := parts.map (fun part => (part, Role.part)) ++ others.map (fun other => (other, Role.other))
    with taggedIs
  have fstIs : tagged.map Prod.fst = parts ++ others := by simp [taggedIs, List.map_map, Function.comp_def]
  have partsIs : partsOf tagged = parts := by
    simp [taggedIs, partsOf, List.filter_append, List.filter_map, Function.comp_def]
  have anchorsIs : anchorsOf tagged = [] := by
    simp [taggedIs, anchorsOf, List.filter_append, List.filter_map, Function.comp_def]
  have othersIs : othersOf tagged = others := by
    simp [taggedIs, othersOf, List.filter_append, List.filter_map, Function.comp_def]
  have weightIs : (tagged.map (weight block ceiling)).sum = parts.length * ceiling := by
    simp [taggedIs, weight, List.map_map, Function.comp_def, List.sum_replicate, Nat.mul_comm]
  have attachedIs : ∀ index, Attached tagged index ↔ ∃ part ∈ parts, mentions index part = true := by
    intro index
    simp only [Attached, partsIs, anchorsIs, List.append_nil]
  have exposed := exposes fresh restrictFresh tagged.length le_rfl (count := count) (ceiling := ceiling)
    (by rw [fstIs]; exact atomic)
    (fun item member isPart => by
      rcases List.mem_append.mp member with inParts | inOthers
      · obtain ⟨part, inParts', rfl⟩ := List.mem_map.mp inParts
        exact plain part inParts'
      · obtain ⟨other, _, rfl⟩ := List.mem_map.mp inOthers
        cases isPart)
    (fun item member isAnchor => by
      rcases List.mem_append.mp member with inParts | inOthers
      · obtain ⟨part, _, rfl⟩ := List.mem_map.mp inParts
        cases isAnchor
      · obtain ⟨other, _, rfl⟩ := List.mem_map.mp inOthers
        cases isAnchor)
    (fun item member replicated => low item.1 (by rw [← fstIs]; exact List.mem_map_of_mem member) replicated)
  rw [weightIs] at exposed
  obtain ⟨unfolded, relabel, shown, rest, unfolds, permutation, related, -, outer, below, injective, aligned⟩ := exposed
  refine ⟨unfolded, relabel, shown, rest, ?_, permutation, partsIs ▸ related, outer,
    fun index inside attached => below index inside ((attachedIs index).mpr attached),
    fun first firstInside second secondInside firstAttached secondAttached same => injective first firstInside second
      secondInside ((attachedIs first).mpr firstAttached) ((attachedIs second).mpr secondAttached) same, ?_⟩
  · rw [← fstIs]
    exact unfolds
  · intro context contextAtomic attached
    rw [← othersIs]
    exact aligned context contextAtomic fun component member index inside mentioned =>
      (attachedIs index).mpr (attached component member index inside mentioned)

end Exposure

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
