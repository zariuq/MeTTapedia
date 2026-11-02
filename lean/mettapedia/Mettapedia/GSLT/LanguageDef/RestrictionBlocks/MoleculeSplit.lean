import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Split

/-!
# A block is its molecules side by side

A list of groups is a **partition** of a block's components when each group's restrictions are restrictions of the
block without repeats, no two groups share a restriction, and each component uses only its group's restrictions
(`Partition`). The block of a partition's components is then the bag of its groups' molecules
(`partition_equivalent`), by splitting off one group at a time (`split_equivalent`): the rest, read as a block of
its own restrictions, is again a partition (`Partition.relabel`), with the same molecules (`molecule_relabel`).

This file holds the relabelling and its facts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

/-- **A group read in the block of the restrictions `outer`**: its restrictions by their places among `outer`, its
components renamed as that block reads them. -/
def Group.relabel (count : Nat) (outer : List Nat) (group : Group) : Group :=
  ⟨group.restrictions.map outer.idxOf, group.components.map (rename (Prenex.groupIndex count outer))⟩

/-- Places are read through a map that tells members apart. -/
theorem idxOf_map_of_injective {list : List Nat} {map : Nat → Nat} {member : Nat}
    (injective : ∀ left ∈ list, ∀ right ∈ list, map left = map right → left = right) (listed : member ∈ list) :
    (list.map map).idxOf (map member) = list.idxOf member := by
  induction list with
  | nil => simp at listed
  | cons head tail recurse =>
      by_cases same : head = member
      · subst same
        simp
      · have different : map head ≠ map member := fun equal =>
          same (injective head (List.mem_cons_self) member listed equal)
        have inTail : member ∈ tail := (List.mem_cons.mp listed).resolve_left (Ne.symm same)
        have rest := recurse (fun left leftIn right rightIn => injective left (List.mem_cons_of_mem _ leftIn) right
          (List.mem_cons_of_mem _ rightIn)) inTail
        simp [different, same, rest]

/-- **A relabelled group has the molecule it had**: read in the block of restrictions holding its own, a group's
restrictions and outside names come back to the same places. -/
theorem molecule_relabel {count : Nat} {outer : List Nat} {group : Group}
    (within : ∀ index ∈ group.restrictions, index ∈ outer)
    (uses : ∀ component ∈ group.components, ∀ index, FreeIn index component → index < count →
      index ∈ group.restrictions) :
    Prenex.molecule outer.length (group.relabel count outer) = Prenex.molecule count group := by
  simp only [Prenex.molecule, Group.relabel, List.length_map, List.map_map, Prenex.mk.injEq, true_and]
  apply List.map_congr_left
  intro component member
  show rename _ (rename _ component) = _
  rw [rename_comp]
  apply rename_congr
  intro index freeHere
  simp only [Function.comp_apply, Prenex.groupIndex]
  by_cases inside : index < count
  · have own := uses component member index freeHere inside
    have inOuter := within index own
    have position := List.idxOf_lt_length_of_mem inOuter
    simp only [inside, position, if_true]
    exact idxOf_map_of_injective (fun left leftIn right rightIn same =>
      SplitParts.eq_of_idxOf_eq (within left leftIn) (within right rightIn) same) own
  · simp only [inside, if_false, List.length_map]
    rw [if_neg (by omega)]
    omega

/-! ## Partitions -/

/-- **A partition of a block's components into groups**: each group's restrictions are restrictions of the block
without repeats, no two groups share a restriction, and each component uses only its group's restrictions. -/
structure Partition (count : Nat) (parts : List Group) : Prop where
  nodup : ∀ group ∈ parts, group.restrictions.Nodup
  inside : ∀ group ∈ parts, ∀ index ∈ group.restrictions, index < count
  disjoint : parts.Pairwise fun group other => ∀ index ∈ group.restrictions, index ∉ other.restrictions
  uses : ∀ group ∈ parts, ∀ component ∈ group.components, ∀ index, FreeIn index component → index < count →
    index ∈ group.restrictions

namespace Partition

variable {count : Nat} {group : Group} {rest : List Group}

/-- The rest of a partition is one. -/
theorem tail (partition : Partition count (group :: rest)) : Partition count rest where
  nodup := fun other member => partition.nodup other (List.mem_cons_of_mem _ member)
  inside := fun other member => partition.inside other (List.mem_cons_of_mem _ member)
  disjoint := (List.pairwise_cons.mp partition.disjoint).2
  uses := fun other member => partition.uses other (List.mem_cons_of_mem _ member)

/-- The restrictions of the rest, together. -/
abbrev outer (rest : List Group) : List Nat := rest.flatMap Group.restrictions

theorem outer_nodup (partition : Partition count rest) : (outer rest).Nodup := by
  rw [outer, List.nodup_flatMap]
  refine ⟨partition.nodup, ?_⟩
  exact partition.disjoint.imp fun separate => fun index inFirst inSecond => separate index inFirst inSecond

/-- **The first group and the rest are a split.** -/
theorem splitParts (partition : Partition count (group :: rest)) :
    SplitParts count group.restrictions (outer rest) where
  firstNodup := partition.nodup group List.mem_cons_self
  secondNodup := partition.tail.outer_nodup
  firstInside := partition.inside group List.mem_cons_self
  secondInside := by
    intro index member
    obtain ⟨other, otherMember, listed⟩ := List.mem_flatMap.mp member
    exact partition.inside other (List.mem_cons_of_mem _ otherMember) index listed
  disjoint := by
    intro index inFirst inSecond
    obtain ⟨other, otherMember, listed⟩ := List.mem_flatMap.mp inSecond
    exact (List.pairwise_cons.mp partition.disjoint).1 other otherMember index inFirst listed

/-- The rest's components use only the rest's restrictions. -/
theorem rest_uses (partition : Partition count rest) :
    ∀ component ∈ rest.flatMap Group.components, ∀ index, FreeIn index component → index < count →
      index ∈ outer rest := by
  intro component member index freeHere inside
  obtain ⟨other, otherMember, listed⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨other, otherMember, partition.uses other otherMember component listed index freeHere inside⟩

/-- **The rest, read in the block of its own restrictions, is a partition.** -/
theorem relabel (partition : Partition count rest) :
    Partition (outer rest).length (rest.map (Group.relabel count (outer rest))) where
  nodup := by
    intro relabelled member
    obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
    refine (partition.nodup other otherMember).map_on ?_
    intro left leftIn right rightIn same
    exact SplitParts.eq_of_idxOf_eq (List.mem_flatMap.mpr ⟨other, otherMember, leftIn⟩)
      (List.mem_flatMap.mpr ⟨other, otherMember, rightIn⟩) same
  inside := by
    intro relabelled member index listed
    obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp listed
    exact List.idxOf_lt_length_of_mem (List.mem_flatMap.mpr ⟨other, otherMember, originalIn⟩)
  disjoint := by
    rw [List.pairwise_map]
    refine partition.disjoint.imp_of_mem ?_
    intro first second firstMember secondMember separate index inFirst inSecond
    obtain ⟨left, leftIn, rfl⟩ := List.mem_map.mp inFirst
    obtain ⟨right, rightIn, same⟩ := List.mem_map.mp inSecond
    have equal := SplitParts.eq_of_idxOf_eq (List.mem_flatMap.mpr ⟨second, secondMember, rightIn⟩)
      (List.mem_flatMap.mpr ⟨first, firstMember, leftIn⟩) same
    exact separate left leftIn (equal ▸ rightIn)
  uses := by
    intro relabelled member component componentIn index freeHere inside
    obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp componentIn
    obtain ⟨source, sourceFree, moved⟩ := (freeIn_rename original).mp freeHere
    simp only [Prenex.groupIndex] at moved
    split_ifs at moved with below
    · have listed := partition.uses other otherMember original originalIn source sourceFree below
      exact List.mem_map.mpr ⟨source, listed, moved⟩
    · omega

end Partition

/-! ## The molecules of a block are a partition -/

/-- Disjointness of groups' restrictions is symmetric. -/
instance : Std.Symm (fun group other : Group => ∀ index ∈ group.restrictions, index ∉ other.restrictions) :=
  ⟨fun _ _ separate index inSecond inFirst => separate index inFirst inSecond⟩

/-- **Merging a component keeps a partition.** -/
theorem Partition.insert {count : Nat} {component : Pattern} {parts : List Group} (partition : Partition count parts) :
    Partition count (insertComponent count component parts) where
  nodup := by
    intro group member
    simp only [insertComponent, insertUsing, List.mem_append, List.mem_filter, List.mem_singleton] at member
    rcases member with ⟨inParts, -⟩ | rfl
    · exact partition.nodup group inParts
    · exact List.nodup_range.filter _
  inside := by
    intro group member index listed
    simp only [insertComponent, insertUsing, List.mem_append, List.mem_filter, List.mem_singleton] at member
    rcases member with ⟨inParts, -⟩ | rfl
    · exact partition.inside group inParts index listed
    · exact List.mem_range.mp (List.mem_filter.mp listed).1
  disjoint := by
    simp only [insertComponent, insertUsing]
    rw [List.pairwise_append]
    refine ⟨partition.disjoint.filter _, List.pairwise_singleton _ _, ?_⟩
    intro apartGroup apartMember merged mergedMember index inApart inMerged
    rw [List.mem_singleton] at mergedMember
    subst mergedMember
    obtain ⟨apartIn, notShared⟩ := List.mem_filter.mp apartMember
    simp only [List.mem_filter, List.mem_range, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem] at inMerged
    rcases inMerged.2 with used | ⟨joinedGroup, joinedMember, listed⟩
    · simp only [Bool.not_eq_true', shares, List.any_eq_false, List.contains_iff_mem] at notShared
      exact notShared index used inApart
    · obtain ⟨joinedIn, shared⟩ := joinedMember
      have different : apartGroup ≠ joinedGroup := by
        rintro rfl
        simp [shared] at notShared
      exact partition.disjoint.forall apartIn joinedIn different index inApart listed
  uses := by
    intro group member other otherMember index freeHere inside
    simp only [insertComponent, insertUsing, List.mem_append, List.mem_filter, List.mem_singleton] at member
    rcases member with ⟨inParts, -⟩ | rfl
    · exact partition.uses group inParts other otherMember index freeHere inside
    · simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at otherMember
      simp only [List.mem_filter, List.mem_range, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem]
      refine ⟨inside, ?_⟩
      rcases otherMember with ⟨joinedGroup, joinedMember, listed⟩ | rfl
      · exact .inr ⟨joinedGroup, List.mem_filter.mp joinedMember,
          partition.uses joinedGroup (List.mem_filter.mp joinedMember).1 other listed index freeHere inside⟩
      · exact .inl (by
          simp only [usedRestrictions, List.mem_filter, List.mem_range]
          exact ⟨inside, (mentions_iff other index).mpr freeHere⟩)

/-- Merging a component adds it to the groups' components, up to order. -/
theorem insert_perm (count : Nat) (component : Pattern) (parts : List Group) :
    ((insertComponent count component parts).flatMap Group.components).Perm
      (parts.flatMap Group.components ++ [component]) := by
  simp only [insertComponent, insertUsing, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc]
  apply List.Perm.append_right
  have whole := (List.filter_append_perm (fun group => shares (usedRestrictions count component) group.restrictions)
    parts).flatMap_right Group.components
  rw [List.flatMap_append] at whole
  exact List.perm_append_comm.trans whole

/-- **The molecules of a block are a partition of its components.** -/
theorem groups_partition (form : Prenex) :
    Partition form.count (groups form) ∧ ((groups form).flatMap Group.components).Perm form.components := by
  obtain ⟨count, components⟩ := form
  simp only [groups]
  suffices invariant : ∀ (start : List Group) (pending : List Pattern), Partition count start →
      Partition count (pending.foldl (fun groups component => insertComponent count component groups) start) ∧
      ((pending.foldl (fun groups component => insertComponent count component groups) start).flatMap
          Group.components).Perm (start.flatMap Group.components ++ pending) by
    have empty : Partition count [] := ⟨by simp, by simp, List.Pairwise.nil, by simp⟩
    simpa using invariant [] components empty
  intro start pending
  induction pending generalizing start with
  | nil => intro partition; simpa using partition
  | cons component rest recurse =>
      intro partition
      obtain ⟨partitioned, permuted⟩ := recurse (insertComponent count component start) partition.insert
      refine ⟨partitioned, permuted.trans ?_⟩
      simpa [List.append_assoc] using (insert_perm count component start).append_right rest

/-! ## Groups linked through allowed restrictions -/

/-- **A partition through allowed restrictions**: each group's restrictions are allowed restrictions of the block
without repeats, no two groups share one, and each component uses, among the allowed restrictions, only its group's. -/
structure ThroughPartition (allowed : List Nat) (count : Nat) (parts : List Group) : Prop where
  nodup : ∀ group ∈ parts, group.restrictions.Nodup
  inside : ∀ group ∈ parts, ∀ index ∈ group.restrictions, index < count
  allowedOnly : ∀ group ∈ parts, ∀ index ∈ group.restrictions, index ∈ allowed
  disjoint : parts.Pairwise fun group other => ∀ index ∈ group.restrictions, index ∉ other.restrictions
  uses : ∀ group ∈ parts, ∀ component ∈ group.components, ∀ index ∈ allowed, FreeIn index component →
    index < count → index ∈ group.restrictions

/-- **Merging a component through the allowed restrictions keeps such a partition.** -/
theorem ThroughPartition.insert {allowed : List Nat} {count : Nat} {component : Pattern} {parts : List Group}
    (partition : ThroughPartition allowed count parts) :
    ThroughPartition allowed count
      (insertUsing count ((usedRestrictions count component).filter allowed.contains) component parts) where
  nodup := by
    intro group member
    simp only [insertUsing, List.mem_append, List.mem_filter, List.mem_singleton] at member
    rcases member with ⟨inParts, -⟩ | rfl
    · exact partition.nodup group inParts
    · exact List.nodup_range.filter _
  inside := by
    intro group member index listed
    simp only [insertUsing, List.mem_append, List.mem_filter, List.mem_singleton] at member
    rcases member with ⟨inParts, -⟩ | rfl
    · exact partition.inside group inParts index listed
    · exact List.mem_range.mp (List.mem_filter.mp listed).1
  allowedOnly := by
    intro group member index listed
    simp only [insertUsing, List.mem_append, List.mem_filter, List.mem_singleton] at member
    rcases member with ⟨inParts, -⟩ | rfl
    · exact partition.allowedOnly group inParts index listed
    · simp only [List.mem_filter, List.mem_range, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem] at listed
      rcases listed.2 with used | ⟨joinedGroup, joinedMember, inJoined⟩
      · exact used.2
      · exact partition.allowedOnly joinedGroup joinedMember.1 index inJoined
  disjoint := by
    simp only [insertUsing]
    rw [List.pairwise_append]
    refine ⟨partition.disjoint.filter _, List.pairwise_singleton _ _, ?_⟩
    intro apartGroup apartMember merged mergedMember index inApart inMerged
    rw [List.mem_singleton] at mergedMember
    subst mergedMember
    obtain ⟨apartIn, notShared⟩ := List.mem_filter.mp apartMember
    simp only [List.mem_filter, List.mem_range, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem] at inMerged
    rcases inMerged.2 with used | ⟨joinedGroup, joinedMember, listed⟩
    · simp only [Bool.not_eq_true', shares, List.any_eq_false, List.contains_iff_mem] at notShared
      exact notShared index (List.mem_filter.mpr ⟨used.1, List.contains_iff_mem.mpr used.2⟩) inApart
    · obtain ⟨joinedIn, shared⟩ := joinedMember
      have different : apartGroup ≠ joinedGroup := by
        rintro rfl
        simp [shared] at notShared
      exact partition.disjoint.forall apartIn joinedIn different index inApart listed
  uses := by
    intro group member other otherMember index permitted freeHere inside
    simp only [insertUsing, List.mem_append, List.mem_filter, List.mem_singleton] at member
    rcases member with ⟨inParts, -⟩ | rfl
    · exact partition.uses group inParts other otherMember index permitted freeHere inside
    · simp only [List.mem_append, List.mem_flatMap, List.mem_singleton] at otherMember
      simp only [List.mem_filter, List.mem_range, Bool.or_eq_true, List.any_eq_true, List.contains_iff_mem]
      refine ⟨inside, ?_⟩
      rcases otherMember with ⟨joinedGroup, joinedMember, listed⟩ | rfl
      · exact .inr ⟨joinedGroup, List.mem_filter.mp joinedMember,
          partition.uses joinedGroup (List.mem_filter.mp joinedMember).1 other listed index permitted freeHere inside⟩
      · refine .inl ⟨?_, permitted⟩
        simp only [usedRestrictions, List.mem_filter, List.mem_range]
        exact ⟨inside, (mentions_iff other index).mpr freeHere⟩

/-- Merging adds the component to the groups' components, up to order. -/
theorem insertUsing_perm (count : Nat) (used : List Nat) (component : Pattern) (parts : List Group) :
    ((insertUsing count used component parts).flatMap Group.components).Perm
      (parts.flatMap Group.components ++ [component]) := by
  simp only [insertUsing, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc]
  apply List.Perm.append_right
  have whole := (List.filter_append_perm (fun group => shares used group.restrictions) parts).flatMap_right
    Group.components
  rw [List.flatMap_append] at whole
  exact List.perm_append_comm.trans whole

/-- **The groups through allowed restrictions are such a partition of the components.** -/
theorem groupsThrough_partition (allowed : List Nat) (count : Nat) (components : List Pattern) :
    ThroughPartition allowed count (groupsThrough allowed count components) ∧
      ((groupsThrough allowed count components).flatMap Group.components).Perm components := by
  simp only [groupsThrough]
  suffices invariant : ∀ (start : List Group) (pending : List Pattern), ThroughPartition allowed count start →
      ThroughPartition allowed count (pending.foldl (fun groups component =>
        insertUsing count ((usedRestrictions count component).filter allowed.contains) component groups) start) ∧
      ((pending.foldl (fun groups component =>
        insertUsing count ((usedRestrictions count component).filter allowed.contains) component groups) start).flatMap
          Group.components).Perm (start.flatMap Group.components ++ pending) by
    have empty : ThroughPartition allowed count [] := ⟨by simp, by simp, by simp, List.Pairwise.nil, by simp⟩
    simpa using invariant [] components empty
  intro start pending
  induction pending generalizing start with
  | nil => intro partition; simpa using partition
  | cons component rest recurse =>
      intro partition
      obtain ⟨partitioned, permuted⟩ := recurse _ partition.insert
      refine ⟨partitioned, permuted.trans ?_⟩
      simpa [List.append_assoc] using (insertUsing_perm count _ component start).append_right rest

/-! ## A partition's block is its molecules side by side -/

section Equivalence

variable {language : LanguageDef} {block : Block} [laws : BlockSignature language block]

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)

/-- A molecule of a partition's group is a process. -/
theorem molecule_typed {free : FreeTypeContext} {bound : List TypeExpr} {count : Nat} {group : Group}
    (members : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      group.components)
    (uses : ∀ component ∈ group.components, ∀ index, FreeIn index component → index < count →
      index ∈ group.restrictions) :
    HasType language free bound (Prenex.toPattern block (Prenex.molecule count group)) (.base block.proc) :=
  restricts_typed _ (body_typed (part_members (restrictions := group.restrictions) members uses))

/-- `{x, {ys}} ≡ {x, ys}`. -/
theorem bag_cons_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {head : Pattern} {tail : List Pattern}
    (headTyped : HasType language free bound head (.base block.proc))
    (tailMembers : Members language block free bound tail) :
    ProcEquiv language block free bound (.collection .hashBag [head, .collection .hashBag tail none] none)
      (.collection .hashBag (head :: tail) none) := by
  have single : ProcEquiv language block free bound (.collection .hashBag [head] none) head :=
    bag_body_equivalent (block := block) (Members.cons headTyped Members.nil)
  have wrapped := bag_fill (before := []) (after := [.collection .hashBag tail none]) (rest := none) Members.nil
    (Members.cons (bag_typed tailMembers) Members.nil) (.symm _ _ single)
  simp only [List.nil_append] at wrapped
  exact .trans _ _ _ wrapped (bag_pair_equivalent (Members.cons headTyped Members.nil) tailMembers)

/-- **The block of a partition's components is its groups' molecules side by side.** -/
theorem partition_equivalent {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {count : Nat} {parts : List Group}, Partition count parts →
      Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
        (parts.flatMap Group.components) →
      ProcEquiv language block free bound (Prenex.toPattern block ⟨count, parts.flatMap Group.components⟩)
        (.collection .hashBag (parts.map fun group => Prenex.toPattern block (Prenex.molecule count group)) none)
  | count, [], _, _ => by
      obtain ⟨-, dropped⟩ := drop_outer_equivalent (block := block) (free := free) (bound := bound) 0 count
        (components := []) (by simpa using (Members.nil : Members language block free _ []))
        (fun _ member => by simp at member)
      simp only [Nat.zero_add, List.map_nil] at dropped
      simp only [List.flatMap_nil, List.map_nil]
      exact .trans _ _ _ dropped (.symm _ _ (bag_body_equivalent Members.nil))
  | count, group :: rest, partition, members => by
      have parts := partition.splitParts
      have restPartition := partition.tail
      have oneMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
          group.components := fun element member => members element (by simp [member])
      have twoMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
          (rest.flatMap Group.components) :=
        fun element member => members element (by simp only [List.flatMap_cons]; exact List.mem_append_right _ member)
      have split := split_equivalent parts (partOne := group.components) (partTwo := rest.flatMap Group.components)
        (by simpa [List.flatMap_cons] using members) (partition.uses group List.mem_cons_self)
        restPartition.rest_uses
      have relabelled := restPartition.relabel
      have relabelledMembers := part_members (restrictions := Partition.outer rest) twoMembers
        restPartition.rest_uses
      have components : (rest.flatMap Group.components).map (rename (Prenex.groupIndex count (Partition.outer rest))) =
          (rest.map (Group.relabel count (Partition.outer rest))).flatMap Group.components := by
        simp [Group.relabel, List.map_flatMap, List.flatMap_map]
      rw [components] at relabelledMembers split
      have inner := partition_equivalent relabelled relabelledMembers
      have molecules : (rest.map (Group.relabel count (Partition.outer rest))).map
          (fun other => Prenex.toPattern block (Prenex.molecule (Partition.outer rest).length other)) =
          rest.map fun other => Prenex.toPattern block (Prenex.molecule count other) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro other member
        simp only [Function.comp_apply]
        rw [molecule_relabel (fun index listed => List.mem_flatMap.mpr ⟨other, member, listed⟩)
          (restPartition.uses other member)]
      rw [molecules] at inner
      have moleculeMembers : Members language block free bound
          (rest.map fun other => Prenex.toPattern block (Prenex.molecule count other)) := by
        intro element member
        obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
        exact molecule_typed (fun element listed => twoMembers element
          (List.mem_flatMap.mpr ⟨other, otherMember, listed⟩)) (restPartition.uses other otherMember)
      have groupTyped := molecule_typed oneMembers (partition.uses group List.mem_cons_self)
      have filled := bag_fill (before := [Prenex.toPattern block (Prenex.molecule count group)]) (after := [])
        (rest := none) (Members.cons groupTyped Members.nil) Members.nil inner
      simp only [List.cons_append, List.nil_append] at filled
      simp only [List.flatMap_cons, List.map_cons]
      exact .trans _ _ _ split (.trans _ _ _ filled (bag_cons_equivalent groupTyped moleculeMembers))
termination_by _ parts => parts.length
decreasing_by simp

/-- **A block is its molecules side by side.** -/
theorem molecules_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {form : Prenex}
    (members : Members language block free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components) :
    ProcEquiv language block free bound (Prenex.toPattern block form)
      (.collection .hashBag ((groups form).map fun group => Prenex.toPattern block (Prenex.molecule form.count group))
        none) := by
  obtain ⟨partition, permuted⟩ := groups_partition form
  have groupMembers : Members language block free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      ((groups form).flatMap Group.components) := fun element member => members element (permuted.subset member)
  have reordered : ProcEquiv language block free bound (Prenex.toPattern block form)
      (Prenex.toPattern block ⟨form.count, (groups form).flatMap Group.components⟩) :=
    restricts_congr form.count (body_perm_equivalent members permuted.symm)
  exact .trans _ _ _ reordered (partition_equivalent partition groupMembers)

end Equivalence

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
