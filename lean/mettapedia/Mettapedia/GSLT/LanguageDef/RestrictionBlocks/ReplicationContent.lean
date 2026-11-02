import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawful

/-!
# What a reading keeps

A reading sorts its components and keeps one of each replicated one (`dedupReplicated`): every finite component as
often as it occurs, every replicated one once (`count_dedupReplicated`). So the sorted reading of a list depends
only on these counts (`content_eq`).

Reading components through two maps that identify the same components and agree on replication keeps the same
places (`dedupBy_same`), and readings agreeing through one map agree through the other (`content_transfer`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

theorem dedupReplicated_sublist : ∀ (components : List Pattern), (dedupReplicated block components).Sublist components
  | [] => by simp [dedupReplicated]
  | component :: rest => by
      unfold dedupReplicated
      split_ifs
      · exact (dedupReplicated_sublist rest).cons component
      · exact (dedupReplicated_sublist rest).cons_cons component

/-- **A reading keeps every finite component as often as it occurs, every replicated one once.** -/
theorem count_dedupReplicated (target : Pattern) : ∀ (components : List Pattern),
    (dedupReplicated block components).count target =
      if isReplicated block target = true then (if target ∈ components then 1 else 0) else components.count target
  | [] => by simp [dedupReplicated]
  | component :: rest => by
      have recurse := count_dedupReplicated target rest
      unfold dedupReplicated
      by_cases same : component = target
      · subst same
        by_cases replicated : isReplicated block component = true
        · by_cases inRest : component ∈ rest
          · have drop : (isReplicated block component && rest.contains component) = true := by
              simp [replicated, inRest]
            rw [if_pos drop, recurse]
            simp [replicated, inRest]
          · have keep : ¬ (isReplicated block component && rest.contains component) = true := by
              simp [inRest]
            rw [if_neg keep, List.count_cons, recurse]
            simp [replicated, inRest]
        · have keep : ¬ (isReplicated block component && rest.contains component) = true := by
            simp [replicated]
          rw [if_neg keep, List.count_cons, recurse]
          simp [replicated]
      · have memberIff : target ∈ component :: rest ↔ target ∈ rest := by
          simp only [List.mem_cons]
          exact ⟨fun holds => holds.resolve_left fun equal => same equal.symm, Or.inr⟩
        have countIs : (component :: rest).count target = rest.count target := by
          rw [List.count_cons]
          simp [same]
        split_ifs at recurse ⊢ <;> simp_all

theorem sortComponents_count (components : List Pattern) (target : Pattern) :
    (sortComponents components).count target = components.count target :=
  (List.perm_insertionSort _ components).count_eq target

theorem mem_sortComponents {components : List Pattern} {target : Pattern} :
    target ∈ sortComponents components ↔ target ∈ components :=
  (List.perm_insertionSort _ components).mem_iff

/-- **What a reading keeps of a list.** -/
theorem count_content (components : List Pattern) (target : Pattern) :
    (dedupReplicated block (sortComponents components)).count target =
      if isReplicated block target = true then (if target ∈ components then 1 else 0)
      else components.count target := by
  rw [count_dedupReplicated, sortComponents_count]
  simp only [mem_sortComponents]

/-- **Readings with the same counts are the same.** -/
theorem content_eq {first second : List Pattern}
    (counts : ∀ target, (dedupReplicated block (sortComponents first)).count target =
      (dedupReplicated block (sortComponents second)).count target) :
    dedupReplicated block (sortComponents first) = dedupReplicated block (sortComponents second) :=
  List.Perm.eq_of_pairwise' ((sortComponents_pairwise first).sublist (dedupReplicated_sublist _))
    ((sortComponents_pairwise second).sublist (dedupReplicated_sublist _)) (List.perm_iff_count.mpr counts)

/-- A reading keeps what keeping one of each replicated component keeps, in some order. -/
theorem content_perm (components : List Pattern) :
    (dedupReplicated block (sortComponents components)).Perm (dedupReplicated block components) := by
  refine List.perm_iff_count.mpr fun target => ?_
  rw [count_content, count_dedupReplicated]

/-! ## Reading through a map -/

/-- **One of each replicated component, as read through a map.** -/
def dedupBy (block : ReplicationBlock) (read : Pattern → Pattern) : List Pattern → List Pattern
  | [] => []
  | component :: rest =>
      if isReplicated block (read component) && (rest.map read).contains (read component) then
        dedupBy block read rest
      else component :: dedupBy block read rest

theorem dedupBy_map (read : Pattern → Pattern) : ∀ (components : List Pattern),
    (dedupBy block read components).map read = dedupReplicated block (components.map read)
  | [] => rfl
  | component :: rest => by
      unfold dedupBy
      simp only [List.map_cons]
      unfold dedupReplicated
      split_ifs
      · exact dedupBy_map read rest
      · simp only [List.map_cons]
        rw [dedupBy_map read rest]

/-- **Two maps that identify the same components and agree on replication keep the same places.** -/
theorem dedupBy_same {read read' : Pattern → Pattern} : ∀ (components : List Pattern),
    (∀ first ∈ components, ∀ second ∈ components, read first = read second ↔ read' first = read' second) →
    (∀ component ∈ components, isReplicated block (read component) = isReplicated block (read' component)) →
    dedupBy block read components = dedupBy block read' components
  | [] => fun _ _ => rfl
  | component :: rest => fun same replicated => by
      have recurse := dedupBy_same rest (fun first inFirst second inSecond =>
        same first (List.mem_cons_of_mem _ inFirst) second (List.mem_cons_of_mem _ inSecond))
        fun other member => replicated other (List.mem_cons_of_mem _ member)
      have containsSame : (rest.map read).contains (read component) = (rest.map read').contains (read' component) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.contains_iff_mem, List.mem_map]
        exact exists_congr fun other => and_congr_right fun member =>
          same other (List.mem_cons_of_mem _ member) component List.mem_cons_self
      unfold dedupBy
      rw [replicated component List.mem_cons_self, containsSame, recurse]

/-- **Readings agreeing through one map agree through another identifying the same components.** -/
theorem content_transfer {first second : List Pattern} {read read' : Pattern → Pattern}
    (same : ∀ component ∈ first ++ second, ∀ other ∈ first ++ second,
      read component = read other ↔ read' component = read' other)
    (replicated : ∀ component ∈ first ++ second,
      isReplicated block (read component) = isReplicated block (read' component))
    (equal : dedupReplicated block (sortComponents (first.map read)) =
      dedupReplicated block (sortComponents (second.map read))) :
    dedupReplicated block (sortComponents (first.map read')) =
      dedupReplicated block (sortComponents (second.map read')) := by
  have countsRead := fun target => congrArg (List.count target) equal
  apply content_eq
  intro target
  rw [count_content, count_content]
  by_cases found : ∃ component ∈ first ++ second, read' component = target
  · obtain ⟨component, member, rfl⟩ := found
    -- membership and counts through `read'` are those through `read`
    have memberIff : ∀ list : List Pattern, list ⊆ first ++ second →
        (read' component ∈ list.map read' ↔ read component ∈ list.map read) := by
      intro list inside
      simp only [List.mem_map]
      exact exists_congr fun other => and_congr_right fun inList =>
        (same other (inside inList) component member).symm
    have countIff : ∀ list : List Pattern, list ⊆ first ++ second →
        (list.map read').count (read' component) = (list.map read).count (read component) := by
      intro list inside
      rw [List.count_eq_countP, List.countP_map, List.count_eq_countP, List.countP_map]
      apply List.countP_congr
      intro other inList
      have holds := (same other (inside inList) component member).symm
      simpa [Function.comp_apply, beq_iff_eq] using holds
    have firstInside : first ⊆ first ++ second := List.subset_append_left _ _
    have secondInside : second ⊆ first ++ second := List.subset_append_right _ _
    have atRead := countsRead (read component)
    rw [count_content, count_content] at atRead
    rw [← replicated component member]
    simp only [memberIff first firstInside, memberIff second secondInside, countIff first firstInside,
      countIff second secondInside]
    exact atRead
  · push Not at found
    have notFirst : target ∉ first.map read' := fun inMap => by
      obtain ⟨component, member, reached⟩ := List.mem_map.mp inMap
      exact found component (List.mem_append_left _ member) reached
    have notSecond : target ∉ second.map read' := fun inMap => by
      obtain ⟨component, member, reached⟩ := List.mem_map.mp inMap
      exact found component (List.mem_append_right _ member) reached
    simp [notFirst, notSecond, List.count_eq_zero_of_not_mem]

theorem dedupBy_subset (read : Pattern → Pattern) : ∀ (components : List Pattern),
    ∀ component ∈ dedupBy block read components, component ∈ components
  | [] => fun _ member => by simp [dedupBy] at member
  | head :: rest => fun component member => by
      unfold dedupBy at member
      split_ifs at member
      · exact List.mem_cons_of_mem _ (dedupBy_subset read rest component member)
      · rcases List.mem_cons.mp member with rfl | inRest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (dedupBy_subset read rest component inRest)

/-- Keeping one of each replicated component keeps something of a nonempty list. -/
theorem dedupReplicated_ne_nil : ∀ {components : List Pattern}, components ≠ [] → dedupReplicated block components ≠ []
  | [], nonempty => absurd rfl nonempty
  | [component], _ => by simp [dedupReplicated]
  | component :: second :: rest, _ => by
      unfold dedupReplicated
      split_ifs
      · exact dedupReplicated_ne_nil (List.cons_ne_nil second rest)
      · exact List.cons_ne_nil _ _

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks

