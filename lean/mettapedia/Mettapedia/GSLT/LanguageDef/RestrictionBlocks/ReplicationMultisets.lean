import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationReflection

/-!
# Blocks of plain components

A block with no restrictions whose components are atoms, none of them replicated, reads as its components read
again (`normal_plain_perm`): there is no copy to absorb, no restriction to order and no replicated component to keep
once. So two such blocks with one canonical form have components read alike, one for one (`plain_reads_alike`). This
is how a named multiset of guards, a sum, is told by its summands.

- Absorption keeps a block's restrictions, and pruning drops some, so a block without restrictions has a canonical
  form without restrictions (`normal_count_zero`).
- A copy group copies a replicated component, so plain components have none (`no_copies_of_plain`).
- A bag with a member whose canonical block is not inaction has a canonical block that is not inaction
  (`canonP_bag_ne_nil`), since the canonical form of a nonempty block of atoms is nonempty: a named multiset of it is
  one component.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)

variable {block : ReplicationBlock}

/-! ## The restrictions of a canonical form -/

/-- **Absorbing a copy keeps the block's restrictions.** -/
theorem absorbOnce_count {canonical : Pattern → Pattern} {form next : Prenex}
    (found : absorbOnce block canonical form = some next) : next.count = form.count := by
  unfold absorbOnce at found
  obtain ⟨position, -, found⟩ := List.exists_of_findSome?_eq_some found
  split at found
  · split_ifs at found
    obtain ⟨group, -, rfl⟩ := Option.map_eq_some_iff.mp found
    rfl
  · cases found

theorem absorbRounds_count {canonical : Pattern → Pattern} :
    ∀ (rounds : Nat) (form : Prenex), (absorbRounds block canonical rounds form).count = form.count
  | 0, _ => rfl
  | rounds + 1, form => by
      unfold absorbRounds
      split
      · rfl
      · rename_i next found
        rw [absorbRounds_count rounds next, absorbOnce_count found]

/-- **A block without restrictions has a canonical form without restrictions.** -/
theorem normal_count_zero (components : List Pattern) : (normal block ⟨0, components⟩).count = 0 := by
  unfold normal
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Prenex.toPattern block.toBlock ⟨0, components⟩) + 3 = fuel + 1 :=
    ⟨_, rfl⟩
  rw [fuelIs]
  simp [normalizeWith, absorb, Prenex.prune, absorbRounds_count]

/-! ## Plain components -/

/-- **Plain components have no copy groups**: a copy group copies a replicated component. -/
theorem no_copies_of_plain {form : Prenex} (plain : ∀ component ∈ form.components, isReplicated block component = false) :
    ∀ p group, ¬ (blockSystem block form).IsCopy (places form).toFinset p group := by
  intro p group copy
  have replicated := copy.isReplicated
  have inside : p < form.components.length := places_inRange form p (List.mem_toFinset.mp copy.isLive)
  simp only [blockSystem, absorptionSystem] at replicated
  rw [plain _ (placeValue_mem inside)] at replicated
  cases replicated

/-- Plain components are kept, each once as often as it stands. -/
theorem dedupReplicated_plain : ∀ {components : List Pattern},
    (∀ component ∈ components, isReplicated block component = false) → dedupReplicated block components = components
  | [], _ => rfl
  | component :: rest, plain => by
      simp only [dedupReplicated, plain component List.mem_cons_self, Bool.false_and, Bool.false_eq_true, if_false]
      rw [dedupReplicated_plain fun other member => plain other (List.mem_cons_of_mem _ member)]

section Plain

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **A block of plain atoms without restrictions reads as its components read again.** -/
theorem normal_plain_perm {components : List Pattern} (atomic : (Prenex.mk 0 components).Atomic block.toBlock)
    (plain : ∀ component ∈ components, isReplicated block component = false) :
    (normal block ⟨0, components⟩).components.Perm (components.map (recanon block)) := by
  obtain ⟨relabel, componentsPerm, outer, -⟩ :=
    exposure_base_uniform fresh restrictFresh atomic (no_copies_of_plain (form := ⟨0, components⟩) plain)
  have identity : relabel = id := funext fun index => by
    have shifted := outer index
    rw [normal_count_zero, Nat.zero_add] at shifted
    exact shifted
  subst identity
  have readPlain : ∀ component ∈ components.map fun component => recanon block (rename id component),
      isReplicated block component = false := by
    intro component member
    obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
    rw [isReplicated_recanon, rename_id]
    exact plain original inComponents
  rw [dedupReplicated_plain readPlain] at componentsPerm
  simpa [rename_id] using componentsPerm

/-- **Two blocks of plain atoms without restrictions with one canonical form have components read alike**, one for
one. -/
theorem plain_reads_alike {first second : List Pattern} (firstAtomic : (Prenex.mk 0 first).Atomic block.toBlock)
    (secondAtomic : (Prenex.mk 0 second).Atomic block.toBlock)
    (firstPlain : ∀ component ∈ first, isReplicated block component = false)
    (secondPlain : ∀ component ∈ second, isReplicated block component = false)
    (same : normal block ⟨0, first⟩ = normal block ⟨0, second⟩) :
    (first.map (recanon block)).Perm (second.map (recanon block)) := by
  have firstPerm := normal_plain_perm fresh restrictFresh firstAtomic firstPlain
  have secondPerm := normal_plain_perm fresh restrictFresh secondAtomic secondPlain
  rw [same] at firstPerm
  exact firstPerm.symm.trans secondPerm

omit fresh restrictFresh in
/-- Each member's canonical block is among the canonical blocks of a list. -/
theorem canonP_mem_canonsP : ∀ {patterns : List Pattern} {pattern : Pattern}, pattern ∈ patterns →
    canonP block pattern ∈ canonsP block patterns
  | first :: rest, pattern, member => by
      rw [canonsP]
      rcases List.mem_cons.mp member with rfl | later
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (canonP_mem_canonsP later)

omit fresh restrictFresh in
theorem canonsP_mem {patterns : List Pattern} {form : Prenex} :
    form ∈ canonsP block patterns → ∃ pattern ∈ patterns, form = canonP block pattern := by
  induction patterns with
  | nil => simp [canonsP]
  | cons first rest recurse =>
      rw [canonsP]
      intro member
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first, List.mem_cons_self, rfl⟩
      · obtain ⟨pattern, inRest, rfl⟩ := recurse later
        exact ⟨pattern, List.mem_cons_of_mem _ inRest, rfl⟩

omit fresh restrictFresh in
/-- Blocks side by side have a component when one of them has. -/
theorem foldr_par_components_ne_nil : ∀ {forms : List Prenex} {form : Prenex}, form ∈ forms →
    form.components ≠ [] → (forms.foldr Prenex.par Prenex.nil).components ≠ []
  | first :: rest, form, member, nonempty => by
      rw [List.foldr_cons]
      simp only [Prenex.par, ne_eq, List.append_eq_nil_iff, List.map_eq_nil_iff, not_and]
      rcases List.mem_cons.mp member with rfl | later
      · exact fun empty => absurd empty nonempty
      · exact fun _ => foldr_par_components_ne_nil later nonempty

/-- **A bag with a member whose canonical block is not inaction has a canonical block that is not inaction**, when
its members are object terms whose restrictions bind. -/
theorem canonP_bag_ne_nil {elements : List Pattern} (objects : ∀ element ∈ elements, isObjectPattern element = true)
    (binds : ∀ element ∈ elements, restrictionsBind block.toBlock element = true)
    (present : ∃ element ∈ elements, canonP block element ≠ Prenex.nil) :
    canonP block (.collection .hashBag elements none) ≠ Prenex.nil := by
  obtain ⟨element, member, notNil⟩ := present
  have facts := canonFacts fresh restrictFresh (objects element member) (binds element member)
  have atomic : ((canonsP block elements).foldr Prenex.par Prenex.nil).Atomic block.toBlock := by
    apply foldr_par_atomic
    intro form inForms
    obtain ⟨pattern, inElements, rfl⟩ := canonsP_mem inForms
    exact (canonFacts fresh restrictFresh (objects pattern inElements) (binds pattern inElements)).atomic
  have nonempty := foldr_par_components_ne_nil (canonP_mem_canonsP member)
    (components_ne_nil_of_used facts.used notNil)
  have normalNonempty := normal_components_ne_nil fresh restrictFresh atomic nonempty
  simp only [canonP]
  intro isNil
  rw [isNil] at normalNonempty
  exact normalNonempty rfl

end Plain

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
