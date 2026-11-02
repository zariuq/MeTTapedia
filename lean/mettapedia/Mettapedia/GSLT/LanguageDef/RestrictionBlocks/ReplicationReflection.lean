import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSimulation

/-!
# Reflecting the steps of a canonical form into the process

A step of a process is matched by a step of an unfolding of its canonical form (`replication_simulation`). This file
gives the converse for the canonical forms the front door lists: a step of an unfolding of the canonical form is
matched, up to the static theory, by a step of the process's own components beside copies of its own replicated
components.

- **Absorption keeps exactly the places in no copy group** (`kept_block`): they make a block without copy groups with
  the block's canonical form.
- **The canonical components come from kept places** (`reflect_kept`): for parts and replicated components of the
  canonical form, the block holds components read as them under one renaming, and every context of these reads beside
  the block's other components as it reads, renamed, beside the canonical form's other components: the copy groups are
  removed beside such a context, and the kept places are read as the canonical form reads them.
- **A reaction of an unfolding of the canonical form is a reaction of the block beside copies of its own replicated
  components** (`replication_reflection`), for a block of canonical components whose replicated components copy one
  canonical component each: the parts and the copies the unfolding takes come from the block and from copies of the
  replicated components they read, and what the reaction leaves reads beside the rest as the unfolding's does.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

/-! ## Removing copy groups -/

namespace CopyGroups.System

variable {ι : Type} [DecidableEq ι] {system : CopyGroups.System ι}

/-- **Removing copy groups shrinks the copies.** -/
theorem Removes.copies_subset {whole : Finset ι} (laws : system.Laws whole) {live rest : Finset ι}
    (inside : live ⊆ whole) (removes : system.Removes live rest) :
    rest ⊆ live ∧ system.copies rest ⊆ system.copies live := by
  induction removes with
  | refl => exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  | @step live rest p copied isCopy _ recurse =>
      obtain ⟨restInside, copiesInside⟩ := recurse (Finset.sdiff_subset.trans inside)
      refine ⟨restInside.trans Finset.sdiff_subset, copiesInside.trans ?_⟩
      rw [removed_copies laws inside isCopy]
      exact Finset.sdiff_subset

/-- An absorption ends where no copy group is left. -/
theorem Absorbs.none {live final : Finset ι} (absorbs : system.Absorbs live final) :
    ∀ p group, ¬ system.IsCopy final p group := by
  induction absorbs with
  | done none => exact none
  | step _ _ recurse => exact recurse

/-- An absorption removes copy groups. -/
theorem Absorbs.removes {live final : Finset ι} (absorbs : system.Absorbs live final) : system.Removes live final := by
  induction absorbs with
  | done => exact .refl
  | step isCopy _ recurse => exact .step isCopy recurse

/-- **No copy group, no copies.** -/
theorem copies_eq_empty {live : Finset ι} (none : ∀ p group, ¬ system.IsCopy live p group) :
    system.copies live = ∅ := by
  ext member
  simp only [system.mem_copies, Finset.notMem_empty, iff_false, not_and, not_exists]
  intro _ q group isCopy
  exact absurd isCopy (none q group)

/-- **Removing copy groups until every one left meets places outside the copies absorbs**: no copy group is left. -/
theorem absorbs_of_removes {whole live : Finset ι} (laws : system.Laws whole) (removes : system.Removes whole live)
    {held : Finset ι} (meets : ∀ p group, system.IsCopy live p group → ∃ place ∈ group, place ∈ held)
    (outside : ∀ place ∈ held, place ∉ system.copies whole) : system.Absorbs whole live := by
  refine removes.absorbs (.done fun p group isCopy => ?_)
  obtain ⟨place, inGroup, inHeld⟩ := meets p group isCopy
  have inCopies := (removes.copies_subset laws (Finset.Subset.refl _)).2 (isCopy.subset_copies inGroup)
  exact outside place inHeld inCopies

end CopyGroups.System

/-! ## The places absorption keeps -/

section Kept

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **Absorption keeps exactly the places in no copy group**: they make a block without copy groups, with the
block's canonical form. -/
theorem kept_block {form : Prenex} (atomic : form.Atomic block.toBlock) :
    ∃ kept : List Nat, kept.Nodup ∧ (∀ place ∈ kept, place < form.components.length) ∧
      kept.toFinset = (places form).toFinset \ (blockSystem block form).copies (places form).toFinset ∧
      (∀ p group, ¬ (blockSystem block (restrictTo block form kept)).IsCopy
        (places (restrictTo block form kept)).toFinset p group) ∧
      normal block (restrictTo block form kept) = normal block form := by
  classical
  obtain ⟨laws, blind⟩ := lawful_all fresh restrictFresh atomic
  obtain ⟨kept, nodup, absorbs, -⟩ := absorb_places blind
  have inside : ∀ place ∈ kept, place < form.components.length := fun place member =>
    places_inRange form place (List.mem_toFinset.mp (absorbs_subset absorbs (List.mem_toFinset.mpr member)))
  refine ⟨kept, nodup, inside, absorbs.eq laws (Finset.Subset.refl _), ?_, ?_⟩
  · intro p group isCopy
    have iso := restrictTo_iso blind inside
    have empty := iso.copies
    rw [CopyGroups.System.copies_eq_empty absorbs.none, Finset.image_empty, image_idxOf nodup] at empty
    have placesIs : (places (restrictTo block form kept)).toFinset = (List.range kept.length).toFinset := by
      simp [places, restrictTo]
    rw [placesIs] at isCopy
    obtain ⟨member, inGroup⟩ := isCopy.isGroup.nonempty
    have inCopies := isCopy.subset_copies inGroup
    rw [empty] at inCopies
    exact Finset.notMem_empty _ inCopies
  · have restricted := normal_restrict_from fresh restrictFresh atomic (live := places form) (kept := kept)
      (places_nodup form) (places_inRange form) nodup
      (fun place member => List.mem_toFinset.mp (absorbs_subset absorbs (List.mem_toFinset.mpr member)))
      absorbs.removes
    rw [restricted]
    unfold restrictTo
    rw [places_map]

/-- **Every component of a block's canonical form reads a component of the block again**, renamed. -/
theorem normal_mem_read {count : Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock) :
    ∀ component ∈ (normal block ⟨count, components⟩).components,
      ∃ (relabel : Nat → Nat) (original : Pattern), original ∈ components ∧
        component = recanon block (rename relabel original) := by
  obtain ⟨kept, -, keptInside, -, noCopies, sameNormal⟩ := kept_block fresh restrictFresh atomic
  have baseAtomic : (Prenex.mk count (kept.map (placeValue block components))).Atomic block.toBlock :=
    restrictTo_atomic atomic keptInside
  obtain ⟨relabel, componentsPerm, -⟩ := exposure_base_uniform fresh restrictFresh baseAtomic noCopies
  have sameNormal' : normal block ⟨count, kept.map (placeValue block components)⟩ = normal block ⟨count, components⟩ :=
    sameNormal
  rw [sameNormal'] at componentsPerm
  intro component member
  obtain ⟨original, inKept, rfl⟩ := List.mem_map.mp (mem_dedupReplicated.mp (componentsPerm.subset member))
  obtain ⟨place, inPlaces, rfl⟩ := List.mem_map.mp inKept
  exact ⟨relabel, _, placeValue_mem (keptInside place inPlaces), rfl⟩

omit fresh restrictFresh in
/-- One copy of a single component beside a block: the component past its components. -/
theorem unfoldWith_atom (form : Prenex) (component : Pattern) :
    form.unfoldWith (Prenex.atom component) = ⟨form.count, form.components ++ [component]⟩ := by
  simp only [Prenex.unfoldWith, Prenex.atom, Nat.zero_add, Prenex.mk.injEq, true_and]
  congr 1
  conv_rhs => rw [← List.map_id form.components]
  exact List.map_congr_left fun component _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ _

/-- **Unfoldings of a block whose replicated components have one-component copies**: the block's components beside
copies of arguments of its replicated components, read again. -/
theorem unfolds_atomic {depth : Nat} {form unfolded : Prenex} (unfolds : UnfoldsWithin block depth form unfolded) :
    (∀ component ∈ form.components, ∀ argument, component = .apply block.replicate [argument] →
      decompose block.toBlock argument = Prenex.atom argument ∧ isReplicated block argument = false) →
    ∃ pairs : List (Pattern × Pattern), unfolded = ⟨form.count, form.components ++ pairs.map Prod.snd⟩ ∧
      ∀ pair ∈ pairs, ∃ argument, pair.1 = .apply block.replicate [argument] ∧ pair.1 ∈ form.components ∧
        pair.2 = recanon block argument := by
  induction unfolds with
  | refl => exact fun _ => ⟨[], by simp, by simp⟩
  | @step depth form next argument member _ recurse =>
      intro servers
      obtain ⟨atomic, plain⟩ := servers _ member argument rfl
      have copyIs : normal block (decompose block.toBlock argument) = Prenex.atom (recanon block argument) := by
        rw [atomic, normal_atom fresh restrictFresh atomic]
      rw [copyIs, unfoldWith_atom] at recurse
      obtain ⟨pairs, nextIs, pairsFacts⟩ := recurse fun component inComponents argument' componentIs => by
        rcases List.mem_append.mp inComponents with inForm | inCopy
        · exact servers component inForm argument' componentIs
        · rw [List.mem_singleton] at inCopy
          subst inCopy
          have replicated : isReplicated block (recanon block argument) = true := by
            rw [componentIs]
            simp [isReplicated]
          rw [isReplicated_recanon, plain] at replicated
          cases replicated
      refine ⟨(.apply block.replicate [argument], recanon block argument) :: pairs, ?_, ?_⟩
      · rw [nextIs]
        simp
      · intro pair inPairs
        rcases List.mem_cons.mp inPairs with rfl | later
        · exact ⟨argument, rfl, member, rfl⟩
        · obtain ⟨argument', serverIs, inComponents, copyIs'⟩ := pairsFacts pair later
          refine ⟨argument', serverIs, ?_, copyIs'⟩
          rcases List.mem_append.mp inComponents with inForm | inCopy
          · exact inForm
          · rw [List.mem_singleton] at inCopy
            have replicated : isReplicated block (recanon block argument) = true := by
              rw [← inCopy, serverIs]
              simp [isReplicated]
            rw [isReplicated_recanon, plain] at replicated
            cases replicated

/-! ## Choosing components read as given ones -/

omit fresh restrictFresh in
/-- **Choosing a sub-multiset with a given image.** -/
theorem exists_subperm_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ {shown : List β} {source : List α}, shown.Subperm (source.map f) →
      ∃ chosen : List α, chosen.Subperm source ∧ chosen.map f = shown
  | [], _, _ => ⟨[], List.nil_subperm, rfl⟩
  | head :: tail, source, sub => by
      obtain ⟨element, inSource, rfl⟩ := List.mem_map.mp (sub.subset List.mem_cons_self)
      have perm : (source.map f).Perm (f element :: (source.erase element).map f) := by
        simpa using (List.perm_cons_erase inSource).map f
      have rest : tail.Subperm ((source.erase element).map f) :=
        (List.subperm_cons (f element)).mp (sub.trans perm.subperm)
      obtain ⟨chosen, chosenSub, chosenMap⟩ := exists_subperm_map f rest
      exact ⟨element :: chosen, ((List.subperm_cons element).mpr chosenSub).trans
        (List.perm_cons_erase inSource).symm.subperm, by simp [chosenMap]⟩

omit fresh restrictFresh in
theorem nodup_of_subperm {α : Type} {first second : List α} (sub : first.Subperm second) (nodup : second.Nodup) :
    first.Nodup := by
  obtain ⟨middle, perm, sublist⟩ := sub
  exact perm.nodup_iff.mp (sublist.nodup nodup)

omit fresh restrictFresh in
/-- **Choosing, for each of some items, a witness.** -/
theorem exists_forall₂_of_forall {α β : Type} {relation : α → β → Prop} {pool : List β} :
    ∀ {items : List α}, (∀ item ∈ items, ∃ chosen ∈ pool, relation item chosen) →
      ∃ chosen : List β, List.Forall₂ relation items chosen ∧ ∀ member ∈ chosen, member ∈ pool
  | [], _ => ⟨[], .nil, by simp⟩
  | item :: items, all => by
      obtain ⟨first, inPool, related⟩ := all item List.mem_cons_self
      obtain ⟨rest, restRelated, restIn⟩ := exists_forall₂_of_forall fun other member =>
        all other (List.mem_cons_of_mem _ member)
      refine ⟨first :: rest, .cons related restRelated, fun member inChosen => ?_⟩
      rcases List.mem_cons.mp inChosen with rfl | later
      · exact inPool
      · exact restIn member later

omit fresh restrictFresh in
/-- Distinct places among some distinct places, and the rest of them, make them all. -/
theorem perm_filter_not_mem {chosen whole : List Nat} (chosenNodup : chosen.Nodup) (wholeNodup : whole.Nodup)
    (inside : ∀ place ∈ chosen, place ∈ whole) :
    whole.Perm (chosen ++ whole.filter fun place => decide (place ∉ chosen)) := by
  rw [List.perm_ext_iff_of_nodup wholeNodup (List.nodup_append.mpr ⟨chosenNodup, wholeNodup.filter _,
    fun first inFirst second inSecond same => by
      subst same
      simp only [List.mem_filter, decide_eq_true_eq] at inSecond
      exact inSecond.2 inFirst⟩)]
  intro place
  simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro member
    by_cases inChosen : place ∈ chosen
    · exact .inl inChosen
    · exact .inr ⟨member, inChosen⟩
  · rintro (inChosen | ⟨member, -⟩)
    · exact inside place inChosen
    · exact member

omit fresh restrictFresh in
/-- **Choosing a sub-multiset with a given image**, beside the rest. -/
theorem exists_perm_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ {shown : List β} {source : List α}, shown.Subperm (source.map f) →
      ∃ chosen rest : List α, source.Perm (chosen ++ rest) ∧ chosen.map f = shown
  | [], source, _ => ⟨[], source, List.Perm.refl _, rfl⟩
  | head :: tail, source, sub => by
      obtain ⟨element, inSource, rfl⟩ := List.mem_map.mp (sub.subset List.mem_cons_self)
      have perm : (source.map f).Perm (f element :: (source.erase element).map f) := by
        simpa using (List.perm_cons_erase inSource).map f
      have rest : tail.Subperm ((source.erase element).map f) :=
        (List.subperm_cons (f element)).mp (sub.trans perm.subperm)
      obtain ⟨chosen, others, othersPerm, chosenMap⟩ := exists_perm_map f rest
      exact ⟨element :: chosen, others, (List.perm_cons_erase inSource).trans (othersPerm.cons element),
        by simp [chosenMap]⟩

/-! ## Interleaving two lists -/

/-- **Two lists interleaved by tags**: `true` takes from the first, `false` from the second; what is left follows. -/
def interleave {α : Type} : List Bool → List α → List α → List α
  | [], first, second => first ++ second
  | true :: tags, item :: first, second => item :: interleave tags first second
  | true :: tags, [], second => interleave tags [] second
  | false :: tags, first, item :: second => item :: interleave tags first second
  | false :: tags, first, [] => interleave tags first []

omit fresh restrictFresh in
theorem interleave_perm {α : Type} : ∀ (tags : List Bool) (first second : List α),
    (interleave tags first second).Perm (first ++ second)
  | [], _, _ => List.Perm.refl _
  | true :: tags, item :: first, second => (interleave_perm tags first second).cons item
  | true :: tags, [], second => interleave_perm tags [] second
  | false :: tags, first, item :: second =>
      ((interleave_perm tags first second).cons item).trans List.perm_middle.symm
  | false :: tags, first, [] => interleave_perm tags first []

omit fresh restrictFresh in
theorem interleave_forall₂ {α β : Type} {relation : α → β → Prop} : ∀ (tags : List Bool) {first second : List α}
    {first' second' : List β}, List.Forall₂ relation first first' → List.Forall₂ relation second second' →
      List.Forall₂ relation (interleave tags first second) (interleave tags first' second')
  | [], _, _, _, _, related, related' => List.rel_append related related'
  | true :: tags, _, _, _, _, .cons head rest, related' => .cons head (interleave_forall₂ tags rest related')
  | true :: tags, _, _, _, _, .nil, related' => interleave_forall₂ tags .nil related'
  | false :: tags, _, _, _, _, related, .cons head rest => .cons head (interleave_forall₂ tags related rest)
  | false :: tags, _, _, _, _, related, .nil => interleave_forall₂ tags related .nil

omit fresh restrictFresh in
/-- **Items of two lists side by side, split between them**: each item taken from one of the lists, the rest of
each beside. -/
theorem perm_append_split {α : Type} [DecidableEq α] :
    ∀ {taken : List α} {first second rest : List α}, (first ++ second).Perm (taken ++ rest) →
      ∃ (tags : List Bool) (takenFirst takenSecond restFirst restSecond : List α),
        taken = interleave tags takenFirst takenSecond ∧ first.Perm (takenFirst ++ restFirst) ∧
        second.Perm (takenSecond ++ restSecond) ∧ rest.Perm (restFirst ++ restSecond)
  | [], first, second, rest, perm => ⟨[], [], [], first, second, rfl, List.Perm.refl _, List.Perm.refl _, perm.symm⟩
  | item :: taken, first, second, rest, perm => by
      have inEither : item ∈ first ++ second := perm.symm.subset List.mem_cons_self
      by_cases inFirst : item ∈ first
      · have smaller : (first.erase item ++ second).Perm (taken ++ rest) := by
          have moved : (first ++ second).Perm (item :: (first.erase item ++ second)) :=
            (List.perm_cons_erase inFirst).append_right second
          exact (moved.symm.trans perm).cons_inv
        obtain ⟨tags, takenFirst, takenSecond, restFirst, restSecond, takenIs, firstPerm, secondPerm, restPerm⟩ :=
          perm_append_split smaller
        refine ⟨true :: tags, item :: takenFirst, takenSecond, restFirst, restSecond, ?_,
          (List.perm_cons_erase inFirst).trans (firstPerm.cons item), secondPerm, restPerm⟩
        rw [takenIs]
        rfl
      · have inSecond : item ∈ second := by
          rcases List.mem_append.mp inEither with here | there
          · exact absurd here inFirst
          · exact there
        have smaller : (first ++ second.erase item).Perm (taken ++ rest) := by
          have moved : (first ++ second).Perm (item :: (first ++ second.erase item)) :=
            ((List.perm_cons_erase inSecond).append_left first).trans List.perm_middle
          exact (moved.symm.trans perm).cons_inv
        obtain ⟨tags, takenFirst, takenSecond, restFirst, restSecond, takenIs, firstPerm, secondPerm, restPerm⟩ :=
          perm_append_split smaller
        refine ⟨false :: tags, takenFirst, item :: takenSecond, restFirst, restSecond, ?_, firstPerm,
          (List.perm_cons_erase inSecond).trans (secondPerm.cons item), restPerm⟩
        rw [takenIs]
        rfl

/-! ## The canonical components come from kept places -/

/-- **The canonical components come from kept places**: for parts of the canonical form of a block beside its other
components, and some replicated components among those, the block holds parts and replicated components read as them
under one renaming, the parts beside its other components; and every context of those parts and replicated
components reads beside the block's other components as it reads, renamed, beside the canonical form's. -/
theorem reflect_kept {count : Nat} {components : List Pattern}
    (atomic : (Prenex.mk count components).Atomic block.toBlock)
    {shown restN : List Pattern} (split : (normal block ⟨count, components⟩).components.Perm (shown ++ restN))
    (plain : ∀ part ∈ shown, isReplicated block part = false)
    {servers : List Pattern} (serversIn : ∀ server ∈ servers, server ∈ restN) :
    ∃ (relabel : Nat → Nat) (parts others anchors : List Pattern),
      components.Perm (parts ++ others) ∧
      List.Forall₂ (fun shownPart part => shownPart = recanon block (rename relabel part)) shown parts ∧
      List.Forall₂ (fun server anchor => server = recanon block (rename relabel anchor)) servers anchors ∧
      (∀ anchor ∈ anchors, anchor ∈ others) ∧
      (∀ index, relabel (count + index) = (normal block ⟨count, components⟩).count + index) ∧
      (∀ index < count, (∃ held ∈ parts ++ anchors, mentions index held = true) →
        relabel index < (normal block ⟨count, components⟩).count) ∧
      (∀ first < count, ∀ second < count, (∃ held ∈ parts ++ anchors, mentions first held = true) →
        (∃ held ∈ parts ++ anchors, mentions second held = true) → relabel first = relabel second → first = second) ∧
      ∀ context : List Pattern, (∀ component ∈ context, decompose block.toBlock component = Prenex.atom component) →
        (∀ component ∈ context, ∀ index < count, mentions index component = true →
          ∃ held ∈ parts ++ anchors, mentions index held = true) →
        normal block ⟨count, others ++ context⟩ =
          normal block ⟨(normal block ⟨count, components⟩).count, restN ++ context.map (rename relabel)⟩ := by
  classical
  set form : Prenex := ⟨count, components⟩ with formIs
  set value := placeValue block components with valueIs
  obtain ⟨kept, keptNodup, keptInside, keptIs, noCopies, sameNormal⟩ := kept_block fresh restrictFresh atomic
  have baseAtomic : (Prenex.mk count (kept.map value)).Atomic block.toBlock := restrictTo_atomic atomic keptInside
  have sameNormal' : normal block ⟨count, kept.map value⟩ = normal block form := sameNormal
  obtain ⟨relabel, componentsPerm, outer, below, injective, aligned⟩ := exposure_base_uniform fresh restrictFresh
    baseAtomic noCopies
  rw [sameNormal'] at componentsPerm outer aligned
  set read := fun component : Pattern => recanon block (rename relabel component) with readIs
  -- the parts, at kept places
  have shownSub : shown.Subperm (kept.map (read ∘ value)) := by
    have chain := ((List.sublist_append_left shown restN).subperm.trans (split.symm.trans componentsPerm).subperm).trans
      (dedupReplicated_sublist _).subperm
    simpa only [List.map_map] using chain
  obtain ⟨partPlaces, partSub, partMap⟩ := exists_subperm_map (read ∘ value) shownSub
  have partNodup := nodup_of_subperm partSub keptNodup
  have partKept : ∀ place ∈ partPlaces, place ∈ kept := fun place member => partSub.subset member
  set keptOthers := kept.filter fun place => decide (place ∉ partPlaces) with keptOthersIs
  have keptPerm := perm_filter_not_mem partNodup keptNodup partKept
  set others₀ := keptOthers.map value with others₀Is
  have partsPlain : ∀ component ∈ (partPlaces.map value).map read, isReplicated block component = false := by
    intro component member
    rw [List.map_map, partMap] at member
    exact plain component member
  have restPerm : restN.Perm (dedupReplicated block (others₀.map read)) := by
    have whole : (normal block form).components.Perm (shown ++ dedupReplicated block (others₀.map read)) := by
      refine componentsPerm.trans ((dedupReplicated_perm ((keptPerm.map value).map read)).trans ?_)
      rw [List.map_append, List.map_append]
      refine (dedupReplicated_append_plain partsPlain).trans ?_
      rw [List.map_map, partMap]
    exact (List.perm_append_left_iff shown).mp (split.symm.trans whole)
  -- the replicated components, at kept places beside the parts
  have serversFound : ∀ server ∈ servers, ∃ place ∈ keptOthers, server = read (value place) := by
    intro server member
    have inRest := restPerm.subset (serversIn server member)
    obtain ⟨other, inOthers, rfl⟩ := List.mem_map.mp (mem_dedupReplicated.mp inRest)
    obtain ⟨place, inKeptOthers, rfl⟩ := List.mem_map.mp inOthers
    exact ⟨place, inKeptOthers, rfl⟩
  obtain ⟨anchorPlaces, anchorRelated, anchorIn⟩ := exists_forall₂_of_forall serversFound
  have anchorNotPart : ∀ place ∈ anchorPlaces, place ∉ partPlaces := fun place member => by
    have := anchorIn place member
    simp only [keptOthersIs, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  have anchorKept : ∀ place ∈ anchorPlaces, place ∈ kept := fun place member => by
    have := anchorIn place member
    simp only [keptOthersIs, List.mem_filter] at this
    exact this.1
  -- the block's places
  set length := components.length with lengthIs
  have rangeIs : (List.range length).map value = components := by
    have mapped := congrArg Prenex.components (places_map (block := block) form)
    simpa [places, formIs] using mapped
  have keptRange : ∀ place ∈ kept, place ∈ List.range length := fun place member =>
    List.mem_range.mpr (keptInside place member)
  set othersPlaces := (List.range length).filter fun place => decide (place ∉ partPlaces) with othersPlacesIs
  have rangePerm := perm_filter_not_mem partNodup List.nodup_range fun place member =>
    keptRange place (partKept place member)
  -- the parts and replicated components are kept components, so the restrictions they mention are used there
  have heldKept : ∀ held ∈ partPlaces.map value ++ anchorPlaces.map value, held ∈ kept.map value := by
    intro held member
    rcases List.mem_append.mp member with inParts | inAnchors
    · obtain ⟨place, inPlaces, rfl⟩ := List.mem_map.mp inParts
      exact List.mem_map_of_mem (partKept place inPlaces)
    · obtain ⟨place, inPlaces, rfl⟩ := List.mem_map.mp inAnchors
      exact List.mem_map_of_mem (anchorKept place inPlaces)
  have usedKept : ∀ {index : Nat}, index < count →
      (∃ held ∈ partPlaces.map value ++ anchorPlaces.map value, mentions index held = true) →
      index ∈ usedOf ⟨count, kept.map value⟩ := by
    rintro index inside ⟨held, member, mentioned⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr inside, List.any_eq_true.mpr ⟨held, heldKept held member, mentioned⟩⟩
  refine ⟨relabel, partPlaces.map value, othersPlaces.map value, anchorPlaces.map value, ?_, ?_, ?_, ?_, outer, ?_, ?_,
    ?_⟩
  · rw [← rangeIs, ← List.map_append]
    exact rangePerm.map value
  · rw [← partMap, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun _ _ => rfl
  · rw [List.forall₂_map_right_iff]
    exact anchorRelated
  · intro anchor member
    obtain ⟨place, inAnchors, rfl⟩ := List.mem_map.mp member
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨keptRange place (anchorKept place inAnchors),
      decide_eq_true (anchorNotPart place inAnchors)⟩)
  · intro index inside attached
    rw [← sameNormal']
    exact below index (usedKept inside attached)
  · intro first firstInside second secondInside firstAttached secondAttached same
    exact injective first (usedKept firstInside firstAttached) second (usedKept secondInside secondAttached) same
  · intro context contextAtomic attached
    -- the block tagged: the parts, the replicated components kept for their copies, and the others
    set role : Nat → Role := fun place =>
      if place ∈ partPlaces then .part else if place ∈ anchorPlaces then .anchor else .other with roleIs
    set tagged := (List.range length).map fun place => (value place, role place) with taggedIs
    have fstIs : tagged.map Prod.fst = components := by
      rw [taggedIs, List.map_map]
      exact rangeIs
    have taggedLength : tagged.length = length := by simp [taggedIs]
    have taggedAtIs : ∀ place < length, taggedAt block tagged place = (value place, role place) := by
      intro place inside
      simp only [taggedAt, taggedIs]
      rw [List.getD_eq_getElem _ _ (by simpa using inside)]
      simp
    have taggedAtomic : (Prenex.mk count (tagged.map Prod.fst)).Atomic block.toBlock := by
      rw [fstIs]
      exact atomic
    have taggedPlain : ∀ item ∈ tagged, item.2 = .part → isReplicated block item.1 = false := by
      intro item member isPart
      obtain ⟨place, -, rfl⟩ := List.mem_map.mp member
      have inParts : place ∈ partPlaces := by
        by_contra notIn
        simp only [roleIs, notIn, if_false] at isPart
        split_ifs at isPart
      have read := partsPlain _ (List.mem_map_of_mem (List.mem_map_of_mem inParts))
      simpa [readIs, isReplicated_recanon, isReplicated_rename] using read
    obtain ⟨laws, -⟩ := lawful_all fresh restrictFresh atomic
    obtain ⟨live, liveInside, -, removes, maximal, sameOthers⟩ := remove_avoiding fresh restrictFresh taggedAtomic
      taggedPlain
    have wholeIs : (List.range tagged.length).toFinset = (places form).toFinset := by
      rw [taggedLength]
      rfl
    rw [fstIs, wholeIs] at removes
    rw [fstIs] at maximal
    -- removing the copy groups beside the parts and replicated components leaves the kept places
    have absorbs : (blockSystem block form).Absorbs (places form).toFinset live := by
      refine CopyGroups.System.absorbs_of_removes laws removes (held := (partPlaces ++ anchorPlaces).toFinset) ?_ ?_
      · intro p group isCopy
        obtain ⟨place, inGroup, notOther⟩ := maximal p group isCopy
        have inLive := (Finset.mem_erase.mp (isCopy.isGroup.subset inGroup)).2
        have below : place < length := by
          have := liveInside inLive
          simpa [taggedLength] using this
        rw [taggedAtIs place below] at notOther
        refine ⟨place, inGroup, List.mem_toFinset.mpr (List.mem_append.mpr ?_)⟩
        by_cases inParts : place ∈ partPlaces
        · exact .inl inParts
        · by_cases inAnchors : place ∈ anchorPlaces
          · exact .inr inAnchors
          · simp [roleIs, inParts, inAnchors] at notOther
      · intro place member inCopies
        have inKept : place ∈ kept := by
          rcases List.mem_append.mp (List.mem_toFinset.mp member) with inParts | inAnchors
          · exact partKept place inParts
          · exact anchorKept place inAnchors
        have := List.mem_toFinset.mpr inKept
        rw [keptIs] at this
        exact (Finset.mem_sdiff.mp this).2 inCopies
    have liveIs : live = kept.toFinset := by
      rw [absorbs.eq laws (Finset.Subset.refl _), keptIs]
    -- the contexts
    have attachedTagged : ∀ component ∈ context, ∀ index < count, mentions index component = true →
        Attached tagged index := by
      intro component member index inside mentioned
      obtain ⟨held, inHeld, heldMentions⟩ := attached component member index inside mentioned
      refine ⟨held, ?_, heldMentions⟩
      rcases List.mem_append.mp inHeld with inParts | inAnchors
      · obtain ⟨place, inPlaces, rfl⟩ := List.mem_map.mp inParts
        refine List.mem_append_left _ (mem_partsOf.mpr (List.mem_map.mpr ⟨place, ?_, ?_⟩))
        · exact keptRange place (partKept place inPlaces)
        · simp [roleIs, inPlaces]
      · obtain ⟨place, inPlaces, rfl⟩ := List.mem_map.mp inAnchors
        refine List.mem_append_right _ (mem_anchorsOf.mpr (List.mem_map.mpr ⟨place, ?_, ?_⟩))
        · exact keptRange place (anchorKept place inPlaces)
        · simp [roleIs, inPlaces, anchorNotPart place inPlaces]
    have same := sameOthers context contextAtomic attachedTagged
    have othersIs : othersOf tagged = othersPlaces.map value := by
      simp only [othersOf, taggedIs, List.filter_map, List.map_map, othersPlacesIs]
      congr 1
      apply List.filter_congr
      intro place _
      by_cases inParts : place ∈ partPlaces <;> simp [roleIs, inParts]; split_ifs <;> simp
    have keptOthersPerm : (othersOf (((List.range tagged.length).filter (· ∈ live)).map (taggedAt block tagged))).Perm
        others₀ := by
      have mapped : ((List.range tagged.length).filter (· ∈ live)).map (taggedAt block tagged) =
          ((List.range length).filter (· ∈ live)).map fun place => (value place, role place) := by
        rw [taggedLength]
        refine List.map_congr_left fun place member => taggedAtIs place ?_
        exact List.mem_range.mp (List.mem_filter.mp member).1
      rw [mapped]
      simp only [othersOf, List.filter_map, List.map_map, others₀Is]
      refine List.Perm.map value ?_
      rw [List.perm_ext_iff_of_nodup ((List.nodup_range.filter _).filter _) (keptNodup.filter _)]
      intro place
      simp only [List.mem_filter, List.mem_range, Function.comp_apply, liveIs, List.mem_toFinset, decide_eq_true_eq]
      by_cases inParts : place ∈ partPlaces
      · simp [roleIs, inParts]
      · by_cases inAnchors : place ∈ anchorPlaces <;> simp [roleIs, inParts, inAnchors] <;>
          exact fun inKept => keptInside place inKept
    have othersAtomic : ∀ component ∈ others₀, decompose block.toBlock component = Prenex.atom component := by
      intro component member
      obtain ⟨place, inKeptOthers, rfl⟩ := List.mem_map.mp member
      exact atomic _ (placeValue_mem (keptInside place (List.mem_filter.mp inKeptOthers).1))
    have contextUsed : ∀ component ∈ context, ∀ index < count, mentions index component = true →
        index ∈ usedOf ⟨count, kept.map value⟩ := fun component member index inside mentioned =>
      usedKept inside (attached component member index inside mentioned)
    have renamedAtomic : ∀ component ∈ context.map (rename relabel),
        decompose block.toBlock component = Prenex.atom component := by
      intro component member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      exact atomic_rename (contextAtomic original inOriginal) relabel
    calc normal block ⟨count, othersPlaces.map value ++ context⟩
        = normal block ⟨count, othersOf (((List.range tagged.length).filter (· ∈ live)).map
            (taggedAt block tagged)) ++ context⟩ := by rw [same, othersIs]
      _ = normal block ⟨count, others₀ ++ context⟩ := by
          refine normal_perm fresh restrictFresh (keptOthersPerm.append_right context) ?_
          intro component member
          rcases List.mem_append.mp member with inOthers | inContext
          · exact othersAtomic component (keptOthersPerm.subset inOthers)
          · exact contextAtomic component inContext
      _ = normal block ⟨(normal block form).count, dedupReplicated block (others₀.map read) ++
            context.map (rename relabel)⟩ :=
          aligned others₀ (fun other member => by
            obtain ⟨place, inKeptOthers, rfl⟩ := List.mem_map.mp member
            exact List.mem_map_of_mem (List.mem_filter.mp inKeptOthers).1) context contextAtomic contextUsed
      _ = normal block ⟨(normal block form).count, restN ++ context.map (rename relabel)⟩ := by
          refine normal_perm fresh restrictFresh (restPerm.symm.append_right _) ?_
          intro component member
          rcases List.mem_append.mp member with inRest | inContext
          · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp (mem_dedupReplicated.mp inRest)
            exact recanon_atom_all fresh restrictFresh (atomic_rename (othersAtomic original inOriginal) relabel)
          · exact renamedAtomic component inContext

end Kept

/-! ## Reflecting a reaction of an unfolding of the canonical form -/

/-- A relation between lists holds through one between their members, both members known. -/
theorem forall₂_imp_mem_both {α β : Type} {relation relation' : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      (∀ a b, a ∈ first → b ∈ second → relation a b → relation' a b) → List.Forall₂ relation' first second
  | _, _, .nil, _ => .nil
  | _, _, .cons head rest, imp => .cons (imp _ _ List.mem_cons_self List.mem_cons_self head)
      (forall₂_imp_mem_both rest fun a b inA inB related =>
        imp a b (List.mem_cons_of_mem _ inA) (List.mem_cons_of_mem _ inB) related)

theorem isReplicated_shape {component : Pattern} (replicated : isReplicated block component = true) :
    ∃ argument, component = .apply block.replicate [argument] := by
  match component, replicated with
  | .apply label [argument], replicated =>
      simp only [isReplicated, beq_iff_eq] at replicated
      exact ⟨argument, by rw [replicated]⟩

/-- A member of the right of a related pair of lists is related to a member of the left. -/
theorem forall₂_mem_right {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      ∀ {b : β}, b ∈ second → ∃ a ∈ first, relation a b
  | _, _, .nil, _, member => absurd member (List.not_mem_nil)
  | _, _, .cons head rest, _, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨a, inFirst, related⟩ := forall₂_mem_right rest later
        exact ⟨a, List.mem_cons_of_mem _ inFirst, related⟩

/-- Related to images, a list is the image. -/
theorem forall₂_eq_map {α β : Type} {map : β → α} :
    ∀ {first : List α} {second : List β}, List.Forall₂ (fun a b => a = map b) first second → first = second.map map
  | _, _, .nil => rfl
  | _, _, .cons head rest => by rw [head, forall₂_eq_map rest]; rfl

section Reflection

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

variable {step : Pattern → Pattern → Prop}

include laws in
/-- **A canonical component renamed reads canonically as itself renamed and read again.** -/
theorem canonR_rename_canonical {pattern : Pattern} (object : isObjectPattern pattern = true)
    (binds : restrictionsBind block.toBlock pattern = true) (canonical : canonP block pattern = Prenex.atom pattern)
    {relabel : Nat → Nat} (injective : Function.Injective relabel) :
    canonR block (rename relabel pattern) = recanon block (rename relabel pattern) := by
  have multisetFresh := replicate_not_multiset (block := block) (language := language)
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  have atomic : decompose block.toBlock pattern = Prenex.atom pattern := by
    have facts := (canonFacts fresh restrictFresh object binds).atomic
    rw [canonical] at facts
    exact facts pattern (List.mem_singleton_self _)
  unfold canonR
  rw [canonP_rename multisetFresh fresh restrictFresh object binds injective, canonical,
    normal_atom_renameOuter fresh restrictFresh atomic]
  rfl

include laws in
/-- **The canonical form of a canonical form is itself.** -/
theorem canonR_canonR {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {pattern : Pattern} {sort : String} (typed : HasType language free bound pattern (.base sort))
    (object : isObjectPattern pattern = true) : canonR block (canonR block pattern) = canonR block pattern := by
  obtain ⟨canonTyped, equivalent⟩ := canonR_sound (block := block) context typed
  exact (canonR_complete (block := block) (base := engineBasePremises RelationEnv.empty) object
    (isObject_canonR object) (restrictionsBind_of_typed (block := block) _ typed) equivalent.toEquationEquiv).symm

include laws in
/-- **A reaction of an unfolding of the canonical form is a reaction of the block beside copies of its own replicated
components**, for a block of canonical components whose replicated components copy one canonical component each:
the reaction's parts and the unfolding's copies are read from the block's components and from copies of the replicated
components they read, under one renaming, and what the reaction leaves reads beside the rest as the unfolding's
reaction leaves it beside the unfolding's rest. -/
theorem replication_reflection (reactions : ReplicationReactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {count : Nat} {components : List Pattern}
    (members : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      components)
    (objects : ∀ component ∈ components, isObjectPattern component = true)
    (canonical : ∀ component ∈ components, canonP block component = Prenex.atom component)
    (servers : ∀ component ∈ components, ∀ argument, component = .apply block.replicate [argument] →
      canonP block argument = Prenex.atom argument ∧ isReplicated block argument = false)
    {depth : Nat} {unfolded : Prenex} (unfolds : UnfoldsWithin block depth (normal block ⟨count, components⟩) unfolded)
    {redex : reactions.Redex} {restU : List Pattern}
    (split : unfolded.components.Perm (reactions.parts redex ++ restU))
    (plain : ∀ part ∈ reactions.parts redex, isReplicated block part = false) :
    ∃ copies : List Pattern, (∀ copy ∈ copies, Pattern.apply block.replicate [copy] ∈ components) ∧
      ∃ target, step (Prenex.restricts block.toBlock count (Prenex.body block.toBlock (components ++ copies))) target ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) language target
          (Prenex.restricts block.toBlock unfolded.count
            (.collection .hashBag (reactions.result redex ++ restU) none)) := by
  classical
  have multisetFresh := replicate_not_multiset (block := block) (language := language)
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  set frame := List.replicate count (TypeExpr.base block.name) ++ bound with frameIs
  have binds : ∀ component ∈ components, restrictionsBind block.toBlock component = true := fun component member =>
    restrictionsBind_of_typed (block := block) component (members component member)
  have atomicOf : ∀ {pattern : Pattern}, isObjectPattern pattern = true → restrictionsBind block.toBlock pattern = true →
      canonP block pattern = Prenex.atom pattern → decompose block.toBlock pattern = Prenex.atom pattern := by
    intro pattern object bindsHere isAtom
    have facts := (canonFacts fresh restrictFresh object bindsHere).atomic
    rw [isAtom] at facts
    exact facts pattern (List.mem_singleton_self _)
  have atomic : (Prenex.mk count components).Atomic block.toBlock := fun component member =>
    atomicOf (objects component member) (binds component member) (canonical component member)
  -- the arguments of the replicated components
  have argumentFacts : ∀ component ∈ components, ∀ argument, component = .apply block.replicate [argument] →
      HasType language free frame argument (.base block.proc) ∧ isObjectPattern argument = true ∧
        decompose block.toBlock argument = Prenex.atom argument ∧ canonP block argument = Prenex.atom argument ∧
        isReplicated block argument = false := by
    intro component member argument componentIs
    have typed := members component member
    rw [componentIs] at typed
    have argumentTyped := replicate_argument_typed typed
    have argumentObject : isObjectPattern argument = true := by
      have object := objects component member
      rw [componentIs] at object
      simpa [isObjectPattern, isObjectPatternList] using object
    obtain ⟨argumentCanonical, argumentPlain⟩ := servers component member argument componentIs
    exact ⟨argumentTyped, argumentObject, atomicOf argumentObject
      (restrictionsBind_of_typed (block := block) _ argumentTyped) argumentCanonical, argumentCanonical, argumentPlain⟩
  have partOfIs : ∀ {argument : Pattern} (relabel : Nat → Nat), decompose block.toBlock argument = Prenex.atom argument →
      partOf block block.replicate (rename relabel argument) = recanon block (rename relabel argument) := by
    intro argument relabel argumentAtomic
    simp only [partOf, if_neg restrictFresh, if_neg multisetFresh]
    exact canonicalOf_atom (atomic_rename argumentAtomic relabel)
  -- the canonical form's replicated components copy one component each
  have kServers : ∀ component ∈ (normal block ⟨count, components⟩).components, ∀ argument,
      component = .apply block.replicate [argument] →
        decompose block.toBlock argument = Prenex.atom argument ∧ isReplicated block argument = false := by
    intro component member argument componentIs
    obtain ⟨relabel, original, inComponents, readIs⟩ := normal_mem_read fresh restrictFresh atomic component member
    have replicated : isReplicated block original = true := by
      have same := congrArg (isReplicated block) readIs
      rw [isReplicated_recanon, isReplicated_rename, componentIs] at same
      simpa [isReplicated] using same.symm
    obtain ⟨originalArgument, rfl⟩ := isReplicated_shape replicated
    obtain ⟨-, -, argumentAtomic, -, argumentPlain⟩ := argumentFacts _ inComponents originalArgument rfl
    rw [rename_apply, List.map_singleton, recanon_apply, List.map_singleton, componentIs,
      partOfIs relabel argumentAtomic] at readIs
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at readIs
    rw [readIs]
    exact ⟨recanon_atom_all fresh restrictFresh (atomic_rename argumentAtomic relabel),
      by rw [isReplicated_recanon, isReplicated_rename, argumentPlain]⟩
  obtain ⟨pairs, unfoldedIs, pairsFacts⟩ := unfolds_atomic fresh restrictFresh unfolds kServers
  have countIs : unfolded.count = (normal block ⟨count, components⟩).count := by rw [unfoldedIs]
  rw [unfoldedIs] at split
  -- the parts, split between the canonical form and the copies; the copies the parts take
  obtain ⟨tags, partsK, partsC, restK, restC, partsIs, kSplit, cSplit, restUPerm⟩ := perm_append_split split
  have partsCSub : partsC.Subperm (pairs.map Prod.snd) :=
    (List.sublist_append_left partsC restC).subperm.trans cSplit.symm.subperm
  obtain ⟨chosen, others, pairsPerm, chosenIs⟩ := exists_perm_map Prod.snd partsCSub
  have restCPerm : restC.Perm (others.map Prod.snd) := by
    have mapped := pairsPerm.map Prod.snd
    rw [List.map_append, chosenIs] at mapped
    exact (List.perm_append_left_iff partsC).mp (cSplit.symm.trans mapped)
  have partsAll : ∀ part ∈ partsK ++ partsC, part ∈ reactions.parts redex := fun part member => by
    rw [partsIs]
    exact (interleave_perm tags partsK partsC).symm.subset member
  have partsKPlain : ∀ part ∈ partsK, isReplicated block part = false := fun part member =>
    plain part (partsAll part (List.mem_append_left _ member))
  have serversIn : ∀ server ∈ (chosen ++ others).map Prod.fst, server ∈ restK := by
    intro server member
    obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp member
    obtain ⟨argument, serverIs, inK, -⟩ := pairsFacts pair (pairsPerm.symm.subset inPairs)
    rcases List.mem_append.mp (kSplit.subset inK) with inParts | inRest
    · have isPlain := partsKPlain _ inParts
      rw [serverIs] at isPlain
      simp [isReplicated] at isPlain
    · exact inRest
  -- the block's components read as them
  obtain ⟨relabel, partsB, othersB, anchors, bPerm, partsRelated, anchorsRelated, anchorsIn, outer, below, injective,
    aligned⟩ := reflect_kept fresh restrictFresh atomic kSplit partsKPlain serversIn
  have countIs : unfolded.count = (normal block ⟨count, components⟩).count := by rw [unfoldedIs]
  -- the replicated components the copies read, and their arguments
  have anchorsComponents : ∀ anchor ∈ anchors, anchor ∈ components := fun anchor member =>
    bPerm.symm.subset (List.mem_append_right _ (anchorsIn anchor member))
  have anchorShape : ∀ anchor ∈ anchors, anchor = .apply block.replicate [argumentOf? anchor] := by
    intro anchor member
    obtain ⟨server, inServers, serverIs⟩ := forall₂_mem_right anchorsRelated member
    obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp inServers
    obtain ⟨argument, pairServer, -, -⟩ := pairsFacts pair (pairsPerm.symm.subset inPairs)
    have replicated : isReplicated block anchor = true := by
      have same := congrArg (isReplicated block) serverIs
      rw [isReplicated_recanon, isReplicated_rename, pairServer] at same
      simpa [isReplicated] using same.symm
    obtain ⟨anchorArgument, rfl⟩ := isReplicated_shape replicated
    rfl
  have pairCopy : ∀ pair anchor, pair ∈ pairs → anchor ∈ anchors → pair.1 = recanon block (rename relabel anchor) →
      pair.2 = recanon block (rename relabel (argumentOf? anchor)) := by
    intro pair anchor inPairs inAnchors serverIs
    obtain ⟨argument, pairServer, -, pairCopyIs⟩ := pairsFacts pair inPairs
    have anchorIs := anchorShape anchor inAnchors
    obtain ⟨-, -, argumentAtomic, -, -⟩ := argumentFacts _ (anchorsComponents _ inAnchors) _ anchorIs
    rw [anchorIs, pairServer, rename_apply, List.map_singleton, recanon_apply, List.map_singleton,
      partOfIs relabel argumentAtomic] at serverIs
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at serverIs
    rw [pairCopyIs, serverIs, recanon_recanon fresh restrictFresh (idemUpTo_all fresh restrictFresh _)]
  have anchorsLength : anchors.length = chosen.length + others.length := by
    rw [← anchorsRelated.length_eq]
    simp
  set anchorsChosen := anchors.take chosen.length with anchorsChosenIs
  set anchorsOthers := anchors.drop chosen.length with anchorsOthersIs
  have chosenRelated : List.Forall₂ (fun server anchor => server = recanon block (rename relabel anchor))
      (chosen.map Prod.fst) anchorsChosen := by
    have taken := List.forall₂_take chosen.length anchorsRelated
    rwa [List.map_append, List.take_left' (by simp)] at taken
  have othersRelated : List.Forall₂ (fun server anchor => server = recanon block (rename relabel anchor))
      (others.map Prod.fst) anchorsOthers := by
    have dropped := List.forall₂_drop chosen.length anchorsRelated
    rwa [List.map_append, List.drop_left' (by simp)] at dropped
  set copiesChosen := anchorsChosen.map argumentOf? with copiesChosenIs
  set copiesOthers := anchorsOthers.map argumentOf? with copiesOthersIs
  have copiesRelated : List.Forall₂ (fun part copy => part = recanon block (rename relabel copy)) partsC
      copiesChosen := by
    rw [← chosenIs, copiesChosenIs, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    rw [List.forall₂_map_left_iff] at chosenRelated
    exact forall₂_imp_mem_both chosenRelated fun pair anchor inChosen inAnchors serverIs =>
      pairCopy pair anchor (pairsPerm.symm.subset (List.mem_append_left _ inChosen)) (List.mem_of_mem_take inAnchors)
        serverIs
  have restCopies : others.map Prod.snd = (copiesOthers.map (rename relabel)).map (recanon block) := by
    rw [List.map_map]
    apply forall₂_eq_map
    rw [copiesOthersIs, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    rw [List.forall₂_map_left_iff] at othersRelated
    exact forall₂_imp_mem_both othersRelated fun pair anchor inOthers inAnchors serverIs =>
      pairCopy pair anchor (pairsPerm.symm.subset (List.mem_append_right _ inOthers)) (List.mem_of_mem_drop inAnchors)
        serverIs
  set copies := copiesChosen ++ copiesOthers with copiesIs
  have copiesArgs : ∀ copy ∈ copies, ∃ anchor ∈ anchors, anchor = .apply block.replicate [copy] := by
    intro copy member
    have inAll : copy ∈ anchors.map argumentOf? := by
      rw [← List.take_append_drop chosen.length anchors, List.map_append]
      exact member
    obtain ⟨anchor, inAnchors, rfl⟩ := List.mem_map.mp inAll
    exact ⟨anchor, inAnchors, anchorShape anchor inAnchors⟩
  have wFacts : ∀ w ∈ components ++ copies, HasType language free frame w (.base block.proc) ∧
      isObjectPattern w = true ∧ canonP block w = Prenex.atom w ∧ decompose block.toBlock w = Prenex.atom w := by
    intro w member
    rcases List.mem_append.mp member with inComponents | inCopies
    · exact ⟨members w inComponents, objects w inComponents, canonical w inComponents, atomic w inComponents⟩
    · obtain ⟨anchor, inAnchors, anchorIs⟩ := copiesArgs w inCopies
      obtain ⟨typed, object, argumentAtomic, canonicalArgument, -⟩ :=
        argumentFacts anchor (anchorsComponents anchor inAnchors) w anchorIs
      exact ⟨typed, object, canonicalArgument, argumentAtomic⟩
  -- the parts the block's reaction takes
  set wParts := interleave tags partsB copiesChosen with wPartsIs
  have partsWRelated : List.Forall₂ (fun part w => part = recanon block (rename relabel w)) (reactions.parts redex)
      wParts := by
    rw [partsIs, wPartsIs]
    exact interleave_forall₂ tags partsRelated copiesRelated
  set restW := othersB ++ copiesOthers with restWIs
  have wPerm : (components ++ copies).Perm (wParts ++ restW) := by
    have first : (components ++ copies).Perm ((partsB ++ othersB) ++ (copiesChosen ++ copiesOthers)) :=
      bPerm.append_right _
    refine first.trans ?_
    have middle : ((partsB ++ othersB) ++ (copiesChosen ++ copiesOthers)).Perm
        ((partsB ++ copiesChosen) ++ (othersB ++ copiesOthers)) := by
      simp only [List.append_assoc]
      refine List.Perm.append_left partsB ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _
    exact middle.trans ((interleave_perm tags partsB copiesChosen).symm.append_right _)
  have wPartsIn : ∀ w ∈ wParts, w ∈ components ++ copies := fun w member =>
    wPerm.symm.subset (List.mem_append_left _ member)
  have restWIn : ∀ w ∈ restW, w ∈ components ++ copies := fun w member =>
    wPerm.symm.subset (List.mem_append_right _ member)
  -- the restrictions the parts mention are attached to the block's parts and replicated components
  have wAttached : ∀ w ∈ wParts, ∀ index, FreeIn index w → index < count →
      ∃ held ∈ partsB ++ anchors, mentions index held = true := by
    intro w member index free _
    rcases List.mem_append.mp ((interleave_perm tags partsB copiesChosen).subset member) with inParts | inCopies
    · exact ⟨w, List.mem_append_left _ inParts, (mentions_iff w index).mpr free⟩
    · obtain ⟨anchor, inAnchors, rfl⟩ := List.mem_map.mp inCopies
      have anchorIn : anchor ∈ anchors := List.mem_of_mem_take inAnchors
      refine ⟨anchor, List.mem_append_right _ anchorIn, (mentions_iff anchor index).mpr ?_⟩
      rw [anchorShape anchor anchorIn]
      exact Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mpr ⟨_, List.mem_singleton_self _, free⟩
  -- a renaming into the unfolding, injective, agreeing with the reading on the parts
  have injOn : ∀ first second, (∃ w ∈ wParts, FreeIn first w) → (∃ w ∈ wParts, FreeIn second w) →
      relabel first = relabel second → first = second := by
    rintro first second ⟨w, inW, freeFirst⟩ ⟨w', inW', freeSecond⟩ same
    by_cases firstBelow : first < count <;> by_cases secondBelow : second < count
    · exact injective first firstBelow second secondBelow (wAttached w inW first freeFirst firstBelow)
        (wAttached w' inW' second freeSecond secondBelow) same
    · have small := below first firstBelow (wAttached w inW first freeFirst firstBelow)
      rw [show second = count + (second - count) by omega, outer] at same
      omega
    · have small := below second secondBelow (wAttached w' inW' second freeSecond secondBelow)
      rw [show first = count + (first - count) by omega, outer] at same
      omega
    · rw [show first = count + (first - count) by omega, show second = count + (second - count) by omega, outer,
        outer] at same
      omega
  obtain ⟨limit, bounded⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
    (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le) wParts fun pattern _ =>
      exists_freeBound pattern
  obtain ⟨relabel', injective', agrees'⟩ := exists_injective_agree relabel limit
    (fun index => ∃ w ∈ wParts, FreeIn index w)
    fun first second _ firstIn _ secondIn same => injOn first second firstIn secondIn same
  have agrees : ∀ w ∈ wParts, ∀ index, FreeIn index w → relabel' index = relabel index := fun w member index free =>
    agrees' index (bounded w member index free) ⟨w, member, free⟩
  -- the unfolding's components are typed object atoms
  have normalMembers := (normal_sound (block := block) (language := language) context
    (form := ⟨count, components⟩) members).1
  have unfoldedMembers := unfolds.members context normalMembers
  have unfoldedObjects := unfolds.objects (normal_objects objects)
  have unfoldedAtomic := unfolds.atomic fresh restrictFresh (normal_atomic fresh restrictFresh atomic)
  have inUnfolded : ∀ component ∈ reactions.parts redex ++ restU, component ∈ unfolded.components := by
    intro component member
    have := split.symm.subset member
    rw [unfoldedIs]
    exact this
  have partsMembers : Members language block.toBlock free
      (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound) (reactions.parts redex) :=
    fun part member => unfoldedMembers part (inUnfolded part (List.mem_append_left _ member))
  have partsObjects : ∀ part ∈ reactions.parts redex, isObjectPattern part = true := fun part member =>
    unfoldedObjects part (inUnfolded part (List.mem_append_left _ member))
  -- the parts the block's reaction takes, renamed into the unfolding
  have mapsW : ∀ w ∈ wParts, ∀ index, FreeIn index w →
      (index < count → relabel' index < unfolded.count) ∧
        (count ≤ index → relabel' index = unfolded.count + (index - count)) := by
    intro w member index free
    rw [agrees w member index free, countIs]
    refine ⟨fun inside => below index inside (wAttached w member index free inside), fun above => ?_⟩
    have shifted := outer (index - count)
    rwa [show count + (index - count) = index by omega] at shifted
  set shown := wParts.map (rename relabel') with shownIs
  have shownMembers : Members language block.toBlock free
      (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound) shown := by
    intro element member
    obtain ⟨w, inW, rfl⟩ := List.mem_map.mp member
    exact rename_typed_on_support (wFacts w (wPartsIn w inW)).1 fun index sort free lookup =>
      frame_lookup (mapsW w inW index free) lookup
  have shownObjects : ∀ part ∈ shown, isObjectPattern part = true := by
    intro element member
    obtain ⟨w, inW, rfl⟩ := List.mem_map.mp member
    rw [isObjectPattern_rename]
    exact (wFacts w (wPartsIn w inW)).2.1
  have alikeRelated : List.Forall₂ (fun part original => AlikeR block part (canonR block original)) shown
      (reactions.parts redex) := by
    rw [shownIs, List.forall₂_map_left_iff]
    refine forall₂_imp_mem_both partsWRelated.flip fun w part inW _ partIs => ?_
    obtain ⟨typed, object, canonicalW, -⟩ := wFacts w (wPartsIn w inW)
    have renamedSame : rename relabel w = rename relabel' w :=
      rename_congr w fun index free => (agrees w inW index free).symm
    have canonIs : canonR block part = part := by
      rw [partIs, renamedSame, ← canonR_rename_canonical (language := language) object
        (restrictionsBind_of_typed (block := block) _ typed) canonicalW injective']
      exact canonR_canonR (context.replicate unfolded.count block.name) (shownMembers _ (List.mem_map_of_mem inW))
        (by rw [isObjectPattern_rename]; exact object)
    rw [canonIs, partIs, renamedSame]
    exact alike_recanon_all fresh restrictFresh _
  obtain ⟨redex', partsIs', resultsRelated⟩ := reactions.alike (context.replicate unfolded.count block.name) redex
    shown partsMembers partsObjects shownMembers shownObjects alikeRelated
  -- renamed back into the block
  set back := Function.invFun relabel' with backIs
  have leftInverse : Function.LeftInverse back relabel' := Function.leftInverse_invFun injective'
  have renamedBack : ∀ pattern, rename back (rename relabel' pattern) = pattern := by
    intro pattern
    rw [rename_comp]
    have identity : back ∘ relabel' = id := funext fun index => leftInverse index
    rw [identity, rename_id]
  set redexW := reactions.rename back redex' with redexWIs
  have partsW : reactions.parts redexW = wParts := by
    rw [redexWIs, reactions.parts_rename, partsIs', shownIs, List.map_map]
    conv_rhs => rw [← List.map_id wParts]
    exact List.map_congr_left fun w _ => renamedBack w
  obtain ⟨target, stepped, targetIs⟩ := reactions.react redexW (components := components ++ copies) (rest := restW)
    (by rw [partsW]; exact wPerm) (fun w member => (wFacts w member).1) (fun w member => (wFacts w member).2.1)
  refine ⟨copies, fun copy member => ?_, Prenex.restricts block.toBlock count target,
    reactions.restricts_step count stepped, ?_⟩
  · obtain ⟨anchor, inAnchors, anchorIs⟩ := copiesArgs copy member
    rw [← anchorIs]
    exact anchorsComponents anchor inAnchors
  -- what the block's reaction leaves, renamed into the unfolding, is what the unfolding's reaction leaves
  have resultsBack : (reactions.result redexW).map (rename relabel') = reactions.result redex' := by
    rw [redexWIs, reactions.result_rename, List.map_map]
    conv_rhs => rw [← List.map_id (reactions.result redex')]
    refine List.map_congr_left fun result member => ?_
    simp only [Function.comp_apply, rename_comp, id]
    conv_rhs => rw [← rename_id result]
    apply rename_congr
    intro index free
    obtain ⟨part, inParts, partFree⟩ := reactions.freeIn_result redex' member free
    rw [partsIs', shownIs] at inParts
    obtain ⟨w, inW, rfl⟩ := List.mem_map.mp inParts
    obtain ⟨original, -, rfl⟩ := (freeIn_rename w).mp partFree
    simp only [Function.comp_apply, id]
    rw [leftInverse original]
  have partsWMembers : Members language block.toBlock free frame (reactions.parts redexW) := by
    rw [partsW]
    exact fun w member => (wFacts w (wPartsIn w member)).1
  have partsWObjects : ∀ part ∈ reactions.parts redexW, isObjectPattern part = true := by
    rw [partsW]
    exact fun w member => (wFacts w (wPartsIn w member)).2.1
  have resultsAttached : ∀ result ∈ reactions.result redexW, ∀ index, FreeIn index result →
      ∃ w ∈ wParts, FreeIn index w := by
    intro result member index free
    obtain ⟨part, inParts, partFree⟩ := reactions.freeIn_result redexW member free
    rw [partsW] at inParts
    exact ⟨part, inParts, partFree⟩
  -- the rest of the block reads beside any context of the parts as the unfolding's rest
  have restFormIs : (restW.map (canonP block)).foldr Prenex.par Prenex.nil = ⟨0, restW⟩ := by
    have mapped : restW.map (canonP block) = restW.map Prenex.atom :=
      List.map_congr_left fun w member => (wFacts w (restWIn w member)).2.2.1
    rw [mapped, foldr_par_atoms]
  have normalAtomic := normal_atomic fresh restrictFresh atomic
  have restKAtomic : ∀ component ∈ restK, decompose block.toBlock component = Prenex.atom component :=
    fun component member => normalAtomic component (kSplit.symm.subset (List.mem_append_right _ member))
  have alignedExtra : ∀ extra : List Pattern,
      (∀ component ∈ extra, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ extra, ∀ index < 0 + count, mentions index component = true →
        ∃ held ∈ partsB ++ anchors, mentions index held = true) →
      normal block ⟨0 + count, restW ++ extra⟩ =
        normal block ⟨unfolded.count, restU ++ extra.map (rename relabel)⟩ := by
    intro extra extraAtomic extraAttached
    have contextAtomic : ∀ component ∈ copiesOthers ++ extra,
        decompose block.toBlock component = Prenex.atom component := by
      intro component member
      rcases List.mem_append.mp member with inCopies | inExtra
      · exact (wFacts component (List.mem_append_right _ (List.mem_append_right _ inCopies))).2.2.2
      · exact extraAtomic component inExtra
    have contextAttached : ∀ component ∈ copiesOthers ++ extra, ∀ index < count,
        mentions index component = true → ∃ held ∈ partsB ++ anchors, mentions index held = true := by
      intro component member index inside mentioned
      rcases List.mem_append.mp member with inCopies | inExtra
      · obtain ⟨anchor, inAnchors, anchorIs⟩ := copiesArgs component (List.mem_append_right _ inCopies)
        refine ⟨anchor, List.mem_append_right _ inAnchors, (mentions_iff anchor index).mpr ?_⟩
        rw [anchorIs]
        exact Mettapedia.OSLF.MeTTaIL.CanonicalBags.freeIn_apply.mpr
          ⟨_, List.mem_singleton_self _, (mentions_iff component index).mp mentioned⟩
      · exact extraAttached component inExtra index (by omega) mentioned
    have keptAligned := aligned (copiesOthers ++ extra) contextAtomic contextAttached
    rw [Nat.zero_add, restWIs, List.append_assoc, keptAligned, countIs, List.map_append]
    set copiesRenamed := copiesOthers.map (rename relabel) with copiesRenamedIs
    set extraRenamed := extra.map (rename relabel) with extraRenamedIs
    have renamedAtomic : ∀ component ∈ copiesRenamed ++ extraRenamed,
        decompose block.toBlock component = Prenex.atom component := by
      intro component member
      rw [copiesRenamedIs, extraRenamedIs, ← List.map_append] at member
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      exact atomic_rename (contextAtomic original inOriginal) relabel
    have firstAtomic : (Prenex.mk (normal block ⟨count, components⟩).count
        (restK ++ (copiesRenamed ++ extraRenamed))).Atomic block.toBlock := by
      intro component member
      rcases List.mem_append.mp member with inRest | inRenamed
      · exact restKAtomic component inRest
      · exact renamedAtomic component inRenamed
    have reordered : (restK ++ (copiesRenamed ++ extraRenamed)).Perm ((restK ++ extraRenamed) ++ copiesRenamed) := by
      rw [List.append_assoc]
      exact List.Perm.append_left restK List.perm_append_comm
    rw [normal_perm fresh restrictFresh reordered firstAtomic,
      ← normal_recanon_append fresh restrictFresh (restK ++ extraRenamed) copiesRenamed
        (fun component member => firstAtomic component (reordered.symm.subset member)),
      copiesRenamedIs, ← restCopies]
    have restAtomic : (Prenex.mk (normal block ⟨count, components⟩).count
        ((restK ++ extraRenamed) ++ others.map Prod.snd)).Atomic block.toBlock := by
      intro component member
      rcases List.mem_append.mp member with inFront | inCopies
      · exact firstAtomic component (reordered.symm.subset (List.mem_append_left _ inFront))
      · rw [restCopies] at inCopies
        obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inCopies
        exact recanon_atom_all fresh restrictFresh (renamedAtomic original (List.mem_append_left _ inOriginal))
    refine normal_perm fresh restrictFresh ?_ restAtomic
    have restUIs : restU.Perm (restK ++ others.map Prod.snd) := restUPerm.trans (restCPerm.append_left restK)
    have regrouped : ((restK ++ extraRenamed) ++ others.map Prod.snd).Perm
        ((restK ++ others.map Prod.snd) ++ extraRenamed) := by
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left restK List.perm_append_comm
    exact regrouped.trans (restUIs.symm.append_right _)
  have aligned' := results_aligned (block := block) (language := language) context (count := count) (inner := 0)
    (unfolded := unfolded.count) (rest := restW) (tail := restW) (results := reactions.result redexW) (restU := restU)
    (outer := relabel) (relabel := relabel')
    (attached := fun index => ∃ held ∈ partsB ++ anchors, mentions index held = true)
    restFormIs (fun w member => (wFacts w (restWIn w member)).1) (fun w member => (wFacts w (restWIn w member)).2.1)
    (reactions.result_members redexW partsWMembers) (reactions.result_objects redexW partsWObjects)
    (by rw [resultsBack]; exact reactions.result_members redex' (by rw [partsIs']; exact shownMembers))
    (fun component member => unfoldedMembers component (inUnfolded component (List.mem_append_right _ member)))
    (fun component member => unfoldedAtomic component (inUnfolded component (List.mem_append_right _ member)))
    (fun index => by rw [Nat.zero_add, outer, countIs])
    (fun index inside attached => by rw [countIs]; exact below index (by omega) attached)
    alignedExtra
    (fun result member index free inside => by
      obtain ⟨w, inW, wFree⟩ := resultsAttached result member index free
      simpa using wAttached w inW index wFree inside)
    injective'
    (fun result member index free => by
      obtain ⟨w, inW, wFree⟩ := resultsAttached result member index free
      simpa using agrees w inW index wFree)
    (fun first second ⟨result, member, free⟩ ⟨result', member', free'⟩ same => by
      simp only [Nat.add_zero] at same
      exact injOn first second (resultsAttached result member first free) (resultsAttached result' member' second free')
        same)
  rw [resultsBack] at aligned'
  have resultsSame := collection_equation (language := language)
    (List.rel_append resultsRelated (List.forall₂_same.mpr fun _ _ => .refl _)) (second := _ ++ restU) []
  simp only [List.nil_append] at resultsSame
  exact Relation.EqvGen.trans _ _ _ (restricts_equation (block := block.toBlock) count targetIs)
    (Relation.EqvGen.trans _ _ _ aligned' (restricts_equation (block := block.toBlock) unfolded.count resultsSame))

end Reflection

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
