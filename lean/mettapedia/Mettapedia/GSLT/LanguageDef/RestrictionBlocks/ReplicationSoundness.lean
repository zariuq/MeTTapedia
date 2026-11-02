import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLaws
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.MoleculeSplit

/-!
# Soundness of the canonical form with replication

Every move the canonical form with replication makes is a chain of laws through processes:

- `replicate_bag_equivalent`: replication of a bag is the bag of the replications, `!{P₁, …, Pₙ} ≡ {!P₁, …, !Pₙ}`,
  from the binary law by induction, with `!0 ≡ 0` for the empty bag;
- `replicate_molecules_equivalent`: a replicated block is its replicated molecules side by side, since a block is
  its molecules side by side (`molecules_equivalent`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn)

variable {language : LanguageDef} {block : ReplicationBlock} [laws : ReplicationSignature language block]

/-- **Replication of a bag is the bag of the replications.** -/
theorem replicate_bag_equivalent {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {members : List Pattern}, Members language block.toBlock free bound members →
      ProcEquiv language block.toBlock free bound (.apply block.replicate [.collection .hashBag members none])
        (.collection .hashBag (members.map fun member => .apply block.replicate [member]) none)
  | [], _ => by
      have empty : ProcEquiv language block.toBlock free bound (.collection .hashBag [] none)
          (.apply block.unit []) := bag_body_equivalent (block := block.toBlock) Members.nil
      exact .trans _ _ _ (replicate_fill empty) (.trans _ _ _ replicate_nil_equivalent (.symm _ _ empty))
  | head :: tail, members => by
      have headTyped := members head List.mem_cons_self
      have tailMembers : Members language block.toBlock free bound tail := members.tail
      have regroup := bag_cons_equivalent (block := block.toBlock) headTyped tailMembers
      have split := replicate_par_equivalent headTyped (bag_typed (block := block.toBlock) (rest := none) tailMembers)
      have inner := replicate_bag_equivalent tailMembers
      have replicatedTail : Members language block.toBlock free bound
          (tail.map fun member => .apply block.replicate [member]) := by
        intro element member
        obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
        exact replicate_typed (tailMembers original originalIn)
      have filled := bag_fill (before := [.apply block.replicate [head]]) (after := []) (rest := none)
        (Members.cons (replicate_typed headTyped) Members.nil) Members.nil inner
      simp only [List.cons_append, List.nil_append] at filled
      simp only [List.map_cons]
      exact .trans _ _ _ (replicate_fill (.symm _ _ regroup)) (.trans _ _ _ split
        (.trans _ _ _ filled (bag_cons_equivalent (replicate_typed headTyped) replicatedTail)))

/-- The molecules of a typed block are processes. -/
theorem molecules_members {free : FreeTypeContext} {bound : List TypeExpr} {form : Prenex}
    (members : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components) :
    Members language block.toBlock free bound
      ((groups form).map fun group => Prenex.toPattern block.toBlock (Prenex.molecule form.count group)) := by
  intro element member
  obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨partition, permuted⟩ := groups_partition form
  exact molecule_typed (fun element listed => members element
    (permuted.subset (List.mem_flatMap.mpr ⟨group, groupMember, listed⟩))) (partition.uses group groupMember)

/-- **A replicated block is its replicated molecules side by side.** -/
theorem replicate_molecules_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {form : Prenex}
    (members : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components) :
    ProcEquiv language block.toBlock free bound (.apply block.replicate [Prenex.toPattern block.toBlock form])
      (.collection .hashBag ((groups form).map fun group =>
        .apply block.replicate [Prenex.toPattern block.toBlock (Prenex.molecule form.count group)]) none) := by
  have split := replicate_bag_equivalent (molecules_members members)
  simp only [List.map_map, Function.comp_def] at split
  exact .trans _ _ _ (replicate_fill (molecules_equivalent members)) split

/-- **The replicated components of a block are its replicated molecules**, each read by a sound canonical form. -/
theorem replicatedOf_sound {free : FreeTypeContext} {bound : List TypeExpr} {canonical : Pattern → Pattern}
    {inner : Prenex}
    (sound : ∀ {process : Pattern}, HasType language free bound process (.base block.proc) →
      HasType language free bound (canonical process) (.base block.proc) ∧
        ProcEquiv language block.toBlock free bound process (canonical process))
    (members : Members language block.toBlock free (List.replicate inner.count (TypeExpr.base block.name) ++ bound)
      inner.components) :
    ProcEquiv language block.toBlock free bound (.apply block.replicate [Prenex.toPattern block.toBlock inner])
      (.collection .hashBag (replicatedOf block canonical inner) none) := by
  refine .trans _ _ _ (replicate_molecules_equivalent members) ?_
  have moleculeMembers := molecules_members members
  have pointwise : ∀ group ∈ groups inner,
      ProcEquiv language block.toBlock free bound
        (.apply block.replicate [Prenex.toPattern block.toBlock (Prenex.molecule inner.count group)])
        (match (Prenex.molecule inner.count group).count, (Prenex.molecule inner.count group).components with
          | 0, [.apply label [argument]] =>
              if label = block.replicate then .apply label [canonical argument]
              else .apply block.replicate [canonical (Prenex.toPattern block.toBlock (Prenex.molecule inner.count group))]
          | _, _ => .apply block.replicate [canonical (Prenex.toPattern block.toBlock (Prenex.molecule inner.count group))]) := by
    intro group member
    have typed := moleculeMembers _ (List.mem_map_of_mem member)
    have whole : ProcEquiv language block.toBlock free bound
        (.apply block.replicate [Prenex.toPattern block.toBlock (Prenex.molecule inner.count group)])
        (.apply block.replicate [canonical (Prenex.toPattern block.toBlock (Prenex.molecule inner.count group))]) :=
      replicate_fill (sound typed).2
    generalize Prenex.molecule inner.count group = form at typed whole ⊢
    split
    · rename_i _ label argument countIs componentsIs
      obtain ⟨count, components⟩ := form
      simp only at countIs componentsIs
      subst countIs componentsIs
      split_ifs with replicated
      · subst replicated
        have argumentTyped : HasType language free bound argument (.base block.proc) := by
          have : Prenex.toPattern block.toBlock ⟨0, [.apply block.replicate [argument]]⟩ =
              .apply block.replicate [argument] := rfl
          rw [this] at typed
          obtain ⟨rule, ruleMember, labelIs, -, -, arguments⟩ :=
            Mettapedia.GSLT.LanguageDef.WellSorted.hasType_apply_inversion typed
          obtain ⟨-, parameter, params⟩ := laws.replicateShape rule ruleMember labelIs.symm
          rw [params] at arguments
          cases arguments with
          | cons _ parameterType argumentTyped _ =>
              simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at parameterType
              subst parameterType
              exact argumentTyped
        have twice := replicate_twice_equivalent argumentTyped
        exact .trans _ _ _ twice (replicate_fill (sound argumentTyped).2)
      · exact whole
    · exact whole
  have replicatedMembers : Members language block.toBlock free bound ((groups inner).map fun group =>
      .apply block.replicate [Prenex.toPattern block.toBlock (Prenex.molecule inner.count group)]) := by
    intro element member
    obtain ⟨group, groupMember, rfl⟩ := List.mem_map.mp member
    exact replicate_typed (moleculeMembers _ (List.mem_map_of_mem groupMember))
  refine collection_congr none replicatedMembers ?_ [] Members.nil
  simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  exact pointwise

/-! ## Absorption -/

omit laws in
/-- An element listed twice in a pairwise related list is related to itself. -/
theorem pairwise_self_of_mem_erase {α : Type} [DecidableEq α] {relation : α → α → Prop} :
    ∀ {list : List α} {element : α}, list.Pairwise relation → element ∈ list.erase element →
      relation element element
  | [], _, _, member => by simp at member
  | head :: tail, element, pairwise, member => by
      rw [List.pairwise_cons] at pairwise
      by_cases same : head = element
      · subst same
        rw [List.erase_cons_head] at member
        exact pairwise.1 head member
      · rw [List.erase_cons_tail (by simpa using same)] at member
        rcases List.mem_cons.mp member with rfl | inTail
        · exact absurd rfl same
        · exact pairwise_self_of_mem_erase pairwise.2 inTail

/-- A bag is any reordering of its members. -/
theorem bag_perm_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {first second : List Pattern}
    (members : Members language block.toBlock free bound first) (permutation : first.Perm second) :
    ProcEquiv language block.toBlock free bound (.collection .hashBag first none) (.collection .hashBag second none) := by
  have secondMembers : Members language block.toBlock free bound second :=
    fun element member => members element (permutation.symm.subset member)
  exact SortedEquiv.ofDerived
    (Mettapedia.GSLT.LanguageDef.EquationSemantics.DerivedInstance.bagPerm_of_sorted
      ⟨free, bound, bag_typed members⟩ permutation) (bag_typed members) (bag_typed secondMembers)

/-- **A copy beside its replication is absorbed**: `{P | !P | rest} ≡ {!P | rest}`. -/
theorem unfold_absorb_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {copy : Pattern}
    {rest : List Pattern} (copyTyped : HasType language free bound copy (.base block.proc))
    (restMembers : Members language block.toBlock free bound rest)
    (replicated : .apply block.replicate [copy] ∈ rest) :
    ProcEquiv language block.toBlock free bound (.collection .hashBag (copy :: rest) none)
      (.collection .hashBag rest none) := by
  have permuted : rest.Perm (.apply block.replicate [copy] :: rest.erase (.apply block.replicate [copy])) :=
    List.perm_cons_erase replicated
  set others := rest.erase (.apply block.replicate [copy])
  have othersMembers : Members language block.toBlock free bound others :=
    fun element member => restMembers element (permuted.symm.subset (List.mem_cons_of_mem _ member))
  have bangTyped := replicate_typed copyTyped
  have pairMembers : Members language block.toBlock free bound [copy, .apply block.replicate [copy]] :=
    Members.cons copyTyped (Members.cons bangTyped Members.nil)
  have reordered := bag_perm_equivalent (Members.cons copyTyped restMembers) (permuted.cons copy)
  have paired := bag_pair_equivalent pairMembers othersMembers
  have consed := bag_cons_equivalent (bag_typed (block := block.toBlock) (rest := none) pairMembers) othersMembers
  have unfolded := bag_fill (before := []) (after := others) (rest := none) Members.nil othersMembers
    (.symm _ _ (unfold_equivalent copyTyped))
  simp only [List.nil_append] at unfolded
  have back := bag_perm_equivalent (Members.cons bangTyped othersMembers) permuted.symm
  simp only [List.cons_append, List.nil_append] at paired
  exact .trans _ _ _ reordered (.trans _ _ _ (.symm _ _ paired) (.trans _ _ _ consed
    (.trans _ _ _ unfolded back)))

/-- **The argument of a typed replication is a process.** -/
theorem replicate_argument_typed {free : FreeTypeContext} {bound : List TypeExpr} {argument : Pattern}
    (typed : HasType language free bound (.apply block.replicate [argument]) (.base block.proc)) :
    HasType language free bound argument (.base block.proc) := by
  obtain ⟨rule, ruleMember, labelIs, -, -, arguments⟩ :=
    Mettapedia.GSLT.LanguageDef.WellSorted.hasType_apply_inversion typed
  obtain ⟨-, parameter, params⟩ := laws.replicateShape rule ruleMember labelIs.symm
  rw [params] at arguments
  cases arguments with
  | cons _ parameterType argumentTyped _ =>
      simp only [Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.some.injEq] at parameterType
      subst parameterType
      exact argumentTyped

/-- **Restrictions over inaction are inaction.** -/
theorem restricts_unit_equivalent {free : FreeTypeContext} :
    ∀ (count : Nat) {bound : List TypeExpr}, ProcEquiv language block.toBlock free bound
      (Prenex.restricts block.toBlock count (.apply block.unit [])) (.apply block.unit [])
  | 0, _ => .refl _
  | count + 1, _ => by
      rw [Prenex.restricts_succ]
      exact .trans _ _ _ (restrict_fill (restricts_unit_equivalent count)) restriction_nil_equivalent

/-- **Restrictions no component uses drop**, the others renumbered in their order. -/
theorem drop_unused_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {count : Nat}
    {restrictions : List Nat} (nodup : restrictions.Nodup) (inside : ∀ index ∈ restrictions, index < count)
    {components : List Pattern}
    (members : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      components)
    (apart : ∀ component ∈ components, ∀ index ∈ restrictions, ¬ FreeIn index component) :
    Members language block.toBlock free
        (List.replicate (outsideOf count restrictions).length (TypeExpr.base block.name) ++ bound)
        (components.map (rename (Prenex.groupIndex count (outsideOf count restrictions)))) ∧
      ProcEquiv language block.toBlock free bound (Prenex.toPattern block.toBlock ⟨count, components⟩)
        (Prenex.toPattern block.toBlock ⟨(outsideOf count restrictions).length,
          components.map (rename (Prenex.groupIndex count (outsideOf count restrictions)))⟩) := by
  obtain ⟨narrowMembers, narrowEquivalent⟩ := narrow_equivalent (block := block.toBlock) nodup inside
    (part := []) (rest := components) (by simpa using members) apart
  have restMembers := narrowMembers.tail
  refine ⟨restMembers, ?_⟩
  set renamed := components.map (rename (Prenex.groupIndex count (outsideOf count restrictions)))
  have emptyCopy : copyOf block.toBlock count ⟨restrictions, []⟩ =
      Prenex.restricts block.toBlock restrictions.length (.apply block.unit []) := rfl
  have copyTyped := narrowMembers _ List.mem_cons_self
  rw [emptyCopy] at copyTyped
  have inner : ProcEquiv language block.toBlock free
      (List.replicate (outsideOf count restrictions).length (TypeExpr.base block.name) ++ bound)
      (Prenex.body block.toBlock (copyOf block.toBlock count ⟨restrictions, []⟩ :: renamed))
      (Prenex.body block.toBlock renamed) := by
    rw [emptyCopy]
    have toBag := bag_body_equivalent (block := block.toBlock) (Members.cons copyTyped restMembers)
    have emptied := bag_fill (before := []) (after := renamed) (rest := none) Members.nil restMembers
      (restricts_unit_equivalent restrictions.length)
    simp only [List.nil_append] at emptied
    have unitTyped : HasType language free
        (List.replicate (outsideOf count restrictions).length (TypeExpr.base block.name) ++ bound)
        (.collection .hashBag (.apply block.unit [] :: renamed) none) (.base block.proc) :=
      bag_typed (Members.cons laws.unit_typed restMembers)
    have dropped := SortedEquiv.ofDerived (laws.unitElim (pre := []) (post := renamed) (by simpa using unitTyped))
      (by simpa using unitTyped) (bag_typed restMembers)
    simp only [List.nil_append] at dropped
    have fromBag := bag_body_equivalent (block := block.toBlock) restMembers
    exact .trans _ _ _ (.symm _ _ toBag) (.trans _ _ _ emptied (.trans _ _ _ dropped fromBag))
  exact .trans _ _ _ narrowEquivalent
    (restricts_congr (block := block.toBlock) (outsideOf count restrictions).length inner)

omit laws in
/-- The restrictions some component uses are those outside the ones none uses. -/
theorem outsideOf_unused (count : Nat) (components : List Pattern) :
    outsideOf count ((List.range count).filter fun index => !components.any (mentions index)) =
      (List.range count).filter fun index => components.any (mentions index) := by
  unfold outsideOf
  apply List.filter_congr
  intro index member
  by_cases used : components.any (mentions index) = true
  · simp [used]
  · have unused : components.any (mentions index) = false := by simpa using used
    simp [unused, List.mem_range.mp member]

/-- **Dropping the restrictions no component uses is sound.** -/
theorem prune_sound {free : FreeTypeContext} {bound : List TypeExpr} {form : Prenex}
    (members : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components) :
    Members language block.toBlock free (List.replicate form.prune.count (TypeExpr.base block.name) ++ bound)
        form.prune.components ∧
      ProcEquiv language block.toBlock free bound (Prenex.toPattern block.toBlock form)
        (Prenex.toPattern block.toBlock form.prune) := by
  obtain ⟨count, components⟩ := form
  have dropped := drop_unused_equivalent (restrictions := (List.range count).filter fun index =>
      !components.any (mentions index)) (List.nodup_range.filter _)
    (fun index member => List.mem_range.mp (List.mem_filter.mp member).1) members (by
      intro component inComponents index listed freeHere
      have unused := (List.mem_filter.mp listed).2
      simp only [Bool.not_eq_true', List.any_eq_false] at unused
      exact absurd ((mentions_iff component index).mpr freeHere) (by simp [unused component inComponents]))
  rw [outsideOf_unused] at dropped
  exact dropped

/-- **One absorption is sound**, when the canonical form it compares by is: dropping a copy of a replicated
component's argument, with the restrictions only the copy uses, is unfolding read backwards. -/
theorem absorbOnce_sound {free : FreeTypeContext} {bound : List TypeExpr} {canonical : Pattern → Pattern}
    {form next : Prenex} (baseContext : BaseContext free bound)
    (sound : ∀ {context : List TypeExpr}, BaseContext free context → ∀ {process : Pattern},
      HasType language free context process (.base block.proc) →
        HasType language free context (canonical process) (.base block.proc) ∧
          ProcEquiv language block.toBlock free context process (canonical process))
    (members : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components)
    (absorbed : absorbOnce block canonical form = some next) :
    Members language block.toBlock free (List.replicate next.count (TypeExpr.base block.name) ++ bound)
        next.components ∧
      ProcEquiv language block.toBlock free bound (Prenex.toPattern block.toBlock form)
        (Prenex.toPattern block.toBlock next) := by
  obtain ⟨count, components⟩ := form
  unfold absorbOnce at absorbed
  obtain ⟨position, positionIn, found⟩ := List.exists_of_findSome?_eq_some absorbed
  have inside : position < components.length := List.mem_range.mp positionIn
  simp only [List.getElem?_eq_getElem inside] at found
  split at found
  swap
  · cases found
  rename_i label argument isAt
  have componentIs : components[position] = .apply label [argument] := Option.some.inj isAt
  split_ifs at found with isReplicate
  subst isReplicate
  obtain ⟨group, groupFound, rfl⟩ := Option.map_eq_some_iff.mp found
  set replicated : Pattern := .apply block.replicate [argument] with replicatedIs
  set allowed := (List.range count).filter fun index => !mentions index replicated with allowedIs
  set candidates := groupsThrough allowed count (components.eraseIdx position) with candidatesIs
  have groupMember := List.mem_of_find?_eq_some groupFound
  have copyFound := List.find?_some groupFound
  obtain ⟨partition, permuted⟩ := groupsThrough_partition allowed count (components.eraseIdx position)
  have nodup := partition.nodup group groupMember
  have insideGroup := partition.inside group groupMember
  set kept := (candidates.erase group).flatMap Group.components ++ [replicated] with keptIs
  have split : components.Perm (group.components ++ kept) := by
    have around : (replicated :: components.eraseIdx position).Perm components := by
      rw [← componentIs]
      exact List.getElem_cons_eraseIdx_perm inside
    have regroup : (components.eraseIdx position).Perm
        (group.components ++ (candidates.erase group).flatMap Group.components) :=
      permuted.symm.trans (by simpa using (List.perm_cons_erase groupMember).flatMap_right Group.components)
    have moved := (List.perm_append_singleton replicated
      (group.components ++ (candidates.erase group).flatMap Group.components)).symm
    rw [keptIs, ← List.append_assoc]
    exact around.symm.trans ((regroup.cons replicated).trans moved)
  have apart : ∀ component ∈ kept, ∀ index ∈ group.restrictions, ¬ FreeIn index component := by
    intro component member index listed freeHere
    have permitted := partition.allowedOnly group groupMember index listed
    rcases List.mem_append.mp member with inGroups | inReplicated
    · obtain ⟨other, otherMember, componentIn⟩ := List.mem_flatMap.mp inGroups
      have otherIn := List.mem_of_mem_erase otherMember
      have used := partition.uses other otherIn component componentIn index permitted freeHere
        (insideGroup index listed)
      by_cases same : other = group
      · subst same
        exact pairwise_self_of_mem_erase partition.disjoint otherMember index listed listed
      · exact partition.disjoint.forall groupMember otherIn (Ne.symm same) index listed used
    · rw [List.mem_singleton] at inReplicated
      subst inReplicated
      have unmentioned := (List.mem_filter.mp permitted).2
      simp only [Bool.not_eq_true'] at unmentioned
      rw [(mentions_iff _ index).mpr freeHere] at unmentioned
      exact Bool.noConfusion unmentioned
  have blockMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (group.components ++ kept) := fun element member => members element (split.symm.subset member)
  obtain ⟨narrowMembers, narrowEquivalent⟩ := narrow_equivalent (block := block.toBlock) nodup insideGroup
    (part := group.components) (rest := kept) blockMembers apart
  have tested := copyFound
  simp only [Bool.and_eq_true, beq_iff_eq] at tested
  have same := tested.1.1.1
  set others := outsideOf count group.restrictions with othersIs
  set renamed := rename (Prenex.groupIndex count others) argument with renamedIs
  have keptMembers : Members language block.toBlock free
      (List.replicate others.length (TypeExpr.base block.name) ++ bound)
      (kept.map (rename (Prenex.groupIndex count others))) := narrowMembers.tail
  have bangIn : .apply block.replicate [renamed] ∈ kept.map (rename (Prenex.groupIndex count others)) :=
    List.mem_map.mpr ⟨replicated, List.mem_append_right _ (List.mem_singleton_self _),
      by simp [replicatedIs, renamedIs, rename_apply]⟩
  have copyTyped := narrowMembers _ List.mem_cons_self
  have renamedTyped := replicate_argument_typed (keptMembers _ bangIn)
  have copyEquivalent : ProcEquiv language block.toBlock free
      (List.replicate others.length (TypeExpr.base block.name) ++ bound)
      (copyOf block.toBlock count ⟨group.restrictions, group.components⟩) renamed := by
    have narrowContext := baseContext.replicate others.length block.name
    have first := (sound narrowContext copyTyped).2
    have second := (sound narrowContext renamedTyped).2
    have eta : (⟨group.restrictions, group.components⟩ : Group) = group := rfl
    rw [eta] at first ⊢
    rw [same] at first
    exact .trans _ _ _ first (.symm _ _ second)
  have inner : ProcEquiv language block.toBlock free (List.replicate others.length (TypeExpr.base block.name) ++ bound)
      (Prenex.body block.toBlock (copyOf block.toBlock count ⟨group.restrictions, group.components⟩ ::
        kept.map (rename (Prenex.groupIndex count others))))
      (Prenex.body block.toBlock (kept.map (rename (Prenex.groupIndex count others)))) := by
    have toBag := bag_body_equivalent (block := block.toBlock) narrowMembers
    have swapped := bag_fill (before := []) (after := kept.map (rename (Prenex.groupIndex count others)))
      (rest := none) Members.nil keptMembers copyEquivalent
    simp only [List.nil_append] at swapped
    have absorbedHere := unfold_absorb_equivalent renamedTyped keptMembers bangIn
    have fromBag := bag_body_equivalent (block := block.toBlock) keptMembers
    exact .trans _ _ _ (.symm _ _ toBag) (.trans _ _ _ swapped (.trans _ _ _ absorbedHere fromBag))
  have outer := restricts_congr (block := block.toBlock) others.length inner
  have reordered := restricts_congr (block := block.toBlock) count (body_perm_equivalent members split)
  have keptCount : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      kept := fun element member => members element (split.symm.subset (List.mem_append_right _ member))
  obtain ⟨-, dropped⟩ := drop_unused_equivalent nodup insideGroup keptCount apart
  exact ⟨keptCount, .trans _ _ _ reordered (.trans _ _ _ narrowEquivalent (.trans _ _ _ outer
    (.symm _ _ dropped)))⟩

/-- **Absorption in rounds is sound.** -/
theorem absorbRounds_sound {free : FreeTypeContext} {bound : List TypeExpr} {canonical : Pattern → Pattern}
    (baseContext : BaseContext free bound)
    (sound : ∀ {context : List TypeExpr}, BaseContext free context → ∀ {process : Pattern},
      HasType language free context process (.base block.proc) →
        HasType language free context (canonical process) (.base block.proc) ∧
          ProcEquiv language block.toBlock free context process (canonical process)) :
    ∀ (rounds : Nat) {form : Prenex},
      Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
        form.components →
      Members language block.toBlock free
          (List.replicate (absorbRounds block canonical rounds form).count (TypeExpr.base block.name) ++ bound)
          (absorbRounds block canonical rounds form).components ∧
        ProcEquiv language block.toBlock free bound (Prenex.toPattern block.toBlock form)
          (Prenex.toPattern block.toBlock (absorbRounds block canonical rounds form))
  | 0, form, members => ⟨members, .refl _⟩
  | rounds + 1, form, members => by
      simp only [absorbRounds]
      split
      · exact ⟨members, .refl _⟩
      · rename_i next absorbed
        obtain ⟨nextMembers, step⟩ := absorbOnce_sound baseContext sound members absorbed
        obtain ⟨finalMembers, rest⟩ := absorbRounds_sound baseContext sound rounds nextMembers
        exact ⟨finalMembers, .trans _ _ _ step rest⟩

/-- **Absorption is sound**, when the canonical form it compares by is. -/
theorem absorb_sound {free : FreeTypeContext} {bound : List TypeExpr} {canonical : Pattern → Pattern}
    {form : Prenex} (baseContext : BaseContext free bound)
    (sound : ∀ {context : List TypeExpr}, BaseContext free context → ∀ {process : Pattern},
      HasType language free context process (.base block.proc) →
        HasType language free context (canonical process) (.base block.proc) ∧
          ProcEquiv language block.toBlock free context process (canonical process))
    (members : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components) :
    Members language block.toBlock free
        (List.replicate (absorb block canonical form).count (TypeExpr.base block.name) ++ bound)
        (absorb block canonical form).components ∧
      ProcEquiv language block.toBlock free bound (Prenex.toPattern block.toBlock form)
        (Prenex.toPattern block.toBlock (absorb block canonical form)) := by
  obtain ⟨roundsMembers, rounds⟩ := absorbRounds_sound baseContext sound form.components.length members
  obtain ⟨prunedMembers, pruned⟩ := prune_sound roundsMembers
  exact ⟨prunedMembers, .trans _ _ _ rounds pruned⟩


/-! ## One of each replicated component -/

omit laws in
/-- A replicated component is a replication. -/
theorem eq_of_isReplicated {component : Pattern} (replicated : isReplicated block component = true) :
    ∃ argument, component = .apply block.replicate [argument] := by
  match component, replicated with
  | .apply label [argument], replicated =>
      simp only [isReplicated, beq_iff_eq] at replicated
      exact ⟨argument, by rw [replicated]⟩

/-- **A replicated component beside a copy of itself is one**: `{!P | rest} ≡ rest` when `!P` occurs in `rest`. -/
theorem idempotent_absorb_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {component : Pattern}
    {rest : List Pattern} (replicated : isReplicated block component = true)
    (componentTyped : HasType language free bound component (.base block.proc))
    (restMembers : Members language block.toBlock free bound rest) (again : component ∈ rest) :
    ProcEquiv language block.toBlock free bound (.collection .hashBag (component :: rest) none)
      (.collection .hashBag rest none) := by
  obtain ⟨argument, rfl⟩ := eq_of_isReplicated replicated
  have argumentTyped := replicate_argument_typed componentTyped
  have permuted : rest.Perm (.apply block.replicate [argument] :: rest.erase (.apply block.replicate [argument])) :=
    List.perm_cons_erase again
  set others := rest.erase (.apply block.replicate [argument])
  have othersMembers : Members language block.toBlock free bound others :=
    fun element member => restMembers element (permuted.symm.subset (List.mem_cons_of_mem _ member))
  have pairMembers : Members language block.toBlock free bound
      [.apply block.replicate [argument], .apply block.replicate [argument]] :=
    Members.cons componentTyped (Members.cons componentTyped Members.nil)
  have reordered := bag_perm_equivalent (Members.cons componentTyped restMembers) (permuted.cons _)
  have paired := bag_pair_equivalent pairMembers othersMembers
  have consed := bag_cons_equivalent (bag_typed (block := block.toBlock) (rest := none) pairMembers) othersMembers
  have merged := bag_fill (before := []) (after := others) (rest := none) Members.nil othersMembers
    (replicate_idempotent_equivalent argumentTyped)
  simp only [List.nil_append] at merged
  have back := bag_perm_equivalent (Members.cons componentTyped othersMembers) permuted.symm
  simp only [List.cons_append, List.nil_append] at paired
  exact .trans _ _ _ reordered (.trans _ _ _ (.symm _ _ paired) (.trans _ _ _ consed (.trans _ _ _ merged back)))

omit laws in
/-- Keeping one of each replicated component only drops components. -/
theorem dedupReplicated_subset : ∀ (components : List Pattern), dedupReplicated block components ⊆ components
  | [] => by simp [dedupReplicated]
  | component :: rest => by
      intro element member
      unfold dedupReplicated at member
      split_ifs at member
      · exact List.mem_cons_of_mem _ (dedupReplicated_subset rest member)
      · rcases List.mem_cons.mp member with rfl | inRest
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (dedupReplicated_subset rest inRest)

/-- **Keeping one of each replicated component is sound.** -/
theorem dedup_sound {free : FreeTypeContext} {bound : List TypeExpr} :
    ∀ {components : List Pattern}, Members language block.toBlock free bound components →
      ProcEquiv language block.toBlock free bound (.collection .hashBag components none)
        (.collection .hashBag (dedupReplicated block components) none)
  | [], _ => by simp only [dedupReplicated]; exact .refl _
  | component :: rest, members => by
      have componentTyped := members component List.mem_cons_self
      have restMembers : Members language block.toBlock free bound rest := members.tail
      have inner := dedup_sound restMembers
      unfold dedupReplicated
      split_ifs with repeated
      · obtain ⟨replicated, again⟩ := Bool.and_eq_true_iff.mp repeated
        exact .trans _ _ _ (idempotent_absorb_equivalent replicated componentTyped restMembers
          (List.contains_iff_mem.mp again)) inner
      · have dedupMembers : Members language block.toBlock free bound (dedupReplicated block rest) :=
          fun element member => restMembers element (dedupReplicated_subset rest member)
        have regroup := bag_cons_equivalent (block := block.toBlock) componentTyped restMembers
        have filled := bag_fill (before := [component]) (after := []) (rest := none)
          (Members.cons componentTyped Members.nil) Members.nil inner
        simp only [List.cons_append, List.nil_append] at filled
        exact .trans _ _ _ (.symm _ _ regroup) (.trans _ _ _ filled
          (bag_cons_equivalent componentTyped dedupMembers))

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
