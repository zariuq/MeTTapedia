import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationExpose
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Reactions

/-!
# Steps through the canonical form, for calculi with replication

A step of a calculus with replication whose steps are reactions takes the parts of a redex from a block; in the
canonical form of the block they may be absorbed into copies of replicated components. They come back in an
unfolding of the canonical form within a bound read off the canonical form, where the redex reacts to a contractum
with the canonical form of the original contractum.

- **The ceiling**: every replicated component of a block is lower than some replicated component of its canonical
  form (`height_lt_ceilingOf`): absorption removes only copies of higher replicated components, and readings keep
  heights.
- **The canonical form of a block of restrictions** closes the canonical form of its body (`canonP_restricts`).
- **Unfoldings of typed blocks are typed** (`UnfoldsWithin.members`).
- **A step of a process is a reaction of an unfolding of its canonical form** within the arity times the ceiling
  (`replication_reaction`), so a step of the unfolding matches it (`replication_simulation`). The presentations of a
  state are its unfoldings within the presentation depth (`replicationPresentations`): the arity when every replicated
  component copies a molecule, a block without replicated components (`moleculeServers`), the arity times the ceiling
  otherwise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn liftIndex freeIn_apply freeIn_lambda freeIn_multiLambda
  freeIn_collection)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {block : ReplicationBlock}

/-! ## The ceiling of a canonical form -/

/-- **The ceiling of a block**: one past the greatest height of its components. -/
def ceilingOf (block : ReplicationBlock) (form : Prenex) : Nat :=
  (form.components.map (height block)).foldr max 0 + 1

/-- A member of a list of numbers is at most their greatest. -/
theorem le_foldr_max : ∀ {numbers : List Nat} {number : Nat}, number ∈ numbers → number ≤ numbers.foldr max 0
  | head :: tail, number, member => by
      rw [List.foldr_cons]
      rcases List.mem_cons.mp member with rfl | inTail
      · exact le_max_left _ _
      · exact (le_foldr_max inTail).trans (le_max_right _ _)

theorem height_lt_ceilingOf_of_mem {form : Prenex} {component : Pattern} (member : component ∈ form.components) :
    height block component < ceilingOf block form := by
  unfold ceilingOf
  have := le_foldr_max (List.mem_map_of_mem (f := height block) member)
  omega

section Ceiling

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict)

include multisetFresh fresh restrictFresh in
/-- **Reading a replicated component again keeps its height**: its argument is read canonically. -/
theorem height_recanon {argument : Pattern} :
    height block (recanon block (.apply block.replicate [argument])) =
      height block (.apply block.replicate [argument]) := by
  unfold height
  rw [recanon_apply_other (Ne.symm restrictFresh |>.symm) multisetFresh]
  simp only [List.map_cons, List.map_nil, argumentOf?]
  rw [canonArgument_canonicalOf, canonicalOf_canonicalOf fresh restrictFresh]

include multisetFresh fresh restrictFresh

/-- **Every replicated component of a block is below the ceiling of its canonical form**: a replicated component of a
copy group is lower than the one it copies, the components absorption keeps are read with their heights, and one of
each replicated component is kept. -/
theorem height_lt_ceilingOf {form : Prenex} (atomic : form.Atomic block.toBlock) :
    ∀ component ∈ form.components, isReplicated block component = true →
      height block component < ceilingOf block (normal block form) := by
  classical
  obtain ⟨-, blind⟩ := lawful_all fresh restrictFresh atomic
  obtain ⟨final, finalNodup, absorbs, absorbedIs⟩ := absorb_places blind
  set value := placeValue block form.components with valueIs
  -- every replicated live component is at most a replicated kept one
  have kept : ∀ {live rest : Finset Nat}, (blockSystem block form).Absorbs live rest →
      ∀ place ∈ live, isReplicated block (value place) = true →
        ∃ place' ∈ rest, isReplicated block (value place') = true ∧ height block (value place) ≤ height block (value place') := by
    intro live rest absorbs'
    induction absorbs' with
    | done =>
        intro place member replicated
        exact ⟨place, member, replicated, le_refl _⟩
    | @step live final' p copied isCopy _ recurse =>
        intro place member replicated
        by_cases inCopied : place ∈ copied
        · have test : CopyTest block (canonicalOf block) form.count (value p)
              (asGroup (allowedFor form.count (value p)) form.count value (copied.sort (· ≤ ·))) := isCopy.isCopy
          obtain ⟨-, -, smaller, -⟩ := test
          have lower := smaller (value place) (List.mem_map_of_mem ((Finset.mem_sort _).mpr inCopied)) replicated
          have pNotCopied : p ∉ copied := fun inside => (Finset.mem_erase.mp (isCopy.isGroup.subset inside)).1 rfl
          obtain ⟨place', inRest, replicated', higher⟩ := recurse p
            (Finset.mem_sdiff.mpr ⟨isCopy.isLive, pNotCopied⟩) isCopy.isReplicated
          refine ⟨place', inRest, replicated', ?_⟩
          unfold height
          exact (le_of_lt lower).trans higher
        · exact recurse place (Finset.mem_sdiff.mpr ⟨member, inCopied⟩) replicated
  -- the kept components are read in the canonical form, with their heights
  have read : ∀ place ∈ final, isReplicated block (value place) = true →
      height block (value place) < ceilingOf block (normal block form) := by
    intro place inFinal replicated
    have inside : place < form.components.length := by
      have := absorbs_subset absorbs (List.mem_toFinset.mpr inFinal)
      simpa [places] using this
    set restricted : Prenex := ⟨form.count, final.map value⟩ with restrictedIs
    obtain ⟨order, inOrders, leastIs⟩ := least_reading_mem (block := block) restricted.prune
    have isOrder : IsOrder restricted.prune.count order := readingOrders_isOrder inOrders
    have normalIs := normal_eq_reading (block := block) form
    rw [absorbedIs] at normalIs
    -- the component, renamed into the pruned block and read
    set used := usedOf restricted with usedIs
    set relabel := Prenex.permute restricted.prune.count order ∘ Prenex.groupIndex form.count used with relabelIs
    have inReading : recanon block (rename relabel (value place)) ∈ (normal block form).components := by
      rw [normalIs]
      simp only
      rw [leastIs]
      refine mem_dedupReplicated.mpr ((List.perm_insertionSort _ _).symm.subset ?_)
      rw [prune_eq]
      simp only [List.map_map]
      refine List.mem_map.mpr ⟨value place, List.mem_map_of_mem inFinal, ?_⟩
      simp only [Function.comp_apply, rename_comp, relabelIs]
      rfl
    have injectiveOn : ∀ first second, FreeIn first (value place) → FreeIn second (value place) →
        relabel first = relabel second → first = second := by
      intro first second firstFree secondFree same
      have usedOf_mem : ∀ index, FreeIn index (value place) → index < form.count → index ∈ used := by
        intro index free below
        refine List.mem_filter.mpr ⟨List.mem_range.mpr below, List.any_eq_true.mpr ⟨value place,
          List.mem_map_of_mem inFinal, (mentions_iff _ _).mpr free⟩⟩
      have countIs : restricted.prune.count = used.length := rfl
      have relabelBelow : ∀ index, FreeIn index (value place) → index < form.count →
          relabel index = Prenex.permute used.length order (used.idxOf index) := by
        intro index _ below
        rw [relabelIs, Function.comp_apply, groupIndex_below below, countIs]
      have relabelAbove : ∀ index, form.count ≤ index → relabel index = index - form.count + used.length := by
        intro index above
        rw [relabelIs, Function.comp_apply, groupIndex_above above, countIs, Prenex.permute, if_neg (by omega)]
      rw [countIs] at isOrder
      by_cases firstBelow : first < form.count <;> by_cases secondBelow : second < form.count
      · rw [relabelBelow first firstFree firstBelow, relabelBelow second secondFree secondBelow] at same
        have back := congrFun (permute_inverse isOrder) (used.idxOf first)
        have back' := congrFun (permute_inverse isOrder) (used.idxOf second)
        simp only [Function.comp, id] at back back'
        have positions : used.idxOf first = used.idxOf second := by rw [← back, ← back', same]
        exact (List.idxOf_inj (usedOf_mem first firstFree firstBelow)).mp positions
      · rw [relabelBelow first firstFree firstBelow, relabelAbove second (by omega)] at same
        have := permute_lt isOrder (List.idxOf_lt_length_of_mem (usedOf_mem first firstFree firstBelow))
        omega
      · rw [relabelAbove first (by omega), relabelBelow second secondFree secondBelow] at same
        have := permute_lt isOrder (List.idxOf_lt_length_of_mem (usedOf_mem second secondFree secondBelow))
        omega
      · rw [relabelAbove first (by omega), relabelAbove second (by omega)] at same
        omega
    obtain ⟨argument, valueIs'⟩ := replicated_shape replicated
    have heightRead : height block (recanon block (rename relabel (value place))) = height block (value place) := by
      rw [valueIs', rename_apply, List.map_singleton, height_recanon multisetFresh fresh restrictFresh,
        ← List.map_singleton, ← rename_apply, ← valueIs']
      exact height_rename_on fresh restrictFresh injectiveOn
    rw [← heightRead]
    exact height_lt_ceilingOf_of_mem inReading
  intro component member replicated
  obtain ⟨place, inside, rfl⟩ := List.getElem_of_mem member
  have valueAt : value place = form.components[place] := List.getD_eq_getElem _ _ inside
  rw [← valueAt] at replicated ⊢
  obtain ⟨place', inFinal, replicated', higher⟩ := kept absorbs place
    (List.mem_toFinset.mpr (by simpa [places] using inside)) replicated
  exact lt_of_le_of_lt higher (read place' (List.mem_toFinset.mp inFinal) replicated')

end Ceiling

/-! ## The canonical form of a block of restrictions -/

section Restricts

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **Restrictions around a process close its canonical block.** -/
theorem canonP_restricts {body : Pattern} (object : isObjectPattern body = true)
    (binds : restrictionsBind block.toBlock body = true) : ∀ count : Nat,
    canonP block (Prenex.restricts block.toBlock count body) =
      normal block ⟨(canonP block body).count + count, (canonP block body).components⟩
  | 0 => by
      show canonP block body = normal block ⟨(canonP block body).count + 0, (canonP block body).components⟩
      rw [Nat.add_zero]
      exact (canonFacts fresh restrictFresh object binds).fixed.symm
  | count + 1 => by
      have atomic : (Prenex.mk ((canonP block body).count + count) (canonP block body).components).Atomic
          block.toBlock := (canonFacts fresh restrictFresh object binds).atomic
      rw [Prenex.restricts_succ, canonP_restrict, canonP_restricts object binds count,
        normal_close_normal fresh restrictFresh atomic, ← normal_succ fresh restrictFresh atomic]
      rfl

/-- **The canonical form of restrictions over a bag of parts and other processes** is that of one block: the
parts read canonically, past the other processes' restrictions, beside their components. -/
theorem canonP_restricts_bag {parts rest : List Pattern} (count : Nat)
    (partsObject : ∀ part ∈ parts, isObjectPattern part = true)
    (restObject : ∀ other ∈ rest, isObjectPattern other = true)
    (partsBind : ∀ part ∈ parts, restrictionsBind block.toBlock part = true)
    (restBind : ∀ other ∈ rest, restrictionsBind block.toBlock other = true)
    (partsAtoms : ∀ part ∈ parts, canonP block part = Prenex.atom (canonR block part)) :
    canonP block (Prenex.restricts block.toBlock count (.collection .hashBag (parts ++ rest) none)) =
      normal block ⟨((rest.map (canonP block)).foldr Prenex.par Prenex.nil).count + count,
        (parts.map (canonR block)).map (liftBVars 0 ((rest.map (canonP block)).foldr Prenex.par Prenex.nil).count) ++
          ((rest.map (canonP block)).foldr Prenex.par Prenex.nil).components⟩ := by
  have bagObject : isObjectPattern (.collection .hashBag (parts ++ rest) none) = true := by
    rw [isObject_bag]
    intro element member
    rcases List.mem_append.mp member with inParts | inRest
    · exact partsObject element inParts
    · exact restObject element inRest
  have bagBinds : restrictionsBind block.toBlock (.collection .hashBag (parts ++ rest) none) = true := by
    rw [restrictionsBind_collection, List.all_eq_true]
    intro element member
    rcases List.mem_append.mp member with inParts | inRest
    · exact partsBind element inParts
    · exact restBind element inRest
  rw [canonP_restricts fresh restrictFresh bagObject bagBinds, canonP_bag, canonsP_eq_map, List.map_append,
    foldr_par_append]
  have partsMapped : parts.map (canonP block) = (parts.map (canonR block)).map Prenex.atom := by
    rw [List.map_map]
    exact List.map_congr_left fun part member => partsAtoms part member
  rw [partsMapped, foldr_par_atoms]
  set restForm := (rest.map (canonP block)).foldr Prenex.par Prenex.nil with restFormIs
  have restAtomic : restForm.Atomic block.toBlock :=
    foldr_par_atomic _ fun form member => by
      obtain ⟨other, inRest, rfl⟩ := List.mem_map.mp member
      exact (canonFacts fresh restrictFresh (restObject other inRest) (restBind other inRest)).atomic
  have partsAtomic : (Prenex.mk 0 (parts.map (canonR block))).Atomic block.toBlock := by
    intro component member
    obtain ⟨part, inParts, rfl⟩ := List.mem_map.mp member
    have facts := (canonFacts fresh restrictFresh (partsObject part inParts) (partsBind part inParts)).atomic
    rw [partsAtoms part inParts] at facts
    exact facts _ (List.mem_singleton_self _)
  have combinedAtomic := par_atomic partsAtomic restAtomic
  rw [← normal_add_normal fresh restrictFresh combinedAtomic]
  simp only [Prenex.par, Nat.zero_add]
  congr 3
  conv_rhs => rw [← List.map_id restForm.components]
  exact List.map_congr_left fun component _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero _ _

end Restricts

/-! ## Canonical forms of object terms are object terms -/

/-- A block of object components reads back as an object term. -/
theorem isObject_toPattern {base : Block} {form : Prenex}
    (objects : ∀ component ∈ form.components, isObjectPattern component = true) :
    isObjectPattern (Prenex.toPattern base form) = true := by
  obtain ⟨count, components⟩ := form
  unfold Prenex.toPattern
  rw [isObject_restricts]
  match components, objects with
  | [], _ => rfl
  | [component], objects => exact objects component (List.mem_singleton_self _)
  | first :: second :: rest, objects =>
      exact isObject_bag.mpr objects

/-- **One absorption keeps only components of the block.** -/
theorem absorbOnce_components {canonical : Pattern → Pattern} {form next : Prenex}
    (found : absorbOnce block canonical form = some next) : ∀ component ∈ next.components, component ∈ form.components := by
  unfold absorbOnce at found
  obtain ⟨position, _, hit⟩ := List.exists_of_findSome?_eq_some found
  split at hit
  · rename_i label argument isAt
    split_ifs at hit with isReplicate
    obtain ⟨group, inCandidates, rfl⟩ := Option.map_eq_some_iff.mp hit
    intro component member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with inGroups | isReplicated'
    · have inAll : component ∈ (groupsThrough ((List.range form.count).filter fun index =>
          !mentions index (.apply label [argument])) form.count (form.components.eraseIdx position)).flatMap
            Group.components := by
        obtain ⟨other, inErased, inOther⟩ := List.mem_flatMap.mp inGroups
        exact List.mem_flatMap.mpr ⟨other, List.mem_of_mem_erase inErased, inOther⟩
      have inOthers := ((groupsThrough_partition _ _ _).2.subset inAll)
      exact List.mem_of_mem_eraseIdx inOthers
    · subst isReplicated'
      exact List.mem_of_getElem? isAt
  · cases hit

/-- Absorption in rounds keeps only components of the block. -/
theorem absorbRounds_components {canonical : Pattern → Pattern} : ∀ (rounds : Nat) (form : Prenex),
    ∀ component ∈ (absorbRounds block canonical rounds form).components, component ∈ form.components
  | 0, _ => fun _ member => member
  | rounds + 1, form => by
      intro component member
      simp only [absorbRounds] at member
      split at member
      · exact member
      · rename_i next found
        exact absorbOnce_components found component (absorbRounds_components rounds next component member)

/-- **Canonical forms within a fuel keep object terms object terms.** -/
theorem objects_canonicalWith : ∀ fuel : Nat,
    (∀ component, isObjectPattern component = true → isObjectPattern (recanonWith block fuel component) = true) ∧
    (∀ form : Prenex, (∀ component ∈ form.components, isObjectPattern component = true) →
      ∀ component ∈ (normalizeWith block fuel form).components, isObjectPattern component = true) ∧
    (∀ argument, isObjectPattern argument = true → isObjectPattern (recanonMultisetWith block fuel argument) = true)
  | 0 => ⟨fun component object => by simpa [recanonWith] using object,
      fun form objects => by simpa [normalizeWith] using objects,
      fun argument object => by simpa [recanonMultisetWith] using object⟩
  | fuel + 1 => by
      obtain ⟨recanonObject, normalObject, multisetObject⟩ := objects_canonicalWith fuel
      have blockObject : ∀ pattern, isObjectPattern pattern = true →
          isObjectPattern (Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern))) =
            true := fun pattern object =>
        isObject_toPattern (normalObject _ (objects_of_decompose (block := block.toBlock) object))
      refine ⟨fun component object => ?_, fun form objects => ?_, fun argument object => ?_⟩
      · cases component with
        | apply constructor arguments =>
            simp only [recanonWith]
            split_ifs with isRestrict isMultiset
            · exact object
            · simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true, List.mem_map] at object ⊢
              rintro _ ⟨argument, member, rfl⟩
              exact multisetObject argument (object argument member)
            · simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true, List.mem_map] at object ⊢
              rintro _ ⟨argument, member, rfl⟩
              have argumentObject := object argument member
              cases argument with
              | lambda binder body =>
                  simp only [canonArgument, isObjectPattern] at argumentObject ⊢
                  exact blockObject body argumentObject
              | bvar => rfl
              | fvar => rfl
              | subst => simp [isObjectPattern] at argumentObject
              | apply => exact blockObject _ argumentObject
              | multiLambda => exact blockObject _ argumentObject
              | collection => exact blockObject _ argumentObject
        | lambda binder body =>
            simp only [recanonWith, isObjectPattern] at object ⊢
            exact blockObject body object
        | multiLambda arity binders body =>
            simp only [recanonWith, isObjectPattern] at object ⊢
            exact blockObject body object
        | collection kind elements rest =>
            simp only [recanonWith, isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true,
              List.mem_map] at object ⊢
            refine ⟨object.1, ?_⟩
            rintro _ ⟨element, member, rfl⟩
            exact blockObject element (object.2 element member)
        | bvar => exact object
        | fvar => exact object
        | subst => exact object
      · intro component member
        simp only [normalizeWith] at member
        set absorbed := absorb block (fun pattern =>
          Prenex.toPattern block.toBlock (normalizeWith block fuel (decompose block.toBlock pattern))) form
          with absorbedIs
        have readingsNonempty : ((readingOrders block absorbed).map fun order =>
            dedupReplicated block (sortComponents (absorbed.components.map fun component =>
              recanonWith block fuel (rename (Prenex.permute absorbed.count order) component)))) ≠ [] := by
          simpa using readingOrders_ne_nil (block := block) absorbed
        obtain ⟨order, _, leastIs⟩ := List.mem_map.mp (least_mem readingsNonempty)
        rw [← leastIs] at member
        have inSorted := (List.perm_insertionSort _ _).subset (mem_dedupReplicated.mp member)
        obtain ⟨original, inAbsorbed, rfl⟩ := List.mem_map.mp inSorted
        apply recanonObject
        rw [isObjectPattern_rename]
        have inPruned : original ∈ (absorbRounds block _ form.components.length form).prune.components := inAbsorbed
        rw [prune_eq] at inPruned
        obtain ⟨kept, inKept, rfl⟩ := List.mem_map.mp inPruned
        rw [isObjectPattern_rename]
        exact objects kept (absorbRounds_components _ _ kept inKept)
      · cases argument with
        | collection kind elements rest =>
            cases rest with
            | some rest => simp [isObjectPattern] at object
            | none =>
                simp only [recanonMultisetWith, multisetOf]
                split_ifs
                · exact isObject_bag.mpr (normalObject _ (objects_of_decompose (block := block.toBlock) object))
                · exact isObject_bag.mpr fun element member => by
                    rw [List.mem_singleton] at member
                    subst member
                    exact blockObject _ object
        | subst => simp [isObjectPattern] at object
        | _ =>
            simp only [recanonMultisetWith, multisetOf]
            split_ifs
            · exact isObject_bag.mpr (normalObject _ (objects_of_decompose (block := block.toBlock) object))
            · exact isObject_bag.mpr fun element member => by
                rw [List.mem_singleton] at member
                subst member
                exact blockObject _ object

/-- **Reading a component again keeps object terms object terms.** -/
theorem isObject_recanon {component : Pattern} (object : isObjectPattern component = true) :
    isObjectPattern (recanon block component) = true :=
  (objects_canonicalWith _).1 component object

/-- **The canonical form of a block of object terms is a block of object terms.** -/
theorem normal_objects {form : Prenex} (objects : ∀ component ∈ form.components, isObjectPattern component = true) :
    ∀ component ∈ (normal block form).components, isObjectPattern component = true :=
  (objects_canonicalWith _).2.1 form objects

/-- **Unfoldings of a block of object terms are blocks of object terms.** -/
theorem UnfoldsWithin.objects {depth : Nat} {form unfolded : Prenex} (unfolds : UnfoldsWithin block depth form unfolded) :
    (∀ component ∈ form.components, isObjectPattern component = true) →
      ∀ component ∈ unfolded.components, isObjectPattern component = true := by
  induction unfolds with
  | refl => exact id
  | @step depth form next argument member _ recurse =>
      intro objects
      apply recurse
      intro component inUnfolded
      simp only [Prenex.unfoldWith, List.mem_append, List.mem_map] at inUnfolded
      rcases inUnfolded with ⟨original, inForm, rfl⟩ | inCopy
      · rw [liftBVars_eq_rename, isObjectPattern_rename]
        exact objects original inForm
      · have replicatedObject := objects _ member
        simp only [isObjectPattern, isObjectPatternList, Bool.and_true] at replicatedObject
        exact normal_objects (objects_of_decompose (block := block.toBlock) replicatedObject) component inCopy

/-! ## Canonical forms keep the free names -/

theorem freePast_atom (component : Pattern) (index : Nat) :
    (Prenex.atom component).FreePast index ↔ FreeIn index component := by
  simp [Prenex.FreePast, Prenex.atom]

theorem freePast_nil (index : Nat) : ¬ Prenex.nil.FreePast index := by
  simp [Prenex.FreePast, Prenex.nil]

theorem freePast_foldr_par (index : Nat) : ∀ forms : List Prenex,
    (forms.foldr Prenex.par Prenex.nil).FreePast index ↔ ∃ form ∈ forms, form.FreePast index
  | [] => by simp [freePast_nil]
  | form :: forms => by
      rw [List.foldr_cons, freePast_par, freePast_foldr_par index forms]
      simp

/-- **A molecule uses past its restrictions the names its components use past the block's.** -/
theorem freePast_molecule {count : Nat} {group : Group}
    (uses : ∀ component ∈ group.components, ∀ index, FreeIn index component → index < count →
      index ∈ group.restrictions) (index : Nat) :
    (Prenex.molecule count group).FreePast index ↔ ∃ component ∈ group.components, FreeIn (index + count) component := by
  simp only [Prenex.FreePast, Prenex.molecule, List.mem_map]
  constructor
  · rintro ⟨_, ⟨component, member, rfl⟩, free⟩
    rw [freeIn_rename] at free
    obtain ⟨original, originalFree, maps⟩ := free
    refine ⟨component, member, ?_⟩
    by_cases below : original < count
    · have inRestrictions := uses component member original originalFree below
      rw [Prenex.groupIndex, if_pos below] at maps
      have := List.idxOf_lt_length_of_mem inRestrictions
      omega
    · rw [Prenex.groupIndex, if_neg below] at maps
      rwa [show index + count = original by omega]
  · rintro ⟨component, member, free⟩
    refine ⟨_, ⟨component, member, rfl⟩, ?_⟩
    rw [freeIn_rename]
    exact ⟨index + count, free, by rw [Prenex.groupIndex, if_neg (by omega)]; omega⟩

section FreeNames

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

theorem freeIn_moleculeEntry (form : Prenex) (index : Nat) :
    FreeIn index (moleculeEntry block form) ↔ form.FreePast index := by
  obtain ⟨count, components⟩ := form
  unfold moleculeEntry
  split
  · rename_i _ _ label argument countIs componentsIs
    simp only at countIs componentsIs
    subst countIs componentsIs
    split_ifs with isReplicate
    · simp only [Prenex.FreePast, List.mem_singleton, exists_eq_left, Nat.add_zero, freeIn_apply]
      rw [freeIn_canonicalOf fresh restrictFresh]
    · rw [freeIn_apply]
      simp only [List.mem_singleton, exists_eq_left]
      rw [freeIn_canonicalOf fresh restrictFresh, freeIn_toPattern]
      rfl
  · rw [freeIn_apply]
    simp only [List.mem_singleton, exists_eq_left]
    rw [freeIn_canonicalOf fresh restrictFresh, freeIn_toPattern]
    rfl

/-- **The replicated molecules of a block use past its restrictions the names the block uses.** -/
theorem freePast_replicatedOf (inner : Prenex) (index : Nat) :
    (Prenex.mk 0 (replicatedOf block (canonicalOf block) inner)).FreePast index ↔ inner.FreePast index := by
  obtain ⟨partition, permutation⟩ := groups_partition inner
  rw [replicatedOf_eq]
  simp only [Prenex.FreePast, Nat.add_zero, List.mem_map]
  constructor
  · rintro ⟨_, ⟨group, member, rfl⟩, free⟩
    rw [freeIn_moleculeEntry fresh restrictFresh, freePast_molecule (partition.uses group member)] at free
    obtain ⟨component, inGroup, componentFree⟩ := free
    exact ⟨component, permutation.subset (List.mem_flatMap.mpr ⟨group, member, inGroup⟩), componentFree⟩
  · rintro ⟨component, member, free⟩
    obtain ⟨group, inGroups, inGroup⟩ := List.mem_flatMap.mp (permutation.symm.subset member)
    refine ⟨_, ⟨group, inGroups, rfl⟩, ?_⟩
    rw [freeIn_moleculeEntry fresh restrictFresh, freePast_molecule (partition.uses group inGroups)]
    exact ⟨component, inGroup, free⟩

omit fresh restrictFresh in
theorem freeIn_argumentOf {label : String} {argument : Pattern} {form : Prenex} (index : Nat) :
    FreeIn index (argumentOf block label argument form) ↔ form.FreePast index := by
  unfold argumentOf
  split_ifs
  · split
    · exact freeIn_toPattern
    · exact freeIn_toPattern
    · rw [freeIn_multisetOf, freeIn_toPattern]
      rfl
  · exact freeIn_toPattern

/-- **The canonical block of an object pattern whose restrictions bind uses past its restrictions exactly the names
the pattern uses**, and so does the canonical block of an abstraction's body. -/
theorem freePast_canonP_and (pattern : Pattern) :
    (isObjectPattern pattern = true → restrictionsBind block.toBlock pattern = true →
      ∀ index, (canonP block pattern).FreePast index ↔ FreeIn index pattern) ∧
    ∀ binder body, pattern = .lambda binder body → isObjectPattern body = true →
      restrictionsBind block.toBlock body = true → ∀ index, (canonP block body).FreePast index ↔ FreeIn index body := by
  induction pattern using Pattern.inductionOn with
  | hbvar other =>
      exact ⟨fun _ _ index => by simp [canonP, freePast_atom], fun _ _ equal => by cases equal⟩
  | hfvar name =>
      exact ⟨fun _ _ index => by simp [canonP, freePast_atom], fun _ _ equal => by cases equal⟩
  | hsubst body replacement _ _ =>
      exact ⟨fun object _ => by simp [isObjectPattern] at object, fun _ _ equal => by cases equal⟩
  | hlambda binder body recurse =>
      refine ⟨fun object binds index => ?_, fun binder' body' equal => by cases equal; exact recurse.1⟩
      have bodyFree := recurse.1 (by simpa [isObjectPattern] using object) (by simpa [restrictionsBind] using binds)
      rw [canonP_lambda, freePast_atom, freeIn_lambda, freeIn_lambda, freeIn_toPattern]
      exact bodyFree (index + 1)
  | hmultiLambda arity binders body recurse =>
      refine ⟨fun object binds index => ?_, fun _ _ equal => by cases equal⟩
      have bodyFree := recurse.1 (by simpa [isObjectPattern] using object) (by simpa [restrictionsBind] using binds)
      have isAtom : canonP block (.multiLambda arity binders body) =
          Prenex.atom (.multiLambda arity binders (Prenex.toPattern block.toBlock (canonP block body))) := by
        simp [canonP]
      rw [isAtom, freePast_atom, freeIn_multiLambda, freeIn_multiLambda, freeIn_toPattern]
      exact bodyFree (index + arity)
  | hcollection kind elements rest recurse =>
      refine ⟨fun object binds index => ?_, fun _ _ equal => by cases equal⟩
      simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
      simp only [restrictionsBind, restrictionsBindList_eq_all, List.all_eq_true] at binds
      obtain ⟨closed, objects⟩ := object
      have elementsFree : ∀ element ∈ elements, ∀ index,
          (canonP block element).FreePast index ↔ FreeIn index element := fun element member =>
        (recurse element member).1 (objects element member) (binds element member)
      have elementsAtomic : ∀ element ∈ elements, (canonP block element).Atomic block.toBlock := fun element member =>
        (canonFacts fresh restrictFresh (objects element member) (binds element member)).atomic
      cases rest with
      | some name => simp at closed
      | none =>
          cases kind with
          | hashBag =>
              rw [canonP_bag, freePast_normal_all fresh restrictFresh (foldr_par_atomic _ fun form member => by
                  rw [canonsP_eq_map] at member
                  obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
                  exact elementsAtomic element inElements),
                freePast_foldr_par, freeIn_collection, canonsP_eq_map]
              simp only [List.mem_map]
              constructor
              · rintro ⟨_, ⟨element, member, rfl⟩, free⟩
                exact ⟨element, member, (elementsFree element member index).mp free⟩
              · rintro ⟨element, member, free⟩
                exact ⟨_, ⟨element, member, rfl⟩, (elementsFree element member index).mpr free⟩
          | hashSet | vec =>
              simp only [canonP, freePast_atom, freeIn_collection, canonsP_eq_map, List.map_map, List.mem_map,
                Function.comp_apply]
              constructor
              · rintro ⟨_, ⟨element, member, rfl⟩, free⟩
                rw [freeIn_toPattern] at free
                exact ⟨element, member, (elementsFree element member index).mp free⟩
              · rintro ⟨element, member, free⟩
                refine ⟨_, ⟨element, member, rfl⟩, ?_⟩
                rw [freeIn_toPattern]
                exact (elementsFree element member index).mpr free
  | happly label arguments recurse =>
      refine ⟨fun object binds index => ?_, fun _ _ equal => by cases equal⟩
      simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      simp only [restrictionsBind, restrictionsBindList_eq_all, Bool.and_eq_true, List.all_eq_true] at binds
      obtain ⟨bindsHere, bindsBelow⟩ := binds
      have argumentsFree : ∀ argument ∈ arguments, ∀ index,
          (canonP block argument).FreePast index ↔ FreeIn index argument := fun argument member =>
        (recurse argument member).1 (object argument member) (bindsBelow argument member)
      rcases arguments with _ | ⟨argument, _ | ⟨second, others⟩⟩
      · by_cases isUnit : label = block.unit
        · subst isUnit
          rw [canonP_unit]
          simp [freePast_nil, freeIn_apply]
        · have isAtom : canonP block (.apply label []) = Prenex.atom (.apply label []) := by simp [canonP, isUnit]
          rw [isAtom, freePast_atom]
      · by_cases isLambda : ∃ binder body, argument = .lambda binder body
        · obtain ⟨binder, body, rfl⟩ := isLambda
          have lambdaObject : isObjectPattern (.lambda binder body) = true := object _ List.mem_cons_self
          have bodyFree := (recurse _ List.mem_cons_self).2 binder body rfl
            (by simpa [isObjectPattern] using lambdaObject)
            (by simpa [restrictionsBind] using bindsBelow _ List.mem_cons_self)
          have bodyFacts := canonFacts fresh restrictFresh (by simpa [isObjectPattern] using lambdaObject)
            (by simpa [restrictionsBind] using bindsBelow _ List.mem_cons_self)
          by_cases isRestrict : label = block.restrict
          · subst isRestrict
            rw [canonP_restrict, freePast_normal_all fresh restrictFresh (close_atomic bodyFacts.atomic),
              freePast_close, bodyFree, freeIn_apply]
            simp [freeIn_lambda]
          · have isAtom : canonP block (.apply label [.lambda binder body]) =
                Prenex.atom (.apply label [argumentOf block label (.lambda binder body)
                  (Prenex.atom (.lambda binder (Prenex.toPattern block.toBlock (canonP block body))))]) := by
              simp [canonP, isRestrict]
            rw [isAtom, freePast_atom, freeIn_apply, freeIn_apply]
            simp only [List.mem_singleton, exists_eq_left]
            rw [freeIn_argumentOf, freePast_atom, freeIn_lambda, freeIn_lambda, freeIn_toPattern]
            exact bodyFree (index + 1)
        · push Not at isLambda
          have argumentFree := argumentsFree argument List.mem_cons_self
          have argumentFacts := canonFacts fresh restrictFresh (object argument List.mem_cons_self)
            (bindsBelow argument List.mem_cons_self)
          by_cases isReplicate : label = block.replicate
          · subst isReplicate
            rw [canonP_replicate isLambda, freePast_normal_all fresh restrictFresh (fun component member =>
                replicated_atomic fresh restrictFresh (replicatedOf_replicated component member)),
              freePast_replicatedOf fresh restrictFresh, argumentFree, freeIn_apply]
            simp
          by_cases empty : label ∈ block.emptyUnits ∧ canonP block argument = Prenex.nil
          · rw [canonP_empty empty.1 isReplicate isLambda empty.2, freeIn_apply]
            simp only [List.mem_singleton, exists_eq_left]
            rw [← argumentFree, empty.2]
          · have isAtom : canonP block (.apply label [argument]) =
                Prenex.atom (.apply label [argumentOf block label argument (canonP block argument)]) := by
              rw [canonP_apply (by simp) (fun binder body equal => by
                  simp only [List.cons.injEq, and_true] at equal
                  exact isLambda binder body equal.2)
                (fun other _ equal => isReplicate equal.1)
                (fun other _ equal listed nil => by
                  simp only [List.cons.injEq, and_true] at equal
                  subst equal
                  exact empty ⟨listed, nil⟩)]
              simp [canonsP]
            rw [isAtom, freePast_atom, freeIn_apply, freeIn_apply]
            simp only [List.mem_singleton, exists_eq_left]
            rw [freeIn_argumentOf, argumentFree]
      · have isAtom : canonP block (.apply label (argument :: second :: others)) =
            Prenex.atom (.apply label ((argument :: second :: others).map fun other =>
              argumentOf block label other (canonP block other))) := by
          rw [canonP_apply (by simp) (by simp) (by simp) (by simp), canonsP_eq_map,
            zipWith_map_self _ _ _ _ fun _ _ => rfl]
        rw [isAtom, freePast_atom, freeIn_apply, freeIn_apply]
        simp only [List.mem_map]
        constructor
        · rintro ⟨_, ⟨other, member, rfl⟩, free⟩
          rw [freeIn_argumentOf] at free
          exact ⟨other, member, (argumentsFree other member index).mp free⟩
        · rintro ⟨other, member, free⟩
          refine ⟨_, ⟨other, member, rfl⟩, ?_⟩
          rw [freeIn_argumentOf]
          exact (argumentsFree other member index).mpr free

/-- **The canonical form of an object term whose restrictions bind uses exactly its free names.** -/
theorem freeIn_canonR {pattern : Pattern} (object : isObjectPattern pattern = true)
    (binds : restrictionsBind block.toBlock pattern = true) (index : Nat) :
    FreeIn index (canonR block pattern) ↔ FreeIn index pattern := by
  unfold canonR
  rw [freeIn_toPattern]
  exact (freePast_canonP_and fresh restrictFresh pattern).1 object binds index

end FreeNames

/-- The canonical form of an object term is an object term. -/
theorem isObject_canonicalOf {pattern : Pattern} (object : isObjectPattern pattern = true) :
    isObjectPattern (canonicalOf block pattern) = true := by
  unfold canonicalOf
  exact isObject_toPattern (normal_objects (objects_of_decompose (block := block.toBlock) object))

/-- **The replicated entry of a block of object terms is an object term.** -/
theorem moleculeEntry_object {form : Prenex} (objects : ∀ component ∈ form.components, isObjectPattern component = true) :
    isObjectPattern (moleculeEntry block form) = true := by
  obtain ⟨count, components⟩ := form
  unfold moleculeEntry
  split
  · rename_i _ _ label argument countIs componentsIs
    simp only at countIs componentsIs
    subst componentsIs
    have entry := objects _ (List.mem_singleton_self _)
    simp only [isObjectPattern, isObjectPatternList, Bool.and_true] at entry
    split_ifs
    · simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
      exact isObject_canonicalOf entry
    · simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
      exact isObject_canonicalOf (isObject_toPattern objects)
  · simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
    exact isObject_canonicalOf (isObject_toPattern objects)

/-- **The replicated molecules of a block of object terms are object terms.** -/
theorem replicatedOf_objects {inner : Prenex} (objects : ∀ component ∈ inner.components, isObjectPattern component = true) :
    ∀ entry ∈ replicatedOf block (canonicalOf block) inner, isObjectPattern entry = true := by
  obtain ⟨-, permutation⟩ := groups_partition inner
  intro entry member
  rw [replicatedOf_eq] at member
  obtain ⟨group, inGroups, rfl⟩ := List.mem_map.mp member
  refine moleculeEntry_object fun component inMolecule => ?_
  simp only [Prenex.molecule, List.mem_map] at inMolecule
  obtain ⟨original, inGroup, rfl⟩ := inMolecule
  rw [isObjectPattern_rename]
  exact objects original (permutation.subset (List.mem_flatMap.mpr ⟨group, inGroups, inGroup⟩))

/-- An argument read from a block of object terms is an object term. -/
theorem argumentOf_object' {label : String} {argument : Pattern} {form : Prenex}
    (objects : ∀ component ∈ form.components, isObjectPattern component = true) :
    isObjectPattern (argumentOf block label argument form) = true := by
  unfold argumentOf
  split_ifs
  · split
    · exact isObject_toPattern objects
    · exact isObject_toPattern objects
    · unfold multisetOf
      split_ifs
      · exact isObject_bag.mpr objects
      · exact isObject_bag.mpr fun element member => by
          rw [List.mem_singleton] at member
          subst member
          exact isObject_toPattern objects
  · exact isObject_toPattern objects

theorem atom_objects {component : Pattern} (object : isObjectPattern component = true) :
    ∀ other ∈ (Prenex.atom component).components, isObjectPattern other = true := by
  intro other member
  simp only [Prenex.atom, List.mem_singleton] at member
  subst member
  exact object

/-- **The canonical block of an object pattern is a block of object terms**, and so is that of an abstraction's
body. -/
theorem objects_canonP_and (pattern : Pattern) :
    (isObjectPattern pattern = true → ∀ component ∈ (canonP block pattern).components, isObjectPattern component = true) ∧
    ∀ binder body, pattern = .lambda binder body → isObjectPattern body = true →
      ∀ component ∈ (canonP block body).components, isObjectPattern component = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar other => exact ⟨fun object => by simpa [canonP] using atom_objects object, fun _ _ equal => by cases equal⟩
  | hfvar name => exact ⟨fun object => by simpa [canonP] using atom_objects object, fun _ _ equal => by cases equal⟩
  | hsubst body replacement _ _ =>
      exact ⟨fun object => by simp [isObjectPattern] at object, fun _ _ equal => by cases equal⟩
  | hlambda binder body recurse =>
      refine ⟨fun object => ?_, fun binder' body' equal => by cases equal; exact recurse.1⟩
      have bodyObjects := recurse.1 (by simpa [isObjectPattern] using object)
      rw [canonP_lambda]
      refine atom_objects ?_
      simp only [isObjectPattern]
      exact isObject_toPattern bodyObjects
  | hmultiLambda arity binders body recurse =>
      refine ⟨fun object => ?_, fun _ _ equal => by cases equal⟩
      have bodyObjects := recurse.1 (by simpa [isObjectPattern] using object)
      have isAtom : canonP block (.multiLambda arity binders body) =
          Prenex.atom (.multiLambda arity binders (Prenex.toPattern block.toBlock (canonP block body))) := by
        simp [canonP]
      rw [isAtom]
      refine atom_objects ?_
      simp only [isObjectPattern]
      exact isObject_toPattern bodyObjects
  | hcollection kind elements rest recurse =>
      refine ⟨fun object => ?_, fun _ _ equal => by cases equal⟩
      simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
      obtain ⟨closed, objects⟩ := object
      have elementsObjects : ∀ element ∈ elements, ∀ component ∈ (canonP block element).components,
          isObjectPattern component = true := fun element member => (recurse element member).1 (objects element member)
      cases rest with
      | some name => simp at closed
      | none =>
          cases kind with
          | hashBag =>
              rw [canonP_bag]
              refine normal_objects ?_
              rw [canonsP_eq_map]
              suffices folded : ∀ forms : List Prenex, (∀ form ∈ forms, ∀ component ∈ form.components,
                  isObjectPattern component = true) →
                  ∀ component ∈ (forms.foldr Prenex.par Prenex.nil).components, isObjectPattern component = true by
                exact folded _ fun form member => by
                  obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
                  exact elementsObjects element inElements
              intro forms
              induction forms with
              | nil => intro _ component member; simp [Prenex.nil] at member
              | cons form forms recurseForms =>
                  intro formsObjects component member
                  rw [List.foldr_cons] at member
                  simp only [Prenex.par, List.mem_append, List.mem_map] at member
                  rcases member with ⟨original, inForm, rfl⟩ | ⟨original, inRest, rfl⟩
                  · rw [liftBVars_eq_rename, isObjectPattern_rename]
                    exact formsObjects form List.mem_cons_self original inForm
                  · rw [liftBVars_eq_rename, isObjectPattern_rename]
                    exact recurseForms (fun other member => formsObjects other (List.mem_cons_of_mem _ member))
                      original inRest
          | hashSet | vec =>
              simp only [canonP]
              refine atom_objects ?_
              simp only [isObjectPattern, Option.isNone_none, Bool.true_and, isObjectPatternList_eq_all,
                List.all_eq_true, List.mem_map]
              rintro _ ⟨form, member, rfl⟩
              rw [canonsP_eq_map] at member
              obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
              exact isObject_toPattern (elementsObjects element inElements)
  | happly label arguments recurse =>
      refine ⟨fun object => ?_, fun _ _ equal => by cases equal⟩
      simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      have argumentsObjects : ∀ argument ∈ arguments, ∀ component ∈ (canonP block argument).components,
          isObjectPattern component = true := fun argument member => (recurse argument member).1 (object argument member)
      rcases arguments with _ | ⟨argument, _ | ⟨second, others⟩⟩
      · by_cases isUnit : label = block.unit
        · subst isUnit
          rw [canonP_unit]
          intro component member
          simp [Prenex.nil] at member
        · have isAtom : canonP block (.apply label []) = Prenex.atom (.apply label []) := by simp [canonP, isUnit]
          rw [isAtom]
          exact atom_objects (by simp [isObjectPattern, isObjectPatternList])
      · by_cases isLambda : ∃ binder body, argument = .lambda binder body
        · obtain ⟨binder, body, rfl⟩ := isLambda
          have lambdaObject : isObjectPattern (.lambda binder body) = true := object _ List.mem_cons_self
          have bodyObjects := (recurse _ List.mem_cons_self).2 binder body rfl
            (by simpa [isObjectPattern] using lambdaObject)
          by_cases isRestrict : label = block.restrict
          · subst isRestrict
            rw [canonP_restrict]
            refine normal_objects ?_
            intro component member
            rw [Prenex.close] at member
            split_ifs at member
            · exact bodyObjects component member
            · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
              rw [isObjectPattern_rename]
              exact bodyObjects original inOriginal
          · have isAtom : canonP block (.apply label [.lambda binder body]) =
                Prenex.atom (.apply label [argumentOf block label (.lambda binder body)
                  (Prenex.atom (.lambda binder (Prenex.toPattern block.toBlock (canonP block body))))]) := by
              simp [canonP, isRestrict]
            rw [isAtom]
            refine atom_objects ?_
            simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
            refine argumentOf_object' (atom_objects ?_)
            simp only [isObjectPattern]
            exact isObject_toPattern bodyObjects
        · push Not at isLambda
          have argumentObjects := argumentsObjects argument List.mem_cons_self
          by_cases isReplicate : label = block.replicate
          · subst isReplicate
            rw [canonP_replicate isLambda]
            exact normal_objects (replicatedOf_objects argumentObjects)
          by_cases empty : label ∈ block.emptyUnits ∧ canonP block argument = Prenex.nil
          · rw [canonP_empty empty.1 isReplicate isLambda empty.2]
            intro component member
            simp [Prenex.nil] at member
          · have isAtom : canonP block (.apply label [argument]) =
                Prenex.atom (.apply label [argumentOf block label argument (canonP block argument)]) := by
              rw [canonP_apply (by simp) (fun binder body equal => by
                  simp only [List.cons.injEq, and_true] at equal
                  exact isLambda binder body equal.2)
                (fun other _ equal => isReplicate equal.1)
                (fun other _ equal listed nil => by
                  simp only [List.cons.injEq, and_true] at equal
                  subst equal
                  exact empty ⟨listed, nil⟩)]
              simp [canonsP]
            rw [isAtom]
            refine atom_objects ?_
            simp only [isObjectPattern, isObjectPatternList, Bool.and_true]
            exact argumentOf_object' argumentObjects
      · have isAtom : canonP block (.apply label (argument :: second :: others)) =
            Prenex.atom (.apply label ((argument :: second :: others).map fun other =>
              argumentOf block label other (canonP block other))) := by
          rw [canonP_apply (by simp) (by simp) (by simp) (by simp), canonsP_eq_map,
            zipWith_map_self _ _ _ _ fun _ _ => rfl]
        rw [isAtom]
        refine atom_objects ?_
        simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true, List.mem_map]
        rintro _ ⟨other, member, rfl⟩
        exact argumentOf_object' (argumentsObjects other member)

/-- **The canonical form of an object term is an object term.** -/
theorem isObject_canonR {pattern : Pattern} (object : isObjectPattern pattern = true) :
    isObjectPattern (canonR block pattern) = true :=
  isObject_toPattern ((objects_canonP_and pattern).1 object)

/-- **Blocks of object terms side by side are a block of object terms.** -/
theorem foldr_par_objects : ∀ forms : List Prenex,
    (∀ form ∈ forms, ∀ component ∈ form.components, isObjectPattern component = true) →
    ∀ component ∈ (forms.foldr Prenex.par Prenex.nil).components, isObjectPattern component = true
  | [], _ => fun _ member => by simp [Prenex.nil] at member
  | form :: forms, objects => by
      intro component member
      rw [List.foldr_cons] at member
      simp only [Prenex.par, List.mem_append, List.mem_map] at member
      rcases member with ⟨original, inForm, rfl⟩ | ⟨original, inRest, rfl⟩
      · rw [liftBVars_eq_rename, isObjectPattern_rename]
        exact objects form List.mem_cons_self original inForm
      · rw [liftBVars_eq_rename, isObjectPattern_rename]
        exact foldr_par_objects forms (fun other member => objects other (List.mem_cons_of_mem _ member)) original inRest

/-- A lookup in a frame of restrictions over a context, carried to another frame by a map that keeps restrictions
among restrictions and moves the context past them. -/
theorem frame_lookup {count count' : Nat} {bound : List TypeExpr} {name : TypeExpr} {index index' : Nat}
    (maps : (index < count → index' < count') ∧ (count ≤ index → index' = count' + (index - count))) {sort : TypeExpr}
    (lookup : (List.replicate count name ++ bound)[index]? = some sort) :
    (List.replicate count' name ++ bound)[index']? = some sort := by
  by_cases below : index < count
  · rw [List.getElem?_append_left (by simpa using below), List.getElem?_replicate, if_pos below] at lookup
    rw [List.getElem?_append_left (by simpa using maps.1 below), List.getElem?_replicate, if_pos (maps.1 below)]
    exact lookup
  · rw [List.getElem?_append_right (by simp; omega)] at lookup
    rw [maps.2 (by omega), List.getElem?_append_right (by simp)]
    simpa using lookup

/-! ## Typed unfoldings -/

section Typed

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

include laws in
/-- **Unfoldings of a typed block are typed**: the block's components past the copy's restrictions, and the copy's
canonical components. -/
theorem UnfoldsWithin.members {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {depth : Nat} {form unfolded : Prenex} (unfolds : UnfoldsWithin block depth form unfolded) :
    Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
        form.components →
      Members language block.toBlock free (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
        unfolded.components := by
  induction unfolds with
  | refl => exact id
  | @step depth form next argument member _ recurse =>
      intro members
      apply recurse
      have argumentTyped := replicate_argument_typed (members _ member)
      obtain ⟨decomposedMembers, -⟩ := decompose_sound (block := block.toBlock) argumentTyped
      obtain ⟨normalMembers, -⟩ := normal_sound (context.replicate form.count block.name) decomposedMembers
      intro element inUnfolded
      simp only [Prenex.unfoldWith, List.mem_append, List.mem_map] at inUnfolded
      show HasType language free (List.replicate ((normal block (decompose block.toBlock argument)).count +
        form.count) (TypeExpr.base block.name) ++ bound) element (TypeExpr.base block.proc)
      rw [List.replicate_add, List.append_assoc]
      rcases inUnfolded with ⟨original, inForm, rfl⟩ | inCopy
      · exact lift_members (block := block.toBlock) _ members _ (List.mem_map_of_mem inForm)
      · exact normalMembers element inCopy

end Typed

/-! ## Renaming the outside, composed and on free names -/

theorem renameOuter_comp (form : Prenex) (first second : Nat → Nat) :
    (form.renameOuter first).renameOuter second = form.renameOuter (second ∘ first) := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.renameOuter, List.map_map, Prenex.mk.injEq, true_and]
  refine List.map_congr_left fun component _ => ?_
  simp only [Function.comp_apply, rename_comp]
  congr 1
  funext index
  by_cases below : index < count
  · simp [liftIndex, below]
  · have notBelow : ¬ first (index - count) + count < count := by omega
    simp [liftIndex, below, notBelow]

theorem renameOuter_congr {form : Prenex} {first second : Nat → Nat}
    (agree : ∀ index, form.FreePast index → first index = second index) :
    form.renameOuter first = form.renameOuter second := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.renameOuter, Prenex.mk.injEq, true_and]
  refine List.map_congr_left fun component member => rename_congr component fun index free => ?_
  simp only [liftIndex]
  split_ifs with low
  · rfl
  · rw [agree (index - count) ⟨component, member, by rw [show index - count + count = index by omega]; exact free⟩]

theorem freePast_renameOuter (form : Prenex) (relabel : Nat → Nat) (index : Nat) :
    (form.renameOuter relabel).FreePast index ↔ ∃ original, form.FreePast original ∧ relabel original = index := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.FreePast, Prenex.renameOuter, List.mem_map]
  constructor
  · rintro ⟨_, ⟨component, member, rfl⟩, free⟩
    rw [freeIn_rename] at free
    obtain ⟨name, nameFree, maps⟩ := free
    simp only [liftIndex] at maps
    split_ifs at maps with low
    · omega
    · exact ⟨name - count, ⟨component, member, by rw [show name - count + count = name by omega]; exact nameFree⟩,
        by omega⟩
  · rintro ⟨original, ⟨component, member, free⟩, rfl⟩
    refine ⟨_, ⟨component, member, rfl⟩, ?_⟩
    rw [freeIn_rename]
    exact ⟨original + count, free, by simp [liftIndex]⟩

/-! ## Renamed results -/

section Results

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict)

include multisetFresh fresh restrictFresh

/-- **The canonical blocks of processes lifted past some restrictions and renamed outside read as the canonical
blocks of the processes renamed alike**, when the renamings agree on their free names. -/
theorem normal_results_renamed {results : List Pattern} {shift : Nat} {outer relabel : Nat → Nat}
    (objects : ∀ result ∈ results, isObjectPattern result = true)
    (binds : ∀ result ∈ results, restrictionsBind block.toBlock result = true)
    (injective : Function.Injective relabel)
    (agree : ∀ result ∈ results, ∀ index, FreeIn index result → relabel index = outer (index + shift))
    (outerInjective : ∀ first second, (∃ result ∈ results, FreeIn first result) →
      (∃ result ∈ results, FreeIn second result) → outer (first + shift) = outer (second + shift) → first = second) :
    normal block ((((results.map (liftBVars 0 shift)).map (canonP block)).foldr Prenex.par Prenex.nil).renameOuter outer) =
      normal block (((results.map (rename relabel)).map (canonP block)).foldr Prenex.par Prenex.nil) := by
  have shiftInjective : Function.Injective (shiftAbove 0 shift) := fun first second same => by
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at same
    omega
  have liftedObject : ∀ result ∈ results, isObjectPattern (liftBVars 0 shift result) = true := fun result member => by
    rw [liftBVars_eq_rename, isObjectPattern_rename]
    exact objects result member
  have liftedBinds : ∀ result ∈ results, restrictionsBind block.toBlock (liftBVars 0 shift result) = true :=
    fun result member => by
      rw [liftBVars_eq_rename, restrictionsBind_rename]
      exact binds result member
  have each : ∀ result ∈ results,
      normal block ((canonP block (liftBVars 0 shift result)).renameOuter outer) =
        canonP block (rename relabel result) := by
    intro result member
    have facts := canonFacts fresh restrictFresh (objects result member) (binds result member)
    have freeIff := (freePast_canonP_and fresh restrictFresh result).1 (objects result member) (binds result member)
    rw [liftBVars_eq_rename, canonP_rename multisetFresh fresh restrictFresh (objects result member)
      (binds result member) shiftInjective, canonP_rename multisetFresh fresh restrictFresh (objects result member)
      (binds result member) injective]
    rw [normal_renameOuter_normal_on fresh restrictFresh (renameOuter_atomic facts.atomic _), renameOuter_comp]
    · congr 1
      apply renameOuter_congr
      intro index past
      simp only [Function.comp_apply, shiftAbove, Nat.not_lt_zero, if_false]
      exact (agree result member index ((freeIff index).mp past)).symm
    · intro first second firstPast secondPast same
      rw [freePast_renameOuter] at firstPast secondPast
      obtain ⟨a, aPast, rfl⟩ := firstPast
      obtain ⟨b, bPast, rfl⟩ := secondPast
      simp only [shiftAbove, Nat.not_lt_zero, if_false] at same ⊢
      rw [outerInjective a b ⟨result, member, (freeIff a).mp aPast⟩ ⟨result, member, (freeIff b).mp bPast⟩ same]
  rw [foldr_par_renameOuter]
  set forms := ((results.map (liftBVars 0 shift)).map (canonP block)).map (Prenex.renameOuter outer) with formsIs
  have formsAtomic : ∀ form ∈ forms, form.Atomic block.toBlock := by
    intro form member
    simp only [formsIs, List.mem_map] at member
    obtain ⟨_, ⟨_, ⟨result, inResults, rfl⟩, rfl⟩, rfl⟩ := member
    exact renameOuter_atomic (canonFacts fresh restrictFresh (liftedObject result inResults)
      (liftedBinds result inResults)).atomic outer
  rw [← normal_foldr_normal fresh restrictFresh forms formsAtomic]
  congr 2
  simp only [formsIs, List.map_map]
  refine List.map_congr_left fun result member => ?_
  simp only [Function.comp_apply]
  exact each result member

end Results

/-! ## A block inside a block, as processes -/

section Inside

variable {language : LanguageDef} [laws : ReplicationLanguage language block]

open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)

include laws in
/-- **A block inside a block is the outer block's components beside the inner block's process**, under the outer
block's restrictions. -/
theorem unfoldWith_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {form copy : Prenex}
    (formMembers : Members language block.toBlock free
      (List.replicate form.count (TypeExpr.base block.name) ++ bound) form.components)
    (copyMembers : Members language block.toBlock free (List.replicate copy.count (TypeExpr.base block.name) ++
      (List.replicate form.count (TypeExpr.base block.name) ++ bound)) copy.components) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (Prenex.restricts block.toBlock form.count
        (.collection .hashBag (form.components ++ [copy.toPattern block.toBlock]) none))
      ((form.unfoldWith copy).toPattern block.toBlock) := by
  obtain ⟨count, components⟩ := form
  obtain ⟨copies, copyComponents⟩ := copy
  simp only at formMembers copyMembers ⊢
  set inner := List.replicate count (TypeExpr.base block.name) ++ bound with innerIs
  have copyBagTyped : HasType language free inner
      (Prenex.restricts block.toBlock copies (.collection .hashBag copyComponents none)) (.base block.proc) :=
    restricts_typed copies (bag_typed copyMembers)
  have bodyBag : EquationEquiv (engineBasePremises RelationEnv.empty) language
      (Prenex.restricts block.toBlock copies (Prenex.body block.toBlock copyComponents))
      (Prenex.restricts block.toBlock copies (.collection .hashBag copyComponents none)) :=
    restricts_equation (block := block.toBlock) copies (.symm _ _ (bag_body_equivalent copyMembers).toEquationEquiv)
  have copyTyped : HasType language free inner
      (Prenex.restricts block.toBlock copies (Prenex.body block.toBlock copyComponents)) (.base block.proc) :=
    restricts_typed copies ((SortedEquiv.typed_iff (bag_body_equivalent copyMembers)).mp (bag_typed copyMembers))
  -- the inner block first among the components
  have reordered := (bag_perm_equivalent (block := block) (Members.append formMembers (Members.cons copyTyped Members.nil))
    (List.perm_append_comm (l₁ := components)
      (l₂ := [Prenex.restricts block.toBlock copies (Prenex.body block.toBlock copyComponents)]))).toEquationEquiv
  have asBag := collection_equation (language := language) (List.Forall₂.cons bodyBag (List.forall₂_same.mpr
    fun _ _ => .refl _)) (first := Prenex.restricts block.toBlock copies (Prenex.body block.toBlock copyComponents) ::
      components) []
  simp only [List.nil_append] at asBag
  -- extruded
  have extruded := bag_block_equivalent (block := block.toBlock) copyMembers formMembers
  have liftedMembers := lift_members (block := block.toBlock) copies formMembers
  rw [← List.append_assoc, ← List.replicate_add] at copyMembers liftedMembers
  have swapped := restricts_equation (block := block.toBlock) copies
    (bag_perm_equivalent (block := block) (Members.append copyMembers liftedMembers)
      (List.perm_append_comm (l₁ := copyComponents) (l₂ := components.map (liftBVars 0 copies)))).toEquationEquiv
  have bodied := restricts_equation (block := block.toBlock) copies
    (bag_body_equivalent (Members.append liftedMembers copyMembers)).toEquationEquiv
  have inside := Relation.EqvGen.trans _ _ _ reordered (Relation.EqvGen.trans _ _ _ asBag
    (Relation.EqvGen.trans _ _ _ extruded (Relation.EqvGen.trans _ _ _ swapped bodied)))
  have outside := restricts_equation (block := block.toBlock) count inside
  rw [restricts_add] at outside
  simp only [Prenex.unfoldWith, Prenex.toPattern, Nat.add_comm copies count]
  exact outside

include laws in
/-- **Processes beside a block's components are a block inside it**: the canonical blocks of the processes side by
side, inside. -/
theorem bag_unfoldWith_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {count : Nat} {others extra : List Pattern}
    (othersMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      others)
    (extraMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      extra) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (Prenex.restricts block.toBlock count (.collection .hashBag (others ++ extra) none))
      (((Prenex.mk count others).unfoldWith ((extra.map (canonP block)).foldr Prenex.par Prenex.nil)).toPattern
        block.toBlock) := by
  obtain ⟨copyMembers, copyEquivalent⟩ := foldr_canonP_sound (context.replicate count block.name)
    (fun element _ => (canonP_sound_all element).1) extraMembers
  have nestedTyped : HasType language free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (.collection .hashBag (others ++ .collection .hashBag extra none :: []) none) (.base block.proc) :=
    bag_typed (Members.append othersMembers (Members.cons (bag_typed extraMembers) Members.nil))
  have flattened := SortedEquiv.ofDerived (laws.flatten (pre := others) (inner := extra) (post := []) nestedTyped)
    nestedTyped (bag_typed (Members.append (Members.append othersMembers extraMembers) Members.nil))
  simp only [List.append_nil] at flattened
  have replaced := bag_fill (before := others) (after := []) (rest := none) othersMembers Members.nil copyEquivalent
  have inside := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ flattened.toEquationEquiv)
    replaced.toEquationEquiv
  exact Relation.EqvGen.trans _ _ _ (restricts_equation (block := block.toBlock) count inside)
    (unfoldWith_equivalent (block := block) (language := language) (form := ⟨count, others⟩)
      (copy := (extra.map (canonP block)).foldr Prenex.par Prenex.nil) othersMembers copyMembers)

include laws in
/-- **Restrictions over a front and other processes are a block inside the block of the others**: the others' canonical
blocks side by side under the restrictions, the front's canonical blocks, past the others' restrictions, inside. -/
theorem restricts_front_equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {count : Nat} {front rest : List Pattern}
    (frontMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      front)
    (restMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      rest) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (Prenex.restricts block.toBlock count (.collection .hashBag (front ++ rest) none))
      (((Prenex.mk (((rest.map (canonP block)).foldr Prenex.par Prenex.nil).count + count)
          ((rest.map (canonP block)).foldr Prenex.par Prenex.nil).components).unfoldWith
        (((front.map (liftBVars 0 ((rest.map (canonP block)).foldr Prenex.par Prenex.nil).count)).map
          (canonP block)).foldr Prenex.par Prenex.nil)).toPattern block.toBlock) := by
  set restForm := (rest.map (canonP block)).foldr Prenex.par Prenex.nil with restFormIs
  set frame := List.replicate count (TypeExpr.base block.name) ++ bound with frameIs
  obtain ⟨tailMembers, restEquivalent⟩ := foldr_canonP_sound (context.replicate count block.name)
    (fun element _ => (canonP_sound_all element).1) restMembers
  -- the others first, as their bag
  have permuted := (bag_perm_equivalent (Members.append frontMembers restMembers)
    (List.perm_append_comm (l₁ := front) (l₂ := rest))).toEquationEquiv
  have nestedTyped : HasType language free frame (.collection .hashBag ([] ++ .collection .hashBag rest none :: front) none)
      (.base block.proc) :=
    bag_typed (Members.cons (bag_typed restMembers) frontMembers)
  have flattened := SortedEquiv.ofDerived (laws.flatten (pre := []) (inner := rest) (post := front) nestedTyped)
    nestedTyped (bag_typed (Members.append restMembers frontMembers))
  simp only [List.nil_append] at flattened
  have replaced := bag_fill (before := []) (after := front) (rest := none) Members.nil frontMembers restEquivalent
  simp only [List.nil_append] at replaced
  have bodied := collection_equation (language := language) (List.Forall₂.cons
    (restricts_equation (block := block.toBlock) restForm.count
      (.symm _ _ (bag_body_equivalent tailMembers).toEquationEquiv))
    (List.forall₂_same.mpr fun _ _ => .refl _)) (first := restForm.toPattern block.toBlock :: front) []
  simp only [List.nil_append] at bodied
  have extruded := bag_block_equivalent (block := block.toBlock) tailMembers frontMembers
  have inside := Relation.EqvGen.trans _ _ _ permuted (Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ flattened.toEquationEquiv) (Relation.EqvGen.trans _ _ _ replaced.toEquationEquiv
      (Relation.EqvGen.trans _ _ _ bodied extruded)))
  have outside := restricts_equation (block := block.toBlock) count inside
  rw [restricts_add, Nat.add_comm count restForm.count] at outside
  have liftedMembers := lift_members (block := block.toBlock) restForm.count frontMembers
  rw [← List.append_assoc, ← List.replicate_add] at tailMembers liftedMembers
  exact Relation.EqvGen.trans _ _ _ outside (bag_unfoldWith_equivalent (block := block) (language := language)
    context (count := restForm.count + count) tailMembers liftedMembers)

include laws in
/-- **What a redex leaves reads beside the block's other processes as it reads, renamed, beside the unfolding's
other components**: both are blocks inside blocks whose canonical forms align. -/
theorem results_aligned {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {count inner unfolded : Nat} {rest tail results restU : List Pattern} {outer relabel : Nat → Nat}
    {attached : Nat → Prop}
    (restFormIs : (rest.map (canonP block)).foldr Prenex.par Prenex.nil = ⟨inner, tail⟩)
    (restMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound) rest)
    (restObjects : ∀ other ∈ rest, isObjectPattern other = true)
    (resultsMembers : Members language block.toBlock free
      (List.replicate count (TypeExpr.base block.name) ++ bound) results)
    (resultsObjects : ∀ result ∈ results, isObjectPattern result = true)
    (renamedMembers : Members language block.toBlock free (List.replicate unfolded (TypeExpr.base block.name) ++ bound)
      (results.map (rename relabel)))
    (restUMembers : Members language block.toBlock free (List.replicate unfolded (TypeExpr.base block.name) ++ bound)
      restU)
    (restUAtomic : ∀ component ∈ restU, decompose block.toBlock component = Prenex.atom component)
    (outerShift : ∀ index, outer (inner + count + index) = unfolded + index)
    (below : ∀ index < inner + count, attached index → outer index < unfolded)
    (aligned : ∀ extra : List Pattern, (∀ component ∈ extra, decompose block.toBlock component = Prenex.atom component) →
      (∀ component ∈ extra, ∀ index < inner + count, mentions index component = true → attached index) →
      normal block ⟨inner + count, tail ++ extra⟩ = normal block ⟨unfolded, restU ++ extra.map (rename outer)⟩)
    (resultsAttached : ∀ result ∈ results, ∀ index, FreeIn index result → index < count → attached (index + inner))
    (injective : Function.Injective relabel)
    (agree : ∀ result ∈ results, ∀ index, FreeIn index result → relabel index = outer (index + inner))
    (outerInjective : ∀ first second, (∃ result ∈ results, FreeIn first result) →
      (∃ result ∈ results, FreeIn second result) → outer (first + inner) = outer (second + inner) → first = second) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (Prenex.restricts block.toBlock count (.collection .hashBag (results ++ rest) none))
      (Prenex.restricts block.toBlock unfolded (.collection .hashBag (results.map (rename relabel) ++ restU) none)) := by
  have multisetFresh := replicate_not_multiset (block := block) (language := language)
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  have resultsBinds : ∀ result ∈ results, restrictionsBind block.toBlock result = true := fun result member =>
    restrictionsBind_of_typed (block := block) result (resultsMembers result member)
  have restBinds : ∀ other ∈ rest, restrictionsBind block.toBlock other = true := fun other member =>
    restrictionsBind_of_typed (block := block) other (restMembers other member)
  set copy := ((results.map (liftBVars 0 inner)).map (canonP block)).foldr Prenex.par Prenex.nil with copyIs
  set copyU := ((results.map (rename relabel)).map (canonP block)).foldr Prenex.par Prenex.nil with copyUIs
  -- the source side
  have source := restricts_front_equivalent (block := block) (language := language) context resultsMembers restMembers
  rw [restFormIs] at source
  -- the blocks are typed and atomic
  obtain ⟨tailMembers, -⟩ := foldr_canonP_sound (context.replicate count block.name)
    (fun element _ => (canonP_sound_all element).1) restMembers
  rw [restFormIs] at tailMembers
  simp only at tailMembers
  have liftedResults := lift_members (block := block.toBlock) inner resultsMembers
  obtain ⟨copyMembers, -⟩ := foldr_canonP_sound ((context.replicate count block.name).replicate inner block.name)
    (fun element _ => (canonP_sound_all element).1) liftedResults
  obtain ⟨copyUMembers, -⟩ := foldr_canonP_sound (context.replicate unfolded block.name)
    (fun element _ => (canonP_sound_all element).1) renamedMembers
  rw [← List.append_assoc, ← List.replicate_add] at tailMembers
  have copyMembers' : Members language block.toBlock free (List.replicate copy.count (TypeExpr.base block.name) ++
      (List.replicate (inner + count) (TypeExpr.base block.name) ++ bound)) copy.components := by
    rw [List.replicate_add, List.append_assoc]
    exact copyMembers
  have tailAtomic : ∀ component ∈ tail, decompose block.toBlock component = Prenex.atom component := by
    have atomic := foldr_par_atomic (block := block) (rest.map (canonP block)) fun form member => by
      obtain ⟨other, inRest, rfl⟩ := List.mem_map.mp member
      exact (canonFacts fresh restrictFresh (restObjects other inRest) (restBinds other inRest)).atomic
    rw [restFormIs] at atomic
    exact atomic
  have copyAtomic : copy.Atomic block.toBlock := foldr_par_atomic _ fun form member => by
    obtain ⟨lifted, inLifted, rfl⟩ := List.mem_map.mp member
    obtain ⟨result, inResults, rfl⟩ := List.mem_map.mp inLifted
    refine (canonFacts fresh restrictFresh ?_ ?_).atomic
    · rw [liftBVars_eq_rename, isObjectPattern_rename]
      exact resultsObjects result inResults
    · rw [liftBVars_eq_rename, restrictionsBind_rename]
      exact resultsBinds result inResults
  have copyUAtomic : copyU.Atomic block.toBlock := foldr_par_atomic _ fun form member => by
    obtain ⟨renamed, inRenamed, rfl⟩ := List.mem_map.mp member
    obtain ⟨result, inResults, rfl⟩ := List.mem_map.mp inRenamed
    refine (canonFacts fresh restrictFresh ?_ ?_).atomic
    · rw [isObjectPattern_rename]
      exact resultsObjects result inResults
    · rw [restrictionsBind_rename]
      exact resultsBinds result inResults
  -- the copy's free names are attached
  have copyAttached : ∀ component ∈ copy.components, ∀ index < inner + count,
      mentions (copy.count + index) component = true → attached index := by
    intro component member index below' mentioned
    have past : copy.FreePast index := ⟨component, member, by rw [Nat.add_comm]; exact (mentions_iff _ _).mp mentioned⟩
    rw [copyIs, freePast_foldr_par] at past
    obtain ⟨form, inForms, formPast⟩ := past
    obtain ⟨lifted, inLifted, rfl⟩ := List.mem_map.mp inForms
    obtain ⟨result, inResults, rfl⟩ := List.mem_map.mp inLifted
    have liftedObject : isObjectPattern (liftBVars 0 inner result) = true := by
      rw [liftBVars_eq_rename, isObjectPattern_rename]
      exact resultsObjects result inResults
    have liftedBinds : restrictionsBind block.toBlock (liftBVars 0 inner result) = true := by
      rw [liftBVars_eq_rename, restrictionsBind_rename]
      exact resultsBinds result inResults
    have free := ((freePast_canonP_and fresh restrictFresh _).1 liftedObject liftedBinds index).mp formPast
    rw [liftBVars_eq_rename, freeIn_rename] at free
    obtain ⟨original, originalFree, maps⟩ := free
    simp only [shiftAbove, Nat.not_lt_zero, if_false] at maps
    subst maps
    exact resultsAttached result inResults original originalFree (by omega)
  -- the canonical forms align
  have kMembers : Members language block.toBlock free
      (List.replicate ((Prenex.mk (inner + count) tail).unfoldWith copy).count (TypeExpr.base block.name) ++ bound)
      ((Prenex.mk (inner + count) tail).unfoldWith copy).components := by
    show Members language block.toBlock free (List.replicate (copy.count + (inner + count)) (TypeExpr.base block.name) ++
      bound) (tail.map (liftBVars 0 copy.count) ++ copy.components)
    rw [List.replicate_add, List.append_assoc]
    exact Members.append (lift_members (block := block.toBlock) copy.count tailMembers) copyMembers'
  have uMembers : Members language block.toBlock free
      (List.replicate ((Prenex.mk unfolded restU).unfoldWith copyU).count (TypeExpr.base block.name) ++ bound)
      ((Prenex.mk unfolded restU).unfoldWith copyU).components := by
    show Members language block.toBlock free (List.replicate (copyU.count + unfolded) (TypeExpr.base block.name) ++
      bound) (restU.map (liftBVars 0 copyU.count) ++ copyU.components)
    rw [List.replicate_add, List.append_assoc]
    exact Members.append (lift_members (block := block.toBlock) copyU.count restUMembers) copyUMembers
  have kNormal := (normal_sound context kMembers).2
  have uNormal := (normal_sound context uMembers).2
  have sameNormal : normal block ((Prenex.mk (inner + count) tail).unfoldWith copy) =
      normal block ((Prenex.mk unfolded restU).unfoldWith copyU) := by
    rw [align_inside fresh restrictFresh tailAtomic restUAtomic outerShift below aligned copyAtomic copyAttached]
    exact normal_unfoldWith_congr fresh restrictFresh restUAtomic (renameOuter_atomic copyAtomic outer) copyUAtomic
      (normal_results_renamed multisetFresh fresh restrictFresh resultsObjects resultsBinds injective agree
        outerInjective)
  rw [sameNormal] at kNormal
  -- the unfolding's side
  have target := bag_unfoldWith_equivalent (block := block) (language := language) context restUMembers renamedMembers
  have swapped := restricts_equation (block := block.toBlock) unfolded (bag_perm_equivalent (block := block)
    (Members.append renamedMembers restUMembers)
    (List.perm_append_comm (l₁ := results.map (rename relabel)) (l₂ := restU))).toEquationEquiv
  exact Relation.EqvGen.trans _ _ _ source (Relation.EqvGen.trans _ _ _ kNormal.toEquationEquiv
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ uNormal.toEquationEquiv)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ target) (Relation.EqvGen.symm _ _ swapped))))

include laws in
/-- **The parts of a redex in a block come back in an unfolding of the block's canonical form**, within as many
unfoldings as the parts times the ceiling of the canonical form, read alike to the canonical forms of the parts
renamed by an injective renaming; and what the redex leaves reads beside the block's other processes as it reads,
renamed, beside the unfolding's other components. -/
theorem replication_source {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {count : Nat} {parts rest : List Pattern}
    (members : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (parts ++ rest))
    (objects : ∀ element ∈ parts ++ rest, isObjectPattern element = true)
    (partsAtoms : ∀ part ∈ parts, canonP block part = Prenex.atom (canonR block part))
    (partsPlain : ∀ part ∈ parts, isReplicated block (canonR block part) = false) :
    ∃ (unfolded : Prenex) (relabel : Nat → Nat) (exposed restU : List Pattern),
      Function.Injective relabel ∧
      UnfoldsWithin block (parts.length * ceilingOf block (canonP block
          (Prenex.restricts block.toBlock count (.collection .hashBag (parts ++ rest) none))))
        (canonP block (Prenex.restricts block.toBlock count (.collection .hashBag (parts ++ rest) none))) unfolded ∧
      unfolded.components.Perm (exposed ++ restU) ∧
      List.Forall₂ (fun shown part => AlikeR block shown (canonR block (rename relabel part))) exposed parts ∧
      Members language block.toBlock free (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
        unfolded.components ∧
      (∀ component ∈ unfolded.components, isObjectPattern component = true) ∧
      (∀ part ∈ parts, ∀ index, FreeIn index part → (index < count → relabel index < unfolded.count) ∧
        (count ≤ index → relabel index = unfolded.count + (index - count))) ∧
      ∀ results : List Pattern,
        Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound) results →
        (∀ result ∈ results, isObjectPattern result = true) →
        (∀ result ∈ results, ∀ index, FreeIn index result → ∃ part ∈ parts, FreeIn index part) →
        EquationEquiv (engineBasePremises RelationEnv.empty) language
          (Prenex.restricts block.toBlock count (.collection .hashBag (results ++ rest) none))
          (Prenex.restricts block.toBlock unfolded.count
            (.collection .hashBag (results.map (rename relabel) ++ restU) none)) := by
  classical
  have multisetFresh := replicate_not_multiset (block := block) (language := language)
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  have partsMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      parts := fun element member => members element (List.mem_append_left _ member)
  have restMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      rest := fun element member => members element (List.mem_append_right _ member)
  have partsObjects : ∀ part ∈ parts, isObjectPattern part = true := fun part member =>
    objects part (List.mem_append_left _ member)
  have restObjects : ∀ other ∈ rest, isObjectPattern other = true := fun other member =>
    objects other (List.mem_append_right _ member)
  have partsBinds : ∀ part ∈ parts, restrictionsBind block.toBlock part = true := fun part member =>
    restrictionsBind_of_typed (block := block) part (partsMembers part member)
  have restBinds : ∀ other ∈ rest, restrictionsBind block.toBlock other = true := fun other member =>
    restrictionsBind_of_typed (block := block) other (restMembers other member)
  have partsFree : ∀ part ∈ parts, ∀ index, FreeIn index (canonR block part) ↔ FreeIn index part := fun part member =>
    freeIn_canonR fresh restrictFresh (partsObjects part member) (partsBinds part member)
  -- the block of the source
  have blockIs := canonP_restricts_bag fresh restrictFresh count partsObjects restObjects partsBinds restBinds partsAtoms
  generalize restFormIs : (rest.map (canonP block)).foldr Prenex.par Prenex.nil = restForm at blockIs
  obtain ⟨inner, tail⟩ := restForm
  simp only at blockIs
  set partsK := (parts.map (canonR block)).map (liftBVars 0 inner) with partsKIs
  have tailFacts : (∀ component ∈ tail, decompose block.toBlock component = Prenex.atom component) ∧
      ∀ component ∈ tail, isObjectPattern component = true := by
    have atomic := foldr_par_atomic (block := block) (rest.map (canonP block)) fun form member => by
      obtain ⟨other, inRest, rfl⟩ := List.mem_map.mp member
      exact (canonFacts fresh restrictFresh (restObjects other inRest) (restBinds other inRest)).atomic
    have objectsTail := foldr_par_objects (rest.map (canonP block)) fun form member => by
      obtain ⟨other, inRest, rfl⟩ := List.mem_map.mp member
      exact (objects_canonP_and other).1 (restObjects other inRest)
    rw [restFormIs] at atomic objectsTail
    exact ⟨atomic, objectsTail⟩
  have canonRAtomic : ∀ part ∈ parts, decompose block.toBlock (canonR block part) = Prenex.atom (canonR block part) := by
    intro part member
    have atomic := (canonFacts fresh restrictFresh (partsObjects part member) (partsBinds part member)).atomic
    rw [partsAtoms part member] at atomic
    exact atomic _ (List.mem_singleton_self _)
  have kAtomic : (Prenex.mk (inner + count) (partsK ++ tail)).Atomic block.toBlock := by
    intro component member
    rcases List.mem_append.mp member with inParts | inTail
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inParts
      obtain ⟨part, inPartsList, rfl⟩ := List.mem_map.mp inOriginal
      rw [liftBVars_eq_rename]
      exact atomic_rename (canonRAtomic part inPartsList) _
    · exact tailFacts.1 component inTail
  have kObjects : ∀ component ∈ partsK ++ tail, isObjectPattern component = true := by
    intro component member
    rcases List.mem_append.mp member with inParts | inTail
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inParts
      obtain ⟨part, inPartsList, rfl⟩ := List.mem_map.mp inOriginal
      rw [liftBVars_eq_rename, isObjectPattern_rename]
      exact isObject_canonR (partsObjects part inPartsList)
    · exact tailFacts.2 component inTail
  have partsKPlain : ∀ part ∈ partsK, isReplicated block part = false := by
    intro component member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    obtain ⟨part, inPartsList, rfl⟩ := List.mem_map.mp inOriginal
    rw [liftBVars_eq_rename, isReplicated_rename]
    exact partsPlain part inPartsList
  have low : ∀ component ∈ partsK ++ tail, isReplicated block component = true →
      height block component < ceilingOf block (canonP block
        (Prenex.restricts block.toBlock count (.collection .hashBag (parts ++ rest) none))) := by
    rw [blockIs]
    exact height_lt_ceilingOf multisetFresh fresh restrictFresh kAtomic
  obtain ⟨unfolded, relabelK, exposed, restU, unfolds, componentsPerm, related, outer, below, injective, aligned⟩ :=
    exposure fresh restrictFresh kAtomic partsKPlain low
  -- the renaming from the block's frame into the unfolding's
  set sigma := relabelK ∘ shiftAbove 0 inner with sigmaIs
  have sigmaShift : ∀ index, sigma index = relabelK (index + inner) := fun index => by
    simp [sigmaIs, shiftAbove]
  have attachedPart : ∀ part ∈ parts, ∀ index, FreeIn index part →
      ∃ held ∈ partsK, mentions (index + inner) held = true := by
    intro part member index free
    refine ⟨_, List.mem_map_of_mem (List.mem_map_of_mem member), ?_⟩
    rw [mentions_iff, liftBVars_eq_rename, freeIn_rename]
    exact ⟨index, (partsFree part member index).mpr free, by simp [shiftAbove]⟩
  have sigmaBelow : ∀ part ∈ parts, ∀ index, FreeIn index part → index < count → sigma index < unfolded.count := by
    intro part member index free below'
    rw [sigmaShift]
    exact below (index + inner) (by omega) (attachedPart part member index free)
  have sigmaAbove : ∀ index, count ≤ index → sigma index = unfolded.count + (index - count) := by
    intro index above
    rw [sigmaShift, show index + inner = inner + count + (index - count) by omega, outer]
  have sigmaInjective : ∀ first second, (∃ part ∈ parts, FreeIn first part) → (∃ part ∈ parts, FreeIn second part) →
      sigma first = sigma second → first = second := by
    rintro first second ⟨firstPart, firstMember, firstFree⟩ ⟨secondPart, secondMember, secondFree⟩ same
    by_cases firstBelow : first < count <;> by_cases secondBelow : second < count
    · rw [sigmaShift, sigmaShift] at same
      have := injective (first + inner) (by omega) (second + inner) (by omega)
        (attachedPart firstPart firstMember first firstFree) (attachedPart secondPart secondMember second secondFree)
        same
      omega
    · have := sigmaBelow firstPart firstMember first firstFree firstBelow
      rw [sigmaAbove second (by omega)] at same
      omega
    · have := sigmaBelow secondPart secondMember second secondFree secondBelow
      rw [sigmaAbove first (by omega)] at same
      omega
    · rw [sigmaAbove first (by omega), sigmaAbove second (by omega)] at same
      omega
  -- an injective renaming agreeing on the parts' free names
  obtain ⟨limit, bounded⟩ := exists_bound_of_list (fun pattern bound => ∀ index, FreeIn index pattern → index < bound)
    (fun _ _ _ le holds index free => lt_of_lt_of_le (holds index free) le) parts fun pattern _ =>
      exists_freeBound pattern
  obtain ⟨relabel, relabelInjective, agrees'⟩ := exists_injective_agree sigma limit
    (fun index => ∃ part ∈ parts, FreeIn index part)
    fun first second _ firstIn _ secondIn same => sigmaInjective first second firstIn secondIn same
  have agrees : ∀ part ∈ parts, ∀ index, FreeIn index part → relabel index = sigma index := fun part member index free =>
    agrees' index (bounded part member index free) ⟨part, member, free⟩
  -- the parts, read alike
  have alikeParts : List.Forall₂ (fun shown part => AlikeR block shown (canonR block (rename relabel part)))
      exposed parts := by
    rw [partsKIs, List.map_map, List.forall₂_map_right_iff] at related
    refine forall₂_imp_mem_right related fun shown part member alike => ?_
    have renamedPart : rename relabelK (liftBVars 0 inner (canonR block part)) =
        rename relabel (canonR block part) := by
      rw [liftBVars_eq_rename, rename_comp]
      apply rename_congr
      intro index free
      rw [agrees part member index ((partsFree part member index).mp free), sigmaShift]
      simp [shiftAbove]
    have canonRenamed : canonR block (rename relabel part) = recanon block (rename relabel (canonR block part)) := by
      unfold canonR
      rw [canonP_rename multisetFresh fresh restrictFresh (partsObjects part member) (partsBinds part member)
        relabelInjective, partsAtoms part member,
        normal_atom_renameOuter fresh restrictFresh (canonRAtomic part member)]
      rfl
    simp only [Function.comp_apply] at alike
    rw [renamedPart] at alike
    rw [canonRenamed]
    exact alike.trans (alike_recanon_all fresh restrictFresh _)
  -- the unfolding is typed, of object terms and atomic
  have sourceTyped : HasType language free bound
      (Prenex.restricts block.toBlock count (.collection .hashBag (parts ++ rest) none)) (.base block.proc) :=
    restricts_typed count (bag_typed members)
  have normalMembers := (canonP_sound_all (block := block) (language := language)
    (Prenex.restricts block.toBlock count (.collection .hashBag (parts ++ rest) none))).1.members context sourceTyped
  rw [blockIs] at normalMembers
  have unfoldedMembers := unfolds.members context normalMembers
  have unfoldedObjects := unfolds.objects (normal_objects kObjects)
  have unfoldedAtomic := unfolds.atomic fresh restrictFresh (normal_atomic fresh restrictFresh kAtomic)
  have restUMembers : Members language block.toBlock free
      (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound) restU := fun element member =>
    unfoldedMembers element (componentsPerm.symm.subset (List.mem_append_right _ member))
  have restUAtomic : ∀ component ∈ restU, decompose block.toBlock component = Prenex.atom component :=
    fun component member => unfoldedAtomic component (componentsPerm.symm.subset (List.mem_append_right _ member))
  have partsMaps : ∀ part ∈ parts, ∀ index, FreeIn index part → (index < count → relabel index < unfolded.count) ∧
      (count ≤ index → relabel index = unfolded.count + (index - count)) := by
    intro part member index free
    rw [agrees part member index free]
    exact ⟨sigmaBelow part member index free, sigmaAbove index⟩
  refine ⟨unfolded, relabel, exposed, restU, relabelInjective, ?_, componentsPerm, alikeParts, unfoldedMembers,
    unfoldedObjects, partsMaps, ?_⟩
  · rw [blockIs]
    rw [blockIs] at unfolds
    have lengthIs : partsK.length = parts.length := by simp [partsKIs]
    rw [← lengthIs]
    exact unfolds
  · intro results resultsMembers resultsObjects resultsFree
    have renamedMembers : Members language block.toBlock free
        (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound) (results.map (rename relabel)) := by
      intro element member
      obtain ⟨result, inResults, rfl⟩ := List.mem_map.mp member
      refine rename_typed_on_support (resultsMembers result inResults) fun index sort free lookup => ?_
      obtain ⟨part, inParts, partFree⟩ := resultsFree result inResults index free
      exact frame_lookup (partsMaps part inParts index partFree) lookup
    exact results_aligned context restFormIs restMembers restObjects resultsMembers resultsObjects renamedMembers
      restUMembers restUAtomic outer below (fun extra extraAtomic extraAttached => aligned extra extraAtomic extraAttached)
      (fun result member index free _ => by
        obtain ⟨part, inParts, partFree⟩ := resultsFree result member index free
        exact attachedPart part inParts index partFree)
      relabelInjective
      (fun result member index free => by
        obtain ⟨part, inParts, partFree⟩ := resultsFree result member index free
        rw [agrees part inParts index partFree, sigmaShift])
      (fun first second firstIn secondIn same => by
        obtain ⟨firstResult, firstMember, firstFree⟩ := firstIn
        obtain ⟨secondResult, secondMember, secondFree⟩ := secondIn
        refine sigmaInjective first second (resultsFree firstResult firstMember first firstFree)
          (resultsFree secondResult secondMember second secondFree) ?_
        rw [sigmaShift, sigmaShift]
        exact same)

/-! ## Calculi with replication whose steps are reactions -/

/-- **A calculus with replication whose steps are reactions**: a redex has parts and leaves a result, as in a calculus
with restriction (`Reactions`); its parts are their own canonical blocks and not replicated, at most `arity` of them;
and components read alike to the canonical forms of a redex's parts are the parts of a redex leaving, up to the static
theory, what it leaves. -/
structure ReplicationReactions (language : LanguageDef) (block : ReplicationBlock) (step : Pattern → Pattern → Prop) where
  /-- The redexes. -/
  Redex : Type
  /-- The components that react. -/
  parts : Redex → List Pattern
  /-- What they leave. -/
  result : Redex → List Pattern
  /-- Renaming a redex's variables. -/
  rename : (Nat → Nat) → Redex → Redex
  parts_rename : ∀ relabel redex, parts (rename relabel redex) = (parts redex).map (RestrictionBlocks.rename relabel)
  result_rename : ∀ relabel redex, result (rename relabel redex) = (result redex).map (RestrictionBlocks.rename relabel)
  /-- A part's canonical block is the part read canonically. -/
  canonicalAtoms : ∀ redex, ∀ part ∈ parts redex, isObjectPattern part = true →
    restrictionsBind block.toBlock part = true → canonP block part = Prenex.atom (canonR block part)
  /-- A part read canonically is not replicated. -/
  plain : ∀ redex, ∀ part ∈ parts redex, isObjectPattern part = true →
    restrictionsBind block.toBlock part = true → isReplicated block (canonR block part) = false
  /-- At most so many parts. -/
  arity : Nat
  arity_le : ∀ redex, (parts redex).length ≤ arity
  /-- What a redex leaves are processes, wherever its parts are. -/
  result_members : ∀ {free : FreeTypeContext} {bound : List TypeExpr} redex,
    Members language block.toBlock free bound (parts redex) → Members language block.toBlock free bound (result redex)
  result_objects : ∀ redex, (∀ part ∈ parts redex, isObjectPattern part = true) →
    ∀ element ∈ result redex, isObjectPattern element = true
  /-- What a redex leaves uses only the variables of its parts. -/
  freeIn_result : ∀ redex {index : Nat} {element : Pattern}, element ∈ result redex → FreeIn index element →
    ∃ part ∈ parts redex, FreeIn index part
  /-- **Components read alike to the canonical forms of a redex's parts are a redex** leaving what it leaves, up to
  the static theory. -/
  alike : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ redex (shown : List Pattern),
    Members language block.toBlock free bound (parts redex) → (∀ part ∈ parts redex, isObjectPattern part = true) →
    Members language block.toBlock free bound shown → (∀ part ∈ shown, isObjectPattern part = true) →
    List.Forall₂ (fun part original => AlikeR block part (canonR block original)) shown (parts redex) →
    ∃ redex', parts redex' = shown ∧
      List.Forall₂ (EquationEquiv (engineBasePremises RelationEnv.empty) language) (result redex') (result redex)
  /-- A redex reacts in any bag that holds its parts. -/
  react : ∀ {free : FreeTypeContext} {bound : List TypeExpr} redex {components rest : List Pattern},
    components.Perm (parts redex ++ rest) → Members language block.toBlock free bound components →
    (∀ component ∈ components, isObjectPattern component = true) →
    ∃ target, step (Prenex.body block.toBlock components) target ∧
      EquationEquiv (engineBasePremises RelationEnv.empty) language target
        (.collection .hashBag (result redex ++ rest) none)
  /-- Steps happen under a restriction. -/
  restrict : ∀ {source target : Pattern}, step source target →
    step (.apply block.restrict [.lambda none source]) (.apply block.restrict [.lambda none target])

variable {step : Pattern → Pattern → Prop}

/-- **A block with a redex at its front**, for a calculus with replication: the redex's parts react at the front of
the block. -/
abbrev ReplicationStepAt (reactions : ReplicationReactions language block step) (free : FreeTypeContext)
    (bound : List TypeExpr) (source target : Pattern) (count : Nat) (redex : reactions.Redex) (rest : List Pattern) :
    Prop :=
  ReactsAt language block.toBlock free bound source target count (reactions.parts redex) (reactions.result redex) rest

omit laws in
theorem ReplicationReactions.restricts_step (reactions : ReplicationReactions language block step) :
    ∀ (count : Nat) {source target : Pattern}, step source target →
      step (Prenex.restricts block.toBlock count source) (Prenex.restricts block.toBlock count target)
  | 0, _, _, stepped => stepped
  | count + 1, _, _, stepped => reactions.restrict (reactions.restricts_step count stepped)

omit laws in
theorem forall₂_mem_left {α β : Type} {relation : α → β → Prop} :
    ∀ {first : List α} {second : List β}, List.Forall₂ relation first second →
      ∀ {a : α}, a ∈ first → ∃ b ∈ second, relation a b
  | _, _, .nil, _, member => absurd member List.not_mem_nil
  | _, _, .cons head rest, _, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨b, inSecond, related⟩ := forall₂_mem_left rest later
        exact ⟨b, List.mem_cons_of_mem _ inSecond, related⟩

include laws in
/-- **A step of a process is a reaction of an unfolding of its canonical form**, within as many unfoldings as the
calculus's arity times the ceiling of the canonical form: the unfolding holds the parts of a redex, none replicated,
beside the rest, and what the redex leaves beside the rest reads, under the unfolding's restrictions, as the original
contractum. -/
theorem replication_reaction (reactions : ReplicationReactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {source target : Pattern} {count : Nat}
    {redex : reactions.Redex} {rest : List Pattern}
    (reached : ReplicationStepAt reactions free bound source target count redex rest)
    (sourceTyped : HasType language free bound source (.base block.proc))
    (sourceObject : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin block (reactions.arity * ceilingOf block (canonP block source)) (canonP block source)
        unfolded ∧
      ∃ (redex' : reactions.Redex) (restU : List Pattern),
        unfolded.components.Perm (reactions.parts redex' ++ restU) ∧
        (∀ part ∈ reactions.parts redex', isReplicated block part = false) ∧
        Members language block.toBlock free (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
          unfolded.components ∧
        (∀ component ∈ unfolded.components, isObjectPattern component = true) ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) language
          (Prenex.restricts block.toBlock unfolded.count (.collection .hashBag (reactions.result redex' ++ restU) none))
          target := by
  have fresh := replicate_not_emptyUnit (block := block) (language := language)
  have restrictFresh := replicate_ne_restrict (block := block) (language := language)
  have partsMembers : Members language block.toBlock free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (reactions.parts redex) := fun element member => reached.members element (List.mem_append_left _ member)
  have partsObjects : ∀ part ∈ reactions.parts redex, isObjectPattern part = true := fun part member =>
    reached.objects part (List.mem_append_left _ member)
  have partsBinds : ∀ part ∈ reactions.parts redex, restrictionsBind block.toBlock part = true := fun part member =>
    restrictionsBind_of_typed (block := block) part (partsMembers part member)
  -- the canonical form is that of the block with the redex at its front
  have blockTyped : HasType language free bound
      (Prenex.restricts block.toBlock count (.collection .hashBag (reactions.parts redex ++ rest) none))
      (.base block.proc) := restricts_typed count (bag_typed reached.members)
  have blockObject : isObjectPattern
      (Prenex.restricts block.toBlock count (.collection .hashBag (reactions.parts redex ++ rest) none)) = true := by
    rw [isObject_restricts, isObject_bag]
    exact reached.objects
  have sameCanon : canonP block source =
      canonP block (Prenex.restricts block.toBlock count (.collection .hashBag (reactions.parts redex ++ rest) none)) := by
    have equal := canonR_complete sourceObject blockObject (restrictionsBind_of_typed (block := block) source sourceTyped)
      reached.source
    exact toPattern_injective
      (canonFacts fresh restrictFresh sourceObject (restrictionsBind_of_typed (block := block) source sourceTyped)).atomic
      (canonFacts fresh restrictFresh blockObject (restrictionsBind_of_typed (block := block) _ blockTyped)).atomic equal
  obtain ⟨unfolded, relabel, exposed, restU, relabelInjective, unfolds, componentsPerm, alikeParts, unfoldedMembers,
    unfoldedObjects, partsMaps, resultsAligned⟩ := replication_source context reached.members reached.objects
      (fun part member => reactions.canonicalAtoms redex part member (partsObjects part member) (partsBinds part member))
      (fun part member => reactions.plain redex part member (partsObjects part member) (partsBinds part member))
  refine ⟨unfolded, ?_, ?_⟩
  · rw [sameCanon]
    exact unfolds.mono (Nat.mul_le_mul_right _ (reactions.arity_le redex))
  -- the redex, renamed into the unfolding, has parts read alike to the exposed components
  have renamedMembers : Members language block.toBlock free
      (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound)
      (reactions.parts (reactions.rename relabel redex)) := by
    rw [reactions.parts_rename]
    intro element member
    obtain ⟨part, inParts, rfl⟩ := List.mem_map.mp member
    exact rename_typed_on_support (partsMembers part inParts) fun index sort free lookup =>
      frame_lookup (partsMaps part inParts index free) lookup
  have renamedObjects : ∀ part ∈ reactions.parts (reactions.rename relabel redex), isObjectPattern part = true := by
    rw [reactions.parts_rename]
    intro element member
    obtain ⟨part, inParts, rfl⟩ := List.mem_map.mp member
    rw [isObjectPattern_rename]
    exact partsObjects part inParts
  have exposedMembers : Members language block.toBlock free
      (List.replicate unfolded.count (TypeExpr.base block.name) ++ bound) exposed := fun element member =>
    unfoldedMembers element (componentsPerm.symm.subset (List.mem_append_left _ member))
  have exposedObjects : ∀ component ∈ exposed, isObjectPattern component = true := fun component member =>
    unfoldedObjects component (componentsPerm.symm.subset (List.mem_append_left _ member))
  have exposedAlike : List.Forall₂ (fun part original => AlikeR block part (canonR block original)) exposed
      (reactions.parts (reactions.rename relabel redex)) := by
    rw [reactions.parts_rename, List.forall₂_map_right_iff]
    exact alikeParts
  obtain ⟨redex', partsIs, resultsRelated⟩ := reactions.alike (context.replicate unfolded.count block.name)
    (reactions.rename relabel redex) exposed renamedMembers renamedObjects exposedMembers exposedObjects exposedAlike
  refine ⟨redex', restU, by rw [partsIs]; exact componentsPerm, ?_, unfoldedMembers, unfoldedObjects, ?_⟩
  -- the exposed parts are read alike to parts read canonically, which are not replicated
  · rw [partsIs]
    intro part member
    obtain ⟨original, inRenamed, alike⟩ := forall₂_mem_left exposedAlike member
    rw [alike.2.1]
    exact reactions.plain _ original inRenamed (renamedObjects original inRenamed)
      (restrictionsBind_of_typed (block := block) original (renamedMembers original inRenamed))
  -- what the redex leaves reads as the original contractum
  have resultsSame := collection_equation (language := language)
    (List.rel_append resultsRelated (List.forall₂_same.mpr fun _ _ => .refl _)) (second := _ ++ restU) []
  simp only [List.nil_append] at resultsSame
  rw [reactions.result_rename] at resultsSame
  have aligned := resultsAligned (reactions.result redex) (reactions.result_members redex partsMembers)
    (reactions.result_objects redex partsObjects) fun result member index free =>
      reactions.freeIn_result redex member free
  exact Relation.EqvGen.trans _ _ _ (restricts_equation (block := block.toBlock) unfolded.count resultsSame)
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ aligned) (Relation.EqvGen.symm _ _ reached.target))

include laws in
/-- **A step of a process is matched by a step of an unfolding of its canonical form**, within as many unfoldings as
the calculus's arity times the ceiling of the canonical form, to a contractum equivalent to the original
contractum. -/
theorem replication_simulation (reactions : ReplicationReactions language block step) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {source target : Pattern} {count : Nat}
    {redex : reactions.Redex} {rest : List Pattern}
    (reached : ReplicationStepAt reactions free bound source target count redex rest)
    (sourceTyped : HasType language free bound source (.base block.proc))
    (sourceObject : isObjectPattern source = true) :
    ∃ unfolded, UnfoldsWithin block (reactions.arity * ceilingOf block (canonP block source)) (canonP block source)
        unfolded ∧
      ∃ target', step (unfolded.toPattern block.toBlock) target' ∧
        EquationEquiv (engineBasePremises RelationEnv.empty) language target' target := by
  obtain ⟨unfolded, unfolds, redex', restU, split, -, members, objects, reaches⟩ :=
    replication_reaction reactions context reached sourceTyped sourceObject
  obtain ⟨contracted, stepped, contractedIs⟩ := reactions.react redex' split members objects
  exact ⟨unfolded, unfolds, Prenex.restricts block.toBlock unfolded.count contracted,
    reactions.restricts_step unfolded.count stepped,
    Relation.EqvGen.trans _ _ _ (restricts_equation (block := block.toBlock) unfolded.count contractedIs) reaches⟩

omit laws in
/-- **A block whose replicated components copy one component each**, none of them replicated: an unfolding adds
that component, and nothing more to unfold. -/
def flatServers (block : ReplicationBlock) (form : Prenex) : Bool :=
  form.components.all fun component => (replicatedArgument block component).all fun argument =>
    decide (decompose block.toBlock argument = Prenex.atom argument) && !isReplicated block argument

omit laws in
theorem flatServers_spec {form : Prenex} (flat : flatServers block form = true) :
    ∀ component ∈ form.components, ∀ argument, component = .apply block.replicate [argument] →
      decompose block.toBlock argument = Prenex.atom argument ∧ isReplicated block argument = false := by
  intro component member argument componentIs
  have holds := List.all_eq_true.mp flat component member
  rw [mem_replicatedArgument.mpr componentIs] at holds
  simpa using holds

omit laws in
/-- **A block whose replicated components copy molecules**: the canonical form of each replicated component's argument
has no replicated component, so unfolding adds none. -/
def moleculeServers (block : ReplicationBlock) (form : Prenex) : Bool :=
  form.components.all fun component => (replicatedArgument block component).all fun argument =>
    (normal block (decompose block.toBlock argument)).components.all fun part => !isReplicated block part

omit laws in
theorem moleculeServers_spec {form : Prenex} (molecular : moleculeServers block form = true) :
    ∀ component ∈ form.components, ∀ argument, component = .apply block.replicate [argument] →
      ∀ part ∈ (normal block (decompose block.toBlock argument)).components, isReplicated block part = false := by
  intro component member argument componentIs part partMember
  have holds := List.all_eq_true.mp molecular component member
  rw [mem_replicatedArgument.mpr componentIs] at holds
  simp only [Option.all_some, List.all_eq_true] at holds
  simpa using holds part partMember

omit laws in
/-- **How many unfoldings a presentation takes**: the arity of the redexes when the replicated components copy
molecules, since a redex takes components of at most one copy per part; otherwise the arity times the ceiling. -/
def presentationDepth (block : ReplicationBlock) (arity : Nat) (form : Prenex) : Nat :=
  if moleculeServers block form then arity else arity * ceilingOf block form

omit laws in
/-- **The presentations of a state of a calculus with replication**: the unfoldings of its block within the
presentation depth, read back as processes. -/
def replicationPresentations (block : ReplicationBlock) (arity : Nat) (state : Pattern) : List Pattern :=
  (unfoldings block (presentationDepth block arity (decompose block.toBlock state))
    (decompose block.toBlock state)).map (Prenex.toPattern block.toBlock)

include laws in
/-- **Unfolding a replicated component is sound**: the block reads as the block with one more copy of the argument
inside, the copy's block in canonical form. -/
theorem unfoldWith_sound {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {form : Prenex} {argument : Pattern} (member : Pattern.apply block.replicate [argument] ∈ form.components)
    (members : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language (form.toPattern block.toBlock)
      ((form.unfoldWith (normal block (decompose block.toBlock argument))).toPattern block.toBlock) := by
  obtain ⟨count, components⟩ := form
  simp only at member members
  set frame := List.replicate count (TypeExpr.base block.name) ++ bound with frameIs
  have argumentTyped := replicate_argument_typed (members _ member)
  obtain ⟨decomposedMembers, decomposedEquivalent⟩ := decompose_sound (block := block.toBlock) argumentTyped
  obtain ⟨normalMembers, normalEquivalent⟩ := normal_sound (context.replicate count block.name) decomposedMembers
  -- the block's bag, a copy beside it
  have bodied := restricts_equation (block := block.toBlock) count
    (.symm _ _ (bag_body_equivalent members).toEquationEquiv)
  have absorbed := (unfold_absorb_equivalent argumentTyped members member).toEquationEquiv
  have reordered := (bag_perm_equivalent (block := block) (Members.cons argumentTyped members)
    (List.perm_append_comm (l₁ := [argument]) (l₂ := components))).toEquationEquiv
  have copied := bag_fill (before := components) (after := []) (rest := none) members Members.nil
    (Relation.EqvGen.trans _ _ _ decomposedEquivalent normalEquivalent)
  have inside := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ absorbed)
    (Relation.EqvGen.trans _ _ _ reordered copied.toEquationEquiv)
  have unfolded := unfoldWith_equivalent (block := block) (language := language) (form := ⟨count, components⟩)
    (copy := normal block (decompose block.toBlock argument)) members normalMembers
  exact Relation.EqvGen.trans _ _ _ bodied (Relation.EqvGen.trans _ _ _
    (restricts_equation (block := block.toBlock) count inside) unfolded)

include laws in
/-- **Unfoldings are sound**: an unfolding of a typed block reads as the block. -/
theorem UnfoldsWithin.equivalent {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {depth : Nat} {form unfolded : Prenex} (unfolds : UnfoldsWithin block depth form unfolded) :
    Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
        form.components →
      EquationEquiv (engineBasePremises RelationEnv.empty) language (form.toPattern block.toBlock)
        (unfolded.toPattern block.toBlock) := by
  induction unfolds with
  | refl => exact fun _ => .refl _
  | @step depth form next argument member rest recurse =>
      intro members
      have nextMembers := (UnfoldsWithin.single (block := block) member).members context members
      exact Relation.EqvGen.trans _ _ _ (unfoldWith_sound context member members) (recurse nextMembers)

include laws in
/-- **The presentations of a typed process read as the process.** -/
theorem replicationPresentations_equivalent {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {state : Pattern} (typed : HasType language free bound state (.base block.proc))
    (arity : Nat) : ∀ shown ∈ replicationPresentations block arity state,
      EquationEquiv (engineBasePremises RelationEnv.empty) language state shown := by
  intro shown member
  unfold replicationPresentations at member
  obtain ⟨unfolded, inUnfoldings, rfl⟩ := List.mem_map.mp member
  obtain ⟨decomposedMembers, decomposedEquivalent⟩ := decompose_sound (block := block.toBlock) typed
  exact Relation.EqvGen.trans _ _ _ decomposedEquivalent.toEquationEquiv
    ((((mem_unfoldings _ _ _).mp inUnfoldings).equivalent context) decomposedMembers)

include laws in
/-- **Presentations are admitted, with the state's canonical form**: every presentation of a typed object process is
a typed object process, and it has the process's canonical form. -/
theorem replicationPresentations_admitted {free : FreeTypeContext} {bound : List TypeExpr}
    (context : BaseContext free bound) {state : Pattern} (typed : HasType language free bound state (.base block.proc))
    (object : isObjectPattern state = true) (arity : Nat) : ∀ shown ∈ replicationPresentations block arity state,
      HasType language free bound shown (.base block.proc) ∧ isObjectPattern shown = true ∧
        canonR block shown = canonR block state := by
  intro shown member
  have equivalent := replicationPresentations_equivalent context typed arity shown member
  unfold replicationPresentations at member
  obtain ⟨unfolded, inUnfoldings, rfl⟩ := List.mem_map.mp member
  have unfolds := (mem_unfoldings _ _ _).mp inUnfoldings
  obtain ⟨decomposedMembers, -⟩ := decompose_sound (block := block.toBlock) typed
  have shownObject := isObject_toPattern (base := block.toBlock)
    (unfolds.objects (objects_of_decompose (block := block.toBlock) object))
  refine ⟨?_, shownObject, (canonR_complete object shownObject
    (restrictionsBind_of_typed (block := block) state typed) equivalent).symm⟩
  unfold Prenex.toPattern
  exact restricts_typed _ (body_typed (unfolds.members context decomposedMembers))

end Inside

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
