import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Completeness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationForm
import Batteries.Data.List.Perm

/-!
# Enough fuel settles the canonical form with replication

The **mass** of a block is twice its restrictions plus the sizes of its components (`Prenex.mass`); the block of a
pattern weighs at most the pattern (`mass_decompose`). Normalizing a block reads the canonical form only on patterns
lighter than the block (`absorb_congr`), and reads again only parts of its components, so enough fuel, three times
the mass, settles it (`settles`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

/-- **The mass of a block**: twice its restrictions and the sizes of its components. -/
def Prenex.mass (form : Prenex) : Nat := 2 * form.count + sizeList form.components

theorem sizeList_append (first second : List Pattern) :
    sizeList (first ++ second) = sizeList first + sizeList second := by
  rw [sizeList_eq_sum, sizeList_eq_sum, sizeList_eq_sum, List.map_append, List.sum_append]

theorem sizeList_map_rename (relabel : Nat → Nat) (patterns : List Pattern) :
    sizeList (patterns.map (rename relabel)) = sizeList patterns := by
  rw [sizeList_eq_sum, sizeList_eq_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun pattern _ => size_rename pattern relabel

theorem sizeList_map_lift (cutoff shift : Nat) (patterns : List Pattern) :
    sizeList (patterns.map (liftBVars cutoff shift)) = sizeList patterns := by
  have lifted : patterns.map (liftBVars cutoff shift) = patterns.map (rename (shiftAbove cutoff shift)) :=
    List.map_congr_left fun pattern _ => liftBVars_eq_rename cutoff shift pattern
  rw [lifted, sizeList_map_rename]

theorem mass_par (first second : Prenex) : (first.par second).mass = first.mass + second.mass := by
  simp only [Prenex.mass, Prenex.par, sizeList_append, sizeList_map_lift]
  omega

theorem mass_close (form : Prenex) : form.close.mass ≤ form.mass + 2 := by
  unfold Prenex.close
  split
  · simp [Prenex.mass, Prenex.restrict]
    omega
  · simp only [Prenex.mass, sizeList_map_rename]
    omega

theorem sizeList_perm {first second : List Pattern} (permutation : first.Perm second) :
    sizeList first = sizeList second := by
  rw [sizeList_eq_sum, sizeList_eq_sum]
  exact (permutation.map size).sum_eq

theorem sizeList_subperm {first second : List Pattern} (subperm : first.Subperm second) :
    sizeList first ≤ sizeList second := by
  obtain ⟨middle, permutation, sublist⟩ := subperm
  rw [← sizeList_perm permutation, sizeList_eq_sum, sizeList_eq_sum]
  exact (sublist.map size).sum_le_sum fun _ _ => Nat.zero_le _

section Block

variable {block : Block}

mutual
  /-- **The block of a pattern weighs at most the pattern.** -/
  theorem mass_decompose (pattern : Pattern) : (decompose block pattern).mass ≤ size pattern := by
    by_cases isNil : pattern = .apply block.unit []
    · subst isNil
      simp [decompose_unit, Prenex.nil, Prenex.mass, sizeList]
    by_cases isRestriction : ∃ binder body, pattern = .apply block.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      rw [decompose_restrict]
      have closed := mass_close (decompose block body)
      have inner := mass_decompose body
      simp only [size, sizeList]
      omega
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      rw [decompose_bag]
      have := mass_decomposeList elements
      simp only [size]
      omega
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ block.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      rw [decompose_multiset (fun binder body equal => isRestriction ⟨binder, body, equal⟩)]
      split_ifs
      · simp [Prenex.nil, Prenex.mass, sizeList]
      · simp [Prenex.atom, Prenex.mass, sizeList]
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
      (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩)]
    simp [Prenex.atom, Prenex.mass, sizeList]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mass_decomposeList (elements : List Pattern) : (decomposeList block elements).mass ≤ sizeList elements := by
    match elements with
    | [] => simp [decomposeList, Prenex.nil, Prenex.mass, sizeList]
    | element :: elements =>
        rw [decomposeList, mass_par]
        have := mass_decompose element
        have := mass_decomposeList elements
        simp only [sizeList]
        omega
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem size_body_le (components : List Pattern) : size (Prenex.body block components) ≤ sizeList components + 1 := by
  match components with
  | [] => simp [Prenex.body, size, sizeList]
  | [component] => simp [Prenex.body, sizeList]
  | first :: second :: rest => simp [Prenex.body, size]

theorem size_restricts (count : Nat) (process : Pattern) :
    size (Prenex.restricts block count process) = 2 * count + size process := by
  induction count with
  | zero => simp [Prenex.restricts]
  | succ count recurse =>
      simp only [Prenex.restricts, size, sizeList, recurse]
      omega

theorem size_toPattern_le (form : Prenex) : size (form.toPattern block) ≤ form.mass + 1 := by
  have := size_body_le (block := block) form.components
  simp only [Prenex.toPattern, size_restricts, Prenex.mass]
  omega

theorem mass_le_size_toPattern (form : Prenex) : form.mass ≤ size (form.toPattern block) := by
  simp only [Prenex.toPattern, size_restricts, Prenex.mass]
  match form.components with
  | [] => simp [Prenex.body, size, sizeList]
  | [component] => simp [Prenex.body, sizeList]
  | first :: second :: rest => simp [Prenex.body, size]

end Block

/-! ## Absorption reads the canonical form on lighter patterns -/

section Absorb

variable {block : ReplicationBlock}

/-- **One absorption keeps the block's restrictions and some of its components.** -/
theorem absorbOnce_subperm {canonical : Pattern → Pattern} {form next : Prenex}
    (absorbed : absorbOnce block canonical form = some next) :
    next.count = form.count ∧ next.components.Subperm form.components := by
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
  split_ifs at found
  obtain ⟨group, groupFound, rfl⟩ := Option.map_eq_some_iff.mp found
  set allowed := (List.range count).filter fun index => !mentions index (Pattern.apply label [argument])
  set candidates := groupsThrough allowed count (components.eraseIdx position)
  obtain ⟨-, permuted⟩ := groupsThrough_partition allowed count (components.eraseIdx position)
  have groupMember := List.mem_of_find?_eq_some groupFound
  refine ⟨rfl, ?_⟩
  have around : (Pattern.apply label [argument] :: components.eraseIdx position).Perm components := by
    rw [← componentIs]
    exact List.getElem_cons_eraseIdx_perm inside
  have regroup : (components.eraseIdx position).Perm
      (group.components ++ (candidates.erase group).flatMap Group.components) :=
    permuted.symm.trans (by simpa using (List.perm_cons_erase groupMember).flatMap_right Group.components)
  have kept : ((candidates.erase group).flatMap Group.components ++
      [Pattern.apply label [argument]]).Subperm (Pattern.apply label [argument] :: components.eraseIdx position) := by
    refine (List.perm_append_singleton _ _).subperm.trans ?_
    exact (List.subperm_cons _).mpr ((List.sublist_append_right _ _).subperm.trans regroup.symm.subperm)
  exact kept.trans around.subperm

/-- The length of a list of restrictions of a block, each distinct and below the block's count, is at most the count. -/
theorem length_le_of_inside {count : Nat} {restrictions : List Nat} (nodup : restrictions.Nodup)
    (inside : ∀ index ∈ restrictions, index < count) : restrictions.length ≤ count := by
  have subperm : restrictions.Subperm (List.range count) :=
    nodup.subperm fun index member => List.mem_range.mpr (inside index member)
  simpa using subperm.length_le

/-- Two tests that agree on a list's members find the same member. -/
theorem find?_congr_mem {α : Type} {first second : α → Bool} :
    ∀ {list : List α}, (∀ item ∈ list, first item = second item) → list.find? first = list.find? second
  | [], _ => rfl
  | item :: list, agree => by
      simp only [List.find?_cons]
      rw [agree item List.mem_cons_self, find?_congr_mem fun other member => agree other (List.mem_cons_of_mem _ member)]

/-- Two tests that agree on a list's members agree on all of them. -/
theorem all_congr_mem {α : Type} {first second : α → Bool} :
    ∀ {list : List α}, (∀ item ∈ list, first item = second item) → list.all first = list.all second
  | [], _ => rfl
  | item :: list, agree => by
      simp only [List.all_cons]
      rw [agree item List.mem_cons_self, all_congr_mem fun other member => agree other (List.mem_cons_of_mem _ member)]

/-- **One absorption reads the canonical form only on patterns lighter than the block.** -/
theorem absorbOnce_congr {first second : Pattern → Pattern} {form : Prenex}
    (agree : ∀ pattern, size pattern < form.mass → first pattern = second pattern) :
    absorbOnce block first form = absorbOnce block second form := by
  obtain ⟨count, components⟩ := form
  unfold absorbOnce
  congr 1
  funext position
  simp only
  rcases lookup : (components[position]? : Option Pattern) with _ | component
  · rfl
  · have inside : position < components.length := by
      rcases List.getElem?_eq_some_iff.mp lookup with ⟨inside, -⟩
      exact inside
    have componentIs : components[position] = component := (List.getElem?_eq_some_iff.mp lookup).2
    match component, componentIs with
    | .apply label [argument], componentIs =>
        simp only
        split_ifs with isReplicate
        · congr 1
          set allowed := (List.range count).filter fun index => !mentions index (Pattern.apply label [argument])
          obtain ⟨partition, permuted⟩ := groupsThrough_partition allowed count (components.eraseIdx position)
          have around : (Pattern.apply label [argument] :: components.eraseIdx position).Perm components := by
            rw [← componentIs]
            exact List.getElem_cons_eraseIdx_perm inside
          have total : size argument + 1 + sizeList (components.eraseIdx position) = sizeList components := by
            have := sizeList_perm around
            simp only [sizeList, size] at this
            omega
          have argumentPositive := size_pos argument
          apply find?_congr_mem
          intro group member
          have restrictionsShort := length_le_of_inside (partition.nodup group member) (partition.inside group member)
          have groupLight : sizeList group.components ≤ sizeList (components.eraseIdx position) :=
            sizeList_subperm ((List.sublist_flatten_of_mem (List.mem_map.mpr ⟨group, member, rfl⟩)).subperm.trans
              (by simpa [List.flatMap] using permuted.subperm))
          have copyLight := size_toPattern_le (block := block.toBlock)
            (⟨group.restrictions.length, group.components.map (rename (Prenex.permute count (splitOrder count
              (outsideOf count group.restrictions) group.restrictions)))⟩ : Prenex)
          simp only [Prenex.mass, sizeList_map_rename] at copyLight
          have argumentSmall : size argument < 2 * count + sizeList components := by omega
          have membersSmall : ∀ member ∈ group.components, size (argumentOf? member) < 2 * count + sizeList components := by
            intro member inGroup
            have within := size_lt_of_mem inGroup
            have shrinks : size (argumentOf? member) ≤ size member := by
              cases member with
              | apply constructor arguments =>
                  rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩
                  · exact le_rfl
                  · simp [argumentOf?, size, sizeList]
                  · exact le_rfl
              | _ => exact le_rfl
            omega
          have allSame : (group.components.all fun member => !isReplicated block member ||
              decide (size (first (argumentOf? member)) < size (first argument))) =
              (group.components.all fun member => !isReplicated block member ||
              decide (size (second (argumentOf? member)) < size (second argument))) := by
            apply all_congr_mem
            intro member inGroup
            rw [agree _ (by simp only [Prenex.mass]; exact membersSmall member inGroup),
              agree argument (by simp only [Prenex.mass]; exact argumentSmall)]
          rw [allSame, agree (copyOf block.toBlock count group) (by
              unfold copyOf
              simp only [Prenex.mass]
              omega),
            agree (rename (Prenex.groupIndex count (outsideOf count group.restrictions)) argument) (by
              rw [size_rename]
              simp only [Prenex.mass]
              omega)]
        · rfl
    | .apply _ [], _ => rfl
    | .apply _ (_ :: _ :: _), _ => rfl
    | .bvar _, _ => rfl
    | .fvar _, _ => rfl
    | .lambda _ _, _ => rfl
    | .multiLambda _ _ _, _ => rfl
    | .subst _ _, _ => rfl
    | .collection _ _ _, _ => rfl

/-- **Absorption in rounds reads the canonical form only on patterns lighter than the block.** -/
theorem absorbRounds_congr {first second : Pattern → Pattern} :
    ∀ (rounds : Nat) {form : Prenex}, (∀ pattern, size pattern < form.mass → first pattern = second pattern) →
      absorbRounds block first rounds form = absorbRounds block second rounds form
  | 0, _, _ => rfl
  | rounds + 1, form, agree => by
      simp only [absorbRounds]
      rw [absorbOnce_congr agree]
      cases absorbed : absorbOnce block second form with
      | none => rfl
      | some next =>
          obtain ⟨countSame, subperm⟩ := absorbOnce_subperm absorbed
          have lighter : next.mass ≤ form.mass := by
            have := sizeList_subperm subperm
            simp only [Prenex.mass, countSame]
            omega
          exact absorbRounds_congr rounds fun pattern small => agree pattern (by omega)

/-- **Absorption reads the canonical form only on patterns lighter than the block.** -/
theorem absorb_congr {first second : Pattern → Pattern} {form : Prenex}
    (agree : ∀ pattern, size pattern < form.mass → first pattern = second pattern) :
    absorb block first form = absorb block second form := by
  unfold absorb
  rw [absorbRounds_congr _ agree]

/-- The components after absorption in rounds are among those before. -/
theorem absorbRounds_subperm {canonical : Pattern → Pattern} :
    ∀ (rounds : Nat) (form : Prenex), (absorbRounds block canonical rounds form).count = form.count ∧
      (absorbRounds block canonical rounds form).components.Subperm form.components
  | 0, _ => ⟨rfl, List.Subperm.refl _⟩
  | rounds + 1, form => by
      simp only [absorbRounds]
      cases absorbed : absorbOnce block canonical form with
      | none => exact ⟨rfl, List.Subperm.refl _⟩
      | some next =>
          obtain ⟨countSame, subperm⟩ := absorbOnce_subperm absorbed
          obtain ⟨countSame', subperm'⟩ := absorbRounds_subperm rounds next
          exact ⟨countSame'.trans countSame, subperm'.trans subperm⟩

/-- **The components after absorption weigh no more than the block's components**, one by one. -/
theorem absorb_components_size {canonical : Pattern → Pattern} {form : Prenex} :
    ∀ component ∈ (absorb block canonical form).components, size component ≤ sizeList form.components := by
  intro component member
  unfold absorb Prenex.prune at member
  simp only [List.mem_map] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  rw [size_rename]
  have inForm := (absorbRounds_subperm form.components.length form).2.subset originalMember
  rw [sizeList_eq_sum]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨original, inForm, rfl⟩)

theorem canonArgument_congr {first second : Pattern → Pattern} {argument : Pattern}
    (agree : ∀ pattern, size pattern ≤ size argument → first pattern = second pattern) :
    canonArgument first argument = canonArgument second argument := by
  cases argument with
  | lambda binder body =>
      simp only [canonArgument]
      rw [agree body (by simp [size])]
  | bvar => rfl
  | fvar => rfl
  | subst => rfl
  | apply constructor arguments => exact agree _ le_rfl
  | multiLambda arity binders body => exact agree _ le_rfl
  | collection kind elements rest => exact agree _ le_rfl

/-- Normalizing the empty block gives it back. -/
theorem normalizeWith_empty (fuel : Nat) : normalizeWith block (fuel + 1) ⟨0, []⟩ = ⟨0, []⟩ := by
  simp [normalizeWith, absorb, absorbRounds, Prenex.prune, readingOrders, keyedArrangements, inverse, orders, least,
    sortComponents, dedupReplicated]

/-- **Enough fuel settles normalizing**: three times the mass and three, for a block; three times the size and two,
for a component's parts; three times the size and four, for a named multiset's argument. -/
theorem settles : ∀ (bound : Nat),
    (∀ (form : Prenex), form.mass ≤ bound → ∀ first second, 3 * form.mass + 3 ≤ first →
      3 * form.mass + 3 ≤ second → normalizeWith block first form = normalizeWith block second form) ∧
    (∀ (component : Pattern), size component ≤ bound → ∀ first second, 3 * size component + 2 ≤ first →
      3 * size component + 2 ≤ second → recanonWith block first component = recanonWith block second component) ∧
    (∀ (argument : Pattern), size argument ≤ bound → ∀ first second, 3 * size argument + 4 ≤ first →
      3 * size argument + 4 ≤ second →
        recanonMultisetWith block first argument = recanonMultisetWith block second argument)
  | 0 => by
      refine ⟨fun form light first second enough enough' => ?_,
        fun component small => absurd small (by have := size_pos component; omega),
        fun argument small => absurd small (by have := size_pos argument; omega)⟩
      obtain ⟨count, components⟩ := form
      have countZero : count = 0 := by simp only [Prenex.mass] at light; omega
      have componentsEmpty : components = [] := by
        cases components with
        | nil => rfl
        | cons component rest =>
            have := size_pos component
            simp only [Prenex.mass, sizeList] at light
            omega
      subst countZero componentsEmpty
      obtain ⟨first, rfl⟩ : ∃ fuel, first = fuel + 1 := ⟨first - 1, by omega⟩
      obtain ⟨second, rfl⟩ : ∃ fuel, second = fuel + 1 := ⟨second - 1, by omega⟩
      rw [normalizeWith_empty, normalizeWith_empty]
  | bound + 1 => by
      obtain ⟨normalSmaller, -, multisetSmaller⟩ := settles bound
      have components : ∀ (component : Pattern), size component ≤ bound + 1 → ∀ first second,
          3 * size component + 2 ≤ first → 3 * size component + 2 ≤ second →
            recanonWith block first component = recanonWith block second component := by
        intro component small first second enough enough'
        have positive := size_pos component
        obtain ⟨first, rfl⟩ : ∃ fuel, first = fuel + 1 := ⟨first - 1, by omega⟩
        obtain ⟨second, rfl⟩ : ∃ fuel, second = fuel + 1 := ⟨second - 1, by omega⟩
        have pieces : ∀ pattern, size pattern < size component →
            Prenex.toPattern block.toBlock (normalizeWith block first (decompose block.toBlock pattern)) =
              Prenex.toPattern block.toBlock (normalizeWith block second (decompose block.toBlock pattern)) := by
          intro pattern smaller
          have light := mass_decompose (block := block.toBlock) pattern
          rw [normalSmaller _ (by omega) first second (by omega) (by omega)]
        cases component with
        | apply constructor arguments =>
            by_cases isRestrict : constructor = block.restrict
            · simp only [recanonWith, if_pos isRestrict]
            by_cases isMultiset : constructor ∈ block.multisets
            · simp only [recanonWith, if_neg isRestrict, if_pos isMultiset]
              congr 1
              refine List.map_congr_left fun argument member => ?_
              have within := size_lt_of_mem member
              simp only [size] at small enough enough'
              exact multisetSmaller argument (by omega) first second (by omega) (by omega)
            · simp only [recanonWith, if_neg isRestrict, if_neg isMultiset]
              congr 1
              refine List.map_congr_left fun argument member => ?_
              have within := size_lt_of_mem member
              refine canonArgument_congr fun pattern small' => pieces pattern ?_
              simp only [size]
              omega
        | lambda binder body =>
            simp only [recanonWith]
            rw [pieces body (by simp [size])]
        | multiLambda arity binders body =>
            simp only [recanonWith]
            rw [pieces body (by simp [size])]
        | collection kind elements rest =>
            simp only [recanonWith]
            congr 1
            refine List.map_congr_left fun element member => pieces element ?_
            have := size_lt_of_mem member
            simp only [size]
            omega
        | bvar => rfl
        | fvar => rfl
        | subst => rfl
      have normals : ∀ (form : Prenex), form.mass ≤ bound + 1 → ∀ first second, 3 * form.mass + 3 ≤ first →
          3 * form.mass + 3 ≤ second → normalizeWith block first form = normalizeWith block second form := by
        intro form light first second enough enough'
        obtain ⟨first, rfl⟩ : ∃ fuel, first = fuel + 1 := ⟨first - 1, by omega⟩
        obtain ⟨second, rfl⟩ : ∃ fuel, second = fuel + 1 := ⟨second - 1, by omega⟩
        simp only [normalizeWith]
        rw [absorb_congr (first := fun pattern => Prenex.toPattern block.toBlock (normalizeWith block first
            (decompose block.toBlock pattern))) (second := fun pattern => Prenex.toPattern block.toBlock
            (normalizeWith block second (decompose block.toBlock pattern))) fun pattern small => by
          have := mass_decompose (block := block.toBlock) pattern
          rw [normalSmaller _ (by omega) first second (by omega) (by omega)]]
        congr 2
        refine List.map_congr_left fun order _ => ?_
        congr 2
        refine List.map_congr_left fun component member => ?_
        have bounded := absorb_components_size component member
        simp only [Prenex.mass] at light enough enough'
        exact components _ (by rw [size_rename]; omega) first second (by rw [size_rename]; omega)
          (by rw [size_rename]; omega)
      refine ⟨normals, components, ?_⟩
      intro argument small first second enough enough'
      have positive := size_pos argument
      obtain ⟨first, rfl⟩ : ∃ fuel, first = fuel + 1 := ⟨first - 1, by omega⟩
      obtain ⟨second, rfl⟩ : ∃ fuel, second = fuel + 1 := ⟨second - 1, by omega⟩
      have whole := mass_decompose (block := block.toBlock) argument
      cases argument with
      | collection kind elements rest =>
          cases rest with
          | some name =>
              simp only [recanonMultisetWith]
              congr 1
              refine List.map_congr_left fun element member => ?_
              have within := size_lt_of_mem member
              have light := mass_decompose (block := block.toBlock) element
              simp only [size] at small enough enough'
              rw [normalSmaller _ (by omega) first second (by omega) (by omega)]
          | none =>
              simp only [recanonMultisetWith]
              rw [normals _ (by omega) first second (by omega) (by omega)]
      | subst => rfl
      | apply constructor arguments =>
          simp only [recanonMultisetWith]
          rw [normals _ (by omega) first second (by omega) (by omega)]
      | bvar =>
          simp only [recanonMultisetWith]
          rw [normals _ (by omega) first second (by omega) (by omega)]
      | fvar =>
          simp only [recanonMultisetWith]
          rw [normals _ (by omega) first second (by omega) (by omega)]
      | lambda =>
          simp only [recanonMultisetWith]
          rw [normals _ (by omega) first second (by omega) (by omega)]
      | multiLambda =>
          simp only [recanonMultisetWith]
          rw [normals _ (by omega) first second (by omega) (by omega)]

/-- **A component's parts read again, with fuel that settles it.** -/
def recanon (block : ReplicationBlock) (component : Pattern) : Pattern :=
  recanonWith block (3 * size component + 2) component

theorem recanonWith_settled {component : Pattern} {fuel : Nat} (enough : 3 * size component + 2 ≤ fuel) :
    recanonWith block fuel component = recanon block component :=
  (settles (size component)).2.1 component le_rfl _ _ enough le_rfl

theorem normalizeWith_settled {form : Prenex} {fuel : Nat} (enough : 3 * form.mass + 3 ≤ fuel) :
    normalizeWith block fuel form = normal block form := by
  have heavier := mass_le_size_toPattern (block := block.toBlock) form
  exact (settles form.mass).1 form le_rfl _ _ enough (by omega)

/-- **The canonical form of a block, unfolded**: its copies absorbed, as the canonical forms of lighter patterns
tell them, then its least reading, each component's parts read again. -/
theorem normal_unfold (form : Prenex) :
    normal block form =
      ⟨(absorb block (canonicalOf block) form).count,
        least ((readingOrders block (absorb block (canonicalOf block) form)).map fun order =>
          dedupReplicated block (sortComponents ((absorb block (canonicalOf block) form).components.map
            fun component => recanon block
              (rename (Prenex.permute (absorb block (canonicalOf block) form).count order) component))))⟩ := by
  have heavier := mass_le_size_toPattern (block := block.toBlock) form
  set fuel := 3 * size (form.toPattern block.toBlock) + 2 with fuelIs
  have unfolded : normal block form = normalizeWith block (fuel + 1) form := rfl
  rw [unfolded]
  simp only [normalizeWith]
  rw [absorb_congr (second := canonicalOf block) fun pattern small => by
    have light := mass_decompose (block := block.toBlock) pattern
    unfold canonicalOf
    rw [normalizeWith_settled (by simp only [Prenex.mass] at heavier small light ⊢; omega)]]
  congr 2
  refine List.map_congr_left fun order _ => ?_
  congr 2
  refine List.map_congr_left fun component member => ?_
  have bounded := absorb_components_size component member
  apply recanonWith_settled
  rw [size_rename]
  simp only [Prenex.mass] at heavier
  omega

end Absorb

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
