import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSoundness
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationOrders

/-!
# The canonical form with replication is sound

Every term is related to its canonical form with replication by a chain of laws through terms of its sort
(`canonR_sound`).

- **Normalizing a block is sound at every fuel** (`normal_sound_at`): its copies are absorbed (`absorb_sound`), its
  restrictions reordered, its components' parts read again (`recanonWith`) and sorted, and one of each replicated
  component kept (`dedup_sound`).
- **The canonical block is sound constructor by constructor** (`canonP_sound`): a restriction closes a sound block,
  a replication unfolds into its replicated molecules (`replicatedOf_sound`), a bag joins sound blocks, and every
  other term keeps its constructor with sound parts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax

variable {block : ReplicationBlock}

/-! ## Normalizing a block of unreplicated components -/

theorem absorbOnce_unreplicated {canonical : Pattern → Pattern} {form : Prenex}
    (unreplicated : ∀ component ∈ form.components, isReplicated block component = false) :
    absorbOnce block canonical form = none := by
  unfold absorbOnce
  rw [List.findSome?_eq_none_iff]
  intro position _
  rcases lookup : (form.components[position]? : Option Pattern) with _ | component
  · rfl
  · have notReplicated := unreplicated component (List.mem_of_getElem? lookup)
    match component, notReplicated with
    | .apply label [argument], notReplicated =>
        have different : label ≠ block.replicate := by
          intro same
          simp [isReplicated, same] at notReplicated
        simp [different]
    | .apply _ [], _ => rfl
    | .apply _ (_ :: _ :: _), _ => rfl
    | .bvar _, _ => rfl
    | .fvar _, _ => rfl
    | .lambda _ _, _ => rfl
    | .multiLambda _ _ _, _ => rfl
    | .subst _ _, _ => rfl
    | .collection _ _ _, _ => rfl

theorem absorbRounds_unreplicated {canonical : Pattern → Pattern} {form : Prenex}
    (unreplicated : ∀ component ∈ form.components, isReplicated block component = false) :
    ∀ rounds, absorbRounds block canonical rounds form = form
  | 0 => rfl
  | _ + 1 => by simp only [absorbRounds, absorbOnce_unreplicated unreplicated]

/-- A block of no restriction has none to drop. -/
theorem prune_zero (components : List Pattern) : (Prenex.mk 0 components).prune = ⟨0, components⟩ := by
  have identity : Prenex.groupIndex 0 [] = id := by
    funext index
    simp [Prenex.groupIndex]
  have renamedId : rename id = id := by
    funext pattern
    exact rename_id pattern
  simp only [Prenex.prune, List.range_zero, List.filter_nil, List.length_nil, identity, renamedId, List.map_id]

theorem absorb_unreplicated {canonical : Pattern → Pattern} {components : List Pattern}
    (unreplicated : ∀ component ∈ components, isReplicated block component = false) :
    absorb block canonical ⟨0, components⟩ = ⟨0, components⟩ := by
  unfold absorb
  rw [absorbRounds_unreplicated unreplicated, prune_zero]

theorem dedupReplicated_unreplicated : ∀ {components : List Pattern},
    (∀ component ∈ components, isReplicated block component = false) → dedupReplicated block components = components
  | [], _ => rfl
  | component :: rest, unreplicated => by
      have restUnreplicated : ∀ other ∈ rest, isReplicated block other = false :=
        fun other member => unreplicated other (List.mem_cons_of_mem _ member)
      simp [dedupReplicated, unreplicated component List.mem_cons_self,
        dedupReplicated_unreplicated restUnreplicated]

/-- Reading a component's parts again keeps it replicated or not. -/
theorem isReplicated_recanonWith (fuel : Nat) (component : Pattern) :
    isReplicated block (recanonWith block fuel component) = isReplicated block component := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases component with
      | apply constructor arguments =>
          by_cases isRestrict : constructor = block.restrict
          · simp only [recanonWith, if_pos isRestrict]
          by_cases isMultiset : constructor ∈ block.multisets
          · simp only [recanonWith, if_neg isRestrict, if_pos isMultiset]
            rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;> rfl
          · simp only [recanonWith, if_neg isRestrict, if_neg isMultiset]
            rcases arguments with _ | ⟨first, _ | ⟨second, rest⟩⟩ <;> rfl
      | bvar => rfl
      | fvar => rfl
      | lambda => rfl
      | multiLambda => rfl
      | subst => rfl
      | collection => rfl

/-- **A block of unreplicated components and no restrictions normalizes to its components, their parts read again,
sorted.** -/
theorem normalizeWith_unreplicated (fuel : Nat) {components : List Pattern}
    (unreplicated : ∀ component ∈ components, isReplicated block component = false) :
    normalizeWith block (fuel + 1) ⟨0, components⟩ =
      ⟨0, sortComponents (components.map (recanonWith block fuel))⟩ := by
  have identity : Prenex.permute 0 [] = id := permute_range 0
  have absorbed := absorb_unreplicated (canonical := fun pattern => Prenex.toPattern block.toBlock
    (normalizeWith block fuel (decompose block.toBlock pattern))) unreplicated
  simp only [normalizeWith, absorbed, readingOrders_zero, List.map_cons, List.map_nil, identity, rename_id,
    least, List.foldl_nil]
  congr 1
  apply dedupReplicated_unreplicated
  intro component member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp ((List.perm_insertionSort _ _).subset member)
  rw [isReplicated_recanonWith]
  exact unreplicated original originalMember

/-- **A single unreplicated component is normal once its parts are read again.** -/
theorem normalizeWith_atom (fuel : Nat) {term : Pattern} (notReplicated : isReplicated block term = false) :
    normalizeWith block (fuel + 1) (Prenex.atom term) = Prenex.atom (recanonWith block fuel term) := by
  rw [Prenex.atom, normalizeWith_unreplicated fuel (fun component member => by
    rw [List.mem_singleton.mp member]; exact notReplicated)]
  rfl

section Typed

variable {language : LanguageDef} [laws : ReplicationSignature language block]

open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext hasType_apply_inversion
  hasType_collection_inversion CollectionTypeOccurs UsesBareCollection ElementsHaveType)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (DerivedInstance)

/-- A replicated term is a process. -/
theorem isReplicated_proc {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {sort : String}
    (typed : HasType language free bound term (.base sort)) (replicated : isReplicated block term = true) :
    sort = block.proc := by
  obtain ⟨argument, rfl⟩ := eq_of_isReplicated replicated
  obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
  simp only [TypeExpr.base.injEq] at typeIs
  exact typeIs.trans (laws.replicateShape rule member labelIs.symm).1

/-- A term of another sort than processes is not replicated. -/
theorem notReplicated_of_other {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {sort : String}
    (typed : HasType language free bound term (.base sort)) (other : sort ≠ block.proc) :
    isReplicated block term = false := by
  cases replicated : isReplicated block term with
  | false => rfl
  | true => exact absurd (isReplicated_proc typed replicated) other

/-! ## Normalizing is sound at every fuel -/

/-- **Normalizing at a fuel is sound**: a block of processes is related to its normal form, a block of processes. -/
def NormalSound (language : LanguageDef) (block : ReplicationBlock) (fuel : Nat) : Prop :=
  ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {form : Prenex},
    Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components →
    Members language block.toBlock free
        (List.replicate (normalizeWith block fuel form).count (TypeExpr.base block.name) ++ bound)
        (normalizeWith block fuel form).components ∧
      ProcEquiv language block.toBlock free bound (form.toPattern block.toBlock)
        ((normalizeWith block fuel form).toPattern block.toBlock)

/-- **Reading a component's parts again at a fuel is sound**, at every sort. -/
def RecanonSound (language : LanguageDef) (block : ReplicationBlock) (fuel : Nat) : Prop :=
  ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {component : Pattern}
    {sort : String}, HasType language free bound component (.base sort) →
    HasType language free bound (recanonWith block fuel component) (.base sort) ∧
      SortedEquiv language free bound (.base sort) component (recanonWith block fuel component)

/-- **Reading a named multiset's argument again at a fuel is sound.** -/
def RecanonMultisetSound (language : LanguageDef) (block : ReplicationBlock) (fuel : Nat) : Prop :=
  ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {argument : Pattern} {sort : String},
    sort ≠ block.proc →
    (∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
      CollectionTypeOccurs .hashBag (.base sort) parameter.typeExpr) →
    HasType language free bound argument (.collection .hashBag (.base sort)) →
    HasType language free bound (recanonMultisetWith block fuel argument) (.collection .hashBag (.base sort)) ∧
      SortedEquiv language free bound (.collection .hashBag (.base sort)) argument
        (recanonMultisetWith block fuel argument)

/-- **A block of terms of another sort, normalized at a fuel and read back as a multiset, is sound.** -/
def GuardSound (language : LanguageDef) (block : ReplicationBlock) (fuel : Nat) : Prop :=
  ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {elements : List Pattern}
    {sort : String}, sort ≠ block.proc →
    (∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
      CollectionTypeOccurs .hashBag (.base sort) parameter.typeExpr) →
    (∀ element ∈ elements, HasType language free bound element (.base sort)) →
    HasType language free bound (multisetOf block.toBlock (normalizeWith block fuel ⟨0, elements⟩))
        (.collection .hashBag (.base sort)) ∧
      SortedEquiv language free bound (.collection .hashBag (.base sort)) (.collection .hashBag elements none)
        (multisetOf block.toBlock (normalizeWith block fuel ⟨0, elements⟩))

/-- **The canonical pattern of a term read as a block, at a fuel, is sound**, at every sort. -/
def PatternSound (language : LanguageDef) (block : ReplicationBlock) (fuel : Nat) : Prop :=
  ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {term : Pattern} {sort : String},
    HasType language free bound term (.base sort) →
    HasType language free bound
        ((normalizeWith block fuel (decompose block.toBlock term)).toPattern block.toBlock) (.base sort) ∧
      SortedEquiv language free bound (.base sort) term
        ((normalizeWith block fuel (decompose block.toBlock term)).toPattern block.toBlock)

/-- **Normalizing at the next fuel is sound**, given the canonical patterns and the components at this fuel. -/
theorem normal_step {fuel : Nat} (patterns : PatternSound language block fuel)
    (components : RecanonSound language block fuel) : NormalSound language block (fuel + 1) := by
  intro free bound context form members
  obtain ⟨absorbedMembers, absorbedEquivalent⟩ := absorb_sound (canonical := fun pattern =>
      (normalizeWith block fuel (decompose block.toBlock pattern)).toPattern block.toBlock) context
    (fun base => patterns base) members
  simp only [normalizeWith]
  generalize absorb block (fun pattern => (normalizeWith block fuel (decompose block.toBlock pattern)).toPattern
    block.toBlock) form = absorbed at absorbedMembers absorbedEquivalent ⊢
  obtain ⟨count, parts⟩ := absorbed
  simp only at absorbedMembers ⊢
  have nonempty : ((readingOrders block ⟨count, parts⟩).map fun order => dedupReplicated block (sortComponents
      (parts.map fun component => recanonWith block fuel (rename (Prenex.permute count order) component)))) ≠ [] := by
    simpa using readingOrders_ne_nil (block := block) ⟨count, parts⟩
  obtain ⟨order, orderMember, chosen⟩ := List.mem_map.mp (least_mem nonempty)
  rw [← chosen]
  obtain ⟨renamedMembers, renamed⟩ :=
    block_reorder_equivalent (block := block.toBlock)
      (orders_reorders _ order (orders_complete _ _ (readingOrders_isOrder orderMember))) absorbedMembers
  generalize renamedIs : parts.map (rename (Prenex.permute count order)) = renamedList at renamedMembers renamed
  have mapped : parts.map (fun component => recanonWith block fuel (rename (Prenex.permute count order) component)) =
      renamedList.map (recanonWith block fuel) := by
    rw [← renamedIs, List.map_map]
    rfl
  rw [mapped]
  have pieces : ∀ component ∈ renamedList,
      HasType language free (List.replicate count (.base block.name) ++ bound)
          (recanonWith block fuel component) (.base block.proc) ∧
        ProcEquiv language block.toBlock free (List.replicate count (.base block.name) ++ bound) component
          (recanonWith block fuel component) :=
    fun component member => components (context.replicate count block.name) (renamedMembers component member)
  have canonMembers : Members language block.toBlock free (List.replicate count (.base block.name) ++ bound)
      (renamedList.map (recanonWith block fuel)) := by
    intro element member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (pieces original originalMember).1
  have related : List.Forall₂ (ProcEquiv language block.toBlock free (List.replicate count (.base block.name) ++ bound))
      renamedList (renamedList.map (recanonWith block fuel)) := by
    rw [List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun component member => (pieces component member).2
  have sortedPerm : (renamedList.map (recanonWith block fuel)).Perm
      (sortComponents (renamedList.map (recanonWith block fuel))) := (List.perm_insertionSort _ _).symm
  have sortedMembers : Members language block.toBlock free (List.replicate count (.base block.name) ++ bound)
      (sortComponents (renamedList.map (recanonWith block fuel))) :=
    fun element member => canonMembers element (sortedPerm.symm.subset member)
  have dedupMembers : Members language block.toBlock free (List.replicate count (.base block.name) ++ bound)
      (dedupReplicated block (sortComponents (renamedList.map (recanonWith block fuel)))) :=
    fun element member => sortedMembers element (dedupReplicated_subset _ member)
  have deduped : ProcEquiv language block.toBlock free (List.replicate count (.base block.name) ++ bound)
      (Prenex.body block.toBlock (sortComponents (renamedList.map (recanonWith block fuel))))
      (Prenex.body block.toBlock
        (dedupReplicated block (sortComponents (renamedList.map (recanonWith block fuel))))) :=
    .trans _ _ _ (.symm _ _ (bag_body_equivalent sortedMembers))
      (.trans _ _ _ (dedup_sound sortedMembers) (bag_body_equivalent dedupMembers))
  refine ⟨dedupMembers, ?_⟩
  exact .trans _ _ _ absorbedEquivalent (.trans _ _ _ renamed
    (.trans _ _ _ (restricts_congr count (body_congr renamedMembers related))
      (.trans _ _ _ (restricts_congr count (body_perm_equivalent canonMembers sortedPerm))
        (restricts_congr count deduped))))

/-- **A block of terms of another sort, normalized at the next fuel, is sound**, given the components at this
fuel. -/
theorem guard_step {fuel : Nat} (components : RecanonSound language block fuel) :
    GuardSound language block (fuel + 1) := by
  intro free bound context elements sort other carrier membersTyped
  rw [normalizeWith_unreplicated fuel (fun element member => notReplicated_of_other (membersTyped element member)
    other)]
  simp only [multisetOf, if_pos]
  have parts : ∀ element ∈ elements,
      HasType language free bound (recanonWith block fuel element) (.base sort) ∧
        SortedEquiv language free bound (.base sort) element (recanonWith block fuel element) :=
    fun element member => components context (membersTyped element member)
  have related : List.Forall₂ (SortedEquiv language free bound (.base sort)) elements
      (elements.map (recanonWith block fuel)) := by
    rw [List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun element member => (parts element member).2
  have canonTyped : ∀ element ∈ elements.map (recanonWith block fuel),
      HasType language free bound element (.base sort) := by
    intro element member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact (parts original originalMember).1
  have chain := elements_congr none membersTyped related [] (by simp)
  simp only [List.nil_append] at chain
  have sortedPerm : (elements.map (recanonWith block fuel)).Perm
      (sortComponents (elements.map (recanonWith block fuel))) := (List.perm_insertionSort _ _).symm
  have sortedTyped : HasType language free bound
      (.collection .hashBag (sortComponents (elements.map (recanonWith block fuel))) none)
      (.collection .hashBag (.base sort)) :=
    .collection (elementsHaveType_iff.mpr fun element member => canonTyped element (sortedPerm.symm.subset member))
  have mappedTyped : HasType language free bound (.collection .hashBag (elements.map (recanonWith block fuel)) none)
      (.collection .hashBag (.base sort)) := .collection (elementsHaveType_iff.mpr canonTyped)
  obtain ⟨rule, member, parameter, parameterMember, occurs⟩ := carrier
  have reordered := SortedEquiv.ofDerived
    (DerivedInstance.bagPerm member ⟨parameter, parameterMember, .base sort, occurs, free, bound, mappedTyped⟩
      sortedPerm) mappedTyped sortedTyped
  exact ⟨sortedTyped, .trans _ _ _ chain reordered⟩

/-- **Canonical patterns at the next fuel are sound**, given normalizing at the next fuel and the components at this
fuel. -/
theorem pattern_step {fuel : Nat} (normalized : NormalSound language block (fuel + 1))
    (components : RecanonSound language block fuel) : PatternSound language block (fuel + 1) := by
  intro free bound context term sort typed
  by_cases isProc : sort = block.proc
  · subst isProc
    obtain ⟨members, equivalent⟩ := decompose_sound (block := block.toBlock) typed
    obtain ⟨normalMembers, normalEquivalent⟩ := normalized context members
    have chain : ProcEquiv language block.toBlock free bound term
        ((normalizeWith block (fuel + 1) (decompose block.toBlock term)).toPattern block.toBlock) :=
      .trans _ _ _ equivalent normalEquivalent
    exact ⟨(SortedEquiv.typed_iff chain).mp typed, chain⟩
  · rw [decompose_other (block := block.toBlock) typed isProc,
      normalizeWith_atom fuel (notReplicated_of_other typed isProc)]
    exact components context typed

/-- **Reading parts again at the next fuel is sound**, given the canonical patterns and multisets at this fuel. -/
theorem recanon_step {fuel : Nat} (patterns : PatternSound language block fuel)
    (multisets : RecanonMultisetSound language block fuel) : RecanonSound language block (fuel + 1) := by
  intro free bound context component sort typed
  cases component with
  | bvar index => exact ⟨typed, .refl _⟩
  | fvar name => exact ⟨typed, .refl _⟩
  | subst body replacement => exact ⟨typed, .refl _⟩
  | lambda binder body => cases typed
  | multiLambda arity binders body => cases typed
  | apply constructor arguments =>
      by_cases isRestrict : constructor = block.restrict
      · simp only [recanonWith, if_pos isRestrict]
        exact ⟨typed, .refl _⟩
      by_cases isMultiset : constructor ∈ block.multisets
      · obtain ⟨rule, member, labelIs, notBare, typeIs, parameterName, elementSort, argument, params, other,
          rfl, argumentTyped⟩ := multiset_argument (block := block.toBlock) typed isMultiset
        have carrier : ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
            CollectionTypeOccurs .hashBag (.base elementSort) parameter.typeExpr :=
          ⟨rule, member, _, by rw [params]; exact List.mem_singleton_self _, .here⟩
        obtain ⟨canonTyped, chain⟩ := multisets context other carrier argumentTyped
        simp only [recanonWith, if_neg isRestrict, if_pos isMultiset, List.map_cons, List.map_nil]
        have rebuild : ∀ filling, HasType language free bound filling (.collection .hashBag (.base elementSort)) →
            HasType language free bound (OneHoleContext.fill (.apply constructor [] .hole []) filling)
              (.base sort) := by
          intro filling fillingTyped
          have built := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor (arguments := [filling])
            member notBare (by rw [params]; exact .cons trivial rfl fillingTyped .nil)
          rw [labelIs, ← typeIs] at built
          simpa [OneHoleContext.fill] using built
        have filled := SortedEquiv.fill (.apply constructor [] .hole []) rebuild chain
        simp only [OneHoleContext.fill, List.nil_append] at filled
        exact ⟨by simpa [OneHoleContext.fill] using rebuild _ canonTyped, filled⟩
      · obtain ⟨rule, member, labelIs, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
        obtain ⟨canonArguments, chain⟩ := arguments_sound (block := block.toBlock)
          (fun context' => patterns context') context member
          notBare (by rw [← labelIs]; exact isMultiset) arguments (before := []) (beforeParameters := []) rfl .nil
          argumentsTyped
        have rebuilt := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor member notBare canonArguments
        simp only [List.nil_append] at chain
        rw [← labelIs, ← typeIs] at rebuilt chain
        simp only [recanonWith, if_neg isRestrict, if_neg isMultiset]
        exact ⟨rebuilt, chain⟩
  | collection kind elements rest =>
      rcases hasType_collection_inversion typed with
        ⟨_, typeIs, _⟩ | ⟨rule, _, _, member, shape, typeIs, elementsTyped⟩
      · cases typeIs
      · obtain ⟨rfl, rfl, category⟩ := laws.bare_shape member shape
        have elementMembers : Members language block.toBlock free bound elements :=
          fun element member => elementsHaveType_iff.mp elementsTyped element member
        have parts : ∀ element ∈ elements,
            HasType language free bound
                ((normalizeWith block fuel (decompose block.toBlock element)).toPattern block.toBlock)
                (.base block.proc) ∧
              ProcEquiv language block.toBlock free bound element
                ((normalizeWith block fuel (decompose block.toBlock element)).toPattern block.toBlock) :=
          fun element member => patterns context (elementMembers element member)
        have canonTyped : ElementsHaveType language free bound (elements.map fun element =>
            (normalizeWith block fuel (decompose block.toBlock element)).toPattern block.toBlock)
            (.base block.proc) := by
          refine elementsHaveType_iff.mpr ?_
          intro element member
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (parts original originalMember).1
        have related : List.Forall₂ (ProcEquiv language block.toBlock free bound) elements
            (elements.map fun element =>
              (normalizeWith block fuel (decompose block.toBlock element)).toPattern block.toBlock) := by
          rw [List.forall₂_map_right_iff]
          exact List.forall₂_same.mpr fun element member => (parts element member).2
        have rebuilt := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.collectionConstructor (rest := rest)
          member shape canonTyped
        have chain := collection_congr rest elementMembers related [] Members.nil
        simp only [List.nil_append] at chain
        rw [category] at rebuilt typeIs
        rw [typeIs]
        simp only [recanonWith]
        exact ⟨rebuilt, chain⟩

/-- **Reading a named multiset's argument again at the next fuel is sound**, given the canonical patterns and the
blocks of other sorts at this fuel. -/
theorem recanonMultiset_step {fuel : Nat} (patterns : PatternSound language block fuel)
    (guards : GuardSound language block fuel) : RecanonMultisetSound language block (fuel + 1) := by
  intro free bound context argument sort other carrier typed
  cases argument with
  | bvar index =>
      cases typed with
      | bvar lookup =>
          obtain ⟨sort', isBase⟩ := context.bound _ (List.mem_of_getElem? lookup)
          cases isBase
  | fvar name =>
      cases typed with
      | fvar lookup =>
          obtain ⟨sort', isBase⟩ := context.free name _ lookup
          cases isBase
  | apply constructor arguments =>
      obtain ⟨_, _, _, _, typeIs, _⟩ := hasType_apply_inversion typed
      cases typeIs
  | lambda binder body => cases typed
  | multiLambda arity binders body => cases typed
  | subst body replacement => exact ⟨typed, .refl _⟩
  | collection kind elements rest =>
      rcases hasType_collection_inversion typed with
        ⟨elementType, typeIs, elementsTyped⟩ | ⟨rule, -, -, -, -, typeIs, -⟩
      swap
      · cases typeIs
      simp only [TypeExpr.collection.injEq] at typeIs
      obtain ⟨rfl, rfl⟩ := typeIs
      have membersTyped : ∀ element ∈ elements, HasType language free bound element (.base sort) :=
        fun element member => elementsHaveType_iff.mp elementsTyped element member
      cases rest with
      | some name =>
          have parts : ∀ element ∈ elements,
              HasType language free bound
                  ((normalizeWith block fuel (decompose block.toBlock element)).toPattern block.toBlock)
                  (.base sort) ∧
                SortedEquiv language free bound (.base sort) element
                  ((normalizeWith block fuel (decompose block.toBlock element)).toPattern block.toBlock) :=
            fun element member => patterns context (membersTyped element member)
          have related : List.Forall₂ (SortedEquiv language free bound (.base sort)) elements
              (elements.map fun element =>
                (normalizeWith block fuel (decompose block.toBlock element)).toPattern block.toBlock) := by
            rw [List.forall₂_map_right_iff]
            exact List.forall₂_same.mpr fun element member => (parts element member).2
          have chain := elements_congr (some name) membersTyped related [] (by simp)
          simp only [List.nil_append] at chain
          simp only [recanonMultisetWith]
          refine ⟨.collection (elementsHaveType_iff.mpr fun element member => ?_), chain⟩
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact (parts original originalMember).1
      | none =>
          have plainAtoms : ∀ element ∈ elements, decompose block.toBlock element = Prenex.atom element :=
            fun element member => decompose_other (block := block.toBlock) (membersTyped element member) other
          have formIs : decompose block.toBlock (.collection .hashBag elements none) = ⟨0, elements⟩ := by
            rw [decompose_bag, decomposeList_atoms plainAtoms]
          simp only [recanonMultisetWith, formIs]
          exact guards context other carrier membersTyped

/-! ## Soundness at every fuel -/

/-- **Every stage of normalizing is sound at a fuel.** -/
def AllSound (language : LanguageDef) (block : ReplicationBlock) (fuel : Nat) : Prop :=
  NormalSound language block fuel ∧ RecanonSound language block fuel ∧ RecanonMultisetSound language block fuel ∧
    GuardSound language block fuel ∧ PatternSound language block fuel

/-- At no fuel, nothing moves. -/
theorem sound_zero : AllSound language block 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro free bound context form members
    exact ⟨members, .refl _⟩
  · intro free bound context component sort typed
    exact ⟨typed, .refl _⟩
  · intro free bound context argument sort other carrier typed
    exact ⟨typed, .refl _⟩
  · intro free bound context elements sort other carrier membersTyped
    simp only [normalizeWith, multisetOf, if_pos]
    exact ⟨.collection (elementsHaveType_iff.mpr membersTyped), .refl _⟩
  · intro free bound context term sort typed
    simp only [normalizeWith]
    by_cases isProc : sort = block.proc
    · subst isProc
      obtain ⟨-, equivalent⟩ := decompose_sound (block := block.toBlock) typed
      exact ⟨(SortedEquiv.typed_iff equivalent).mp typed, equivalent⟩
    · rw [decompose_other (block := block.toBlock) typed isProc]
      exact ⟨typed, .refl _⟩

/-- **Normalizing is sound at every fuel**, with every stage it reads. -/
theorem normal_sound_at : ∀ fuel, AllSound language block fuel
  | 0 => sound_zero
  | fuel + 1 =>
      let ⟨_, components, multisets, guards, patterns⟩ := normal_sound_at fuel
      have normalized : NormalSound language block (fuel + 1) := normal_step patterns components
      ⟨normalized, recanon_step patterns multisets, recanonMultiset_step patterns guards, guard_step components,
        pattern_step normalized components⟩

/-! ## The canonical block, constructor by constructor -/

omit laws in
theorem canonsP_eq_map : ∀ (patterns : List Pattern), canonsP block patterns = patterns.map (canonP block)
  | [] => by simp [canonsP]
  | pattern :: patterns => by simp [canonsP, canonsP_eq_map patterns]

omit laws in
theorem canonP_unit : canonP block (.apply block.unit []) = Prenex.nil := by simp [canonP]

omit laws in
theorem canonP_restrict (binder : Option String) (body : Pattern) :
    canonP block (.apply block.restrict [.lambda binder body]) = normal block (canonP block body).close := by
  simp [canonP]

omit laws in
theorem canonP_replicate {argument : Pattern} (notLambda : ∀ binder body, argument ≠ .lambda binder body) :
    canonP block (.apply block.replicate [argument]) =
      normal block ⟨0, replicatedOf block (canonicalOf block) (canonP block argument)⟩ := by
  cases argument with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | _ => simp [canonP]

omit laws in
theorem canonP_bag (elements : List Pattern) :
    canonP block (.collection .hashBag elements none) =
      normal block ((canonsP block elements).foldr Prenex.par Prenex.nil) := by
  simp [canonP]

omit laws in
theorem canonP_lambda (binder : Option String) (body : Pattern) :
    canonP block (.lambda binder body) =
      Prenex.atom (.lambda binder (Prenex.toPattern block.toBlock (canonP block body))) := by
  simp [canonP]

omit laws in
/-- The pattern of a single component is the component. -/
theorem toPattern_atom (component : Pattern) : (Prenex.atom component).toPattern block.toBlock = component := rfl

omit laws in
/-- **Any other application is one component with canonical arguments.** -/
theorem canonP_apply {label : String} {arguments : List Pattern}
    (notUnit : ¬ (label = block.unit ∧ arguments = []))
    (notRestriction : ∀ binder body, ¬ (label = block.restrict ∧ arguments = [.lambda binder body]))
    (notReplicated : ∀ argument, (∀ binder body, argument ≠ .lambda binder body) →
      ¬ (label = block.replicate ∧ arguments = [argument]))
    (notEmpty : ∀ argument, (∀ binder body, argument ≠ .lambda binder body) → arguments = [argument] →
      label ∈ block.emptyUnits → canonP block argument ≠ Prenex.nil) :
    canonP block (.apply label arguments) =
      Prenex.atom (.apply label (List.zipWith (argumentOf block label) arguments (canonsP block arguments))) := by
  match arguments, notUnit, notRestriction, notReplicated, notEmpty with
  | [], notUnit, _, _, _ =>
      have different : label ≠ block.unit := fun same => notUnit ⟨same, rfl⟩
      simp [canonP, different, canonsP]
  | [.lambda binder body], _, notRestriction, _, _ =>
      have different : label ≠ block.restrict := fun same => notRestriction binder body ⟨same, rfl⟩
      simp [canonP, different, canonsP]
  | [.bvar index], _, _, notReplicated, _ =>
      have different : label ≠ block.replicate := fun same => notReplicated _ (by simp) ⟨same, rfl⟩
      simp [canonP, different, canonsP, Prenex.atom, Prenex.nil]
  | [.fvar name], _, _, notReplicated, _ =>
      have different : label ≠ block.replicate := fun same => notReplicated _ (by simp) ⟨same, rfl⟩
      simp [canonP, different, canonsP, Prenex.atom, Prenex.nil]
  | [.apply constructor inner], _, _, notReplicated, notEmpty =>
      have different : label ≠ block.replicate := fun same => notReplicated _ (by simp) ⟨same, rfl⟩
      have notNil := notEmpty _ (by simp) rfl
      simp only [canonP, different, if_false, canonsP, List.zipWith_cons_cons, List.zipWith_nil_right]
      split_ifs with empty
      · exact absurd empty.2 (notNil empty.1)
      · rfl
  | [.multiLambda arity binders body], _, _, notReplicated, _ =>
      have different : label ≠ block.replicate := fun same => notReplicated _ (by simp) ⟨same, rfl⟩
      simp [canonP, different, canonsP, Prenex.atom, Prenex.nil]
  | [.subst body replacement], _, _, notReplicated, _ =>
      have different : label ≠ block.replicate := fun same => notReplicated _ (by simp) ⟨same, rfl⟩
      simp [canonP, different, canonsP, Prenex.atom, Prenex.nil]
  | [.collection kind elements rest], _, _, notReplicated, notEmpty =>
      have different : label ≠ block.replicate := fun same => notReplicated _ (by simp) ⟨same, rfl⟩
      have notNil := notEmpty _ (by simp) rfl
      simp only [canonP, different, if_false, canonsP, List.zipWith_cons_cons, List.zipWith_nil_right]
      split_ifs with empty
      · exact absurd empty.2 (notNil empty.1)
      · rfl
  | _ :: _ :: _, _, _, _, _ => simp [canonP]

omit laws in
/-- A list zipped with its own image is the image of the zipped function. -/
theorem zipWith_map_self {α β γ : Type} (combine : α → β → γ) (image : α → β) (result : α → γ) :
    ∀ (list : List α), (∀ element ∈ list, combine element (image element) = result element) →
      List.zipWith combine list (list.map image) = list.map result
  | [], _ => rfl
  | element :: list, pointwise => by
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [pointwise element List.mem_cons_self,
        zipWith_map_self combine image result list fun other member => pointwise other (List.mem_cons_of_mem _ member)]

omit laws in
/-- Members that are single components side by side are a block of no restriction. -/
theorem foldr_par_atoms : ∀ (components : List Pattern),
    (components.map Prenex.atom).foldr Prenex.par Prenex.nil = ⟨0, components⟩
  | [] => rfl
  | component :: components => by
      rw [List.map_cons, List.foldr_cons, foldr_par_atoms components]
      simp [Prenex.par, Prenex.atom, decomposeList_atoms.map_liftBVars_zero',
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

/-- **A term of another sort than processes is one component**, its canonical pattern. -/
theorem canonP_other {free : FreeTypeContext} {bound : List TypeExpr} {term : Pattern} {sort : String}
    (typed : HasType language free bound term (.base sort)) (other : sort ≠ block.proc) :
    canonP block term = Prenex.atom (canonR block term) := by
  suffices single : ∃ component, canonP block term = Prenex.atom component by
    obtain ⟨component, isAtom⟩ := single
    rw [canonR, isAtom, toPattern_atom]
  cases term with
  | apply label arguments =>
      obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      have notProc : rule.category ≠ block.proc := fun isProc => other (typeIs.trans isProc)
      refine ⟨_, canonP_apply ?_ ?_ ?_ ?_⟩
      · rintro ⟨rfl, rfl⟩
        exact notProc (laws.unitShape rule member labelIs.symm)
      · rintro binder body ⟨rfl, rfl⟩
        exact notProc (laws.restrictShape rule member labelIs.symm).1
      · rintro argument - ⟨rfl, rfl⟩
        exact notProc (laws.replicateShape rule member labelIs.symm).1
      · rintro argument - rfl listed -
        exact notProc ((laws.emptyUnitShape label listed).2 rule member labelIs.symm)
  | collection kind elements rest => exact absurd (laws.bag_members typed).2.1 other
  | lambda binder body => cases typed
  | multiLambda arity binders body => cases typed
  | bvar index => exact ⟨.bvar index, by simp [canonP]⟩
  | fvar name => exact ⟨.fvar name, by simp [canonP]⟩
  | subst body replacement => exact ⟨.subst body replacement, by simp [canonP]⟩

/-- **What the canonical block of a term owes**, at every base context: at a base sort, its pattern has the sort and
is equivalent; at the process sort, its components are processes; as a named multiset's argument, the canonical
argument is equivalent. -/
structure Sound₀ (language : LanguageDef) (block : ReplicationBlock) (term : Pattern) : Prop where
  base : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort : String},
    HasType language free bound term (.base sort) →
    HasType language free bound (canonR block term) (.base sort) ∧
      SortedEquiv language free bound (.base sort) term (canonR block term)
  members : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound →
    HasType language free bound term (.base block.proc) →
    Members language block.toBlock free (List.replicate (canonP block term).count (TypeExpr.base block.name) ++ bound)
      (canonP block term).components
  multiset : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort label : String},
    label ∈ block.multisets → sort ≠ block.proc →
    (∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
      CollectionTypeOccurs .hashBag (.base sort) parameter.typeExpr) →
    HasType language free bound term (.collection .hashBag (.base sort)) →
    HasType language free bound (argumentOf block label term (canonP block term)) (.collection .hashBag (.base sort)) ∧
      SortedEquiv language free bound (.collection .hashBag (.base sort)) term
        (argumentOf block label term (canonP block term))

omit laws in
/-- A single component owes its own typing as the block's one member. -/
theorem atom_members {free : FreeTypeContext} {bound : List TypeExpr} {term component : Pattern}
    (isAtom : canonP block term = Prenex.atom component)
    (typed : HasType language free bound (canonR block term) (.base block.proc)) :
    Members language block.toBlock free (List.replicate (canonP block term).count (TypeExpr.base block.name) ++ bound)
      (canonP block term).components := by
  rw [canonR, isAtom, toPattern_atom] at typed
  rw [isAtom]
  intro element member
  simp only [Prenex.atom, List.mem_singleton] at member
  subst member
  simpa [Prenex.atom] using typed

/-- An application is never of a collection type. -/
theorem apply_typed_not_collection {free : FreeTypeContext} {bound : List TypeExpr} {label : String}
    {arguments : List Pattern} {sort : String}
    (typed : HasType language free bound (.apply label arguments) (.collection .hashBag (.base sort))) : False := by
  obtain ⟨_, _, _, _, typeIs, _⟩ := hasType_apply_inversion typed
  cases typeIs

/-- **The canonical form of a normalized block, at its settled fuel, is sound.** -/
theorem normal_sound {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {form : Prenex}
    (members : Members language block.toBlock free (List.replicate form.count (TypeExpr.base block.name) ++ bound)
      form.components) :
    Members language block.toBlock free
        (List.replicate (normal block form).count (TypeExpr.base block.name) ++ bound) (normal block form).components ∧
      ProcEquiv language block.toBlock free bound (form.toPattern block.toBlock)
        ((normal block form).toPattern block.toBlock) :=
  (normal_sound_at _).1 context members

/-- **The canonical pattern of a term with canonical parts is sound.** -/
theorem canonicalOf_sound {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {term : Pattern} {sort : String} (typed : HasType language free bound term (.base sort)) :
    HasType language free bound (canonicalOf block term) (.base sort) ∧
      SortedEquiv language free bound (.base sort) term (canonicalOf block term) :=
  (normal_sound_at _).2.2.2.2 context typed

omit laws in
theorem unit_sound : Sound₀ language block (.apply block.unit []) where
  base := by
    intro free bound context sort typed
    have isUnit : canonR block (.apply block.unit []) = .apply block.unit [] := by
      simp [canonR, canonP_unit, Prenex.toPattern, Prenex.restricts, Prenex.body, Prenex.nil]
    rw [isUnit]
    exact ⟨typed, .refl _⟩
  members := by
    intro free bound context typed element member
    simp [canonP_unit, Prenex.nil] at member
  multiset := by
    intro free bound context sort label _ _ _ typed
    exact (apply_typed_not_collection typed).elim

theorem restriction_sound {binder : Option String} {body : Pattern} (bodySound : Sound₀ language block body) :
    Sound₀ language block (.apply block.restrict [.lambda binder body]) where
  base := by
    intro free bound context sort typed
    obtain ⟨bodyTyped, typeIs, rfl⟩ := laws.restriction_typed typed
    simp only [TypeExpr.base.injEq] at typeIs
    subst typeIs
    have members := bodySound.members (context.cons block.name) bodyTyped
    have bodyEquivalent := (bodySound.base (context.cons block.name) bodyTyped).2
    obtain ⟨closedMembers, closed⟩ := close_sound (block := block.toBlock) members
    obtain ⟨-, normalEquivalent⟩ := normal_sound context closedMembers
    have chain : ProcEquiv language block.toBlock free bound (.apply block.restrict [.lambda none body])
        (canonR block (.apply block.restrict [.lambda none body])) := by
      rw [canonR, canonP_restrict]
      exact .trans _ _ _ (restrict_fill bodyEquivalent) (.trans _ _ _ closed normalEquivalent)
    exact ⟨(SortedEquiv.typed_iff chain).mp typed, chain⟩
  members := by
    intro free bound context typed
    obtain ⟨bodyTyped, -, rfl⟩ := laws.restriction_typed typed
    have members := bodySound.members (context.cons block.name) bodyTyped
    obtain ⟨closedMembers, -⟩ := close_sound (block := block.toBlock) members
    rw [canonP_restrict]
    exact (normal_sound context closedMembers).1
  multiset := by
    intro free bound context sort label _ _ _ typed
    exact (apply_typed_not_collection typed).elim

theorem replicate_sound {argument : Pattern} (notLambda : ∀ binder body, argument ≠ .lambda binder body)
    (argumentSound : Sound₀ language block argument) :
    Sound₀ language block (.apply block.replicate [argument]) := by
  have typing : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort : String},
      HasType language free bound (.apply block.replicate [argument]) (.base sort) →
      sort = block.proc ∧
        Members language block.toBlock free
          (List.replicate (canonP block (.apply block.replicate [argument])).count (TypeExpr.base block.name) ++ bound)
          (canonP block (.apply block.replicate [argument])).components ∧
        ProcEquiv language block.toBlock free bound (.apply block.replicate [argument])
          (canonR block (.apply block.replicate [argument])) := by
    intro free bound context sort typed
    obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
    simp only [TypeExpr.base.injEq] at typeIs
    have isProc : sort = block.proc := typeIs.trans (laws.replicateShape rule member labelIs.symm).1
    subst isProc
    have argumentTyped := replicate_argument_typed typed
    have innerMembers := argumentSound.members context argumentTyped
    have innerEquivalent := (argumentSound.base context argumentTyped).2
    have innerTyped := (SortedEquiv.typed_iff innerEquivalent).mp argumentTyped
    have expanded := replicatedOf_sound (canonical := canonicalOf block)
      (fun typed' => canonicalOf_sound context typed') innerMembers
    have bagTyped := (SortedEquiv.typed_iff expanded).mp (replicate_typed innerTyped)
    have expandedMembers : Members language block.toBlock free bound
        (replicatedOf block (canonicalOf block) (canonP block argument)) :=
      elementsHaveType_iff.mp (laws.bag_members bagTyped).2.2
    have formMembers : Members language block.toBlock free
        (List.replicate (Prenex.mk 0 (replicatedOf block (canonicalOf block) (canonP block argument))).count
          (TypeExpr.base block.name) ++ bound)
        (Prenex.mk 0 (replicatedOf block (canonicalOf block) (canonP block argument))).components := by
      simpa using expandedMembers
    obtain ⟨normalMembers, normalEquivalent⟩ := normal_sound context formMembers
    have unbag := bag_body_equivalent (block := block.toBlock) expandedMembers
    refine ⟨rfl, ?_, ?_⟩
    · rw [canonP_replicate notLambda]
      exact normalMembers
    · rw [canonR, canonP_replicate notLambda]
      exact .trans _ _ _ (replicate_fill innerEquivalent) (.trans _ _ _ expanded (.trans _ _ _ unbag normalEquivalent))
  refine ⟨?_, fun context typed => (typing context typed).2.1, ?_⟩
  · intro free bound context sort typed
    obtain ⟨rfl, -, chain⟩ := typing context typed
    exact ⟨(SortedEquiv.typed_iff chain).mp typed, chain⟩
  · intro free bound context sort label _ _ _ typed
    exact (apply_typed_not_collection typed).elim

omit laws in
/-- The canonical block of an empty named multiset whose empty instance is the unit is inaction. -/
theorem canonP_empty {label : String} {argument : Pattern} (listed : label ∈ block.emptyUnits)
    (notReplicate : label ≠ block.replicate) (notLambda : ∀ binder body, argument ≠ .lambda binder body)
    (empty : canonP block argument = Prenex.nil) :
    canonP block (.apply label [argument]) = Prenex.nil := by
  cases argument with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | bvar _ => simp [canonP, Prenex.atom, Prenex.nil] at empty
  | fvar _ => simp [canonP, Prenex.atom, Prenex.nil] at empty
  | multiLambda _ _ _ => simp [canonP, Prenex.atom, Prenex.nil] at empty
  | subst _ _ => simp [canonP, Prenex.atom, Prenex.nil] at empty
  | apply _ _ => simp [canonP, notReplicate, listed, empty]
  | collection _ _ _ => simp [canonP, notReplicate, listed, empty]

theorem empty_sound {label : String} {argument : Pattern} (listed : label ∈ block.emptyUnits)
    (notLambda : ∀ binder body, argument ≠ .lambda binder body) (empty : canonP block argument = Prenex.nil)
    (argumentSound : Sound₀ language block argument) : Sound₀ language block (.apply label [argument]) := by
  have isMultiset := (laws.emptyUnitShape label listed).1
  have notReplicate : label ≠ block.replicate := fun equal => laws.replicateFresh.2.2 (equal ▸ isMultiset)
  have canonical : argumentOf block label argument (canonP block argument) = .collection .hashBag [] none := by
    simp only [argumentOf, if_pos isMultiset, empty]
    cases argument with
    | collection kind elements rest =>
        cases rest with
        | some name => simp [canonP, Prenex.atom, Prenex.nil] at empty
        | none => rfl
    | subst body replacement => simp [canonP, Prenex.atom, Prenex.nil] at empty
    | _ => rfl
  have typing : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort : String},
      HasType language free bound (.apply label [argument]) (.base sort) →
      sort = block.proc ∧ ProcEquiv language block.toBlock free bound (.apply label [argument])
        (canonR block (.apply label [argument])) := by
    intro free bound context sort typed
    obtain ⟨rule, member, labelIs, notBare, typeIs, parameterName, elementSort, argument', params, other,
      argumentsIs, argumentTyped⟩ := multiset_argument (block := block.toBlock) typed isMultiset
    simp only [List.cons.injEq, and_true] at argumentsIs
    subst argumentsIs
    simp only [TypeExpr.base.injEq] at typeIs
    have isProc : sort = block.proc := typeIs.trans ((laws.emptyUnitShape label listed).2 rule member labelIs)
    subst isProc
    have carrier : ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
        CollectionTypeOccurs .hashBag (.base elementSort) parameter.typeExpr :=
      ⟨rule, member, _, by rw [params]; exact List.mem_singleton_self _, .here⟩
    obtain ⟨emptyTyped, chain⟩ := argumentSound.multiset context isMultiset other carrier argumentTyped
    rw [canonical] at emptyTyped chain
    have rebuild : ∀ filling, HasType language free bound filling (.collection .hashBag (.base elementSort)) →
        HasType language free bound (OneHoleContext.fill (.apply label [] .hole []) filling) (.base block.proc) := by
      intro filling fillingTyped
      have built := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor (arguments := [filling])
        member notBare (by rw [params]; exact .cons trivial rfl fillingTyped .nil)
      rw [labelIs, ← typeIs] at built
      simpa [OneHoleContext.fill] using built
    have filled := SortedEquiv.fill (.apply label [] .hole []) rebuild chain
    simp only [OneHoleContext.fill, List.nil_append] at filled
    have emptyApplied : HasType language free bound (.apply label [.collection .hashBag [] none]) (.base block.proc) :=
      by simpa [OneHoleContext.fill] using rebuild _ emptyTyped
    have toUnit := empty_unit_equivalent (block := block.toBlock) listed emptyApplied
    have isUnit : canonR block (.apply label [argument]) = .apply block.unit [] := by
      simp [canonR, canonP_empty listed notReplicate notLambda empty, Prenex.toPattern, Prenex.restricts, Prenex.body, Prenex.nil]
    rw [isUnit]
    exact ⟨rfl, .trans _ _ _ filled toUnit⟩
  refine ⟨?_, ?_, ?_⟩
  · intro free bound context sort typed
    obtain ⟨rfl, chain⟩ := typing context typed
    exact ⟨(SortedEquiv.typed_iff chain).mp typed, chain⟩
  · intro free bound context typed element member
    simp [canonP_empty listed notReplicate notLambda empty, Prenex.nil] at member
  · intro free bound context sort label' _ _ _ typed
    exact (apply_typed_not_collection typed).elim

theorem multisetApply_sound {label : String} {argument : Pattern} (isMultiset : label ∈ block.multisets)
    (isAtom : canonP block (.apply label [argument]) =
      Prenex.atom (.apply label [argumentOf block label argument (canonP block argument)]))
    (argumentSound : Sound₀ language block argument) : Sound₀ language block (.apply label [argument]) := by
  have baseSound : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort : String},
      HasType language free bound (.apply label [argument]) (.base sort) →
      HasType language free bound (canonR block (.apply label [argument])) (.base sort) ∧
        SortedEquiv language free bound (.base sort) (.apply label [argument]) (canonR block (.apply label [argument])) := by
    intro free bound context sort typed
    obtain ⟨rule, member, labelIs, notBare, typeIs, parameterName, elementSort, argument', params, other,
      argumentsIs, argumentTyped⟩ := multiset_argument (block := block.toBlock) typed isMultiset
    simp only [List.cons.injEq, and_true] at argumentsIs
    subst argumentsIs
    have carrier : ∃ rule ∈ language.terms, ∃ parameter ∈ rule.params,
        CollectionTypeOccurs .hashBag (.base elementSort) parameter.typeExpr :=
      ⟨rule, member, _, by rw [params]; exact List.mem_singleton_self _, .here⟩
    obtain ⟨canonTyped, chain⟩ := argumentSound.multiset context isMultiset other carrier argumentTyped
    have rebuild : ∀ filling, HasType language free bound filling (.collection .hashBag (.base elementSort)) →
        HasType language free bound (OneHoleContext.fill (.apply label [] .hole []) filling) (.base sort) := by
      intro filling fillingTyped
      have built := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor (arguments := [filling])
        member notBare (by rw [params]; exact .cons trivial rfl fillingTyped .nil)
      rw [labelIs, ← typeIs] at built
      simpa [OneHoleContext.fill] using built
    have filled := SortedEquiv.fill (.apply label [] .hole []) rebuild chain
    simp only [OneHoleContext.fill, List.nil_append] at filled
    rw [canonR, isAtom, toPattern_atom]
    exact ⟨by simpa [OneHoleContext.fill] using rebuild _ canonTyped, filled⟩
  refine ⟨baseSound, fun context typed => atom_members isAtom (baseSound context typed).1, ?_⟩
  intro free bound context sort label' _ _ _ typed
  exact (apply_typed_not_collection typed).elim

open Classical in
theorem constructor_sound {label : String} {arguments : List Pattern} (notMultiset : label ∉ block.multisets)
    (isAtom : canonP block (.apply label arguments) =
      Prenex.atom (.apply label (List.zipWith (argumentOf block label) arguments (canonsP block arguments))))
    (recurse : ∀ argument ∈ arguments, Sound₀ language block argument ∧
      ∀ binder body, argument = .lambda binder body → Sound₀ language block body) :
    Sound₀ language block (.apply label arguments) := by
  let canonical : Pattern → Pattern := fun term =>
    if ∃ argument ∈ arguments, argument = term ∨ ∃ binder, argument = .lambda binder term then canonR block term
    else term
  have mapped : List.zipWith (argumentOf block label) arguments (canonsP block arguments) =
      arguments.map (canonArgument canonical) := by
    rw [canonsP_eq_map]
    have pointwise : ∀ argument ∈ arguments,
        argumentOf block label argument (canonP block argument) = canonArgument canonical argument := by
      intro argument member
      simp only [argumentOf, if_neg notMultiset]
      cases argument with
      | lambda binder body =>
          have chosen : canonical body = canonR block body := if_pos ⟨_, member, .inr ⟨binder, rfl⟩⟩
          simp only [canonArgument, chosen, canonP_lambda, toPattern_atom, canonR]
      | bvar index => simp [canonP, canonArgument, Prenex.toPattern, Prenex.restricts, Prenex.body, Prenex.atom]
      | fvar name => simp [canonP, canonArgument, Prenex.toPattern, Prenex.restricts, Prenex.body, Prenex.atom]
      | subst body replacement =>
          simp [canonP, canonArgument, Prenex.toPattern, Prenex.restricts, Prenex.body, Prenex.atom]
      | apply constructor inner =>
          have chosen : canonical (.apply constructor inner) = canonR block (.apply constructor inner) :=
            if_pos ⟨_, member, .inl rfl⟩
          simp only [canonArgument, chosen, canonR]
      | multiLambda arity binders body =>
          have chosen : canonical (.multiLambda arity binders body) =
              canonR block (.multiLambda arity binders body) := if_pos ⟨_, member, .inl rfl⟩
          simp only [canonArgument, chosen, canonR]
      | collection kind elements rest =>
          have chosen : canonical (.collection kind elements rest) = canonR block (.collection kind elements rest) :=
            if_pos ⟨_, member, .inl rfl⟩
          simp only [canonArgument, chosen, canonR]
    exact zipWith_map_self _ _ _ arguments pointwise
  have sound : ∀ {bound : List TypeExpr} {free : FreeTypeContext}, BaseContext free bound → ∀ {term : Pattern}
      {sort : String}, HasType language free bound term (.base sort) →
      HasType language free bound (canonical term) (.base sort) ∧
        SortedEquiv language free bound (.base sort) term (canonical term) := by
    intro bound free context term sort typed
    by_cases chosen : ∃ argument ∈ arguments, argument = term ∨ ∃ binder, argument = .lambda binder term
    · have isCanon : canonical term = canonR block term := if_pos chosen
      rw [isCanon]
      obtain ⟨argument, member, rfl | ⟨binder, rfl⟩⟩ := chosen
      · exact (recurse argument member).1.base context typed
      · exact ((recurse _ member).2 binder term rfl).base context typed
    · have isSame : canonical term = term := if_neg chosen
      rw [isSame]
      exact ⟨typed, .refl _⟩
  have baseSound : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort : String},
      HasType language free bound (.apply label arguments) (.base sort) →
      HasType language free bound (canonR block (.apply label arguments)) (.base sort) ∧
        SortedEquiv language free bound (.base sort) (.apply label arguments) (canonR block (.apply label arguments)) := by
    intro free bound context sort typed
    obtain ⟨rule, member, labelIs, notBare, typeIs, argumentsTyped⟩ := hasType_apply_inversion typed
    obtain ⟨canonArguments, chain⟩ := arguments_sound (block := block.toBlock) (canonical := canonical)
      (fun context' => sound context') context member notBare (by rw [← labelIs]; exact notMultiset) arguments
      (before := []) (beforeParameters := []) rfl .nil argumentsTyped
    have rebuilt := Mettapedia.GSLT.LanguageDef.WellSorted.HasType.constructor member notBare canonArguments
    simp only [List.nil_append] at chain
    rw [← labelIs, ← typeIs] at rebuilt chain
    rw [canonR, isAtom, toPattern_atom, mapped]
    exact ⟨rebuilt, chain⟩
  refine ⟨baseSound, fun context typed => atom_members isAtom (baseSound context typed).1, ?_⟩
  intro free bound context sort label' _ _ _ typed
  exact (apply_typed_not_collection typed).elim

/-- **A bag of sound members is their canonical blocks side by side.** -/
theorem foldr_canonP_sound {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound) :
    ∀ {elements : List Pattern}, (∀ element ∈ elements, Sound₀ language block element) →
      Members language block.toBlock free bound elements →
      Members language block.toBlock free
          (List.replicate ((elements.map (canonP block)).foldr Prenex.par Prenex.nil).count
            (TypeExpr.base block.name) ++ bound)
          ((elements.map (canonP block)).foldr Prenex.par Prenex.nil).components ∧
        ProcEquiv language block.toBlock free bound (.collection .hashBag elements none)
          (((elements.map (canonP block)).foldr Prenex.par Prenex.nil).toPattern block.toBlock)
  | [], _, typed => by
      refine ⟨by simp [Prenex.nil, Members], ?_⟩
      simpa [Prenex.nil, Prenex.toPattern, Prenex.restricts] using bag_body_equivalent (block := block.toBlock) typed
  | element :: elements, sound, typed => by
      have elementTyped := typed element List.mem_cons_self
      have restTyped : Members language block.toBlock free bound elements := typed.tail
      have firstMembers := (sound element List.mem_cons_self).members context elementTyped
      have firstEquivalent : ProcEquiv language block.toBlock free bound element
          ((canonP block element).toPattern block.toBlock) := ((sound element List.mem_cons_self).base context
        elementTyped).2
      obtain ⟨secondMembers, secondEquivalent⟩ := foldr_canonP_sound context
        (fun other member => sound other (List.mem_cons_of_mem _ member)) restTyped
      simp only [List.map_cons, List.foldr_cons]
      refine ⟨par_members firstMembers secondMembers, ?_⟩
      have outer : Members language block.toBlock free bound [element, .collection .hashBag elements none] :=
        Members.cons elementTyped (Members.cons (bag_typed restTyped) Members.nil)
      have flat := laws.flatten (pre := [element]) (inner := elements) (post := []) (bag_typed outer)
      simp only [List.append_nil, List.cons_append, List.nil_append] at flat
      have firstTyped := (SortedEquiv.typed_iff firstEquivalent).mp elementTyped
      have left := bag_fill (before := []) (after := [.collection .hashBag elements none]) (rest := none) Members.nil
        (Members.cons (bag_typed restTyped) Members.nil) firstEquivalent
      have right := bag_fill (before := [((canonP block element).toPattern block.toBlock)]) (after := [])
        (rest := none) (Members.cons firstTyped Members.nil) Members.nil secondEquivalent
      simp only [List.nil_append, List.cons_append] at left right
      exact .trans _ _ _ (.symm _ _ (SortedEquiv.ofDerived flat (bag_typed outer) (bag_typed typed)))
        (.trans _ _ _ left (.trans _ _ _ right (par_equivalent firstMembers secondMembers)))

theorem bag_sound {elements : List Pattern} (recurse : ∀ element ∈ elements, Sound₀ language block element) :
    Sound₀ language block (.collection .hashBag elements none) := by
  have typing : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort : String},
      HasType language free bound (.collection .hashBag elements none) (.base sort) →
      sort = block.proc ∧
        Members language block.toBlock free
          (List.replicate (canonP block (.collection .hashBag elements none)).count (TypeExpr.base block.name) ++
            bound) (canonP block (.collection .hashBag elements none)).components ∧
        ProcEquiv language block.toBlock free bound (.collection .hashBag elements none)
          (canonR block (.collection .hashBag elements none)) := by
    intro free bound context sort typed
    obtain ⟨-, rfl, elementsTyped⟩ := laws.bag_members typed
    obtain ⟨foldMembers, foldEquivalent⟩ := foldr_canonP_sound context recurse
      (elementsHaveType_iff.mp elementsTyped)
    rw [← canonsP_eq_map] at foldMembers foldEquivalent
    obtain ⟨normalMembers, normalEquivalent⟩ := normal_sound context foldMembers
    refine ⟨rfl, ?_, ?_⟩
    · rw [canonP_bag]
      exact normalMembers
    · rw [canonR, canonP_bag]
      exact .trans _ _ _ foldEquivalent normalEquivalent
  refine ⟨?_, fun context typed => (typing context typed).2.1, ?_⟩
  · intro free bound context sort typed
    obtain ⟨rfl, -, chain⟩ := typing context typed
    exact ⟨(SortedEquiv.typed_iff chain).mp typed, chain⟩
  · intro free bound context sort label isMultiset other carrier typed
    rcases hasType_collection_inversion typed with
      ⟨elementType, typeIs, elementsTyped⟩ | ⟨rule, -, -, -, -, typeIs, -⟩
    swap
    · cases typeIs
    simp only [TypeExpr.collection.injEq, true_and] at typeIs
    subst typeIs
    have membersTyped : ∀ element ∈ elements, HasType language free bound element (.base sort) :=
      fun element member => elementsHaveType_iff.mp elementsTyped element member
    have atoms : canonsP block elements = (elements.map (canonR block)).map Prenex.atom := by
      rw [canonsP_eq_map, List.map_map]
      exact List.map_congr_left fun element member => canonP_other (membersTyped element member) other
    have parts : ∀ element ∈ elements,
        HasType language free bound (canonR block element) (.base sort) ∧
          SortedEquiv language free bound (.base sort) element (canonR block element) :=
      fun element member => (recurse element member).base context (membersTyped element member)
    have canonTyped : ∀ element ∈ elements.map (canonR block), HasType language free bound element (.base sort) := by
      intro element member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact (parts original originalMember).1
    have related : List.Forall₂ (SortedEquiv language free bound (.base sort)) elements
        (elements.map (canonR block)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun element member => (parts element member).2
    have chain := elements_congr none membersTyped related [] (by simp)
    simp only [List.nil_append] at chain
    obtain ⟨guardTyped, guardChain⟩ := (normal_sound_at
      (3 * size ((Prenex.mk 0 (elements.map (canonR block))).toPattern block.toBlock) + 3)).2.2.2.1 context other
      carrier canonTyped
    have reading : argumentOf block label (.collection .hashBag elements none)
        (canonP block (.collection .hashBag elements none)) =
        multisetOf block.toBlock (normalizeWith block
          (3 * size ((Prenex.mk 0 (elements.map (canonR block))).toPattern block.toBlock) + 3)
          ⟨0, elements.map (canonR block)⟩) := by
      simp only [argumentOf, if_pos isMultiset, canonP_bag, atoms, foldr_par_atoms, normal]
    rw [reading]
    exact ⟨guardTyped, .trans _ _ _ chain guardChain⟩

theorem collection_sound {kind : CollType} {elements : List Pattern} {rest : Option String}
    (notBag : ¬ (kind = .hashBag ∧ rest = none)) (recurse : ∀ element ∈ elements, Sound₀ language block element) :
    Sound₀ language block (.collection kind elements rest) := by
  have isAtom : canonP block (.collection kind elements rest) =
      Prenex.atom (.collection kind (elements.map (canonR block)) rest) := by
    have canonRIs : canonR block = fun term => Prenex.toPattern block.toBlock (canonP block term) := rfl
    rcases kind with _ | _ | _ <;> rcases rest with _ | name <;>
      first
        | exact absurd ⟨rfl, rfl⟩ notBag
        | simp [canonP, canonsP_eq_map, canonRIs, List.map_map, Function.comp_def]
  have baseSound : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {sort : String},
      HasType language free bound (.collection kind elements rest) (.base sort) →
      HasType language free bound (canonR block (.collection kind elements rest)) (.base sort) ∧
        SortedEquiv language free bound (.base sort) (.collection kind elements rest)
          (canonR block (.collection kind elements rest)) := by
    intro free bound context sort typed
    obtain ⟨rfl, rfl, elementsTyped⟩ := laws.bag_members typed
    have elementMembers : Members language block.toBlock free bound elements :=
      elementsHaveType_iff.mp elementsTyped
    have parts : ∀ element ∈ elements,
        HasType language free bound (canonR block element) (.base block.proc) ∧
          ProcEquiv language block.toBlock free bound element (canonR block element) :=
      fun element member => (recurse element member).base context (elementMembers element member)
    have canonMembers : Members language block.toBlock free bound (elements.map (canonR block)) := by
      intro element member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact (parts original originalMember).1
    have related : List.Forall₂ (ProcEquiv language block.toBlock free bound) elements
        (elements.map (canonR block)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun element member => (parts element member).2
    have chain := collection_congr rest elementMembers related [] Members.nil
    simp only [List.nil_append] at chain
    rw [canonR, isAtom, toPattern_atom]
    exact ⟨laws.bag_typed (rest := rest) (elementsHaveType_iff.mpr canonMembers), chain⟩
  refine ⟨baseSound, fun context typed => atom_members isAtom (baseSound context typed).1, ?_⟩
  intro free bound context sort label isMultiset other carrier typed
  rcases hasType_collection_inversion typed with
    ⟨elementType, typeIs, elementsTyped⟩ | ⟨rule, -, -, -, -, typeIs, -⟩
  swap
  · cases typeIs
  simp only [TypeExpr.collection.injEq] at typeIs
  obtain ⟨rfl, rfl⟩ := typeIs
  cases rest with
  | none => exact absurd ⟨rfl, rfl⟩ notBag
  | some name =>
      have membersTyped : ∀ element ∈ elements, HasType language free bound element (.base sort) :=
        fun element member => elementsHaveType_iff.mp elementsTyped element member
      have parts : ∀ element ∈ elements,
          HasType language free bound (canonR block element) (.base sort) ∧
            SortedEquiv language free bound (.base sort) element (canonR block element) :=
        fun element member => (recurse element member).base context (membersTyped element member)
      have related : List.Forall₂ (SortedEquiv language free bound (.base sort)) elements
          (elements.map (canonR block)) := by
        rw [List.forall₂_map_right_iff]
        exact List.forall₂_same.mpr fun element member => (parts element member).2
      have chain := elements_congr (some name) membersTyped related [] (by simp)
      simp only [List.nil_append] at chain
      have reading : argumentOf block label (.collection .hashBag elements (some name))
          (canonP block (.collection .hashBag elements (some name))) =
          .collection .hashBag (elements.map (canonR block)) (some name) := by
        simp only [argumentOf, if_pos isMultiset, isAtom, toPattern_atom]
      rw [reading]
      refine ⟨.collection (elementsHaveType_iff.mpr fun element member => ?_), chain⟩
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      exact (parts original originalMember).1

omit laws in
/-- A variable or an explicit substitution is its own canonical block. -/
theorem inert_sound {term : Pattern} (isAtom : canonP block term = Prenex.atom term)
    (notMultiset : ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound → ∀ {label sort : String},
      label ∈ block.multisets → HasType language free bound term (.collection .hashBag (.base sort)) →
      argumentOf block label term (canonP block term) = term) :
    Sound₀ language block term := by
  have same : canonR block term = term := by rw [canonR, isAtom, toPattern_atom]
  refine ⟨?_, fun _ typed => atom_members isAtom (by rw [same]; exact typed), ?_⟩
  · intro free bound context sort typed
    rw [same]
    exact ⟨typed, .refl _⟩
  intro free bound context sort label isMultiset _ _ typed
  rw [notMultiset context isMultiset typed]
  exact ⟨typed, .refl _⟩

/-- **Every term's canonical block is sound**, and so is the body of every abstraction. -/
theorem canonP_sound_all (term : Pattern) :
    Sound₀ language block term ∧ ∀ binder body, term = .lambda binder body → Sound₀ language block body := by
  induction term using Pattern.inductionOn with
  | hbvar index =>
      refine ⟨inert_sound (by simp [canonP]) ?_, fun _ _ equal => by cases equal⟩
      intro free bound context label sort _ typed
      cases typed with
      | bvar lookup =>
          obtain ⟨sort', isBase⟩ := context.bound _ (List.mem_of_getElem? lookup)
          cases isBase
  | hfvar name =>
      refine ⟨inert_sound (by simp [canonP]) ?_, fun _ _ equal => by cases equal⟩
      intro free bound context label sort _ typed
      cases typed with
      | fvar lookup =>
          obtain ⟨sort', isBase⟩ := context.free name _ lookup
          cases isBase
  | hsubst body replacement _ _ =>
      refine ⟨inert_sound (by simp [canonP]) ?_, fun _ _ equal => by cases equal⟩
      intro free bound context label sort isMultiset _
      simp [argumentOf, isMultiset, canonP, Prenex.toPattern, Prenex.restricts, Prenex.body, Prenex.atom]
  | hlambda binder body recurse =>
      refine ⟨⟨(by intro free bound context sort typed; cases typed), (by intro free bound context typed; cases typed),
        (by intro free bound context sort label _ _ _ typed; cases typed)⟩, fun binder' body' equal => ?_⟩
      cases equal
      exact recurse.1
  | hmultiLambda arity binders body _ =>
      exact ⟨⟨(by intro free bound context sort typed; cases typed), (by intro free bound context typed; cases typed),
        (by intro free bound context sort label _ _ _ typed; cases typed)⟩, fun _ _ equal => by cases equal⟩
  | hcollection kind elements rest recurse =>
      refine ⟨?_, fun _ _ equal => by cases equal⟩
      by_cases isBag : kind = .hashBag ∧ rest = none
      · obtain ⟨rfl, rfl⟩ := isBag
        exact bag_sound fun element member => (recurse element member).1
      · exact collection_sound isBag fun element member => (recurse element member).1
  | happly label arguments recurse =>
      refine ⟨?_, fun _ _ equal => by cases equal⟩
      by_cases isUnit : label = block.unit ∧ arguments = []
      · obtain ⟨rfl, rfl⟩ := isUnit
        exact unit_sound
      by_cases isRestriction : ∃ binder body, label = block.restrict ∧ arguments = [.lambda binder body]
      · obtain ⟨binder, body, rfl, rfl⟩ := isRestriction
        exact restriction_sound ((recurse _ List.mem_cons_self).2 binder body rfl)
      by_cases isReplicate : ∃ argument, (∀ binder body, argument ≠ .lambda binder body) ∧
          label = block.replicate ∧ arguments = [argument]
      · obtain ⟨argument, notLambda, rfl, rfl⟩ := isReplicate
        exact replicate_sound notLambda (recurse _ List.mem_cons_self).1
      by_cases isEmpty : ∃ argument, (∀ binder body, argument ≠ .lambda binder body) ∧ arguments = [argument] ∧
          label ∈ block.emptyUnits ∧ canonP block argument = Prenex.nil
      · obtain ⟨argument, notLambda, rfl, listed, empty⟩ := isEmpty
        exact empty_sound listed notLambda empty (recurse _ List.mem_cons_self).1
      have isAtom := canonP_apply (block := block) (label := label) (arguments := arguments) isUnit
        (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
        (fun argument notLambda equal => isReplicate ⟨argument, notLambda, equal⟩)
        (fun argument notLambda equal listed empty => isEmpty ⟨argument, notLambda, equal, listed, empty⟩)
      by_cases isMultiset : label ∈ block.multisets
      · by_cases single : ∃ argument, arguments = [argument]
        · obtain ⟨argument, rfl⟩ := single
          refine multisetApply_sound isMultiset ?_ (recurse _ List.mem_cons_self).1
          rw [isAtom]
          simp [canonsP]
        · refine ⟨?_, ?_, ?_⟩
          · intro free bound context sort typed
            obtain ⟨-, -, -, -, -, -, -, argument, -, -, isSingle, -⟩ :=
              multiset_argument (block := block.toBlock) typed isMultiset
            exact absurd ⟨argument, isSingle⟩ single
          · intro free bound context typed
            obtain ⟨-, -, -, -, -, -, -, argument, -, -, isSingle, -⟩ :=
              multiset_argument (block := block.toBlock) typed isMultiset
            exact absurd ⟨argument, isSingle⟩ single
          · intro free bound context sort label' _ _ _ typed
            exact (apply_typed_not_collection typed).elim
      · exact constructor_sound isMultiset isAtom recurse

/-- **The canonical form with replication is sound**: every term of a sort is related to its canonical form, which
has that sort, by a chain of laws through terms of that sort, the laws of replication among them. -/
theorem canonR_sound {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {process : Pattern} {sort : String} (typed : HasType language free bound process (.base sort)) :
    HasType language free bound (canonR block process) (.base sort) ∧
      SortedEquiv language free bound (.base sort) process (canonR block process) :=
  (canonP_sound_all process).1.base context typed

end Typed

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
