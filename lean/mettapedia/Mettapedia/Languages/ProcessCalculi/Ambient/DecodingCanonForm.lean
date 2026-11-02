import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingRoot
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationMultisets

/-!
# Reading back a block's canonical form in the located calculus

A well-located block reads back as the canonical form of its process in the located calculus does
(`decode_canonForm`): the canonical form reads every capability's continuation canonically, splits every replication
into one replication per molecule of its block, and normalizes; the read-back keeps each of these, by induction on the
weight of the block.

This file holds:

- a replication replaced, at its place, by replications reading as it does (`readPlaced_replace_replication`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc capType)

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex Members ProcEquiv body_typed body_congr body_pair_equivalent
  bag_body_equivalent restricts_congr)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock ambientRepBlock prefix_fill acap_fill input_fill)
open Mettapedia.Languages.ProcessCalculi.Ambient.Located (locatedCalc locatedBlock locatedRepBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

variable {free : FreeTypeContext}

/-! ## A replication replaced at its place -/

/-- **A replication replaced by replications reading as it does at its place reads equivalently**, wherever the block
is read. -/
theorem readPlaced_replace_replication {argument at' : Pattern} {group : List Pattern} {low : Nat}
    {bound : List TypeExpr} (sits : placeAt (.apply "LRep" [argument]) = some at')
    (groupSits : ∀ member ∈ group, placeAt member = some at')
    (groupReads : ∀ fuel, low ≤ fuel → ∀ elsewhere : List Pattern,
      ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.body ambientBlock (group.map fun member => readComponent fuel at' member elsewhere))
        (readComponent fuel at' (.apply "LRep" [argument]) elsewhere))
    (groupMembers : Members locatedCalc locatedBlock free bound group)
    (typed : HasType locatedCalc free bound (.apply "LRep" [argument]) procType) :
    ∀ (fuel : Nat) {components : List Pattern} (place : Pattern), low + 2 * components.length + 2 ≤ fuel →
      Members locatedCalc locatedBlock free bound components →
      ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.body ambientBlock (readPlaced fuel place (group ++ components)))
        (Prenex.body ambientBlock (readPlaced fuel place (.apply "LRep" [argument] :: components)))
  | 0, _, _, enough, _ => absurd enough (by omega)
  | fuel + 1, components, place, enough, members => by
      have restMembers : Members locatedCalc locatedBlock free bound
          (components.filter fun other => !placedAt place other) :=
        fun element member => members element (List.mem_filter.mp member).1
      rw [readPlaced_succ, readPlaced_succ]
      by_cases here : at' = place
      · -- the group reads, at the place, as the replication
        subst here
        have groupHere : group.filter (placedAt at') = group :=
          List.filter_eq_self.mpr fun member inGroup => by simp [placedAt, groupSits member inGroup]
        have groupAway : group.filter (fun other => !placedAt at' other) = [] :=
          List.filter_eq_nil_iff.mpr fun member inGroup => by simp [placedAt, groupSits member inGroup]
        have replicationHere : placedAt at' (.apply "LRep" [argument]) = true := by simp [placedAt, sits]
        rw [List.filter_append, List.filter_append, groupHere, groupAway, List.nil_append,
          List.filter_cons_of_pos replicationHere, List.filter_cons_of_neg (by simp [replicationHere]),
          List.map_append, List.map_cons]
        set elsewhere := components.filter fun other => !placedAt at' other with elsewhereIs
        have itemsMembers : Members ambientCoreCalc ambientBlock free bound
            ((components.filter (placedAt at')).map fun component => readComponent fuel at' component elsewhere) := by
          intro item member
          obtain ⟨component, inFiltered, rfl⟩ := List.mem_map.mp member
          exact (decode_typed fuel).2.2 at' component elsewhere
            (members component (List.mem_filter.mp inFiltered).1) restMembers
        have groupItemsMembers : Members ambientCoreCalc ambientBlock free bound
            (group.map fun member => readComponent fuel at' member elsewhere) := by
          intro item member
          obtain ⟨component, inGroup, rfl⟩ := List.mem_map.mp member
          exact (decode_typed fuel).2.2 at' component elsewhere (groupMembers component inGroup) restMembers
        have replicationTyped : HasType ambientCoreCalc free bound
            (readComponent fuel at' (.apply "LRep" [argument]) elsewhere) procType :=
          (decode_typed fuel).2.2 at' _ elsewhere typed restMembers
        refine .trans _ _ _ (Relation.EqvGen.symm _ _ (body_pair_equivalent groupItemsMembers itemsMembers)) ?_
        refine .trans _ _ _ ?_ (body_pair_equivalent (first := [_]) (Members.cons replicationTyped Members.nil)
          itemsMembers)
        exact body_congr (first := [_, _]) (second := [_, _])
          (Members.cons (body_typed groupItemsMembers) (Members.cons (body_typed itemsMembers) Members.nil))
          (.cons (groupReads fuel (by omega) elsewhere) (.cons (.refl _) .nil))
      · -- elsewhere: every ambient here reads the group as it reads the replication
        have groupHere : group.filter (placedAt place) = [] :=
          List.filter_eq_nil_iff.mpr fun member inGroup => by simp [placedAt, groupSits member inGroup, here]
        have groupAway : group.filter (fun other => !placedAt place other) = group :=
          List.filter_eq_self.mpr fun member inGroup => by simp [placedAt, groupSits member inGroup, here]
        have replicationAway : placedAt place (.apply "LRep" [argument]) = false := by simp [placedAt, sits, here]
        have notHere : ¬ placedAt place (.apply "LRep" [argument]) = true := by simp [replicationAway]
        have isAway : (!placedAt place (.apply "LRep" [argument])) = true := by simp [replicationAway]
        rw [List.filter_append, List.filter_append, groupHere, groupAway, List.nil_append,
          List.filter_cons_of_neg (p := placedAt place) notHere,
          List.filter_cons_of_pos (p := fun other => !placedAt place other) isAway]
        refine body_congr ?_ (forall₂_map_map fun component inFiltered => ?_)
        · intro item member
          obtain ⟨component, inFiltered, rfl⟩ := List.mem_map.mp member
          exact (decode_typed fuel).2.2 place component _ (members component (List.mem_filter.mp inFiltered).1)
            (groupMembers.append restMembers)
        · obtain ⟨inComponents, isHere⟩ := List.mem_filter.mp inFiltered
          have shorter : (components.filter fun other => !placedAt place other).length + 1 ≤ components.length := by
            have total := List.length_eq_length_filter_add (l := components) (placedAt place)
            have positive : 0 < (components.filter (placedAt place)).length :=
              List.length_pos_of_mem (List.mem_filter.mpr ⟨inComponents, isHere⟩)
            omega
          cases fuel with
          | zero => exact .refl _
          | succ fuel =>
              refine readComponent_equivalent (members component inComponents) fun child _ => ?_
              exact readPlaced_replace_replication sits groupSits groupReads groupMembers typed fuel child
                (by omega) restMembers

/-! ## Canonical forms of components -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (canonP canonR normal canonicalOf replicatedOf decompose
  decompose_toPattern canonFacts canonR_sound canonR_complete restrictionsBind_of_typed isObject_canonR normal_objects
  replicatedOf_objects objects_of_decompose decompose_sound normal_count_zero canonP_replicate canonP_many
  objectArgument normal_sound isReplicated isReplicated_recanon isReplicated_rename normal_mem_read SortedEquiv
  isObject_toPattern isReplicated_shape replicatedOf_replicated objects_canonP_and recanon rename BaseContext sizeList
  size)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

theorem variable_object {pattern : Pattern} (isVar : isVariable pattern = true) : isObjectPattern pattern = true := by
  cases pattern with
  | bvar index => rfl
  | fvar name => rfl
  | _ => simp [isVariable] at isVar

/-- **A pattern's block, written out, has the pattern's canonical block.** -/
theorem canonP_toPattern_decompose {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType locatedCalc free bound pattern procType) (object : isObjectPattern pattern = true) :
    canonP locatedRepBlock (Prenex.toPattern locatedBlock (decompose locatedBlock pattern)) =
      canonP locatedRepBlock pattern := by
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  obtain ⟨-, sound⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) typed
  have blockObject : isObjectPattern (Prenex.toPattern locatedBlock (decompose locatedBlock pattern)) = true :=
    isObject_toPattern (objects_of_decompose object)
  have blockTyped : HasType locatedCalc free bound (Prenex.toPattern locatedBlock (decompose locatedBlock pattern))
      procType := (SortedEquiv.typed_iff sound).mp typed
  have same := canonR_complete (block := locatedRepBlock) (base := engineBasePremises RelationEnv.empty)
    blockObject object (restrictionsBind_of_typed (block := locatedRepBlock) _ blockTyped)
    (SortedEquiv.toEquationEquiv (Relation.EqvGen.symm _ _ sound))
  have firstFacts := canonFacts fresh restrictFresh blockObject
    (restrictionsBind_of_typed (block := locatedRepBlock) _ blockTyped)
  have secondFacts := canonFacts fresh restrictFresh object (restrictionsBind_of_typed (block := locatedRepBlock) _
    typed)
  have decomposed := congrArg (decompose locatedRepBlock.toBlock) same
  unfold canonR at decomposed
  rwa [decompose_toPattern firstFacts.atomic firstFacts.used,
    decompose_toPattern secondFacts.atomic secondFacts.used] at decomposed

/-- A replication reads alike among any other components. -/
theorem readComponent_replication (fuel : Nat) (place argument : Pattern) (first second : List Pattern) :
    readComponent fuel place (.apply "LRep" [argument]) first =
      readComponent fuel place (.apply "LRep" [argument]) second := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [readComponent]

/-! ## What reading a block's canonical form keeps -/

/-- **What reading a block's canonical form keeps**: a well-located typed block of object components has, in the
located calculus, a well-located canonical form of typed components, which reads back as the block. -/
def CanonFormFacts (free : FreeTypeContext) (form : Prenex) : Prop :=
  ∀ {isLoc : Pattern → Prop} {outer : Nat} {bound : List TypeExpr},
    WellLocated isLoc (.bvar outer) form → LocVariables isLoc → BaseContext free bound →
    Members locatedCalc locatedBlock free (List.replicate form.count nameType ++ bound) form.components →
    (∀ component ∈ form.components, isObjectPattern component = true) →
    WellLocated isLoc (.bvar outer) (canonP locatedRepBlock (Prenex.toPattern locatedBlock form)) ∧
      Members locatedCalc locatedBlock free
        (List.replicate (canonP locatedRepBlock (Prenex.toPattern locatedBlock form)).count nameType ++ bound)
        (canonP locatedRepBlock (Prenex.toPattern locatedBlock form)).components ∧
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer)
          (canonP locatedRepBlock (Prenex.toPattern locatedBlock form))))
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) form))

/-- What reading canonical forms keeps, for the blocks lighter than a weight. -/
def CanonFormBelow (free : FreeTypeContext) (weight : Nat) : Prop :=
  ∀ (form : Prenex), form.mass < weight → CanonFormFacts free form

/-! ## A replication's canonical form -/

/-- **A replication's canonical form reads at its place as the replication**: one replication per molecule of its
block, read canonically, each at the replication's place, read together as the replication. -/
theorem replication_canonForm {bound : List TypeExpr} {isLoc : Pattern → Prop} {place : Nat} {argument : Pattern}
    (argumentWell : WellLocated isLoc (.bvar place) (decompose locatedBlock argument))
    (locVariables : LocVariables isLoc) (context : BaseContext free bound)
    (argumentTyped : HasType locatedCalc free bound argument procType) (argumentObject : isObjectPattern argument = true)
    (facts : CanonFormFacts free (decompose locatedBlock argument)) :
    (canonP locatedRepBlock (.apply "LRep" [argument])).count = 0 ∧
      WellLocated isLoc (.bvar place) (canonP locatedRepBlock (.apply "LRep" [argument])) ∧
      Members locatedCalc locatedBlock free bound (canonP locatedRepBlock (.apply "LRep" [argument])).components ∧
      (∀ component ∈ (canonP locatedRepBlock (.apply "LRep" [argument])).components,
        isObjectPattern component = true ∧ placeAt component = some (.bvar place) ∧
          ∃ inner, component = .apply "LRep" [inner]) ∧
      ∃ least, ∀ fuel, least ≤ fuel → ∀ elsewhere : List Pattern, ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.body ambientBlock ((canonP locatedRepBlock (.apply "LRep" [argument])).components.map
          fun component => readComponent fuel (.bvar place) component elsewhere))
        (readComponent fuel (.bvar place) (.apply "LRep" [argument]) elsewhere) := by
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  have notLambda : ∀ binder body, argument ≠ .lambda binder body := by
    rintro binder body rfl
    cases argumentTyped
  have replicateIs : canonP locatedRepBlock (.apply "LRep" [argument]) =
      normal locatedRepBlock ⟨0, replicatedOf locatedRepBlock (canonicalOf locatedRepBlock)
        (canonP locatedRepBlock argument)⟩ := canonP_replicate notLambda
  rw [replicateIs]
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  -- the argument's canonical block, read
  obtain ⟨argumentMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) argumentTyped
  obtain ⟨canonWell, canonMembers, least₀, reads₀⟩ := facts argumentWell locVariables context argumentMembers
    (objects_of_decompose argumentObject)
  rw [canonP_toPattern_decompose argumentTyped argumentObject] at canonWell canonMembers reads₀
  set inner := canonP locatedRepBlock argument with innerIs
  -- its molecules, replicated, then normalized
  obtain ⟨moleculesWell, moleculesMembers, least₁, reads₁⟩ :=
    decode_replicatedOf (count := inner.count) (components := inner.components) canonWell locVariables context
      canonMembers
  set molecules := replicatedOf locatedRepBlock (canonicalOf locatedRepBlock) inner with moleculesIs
  have normalFacts := decode_normal (free := free) ⟨0, molecules⟩ moleculesWell locVariables context moleculesMembers
  obtain ⟨normalWell, normalReads⟩ := normalFacts
  have normalMembers := (normal_sound (language := locatedCalc) (block := locatedRepBlock) context
    (form := ⟨0, molecules⟩) moleculesMembers).1
  have countIs := normal_count_zero (block := locatedRepBlock) molecules
  set normalized := normal locatedRepBlock ⟨0, molecules⟩ with normalizedIs
  -- the molecules are object replications at the place
  have innerObjects : ∀ component ∈ inner.components, isObjectPattern component = true :=
    (objects_canonP_and (block := locatedRepBlock) argument).1 argumentObject
  have moleculesObjects : ∀ component ∈ molecules, isObjectPattern component = true :=
    replicatedOf_objects innerObjects
  have normalizedObjects : ∀ component ∈ normalized.components, isObjectPattern component = true :=
    normal_objects moleculesObjects
  have moleculesAtomic : (Prenex.mk 0 molecules).Atomic locatedRepBlock.toBlock := fun component member =>
    ComponentKind.decompose_atom (moleculesWell.kinds component member)
  have shape : ∀ component ∈ normalized.components, ∃ inner', component = .apply "LRep" [inner'] := by
    intro component member
    obtain ⟨relabel, original, originalIn, rfl⟩ := normal_mem_read fresh restrictFresh moleculesAtomic component member
    have replicated : isReplicated locatedRepBlock (recanon locatedRepBlock (rename relabel original)) = true := by
      rw [isReplicated_recanon, isReplicated_rename]
      exact replicatedOf_replicated original originalIn
    exact isReplicated_shape replicated
  have placedHere : ∀ component ∈ normalized.components, placeAt component = some (.bvar place) := by
    intro component member
    obtain ⟨inner', rfl⟩ := shape component member
    obtain ⟨at', sits⟩ := Option.isSome_iff_exists.mp (normalWell.repsPlaced _ member inner' rfl)
    rcases normalWell.placed _ member at' sits with atRoot | ⟨index, below, -, -⟩
    · rw [sits, atRoot, countIs, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
    · rw [countIs] at below
      omega
  refine ⟨countIs, normalWell, by rw [countIs] at normalMembers; simpa using normalMembers,
    fun component member => ⟨normalizedObjects component member, placedHere component member, shape component member⟩,
    ?_⟩
  -- the molecules, read at the place, read as the replication
  refine ⟨max (max least₀ (least₁ + 1)) (max (3 * (Prenex.mk 0 molecules).mass + 3)
    (max (3 * normalized.mass + 3) (3 * (decompose locatedBlock argument).mass + 4))), fun fuel enough elsewhere => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have allHere : normalized.components.filter (placedAt (.bvar place)) = normalized.components :=
    List.filter_eq_self.mpr fun component member => by simp [placedAt, placedHere component member]
  have noneElse : normalized.components.filter (fun other => !placedAt (.bvar place) other) = [] :=
    List.filter_eq_nil_iff.mpr fun component member => by simp [placedAt, placedHere component member]
  have readingIs : Prenex.toPattern ambientBlock (decodeForm (f + 3) (.bvar place) normalized) =
      Prenex.body ambientBlock (normalized.components.map fun component =>
        readComponent (f + 1) (.bvar place) component elsewhere) := by
    simp only [decodeForm, Prenex.toPattern]
    rw [countIs, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero, readPlaced_succ, allHere, noneElse]
    simp only [Prenex.restricts]
    congr 1
    refine List.map_congr_left fun component member => ?_
    obtain ⟨inner', rfl⟩ := shape component member
    exact readComponent_replication _ _ _ _ _
  rw [← readingIs]
  have settled : decodeForm (f + 1) (.bvar place) (decompose locatedBlock argument) =
      decodeForm f (.bvar place) (decompose locatedBlock argument) :=
    decodeForm_settled _ _ (by omega) (by omega)
  have replicationIs : readComponent (f + 1) (.bvar place) (.apply "LRep" [argument]) elsewhere =
      .apply "ARep" [Prenex.toPattern ambientBlock (decodeForm f (.bvar place) (decompose locatedBlock argument))] := by
    simp [readComponent]
  rw [replicationIs, ← settled]
  refine .trans _ _ _ (normalReads (f + 3) (by omega) (by omega)) (.trans _ _ _ (reads₁ f (by omega)) ?_)
  exact Mettapedia.GSLT.LanguageDef.RestrictionBlocks.replicate_fill (language := ambientCoreCalc)
    (block := ambientRepBlock) (reads₀ (f + 1) (by omega))

/-! ## Continuations read canonically -/

/-- **The part of a component its canonical form reads canonically**: a capability's continuation; markers and
replications stay as they are. -/
def canonPart (component : Pattern) : Pattern :=
  if isReplicated locatedRepBlock component then component else canonR locatedRepBlock component

/-- **A typed object's canonical form, read as a block, is its canonical block.** -/
theorem decompose_canonR {bound : List TypeExpr} {pattern : Pattern}
    (typed : HasType locatedCalc free bound pattern procType) (object : isObjectPattern pattern = true) :
    decompose locatedBlock (canonR locatedRepBlock pattern) = canonP locatedRepBlock pattern := by
  have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
  have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
  have facts := canonFacts fresh restrictFresh object (restrictionsBind_of_typed (block := locatedRepBlock) _ typed)
  exact decompose_toPattern facts.atomic facts.used

/-- **A component of a well-located block keeps its shape read canonically**: a marker, a replication and an output
stay; a capability and a prefix read their continuations canonically, an input its body. -/
theorem WellLocated.canonPart_shape {isLoc : Pattern → Prop} {place : Pattern} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩) (locVariables : LocVariables isLoc)
    {component : Pattern} (member : component ∈ components) (object : isObjectPattern component = true) :
    canonPart component = component ∨
      (∃ label at' name continuation, component = .apply label [at', name, continuation] ∧ label ∈ capabilities ∧
        canonPart component = .apply label [at', name, canonR locatedRepBlock continuation]) ∨
      (∃ at' message continuation, component = .apply "LCap" [at', message, continuation] ∧
        canonPart component = .apply "LCap" [at', message, canonR locatedRepBlock continuation]) ∨
      (∃ label at' binder body, component = .apply label [at', .lambda binder body] ∧ label ∈ inputs ∧
        canonPart component = .apply label [at', .lambda binder (canonR locatedRepBlock body)]) := by
  have placeVar : ∀ at', placeAt component = some at' → isVariable at' = true := fun at' isPlaced =>
    insideLoc_locVariables isLoc count components at' (well.placeInside locVariables component member at' isPlaced)
  cases well.kinds component member with
  | @marker markerLabel parent name index isMarker below =>
      left
      have notRestrict : markerLabel ≠ "LNu" := by
        simp only [markers, List.mem_cons, List.not_mem_nil, or_false] at isMarker
        rcases isMarker with rfl | rfl <;> decide
      have nameVar := (well.names _ member name (by simp [nameOf, isMarker])).1
      have parentVar := placeVar parent (placeAt_ofMarker isMarker _ _ _)
      unfold canonPart canonR
      rw [if_neg (by simp [isReplicated]), canonP_triple notRestrict parentVar rfl (variable_object nameVar),
        canonP_variable nameVar]
      rfl
  | @capability label at' name continuation listed =>
      right
      have notRestrict : label ≠ "LNu" := by
        simp only [capabilities, List.mem_cons, List.not_mem_nil, or_false] at listed
        rcases listed with rfl | rfl | rfl <;> decide
      have notMarker := not_marker_of_capability listed
      have nameVar := (well.names _ member name (by simp [nameOf, notMarker, listed])).1
      have continuationObject : isObjectPattern continuation = true := by
        simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Bool.and_eq_true]
          at object
        exact object.2.2.1
      refine .inl ⟨label, at', name, continuation, rfl, listed, ?_⟩
      unfold canonPart canonR
      rw [if_neg (by simp [isReplicated]),
        canonP_triple notRestrict (placeVar at' (placeAt_capability listed _ _ _)) nameVar continuationObject]
      rfl
  | @replication argument =>
      left
      unfold canonPart
      rw [if_pos (by simp [isReplicated])]
  | @cap at' message continuation =>
      right; right; left
      have messageIs := (well.messages _ member message (by simp [messageOf])).1
      have continuationObject : isObjectPattern continuation = true := by
        simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Bool.and_eq_true]
          at object
        exact object.2.2.1
      refine ⟨at', message, continuation, rfl, ?_⟩
      unfold canonPart canonR
      rw [if_neg (by simp [isReplicated]),
        canonP_cap (placeVar at' (placeAt_cap _ _ _)) messageIs continuationObject]
      rfl
  | @input label at' binder body listed =>
      right; right; right
      have bodyObject : isObjectPattern body = true := by
        simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Bool.and_eq_true,
          Bool.and_true] at object
        exact object.2
      refine ⟨label, at', binder, body, rfl, listed, ?_⟩
      unfold canonPart canonR
      rw [if_neg (by simp [isReplicated]), canonP_input listed (placeVar at' (placeAt_input listed _ _)) bodyObject]
      rfl
  | @output label at' message listed =>
      left
      have messageIs := (well.messages _ member message (by simp [messageOf, listed])).1
      unfold canonPart canonR
      rw [if_neg (by simp [isReplicated]), canonP_output listed (placeVar at' (placeAt_output listed _ _)) messageIs]
      rfl

/-- **Finitely many thresholds have a common bound.** -/
theorem exists_upper {α : Type} {holds : α → Nat → Prop} : ∀ (items : List α),
    (∀ item ∈ items, ∃ least, ∀ fuel, least ≤ fuel → holds item fuel) →
    ∃ least, ∀ item ∈ items, ∀ fuel, least ≤ fuel → holds item fuel
  | [], _ => ⟨0, fun _ member => absurd member List.not_mem_nil⟩
  | item :: rest, each => by
      obtain ⟨first, firstHolds⟩ := each item List.mem_cons_self
      obtain ⟨second, secondHolds⟩ := exists_upper rest fun other member => each other (List.mem_cons_of_mem _ member)
      refine ⟨max first second, fun other member fuel enough => ?_⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact firstHolds fuel (le_of_max_le_left enough)
      · exact secondHolds other inRest fuel (le_of_max_le_right enough)

/-- **Continuations read canonically read back equivalently**, and keep the block well-located, when the lighter
blocks read back as their canonical forms. -/
theorem decode_canonParts {bound : List TypeExpr} {isLoc : Pattern → Prop} {outer count : Nat}
    {components : List Pattern} (well : WellLocated isLoc (.bvar outer) ⟨count, components⟩)
    (locVariables : LocVariables isLoc) (context : BaseContext free bound)
    (members : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) components)
    (objects : ∀ component ∈ components, isObjectPattern component = true)
    (canonBelow : CanonFormBelow free (Prenex.mk count components).mass) :
    WellLocated isLoc (.bvar outer) ⟨count, components.map canonPart⟩ ∧
      Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound) (components.map canonPart) ∧
      (∀ component ∈ components.map canonPart, isObjectPattern component = true) ∧
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) ⟨count, components.map canonPart⟩))
        (Prenex.toPattern ambientBlock (decodeForm fuel (.bvar outer) ⟨count, components⟩)) := by
  have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
    Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
  have innerContext := context.replicate count "Name"
  have insideVariables := insideLoc_locVariables isLoc count components
  -- each continuation of a capability or a prefix: well-located at its place, typed, read canonically
  have continuationFacts : ∀ component ∈ components, ∀ label at' name continuation,
      component = .apply label [at', name, continuation] → (label ∈ capabilities ∨ label = "LCap") →
      (∃ index, at' = .bvar index) ∧
        WellLocated (insideLoc isLoc count components) at' (canonP locatedRepBlock continuation) ∧
        HasType locatedCalc free (List.replicate count nameType ++ bound) continuation procType ∧
        isObjectPattern continuation = true ∧
        ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free
          (List.replicate count nameType ++ bound)
          (Prenex.toPattern ambientBlock (decodeForm fuel at' (canonP locatedRepBlock continuation)))
          (Prenex.toPattern ambientBlock (decodeForm fuel at' (decompose locatedBlock continuation))) := by
    intro component member label at' name continuation shape listed
    subst shape
    have sits : placeAt (.apply label [at', name, continuation]) = some at' := by
      rcases listed with listed | rfl
      · exact placeAt_capability listed _ _ _
      · exact placeAt_cap _ _ _
    have atBvar : ∃ index, at' = .bvar index := by
      rcases well.placed _ member at' sits with same | ⟨index, -, same, -⟩
      · exact ⟨outer + count, by rw [same]; simp [liftBVars]⟩
      · exact ⟨index, same⟩
    obtain ⟨index, rfl⟩ := atBvar
    have innerWell : WellLocated (insideLoc isLoc count components) (.bvar index)
        (decompose locatedBlock continuation) := by
      rcases listed with listed | rfl
      · exact match well with
          | .intro _ _ _ _ _ caps _ _ _ _ _ _ => caps _ member label _ name continuation rfl listed
      · exact well.capConts _ member _ name continuation rfl
    have continuationTyped : HasType locatedCalc free (List.replicate count nameType ++ bound) continuation
        procType := by
      rcases triple_inv (members _ member) with ⟨isMarker, -⟩ | ⟨-, -, third⟩ | ⟨-, -, third⟩
      · rcases listed with listed | rfl
        · exact absurd listed (not_capability_of_marker isMarker)
        · simp [markers] at isMarker
      · exact third
      · exact third
    have continuationObject : isObjectPattern continuation = true := by
      have object := objects _ member
      simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Bool.and_eq_true]
        at object
      exact object.2.2.1
    have lighter : (decompose locatedBlock continuation).mass < (Prenex.mk count components).mass := by
      have massLe := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mass_decompose (block := locatedBlock) continuation
      have inComponents := size_le_sizeList member
      have formMass : (Prenex.mk count components).mass = 2 * count + sizeList components := rfl
      simp only [size, sizeList] at inComponents
      omega
    obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) continuationTyped
    obtain ⟨canonWell, -, least, reads⟩ := canonBelow _ lighter innerWell insideVariables innerContext innerMembers
      (objects_of_decompose continuationObject)
    rw [canonP_toPattern_decompose continuationTyped continuationObject] at canonWell reads
    exact ⟨⟨index, rfl⟩, canonWell, continuationTyped, continuationObject, least, reads⟩
  -- each input's body: well-located at the input's place under its binder, typed there, read canonically
  have bodyFacts : ∀ component ∈ components, ∀ label at' binder body,
      component = .apply label [at', .lambda binder body] → label ∈ inputs →
      (∃ index, at' = .bvar index) ∧ binder = none ∧ ∃ sort, (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")] ∧
        WellLocated (underName (insideLoc isLoc count components)) (liftBVars 0 1 at') (canonP locatedRepBlock body) ∧
        HasType locatedCalc free (.base sort :: (List.replicate count nameType ++ bound)) body procType ∧
        isObjectPattern body = true ∧
        ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free
          (.base sort :: (List.replicate count nameType ++ bound))
          (Prenex.toPattern ambientBlock (decodeForm fuel (liftBVars 0 1 at') (canonP locatedRepBlock body)))
          (Prenex.toPattern ambientBlock (decodeForm fuel (liftBVars 0 1 at') (decompose locatedBlock body))) := by
    intro component member label at' binder body shape listed
    subst shape
    have atBvar : ∃ index, at' = .bvar index := by
      rcases well.placed _ member at' (placeAt_input listed _ _) with same | ⟨index, -, same, -⟩
      · exact ⟨outer + count, by rw [same]; simp [liftBVars]⟩
      · exact ⟨index, same⟩
    obtain ⟨index, rfl⟩ := atBvar
    have innerWell := well.bodies _ member label _ binder body rfl listed
    rw [show liftBVars 0 1 (Pattern.bvar index) = .bvar (index + 1) by simp [liftBVars]] at innerWell ⊢
    obtain ⟨-, ⟨sort, body', sorted, same, bodyTyped⟩ | ⟨sort, sorted, -⟩⟩ := pair_inv (members _ member)
    · simp only [Pattern.lambda.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      have bodyObject : isObjectPattern body = true := by
        have object := objects _ member
        simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList, Bool.and_eq_true,
          Bool.and_true] at object
        exact object.2
      have lighter : (decompose locatedBlock body).mass < (Prenex.mk count components).mass := by
        have massLe := Mettapedia.GSLT.LanguageDef.RestrictionBlocks.mass_decompose (block := locatedBlock) body
        have inComponents := size_le_sizeList member
        have formMass : (Prenex.mk count components).mass = 2 * count + sizeList components := rfl
        simp only [size, sizeList] at inComponents
        omega
      obtain ⟨innerMembers, -⟩ := decompose_sound (language := locatedCalc) (block := locatedBlock) bodyTyped
      obtain ⟨canonWell, -, least, reads⟩ := canonBelow _ lighter innerWell (underName_locVariables _)
        (innerContext.cons sort) innerMembers (objects_of_decompose bodyObject)
      rw [canonP_toPattern_decompose bodyTyped bodyObject] at canonWell reads
      exact ⟨⟨index, rfl⟩, rfl, sort, sorted, canonWell, bodyTyped, bodyObject, least, reads⟩
    · exfalso
      apply not_output_of_input listed
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at sorted
      rcases sorted with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  -- a component read canonically keeps its place, its location, its name, its kind and its message
  have facts : ∀ component ∈ components,
      placeAt (canonPart component) = placeAt component ∧ childOf (canonPart component) = childOf component ∧
        nameOf (canonPart component) = nameOf component ∧ ComponentKind count (canonPart component) ∧
        messageOf (canonPart component) = messageOf component := by
    intro component member
    rcases well.canonPart_shape locVariables member (objects _ member) with same |
        ⟨label, at', name, continuation, rfl, listed, same⟩ | ⟨at', message, continuation, rfl, same⟩ |
        ⟨label, at', binder, body, rfl, listed, same⟩
    · rw [same]
      exact ⟨rfl, rfl, rfl, well.kinds component member, rfl⟩
    · have notMarker := not_marker_of_capability listed
      have notCap : label ≠ "LCap" := by rintro rfl; simp [capabilities] at listed
      rw [same]
      exact ⟨by rw [placeAt_capability listed, placeAt_capability listed], by simp [childOf, notMarker],
        by simp [nameOf, notMarker, listed], .capability listed, by simp [messageOf, notCap]⟩
    · rw [same]
      exact ⟨by rw [placeAt_cap, placeAt_cap], by simp [childOf, markers], by simp [nameOf, markers, capabilities],
        .cap, by simp [messageOf]⟩
    · rw [same]
      exact ⟨by rw [placeAt_input listed, placeAt_input listed], by simp [childOf], by simp [nameOf], .input listed,
        by simp [messageOf, not_output_of_input listed]⟩
  have changedMember : ∀ {component}, component ∈ components → canonPart component ∈ components.map canonPart :=
    fun member => List.mem_map.mpr ⟨_, member, rfl⟩
  have markedSame : ∀ index, Marked (components.map canonPart) index ↔ Marked components index := by
    intro index
    constructor
    · rintro ⟨marker, member, isChild⟩
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      exact ⟨original, inComponents, by rw [← (facts original inComponents).2.1]; exact isChild⟩
    · rintro ⟨marker, member, isChild⟩
      exact ⟨_, changedMember member, by rw [(facts marker member).2.1]; exact isChild⟩
  have insideSame : insideLoc isLoc count (components.map canonPart) = insideLoc isLoc count components := by
    funext pattern
    apply propext
    cases pattern with
    | bvar index =>
        simp only [insideLoc]
        split_ifs
        · exact markedSame index
        · exact Iff.rfl
    | _ => exact Iff.rfl
  have changedMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
      (components.map canonPart) := by
    intro element member
    obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
    unfold canonPart
    split_ifs
    · exact members original inComponents
    · exact (canonR_sound (block := locatedRepBlock) innerContext (members original inComponents)).1
  have changedObjects : ∀ component ∈ components.map canonPart, isObjectPattern component = true := by
    intro element member
    obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
    unfold canonPart
    split_ifs
    · exact objects original inComponents
    · exact isObject_canonR (block := locatedRepBlock) (objects original inComponents)
  refine ⟨?_, changedMembers, changedObjects, ?_⟩
  · -- well-located
    refine .intro well.placeIsLoc (fun component member => ?_) (fun component member at' isPlaced => ?_)
      (fun index => ?_) (fun component member name isName => ?_) ?_ ?_ (fun component member argument isRep => ?_) ?_
      (fun component member message isMsgOf => ?_) ?_ ?_
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      exact (facts original inComponents).2.2.2.1
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).1] at isPlaced
      rcases well.placed original inComponents at' isPlaced with same | ⟨index, below, same, isMarked⟩
      · exact .inl same
      · exact .inr ⟨index, below, same, (markedSame index).mpr isMarked⟩
    · have whole := well.unique index
      simp only at whole ⊢
      rw [List.filter_map, List.length_map]
      refine le_of_eq_of_le ?_ whole
      congr 1
      exact List.filter_congr fun component member => by simp [Function.comp, (facts component member).2.1]
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).2.2.1] at isName
      rw [insideSame]
      exact well.names original inComponents name isName
    · intro component member label at' name continuation isCap listed
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      rcases well.canonPart_shape locVariables inComponents (objects _ inComponents) with same |
          ⟨label', at'', name', inner, rfl, listed', same⟩ | ⟨at'', message', inner, rfl, same⟩ |
          ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isCap
        subst isCap
        exact match well with | .intro _ _ _ _ _ caps _ _ _ _ _ _ => caps _ inComponents label at' name continuation rfl listed
      · rw [same] at isCap
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at isCap
        obtain ⟨rfl, rfl, rfl, rfl⟩ := isCap
        obtain ⟨-, innerWell, innerTyped, innerObject, -⟩ :=
          continuationFacts _ inComponents label' at'' name' inner rfl (.inl listed')
        rw [decompose_canonR innerTyped innerObject]
        exact innerWell
      · rw [same] at isCap
        simp only [Pattern.apply.injEq] at isCap
        obtain ⟨rfl, -⟩ := isCap
        simp [capabilities] at listed
      · rw [same] at isCap
        cases isCap
    · intro component member argument at' isRep isPlaced
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      have originalPlaced := isPlaced
      rw [(facts original inComponents).1] at originalPlaced
      rcases well.canonPart_shape locVariables inComponents (objects _ inComponents) with same |
          ⟨label', at'', name', inner, rfl, listed', same⟩ | ⟨at'', message', inner, rfl, same⟩ |
          ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isRep
        subst isRep
        exact match well with | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ inComponents argument at' rfl originalPlaced
      · rw [same] at isRep
        cases isRep
      · rw [same] at isRep
        simp at isRep
      · rw [same] at isRep
        cases isRep
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).1]
      rcases well.canonPart_shape locVariables inComponents (objects _ inComponents) with same |
          ⟨label', at'', name', inner, rfl, listed', same⟩ | ⟨at'', message', inner, rfl, same⟩ |
          ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isRep
        exact well.repsPlaced original inComponents argument isRep
      · rw [same] at isRep
        cases isRep
      · rw [same] at isRep
        simp at isRep
      · rw [same] at isRep
        cases isRep
    · obtain ⟨depth, grows⟩ := well.nested
      refine ⟨depth, fun component member index child below childBelow isPlaced isChild => ?_⟩
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).1] at isPlaced
      rw [(facts original inComponents).2.1] at isChild
      exact grows original inComponents index child below childBelow isPlaced isChild
    · obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [(facts original inComponents).2.2.2.2] at isMsgOf
      rw [insideSame]
      exact well.messages original inComponents message isMsgOf
    · intro component member at' message continuation isCapComponent
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      rcases well.canonPart_shape locVariables inComponents (objects _ inComponents) with same |
          ⟨label', at'', name', inner, rfl, listed', same⟩ | ⟨at'', message', inner, rfl, same⟩ |
          ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isCapComponent
        subst isCapComponent
        exact well.capConts _ inComponents at' message continuation rfl
      · rw [same] at isCapComponent
        simp only [Pattern.apply.injEq] at isCapComponent
        obtain ⟨rfl, -⟩ := isCapComponent
        simp [capabilities] at listed'
      · rw [same] at isCapComponent
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at isCapComponent
        obtain ⟨rfl, rfl, rfl⟩ := isCapComponent
        obtain ⟨-, innerWell, innerTyped, innerObject, -⟩ :=
          continuationFacts _ inComponents "LCap" _ message' inner rfl (.inr rfl)
        rw [decompose_canonR innerTyped innerObject]
        exact innerWell
      · rw [same] at isCapComponent
        cases isCapComponent
    · intro component member label at' binder body isInput listed
      obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
      rw [insideSame]
      rcases well.canonPart_shape locVariables inComponents (objects _ inComponents) with same |
          ⟨label', at'', name', inner, rfl, listed', same⟩ | ⟨at'', message', inner, rfl, same⟩ |
          ⟨label', at'', binder', body', rfl, listed', same⟩
      · rw [same] at isInput
        subst isInput
        exact well.bodies _ inComponents label at' binder body rfl listed
      · rw [same] at isInput
        cases isInput
      · rw [same] at isInput
        cases isInput
      · rw [same] at isInput
        simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true] at isInput
        obtain ⟨rfl, rfl, rfl, rfl⟩ := isInput
        obtain ⟨-, -, sort, -, bodyWell, bodyTyped, bodyObject, -⟩ :=
          bodyFacts _ inComponents _ _ _ _ rfl listed'
        rw [decompose_canonR bodyTyped bodyObject]
        exact bodyWell
  · -- read back equivalently, past the thresholds of the continuations and the bodies
    obtain ⟨low, lowReads⟩ := exists_upper (holds := fun component fuel =>
        (∀ label at' name continuation, component = .apply label [at', name, continuation] →
          (label ∈ capabilities ∨ label = "LCap") →
          ProcEquiv ambientCoreCalc ambientBlock free (List.replicate count nameType ++ bound)
            (Prenex.toPattern ambientBlock (decodeForm fuel at' (canonP locatedRepBlock continuation)))
            (Prenex.toPattern ambientBlock (decodeForm fuel at' (decompose locatedBlock continuation)))) ∧
        (∀ label at' binder body sort, component = .apply label [at', .lambda binder body] →
          (label, sort) ∈ [("LInName", "Name"), ("LInCap", "Cap")] →
          ProcEquiv ambientCoreCalc ambientBlock free (.base sort :: (List.replicate count nameType ++ bound))
            (Prenex.toPattern ambientBlock (decodeForm fuel (liftBVars 0 1 at') (canonP locatedRepBlock body)))
            (Prenex.toPattern ambientBlock (decodeForm fuel (liftBVars 0 1 at') (decompose locatedBlock body)))))
      components
      (fun component member => by
        by_cases isCont : ∃ label at' name continuation, component = .apply label [at', name, continuation] ∧
            (label ∈ capabilities ∨ label = "LCap")
        · obtain ⟨label, at', name, continuation, rfl, listed⟩ := isCont
          obtain ⟨-, -, -, -, least, reads⟩ := continuationFacts _ member label at' name continuation rfl listed
          refine ⟨least, fun fuel enough => ⟨fun label' at'' name' continuation' same listed' => ?_,
            fun label' at'' binder body sort same _ => by simp at same⟩⟩
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at same
          obtain ⟨rfl, rfl, rfl, rfl⟩ := same
          exact reads fuel enough
        · by_cases isBody : ∃ label at' binder body, component = .apply label [at', .lambda binder body] ∧
              label ∈ inputs
          · obtain ⟨label, at', binder, body, rfl, listed⟩ := isBody
            obtain ⟨-, -, sort, sorted, -, -, -, least, reads⟩ := bodyFacts _ member label at' binder body rfl listed
            refine ⟨least, fun fuel enough => ⟨fun label' at'' name' continuation' same _ => by simp at same,
              fun label' at'' binder' body' sort' same sorted' => ?_⟩⟩
            simp only [Pattern.apply.injEq, List.cons.injEq, Pattern.lambda.injEq, and_true] at same
            obtain ⟨rfl, rfl, rfl, rfl⟩ := same
            have sortSame : sort' = sort := by
              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at sorted sorted'
              rcases sorted with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases sorted' with ⟨same, rfl⟩ | ⟨same, rfl⟩ <;>
                simp_all
            subst sortSame
            exact reads fuel enough
          · refine ⟨0, fun fuel _ => ⟨fun label at' name continuation same listed =>
              absurd ⟨label, at', name, continuation, same, listed⟩ isCont, fun label at' binder body sort same sorted =>
              absurd ⟨label, at', binder, body, same, ?_⟩ isBody⟩⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at sorted
            rcases sorted with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
    refine ⟨low + 2 * components.length + 3, fun fuel enough => ?_⟩
    obtain ⟨fuel, rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
    simp only [decodeForm, Prenex.toPattern]
    refine restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count ?_
    refine readPlaced_map_from (low := low) fuel _ (by omega) members changedMembers
      (fun component member => (facts component member).1) ?_
    intro component member fuel' floor place' first second isPlaced firstMembers secondMembers children
    have placed : placeAt component = some place' := by simpa [placedAt] using isPlaced
    rcases well.canonPart_shape locVariables member (objects _ member) with same |
        ⟨label, at', name, continuation, rfl, listed, same⟩ | ⟨at', message, continuation, rfl, same⟩ |
        ⟨label, at', binder, body, rfl, listed, same⟩
    · rw [same]
      exact readComponent_equivalent (members component member) children
    · rw [same]
      have notMarker := not_marker_of_capability listed
      rw [placeAt_capability listed, Option.some.injEq] at placed
      subst placed
      have nameVar := (well.names _ member name (by simp [nameOf, notMarker, listed])).1
      have nameTyped : HasType ambientCoreCalc free (List.replicate count nameType ++ bound) name nameType := by
        rcases triple_inv (members _ member) with ⟨isMarker, -⟩ | ⟨-, nameTyped, -⟩ | ⟨rfl, -, -⟩
        · exact absurd listed (not_capability_of_marker isMarker)
        · exact variable_typed nameTyped nameVar
        · simp [capabilities] at listed
      obtain ⟨-, -, continuationTyped, continuationObject, -⟩ :=
        continuationFacts _ member label at' name continuation rfl (.inl listed)
      simp only [readComponent, if_neg notMarker, if_pos listed, if_pos nameVar]
      rw [decompose_canonR continuationTyped continuationObject]
      exact prefix_fill (ambientCapability_mem listed) nameTyped
        ((lowReads _ member fuel' floor).1 label at' name continuation rfl (.inl listed))
    · rw [same]
      rw [placeAt_cap, Option.some.injEq] at placed
      subst placed
      have messageIs := (well.messages _ member message (by simp [messageOf])).1
      have messageTyped : HasType ambientCoreCalc free (List.replicate count nameType ++ bound) message capType := by
        rcases triple_inv (members _ member) with ⟨isMarker, -⟩ | ⟨listed, -, -⟩ | ⟨-, typed, -⟩
        · simp [markers] at isMarker
        · simp [capabilities] at listed
        · exact message_typed typed messageIs
      obtain ⟨-, -, continuationTyped, continuationObject, -⟩ :=
        continuationFacts _ member "LCap" at' message continuation rfl (.inr rfl)
      rw [readComponent_cap, readComponent_cap, if_pos messageIs, if_pos messageIs]
      simp only [decodeAt]
      rw [decompose_canonR continuationTyped continuationObject]
      exact acap_fill messageTyped ((lowReads _ member fuel' floor).1 "LCap" at' message continuation rfl (.inr rfl))
    · rw [same]
      rw [placeAt_input listed, Option.some.injEq] at placed
      subst placed
      obtain ⟨-, rfl, sort, sorted, -, bodyTyped, bodyObject, -⟩ := bodyFacts _ member label at' binder body rfl listed
      rw [readComponent_input listed, readComponent_input listed]
      simp only [decodeAt]
      rw [decompose_canonR bodyTyped bodyObject]
      exact input_fill (ambientInput_listed sorted)
        ((lowReads _ member fuel' floor).2 label at' none body sort rfl sorted)

/-! ## Replications replaced by their canonical molecules -/

/-- **Replications replaced by the molecules of their canonical forms read equivalently**, wherever the block is
read, when each replication's molecules sit at its place and read together as it does. -/
theorem readPlaced_replace_replications {bound : List TypeExpr} (place : Pattern) :
    ∀ (replications kept : List Pattern),
      Members locatedCalc locatedBlock free bound (kept ++ replications) →
      (∀ replication ∈ replications, ∃ argument at', replication = .apply "LRep" [argument] ∧
        placeAt replication = some at' ∧
        Members locatedCalc locatedBlock free bound (canonP locatedRepBlock replication).components ∧
        (∀ molecule ∈ (canonP locatedRepBlock replication).components, placeAt molecule = some at') ∧
        ∃ least, ∀ fuel, least ≤ fuel → ∀ elsewhere : List Pattern, ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.body ambientBlock ((canonP locatedRepBlock replication).components.map
            fun molecule => readComponent fuel at' molecule elsewhere))
          (readComponent fuel at' replication elsewhere)) →
      ∃ least, ∀ fuel, least ≤ fuel → ProcEquiv ambientCoreCalc ambientBlock free bound
        (Prenex.body ambientBlock (readPlaced fuel place
          (kept ++ replications.flatMap fun replication => (canonP locatedRepBlock replication).components)))
        (Prenex.body ambientBlock (readPlaced fuel place (kept ++ replications)))
  | [], kept, _, _ => ⟨0, fun fuel _ => by simp only [List.flatMap_nil]; exact .refl _⟩
  | replication :: rest, kept, members, facts => by
      obtain ⟨argument, at', rfl, sits, moleculesMembers, moleculesSit, least₀, reads₀⟩ :=
        facts _ List.mem_cons_self
      have restFacts : ∀ other ∈ rest, _ := fun other member => facts other (List.mem_cons_of_mem _ member)
      have movedMembers : Members locatedCalc locatedBlock free bound
          ((kept ++ [.apply "LRep" [argument]]) ++ rest) := by
        rw [List.append_assoc]
        exact members
      obtain ⟨least₁, reads₁⟩ := readPlaced_replace_replications place rest (kept ++ [.apply "LRep" [argument]])
        movedMembers restFacts
      set molecules := (canonP locatedRepBlock (.apply "LRep" [argument])).components with moleculesIs
      set restMolecules := rest.flatMap fun other => (canonP locatedRepBlock other).components with restMoleculesIs
      have keptMembers : Members locatedCalc locatedBlock free bound kept := fun element member =>
        members element (List.mem_append_left _ member)
      have replicationTyped : HasType locatedCalc free bound (.apply "LRep" [argument]) procType :=
        members _ (List.mem_append_right _ List.mem_cons_self)
      have restMoleculesMembers : Members locatedCalc locatedBlock free bound restMolecules := by
        intro element member
        obtain ⟨other, otherIn, inMolecules⟩ := List.mem_flatMap.mp member
        obtain ⟨-, -, -, -, otherMembers, -⟩ := restFacts other otherIn
        exact otherMembers element inMolecules
      have componentsMembers : Members locatedCalc locatedBlock free bound (kept ++ restMolecules) :=
        keptMembers.append restMoleculesMembers
      refine ⟨max least₁ (least₀ + 2 * (kept ++ restMolecules).length + 2), fun fuel enough => ?_⟩
      have first := readPlaced_perm fuel place
        (show (kept ++ (molecules ++ restMolecules)).Perm (molecules ++ (kept ++ restMolecules)) by
          simpa [List.append_assoc] using (List.perm_append_comm (l₁ := kept) (l₂ := molecules)).append_right
            restMolecules)
        (keptMembers.append (moleculesMembers.append restMoleculesMembers))
      have second := readPlaced_replace_replication sits moleculesSit reads₀ moleculesMembers replicationTyped fuel
        place (by omega) componentsMembers
      have third := readPlaced_perm fuel place
        (show (Pattern.apply "LRep" [argument] :: (kept ++ restMolecules)).Perm
            ((kept ++ [.apply "LRep" [argument]]) ++ restMolecules) by
          rw [List.append_assoc, List.singleton_append]
          exact List.perm_middle.symm)
        (Members.cons replicationTyped componentsMembers)
      have fourth := reads₁ fuel (le_of_max_le_left enough)
      simp only [List.flatMap_cons]
      rw [show kept ++ Pattern.apply "LRep" [argument] :: rest = (kept ++ [.apply "LRep" [argument]]) ++ rest by simp]
      exact .trans _ _ _ first (.trans _ _ _ second (.trans _ _ _ third fourth))

/-! ## A block's canonical form, read back -/

open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (canonP_restricts_bag bag_perm_equivalent restricts_typed
  isObject_bag isObject_restricts mass_decompose)
open Mettapedia.GSLT.LanguageDef.BagNormalForm (elementsHaveType_iff)

/-- A component of a well-located block holds the same location read canonically. -/
theorem WellLocated.childOf_canonPart {isLoc : Pattern → Prop} {place : Pattern} {count : Nat}
    {components : List Pattern} (well : WellLocated isLoc place ⟨count, components⟩) (locVariables : LocVariables isLoc)
    {component : Pattern} (member : component ∈ components) (object : isObjectPattern component = true) :
    childOf (canonPart component) = childOf component := by
  rcases well.canonPart_shape locVariables member object with same | ⟨label, at', name, continuation, rfl, listed, same⟩ |
      ⟨at', message, continuation, rfl, same⟩ | ⟨label, at', binder, body, rfl, listed, same⟩
  · rw [same]
  · rw [same]
    simp [childOf, not_marker_of_capability listed]
  · rw [same]
    simp [childOf, markers]
  · rw [same]
    simp [childOf]

/-- Blocks of no restrictions side by side are one block of their components. -/
theorem foldr_par_count_zero : ∀ (forms : List Prenex), (∀ form ∈ forms, form.count = 0) →
    forms.foldr Prenex.par Prenex.nil = ⟨0, forms.flatMap Prenex.components⟩
  | [], _ => rfl
  | form :: rest, counts => by
      rw [List.foldr_cons, foldr_par_count_zero rest fun other member => counts other (List.mem_cons_of_mem _ member)]
      obtain ⟨count, components⟩ := form
      have zero : count = 0 := counts _ List.mem_cons_self
      subst zero
      have liftZero : liftBVars 0 0 = id := funext fun pattern =>
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero pattern 0
      simp [Prenex.par, liftZero]

/-- **A well-located block reads back as its canonical form in the located calculus does.** -/
theorem decode_canonForm (form : Prenex) : CanonFormFacts free form := by
  suffices all : ∀ weight, ∀ form : Prenex, form.mass < weight → CanonFormFacts free form from
    fun {_ _ _} well locVariables context members objects =>
      all _ form (Nat.lt_succ_self _) well locVariables context members objects
  intro weight
  induction weight with
  | zero => intro form light; omega
  | succ weight recurse =>
      intro form light
      have canonBelow : CanonFormBelow free form.mass := fun lighter lighterMass => recurse lighter (by omega)
      intro isLoc outer bound well locVariables context members objects
      obtain ⟨count, components⟩ := form
      have signature : Mettapedia.GSLT.LanguageDef.RestrictionBlocks.BlockSignature locatedCalc locatedBlock :=
        Mettapedia.Languages.ProcessCalculi.Ambient.Located.locatedLanguage.toBlockSignature
      have fresh : locatedRepBlock.replicate ∉ locatedRepBlock.emptyUnits := by decide
      have restrictFresh : locatedRepBlock.replicate ≠ locatedRepBlock.restrict := by decide
      have innerContext := context.replicate count "Name"
      have insideVariables := insideLoc_locVariables isLoc count components
      simp only at members objects
      -- the continuations read canonically
      obtain ⟨changedWell, changedMembers, -, least₁, reads₁⟩ :=
        decode_canonParts well locVariables context members objects canonBelow
      -- the replications, and the other components
      set replications := components.filter (isReplicated locatedRepBlock) with replicationsIs
      set others := components.filter (fun component => !isReplicated locatedRepBlock component) with othersIs
      have split : components.Perm (others ++ replications) :=
        (List.filter_append_perm (isReplicated locatedRepBlock) components).symm.trans List.perm_append_comm
      have othersIn : ∀ part ∈ others, part ∈ components := fun part member => (List.mem_filter.mp member).1
      have replicationsIn : ∀ replication ∈ replications, replication ∈ components := fun replication member =>
        (List.mem_filter.mp member).1
      have notReplicated : ∀ part ∈ others, isReplicated locatedRepBlock part = false := fun part member => by
        simpa using (List.mem_filter.mp member).2
      have othersCanon : others.map canonPart = others.map (canonR locatedRepBlock) :=
        List.map_congr_left fun part member => by
          unfold canonPart
          rw [if_neg (by simp [notReplicated part member])]
      have replicationsKept : replications.map canonPart = replications := by
        conv_rhs => rw [← List.map_id replications]
        exact List.map_congr_left fun replication member => by
          unfold canonPart
          rw [if_pos (List.mem_filter.mp member).2]
          rfl
      -- each replication's canonical form, at its place
      have replicationFacts : ∀ replication ∈ replications, ∃ argument index,
          replication = .apply "LRep" [argument] ∧ placeAt replication = some (.bvar index) ∧
          (canonP locatedRepBlock replication).count = 0 ∧
          WellLocated (insideLoc isLoc count components) (.bvar index) (canonP locatedRepBlock replication) ∧
          Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
            (canonP locatedRepBlock replication).components ∧
          (∀ molecule ∈ (canonP locatedRepBlock replication).components, isObjectPattern molecule = true ∧
            placeAt molecule = some (.bvar index) ∧ ∃ inner, molecule = .apply "LRep" [inner]) ∧
          ∃ least, ∀ fuel, least ≤ fuel → ∀ elsewhere : List Pattern, ProcEquiv ambientCoreCalc ambientBlock free
            (List.replicate count nameType ++ bound)
            (Prenex.body ambientBlock ((canonP locatedRepBlock replication).components.map
              fun molecule => readComponent fuel (.bvar index) molecule elsewhere))
            (readComponent fuel (.bvar index) replication elsewhere) := by
        intro replication member
        obtain ⟨argument, rfl⟩ := isReplicated_shape (List.mem_filter.mp member).2
        have inComponents := (List.mem_filter.mp member).1
        obtain ⟨at', sits⟩ := Option.isSome_iff_exists.mp (well.repsPlaced _ inComponents argument rfl)
        have atBvar : ∃ index, at' = .bvar index := by
          rcases well.placed _ inComponents at' sits with same | ⟨index, -, same, -⟩
          · exact ⟨outer + count, by rw [same]; simp [liftBVars]⟩
          · exact ⟨index, same⟩
        obtain ⟨index, rfl⟩ := atBvar
        have innerWell := match well with
          | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ inComponents argument _ rfl sits
        have argumentTyped := rep_inv (members _ inComponents)
        have argumentObject : isObjectPattern argument = true := by
          have object := objects _ inComponents
          simpa [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList] using object
        have lighter : (decompose locatedBlock argument).mass < (Prenex.mk count components).mass := by
          have massLe := mass_decompose (block := locatedBlock) argument
          have inSize := size_le_sizeList inComponents
          have formMass : (Prenex.mk count components).mass = 2 * count + sizeList components := rfl
          simp only [size, sizeList] at inSize
          omega
        obtain ⟨countZero, canonWell, canonMembers, moleculeFacts, least, reads⟩ :=
          replication_canonForm innerWell insideVariables innerContext argumentTyped argumentObject
            (canonBelow _ lighter)
        exact ⟨argument, index, rfl, sits, countZero, canonWell, canonMembers, moleculeFacts, least, reads⟩
      set molecules := replications.flatMap fun replication => (canonP locatedRepBlock replication).components
        with moleculesIs
      -- the canonical form: the other components read canonically beside the molecules, normalized
      have othersObjects : ∀ part ∈ others, isObjectPattern part = true := fun part member =>
        objects part (othersIn part member)
      have replicationsObjects : ∀ replication ∈ replications, isObjectPattern replication = true :=
        fun replication member => objects replication (replicationsIn replication member)
      have othersAtoms : ∀ part ∈ others, canonP locatedRepBlock part = Prenex.atom (canonR locatedRepBlock part) := by
        intro part member
        have inComponents := othersIn part member
        have placeVar : ∀ at', placeAt part = some at' → isVariable at' = true := fun at' isPlaced =>
          insideLoc_locVariables isLoc count components at' (well.placeInside locVariables part inComponents at' isPlaced)
        have isAtom : ∃ atom, canonP locatedRepBlock part = Prenex.atom atom := by
          cases kind : well.kinds part inComponents with
          | @marker markerLabel parent name index isMarker below =>
              have notRestrict : markerLabel ≠ "LNu" := by
                simp only [markers, List.mem_cons, List.not_mem_nil, or_false] at isMarker
                rcases isMarker with rfl | rfl <;> decide
              exact ⟨_, canonP_triple notRestrict (placeVar parent (placeAt_ofMarker isMarker _ _ _)) rfl
                (variable_object (well.names _ inComponents name (by simp [nameOf, isMarker])).1)⟩
          | @capability label at' name continuation listed =>
              have notRestrict : label ≠ "LNu" := by
                simp only [capabilities, List.mem_cons, List.not_mem_nil, or_false] at listed
                rcases listed with rfl | rfl | rfl <;> decide
              have notMarker := not_marker_of_capability listed
              have continuationObject : isObjectPattern continuation = true := by
                have object := objects _ inComponents
                simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at object
                exact object.2.2.1
              exact ⟨_, canonP_triple notRestrict (placeVar at' (placeAt_capability listed _ _ _))
                (well.names _ inComponents name (by simp [nameOf, notMarker, listed])).1 continuationObject⟩
          | @replication argument => exact absurd (notReplicated _ member) (by simp [isReplicated])
          | @cap at' message continuation =>
              have continuationObject : isObjectPattern continuation = true := by
                have object := objects _ inComponents
                simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList,
                  Bool.and_eq_true] at object
                exact object.2.2.1
              exact ⟨_, canonP_cap (placeVar at' (placeAt_cap _ _ _))
                (well.messages _ inComponents message (by simp [messageOf])).1 continuationObject⟩
          | @input label at' binder body listed =>
              have bodyObject : isObjectPattern body = true := by
                have object := objects _ inComponents
                simp only [isObjectPattern, Mettapedia.GSLT.LanguageDef.WellSorted.isObjectPatternList,
                  Bool.and_eq_true, Bool.and_true] at object
                exact object.2
              exact ⟨_, canonP_input listed (placeVar at' (placeAt_input listed _ _)) bodyObject⟩
          | @output label at' message listed =>
              exact ⟨_, canonP_output listed (placeVar at' (placeAt_output listed _ _))
                (well.messages _ inComponents message (by simp [messageOf, listed])).1⟩
        obtain ⟨atom, isAtom⟩ := isAtom
        have canonIs : canonR locatedRepBlock part = atom := by
          unfold canonR
          rw [isAtom]
          rfl
        rw [isAtom, canonIs]
      have restIs : (replications.map (canonP locatedRepBlock)).foldr Prenex.par Prenex.nil = ⟨0, molecules⟩ := by
        rw [foldr_par_count_zero _ fun canonical member => by
          obtain ⟨replication, inReplications, rfl⟩ := List.mem_map.mp member
          obtain ⟨-, -, -, -, countZero, -⟩ := replicationFacts replication inReplications
          exact countZero]
        simp [moleculesIs, List.flatMap_map]
      have patternTyped : HasType locatedCalc free bound (Prenex.toPattern locatedBlock ⟨count, components⟩) procType :=
        restricts_typed (language := locatedCalc) (block := locatedBlock) count (body_typed members)
      have bagMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
          (others ++ replications) := fun element member => members element (split.symm.subset member)
      have bagTyped : HasType locatedCalc free bound
          (Prenex.restricts locatedBlock count (.collection .hashBag (others ++ replications) none)) procType :=
        restricts_typed (language := locatedCalc) (block := locatedBlock) count
          (signature.bag_typed (rest := none) (elementsHaveType_iff.mpr bagMembers))
      have patternObject : isObjectPattern (Prenex.toPattern locatedBlock ⟨count, components⟩) = true :=
        isObject_toPattern objects
      have bagObject : isObjectPattern
          (Prenex.restricts locatedBlock count (.collection .hashBag (others ++ replications) none)) = true := by
        rw [isObject_restricts, isObject_bag]
        intro element member
        exact objects element (split.symm.subset member)
      have equivalent : ProcEquiv locatedCalc locatedBlock free bound (Prenex.toPattern locatedBlock ⟨count, components⟩)
          (Prenex.restricts locatedBlock count (.collection .hashBag (others ++ replications) none)) := by
        simp only [Prenex.toPattern]
        refine restricts_congr (language := locatedCalc) (block := locatedBlock) count ?_
        exact .trans _ _ _ (Relation.EqvGen.symm _ _ (bag_body_equivalent members))
          (bag_perm_equivalent (language := locatedCalc) (block := locatedRepBlock) members split)
      have canonIs : canonP locatedRepBlock (Prenex.toPattern locatedBlock ⟨count, components⟩) =
          normal locatedRepBlock ⟨count, others.map canonPart ++ molecules⟩ := by
        have same := canonR_complete (block := locatedRepBlock) (base := engineBasePremises RelationEnv.empty)
          patternObject bagObject (restrictionsBind_of_typed (block := locatedRepBlock) _ patternTyped)
          (SortedEquiv.toEquationEquiv equivalent)
        have firstFacts := canonFacts fresh restrictFresh patternObject
          (restrictionsBind_of_typed (block := locatedRepBlock) _ patternTyped)
        have secondFacts := canonFacts fresh restrictFresh bagObject
          (restrictionsBind_of_typed (block := locatedRepBlock) _ bagTyped)
        have decomposed := congrArg (decompose locatedRepBlock.toBlock) same
        unfold canonR at decomposed
        rw [decompose_toPattern firstFacts.atomic firstFacts.used,
          decompose_toPattern secondFacts.atomic secondFacts.used] at decomposed
        rw [decomposed, canonP_restricts_bag fresh restrictFresh count othersObjects replicationsObjects
          (fun part member => restrictionsBind_of_typed (block := locatedRepBlock) _ (members _ (othersIn part member)))
          (fun replication member => restrictionsBind_of_typed (block := locatedRepBlock) _
            (members _ (replicationsIn replication member))) othersAtoms, restIs, othersCanon]
        have liftZero : liftBVars 0 0 = id := funext fun pattern =>
          Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero pattern 0
        simp [liftZero]
      -- the block of the other components read canonically beside the molecules: well-located and typed
      have moleculesIn : ∀ molecule ∈ molecules, ∃ replication ∈ replications,
          molecule ∈ (canonP locatedRepBlock replication).components := fun molecule member => by
        simpa using List.mem_flatMap.mp member
      have othersChanged : ∀ component ∈ others.map canonPart, component ∈ components.map canonPart :=
        fun component member => by
          obtain ⟨original, originalIn, rfl⟩ := List.mem_map.mp member
          exact List.mem_map_of_mem (othersIn original originalIn)
      have moleculeShape : ∀ molecule ∈ molecules, ∃ replication ∈ replications, ∃ argument index inner,
          replication = .apply "LRep" [argument] ∧ placeAt replication = some (.bvar index) ∧
          molecule = .apply "LRep" [inner] ∧ placeAt molecule = some (.bvar index) ∧
          molecule ∈ (canonP locatedRepBlock replication).components := by
        intro molecule member
        obtain ⟨replication, inReplications, inMolecules⟩ := moleculesIn molecule member
        obtain ⟨argument, index, isReplication, sits, -, -, -, moleculeFacts, -⟩ :=
          replicationFacts replication inReplications
        obtain ⟨-, moleculeSits, inner, isMolecule⟩ := moleculeFacts molecule inMolecules
        exact ⟨replication, inReplications, argument, index, inner, isReplication, sits, isMolecule, moleculeSits,
          inMolecules⟩
      have markedChanged : ∀ index, Marked (components.map canonPart) index ↔ Marked components index := by
        intro index
        constructor
        · rintro ⟨marker, member, isChild⟩
          obtain ⟨original, inComponents, rfl⟩ := List.mem_map.mp member
          exact ⟨original, inComponents, by
            rw [← well.childOf_canonPart locVariables inComponents (objects _ inComponents)]; exact isChild⟩
        · rintro ⟨marker, member, isChild⟩
          exact ⟨_, List.mem_map_of_mem member, by
            rw [well.childOf_canonPart locVariables member (objects _ member)]; exact isChild⟩
      have markedJoined : ∀ index, Marked (others.map canonPart ++ molecules) index ↔ Marked components index := by
        intro index
        constructor
        · rintro ⟨marker, member, isChild⟩
          rcases List.mem_append.mp member with inOthers | inMolecules
          · exact (markedChanged index).mp ⟨marker, othersChanged marker inOthers, isChild⟩
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape marker inMolecules
            simp [childOf] at isChild
        · rintro ⟨marker, member, isChild⟩
          have notRep : isReplicated locatedRepBlock marker = false := by
            cases found : isReplicated locatedRepBlock marker with
            | false => rfl
            | true =>
                obtain ⟨argument, rfl⟩ := isReplicated_shape found
                simp [childOf] at isChild
          refine ⟨canonPart marker, List.mem_append_left _ (List.mem_map_of_mem
            (List.mem_filter.mpr ⟨member, by simp [notRep]⟩)), ?_⟩
          rw [well.childOf_canonPart locVariables member (objects _ member)]
          exact isChild
      have insideJoined : insideLoc isLoc count (others.map canonPart ++ molecules) =
          insideLoc isLoc count (components.map canonPart) := by
        funext pattern
        apply propext
        cases pattern with
        | bvar index =>
            simp only [insideLoc]
            split_ifs
            · exact (markedJoined index).trans (markedChanged index).symm
            · exact Iff.rfl
        | _ => exact Iff.rfl
      have insideChanged : insideLoc isLoc count (components.map canonPart) = insideLoc isLoc count components := by
        funext pattern
        apply propext
        cases pattern with
        | bvar index =>
            simp only [insideLoc]
            split_ifs
            · exact markedChanged index
            · exact Iff.rfl
        | _ => exact Iff.rfl
      have joinedMembers : Members locatedCalc locatedBlock free (List.replicate count nameType ++ bound)
          (others.map canonPart ++ molecules) := by
        intro component member
        rcases List.mem_append.mp member with inOthers | inMolecules
        · exact changedMembers component (othersChanged component inOthers)
        · obtain ⟨replication, inReplications, -, -, -, -, -, -, -, inMolecules⟩ :=
            moleculeShape component inMolecules
          obtain ⟨-, -, -, -, -, -, moleculesMembers, -⟩ := replicationFacts replication inReplications
          exact moleculesMembers component inMolecules
      have joinedWell : WellLocated isLoc (.bvar outer) ⟨count, others.map canonPart ++ molecules⟩ := by
        refine .intro well.placeIsLoc (fun component member => ?_) (fun component member at' isPlaced => ?_)
          (fun index => ?_) (fun component member name isName => ?_)
          (fun component member label at' name continuation isCap listed => ?_)
          (fun component member argument at' isRep isPlaced => ?_) (fun component member argument isRep => ?_) ?_
          (fun component member message isMsgOf => ?_)
          (fun component member at' message continuation isCapComponent => ?_)
          (fun component member label at' binder body isInput listed => ?_)
        · rcases List.mem_append.mp member with inOthers | inMolecules
          · exact changedWell.kinds component (othersChanged component inOthers)
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component inMolecules
            exact .replication
        · rcases List.mem_append.mp member with inOthers | inMolecules
          · rcases changedWell.placed component (othersChanged component inOthers) at' isPlaced with
                same | ⟨index, below, same, isMarked⟩
            · exact .inl same
            · exact .inr ⟨index, below, same, (markedJoined index).mpr ((markedChanged index).mp isMarked)⟩
          · obtain ⟨replication, inReplications, argument, index, inner, rfl, sits, rfl, moleculeSits, -⟩ :=
              moleculeShape component inMolecules
            rw [moleculeSits, Option.some.injEq] at isPlaced
            subst isPlaced
            rcases well.placed _ (replicationsIn _ inReplications) _ sits with same | ⟨index', below, same, isMarked⟩
            · exact .inl same
            · exact .inr ⟨index', below, same, (markedJoined index').mpr isMarked⟩
        · have whole := changedWell.unique index
          simp only at whole ⊢
          rw [List.filter_append]
          have moleculesNone : molecules.filter (fun component => childOf component == some (.bvar index)) = [] :=
            List.filter_eq_nil_iff.mpr fun component member => by
              obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component member
              simp [childOf]
          rw [moleculesNone, List.append_nil]
          refine le_trans (List.Sublist.length_le ?_) whole
          refine List.Sublist.filter _ ?_
          rw [othersIs]
          exact (List.filter_sublist).map canonPart
        · rw [insideJoined]
          rcases List.mem_append.mp member with inOthers | inMolecules
          · exact changedWell.names component (othersChanged component inOthers) name isName
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component inMolecules
            simp [nameOf] at isName
        · rw [insideJoined]
          rcases List.mem_append.mp member with inOthers | inMolecules
          · exact match changedWell with
              | .intro _ _ _ _ _ caps _ _ _ _ _ _ => caps _ (othersChanged component inOthers) label at' name continuation
                  isCap listed
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component inMolecules
            cases isCap
        · rw [insideJoined, insideChanged]
          rcases List.mem_append.mp member with inOthers | inMolecules
          · rw [← insideChanged]
            exact match changedWell with
              | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ (othersChanged component inOthers) argument at' isRep isPlaced
          · obtain ⟨replication, inReplications, -, index, inner, -, -, isMolecule, moleculeSits, inMolecules'⟩ :=
              moleculeShape component inMolecules
            subst isMolecule
            simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at isRep
            subst isRep
            obtain ⟨argument', index', isReplication', sits', countZero', canonWell, rest'⟩ :=
              replicationFacts replication inReplications
            have canonWell' : WellLocated (insideLoc isLoc count components) (.bvar index')
                ⟨(canonP locatedRepBlock replication).count, (canonP locatedRepBlock replication).components⟩ :=
              canonWell
            have moleculeWell := match canonWell' with
              | .intro _ _ _ _ _ _ reps _ _ _ _ _ => reps _ inMolecules' inner at' rfl isPlaced
            have insideZero : insideLoc (insideLoc isLoc count components) (canonP locatedRepBlock replication).count
                (canonP locatedRepBlock replication).components = insideLoc isLoc count components := by
              funext pattern
              cases pattern with
              | bvar index'' => simp [insideLoc, countZero']
              | fvar name => rfl
              | _ => rfl
            rw [insideZero] at moleculeWell
            exact moleculeWell
        · rcases List.mem_append.mp member with inOthers | inMolecules
          · exact changedWell.repsPlaced component (othersChanged component inOthers) argument isRep
          · obtain ⟨-, -, -, index, -, -, -, -, moleculeSits, -⟩ := moleculeShape component inMolecules
            rw [moleculeSits]
            rfl
        · obtain ⟨depth, grows⟩ := (changedWell.nested : Nested count (components.map canonPart))
          refine ⟨depth, fun component member index child below childBelow isPlaced isChild => ?_⟩
          rcases List.mem_append.mp member with inOthers | inMolecules
          · exact grows component (othersChanged component inOthers) index child below childBelow isPlaced isChild
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component inMolecules
            simp [childOf] at isChild
        · rw [insideJoined]
          rcases List.mem_append.mp member with inOthers | inMolecules
          · exact changedWell.messages component (othersChanged component inOthers) message isMsgOf
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component inMolecules
            simp [messageOf] at isMsgOf
        · rw [insideJoined]
          rcases List.mem_append.mp member with inOthers | inMolecules
          · exact changedWell.capConts component (othersChanged component inOthers) at' message continuation
              isCapComponent
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component inMolecules
            simp at isCapComponent
        · rw [insideJoined]
          rcases List.mem_append.mp member with inOthers | inMolecules
          · exact changedWell.bodies component (othersChanged component inOthers) label at' binder body isInput listed
          · obtain ⟨-, -, -, -, inner, -, -, rfl, -⟩ := moleculeShape component inMolecules
            simp at isInput
      -- the molecules read as the replications
      obtain ⟨normalWell, normalReads⟩ := decode_normal (free := free) ⟨count, others.map canonPart ++ molecules⟩
        joinedWell locVariables context joinedMembers
      obtain ⟨least₂, reads₂⟩ := readPlaced_replace_replications (bound := List.replicate count nameType ++ bound)
        (liftBVars 0 count (.bvar outer)) replications (others.map canonPart)
        (fun element member => by
          rcases List.mem_append.mp member with inOthers | inReplications
          · exact changedMembers element (othersChanged element inOthers)
          · exact members element (replicationsIn element inReplications))
        (fun replication member => by
          obtain ⟨argument, index, isReplication, sits, -, -, moleculesMembers, moleculeFacts, least, reads⟩ :=
            replicationFacts replication member
          exact ⟨argument, .bvar index, isReplication, sits, moleculesMembers,
            fun molecule inMolecules => (moleculeFacts molecule inMolecules).2.1, least, reads⟩)
      rw [canonIs]
      refine ⟨normalWell, ?_, max (max (least₁ + 1) (least₂ + 1))
        (max (3 * (Prenex.mk count (others.map canonPart ++ molecules)).mass + 3)
          (3 * (normal locatedRepBlock ⟨count, others.map canonPart ++ molecules⟩).mass + 3)), fun fuel enough => ?_⟩
      · exact (normal_sound (language := locatedCalc) (block := locatedRepBlock) context
          (form := ⟨count, others.map canonPart ++ molecules⟩) joinedMembers).1
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have replaced : ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.toPattern ambientBlock (decodeForm (f + 1) (.bvar outer)
            ⟨count, others.map canonPart ++ molecules⟩))
          (Prenex.toPattern ambientBlock (decodeForm (f + 1) (.bvar outer)
            ⟨count, others.map canonPart ++ replications⟩)) := by
        simp only [decodeForm, Prenex.toPattern]
        exact restricts_congr (language := ambientCoreCalc) (block := ambientBlock) count (reads₂ f (by omega))
      have reordered : ProcEquiv ambientCoreCalc ambientBlock free bound
          (Prenex.toPattern ambientBlock (decodeForm (f + 1) (.bvar outer)
            ⟨count, others.map canonPart ++ replications⟩))
          (Prenex.toPattern ambientBlock (decodeForm (f + 1) (.bvar outer) ⟨count, components.map canonPart⟩)) := by
        refine decode_perm f _ ?_ (fun element member => by
          rcases List.mem_append.mp member with inOthers | inReplications
          · exact changedMembers element (othersChanged element inOthers)
          · exact members element (replicationsIn element inReplications))
        rw [← replicationsKept, ← List.map_append]
        exact (split.map canonPart).symm
      exact .trans _ _ _ (normalReads (f + 1) (by omega) (by omega))
        (.trans _ _ _ replaced (.trans _ _ _ reordered (reads₁ (f + 1) (by omega))))

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
