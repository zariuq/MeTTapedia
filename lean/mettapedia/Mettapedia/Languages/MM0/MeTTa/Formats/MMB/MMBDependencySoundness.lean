import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBTheoremSoundness
import Mathlib.Data.List.Sigma

/-!
# Recorded MMB dependencies and kernel occurrence support

Assertion allocations record ranks of bound variables. The retained context
projection maps those ranks to context positions. Bounded ranks are necessary:
the projection's out-of-range fallback can collide with an allocated rank.
The store invariant below uses the existing kernel support judgment and the
actual allocated expressions; definition-mode free-variable dependencies are
a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBDependencySoundness

open Formats.MMB Kernel
open MMBMachineSoundness

theorem rankPositions_nodup (context : Context) : (Soundness.rankPositions context).Nodup := by
  exact (List.filter_sublist.map Prod.snd).nodup (List.nodup_zipIdx_map_snd context)

theorem rankPositions_getD_injective (context : Context) (first second : Nat)
    (firstBound : first < (Soundness.rankPositions context).length)
    (secondBound : second < (Soundness.rankPositions context).length)
    (same : (Soundness.rankPositions context).getD first first =
      (Soundness.rankPositions context).getD second second) : first = second := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem firstBound,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem secondBound] at same
  exact (rankPositions_nodup context).getElem_inj_iff.mp same

theorem positionsOf_union (context : Context) (first second : Finset Nat) :
    Soundness.positionsOf context (first ∪ second) =
      Soundness.positionsOf context first ∪ Soundness.positionsOf context second := by
  exact Finset.image_union _ _

theorem positionsOf_disjoint (context : Context) (first second : Finset Nat)
    (firstBound : ∀ rank ∈ first, rank < (Soundness.rankPositions context).length)
    (secondBound : ∀ rank ∈ second, rank < (Soundness.rankPositions context).length) :
    Disjoint (Soundness.positionsOf context first) (Soundness.positionsOf context second) ↔
      Disjoint first second := by
  constructor
  · intro disjoint
    rw [Finset.disjoint_left] at disjoint ⊢
    intro rank inFirst inSecond
    exact disjoint (Finset.mem_image_of_mem _ inFirst) (Finset.mem_image_of_mem _ inSecond)
  · intro disjoint
    rw [Finset.disjoint_left] at disjoint ⊢
    intro position inFirst inSecond
    obtain ⟨firstRank, firstMember, firstImage⟩ := Finset.mem_image.mp inFirst
    obtain ⟨secondRank, secondMember, secondImage⟩ := Finset.mem_image.mp inSecond
    have same := rankPositions_getD_injective context firstRank secondRank
      (firstBound firstRank firstMember) (secondBound secondRank secondMember)
      (firstImage.trans secondImage.symm)
    exact disjoint firstMember (same ▸ secondMember)

theorem supports_applyArgs (context : Context) (function : Preterm) (left : Finset Nat)
    (expressions : List Preterm) (types : List ExprType)
    (head : Preterm.Supports context function left)
    (children : List.Forall₂ (fun expression type =>
      Preterm.Supports context expression (Soundness.positionsOf context type.deps)) expressions types) :
    Preterm.Supports context (Preterm.applyArgs function expressions)
      (left ∪ Soundness.positionsOf context (appDeps .assertion [] ⟨0, false, ∅⟩ types)) := by
  induction children generalizing function left with
  | nil => simpa [Preterm.applyArgs, appDeps, Soundness.positionsOf] using head
  | cons first rest ih =>
      have applied := ih _ _ (Preterm.Supports.app head first)
      simpa [Preterm.applyArgs, appDeps, positionsOf_union, Finset.union_assoc] using applied

/-- Actual allocated expressions have complete kernel occurrence support
given by their recorded dependencies, and every recorded rank is allocated. -/
structure RankedStore (context : Context) (store : List Alloc) : Prop where
  supported : ∀ (position : Nat) (allocation : Alloc), store[position]? = some allocation →
    ∃ expression, Soundness.decode store position = some expression ∧
      Preterm.Supports context expression (Soundness.positionsOf context allocation.type.deps)
  bounded : ∀ (position : Nat) (allocation : Alloc), store[position]? = some allocation →
    ∀ rank ∈ allocation.type.deps, rank < (Soundness.rankPositions context).length

theorem RankedStore.arguments (context : Context) (store : List Alloc)
    (ranked : RankedStore context store) (positions : List Nat) (types : List ExprType)
    (read : positions.mapM (fun position => (store[position]?).map (·.type)) = some types) :
    ∃ expressions, positions.mapM (Soundness.decode store) = some expressions ∧
      List.Forall₂ (fun expression type =>
        Preterm.Supports context expression (Soundness.positionsOf context type.deps)) expressions types ∧
      ∀ type ∈ types, ∀ rank ∈ type.deps, rank < (Soundness.rankPositions context).length := by
  induction positions generalizing types with
  | nil =>
      have empty : [] = types := by simpa using read
      subst types
      exact ⟨[], rfl, .nil, by simp⟩
  | cons position positions ih =>
      cases first : (store[position]?).map (·.type) with
      | none => simp [first] at read
      | some type =>
          cases rest : positions.mapM (fun position => (store[position]?).map (·.type)) with
          | none => simp [first, rest] at read
          | some earlier =>
              have same : type :: earlier = types := by simpa [first, rest] using read
              subst types
              obtain ⟨allocation, allocationRead, sameType⟩ := Option.map_eq_some_iff.mp first
              obtain ⟨expression, decoded, support⟩ := ranked.supported position allocation allocationRead
              obtain ⟨expressions, decodedRest, supportedRest, boundedRest⟩ := ih earlier rest
              rw [sameType] at support
              refine ⟨expression :: expressions, by simp [decoded, decodedRest],
                .cons support supportedRest, ?_⟩
              intro source member rank occurs
              rcases List.mem_cons.mp member with same | later
              · subst source
                rw [← sameType] at occurs
                exact ranked.bounded position allocation allocationRead rank occurs
              · exact boundedRest source later rank occurs

theorem RankedStore.allocate_assertion_application (context : Context) (state : Formats.MMB.State)
    (ranked : RankedStore context state.store) (term : Nat) (positions : List Nat)
    (types targets : List ExprType) (ret : ExprType) (sort : Nat)
    (read : positions.mapM state.typeOf = some types) :
    RankedStore context (state.alloc
      ⟨.app term positions, ⟨sort, false, appDeps .assertion targets ret types⟩⟩).1.store := by
  change RankedStore context (state.store ++
    [⟨.app term positions, ⟨sort, false, appDeps .assertion targets ret types⟩⟩])
  obtain ⟨expressions, decoded, children, bounded⟩ := ranked.arguments context state.store positions types read
  have earlier := State.typesOf_allocated state positions types read
  have support : Preterm.Supports context (Preterm.applyArgs (.term term) expressions)
      (Soundness.positionsOf context (appDeps .assertion targets ret types)) := by
    simpa [appDeps] using supports_applyArgs context (.term term) ∅ expressions types (.term term) children
  constructor
  · intro position allocation found
    by_cases old : position < state.store.length
    · rw [List.getElem?_append_left old] at found
      obtain ⟨expression, expressionRead, supported⟩ := ranked.supported position allocation found
      exact ⟨expression, (MMBExecution.decode_append_preserves state.store _ position old).trans expressionRead, supported⟩
    · have inside := (List.getElem?_eq_some_iff.mp found).choose
      have last : position = state.store.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at inside
        omega
      subst position
      have allocationRead : (state.alloc
          ⟨.app term positions, ⟨sort, false, appDeps .assertion targets ret types⟩⟩).1.store[state.store.length]? =
          some ⟨.app term positions, ⟨sort, false, appDeps .assertion targets ret types⟩⟩ := by simp [State.alloc]
      have same := Option.some.inj (found.symm.trans allocationRead)
      subst allocation
      refine ⟨Preterm.applyArgs (.term term) expressions, ?_, support⟩
      have fresh := MMBExecution.decode_alloc_application state term positions
        ⟨sort, false, appDeps .assertion targets ret types⟩ earlier
      rw [decoded] at fresh
      exact fresh
  · intro position allocation found rank occurs
    by_cases old : position < state.store.length
    · rw [List.getElem?_append_left old] at found
      exact ranked.bounded position allocation found rank occurs
    · have inside := (List.getElem?_eq_some_iff.mp found).choose
      have last : position = state.store.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at inside
        omega
      subst position
      have allocationRead : (state.alloc
          ⟨.app term positions, ⟨sort, false, appDeps .assertion targets ret types⟩⟩).1.store[state.store.length]? =
          some ⟨.app term positions, ⟨sort, false, appDeps .assertion targets ret types⟩⟩ := by simp [State.alloc]
      have same := Option.some.inj (found.symm.trans allocationRead)
      subst allocation
      obtain ⟨source, member, childOccurs⟩ := (mem_appDeps_assertion targets ret types rank).mp occurs
      exact bounded source member rank childOccurs

theorem stepTerm_preserves_ranked_support (context : Context) (tables : Tables)
    (before after : Formats.MMB.State) (term : Nat) (save : Bool) (entry : TermEntry)
    (ranked : RankedStore context before.store)
    (entryRead : tables.terms[term]? = some entry)
    (executed : stepTerm tables .assertion before term save = some after) :
    RankedStore context after.store := by
  obtain ⟨positions, types, _, readings, _, store⟩ :=
    stepTerm_operands tables .assertion before after term save entry entryRead executed
  rw [store]
  exact ranked.allocate_assertion_application context before term positions types entry.args entry.ret entry.sort readings

theorem RankedStore.disjoint_bound_fresh (signature : TermSignature) (context : Context)
    (store : List Alloc) (ranked : RankedStore context store) (typed : TypedStore signature context store)
    (boundPosition otherPosition : Nat) (boundAllocation otherAllocation : Alloc)
    (boundRead : store[boundPosition]? = some boundAllocation)
    (otherRead : store[otherPosition]? = some otherAllocation)
    (bound : boundAllocation.type.bound = true)
    (disjoint : Disjoint otherAllocation.type.deps boundAllocation.type.deps) :
    ∃ index expression, Soundness.decode store boundPosition = some (.var index) ∧
      context[index]? = some (.bound boundAllocation.type.sort) ∧
      Soundness.decode store otherPosition = some expression ∧
      Preterm.FreshFor context index expression := by
  obtain ⟨boundImage, boundDecoded, _, boundTyping⟩ := typed.expression boundPosition boundAllocation boundRead
  obtain ⟨index, sameBound, boundLookup⟩ := boundTyping bound
  subst boundImage
  obtain ⟨supportedImage, supportedRead, boundSupport⟩ := ranked.supported boundPosition boundAllocation boundRead
  have sameSupported : supportedImage = Preterm.var index := Option.some.inj (supportedRead.symm.trans boundDecoded)
  subst supportedImage
  have boundDependencies : Soundness.positionsOf context boundAllocation.type.deps = {index} :=
    boundSupport.deterministic (.bound boundLookup)
  obtain ⟨expression, expressionRead, support⟩ := ranked.supported otherPosition otherAllocation otherRead
  have independent := (positionsOf_disjoint context otherAllocation.type.deps boundAllocation.type.deps
    (ranked.bounded otherPosition otherAllocation otherRead)
    (ranked.bounded boundPosition boundAllocation boundRead)).mpr disjoint
  rw [boundDependencies, Finset.disjoint_left] at independent
  refine ⟨index, expression, boundDecoded, boundLookup, expressionRead, ⟨⟨_, support⟩, ?_⟩⟩
  intro occurs
  exact independent ((support.mem_iff_hasVar index).mpr occurs) (by simp)

/-- The actual dummy guard earns freshness for every unsaved argument or
earlier dummy on the unifier heap. Saved expression nodes remain exempt. -/
theorem unify_definition_dummy_fresh (signature : TermSignature) (context : Context)
    (store : List Alloc) (ranked : RankedStore context store) (typed : TypedStore signature context store)
    (before after : Unifier) (sort : Nat)
    (executed : unifyStep store .definition before (.dummy sort) = some after) :
    ∃ position rest index, before.stack = position :: rest ∧
      after = { before with stack := rest, heap := before.heap ++ [(position, false)] } ∧
      Soundness.decode store position = some (.var index) ∧
      context[index]? = some (.bound sort) ∧
      ∀ other, (other, false) ∈ before.heap →
        ∃ expression, Soundness.decode store other = some expression ∧
          Preterm.FreshFor context index expression := by
  change (match before.stack with
    | position :: rest => (store[position]?).bind fun allocation =>
        match allocation.node with
        | .var _ => if allocation.type.bound ∧ allocation.type.sort = sort ∧
            before.heap.all (fun (entry, saved) => saved ||
              ((store[entry]?).map (fun a => decide (Disjoint a.type.deps allocation.type.deps))).getD false)
            then some { before with stack := rest, heap := before.heap ++ [(position, false)] }
            else none
        | .app _ _ => none
    | [] => none) = some after at executed
  split at executed
  · rename_i position rest shaped
    obtain ⟨allocation, allocationRead, checked⟩ := Option.bind_eq_some_iff.mp executed
    split at checked
    · split at checked
      · rename_i passed
        have sameAfter := (Option.some.inj checked).symm
        obtain ⟨bound, sameSort, guarded⟩ := passed
        obtain ⟨image, imageRead, _, boundTyping⟩ := typed.expression position allocation allocationRead
        obtain ⟨index, sameImage, lookup⟩ := boundTyping bound
        subst image
        refine ⟨position, rest, index, shaped, sameAfter, imageRead, ?_, ?_⟩
        · simpa only [sameSort] using lookup
        · intro other member
          have control := (List.all_eq_true.mp guarded) (other, false) member
          cases otherRead : store[other]? with
          | none => simp [otherRead] at control
          | some otherAllocation =>
              have disjoint : Disjoint otherAllocation.type.deps allocation.type.deps := by
                simpa [otherRead] using control
              obtain ⟨otherIndex, expression, boundDecoded, _, expressionRead, fresh⟩ :=
                ranked.disjoint_bound_fresh signature context store typed position other allocation otherAllocation
                  allocationRead otherRead bound disjoint
              have sameIndex : otherIndex = index := by
                have same := Option.some.inj (boundDecoded.symm.trans imageRead)
                cases same
                rfl
              subst otherIndex
              exact ⟨expression, expressionRead, fresh⟩
      · cases checked
    · cases checked
  · cases executed

/-- A successful ordered dependency check retains the complete histories
after any equally sized argument prefix. -/
theorem disjointness_after_prefix (firstTargets firstSources targets sources earlier : List ExprType)
    (boundDependencies : List (Finset Nat)) (lengths : firstTargets.length = firstSources.length)
    (accepted : thmArgsDisjoint.go (firstTargets ++ targets) (firstSources ++ sources)
      earlier boundDependencies = true) :
    thmArgsDisjoint.go targets sources (earlier ++ firstSources)
      (boundDependencies ++ ((firstTargets.zip firstSources).filter (·.1.bound)).map (·.2.deps)) = true := by
  induction firstTargets generalizing firstSources earlier boundDependencies with
  | nil =>
      have empty : firstSources = [] := List.length_eq_zero_iff.mp lengths.symm
      subst firstSources
      simpa using accepted
  | cons target firstTargets ih =>
      cases firstSources with
      | nil => simp at lengths
      | cons source firstSources =>
          have tailLength : firstTargets.length = firstSources.length := by simpa using lengths
          have rest : thmArgsDisjoint.go (firstTargets ++ targets) (firstSources ++ sources)
              (earlier ++ [source])
              (if target.bound then boundDependencies ++ [source.deps] else boundDependencies) = true := by
            simp only [List.cons_append, thmArgsDisjoint.go, Bool.and_eq_true] at accepted
            exact accepted.2
          have completed := ih firstSources (earlier ++ [source])
            (if target.bound then boundDependencies ++ [source.deps] else boundDependencies) tailLength rest
          cases targetBound : target.bound <;>
            simpa [targetBound, List.append_assoc] using completed

theorem disjointness_at_position (targets sources : List ExprType) (position : Nat)
    (target source : ExprType) (lengths : targets.length = sources.length)
    (targetRead : targets[position]? = some target) (sourceRead : sources[position]? = some source)
    (accepted : thmArgsDisjoint targets sources = true) :
    (if target.bound then
      (sources.take position).all (fun previous => Disjoint previous.deps source.deps)
    else
      ((((targets.take position).zip (sources.take position)).filter (·.1.bound)).map (·.2.deps)).zipIdx.all
        (fun (dependencies, rank) => rank ∈ target.deps || Disjoint dependencies source.deps)) = true := by
  obtain ⟨targetBound, targetAt⟩ := List.getElem?_eq_some_iff.mp targetRead
  obtain ⟨sourceBound, sourceAt⟩ := List.getElem?_eq_some_iff.mp sourceRead
  have targetSplit : targets = targets.take position ++ target :: targets.drop (position + 1) := by
    rw [← targetAt, ← List.drop_eq_getElem_cons targetBound, List.take_append_drop]
  have sourceSplit : sources = sources.take position ++ source :: sources.drop (position + 1) := by
    rw [← sourceAt, ← List.drop_eq_getElem_cons sourceBound, List.take_append_drop]
  have prefixRead : thmArgsDisjoint.go (targets.take position ++ target :: targets.drop (position + 1))
      (sources.take position ++ source :: sources.drop (position + 1)) [] [] = true := by
    rw [← targetSplit, ← sourceSplit]
    exact accepted
  have tailRead := disjointness_after_prefix (targets.take position) (sources.take position)
    (target :: targets.drop (position + 1)) (source :: sources.drop (position + 1)) [] []
    (by simp [lengths]) prefixRead
  simp only [List.nil_append, thmArgsDisjoint.go, Bool.and_eq_true] at tailRead
  exact tailRead.1

theorem zipIdx_filter_project {α : Type} (values : List α) (predicate : α → Bool) :
    (values.zipIdx.filter (fun row => predicate row.1)).map (·.1) = values.filter predicate := by
  simpa only [Function.comp_def, List.zipIdx_map_fst] using
    (List.filter_map (f := Prod.fst) (p := predicate) (l := values.zipIdx)).symm

theorem boundPositions_zip (targets sources : List ExprType)
    (lengths : targets.length = sources.length) :
    Statements.boundPositions targets =
      ((targets.zip sources).zipIdx.filter (·.1.1.bound)).map (·.2) := by
  have projected : (targets.zip sources).map Prod.fst = targets := List.map_fst_zip lengths.le
  calc
    Statements.boundPositions targets = Statements.boundPositions ((targets.zip sources).map Prod.fst) := by rw [projected]
    _ = _ := by simp [Statements.boundPositions, List.zipIdx_map, List.filter_map, List.map_map, Function.comp_def]

theorem boundPositions_take_prefix (targets : List ExprType) (position : Nat) :
    ∃ suffix, Statements.boundPositions targets = Statements.boundPositions (targets.take position) ++ suffix := by
  refine ⟨((targets.drop position).zipIdx (targets.take position).length).filter (·.1.bound) |>.map (·.2), ?_⟩
  have partition := congrArg Statements.boundPositions (List.take_append_drop position targets)
  simp only [Statements.boundPositions, List.zipIdx_append, List.filter_append, List.map_append, Nat.zero_add] at partition
  exact partition.symm

/-- The bound-source history at a later position retains the source type of
each earlier bound argument at the same rank used by the formal projection. -/
theorem bound_history_member (targets sources : List ExprType) (boundPosition laterPosition : Nat)
    (boundTarget boundSource : ExprType) (lengths : targets.length = sources.length)
    (targetRead : targets[boundPosition]? = some boundTarget)
    (sourceRead : sources[boundPosition]? = some boundSource)
    (bound : boundTarget.bound = true) (earlier : boundPosition < laterPosition) :
    ∃ rank,
      (boundSource.deps, rank) ∈
        ((((targets.take laterPosition).zip (sources.take laterPosition)).filter (·.1.bound)).map (·.2.deps)).zipIdx ∧
      (Statements.boundPositions targets).getD rank rank = boundPosition := by
  let rows := (((targets.take laterPosition).zip (sources.take laterPosition)).zipIdx.filter (·.1.1.bound))
  have targetEarlier : (targets.take laterPosition)[boundPosition]? = some boundTarget := by
    rw [List.getElem?_take_of_lt earlier, targetRead]
  have sourceEarlier : (sources.take laterPosition)[boundPosition]? = some boundSource := by
    rw [List.getElem?_take_of_lt earlier, sourceRead]
  have member : ((boundTarget, boundSource), boundPosition) ∈ rows := by
    simp [rows, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, targetEarlier, sourceEarlier, bound]
  obtain ⟨rank, rankInside, rankRead⟩ := List.mem_iff_getElem.mp member
  have projected : rows.map (·.1.2.deps) =
      (((targets.take laterPosition).zip (sources.take laterPosition)).filter (·.1.bound)).map (·.2.deps) := by
    have projection := zipIdx_filter_project ((targets.take laterPosition).zip (sources.take laterPosition)) (·.1.bound)
    simpa only [rows, List.map_map, Function.comp_def] using congrArg (List.map (fun row => row.2.deps)) projection
  have dependencyRead : (rows.map (·.1.2.deps))[rank]? = some boundSource.deps := by
    simp [List.getElem?_map, List.getElem?_eq_getElem rankInside, rankRead]
  have positionRead : (rows.map (·.2))[rank]? = some boundPosition := by
    simp [List.getElem?_map, List.getElem?_eq_getElem rankInside, rankRead]
  refine ⟨rank, ?_, ?_⟩
  · rw [List.mem_zipIdx_iff_getElem?, ← projected]
    exact dependencyRead
  · have samePositions : Statements.boundPositions (targets.take laterPosition) = rows.map (·.2) :=
      boundPositions_zip _ _ (by simp [lengths])
    obtain ⟨suffix, whole⟩ := boundPositions_take_prefix targets laterPosition
    have within : rank < (Statements.boundPositions (targets.take laterPosition)).length := by
      rw [samePositions, List.length_map]
      exact rankInside
    rw [List.getD_eq_getElem?_getD, whole, List.getElem?_append_left within, samePositions, positionRead]
    rfl

theorem disjointness_preserves_independence (context : Context) (targets sources : List ExprType)
    (boundPosition otherPosition image sort : Nat) (boundTarget boundSource otherTarget otherSource : ExprType)
    (expression : Preterm) (lengths : targets.length = sources.length)
    (targetBoundRead : targets[boundPosition]? = some boundTarget)
    (sourceBoundRead : sources[boundPosition]? = some boundSource)
    (targetOtherRead : targets[otherPosition]? = some otherTarget)
    (sourceOtherRead : sources[otherPosition]? = some otherSource)
    (bound : boundTarget.bound = true)
    (lookup : context[image]? = some (.bound sort))
    (boundSupport : Preterm.Supports context (.var image) (Soundness.positionsOf context boundSource.deps))
    (otherSupport : Preterm.Supports context expression (Soundness.positionsOf context otherSource.deps))
    (boundRanks : ∀ rank ∈ boundSource.deps, rank < (Soundness.rankPositions context).length)
    (otherRanks : ∀ rank ∈ otherSource.deps, rank < (Soundness.rankPositions context).length)
    (independent : ¬ (Statements.binder (Statements.boundPositions targets) otherTarget).DependsOn
      otherPosition boundPosition)
    (accepted : thmArgsDisjoint targets sources = true) :
    ¬ Preterm.HasVar context image expression := by
  have disjoint : Disjoint otherSource.deps boundSource.deps := by
    rcases lt_trichotomy otherPosition boundPosition with earlier | same | later
    · have checked := disjointness_at_position targets sources boundPosition boundTarget boundSource
        lengths targetBoundRead sourceBoundRead accepted
      rw [bound] at checked
      have member : otherSource ∈ sources.take boundPosition := by
        apply List.mem_iff_getElem?.mpr
        exact ⟨otherPosition, (List.getElem?_take_of_lt earlier).trans sourceOtherRead⟩
      exact of_decide_eq_true ((List.all_eq_true.mp checked) otherSource member)
    · subst otherPosition
      have sameTarget : otherTarget = boundTarget := Option.some.inj (targetOtherRead.symm.trans targetBoundRead)
      subst otherTarget
      exact False.elim (independent (by simp [Statements.binder, bound, Binder.DependsOn]))
    · have checked := disjointness_at_position targets sources otherPosition otherTarget otherSource
        lengths targetOtherRead sourceOtherRead accepted
      cases otherBound : otherTarget.bound with
      | true =>
          rw [otherBound] at checked
          have member : boundSource ∈ sources.take otherPosition := by
            apply List.mem_iff_getElem?.mpr
            exact ⟨boundPosition, (List.getElem?_take_of_lt later).trans sourceBoundRead⟩
          have apart : Disjoint boundSource.deps otherSource.deps :=
            of_decide_eq_true ((List.all_eq_true.mp checked) boundSource member)
          exact apart.symm
      | false =>
          rw [otherBound] at checked
          obtain ⟨rank, member, rankPosition⟩ := bound_history_member targets sources boundPosition otherPosition
            boundTarget boundSource lengths targetBoundRead sourceBoundRead bound later
          have undeclared : rank ∉ otherTarget.deps := by
            intro declared
            apply independent
            simp only [Statements.binder, otherBound, Bool.false_eq_true, ↓reduceIte, Binder.DependsOn]
            exact Finset.mem_image.mpr ⟨rank, declared, rankPosition⟩
          have guarded := (List.all_eq_true.mp checked) (boundSource.deps, rank) member
          have apart : Disjoint boundSource.deps otherSource.deps := by simpa [undeclared] using guarded
          exact apart.symm
  have positions := (positionsOf_disjoint context otherSource.deps boundSource.deps otherRanks boundRanks).mpr disjoint
  have singleton : Soundness.positionsOf context boundSource.deps = {image} :=
    boundSupport.deterministic (.bound lookup)
  rw [singleton, Finset.disjoint_left] at positions
  intro occurs
  exact positions ((otherSupport.mem_iff_hasVar image).mpr occurs) (by simp)

/-- Exact argument reads, fitting and the actual ordered rank checks earn
the existing kernel admissibility judgment, including every formal bound row. -/
theorem RankedStore.arguments_admissible (signature : TermSignature) (context : Context)
    (store : List Alloc) (ranked : RankedStore context store) (typed : TypedStore signature context store)
    (positions : List Nat) (types targets : List ExprType)
    (read : positions.mapM (fun position => (store[position]?).map (·.type)) = some types)
    (arity : positions.length = targets.length)
    (compatible : (types.zip targets).all (fun (source, target) => source.fits target) = true)
    (accepted : thmArgsDisjoint targets types = true) :
    ∃ expressions, positions.mapM (Soundness.decode store) = some expressions ∧
      Substitution.Admissible signature (Statements.context targets) context expressions := by
  obtain ⟨expressions, decoded, fitted⟩ := typed.arguments_fit signature context store positions types targets
    (Statements.boundPositions targets) read arity compatible
  obtain ⟨supportedExpressions, supportRead, support, bounded⟩ := ranked.arguments context store positions types read
  have same : supportedExpressions = expressions := Option.some.inj (supportRead.symm.trans decoded)
  subst supportedExpressions
  have fittedContext : List.Forall₂ (Preterm.FitsBinder signature context) expressions (Statements.context targets) := fitted
  have lengths : targets.length = types.length := by
    have typedLengths := fittedContext.length_eq
    have supportLengths := support.length_eq
    simpa only [Statements.context, List.length_map] using typedLengths.symm.trans supportLengths
  have matched : ∀ entry ∈ Substitution.entries (Statements.context targets) expressions,
      ∃ target source,
        targets[entry.2]? = some target ∧ types[entry.2]? = some source ∧
        entry.1.1 = Statements.binder (Statements.boundPositions targets) target ∧
        Preterm.Supports context entry.1.2 (Soundness.positionsOf context source.deps) ∧
        Preterm.FitsBinder signature context entry.1.2 entry.1.1 := by
    intro entry member
    have reads : (Statements.context targets)[entry.2]? = some entry.1.1 ∧
        expressions[entry.2]? = some entry.1.2 := by
      simpa only [Substitution.entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] using member
    have formalRead : (targets[entry.2]?).map (Statements.binder (Statements.boundPositions targets)) = some entry.1.1 := by
      simpa only [Statements.context, List.getElem?_map] using reads.1
    obtain ⟨target, targetRead, sameBinder⟩ := Option.map_eq_some_iff.mp formalRead
    have inside : entry.2 < types.length := by
      rw [← support.length_eq]
      exact (List.getElem?_eq_some_iff.mp reads.2).choose
    let source := types[entry.2]'inside
    have sourceRead : types[entry.2]? = some source := List.getElem?_eq_getElem inside
    have supportPair : (entry.1.2, source) ∈ expressions.zip types := by
      apply List.mem_iff_getElem?.mpr
      exact ⟨entry.2, List.getElem?_zip_eq_some.mpr ⟨reads.2, sourceRead⟩⟩
    have fittedPair : (entry.1.2, entry.1.1) ∈ expressions.zip (Statements.context targets) := by
      apply List.mem_iff_getElem?.mpr
      exact ⟨entry.2, List.getElem?_zip_eq_some.mpr ⟨reads.2, reads.1⟩⟩
    exact ⟨target, source, targetRead, sourceRead, sameBinder.symm,
      List.forall₂_zip support supportPair, List.forall₂_zip fittedContext fittedPair⟩
  refine ⟨expressions, decoded, fittedContext, ?_⟩
  intro entry member sort image equal other otherMember independent
  obtain ⟨boundTarget, boundSource, targetRead, sourceRead, binderEqual, boundSupport, boundFit⟩ := matched entry member
  obtain ⟨otherTarget, otherSource, otherTargetRead, otherSourceRead, otherBinder, otherSupport, _⟩ := matched other otherMember
  have sameBinder : entry.1.1 = .bound sort := congrArg Prod.fst equal
  have sameImage : entry.1.2 = .var image := congrArg Prod.snd equal
  have bound : boundTarget.bound = true := by
    cases targetBound : boundTarget.bound with
    | false => simp [Statements.binder, targetBound, sameBinder] at binderEqual
    | true => rfl
  rw [sameBinder, sameImage] at boundFit
  rw [sameImage] at boundSupport
  have rawIndependent : ¬ (Statements.binder (Statements.boundPositions targets) otherTarget).DependsOn
      other.2 entry.2 := by
    rw [← otherBinder]
    exact independent
  have boundMember : boundSource ∈ types := List.mem_iff_getElem?.mpr ⟨entry.2, sourceRead⟩
  have otherSourceMember : otherSource ∈ types := List.mem_iff_getElem?.mpr ⟨other.2, otherSourceRead⟩
  cases boundFit with
  | bound lookup =>
      exact disjointness_preserves_independence context targets types entry.2 other.2 image sort
        boundTarget boundSource otherTarget otherSource other.1.2 lengths targetRead sourceRead otherTargetRead
        otherSourceRead bound lookup boundSupport otherSupport (bounded boundSource boundMember)
        (bounded otherSource otherSourceMember) rawIndependent accepted

theorem theoremDecl_arguments (terms : List TermEntry) (entry : ThmEntry) (declaration : TheoremDecl)
    (decoded : Statements.theoremDecl terms entry = some declaration) :
    declaration.arguments = Statements.context entry.args := by
  change (Statements.decodeExpr (Statements.arityOf terms) entry.args.length (2 * entry.unify.length + 2)
    (Statements.initial entry.args.length) entry.unify).bind _ = some declaration at decoded
  obtain ⟨value, _, following⟩ := Option.bind_eq_some_iff.mp decoded
  rcases value with ⟨expression, middle, commands⟩
  change (if middle.dummies ≠ [] then none else
    (Statements.decodeHyps (Statements.arityOf terms) entry.args.length (2 * entry.unify.length + 2) middle commands).bind
      (fun premises => some (⟨Statements.context entry.args, premises, expression⟩ : TheoremDecl))) = some declaration at following
  split at following
  · cases following
  · obtain ⟨premises, _, finished⟩ := Option.bind_eq_some_iff.mp following
    have same : (⟨Statements.context entry.args, premises, expression⟩ : TheoremDecl) = declaration := Option.some.inj finished
    rw [← same]

/-- The actual theorem command preserves completed stack and heap evidence.
Argument admissibility is derived from its reads and dependency guard. The
available source declaration and arity table still come from earlier admission. -/
theorem stepThm_preserves_evidence (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (context : Context) (hypotheses : List Preterm)
    (tables : Tables) (before after : Formats.MMB.State) (theorem_ : Nat) (save : Bool)
    (entry : ThmEntry) (declaration : TheoremDecl)
    (typed : TypedStore signature context before.store) (ranked : RankedStore context before.store)
    (sound : StackSound signature definitions theorems context hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems context hypotheses before.store before.heap)
    (entryRead : tables.thms[theorem_]? = some entry)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (available : theorems theorem_ = some declaration)
    (arities : ∀ term termDeclaration, signature term = some termDeclaration →
      Statements.arityOf tables.terms term = some termDeclaration.arguments.length)
    (executed : stepThm tables before theorem_ save = some after) :
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  unfold stepThm at executed
  change (tables.thms[theorem_]?).bind _ = some after at executed
  rw [entryRead, Option.bind_some] at executed
  obtain ⟨⟨position, middle⟩, firstPop, following⟩ := Option.bind_eq_some_iff.mp executed
  obtain ⟨⟨positions, state⟩, argumentsPop, following⟩ := Option.bind_eq_some_iff.mp following
  obtain ⟨types, readings, checked⟩ := Option.bind_eq_some_iff.mp following
  split at checked
  · rename_i guard
    obtain ⟨unified, unifiedRead, finished⟩ := Option.bind_eq_some_iff.mp checked
    have firstSound := sound.popExpr before middle position firstPop
    have poppedSound := firstSound.popExprs middle state entry.args.length positions argumentsPop
    have firstKept := State.popExpr_keeps_state before middle position firstPop
    have restKept := State.popExprs_keeps_state middle state entry.args.length positions argumentsPop
    have storeKept : state.store = before.store := by
      have first := congrArg State.store firstKept
      have rest := congrArg State.store restKept
      exact rest.trans first
    have heapKept : state.heap = before.heap := by
      have first := congrArg State.heap firstKept
      have rest := congrArg State.heap restKept
      exact rest.trans first
    have typedState : TypedStore signature context state.store := storeKept ▸ typed
    have rankedState : RankedStore context state.store := storeKept ▸ ranked
    have heapState : HeapSound signature definitions theorems context hypotheses state.store state.heap := by
      simpa only [storeKept, heapKept] using heap
    have count := State.popExprs_count middle state entry.args.length positions argumentsPop
    simp only [Bool.and_eq_true] at guard
    obtain ⟨expressions, expressionsRead, admissible⟩ := rankedState.arguments_admissible signature context state.store
      typedState positions types entry.args readings count guard.1 guard.2
    rw [← theoremDecl_arguments tables.terms entry declaration declared] at admissible
    obtain ⟨proved, afterMain, _⟩ := MMBTheoremSoundness.unify_theorem_proven signature definitions theorems
      context hypotheses state.store typedState tables.terms entry declaration theorem_ arities declared available
      positions expressions position state.stack state.hyps unified count expressionsRead admissible poppedSound unifiedRead
    cases save <;> simp at finished
    · subst after
      exact ⟨typedState, rankedState, .proof proved afterMain, heapState⟩
    · subst after
      exact ⟨typedState, rankedState, .proof proved afterMain, heapState.append_certified proved⟩
  · cases checked

namespace Controls

private def regularType : ExprType := ⟨0, false, ∅⟩
private def boundType : ExprType := ⟨0, true, {0}⟩
private def context : Context := [.regular 0 ∅, .bound 0]
private def store : List Alloc := [⟨.var 0, regularType⟩, ⟨.var 1, boundType⟩]
private def entry : TermEntry := ⟨0, [boundType], regularType, none⟩
private def tables : Tables := ⟨[⟨false, false, false, false⟩], [entry], []⟩
private def declaration : TermDecl := ⟨[.bound 0], 0, ∅⟩
private def signature : TermSignature := fun term => if term = 0 then some declaration else none
private def initial : Formats.MMB.State := ⟨store, [], [.expr 0, .expr 1], [], 1, 2⟩
private def before : Formats.MMB.State := { initial with stack := [.expr 1] }
private def after : Formats.MMB.State :=
  { initial with store := store ++ [⟨.app 0 [1], ⟨0, false, {0}⟩⟩], stack := [.expr 2] }

private theorem decode_zero : Soundness.decode store 0 = some (.var 0) := by
  rw [Soundness.decode]
  rfl

private theorem decode_one : Soundness.decode store 1 = some (.var 1) := by
  rw [Soundness.decode]
  rfl

private theorem ranked : RankedStore context store := by
  constructor
  · intro position allocation read
    cases position with
    | zero =>
        have same : (⟨.var 0, regularType⟩ : Alloc) = allocation := by simpa [store] using read
        subst allocation
        refine ⟨.var 0, decode_zero, ?_⟩
        exact .regular rfl
    | succ position =>
        cases position with
        | zero =>
            have same : (⟨.var 1, boundType⟩ : Alloc) = allocation := by simpa [store] using read
            subst allocation
            refine ⟨.var 1, decode_one, ?_⟩
            have support : Preterm.Supports context (.var 1) {1} := .bound rfl
            simpa [Soundness.positionsOf, Soundness.rankPositions, context, boundType] using support
        | succ position => simp [store] at read
  · intro position allocation read rank occurs
    cases position with
    | zero =>
        have same : (⟨.var 0, regularType⟩ : Alloc) = allocation := by simpa [store] using read
        subst allocation
        simp [regularType] at occurs
    | succ position =>
        cases position with
        | zero =>
            have same : (⟨.var 1, boundType⟩ : Alloc) = allocation := by simpa [store] using read
            subst allocation
            have zero : rank = 0 := by simpa [boundType] using occurs
            subst rank
            decide
        | succ position => simp [store] at read

private theorem typed : TypedStore signature context store := by
  constructor
  intro position allocation read
  cases position with
  | zero =>
      have same : (⟨.var 0, regularType⟩ : Alloc) = allocation := by simpa [store] using read
      subst allocation
      exact ⟨.var 0, decode_zero, .var (binder := .regular 0 ∅) rfl, by simp [regularType]⟩
  | succ position =>
      cases position with
      | zero =>
          have same : (⟨.var 1, boundType⟩ : Alloc) = allocation := by simpa [store] using read
          subst allocation
          exact ⟨.var 1, decode_one, .var (binder := .bound 0) rfl, fun _ => ⟨1, rfl, rfl⟩⟩
      | succ position => simp [store] at read

theorem actual_descriptor_initialization :
    loadArgs tables.sorts [regularType, boundType] = some initial := by decide

theorem later_bound_rank_differs_from_context_position :
    Soundness.rankPositions context = [1] ∧ Soundness.positionsOf context {0} = {1} := by decide

theorem fallback_rank_collision_requires_bounds :
    Disjoint ({0} : Finset Nat) {1} ∧
      ¬ Disjoint (Soundness.positionsOf context {0}) (Soundness.positionsOf context {1}) := by decide

theorem out_of_range_recorded_rank_refused :
    ¬ (∀ rank ∈ ({1} : Finset Nat), rank < (Soundness.rankPositions context).length) := by decide

theorem actual_bound_child_retains_kernel_support :
    stepTerm tables .assertion before 0 false = some after ∧ RankedStore context after.store := by
  have executed : stepTerm tables .assertion before 0 false = some after := by decide
  exact ⟨executed, stepTerm_preserves_ranked_support context tables before after 0 false entry ranked rfl executed⟩

theorem earlier_bound_argument_admissible :
    Substitution.Admissible signature [.bound 0, .regular 0 ∅] context [.var 1, .var 0] := by
  obtain ⟨images, imagesRead, admitted⟩ := ranked.arguments_admissible signature context store typed
    [1, 0] [boundType, regularType] [boundType, regularType] (by decide) rfl (by decide) (by decide)
  have expected : ([1, 0] : List Nat).mapM (Soundness.decode store) = some [.var 1, .var 0] := by
    simp [decode_zero, decode_one]
  have same := Option.some.inj (imagesRead.symm.trans expected)
  subst images
  exact admitted

theorem later_bound_argument_admissible :
    Substitution.Admissible signature [.regular 0 ∅, .bound 0] context [.var 0, .var 1] := by
  obtain ⟨images, imagesRead, admitted⟩ := ranked.arguments_admissible signature context store typed
    [0, 1] [regularType, boundType] [regularType, boundType] (by decide) rfl (by decide) (by decide)
  have expected : ([0, 1] : List Nat).mapM (Soundness.decode store) = some [.var 0, .var 1] := by
    simp [decode_zero, decode_one]
  have same := Option.some.inj (imagesRead.symm.trans expected)
  subst images
  exact admitted

theorem dummy_guard_earns_kernel_freshness : Preterm.FreshFor context 1 (.var 0) := by
  have executed : unifyStep store .definition ⟨[1], [(0, false)], [], []⟩ (.dummy 0) =
      some ⟨[], [(0, false), (1, false)], [], []⟩ := by rfl
  obtain ⟨position, rest, image, shape, _, decoded, _, fresh⟩ :=
    unify_definition_dummy_fresh signature context store ranked typed _ _ 0 executed
  have shapeParts : position = 1 ∧ rest = [] := by simpa using shape.symm
  have samePosition := shapeParts.1
  subst position
  have sameImage : image = 1 := by
    have same := Option.some.inj (decoded.symm.trans decode_one)
    cases same
    rfl
  subst image
  obtain ⟨expression, expressionRead, earned⟩ := fresh 0 (by simp)
  have same := Option.some.inj (expressionRead.symm.trans decode_zero)
  subst expression
  exact earned

theorem bound_child_freshness_violation_refused :
    unifyStep after.store .definition ⟨[1], [(2, false)], [], []⟩ (.dummy 0) = none := by decide

theorem undeclared_bound_child_dependency_refused :
    thmArgsDisjoint [boundType, regularType] [boundType, ⟨0, false, {0}⟩] = false := by decide

theorem collapsed_bound_images_refused :
    thmArgsDisjoint [boundType, ⟨0, true, {1}⟩] [boundType, boundType] = false := by decide

private theorem after_typed : TypedStore signature context after.store := by
  exact MMBMachineSoundness.stepTerm_preserves_typing signature context tables .assertion before after 0 false
    entry declaration typed rfl (by simp [signature]) rfl rfl (by decide)

private theorem after_ranked : RankedStore context after.store := actual_bound_child_retains_kernel_support.2

private theorem decode_two : Soundness.decode after.store 2 = some (.app (.term 0) (.var 1)) := by
  have earlier : ∀ position ∈ ([1] : List Nat), position < before.store.length := by
    intro position member
    have same : position = 1 := by simpa using member
    subst position
    decide
  have decoded := MMBExecution.decode_alloc_application before 0 [1] ⟨0, false, {0}⟩ earlier
  have count : store.length = 2 := rfl
  simpa [State.alloc, before, after, initial, decode_one, count, Preterm.applyArgs] using decoded

theorem declared_bound_child_dependency_admissible :
    Substitution.Admissible signature [.bound 0, .regular 0 {0}] context [.var 1, .app (.term 0) (.var 1)] := by
  obtain ⟨images, imagesRead, admitted⟩ := after_ranked.arguments_admissible signature context after.store after_typed
    [1, 2] [boundType, ⟨0, false, {0}⟩] [boundType, ⟨0, false, {0}⟩] (by decide) rfl (by decide) (by decide)
  have first : Soundness.decode after.store 1 = some (.var 1) := by
    have preserved := MMBExecution.decode_append_preserves store [⟨.app 0 [1], ⟨0, false, {0}⟩⟩] 1 (by decide)
    exact preserved.trans decode_one
  have expected : ([1, 2] : List Nat).mapM (Soundness.decode after.store) = some [.var 1, .app (.term 0) (.var 1)] := by
    simp [first, decode_two]
  have same := Option.some.inj (imagesRead.symm.trans expected)
  subst images
  exact admitted

private def theoremEntry : ThmEntry := ⟨[boundType], [.term 0, .ref 0]⟩
private def theoremTables : Tables := { tables with thms := [theoremEntry] }
private def assertionDeclaration : TheoremDecl := ⟨[.bound 0], [], .app (.term 0) (.var 0)⟩
private def theoremSignature : TheoremSignature := fun index => if index = 0 then some assertionDeclaration else none
private def theoremBefore : Formats.MMB.State := { after with stack := [.expr 2, .expr 1] }
private def theoremAfter : Formats.MMB.State := { after with stack := [.proof 2], heap := after.heap ++ [.proof 2] }

private theorem declared_arities (term : Nat) (termDeclaration : TermDecl)
    (found : signature term = some termDeclaration) :
    Statements.arityOf theoremTables.terms term = some termDeclaration.arguments.length := by
  by_cases zero : term = 0
  · subst term
    have same : declaration = termDeclaration := by simpa [signature] using found
    subst termDeclaration
    rfl
  · simp [signature, zero] at found

private theorem theorem_before_sound :
    StackSound signature (fun _ => none) theoremSignature context [] theoremBefore.store theoremBefore.stack := by
  exact .expr (after_typed.pointer signature context after.store 2 ⟨.app 0 [1], ⟨0, false, {0}⟩⟩ rfl)
    (.expr (after_typed.pointer signature context after.store 1 ⟨.var 1, boundType⟩ rfl) .empty)

private theorem theorem_before_heap :
    HeapSound signature (fun _ => none) theoremSignature context [] theoremBefore.store theoremBefore.heap := by
  intro element member
  have choices : element = .expr 0 ∨ element = .expr 1 := by simpa [theoremBefore, after, initial] using member
  rcases choices with same | same
  · subst element
    exact after_typed.pointer signature context after.store 0 ⟨.var 0, regularType⟩ rfl
  · subst element
    exact after_typed.pointer signature context after.store 1 ⟨.var 1, boundType⟩ rfl

theorem actual_theorem_command_preserves_completed_evidence :
    stepThm theoremTables theoremBefore 0 true = some theoremAfter ∧
      StackSound signature (fun _ => none) theoremSignature context [] theoremAfter.store theoremAfter.stack ∧
      HeapSound signature (fun _ => none) theoremSignature context [] theoremAfter.store theoremAfter.heap := by
  have executed : stepThm theoremTables theoremBefore 0 true = some theoremAfter := by decide
  obtain ⟨_, _, stack, heap⟩ := stepThm_preserves_evidence signature (fun _ => none) theoremSignature context []
    theoremTables theoremBefore theoremAfter 0 true theoremEntry assertionDeclaration after_typed after_ranked
    theorem_before_sound theorem_before_heap rfl (by decide) (by simp [theoremSignature]) declared_arities executed
  exact ⟨executed, stack, heap⟩

theorem regular_image_in_bound_theorem_slot_refused :
    stepThm theoremTables { theoremBefore with stack := [.expr 2, .expr 0] } 0 true = none := by decide

theorem mismatched_theorem_conclusion_pointer_refused :
    stepThm theoremTables { theoremBefore with stack := [.expr 1, .expr 1] } 0 true = none := by decide

end Controls

end Mettapedia.Languages.MM0.MeTTa.MMBDependencySoundness
