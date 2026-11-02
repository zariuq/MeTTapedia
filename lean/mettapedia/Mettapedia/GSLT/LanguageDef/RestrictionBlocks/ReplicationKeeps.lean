import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawsCanon

/-!
# What each law keeps

Both sides of each law of a calculus with restriction and replication are no abstractions, have pending substitutions
and binding restrictions alike, and, when they have no pending substitution and their restrictions bind, their object
readings have one canonical block (`Keeps`). The relation is symmetric (`Keeps.symm`), so one orientation of each
law suffices; a raw match of a bag may leave a tail on the matched term, which the object reading closes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

variable {block : ReplicationBlock}

/-- **What a law keeps**: neither side an abstraction, pending substitutions and binding restrictions alike, and
one canonical block of the object readings when the source has no pending substitution and binds. -/
structure Keeps (block : ReplicationBlock) (source target : Pattern) : Prop where
  sourceNotLambda : ∀ binder body, source ≠ .lambda binder body
  targetNotLambda : ∀ binder body, target ≠ .lambda binder body
  sameSubst : substFree source = substFree target
  sameBinds : restrictionsBind block.toBlock source = restrictionsBind block.toBlock target
  canon : substFree source = true → restrictionsBind block.toBlock source = true →
    canonP block (closeTails source) = canonP block (closeTails target)

theorem Keeps.symm {source target : Pattern} (keeps : Keeps block source target) : Keeps block target source where
  sourceNotLambda := keeps.targetNotLambda
  targetNotLambda := keeps.sourceNotLambda
  sameSubst := keeps.sameSubst.symm
  sameBinds := keeps.sameBinds.symm
  canon free binds := (keeps.canon (keeps.sameSubst ▸ free) (keeps.sameBinds ▸ binds)).symm

/-! ## Reading the shapes -/

theorem substFree_apply (label : String) (arguments : List Pattern) :
    substFree (.apply label arguments) = arguments.all substFree := by
  simp [substFree, substFreeList_eq_all]

theorem substFree_lambda (binder : Option String) (body : Pattern) :
    substFree (.lambda binder body) = substFree body := rfl

theorem substFree_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    substFree (.collection kind elements rest) = elements.all substFree := by
  simp [substFree, substFreeList_eq_all]

theorem restrictionsBind_apply (base : Block) (label : String) (arguments : List Pattern) :
    restrictionsBind base (.apply label arguments) =
      (bindsAt base label arguments && arguments.all (restrictionsBind base)) := by
  simp [restrictionsBind, restrictionsBindList_eq_all]

theorem restrictionsBind_lambda (base : Block) (binder : Option String) (body : Pattern) :
    restrictionsBind base (.lambda binder body) = restrictionsBind base body := rfl

theorem restrictionsBind_collection (base : Block) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    restrictionsBind base (.collection kind elements rest) = elements.all (restrictionsBind base) := by
  simp [restrictionsBind, restrictionsBindList_eq_all]

theorem bindsAt_of_ne {base : Block} {label : String} (different : label ≠ base.restrict) (arguments : List Pattern) :
    bindsAt base label arguments = true := by
  unfold bindsAt
  split <;> simp [different]

theorem bindsAt_lambda (base : Block) (label : String) (binder : Option String) (body : Pattern) :
    bindsAt base label [.lambda binder body] = true := rfl

theorem closeTails_apply (label : String) (arguments : List Pattern) :
    closeTails (.apply label arguments) = .apply label (arguments.map closeTails) := by
  simp [closeTails, closeTailsList_eq_map]

theorem closeTails_lambda (binder : Option String) (body : Pattern) :
    closeTails (.lambda binder body) = .lambda binder (closeTails body) := rfl

theorem closeTails_collection (kind : CollType) (elements : List Pattern) (rest : Option String) :
    closeTails (.collection kind elements rest) = .collection kind (elements.map closeTails) none := by
  simp [closeTails, closeTailsList_eq_map]

/-- The object reading of a term without pending substitutions is an object term, binding as the term does. -/
theorem closeTails_facts {base : Block} {pattern : Pattern} (free : substFree pattern = true)
    (binds : restrictionsBind base pattern = true) :
    isObjectPattern (closeTails pattern) = true ∧ restrictionsBind base (closeTails pattern) = true :=
  ⟨by rw [isObject_closeTails]; exact free, by rw [restrictionsBind_closeTails]; exact binds⟩

theorem all_perm_eq {α : Type} {first second : List α} (permutation : first.Perm second) (test : α → Bool) :
    first.all test = second.all test := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  exact ⟨fun all element member => all element (permutation.mem_iff.mpr member),
    fun all element member => all element (permutation.mem_iff.mp member)⟩

section Laws

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict) (unitFresh : block.unit ≠ block.restrict)

include multisetFresh fresh restrictFresh

/-! ## The laws of replication -/

/-- `{P, !P} = !P`, the bag's tail left by a raw match closed. -/
theorem unfold_keeps (process : Pattern) (rest : Option String) :
    Keeps block (.collection .hashBag [process, .apply block.replicate [process]] rest)
      (.apply block.replicate [process]) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply, substFree_collection]
  sameBinds := by simp [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh.symm.symm]
  canon free binds := by
    have parts := closeTails_facts (base := block.toBlock) (pattern := process)
      (by simpa [substFree_apply, substFree_collection] using free)
      (by simpa [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh] using binds)
    simp only [closeTails_apply, closeTails_collection, List.map_cons, List.map_nil]
    exact (canonP_unfold multisetFresh fresh restrictFresh parts.1 parts.2).1

/-- `{!P, P} = !P`, the bag's tail left by a raw match closed. -/
theorem unfold_keeps_swap (process : Pattern) (rest : Option String) :
    Keeps block (.collection .hashBag [.apply block.replicate [process], process] rest)
      (.apply block.replicate [process]) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply, substFree_collection]
  sameBinds := by simp [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh]
  canon free binds := by
    have parts := closeTails_facts (base := block.toBlock) (pattern := process)
      (by simpa [substFree_apply, substFree_collection] using free)
      (by simpa [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh] using binds)
    simp only [closeTails_apply, closeTails_collection, List.map_cons, List.map_nil]
    exact (canonP_unfold multisetFresh fresh restrictFresh parts.1 parts.2).2

omit multisetFresh fresh in
include unitFresh in
/-- `!0 = 0`. -/
theorem replicationNil_keeps :
    Keeps block (.apply block.replicate [.apply block.unit []]) (.apply block.unit []) where
  sourceNotLambda := apply_notLambda _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply]
  sameBinds := by simp [restrictionsBind_apply, bindsAt_of_ne restrictFresh, bindsAt_of_ne unitFresh]
  canon _ _ := by
    simp only [closeTails_apply, List.map_cons, List.map_nil]
    exact canonP_replicationNil

/-- `!!P = !P`. -/
theorem twice_keeps (process : Pattern) :
    Keeps block (.apply block.replicate [.apply block.replicate [process]]) (.apply block.replicate [process]) where
  sourceNotLambda := apply_notLambda _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply]
  sameBinds := by simp [restrictionsBind_apply, bindsAt_of_ne restrictFresh]
  canon free binds := by
    have parts := closeTails_facts (base := block.toBlock) (pattern := process)
      (by simpa [substFree_apply] using free)
      (by simpa [restrictionsBind_apply, bindsAt_of_ne restrictFresh] using binds)
    simp only [closeTails_apply, List.map_cons, List.map_nil]
    exact canonP_twice multisetFresh fresh restrictFresh parts.1 parts.2

/-- `!{P, Q} = {!P, !Q}`, in either order of the replicated bag, its tail closed. -/
theorem replicationPar_keeps (first second : Pattern) (rest : Option String) (swapped : Bool) :
    Keeps block (.apply block.replicate [.collection .hashBag (if swapped then [second, first] else [first, second]) rest])
      (.collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]] none) where
  sourceNotLambda := apply_notLambda _ _
  targetNotLambda := collection_notLambda _ _ _
  sameSubst := by cases swapped <;> simp [substFree_apply, substFree_collection, Bool.and_comm]
  sameBinds := by
    cases swapped <;> simp [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh,
      Bool.and_comm]
  canon free binds := by
    have freeParts : substFree first = true ∧ substFree second = true := by
      cases swapped <;> simp_all [substFree_apply, substFree_collection]
    have bindParts : restrictionsBind block.toBlock first = true ∧ restrictionsBind block.toBlock second = true := by
      cases swapped <;> simp_all [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh]
    have firstParts := closeTails_facts (base := block.toBlock) freeParts.1 bindParts.1
    have secondParts := closeTails_facts (base := block.toBlock) freeParts.2 bindParts.2
    have laws := canonP_replicationPar multisetFresh fresh restrictFresh firstParts.1 firstParts.2 secondParts.1
      secondParts.2
    cases swapped
    · simp only [if_false, Bool.false_eq_true, closeTails_apply, closeTails_collection, List.map_cons, List.map_nil]
      exact laws.1
    · simp only [if_true, closeTails_apply, closeTails_collection, List.map_cons, List.map_nil]
      exact laws.2

/-- `{!P, !Q} = !{P, Q}` read from a bag in either order, its tail closed. -/
theorem replicationPar_keeps_reverse (first second : Pattern) (rest : Option String) (swapped : Bool) :
    Keeps block (.collection .hashBag (if swapped then [.apply block.replicate [second], .apply block.replicate [first]]
        else [.apply block.replicate [first], .apply block.replicate [second]]) rest)
      (.apply block.replicate [.collection .hashBag [first, second] none]) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by cases swapped <;> simp [substFree_apply, substFree_collection, Bool.and_comm]
  sameBinds := by
    cases swapped <;> simp [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh,
      Bool.and_comm]
  canon free binds := by
    have freeParts : substFree first = true ∧ substFree second = true := by
      cases swapped <;> simp_all [substFree_apply, substFree_collection]
    have bindParts : restrictionsBind block.toBlock first = true ∧ restrictionsBind block.toBlock second = true := by
      cases swapped <;> simp_all [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh]
    have firstParts := closeTails_facts (base := block.toBlock) freeParts.1 bindParts.1
    have secondParts := closeTails_facts (base := block.toBlock) freeParts.2 bindParts.2
    cases swapped
    · simp only [if_false, Bool.false_eq_true, closeTails_apply, closeTails_collection, List.map_cons, List.map_nil]
      exact (canonP_replicationPar multisetFresh fresh restrictFresh firstParts.1 firstParts.2 secondParts.1
        secondParts.2).1.symm
    · simp only [if_true, closeTails_apply, closeTails_collection, List.map_cons, List.map_nil]
      exact (canonP_replicationPar multisetFresh fresh restrictFresh secondParts.1 secondParts.2 firstParts.1
        firstParts.2).2.symm

/-- `{!P, !P} = !P`, its tail closed. -/
theorem idempotent_keeps (process : Pattern) (rest : Option String) :
    Keeps block (.collection .hashBag [.apply block.replicate [process], .apply block.replicate [process]] rest)
      (.apply block.replicate [process]) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply, substFree_collection]
  sameBinds := by simp [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh]
  canon free binds := by
    have parts := closeTails_facts (base := block.toBlock) (pattern := process)
      (by simpa [substFree_apply, substFree_collection] using free)
      (by simpa [restrictionsBind_apply, restrictionsBind_collection, bindsAt_of_ne restrictFresh] using binds)
    simp only [closeTails_apply, closeTails_collection, List.map_cons, List.map_nil]
    exact canonP_idempotent multisetFresh fresh restrictFresh parts.1 parts.2

omit multisetFresh

/-! ## The laws of restriction -/

omit fresh restrictFresh in
include unitFresh in
/-- `(νx)0 = 0`. -/
theorem restrictionNil_keeps (binder : Option String) :
    Keeps block (.apply block.restrict [.lambda binder (.apply block.unit [])]) (.apply block.unit []) where
  sourceNotLambda := apply_notLambda _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply, substFree_lambda]
  sameBinds := by simp [restrictionsBind_apply, restrictionsBind_lambda, bindsAt_lambda, bindsAt_of_ne unitFresh]
  canon _ _ := by
    simp only [closeTails_apply, closeTails_lambda, List.map_cons, List.map_nil]
    exact canonP_restrictionNil binder

include multisetFresh in
/-- Exchanging two restrictions. -/
theorem exchange_keeps (outerBinder innerBinder : Option String) (body : Pattern) :
    Keeps block (.apply block.restrict [.lambda outerBinder (.apply block.restrict [.lambda innerBinder body])])
      (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none (rename swapInner body)])]) where
  sourceNotLambda := apply_notLambda _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply, substFree_lambda, substFree_rename]
  sameBinds := by
    simp [restrictionsBind_apply, restrictionsBind_lambda, bindsAt_lambda, restrictionsBind_rename]
  canon free binds := by
    have parts := closeTails_facts (base := block.toBlock) (pattern := body)
      (by simpa [substFree_apply, substFree_lambda] using free)
      (by simpa [restrictionsBind_apply, restrictionsBind_lambda, bindsAt_lambda] using binds)
    simp only [closeTails_apply, closeTails_lambda, List.map_cons, List.map_nil, closeTails_rename]
    exact canonP_exchange multisetFresh fresh restrictFresh parts.1 parts.2

omit restrictFresh in
include unitFresh in
/-- An empty named multiset whose empty instance is the unit is the restriction of inaction. -/
theorem emptyUnit_keeps (restrictNotEmpty : block.restrict ∉ block.emptyUnits) {label : String}
    (listed : label ∈ block.emptyUnits) (binder : Option String) :
    Keeps block (.apply label [.collection .hashBag [] none])
      (.apply block.restrict [.lambda binder (.apply block.unit [])]) where
  sourceNotLambda := apply_notLambda _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_apply, substFree_lambda, substFree_collection]
  sameBinds := by
    have different : label ≠ block.restrict := fun same => restrictNotEmpty (same ▸ listed)
    simp [restrictionsBind_apply, restrictionsBind_lambda, restrictionsBind_collection, bindsAt_lambda,
      bindsAt_of_ne different, bindsAt_of_ne unitFresh]
  canon _ _ := by
    simp only [closeTails_apply, closeTails_lambda, closeTails_collection, List.map_cons, List.map_nil]
    rw [canonP_emptyUnit fresh listed, canonP_restrictionNil, canonP_restrictionNil]

omit fresh restrictFresh in
/-- Members lifted past a restriction have the pending substitutions and binding restrictions of the members. -/
theorem lift_all (test : Pattern → Bool) (renamed : ∀ pattern, test (liftBVars 0 1 pattern) = test pattern)
    (patterns : List Pattern) : (patterns.map (liftBVars 0 1)).all test = patterns.all test := by
  simp only [List.all_map]
  congr 1
  funext pattern
  exact renamed pattern

omit fresh restrictFresh in
theorem substFree_lift (pattern : Pattern) : substFree (liftBVars 0 1 pattern) = substFree pattern := by
  rw [liftBVars_eq_rename, substFree_rename]

omit fresh restrictFresh in
theorem restrictionsBind_lift (base : Block) (pattern : Pattern) :
    restrictionsBind base (liftBVars 0 1 pattern) = restrictionsBind base pattern := by
  rw [liftBVars_eq_rename, restrictionsBind_rename]

omit fresh restrictFresh in
theorem closeTails_lift (pattern : Pattern) : closeTails (liftBVars 0 1 pattern) = liftBVars 0 1 (closeTails pattern) := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, closeTails_rename]

omit fresh restrictFresh in
/-- The members of a bag with a restriction among them, read as the restriction first. -/
theorem all_members {members : List Pattern} {selected : Nat} (inside : selected < members.length)
    (test : Pattern → Bool) : members.all test = (test members[selected] && (members.eraseIdx selected).all test) := by
  rw [all_perm_eq (perm_getElem_eraseIdx members selected inside) test, List.all_cons]

include multisetFresh in
/-- Scope extrusion. -/
theorem extrusion_keeps {members : List Pattern} {selected : Nat} (inside : selected < members.length)
    {binder : Option String} {body : Pattern} (chosen : members[selected] = .apply block.restrict [.lambda binder body]) :
    Keeps block (.collection .hashBag members none)
      (.apply block.restrict [.lambda none (.collection .hashBag
        (body :: (members.eraseIdx selected).map (liftBVars 0 1)) none)]) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by
    rw [substFree_collection, all_members inside, chosen]
    simp only [substFree_apply, substFree_lambda, substFree_collection, List.all_cons, List.all_nil, Bool.and_true,
      lift_all substFree substFree_lift]
  sameBinds := by
    rw [restrictionsBind_collection, all_members inside, chosen]
    simp only [restrictionsBind_apply, restrictionsBind_lambda, restrictionsBind_collection, List.all_cons,
      List.all_nil, Bool.and_true, bindsAt_lambda, Bool.true_and, lift_all _ (restrictionsBind_lift block.toBlock)]
  canon free binds := by
    rw [substFree_collection, List.all_eq_true] at free
    rw [restrictionsBind_collection, List.all_eq_true] at binds
    have objects : ∀ member ∈ members.map closeTails, isObjectPattern member = true := by
      intro member inMembers
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (free original inOriginal) (binds original inOriginal)).1
    have bindsAll : ∀ member ∈ members.map closeTails, restrictionsBind block.toBlock member = true := by
      intro member inMembers
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (free original inOriginal) (binds original inOriginal)).2
    have closedChosen : (members.map closeTails)[selected]'(by simpa using inside) =
        .apply block.restrict [.lambda binder (closeTails body)] := by
      rw [List.getElem_map, chosen]
      rfl
    have extruded := canonP_extrusion multisetFresh fresh restrictFresh (by simpa using inside) closedChosen objects
      bindsAll
    rw [closeTails_collection, extruded, closeTails_apply, List.map_singleton, closeTails_lambda, closeTails_collection,
      List.map_cons, List.eraseIdx_map, List.map_map, List.map_map]
    congr 6
    exact List.map_congr_left fun member _ => (closeTails_lift member).symm

include multisetFresh in
/-- Scope extrusion, read backward. -/
theorem extrusion_reverse_keeps {binder : Option String} {members : List Pattern} {selected : Nat}
    (inside : selected < members.length) {originals : List Pattern}
    (erased : members.eraseIdx selected = originals.map (liftBVars 0 1)) :
    Keeps block (.apply block.restrict [.lambda binder (.collection .hashBag members none)])
      (.collection .hashBag (.apply block.restrict [.lambda none members[selected]] :: originals) none) where
  sourceNotLambda := apply_notLambda _ _
  targetNotLambda := collection_notLambda _ _ _
  sameSubst := by
    simp only [substFree_apply, substFree_lambda, substFree_collection, List.all_cons, List.all_nil, Bool.and_true]
    rw [all_members inside, erased, lift_all substFree substFree_lift]
  sameBinds := by
    simp only [restrictionsBind_apply, restrictionsBind_lambda, restrictionsBind_collection, List.all_cons,
      List.all_nil, Bool.and_true, bindsAt_lambda, Bool.true_and]
    rw [all_members inside, erased, lift_all _ (restrictionsBind_lift block.toBlock)]
  canon free binds := by
    simp only [substFree_apply, substFree_lambda, substFree_collection, List.all_cons, List.all_nil, Bool.and_true,
      List.all_eq_true] at free
    simp only [restrictionsBind_apply, restrictionsBind_lambda, restrictionsBind_collection, List.all_cons,
      List.all_nil, Bool.and_true, bindsAt_lambda, Bool.true_and, List.all_eq_true] at binds
    have objects : ∀ member ∈ members.map closeTails, isObjectPattern member = true := by
      intro member inMembers
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (free original inOriginal) (binds original inOriginal)).1
    have bindsAll : ∀ member ∈ members.map closeTails, restrictionsBind block.toBlock member = true := by
      intro member inMembers
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (free original inOriginal) (binds original inOriginal)).2
    have closedErased : (members.map closeTails).eraseIdx selected = (originals.map closeTails).map (liftBVars 0 1) := by
      rw [List.eraseIdx_map, erased, List.map_map, List.map_map]
      exact List.map_congr_left fun original _ => closeTails_lift original
    have extruded := canonP_extrusion_reverse multisetFresh fresh restrictFresh (binder := binder)
      (by simpa using inside) closedErased objects bindsAll
    rw [closeTails_apply, List.map_singleton, closeTails_lambda, closeTails_collection, extruded,
      closeTails_collection, List.map_cons, closeTails_apply, List.map_singleton, closeTails_lambda, List.getElem_map]

/-! ## The laws of the bag -/

omit multisetFresh in
/-- Permuting the members of a bag. -/
theorem bagPerm_keeps {first second : List Pattern} (permutation : first.Perm second) :
    Keeps block (.collection .hashBag first none) (.collection .hashBag second none) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := collection_notLambda _ _ _
  sameSubst := by rw [substFree_collection, substFree_collection, all_perm_eq permutation]
  sameBinds := by rw [restrictionsBind_collection, restrictionsBind_collection, all_perm_eq permutation]
  canon free binds := by
    rw [substFree_collection, List.all_eq_true] at free
    rw [restrictionsBind_collection, List.all_eq_true] at binds
    rw [closeTails_collection, closeTails_collection]
    refine canonP_bag_perm fresh restrictFresh (permutation.map closeTails) (fun member inMembers => ?_)
      (fun member inMembers => ?_)
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (base := block.toBlock) (free original inOriginal) (binds original inOriginal)).1
    · obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (free original inOriginal) (binds original inOriginal)).2

omit multisetFresh in
/-- A bag inside a bag is flattened. -/
theorem flatten_keeps (pre inner post : List Pattern) :
    Keeps block (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none)
      (.collection .hashBag (pre ++ inner ++ post) none) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := collection_notLambda _ _ _
  sameSubst := by
    simp only [substFree_collection, List.all_append, List.all_cons]
    simp [Bool.and_assoc]
  sameBinds := by
    simp only [restrictionsBind_collection, List.all_append, List.all_cons]
    simp [Bool.and_assoc]
  canon free binds := by
    simp only [substFree_collection, List.all_append, List.all_cons, Bool.and_eq_true, List.all_eq_true] at free
    simp only [restrictionsBind_collection, List.all_append, List.all_cons, Bool.and_eq_true,
      List.all_eq_true] at binds
    have parts : ∀ member ∈ pre ++ inner ++ post, substFree member = true ∧
        restrictionsBind block.toBlock member = true := by
      intro member inMembers
      simp only [List.mem_append] at inMembers
      rcases inMembers with (inPre | inInner) | inPost
      · exact ⟨free.1 member inPre, binds.1 member inPre⟩
      · exact ⟨free.2.1 member inInner, binds.2.1 member inInner⟩
      · exact ⟨free.2.2 member inPost, binds.2.2 member inPost⟩
    simp only [closeTails_collection, List.map_append, List.map_cons]
    refine canonP_flatten fresh restrictFresh (fun member inMembers => ?_) (fun member inMembers => ?_)
    · simp only [← List.map_append] at inMembers
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (base := block.toBlock) (parts original inOriginal).1 (parts original inOriginal).2).1
    · simp only [← List.map_append] at inMembers
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp inMembers
      exact (closeTails_facts (parts original inOriginal).1 (parts original inOriginal).2).2

omit multisetFresh in
/-- A one-member bag is its member, a member that is not an abstraction. -/
theorem singleton_keeps {element : Pattern} (notLambda : ∀ binder body, element ≠ .lambda binder body) :
    Keeps block (.collection .hashBag [element] none) element where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := notLambda
  sameSubst := by simp [substFree_collection]
  sameBinds := by simp [restrictionsBind_collection]
  canon free binds := by
    have parts := closeTails_facts (base := block.toBlock) (pattern := element)
      (by simpa [substFree_collection] using free) (by simpa [restrictionsBind_collection] using binds)
    rw [closeTails_collection, List.map_singleton]
    exact canonP_singleton fresh restrictFresh parts.1 parts.2

omit multisetFresh fresh restrictFresh in
include unitFresh in
/-- The unit inside a bag is dropped. -/
theorem unitElim_keeps (pre post : List Pattern) :
    Keeps block (.collection .hashBag (pre ++ .apply block.unit [] :: post) none)
      (.collection .hashBag (pre ++ post) none) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := collection_notLambda _ _ _
  sameSubst := by simp [substFree_collection, substFree_apply]
  sameBinds := by simp [restrictionsBind_collection, restrictionsBind_apply, bindsAt_of_ne unitFresh]
  canon _ _ := by
    simp only [closeTails_collection, List.map_append, List.map_cons, closeTails_apply, List.map_nil]
    exact canonP_unitElim _ _

omit multisetFresh fresh restrictFresh in
include unitFresh in
/-- The empty bag is the unit. -/
theorem emptyBag_keeps : Keeps block (.collection .hashBag [] none) (.apply block.unit []) where
  sourceNotLambda := collection_notLambda _ _ _
  targetNotLambda := apply_notLambda _ _
  sameSubst := by simp [substFree_collection, substFree_apply]
  sameBinds := by simp [restrictionsBind_collection, restrictionsBind_apply, bindsAt_of_ne unitFresh]
  canon _ _ := by
    simp only [closeTails_collection, closeTails_apply, List.map_nil]
    exact canonP_emptyBag

end Laws

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
