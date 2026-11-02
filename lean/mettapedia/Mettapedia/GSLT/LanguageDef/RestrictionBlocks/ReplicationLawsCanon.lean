import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationTails

/-!
# Each law keeps the canonical block

For object terms whose restrictions bind, both sides of every law have one canonical block: the laws of replication
(`canonP_unfold`, `canonP_replicationNil`, `canonP_twice`, `canonP_replicationPar`, `canonP_idempotent`), of
restriction (`canonP_restrictionNil`, `canonP_exchange`, `canonP_extrusion`, `canonP_extrusion_reverse`,
`canonP_emptyUnit`) and of the bag (`canonP_bag_perm`, `canonP_flatten`, `canonP_singleton`, `canonP_unitElim`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)

variable {block : ReplicationBlock}

/-! ## Blocks side by side -/

/-- A bag of two members joins their canonical blocks. -/
theorem canonP_pair (first second : Pattern) :
    canonP block (.collection .hashBag [first, second] none) =
      normal block ((canonP block first).par (canonP block second)) := by
  rw [canonP_bag, canonsP_eq_map]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, par_nil]

/-- Blocks of no restriction side by side are the block of both lists of components. -/
theorem par_zero (first second : List Pattern) :
    (Prenex.mk 0 first).par ⟨0, second⟩ = ⟨0, first ++ second⟩ := by
  simp only [Prenex.par, Nat.add_zero, Prenex.mk.injEq, true_and]
  have identity : ∀ list : List Pattern, list.map (liftBVars 0 0) = list := fun list => by
    conv_rhs => rw [← List.map_id list]
    exact List.map_congr_left fun component _ => Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero component 0
  rw [identity, identity]

/-- **Blocks side by side, joined in a list, are the blocks of the two lists side by side.** -/
theorem foldr_par_append : ∀ (first second : List Prenex),
    (first ++ second).foldr Prenex.par Prenex.nil =
      (first.foldr Prenex.par Prenex.nil).par (second.foldr Prenex.par Prenex.nil)
  | [], second => (Prenex.nil_par _).symm
  | form :: first, second => by
      rw [List.cons_append, List.foldr_cons, List.foldr_cons, foldr_par_append first second, par_assoc]

/-- No replicated molecule of inaction. -/
theorem replicatedOf_nil (canonical : Pattern → Pattern) : replicatedOf block canonical Prenex.nil = [] := rfl

/-- The replicated molecule of an abstraction alone is its replication. -/
theorem replicatedOf_atom_lambda (canonical : Pattern → Pattern) (binder : Option String) (body : Pattern) :
    replicatedOf block canonical (Prenex.atom (.lambda binder body)) =
      [.apply block.replicate [canonical (.lambda binder body)]] := by
  have identity : Prenex.groupIndex 0 [] = id := by
    funext index
    simp [Prenex.groupIndex]
  simp [replicatedOf, groups, insertComponent, insertUsing, usedRestrictions, Prenex.atom, Prenex.molecule, identity,
    rename_id, Prenex.toPattern, Prenex.restricts, Prenex.body]

/-- Every replicated molecule is the replication of a canonical form. -/
theorem replicatedOf_shape {form : Prenex} {entry : Pattern}
    (member : entry ∈ replicatedOf block (canonicalOf block) form) :
    ∃ pattern, entry = .apply block.replicate [canonicalOf block pattern] := by
  rw [replicatedOf_eq] at member
  obtain ⟨group, _, rfl⟩ := List.mem_map.mp member
  unfold moleculeEntry
  split
  · split_ifs with isReplicate
    · subst isReplicate
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

section Laws

variable (multisetFresh : block.replicate ∉ block.multisets) (fresh : block.replicate ∉ block.emptyUnits)
  (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **Permuting blocks side by side keeps the canonical form.** -/
theorem normal_foldr_perm {first second : List Prenex} (permutation : first.Perm second)
    (atomic : ∀ form ∈ first, form.Atomic block.toBlock) :
    normal block (first.foldr Prenex.par Prenex.nil) = normal block (second.foldr Prenex.par Prenex.nil) := by
  induction permutation with
  | nil => rfl
  | cons form permutation recurse =>
      have formAtomic := atomic form List.mem_cons_self
      have restAtomic : ∀ other ∈ _, Prenex.Atomic block.toBlock other := fun other member =>
        atomic other (List.mem_cons_of_mem _ member)
      rw [List.foldr_cons, List.foldr_cons,
        ← normal_par_normal_right fresh restrictFresh formAtomic (foldr_par_atomic _ restAtomic), recurse restAtomic,
        normal_par_normal_right fresh restrictFresh formAtomic
          (foldr_par_atomic _ fun other member => restAtomic other (permutation.mem_iff.mpr member))]
  | swap first second rest =>
      have firstAtomic := atomic first (by simp)
      have secondAtomic := atomic second (by simp)
      have restAtomic := foldr_par_atomic rest fun other member => atomic other (by simp [member])
      rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, List.foldr_cons, ← par_assoc, ← par_assoc,
        ← normal_par_normal_left fresh restrictFresh (par_atomic secondAtomic firstAtomic) restAtomic,
        normal_par_comm fresh restrictFresh secondAtomic firstAtomic,
        normal_par_normal_left fresh restrictFresh (par_atomic firstAtomic secondAtomic) restAtomic]
  | trans firstPermutation _ firstRecurse secondRecurse =>
      rw [firstRecurse atomic, secondRecurse fun form member => atomic form (firstPermutation.mem_iff.mpr member)]

omit fresh restrictFresh in
/-- Closing twice reads a block only through its canonical form. -/
theorem normal_close_close_normal (fresh : block.replicate ∉ block.emptyUnits)
    (restrictFresh : block.replicate ≠ block.restrict) {form : Prenex} (atomic : form.Atomic block.toBlock) :
    normal block (normal block form).close.close = normal block form.close.close := by
  rw [← normal_close_normal fresh restrictFresh (close_atomic (normal_atomic fresh restrictFresh atomic)),
    normal_close_normal fresh restrictFresh atomic, normal_close_normal fresh restrictFresh (close_atomic atomic)]

/-- Beside a block, inside a restriction, blocks side by side read through their canonical forms. -/
theorem normal_close_par_foldr_normal {first : Prenex} (firstAtomic : first.Atomic block.toBlock)
    {forms : List Prenex} (atomic : ∀ form ∈ forms, form.Atomic block.toBlock) :
    normal block (first.par ((forms.map (normal block)).foldr Prenex.par Prenex.nil)).close =
      normal block (first.par (forms.foldr Prenex.par Prenex.nil)).close := by
  have mappedAtomic : ((forms.map (normal block)).foldr Prenex.par Prenex.nil).Atomic block.toBlock :=
    foldr_par_atomic _ fun form member => by
      obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
      exact normal_atomic fresh restrictFresh (atomic original inOriginal)
  have foldAtomic := foldr_par_atomic forms atomic
  rw [← normal_close_normal fresh restrictFresh (par_atomic firstAtomic mappedAtomic),
    ← normal_par_normal_right fresh restrictFresh firstAtomic mappedAtomic,
    normal_foldr_normal fresh restrictFresh forms atomic,
    normal_par_normal_right fresh restrictFresh firstAtomic foldAtomic,
    normal_close_normal fresh restrictFresh (par_atomic firstAtomic foldAtomic)]

/-! ## The laws of replication -/

include multisetFresh

/-- **A replication's canonical block collects the replicated molecules of its argument's**, an abstraction
included. -/
theorem canonP_replicate_all {argument : Pattern} (object : isObjectPattern argument = true)
    (binds : restrictionsBind block.toBlock argument = true) :
    canonP block (.apply block.replicate [argument]) =
      normal block ⟨0, replicatedOf block (canonicalOf block) (canonP block argument)⟩ := by
  by_cases isLambda : ∃ binder body, argument = .lambda binder body
  · obtain ⟨binder, body, rfl⟩ := isLambda
    have fixed := (canonFacts fresh restrictFresh object binds).fixed
    rw [canonP_lambda] at fixed ⊢
    set inner := Pattern.lambda binder (Prenex.toPattern block.toBlock (canonP block body)) with innerIs
    have innerAtomic : decompose block.toBlock inner = Prenex.atom inner := decompose_lambda binder _
    have innerRead : canonicalOf block inner = inner := by
      rw [canonicalOf_atom innerAtomic]
      rw [normal_atom fresh restrictFresh innerAtomic] at fixed
      exact (List.cons.inj (Prenex.mk.inj fixed).2).1
    rw [canonP_apply_lambda restrictFresh, canonP_lambda, ← innerIs, replicatedOf_atom_lambda, innerRead]
    have argumentIs : objectArgument block block.replicate (Prenex.atom inner) = inner := by
      simp [objectArgument, multisetFresh, toPattern_atom]
    rw [argumentIs]
    have replicateAtomic : decompose block.toBlock (.apply block.replicate [inner]) =
        Prenex.atom (.apply block.replicate [inner]) :=
      replicated_atomic fresh restrictFresh (by simp [isReplicated])
    rw [show (⟨0, [.apply block.replicate [inner]]⟩ : Prenex) = Prenex.atom (.apply block.replicate [inner]) from rfl,
      normal_atom fresh restrictFresh replicateAtomic, recanon_apply_other (Ne.symm restrictFresh.symm) multisetFresh,
      List.map_singleton, canonArgument_canonicalOf, innerRead]
  · push Not at isLambda
    exact canonP_replicate isLambda

/-- Every replicated molecule of a canonical block is read again as itself. -/
theorem recanon_replicatedOf {form : Prenex} {entry : Pattern}
    (member : entry ∈ replicatedOf block (canonicalOf block) form) : recanon block entry = entry := by
  obtain ⟨pattern, rfl⟩ := replicatedOf_shape member
  rw [recanon_apply_other restrictFresh multisetFresh, List.map_singleton, canonArgument_canonicalOf,
    canonicalOf_canonicalOf fresh restrictFresh]

/-- **`!P = {P, !P}`**, in either order of the bag. -/
theorem canonP_unfold {process : Pattern} (object : isObjectPattern process = true)
    (binds : restrictionsBind block.toBlock process = true) :
    canonP block (.collection .hashBag [process, .apply block.replicate [process]] none) =
        canonP block (.apply block.replicate [process]) ∧
      canonP block (.collection .hashBag [.apply block.replicate [process], process] none) =
        canonP block (.apply block.replicate [process]) := by
  have facts := canonFacts fresh restrictFresh object binds
  have entriesAtomic : (Prenex.mk 0 (replicatedOf block (canonicalOf block) (canonP block process))).Atomic
      block.toBlock := fun component member => replicated_atomic fresh restrictFresh (replicatedOf_replicated component member)
  have replicateIs := canonP_replicate_all multisetFresh fresh restrictFresh object binds
  constructor
  · rw [canonP_pair, replicateIs, normal_par_normal_right fresh restrictFresh facts.atomic entriesAtomic,
      normal_par_replicatedOf multisetFresh fresh restrictFresh facts.atomic]
  · rw [canonP_pair, replicateIs, normal_par_normal_left fresh restrictFresh entriesAtomic facts.atomic,
      normal_par_comm fresh restrictFresh entriesAtomic facts.atomic,
      normal_par_replicatedOf multisetFresh fresh restrictFresh facts.atomic]

omit multisetFresh fresh restrictFresh in
/-- **`!0 = 0`.** -/
theorem canonP_replicationNil :
    canonP block (.apply block.replicate [.apply block.unit []]) = canonP block (.apply block.unit []) := by
  rw [canonP_replicate (fun _ _ equal => by cases equal), canonP_unit, replicatedOf_nil]
  exact normal_nil

/-- **`!!P = !P`.** -/
theorem canonP_twice {process : Pattern} (object : isObjectPattern process = true)
    (binds : restrictionsBind block.toBlock process = true) :
    canonP block (.apply block.replicate [.apply block.replicate [process]]) =
      canonP block (.apply block.replicate [process]) := by
  set entries := replicatedOf block (canonicalOf block) (canonP block process) with entriesIs
  have entriesReplicated : ∀ entry ∈ entries, isReplicated block entry = true := fun entry member =>
    replicatedOf_replicated entry member
  have entriesAtomic : (Prenex.mk 0 entries).Atomic block.toBlock := fun component member =>
    replicated_atomic fresh restrictFresh (entriesReplicated component member)
  rw [canonP_replicate (fun _ _ equal => by cases equal), canonP_replicate_all multisetFresh fresh restrictFresh object binds,
    ← entriesIs, normal_replicatedOf_normal multisetFresh fresh restrictFresh entriesAtomic]
  exact normal_replicated_of_mem_iff fresh restrictFresh replicatedOf_replicated entriesReplicated
    (mem_replicatedOf_replications multisetFresh fresh restrictFresh entriesReplicated
      fun entry member => recanon_replicatedOf multisetFresh fresh restrictFresh member)

/-- **`!{P, Q} = {!P, !Q}`**, in either order of the bag. -/
theorem canonP_replicationPar {first second : Pattern} (firstObject : isObjectPattern first = true)
    (firstBinds : restrictionsBind block.toBlock first = true) (secondObject : isObjectPattern second = true)
    (secondBinds : restrictionsBind block.toBlock second = true) :
    canonP block (.apply block.replicate [.collection .hashBag [first, second] none]) =
        canonP block (.collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]] none) ∧
      canonP block (.apply block.replicate [.collection .hashBag [second, first] none]) =
        canonP block (.collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]] none) := by
  have firstFacts := canonFacts fresh restrictFresh firstObject firstBinds
  have secondFacts := canonFacts fresh restrictFresh secondObject secondBinds
  have entriesAtomic : ∀ process : Pattern,
      (Prenex.mk 0 (replicatedOf block (canonicalOf block) (canonP block process))).Atomic block.toBlock :=
    fun _ component member => replicated_atomic fresh restrictFresh (replicatedOf_replicated component member)
  -- the replication of a pair reads the replicated molecules of both
  have pairIs : ∀ {x y : Pattern}, (canonP block x).Atomic block.toBlock → (canonP block y).Atomic block.toBlock →
      canonP block (.apply block.replicate [.collection .hashBag [x, y] none]) =
        normal block ⟨0, replicatedOf block (canonicalOf block) (canonP block x) ++
          replicatedOf block (canonicalOf block) (canonP block y)⟩ := by
    intro x y xAtomic yAtomic
    rw [canonP_replicate (fun _ _ equal => by cases equal), canonP_pair,
      normal_replicatedOf_normal multisetFresh fresh restrictFresh (par_atomic xAtomic yAtomic),
      normal_replicatedOf_par multisetFresh fresh restrictFresh xAtomic yAtomic]
  have bagIs : canonP block (.collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]]
      none) = normal block ⟨0, replicatedOf block (canonicalOf block) (canonP block first) ++
        replicatedOf block (canonicalOf block) (canonP block second)⟩ := by
    rw [canonP_pair, canonP_replicate_all multisetFresh fresh restrictFresh firstObject firstBinds,
      canonP_replicate_all multisetFresh fresh restrictFresh secondObject secondBinds,
      normal_par_normal_left fresh restrictFresh (entriesAtomic first)
        (normal_atomic fresh restrictFresh (entriesAtomic second)),
      normal_par_normal_right fresh restrictFresh (entriesAtomic first) (entriesAtomic second), par_zero]
  refine ⟨by rw [pairIs firstFacts.atomic secondFacts.atomic, bagIs], ?_⟩
  rw [pairIs secondFacts.atomic firstFacts.atomic, bagIs]
  refine normal_replicated_of_mem_iff fresh restrictFresh ?_ ?_ fun component => ?_
  · intro component member
    rcases List.mem_append.mp member with inSecond | inFirst
    · exact replicatedOf_replicated component inSecond
    · exact replicatedOf_replicated component inFirst
  · intro component member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact replicatedOf_replicated component inFirst
    · exact replicatedOf_replicated component inSecond
  · simp only [List.mem_append]
    exact Or.comm

/-- **`{!P, !P} = !P`.** -/
theorem canonP_idempotent {process : Pattern} (object : isObjectPattern process = true)
    (binds : restrictionsBind block.toBlock process = true) :
    canonP block (.collection .hashBag [.apply block.replicate [process], .apply block.replicate [process]] none) =
      canonP block (.apply block.replicate [process]) := by
  set entries := replicatedOf block (canonicalOf block) (canonP block process) with entriesIs
  have entriesReplicated : ∀ entry ∈ entries, isReplicated block entry = true := fun entry member =>
    replicatedOf_replicated entry member
  have entriesAtomic : (Prenex.mk 0 entries).Atomic block.toBlock := fun component member =>
    replicated_atomic fresh restrictFresh (entriesReplicated component member)
  have doubleAtomic : (Prenex.mk 0 (entries ++ entries)).Atomic block.toBlock := fun component member => by
    rcases List.mem_append.mp member with inside | inside <;> exact entriesAtomic component inside
  rw [canonP_pair, canonP_replicate_all multisetFresh fresh restrictFresh object binds, ← entriesIs,
    normal_par_normal_left fresh restrictFresh entriesAtomic (normal_atomic fresh restrictFresh entriesAtomic),
    normal_par_normal_right fresh restrictFresh entriesAtomic entriesAtomic, par_zero]
  exact normal_append_duplicates fresh restrictFresh entries (fun _ member => member) entriesReplicated doubleAtomic

omit multisetFresh

/-! ## The laws of restriction -/

omit fresh restrictFresh in
/-- **`(νx)0 = 0`.** -/
theorem canonP_restrictionNil (binder : Option String) :
    canonP block (.apply block.restrict [.lambda binder (.apply block.unit [])]) =
      canonP block (.apply block.unit []) := by
  rw [canonP_restrict, canonP_unit]
  have closed : Prenex.nil.close = Prenex.nil := by simp [Prenex.close, Prenex.nil]
  rw [closed]
  exact normal_nil

include multisetFresh in
/-- **Exchanging two restrictions.** -/
theorem canonP_exchange {outerBinder innerBinder : Option String} {body : Pattern}
    (object : isObjectPattern body = true) (binds : restrictionsBind block.toBlock body = true) :
    canonP block (.apply block.restrict [.lambda outerBinder (.apply block.restrict [.lambda innerBinder body])]) =
      canonP block (.apply block.restrict [.lambda none (.apply block.restrict [.lambda none
        (rename swapInner body)])]) := by
  have facts := canonFacts fresh restrictFresh object binds
  have injective : Function.Injective swapInner := fun first second same => by
    rw [← swapInner_swapInner first, same, swapInner_swapInner]
  rw [canonP_restrict, canonP_restrict, canonP_restrict, canonP_restrict,
    normal_close_normal fresh restrictFresh (close_atomic facts.atomic),
    canonP_rename multisetFresh fresh restrictFresh object binds injective,
    normal_close_normal fresh restrictFresh (close_atomic (normal_atomic fresh restrictFresh
      (renameOuter_atomic facts.atomic swapInner))),
    normal_close_close_normal fresh restrictFresh (renameOuter_atomic facts.atomic swapInner)]
  exact normal_exchange fresh restrictFresh facts.atomic

omit restrictFresh in
/-- An empty named multiset whose empty instance is the unit, and the restriction of inaction, are inaction. -/
theorem canonP_emptyUnit {label : String} (listed : label ∈ block.emptyUnits) :
    canonP block (.apply label [.collection .hashBag [] none]) =
      canonP block (.apply block.restrict [.lambda none (.apply block.unit [])]) := by
  rw [canonP_restrictionNil, canonP_unit]
  refine canonP_empty listed (fun same => fresh (same ▸ listed)) (fun _ _ equal => by cases equal) ?_
  rw [canonP_bag]
  exact normal_nil

/-- Members of a list whose canonical blocks are canonical blocks of atoms. -/
theorem map_canonP_atomic {patterns : List Pattern} (object : ∀ pattern ∈ patterns, isObjectPattern pattern = true)
    (binds : ∀ pattern ∈ patterns, restrictionsBind block.toBlock pattern = true) :
    ∀ form ∈ patterns.map (canonP block), form.Atomic block.toBlock := by
  intro form member
  obtain ⟨pattern, inPatterns, rfl⟩ := List.mem_map.mp member
  exact (canonFacts fresh restrictFresh (object pattern inPatterns) (binds pattern inPatterns)).atomic

omit fresh restrictFresh in
theorem shiftAbove_injective : Function.Injective (shiftAbove 0 1) := fun first second same => by
  simp only [shiftAbove, Nat.not_lt_zero, if_false] at same
  omega

include multisetFresh in
/-- Members lifted past a new restriction have the canonical blocks of the members, renamed outside. -/
theorem map_canonP_lift {patterns : List Pattern} (object : ∀ pattern ∈ patterns, isObjectPattern pattern = true)
    (binds : ∀ pattern ∈ patterns, restrictionsBind block.toBlock pattern = true) :
    (patterns.map (liftBVars 0 1)).map (canonP block) =
      ((patterns.map (canonP block)).map (Prenex.renameOuter (shiftAbove 0 1))).map (normal block) := by
  simp only [List.map_map]
  exact List.map_congr_left fun pattern member => by
    simp only [Function.comp_apply]
    rw [liftBVars_eq_rename, canonP_rename multisetFresh fresh restrictFresh (object pattern member) (binds pattern member)
      shiftAbove_injective]

omit fresh restrictFresh in
theorem map_renameOuter_atomic {forms : List Prenex} (atomic : ∀ form ∈ forms, form.Atomic block.toBlock)
    (relabel : Nat → Nat) : ∀ form ∈ forms.map (Prenex.renameOuter relabel), form.Atomic block.toBlock := by
  intro form member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
  exact renameOuter_atomic (atomic original inOriginal) relabel

theorem map_normal_atomic {forms : List Prenex} (atomic : ∀ form ∈ forms, form.Atomic block.toBlock) :
    ∀ form ∈ forms.map (normal block), form.Atomic block.toBlock := by
  intro form member
  obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
  exact normal_atomic fresh restrictFresh (atomic original inOriginal)

include multisetFresh in
/-- **Scope extrusion**: a bag with a restriction among its members, and the restriction over the bag of the
restricted body and the other members lifted past it. -/
theorem canonP_extrusion {members : List Pattern} {selected : Nat} (inside : selected < members.length)
    {binder : Option String} {body : Pattern} (chosen : members[selected] = .apply block.restrict [.lambda binder body])
    (object : ∀ member ∈ members, isObjectPattern member = true)
    (binds : ∀ member ∈ members, restrictionsBind block.toBlock member = true) :
    canonP block (.collection .hashBag members none) =
      canonP block (.apply block.restrict [.lambda none (.collection .hashBag
        (body :: (members.eraseIdx selected).map (liftBVars 0 1)) none)]) := by
  have selectedMember : members[selected] ∈ members := List.getElem_mem inside
  have restrictionObject := object _ selectedMember
  have restrictionBinds := binds _ selectedMember
  rw [chosen] at restrictionObject restrictionBinds
  have bodyObject : isObjectPattern body = true := by
    simpa [isObjectPattern, isObjectPatternList] using restrictionObject
  have bodyBinds : restrictionsBind block.toBlock body = true := by
    simpa [restrictionsBind, restrictionsBindList, bindsAt] using restrictionBinds
  have bodyFacts := canonFacts fresh restrictFresh bodyObject bodyBinds
  have othersObject : ∀ other ∈ members.eraseIdx selected, isObjectPattern other = true := fun other member =>
    object other (List.mem_of_mem_eraseIdx member)
  have othersBinds : ∀ other ∈ members.eraseIdx selected, restrictionsBind block.toBlock other = true :=
    fun other member => binds other (List.mem_of_mem_eraseIdx member)
  have othersAtomic := map_canonP_atomic fresh restrictFresh othersObject othersBinds
  have sourceIs : canonP block (.collection .hashBag members none) =
      normal block ((canonP block body).par ((((members.eraseIdx selected).map (canonP block)).foldr Prenex.par
        Prenex.nil).renameOuter (shiftAbove 0 1))).close := by
    rw [canonP_bag, canonsP_eq_map, normal_foldr_perm fresh restrictFresh
      ((perm_getElem_eraseIdx members selected inside).map (canonP block))
      (map_canonP_atomic fresh restrictFresh object binds), List.map_cons, List.foldr_cons, chosen, canonP_restrict,
      normal_par_normal_left fresh restrictFresh (close_atomic bodyFacts.atomic) (foldr_par_atomic _ othersAtomic),
      extrusion_block]
  have liftedObject : ∀ other ∈ (members.eraseIdx selected).map (liftBVars 0 1), isObjectPattern other = true := by
    intro other member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [liftBVars_eq_rename, isObjectPattern_rename]
    exact othersObject original inOriginal
  have liftedBinds : ∀ other ∈ (members.eraseIdx selected).map (liftBVars 0 1),
      restrictionsBind block.toBlock other = true := by
    intro other member
    obtain ⟨original, inOriginal, rfl⟩ := List.mem_map.mp member
    rw [liftBVars_eq_rename, restrictionsBind_rename]
    exact othersBinds original inOriginal
  have targetIs : canonP block (.apply block.restrict [.lambda none (.collection .hashBag
      (body :: (members.eraseIdx selected).map (liftBVars 0 1)) none)]) =
      normal block ((canonP block body).par ((((members.eraseIdx selected).map (canonP block)).foldr Prenex.par
        Prenex.nil).renameOuter (shiftAbove 0 1))).close := by
    rw [canonP_restrict, canonP_bag, canonsP_eq_map, List.map_cons, List.foldr_cons,
      normal_close_normal fresh restrictFresh (par_atomic bodyFacts.atomic
        (foldr_par_atomic _ (map_canonP_atomic fresh restrictFresh liftedObject liftedBinds))),
      map_canonP_lift multisetFresh fresh restrictFresh othersObject othersBinds,
      normal_close_par_foldr_normal fresh restrictFresh bodyFacts.atomic
        (map_renameOuter_atomic othersAtomic _), ← foldr_par_renameOuter]
  rw [sourceIs, targetIs]

include multisetFresh in
/-- **Scope extrusion, read backward.** -/
theorem canonP_extrusion_reverse {binder : Option String} {members : List Pattern} {selected : Nat}
    (inside : selected < members.length) {originals : List Pattern}
    (erased : members.eraseIdx selected = originals.map (liftBVars 0 1))
    (object : ∀ member ∈ members, isObjectPattern member = true)
    (binds : ∀ member ∈ members, restrictionsBind block.toBlock member = true) :
    canonP block (.apply block.restrict [.lambda binder (.collection .hashBag members none)]) =
      canonP block (.collection .hashBag (.apply block.restrict [.lambda none members[selected]] :: originals) none) := by
  have selectedMember : members[selected] ∈ members := List.getElem_mem inside
  have selectedFacts := canonFacts fresh restrictFresh (object _ selectedMember) (binds _ selectedMember)
  have originalsObject : ∀ original ∈ originals, isObjectPattern original = true := by
    intro original member
    have lifted : liftBVars 0 1 original ∈ members.eraseIdx selected := by
      rw [erased]
      exact List.mem_map_of_mem member
    have := object _ (List.mem_of_mem_eraseIdx lifted)
    rwa [liftBVars_eq_rename, isObjectPattern_rename] at this
  have originalsBinds : ∀ original ∈ originals, restrictionsBind block.toBlock original = true := by
    intro original member
    have lifted : liftBVars 0 1 original ∈ members.eraseIdx selected := by
      rw [erased]
      exact List.mem_map_of_mem member
    have := binds _ (List.mem_of_mem_eraseIdx lifted)
    rwa [liftBVars_eq_rename, restrictionsBind_rename] at this
  have originalsAtomic := map_canonP_atomic fresh restrictFresh originalsObject originalsBinds
  have othersObject : ∀ other ∈ members.eraseIdx selected, isObjectPattern other = true := fun other member =>
    object other (List.mem_of_mem_eraseIdx member)
  have othersBinds : ∀ other ∈ members.eraseIdx selected, restrictionsBind block.toBlock other = true :=
    fun other member => binds other (List.mem_of_mem_eraseIdx member)
  have sourceIs : canonP block (.apply block.restrict [.lambda binder (.collection .hashBag members none)]) =
      normal block ((canonP block members[selected]).close.par ((originals.map (canonP block)).foldr Prenex.par
        Prenex.nil)) := by
    rw [canonP_restrict, canonP_bag, canonsP_eq_map, normal_foldr_perm fresh restrictFresh
      ((perm_getElem_eraseIdx members selected inside).map (canonP block))
      (map_canonP_atomic fresh restrictFresh object binds),
      normal_close_normal fresh restrictFresh (foldr_par_atomic _
        (map_canonP_atomic fresh restrictFresh (fun other member => by
          rcases List.mem_cons.mp member with rfl | inOthers
          · exact object _ selectedMember
          · exact othersObject other inOthers) (fun other member => by
          rcases List.mem_cons.mp member with rfl | inOthers
          · exact binds _ selectedMember
          · exact othersBinds other inOthers))),
      List.map_cons, List.foldr_cons, erased,
      map_canonP_lift multisetFresh fresh restrictFresh originalsObject originalsBinds,
      normal_close_par_foldr_normal fresh restrictFresh selectedFacts.atomic
        (map_renameOuter_atomic originalsAtomic _), ← foldr_par_renameOuter, ← extrusion_block]
  have targetIs : canonP block (.collection .hashBag (.apply block.restrict [.lambda none members[selected]] ::
      originals) none) = normal block ((canonP block members[selected]).close.par
        ((originals.map (canonP block)).foldr Prenex.par Prenex.nil)) := by
    rw [canonP_bag, canonsP_eq_map, List.map_cons, List.foldr_cons, canonP_restrict,
      normal_par_normal_left fresh restrictFresh (close_atomic selectedFacts.atomic)
        (foldr_par_atomic _ originalsAtomic)]
  rw [sourceIs, targetIs]

/-! ## The laws of the bag -/

/-- **Permuting the members of a bag.** -/
theorem canonP_bag_perm {first second : List Pattern} (permutation : first.Perm second)
    (object : ∀ member ∈ first, isObjectPattern member = true)
    (binds : ∀ member ∈ first, restrictionsBind block.toBlock member = true) :
    canonP block (.collection .hashBag first none) = canonP block (.collection .hashBag second none) := by
  rw [canonP_bag, canonP_bag, canonsP_eq_map, canonsP_eq_map]
  exact normal_foldr_perm fresh restrictFresh (permutation.map (canonP block))
    (map_canonP_atomic fresh restrictFresh object binds)

/-- **A bag inside a bag is flattened.** -/
theorem canonP_flatten {pre inner post : List Pattern}
    (object : ∀ member ∈ pre ++ inner ++ post, isObjectPattern member = true)
    (binds : ∀ member ∈ pre ++ inner ++ post, restrictionsBind block.toBlock member = true) :
    canonP block (.collection .hashBag (pre ++ .collection .hashBag inner none :: post) none) =
      canonP block (.collection .hashBag (pre ++ inner ++ post) none) := by
  have atomic := map_canonP_atomic fresh restrictFresh object binds
  have preAtomic : ∀ form ∈ pre.map (canonP block), form.Atomic block.toBlock := fun form member =>
    atomic form (by simp only [List.map_append, List.mem_append] at member ⊢; exact .inl (.inl member))
  have innerAtomic : ∀ form ∈ inner.map (canonP block), form.Atomic block.toBlock := fun form member =>
    atomic form (by simp only [List.map_append, List.mem_append] at member ⊢; exact .inl (.inr member))
  have postAtomic : ∀ form ∈ post.map (canonP block), form.Atomic block.toBlock := fun form member =>
    atomic form (by simp only [List.map_append, List.mem_append] at member ⊢; exact .inr member)
  have preFold := foldr_par_atomic _ preAtomic
  have innerFold := foldr_par_atomic _ innerAtomic
  have postFold := foldr_par_atomic _ postAtomic
  rw [canonP_bag, canonP_bag, canonsP_eq_map, canonsP_eq_map, List.map_append, List.map_cons, canonP_bag,
    canonsP_eq_map, List.map_append, List.map_append, foldr_par_append, foldr_par_append, foldr_par_append,
    List.foldr_cons,
    ← normal_par_normal_right fresh restrictFresh preFold (par_atomic (normal_atomic fresh restrictFresh innerFold)
      postFold),
    normal_par_normal_left fresh restrictFresh innerFold postFold,
    normal_par_normal_right fresh restrictFresh preFold (par_atomic innerFold postFold), par_assoc]

omit fresh restrictFresh in
/-- **The unit inside a bag is dropped.** -/
theorem canonP_unitElim (pre post : List Pattern) :
    canonP block (.collection .hashBag (pre ++ .apply block.unit [] :: post) none) =
      canonP block (.collection .hashBag (pre ++ post) none) := by
  rw [canonP_bag, canonP_bag, canonsP_eq_map, canonsP_eq_map, List.map_append, List.map_cons, canonP_unit,
    List.map_append, foldr_par_append, foldr_par_append, List.foldr_cons, Prenex.nil_par]

/-- **A one-member bag is its member.** -/
theorem canonP_singleton {element : Pattern} (object : isObjectPattern element = true)
    (binds : restrictionsBind block.toBlock element = true) :
    canonP block (.collection .hashBag [element] none) = canonP block element := by
  rw [canonP_bag, canonsP_eq_map, List.map_singleton, List.foldr_cons, List.foldr_nil, par_nil]
  exact (canonFacts fresh restrictFresh object binds).fixed

omit fresh restrictFresh in
/-- **The empty bag is the unit.** -/
theorem canonP_emptyBag :
    canonP block (.collection .hashBag [] none) = canonP block (.apply block.unit []) := by
  rw [canonP_bag, canonP_unit]
  exact normal_nil

end Laws

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
