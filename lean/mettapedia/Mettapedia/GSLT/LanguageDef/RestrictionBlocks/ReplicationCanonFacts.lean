import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationUnfold

/-!
# The canonical block of an object pattern is canonical

The canonical block of an object pattern is a block of atoms using every restriction it keeps, and it is its own
canonical form (`canonFacts`); so its pattern is its own canonical form (`canonicalOf_canonR`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern isObjectPatternList)

variable {block : ReplicationBlock}

/-- Whether the arguments of a constructor bind as the restriction's must: the restriction takes one abstraction. -/
def bindsAt (block : Block) (label : String) : List Pattern → Bool
  | [.lambda _ _] => true
  | _ => label != block.restrict

mutual
  /-- **Whether every restriction binds**: at every node, the restriction applied to one argument is applied to an
  abstraction. Every term of a sort is such a term. -/
  def restrictionsBind (block : Block) : Pattern → Bool
    | .bvar _ | .fvar _ => true
    | .apply label arguments => bindsAt block label arguments && restrictionsBindList block arguments
    | .lambda _ body => restrictionsBind block body
    | .multiLambda _ _ body => restrictionsBind block body
    | .subst body replacement => restrictionsBind block body && restrictionsBind block replacement
    | .collection _ elements _ => restrictionsBindList block elements

  def restrictionsBindList (block : Block) : List Pattern → Bool
    | [] => true
    | pattern :: patterns => restrictionsBind block pattern && restrictionsBindList block patterns
end

theorem restrictionsBindList_eq_all (base : Block) (patterns : List Pattern) :
    restrictionsBindList base patterns = patterns.all (restrictionsBind base) := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [restrictionsBindList, recurse]

/-- **What the canonical block of a pattern owes**: atoms, every restriction used, its own canonical form. -/
structure CanonFacts (block : ReplicationBlock) (pattern : Pattern) : Prop where
  atomic : (canonP block pattern).Atomic block.toBlock
  used : (canonP block pattern).Used
  fixed : normal block (canonP block pattern) = canonP block pattern

theorem normal_nil : normal block Prenex.nil = Prenex.nil := by
  unfold normal
  obtain ⟨fuel, fuelIs⟩ : ∃ fuel, 3 * size (Prenex.toPattern block.toBlock Prenex.nil) + 3 = fuel + 1 := ⟨_, rfl⟩
  rw [fuelIs]
  exact normalizeWith_empty fuel

section Facts

variable (fresh : block.replicate ∉ block.emptyUnits) (restrictFresh : block.replicate ≠ block.restrict)

include fresh restrictFresh

/-- **A block of one atom reads canonically as the atom with its parts read again.** -/
theorem normal_atom {component : Pattern} (atomic : decompose block.toBlock component = Prenex.atom component) :
    normal block (Prenex.atom component) = Prenex.atom (recanon block component) := by
  have canonicalIs := canonicalOf_atom (block := block) atomic
  unfold canonicalOf at canonicalIs
  rw [atomic] at canonicalIs
  have atomAtomic : (Prenex.atom component).Atomic block.toBlock := by
    intro other member
    rw [show (Prenex.atom component).components = [component] from rfl, List.mem_singleton] at member
    subst member
    exact atomic
  have bundle := bundle_all fresh restrictFresh (size component + 1)
  have readAtomic : (Prenex.atom (recanon block component)).Atomic block.toBlock := by
    intro other member
    rw [show (Prenex.atom (recanon block component)).components = [recanon block component] from rfl,
      List.mem_singleton] at member
    subst member
    exact recanon_atomic bundle.atomic bundle.nonEmpty (le_of_lt (Nat.lt_succ_self _)) atomic
  exact toPattern_injective (normal_atomic fresh restrictFresh atomAtomic) readAtomic canonicalIs

omit fresh restrictFresh in
theorem atom_facts {component : Pattern} (atomic : decompose block.toBlock component = Prenex.atom component) :
    (Prenex.atom component).Atomic block.toBlock ∧ (Prenex.atom component).Used := by
  refine ⟨fun other member => ?_, fun index below => absurd below (Nat.not_lt_zero _)⟩
  rw [show (Prenex.atom component).components = [component] from rfl, List.mem_singleton] at member
  subst member
  exact atomic

omit fresh restrictFresh in
theorem close_atomic {form : Prenex} (atomic : form.Atomic block.toBlock) : form.close.Atomic block.toBlock := by
  unfold Prenex.close
  split_ifs
  · exact atomic
  · exact atomic_map_rename atomic _

/-- **The canonical block of a normalized block owes what a canonical block owes.** -/
theorem normal_facts {form : Prenex} (atomic : form.Atomic block.toBlock) :
    (normal block form).Atomic block.toBlock ∧ (normal block form).Used ∧
      normal block (normal block form) = normal block form :=
  ⟨normal_atomic fresh restrictFresh atomic, used_normal fresh restrictFresh _ atomic,
    normal_normal fresh restrictFresh atomic⟩

omit fresh restrictFresh in
/-- **A block's pattern is its own canonical form when the block is.** -/
theorem canonicalOf_toPattern_fixed {form : Prenex} (atomic : form.Atomic block.toBlock) (used : form.Used)
    (fixed : normal block form = form) :
    canonicalOf block (Prenex.toPattern block.toBlock form) = Prenex.toPattern block.toBlock form := by
  rw [canonicalOf_toPattern atomic used, fixed]

omit fresh restrictFresh in
/-- An object argument is read as the multiset of its canonical block under a named multiset, and as the canonical
block's pattern otherwise. -/
theorem argumentOf_object {label : String} {argument : Pattern} {form : Prenex}
    (object : isObjectPattern argument = true) :
    argumentOf block label argument form =
      if label ∈ block.multisets then multisetOf block.toBlock form else Prenex.toPattern block.toBlock form := by
  unfold argumentOf
  split_ifs with listed
  · cases argument with
    | collection kind elements rest =>
        cases rest with
        | none => rfl
        | some rest => simp [isObjectPattern] at object
    | subst body replacement => simp [isObjectPattern] at object
    | _ => rfl
  · rfl

omit fresh restrictFresh in
/-- **An argument read again from a canonical block is the canonical argument.** -/
theorem partOf_argumentOf {label : String} {argument : Pattern} {form : Prenex} (atomic : form.Atomic block.toBlock)
    (used : form.Used) (fixed : normal block form = form) (object : isObjectPattern argument = true) :
    partOf block label (argumentOf block label argument form) = argumentOf block label argument form := by
  rw [argumentOf_object object]
  unfold partOf
  by_cases isRestrict : label = block.restrict
  · simp only [if_pos isRestrict, id]
  · by_cases listed : label ∈ block.multisets
    · simp only [if_neg isRestrict, if_pos listed]
      obtain ⟨elements, bagIs⟩ := multisetOf_shape block.toBlock form
      rw [bagIs, multisetPart_other (fun _ _ _ equal => by cases equal) (fun _ _ equal => by cases equal), ← bagIs,
        decompose_multisetOf atomic used, fixed]
    · simp only [if_neg isRestrict, if_neg listed]
      exact canonicalOf_toPattern_fixed atomic used fixed

omit fresh restrictFresh in
/-- An abstraction with a canonical body is read again as itself. -/
theorem recanon_lambda_fixed {binder : Option String} {body : Pattern}
    (fixed : canonicalOf block body = body) : recanon block (.lambda binder body) = .lambda binder body := by
  rw [recanon_lambda, fixed]

omit fresh restrictFresh in
/-- An object argument read from a block of atoms, every restriction used, decomposes into that block. -/
theorem decompose_argumentOf {label : String} {argument : Pattern} {form : Prenex}
    (object : isObjectPattern argument = true) (atomic : form.Atomic block.toBlock) (used : form.Used) :
    decompose block.toBlock (argumentOf block label argument form) = form := by
  rw [argumentOf_object object]
  split_ifs
  · exact decompose_multisetOf atomic used
  · exact decompose_toPattern atomic used

omit fresh restrictFresh in
/-- **One argument of a constructor other than the restriction**, its block not the inaction of an empty named
multiset, is one component. -/
theorem decompose_single {label : String} {argument : Pattern} {form : Prenex} (notRestrict : label ≠ block.restrict)
    (read : decompose block.toBlock argument = form) (notEmpty : ¬ (label ∈ block.emptyUnits ∧ form = Prenex.nil)) :
    decompose block.toBlock (.apply label [argument]) = Prenex.atom (.apply label [argument]) := by
  refine decompose_multiset_atom (fun binder body equal => ?_) (by rw [read]; exact notEmpty)
  simp only [Pattern.apply.injEq] at equal
  exact notRestrict equal.1

omit fresh restrictFresh in
/-- Blocks of atoms side by side are a block of atoms. -/
theorem foldr_par_atomic : ∀ (forms : List Prenex), (∀ form ∈ forms, form.Atomic block.toBlock) →
    (forms.foldr Prenex.par Prenex.nil).Atomic block.toBlock
  | [], _ => fun _ member => by simp [Prenex.nil] at member
  | form :: forms, atomic => by
      rw [List.foldr_cons]
      exact par_atomic (atomic form List.mem_cons_self)
        (foldr_par_atomic forms fun other member => atomic other (List.mem_cons_of_mem _ member))

/-- The facts of a pattern whose canonical block is one component that is its own block and is read again as
itself. -/
theorem canonFacts_of_atom {pattern component : Pattern} (isAtom : canonP block pattern = Prenex.atom component)
    (atomic : decompose block.toBlock component = Prenex.atom component) (read : recanon block component = component) :
    CanonFacts block pattern := by
  obtain ⟨atoms, used⟩ := atom_facts atomic
  refine ⟨?_, ?_, ?_⟩ <;> rw [isAtom]
  · exact atoms
  · exact used
  · rw [normal_atom fresh restrictFresh atomic, read]

/-- The facts of a pattern whose canonical block is a normalized block of atoms. -/
theorem canonFacts_of_normal {pattern : Pattern} {form : Prenex} (isNormal : canonP block pattern = normal block form)
    (atomic : form.Atomic block.toBlock) : CanonFacts block pattern := by
  obtain ⟨atoms, used, fixed⟩ := normal_facts fresh restrictFresh atomic
  refine ⟨?_, ?_, ?_⟩ <;> rw [isNormal]
  · exact atoms
  · exact used
  · exact fixed

omit fresh restrictFresh in
/-- The facts of a pattern whose canonical block is inaction. -/
theorem canonFacts_of_nil {pattern : Pattern} (isNil : canonP block pattern = Prenex.nil) : CanonFacts block pattern := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [isNil]
  · intro component member
    simp [Prenex.nil] at member
  · intro index below
    exact absurd below (Nat.not_lt_zero _)
  · exact normal_nil

omit fresh restrictFresh in
/-- A constructor's arguments read again from their canonical blocks are themselves. -/
theorem map_partOf_argumentOf {label : String} {arguments : List Pattern}
    (facts : ∀ argument ∈ arguments, CanonFacts block argument)
    (object : ∀ argument ∈ arguments, isObjectPattern argument = true) :
    (arguments.map fun argument => argumentOf block label argument (canonP block argument)).map (partOf block label) =
      arguments.map fun argument => argumentOf block label argument (canonP block argument) := by
  rw [List.map_map]
  refine List.map_congr_left fun argument member => ?_
  exact partOf_argumentOf (facts argument member).atomic (facts argument member).used (facts argument member).fixed
    (object argument member)

omit fresh restrictFresh in
/-- A lone argument other than an abstraction binds exactly under a constructor other than the restriction. -/
theorem bindsAt_single {base : Block} {label : String} {argument : Pattern}
    (notLambda : ∀ binder body, argument ≠ .lambda binder body) :
    bindsAt base label [argument] = (label != base.restrict) := by
  cases argument with
  | lambda binder body => exact absurd rfl (notLambda binder body)
  | _ => rfl

omit fresh restrictFresh in
/-- Arguments other than one abstraction bind exactly under a constructor other than the restriction. -/
theorem bindsAt_other {base : Block} {label : String} {arguments : List Pattern}
    (notLambda : ∀ binder body, arguments ≠ [.lambda binder body]) :
    bindsAt base label arguments = (label != base.restrict) := by
  match arguments, notLambda with
  | [.lambda binder body], notLambda => exact absurd rfl (notLambda binder body)
  | [], _ => rfl
  | [.bvar _], _ => rfl
  | [.fvar _], _ => rfl
  | [.apply _ _], _ => rfl
  | [.multiLambda _ _ _], _ => rfl
  | [.subst _ _], _ => rfl
  | [.collection _ _ _], _ => rfl
  | first :: _ :: _, _ => cases first <;> rfl

/-- The canonical facts of a pattern, and of the body of an abstraction. -/
theorem canonFacts_and (pattern : Pattern) :
    (isObjectPattern pattern = true → restrictionsBind block.toBlock pattern = true → CanonFacts block pattern) ∧
      ∀ binder body, pattern = .lambda binder body → isObjectPattern body = true →
        restrictionsBind block.toBlock body = true → CanonFacts block body := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      exact ⟨fun _ _ => canonFacts_of_atom fresh restrictFresh (by simp [canonP]) (decompose_bvar index)
        (recanon_bvar index), fun _ _ equal => by cases equal⟩
  | hfvar name =>
      exact ⟨fun _ _ => canonFacts_of_atom fresh restrictFresh (by simp [canonP]) (decompose_fvar name)
        (recanon_fvar name), fun _ _ equal => by cases equal⟩
  | hsubst body replacement _ _ =>
      exact ⟨fun object _ => by simp [isObjectPattern] at object, fun _ _ equal => by cases equal⟩
  | hlambda binder body recurse =>
      refine ⟨fun object binds => ?_, fun binder' body' equal => by cases equal; exact recurse.1⟩
      have facts := recurse.1 (by simpa [isObjectPattern] using object) (by simpa [restrictionsBind] using binds)
      exact canonFacts_of_atom fresh restrictFresh (canonP_lambda binder body) (decompose_lambda binder _)
        (recanon_lambda_fixed (canonicalOf_toPattern_fixed facts.atomic facts.used facts.fixed))
  | hmultiLambda arity binders body recurse =>
      refine ⟨fun object binds => ?_, fun _ _ equal => by cases equal⟩
      have facts := recurse.1 (by simpa [isObjectPattern] using object) (by simpa [restrictionsBind] using binds)
      have isAtom : canonP block (.multiLambda arity binders body) =
          Prenex.atom (.multiLambda arity binders (Prenex.toPattern block.toBlock (canonP block body))) := by
        simp [canonP]
      refine canonFacts_of_atom fresh restrictFresh isAtom (decompose_multiLambda arity binders _) ?_
      rw [recanon_multiLambda, canonicalOf_toPattern_fixed facts.atomic facts.used facts.fixed]
  | hcollection kind elements rest recurse =>
      refine ⟨fun object binds => ?_, fun _ _ equal => by cases equal⟩
      simp only [isObjectPattern, isObjectPatternList_eq_all, Bool.and_eq_true, List.all_eq_true] at object
      simp only [restrictionsBind, restrictionsBindList_eq_all, List.all_eq_true] at binds
      obtain ⟨closed, objects⟩ := object
      have facts : ∀ element ∈ elements, CanonFacts block element := fun element member =>
        (recurse element member).1 (objects element member) (binds element member)
      have fixedAll : ((canonsP block elements).map (Prenex.toPattern block.toBlock)).map (canonicalOf block) =
          (canonsP block elements).map (Prenex.toPattern block.toBlock) := by
        rw [canonsP_eq_map]
        simp only [List.map_map]
        exact List.map_congr_left fun element member => by
          simp only [Function.comp_apply]
          exact canonicalOf_toPattern_fixed (facts element member).atomic (facts element member).used
            (facts element member).fixed
      cases rest with
      | some name => simp at closed
      | none =>
          cases kind with
          | hashBag =>
              refine canonFacts_of_normal fresh restrictFresh (canonP_bag elements) ?_
              rw [canonsP_eq_map]
              exact foldr_par_atomic _ fun form member => by
                obtain ⟨element, inElements, rfl⟩ := List.mem_map.mp member
                exact (facts element inElements).atomic
          | hashSet =>
              have isAtom : canonP block (.collection .hashSet elements none) =
                  Prenex.atom (.collection .hashSet ((canonsP block elements).map (Prenex.toPattern block.toBlock))
                    none) := by
                simp [canonP]
              refine canonFacts_of_atom fresh restrictFresh isAtom (decompose_atom (by simp)
                (fun _ _ equal => by cases equal) (fun _ equal => by cases equal) (fun _ _ equal => by cases equal)) ?_
              rw [recanon_collection, fixedAll]
          | vec =>
              have isAtom : canonP block (.collection .vec elements none) =
                  Prenex.atom (.collection .vec ((canonsP block elements).map (Prenex.toPattern block.toBlock))
                    none) := by
                simp [canonP]
              refine canonFacts_of_atom fresh restrictFresh isAtom (decompose_atom (by simp)
                (fun _ _ equal => by cases equal) (fun _ equal => by cases equal) (fun _ _ equal => by cases equal)) ?_
              rw [recanon_collection, fixedAll]
  | happly label arguments recurse =>
      refine ⟨fun object binds => ?_, fun _ _ equal => by cases equal⟩
      simp only [isObjectPattern, isObjectPatternList_eq_all, List.all_eq_true] at object
      simp only [restrictionsBind, restrictionsBindList_eq_all, Bool.and_eq_true, List.all_eq_true] at binds
      obtain ⟨bindsHere, bindsBelow⟩ := binds
      have facts : ∀ argument ∈ arguments, CanonFacts block argument := fun argument member =>
        (recurse argument member).1 (object argument member) (bindsBelow argument member)
      rcases arguments with _ | ⟨argument, _ | ⟨second, rest⟩⟩
      · -- no argument: the unit is inaction, any other constant one component
        by_cases isUnit : label = block.unit
        · subst isUnit
          exact canonFacts_of_nil canonP_unit
        · have isAtom : canonP block (.apply label []) = Prenex.atom (.apply label []) := by simp [canonP, isUnit]
          refine canonFacts_of_atom fresh restrictFresh isAtom (by simp [decompose, isUnit]) ?_
          rw [recanon_apply, List.map_nil]
      · by_cases isLambda : ∃ binder body, argument = .lambda binder body
        · obtain ⟨binder, body, rfl⟩ := isLambda
          have lambdaObject : isObjectPattern (.lambda binder body) = true := object _ List.mem_cons_self
          have bodyFacts : CanonFacts block body := (recurse _ List.mem_cons_self).2 binder body rfl
            (by simpa [isObjectPattern] using lambdaObject)
            (by simpa [restrictionsBind] using bindsBelow _ List.mem_cons_self)
          by_cases isRestrict : label = block.restrict
          · -- a restriction closes its body's canonical block
            subst isRestrict
            exact canonFacts_of_normal fresh restrictFresh (canonP_restrict binder body) (close_atomic bodyFacts.atomic)
          · -- any other binder is one component, the abstraction's body canonical
            set inner := Pattern.lambda binder (Prenex.toPattern block.toBlock (canonP block body)) with innerIs
            have innerAtomic : decompose block.toBlock inner = Prenex.atom inner := decompose_lambda binder _
            have innerRead : recanon block inner = inner :=
              recanon_lambda_fixed (canonicalOf_toPattern_fixed bodyFacts.atomic bodyFacts.used bodyFacts.fixed)
            obtain ⟨innerAtoms, innerUsed⟩ := atom_facts innerAtomic
            have innerFixed : normal block (Prenex.atom inner) = Prenex.atom inner := by
              rw [normal_atom fresh restrictFresh innerAtomic, innerRead]
            have isAtom : canonP block (.apply label [.lambda binder body]) =
                Prenex.atom (.apply label [argumentOf block label (.lambda binder body) (Prenex.atom inner)]) := by
              simp [canonP, isRestrict, innerIs]
            refine canonFacts_of_atom fresh restrictFresh isAtom
              (decompose_single isRestrict (decompose_argumentOf lambdaObject innerAtoms innerUsed)
                fun empty => by simp [Prenex.atom, Prenex.nil] at empty) ?_
            rw [recanon_apply, List.map_singleton, partOf_argumentOf innerAtoms innerUsed innerFixed lambdaObject]
        · push Not at isLambda
          have argumentFacts := facts argument List.mem_cons_self
          have argumentObject := object argument List.mem_cons_self
          have notRestrict : label ≠ block.restrict := by
            intro same
            rw [bindsAt_single isLambda, same] at bindsHere
            simp at bindsHere
          by_cases isReplicate : label = block.replicate
          · -- a replication is the block of its replicated molecules
            subst isReplicate
            exact canonFacts_of_normal fresh restrictFresh (canonP_replicate isLambda) fun component member =>
              replicated_atomic fresh restrictFresh (replicatedOf_replicated component member)
          by_cases empty : label ∈ block.emptyUnits ∧ canonP block argument = Prenex.nil
          · exact canonFacts_of_nil (canonP_empty empty.1 isReplicate isLambda empty.2)
          · -- any other constructor of one argument is one component, its argument canonical
            have isAtom : canonP block (.apply label [argument]) =
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
            refine canonFacts_of_atom fresh restrictFresh isAtom
              (decompose_single notRestrict (decompose_argumentOf argumentObject argumentFacts.atomic
                argumentFacts.used) empty) ?_
            rw [recanon_apply, List.map_singleton,
              partOf_argumentOf argumentFacts.atomic argumentFacts.used argumentFacts.fixed argumentObject]
      · -- two arguments or more: one component, its arguments canonical
        have isAtom : canonP block (.apply label (argument :: second :: rest)) =
            Prenex.atom (.apply label ((argument :: second :: rest).map fun other =>
              argumentOf block label other (canonP block other))) := by
          rw [canonP_apply (by simp) (by simp) (by simp) (by simp), canonsP_eq_map,
            zipWith_map_self _ _ _ _ fun _ _ => rfl]
        refine canonFacts_of_atom fresh restrictFresh isAtom (by simp [decompose]) ?_
        rw [recanon_apply, map_partOf_argumentOf facts object]

/-- **The canonical block of an object pattern whose restrictions bind is a canonical block**: atoms, every
restriction used, its own canonical form. -/
theorem canonFacts {pattern : Pattern} (object : isObjectPattern pattern = true)
    (binds : restrictionsBind block.toBlock pattern = true) : CanonFacts block pattern :=
  (canonFacts_and fresh restrictFresh pattern).1 object binds

end Facts

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
