import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Reactions

/-!
# The block of a substituted process

A substitution whose images are atoms of a calculus's blocks — each image its own block, none an abstraction
(`AtomicImages`) — keeps the outermost shape of every process it substitutes into: a variable becomes its image, an
atom, and inaction, a restriction, a bag and a multiset whose empty instance is the unit stay what they are. So the
block of a substituted process is the block of the process with its components substituted past its restrictions
(`decompose_substitute`): substituting commutes with putting blocks side by side (`par_substituteOuter`) and with
closing a restriction (`close_substituteOuter`), which a substitution of the outside does not reach. Reading a block
back commutes with substitution too (`toPattern_substituteOuter`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift lift_zero lift_lift substitute_comp
  substituteList_eq_map substitute_liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (FreeIn freeIn_bvar freeIn_apply freeIn_lambda freeIn_multiLambda
  freeIn_subst freeIn_collection)

variable {block : Block}

/-! ## Variables of a substitution -/

/-- A variable of an image, past the binders the assignment is lifted under. -/
theorem freeIn_lift_of {assignment : Assignment} {arity original index : Nat}
    (image : FreeIn index (assignment original)) :
    FreeIn (index + arity) (lift arity assignment (original + arity)) := by
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  rw [if_neg (by omega), Nat.add_sub_cancel]
  exact freeIn_liftBVars.mpr image

/-- **A variable of an image is a variable of the substitution** wherever the substituted variable occurs. -/
theorem freeIn_substitute_of (pattern : Pattern) : ∀ {assignment : Assignment} {original index : Nat},
    FreeIn original pattern → FreeIn index (assignment original) → FreeIn index (substitute assignment pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar other =>
      intro assignment original index free image
      rw [freeIn_bvar] at free
      subst free
      exact image
  | hfvar => intro _ _ _ free; cases free
  | happly label arguments recurse =>
      intro assignment original index free image
      obtain ⟨argument, member, free⟩ := freeIn_apply.mp free
      simp only [substitute, substituteList_eq_map]
      exact freeIn_apply.mpr ⟨_, List.mem_map.mpr ⟨argument, member, rfl⟩, recurse argument member free image⟩
  | hlambda binder body recurse =>
      intro assignment original index free image
      simp only [substitute]
      exact freeIn_lambda.mpr (recurse (freeIn_lambda.mp free) (freeIn_lift_of image))
  | hmultiLambda arity binders body recurse =>
      intro assignment original index free image
      simp only [substitute]
      exact freeIn_multiLambda.mpr (recurse (freeIn_multiLambda.mp free) (freeIn_lift_of image))
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro assignment original index free image
      simp only [substitute]
      rcases freeIn_subst.mp free with free | free
      · exact freeIn_subst.mpr (.inl (bodyRecurse free (freeIn_lift_of image)))
      · exact freeIn_subst.mpr (.inr (replacementRecurse free image))
  | hcollection kind elements rest recurse =>
      intro assignment original index free image
      obtain ⟨element, member, free⟩ := freeIn_collection.mp free
      simp only [substitute, substituteList_eq_map]
      exact freeIn_collection.mpr ⟨_, List.mem_map.mpr ⟨element, member, rfl⟩, recurse element member free image⟩

/-- No variable below a lift is free in a lifted pattern. -/
theorem not_freeIn_liftBVars_below {index arity : Nat} {pattern : Pattern} (below : index < arity) :
    ¬ FreeIn index (liftBVars 0 arity pattern) := by
  rw [liftBVars_eq_rename, freeIn_rename]
  rintro ⟨original, -, equal⟩
  simp only [shiftAbove] at equal
  split_ifs at equal <;> omega

/-- **The variable just past a block's restrictions is free in a substituted component exactly when it is free in the
component**: a substitution of the outside, lifted past it, never produces it. -/
theorem freeIn_substitute_lift_iff {count : Nat} {assignment : Assignment} (pattern : Pattern) :
    FreeIn count (substitute (lift (count + 1) assignment) pattern) ↔ FreeIn count pattern := by
  constructor
  · intro free
    obtain ⟨original, originalFree, image⟩ := freeIn_substitute pattern free
    unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift at image
    split_ifs at image with below
    · rw [freeIn_bvar] at image
      rwa [image]
    · exact absurd image (not_freeIn_liftBVars_below (Nat.lt_succ_self count))
  · intro free
    refine freeIn_substitute_of pattern free ?_
    unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
    rw [if_pos (Nat.lt_succ_self count)]
    exact .bvar count

/-! ## Substitutions agreeing on the free variables -/

theorem lift_congr_free {first second : Assignment} {arity index : Nat}
    (agree : arity ≤ index → first (index - arity) = second (index - arity)) :
    lift arity first index = lift arity second index := by
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  by_cases inside : index < arity
  · simp [inside]
  · simp only [inside, if_false]
    rw [agree (by omega)]

/-- **Substitutions agreeing on the free variables of a pattern substitute it alike.** -/
theorem substitute_congr_free (pattern : Pattern) : ∀ {first second : Assignment},
    (∀ index, FreeIn index pattern → first index = second index) →
      substitute first pattern = substitute second pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro first second agree; exact agree index (.bvar index)
  | hfvar => intros; rfl
  | happly constructor arguments recurse =>
      intro first second agree
      simp only [substitute, substituteList_eq_map]
      congr 1
      exact List.map_congr_left fun argument member =>
        recurse argument member fun index free => agree index (.apply member free)
  | hlambda binder body recurse =>
      intro first second agree
      simp only [substitute]
      congr 1
      exact recurse fun index free => lift_congr_free fun outside =>
        agree _ (.lambda (by rwa [Nat.sub_add_cancel outside]))
  | hmultiLambda arity binders body recurse =>
      intro first second agree
      simp only [substitute]
      congr 1
      exact recurse fun index free => lift_congr_free fun outside =>
        agree _ (.multiLambda (by rwa [Nat.sub_add_cancel outside]))
  | hsubst body replacement recurseBody recurseReplacement =>
      intro first second agree
      simp only [substitute]
      congr 1
      · exact recurseBody fun index free => lift_congr_free fun outside =>
          agree _ (.substBody (by rwa [Nat.sub_add_cancel outside]))
      · exact recurseReplacement fun index free => agree index (.substReplacement free)
  | hcollection kind elements rest recurse =>
      intro first second agree
      simp only [substitute, substituteList_eq_map]
      congr 1
      exact List.map_congr_left fun element member =>
        recurse element member fun index free => agree index (.element member free)

/-! ## Renaming and substitution -/

theorem rename_substitute (relabel : Nat → Nat) (assignment : Assignment) (pattern : Pattern) :
    rename relabel (substitute assignment pattern) =
      substitute (fun index => rename relabel (assignment index)) pattern := by
  unfold rename
  rw [substitute_comp]

theorem substitute_rename (assignment : Assignment) (relabel : Nat → Nat) (pattern : Pattern) :
    substitute assignment (rename relabel pattern) = substitute (fun index => assignment (relabel index)) pattern := by
  unfold rename
  rw [substitute_comp]
  rfl

/-- Dropping the variable just past a lift of one more than the dropped place is the lift without it. -/
theorem rename_dropIndex_liftBVars (count : Nat) (pattern : Pattern) :
    rename (dropIndex count) (liftBVars 0 (count + 1) pattern) = liftBVars 0 count pattern := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, dropIndex]
  split_ifs <;> omega

/-! ## Blocks under substitution -/

namespace Prenex

/-- **Substitute the variables a block reads from outside**, past its restrictions. -/
def substituteOuter (assignment : Assignment) (form : Prenex) : Prenex :=
  ⟨form.count, form.components.map (substitute (lift form.count assignment))⟩

end Prenex

theorem nil_substituteOuter (assignment : Assignment) : Prenex.nil.substituteOuter assignment = Prenex.nil := rfl

theorem atom_substituteOuter (assignment : Assignment) (component : Pattern) :
    (Prenex.atom component).substituteOuter assignment = Prenex.atom (substitute assignment component) := by
  simp [Prenex.substituteOuter, Prenex.atom, lift_zero]

theorem substituteOuter_eq_nil {assignment : Assignment} {form : Prenex}
    (isNil : form.substituteOuter assignment = Prenex.nil) : form = Prenex.nil := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.substituteOuter, Prenex.nil, Prenex.mk.injEq, List.map_eq_nil_iff] at isNil
  obtain ⟨rfl, rfl⟩ := isNil
  rfl

/-- **Substitution commutes with putting blocks side by side.** -/
theorem par_substituteOuter (assignment : Assignment) (first second : Prenex) :
    (first.par second).substituteOuter assignment =
      (first.substituteOuter assignment).par (second.substituteOuter assignment) := by
  obtain ⟨outer, firstComponents⟩ := first
  obtain ⟨inner, secondComponents⟩ := second
  simp only [Prenex.par, Prenex.substituteOuter, List.map_append, List.map_map, Prenex.mk.injEq, true_and]
  congr 1
  · refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp]
    have shifted := substitute_liftBVars (lift outer assignment) component 0 inner
    rw [Nat.zero_add, lift_lift, lift_zero] at shifted
    exact shifted
  · refine List.map_congr_left fun component _ => ?_
    simp only [Function.comp]
    have shifted := substitute_liftBVars assignment component inner outer
    rw [Nat.add_comm inner outer] at shifted
    exact shifted

/-- Past one more restriction, a lifted assignment dropping that restriction is the assignment dropping it after. -/
theorem rename_dropIndex_lift (assignment : Assignment) {count index : Nat} (different : index ≠ count) :
    rename (dropIndex count) (lift (count + 1) assignment index) = lift count assignment (dropIndex count index) := by
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  by_cases below : index < count
  · rw [if_pos (by omega), rename_bvar, dropIndex, if_pos below, if_pos below]
  · rw [if_neg (by omega), rename_dropIndex_liftBVars, dropIndex, if_neg below, if_neg (by omega),
      show index - 1 - count = index - (count + 1) by omega]

/-- **Substitution commutes with closing a restriction**: the restriction is the variable just past the block's own,
which a substitution of the outside does not reach. -/
theorem close_substituteOuter (assignment : Assignment) (form : Prenex) :
    (form.substituteOuter (lift 1 assignment)).close = form.close.substituteOuter assignment := by
  obtain ⟨count, components⟩ := form
  have lifted : lift count (lift 1 assignment) = lift (count + 1) assignment := by
    rw [lift_lift, Nat.add_comm]
  have mentionsSame : ∀ component, mentions count (substitute (lift (count + 1) assignment) component) =
      mentions count component := fun component =>
    Bool.eq_iff_iff.mpr (by rw [mentions_iff, mentions_iff]; exact freeIn_substitute_lift_iff component)
  simp only [Prenex.substituteOuter, Prenex.close, lifted, List.any_map, Function.comp_def, mentionsSame]
  split_ifs with used
  · rfl
  · simp only [Prenex.mk.injEq, true_and, List.map_map]
    refine List.map_congr_left fun component member => ?_
    have unused : ¬ FreeIn count component := fun free =>
      used (List.any_eq_true.mpr ⟨component, member, (mentions_iff component count).mpr free⟩)
    simp only [Function.comp, rename_substitute, substitute_rename]
    exact substitute_congr_free component fun index free =>
      rename_dropIndex_lift assignment fun same => unused (same ▸ free)

/-! ## Substitution keeps the outermost shape -/

/-- **A substitution's images are atoms of a calculus's blocks**: each image is its own block, and none is an
abstraction. Variables and the terms of a sort other than the processes' are. -/
def AtomicImages (block : Block) (assignment : Assignment) : Prop :=
  ∀ index, decompose block (assignment index) = Prenex.atom (assignment index) ∧
    ∀ binder body, assignment index ≠ .lambda binder body

theorem decompose_bvar_atom (index : Nat) : decompose block (.bvar index) = Prenex.atom (.bvar index) :=
  decompose_atom (by simp) (fun _ _ equal => by cases equal) (fun _ equal => by cases equal)
    (fun _ _ equal => by cases equal)

/-- Images that are atoms stay atoms past binders. -/
theorem atomicImages_lift {assignment : Assignment} (atomic : AtomicImages block assignment) (arity : Nat) :
    AtomicImages block (lift arity assignment) := by
  intro index
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split_ifs
  · exact ⟨decompose_bvar_atom index, fun _ _ equal => by cases equal⟩
  · obtain ⟨image, notLambda⟩ := atomic (index - arity)
    refine ⟨?_, fun binder body equal => ?_⟩
    · rw [liftBVars_eq_rename, decompose_renameOuter, image, atom_renameOuter]
    · cases imageIs : assignment (index - arity) with
      | lambda binder' body' => exact notLambda binder' body' imageIs
      | _ => rw [imageIs] at equal; simp [liftBVars] at equal

theorem substitute_eq_lambda {assignment : Assignment}
    (notLambda : ∀ index binder body, assignment index ≠ .lambda binder body) {pattern : Pattern}
    {binder : Option String} {body : Pattern} (equal : substitute assignment pattern = .lambda binder body) :
    ∃ binder' original, pattern = .lambda binder' original := by
  cases pattern with
  | bvar index => exact absurd equal (notLambda index binder body)
  | lambda binder' original => exact ⟨binder', original, rfl⟩
  | _ => simp [substitute] at equal

/-- **Substitution keeps an atom that is no variable an atom**, when no image is an abstraction. -/
theorem substitute_keeps_atom {assignment : Assignment}
    (notLambda : ∀ index binder body, assignment index ≠ .lambda binder body) {pattern : Pattern}
    (notVariable : ∀ index, pattern ≠ .bvar index) (notNil : pattern ≠ .apply block.unit [])
    (notRestriction : ∀ binder body, pattern ≠ .apply block.restrict [.lambda binder body])
    (notBag : ∀ elements, pattern ≠ .collection .hashBag elements none)
    (notEmpty : ∀ label argument, pattern = .apply label [argument] → label ∉ block.emptyUnits) :
    substitute assignment pattern ≠ .apply block.unit [] ∧
      (∀ binder body, substitute assignment pattern ≠ .apply block.restrict [.lambda binder body]) ∧
      (∀ elements, substitute assignment pattern ≠ .collection .hashBag elements none) ∧
      (∀ label argument, substitute assignment pattern = .apply label [argument] → label ∉ block.emptyUnits) := by
  cases pattern with
  | bvar index => exact absurd rfl (notVariable index)
  | fvar name => simp [substitute]
  | apply label arguments =>
      simp only [substitute, substituteList_eq_map]
      refine ⟨fun equal => ?_, fun binder body equal => ?_, fun elements equal => (by cases equal),
        fun label' argument equal => ?_⟩
      · simp only [Pattern.apply.injEq, List.map_eq_nil_iff] at equal
        exact notNil (by rw [equal.1, equal.2])
      · simp only [Pattern.apply.injEq, List.map_eq_singleton_iff] at equal
        obtain ⟨rfl, argument, rfl, isLambda⟩ := equal
        obtain ⟨binder', body', rfl⟩ := substitute_eq_lambda notLambda isLambda
        exact notRestriction binder' body' rfl
      · simp only [Pattern.apply.injEq, List.map_eq_singleton_iff] at equal
        obtain ⟨rfl, original, rfl, -⟩ := equal
        exact notEmpty _ original rfl
  | lambda binder body => simp [substitute]
  | multiLambda arity binders body => simp [substitute]
  | subst body replacement => simp [substitute]
  | collection kind elements rest =>
      simp only [substitute, substituteList_eq_map]
      refine ⟨by simp, by simp, fun elements' equal => ?_, by simp⟩
      simp only [Pattern.collection.injEq] at equal
      obtain ⟨rfl, -, rfl⟩ := equal
      exact notBag elements rfl

mutual
  /-- **The block of a substituted process** is the block of the process, its components substituted past its
  restrictions, when the substitution's images are atoms. -/
  theorem decompose_substitute {assignment : Assignment} (atomic : AtomicImages block assignment)
      (pattern : Pattern) :
      decompose block (substitute assignment pattern) = (decompose block pattern).substituteOuter assignment := by
    by_cases isBVar : ∃ index, pattern = .bvar index
    · obtain ⟨index, rfl⟩ := isBVar
      rw [decompose_bvar_atom, atom_substituteOuter]
      exact (atomic index).1
    by_cases isNil : pattern = .apply block.unit []
    · subst isNil
      have substituted : substitute assignment (.apply block.unit []) = .apply block.unit [] := by
        simp only [substitute, substituteList_eq_map, List.map_nil]
      rw [substituted, decompose_unit, nil_substituteOuter]
    by_cases isRestriction : ∃ binder body, pattern = .apply block.restrict [.lambda binder body]
    · obtain ⟨binder, body, rfl⟩ := isRestriction
      have substituted : substitute assignment (.apply block.restrict [.lambda binder body]) =
          .apply block.restrict [.lambda binder (substitute (lift 1 assignment) body)] := by
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
      rw [substituted, decompose_restrict, decompose_restrict,
        decompose_substitute (atomicImages_lift atomic 1) body, close_substituteOuter]
    by_cases isBag : ∃ elements, pattern = .collection .hashBag elements none
    · obtain ⟨elements, rfl⟩ := isBag
      have substituted : substitute assignment (.collection .hashBag elements none) =
          .collection .hashBag (elements.map (substitute assignment)) none := by
        simp only [substitute, substituteList_eq_map]
      rw [substituted, decompose_bag, decompose_bag]
      exact decomposeList_substitute atomic elements
    by_cases isEmptyCandidate : ∃ label argument, pattern = .apply label [argument] ∧ label ∈ block.emptyUnits
    · obtain ⟨label, argument, rfl, listed⟩ := isEmptyCandidate
      have substituted : substitute assignment (.apply label [argument]) =
          .apply label [substitute assignment argument] := by
        simp only [substitute, substituteList_eq_map, List.map_cons, List.map_nil]
      have notRestriction := fun binder body equal => isRestriction ⟨binder, body, equal⟩
      have substitutedNotRestriction : ∀ binder body,
          Pattern.apply label [substitute assignment argument] ≠ .apply block.restrict [.lambda binder body] := by
        intro binder body equal
        simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at equal
        obtain ⟨rfl, isLambda⟩ := equal
        obtain ⟨binder', body', rfl⟩ := substitute_eq_lambda (fun index => (atomic index).2) isLambda
        exact isRestriction ⟨binder', body', rfl⟩
      rw [substituted, decompose_multiset notRestriction, decompose_multiset substitutedNotRestriction,
        decompose_substitute atomic argument]
      by_cases empty : decompose block argument = Prenex.nil
      · rw [if_pos ⟨listed, by rw [empty, nil_substituteOuter]⟩, if_pos ⟨listed, empty⟩, nil_substituteOuter]
      · have notEmpty : ¬ (label ∈ block.emptyUnits ∧
            (decompose block argument).substituteOuter assignment = Prenex.nil) := by
          rintro ⟨-, substitutedNil⟩
          exact empty (substituteOuter_eq_nil substitutedNil)
        rw [if_neg notEmpty, if_neg (fun both => empty both.2), atom_substituteOuter, substituted]
    obtain ⟨notNil', notRestriction', notBag', notEmpty'⟩ := substitute_keeps_atom (assignment := assignment)
      (fun index => (atomic index).2) (fun index equal => isBVar ⟨index, equal⟩) isNil
      (fun binder body equal => isRestriction ⟨binder, body, equal⟩) (fun elements equal => isBag ⟨elements, equal⟩)
      (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩)
    rw [decompose_atom isNil (fun binder body equal => isRestriction ⟨binder, body, equal⟩)
        (fun elements equal => isBag ⟨elements, equal⟩)
        (fun label argument equal listed => isEmptyCandidate ⟨label, argument, equal, listed⟩),
      decompose_atom notNil' notRestriction' notBag' notEmpty', atom_substituteOuter]
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem decomposeList_substitute {assignment : Assignment} (atomic : AtomicImages block assignment)
      (elements : List Pattern) :
      decomposeList block (elements.map (substitute assignment)) =
        (decomposeList block elements).substituteOuter assignment := by
    match elements with
    | [] => rfl
    | element :: elements =>
        simp only [List.map_cons, decomposeList]
        rw [decompose_substitute atomic element, decomposeList_substitute atomic elements, par_substituteOuter]
  termination_by sizeOf elements
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Reading a block back under substitution -/

theorem substitute_restricts (block : Block) : ∀ (count : Nat) (assignment : Assignment) (process : Pattern),
    substitute assignment (Prenex.restricts block count process) =
      Prenex.restricts block count (substitute (lift count assignment) process)
  | 0, assignment, process => by simp [Prenex.restricts, lift_zero]
  | count + 1, assignment, process => by
      simp only [Prenex.restricts, substitute, substituteList_eq_map, List.map_cons, List.map_nil]
      rw [substitute_restricts block count (lift 1 assignment) process, lift_lift, Nat.add_comm 1 count]

theorem substitute_body (block : Block) (assignment : Assignment) (components : List Pattern) :
    substitute assignment (Prenex.body block components) =
      Prenex.body block (components.map (substitute assignment)) := by
  match components with
  | [] => simp [Prenex.body, substitute]
  | [component] => simp [Prenex.body]
  | first :: second :: rest => simp [Prenex.body, substitute, substituteList_eq_map]

/-- **Reading a block back commutes with substituting what it reads from outside.** -/
theorem toPattern_substituteOuter (block : Block) (assignment : Assignment) (form : Prenex) :
    Prenex.toPattern block (form.substituteOuter assignment) = substitute assignment (Prenex.toPattern block form) := by
  obtain ⟨count, components⟩ := form
  simp only [Prenex.toPattern, Prenex.substituteOuter]
  rw [substitute_restricts, substitute_body]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
