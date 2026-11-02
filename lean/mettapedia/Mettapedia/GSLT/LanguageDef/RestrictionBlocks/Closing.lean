import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Substitution
import Mettapedia.GSLT.LanguageDef.WellSortedClosing
import Mettapedia.OSLF.MeTTaIL.ContextClosing

/-!
# The static theory of restriction blocks is closed under binding a free name

Over any calculus with restriction: a chain of laws through processes, from an object, is carried by closing a free
name of a base sort into a new innermost bound variable of that sort to a chain through processes again
(`sortedEquiv_close`). This is how a name becomes a binder's variable in a named translation. Each law keeps its
shape: closing passes a law's binders one level deeper, commutes with extrusion's lifting and is untouched by
exchange; the bag laws follow because closing acts on a bag member by member.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars closeFVar)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationContextStep EquationEquiv)
open Prenex

variable {language : LanguageDef} {block : Block}

/-! ## Closing and the operations of the laws -/

theorem isObject_closeFVar (name : String) (pattern : Pattern) :
    ∀ level, isObjectPattern (closeFVar level name pattern) = isObjectPattern pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar => intro _; simp [closeFVar]
  | hfvar other => intro _; simp only [closeFVar]; split <;> rfl
  | happly constructor arguments recurse =>
      intro level
      simp only [closeFVar, isObjectPattern, isObjectPatternList_eq_all, List.all_map]
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      exact forall₂_congr fun argument member => by rw [Function.comp_apply, recurse argument member]
  | hlambda binder body recurse => intro level; simp [closeFVar, isObjectPattern, recurse]
  | hmultiLambda arity binders body recurse => intro level; simp [closeFVar, isObjectPattern, recurse]
  | hsubst => intro _; simp [closeFVar, isObjectPattern]
  | hcollection kind elements rest recurse =>
      intro level
      simp only [closeFVar, isObjectPattern, isObjectPatternList_eq_all, List.all_map]
      congr 1
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      exact forall₂_congr fun element member => by rw [Function.comp_apply, recurse element member]

/-- Closing one level deeper commutes with lifting past one new outer variable. -/
theorem closeFVar_liftBVars (name : String) (pattern : Pattern) :
    ∀ (level cutoff : Nat), cutoff ≤ level →
      closeFVar (level + 1) name (liftBVars cutoff 1 pattern) = liftBVars cutoff 1 (closeFVar level name pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro level cutoff _
      simp only [liftBVars, closeFVar]
      split <;> simp [closeFVar]
  | hfvar other =>
      intro level cutoff below
      simp only [liftBVars, closeFVar]
      split
      · simp only [liftBVars, show level ≥ cutoff from below, if_true]
      · rfl
  | happly constructor arguments recurse =>
      intro level cutoff below
      simp only [liftBVars, closeFVar, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => recurse argument member level cutoff below
  | hlambda binder body recurse =>
      intro level cutoff below
      simp only [liftBVars, closeFVar]
      congr 1
      exact recurse (level + 1) (cutoff + 1) (by omega)
  | hmultiLambda arity binders body recurse =>
      intro level cutoff below
      simp only [liftBVars, closeFVar]
      congr 1
      rw [show level + 1 + arity = level + arity + 1 by omega]
      exact recurse (level + arity) (cutoff + arity) (by omega)
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro level cutoff below
      simp only [liftBVars, closeFVar]
      congr 1
      · exact bodyRecurse (level + 1) (cutoff + 1) (by omega)
      · exact replacementRecurse level cutoff below
  | hcollection kind elements rest recurse =>
      intro level cutoff below
      simp only [liftBVars, closeFVar, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member level cutoff below

/-- A renaming fixing the closed level commutes with closing. -/
theorem rename_closeFVar (name : String) (pattern : Pattern) :
    ∀ (level : Nat) (relabel : Nat → Nat), relabel level = level →
      rename relabel (closeFVar level name pattern) = closeFVar level name (rename relabel pattern) := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro level relabel _; simp [closeFVar, rename_bvar]
  | hfvar other =>
      intro level relabel fixed
      simp only [closeFVar, rename_fvar]
      split
      · rw [rename_bvar, fixed]
      · rfl
  | happly constructor arguments recurse =>
      intro level relabel fixed
      simp only [closeFVar, rename_apply, List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => recurse argument member level relabel fixed
  | hlambda binder body recurse =>
      intro level relabel fixed
      simp only [closeFVar, rename_lambda]
      congr 1
      exact recurse (level + 1) (liftIndex 1 relabel) (by simp [liftIndex, fixed])
  | hmultiLambda arity binders body recurse =>
      intro level relabel fixed
      simp only [closeFVar, rename_multiLambda]
      congr 1
      exact recurse (level + arity) (liftIndex arity relabel) (by simp [liftIndex, fixed])
  | hsubst body replacement bodyRecurse replacementRecurse =>
      intro level relabel fixed
      simp only [closeFVar, rename_subst]
      congr 1
      · exact bodyRecurse (level + 1) (liftIndex 1 relabel) (by simp [liftIndex, fixed])
      · exact replacementRecurse level relabel fixed
  | hcollection kind elements rest recurse =>
      intro level relabel fixed
      simp only [closeFVar, rename_collection, List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member level relabel fixed

variable [laws : BlockLanguage language block]

omit laws in
theorem close_restriction (name : String) (level : Nat) (binder : Option String) (body : Pattern) :
    closeFVar level name (.apply block.restrict [.lambda binder body]) =
      .apply block.restrict [.lambda binder (closeFVar (level + 1) name body)] := by
  simp [closeFVar]

omit laws in
theorem close_inaction (name : String) (level : Nat) :
    closeFVar level name (.apply block.unit []) = .apply block.unit [] := by
  simp [closeFVar]

omit laws in
theorem close_bag (name : String) (level : Nat) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    closeFVar level name (.collection kind elements rest) = .collection kind (elements.map (closeFVar level name)) rest :=
  by simp [closeFVar]

omit laws in
theorem close_structural (name : String) (level : Nat) : Structural block (closeFVar level name) :=
  ⟨close_bag name level, close_inaction name level⟩

omit laws in
/-- Closing keeps applications applications. -/
theorem close_applies (name : String) (level : Nat) (constructor : String) (arguments : List Pattern) :
    ∃ arguments', closeFVar level name (.apply constructor arguments) = .apply constructor arguments' :=
  ⟨arguments.map (closeFVar level name), by simp [closeFVar]⟩

omit laws in
theorem close_emptyMultiset (name : String) (level : Nat) (label : String) :
    closeFVar level name (.apply label [.collection .hashBag [] none]) = .apply label [.collection .hashBag [] none] := by
  simp [closeFVar]

/-- **Closing keeps the shape of a law**, once the closed source has the process sort. -/
theorem generator_close (name : String) (level : Nat) {free : FreeTypeContext} {bound : List TypeExpr}
    {source target : Pattern} (generator : BlockGenerator language block source target)
    (typed : HasType language free bound (closeFVar level name source) (.base block.proc)) :
    BlockGenerator language block (closeFVar level name source) (closeFVar level name target) := by
  cases generator with
  | nil binder =>
      rw [close_restriction, close_inaction, close_inaction]
      exact .nil binder
  | nilReverse =>
      rw [close_restriction, close_inaction, close_inaction]
      exact .nilReverse
  | extrusion members selected binder body inside chosen =>
      rw [close_bag, close_restriction, close_bag, List.map_cons, List.map_map]
      have inside' : selected < (members.map (closeFVar level name)).length := by simpa using inside
      have chosen' : (members.map (closeFVar level name))[selected] =
          .apply block.restrict [.lambda binder (closeFVar (level + 1) name body)] := by
        rw [List.getElem_map]
        simp only [chosen, close_restriction]
      have shape := BlockGenerator.extrusion (language := language) _ selected binder _ inside' chosen'
      rw [map_eraseIdx, List.map_map] at shape
      have commute : closeFVar (level + 1) name ∘ liftBVars 0 1 = liftBVars 0 1 ∘ closeFVar level name :=
        funext fun pattern => closeFVar_liftBVars name pattern level 0 (Nat.zero_le _)
      rw [commute]
      exact shape
  | extrusionReverse binder members selected originals inside othersEq =>
      rw [close_restriction, close_bag, close_bag, List.map_cons, close_restriction]
      have inside' : selected < (members.map (closeFVar (level + 1) name)).length := by simpa using inside
      have othersEq' : (members.map (closeFVar (level + 1) name)).eraseIdx selected =
          (originals.map (closeFVar level name)).map (liftBVars 0 1) := by
        rw [map_eraseIdx, othersEq, List.map_map, List.map_map]
        exact List.map_congr_left fun original _ => closeFVar_liftBVars name original level 0 (Nat.zero_le _)
      have shape := BlockGenerator.extrusionReverse (language := language) (block := block) binder _ selected _ inside' othersEq'
      simpa only [List.getElem_map] using shape
  | exchange outerBinder innerBinder body =>
      rw [close_restriction, close_restriction, close_restriction, close_restriction,
        ← rename_closeFVar name body (level + 1 + 1) swapInner (by simp [swapInner])]
      exact .exchange outerBinder innerBinder _
  | emptyUnit label listed =>
      rw [close_emptyMultiset, close_restriction, close_inaction]
      exact .emptyUnit label listed
  | emptyUnitReverse label listed binder =>
      rw [close_emptyMultiset, close_restriction, close_inaction]
      exact .emptyUnitReverse label listed binder
  | derived derivedInstance =>
      exact .derived (derived_map (close_structural name level) derivedInstance (.inl typed)).1

/-- **The closed source of a generator is a process**, if it has a sort at all. -/
theorem close_source_sort (name : String) (level : Nat) {source target : Pattern}
    (generator : BlockGenerator language block source target) {free : FreeTypeContext} {bound : List TypeExpr}
    {sort : String} (typed : HasType language free bound (closeFVar level name source) (.base sort)) :
    sort = block.proc := by
  cases generator with
  | nil binder =>
      rw [close_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | nilReverse =>
      rw [close_inaction] at typed
      obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      exact typeIs.trans (laws.unitShape rule member labelIs.symm)
  | extrusion =>
      rw [close_bag] at typed
      exact (laws.bag_members typed).2.1
  | extrusionReverse =>
      rw [close_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | exchange =>
      rw [close_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | emptyUnit label listed =>
      rw [close_emptyMultiset] at typed
      obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      exact typeIs.trans ((laws.emptyUnitShape label listed).2 rule member labelIs.symm)
  | emptyUnitReverse label listed binder =>
      rw [close_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | derived derivedInstance =>
      cases derivedInstance <;> rw [close_bag] at typed <;> exact (laws.bag_members typed).2.1

omit laws in
theorem close_source_notLambda (name : String) (level : Nat) {source target : Pattern}
    (generator : BlockGenerator language block source target) :
    ∀ binder body, closeFVar level name source ≠ .lambda binder body := by
  intro binder body equal
  rcases generator_source_head generator with ⟨constructor, arguments, rfl⟩ | ⟨kind, elements, rest, rfl⟩ <;>
    simp [closeFVar] at equal

theorem BaseContext.snoc {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (sort : String) : BaseContext free (bound ++ [.base sort]) :=
  ⟨context.free, by
    intro type member
    rcases List.mem_append.mp member with inside | last
    · exact context.bound type inside
    · exact ⟨sort, by simpa using last⟩⟩

/-- **The static theory between processes is closed under binding a free name**: a chain through processes from an
object is carried by closing a free name of a base sort into a new innermost variable of that sort to a chain through
processes. -/
theorem sortedEquiv_close {free : FreeTypeContext} {bound : List TypeExpr} (baseContext : BaseContext free bound)
    {name sort : String} (lookup : free name = some (.base sort)) {first second : Pattern}
    (equivalent : ProcEquiv language block free bound first second) :
    isObjectPattern first = true →
      ProcEquiv language block free (bound ++ [.base sort]) (closeFVar bound.length name first)
        (closeFVar bound.length name second) := by
  induction equivalent with
  | rel source target step =>
      intro sourceObject
      have targetObject : isObjectPattern target = true := by
        rw [← step_isObject (block := block) step.step]; exact sourceObject
      have firstTyped := step.firstTyped.closeFVar name (.base sort) lookup
      have secondTyped := step.secondTyped.closeFVar name (.base sort) lookup
      have firstObject : isObjectPattern (closeFVar bound.length name source) = true := by
        rw [isObject_closeFVar]; exact sourceObject
      have secondObject : isObjectPattern (closeFVar bound.length name target) = true := by
        rw [isObject_closeFVar]; exact targetObject
      have stepped := step.step
      cases stepped with
      | @inContext context redex contractum generator =>
          have shape := generator_shape (block := block) generator
          rw [OneHoleContext.closeFVar_fill] at firstTyped firstObject secondTyped secondObject
          rw [OneHoleContext.closeFVar_fill, OneHoleContext.closeFVar_fill]
          obtain ⟨holeBound, holeType, holeContext, holeKind, redexTyped, contractumTyped, rebuild⟩ :=
            fill_typed_pair (block := block) _ (baseContext.snoc sort) firstTyped secondTyped
              (.inl ⟨block.proc, rfl⟩) firstObject secondObject (close_source_notLambda _ _ shape)
          rcases holeKind with ⟨holeSort, rfl⟩ | multiset
          · obtain rfl := close_source_sort _ _ shape redexTyped
            have closed := generator_close _ _ shape redexTyped
            have redexObject := isObject_of_fill _ firstObject
            have canonical := (metadata_of_typed (block := block) _ redexTyped redexObject).1 ⟨block.proc, rfl⟩
            exact SortedEquiv.fill _ rebuild (generator_equiv closed canonical redexTyped)
          · have derived := generator_at_multiset (close_structural name _) (close_applies name _) holeContext shape
              multiset redexTyped contractumTyped (isObject_of_fill _ secondObject)
            exact SortedEquiv.fill _ rebuild (SortedEquiv.ofDerived derived redexTyped contractumTyped)
  | refl => intro _; exact .refl _
  | symm first second chain recurse =>
      intro object
      exact .symm _ _ (recurse (by
        rw [equationEquiv_isObject (block := block) (SortedEquiv.toEquationEquiv chain)]; exact object))
  | trans first middle third left _ leftRecurse rightRecurse =>
      intro object
      exact .trans _ _ _ (leftRecurse object)
        (rightRecurse (by rw [← equationEquiv_isObject (block := block) (SortedEquiv.toEquationEquiv left)]; exact object))

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
