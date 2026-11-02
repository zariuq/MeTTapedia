import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Generators

/-!
# The static theory of restriction blocks is closed under substitution

Over any calculus with restriction: a chain of laws through processes, from an object, is carried by a substitution
of terms of the variables' sorts to a chain through processes again (`sortedEquiv_substitute`). Each law keeps its
shape: the substitution passes the binders of a law with the assignment lifted, extrusion's lifted members commute
with it, and the exchanged body's two inner names are untouched by it. The bag laws follow because the substitution
acts on a bag member by member. So a received datum keeps equivalent continuations equivalent
(`sortedEquiv_instantiate`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift lift_zero lift_lift substitute_comp
  substitute_liftBVars substituteList_eq_map)
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationContextStep EquationEquiv)
open Prenex

variable {language : LanguageDef} {block : Block}


/-! ## Substitution through a context -/

namespace ContextSubstitution

/-- Substitute into a context, passing each binder with the assignment lifted. -/
def transport : Assignment → OneHoleContext → OneHoleContext
  | _, .hole => .hole
  | assignment, .apply constructor before inner after =>
      .apply constructor (before.map (substitute assignment)) (transport assignment inner)
        (after.map (substitute assignment))
  | assignment, .lambda binder inner => .lambda binder (transport (lift 1 assignment) inner)
  | assignment, .multiLambda arity binders inner => .multiLambda arity binders (transport (lift arity assignment) inner)
  | assignment, .substBody inner replacement =>
      .substBody (transport (lift 1 assignment) inner) (substitute assignment replacement)
  | assignment, .substReplacement body inner =>
      .substReplacement (substitute (lift 1 assignment) body) (transport assignment inner)
  | assignment, .collection kind before inner after rest =>
      .collection kind (before.map (substitute assignment)) (transport assignment inner)
        (after.map (substitute assignment)) rest

/-- The assignment that reaches the hole. -/
def atHole : Assignment → OneHoleContext → Assignment
  | assignment, .hole => assignment
  | assignment, .apply _ _ inner _ => atHole assignment inner
  | assignment, .lambda _ inner => atHole (lift 1 assignment) inner
  | assignment, .multiLambda arity _ inner => atHole (lift arity assignment) inner
  | assignment, .substBody inner _ => atHole (lift 1 assignment) inner
  | assignment, .substReplacement _ inner => atHole assignment inner
  | assignment, .collection _ _ inner _ _ => atHole assignment inner

/-- **Substituting into a filled context** substitutes into the context and into the filling, the filling with the
assignment lifted past the context's binders. -/
theorem substitute_fill : ∀ (assignment : Assignment) (context : OneHoleContext) (filling : Pattern),
    substitute assignment (context.fill filling) =
      (transport assignment context).fill (substitute (atHole assignment context) filling)
  | _, .hole, _ => rfl
  | assignment, .apply _ _ inner _, filling => by
      simp only [OneHoleContext.fill, transport, atHole, substitute, substituteList_eq_map, List.map_append,
        List.map_cons, substitute_fill assignment inner filling]
  | assignment, .lambda _ inner, filling => by
      simp only [OneHoleContext.fill, transport, atHole, substitute, substitute_fill _ inner filling]
  | assignment, .multiLambda _ _ inner, filling => by
      simp only [OneHoleContext.fill, transport, atHole, substitute, substitute_fill _ inner filling]
  | assignment, .substBody inner _, filling => by
      simp only [OneHoleContext.fill, transport, atHole, substitute, substitute_fill _ inner filling]
  | assignment, .substReplacement _ inner, filling => by
      simp only [OneHoleContext.fill, transport, atHole, substitute, substitute_fill assignment inner filling]
  | assignment, .collection _ _ inner _ _, filling => by
      simp only [OneHoleContext.fill, transport, atHole, substitute, substituteList_eq_map, List.map_append,
        List.map_cons, substitute_fill assignment inner filling]

end ContextSubstitution

/-! ## Object patterns -/

theorem isObject_liftBVars (pattern : Pattern) (cutoff shift : Nat) :
    isObjectPattern (liftBVars cutoff shift pattern) = isObjectPattern pattern := by
  rw [liftBVars_eq_rename, isObjectPattern_rename]

/-- An assignment of object patterns. -/
def ObjectAssignment (assignment : Assignment) : Prop := ∀ index, isObjectPattern (assignment index) = true

theorem ObjectAssignment.lift {assignment : Assignment} (objects : ObjectAssignment assignment) (arity : Nat) :
    ObjectAssignment (lift arity assignment) := by
  intro index
  unfold Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift
  split
  · rfl
  · rw [isObject_liftBVars]
    exact objects _

theorem isObject_substitute (pattern : Pattern) : ∀ {assignment : Assignment}, ObjectAssignment assignment →
    isObjectPattern pattern = true → isObjectPattern (substitute assignment pattern) = true := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro assignment objects _; exact objects index
  | hfvar => intro _ _ _; rfl
  | happly constructor arguments recurse =>
      intro assignment objects object
      simp only [substitute, substituteList_eq_map, isObjectPattern, isObjectPatternList_eq_all, List.all_map,
        List.all_eq_true, Function.comp_apply] at object ⊢
      exact fun argument member => recurse argument member objects (object argument member)
  | hlambda binder body recurse =>
      intro assignment objects object
      simp only [substitute, isObjectPattern] at object ⊢
      exact recurse (objects.lift 1) object
  | hmultiLambda arity binders body recurse =>
      intro assignment objects object
      simp only [substitute, isObjectPattern] at object ⊢
      exact recurse (objects.lift arity) object
  | hsubst => intro _ _ object; simp [isObjectPattern] at object
  | hcollection kind elements rest recurse =>
      intro assignment objects object
      simp only [substitute, substituteList_eq_map, isObjectPattern, isObjectPatternList_eq_all, List.all_map,
        List.all_eq_true, Function.comp_apply, Bool.and_eq_true] at object ⊢
      exact ⟨object.1, fun element member => recurse element member objects (object.2 element member)⟩

theorem map_eraseIdx {α β : Type} (map : α → β) : ∀ (list : List α) (index : Nat),
    (list.map map).eraseIdx index = (list.eraseIdx index).map map
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | head :: tail, index + 1 => by simp [map_eraseIdx map tail index]

/-! ## The laws keep their shape under substitution -/

section Shapes

variable [laws : BlockSignature language block]

theorem substitute_restriction (assignment : Assignment) (binder : Option String) (body : Pattern) :
    substitute assignment (.apply block.restrict [.lambda binder body]) =
      .apply block.restrict [.lambda binder (substitute (lift 1 assignment) body)] := by
  simp [substitute, substituteList_eq_map]

theorem substitute_inaction (assignment : Assignment) :
    substitute assignment (.apply block.unit []) = .apply block.unit [] := by
  simp [substitute, substituteList_eq_map]

theorem substitute_bag (assignment : Assignment) (kind : CollType) (elements : List Pattern) (rest : Option String) :
    substitute assignment (.collection kind elements rest) = .collection kind (elements.map (substitute assignment)) rest :=
  by simp [substitute, substituteList_eq_map]

theorem substitute_structural (assignment : Assignment) : Structural block (substitute assignment) :=
  ⟨substitute_bag assignment, substitute_inaction assignment⟩

/-- Substitution under one more binder commutes with lifting past it. -/
theorem substitute_lift_one (assignment : Assignment) (pattern : Pattern) :
    substitute (lift 1 assignment) (liftBVars 0 1 pattern) = liftBVars 0 1 (substitute assignment pattern) := by
  simpa only [Nat.zero_add, lift_zero] using substitute_liftBVars assignment pattern 0 1

/-- Substitution under two more binders commutes with exchanging them. -/
theorem substitute_swapInner (assignment : Assignment) (pattern : Pattern) :
    substitute (lift 2 assignment) (rename swapInner pattern) = rename swapInner (substitute (lift 2 assignment) pattern) := by
  rw [rename, rename, substitute_comp, substitute_comp]
  congr 1
  funext index
  rcases index with _ | _ | index
  · simp [substitute, swapInner, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift]
  · simp [substitute, swapInner, Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift]
  · have fixed : swapInner (index + 2) = index + 2 := by simp [swapInner]
    simp only [substitute, fixed]
    show Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift 2 assignment (index + 2) =
      rename swapInner (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift 2 assignment (index + 2))
    simp only [Mettapedia.OSLF.MeTTaIL.ContextSubstitution.lift, show ¬ index + 2 < 2 by omega, if_false]
    rw [liftBVars_eq_rename, rename_comp]
    congr 1

/-- **Substitution keeps the shape of a law**, once the substituted source has the process sort. -/
theorem generator_substitute (assignment : Assignment) {free : FreeTypeContext} {bound : List TypeExpr}
    {source target : Pattern} (generator : BlockGenerator language block source target)
    (typed : HasType language free bound (substitute assignment source) (.base block.proc)) :
    BlockGenerator language block (substitute assignment source) (substitute assignment target) := by
  cases generator with
  | nil binder =>
      rw [substitute_restriction, substitute_inaction, substitute_inaction]
      exact .nil binder
  | nilReverse =>
      rw [substitute_restriction, substitute_inaction, substitute_inaction]
      exact .nilReverse
  | extrusion members selected binder body inside chosen =>
      rw [substitute_bag, substitute_restriction, substitute_bag, List.map_cons, List.map_map]
      have inside' : selected < (members.map (substitute assignment)).length := by simpa using inside
      have chosen' : (members.map (substitute assignment))[selected] =
          .apply block.restrict [.lambda binder (substitute (lift 1 assignment) body)] := by
        rw [List.getElem_map]
        simp only [chosen, substitute_restriction]
      have shape := BlockGenerator.extrusion (language := language) _ selected binder _ inside' chosen'
      rw [map_eraseIdx, List.map_map] at shape
      have commute : substitute (lift 1 assignment) ∘ liftBVars 0 1 = liftBVars 0 1 ∘ substitute assignment :=
        funext (substitute_lift_one assignment)
      rw [commute]
      exact shape
  | extrusionReverse binder members selected originals inside othersEq =>
      rw [substitute_restriction, substitute_bag, substitute_bag, List.map_cons, substitute_restriction]
      have inside' : selected < (members.map (substitute (lift 1 assignment))).length := by simpa using inside
      have othersEq' : (members.map (substitute (lift 1 assignment))).eraseIdx selected =
          (originals.map (substitute assignment)).map (liftBVars 0 1) := by
        rw [map_eraseIdx, othersEq, List.map_map, List.map_map]
        exact List.map_congr_left fun original _ => substitute_lift_one assignment original
      have shape := BlockGenerator.extrusionReverse (language := language) (block := block) binder _ selected _ inside' othersEq'
      simpa only [List.getElem_map, lift_zero] using shape
  | exchange outerBinder innerBinder body =>
      rw [substitute_restriction, substitute_restriction, substitute_restriction, substitute_restriction,
        lift_lift, substitute_swapInner]
      exact .exchange outerBinder innerBinder _
  | emptyUnit label listed =>
      have emptyIs : substitute assignment (.apply label [.collection .hashBag [] none]) =
          .apply label [.collection .hashBag [] none] := by simp [substitute, substituteList_eq_map]
      rw [emptyIs, substitute_restriction, substitute_inaction]
      exact .emptyUnit label listed
  | emptyUnitReverse label listed binder =>
      have emptyIs : substitute assignment (.apply label [.collection .hashBag [] none]) =
          .apply label [.collection .hashBag [] none] := by simp [substitute, substituteList_eq_map]
      rw [emptyIs, substitute_restriction, substitute_inaction]
      exact .emptyUnitReverse label listed binder
  | derived derivedInstance =>
      exact .derived (derived_map (substitute_structural assignment) derivedInstance (.inl typed)).1

omit laws in
/-- Substitution keeps applications applications. -/
theorem substitute_applies (assignment : Assignment) (constructor : String) (arguments : List Pattern) :
    ∃ arguments', substitute assignment (.apply constructor arguments) = .apply constructor arguments' :=
  ⟨arguments.map (substitute assignment), by simp [substitute, substituteList_eq_map]⟩

omit laws in
/-- The source of a law is an application or a collection. -/
theorem generator_source_head {source target : Pattern} (generator : BlockGenerator language block source target) :
    (∃ constructor arguments, source = .apply constructor arguments) ∨
      ∃ kind elements rest, source = .collection kind elements rest := by
  cases generator with
  | nil => exact .inl ⟨_, _, rfl⟩
  | nilReverse => exact .inl ⟨_, _, rfl⟩
  | extrusion => exact .inr ⟨_, _, _, rfl⟩
  | extrusionReverse => exact .inl ⟨_, _, rfl⟩
  | exchange => exact .inl ⟨_, _, rfl⟩
  | emptyUnit => exact .inl ⟨_, _, rfl⟩
  | emptyUnitReverse => exact .inl ⟨_, _, rfl⟩
  | derived derivedInstance => cases derivedInstance <;> exact .inr ⟨_, _, _, rfl⟩

omit laws in
theorem substitute_source_notLambda (assignment : Assignment) {source target : Pattern}
    (generator : BlockGenerator language block source target) :
    ∀ binder body, substitute assignment source ≠ .lambda binder body := by
  intro binder body equal
  rcases generator_source_head generator with ⟨constructor, arguments, rfl⟩ | ⟨kind, elements, rest, rfl⟩ <;>
    simp [substitute] at equal

/-! ## Substitution of terms for variables -/

open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationGenerator)

/-- **An assignment of terms of the sorts of the variables**: every variable of the source context is sent to an
object of its sort in the target context. -/
structure SortedAssignment (language : LanguageDef) (free : FreeTypeContext) (bound target : List TypeExpr)
    (assignment : Assignment) : Prop where
  typed : ∀ index type, bound[index]? = some type → HasType language free target (assignment index) type
  objects : ObjectAssignment assignment

omit laws in
theorem isObject_of_fill : ∀ (context : OneHoleContext) {filling : Pattern},
    isObjectPattern (context.fill filling) = true → isObjectPattern filling = true
  | .hole, _, object => object
  | .apply _ _ inner _, _, object => isObject_of_fill inner (isObject_apply_member object)
  | .lambda _ inner, _, object => isObject_of_fill inner (by simpa [OneHoleContext.fill, isObjectPattern] using object)
  | .multiLambda _ _ inner, _, object =>
      isObject_of_fill inner (by simpa [OneHoleContext.fill, isObjectPattern] using object)
  | .substBody _ _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .substReplacement _ _, _, object => by simp [OneHoleContext.fill, isObjectPattern] at object
  | .collection _ _ inner _ _, _, object => isObject_of_fill inner (isObject_collection_member object)

/-- **The substituted source of a generator is a process**, if it has a sort at all. -/
theorem substitute_source_sort (assignment : Assignment) {source target : Pattern}
    (generator : BlockGenerator language block source target) {free : FreeTypeContext} {bound : List TypeExpr}
    {sort : String} (typed : HasType language free bound (substitute assignment source) (.base sort)) :
    sort = block.proc := by
  cases generator with
  | nil binder =>
      rw [substitute_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | nilReverse =>
      rw [substitute_inaction] at typed
      obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      exact typeIs.trans (laws.unitShape rule member labelIs.symm)
  | extrusion =>
      rw [substitute_bag] at typed
      exact (laws.bag_members typed).2.1
  | extrusionReverse =>
      rw [substitute_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | exchange =>
      rw [substitute_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | emptyUnit label listed =>
      have emptyIs : substitute assignment (.apply label [.collection .hashBag [] none]) =
          .apply label [.collection .hashBag [] none] := by simp [substitute, substituteList_eq_map]
      rw [emptyIs] at typed
      obtain ⟨rule, member, labelIs, -, typeIs, -⟩ := hasType_apply_inversion typed
      simp only [TypeExpr.base.injEq] at typeIs
      exact typeIs.trans ((laws.emptyUnitShape label listed).2 rule member labelIs.symm)
  | emptyUnitReverse label listed binder =>
      rw [substitute_restriction] at typed
      simpa using (laws.restriction_typed typed).2.1
  | derived derivedInstance =>
      cases derivedInstance <;> rw [substitute_bag] at typed <;> exact (laws.bag_members typed).2.1

end Shapes

section Laws

variable [laws : BlockLanguage language block]

include laws in
/-- A step of the static theory keeps object patterns, both ways. -/
theorem step_isObject {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator} {first second : Pattern}
    (step : EquationContextStep base language first second) : isObjectPattern first = isObjectPattern second := by
  cases step with
  | inContext context generator =>
      exact isObject_fill_congr (generator_interchangeable (block := block) generator).object context

/-- **The static theory between processes is closed under substitution**: a chain through processes from an object
is carried by an assignment of terms of the variables' sorts to a chain through processes. -/
theorem sortedEquiv_substitute {free : FreeTypeContext} {bound target : List TypeExpr}
    (targetContext : BaseContext free target) {assignment : Assignment}
    (assigned : SortedAssignment language free bound target assignment) {first second : Pattern}
    (equivalent : ProcEquiv language block free bound first second) :
    isObjectPattern first = true →
      ProcEquiv language block free target (substitute assignment first) (substitute assignment second) := by
  induction equivalent with
  | rel first second step =>
      intro firstObject
      have secondObject : isObjectPattern second = true := by rw [← step_isObject (block := block) step.step]; exact firstObject
      have firstTyped := HasType.substituteBoundOnSupport step.firstTyped assignment
        (fun index type _ lookup => assigned.typed index type lookup)
      have secondTyped := HasType.substituteBoundOnSupport step.secondTyped assignment
        (fun index type _ lookup => assigned.typed index type lookup)
      have firstObject' := isObject_substitute _ assigned.objects firstObject
      have secondObject' := isObject_substitute _ assigned.objects secondObject
      have stepped := step.step
      cases stepped with
      | @inContext context redex contractum generator =>
          have shape := generator_shape (block := block) generator
          change HasType language free target (substitute assignment (context.fill redex)) (.base block.proc)
            at firstTyped
          change HasType language free target (substitute assignment (context.fill contractum)) (.base block.proc)
            at secondTyped
          rw [ContextSubstitution.substitute_fill] at firstTyped firstObject' secondTyped secondObject'
          rw [ContextSubstitution.substitute_fill, ContextSubstitution.substitute_fill]
          obtain ⟨holeBound, holeType, holeContext, holeKind, redexTyped, contractumTyped, rebuild⟩ :=
            fill_typed_pair (block := block) _ targetContext firstTyped secondTyped (.inl ⟨block.proc, rfl⟩)
              firstObject' secondObject' (substitute_source_notLambda _ shape)
          rcases holeKind with ⟨holeSort, rfl⟩ | multiset
          · obtain rfl := substitute_source_sort _ shape redexTyped
            have substituted := generator_substitute _ shape redexTyped
            have redexObject := isObject_of_fill _ firstObject'
            have canonical := (metadata_of_typed (block := block) _ redexTyped redexObject).1 ⟨block.proc, rfl⟩
            exact SortedEquiv.fill _ rebuild (generator_equiv substituted canonical redexTyped)
          · have derived := generator_at_multiset (substitute_structural (ContextSubstitution.atHole assignment context))
              (substitute_applies (ContextSubstitution.atHole assignment context)) holeContext shape multiset redexTyped
              contractumTyped (isObject_of_fill _ secondObject')
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

/-! ## Communication: a received datum -/

open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (single substitute_single_eq_instantiateBVar)

omit laws in
theorem single_assignment {free : FreeTypeContext} {bound : List TypeExpr} {datum : Pattern} {sort : String}
    (typed : HasType language free bound datum (.base sort)) (object : isObjectPattern datum = true) :
    SortedAssignment language free (.base sort :: bound) bound (single datum) where
  typed index type lookup := by
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
        subst lookup
        exact typed
    | succ index => exact HasType.bvar (by simpa using lookup)
  objects index := by
    cases index with
    | zero => exact object
    | succ index => rfl

/-- **Equivalent continuations stay equivalent once a datum is received.** -/
theorem sortedEquiv_instantiate {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    {datum first second : Pattern} {sort : String} (typed : HasType language free bound datum (.base sort))
    (object : isObjectPattern datum = true)
    (equivalent : ProcEquiv language block free (.base sort :: bound) first second)
    (firstObject : isObjectPattern first = true) :
    ProcEquiv language block free bound (instantiateBVar datum first) (instantiateBVar datum second) := by
  rw [← substitute_single_eq_instantiateBVar, ← substitute_single_eq_instantiateBVar]
  exact sortedEquiv_substitute context (single_assignment typed object) equivalent firstObject

omit laws in
/-- The shift past one new variable, as an assignment. -/
theorem shift_assignment {free : FreeTypeContext} {bound : List TypeExpr} {sort : String} :
    SortedAssignment language free bound (.base sort :: bound) (fun index => .bvar (1 + index)) where
  typed index type lookup := HasType.bvar (by rw [Nat.add_comm]; simpa using lookup)
  objects _ := rfl

/-- **A chain through processes read under one more variable.** -/
theorem sortedEquiv_lift {free : FreeTypeContext} {bound : List TypeExpr} (context : BaseContext free bound)
    (sort : String) {first second : Pattern} (equivalent : ProcEquiv language block free bound first second)
    (firstObject : isObjectPattern first = true) :
    ProcEquiv language block free (.base sort :: bound) (liftBVars 0 1 first) (liftBVars 0 1 second) := by
  have shifted := sortedEquiv_substitute (context.cons sort) (shift_assignment (sort := sort)) equivalent firstObject
  have shift := fun pattern => substitute_shift 1 pattern 0
  simp only [lift_zero] at shift
  rwa [shift, shift] at shifted

end Laws

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
