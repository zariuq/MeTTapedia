import Mettapedia.Languages.ProcessCalculi.CCS.LabelledCongruence

/-!
# Strong bisimilarity of CCS with recursion

**Bisimilarity** is an equivalence and the largest strong bisimulation (`Bisimilar.refl`, `Bisimilar.symm`,
`Bisimilar.trans`, `bisimilar_bisimulation`). It is a congruence for parallel composition (`bisimilar_bag`) and for
restriction (`bisimilar_restrict`).

**Transitions create no free name** (`LStep.names_sub`): the free names of the target, and the action's, are the
source's. A call's body has no free name of its own, and its parameters are put the call's arguments
(`offered_names`).

**A fresh sentinel cancels** (`bisimilar_cancel`): two processes bisimilar beside the sentinel `k.0`, with `k` free in
neither, are bisimilar. The sentinel's transition is an action on `k`, which neither process performs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList_eq_map)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift substituteList_eq_map)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

variable {definitions : List Definition}

/-! ## Bisimilarity is an equivalence -/

theorem Bisimulation.flip {relation : Pattern → Pattern → Prop} (bisimulation : Bisimulation definitions relation) :
    Bisimulation definitions (fun first second => relation second first) :=
  fun _ _ related => ⟨(bisimulation related).2, (bisimulation related).1⟩

theorem Bisimulation.comp {left right : Pattern → Pattern → Prop} (leftBisimulation : Bisimulation definitions left)
    (rightBisimulation : Bisimulation definitions right) :
    Bisimulation definitions (fun first third => ∃ second, left first second ∧ right second third) := by
  rintro first third ⟨second, leftRelated, rightRelated⟩
  constructor
  · intro action target step
    obtain ⟨target', step', related'⟩ := (leftBisimulation leftRelated).1 step
    obtain ⟨target'', step'', related''⟩ := (rightBisimulation rightRelated).1 step'
    exact ⟨target'', step'', target', related', related''⟩
  · intro action target'' step''
    obtain ⟨target', step', related'⟩ := (rightBisimulation rightRelated).2 step''
    obtain ⟨target, step, related⟩ := (leftBisimulation leftRelated).2 step'
    exact ⟨target, step, target', related, related'⟩

theorem Bisimilar.refl (process : Pattern) : Bisimilar definitions process process :=
  ⟨Eq, fun first _ same => by
    subst same
    exact ⟨fun _ target step => ⟨target, step, rfl⟩, fun _ target step => ⟨target, step, rfl⟩⟩, rfl⟩

theorem Bisimilar.symm {first second : Pattern} (bisimilar : Bisimilar definitions first second) :
    Bisimilar definitions second first :=
  let ⟨_, bisimulation, related⟩ := bisimilar
  ⟨_, bisimulation.flip, related⟩

theorem Bisimilar.trans {first second third : Pattern} (left : Bisimilar definitions first second)
    (right : Bisimilar definitions second third) : Bisimilar definitions first third :=
  let ⟨_, leftBisimulation, leftRelated⟩ := left
  let ⟨_, rightBisimulation, rightRelated⟩ := right
  ⟨_, leftBisimulation.comp rightBisimulation, _, leftRelated, rightRelated⟩

/-- **Bisimilarity is a bisimulation**, the largest. -/
theorem bisimilar_bisimulation : Bisimulation definitions (Bisimilar definitions) := by
  rintro first second ⟨relation, bisimulation, related⟩
  constructor
  · intro action target step
    obtain ⟨target', step', related'⟩ := (bisimulation related).1 step
    exact ⟨target', step', relation, bisimulation, related'⟩
  · intro action target' step'
    obtain ⟨target, step, related⟩ := (bisimulation related).2 step'
    exact ⟨target, step, relation, bisimulation, related⟩

/-- A transition of the first of two bisimilar processes is matched by the second. -/
theorem Bisimilar.forth {first second : Pattern} (bisimilar : Bisimilar definitions first second) {action : Action}
    {target : Pattern} (step : LStep definitions first action target) :
    ∃ target', LStep definitions second action target' ∧ Bisimilar definitions target target' :=
  (bisimilar_bisimulation bisimilar).1 step

/-- A relation within bisimilarity's closure: every pair of a bisimulation is bisimilar. -/
theorem Bisimulation.bisimilar {relation : Pattern → Pattern → Prop} (bisimulation : Bisimulation definitions relation)
    {first second : Pattern} (related : relation first second) : Bisimilar definitions first second :=
  ⟨relation, bisimulation, related⟩

/-! ## A congruence -/

theorem forall₂_getElem {relation : Pattern → Pattern → Prop} : ∀ {elements elements' : List Pattern},
    List.Forall₂ relation elements elements' → ∀ (index : Nat) (inside : index < elements.length),
      ∃ inside' : index < elements'.length, relation elements[index] elements'[index]
  | _ :: _, _ :: _, .cons head _, 0, _ => ⟨by simp, head⟩
  | _ :: _, _ :: _, .cons _ tail, index + 1, inside => by
      obtain ⟨inside', related⟩ := forall₂_getElem tail index (by simpa using inside)
      exact ⟨by simpa using inside', related⟩

theorem forall₂_eraseIdx {relation : Pattern → Pattern → Prop} : ∀ {elements elements' : List Pattern},
    List.Forall₂ relation elements elements' → ∀ (index : Nat),
      List.Forall₂ relation (elements.eraseIdx index) (elements'.eraseIdx index)
  | [], [], .nil, _ => by simp
  | _ :: _, _ :: _, .cons _ tail, 0 => by simpa using tail
  | _ :: _, _ :: _, .cons head tail, index + 1 => by
      simpa using List.Forall₂.cons head (forall₂_eraseIdx tail index)

/-- A transition of a bag of members, matched by a bag of bisimilar members, to bags of bisimilar members. -/
theorem bag_forth {members members' : List Pattern} (related : List.Forall₂ (Bisimilar definitions) members members')
    {action : Action} {target : Pattern} (step : LStep definitions (.collection .hashBag members none) action target) :
    ∃ results results', target = .collection .hashBag results none ∧
      LStep definitions (.collection .hashBag members' none) action (.collection .hashBag results' none) ∧
      List.Forall₂ (Bisimilar definitions) results results' := by
  cases step with
  | offer offered => simp [offers] at offered
  | par i hi inner =>
      obtain ⟨hi', memberBisimilar⟩ := forall₂_getElem related i hi
      obtain ⟨target', step', targetBisimilar⟩ := memberBisimilar.forth inner
      exact ⟨_, _, rfl, .par i hi' step', .cons targetBisimilar (forall₂_eraseIdx related i)⟩
  | sync i hi j hj first second =>
      obtain ⟨hi', firstBisimilar⟩ := forall₂_getElem related i hi
      have erased := forall₂_eraseIdx related i
      obtain ⟨hj', secondBisimilar⟩ := forall₂_getElem erased j hj
      obtain ⟨target₁, step₁, bisimilar₁⟩ := firstBisimilar.forth first
      obtain ⟨target₂, step₂, bisimilar₂⟩ := secondBisimilar.forth second
      exact ⟨_, _, rfl, .sync i hi' j hj' step₁ step₂, .cons bisimilar₁ (.cons bisimilar₂ (forall₂_eraseIdx erased j))⟩

theorem forall₂_bisimilar_symm {members members' : List Pattern}
    (related : List.Forall₂ (Bisimilar definitions) members members') :
    List.Forall₂ (Bisimilar definitions) members' members :=
  related.flip.imp fun _ _ bisimilar => Bisimilar.symm bisimilar

/-- **Bags of pairwise bisimilar members are bisimilar**: bisimilarity is a congruence for parallel composition. -/
theorem bisimilar_bag {elements elements' : List Pattern}
    (pairwise : List.Forall₂ (Bisimilar definitions) elements elements') :
    Bisimilar definitions (.collection .hashBag elements none) (.collection .hashBag elements' none) := by
  refine ⟨fun first second => (∃ members members', first = .collection .hashBag members none ∧
      second = .collection .hashBag members' none ∧ List.Forall₂ (Bisimilar definitions) members members') ∨
    Bisimilar definitions first second, ?_, .inl ⟨_, _, rfl, rfl, pairwise⟩⟩
  rintro first second (⟨members, members', rfl, rfl, related⟩ | bisimilar)
  · constructor
    · intro action target step
      obtain ⟨results, results', rfl, step', resultsRelated⟩ := bag_forth related step
      exact ⟨_, step', .inl ⟨_, _, rfl, rfl, resultsRelated⟩⟩
    · intro action target step
      obtain ⟨results', results, rfl, step', resultsRelated⟩ := bag_forth (forall₂_bisimilar_symm related) step
      exact ⟨_, step', .inl ⟨_, _, rfl, rfl, forall₂_bisimilar_symm resultsRelated⟩⟩
  · obtain ⟨forth, back⟩ := bisimilar_bisimulation bisimilar
    exact ⟨fun _ _ step => let ⟨target', step', related⟩ := forth step; ⟨target', step', .inr related⟩,
      fun _ _ step => let ⟨target, step', related⟩ := back step; ⟨target, step', .inr related⟩⟩

/-- **Restrictions of bisimilar processes are bisimilar.** -/
theorem bisimilar_restrict {first second : Pattern} (bisimilar : Bisimilar definitions first second)
    (binder binder' : Option String) :
    Bisimilar definitions (.apply "CNu" [.lambda binder first]) (.apply "CNu" [.lambda binder' second]) := by
  refine ⟨fun outer outer' => (∃ binder binder' inner inner', outer = .apply "CNu" [.lambda binder inner] ∧
      outer' = .apply "CNu" [.lambda binder' inner'] ∧ Bisimilar definitions inner inner') ∨
    Bisimilar definitions outer outer', ?_, .inl ⟨_, _, _, _, rfl, rfl, bisimilar⟩⟩
  rintro outer outer' (⟨binder, binder', inner, inner', rfl, rfl, related⟩ | related)
  · constructor
    · intro action target step
      obtain ⟨action', target', innerStep, seen, rfl⟩ := lstep_restriction_inv step
      obtain ⟨target'', step', targetRelated⟩ := related.forth innerStep
      exact ⟨_, .res binder' step' seen, .inl ⟨_, _, _, _, rfl, rfl, targetRelated⟩⟩
    · intro action target step
      obtain ⟨action', target', innerStep, seen, rfl⟩ := lstep_restriction_inv step
      obtain ⟨target'', step', targetRelated⟩ := related.symm.forth innerStep
      exact ⟨_, .res binder step' seen, .inl ⟨_, _, _, _, rfl, rfl, targetRelated.symm⟩⟩
  · obtain ⟨forth, back⟩ := bisimilar_bisimulation related
    exact ⟨fun _ _ step => let ⟨target', step', related⟩ := forth step; ⟨target', step', .inr related⟩,
      fun _ _ step => let ⟨target, step', related⟩ := back step; ⟨target, step', .inr related⟩⟩

/-! ## Free names -/

theorem mem_names_bag {name : String} {kind : CollType} {elements : List Pattern} {tail : Option String} :
    name ∈ (Pattern.collection kind elements tail).freeFvarNames ↔
      (∃ element ∈ elements, name ∈ element.freeFvarNames) ∨ name ∈ tail.toList := by
  simp [Pattern.freeFvarNames, List.mem_flatMap]

theorem mem_names_apply {name : String} {label : String} {arguments : List Pattern} :
    name ∈ (Pattern.apply label arguments).freeFvarNames ↔ ∃ argument ∈ arguments, name ∈ argument.freeFvarNames := by
  simp [Pattern.freeFvarNames, List.mem_flatMap]

theorem freeFvarNames_liftBVars : ∀ (pattern : Pattern) (cutoff shift : Nat),
    (liftBVars cutoff shift pattern).freeFvarNames = pattern.freeFvarNames := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro cutoff shift
      simp only [liftBVars]
      split <;> simp [Pattern.freeFvarNames]
  | hfvar name => intro _ _; simp [liftBVars, Pattern.freeFvarNames]
  | happly label arguments recurse =>
      intro cutoff shift
      simp only [liftBVars, liftBVarsList_eq_map, Pattern.freeFvarNames, List.flatMap_map]
      exact List.flatMap_congr fun argument member => recurse argument member cutoff shift
  | hlambda binder body recurse =>
      intro cutoff shift
      simp only [liftBVars, Pattern.freeFvarNames]
      exact recurse _ _
  | hmultiLambda arity binders body recurse =>
      intro cutoff shift
      simp only [liftBVars, Pattern.freeFvarNames]
      exact recurse _ _
  | hsubst body replacement recurseBody recurseReplacement =>
      intro cutoff shift
      simp only [liftBVars, Pattern.freeFvarNames]
      rw [recurseBody, recurseReplacement]
  | hcollection kind elements rest recurse =>
      intro cutoff shift
      simp only [liftBVars, liftBVarsList_eq_map, Pattern.freeFvarNames, List.flatMap_map]
      rw [List.flatMap_congr fun element member => recurse element member cutoff shift]

/-- **A substitution's free names** are the pattern's or the assignment's. -/
theorem mem_names_substitute {name : String} : ∀ (pattern : Pattern) (assignment : Assignment),
    name ∈ (substitute assignment pattern).freeFvarNames →
      name ∈ pattern.freeFvarNames ∨ ∃ index, name ∈ (assignment index).freeFvarNames := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro assignment member; exact .inr ⟨index, by simpa [substitute] using member⟩
  | hfvar _ => intro assignment member; exact .inl (by simpa [substitute] using member)
  | happly label arguments recurse =>
      intro assignment member
      simp only [substitute, substituteList_eq_map, mem_names_apply, List.mem_map] at member
      obtain ⟨_, ⟨argument, inArguments, rfl⟩, inArgument⟩ := member
      rcases recurse argument inArguments assignment inArgument with here | there
      · exact .inl (mem_names_apply.mpr ⟨argument, inArguments, here⟩)
      · exact .inr there
  | hlambda binder body recurse =>
      intro assignment member
      simp only [substitute, Pattern.freeFvarNames] at member
      rcases recurse (lift 1 assignment) member with here | ⟨index, there⟩
      · exact .inl (by simpa [Pattern.freeFvarNames] using here)
      · unfold lift at there
        split at there
        · simp [Pattern.freeFvarNames] at there
        · rw [freeFvarNames_liftBVars] at there
          exact .inr ⟨_, there⟩
  | hmultiLambda arity binders body recurse =>
      intro assignment member
      simp only [substitute, Pattern.freeFvarNames] at member
      rcases recurse (lift arity assignment) member with here | ⟨index, there⟩
      · exact .inl (by simpa [Pattern.freeFvarNames] using here)
      · unfold lift at there
        split at there
        · simp [Pattern.freeFvarNames] at there
        · rw [freeFvarNames_liftBVars] at there
          exact .inr ⟨_, there⟩
  | hsubst body replacement recurseBody recurseReplacement =>
      intro assignment member
      simp only [substitute, Pattern.freeFvarNames, List.mem_append] at member
      rcases member with member | member
      · rcases recurseBody (lift 1 assignment) member with here | ⟨index, there⟩
        · exact .inl (by simp [Pattern.freeFvarNames, here])
        · unfold lift at there
          split at there
          · simp [Pattern.freeFvarNames] at there
          · rw [freeFvarNames_liftBVars] at there
            exact .inr ⟨_, there⟩
      · rcases recurseReplacement assignment member with here | there
        · exact .inl (by simp [Pattern.freeFvarNames, here])
        · exact .inr there
  | hcollection kind elements rest recurse =>
      intro assignment member
      simp only [substitute, substituteList_eq_map, mem_names_bag, List.mem_map] at member
      rcases member with ⟨_, ⟨element, inElements, rfl⟩, inElement⟩ | inRest
      · rcases recurse element inElements assignment inElement with here | there
        · exact .inl (mem_names_bag.mpr (.inl ⟨element, inElements, here⟩))
        · exact .inr there
      · exact .inl (mem_names_bag.mpr (.inr inRest))

theorem mem_names_arguments {name : String} : ∀ {names : List Pattern},
    name ∈ (arguments names).freeFvarNames → ∃ argument ∈ names, name ∈ argument.freeFvarNames
  | [], member => by simp [arguments, Pattern.freeFvarNames] at member
  | first :: others, member => by
      simp only [arguments, mem_names_apply, List.mem_cons, List.not_mem_nil, or_false] at member
      obtain ⟨argument, inArguments, inArgument⟩ := member
      rcases inArguments with rfl | rfl
      · exact ⟨argument, List.mem_cons_self, inArgument⟩
      · obtain ⟨found, inOthers, inFound⟩ := mem_names_arguments inArgument
        exact ⟨found, List.mem_cons_of_mem _ inOthers, inFound⟩

/-- **What a component offers has only its free names**: a sum's summands are its parts, and a call's body has no
free name of its own, its parameters put the call's arguments. -/
theorem offered_names (admitted : admits definitions = true) {component : Pattern} {guards : List Pattern}
    (offered : offers definitions component = some guards) :
    ∀ guard ∈ guards, ∀ name ∈ guard.freeFvarNames, name ∈ component.freeFvarNames := by
  rcases offers_cases offered with ⟨tail, rfl⟩ | ⟨callName, args, rfl, found⟩
  · intro guard member name inGuard
    exact mem_names_apply.mpr ⟨_, List.mem_singleton_self _, mem_names_bag.mpr (.inl ⟨guard, member, inGuard⟩)⟩
  · obtain ⟨definition, names, lookupFound, namesFound, rfl⟩ := body_some found
    obtain ⟨rfl, -⟩ := arguments_of_argumentsOf namesFound
    intro guard member name inGuard
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨originalTyped, originalObject⟩ := guard_admitted admitted (lookup_mem lookupFound) originalMember
    rcases mem_names_substitute original _ inGuard with inOriginal | ⟨index, inArgument⟩
    · obtain ⟨_, assigned⟩ := originalTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern originalObject inOriginal
      simp [noFreeNames] at assigned
    · simp only [argumentAssignment] at inArgument
      by_cases inside : index < names.length
      · rw [List.getD_eq_getElem _ _ inside] at inArgument
        exact mem_names_apply.mpr ⟨arguments names, by simp,
          mem_names_arguments_of (List.getElem_mem inside) inArgument⟩
      · rw [List.getD_eq_default _ _ (by omega)] at inArgument
        simp [Pattern.freeFvarNames] at inArgument
where
  mem_names_arguments_of {name : String} : ∀ {names : List Pattern} {argument : Pattern}, argument ∈ names →
      name ∈ argument.freeFvarNames → name ∈ (arguments names).freeFvarNames
    | first :: others, argument, inNames, inArgument => by
        simp only [arguments, mem_names_apply, List.mem_cons, List.not_mem_nil, or_false]
        rcases List.mem_cons.mp inNames with rfl | inOthers
        · exact ⟨argument, .inl rfl, inArgument⟩
        · exact ⟨arguments others, .inr rfl, mem_names_arguments_of inOthers inArgument⟩

/-- The free names of an action. -/
def Action.names : Action → List String
  | .act name => name.freeFvarNames
  | .coact name => name.freeFvarNames
  | .tau => []

theorem Action.lower?_names {action action' : Action} (seen : action.lower? = some action') :
    action'.names = action.names := by
  have lowered : ∀ {name name' : Pattern}, lowerName? name = some name' → name'.freeFvarNames = name.freeFvarNames := by
    intro name name' found
    match name, found with
    | .bvar (_ + 1), found =>
        simp only [lowerName?, Option.some.injEq] at found
        subst found
        simp [Pattern.freeFvarNames]
    | .fvar _, found =>
        simp only [lowerName?, Option.some.injEq] at found
        subst found
        rfl
  cases action with
  | act name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      exact lowered found
  | coact name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      exact lowered found
  | tau =>
      simp only [Action.lower?, Option.some.injEq] at seen
      subst seen
      rfl

/-- **A transition creates no free name**: the free names of the target, and the action's, are the source's. -/
theorem LStep.names_sub (admitted : admits definitions = true) {source : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions source action target) :
    (∀ name ∈ target.freeFvarNames, name ∈ source.freeFvarNames) ∧
      (∀ name ∈ action.names, name ∈ source.freeFvarNames) := by
  induction step with
  | @offer component guards offered k hk action continuation performs =>
      have guardNames := offered_names admitted offered _ (List.getElem_mem hk)
      rcases guardAction_some performs with ⟨name, rfl, guardIs⟩ | ⟨name, rfl, guardIs⟩ | ⟨rfl, guardIs⟩ <;>
        rw [guardIs] at guardNames
      · exact ⟨fun found member => guardNames found (mem_names_apply.mpr ⟨_, by simp, member⟩),
          fun found member => guardNames found (mem_names_apply.mpr ⟨_, by simp, member⟩)⟩
      · exact ⟨fun found member => guardNames found (mem_names_apply.mpr ⟨_, by simp, member⟩),
          fun found member => guardNames found (mem_names_apply.mpr ⟨_, by simp, member⟩)⟩
      · exact ⟨fun found member => guardNames found (mem_names_apply.mpr ⟨_, by simp, member⟩),
          fun found member => by simp [Action.names] at member⟩
  | @par elements tail i hi action target inner recurse =>
      obtain ⟨targetNames, actionNames⟩ := recurse
      have memberNames : ∀ name ∈ elements[i].freeFvarNames,
          name ∈ (Pattern.collection .hashBag elements tail).freeFvarNames :=
        fun _ member => mem_names_bag.mpr (.inl ⟨_, List.getElem_mem hi, member⟩)
      refine ⟨fun name member => ?_, fun name member => memberNames name (actionNames name member)⟩
      rcases mem_names_bag.mp member with ⟨element, inElements, inElement⟩ | inTail
      · rcases List.mem_cons.mp inElements with rfl | inRest
        · exact memberNames name (targetNames name inElement)
        · exact mem_names_bag.mpr (.inl ⟨element, List.mem_of_mem_eraseIdx inRest, inElement⟩)
      · simp at inTail
  | @sync elements tail i hi j hj name target target' first second recurseFirst recurseSecond =>
      obtain ⟨firstNames, -⟩ := recurseFirst
      obtain ⟨secondNames, -⟩ := recurseSecond
      have inBag : ∀ {element : Pattern}, element ∈ elements → ∀ found ∈ element.freeFvarNames,
          found ∈ (Pattern.collection .hashBag elements tail).freeFvarNames :=
        fun inElements _ member => mem_names_bag.mpr (.inl ⟨_, inElements, member⟩)
      refine ⟨fun found member => ?_, fun found member => by simp [Action.names] at member⟩
      rcases mem_names_bag.mp member with ⟨element, inElements, inElement⟩ | inTail
      · simp only [List.mem_cons] at inElements
        rcases inElements with rfl | rfl | inRest
        · exact inBag (List.getElem_mem hi) found (firstNames found inElement)
        · exact inBag (List.mem_of_mem_eraseIdx (List.getElem_mem hj)) found (secondNames found inElement)
        · exact inBag (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx inRest)) found inElement
      · simp at inTail
  | @res binder source target action action' inner seen recurse =>
      obtain ⟨targetNames, actionNames⟩ := recurse
      refine ⟨fun found member => ?_, fun found member => ?_⟩
      · have inBody : found ∈ target.freeFvarNames := by
          simpa [Pattern.freeFvarNames] using member
        simpa [Pattern.freeFvarNames] using targetNames found inBody
      · rw [Action.lower?_names seen] at member
        simpa [Pattern.freeFvarNames] using actionNames found member

/-! ## A fresh sentinel cancels -/

/-- **The sentinel** `k.0`: a sum of one action on the name. -/
def sentinel (name : String) : Pattern :=
  .apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar name, .apply "CNil" []]] none]

theorem sentinel_step {name : String} {action : Action} {target : Pattern}
    (step : LStep definitions (sentinel name) action target) :
    action = .act (.fvar name) ∧ target = .apply "CNil" [] := by
  obtain ⟨k, hk, performs⟩ := lstep_sum_inv step
  match k, hk, performs with
  | 0, _, performs =>
      simp only [List.getElem_cons_zero, guardAction, Option.some.injEq, Prod.mk.injEq] at performs
      exact ⟨performs.1.symm, performs.2.symm⟩

/-- A transition of one of two processes beside a fresh sentinel, matched beside the sentinel. -/
theorem cancel_forth (admitted : admits definitions = true) {name : String} {first second : Pattern}
    (firstFresh : name ∉ first.freeFvarNames) (secondFresh : name ∉ second.freeFvarNames)
    (related : Bisimilar definitions (.collection .hashBag [first, sentinel name] none)
      (.collection .hashBag [second, sentinel name] none))
    {action : Action} {target : Pattern} (step : LStep definitions first action target) :
    ∃ target', LStep definitions second action target' ∧ name ∉ target.freeFvarNames ∧
      name ∉ target'.freeFvarNames ∧ Bisimilar definitions (.collection .hashBag [target, sentinel name] none)
        (.collection .hashBag [target', sentinel name] none) := by
  have actionFresh : name ∉ action.names := fun member => firstFresh ((step.names_sub admitted).2 name member)
  have targetFresh : name ∉ target.freeFvarNames := fun member => firstFresh ((step.names_sub admitted).1 name member)
  obtain ⟨matched, matchedStep, matchedRelated⟩ :=
    related.forth (LStep.par (elements := [first, sentinel name]) (tail := none) 0 (by simp) step)
  cases matchedStep with
  | offer offered => simp [offers] at offered
  | par i hi inner =>
      match i, hi, inner with
      | 0, _, inner =>
          exact ⟨_, inner, targetFresh, fun member => secondFresh ((inner.names_sub admitted).1 name member),
            matchedRelated⟩
      | 1, _, inner =>
          obtain ⟨rfl, -⟩ := sentinel_step inner
          exact absurd (by simp [Action.names, Pattern.freeFvarNames]) actionFresh
  | sync i hi j hj firstStep secondStep =>
      match i, hi, j, hj, firstStep, secondStep with
      | 0, _, 0, _, _, secondStep => exact absurd (sentinel_step secondStep).1 (by simp)
      | 1, _, 0, _, firstStep, secondStep =>
          obtain ⟨actIs, -⟩ := sentinel_step firstStep
          cases actIs
          exact absurd ((secondStep.names_sub admitted).2 name (by simp [Action.names, Pattern.freeFvarNames]))
            secondFresh

/-- **A fresh sentinel cancels**: two processes bisimilar beside the sentinel `k.0`, with `k` free in neither, are
bisimilar. -/
theorem bisimilar_cancel (admitted : admits definitions = true) {name : String} {first second : Pattern}
    (firstFresh : name ∉ first.freeFvarNames) (secondFresh : name ∉ second.freeFvarNames)
    (related : Bisimilar definitions (.collection .hashBag [first, sentinel name] none)
      (.collection .hashBag [second, sentinel name] none)) :
    Bisimilar definitions first second := by
  refine ⟨fun left right => name ∉ left.freeFvarNames ∧ name ∉ right.freeFvarNames ∧
      Bisimilar definitions (.collection .hashBag [left, sentinel name] none)
        (.collection .hashBag [right, sentinel name] none), ?_, firstFresh, secondFresh, related⟩
  rintro left right ⟨leftFresh, rightFresh, bisimilar⟩
  constructor
  · intro action target step
    obtain ⟨target', step', targetFresh, targetFresh', related'⟩ :=
      cancel_forth admitted leftFresh rightFresh bisimilar step
    exact ⟨target', step', targetFresh, targetFresh', related'⟩
  · intro action target' step
    obtain ⟨target, step', targetFresh', targetFresh, related'⟩ :=
      cancel_forth admitted rightFresh leftFresh bisimilar.symm step
    exact ⟨target, step', targetFresh, targetFresh', related'.symm⟩

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
