import Mettapedia.Languages.ProcessCalculi.CCS.LabelledBisimilarity
import Mettapedia.OSLF.MeTTaIL.FreeNameMaps

/-!
# Relabelling CCS with recursion

Relabelling has two homes.

**Renaming free names** (`mapFVars`), the front door's relabelling, commutes with transitions (`LStep.renameFree`): a
renamed process performs the renamed action to the renamed target. A call's body has no free name of its own, so
calls commute with renaming. An injective renaming also reflects transitions (`LStep.renameFree_inv`), so it keeps
strong bisimilarity (`bisimilar_mapFVars`).

**Milner's relabelling operator** `P[f]` (`RelabelStep`) performs `f α` when `P` performs `α`, to `P'[f]`. It agrees
with renaming free names when the relabelling is injective (`relabel_agrees`): the relabelled process and the renamed
process match each other's transitions, to the relabelled and the renamed targets. Without injectivity they differ
(`relabel_not_renaming`): `(a.0 | ~b.0)[c/a, c/b]` has no silent transition, since `a.0 | ~b.0` has none, while its
renaming `c.0 | ~c.0` synchronizes. Relabelling does not distribute over parallel composition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList_eq_map mapFVars)
open Mettapedia.OSLF.MeTTaIL.ContextSubstitution (Assignment substitute lift substituteList_eq_map)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {definitions : List Definition}

/-! ## Renaming free names -/

section MapFVars

variable (relabel : String → String)

@[simp] theorem mapFVars_bvar' (index : Nat) : mapFVars relabel (.bvar index) = .bvar index := by
  simp [mapFVars]

@[simp] theorem mapFVars_fvar' (name : String) : mapFVars relabel (.fvar name) = .fvar (relabel name) := by
  simp [mapFVars]

@[simp] theorem mapFVars_apply' (label : String) (arguments : List Pattern) :
    mapFVars relabel (.apply label arguments) = .apply label (arguments.map (mapFVars relabel)) := by
  simp [mapFVars]

@[simp] theorem mapFVars_lambda' (binder : Option String) (body : Pattern) :
    mapFVars relabel (.lambda binder body) = .lambda binder (mapFVars relabel body) := by
  simp [mapFVars]

@[simp] theorem mapFVars_collection' (kind : CollType) (elements : List Pattern) (rest : Option String) :
    mapFVars relabel (.collection kind elements rest) = .collection kind (elements.map (mapFVars relabel)) rest := by
  simp [mapFVars]

end MapFVars

theorem mapFVars_liftBVars (relabel : String → String) : ∀ (pattern : Pattern) (cutoff shift : Nat),
    mapFVars relabel (liftBVars cutoff shift pattern) = liftBVars cutoff shift (mapFVars relabel pattern) := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro cutoff shift
      simp only [liftBVars]
      split <;> simp [liftBVars, *]
  | hfvar name => intro _ _; simp [liftBVars]
  | happly label arguments recurse =>
      intro cutoff shift
      simp only [liftBVars, liftBVarsList_eq_map, mapFVars_apply', List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => recurse argument member cutoff shift
  | hlambda binder body recurse =>
      intro cutoff shift
      simp only [liftBVars, mapFVars_lambda']
      rw [recurse]
  | hmultiLambda arity binders body recurse =>
      intro cutoff shift
      simp only [liftBVars, mapFVars]
      rw [recurse]
  | hsubst body replacement recurseBody recurseReplacement =>
      intro cutoff shift
      simp only [liftBVars, mapFVars]
      rw [recurseBody, recurseReplacement]
  | hcollection kind elements rest recurse =>
      intro cutoff shift
      simp only [liftBVars, liftBVarsList_eq_map, mapFVars_collection', List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member cutoff shift

theorem mapFVars_lift (relabel : String → String) (arity : Nat) (assignment : Assignment) :
    (fun index => mapFVars relabel (lift arity assignment index)) =
      lift arity (fun index => mapFVars relabel (assignment index)) := by
  funext index
  unfold lift
  split
  · simp
  · rw [mapFVars_liftBVars]

/-- **Renaming free names commutes with substitution.** -/
theorem mapFVars_substitute (relabel : String → String) : ∀ (pattern : Pattern) (assignment : Assignment),
    mapFVars relabel (substitute assignment pattern) =
      substitute (fun index => mapFVars relabel (assignment index)) (mapFVars relabel pattern) := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro assignment; simp [substitute]
  | hfvar name => intro assignment; simp [substitute]
  | happly label arguments recurse =>
      intro assignment
      simp only [substitute, substituteList_eq_map, mapFVars_apply', List.map_map]
      congr 1
      exact List.map_congr_left fun argument member => recurse argument member assignment
  | hlambda binder body recurse =>
      intro assignment
      simp only [substitute, mapFVars_lambda']
      rw [recurse, mapFVars_lift]
  | hmultiLambda arity binders body recurse =>
      intro assignment
      simp only [substitute, mapFVars]
      rw [recurse, mapFVars_lift]
  | hsubst body replacement recurseBody recurseReplacement =>
      intro assignment
      simp only [substitute, mapFVars]
      rw [recurseBody, recurseReplacement, mapFVars_lift]
  | hcollection kind elements rest recurse =>
      intro assignment
      simp only [substitute, substituteList_eq_map, mapFVars_collection', List.map_map]
      congr 1
      exact List.map_congr_left fun element member => recurse element member assignment

/-- A pattern with no free name is its own renaming. -/
theorem mapFVars_of_no_names (relabel : String → String) : ∀ (pattern : Pattern),
    (∀ name, name ∉ pattern.freeFvarNames) → mapFVars relabel pattern = pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro _; simp
  | hfvar name => intro absent; exact absurd (by simp [Pattern.freeFvarNames]) (absent name)
  | happly label arguments recurse =>
      intro absent
      simp only [mapFVars_apply']
      congr 1
      conv_rhs => rw [← List.map_id arguments]
      exact List.map_congr_left fun argument member => recurse argument member fun name inArgument =>
        absent name (mem_names_apply.mpr ⟨argument, member, inArgument⟩)
  | hlambda binder body recurse =>
      intro absent
      simp only [mapFVars_lambda']
      rw [recurse fun name inBody => absent name (by simpa [Pattern.freeFvarNames] using inBody)]
  | hmultiLambda arity binders body recurse =>
      intro absent
      simp only [mapFVars]
      rw [recurse fun name inBody => absent name (by simpa [Pattern.freeFvarNames] using inBody)]
  | hsubst body replacement recurseBody recurseReplacement =>
      intro absent
      simp only [mapFVars]
      rw [recurseBody fun name inBody => absent name (by simp [Pattern.freeFvarNames, inBody]),
        recurseReplacement fun name inReplacement => absent name (by simp [Pattern.freeFvarNames, inReplacement])]
  | hcollection kind elements rest recurse =>
      intro absent
      simp only [mapFVars_collection']
      congr 1
      conv_rhs => rw [← List.map_id elements]
      exact List.map_congr_left fun element member => recurse element member fun name inElement =>
        absent name (mem_names_bag.mpr (.inl ⟨element, member, inElement⟩))

theorem mapFVars_constant (relabel : String → String) : ∀ index, mapFVars relabel (constant index) = constant index
  | 0 => by simp [constant]
  | index + 1 => by simp [constant, mapFVars_constant relabel index]

theorem mapFVars_arguments (relabel : String → String) : ∀ names : List Pattern,
    mapFVars relabel (arguments names) = arguments (names.map (mapFVars relabel))
  | [] => by simp [arguments]
  | first :: others => by simp [arguments, mapFVars_arguments relabel others]

/-- **The calls of admitted definitions commute with renaming free names.** -/
theorem instantiate_mapFVars (admitted : admits definitions = true) {definition : Definition}
    (member : definition ∈ definitions) (relabel : String → String) (names : List Pattern) :
    definition.instantiate (names.map (mapFVars relabel)) = (definition.instantiate names).map (mapFVars relabel) := by
  simp only [Definition.instantiate, List.map_map]
  apply List.map_congr_left
  intro guard guardMember
  obtain ⟨guardTyped, guardObject⟩ := guard_admitted admitted member guardMember
  have noNames : ∀ name, name ∉ guard.freeFvarNames := by
    intro name inGuard
    obtain ⟨_, assigned⟩ := guardTyped.freeType_of_mem_freeFvarNames_of_isObjectPattern guardObject inGuard
    simp [noFreeNames] at assigned
  simp only [Function.comp_apply, mapFVars_substitute, mapFVars_of_no_names relabel guard noNames]
  congr 1
  funext index
  simp only [argumentAssignment]
  by_cases inside : index < names.length
  · rw [List.getD_eq_getElem _ _ inside, List.getD_eq_getElem _ _ (by simpa using inside)]
    simp
  · have outside : names.length ≤ index := by omega
    have outside' : (names.map (mapFVars relabel)).length ≤ index := by simpa using outside
    rw [List.getD_eq_default _ _ outside, List.getD_eq_default _ _ outside']
    simp

/-- **What a renamed component offers is renamed.** -/
theorem offers_mapFVars (admitted : admits definitions = true) (relabel : String → String) {component : Pattern}
    {guards : List Pattern} (offered : offers definitions component = some guards) :
    offers definitions (mapFVars relabel component) = some (guards.map (mapFVars relabel)) := by
  rcases offers_cases offered with ⟨tail, rfl⟩ | ⟨name, args, rfl, found⟩
  · simp [offers]
  · obtain ⟨definition, names, lookupFound, namesFound, rfl⟩ := body_some found
    obtain ⟨rfl, length⟩ := arguments_of_argumentsOf namesFound
    obtain ⟨index, rfl⟩ := lookup_constant lookupFound
    simp only [mapFVars_apply', List.map_cons, List.map_nil, mapFVars_constant, mapFVars_arguments, offers, body,
      lookupFound, Option.bind_some]
    rw [show definition.arity = (names.map (mapFVars relabel)).length by simp [length], argumentsOf_arguments]
    simp [instantiate_mapFVars admitted (lookup_mem lookupFound) relabel names]

/-- An action with its name renamed. -/
def Action.mapNames (relabel : String → String) : Action → Action
  | .act name => .act (mapFVars relabel name)
  | .coact name => .coact (mapFVars relabel name)
  | .tau => .tau

theorem guardAction_mapFVars (relabel : String → String) {guard continuation : Pattern} {action : Action}
    (performs : guardAction guard = some (action, continuation)) :
    guardAction (mapFVars relabel guard) = some (action.mapNames relabel, mapFVars relabel continuation) := by
  rcases guardAction_some performs with ⟨name, rfl, rfl⟩ | ⟨name, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [guardAction, Action.mapNames]

theorem lowerName?_mapFVars (relabel : String → String) {name name' : Pattern} (seen : lowerName? name = some name') :
    lowerName? (mapFVars relabel name) = some (mapFVars relabel name') := by
  match name, seen with
  | .bvar (_ + 1), seen =>
      simp only [lowerName?, Option.some.injEq] at seen
      subst seen
      simp [lowerName?]
  | .fvar _, seen =>
      simp only [lowerName?, Option.some.injEq] at seen
      subst seen
      simp [lowerName?]

theorem lower?_mapNames (relabel : String → String) {action action' : Action} (seen : action.lower? = some action') :
    (action.mapNames relabel).lower? = some (action'.mapNames relabel) := by
  cases action with
  | act name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      simp [Action.mapNames, Action.lower?, lowerName?_mapFVars relabel found]
  | coact name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      simp [Action.mapNames, Action.lower?, lowerName?_mapFVars relabel found]
  | tau =>
      simp only [Action.lower?, Option.some.injEq] at seen
      subst seen
      rfl

/-- **A process with its free names renamed performs the renamed action, to the renamed target.** -/
theorem LStep.renameFree (admitted : admits definitions = true) (relabel : String → String) {source : Pattern}
    {action : Action} {target : Pattern} (step : LStep definitions source action target) :
    LStep definitions (mapFVars relabel source) (action.mapNames relabel) (mapFVars relabel target) := by
  induction step with
  | offer offered k hk performs =>
      exact .offer (offers_mapFVars admitted relabel offered) k (by simpa using hk)
        (by simpa using guardAction_mapFVars relabel performs)
  | @par elements tail i hi action target inner recurse =>
      rw [mapFVars_collection', mapFVars_collection', List.map_cons, ← List.eraseIdx_map]
      exact .par i (by simpa using hi) (by simpa using recurse)
  | @sync elements tail i hi j hj name target target' first second firstRecurse secondRecurse =>
      rw [mapFVars_collection', mapFVars_collection', List.map_cons, List.map_cons, ← List.eraseIdx_map,
        ← List.eraseIdx_map]
      exact .sync i (by simpa using hi) j (by simpa [List.length_eraseIdx] using hj)
        (by simpa [Action.mapNames] using firstRecurse)
        (by simpa [Action.mapNames, List.eraseIdx_map] using secondRecurse)
  | res binder inner seen recurse =>
      simp only [mapFVars_apply', List.map_cons, List.map_nil, mapFVars_lambda']
      exact .res binder recurse (lower?_mapNames relabel seen)

/-! ## Inverting a renaming of free names -/

theorem mapFVars_eq_apply {relabel : String → String} {pattern : Pattern} {label : String}
    {arguments' : List Pattern} (renamed : mapFVars relabel pattern = .apply label arguments') :
    ∃ arguments, pattern = .apply label arguments ∧ arguments' = arguments.map (mapFVars relabel) := by
  cases pattern with
  | apply label' arguments =>
      simp only [mapFVars_apply', Pattern.apply.injEq] at renamed
      obtain ⟨rfl, rfl⟩ := renamed
      exact ⟨arguments, rfl, rfl⟩
  | _ => simp [mapFVars] at renamed

theorem mapFVars_eq_collection {relabel : String → String} {pattern : Pattern} {kind : CollType}
    {elements' : List Pattern} {tail : Option String}
    (renamed : mapFVars relabel pattern = .collection kind elements' tail) :
    ∃ elements, pattern = .collection kind elements tail ∧ elements' = elements.map (mapFVars relabel) := by
  cases pattern with
  | collection kind' elements tail' =>
      simp only [mapFVars_collection', Pattern.collection.injEq] at renamed
      obtain ⟨rfl, rfl, rfl⟩ := renamed
      exact ⟨elements, rfl, rfl⟩
  | _ => simp [mapFVars] at renamed

theorem mapFVars_eq_lambda {relabel : String → String} {pattern : Pattern} {binder : Option String}
    {body' : Pattern} (renamed : mapFVars relabel pattern = .lambda binder body') :
    ∃ body, pattern = .lambda binder body ∧ body' = mapFVars relabel body := by
  cases pattern with
  | lambda binder' body =>
      simp only [mapFVars_lambda', Pattern.lambda.injEq] at renamed
      obtain ⟨rfl, rfl⟩ := renamed
      exact ⟨body, rfl, rfl⟩
  | _ => simp [mapFVars] at renamed

theorem mapFVars_eq_constant {relabel : String → String} : ∀ {index : Nat} {pattern : Pattern},
    mapFVars relabel pattern = constant index → pattern = constant index
  | 0, pattern, renamed => by
      obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply renamed
      cases arguments with
      | nil => rfl
      | cons => simp at mapped
  | index + 1, pattern, renamed => by
      obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply renamed
      match arguments, mapped with
      | [inner], mapped =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
          rw [mapFVars_eq_constant mapped.symm]
          rfl
      | [], mapped | _ :: _ :: _, mapped => simp at mapped

theorem mapFVars_eq_arguments {relabel : String → String} : ∀ {names' : List Pattern} {pattern : Pattern},
    mapFVars relabel pattern = arguments names' →
      ∃ names, pattern = arguments names ∧ names' = names.map (mapFVars relabel)
  | [], pattern, renamed => by
      obtain ⟨arguments', rfl, mapped⟩ := mapFVars_eq_apply renamed
      cases arguments' with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons => simp at mapped
  | name' :: names', pattern, renamed => by
      obtain ⟨arguments', rfl, mapped⟩ := mapFVars_eq_apply renamed
      match arguments', mapped with
      | [name, rest], mapped =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
          obtain ⟨rfl, restIs⟩ := mapped
          obtain ⟨names, rfl, rfl⟩ := mapFVars_eq_arguments restIs.symm
          exact ⟨name :: names, rfl, rfl⟩
      | [], mapped | [_], mapped | _ :: _ :: _ :: _, mapped => simp at mapped

/-- **What a renamed component offers is the renaming of what it offers.** -/
theorem offers_mapFVars_inv (admitted : admits definitions = true) (relabel : String → String) {component : Pattern}
    {guards' : List Pattern} (offered : offers definitions (mapFVars relabel component) = some guards') :
    ∃ guards, offers definitions component = some guards ∧ guards' = guards.map (mapFVars relabel) := by
  rcases offers_cases offered with ⟨tail, componentIs⟩ | ⟨name', args', componentIs, found⟩
  · obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply componentIs
    match arguments, mapped with
    | [guardsBag], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        obtain ⟨guards, rfl, rfl⟩ := mapFVars_eq_collection mapped.symm
        exact ⟨guards, rfl, rfl⟩
    | [], mapped | _ :: _ :: _, mapped => simp at mapped
  · obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply componentIs
    match arguments, mapped with
    | [name, args], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        obtain ⟨nameIs, argsIs⟩ := mapped
        obtain ⟨definition, names', lookupFound, namesFound, rfl⟩ := body_some found
        obtain ⟨index, rfl⟩ := lookup_constant lookupFound
        obtain ⟨argsShape, length⟩ := arguments_of_argumentsOf namesFound
        rw [argsShape] at argsIs
        obtain ⟨names, rfl, rfl⟩ := mapFVars_eq_arguments argsIs.symm
        rw [mapFVars_eq_constant nameIs.symm]
        refine ⟨definition.instantiate names, ?_, ?_⟩
        · simp only [offers, body, lookupFound, Option.bind_some]
          rw [show definition.arity = names.length by simpa using length.symm, argumentsOf_arguments]
          rfl
        · exact instantiate_mapFVars admitted (lookup_mem lookupFound) relabel names
    | [], mapped | [_], mapped | _ :: _ :: _ :: _, mapped => simp at mapped

theorem guardAction_mapFVars_inv {relabel : String → String} {guard continuation' : Pattern} {action' : Action}
    (performs : guardAction (mapFVars relabel guard) = some (action', continuation')) :
    ∃ action continuation, guardAction guard = some (action, continuation) ∧ action' = action.mapNames relabel ∧
      continuation' = mapFVars relabel continuation := by
  rcases guardAction_some performs with ⟨name', rfl, guardIs⟩ | ⟨name', rfl, guardIs⟩ | ⟨rfl, guardIs⟩
  · obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply guardIs
    match arguments, mapped with
    | [name, continuation], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        obtain ⟨rfl, rfl⟩ := mapped
        exact ⟨.act name, continuation, rfl, rfl, rfl⟩
    | [], mapped | [_], mapped | _ :: _ :: _ :: _, mapped => simp at mapped
  · obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply guardIs
    match arguments, mapped with
    | [name, continuation], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        obtain ⟨rfl, rfl⟩ := mapped
        exact ⟨.coact name, continuation, rfl, rfl, rfl⟩
    | [], mapped | [_], mapped | _ :: _ :: _ :: _, mapped => simp at mapped
  · obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply guardIs
    match arguments, mapped with
    | [continuation], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        subst mapped
        exact ⟨.tau, continuation, rfl, rfl, rfl⟩
    | [], mapped | _ :: _ :: _, mapped => simp at mapped

theorem map_eq_map_of_injOn {mapping : Pattern → Pattern} : ∀ {first second : List Pattern},
    (∀ element ∈ first, ∀ other, mapping element = mapping other → element = other) →
    first.map mapping = second.map mapping → first = second
  | [], [], _, _ => rfl
  | [], _ :: _, _, same => by simp at same
  | _ :: _, [], _, same => by simp at same
  | element :: first, other :: second, injective, same => by
      simp only [List.map_cons, List.cons.injEq] at same
      rw [injective element List.mem_cons_self other same.1,
        map_eq_map_of_injOn (fun inner member => injective inner (List.mem_cons_of_mem _ member)) same.2]

/-- An injective renaming of free names is injective on patterns. -/
theorem mapFVars_injective {relabel : String → String} (injective : Function.Injective relabel) :
    Function.Injective (mapFVars relabel) := by
  intro first
  induction first using Pattern.inductionOn with
  | hbvar index =>
      intro second same
      cases second <;> simp_all [mapFVars]
  | hfvar name =>
      intro second same
      cases second <;> simp_all [mapFVars]
      exact injective same
  | happly label arguments recurse =>
      intro second same
      rw [mapFVars_apply'] at same
      obtain ⟨arguments', rfl, mapped⟩ := mapFVars_eq_apply same.symm
      rw [map_eq_map_of_injOn recurse mapped]
  | hlambda binder body recurse =>
      intro second same
      rw [mapFVars_lambda'] at same
      obtain ⟨body', rfl, mapped⟩ := mapFVars_eq_lambda same.symm
      rw [recurse mapped]
  | hmultiLambda arity binders body recurse =>
      intro second same
      cases second <;> simp only [mapFVars, reduceCtorEq, Pattern.multiLambda.injEq] at same
      obtain ⟨rfl, rfl, mapped⟩ := same
      rw [recurse mapped]
  | hsubst body replacement recurseBody recurseReplacement =>
      intro second same
      cases second <;> simp only [mapFVars, reduceCtorEq, Pattern.subst.injEq] at same
      rw [recurseBody same.1, recurseReplacement same.2]
  | hcollection kind elements rest recurse =>
      intro second same
      rw [mapFVars_collection'] at same
      obtain ⟨elements', rfl, mapped⟩ := mapFVars_eq_collection same.symm
      rw [map_eq_map_of_injOn recurse mapped]

theorem lower?_mapNames_inv {relabel : String → String} {action : Action} {action'' : Action}
    (seen : (action.mapNames relabel).lower? = some action'') :
    ∃ action', action.lower? = some action' ∧ action'' = action'.mapNames relabel := by
  have lowered : ∀ {name name'' : Pattern}, lowerName? (mapFVars relabel name) = some name'' →
      ∃ name', lowerName? name = some name' ∧ name'' = mapFVars relabel name' := by
    intro name name'' found
    cases name with
    | bvar index =>
        cases index with
        | zero => simp [lowerName?] at found
        | succ index =>
            simp only [mapFVars_bvar', lowerName?, Option.some.injEq] at found
            subst found
            exact ⟨.bvar index, rfl, by simp⟩
    | fvar held =>
        simp only [mapFVars_fvar', lowerName?, Option.some.injEq] at found
        subst found
        exact ⟨.fvar held, rfl, by simp⟩
    | _ => simp [mapFVars, lowerName?] at found
  cases action with
  | act name =>
      obtain ⟨name'', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      obtain ⟨name', found', rfl⟩ := lowered found
      exact ⟨.act name', by simp [Action.lower?, found'], rfl⟩
  | coact name =>
      obtain ⟨name'', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      obtain ⟨name', found', rfl⟩ := lowered found
      exact ⟨.coact name', by simp [Action.lower?, found'], rfl⟩
  | tau =>
      simp only [Action.mapNames, Action.lower?, Option.some.injEq] at seen
      subst seen
      exact ⟨.tau, rfl, rfl⟩

/-- **An injective renaming of free names reflects transitions**: what a renamed process performs is the renaming of
what the process performs. -/
theorem LStep.renameFree_inv (admitted : admits definitions = true) {relabel : String → String}
    (injective : Function.Injective relabel) {source' : Pattern} {action' : Action} {target' : Pattern}
    (step : LStep definitions source' action' target') :
    ∀ {source : Pattern}, mapFVars relabel source = source' →
      ∃ action target, LStep definitions source action target ∧ action' = action.mapNames relabel ∧
        target' = mapFVars relabel target := by
  induction step with
  | @offer component' guards' offered k hk action' continuation' performs =>
      intro source renamed
      subst renamed
      obtain ⟨guards, offeredIs, rfl⟩ := offers_mapFVars_inv admitted relabel offered
      have performsIs : guardAction (mapFVars relabel (guards[k]'(by simpa using hk))) =
          some (action', continuation') := by simpa using performs
      obtain ⟨action, continuation, performs', rfl, rfl⟩ := guardAction_mapFVars_inv performsIs
      exact ⟨action, continuation, .offer offeredIs k (by simpa using hk) performs', rfl, rfl⟩
  | @par elements' tail i hi action' target' inner recurse =>
      intro source renamed
      obtain ⟨elements, rfl, rfl⟩ := mapFVars_eq_collection renamed
      have inside : i < elements.length := by simpa using hi
      obtain ⟨action, target, step, rfl, rfl⟩ := recurse (source := elements[i]) (by simp)
      refine ⟨action, .collection .hashBag (target :: elements.eraseIdx i) none, .par i inside step, rfl, ?_⟩
      rw [mapFVars_collection', List.map_cons, List.eraseIdx_map]
  | @sync elements' tail i hi j hj name' target' target'' first second firstRecurse secondRecurse =>
      intro source renamed
      obtain ⟨elements, rfl, rfl⟩ := mapFVars_eq_collection renamed
      have inside : i < elements.length := by simpa using hi
      have inside' : j < (elements.eraseIdx i).length := by simpa [List.eraseIdx_map] using hj
      obtain ⟨action, target, step, actionIs, rfl⟩ := firstRecurse (source := elements[i]) (by simp)
      obtain ⟨action₂, target₂, step₂, actionIs₂, rfl⟩ := secondRecurse
        (source := (elements.eraseIdx i)[j]) (by simp [List.eraseIdx_map])
      cases action with
      | act name =>
          cases action₂ with
          | coact name₂ =>
              simp only [Action.mapNames, Action.act.injEq, Action.coact.injEq] at actionIs actionIs₂
              subst actionIs
              have same := mapFVars_injective injective actionIs₂
              subst same
              refine ⟨.tau, .collection .hashBag (target :: target₂ :: (elements.eraseIdx i).eraseIdx j) none,
                .sync i inside j inside' step step₂, rfl, ?_⟩
              rw [mapFVars_collection', List.map_cons, List.map_cons, List.eraseIdx_map, List.eraseIdx_map]
          | act => simp [Action.mapNames] at actionIs₂
          | tau => simp [Action.mapNames] at actionIs₂
      | coact => simp [Action.mapNames] at actionIs
      | tau => simp [Action.mapNames] at actionIs
  | @res binder source' target' action' action'' inner seen recurse =>
      intro source renamed
      obtain ⟨arguments, rfl, mapped⟩ := mapFVars_eq_apply renamed
      match arguments, mapped with
      | [argument], mapped =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
          obtain ⟨body, rfl, rfl⟩ := mapFVars_eq_lambda mapped.symm
          obtain ⟨action, target, step, rfl, rfl⟩ := recurse (source := body) rfl
          obtain ⟨action₀, lowered, rfl⟩ := lower?_mapNames_inv seen
          exact ⟨action₀, .apply "CNu" [.lambda none target], .res binder step lowered, rfl, by simp⟩
      | [], mapped | _ :: _ :: _, mapped => simp at mapped

/-- **An injective renaming of free names keeps strong bisimilarity.** -/
theorem bisimilar_mapFVars (admitted : admits definitions = true) {relabel : String → String}
    (injective : Function.Injective relabel) {first second : Pattern} (bisimilar : Bisimilar definitions first second) :
    Bisimilar definitions (mapFVars relabel first) (mapFVars relabel second) := by
  refine ⟨fun left right => ∃ left₀ right₀, left = mapFVars relabel left₀ ∧ right = mapFVars relabel right₀ ∧
      Bisimilar definitions left₀ right₀, ?_, first, second, rfl, rfl, bisimilar⟩
  rintro _ _ ⟨left₀, right₀, rfl, rfl, related⟩
  constructor
  · intro action target step
    obtain ⟨action₀, target₀, step₀, rfl, rfl⟩ := step.renameFree_inv admitted injective rfl
    obtain ⟨target₀', step₀', related'⟩ := related.forth step₀
    exact ⟨_, step₀'.renameFree admitted relabel, target₀, target₀', rfl, rfl, related'⟩
  · intro action target step
    obtain ⟨action₀, target₀, step₀, rfl, rfl⟩ := step.renameFree_inv admitted injective rfl
    obtain ⟨target₀', step₀', related'⟩ := related.symm.forth step₀
    exact ⟨_, step₀'.renameFree admitted relabel, target₀', target₀, rfl, rfl, related'.symm⟩

/-! ## Milner's relabelling operator -/

/-- **The relabelling operator** `P[f]`: it performs `f α` when `P` performs `α`, to `P'[f]`. The states are the
relabelled processes `P`, and the transitions those of `P[f]`. -/
inductive RelabelStep (definitions : List Definition) (relabel : String → String) :
    Pattern → Action → Pattern → Prop where
  | relabel {source : Pattern} {action : Action} {target : Pattern} (step : LStep definitions source action target) :
      RelabelStep definitions relabel source (action.mapNames relabel) target

/-- **The relabelling operator agrees with renaming free names, for an injective relabelling**: `P[f]` and the
renaming of `P` match each other's transitions, to the relabelled and the renamed targets. -/
theorem relabel_agrees (admitted : admits definitions = true) {relabel : String → String} (process : Pattern) :
    (∀ {action target}, RelabelStep definitions relabel process action target →
      LStep definitions (mapFVars relabel process) action (mapFVars relabel target)) ∧
    (Function.Injective relabel → ∀ {action target'}, LStep definitions (mapFVars relabel process) action target' →
      ∃ target, RelabelStep definitions relabel process action target ∧ target' = mapFVars relabel target) := by
  constructor
  · intro action target step
    cases step with
    | relabel step => exact step.renameFree admitted relabel
  · intro injective action target' step
    obtain ⟨action₀, target, step₀, rfl, rfl⟩ := step.renameFree_inv admitted injective rfl
    exact ⟨target, .relabel step₀, rfl⟩

/-- `a.0 | ~b.0`. -/
def apart : Pattern :=
  .collection .hashBag [.apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar "a", .apply "CNil" []]] none],
    .apply "CSum" [.collection .hashBag [.apply "CCoAct" [.fvar "b", .apply "CNil" []]] none]] none

/-- `[c/a, c/b]`. -/
def merge (name : String) : String := if name = "a" ∨ name = "b" then "c" else name

/-- A sum of one summand performs it. -/
theorem single_sum_step {guard : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions (.apply "CSum" [.collection .hashBag [guard] none]) action target) :
    guardAction guard = some (action, target) := by
  obtain ⟨k, hk, performs⟩ := lstep_sum_inv step
  match k, hk, performs with
  | 0, _, performs => simpa using performs

/-- **Relabelling is not renaming without injectivity**: `(a.0 | ~b.0)[c/a, c/b]` has no silent transition, while
its renaming `c.0 | ~c.0` synchronizes. -/
theorem relabel_not_renaming :
    (∀ target, ¬ RelabelStep definitions merge apart .tau target) ∧
      LStep definitions (mapFVars merge apart) .tau
        (.collection .hashBag [.apply "CNil" [], .apply "CNil" []] none) := by
  constructor
  · intro target step
    generalize tauIs : Action.tau = action at step
    cases step with
    | relabel step =>
        rename_i action₀
        have silent : action₀ = .tau := by cases action₀ <;> simp_all [Action.mapNames]
        subst silent
        unfold apart at step
        obtain ⟨result, move, -⟩ := bagMove_of_step step
        rcases move.result_cases with ⟨member, rest, moved, perm, memberStep, -⟩ |
          ⟨first, second, rest, moved, moved', name, perm, firstStep, secondStep, -, -⟩
        · have inApart := perm.mem_iff.mpr List.mem_cons_self
          simp only [List.mem_cons, List.not_mem_nil, or_false] at inApart
          rcases inApart with rfl | rfl
          · have performs := single_sum_step memberStep
            simp [guardAction] at performs
          · have performs := single_sum_step memberStep
            simp [guardAction] at performs
        · have firstIn := perm.mem_iff.mpr List.mem_cons_self
          have secondIn := perm.mem_iff.mpr (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at firstIn secondIn
          rcases firstIn with rfl | rfl <;> rcases secondIn with rfl | rfl
          · have performs' := single_sum_step secondStep
            simp [guardAction] at performs'
          · have performs := single_sum_step firstStep
            have performs' := single_sum_step secondStep
            simp only [guardAction, Option.some.injEq, Prod.mk.injEq, Action.act.injEq, Action.coact.injEq]
              at performs performs'
            have same := performs.1.trans performs'.1.symm
            simp at same
          · have performs := single_sum_step firstStep
            simp [guardAction] at performs
          · have performs := single_sum_step firstStep
            simp [guardAction] at performs
  · have computed : mapFVars merge apart = .collection .hashBag
        [.apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar "c", .apply "CNil" []]] none],
          .apply "CSum" [.collection .hashBag [.apply "CCoAct" [.fvar "c", .apply "CNil" []]] none]] none := by
      simp [apart, merge]
    rw [computed]
    exact .sync 0 (by simp) 0 (by simp) (.offer rfl 0 (by simp) rfl) (.offer rfl 0 (by simp) rfl)

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
