import Mettapedia.Languages.ProcessCalculi.CCS.Labelled
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationShapes

/-!
# Labelled transitions under renaming, and their typing

The labelled transitions of CCS with recursion commute with renaming bound variables (`LStep.rename`): a renamed
process performs the renamed action to the renamed target. Calls of admitted definitions commute with renaming, since
a body's only names are its parameters. An injective renaming also reflects transitions (`LStep.rename_inv`): what a
renamed process performs is the renaming of what the process performs. So lifting past restrictions keeps and reflects
transitions, which scope extrusion needs.

Transitions keep typed object processes typed object processes (`LStep.typed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (liftIndex)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

variable {definitions : List Definition}

/-! ## Actions under renaming -/

/-- Rename an action's name. -/
def Action.rename (relabel : Nat → Nat) : Action → Action
  | .act name => .act (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel name)
  | .coact name => .coact (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel name)
  | .tau => .tau

theorem guardAction_rename (relabel : Nat → Nat) {guard continuation : Pattern} {action : Action}
    (performs : guardAction guard = some (action, continuation)) :
    guardAction (rename relabel guard) = some (action.rename relabel, rename relabel continuation) := by
  rcases guardAction_some performs with ⟨name, rfl, rfl⟩ | ⟨name, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [rename_apply, guardAction, Action.rename]

theorem guardAction_rename_inv {relabel : Nat → Nat} {guard continuation' : Pattern} {action' : Action}
    (performs : guardAction (rename relabel guard) = some (action', continuation')) :
    ∃ action continuation, guardAction guard = some (action, continuation) ∧ action' = action.rename relabel ∧
      continuation' = rename relabel continuation := by
  rcases guardAction_some performs with ⟨name', rfl, guardIs⟩ | ⟨name', rfl, guardIs⟩ | ⟨rfl, guardIs⟩ <;>
    · cases guard with
      | apply label arguments =>
          rw [rename_apply] at guardIs
          simp only [Pattern.apply.injEq] at guardIs
          obtain ⟨rfl, mapped⟩ := guardIs
          first
            | (obtain ⟨name, continuation, rfl⟩ : ∃ name continuation, arguments = [name, continuation] := by
                match arguments, mapped with
                | [name, continuation], _ => exact ⟨name, continuation, rfl⟩)
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
              obtain ⟨rfl, rfl⟩ := mapped
              exact ⟨_, continuation, rfl, rfl, rfl⟩
            | (obtain ⟨continuation, rfl⟩ : ∃ continuation, arguments = [continuation] := by
                match arguments, mapped with
                | [continuation], _ => exact ⟨continuation, rfl⟩)
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
              subst mapped
              exact ⟨_, continuation, rfl, rfl, rfl⟩
      | bvar => simp [rename_bvar] at guardIs
      | fvar => simp [rename_fvar] at guardIs
      | lambda => simp [rename_lambda] at guardIs
      | multiLambda => simp [rename_multiLambda] at guardIs
      | subst => simp [rename_subst] at guardIs
      | collection => simp [rename_collection] at guardIs

/-- Lowering a lifted renaming's action is renaming the lowered action. -/
theorem lower?_rename {relabel : Nat → Nat} {action action' : Action} (seen : action.lower? = some action') :
    (action.rename (liftIndex 1 relabel)).lower? = some (action'.rename relabel) := by
  have lowered : ∀ {name name' : Pattern}, lowerName? name = some name' →
      lowerName? (rename (liftIndex 1 relabel) name) = some (rename relabel name') := by
    intro name name' found
    match name, found with
    | .bvar (index + 1), found =>
        simp only [lowerName?, Option.some.injEq] at found
        subst found
        simp [rename_bvar, liftIndex, lowerName?]
    | .fvar held, found =>
        simp only [lowerName?, Option.some.injEq] at found
        subst found
        simp [rename_fvar, lowerName?]
  cases action with
  | act name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      simp [Action.rename, Action.lower?, lowered found]
  | coact name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      simp [Action.rename, Action.lower?, lowered found]
  | tau =>
      simp only [Action.lower?, Option.some.injEq] at seen
      subst seen
      rfl

/-- What a lifted renaming's action lowers to is the renaming of a lowered action, for an injective renaming. -/
theorem lower?_rename_inv {relabel : Nat → Nat} {action : Action} {action'' : Action}
    (seen : (action.rename (liftIndex 1 relabel)).lower? = some action'') :
    ∃ action', action.lower? = some action' ∧ action'' = action'.rename relabel := by
  have lowered : ∀ {name name'' : Pattern}, lowerName? (rename (liftIndex 1 relabel) name) = some name'' →
      ∃ name', lowerName? name = some name' ∧ name'' = rename relabel name' := by
    intro name name'' found
    cases name with
    | bvar index =>
        cases index with
        | zero => simp [rename_bvar, liftIndex, lowerName?] at found
        | succ index =>
            simp only [rename_bvar, liftIndex, lowerName?] at found
            simp only [Nat.add_sub_cancel] at found
            split_ifs at found with small
            · omega
            · simp only [Option.some.injEq] at found
              subst found
              exact ⟨.bvar index, rfl, by simp [rename_bvar]⟩
    | fvar held =>
        simp only [rename_fvar, lowerName?, Option.some.injEq] at found
        subst found
        exact ⟨.fvar held, rfl, rfl⟩
    | apply => simp [rename_apply, lowerName?] at found
    | lambda => simp [rename_lambda, lowerName?] at found
    | multiLambda => simp [rename_multiLambda, lowerName?] at found
    | subst => simp [rename_subst, lowerName?] at found
    | collection => simp [rename_collection, lowerName?] at found
  cases action with
  | act name =>
      obtain ⟨name'', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      obtain ⟨name', lowerIs, rfl⟩ := lowered found
      exact ⟨.act name', by simp [Action.lower?, lowerIs], rfl⟩
  | coact name =>
      obtain ⟨name'', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      obtain ⟨name', lowerIs, rfl⟩ := lowered found
      exact ⟨.coact name', by simp [Action.lower?, lowerIs], rfl⟩
  | tau =>
      simp only [Action.rename, Action.lower?, Option.some.injEq] at seen
      exact ⟨.tau, rfl, seen.symm⟩

/-! ## Inverting a renaming -/

theorem rename_eq_apply {relabel : Nat → Nat} {pattern : Pattern} {label : String} {arguments' : List Pattern}
    (renamed : rename relabel pattern = .apply label arguments') :
    ∃ arguments, pattern = .apply label arguments ∧ arguments' = arguments.map (rename relabel) := by
  cases pattern with
  | apply label' arguments =>
      rw [rename_apply] at renamed
      simp only [Pattern.apply.injEq] at renamed
      obtain ⟨rfl, rfl⟩ := renamed
      exact ⟨arguments, rfl, rfl⟩
  | bvar => simp [rename_bvar] at renamed
  | fvar => simp [rename_fvar] at renamed
  | lambda => simp [rename_lambda] at renamed
  | multiLambda => simp [rename_multiLambda] at renamed
  | subst => simp [rename_subst] at renamed
  | collection => simp [rename_collection] at renamed

theorem rename_eq_collection {relabel : Nat → Nat} {pattern : Pattern} {kind : CollType} {elements' : List Pattern}
    {tail : Option String} (renamed : rename relabel pattern = .collection kind elements' tail) :
    ∃ elements, pattern = .collection kind elements tail ∧ elements' = elements.map (rename relabel) := by
  cases pattern with
  | collection kind' elements tail' =>
      rw [rename_collection] at renamed
      simp only [Pattern.collection.injEq] at renamed
      obtain ⟨rfl, rfl, rfl⟩ := renamed
      exact ⟨elements, rfl, rfl⟩
  | bvar => simp [rename_bvar] at renamed
  | fvar => simp [rename_fvar] at renamed
  | apply => simp [rename_apply] at renamed
  | lambda => simp [rename_lambda] at renamed
  | multiLambda => simp [rename_multiLambda] at renamed
  | subst => simp [rename_subst] at renamed

theorem rename_eq_lambda {relabel : Nat → Nat} {pattern : Pattern} {binder : Option String} {body' : Pattern}
    (renamed : rename relabel pattern = .lambda binder body') :
    ∃ body, pattern = .lambda binder body ∧ body' = rename (liftIndex 1 relabel) body := by
  cases pattern with
  | lambda binder' body =>
      rw [rename_lambda] at renamed
      simp only [Pattern.lambda.injEq] at renamed
      obtain ⟨rfl, rfl⟩ := renamed
      exact ⟨body, rfl, rfl⟩
  | bvar => simp [rename_bvar] at renamed
  | fvar => simp [rename_fvar] at renamed
  | apply => simp [rename_apply] at renamed
  | multiLambda => simp [rename_multiLambda] at renamed
  | subst => simp [rename_subst] at renamed
  | collection => simp [rename_collection] at renamed

theorem rename_eq_constant {relabel : Nat → Nat} : ∀ {index : Nat} {pattern : Pattern},
    rename relabel pattern = constant index → pattern = constant index
  | 0, pattern, renamed => by
      obtain ⟨arguments, rfl, mapped⟩ := rename_eq_apply renamed
      cases arguments with
      | nil => rfl
      | cons => simp at mapped
  | index + 1, pattern, renamed => by
      obtain ⟨arguments, rfl, mapped⟩ := rename_eq_apply renamed
      match arguments, mapped with
      | [inner], mapped =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
          rw [rename_eq_constant mapped.symm]
          rfl
      | [], mapped | _ :: _ :: _, mapped => simp at mapped

theorem rename_eq_arguments {relabel : Nat → Nat} : ∀ {names' : List Pattern} {pattern : Pattern},
    rename relabel pattern = arguments names' → ∃ names, pattern = arguments names ∧ names' = names.map (rename relabel)
  | [], pattern, renamed => by
      obtain ⟨arguments', rfl, mapped⟩ := rename_eq_apply renamed
      cases arguments' with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons => simp at mapped
  | name' :: names', pattern, renamed => by
      obtain ⟨arguments', rfl, mapped⟩ := rename_eq_apply renamed
      match arguments', mapped with
      | [name, rest], mapped =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
          obtain ⟨rfl, restIs⟩ := mapped
          obtain ⟨names, rfl, rfl⟩ := rename_eq_arguments restIs.symm
          exact ⟨name :: names, rfl, rfl⟩
      | [], mapped | [_], mapped | _ :: _ :: _ :: _, mapped => simp at mapped

/-- **What a renamed component offers is renamed**: an injective renaming reflects offers, for admitted definitions. -/
theorem offers_rename_inv (admitted : admits definitions = true) (relabel : Nat → Nat) {component : Pattern}
    {guards' : List Pattern} (offered : offers definitions (rename relabel component) = some guards') :
    ∃ guards, offers definitions component = some guards ∧ guards' = guards.map (rename relabel) := by
  rcases offers_cases offered with ⟨tail, componentIs⟩ | ⟨name', args', componentIs, found⟩
  · obtain ⟨arguments, rfl, mapped⟩ := rename_eq_apply componentIs
    match arguments, mapped with
    | [guardsBag], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        obtain ⟨guards, rfl, rfl⟩ := rename_eq_collection mapped.symm
        exact ⟨guards, rfl, rfl⟩
    | [], mapped | _ :: _ :: _, mapped => simp at mapped
  · obtain ⟨arguments, rfl, mapped⟩ := rename_eq_apply componentIs
    match arguments, mapped with
    | [name, args], mapped =>
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
        obtain ⟨nameIs, argsIs⟩ := mapped
        obtain ⟨definition, names', lookupFound, namesFound, rfl⟩ := body_some found
        obtain ⟨index, rfl⟩ := lookup_constant lookupFound
        obtain ⟨argsShape, length⟩ := arguments_of_argumentsOf namesFound
        rw [argsShape] at argsIs
        obtain ⟨names, rfl, rfl⟩ := rename_eq_arguments argsIs.symm
        rw [rename_eq_constant nameIs.symm]
        refine ⟨definition.instantiate names, ?_, ?_⟩
        · simp only [offers, body, lookupFound, Option.bind_some]
          rw [show definition.arity = names.length by simpa using length.symm, argumentsOf_arguments]
          rfl
        · exact instantiate_rename admitted (lookup_mem lookupFound) relabel (by simpa using length)
    | [], mapped | [_], mapped | _ :: _ :: _ :: _, mapped => simp at mapped

/-! ## Transitions under renaming -/

/-- **A renamed process performs the renamed action, to the renamed target.** -/
theorem LStep.rename (admitted : admits definitions = true) {source : Pattern} {action : Action} {target : Pattern}
    (step : LStep definitions source action target) :
    ∀ relabel : Nat → Nat, LStep definitions (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel source)
      (action.rename relabel) (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel target) := by
  induction step with
  | offer offered k hk performs =>
      intro relabel
      exact .offer (offers_rename admitted relabel offered) k (by simpa using hk)
        (by simpa using guardAction_rename relabel performs)
  | @par elements tail i hi action target inner recurse =>
      intro relabel
      rw [rename_collection, rename_collection, List.map_cons, ← List.eraseIdx_map]
      exact .par i (by simpa using hi) (by simpa using recurse relabel)
  | @sync elements tail i hi j hj name target target' first second firstRecurse secondRecurse =>
      intro relabel
      rw [rename_collection, rename_collection, List.map_cons, List.map_cons, ← List.eraseIdx_map,
        ← List.eraseIdx_map]
      exact .sync i (by simpa using hi) j (by simpa [List.length_eraseIdx] using hj)
        (by simpa [Action.rename] using firstRecurse relabel)
        (by simpa [Action.rename, List.eraseIdx_map] using secondRecurse relabel)
  | res binder inner seen recurse =>
      intro relabel
      rw [rename_apply, rename_apply]
      simp only [List.map_cons, List.map_nil, rename_lambda]
      exact .res binder (recurse (liftIndex 1 relabel)) (lower?_rename seen)

/-- **An injective renaming reflects transitions**: what a renamed process performs is the renaming of what the
process performs. -/
theorem LStep.rename_inv (admitted : admits definitions = true) {source' : Pattern} {action' : Action}
    {target' : Pattern} (step : LStep definitions source' action' target') :
    ∀ {relabel : Nat → Nat}, Function.Injective relabel → ∀ {source : Pattern},
      Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel source = source' →
      ∃ action target, LStep definitions source action target ∧ action' = action.rename relabel ∧
        target' = Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel target := by
  induction step with
  | @offer component' guards' offered k hk action' continuation' performs =>
      intro relabel _ source renamed
      subst renamed
      obtain ⟨guards, offeredIs, rfl⟩ := offers_rename_inv admitted relabel offered
      have performsIs : guardAction (Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename relabel
          (guards[k]'(by simpa using hk))) = some (action', continuation') := by simpa using performs
      obtain ⟨action, continuation, performs', rfl, rfl⟩ := guardAction_rename_inv performsIs
      exact ⟨action, continuation, .offer offeredIs k (by simpa using hk) performs', rfl, rfl⟩
  | @par elements' tail i hi action' target' inner recurse =>
      intro relabel injective source renamed
      obtain ⟨elements, rfl, rfl⟩ := rename_eq_collection renamed
      have inside : i < elements.length := by simpa using hi
      obtain ⟨action, target, step, rfl, rfl⟩ := recurse injective (source := elements[i]) (by simp)
      refine ⟨action, .collection .hashBag (target :: elements.eraseIdx i) none, .par i inside step, rfl, ?_⟩
      rw [rename_collection, List.map_cons, List.eraseIdx_map]
  | @sync elements' tail i hi j hj name' target' target'' first second firstRecurse secondRecurse =>
      intro relabel injective source renamed
      obtain ⟨elements, rfl, rfl⟩ := rename_eq_collection renamed
      have inside : i < elements.length := by simpa using hi
      have inside' : j < (elements.eraseIdx i).length := by simpa [List.eraseIdx_map] using hj
      obtain ⟨action, target, step, actionIs, rfl⟩ := firstRecurse injective (source := elements[i]) (by simp)
      obtain ⟨action₂, target₂, step₂, actionIs₂, rfl⟩ := secondRecurse injective
        (source := (elements.eraseIdx i)[j]) (by simp [List.eraseIdx_map])
      cases action with
      | act name =>
          cases action₂ with
          | coact name₂ =>
              simp only [Action.rename, Action.act.injEq, Action.coact.injEq] at actionIs actionIs₂
              subst actionIs
              have same := rename_injective injective actionIs₂
              subst same
              refine ⟨.tau, .collection .hashBag (target :: target₂ :: (elements.eraseIdx i).eraseIdx j) none,
                .sync i inside j inside' step step₂, rfl, ?_⟩
              rw [rename_collection, List.map_cons, List.map_cons, List.eraseIdx_map, List.eraseIdx_map]
          | act => simp [Action.rename] at actionIs₂
          | tau => simp [Action.rename] at actionIs₂
      | coact => simp [Action.rename] at actionIs
      | tau => simp [Action.rename] at actionIs
  | @res binder source' target' action' action'' inner seen recurse =>
      intro relabel injective source renamed
      obtain ⟨arguments, rfl, mapped⟩ := rename_eq_apply renamed
      match arguments, mapped with
      | [abstraction], mapped =>
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at mapped
          obtain ⟨body, rfl, rfl⟩ := rename_eq_lambda mapped.symm
          obtain ⟨action, target, step, rfl, rfl⟩ := recurse (liftIndex_injective injective 1) (source := body) rfl
          obtain ⟨action₀, lowered, rfl⟩ := lower?_rename_inv seen
          refine ⟨action₀, .apply "CNu" [.lambda none target], .res binder step lowered, rfl, ?_⟩
          rw [rename_apply]
          simp [rename_lambda]
      | [], mapped | _ :: _ :: _, mapped => simp at mapped

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
