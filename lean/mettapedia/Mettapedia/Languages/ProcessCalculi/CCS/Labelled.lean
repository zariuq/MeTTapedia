import Mettapedia.Languages.ProcessCalculi.CCS.RecursiveSteps
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReactionPairs

/-!
# The labelled transitions of CCS with recursion

Milner's structural operational semantics of CCS, on the terms of `ccsRecCalc` in de Bruijn form (`LStep`):

- a component performs a guard it offers, `α.P + M --α--> P`, a call acting as its body (Milner's rule for
  constants);
- a member of a parallel composition moves, the others staying;
- two members synchronize on an action and its co-action, silently;
- a restriction lets through what does not use its name: the restricted name is the bound variable `0`, so an action
  on it is not seen, and the names of the others move down past the binder (`Action.lower?`).

No label carries a bound name: CCS never sends one, so the restriction rule needs no fresh names.

**Reductions are silent transitions** (`tau_of_raw`): a reaction of two offers is a synchronization of their guards,
and a silent guard taken is a silent transition, to the same contractum.

**Transitions are exposed at the front of a block** (`expose`): a visible transition of a process is a guard offered
by the front member of a block equivalent to it, performing the action lifted past the block's restrictions, the
target the block with the guard's continuation in its place (`Exposes`); a silent transition is a reaction at the
front of a block (`StepBlock`), two blocks joined for a synchronization (`ReactsAt.pair`). So **silent transitions are
reductions up to the static theory**: the canonical form makes a reduction to a contractum with the target's
canonical form (`harmony`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Recursive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.Languages.ProcessCalculi.CCS (act coact tau)
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

/-! ## Actions -/

/-- **An action**: an action or a co-action on a name, or the silent action. -/
inductive Action where
  | act (name : Pattern)
  | coact (name : Pattern)
  | tau
  deriving DecidableEq, Repr

/-- The action a guard performs, with its continuation. -/
def guardAction : Pattern → Option (Action × Pattern)
  | .apply "CAct" [name, continuation] => some (.act name, continuation)
  | .apply "CCoAct" [name, continuation] => some (.coact name, continuation)
  | .apply "CTau" [continuation] => some (.tau, continuation)
  | _ => none

/-- A name seen outside a restriction: the restricted name is not seen, the others move down. -/
def lowerName? : Pattern → Option Pattern
  | .bvar 0 => none
  | .bvar (index + 1) => some (.bvar index)
  | .fvar name => some (.fvar name)
  | _ => none

/-- An action seen outside a restriction. -/
def Action.lower? : Action → Option Action
  | .act name => (lowerName? name).map .act
  | .coact name => (lowerName? name).map .coact
  | .tau => some .tau

theorem guardAction_act (name continuation : Pattern) :
    guardAction (.apply "CAct" [name, continuation]) = some (.act name, continuation) := rfl

theorem guardAction_coact (name continuation : Pattern) :
    guardAction (.apply "CCoAct" [name, continuation]) = some (.coact name, continuation) := rfl

theorem guardAction_tau (continuation : Pattern) :
    guardAction (.apply "CTau" [continuation]) = some (.tau, continuation) := rfl

/-! ## Transitions -/

/-- **The labelled transitions of CCS with recursion.** -/
inductive LStep (definitions : List Definition) : Pattern → Action → Pattern → Prop where
  /-- A component performs a guard it offers, a call as its body. -/
  | offer {component : Pattern} {guards : List Pattern} (offered : offers definitions component = some guards)
      (k : ℕ) (hk : k < guards.length) {action : Action} {continuation : Pattern}
      (performs : guardAction guards[k] = some (action, continuation)) :
      LStep definitions component action continuation
  /-- A member of a parallel composition moves, the others staying. -/
  | par {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) {action : Action}
      {target : Pattern} (inner : LStep definitions elements[i] action target) :
      LStep definitions (.collection .hashBag elements tail) action
        (.collection .hashBag (target :: elements.eraseIdx i) none)
  /-- Two members synchronize on an action and its co-action. -/
  | sync {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) (j : ℕ)
      (hj : j < (elements.eraseIdx i).length) {name target target' : Pattern}
      (first : LStep definitions elements[i] (.act name) target)
      (second : LStep definitions (elements.eraseIdx i)[j] (.coact name) target') :
      LStep definitions (.collection .hashBag elements tail) .tau
        (.collection .hashBag (target :: target' :: (elements.eraseIdx i).eraseIdx j) none)
  /-- A restriction lets through what does not use its name. -/
  | res (binder : Option String) {source target : Pattern} {action action' : Action}
      (inner : LStep definitions source action target) (seen : action.lower? = some action') :
      LStep definitions (.apply "CNu" [.lambda binder source]) action' (.apply "CNu" [.lambda none target])

/-- **A reduction is a silent transition**, to the same contractum. -/
theorem tau_of_raw {definitions : List Definition} {source target : Pattern}
    (step : RecRawStep definitions source target) : LStep definitions source .tau target := by
  induction step with
  | react i hi j hj k hk l hl name continuation continuation' first second acting coacting =>
      exact .sync i hi j hj (.offer first k hk (by rw [acting]; rfl)) (.offer second l hl (by rw [coacting]; rfl))
  | tau k hk continuation offered taken => exact .offer offered k hk (by rw [taken]; rfl)
  | par i hi _ recurse => exact .par i hi recurse
  | res binder _ recurse => exact .res binder recurse rfl

/-! ## Lifting actions -/

/-- An action lifted past restrictions. -/
def Action.lift (count : Nat) : Action → Action
  | .act name => .act (liftBVars 0 count name)
  | .coact name => .coact (liftBVars 0 count name)
  | .tau => .tau

theorem Action.lift_zero (action : Action) : action.lift 0 = action := by
  cases action <;> simp [Action.lift, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]

theorem Action.lift_lift (action : Action) (first second : Nat) :
    (action.lift first).lift second = action.lift (first + second) := by
  cases action <;> simp [Action.lift, liftBVars_zero_zero]

theorem lowerName?_some {name name' : Pattern} (seen : lowerName? name = some name') : name = liftBVars 0 1 name' := by
  match name, seen with
  | .bvar (index + 1), seen =>
      simp only [lowerName?, Option.some.injEq] at seen
      subst seen
      simp [liftBVars]
  | .fvar held, seen =>
      simp only [lowerName?, Option.some.injEq] at seen
      subst seen
      rfl

/-- **What a restriction lets through is the lowered action**: the action inside is the one outside, lifted. -/
theorem Action.lower?_some {action action' : Action} (seen : action.lower? = some action') :
    action = action'.lift 1 := by
  cases action with
  | act name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      simp [Action.lift, lowerName?_some found]
  | coact name =>
      obtain ⟨name', found, rfl⟩ := Option.map_eq_some_iff.mp seen
      simp [Action.lift, lowerName?_some found]
  | tau =>
      simp only [Action.lower?, Option.some.injEq] at seen
      subst seen
      rfl

theorem Action.lift_tau {action : Action} {count : Nat} : action.lift count = .tau ↔ action = .tau := by
  cases action <;> simp [Action.lift]

theorem guardAction_some {guard continuation : Pattern} {action : Action}
    (performs : guardAction guard = some (action, continuation)) :
    (∃ name, action = .act name ∧ guard = .apply "CAct" [name, continuation]) ∨
      (∃ name, action = .coact name ∧ guard = .apply "CCoAct" [name, continuation]) ∨
        (action = .tau ∧ guard = .apply "CTau" [continuation]) := by
  unfold guardAction at performs
  split at performs <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at performs
  · obtain ⟨rfl, rfl⟩ := performs
    exact .inl ⟨_, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := performs
    exact .inr (.inl ⟨_, rfl, rfl⟩)
  · obtain ⟨rfl, rfl⟩ := performs
    exact .inr (.inr ⟨rfl, rfl⟩)

/-- The continuation of a guard a typed component offers is a process. -/
theorem continuation_typed {definitions : List Definition} (admitted : admits definitions = true)
    {free : FreeTypeContext} {bound : List TypeExpr} {component : Pattern} {guards : List Pattern}
    (typed : HasType ccsRecCalc free bound component (.base "Proc")) (offered : offers definitions component = some guards)
    {k : Nat} (hk : k < guards.length) {action : Action} {continuation : Pattern}
    (performs : guardAction guards[k] = some (action, continuation)) :
    HasType ccsRecCalc free bound continuation (.base "Proc") := by
  have guardTyped := offers_guards_typed admitted typed offered _ (List.getElem_mem hk)
  rcases guardAction_some performs with ⟨name, -, guardIs⟩ | ⟨name, -, guardIs⟩ | ⟨-, guardIs⟩ <;>
    rw [guardIs] at guardTyped
  · exact (prefix_parts (.inl rfl) guardTyped).2
  · exact (prefix_parts (.inr rfl) guardTyped).2
  · exact tau_part guardTyped

/-! ## Transitions at the front of a block -/

/-- **A visible transition exposed at the front of a block**: the process is equivalent to a block whose front member
offers a guard performing the action lifted past the block's restrictions, and the target to the block with that
guard's continuation in its place. -/
def Exposes (definitions : List Definition) (free : FreeTypeContext) (bound : List TypeExpr) (source : Pattern)
    (action : Action) (target : Pattern) : Prop :=
  ∃ (count : Nat) (offer : Offer definitions) (continuation : Pattern) (rest : List Pattern),
    guardAction offer.guard = some (action.lift count, continuation) ∧
      ReactsAt ccsRecCalc ccsBlock free bound source target count [offer.component] [continuation] rest

theorem ReactsAt.source_trans {free : FreeTypeContext} {bound : List TypeExpr} {source source' target : Pattern}
    {count : Nat} {parts result rest : List Pattern}
    (same : EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc source' source)
    (reacts : ReactsAt ccsRecCalc ccsBlock free bound source target count parts result rest) :
    ReactsAt ccsRecCalc ccsBlock free bound source' target count parts result rest :=
  ⟨reacts.members, reacts.objects, .trans _ _ _ same reacts.source, reacts.target⟩

/-- An offer lifted past restrictions: its component and its guards lifted. -/
def Offer.lift {definitions : List Definition} (admitted : admits definitions = true) (cutoff shift : Nat)
    (offer : Offer definitions) : Offer definitions :=
  ⟨liftBVars cutoff shift offer.component, offer.guards.map (liftBVars cutoff shift), by
    have liftIsRename : (liftBVars cutoff shift : Pattern → Pattern) =
        Mettapedia.GSLT.LanguageDef.RestrictionBlocks.rename (shiftAbove cutoff shift) :=
      funext (liftBVars_eq_rename cutoff shift)
    rw [liftIsRename]
    exact offers_rename admitted _ offer.offered, offer.position, by simpa using offer.inside⟩

theorem Offer.lift_guard {definitions : List Definition} (admitted : admits definitions = true) (cutoff shift : Nat)
    (offer : Offer definitions) : (offer.lift admitted cutoff shift).guard = liftBVars cutoff shift offer.guard := by
  simp [Offer.lift, Offer.guard]

theorem liftBVars_prefix (cutoff shift : Nat) (label : String) (name continuation : Pattern) :
    liftBVars cutoff shift (.apply label [name, continuation]) =
      .apply label [liftBVars cutoff shift name, liftBVars cutoff shift continuation] := by
  simp [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]

/-- **Transitions at the front of a block**: a silent transition is a reaction at the front of a block, a visible one
a guard offered at the front of a block. -/
theorem expose {definitions : List Definition} (admitted : admits definitions = true) {source : Pattern}
    {action : Action} {target : Pattern} (step : LStep definitions source action target) :
    ∀ {free : FreeTypeContext} {bound : List TypeExpr}, BaseContext free bound →
      HasType ccsRecCalc free bound source (.base "Proc") → isObjectPattern source = true →
        (action = .tau → StepBlock (recReactions admitted) free bound source target) ∧
          (action ≠ .tau → Exposes definitions free bound source action target) := by
  induction step with
  | @offer component guards offered k hk action continuation performs =>
      intro free bound _ typed object
      have continuationTyped := continuation_typed admitted typed offered hk performs
      have reached : EquationEquiv (engineBasePremises RelationEnv.empty) ccsRecCalc continuation
          (.collection .hashBag [continuation] none) :=
        .symm _ _ (derivedInstance_equivalent (ccsRecBlockLanguage.singleton continuationTyped))
      refine ⟨fun isTau => ?_, fun _ => ?_⟩
      · subst isTau
        rcases guardAction_some performs with ⟨_, absurd, _⟩ | ⟨_, absurd, _⟩ | ⟨-, guardIs⟩
        · cases absurd
        · cases absurd
        · let redex : Redex definitions := .silent ⟨component, guards, offered, k, hk⟩ continuation guardIs
          exact ⟨0, redex, [], StepBlockAt.single (reactions := recReactions admitted) (redex := redex) rfl typed object
            reached⟩
      · refine ⟨0, ⟨component, guards, offered, k, hk⟩, continuation, [], ?_, ReactsAt.single rfl typed object reached⟩
        rw [Action.lift_zero]
        exact performs
  | @par elements tail i hi action target inner recurse =>
      intro free bound context typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      obtain ⟨silent, visible⟩ := recurse context (members _ (List.getElem_mem hi)) (objects _ (List.getElem_mem hi))
      refine ⟨fun isTau => ?_, fun notTau => ?_⟩
      · obtain ⟨count, redex, rest, stepBlock⟩ := silent isTau
        exact ⟨count, redex, _, stepBlock.inBag i hi typed objects⟩
      · obtain ⟨count, offer, continuation, rest, performs, reacts⟩ := visible notTau
        refine ⟨count, offer, continuation, _, performs, ReactsAt.inBag i hi ?_ typed objects reacts⟩
        intro offerMembers element member
        simp only [List.mem_singleton] at member
        subst member
        exact continuation_typed admitted (offerMembers offer.component (by simp)) offer.offered offer.inside performs
  | @sync elements tail i hi j hj name target target' first second firstRecurse secondRecurse =>
      intro free bound context typed object
      cases bag_tail_none object
      have members := members_of_bag (block := ccsBlock) typed
      have objects := bag_objects object
      have firstMember := List.getElem_mem hi
      have secondMember := List.mem_of_mem_eraseIdx (List.getElem_mem hj)
      obtain ⟨count, offer, continuation, rest, performs, reacts⟩ :=
        (firstRecurse context (members _ firstMember) (objects _ firstMember)).2 (by simp)
      obtain ⟨count', offer', continuation', rest', performs', reacts'⟩ :=
        (secondRecurse context (members _ secondMember) (objects _ secondMember)).2 (by simp)
      refine ⟨fun _ => ?_, fun notTau => absurd rfl notTau⟩
      have othersMembers : Members ccsRecCalc ccsBlock free bound ((elements.eraseIdx i).eraseIdx j) :=
        fun element member => members element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member))
      have othersObjects : ∀ element ∈ (elements.eraseIdx i).eraseIdx j, isObjectPattern element = true :=
        fun element member => objects element (List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member))
      have results : ∀ {count : Nat} (offer : Offer definitions) {action : Action} {continuation : Pattern},
          guardAction offer.guard = some (action, continuation) →
          Members ccsRecCalc ccsBlock free (List.replicate count (TypeExpr.base ccsBlock.name) ++ bound)
            [offer.component] →
          Members ccsRecCalc ccsBlock free (List.replicate count (TypeExpr.base ccsBlock.name) ++ bound)
            [continuation] := by
        intro count offer action continuation performs offerMembers element member
        simp only [List.mem_singleton] at member
        subst member
        exact continuation_typed admitted (offerMembers offer.component (by simp)) offer.offered offer.inside performs
      have paired := ReactsAt.pair (results offer performs) (results offer' performs') othersMembers othersObjects
        reacts reacts'
      have permutation := (perm_getElem_eraseIdx elements i hi).trans
        ((perm_getElem_eraseIdx (elements.eraseIdx i) j hj).cons _)
      have reordered := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
        (DerivedInstance.bagPerm_of_sorted ⟨free, bound, typed⟩ permutation)
      rcases guardAction_some performs with ⟨name₁, actIs, acting⟩ | ⟨_, absurd, _⟩ | ⟨absurd, _⟩
      rotate_left
      · cases absurd
      · cases absurd
      rcases guardAction_some performs' with ⟨_, absurd, _⟩ | ⟨name₂, coactIs, coacting⟩ | ⟨absurd, _⟩
      · cases absurd
      rotate_left
      · cases absurd
      simp only [Action.lift, Action.act.injEq, Action.coact.injEq] at actIs coactIs
      subst actIs coactIs
      have acting' : (offer.lift admitted 0 count').guard =
          .apply "CAct" [liftBVars 0 (count + count') name, liftBVars 0 count' continuation] := by
        rw [Offer.lift_guard, acting, liftBVars_prefix, liftBVars_zero_zero]
      have coacting' : (offer'.lift admitted count' count).guard =
          .apply "CCoAct" [liftBVars 0 (count + count') name, liftBVars count' count continuation'] := by
        rw [Offer.lift_guard, coacting, liftBVars_prefix, liftBVars_above_lift, Nat.add_comm]
      let redex : Redex definitions := .react (offer.lift admitted 0 count') (offer'.lift admitted count' count)
        (liftBVars 0 (count + count') name) _ _ acting' coacting'
      exact ⟨count + count', redex, _, ReactsAt.source_trans reordered paired⟩
  | @res binder source target action action' inner seen recurse =>
      intro free bound context typed object
      cases restriction_binder (block := ccsBlock) typed
      have bodyTyped := restriction_body (block := ccsBlock) typed
      have bodyObject : isObjectPattern source = true := by rwa [isObject_restriction] at object
      obtain ⟨silent, visible⟩ := recurse (context.cons "Name") bodyTyped bodyObject
      have actionIs := Action.lower?_some seen
      refine ⟨fun isTau => ?_, fun notTau => ?_⟩
      · subst isTau
        obtain ⟨count, redex, rest, stepBlock⟩ := silent actionIs
        exact ⟨count + 1, redex, rest, stepBlock.restrict⟩
      · have innerNotTau : action ≠ .tau := by
          rw [actionIs]
          intro isTau
          exact notTau (Action.lift_tau.mp isTau)
        obtain ⟨count, offer, continuation, rest, performs, reacts⟩ := visible innerNotTau
        refine ⟨count + 1, offer, continuation, rest, ?_, reacts.restrict⟩
        rw [actionIs, Action.lift_lift, Nat.add_comm] at performs
        exact performs

/-- **Harmony**: a silent transition is a reduction up to the static theory. The canonical form reduces to a
contractum with the target's canonical form. -/
theorem harmony {definitions : List Definition} (admitted : admits definitions = true) {free : FreeTypeContext}
    {bound : List TypeExpr} (context : BaseContext free bound) {source target : Pattern}
    (step : LStep definitions source .tau target) (typed : HasType ccsRecCalc free bound source (.base "Proc"))
    (object : isObjectPattern source = true) :
    ∃ target', RecRawStep definitions (canon ccsBlock source) target' ∧ canon ccsBlock target' = canon ccsBlock target :=
  Mettapedia.GSLT.LanguageDef.RestrictionBlocks.simulation (recReactions admitted) context
    ((expose admitted step context typed object).1 rfl) object

end Mettapedia.Languages.ProcessCalculi.CCS.Recursive
