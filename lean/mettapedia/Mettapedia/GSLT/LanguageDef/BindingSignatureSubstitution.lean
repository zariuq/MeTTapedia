import Mettapedia.GSLT.LanguageDef.BindingSignature
import Mettapedia.OSLF.Syntax.PatternAsBindingSignature

/-!
# Substitution coherence for declaration-derived binding syntax

The intrinsic substitution algebra erases to the existing locally nameless
instantiation. Constructor arguments use their authored binding prefixes;
the equation therefore includes mixed-sort and multiple-binder arguments.
The result concerns object substitution, not the executable rule matcher or
premise-produced schema bindings.
-/

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.Binding

set_option autoImplicit false

theorem ParameterScope.wrap_lift
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType)
    (cutoff amount : Nat) (body : Pattern) :
    liftBVars cutoff amount (scope.wrap body) =
      scope.wrap (liftBVars (cutoff + binders.length) amount body) := by
  cases scope <;> simp [ParameterScope.wrap, liftBVars]

/-- Position compatibility for an intrinsic rho and a raw index shift. -/
def ShiftsAtBy {language : LanguageDef} {bound target : List TypeExpr}
    (rho : Ren (signatureOf language) bound target) (cutoff amount : Nat) : Prop :=
  ∀ type position, variableIndex (rho type position) =
    if cutoff ≤ variableIndex position then variableIndex position + amount
    else variableIndex position

theorem shiftsAtBy_liftRen {language : LanguageDef} {bound target : List TypeExpr}
    {rho : Ren (signatureOf language) bound target} {cutoff amount : Nat}
    (compatible : ShiftsAtBy rho cutoff amount) :
    ∀ binders, ShiftsAtBy (liftRen rho binders) (cutoff + binders.length) amount
  | [] => compatible
  | _ :: binders => by
      intro type position
      cases position with
      | zero => simp [liftRen, variableIndex]
      | succ old =>
          have inductionHypothesis := shiftsAtBy_liftRen compatible binders type old
          change variableIndex (liftRen rho binders type old) + 1 = _
          by_cases shifted : cutoff + binders.length ≤ variableIndex old
          · simp [variableIndex, shifted, show cutoff + (binders.length + 1) ≤
                variableIndex old + 1 by omega] at inductionHypothesis ⊢
            omega
          · simp [variableIndex, shifted, show ¬ cutoff + (binders.length + 1) ≤
                variableIndex old + 1 by omega] at inductionHypothesis ⊢
            omega

mutual
theorem erase_rename_shiftBy {language : LanguageDef} :
    ∀ {bound target : List TypeExpr}
      (rho : Ren (signatureOf language) bound target) (cutoff amount : Nat),
      ShiftsAtBy rho cutoff amount → ∀ {type : TypeExpr}
      (term : Term (signatureOf language) bound type),
      erase (rename rho term) = liftBVars cutoff amount (erase term)
  | _, _, rho, cutoff, amount, compatible, _, .var position => by
      change Pattern.bvar (variableIndex (rho _ position)) = _
      rw [compatible _ position]
      by_cases shifted : cutoff ≤ variableIndex position <;>
        simp [erase, liftBVars, shifted]
  | _, _, rho, cutoff, amount, compatible, _,
      .op (.constructor rule _ _ scopes) arguments => by
      change Pattern.apply rule.label
        (eraseConstructorArguments scopes (renameArgs rho arguments)) = _
      rw [eraseConstructorArguments_rename_shiftBy rho cutoff amount compatible scopes arguments]
      simp [erase, liftBVars]
  | _, _, rho, cutoff, amount, compatible, _,
      .op (.collectionConstructor _ _ _ kind _ _ _) arguments => by
      change Pattern.collection kind (eraseArguments (renameArgs rho arguments)) none = _
      rw [eraseArguments_rename_shiftBy rho cutoff amount compatible arguments
        (by intro slot membership; exact congrArg Prod.fst (List.eq_of_mem_replicate membership))]
      simp [erase, liftBVars]
  | _, _, rho, cutoff, amount, compatible, _, .op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => by
          change Pattern.lambda none (erase (rename (liftRen rho [_]) body)) = _
          rw [erase_rename_shiftBy _ (cutoff + 1) amount
            (by simpa using shiftsAtBy_liftRen compatible [_]) body]
          simp only [erase, liftBVars]
  | _, _, rho, cutoff, amount, compatible, _, .op (.multiLambda _ _ count) arguments =>
      match arguments with
      | .cons body .nil => by
          change Pattern.multiLambda count [] (erase (rename (liftRen rho _) body)) = _
          rw [erase_rename_shiftBy _ (cutoff + count) amount
            (by simpa using shiftsAtBy_liftRen compatible (List.replicate count _)) body]
          simp only [erase, liftBVars]
  | _, _, rho, cutoff, amount, compatible, _, .op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons replacement .nil) => by
          change Pattern.subst (erase (rename (liftRen rho [_]) body))
            (erase (rename rho replacement)) = _
          rw [erase_rename_shiftBy _ (cutoff + 1) amount
              (by simpa using shiftsAtBy_liftRen compatible [_]) body,
            erase_rename_shiftBy rho cutoff amount compatible replacement]
          simp only [erase, liftBVars]
  | _, _, rho, cutoff, amount, compatible, _, .op (.collection kind _ _) arguments => by
      change Pattern.collection kind (eraseArguments (renameArgs rho arguments)) none = _
      rw [eraseArguments_rename_shiftBy rho cutoff amount compatible arguments
        (by intro slot membership; exact congrArg Prod.fst (List.eq_of_mem_replicate membership))]
      simp [erase, liftBVars]

termination_by _ _ _ _ _ _ _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize, argsSize]
  all_goals omega

theorem eraseArguments_rename_shiftBy {language : LanguageDef} :
    ∀ {bound target : List TypeExpr}
      (rho : Ren (signatureOf language) bound target) (cutoff amount : Nat),
      ShiftsAtBy rho cutoff amount →
      ∀ {arity : List (List TypeExpr × TypeExpr)}
      (arguments : Args (signatureOf language) arity bound),
      (∀ slot ∈ arity, slot.1 = []) →
      eraseArguments (renameArgs rho arguments) =
        (eraseArguments arguments).map (liftBVars cutoff amount)
  | _, _, _, _, _, _, _, .nil, _ => rfl
  | _, _, rho, cutoff, amount, compatible, (binders, _) :: _,
      .cons head tail, noBinders => by
      have empty : binders = [] := noBinders _ List.mem_cons_self
      have lifted : ShiftsAtBy (liftRen rho binders) cutoff amount := by
        subst binders
        exact compatible
      change erase (rename (liftRen rho binders) head) :: eraseArguments (renameArgs rho tail) = _
      rw [erase_rename_shiftBy _ cutoff amount lifted head,
        eraseArguments_rename_shiftBy rho cutoff amount compatible tail
          (fun slot membership => noBinders slot (List.mem_cons_of_mem _ membership))]
      rfl
termination_by _ _ _ _ _ _ _ arguments _ => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega

theorem eraseConstructorArguments_rename_shiftBy {language : LanguageDef} :
    ∀ {bound target : List TypeExpr}
      (rho : Ren (signatureOf language) bound target) (cutoff amount : Nat),
      ShiftsAtBy rho cutoff amount →
      ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      eraseConstructorArguments scopes (renameArgs rho arguments) =
        (eraseConstructorArguments scopes arguments).map (liftBVars cutoff amount)
  | _, _, _, _, _, _, _, _, .nil, .nil => rfl
  | _, _, rho, cutoff, amount, compatible, _, _,
      .cons (binders := binders) scope scopes, .cons head tail => by
      change scope.wrap (erase (rename (liftRen rho binders) head)) ::
        eraseConstructorArguments scopes (renameArgs rho tail) = _
      rw [erase_rename_shiftBy _ (cutoff + binders.length) amount
          (shiftsAtBy_liftRen compatible binders) head,
        eraseConstructorArguments_rename_shiftBy rho cutoff amount compatible scopes tail]
      simp [eraseConstructorArguments, ParameterScope.wrap_lift]
termination_by _ _ _ _ _ _ _ _ _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega
end

theorem erase_weaken {language : LanguageDef} {bound : List TypeExpr}
    {type added : TypeExpr} (term : Term (signatureOf language) bound type) :
    erase (weaken (t := added) term) = liftBVars 0 1 (erase term) := by
  apply erase_rename_shiftBy
  intro type position
  simp [variableIndex]

/-- Compatibility of one intrinsic substitution with raw binder elimination. -/
def InstAt {language : LanguageDef} {bound target : List TypeExpr}
    (substitution : Sub (signatureOf language) bound target) (depth : Nat)
    (replacement : Pattern) : Prop :=
  ∀ type position, erase (substitution type position) =
    instantiateBVarAt depth replacement (.bvar (variableIndex position))

theorem instAt_liftSub {language : LanguageDef} {bound target : List TypeExpr}
    {substitution : Sub (signatureOf language) bound target} {depth : Nat}
    {replacement : Pattern} (compatible : InstAt substitution depth replacement) :
    ∀ binders, InstAt (liftSub substitution binders) (depth + binders.length) replacement
  | [] => compatible
  | _ :: binders => by
      intro type position
      cases position with
      | zero =>
          change Pattern.bvar 0 = instantiateBVarAt (depth + (binders.length + 1)) replacement (.bvar 0)
          simp [instantiateBVarAt]
      | succ old =>
          change erase (weaken (liftSub substitution binders type old)) = _
          rw [erase_weaken, instAt_liftSub compatible binders type old]
          simpa [variableIndex, Nat.add_assoc] using
            PatternPresentation.liftBVars_instantiateBVarAt_bvar
              replacement (depth + binders.length) (variableIndex old)

theorem ParameterScope.wrap_instantiate
    {parameter : TermParam} {binders : List TypeExpr} {bodyType : TypeExpr}
    (scope : ParameterScope parameter binders bodyType)
    (depth : Nat) (replacement body : Pattern) :
    instantiateBVarAt depth replacement (scope.wrap body) =
      scope.wrap (instantiateBVarAt (depth + binders.length) replacement body) := by
  cases scope <;> simp [ParameterScope.wrap, instantiateBVarAt]

mutual
theorem erase_bind_inst {language : LanguageDef} :
    ∀ {bound target : List TypeExpr}
      (substitution : Sub (signatureOf language) bound target) (depth : Nat)
      (replacement : Pattern), InstAt substitution depth replacement →
      ∀ {type : TypeExpr} (term : Term (signatureOf language) bound type),
      erase (bind substitution term) = instantiateBVarAt depth replacement (erase term)
  | _, _, substitution, depth, replacement, compatible, _, .var position => compatible _ position
  | _, _, substitution, depth, replacement, compatible, _,
      .op (.constructor rule _ _ scopes) arguments => by
      change Pattern.apply rule.label
        (eraseConstructorArguments scopes (bindArgs substitution arguments)) = _
      rw [eraseConstructorArguments_bind_inst substitution depth replacement compatible scopes arguments]
      simp only [erase, instantiateBVarAt]
  | _, _, substitution, depth, replacement, compatible, _,
      .op (.collectionConstructor _ _ _ kind _ _ _) arguments => by
      change Pattern.collection kind (eraseArguments (bindArgs substitution arguments)) none = _
      rw [eraseArguments_bind_inst substitution depth replacement compatible arguments
        (by intro slot membership; exact congrArg Prod.fst (List.eq_of_mem_replicate membership))]
      simp only [erase, instantiateBVarAt]
  | _, _, substitution, depth, replacement, compatible, _, .op (.lambda _ _) arguments =>
      match arguments with
      | .cons body .nil => by
          change Pattern.lambda none (erase (bind (liftSub substitution [_]) body)) = _
          rw [erase_bind_inst _ (depth + 1) replacement
            (by simpa using instAt_liftSub compatible [_]) body]
          simp only [erase, instantiateBVarAt]
  | _, _, substitution, depth, replacement, compatible, _, .op (.multiLambda _ _ count) arguments =>
      match arguments with
      | .cons body .nil => by
          change Pattern.multiLambda count [] (erase (bind (liftSub substitution _) body)) = _
          rw [erase_bind_inst _ (depth + count) replacement
            (by simpa using instAt_liftSub compatible (List.replicate count _)) body]
          simp only [erase, instantiateBVarAt]
  | _, _, substitution, depth, replacement, compatible, _, .op (.subst _ _) arguments =>
      match arguments with
      | .cons body (.cons argument .nil) => by
          change Pattern.subst (erase (bind (liftSub substitution [_]) body))
            (erase (bind substitution argument)) = _
          rw [erase_bind_inst _ (depth + 1) replacement
              (by simpa using instAt_liftSub compatible [_]) body,
            erase_bind_inst substitution depth replacement compatible argument]
          simp only [erase, instantiateBVarAt]
  | _, _, substitution, depth, replacement, compatible, _, .op (.collection kind _ _) arguments => by
      change Pattern.collection kind (eraseArguments (bindArgs substitution arguments)) none = _
      rw [eraseArguments_bind_inst substitution depth replacement compatible arguments
        (by intro slot membership; exact congrArg Prod.fst (List.eq_of_mem_replicate membership))]
      simp only [erase, instantiateBVarAt]
termination_by _ _ _ _ _ _ _ term => 2 * termSize term
decreasing_by
  all_goals simp_wf
  all_goals simp only [termSize, argsSize]
  all_goals omega

theorem eraseArguments_bind_inst {language : LanguageDef} :
    ∀ {bound target : List TypeExpr}
      (substitution : Sub (signatureOf language) bound target) (depth : Nat)
      (replacement : Pattern), InstAt substitution depth replacement →
      ∀ {arity : List (List TypeExpr × TypeExpr)}
      (arguments : Args (signatureOf language) arity bound),
      (∀ slot ∈ arity, slot.1 = []) →
      eraseArguments (bindArgs substitution arguments) =
        (eraseArguments arguments).map (instantiateBVarAt depth replacement)
  | _, _, _, _, _, _, _, .nil, _ => rfl
  | _, _, substitution, depth, replacement, compatible, (binders, _) :: _,
      .cons head tail, noBinders => by
      have empty : binders = [] := noBinders _ List.mem_cons_self
      have lifted : InstAt (liftSub substitution binders) depth replacement := by
        subst binders
        exact compatible
      change erase (bind (liftSub substitution binders) head) :: eraseArguments (bindArgs substitution tail) = _
      rw [erase_bind_inst _ depth replacement lifted head,
        eraseArguments_bind_inst substitution depth replacement compatible tail
          (fun slot membership => noBinders slot (List.mem_cons_of_mem _ membership))]
      rfl
termination_by _ _ _ _ _ _ _ arguments _ => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega

theorem eraseConstructorArguments_bind_inst {language : LanguageDef} :
    ∀ {bound target : List TypeExpr}
      (substitution : Sub (signatureOf language) bound target) (depth : Nat)
      (replacement : Pattern), InstAt substitution depth replacement →
      ∀ {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
      (scopes : ParameterScopes parameters arity)
      (arguments : Args (signatureOf language) arity bound),
      eraseConstructorArguments scopes (bindArgs substitution arguments) =
        (eraseConstructorArguments scopes arguments).map (instantiateBVarAt depth replacement)
  | _, _, _, _, _, _, _, _, .nil, .nil => rfl
  | _, _, substitution, depth, replacement, compatible, _, _,
      .cons (binders := binders) scope scopes, .cons head tail => by
      change scope.wrap (erase (bind (liftSub substitution binders) head)) ::
        eraseConstructorArguments scopes (bindArgs substitution tail) = _
      rw [erase_bind_inst _ (depth + binders.length) replacement
          (instAt_liftSub compatible binders) head,
        eraseConstructorArguments_bind_inst substitution depth replacement compatible scopes tail]
      simp [eraseConstructorArguments, ParameterScope.wrap_instantiate]
termination_by _ _ _ _ _ _ _ _ _ arguments => 2 * argsSize arguments + 1
decreasing_by
  all_goals simp_wf
  all_goals have := termSize_pos head
  all_goals simp only [argsSize]
  all_goals omega
end

/-- Eliminating a typed context variable commutes with the actual raw binder
instantiation throughout declaration-derived syntax. -/
theorem erase_bind_extend {language : LanguageDef} {bound : List TypeExpr}
    {domain codomain : TypeExpr} (replacement : Term (signatureOf language) bound domain)
    (body : Term (signatureOf language) (domain :: bound) codomain) :
    erase (bind (extend replacement) body) = instantiateBVar (erase replacement) (erase body) := by
  apply erase_bind_inst
  intro type position
  cases position with
  | zero => simp [extend, variableIndex, instantiateBVarAt, liftBVars_zero]
  | succ old => simp [extend, erase, variableIndex, instantiateBVarAt]

end Mettapedia.GSLT.LanguageDef.BindingSyntax
