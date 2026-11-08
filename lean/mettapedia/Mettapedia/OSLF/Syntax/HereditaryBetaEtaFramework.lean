import Mettapedia.OSLF.Syntax.ContextualFamily
import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment

/-!
# Contextual instantiation is hereditary substitution

A binding signature presents second-order syntax. Object variables have
sorts, an operator argument declares the sorts it binds, and a metavariable
of a declaration frame takes one argument for each declared parameter sort.
This syntax has no framework application of an abstraction, and every
metavariable occurrence is applied to all of its parameters: its terms are
the beta-normal, eta-long forms of the simply typed framework over the
signature, and nothing else.

This module adds the missing framework redexes explicitly, so that being
canonical becomes a property rather than a matter of syntax.

* `withRedexes T` extends a signature `T` by one operator for each parameter
  list: an abstraction over the parameters, applied to one argument for each
  parameter.
* `evaluate` contracts every such redex by capture-avoiding substitution.
  The substituted arguments have sorts, so a contraction never creates a new
  redex. Evaluation is therefore structurally recursive and returns a term
  of `T` itself.
* Evaluation fixes canonical terms (`evaluate_incl`) and is a substitution
  homomorphism (`evaluate_rename`, `evaluate_bind`).
* A contraction preserves the evaluation (`evaluate_contracts`), and every
  term reduces to the inclusion of its evaluation (`reduces_evaluate`). So
  two raw terms are convertible exactly when their evaluations are equal
  (`convertible_iff`), and the canonical terms are exactly the irreducible
  ones (`canonical_iff_irreducible`).
* Lazy instantiation (`lazy`) replaces each metavariable occurrence by an
  explicit redex: the image of the metavariable applied to the occurrence's
  arguments. Its evaluation is `ContextualFamily.instantiate`
  (`evaluate_lazy`). In particular the lazy instance of a canonical term
  reduces to the contextual instance (`lazy_reduces_to_instantiate`), and
  two canonical terms are equal after instantiation exactly when their lazy
  instances are convertible (`convertible_lazy_iff`).

The controls use a signature with constants and a pairing operator. One
metavariable with one parameter is instantiated by `pair x 2`. Its lazy
instance at `1` is an explicit redex, not canonical, and evaluates to
`pair 1 2`. Two distinct constants are not convertible.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.HereditaryBetaEta

open Mettapedia.OSLF.Binding.ContextualAssignment
  (joinSub joinSub_prefix joinSub_liftSub bind_joinSub)

/-- A framework redex: an abstraction over a parameter list, applied to one
argument for each parameter. -/
inductive Redex (T : Signature) : T.Srt → Type where
  | apply (parameters : List T.Srt) (sort : T.Srt) : Redex T sort

/-- A signature extended by explicit framework redexes. The first argument
binds the parameters; the remaining arguments supply them. -/
abbrev withRedexes (T : Signature) : Signature where
  Srt := T.Srt
  Op sort := T.Op sort ⊕ Redex T sort
  arity operator := match operator with
    | .inl original => T.arity original
    | .inr (.apply parameters sort) => (parameters, sort) :: parameters.map (fun b => ([], b))

section Framework

variable {T : Signature}

/-! ## Contraction and evaluation -/

/-- Contract one redex: substitute the arguments for the parameters, and
keep every ambient variable. -/
def contract {Γ : Ctx T} {parameters : List T.Srt} {sort : T.Srt}
    (body : Term T (parameters ++ Γ) sort)
    (arguments : Args T (parameters.map (fun b => ([], b))) Γ) : Term T Γ sort :=
  bind (joinSub (argsToSub arguments) (fun _ position => .var position)) body

def contractArgs {Γ : Ctx T} {parameters : List T.Srt} {sort : T.Srt} :
    Args T ((parameters, sort) :: parameters.map (fun b => ([], b))) Γ → Term T Γ sort
  | .cons body arguments => contract body arguments

/-- One operator node, from its evaluated arguments. -/
def evaluateNode {Γ : Ctx T} : {sort : T.Srt} → (operator : (withRedexes T).Op sort) →
    Args T ((withRedexes T).arity operator) Γ → Term T Γ sort
  | _, .inl original, arguments => .op original arguments
  | _, .inr (.apply _ _), arguments => contractArgs arguments

mutual

/-- Evaluation contracts every framework redex. -/
def evaluate : {Γ : Ctx T} → {sort : T.Srt} → Term (withRedexes T) Γ sort → Term T Γ sort
  | _, _, .var position => .var position
  | _, _, .op operator arguments => evaluateNode operator (evaluateArgs arguments)

def evaluateArgs : {arities : List (List T.Srt × T.Srt)} → {Γ : Ctx T} →
    Args (withRedexes T) arities Γ → Args T arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (evaluate head) (evaluateArgs tail)

end

mutual

/-- Canonical terms are the raw terms without framework redexes. -/
def incl : {Γ : Ctx T} → {sort : T.Srt} → Term T Γ sort → Term (withRedexes T) Γ sort
  | _, _, .var position => .var position
  | _, _, .op operator arguments => .op (Sum.inl operator) (inclArgs arguments)

def inclArgs : {arities : List (List T.Srt × T.Srt)} → {Γ : Ctx T} →
    Args T arities Γ → Args (withRedexes T) arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (incl head) (inclArgs tail)

end

mutual

/-- One redex contracted, anywhere in a raw term. -/
inductive Contracts : {Γ : Ctx T} → {sort : T.Srt} →
    Term (withRedexes T) Γ sort → Term (withRedexes T) Γ sort → Prop where
  | redex {Γ : Ctx T} {parameters : List T.Srt} {sort : T.Srt}
      (body : Term (withRedexes T) (parameters ++ Γ) sort)
      (arguments : Args (withRedexes T) (parameters.map (fun b => ([], b))) Γ) :
      Contracts (.op (Sum.inr (.apply parameters sort)) (.cons body arguments))
        (bind (joinSub (argsToSub arguments) (fun _ position => .var position)) body)
  | inside {Γ : Ctx T} {sort : T.Srt} (operator : (withRedexes T).Op sort)
      {first second : Args (withRedexes T) ((withRedexes T).arity operator) Γ} :
      ContractsArgs first second → Contracts (.op operator first) (.op operator second)

inductive ContractsArgs : {arities : List (List T.Srt × T.Srt)} → {Γ : Ctx T} →
    Args (withRedexes T) arities Γ → Args (withRedexes T) arities Γ → Prop where
  | head {binders : List T.Srt} {sort : T.Srt} {arities : List (List T.Srt × T.Srt)} {Γ : Ctx T}
      {first second : Term (withRedexes T) (binders ++ Γ) sort}
      (tail : Args (withRedexes T) arities Γ) :
      Contracts first second → ContractsArgs (.cons first tail) (.cons second tail)
  | tail {binders : List T.Srt} {sort : T.Srt} {arities : List (List T.Srt × T.Srt)} {Γ : Ctx T}
      (head : Term (withRedexes T) (binders ++ Γ) sort)
      {first second : Args (withRedexes T) arities Γ} :
      ContractsArgs first second → ContractsArgs (.cons head first) (.cons head second)

end

/-! ## Canonical terms are fixed -/

mutual

theorem evaluate_incl : ∀ {Γ : Ctx T} {sort : T.Srt} (term : Term T Γ sort),
    evaluate (incl term) = term
  | _, _, .var _ => rfl
  | _, _, .op operator arguments => by
      show Term.op operator (evaluateArgs (inclArgs arguments)) = Term.op operator arguments
      rw [evaluateArgs_inclArgs arguments]

theorem evaluateArgs_inclArgs : ∀ {arities : List (List T.Srt × T.Srt)} {Γ : Ctx T}
    (arguments : Args T arities Γ), evaluateArgs (inclArgs arguments) = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      show Args.cons (evaluate (incl head)) (evaluateArgs (inclArgs tail)) = Args.cons head tail
      rw [evaluate_incl head, evaluateArgs_inclArgs tail]

end

/-! ## The inclusion is a substitution homomorphism -/

mutual

theorem incl_rename : ∀ {Γ Δ : Ctx T} {sort : T.Srt} (rho : Ren T Γ Δ) (term : Term T Γ sort),
    incl (rename rho term) = rename (S := withRedexes T) rho (incl term)
  | _, _, _, _, .var _ => rfl
  | _, _, _, rho, .op operator arguments => by
      show Term.op (S := withRedexes T) (Sum.inl operator) (inclArgs (renameArgs rho arguments)) =
        Term.op (S := withRedexes T) (Sum.inl operator)
          (renameArgs (S := withRedexes T) rho (inclArgs arguments))
      rw [inclArgs_renameArgs rho arguments]

theorem inclArgs_renameArgs : ∀ {arities : List (List T.Srt × T.Srt)} {Γ Δ : Ctx T}
    (rho : Ren T Γ Δ) (arguments : Args T arities Γ),
    inclArgs (renameArgs rho arguments) = renameArgs (S := withRedexes T) rho (inclArgs arguments)
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := binders) head tail => by
      show Args.cons (incl (rename (liftRen rho binders) head)) (inclArgs (renameArgs rho tail)) =
        Args.cons (rename (S := withRedexes T) (liftRen rho binders) (incl head))
          (renameArgs (S := withRedexes T) rho (inclArgs tail))
      rw [incl_rename (liftRen rho binders) head, inclArgs_renameArgs rho tail]

end

theorem incl_liftSub {Γ Δ : Ctx T} (sigma : Sub T Γ Δ) :
    ∀ (binders : List T.Srt) (sort : T.Srt) (position : Var (binders ++ Γ) sort),
      incl (liftSub sigma binders sort position) =
        liftSub (S := withRedexes T) (fun s v => incl (sigma s v)) binders sort position
  | [], _, _ => rfl
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => by
      simp only [liftSub, weaken, incl_rename, incl_liftSub sigma binders sort position]

mutual

theorem incl_bind : ∀ {Γ Δ : Ctx T} {sort : T.Srt} (sigma : Sub T Γ Δ) (term : Term T Γ sort),
    incl (bind sigma term) = bind (S := withRedexes T) (fun s v => incl (sigma s v)) (incl term)
  | _, _, _, _, .var _ => rfl
  | _, _, _, sigma, .op operator arguments => by
      show Term.op (S := withRedexes T) (Sum.inl operator) (inclArgs (bindArgs sigma arguments)) =
        Term.op (S := withRedexes T) (Sum.inl operator)
          (bindArgs (S := withRedexes T) (fun s v => incl (sigma s v)) (inclArgs arguments))
      rw [inclArgs_bindArgs sigma arguments]

theorem inclArgs_bindArgs : ∀ {arities : List (List T.Srt × T.Srt)} {Γ Δ : Ctx T}
    (sigma : Sub T Γ Δ) (arguments : Args T arities Γ),
    inclArgs (bindArgs sigma arguments) =
      bindArgs (S := withRedexes T) (fun s v => incl (sigma s v)) (inclArgs arguments)
  | _, _, _, _, .nil => rfl
  | _, _, _, sigma, .cons (bs := binders) head tail => by
      have lifted : (fun s v => incl (liftSub sigma binders s v)) =
          liftSub (S := withRedexes T) (fun s v => incl (sigma s v)) binders := by
        funext s v
        exact incl_liftSub sigma binders s v
      show Args.cons (incl (bind (liftSub sigma binders) head)) (inclArgs (bindArgs sigma tail)) =
        Args.cons (bind (S := withRedexes T) (liftSub (S := withRedexes T)
            (fun s v => incl (sigma s v)) binders) (incl head))
          (bindArgs (S := withRedexes T) (fun s v => incl (sigma s v)) (inclArgs tail))
      rw [incl_bind (liftSub sigma binders) head, lifted, inclArgs_bindArgs sigma tail]

end

theorem incl_argsToSub {Γ : Ctx T} : ∀ (parameters : List T.Srt)
    (arguments : Args T (parameters.map (fun b => ([], b))) Γ) (sort : T.Srt)
    (position : Var parameters sort),
      incl (argsToSub arguments sort position) = argsToSub (inclArgs arguments) sort position
  | [], _, _, position => nomatch position
  | _ :: _, .cons _ _, _, .zero => rfl
  | _ :: parameters, .cons _ tail, sort, .succ position =>
      incl_argsToSub parameters tail sort position

theorem incl_joinSub {Γ Δ : Ctx T} (ambient : Sub T Γ Δ) : ∀ (parameters : List T.Srt)
    (arguments : Sub T parameters Δ) (sort : T.Srt) (position : Var (parameters ++ Γ) sort),
      incl (joinSub arguments ambient sort position) =
        joinSub (S := withRedexes T) (fun s v => incl (arguments s v))
          (fun s v => incl (ambient s v)) sort position
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: parameters, arguments, sort, .succ position =>
      incl_joinSub ambient parameters (fun s v => arguments s (.succ v)) sort position

theorem incl_contract {Γ : Ctx T} {parameters : List T.Srt} {sort : T.Srt}
    (body : Term T (parameters ++ Γ) sort)
    (arguments : Args T (parameters.map (fun b => ([], b))) Γ) :
    incl (contract body arguments) =
      bind (S := withRedexes T) (joinSub (argsToSub (inclArgs arguments))
        (fun _ position => .var position)) (incl body) := by
  unfold contract
  rw [incl_bind]
  congr 1
  funext s v
  rw [incl_joinSub]
  have reads : (fun s w => incl (argsToSub arguments s w)) = argsToSub (inclArgs arguments) := by
    funext s w
    exact incl_argsToSub parameters arguments s w
  rw [reads]
  rfl

/-! ## Evaluation is a substitution homomorphism -/

theorem rename_joinSub {Γ Δ : Ctx T} (rho : Ren T Γ Δ) : ∀ (parameters : List T.Srt)
    (arguments : Sub T parameters Γ) (sort : T.Srt) (position : Var (parameters ++ Γ) sort),
      rename rho (joinSub arguments (fun _ v => Term.var v) sort position) =
        joinSub (fun s v => rename rho (arguments s v)) (fun _ v => Term.var v) sort
          (liftRen rho parameters sort position)
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: parameters, arguments, sort, .succ position =>
      rename_joinSub rho parameters (fun s v => arguments s (.succ v)) sort position

theorem rename_contract {Γ Δ : Ctx T} {parameters : List T.Srt} {sort : T.Srt} (rho : Ren T Γ Δ)
    (body : Term T (parameters ++ Γ) sort)
    (arguments : Args T (parameters.map (fun b => ([], b))) Γ) :
    rename rho (contract body arguments) =
      contract (rename (liftRen rho parameters) body) (renameArgs rho arguments) := by
  unfold contract
  rw [rename_bind, bind_rename]
  congr 1
  funext s v
  rw [rename_joinSub rho parameters (argsToSub arguments) s v]
  have reads : (fun s w => rename rho (argsToSub arguments s w)) =
      argsToSub (renameArgs rho arguments) := by
    funext s w
    exact (argsToSub_renameArgs rho parameters arguments s w).symm
  rw [reads]

theorem bind_contract {Γ Δ : Ctx T} {parameters : List T.Srt} {sort : T.Srt} (sigma : Sub T Γ Δ)
    (body : Term T (parameters ++ Γ) sort)
    (arguments : Args T (parameters.map (fun b => ([], b))) Γ) :
    bind sigma (contract body arguments) =
      contract (bind (liftSub sigma parameters) body) (bindArgs sigma arguments) := by
  unfold contract
  rw [bind_comp, bind_comp]
  congr 1
  have left := bind_joinSub sigma parameters (argsToSub arguments)
    (fun _ position => Term.var (S := T) position)
  have right := joinSub_liftSub sigma parameters (argsToSub (bindArgs sigma arguments))
    (fun _ position => Term.var (S := T) position)
  rw [left, right]
  have reads : (fun s v => bind sigma (argsToSub arguments s v)) =
      argsToSub (bindArgs sigma arguments) := by
    funext s v
    exact (argsToSub_bindArgs sigma parameters arguments s v).symm
  have ambient : (fun s (v : Var Γ s) => bind sigma (Term.var (S := T) v)) =
      fun s v => bind (fun _ position => Term.var position) (sigma s v) := by
    funext s v
    rw [bind_id]
    rfl
  rw [reads, ambient]

theorem contractArgs_renameArgs {Γ Δ : Ctx T} {parameters : List T.Srt} {sort : T.Srt}
    (rho : Ren T Γ Δ) :
    ∀ (arguments : Args T ((parameters, sort) :: parameters.map (fun b => ([], b))) Γ),
      contractArgs (renameArgs rho arguments) = rename rho (contractArgs arguments)
  | .cons body rest => (rename_contract rho body rest).symm

theorem contractArgs_bindArgs {Γ Δ : Ctx T} {parameters : List T.Srt} {sort : T.Srt}
    (sigma : Sub T Γ Δ) :
    ∀ (arguments : Args T ((parameters, sort) :: parameters.map (fun b => ([], b))) Γ),
      contractArgs (bindArgs sigma arguments) = bind sigma (contractArgs arguments)
  | .cons body rest => (bind_contract sigma body rest).symm

theorem evaluateNode_renameArgs {Γ Δ : Ctx T} {sort : T.Srt} (rho : Ren T Γ Δ) :
    ∀ (operator : (withRedexes T).Op sort) (arguments : Args T ((withRedexes T).arity operator) Γ),
      evaluateNode operator (renameArgs rho arguments) = rename rho (evaluateNode operator arguments)
  | .inl _, _ => rfl
  | .inr (.apply _ _), arguments => contractArgs_renameArgs rho arguments

theorem evaluateNode_bindArgs {Γ Δ : Ctx T} {sort : T.Srt} (sigma : Sub T Γ Δ) :
    ∀ (operator : (withRedexes T).Op sort) (arguments : Args T ((withRedexes T).arity operator) Γ),
      evaluateNode operator (bindArgs sigma arguments) = bind sigma (evaluateNode operator arguments)
  | .inl _, _ => rfl
  | .inr (.apply _ _), arguments => contractArgs_bindArgs sigma arguments

mutual

theorem evaluate_rename : ∀ {Γ Δ : Ctx T} {sort : T.Srt} (rho : Ren T Γ Δ)
    (term : Term (withRedexes T) Γ sort),
      evaluate (rename (S := withRedexes T) rho term) = rename rho (evaluate term)
  | _, _, _, _, .var _ => rfl
  | _, _, _, rho, .op operator arguments => by
      show evaluateNode operator (evaluateArgs (renameArgs (S := withRedexes T) rho arguments)) =
        rename rho (evaluateNode operator (evaluateArgs arguments))
      rw [evaluateArgs_renameArgs rho arguments, evaluateNode_renameArgs]

theorem evaluateArgs_renameArgs : ∀ {arities : List (List T.Srt × T.Srt)} {Γ Δ : Ctx T}
    (rho : Ren T Γ Δ) (arguments : Args (withRedexes T) arities Γ),
      evaluateArgs (renameArgs (S := withRedexes T) rho arguments) =
        renameArgs rho (evaluateArgs arguments)
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := binders) head tail => by
      show Args.cons (evaluate (rename (S := withRedexes T) (liftRen rho binders) head))
          (evaluateArgs (renameArgs (S := withRedexes T) rho tail)) =
        Args.cons (rename (liftRen rho binders) (evaluate head)) (renameArgs rho (evaluateArgs tail))
      rw [evaluate_rename (liftRen rho binders) head, evaluateArgs_renameArgs rho tail]

end

theorem evaluate_liftSub {Γ Δ : Ctx T} (sigma : Sub (withRedexes T) Γ Δ) :
    ∀ (binders : List T.Srt) (sort : T.Srt) (position : Var (binders ++ Γ) sort),
      evaluate (liftSub sigma binders sort position) =
        liftSub (S := T) (fun s v => evaluate (sigma s v)) binders sort position
  | [], _, _ => rfl
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => by
      simp only [liftSub, weaken, evaluate_rename, evaluate_liftSub sigma binders sort position]

mutual

theorem evaluate_bind : ∀ {Γ Δ : Ctx T} {sort : T.Srt} (sigma : Sub (withRedexes T) Γ Δ)
    (term : Term (withRedexes T) Γ sort),
      evaluate (bind sigma term) = bind (S := T) (fun s v => evaluate (sigma s v)) (evaluate term)
  | _, _, _, _, .var _ => rfl
  | _, _, _, sigma, .op operator arguments => by
      show evaluateNode operator (evaluateArgs (bindArgs sigma arguments)) =
        bind (S := T) (fun s v => evaluate (sigma s v)) (evaluateNode operator (evaluateArgs arguments))
      rw [evaluateArgs_bindArgs sigma arguments, evaluateNode_bindArgs]

theorem evaluateArgs_bindArgs : ∀ {arities : List (List T.Srt × T.Srt)} {Γ Δ : Ctx T}
    (sigma : Sub (withRedexes T) Γ Δ) (arguments : Args (withRedexes T) arities Γ),
      evaluateArgs (bindArgs sigma arguments) =
        bindArgs (S := T) (fun s v => evaluate (sigma s v)) (evaluateArgs arguments)
  | _, _, _, _, .nil => rfl
  | _, _, _, sigma, .cons (bs := binders) head tail => by
      have lifted : (fun (s : T.Srt) (v : Var (binders ++ _) s) => evaluate (liftSub sigma binders s v)) =
          liftSub (S := T) (fun s v => evaluate (sigma s v)) binders := by
        funext s v
        exact evaluate_liftSub sigma binders s v
      show Args.cons (evaluate (bind (liftSub sigma binders) head)) (evaluateArgs (bindArgs sigma tail)) =
        Args.cons (bind (S := T) (liftSub (S := T) (fun s v => evaluate (sigma s v)) binders)
            (evaluate head))
          (bindArgs (S := T) (fun s v => evaluate (sigma s v)) (evaluateArgs tail))
      rw [evaluate_bind (liftSub sigma binders) head, lifted, evaluateArgs_bindArgs sigma tail]

end

/-! ## Conversion is equality of evaluations -/

theorem evaluate_joinSub {Γ Δ : Ctx T} (ambient : Sub (withRedexes T) Γ Δ) :
    ∀ (parameters : List T.Srt) (arguments : Sub (withRedexes T) parameters Δ) (sort : T.Srt)
      (position : Var (parameters ++ Γ) sort),
      evaluate (joinSub arguments ambient sort position) =
        joinSub (S := T) (fun s v => evaluate (arguments s v)) (fun s v => evaluate (ambient s v))
          sort position
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: parameters, arguments, sort, .succ position =>
      evaluate_joinSub ambient parameters (fun s v => arguments s (.succ v)) sort position

theorem evaluate_argsToSub {Γ : Ctx T} : ∀ (parameters : List T.Srt)
    (arguments : Args (withRedexes T) (parameters.map (fun b => ([], b))) Γ) (sort : T.Srt)
    (position : Var parameters sort),
      evaluate (argsToSub arguments sort position) = argsToSub (evaluateArgs arguments) sort position
  | [], _, _, position => nomatch position
  | _ :: _, .cons _ _, _, .zero => rfl
  | _ :: parameters, .cons _ tail, sort, .succ position =>
      evaluate_argsToSub parameters tail sort position

mutual

theorem evaluate_contracts : ∀ {Γ : Ctx T} {sort : T.Srt}
    {first second : Term (withRedexes T) Γ sort}, Contracts first second → evaluate first = evaluate second
  | _, _, _, _, .redex body arguments => by
      rw [evaluate_bind]
      show contract (evaluate body) (evaluateArgs arguments) = _
      unfold contract
      congr 1
      funext s v
      rw [evaluate_joinSub]
      have reads : (fun (s : T.Srt) (w : Var _ s) => evaluate (argsToSub arguments s w)) =
          argsToSub (evaluateArgs arguments) := by
        funext s w
        exact evaluate_argsToSub _ arguments s w
      rw [reads]
      rfl
  | _, _, _, _, .inside operator inner => by
      show evaluateNode operator (evaluateArgs _) = evaluateNode operator (evaluateArgs _)
      rw [evaluateArgs_contracts inner]

theorem evaluateArgs_contracts : ∀ {arities : List (List T.Srt × T.Srt)} {Γ : Ctx T}
    {first second : Args (withRedexes T) arities Γ},
    ContractsArgs first second → evaluateArgs first = evaluateArgs second
  | _, _, _, _, .head tail inner => by
      show Args.cons (evaluate _) (evaluateArgs tail) = Args.cons (evaluate _) (evaluateArgs tail)
      rw [evaluate_contracts inner]
  | _, _, _, _, .tail head inner => by
      show Args.cons (evaluate head) (evaluateArgs _) = Args.cons (evaluate head) (evaluateArgs _)
      rw [evaluateArgs_contracts inner]

end

theorem reduces_inside {Γ : Ctx T} {sort : T.Srt} (operator : (withRedexes T).Op sort)
    {first second : Args (withRedexes T) ((withRedexes T).arity operator) Γ}
    (steps : Relation.ReflTransGen ContractsArgs first second) :
    Relation.ReflTransGen Contracts (Term.op operator first) (Term.op operator second) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Contracts.inside operator step)

theorem reducesArgs_head {Γ : Ctx T} {binders : List T.Srt} {sort : T.Srt}
    {arities : List (List T.Srt × T.Srt)} {first second : Term (withRedexes T) (binders ++ Γ) sort}
    (tail : Args (withRedexes T) arities Γ) (steps : Relation.ReflTransGen Contracts first second) :
    Relation.ReflTransGen ContractsArgs (Args.cons first tail) (Args.cons second tail) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (ContractsArgs.head tail step)

theorem reducesArgs_tail {Γ : Ctx T} {binders : List T.Srt} {sort : T.Srt}
    {arities : List (List T.Srt × T.Srt)} (head : Term (withRedexes T) (binders ++ Γ) sort)
    {first second : Args (withRedexes T) arities Γ}
    (steps : Relation.ReflTransGen ContractsArgs first second) :
    Relation.ReflTransGen ContractsArgs (Args.cons head first) (Args.cons head second) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (ContractsArgs.tail head step)

theorem reduces_contractArgs {Γ : Ctx T} {parameters : List T.Srt} {sort : T.Srt} :
    ∀ (arguments : Args T ((parameters, sort) :: parameters.map (fun b => ([], b))) Γ),
      Relation.ReflTransGen Contracts
        (Term.op (S := withRedexes T) (Sum.inr (.apply parameters sort)) (inclArgs arguments))
        (incl (contractArgs arguments))
  | .cons body rest => by
      have step := Contracts.redex (incl body) (inclArgs rest)
      have same := incl_contract body rest
      rw [← same] at step
      exact .single step

theorem reduces_node {Γ : Ctx T} {sort : T.Srt} :
    ∀ (operator : (withRedexes T).Op sort) (arguments : Args T ((withRedexes T).arity operator) Γ),
      Relation.ReflTransGen Contracts (Term.op operator (inclArgs arguments))
        (incl (evaluateNode operator arguments))
  | .inl _, _ => .refl
  | .inr (.apply _ _), arguments => reduces_contractArgs arguments

mutual

/-- **Every raw term reduces to the inclusion of its evaluation.** -/
theorem reduces_evaluate : ∀ {Γ : Ctx T} {sort : T.Srt} (term : Term (withRedexes T) Γ sort),
    Relation.ReflTransGen Contracts term (incl (evaluate term))
  | _, _, .var _ => .refl
  | _, _, .op operator arguments =>
      (reduces_inside operator (reducesArgs_evaluate arguments)).trans
        (reduces_node operator (evaluateArgs arguments))

theorem reducesArgs_evaluate : ∀ {arities : List (List T.Srt × T.Srt)} {Γ : Ctx T}
    (arguments : Args (withRedexes T) arities Γ),
    Relation.ReflTransGen ContractsArgs arguments (inclArgs (evaluateArgs arguments))
  | _, _, .nil => .refl
  | _, _, .cons head tail =>
      (reducesArgs_head tail (reduces_evaluate head)).trans
        (reducesArgs_tail (incl (evaluate head)) (reducesArgs_evaluate tail))

end

theorem eqvGen_of_reduces {α : Type} {relation : α → α → Prop} {first second : α}
    (steps : Relation.ReflTransGen relation first second) : Relation.EqvGen relation first second := by
  induction steps with
  | refl => exact .refl _
  | tail _ step ih => exact .trans _ _ _ ih (.rel _ _ step)

/-- **Convertibility is equality of evaluations.** Canonical forms are unique
representatives of framework conversion classes. -/
theorem convertible_iff {Γ : Ctx T} {sort : T.Srt} (first second : Term (withRedexes T) Γ sort) :
    Relation.EqvGen Contracts first second ↔ evaluate first = evaluate second := by
  constructor
  · intro related
    induction related with
    | rel _ _ step => exact evaluate_contracts step
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'
  · intro same
    have there := eqvGen_of_reduces (reduces_evaluate first)
    have back := eqvGen_of_reduces (reduces_evaluate second)
    rw [same] at there
    exact Relation.EqvGen.trans _ _ _ there (Relation.EqvGen.symm _ _ back)

/-! ## Canonical terms are exactly the irreducible terms -/

def nodeWeight : {sort : T.Srt} → (withRedexes T).Op sort → Nat
  | _, .inl _ => 0
  | _, .inr _ => 1

mutual

/-- The number of framework redexes in a raw term. -/
def redexCount : {Γ : Ctx T} → {sort : T.Srt} → Term (withRedexes T) Γ sort → Nat
  | _, _, .var _ => 0
  | _, _, .op operator arguments => redexCountArgs arguments + nodeWeight operator

def redexCountArgs : {arities : List (List T.Srt × T.Srt)} → {Γ : Ctx T} →
    Args (withRedexes T) arities Γ → Nat
  | _, _, .nil => 0
  | _, _, .cons head tail => redexCount head + redexCountArgs tail

end

mutual

theorem redexCount_incl : ∀ {Γ : Ctx T} {sort : T.Srt} (term : Term T Γ sort),
    redexCount (incl term) = 0
  | _, _, .var _ => rfl
  | _, _, .op _ arguments => by
      show redexCountArgs (inclArgs arguments) + 0 = 0
      rw [redexCountArgs_inclArgs arguments]

theorem redexCountArgs_inclArgs : ∀ {arities : List (List T.Srt × T.Srt)} {Γ : Ctx T}
    (arguments : Args T arities Γ), redexCountArgs (inclArgs arguments) = 0
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      show redexCount (incl head) + redexCountArgs (inclArgs tail) = 0
      rw [redexCount_incl head, redexCountArgs_inclArgs tail]

end

mutual

theorem redexCount_pos_of_contracts : ∀ {Γ : Ctx T} {sort : T.Srt}
    {first second : Term (withRedexes T) Γ sort}, Contracts first second → 0 < redexCount first
  | _, _, _, _, .redex _ _ => by
      show 0 < redexCountArgs _ + 1
      omega
  | _, _, _, _, .inside operator inner => by
      have positive := redexCountArgs_pos_of_contracts inner
      show 0 < redexCountArgs _ + nodeWeight operator
      omega

theorem redexCountArgs_pos_of_contracts : ∀ {arities : List (List T.Srt × T.Srt)} {Γ : Ctx T}
    {first second : Args (withRedexes T) arities Γ}, ContractsArgs first second → 0 < redexCountArgs first
  | _, _, _, _, .head _ inner => by
      have positive := redexCount_pos_of_contracts inner
      show 0 < redexCount _ + redexCountArgs _
      omega
  | _, _, _, _, .tail _ inner => by
      have positive := redexCountArgs_pos_of_contracts inner
      show 0 < redexCount _ + redexCountArgs _
      omega

end

/-- **The canonical terms are exactly the irreducible raw terms.** -/
theorem canonical_iff_irreducible {Γ : Ctx T} {sort : T.Srt} (term : Term (withRedexes T) Γ sort) :
    (∃ canonical : Term T Γ sort, incl canonical = term) ↔ ∀ other, ¬ Contracts term other := by
  constructor
  · rintro ⟨canonical, rfl⟩ other step
    have positive := redexCount_pos_of_contracts step
    rw [redexCount_incl] at positive
    exact Nat.lt_irrefl 0 positive
  · intro irreducible
    refine ⟨evaluate term, ?_⟩
    rcases (reduces_evaluate term).cases_head with same | ⟨middle, step, _⟩
    · exact same.symm
    · exact absurd step (irreducible middle)

end Framework

/-! ## Lazy instantiation evaluates to contextual instantiation -/

section Contextual

open ContextualFamily (signature Assignment)

variable {S : Signature} {V W : Type} {source : V → MetaArity S} {target : W → MetaArity S}

/-- The image of a metavariable, opened beneath the ambient context of an
occurrence. Its free variables are the metavariable's parameters. -/
def openImage {Γ : Ctx S} (assignment : Assignment source target) (identity : V) :
    Term (withRedexes (signature S target)) ((source identity).1 ++ Γ) (source identity).2 :=
  rename (S := withRedexes (signature S target))
    (fun _ position => injPrefix (S := signature S target) (source identity).1 position)
    (incl (assignment identity))

mutual

/-- Lazy instantiation: each metavariable occurrence becomes an explicit
framework redex, its image applied to the occurrence's arguments. -/
def lazy (assignment : Assignment source target) : {Γ : Ctx S} → {sort : S.Srt} →
    Term (withRedexes (signature S source)) Γ sort → Term (withRedexes (signature S target)) Γ sort
  | _, _, .var position => .var position
  | _, _, .op (.inl (.inl original)) arguments =>
      .op (Sum.inl (Sum.inl original)) (lazyArgs assignment arguments)
  | _, _, .op (.inl (.inr (.mk identity))) arguments =>
      .op (Sum.inr (Redex.apply (T := signature S target) (source identity).1 (source identity).2))
        (.cons (openImage assignment identity) (lazyArgs assignment arguments))
  | _, _, .op (.inr (.apply parameters result)) arguments =>
      .op (Sum.inr (Redex.apply (T := signature S target) parameters result))
        (lazyArgs assignment arguments)

def lazyArgs (assignment : Assignment source target) : {arities : List (List S.Srt × S.Srt)} →
    {Γ : Ctx S} → Args (withRedexes (signature S source)) arities Γ →
      Args (withRedexes (signature S target)) arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail => .cons (lazy assignment head) (lazyArgs assignment tail)

end

theorem instantiate_joinSub (assignment : Assignment source target) {Γ Δ : Ctx S}
    (ambient : Sub (signature S source) Γ Δ) : ∀ (parameters : List S.Srt)
    (arguments : Sub (signature S source) parameters Δ) (sort : S.Srt)
    (position : Var (parameters ++ Γ) sort),
      ContextualFamily.instantiate assignment (joinSub arguments ambient sort position) =
        joinSub (S := signature S target) (fun s v => ContextualFamily.instantiate assignment (arguments s v))
          (fun s v => ContextualFamily.instantiate assignment (ambient s v)) sort position
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: parameters, arguments, sort, .succ position =>
      instantiate_joinSub assignment ambient parameters (fun s v => arguments s (.succ v)) sort position

theorem instantiate_contract (assignment : Assignment source target) {Γ : Ctx S}
    {parameters : List S.Srt} {sort : S.Srt} (body : Term (signature S source) (parameters ++ Γ) sort)
    (arguments : Args (signature S source) (parameters.map (fun b => ([], b))) Γ) :
    ContextualFamily.instantiate assignment (contract body arguments) =
      contract (ContextualFamily.instantiate assignment body)
        (ContextualFamily.instantiateArgs assignment arguments) := by
  unfold contract
  rw [ContextualFamily.instantiate_bind]
  congr 1
  funext s v
  rw [instantiate_joinSub]
  have reads : (fun (s : S.Srt) (w : Var parameters s) =>
        ContextualFamily.instantiate assignment (argsToSub arguments s w)) =
      argsToSub (S := signature S target) (ContextualFamily.instantiateArgs assignment arguments) := by
    funext s w
    exact (ContextualFamily.argsToSub_instantiateArgs assignment parameters arguments s w).symm
  rw [reads]
  rfl

theorem contractArgs_instantiateArgs (assignment : Assignment source target) {Γ : Ctx S}
    {parameters : List S.Srt} {sort : S.Srt} :
    ∀ (arguments : Args (signature S source) ((parameters, sort) :: parameters.map (fun b => ([], b))) Γ),
      contractArgs (ContextualFamily.instantiateArgs assignment arguments) =
        ContextualFamily.instantiate assignment (contractArgs arguments)
  | .cons body arguments => (instantiate_contract assignment body arguments).symm

/-- Contracting the explicit redex of an occurrence substitutes the
occurrence's arguments into the image: the framework beta step. -/
theorem contract_openImage (assignment : Assignment source target) {Γ : Ctx S} (identity : V)
    (arguments : Args (signature S target) ((source identity).1.map (fun b => ([], b))) Γ) :
    contract (evaluate (openImage (Γ := Γ) assignment identity)) arguments =
      bind (argsToSub (S := signature S target) arguments) (assignment identity) := by
  unfold openImage contract
  rw [evaluate_rename, evaluate_incl, bind_rename]
  congr 1
  funext s v
  exact joinSub_prefix (S := signature S target) (source identity).1
    (argsToSub (S := signature S target) arguments) (fun _ position => Term.var position) s v

mutual

/-- **Evaluation turns lazy instantiation into contextual instantiation.** -/
theorem evaluate_lazy (assignment : Assignment source target) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (withRedexes (signature S source)) Γ sort),
      evaluate (lazy assignment term) = ContextualFamily.instantiate assignment (evaluate term)
  | _, _, .var _ => rfl
  | _, _, .op (.inl (.inl original)) arguments => by
      show Term.op (S := signature S target) (Sum.inl original)
          (evaluateArgs (lazyArgs assignment arguments)) =
        Term.op (S := signature S target) (Sum.inl original)
          (ContextualFamily.instantiateArgs assignment (evaluateArgs arguments))
      rw [evaluateArgs_lazyArgs assignment arguments]
  | _, _, .op (.inl (.inr (.mk identity))) arguments => by
      show contract (evaluate (openImage assignment identity)) (evaluateArgs (lazyArgs assignment arguments)) =
        bind (argsToSub (S := signature S target)
            (ContextualFamily.instantiateArgs assignment (evaluateArgs arguments)))
          (assignment identity)
      rw [evaluateArgs_lazyArgs assignment arguments]
      exact contract_openImage assignment identity _
  | _, _, .op (.inr (.apply parameters result)) arguments => by
      show evaluateNode (T := signature S target)
          (Sum.inr (Redex.apply (T := signature S target) parameters result))
          (evaluateArgs (lazyArgs assignment arguments)) =
        ContextualFamily.instantiate assignment
          (evaluateNode (T := signature S source)
            (Sum.inr (Redex.apply (T := signature S source) parameters result))
            (evaluateArgs arguments))
      rw [evaluateArgs_lazyArgs assignment arguments]
      exact contractArgs_instantiateArgs assignment (evaluateArgs arguments)

theorem evaluateArgs_lazyArgs (assignment : Assignment source target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (withRedexes (signature S source)) arities Γ),
      evaluateArgs (lazyArgs assignment arguments) =
        ContextualFamily.instantiateArgs assignment (evaluateArgs arguments)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      show Args.cons (evaluate (lazy assignment head)) (evaluateArgs (lazyArgs assignment tail)) =
        Args.cons (ContextualFamily.instantiate assignment (evaluate head))
          (ContextualFamily.instantiateArgs assignment (evaluateArgs tail))
      rw [evaluate_lazy assignment head, evaluateArgs_lazyArgs assignment tail]

end

/-- **Contextual instantiation is hereditary substitution.** The lazy instance
of a canonical term evaluates to its contextual instance. -/
theorem evaluate_lazy_incl (assignment : Assignment source target) {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) :
    evaluate (lazy assignment (incl term)) = ContextualFamily.instantiate assignment term := by
  rw [evaluate_lazy, evaluate_incl]

/-- The lazy instance reduces, by framework beta steps, to the contextual instance. -/
theorem lazy_reduces_to_instantiate (assignment : Assignment source target) {Γ : Ctx S}
    {sort : S.Srt} (term : Term (signature S source) Γ sort) :
    Relation.ReflTransGen Contracts (lazy assignment (incl term))
      (incl (ContextualFamily.instantiate assignment term)) := by
  have reduces := reduces_evaluate (lazy assignment (incl term))
  rw [evaluate_lazy_incl] at reduces
  exact reduces

/-- **Unification modulo framework conversion is syntactic unification of
canonical terms.** An assignment equates two canonical terms after
contextual instantiation exactly when their lazy instances are convertible. -/
theorem convertible_lazy_iff (assignment : Assignment source target) {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S source) Γ sort) :
    Relation.EqvGen Contracts (lazy assignment (incl left)) (lazy assignment (incl right)) ↔
      ContextualFamily.instantiate assignment left = ContextualFamily.instantiate assignment right := by
  rw [convertible_iff, evaluate_lazy_incl, evaluate_lazy_incl]

/-- The identity principle: the eta-expanded metavariable, instantiated lazily,
evaluates to the metavariable's image. -/
theorem evaluate_lazy_generator (assignment : Assignment source target) (identity : V) :
    evaluate (lazy assignment (incl (ContextualFamily.generator source identity))) =
      assignment identity := by
  rw [evaluate_lazy_incl, ContextualFamily.instantiate_generator]

/-- The lazy instance of an occurrence is an explicit redex, so it is not canonical. -/
theorem lazy_generator_not_canonical (assignment : Assignment source target) (identity : V) :
    ¬ ∃ canonical : Term (signature S target) (source identity).1 (source identity).2,
      incl canonical = lazy assignment (incl (ContextualFamily.generator source identity)) := by
  rintro ⟨canonical, same⟩
  have counted := congrArg redexCount same
  rw [redexCount_incl] at counted
  have positive : 0 < redexCount (lazy assignment (incl (ContextualFamily.generator source identity))) := by
    show 0 < redexCountArgs _ + 1
    omega
  omega

end Contextual

/-! ## Controls -/

namespace Controls

open ContextualFamily (signature Assignment)

inductive DataOperator where
  | symbol : Nat → DataOperator
  | pair
  deriving DecidableEq

abbrev data : Signature where
  Srt := Unit
  Op _ := DataOperator
  arity
    | .symbol _ => []
    | .pair => [([], ()), ([], ())]

/-- One metavariable with one parameter. -/
def unary (_ : Unit) : MetaArity data := ([()], ())

/-- No metavariables. -/
def closed (impossible : Empty) : MetaArity data := nomatch impossible

def symbol {V : Type} {declaration : V → MetaArity data} {Γ : Ctx data} (number : Nat) :
    Term (signature data declaration) Γ () :=
  .op (.inl (.symbol number)) .nil

def pair {V : Type} {declaration : V → MetaArity data} {Γ : Ctx data}
    (first second : Term (signature data declaration) Γ ()) : Term (signature data declaration) Γ () :=
  .op (.inl .pair) (.cons first (.cons second .nil))

/-- The image `pair x 2` of the metavariable. -/
def image : Assignment unary closed := fun _ => pair (.var .zero) (symbol 2)

/-- The occurrence `F[1]`. -/
def occurrence : Term (signature data unary) [] () :=
  .op (.inr (.mk ())) (.cons (symbol 1) .nil)

/-- The lazy instance is an explicit framework redex. -/
theorem lazy_occurrence :
    lazy image (incl occurrence) =
      .op (Sum.inr (Redex.apply (T := signature data closed) [()] ()))
        (.cons (openImage image ()) (.cons (incl (symbol 1)) .nil)) :=
  rfl

theorem lazy_occurrence_not_canonical :
    ¬ ∃ canonical : Term (signature data closed) [] (), incl canonical = lazy image (incl occurrence) := by
  rintro ⟨canonical, same⟩
  have counted := congrArg redexCount same
  rw [redexCount_incl] at counted
  have positive : 0 < redexCount (lazy image (incl occurrence)) := by
    show 0 < redexCountArgs _ + 1
    omega
  omega

/-- Positive control: evaluation computes `pair 1 2`. -/
theorem evaluate_lazy_occurrence :
    evaluate (lazy image (incl occurrence)) = pair (symbol 1) (symbol 2) :=
  (evaluate_lazy_incl image occurrence).trans rfl

theorem lazy_occurrence_reduces :
    Relation.ReflTransGen Contracts (lazy image (incl occurrence)) (incl (pair (symbol 1) (symbol 2))) := by
  have reduces := lazy_reduces_to_instantiate image occurrence
  have computed : ContextualFamily.instantiate image occurrence = pair (symbol 1) (symbol 2) := rfl
  rw [computed] at reduces
  exact reduces

/-- Negative control: distinct canonical constants are not convertible. -/
theorem distinct_symbols_not_convertible :
    ¬ Relation.EqvGen Contracts (incl (symbol (declaration := closed) (Γ := []) 1))
      (incl (symbol (declaration := closed) (Γ := []) 2)) := by
  rw [convertible_iff, evaluate_incl, evaluate_incl]
  intro same
  have heads := Term.op.inj same
  have operators : DataOperator.symbol 1 = DataOperator.symbol 2 := Sum.inl.inj heads.1
  cases operators

end Controls

end Mettapedia.OSLF.Binding.HereditaryBetaEta

open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms evaluate_incl
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms evaluate_bind
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms evaluate_contracts
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms reduces_evaluate
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms convertible_iff
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms canonical_iff_irreducible
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms evaluate_lazy
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms evaluate_lazy_incl
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms lazy_reduces_to_instantiate
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms convertible_lazy_iff
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms evaluate_lazy_generator
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms lazy_generator_not_canonical
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms Controls.lazy_occurrence_not_canonical
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms Controls.evaluate_lazy_occurrence
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms Controls.lazy_occurrence_reduces
open Mettapedia.OSLF.Binding.HereditaryBetaEta in
#print axioms Controls.distinct_symbols_not_convertible
