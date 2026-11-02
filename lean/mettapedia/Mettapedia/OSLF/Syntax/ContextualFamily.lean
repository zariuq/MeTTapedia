import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# Contextual substitution over an arbitrary family of declarations

A declaration gives each metavariable its parameter context and result sort.
The family of identities need not be finite. Metavariables extend the existing
binding signature as operators; terms and capture-avoiding object substitution
are the existing `Term`, `Args` and `bind` operations.

Images may contain unresolved metavariables in another declaration family.
Instantiation preserves object-variable renaming and substitution, and its
composition is associative. No solver, most-general-answer assumption, or
restriction on general application spines is imposed here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W X : Type}

inductive Operator (declaration : V → MetaArity S) : S.Srt → Type where
  | mk (identity : V) : Operator declaration (declaration identity).2

def Operator.key {declaration : V → MetaArity S} :
    {sort : S.Srt} → Operator declaration sort → V
  | _, .mk identity => identity

private theorem Operator.key_heq {declaration : V → MetaArity S} :
    ∀ {sort otherSort : S.Srt} (first : Operator declaration sort) (second : Operator declaration otherSort),
      first.key = second.key → HEq first second
  | _, _, .mk identity, .mk other, same => by cases same; rfl

theorem Operator.key_injective {declaration : V → MetaArity S} {sort : S.Srt} :
    Function.Injective (Operator.key (declaration := declaration) (sort := sort)) :=
  fun _ _ same => eq_of_heq (Operator.key_heq _ _ same)

instance {declaration : V → MetaArity S} [DecidableEq V] {sort : S.Srt} :
    DecidableEq (Operator declaration sort) := Operator.key_injective.decidableEq

/-- Extend operators without introducing a second term syntax. -/
abbrev signature (S : Signature) {V : Type} (declaration : V → MetaArity S) : Signature where
  Srt := S.Srt
  Op sort := S.Op sort ⊕ Operator declaration sort
  arity operator := match operator with
    | .inl original => S.arity original
    | .inr (.mk identity) => (declaration identity).1.map (fun sort => ([], sort))

/-- Formal parameter projections, available over every binding signature. -/
def selfArgs {T : Signature} :
    (parameters : Ctx T) → Args T (parameters.map (fun sort => ([], sort))) parameters
  | [] => .nil
  | _ :: rest => .cons (.var .zero) (renameArgs (fun _ index => .succ index) (selfArgs rest))

theorem argsToSub_selfArgs {T : Signature} :
    ∀ (parameters : Ctx T) (sort : T.Srt) (index : Var parameters sort),
      argsToSub (selfArgs parameters) sort index = Term.var (S := T) index
  | [], _, index => nomatch index
  | _ :: _, _, .zero => rfl
  | _ :: rest, sort, .succ index => by
      simp only [selfArgs, argsToSub, argsToSub_renameArgs,
        argsToSub_selfArgs rest sort index, rename]

theorem bindArgs_selfArgs {T : Signature} :
    ∀ (parameters : Ctx T) {Γ : Ctx T}
      (arguments : Args T (parameters.map (fun sort => ([], sort))) Γ),
      bindArgs (argsToSub arguments) (selfArgs parameters) = arguments
  | [], _, arguments => by cases arguments; rfl
  | _ :: rest, _, .cons head tail => by
      simp only [selfArgs, bindArgs, liftSub, bind, argsToSub, bindArgs_rename,
        bindArgs_selfArgs rest tail]

def generator (declaration : V → MetaArity S) (identity : V) :
    Term (signature S declaration) (declaration identity).1 (declaration identity).2 :=
  .op (.inr (.mk identity)) (selfArgs (T := signature S declaration) (declaration identity).1)

abbrev Assignment (source : V → MetaArity S) (target : W → MetaArity S) :=
  (identity : V) → Term (signature S target) (source identity).1 (source identity).2

variable {source : V → MetaArity S} {target : W → MetaArity S}
  {next : X → MetaArity S}

mutual

/-- Contextual instantiation acts on both sides of an equation. An image
uses exactly its declared parameters; occurrence arguments supply them. -/
def instantiate (assignment : Assignment source target) :
    {Γ : Ctx S} → {sort : S.Srt} →
      Term (signature S source) Γ sort → Term (signature S target) Γ sort
  | _, _, .var index => .var index
  | _, _, .op (.inl original) arguments =>
      .op (.inl original) (instantiateArgs assignment arguments)
  | _, _, .op (.inr (.mk identity)) arguments =>
      bind (argsToSub (instantiateArgs assignment arguments)) (assignment identity)

def instantiateArgs (assignment : Assignment source target) :
    {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      Args (signature S source) arities Γ → Args (signature S target) arities Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (instantiate assignment head) (instantiateArgs assignment tail)

end

mutual

theorem instantiate_rename (assignment : Assignment source target) :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (rho : Ren S Γ Δ)
      (term : Term (signature S source) Γ sort),
      instantiate assignment (rename (S := signature S source) rho term) =
        rename (S := signature S target) rho (instantiate assignment term)
  | _, _, _, _, .var _ => rfl
  | _, _, _, rho, .op (.inl original) arguments => by
      simp only [rename, instantiate, instantiateArgs_renameArgs assignment rho arguments]
  | _, _, _, rho, .op (.inr (.mk identity)) arguments => by
      simp only [rename, instantiate, instantiateArgs_renameArgs assignment rho arguments,
        rename_bind]
      congr 1
      funext sort index
      exact argsToSub_renameArgs (T := signature S target) rho _ _ sort index

theorem instantiateArgs_renameArgs (assignment : Assignment source target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S} (rho : Ren S Γ Δ)
      (arguments : Args (signature S source) arities Γ),
      instantiateArgs assignment (renameArgs (S := signature S source) rho arguments) =
        renameArgs (S := signature S target) rho (instantiateArgs assignment arguments)
  | _, _, _, _, .nil => rfl
  | _, _, _, rho, .cons (bs := binders) head tail => by
      simp only [renameArgs, instantiateArgs,
        instantiateArgs_renameArgs assignment rho tail]
      exact congrArg₂ Args.cons
        (instantiate_rename assignment (liftRen rho binders) head) rfl

end

theorem instantiateArgs_selfArgs (assignment : Assignment source target) :
    ∀ (parameters : Ctx S),
      instantiateArgs assignment (selfArgs (T := signature S source) parameters) =
        selfArgs (T := signature S target) parameters
  | [] => rfl
  | _ :: rest => by
      simp only [selfArgs, instantiateArgs, instantiate, instantiateArgs_renameArgs,
        instantiateArgs_selfArgs assignment rest]

theorem instantiate_generator (assignment : Assignment source target) (identity : V) :
    instantiate assignment (generator source identity) = assignment identity := by
  simp only [generator, instantiate, instantiateArgs_selfArgs]
  have projections : argsToSub (selfArgs (T := signature S target) (source identity).1) =
      fun _ index => Term.var (S := signature S target) index := by
    funext sort index
    exact argsToSub_selfArgs _ sort index
  rw [projections, bind_id]

mutual

theorem instantiate_identity :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      instantiate (generator source) term = term
  | _, _, .var _ => rfl
  | _, _, .op (.inl original) arguments => by
      simp only [instantiate, instantiateArgs_identity arguments]
  | _, _, .op (.inr (.mk identity)) arguments => by
      simp only [instantiate, instantiateArgs_identity arguments, generator, bind,
        bindArgs_selfArgs]

theorem instantiateArgs_identity :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (signature S source) arities Γ),
      instantiateArgs (generator source) arguments = arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [instantiateArgs, instantiate_identity head, instantiateArgs_identity tail]

end

theorem argsToSub_instantiateArgs (assignment : Assignment source target) :
    ∀ (parameters : Ctx S) {Γ : Ctx S}
      (arguments : Args (signature S source) (parameters.map (fun sort => ([], sort))) Γ)
      (sort : S.Srt) (index : Var parameters sort),
      argsToSub (instantiateArgs assignment arguments) sort index =
        instantiate assignment (argsToSub arguments sort index)
  | [], _, _, _, index => nomatch index
  | _ :: _, _, .cons _ _, _, .zero => rfl
  | _ :: rest, _, .cons _ tail, sort, .succ index =>
      argsToSub_instantiateArgs assignment rest tail sort index

theorem instantiate_liftSub (assignment : Assignment source target)
    {Γ Δ : Ctx S} (environment : Sub (signature S source) Γ Δ) :
    ∀ (binders : Ctx S) (sort : S.Srt) (index : Var (binders ++ Γ) sort),
      instantiate assignment (liftSub environment binders sort index) =
        liftSub (fun sort index => instantiate assignment (environment sort index)) binders sort index
  | [], _, _ => rfl
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ index => by
      simp only [liftSub, weaken, instantiate_rename,
        instantiate_liftSub assignment environment binders sort index]

mutual

/-- Object substitution and metavariable instantiation commute, including
the binder lifting on every operator argument. -/
theorem instantiate_bind (assignment : Assignment source target) :
    ∀ {Γ Δ : Ctx S} {sort : S.Srt} (environment : Sub (signature S source) Γ Δ)
      (term : Term (signature S source) Γ sort),
      instantiate assignment (bind environment term) =
        bind (fun sort index => instantiate assignment (environment sort index))
          (instantiate assignment term)
  | _, _, _, _, .var _ => rfl
  | _, _, _, environment, .op (.inl original) arguments => by
      simp only [bind, instantiate, instantiateArgs_bindArgs assignment environment arguments]
  | _, _, _, environment, .op (.inr (.mk identity)) arguments => by
      simp only [bind, instantiate, instantiateArgs_bindArgs assignment environment arguments, bind_comp]
      congr 1
      funext sort index
      exact argsToSub_bindArgs _ _ _ sort index

theorem instantiateArgs_bindArgs (assignment : Assignment source target) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ Δ : Ctx S}
      (environment : Sub (signature S source) Γ Δ)
      (arguments : Args (signature S source) arities Γ),
      instantiateArgs assignment (bindArgs environment arguments) =
        bindArgs (fun sort index => instantiate assignment (environment sort index))
          (instantiateArgs assignment arguments)
  | _, _, _, _, .nil => rfl
  | _, _, _, environment, .cons (bs := binders) head tail => by
      have lifted : (fun sort index => instantiate assignment (liftSub environment binders sort index)) =
          liftSub (fun sort index => instantiate assignment (environment sort index)) binders := by
        funext sort index
        exact instantiate_liftSub assignment environment binders sort index
      simp only [bindArgs, instantiateArgs,
        instantiateArgs_bindArgs assignment environment tail,
        instantiate_bind assignment (liftSub environment binders) head, lifted]

end

mutual

/-- Contextual assignments compose without expanding their variables into
ground terms or changing any declared parameter context. -/
theorem instantiate_comp (first : Assignment source target) (second : Assignment target next) :
    ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
      instantiate second (instantiate first term) =
        instantiate (fun identity => instantiate second (first identity)) term
  | _, _, .var _ => rfl
  | _, _, .op (.inl original) arguments => by
      simp only [instantiate, instantiateArgs_comp first second arguments]
  | _, _, .op (.inr (.mk identity)) arguments => by
      have parameters :
          (fun sort index => instantiate second (argsToSub (instantiateArgs first arguments) sort index)) =
            argsToSub (instantiateArgs (fun identity => instantiate second (first identity)) arguments) := by
        funext sort index
        rw [← argsToSub_instantiateArgs second _ (instantiateArgs first arguments) sort index,
          instantiateArgs_comp first second arguments]
      simp only [instantiate, instantiate_bind, parameters]

theorem instantiateArgs_comp (first : Assignment source target) (second : Assignment target next) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (arguments : Args (signature S source) arities Γ),
      instantiateArgs second (instantiateArgs first arguments) =
        instantiateArgs (fun identity => instantiate second (first identity)) arguments
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [instantiateArgs, instantiate_comp first second head,
        instantiateArgs_comp first second tail]

end

end Mettapedia.OSLF.Binding.ContextualFamily
