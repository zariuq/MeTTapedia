import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersNested
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersPending

/-!
# Raising root equations along binders

A call under a binder may use that binder: the holes of an equation written at the root must be
allowed to depend on it. **Raising** (Miller's) adds one new binder to every hole's parameters and
passes it at every occurrence; object variables are renamed into the larger context.
- `instantiate_raise`: instantiating a raised term by a solution that ignores the new binder is
  renaming the original instance. So every root answer, weakened, is an answer of the raised
  equation (`raise_answers`).
- `raise_pattern`: raising keeps Miller patterns, since the new binder is distinct from every
  renamed variable. Principal answers survive raising.
- For λ contexts, `raiseAt` raises along every binder the context passes; at the hole it is the
  equation itself.

**Controls**, with root equations only:
- `(= (k $y) $y)` rewrites `λx. (k x)` to `λx. x` (`raised_under_binder`);
- for `(= (k (λz. $N)) $N)` under `λx`, the hole takes `x` (`raised_outer_available`), but never
  the pattern's own `z` (`raised_inner_refused`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment (Pattern PatternArgs)

variable {S : Signature} {V : Type} {source : V → MetaArity S}

/-- Every hole also lists one new binder of sort `binder`, first. -/
abbrev raisedArity (binder : S.Srt) (source : V → MetaArity S) : V → MetaArity S :=
  fun hole => (binder :: (source hole).1, (source hole).2)

mutual
/-- Rename object variables by `ρ`, and pass the new binder `fresh` first at every hole occurrence. -/
def raiseTerm (binder : S.Srt) : {Θ Θ' : Ctx S} → {sort : S.Srt} → Ren S Θ Θ' → Var Θ' binder →
    Term (signature S source) Θ sort → Term (signature S (raisedArity binder source)) Θ' sort
  | _, _, _, ρ, _, .var position => .var (ρ _ position)
  | _, _, _, ρ, fresh, .op (.inl operator) arguments => .op (.inl operator) (raiseArgs binder ρ fresh arguments)
  | _, _, _, ρ, fresh, .op (.inr (.mk identity)) arguments =>
      .op (.inr (.mk identity)) (.cons (.var fresh) (raiseArgs binder ρ fresh arguments))

def raiseArgs (binder : S.Srt) : {arities : List (MetaArity S)} → {Θ Θ' : Ctx S} → Ren S Θ Θ' →
    Var Θ' binder → Args (signature S source) arities Θ → Args (signature S (raisedArity binder source)) arities Θ'
  | _, _, _, _, _, .nil => .nil
  | _, _, _, ρ, fresh, .cons (bs := binders) head tail =>
      .cons (raiseTerm binder (liftRen ρ binders) (weakenVar (S := S) binders fresh) head)
        (raiseArgs binder ρ fresh tail)
end

/-- A solution that ignores the new binder. -/
def weakenSolution (binder : S.Srt) {W : Type} {target : W → MetaArity S} (θ : Assignment source target) :
    Assignment (raisedArity binder source) target :=
  fun hole => rename (fun _ position => .succ position) (θ hole)

mutual
theorem instantiate_raise (binder : S.Srt) {W : Type} {target : W → MetaArity S} (θ : Assignment source target) :
    ∀ {Θ Θ' : Ctx S} {sort : S.Srt} (ρ : Ren S Θ Θ') (fresh : Var Θ' binder)
      (term : Term (signature S source) Θ sort),
      instantiate (weakenSolution binder θ) (raiseTerm binder ρ fresh term) =
        rename (S := signature S target) ρ (instantiate θ term)
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, ρ, fresh, .op (.inl operator) arguments =>
      congrArg (Term.op (S := signature S target) (Sum.inl operator)) (instantiateArgs_raise binder θ ρ fresh arguments)
  | _, _, _, ρ, fresh, .op (.inr (.mk identity)) arguments => by
      change Mettapedia.OSLF.Binding.bind (S := signature S target)
          (argsToSub (S := signature S target) (bs := binder :: (source identity).1)
            (Args.cons (S := signature S target) (bs := []) (Term.var fresh)
              (instantiateArgs (weakenSolution binder θ) (raiseArgs binder ρ fresh arguments))))
          (rename (fun _ position => Var.succ position) (θ identity)) =
        rename (S := signature S target) ρ (Mettapedia.OSLF.Binding.bind (S := signature S target)
          (argsToSub (S := signature S target) (bs := (source identity).1) (instantiateArgs θ arguments))
          (θ identity))
      rw [bind_rename, rename_bind, instantiateArgs_raise binder θ ρ fresh arguments]
      congr 1
      funext sort position
      exact argsToSub_renameArgs (T := signature S target) ρ (source identity).1 (instantiateArgs θ arguments)
        sort position

theorem instantiateArgs_raise (binder : S.Srt) {W : Type} {target : W → MetaArity S} (θ : Assignment source target) :
    ∀ {arities : List (MetaArity S)} {Θ Θ' : Ctx S} (ρ : Ren S Θ Θ') (fresh : Var Θ' binder)
      (arguments : Args (signature S source) arities Θ),
      instantiateArgs (weakenSolution binder θ) (raiseArgs binder ρ fresh arguments) =
        renameArgs (S := signature S target) ρ (instantiateArgs θ arguments)
  | _, _, _, _, _, .nil => rfl
  | _, _, _, ρ, fresh, .cons (bs := binders) head tail =>
      congrArg₂ (Args.cons (S := signature S target))
        (instantiate_raise binder θ (liftRen ρ binders) (weakenVar (S := S) binders fresh) head)
        (instantiateArgs_raise binder θ ρ fresh tail)
end

/-! ## Miller patterns survive raising -/

/-- Extend a renaming of the parameters by the new binder, first. -/
def consRen {binder : S.Srt} {Ψ Θ : Ctx S} (fresh : Var Θ binder) (rest : Ren S Ψ Θ) : Ren S (binder :: Ψ) Θ
  | _, .zero => fresh
  | _, .succ position => rest _ position

theorem lift_avoids {binder : S.Srt} {Θ Θ' : Ctx S} (ρ : Ren S Θ Θ') (fresh : Var Θ' binder)
    (avoids : ∀ position, ρ binder position ≠ fresh) :
    ∀ (binders : Ctx S) (position : Var (binders ++ Θ) binder),
      liftRen ρ binders binder position ≠ weakenVar binders fresh
  | [], position => avoids position
  | _ :: _, .zero => by intro same; cases same
  | _ :: rest, .succ position => by
      intro same
      exact lift_avoids ρ fresh avoids rest position (Var.succ.inj same)

theorem argsToSub_raiseArgs (binder : S.Srt) {Θ Θ' : Ctx S} (ρ : Ren S Θ Θ') (fresh : Var Θ' binder) :
    ∀ (parameters : Ctx S) (arguments : Args (signature S source) (parameters.map fun sort => ([], sort)) Θ)
      (sort : S.Srt) (position : Var parameters sort),
      argsToSub (raiseArgs binder ρ fresh arguments) sort position =
        raiseTerm binder ρ fresh (argsToSub arguments sort position)
  | [], _, _, position => nomatch position
  | _ :: _, .cons _ _, _, .zero => rfl
  | _ :: rest, .cons _ tail, sort, .succ position => argsToSub_raiseArgs binder ρ fresh rest tail sort position

theorem raise_pattern (binder : S.Srt) {Θ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Θ sort)
    (patterned : Pattern S source term) {Θ' : Ctx S} (ρ : Ren S Θ Θ') (fresh : Var Θ' binder)
    (injective : ∀ sort, Function.Injective (ρ sort)) (avoids : ∀ position, ρ binder position ≠ fresh) :
    Pattern S (raisedArity binder source) (raiseTerm binder ρ fresh term) := by
  refine Pattern.rec
    (motive_1 := fun {context} _ value _ =>
      ∀ {next : Ctx S} (mapping : Ren S context next) (new : Var next binder),
        (∀ sort, Function.Injective (mapping sort)) → (∀ position, mapping binder position ≠ new) →
          Pattern S (raisedArity binder source) (raiseTerm binder mapping new value))
    (motive_2 := fun {_} {context} values _ =>
      ∀ {next : Ctx S} (mapping : Ren S context next) (new : Var next binder),
        (∀ sort, Function.Injective (mapping sort)) → (∀ position, mapping binder position ≠ new) →
          PatternArgs S (raisedArity binder source) (raiseArgs binder mapping new values))
    ?_ ?_ ?_ ?_ ?_ patterned ρ fresh injective avoids
  · intro context result position next mapping new _ _
    exact Pattern.object (S := S) (declaration := raisedArity binder source) (mapping result position)
  · intro context result operator arguments fields checked next mapping new oneToOne apart
    exact Pattern.rigid operator _ (checked mapping new oneToOne apart)
  · intro context identity arguments spineMap spine distinct next mapping new oneToOne apart
    refine Pattern.hole (S := S) (declaration := raisedArity binder source) identity
      (Args.cons (S := signature S (raisedArity binder source)) (bs := []) (Term.var new)
        (raiseArgs binder mapping new arguments))
      (consRen new (fun sort position => mapping sort (spineMap sort position))) ?_ ?_
    · intro result position
      cases position with
      | zero => rfl
      | succ position =>
          change argsToSub (raiseArgs binder mapping new arguments) result position = _
          rw [argsToSub_raiseArgs, spine]
          rfl
    · intro result first second same
      cases first with
      | zero =>
          cases second with
          | zero => rfl
          | succ second => exact absurd same.symm (apart _)
      | succ first =>
          cases second with
          | zero => exact absurd same (apart _)
          | succ second =>
              exact congrArg Var.succ (distinct result (oneToOne result same))
  · intro context next mapping new _ _
    exact .nil
  · intro arities context binders result head tail first rest checkedHead checkedTail next mapping new oneToOne apart
    exact .cons _ _ (checkedHead (liftRen mapping binders) (weakenVar (S := S) binders new)
      (RenamingSlots.lift_injective mapping oneToOne binders) (lift_avoids mapping new apart binders))
      (checkedTail mapping new oneToOne apart)

/-! ## Raising an equation by one binder -/

variable {Γ : Ctx S} {sort : S.Srt}

/-- The equation under one more binder of sort `binder`: every hole may use it. -/
def raiseOne (binder : S.Srt) (e : Equation S Γ sort) : Equation S (binder :: Γ) sort :=
  ⟨e.Holes, e.holesEq, raisedArity binder e.arity,
    raiseTerm binder (fun _ position => .succ position) .zero e.lhs,
    raiseTerm binder (fun _ position => .succ position) .zero e.rhs⟩

theorem raiseOne_pattern (binder : S.Srt) (e : Equation S Γ sort) (patterned : Pattern S e.arity e.lhs) :
    Pattern S (raiseOne binder e).arity (raiseOne binder e).lhs :=
  raise_pattern binder e.lhs patterned _ _ (fun _ _ _ same => Var.succ.inj same) (fun _ same => by cases same)

/-- **Root answers survive raising**, weakened past the new binder. -/
theorem raise_answers (binder : S.Srt) (e : Equation S Γ sort) {call answer : Term S Γ sort}
    (answered : Answers e call answer) :
    Answers (raiseOne binder e) (weaken (t := binder) call) (weaken (t := binder) answer) := by
  obtain ⟨θ, matched, read⟩ := answered
  have weakened : (raiseOne binder e).assign (fun hole => weaken (t := binder) (θ hole)) (ground S) =
      weakenSolution binder (e.assign θ (ground S)) := by
    funext hole
    exact Rigid.include_rename (ground S) _ (θ hole)
  refine ⟨fun hole => weaken (t := binder) (θ hole), ?_, ?_⟩
  · change instantiate _ (raiseTerm binder _ _ e.lhs) = _
    rw [weakened, instantiate_raise, matched]
    exact (Rigid.include_rename (ground S) _ call).symm
  · change instantiate _ (raiseTerm binder _ _ e.rhs) = _
    rw [weakened, instantiate_raise, read]
    exact (Rigid.include_rename (ground S) _ answer).symm

/-! ## λ contexts -/

namespace Nested

open LambdaContextualRung (sig Srt Context appT lamT)
open LambdaComparison (app lam app_inj lam_inj)
open Controls (Consts)

/-- Raise an equation along every binder the context passes. At the hole it is the equation. -/
def raiseAt : {Γ Δ : Ctx sig} → Context Γ Δ → Equation sig Γ .term → Equation sig Δ .term
  | _, _, .hole, e => e
  | _, _, .appLeft inner _, e => raiseAt inner e
  | _, _, .appRight _ inner, e => raiseAt inner e
  | _, _, .underLam inner, e => raiseAt inner (raiseOne Srt.term e)

theorem raiseAt_pattern : ∀ {Γ Δ : Ctx sig} (context : Context Γ Δ) (e : Equation sig Γ .term),
    Pattern sig e.arity e.lhs → Pattern sig (raiseAt context e).arity (raiseAt context e).lhs
  | _, _, .hole, _, patterned => patterned
  | _, _, .appLeft inner _, e, patterned => raiseAt_pattern inner e patterned
  | _, _, .appRight _ inner, e, patterned => raiseAt_pattern inner e patterned
  | _, _, .underLam inner, e, patterned => raiseAt_pattern inner _ (raiseOne_pattern Srt.term e patterned)

/-- A root program, raised along each context's binders. -/
def raisedSchema {Γ : Ctx sig} {ι : Type} (program : ι → Equation sig Γ .term) : Schema grammar Γ ι :=
  fun context index => raiseAt context (program index)

/-- `(= (k $y) $y)` at the root: the hole lists the constants. -/
def callRoot : Equation sig Consts .term :=
  ⟨Unit, inferInstance, fun _ => (Consts, .term), app _ (.var .zero) (generator _ ()), generator _ ()⟩

/-- `(= (k (λz. $N)) $N)` at the root. -/
def scopeRoot : Equation sig Consts .term :=
  ⟨Unit, inferInstance, fun _ => (Consts, .term),
    app _ (.var .zero) (lam _ (weaken (generator (fun _ : Unit => ((Consts, .term) : MetaArity sig)) ()))),
    generator _ ()⟩

/-- **Raised under `λx`**, the root equation rewrites `λx. (k x)` to `λx. x`. -/
theorem raised_under_binder :
    CRewrites grammar (raisedSchema fun _ : Unit => callRoot)
      (lamT (appT (.var (.succ .zero)) (.var .zero)) : Term sig Consts .term) (lamT (.var .zero)) :=
  ⟨_, .underLam .hole, (), _, _, rfl, rfl, fun _ => .var .zero, rfl, rfl⟩

/-- Raised under `λx`, the hole of `(= (k (λz. $N)) $N)` takes `x`. -/
theorem raised_outer_available :
    Answers (raiseAt (Γ := Consts) (.underLam .hole) scopeRoot)
      (appT (.var (.succ .zero)) (lamT (.var (.succ .zero)))) (.var .zero) :=
  ⟨fun _ => .var .zero, rfl, rfl⟩

/-- The substitution at the raised occurrence of `$N` under `λx. … (λz. …)`: `x`, `k`, `a`, never `z`. -/
def scopeArgs {W : Type} (target : W → MetaArity sig) :
    Args (signature sig target) ([Srt.term, Srt.term, Srt.term].map fun sort => ([], sort))
      (Srt.term :: Srt.term :: Consts) :=
  .cons (.var (.succ .zero)) (.cons (.var (.succ (.succ .zero))) (.cons (.var (.succ (.succ (.succ .zero)))) .nil))

def scopeSub {W : Type} (target : W → MetaArity sig) :
    Sub (signature sig target) [Srt.term, Srt.term, Srt.term] (Srt.term :: Srt.term :: Consts) :=
  argsToSub (scopeArgs target)

theorem instantiate_raised_scope {W : Type} {target : W → MetaArity sig}
    (change : Assignment (raiseAt (Γ := Consts) (.underLam .hole) scopeRoot).arity target) :
    instantiate change (raiseAt (Γ := Consts) (.underLam .hole) scopeRoot).lhs =
      app target (.var (.succ .zero)) (lam target (Mettapedia.OSLF.Binding.bind (scopeSub target) (change ()))) :=
  rfl

/-- Raised under `λx`, the hole of `(= (k (λz. $N)) $N)` never captures the pattern's `z`. -/
theorem raised_inner_refused (answer : Term sig (.term :: Consts) .term) :
    ¬ Answers (raiseAt (Γ := Consts) (.underLam .hole) scopeRoot)
      (appT (.var (.succ .zero)) (lamT (.var .zero))) answer := by
  rintro ⟨θ, matched, _⟩
  have opened := (instantiate_raised_scope _).symm.trans matched
  have body := lam_inj (app_inj opened).2
  obtain ⟨position, isVar⟩ := Controls.bind_var_shape _ _ _ body
  have atPosition : Mettapedia.OSLF.Binding.bind (scopeSub (ground sig)) (Term.var position) =
      Term.var Var.zero := isVar ▸ body
  match position, atPosition with
  | .zero, atPosition => cases atPosition
  | .succ .zero, atPosition => cases atPosition
  | .succ (.succ .zero), atPosition => cases atPosition

/-- β and `(= (k $y) $y)`, both written at the root. -/
def rootProgram : Bool → Equation sig Consts .term := fun rule => cond rule (betaEquation Consts) callRoot

/-- **Root equations, raised, in both orders.** In `(λx. (k x)) a`, β at the root and the raised call
under `λx` both fire, and both orders reach `a`, on the step too. -/
theorem raised_both_orders :
    CRewrites grammar (raisedSchema rootProgram) nestedProgram (appT Controls.fC Controls.gC) ∧
      CRewrites grammar (raisedSchema rootProgram) nestedProgram (appT (lamT (.var .zero)) Controls.gC) ∧
      Relation.ReflTransGen (CRewrites grammar (raisedSchema rootProgram)) nestedProgram Controls.gC ∧
      Relation.ReflTransGen (CRewrites grammar (raisedSchema rootProgram))
        (appT (lamT (.var .zero)) Controls.gC) Controls.gC ∧
      ∃ after, Relation.ReflTransGen (Transition (contextProgram grammar (raisedSchema rootProgram)))
          (initial nestedProgram) after ∧
        Reads (contextProgram grammar (raisedSchema rootProgram)) after Controls.gC := by
  have betaRoot : CRewrites grammar (raisedSchema rootProgram) nestedProgram (appT Controls.fC Controls.gC) :=
    ⟨_, .hole, true, _, _, rfl, rfl, (beta_answers _ _).mpr ⟨_, _, rfl, rfl⟩⟩
  have callUnder : CRewrites grammar (raisedSchema rootProgram) nestedProgram
      (appT (lamT (.var .zero)) Controls.gC) :=
    ⟨_, .appLeft (.underLam .hole) Controls.gC, false, _, _, rfl, rfl, fun _ => .var .zero, rfl, rfl⟩
  have callAtRoot : CRewrites grammar (raisedSchema rootProgram) (appT Controls.fC Controls.gC) Controls.gC :=
    ⟨_, .hole, false, _, _, rfl, rfl, fun _ => Controls.gC, rfl, rfl⟩
  have betaAfter : CRewrites grammar (raisedSchema rootProgram) (appT (lamT (.var .zero)) Controls.gC)
      Controls.gC :=
    ⟨_, .hole, true, _, _, rfl, rfl, (beta_answers _ _).mpr ⟨_, _, rfl, rfl⟩⟩
  have whole := (Relation.ReflTransGen.single betaRoot).tail callAtRoot
  exact ⟨betaRoot, callUnder, whole, .single betaAfter, (context_execution_iff _ _ _).mp whole⟩

/-- Raised Miller-pattern root programs keep principal answers: at the initial state of any call,
an admitted firing in any λ context has a completed worklist run. -/
theorem raised_principal_first {Γ : Ctx sig} {ι : Type} [DecidableEq ι] (program : ι → Equation sig Γ .term)
    (patterns : ∀ index, Pattern sig (program index).arity (program index).lhs) (call : Term sig Γ .term)
    (key : Σ Δ : Ctx sig, grammar.Context Γ Δ × ι)
    (valid : Admitted (contextProgram grammar (raisedSchema program)) (initial call) key) :
    ∃ (fuel : Nat) (update : ContextualFrameUpdate.Update (firingProblem (initial call) key)),
      (letI := (destination (contextProgram grammar (raisedSchema program)) (initial call) key valid).1.equality;
        ContextualFrameWorklist.run fuel (active (contextProgram grammar (raisedSchema program))
          (initial (program := contextProgram grammar (raisedSchema program)) call).1.declarations)
          (firingProblem (initial call) key)) = .residual update ∧
        update.remaining = [] := by
  obtain ⟨fuel, update, computed, empty, _⟩ := principal_firing (initial call) key valid (initial_pattern call)
    (atContext_pattern key.2.1 _ (raiseAt_pattern key.2.1 (program key.2.2) (patterns key.2.2)))
  exact ⟨fuel, update, computed, empty⟩

end Nested

#print axioms instantiate_raise
#print axioms lift_avoids
#print axioms raise_pattern
#print axioms raiseOne_pattern
#print axioms raise_answers
#print axioms Nested.raiseAt_pattern
#print axioms Nested.raised_under_binder
#print axioms Nested.raised_outer_available
#print axioms Nested.raised_inner_refused
#print axioms Nested.raised_both_orders
#print axioms Nested.raised_principal_first

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
