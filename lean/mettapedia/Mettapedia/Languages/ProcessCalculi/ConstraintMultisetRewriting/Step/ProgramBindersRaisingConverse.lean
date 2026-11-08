import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersRaisingConverseGrammar

/-!
# The converse of `raise_answers`

Raising an equation by one binder adds no answers. If the raised equation answers a call that does
not mention the new binder by an answer that does not mention it, the root equation answers the call
by that answer (`raise_answers_converse`). With R98's `raise_answers` this is an equivalence
(`raise_answers_iff`), and along every λ context and every active quoted-λ context
(`Nested.raiseAt_answers_iff`, `Quoted.raiseAt_answers_iff`).

**The proof** substitutes a closed term for the new binder. A raised solution may use the binder;
`closeBinder` replaces it by a closed term in every hole's solution. Substituting the closed term into
an instance of a raised term is the instance of the original term under the closed solution
(`bind_raise`). A call that does not mention the binder is unchanged by the substitution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} [ClosedTerms S]

/-! ## Closed terms are fixed by renaming and substitution -/

/-- The closed term of a sort, in any context, over a signature with holes. -/
def closedIn {W : Type} (target : W → MetaArity S) (Ξ : Ctx S) (sort : S.Srt) : Term (signature S target) Ξ sort :=
  Rigid.includeTerm target (closedAt Ξ sort)

theorem rename_closedIn {W : Type} (target : W → MetaArity S) {Ξ Ξ' : Ctx S} (ρ : Ren S Ξ Ξ') (sort : S.Srt) :
    rename (S := signature S target) ρ (closedIn target Ξ sort) = closedIn target Ξ' sort := by
  unfold closedIn closedAt
  rw [Rigid.include_rename, Rigid.include_rename, rename_comp]
  congr 1
  funext _ impossible
  exact nomatch impossible

theorem bind_closedIn {W : Type} (target : W → MetaArity S) {Ξ Ξ' : Ctx S}
    (σ : Sub (signature S target) Ξ Ξ') (sort : S.Srt) :
    bind σ (closedIn target Ξ sort) = closedIn target Ξ' sort := by
  unfold closedIn closedAt
  rw [Rigid.include_rename, Rigid.include_rename, bind_rename, ← bind_var_eq_rename]
  congr 1
  funext _ impossible
  exact nomatch impossible

omit [ClosedTerms S] in
/-- A lifted substitution at a weakened variable is the weakened value. -/
theorem liftSub_weakenVar_holes {W : Type} {target : W → MetaArity S} {Ξ Ξ' : Ctx S}
    (σ : Sub (signature S target) Ξ Ξ') {c : S.Srt} (x : Var Ξ c) :
    ∀ (binders : List S.Srt), liftSub σ binders c (weakenVar (S := S) binders x) =
      rename (S := signature S target) (fun _ position => weakenVar (S := S) binders position) (σ c x)
  | [] => (rename_id _).symm
  | _ :: binders => by
      simp only [weakenVar, liftSub, liftSub_weakenVar_holes σ x binders, weaken, rename_comp]

/-! ## Substituting a closed term for the new binder -/

variable {V : Type} {source : V → MetaArity S}

/-- Replace the new binder by a closed term in every hole's solution. -/
def closeBinder (binder : S.Srt) {W : Type} {target : W → MetaArity S}
    (θ : Assignment (raisedArity binder source) target) : Assignment source target :=
  fun hole => bind (extend (closedIn target (source hole).1 binder)) (θ hole)

mutual
/-- **Substitution into a raised instance.** If the substitution sends the new binder to the closed
term, it turns an instance of a raised term into the instance of the term under `closeBinder`. -/
theorem bind_raise (binder : S.Srt) {W : Type} {target : W → MetaArity S}
    (θ : Assignment (raisedArity binder source) target) :
    ∀ {Θ Θ' Ξ : Ctx S} {sort : S.Srt} (ρ : Ren S Θ Θ') (fresh : Var Θ' binder)
      (σ : Sub (signature S target) Θ' Ξ), σ binder fresh = closedIn target Ξ binder →
      ∀ (term : Term (signature S source) Θ sort),
        bind σ (instantiate θ (raiseTerm binder ρ fresh term)) =
          bind (fun sort position => σ sort (ρ sort position)) (instantiate (closeBinder binder θ) term)
  | _, _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, _, ρ, fresh, σ, closed, .op (.inl operator) arguments =>
      congrArg (Term.op (S := signature S target) (Sum.inl operator))
        (bindArgs_raise binder θ ρ fresh σ closed arguments)
  | _, _, _, _, ρ, fresh, σ, closed, .op (.inr (.mk identity)) arguments => by
      change bind σ (bind (argsToSub (S := signature S target) (bs := binder :: (source identity).1)
          (Args.cons (S := signature S target) (bs := []) (Term.var fresh)
            (instantiateArgs θ (raiseArgs binder ρ fresh arguments)))) (θ identity)) =
        bind (fun sort position => σ sort (ρ sort position))
          (bind (argsToSub (S := signature S target) (bs := (source identity).1)
            (instantiateArgs (closeBinder binder θ) arguments))
            (bind (extend (closedIn target (source identity).1 binder)) (θ identity)))
      rw [bind_comp, bind_comp, bind_comp]
      congr 1
      funext sort position
      cases position with
      | zero =>
          change σ binder fresh = _
          rw [closed]
          simp only [extend, bind_closedIn]
      | succ position =>
          change bind σ (argsToSub (instantiateArgs θ (raiseArgs binder ρ fresh arguments)) sort position) =
            bind (fun sort position => σ sort (ρ sort position))
              (argsToSub (instantiateArgs (closeBinder binder θ) arguments) sort position)
          rw [← argsToSub_bindArgs, ← argsToSub_bindArgs, bindArgs_raise binder θ ρ fresh σ closed arguments]

theorem bindArgs_raise (binder : S.Srt) {W : Type} {target : W → MetaArity S}
    (θ : Assignment (raisedArity binder source) target) :
    ∀ {arities : List (MetaArity S)} {Θ Θ' Ξ : Ctx S} (ρ : Ren S Θ Θ') (fresh : Var Θ' binder)
      (σ : Sub (signature S target) Θ' Ξ), σ binder fresh = closedIn target Ξ binder →
      ∀ (arguments : Args (signature S source) arities Θ),
        bindArgs σ (instantiateArgs θ (raiseArgs binder ρ fresh arguments)) =
          bindArgs (fun sort position => σ sort (ρ sort position)) (instantiateArgs (closeBinder binder θ) arguments)
  | _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, _, ρ, fresh, σ, closed, .cons (bs := binders) head tail => by
      have lifted : liftSub σ binders binder (weakenVar (S := S) binders fresh) =
          closedIn target (binders ++ _) binder := by
        refine (liftSub_weakenVar_holes σ fresh binders).trans ?_
        rw [closed]
        exact rename_closedIn target _ binder
      change Args.cons (bind (liftSub σ binders)
          (instantiate θ (raiseTerm binder (liftRen ρ binders) (weakenVar (S := S) binders fresh) head)))
          (bindArgs σ (instantiateArgs θ (raiseArgs binder ρ fresh tail))) =
        Args.cons (bind (liftSub (fun sort position => σ sort (ρ sort position)) binders)
          (instantiate (closeBinder binder θ) head))
          (bindArgs (fun sort position => σ sort (ρ sort position)) (instantiateArgs (closeBinder binder θ) tail))
      rw [bind_raise binder θ (liftRen ρ binders) (weakenVar (S := S) binders fresh) (liftSub σ binders) lifted head,
        liftSub_liftRen, bindArgs_raise binder θ ρ fresh σ closed tail]
end

/-! ## The converse -/

variable {Γ : Ctx S} {sort : S.Srt}

/-- The substitution of the closed term for the new binder fixes every weakened term. -/
theorem bind_close_weaken {W : Type} (target : W → MetaArity S) (binder : S.Srt) (term : Term S Γ sort) :
    bind (extend (closedIn target Γ binder)) (Rigid.includeTerm target (weaken (t := binder) term)) =
      Rigid.includeTerm target term := by
  rw [weaken, Rigid.include_rename]
  exact inst_weaken (S := signature S target) _ _

/-- **Raising adds no answers.** If the raised equation answers a call that does not mention the new
binder by an answer that does not mention it, the root equation answers the call by that answer. -/
theorem raise_answers_converse (binder : S.Srt) (e : Equation S Γ sort) {call answer : Term S Γ sort}
    (answered : Answers (raiseOne binder e) (weaken (t := binder) call) (weaken (t := binder) answer)) :
    Answers e call answer := by
  obtain ⟨θ', matched, read⟩ := answered
  let raised := (raiseOne binder e).assign θ' (ground S)
  have restored := e.ground_assignment (closeBinder binder raised)
  refine ⟨fun hole => decode (closeBinder binder raised hole), ?_, ?_⟩
  · unfold Matches
    rw [restored]
    have closedUp := congrArg (bind (extend (closedIn (ground S) Γ binder))) matched
    change bind (extend (closedIn (ground S) Γ binder))
        (instantiate raised (raiseTerm binder (fun _ position => .succ position) .zero e.lhs)) = _ at closedUp
    rw [bind_raise binder raised (fun _ position => .succ position) .zero
      (extend (closedIn (ground S) Γ binder)) rfl e.lhs, bind_close_weaken] at closedUp
    rw [← closedUp]
    exact (bind_id _).symm
  · rw [restored]
    have closedUp := congrArg (bind (extend (closedIn (ground S) Γ binder))) read
    change bind (extend (closedIn (ground S) Γ binder))
        (instantiate raised (raiseTerm binder (fun _ position => .succ position) .zero e.rhs)) = _ at closedUp
    rw [bind_raise binder raised (fun _ position => .succ position) .zero
      (extend (closedIn (ground S) Γ binder)) rfl e.rhs, bind_close_weaken] at closedUp
    rw [← closedUp]
    exact (bind_id _).symm

/-- **Raising by one binder answers exactly the weakened root answers.** -/
theorem raise_answers_iff (binder : S.Srt) (e : Equation S Γ sort) (call answer : Term S Γ sort) :
    Answers (raiseOne binder e) (weaken (t := binder) call) (weaken (t := binder) answer) ↔ Answers e call answer :=
  ⟨raise_answers_converse binder e, raise_answers binder e⟩

/-! ## Along contexts -/

namespace Nested

open LambdaContextualRung (sig Srt Context)

/-- **Along a λ context**, the raised equation answers a weakened call exactly by the weakened root
answers. -/
theorem raiseAt_answers_iff {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    ∀ (e : Equation sig Γ .term) (call answer : Term sig Γ .term),
      Answers (raiseAt context e) (rename (weakening context) call) (rename (weakening context) answer) ↔
        Answers e call answer := by
  induction context with
  | hole =>
      intro e call answer
      change Answers e (rename (fun _ position => position) call) (rename (fun _ position => position) answer) ↔ _
      rw [rename_id, rename_id]
  | appLeft inner _ ih => exact ih
  | appRight _ inner ih => exact ih
  | underLam inner ih =>
      intro e call answer
      have step := ih (raiseOne Srt.term e) (weaken (t := Srt.term) call) (weaken (t := Srt.term) answer)
      rw [weaken, weaken, rename_comp, rename_comp] at step
      exact step.trans (raise_answers_iff Srt.term e call answer)

end Nested

namespace Quoted

open QuotedLambda (sig Context)
open LambdaContextualRung (Srt)

/-- **Along an active quoted-λ context**, likewise. -/
theorem raiseAt_answers_iff {Γ Δ : Ctx sig} (context : Context Γ Δ) :
    ∀ (e : Equation sig Γ .term) (call answer : Term sig Γ .term),
      Answers (raiseAt context e) (rename (weakening context) call) (rename (weakening context) answer) ↔
        Answers e call answer := by
  induction context with
  | hole =>
      intro e call answer
      change Answers e (rename (fun _ position => position) call) (rename (fun _ position => position) answer) ↔ _
      rw [rename_id, rename_id]
  | appLeft inner _ ih => exact ih
  | appRight _ inner ih => exact ih
  | underLam inner ih =>
      intro e call answer
      have step := ih (raiseOne Srt.term e) (weaken (t := Srt.term) call) (weaken (t := Srt.term) answer)
      rw [weaken, weaken, rename_comp, rename_comp] at step
      exact step.trans (raise_answers_iff Srt.term e call answer)
  | underActivate inner ih => exact ih

end Quoted

#print axioms rename_closedIn
#print axioms bind_closedIn
#print axioms bind_raise
#print axioms raise_answers_converse
#print axioms raise_answers_iff
#print axioms Nested.raiseAt_answers_iff
#print axioms Quoted.raiseAt_answers_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
