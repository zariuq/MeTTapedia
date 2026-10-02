import Mettapedia.OSLF.Syntax.CategoricalBindingGroupoid
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalCongruence

/-!
# Actual argument assignments for generic operator and evaluation arrows

An ordered family of binder-local bodies gives the contextual assignment to
an operator's own arity list. Instantiating its generic operator returns that
family unchanged. Generic evaluation uses the same assignment construction
and performs the existing capture-avoiding ordinary substitution.

These calculations use the established instantiation and prefix laws. They
do not introduce another traversal of terms or another notion of application.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.Binding.CategoricalBindingModel
open _root_.CategoryTheory SecondOrderContext
open IntrinsicScopedLocalCongruence (getArg)
variable {S : Signature}

/-- An actual closed argument family is a contextual assignment to the
operator's own ordered arity list. -/
def closedArgsAssignment {X : Object S} {arity : List (MetaArity S)}
    (args : Args (withMetas S X.arities) arity []) : X ⟶ (⟨arity⟩ : Object S) :=
  fun i => unScope (S := withMetas S X.arities) (arity.get i).1 (getArg args i)

/-- The tail assignment retains exactly the remaining ordered arguments. -/
theorem closedArgsAssignment_tail {X : Object S} {a : MetaArity S}
    {L : List (MetaArity S)} (head : Term (withMetas S X.arities) (a.1 ++ []) a.2)
    (tail : Args (withMetas S X.arities) L []) :
    closedArgsAssignment (.cons head tail) ≫ tailArrow a ⟨L⟩ =
      closedArgsAssignment tail := by
  funext i
  exact instInto_metaVar (closedArgsAssignment (.cons head tail)) i.succ

/-- Extending an already closed binder body by an empty ambient context
changes none of its variables. -/
theorem weakenInto_empty {T : Signature} (bs : Ctx T) {s : T.Srt}
    (body : Term T (bs ++ []) s) : weakenInto (Γ := []) bs body = body := by
  let env : Sub T [] [] := fun _ v => Term.var v
  have given := bind_weakenInto env bs body
  have unchanged : bind (liftSub env bs) (weakenInto (Γ := []) bs body) =
      weakenInto (Γ := []) bs body := by
    change bind (liftSub (fun _ v => Term.var v) bs) _ = _
    rw [liftSub_var, bind_id]
  exact unchanged.symm.trans given

/-- Instantiating a generic head applies its dependency variables and
reconstructs the supplied argument in its declared local scope. -/
theorem closedArgsAssignment_metaHead {X : Object S} {a : MetaArity S}
    {L : List (MetaArity S)} (head : Term (withMetas S X.arities) (a.1 ++ []) a.2)
    (tail : Args (withMetas S X.arities) L []) :
    instInto (closedArgsAssignment (.cons head tail)) (metaHead a L) = head := by
  simp only [metaHead, instInto, instIntoArgs_prefixArgs]
  have parameters : argsToSub
      (prefixArgs (T := withMetas S X.arities) (Γ := []) a.1) =
      (fun r v => Term.var (S := withMetas S X.arities) (injPrefix (S := withMetas S X.arities) (Γ := []) a.1 v)) := by
    funext r v
    exact argsToSub_prefixArgs (T := withMetas S X.arities) (Γ := []) a.1 r v
  rw [parameters]
  change bind (fun r v => Term.var (S := withMetas S X.arities)
    (injPrefix (S := withMetas S X.arities) (Γ := []) a.1 v)) (unScope (S := withMetas S X.arities) a.1 head) = head
  exact (bind_var_eq_rename (S := withMetas S X.arities)
    (fun r v => injPrefix (S := withMetas S X.arities) (Γ := []) a.1 v)
    (unScope (S := withMetas S X.arities) a.1 head)).trans ((rename_injPrefix_unScope (S := withMetas S X.arities) (Γ := []) a.1 head).trans
      (weakenInto_empty (T := withMetas S X.arities) a.1 head))

/-- The generic ordered operator arguments instantiate to the actual
argument family, including every binder-local body. -/
theorem closedArgsAssignment_metaArgs {X : Object S} :
    ∀ {L : List (MetaArity S)} (args : Args (withMetas S X.arities) L []),
      instIntoArgs (closedArgsAssignment args) (metaArgs L) = args
  | _, .nil => rfl
  | a :: L, .cons head tail => by
      simp only [metaArgs, instIntoArgs, closedArgsAssignment_metaHead]
      rw [instIntoArgs_instIntoArgs]
      change Args.cons head (instIntoArgs
        (closedArgsAssignment (.cons head tail) ≫ tailArrow a ⟨L⟩) (metaArgs L)) = _
      rw [closedArgsAssignment_tail]
      exact congrArg (Args.cons head) (closedArgsAssignment_metaArgs tail)

/-- The operator's generic arrow, after the actual argument assignment,
is the original operator applied to those ordered arguments. -/
theorem closedArgsAssignment_opTerm {X : Object S} {s : S.Srt} (o : S.Op s)
    (args : Args (withMetas S X.arities) (S.arity o) []) :
    closedArgsAssignment args ≫ termArrow (opTerm o) =
      termArrow (Term.op (Sum.inl o) args) := by
  apply oneObj_hom_ext
  change instInto (closedArgsAssignment args) (opTerm o) = _
  simp only [opTerm, instInto, closedArgsAssignment_metaArgs]
  rfl

/-- The assignment retains every ordered body: two actual argument
families cannot become equal assignments unless they were already equal. -/
theorem closedArgsAssignment_injective {X : Object S} {L : List (MetaArity S)} :
    Function.Injective (closedArgsAssignment (X := X) (arity := L)) := by
  intro first second same
  have bodies := congrArg (fun assignment => instIntoArgs assignment (metaArgs L)) same
  exact (closedArgsAssignment_metaArgs first).symm.trans
    (bodies.trans (closedArgsAssignment_metaArgs second))

/-- A body and its actual argument family form the assignment to the
generic evaluation context. -/
def closedEvaluationAssignment {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (body : Term (withMetas S X.arities) Γ s)
    (args : Args (withMetas S X.arities) (nullaries Γ) []) : X ⟶ evalObj Γ s
  | ⟨0, _⟩ => body
  | ⟨n + 1, bound⟩ => closedArgsAssignment args ⟨n, Nat.lt_of_succ_lt_succ bound⟩

/-- The tail of the evaluation assignment is exactly the actual argument
assignment, without reordering the dependencies. -/
theorem closedEvaluationAssignment_tail {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (body : Term (withMetas S X.arities) Γ s)
    (args : Args (withMetas S X.arities) (nullaries Γ) []) :
    closedEvaluationAssignment body args ≫ tailArrow (Γ, s) ⟨nullaries Γ⟩ =
      closedArgsAssignment args := by
  funext i
  exact instInto_metaVar (closedEvaluationAssignment body args) i.succ

/-- Generic evaluation performs the existing capture-avoiding ordinary
substitution using the actual arguments. -/
theorem closedEvaluationAssignment_evalTerm {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (body : Term (withMetas S X.arities) Γ s)
    (args : Args (withMetas S X.arities) (nullaries Γ) []) :
    closedEvaluationAssignment body args ≫ termArrow (evalTerm Γ s) =
      termArrow (bind (argsToSub args) body) := by
  apply oneObj_hom_ext
  change instInto (closedEvaluationAssignment body args) (evalTerm Γ s) = _
  simp only [evalTerm, instInto]
  rw [instIntoArgs_instIntoArgs]
  change bind (argsToSub (instIntoArgs
      (closedEvaluationAssignment body args ≫ tailArrow (Γ, s) ⟨nullaries Γ⟩)
      (metaArgs (nullaries Γ)))) body = _
  rw [closedEvaluationAssignment_tail, closedArgsAssignment_metaArgs]
  rfl

/-- Reading an argument after ordinary substitution applies the same
substitution lifted through that argument's declared binder list. -/
theorem getArg_bindArgs {T : Signature} {Γ Δ : Ctx T} (environment : Sub T Γ Δ) :
    ∀ {arity : List (MetaArity T)} (args : Args T arity Γ)
      (i : Fin arity.length),
      getArg (bindArgs environment args) i =
        bind (liftSub environment (arity.get i).1) (getArg args i)
  | _ :: _, .cons _ _, ⟨0, _⟩ => rfl
  | _ :: _, .cons _ tail, ⟨n + 1, bound⟩ =>
      getArg_bindArgs environment tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩

/-- Reading an argument after changing the metavariable assignment is the
same change applied to that ordered argument body. -/
theorem getArg_instIntoArgs {X Y : Object S} (assignment : X ⟶ Y) :
    ∀ {arity : List (MetaArity S)} {Γ : Ctx S}
      (args : Args (withMetas S Y.arities) arity Γ) (i : Fin arity.length),
      getArg (instIntoArgs assignment args) i = instInto assignment (getArg args i)
  | _ :: _, _, .cons _ _, ⟨0, _⟩ => rfl
  | _ :: _, _, .cons _ tail, ⟨n + 1, bound⟩ =>
      getArg_instIntoArgs assignment tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩

end Mettapedia.OSLF.Binding.CategoricalBindingModel
