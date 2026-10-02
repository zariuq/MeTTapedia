import Mettapedia.OSLF.Syntax.ContextualMetavariableAssignment

/-!
# Moving ordinary variables to fresh nullary metavariables

A fresh nullary metavariable represents one ordinary variable. The existing
metavariable instantiation and simultaneous substitution perform abstraction;
restoration interprets the fresh declaration in an ambient context. Both
operations retain every operator's declared binder list.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction

open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)}

/-- Insert one fresh nullary declaration before the existing declarations. -/
abbrev headMetas (a : S.Srt) (M : List (MetaArity S)) : List (MetaArity S) :=
  ([], a) :: M

/-- Existing declarations retain their arities and shift by one position. -/
def shiftAssignment (a : S.Srt) (i : Fin M.length) :
    Term (withMetas S (headMetas a M)) (M.get i).1 (M.get i).2 :=
  metaVar (S := S) (M := headMetas a M) i.succ

/-- Inclusion into the extension with one fresh declaration. -/
def shift (a : S.Srt) {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S M) Γ s) :
    Term (withMetas S (headMetas a M)) Γ s :=
  instInto (shiftAssignment (S := S) (M := M) a) t

/-- The newly adjoined nullary metavariable is available in every context. -/
def fresh (a : S.Srt) (Γ : Ctx S) : Term (withMetas S (headMetas a M)) Γ a :=
  Term.op (S := withMetas S (headMetas a M)) (.inr (MetaOp.mk (S := S) (M := headMetas a M) ⟨0, Nat.succ_pos _⟩)) .nil

theorem shift_old {Γ : Ctx S} (a : S.Srt) (i : Fin M.length)
    (args : Args (withMetas S M) ((M.get i).1.map (fun b => ([], b))) Γ) :
    shift (S := S) (M := M) a (Term.op (S := withMetas S M) (.inr (.mk i)) args) =
      Term.op (S := withMetas S (headMetas a M)) (.inr (MetaOp.mk (S := S) (M := headMetas a M) i.succ)) (instIntoArgs (S := S) (shiftAssignment (S := S) (M := M) a) args) := by
  simp only [shift, instInto, shiftAssignment, metaVar, bind]
  exact congrArg (Term.op (S := withMetas S (headMetas a M)) (.inr (MetaOp.mk (S := S) (M := headMetas a M) i.succ)))
    (bindArgs_argsToSub_idArgs (S := S) (M := headMetas a M) (M.get i).1 _)

/-- Weakening the value of the fresh declaration does not add dependencies. -/
def weakenFresh {T : Signature} {Γ : Ctx T} {a : T.Srt} (bs : Ctx T)
    (t : Term T Γ a) : Term T (bs ++ Γ) a :=
  rename (fun _ v => weakenVar bs v) t

theorem bind_weakenFresh {Γ Δ : Ctx S} {a : S.Srt}
    (sigma : Sub (withMetas S M) Γ Δ) (bs : Ctx S)
    (t : Term (withMetas S M) Γ a) :
    bind (liftSub sigma bs) (weakenFresh (T := withMetas S M) bs t) = weakenFresh (T := withMetas S M) bs (bind sigma t) := by
  simp only [weakenFresh, bind_rename, rename_bind]
  congr 1
  funext s v
  exact liftSub_weakenVar sigma v bs

mutual

/-- Interpret the fresh nullary declaration as an arbitrary ambient term.
The other metavariables remain the original, position-sensitive declarations. -/
def restoreHead {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    {Ξ Δ : Ctx S} → Term (withMetas S M) Δ a →
    Sub (withMetas S M) Ξ Δ → {s : S.Srt} →
    Term (withMetas S (headMetas a M)) Ξ s → Term (withMetas S M) Δ s
  | _, _, _, env, _, .var v => env _ v
  | _, _, value, env, _, .op (.inl op) args =>
      .op (.inl op) (restoreHeadArgs (S := S) (M := M) value env args)
  | _, _, value, _, _, .op (.inr (.mk ⟨0, _⟩)) args => by
      change Args (withMetas S (headMetas a M)) [] _ at args
      cases args
      exact value
  | _, _, value, env, _, .op (.inr (.mk ⟨n + 1, h⟩)) args =>
      .op (.inr (.mk ⟨n, Nat.lt_of_succ_lt_succ h⟩)) (restoreHeadArgs (S := S) (M := M) value env args)

/-- Restoration follows each argument into its declared binder context. -/
def restoreHeadArgs {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    {Ξ Δ : Ctx S} → Term (withMetas S M) Δ a →
    Sub (withMetas S M) Ξ Δ → {as : List (List S.Srt × S.Srt)} →
    Args (withMetas S (headMetas a M)) as Ξ → Args (withMetas S M) as Δ
  | _, _, _, _, _, .nil => .nil
  | _, _, value, env, _, .cons (bs := bs) head tail =>
      .cons (restoreHead (S := S) (M := M) (weakenFresh (T := withMetas S M) bs value) (liftSub env bs) head)
        (restoreHeadArgs (S := S) (M := M) value env tail)

end

mutual

/-- Restoration commutes with arbitrary simultaneous substitution. -/
theorem bind_restoreHead {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Δ Θ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ) (sigma : Sub (withMetas S M) Δ Θ)
      {s : S.Srt} (t : Term (withMetas S (headMetas a M)) Ξ s),
      bind sigma (restoreHead (S := S) (M := M) value env t) =
        restoreHead (S := S) (M := M) (bind sigma value) (fun s v => bind sigma (env s v)) t
  | _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, value, env, sigma, _, .op (.inl op) args => by
      simp only [restoreHead, bind, bindArgs_restoreHeadArgs (S := S) (M := M) value env sigma args]
  | _, _, _, _, _, _, _, .op (.inr (.mk ⟨0, _⟩)) args => by
      change Args (withMetas S (headMetas a M)) [] _ at args
      cases args
      rfl
  | _, _, _, value, env, sigma, _, .op (.inr (.mk ⟨n + 1, h⟩)) args => by
      simp only [restoreHead, bind, bindArgs_restoreHeadArgs (S := S) (M := M) value env sigma args]

theorem bindArgs_restoreHeadArgs {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Δ Θ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ) (sigma : Sub (withMetas S M) Δ Θ)
      {as : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S (headMetas a M)) as Ξ),
      bindArgs sigma (restoreHeadArgs (S := S) (M := M) value env args) =
        restoreHeadArgs (S := S) (M := M) (bind sigma value) (fun s v => bind sigma (env s v)) args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, value, env, sigma, _, .cons (bs := bs) head tail => by
      simp only [restoreHeadArgs, bindArgs,
        bind_restoreHead (S := S) (M := M) (weakenFresh (T := withMetas S M) bs value) (liftSub env bs) (liftSub sigma bs) head,
        bindArgs_restoreHeadArgs (S := S) (M := M) value env sigma tail, bind_weakenFresh]
      rw [liftSub_comp (S := withMetas S M) env sigma bs]

end


mutual

/-- Restoring after inclusion retains every old declaration and applies
only the supplied ordinary-variable environment. -/
theorem restoreHead_shift {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ) {s : S.Srt} (t : Term (withMetas S M) Ξ s),
      restoreHead value env (shift (S := S) (M := M) a t) = bind env t
  | _, _, _, _, _, .var _ => rfl
  | _, _, value, env, _, .op (.inl op) args => by
      simp only [shift, instInto, restoreHead, bind,
        restoreHeadArgs_shift (S := S) (M := M) value env args]
  | _, _, value, env, _, .op (.inr (.mk i)) args => by
      rw [shift_old]
      change Term.op (S := withMetas S M) (.inr (.mk i))
        (restoreHeadArgs value env (instIntoArgs (shiftAssignment (S := S) (M := M) a) args)) =
        Term.op (S := withMetas S M) (.inr (.mk i)) (bindArgs env args)
      rw [restoreHeadArgs_shift]

/-- Inclusion/restoration is compatible with each argument's local binders. -/
theorem restoreHeadArgs_shift {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ) {as : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S M) as Ξ),
      restoreHeadArgs value env (instIntoArgs (shiftAssignment (S := S) (M := M) a) args) = bindArgs env args
  | _, _, _, _, _, .nil => rfl
  | _, _, value, env, _, .cons (bs := bs) head tail => by
      simp only [instIntoArgs, restoreHeadArgs, bindArgs,
        restoreHeadArgs_shift (S := S) (M := M) value env tail]
      have headEq := restoreHead_shift (S := S) (M := M)
        (weakenFresh (T := withMetas S M) bs value) (liftSub env bs) head
      change restoreHead _ _ (instInto (shiftAssignment (S := S) (M := M) a) head) = bind _ head at headEq
      rw [headEq]

end

mutual

/-- Renaming schema variables changes only the ordinary-variable environment. -/
theorem restoreHead_rename {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Ξ' Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ' Δ) (rho : Ren S Ξ Ξ') {s : S.Srt}
      (t : Term (withMetas S (headMetas a M)) Ξ s),
      restoreHead value env (rename rho t) = restoreHead value (fun s v => env s (rho s v)) t
  | _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, value, env, rho, _, .op (.inl op) args => by
      simp only [rename, restoreHead,
        restoreHeadArgs_renameArgs (S := S) (M := M) value env rho args]
  | _, _, _, _, _, _, _, .op (.inr (.mk ⟨0, _⟩)) args => by
      change Args (withMetas S (headMetas a M)) [] _ at args
      cases args
      rfl
  | _, _, _, value, env, rho, _, .op (.inr (.mk ⟨n + 1, h⟩)) args => by
      simp only [rename, restoreHead,
        restoreHeadArgs_renameArgs (S := S) (M := M) value env rho args]

theorem restoreHeadArgs_renameArgs {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Ξ' Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ' Δ) (rho : Ren S Ξ Ξ')
      {as : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S (headMetas a M)) as Ξ),
      restoreHeadArgs value env (renameArgs rho args) =
        restoreHeadArgs value (fun s v => env s (rho s v)) args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, value, env, rho, _, .cons (bs := bs) head tail => by
      simp only [renameArgs, restoreHeadArgs,
        restoreHead_rename (S := S) (M := M) (weakenFresh (T := withMetas S M) bs value)
          (liftSub env bs) (liftRen rho bs) head,
        restoreHeadArgs_renameArgs (S := S) (M := M) value env rho tail]
      rw [liftSub_liftRen (S := withMetas S M) rho env bs]

end

/-- Restoring after weakening is weakening after restoration. -/
theorem restoreHead_weaken {a : S.Srt} {Ξ Δ : Ctx S} {b s : S.Srt}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Ξ Δ)
    (t : Term (withMetas S (headMetas a M)) Ξ s) :
    restoreHead (weaken (S := withMetas S M) (t := b) value) (liftSub env [b]) (weaken (S := withMetas S (headMetas a M)) (t := b) t) =
      weaken (S := withMetas S M) (t := b) (restoreHead value env t) := by
  simp only [weaken, restoreHead_rename]
  have core := bind_restoreHead (S := S) (M := M) value env
    (fun (s : S.Srt) (v : Var Δ s) => Term.var (S := withMetas S M) (Γ := b :: Δ) (.succ v)) t
  simp only [bind_var_eq_rename] at core
  change restoreHead _ (fun s v => rename (fun _ w => Var.succ w) (env s v)) t = _
  exact core.symm

/-- Weakening by a binder list agrees with repeated one-variable weakening. -/
theorem weakenFresh_cons {T : Signature} {Γ : Ctx T} {a b : T.Srt} (bs : Ctx T)
    (value : Term T Γ a) :
    weakenFresh (b :: bs) value = weaken (t := b) (weakenFresh bs value) := by
  simp only [weakenFresh, weaken, rename_comp, weakenVar]

/-- Restoration commutes with the binder lift of an arbitrary source substitution. -/
theorem restoreHead_liftSub {a : S.Srt} {Ξ Ξ' Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Ξ' Δ)
    (sigma : Sub (withMetas S (headMetas a M)) Ξ Ξ') :
    ∀ (bs : Ctx S) (s : S.Srt) (v : Var (bs ++ Ξ) s),
      restoreHead (weakenFresh (T := withMetas S M) bs value) (liftSub env bs)
          (liftSub sigma bs s v) =
        liftSub (fun s v => restoreHead value env (sigma s v)) bs s v
  | [], s, v => by
      change restoreHead (rename (fun _ v => v) value) env (sigma s v) = _
      rw [rename_id]
      rfl
  | b :: bs, s, v => by
      cases v with
      | zero => rfl
      | succ w =>
          simp only [liftSub, weakenFresh_cons]
          have liftCons : liftSub env (b :: bs) =
              liftSub (S := withMetas S M) (liftSub env bs) [b] := by
            funext s v
            cases v <;> rfl
          rw [liftCons]
          rw [restoreHead_weaken]
          exact congrArg (weaken (S := withMetas S M) (t := b)) (restoreHead_liftSub value env sigma bs s w)

mutual

/-- Source-variable substitution is interpreted by substitution of its restored values. -/
theorem restoreHead_bind {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Ξ' Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ' Δ)
      (sigma : Sub (withMetas S (headMetas a M)) Ξ Ξ') {s : S.Srt}
      (t : Term (withMetas S (headMetas a M)) Ξ s),
      restoreHead value env (bind sigma t) =
        restoreHead value (fun s v => restoreHead value env (sigma s v)) t
  | _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, value, env, sigma, _, .op (.inl op) args => by
      simp only [bind, restoreHead,
        restoreHeadArgs_bindArgs (S := S) (M := M) value env sigma args]
  | _, _, _, _, _, _, _, .op (.inr (.mk ⟨0, _⟩)) args => by
      change Args (withMetas S (headMetas a M)) [] _ at args
      cases args
      rfl
  | _, _, _, value, env, sigma, _, .op (.inr (.mk ⟨n + 1, h⟩)) args => by
      simp only [bind, restoreHead,
        restoreHeadArgs_bindArgs (S := S) (M := M) value env sigma args]

theorem restoreHeadArgs_bindArgs {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Ξ' Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ' Δ)
      (sigma : Sub (withMetas S (headMetas a M)) Ξ Ξ')
      {as : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S (headMetas a M)) as Ξ),
      restoreHeadArgs value env (bindArgs sigma args) =
        restoreHeadArgs value (fun s v => restoreHead value env (sigma s v)) args
  | _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, value, env, sigma, _, .cons (bs := bs) head tail => by
      simp only [bindArgs, restoreHeadArgs,
        restoreHead_bind (S := S) (M := M) (weakenFresh (T := withMetas S M) bs value)
          (liftSub env bs) (liftSub sigma bs) head,
        restoreHeadArgs_bindArgs (S := S) (M := M) value env sigma tail]
      have lifted :
          (fun s v => restoreHead (weakenFresh (T := withMetas S M) bs value)
            (liftSub env bs) (liftSub sigma bs s v)) =
          liftSub (fun s v => restoreHead value env (sigma s v)) bs := by
        funext s v
        exact restoreHead_liftSub value env sigma bs s v
      rw [lifted]

end


/-- Adjoining operators does not change the position of a weakened variable. -/
theorem weakenVar_withMetas {S : Signature} (N : List (MetaArity S)) {Γ : Ctx S} {s : S.Srt} :
    ∀ (bs : Ctx S) (v : Var Γ s),
      weakenVar (S := withMetas S N) bs v = weakenVar (S := S) bs v
  | [], _ => rfl
  | _ :: bs, v => congrArg Var.succ (weakenVar_withMetas N bs v)

/-- Inclusion commutes with weakening of an ambient value. -/
theorem shift_weakenFresh {a s : S.Srt} {Γ : Ctx S} (bs : Ctx S)
    (value : Term (withMetas S M) Γ s) :
    shift (S := S) (M := M) a (weakenFresh (T := withMetas S M) bs value) =
      weakenFresh (T := withMetas S (headMetas a M)) bs (shift (S := S) (M := M) a value) := by
  unfold shift weakenFresh
  have left : (fun s v => weakenVar (S := withMetas S M) bs (v : Var Γ s)) =
      fun s v => weakenVar (S := S) bs (v : Var Γ s) := by
    funext s v
    exact weakenVar_withMetas M bs v
  have right : (fun s v => weakenVar (S := withMetas S (headMetas a M)) bs (v : Var Γ s)) =
      fun s v => weakenVar (S := S) bs (v : Var Γ s) := by
    funext s v
    exact weakenVar_withMetas (headMetas a M) bs v
  rw [left, right]
  exact instInto_rename (S := S) (shiftAssignment (S := S) (M := M) a)
    (fun _ v => weakenVar (S := S) bs v) value

/-- A fresh nullary declaration is unchanged by weakening. -/
theorem weakenFresh_fresh (a : S.Srt) (Γ bs : Ctx S) :
    weakenFresh (T := withMetas S (headMetas a M)) bs (fresh a Γ) =
      fresh (M := M) a (bs ++ Γ) := rfl

/-- Inclusion carries lifted ordinary substitutions to the same lifted images. -/
theorem shift_liftSub (a : S.Srt) {Ξ Δ : Ctx S}
    (env : Sub (withMetas S M) Ξ Δ) (bs : Ctx S) :
    (fun s v => shift (S := S) (M := M) a (liftSub env bs s v)) =
      liftSub (fun s v => shift (S := S) (M := M) a (env s v)) bs := by
  funext s v
  exact instInto_liftSub (shiftAssignment (S := S) (M := M) a) env bs s v

/-- The variable-generator comparison lifts under arbitrary binders. -/
theorem rebuildHead_lift {a : S.Srt} {Ξ Δ : Ctx S}
    (env : Sub (withMetas S M) Ξ Δ)
    (sigma : Sub (withMetas S (headMetas a M)) Δ Ξ)
    (h : ∀ s v, bind sigma (shift (S := S) (M := M) a (env s v)) = Term.var (S := withMetas S (headMetas a M)) v) (bs : Ctx S) :
    ∀ s v, bind (liftSub sigma bs) (shift (S := S) (M := M) a (liftSub env bs s v)) = Term.var (S := withMetas S (headMetas a M)) v := by
  have identity : (fun s v => bind sigma (shift (S := S) (M := M) a (env s v))) =
      fun s v => Term.var (S := withMetas S (headMetas a M)) v := by
    funext s v
    exact h s v
  have lifted := liftSub_comp (S := withMetas S (headMetas a M))
    (fun s v => shift (S := S) (M := M) a (env s v)) sigma bs
  rw [identity, liftSub_var] at lifted
  intro s v
  rw [congrFun (congrFun (shift_liftSub a env bs) s) v]
  exact congrFun (congrFun lifted s) v

mutual

/-- A restoration whose two kinds of generators are sent back to themselves
is inverted on all terms, including metavariable applications under binders. -/
theorem rebuildHead {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ)
      (sigma : Sub (withMetas S (headMetas a M)) Δ Ξ)
      (_hfresh : bind sigma (shift (S := S) (M := M) a value) = fresh (M := M) a Ξ)
      (_hvars : ∀ s v, bind sigma (shift (S := S) (M := M) a (env s v)) = Term.var (S := withMetas S (headMetas a M)) v)
      {s : S.Srt} (t : Term (withMetas S (headMetas a M)) Ξ s),
      bind sigma (shift (S := S) (M := M) a (restoreHead value env t)) = t
  | _, _, _, _, _, _, hvars, _, .var v => hvars _ v
  | _, _, value, env, sigma, hfresh, hvars, _, .op (.inl op) args => by
      simp only [restoreHead, shift, instInto, bind,
        rebuildHeadArgs (S := S) (M := M) value env sigma hfresh hvars args]
  | _, _, _, _, _, hfresh, _, _, .op (.inr (.mk ⟨0, _⟩)) args => by
      change Args (withMetas S (headMetas a M)) [] _ at args
      cases args
      exact hfresh
  | _, _, value, env, sigma, hfresh, hvars, _, .op (.inr (.mk ⟨n + 1, h⟩)) args => by
      simp only [restoreHead]
      rw [shift_old]
      change Term.op (S := withMetas S (headMetas a M)) (.inr (.mk ⟨n + 1, h⟩))
        (bindArgs sigma (instIntoArgs (shiftAssignment (S := S) (M := M) a) (restoreHeadArgs value env args))) = _
      exact congrArg (Term.op (S := withMetas S (headMetas a M))
        (.inr (MetaOp.mk (S := S) (M := headMetas a M) ⟨n + 1, h⟩)))
        (rebuildHeadArgs (S := S) (M := M) value env sigma hfresh hvars args)

theorem rebuildHeadArgs {S : Signature} {M : List (MetaArity S)} {a : S.Srt} :
    ∀ {Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ)
      (sigma : Sub (withMetas S (headMetas a M)) Δ Ξ)
      (_hfresh : bind sigma (shift (S := S) (M := M) a value) = fresh (M := M) a Ξ)
      (_hvars : ∀ s v, bind sigma (shift (S := S) (M := M) a (env s v)) = Term.var (S := withMetas S (headMetas a M)) v)
      {as : List (List S.Srt × S.Srt)}
      (args : Args (withMetas S (headMetas a M)) as Ξ),
      bindArgs sigma (instIntoArgs (shiftAssignment (S := S) (M := M) a) (restoreHeadArgs value env args)) = args
  | _, _, _, _, _, _, _, _, .nil => rfl
  | Ξ, Δ, value, env, sigma, hfresh, hvars, _, .cons (bs := bs) head tail => by
      have hfresh' : bind (liftSub sigma bs)
          (shift (S := S) (M := M) a (weakenFresh (T := withMetas S M) bs value)) =
          fresh (M := M) a (bs ++ Ξ) := by
        rw [shift_weakenFresh, bind_weakenFresh, hfresh, weakenFresh_fresh]
      have headEq := rebuildHead (S := S) (M := M)
        (weakenFresh (T := withMetas S M) bs value) (liftSub env bs) (liftSub sigma bs)
        hfresh' (rebuildHead_lift env sigma hvars bs) head
      simp only [shift] at headEq
      exact congrArg₂ Args.cons headEq
        (rebuildHeadArgs (S := S) (M := M) value env sigma hfresh hvars tail)

end

/-- Replace the leading ordinary variable by the fresh nullary declaration. -/
def closeHead (a : S.Srt) (Γ : Ctx S) :
    Sub (withMetas S (headMetas a M)) (a :: Γ) Γ := fun _ v =>
  match v with
  | .zero => fresh (M := M) a Γ
  | .succ old => .var old

/-- Abstract one ordinary variable, retaining every existing metavariable. -/
def abstractHead {a s : S.Srt} {Γ : Ctx S}
    (t : Term (withMetas S M) (a :: Γ) s) :
    Term (withMetas S (headMetas a M)) Γ s :=
  bind (closeHead a Γ) (shift (S := S) (M := M) a t)

/-- Restore one declaration as a leading ordinary variable. -/
def openHead {a s : S.Srt} {Γ : Ctx S}
    (t : Term (withMetas S (headMetas a M)) Γ s) :
    Term (withMetas S M) (a :: Γ) s :=
  restoreHead (.var .zero) (fun _ v => .var (.succ v)) t

/-- Abstraction followed by restoration is the identity on open terms. -/
theorem openHead_abstractHead {a s : S.Srt} {Γ : Ctx S}
    (t : Term (withMetas S M) (a :: Γ) s) : openHead (abstractHead t) = t := by
  unfold openHead abstractHead
  rw [restoreHead_bind, restoreHead_shift]
  have identity : (fun s v => restoreHead (S := S) (M := M)
      (Term.var (S := withMetas S M) (Γ := a :: Γ) .zero)
      (fun _ v => Term.var (.succ v)) (closeHead (M := M) a Γ s v)) =
      fun s v => Term.var (S := withMetas S M) v := by
    funext s v
    cases v <;> rfl
  rw [identity, bind_id]

/-- Restoration followed by abstraction is the identity on extended terms. -/
theorem abstractHead_openHead {a s : S.Srt} {Γ : Ctx S}
    (t : Term (withMetas S (headMetas a M)) Γ s) : abstractHead (openHead t) = t := by
  unfold abstractHead openHead
  exact rebuildHead (S := S) (M := M) (.var .zero) (fun _ v => .var (.succ v))
    (closeHead (M := M) a Γ) rfl (fun _ _ => rfl) t

/-- One ordinary-variable context extension is exactly one fresh nullary declaration. -/
def headEquiv (a s : S.Srt) (Γ : Ctx S) :
    Term (withMetas S M) (a :: Γ) s ≃ Term (withMetas S (headMetas a M)) Γ s where
  toFun := abstractHead
  invFun := openHead
  left_inv := openHead_abstractHead
  right_inv := abstractHead_openHead


/-- The fresh declarations are introduced in reverse ordinary-variable order.
Their positions are retained, even when several variables have the same sort. -/
def extendedMetas : Ctx S → List (MetaArity S) → List (MetaArity S)
  | [], M => M
  | a :: Γ, M => extendedMetas Γ (headMetas a M)

/-- The concrete extension is exactly the reversed list of nullary declarations
followed by the original metavariables. -/
theorem extendedMetas_eq (Γ : Ctx S) (M : List (MetaArity S)) :
    extendedMetas Γ M = Γ.reverse.map (fun a => ([], a)) ++ M := by
  induction Γ generalizing M with
  | nil => rfl
  | cons a Γ ih =>
      rw [extendedMetas, ih]
      simp only [List.reverse_cons, List.map_append, List.map_singleton, List.append_assoc]
      rfl

/-- Move all ordinary variables into fresh nullary metavariables, using the
one-variable equivalence at every stage. -/
def variablesEquiv : (Γ : Ctx S) → (M : List (MetaArity S)) → (s : S.Srt) →
    Term (withMetas S M) Γ s ≃ Term (withMetas S (extendedMetas Γ M)) [] s
  | [], _M, _s => Equiv.refl _
  | a :: Γ, M, s =>
      (headEquiv (S := S) (M := M) a s Γ).trans (variablesEquiv Γ (headMetas a M) s)

/-- Abstraction is the forward map of the established equivalence. -/
def abstractVars {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S M) Γ s) :
    Term (withMetas S (extendedMetas Γ M)) [] s := variablesEquiv Γ M s t

/-- Restoration is the inverse map of the same equivalence. -/
def restoreVars {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S (extendedMetas Γ M)) [] s) : Term (withMetas S M) Γ s :=
  (variablesEquiv Γ M s).symm t

/-- Every open term is recovered exactly, rather than merely up to alpha-equivalence. -/
theorem restoreVars_abstractVars {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S M) Γ s) : restoreVars (abstractVars t) = t :=
  (variablesEquiv Γ M s).symm_apply_apply t

/-- Every term over the fresh declarations comes from an open term. -/
theorem abstractVars_restoreVars {Γ : Ctx S} {s : S.Srt}
    (t : Term (withMetas S (extendedMetas Γ M)) [] s) :
    abstractVars (restoreVars (S := S) (M := M) (Γ := Γ) t) = t :=
  (variablesEquiv Γ M s).apply_symm_apply t

end Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction
