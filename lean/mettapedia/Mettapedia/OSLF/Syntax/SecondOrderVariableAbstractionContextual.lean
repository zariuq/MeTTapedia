import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionNaturality
import Mettapedia.OSLF.Syntax.SecondOrderSchemaInterpretation

/-!
# Restoring contextual authored schema instances

A fresh nullary metavariable may be restored by an open ambient term. Captured
schema bodies are transported with their declared dependencies intact. The
comparison uses the existing contextual instantiator and ordinary substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SecondOrderContext

variable {S : Signature} {M K : List (MetaArity S)}

/-- Restore a contextual schema body under its declared dependency variables. -/
def restoreContextualBody {a : S.Srt} {Γ Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Γ Δ)
    (body : ContextualAssignment (withMetas S (headMetas a M)) K Γ) :
    ContextualAssignment (withMetas S M) K Δ :=
  fun i => restoreHead (weakenFresh (T := withMetas S M) (K.get i).1 value)
    (liftSub env (K.get i).1) (body i)

/-- Absorbing a captured environment before restoration composes its actual
restored values; it does not discard captured dependencies. -/
theorem restoreContextualBody_mapSub {a : S.Srt} {Γ Γ' Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Γ' Δ)
    (sigma : Sub (withMetas S (headMetas a M)) Γ Γ')
    (body : ContextualAssignment (withMetas S (headMetas a M)) K Γ) :
    restoreContextualBody value env (ContextualAssignment.mapSub sigma body) =
      restoreContextualBody value (fun s v => restoreHead value env (sigma s v)) body := by
  funext i
  simp only [restoreContextualBody, ContextualAssignment.mapSub, restoreHead_bind]
  congr 1
  funext s v
  exact restoreHead_liftSub value env sigma (K.get i).1 s v

/-- Ordinary substitution after restoring a body transports its fresh value
and its captured environment together. -/
theorem mapSub_restoreContextualBody {a : S.Srt} {Γ Δ Δ' : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Γ Δ)
    (sigma : Sub (withMetas S M) Δ Δ')
    (body : ContextualAssignment (withMetas S (headMetas a M)) K Γ) :
    ContextualAssignment.mapSub sigma (restoreContextualBody value env body) =
      restoreContextualBody (bind sigma value) (fun s v => bind sigma (env s v)) body := by
  funext i
  simp only [ContextualAssignment.mapSub, restoreContextualBody, bind_restoreHead,
    bind_weakenFresh]
  rw [liftSub_comp (S := withMetas S M) env sigma (K.get i).1]

/-- A weakened identity environment is the existing variable renaming. -/
theorem bind_weakenIdentity {T : Signature} {Γ : Ctx T} {s : T.Srt}
    (bs : Ctx T) (term : Term T Γ s) :
    bind (ContextualAssignment.weakenSub (S := T) bs (fun _ v => .var v)) term =
      weakenFresh (T := T) bs term :=
  bind_var_eq_rename (fun _ v => weakenVar bs v) term

/-- Restoring a body underneath additional binders agrees with weakening the
already restored body. The local dependency list is preserved on both sides. -/
theorem restoreContextualBody_weaken {a : S.Srt} {Γ Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Γ Δ)
    (body : ContextualAssignment (withMetas S (headMetas a M)) K Γ) (bs : Ctx S) :
    restoreContextualBody (weakenFresh (T := withMetas S M) bs value) (liftSub env bs)
        (ContextualAssignment.mapSub
          (ContextualAssignment.weakenSub (S := withMetas S (headMetas a M)) bs
            (fun _ v => .var v)) body) =
      ContextualAssignment.mapSub
        (ContextualAssignment.weakenSub (S := withMetas S M) bs (fun _ v => .var v))
        (restoreContextualBody value env body) := by
  rw [restoreContextualBody_mapSub, mapSub_restoreContextualBody, bind_weakenIdentity]
  congr 1
  funext s v
  change liftSub env bs s (weakenVar (S := withMetas S (headMetas a M)) bs v) =
    bind (ContextualAssignment.weakenSub (S := withMetas S M) bs (fun _ w => .var w)) (env s v)
  rw [weakenVar_withMetas, ← weakenVar_withMetas M]
  exact (ContextualAssignment.liftSub_weakenVar env bs s v).trans
    (bind_weakenIdentity (T := withMetas S M) bs (env s v)).symm

/-- Restoration distributes over a joined dependency-and-ambient environment. -/
theorem restoreHead_joinSub {a : S.Srt} {Γ Ξ Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Ξ Δ) :
    ∀ (dependencies : Ctx S)
      (arguments : Sub (withMetas S (headMetas a M)) dependencies Ξ)
      (ambient : Sub (withMetas S (headMetas a M)) Γ Ξ),
      (fun s v => restoreHead value env
        (ContextualAssignment.joinSub arguments ambient s v)) =
        ContextualAssignment.joinSub (fun s v => restoreHead value env (arguments s v))
          (fun s v => restoreHead value env (ambient s v))
  | [], _, _ => rfl
  | _ :: dependencies, arguments, ambient => by
    funext s v
    cases v with
    | zero => rfl
    | succ v => exact congrFun (congrFun
        (restoreHead_joinSub value env dependencies (fun s w => arguments s (.succ w)) ambient) s) v

/-- Filling a dependency prefix leaves a value depending only on the ambient
context unchanged when the ambient environment is the identity. -/
theorem bind_joinSub_weakenFresh {T : Signature} {Γ Δ : Ctx T} {s : T.Srt}
    (dependencies : Ctx T) (arguments : Sub T dependencies Δ) (ambient : Sub T Γ Δ)
    (term : Term T Γ s) :
    bind (ContextualAssignment.joinSub arguments ambient) (weakenFresh dependencies term) =
      bind ambient term := by
  simp only [weakenFresh, bind_rename, ContextualAssignment.joinSub_ambient]

/-- A contextual metavariable application restores by applying its restored
body to the restored arguments. -/
theorem restoreContextualBody_apply {a : S.Srt} {Γ Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Γ Δ)
    (body : ContextualAssignment (withMetas S (headMetas a M)) K Γ)
    (i : Fin K.length) (arguments : Sub (withMetas S (headMetas a M)) (K.get i).1 Γ) :
    restoreHead value env
        (ContextualAssignment.apply body i arguments (fun _ v => .var v)) =
      ContextualAssignment.apply (restoreContextualBody value env body) i
        (fun s v => restoreHead value env (arguments s v)) (fun _ v => .var v) := by
  simp only [ContextualAssignment.apply, restoreContextualBody]
  rw [restoreHead_bind (S := S) (M := M), bind_restoreHead (S := S) (M := M)]
  rw [bind_joinSub_weakenFresh, bind_id,
    ContextualAssignment.joinSub_liftSub]
  simp only [restoreHead_joinSub, restoreHead, bind_id]

/-- Reading the ordered dependency arguments commutes with restoration. -/
theorem argsToSub_restoreHeadArgs {a : S.Srt} {Γ Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Γ Δ) :
    ∀ (dependencies : Ctx S)
      (args : Args (withMetas S (headMetas a M))
        (dependencies.map (fun b => ([], b))) Γ) (s : S.Srt) (v : Var dependencies s),
      argsToSub (restoreHeadArgs value env args) s v =
        restoreHead value env (argsToSub args s v)
  | [], .nil, _, v => nomatch v
  | _ :: _, .cons head _, _, .zero => by
    simp only [restoreHeadArgs, argsToSub, weakenFresh, weakenVar, rename_id, liftSub]
  | _ :: dependencies, .cons _ tail, s, .succ v =>
    argsToSub_restoreHeadArgs value env dependencies tail s v

mutual

/-- Restoration commutes with an authored schema instance after its captured
environment has been absorbed into the supplied contextual bodies. -/
theorem restoreHead_contextual_normal {S : Signature} {M K : List (MetaArity S)} {a : S.Srt} :
    ∀ {Γ Δ Ξ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Γ Δ)
      (body : ContextualAssignment (withMetas S (headMetas a M)) K Γ)
      (ordinary : Sub (withMetas S (headMetas a M)) Ξ Γ) {s : S.Srt}
      (term : Term (withMetas S K) Ξ s),
      restoreHead value env
          (ContextualAssignment.instantiate body (fun _ v => .var v) ordinary
            (liftSchema (⟨headMetas a M⟩ : Object S) term)) =
        ContextualAssignment.instantiate (restoreContextualBody value env body)
          (fun _ v => .var v) (fun s v => restoreHead value env (ordinary s v))
          (liftSchema (⟨M⟩ : Object S) term)
  | _, _, _, _, _, _, _, _, .var _ => rfl
  | _, _, _, value, env, body, ordinary, _, .op (.inl op) args => by
    simp only [liftSchema, ContextualAssignment.instantiate, restoreHead]
    exact congrArg (Term.op (S := withMetas S M) (.inl op))
      (restoreHeadArgs_contextual_normal value env body ordinary args)
  | _, _, _, value, env, body, ordinary, _, .op (.inr (.mk i)) args => by
    simp only [liftSchema, ContextualAssignment.instantiate]
    rw [restoreContextualBody_apply]
    have compared := restoreHeadArgs_contextual_normal value env body ordinary args
    congr 1
    funext s v
    exact (argsToSub_restoreHeadArgs value env (K.get i).1 _ s v).symm.trans
      (congrFun (congrFun (congrArg argsToSub compared) s) v)

/-- The same comparison preserves the full ordered argument spine, including
every operator's local binder extension. -/
theorem restoreHeadArgs_contextual_normal {S : Signature} {M K : List (MetaArity S)} {a : S.Srt} :
    ∀ {Γ Δ Ξ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Γ Δ)
      (body : ContextualAssignment (withMetas S (headMetas a M)) K Γ)
      (ordinary : Sub (withMetas S (headMetas a M)) Ξ Γ)
      {as : List (List S.Srt × S.Srt)} (args : Args (withMetas S K) as Ξ),
      restoreHeadArgs value env
          (ContextualAssignment.instantiateArgs body (fun _ v => .var v) ordinary
            (liftSchemaArgs (⟨headMetas a M⟩ : Object S) args)) =
        ContextualAssignment.instantiateArgs (restoreContextualBody value env body)
          (fun _ v => .var v) (fun s v => restoreHead value env (ordinary s v))
          (liftSchemaArgs (⟨M⟩ : Object S) args)
  | _, _, _, _, _, _, _, _, .nil => rfl
  | _, _, _, value, env, body, ordinary, _, .cons (bs := bs) head tail => by
    simp only [liftSchemaArgs, ContextualAssignment.instantiateArgs, restoreHeadArgs]
    apply congrArg₂ Args.cons
    · rw [ContextualAssignment.instantiate_ambient_normal_form]
      rw [restoreHead_contextual_normal (S := S) (M := M)
        (weakenFresh (T := withMetas S M) bs value) (liftSub env bs)]
      rw [restoreContextualBody_weaken]
      rw [ContextualAssignment.instantiate_mapSub]
      simp only [bind_id]
      congr 1
      funext s v
      exact restoreHead_liftSub value env ordinary bs s v
    · exact restoreHeadArgs_contextual_normal value env body ordinary tail

end

/-- Restoring an arbitrary contextual authored instance retains all captured
ambient values by first absorbing the actual ambient substitution. -/
theorem restoreHead_contextual_instance {a : S.Srt} {Θ Γ Δ Ξ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Γ Δ)
    (body : ContextualAssignment (withMetas S (headMetas a M)) K Θ)
    (ambient : Sub (withMetas S (headMetas a M)) Θ Γ)
    (ordinary : Sub (withMetas S (headMetas a M)) Ξ Γ)
    {s : S.Srt} (term : Term (withMetas S K) Ξ s) :
    restoreHead value env (ContextualAssignment.instantiate body ambient ordinary
        (liftSchema (⟨headMetas a M⟩ : Object S) term)) =
      ContextualAssignment.instantiate
        (restoreContextualBody value env (ContextualAssignment.mapSub ambient body))
        (fun _ v => .var v) (fun s v => restoreHead value env (ordinary s v))
        (liftSchema (⟨M⟩ : Object S) term) := by
  rw [ContextualAssignment.instantiate_ambient_normal_form]
  exact restoreHead_contextual_normal value env _ ordinary term

end Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction
