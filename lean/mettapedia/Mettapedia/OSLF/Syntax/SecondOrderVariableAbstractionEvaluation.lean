import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionNaturality

/-!
# Evaluating fresh-parameter abstraction

The fresh nullary declarations introduced by ordinary-variable abstraction
can be supplied with actual parameter values. Instantiating the resulting
closed body is the same operation as substituting those values into the
original body, with the original metavariable assignment retained.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction

open Mettapedia.OSLF.Binding

variable {S : Signature} {M N : List (MetaArity S)}

/-- The unique substitution out of the empty ordinary context. -/
def emptyEnvironment (T : Signature) (Γ : Ctx T) : Sub T [] Γ :=
  fun s (v : Var [] s) => nomatch v

/-- Supply the fresh head declaration while retaining every old assignment. -/
def dischargeHeadAssignment {a : S.Srt}
    (value : Term (withMetas S N) [] a)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) :
    (i : Fin (headMetas a M).length) →
      Term (withMetas S N) ((headMetas a M).get i).1 ((headMetas a M).get i).2
  | ⟨0, _⟩ => value
  | ⟨n + 1, bound⟩ => body ⟨n, Nat.lt_of_succ_lt_succ bound⟩

/-- A closed value fills the first variable without changing the remaining scope. -/
def dischargeHeadEnvironment {a : S.Srt} (Γ : Ctx S)
    (value : Term (withMetas S N) [] a) :
    Sub (withMetas S N) (a :: Γ) Γ := fun _ v =>
  match v with
  | .zero => bind (emptyEnvironment (withMetas S N) Γ) value
  | .succ old => .var old

/-- Instantiating the included old metavariables uses exactly the old assignment. -/
theorem dischargeHeadAssignment_shift {a : S.Srt}
    (value : Term (withMetas S N) [] a)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S M) Γ s) :
    instInto (dischargeHeadAssignment value body) (shift a term) = instInto body term := by
  unfold shift
  rw [instInto_instInto]
  congr 1
  funext i
  exact instInto_metaVar (dischargeHeadAssignment value body) i.succ

/-- Filling the fresh declaration reads it as the ordinary head substitution. -/
theorem dischargeHeadAssignment_closeHead {a : S.Srt}
    (value : Term (withMetas S N) [] a)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (Γ : Ctx S) :
    (fun s v => instInto (dischargeHeadAssignment value body)
      (closeHead (S := S) (M := M) a Γ s v)) = dischargeHeadEnvironment Γ value := by
  funext s v
  cases v with
  | zero =>
      change bind (argsToSub (Args.nil (S := withMetas S N) (Γ := Γ))) value =
        bind (emptyEnvironment (withMetas S N) Γ) value
      congr 1
  | succ old => rfl

/-- One-variable abstraction evaluates by the corresponding ordinary substitution. -/
theorem dischargeHeadAssignment_abstractHead {a : S.Srt}
    (value : Term (withMetas S N) [] a)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    {Γ : Ctx S} {s : S.Srt} (term : Term (withMetas S M) (a :: Γ) s) :
    instInto (dischargeHeadAssignment value body) (abstractHead term) =
      bind (dischargeHeadEnvironment Γ value) (instInto body term) := by
  unfold abstractHead
  rw [instInto_bind, dischargeHeadAssignment_closeHead, dischargeHeadAssignment_shift]

/-- Give every fresh declaration its ordinary parameter value, in the same
order in which abstraction introduced it. -/
def dischargeAssignment {S : Signature} {M N : List (MetaArity S)} : (Γ : Ctx S) →
    ((i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2) →
    Sub (withMetas S N) Γ [] →
    (i : Fin (extendedMetas Γ M).length) →
      Term (withMetas S N) ((extendedMetas Γ M).get i).1 ((extendedMetas Γ M).get i).2
  | [], body, _ => body
  | a :: Γ, body, env => dischargeAssignment (M := headMetas a M) Γ
      (dischargeHeadAssignment (env _ .zero) body) (fun s v => env s (.succ v))

/-- Closing an already closed value, after weakening it to an arbitrary
scope, returns that value. -/
theorem bind_closed_value {T : Signature} {Γ : Ctx T} {s : T.Srt}
    (env : Sub T Γ []) (value : Term T [] s) :
    bind env (bind (emptyEnvironment T Γ) value) = value := by
  rw [bind_comp]
  have empty : (fun r v => bind env (emptyEnvironment T Γ r v)) =
      (fun r v => Term.var (S := T) (Γ := []) v) := by
    funext r v
    nomatch v
  rw [empty, bind_id]

/-- Applying the abstracted body is precisely ordinary substitution into
the original term, for all original metavariables and local binder lists. -/
theorem dischargeAssignment_abstractVars (Γ : Ctx S)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (env : Sub (withMetas S N) Γ []) {s : S.Srt}
    (term : Term (withMetas S M) Γ s) :
    instInto (dischargeAssignment Γ body env) (abstractVars term) =
      bind env (instInto body term) := by
  induction Γ generalizing M with
  | nil =>
      change instInto body term = bind env (instInto body term)
      have identity : env = fun r v => Term.var (S := withMetas S N) (Γ := []) v := by
        funext r v
        nomatch v
      rw [identity, bind_id]
  | cons a Γ ih =>
      change instInto (dischargeAssignment Γ (dischargeHeadAssignment (env _ .zero) body)
          (fun r v => env r (.succ v))) (abstractVars (abstractHead term)) = _
      rw [ih, dischargeHeadAssignment_abstractHead, bind_comp]
      congr 1
      funext r v
      cases v with
      | zero =>
          exact bind_closed_value (fun s w => env s (.succ w)) (env a .zero)
      | succ old => rfl

end Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction
