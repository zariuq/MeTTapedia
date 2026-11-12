import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ScopedEffects

/-!
# Faithful native runs at a fixed scope identity

Attaching a fixed scope key preserves and reflects every native run. The
encodings retain all candidate data and the original endpoint; their inverses
do not require an inhabitant of the key type or a choice of fresh keys.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step

universe uO uT uH uOcc uS uF uK

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing) (Key : Type uK)

def liftScopeRun (key : Key) : {state : State} → P.Run state → (P.withScopeKeys Key).Run (key, state)
  | _, .nil _ => .nil _
  | _, .cons firing allowed rest =>
      .cons firing ((P.scope_admits_iff Key key firing).mpr allowed) (liftScopeRun key rest)

def forgetScopeRun : {state : Key × State} → (P.withScopeKeys Key).Run state → P.Run state.2
  | _, .nil state => .nil state.2
  | state, .cons firing allowed rest =>
      .cons firing ((P.scope_admits_iff Key state.1 firing).mp allowed) (forgetScopeRun rest)

theorem forget_liftScopeRun (key : Key) : ∀ {state : State} (run : P.Run state),
    P.forgetScopeRun Key (P.liftScopeRun Key key run) = run
  | _, .nil _ => rfl
  | _, .cons firing allowed rest => by
      change Run.cons firing allowed (P.forgetScopeRun Key (P.liftScopeRun Key key rest)) = _
      rw [forget_liftScopeRun]

theorem lift_forgetScopeRun : ∀ {state : Key × State} (run : (P.withScopeKeys Key).Run state),
    P.liftScopeRun Key state.1 (P.forgetScopeRun Key run) = run
  | _, .nil _ => rfl
  | state, .cons firing allowed rest => by
      exact congrArg
        (fun tail : (P.withScopeKeys Key).Run ((P.withScopeKeys Key).result (s := state) firing allowed) =>
          Run.cons (P := P.withScopeKeys Key) firing allowed tail)
        (lift_forgetScopeRun rest)

def scopeRunEquiv (key : Key) (state : State) : P.Run state ≃ (P.withScopeKeys Key).Run (key, state) where
  toFun := P.liftScopeRun Key key
  invFun := P.forgetScopeRun Key
  left_inv := P.forget_liftScopeRun Key key
  right_inv := P.lift_forgetScopeRun Key

theorem liftScopeRun_last (key : Key) : ∀ {state : State} (run : P.Run state),
    (P.liftScopeRun Key key run).last = (key, run.last)
  | _, .nil _ => rfl
  | _, .cons _ _ rest => liftScopeRun_last key rest

theorem liftScopeRun_word (key : Key) : ∀ {state : State} (run : P.Run state),
    (P.liftScopeRun Key key run).word = run.word.map (fun entry => ⟨(key, entry.1), entry.2⟩)
  | _, .nil _ => rfl
  | _, .cons firing allowed rest => by
      change _ :: (P.liftScopeRun Key key rest).word = _ :: _
      rw [liftScopeRun_word]

theorem forgetScopeRun_word : ∀ {state : Key × State} (run : (P.withScopeKeys Key).Run state),
    (P.forgetScopeRun Key run).word = run.word.map (fun entry => ⟨entry.1.2, entry.2⟩)
  | _, .nil _ => rfl
  | _, .cons firing allowed rest => by
      change _ :: (P.forgetScopeRun Key rest).word = _ :: _
      rw [forgetScopeRun_word]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step
