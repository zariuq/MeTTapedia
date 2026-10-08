import Mettapedia.OSLF.Syntax.ContextualLinearSubstitution

/-!
# Opening one or two sorted binders under simultaneous substitution

The comparisons keep each received argument in its declared position.
Every other supplied term passes unchanged through opening the lifted
substitution, including terms depending on arbitrarily many ambient names.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S : Signature}

theorem inst_substitution {Γ Δ : Ctx S} {binder result : S.Srt}
    (body : Term S (binder :: Γ) result) (argument : Term S Γ binder)
    (assigned : Sub S Γ Δ) :
    bind assigned (inst body argument) =
      inst (bind (liftSub assigned [binder]) body) (bind assigned argument) :=
  ContextualLinearSubstitution.bind_inst assigned body argument

/-- Weakening under a single sorted binder commutes with every ambient
substitution, including terms with binding arguments of their own. -/
theorem bind_weaken {Γ Δ : Ctx S} {binder result : S.Srt}
    (term : Term S Γ result) (assigned : Sub S Γ Δ) :
    bind (liftSub assigned [binder]) (weaken term) = weaken (bind assigned term) := by
  simp only [weaken, bind_rename, rename_bind]
  apply congrArg (fun assignment => bind assignment term)
  funext sort position
  rfl

/-- A new first binder can be lifted separately from any existing prefix.
No positions are exchanged. -/
theorem liftSub_cons {Γ Δ : Ctx S} (assigned : Sub S Γ Δ)
    (binder : S.Srt) (binders : Ctx S) :
    liftSub assigned (binder :: binders) = liftSub (liftSub assigned binders) [binder] := by
  funext sort position
  cases position <;> rfl

def extendTwo {Γ : Ctx S} {firstBinder secondBinder : S.Srt}
    (first : Term S Γ firstBinder) (second : Term S Γ secondBinder) :
    Sub S (firstBinder :: secondBinder :: Γ) Γ
  | _, .zero => first
  | sort, .succ old => extend second sort old

def instTwo {Γ : Ctx S} {firstBinder secondBinder result : S.Srt}
    (body : Term S (firstBinder :: secondBinder :: Γ) result)
    (first : Term S Γ firstBinder) (second : Term S Γ secondBinder) : Term S Γ result :=
  bind (extendTwo first second) body

theorem extendTwo_weaken_twice {Γ : Ctx S} {firstBinder secondBinder result : S.Srt}
    (term : Term S Γ result) (first : Term S Γ firstBinder) (second : Term S Γ secondBinder) :
    bind (extendTwo first second) (weaken (weaken term)) = term := by
  simp only [weaken, bind_rename, extendTwo, extend, bind_id]

theorem instTwo_substitution {Γ Δ : Ctx S} {firstBinder secondBinder result : S.Srt}
    (body : Term S (firstBinder :: secondBinder :: Γ) result)
    (first : Term S Γ firstBinder) (second : Term S Γ secondBinder)
    (assigned : Sub S Γ Δ) :
    bind assigned (instTwo body first second) =
      instTwo (bind (liftSub assigned [firstBinder, secondBinder]) body)
        (bind assigned first) (bind assigned second) := by
  simp only [instTwo, bind_comp]
  apply congrArg (fun assignment => bind assignment body)
  funext sort position
  cases position with
  | zero => rfl
  | succ old =>
      cases old with
      | zero => rfl
      | succ old =>
          change assigned sort old = bind (extendTwo (bind assigned first) (bind assigned second))
            (weaken (weaken (assigned sort old)))
          exact (extendTwo_weaken_twice _ _ _).symm

end Mettapedia.OSLF.Binding
