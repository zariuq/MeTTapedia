import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication

/-!
# Exact structural equality of the scoped polyadic presentation

The seven declared equation schemas generate precisely the structural
relation used by the compiler. Their instances use the shared contextual
metavariable substitution, including arbitrary ambient open terms. Scope
extrusion keeps its frame outside the private binder; exchange reindexes
both bound positions and retains the ambient context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualAssignment
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredCommunication

/-- Names have no authored equations; processes have the structural theory. -/
def StaticEq {Γ : Ctx sig} : {sort : Srt} → Term sig Γ sort → Term sig Γ sort → Prop
  | .nm, left, right => left = right
  | .pr, left, right => StructuralEq left right

private theorem unary_lift {Θ Γ : Ctx sig} (ambient : Sub sig Θ Γ) :
    joinSub (dependencies := [Srt.nm])
      (argsToSub (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
      (weakenSub [Srt.nm] ambient) = liftSub ambient [Srt.nm] := by
  funext s x
  cases x <;> rfl

private theorem double_weaken {Θ Γ : Ctx sig} (ambient : Sub sig Θ Γ) :
    weakenSub [Srt.nm] (weakenSub [Srt.nm] ambient) =
      weakenSub [Srt.nm, Srt.nm] ambient := by
  funext s x
  simp only [weakenSub, rename_comp]
  rfl

private theorem binary_lift {Θ Γ : Ctx sig} (ambient : Sub sig Θ Γ) :
    joinSub (S := sig) (Γ := Θ) (Δ := Srt.nm :: Srt.nm :: Γ)
      (dependencies := [Srt.nm, Srt.nm])
      (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
        (.cons (Term.var .zero : Name (.nm :: .nm :: Γ))
        (.cons (.var (.succ .zero)) .nil)))
      (weakenSub (S := sig) [Srt.nm, Srt.nm] ambient) = liftSub ambient [Srt.nm, Srt.nm] := by
  funext s x
  cases x with
  | zero => rfl
  | succ x =>
      cases x with
      | zero => rfl
      | succ x =>
          change rename (fun _ x => weakenVar [Srt.nm, Srt.nm] x) (ambient s x) =
            weaken (weaken (ambient s x))
          simp only [weaken, rename_comp]
          rfl

private theorem binary_swap {Θ Γ : Ctx sig} (ambient : Sub sig Θ Γ) :
    joinSub (S := sig) (Γ := Θ) (Δ := Srt.nm :: Srt.nm :: Γ)
      (dependencies := [Srt.nm, Srt.nm])
      (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
        (.cons (Term.var (.succ .zero) : Name (.nm :: .nm :: Γ))
        (.cons (.var .zero) .nil)))
      (weakenSub (S := sig) [Srt.nm, Srt.nm] ambient) =
      (fun s x => rename swapRen (liftSub ambient [Srt.nm, Srt.nm] s x)) := by
  funext s x
  cases x with
  | zero => rfl
  | succ x =>
      cases x with
      | zero => rfl
      | succ x =>
          change rename (fun _ x => weakenVar [Srt.nm, Srt.nm] x) (ambient s x) =
            rename swapRen (weaken (weaken (ambient s x)))
          simp only [weaken, rename_comp]
          rfl

/-- Every instance of an authored static equation is one structural law,
including instances with an independent ambient substitution. -/
theorem axiom_sound : ∀ (i : Fin equations.length) {Θ Γ : Ctx sig}
    (body : ContextualAssignment sig metas Θ) (ambient : Sub sig Θ Γ)
    (ordinary : Sub sig (equations.get i).ctx Γ),
    StaticEq
      (ContextualAssignment.instantiate body ambient ordinary (equations.get i).lhs)
      (ContextualAssignment.instantiate body ambient ordinary (equations.get i).rhs)
  | ⟨0, _⟩, _, _, body, ambient, ordinary => by
      change StructuralEq (par (ordinary _ .zero) (ordinary _ (.succ .zero)))
        (par (ordinary _ (.succ .zero)) (ordinary _ .zero))
      exact .parComm _ _
  | ⟨1, _⟩, _, _, body, ambient, ordinary => by
      change StructuralEq
        (par (par (ordinary _ .zero) (ordinary _ (.succ .zero)))
          (ordinary _ (.succ (.succ .zero))))
        (par (ordinary _ .zero)
          (par (ordinary _ (.succ .zero)) (ordinary _ (.succ (.succ .zero)))))
      exact .parAssoc _ _ _
  | ⟨2, _⟩, _, _, body, ambient, ordinary => by
      change StructuralEq (par (ordinary _ .zero) nil) (ordinary _ .zero)
      exact .parUnit _
  | ⟨3, _⟩, _, _, body, ambient, ordinary => by
      change StructuralEq (nu (weaken (ordinary _ .zero))) (ordinary _ .zero)
      exact .nuUnused _
  | ⟨4, _⟩, _, Γ, body, ambient, ordinary => by
      dsimp only [equations, List.get, StaticEq, eqNuPar, unaryContinuation,
        ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        ContextualAssignment.apply]
      rw [ContextualAssignment.weakenSub_nil ambient,
        ContextualAssignment.weakenSub_nil (weakenSub [Srt.nm] ambient)]
      change StructuralEq
        (par (nu (Mettapedia.OSLF.Binding.bind
          (joinSub (argsToSub (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
            (weakenSub [Srt.nm] ambient)) (body 0))) (ordinary _ .zero))
        (nu (par (Mettapedia.OSLF.Binding.bind
          (joinSub (argsToSub (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
            (weakenSub [Srt.nm] ambient)) (body 0)) (weaken (ordinary _ .zero))))
      exact .nuPar _ _
  | ⟨5, _⟩, _, Γ, body, ambient, ordinary => by
      dsimp only [equations, List.get, StaticEq, eqNuSwap, binaryContinuation,
        ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
        ContextualAssignment.apply]
      change StructuralEq
        (nu (nu (Mettapedia.OSLF.Binding.bind
          (joinSub (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
            (.cons (Term.var .zero : Name (.nm :: .nm :: Γ))
            (.cons (.var (.succ .zero)) .nil)))
            (weakenSub [Srt.nm] (weakenSub [Srt.nm] ambient))) (body 1))))
        (nu (nu (Mettapedia.OSLF.Binding.bind
          (joinSub (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
            (.cons (Term.var (.succ .zero) : Name (.nm :: .nm :: Γ))
            (.cons (.var .zero) .nil)))
            (weakenSub [Srt.nm] (weakenSub [Srt.nm] ambient))) (body 1))))
      rw [double_weaken, binary_lift, binary_swap, ← rename_bind]
      exact .nuSwap _
  | ⟨6, _⟩, _, _, body, ambient, ordinary => by
      change StructuralEq (rep (ordinary _ .zero))
        (par (ordinary _ .zero) (rep (ordinary _ .zero)))
      exact .repUnfold _
  | ⟨n + 7, impossible⟩, _, _, _, _, _ => by simp [equations] at impossible

private theorem static_refl {Γ : Ctx sig} {sort : Srt} (value : Term sig Γ sort) :
    StaticEq value value := by
  cases sort with
  | nm => rfl
  | pr => exact .refl _

private theorem static_symm {Γ : Ctx sig} {sort : Srt} {left right : Term sig Γ sort}
    (equal : StaticEq left right) : StaticEq right left := by
  cases sort with
  | nm => exact equal.symm
  | pr => exact .symm equal

private theorem static_trans {Γ : Ctx sig} {sort : Srt}
    {left middle right : Term sig Γ sort}
    (first : StaticEq left middle) (second : StaticEq middle right) :
    StaticEq left right := by
  cases sort with
  | nm => exact first.trans second
  | pr => exact .trans first second

/-- Argumentwise structural equality at each argument's actual binder context. -/
inductive StaticArgs : {arity : List (List Srt × Srt)} → {Γ : Ctx sig} →
    Args sig arity Γ → Args sig arity Γ → Prop where
  | nil {Γ} : StaticArgs (Args.nil (S := sig) (Γ := Γ)) .nil
  | cons {Γ bs sort rest} {left right : Term sig (bs ++ Γ) sort}
      {tail tail' : Args sig rest Γ} :
      StaticEq left right → StaticArgs tail tail' →
      StaticArgs (.cons left tail) (.cons right tail')

private theorem static_cong {Γ : Ctx sig} {sort : Srt} (op : Op sort)
    {left right : Args sig (sig.arity op) Γ} (equal : StaticArgs left right) :
    StaticEq (.op op left) (.op op right) := by
  cases op with
  | nil => cases equal; exact .refl _
  | par =>
      cases equal with
      | cons first tail =>
          cases tail with
          | cons second last => cases last; exact .par first second
  | inp1 =>
      cases equal with
      | cons channel tail =>
          cases tail with
          | cons body last =>
              cases last
              change _ = _ at channel
              cases channel
              exact .inp1 _ body
  | inp2 =>
      cases equal with
      | cons channel tail =>
          cases tail with
          | cons body last =>
              cases last
              change _ = _ at channel
              cases channel
              exact .inp2 _ body
  | out1 =>
      cases equal with
      | cons channel tail =>
          cases tail with
          | cons datum last =>
              cases last
              change _ = _ at channel datum
              cases channel
              cases datum
              exact .refl _
  | out2 =>
      cases equal with
      | cons channel tail =>
          cases tail with
          | cons first tail =>
              cases tail with
              | cons second last =>
                  cases last
                  change _ = _ at channel first second
                  cases channel
                  cases first
                  cases second
                  exact .refl _
  | nu => cases equal with
      | cons body last => cases last; exact .nu body
  | rep => cases equal with
      | cons body last => cases last; exact .rep body

mutual
/-- Soundness includes congruence under every constructor, not only active
operational contexts. -/
theorem eqClosure_sound : ∀ {Γ : Ctx sig} {sort : Srt}
    {left right : Term sig Γ sort}, EqClosure equations left right → StaticEq left right
  | _, _, _, _, .ax i body ambient ordinary => axiom_sound i body ambient ordinary
  | _, _, _, _, .refl value => static_refl value
  | _, _, _, _, .symm equal => static_symm (eqClosure_sound equal)
  | _, _, _, _, .trans first second =>
      static_trans (eqClosure_sound first) (eqClosure_sound second)
  | _, _, _, _, .cong op equal => static_cong op (eqArgs_sound equal)

theorem eqArgs_sound : ∀ {Γ : Ctx sig} {arity : List (List Srt × Srt)}
    {left right : Args sig arity Γ}, EqArgs equations left right → StaticArgs left right
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head tail => .cons (eqClosure_sound head) (eqArgs_sound tail)
end

private theorem declared_parComm {Γ : Ctx sig} (first second : Proc Γ) :
    EqClosure equations (par first second) (par second first) := by
  exact EqClosure.ax (E := equations) ⟨0, by decide⟩ (supply (Γ := Γ) nil nil) (fun _ x => .var x)
    (argsToSub (S := sig) (bs := [Srt.pr, Srt.pr]) (.cons first (.cons second .nil)))

private theorem declared_parAssoc {Γ : Ctx sig} (first second third : Proc Γ) :
    EqClosure equations (par (par first second) third) (par first (par second third)) := by
  exact EqClosure.ax (E := equations) ⟨1, by decide⟩ (supply (Γ := Γ) nil nil) (fun _ x => .var x)
    (argsToSub (S := sig) (bs := [Srt.pr, Srt.pr, Srt.pr]) (.cons first (.cons second (.cons third .nil))))

private theorem declared_parUnit {Γ : Ctx sig} (process : Proc Γ) :
    EqClosure equations (par process nil) process := by
  exact EqClosure.ax (E := equations) ⟨2, by decide⟩ (supply (Γ := Γ) nil nil) (fun _ x => .var x) (argsToSub (S := sig) (bs := [Srt.pr]) (.cons process .nil))

private theorem declared_nuUnused {Γ : Ctx sig} (process : Proc Γ) :
    EqClosure equations (nu (weaken process)) process := by
  exact EqClosure.ax (E := equations) ⟨3, by decide⟩ (supply (Γ := Γ) nil nil) (fun _ x => .var x) (argsToSub (S := sig) (bs := [Srt.pr]) (.cons process .nil))

private theorem declared_nuPar {Γ : Ctx sig} (process : Proc (.nm :: Γ)) (frame : Proc Γ) :
    EqClosure equations (par (nu process) frame) (nu (par process (weaken frame))) := by
  have declared := EqClosure.ax (E := equations) ⟨4, by decide⟩ (supply (Γ := Γ) process nil)
    (fun _ x => .var x) (argsToSub (S := sig) (bs := [Srt.pr]) (.cons frame .nil))
  dsimp only [equations, List.get, eqNuPar, unaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, supply] at declared
  rw [ContextualAssignment.weakenSub_nil,
    ContextualAssignment.weakenSub_nil] at declared
  change EqClosure equations
    (par (nu (Mettapedia.OSLF.Binding.bind
      (joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Γ) (dependencies := [Srt.nm])
        (argsToSub (S := sig) (bs := [Srt.nm])
          (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
        (weakenSub (S := sig) [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ))) process)) frame)
    (nu (par (Mettapedia.OSLF.Binding.bind
      (joinSub (S := sig) (Γ := Γ) (Δ := Srt.nm :: Γ) (dependencies := [Srt.nm])
        (argsToSub (S := sig) (bs := [Srt.nm])
          (.cons (Term.var .zero : Name (.nm :: Γ)) .nil))
        (weakenSub (S := sig) [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ))) process) (weaken frame))) at declared
  rw [unary_lift, liftSub_var, bind_id] at declared
  exact declared

private theorem declared_nuSwap {Γ : Ctx sig} (process : Proc (.nm :: .nm :: Γ)) :
    EqClosure equations (nu (nu process)) (nu (nu (rename swapRen process))) := by
  have declared := EqClosure.ax (E := equations) ⟨5, by decide⟩ (supply (Γ := Γ) nil process)
    (fun _ x => .var x : Sub sig Γ Γ) (fun _ x => nomatch x : Sub sig [] Γ)
  dsimp only [equations, List.get, eqNuSwap, binaryContinuation,
    ContextualAssignment.instantiate, ContextualAssignment.instantiateArgs,
    ContextualAssignment.apply, supply] at declared
  change EqClosure equations
    (nu (nu (Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
        (.cons (Term.var .zero : Name (.nm :: .nm :: Γ)) (.cons (.var (.succ .zero)) .nil)))
        (weakenSub (S := sig) [Srt.nm] (weakenSub (S := sig) [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ)))) process)))
    (nu (nu (Mettapedia.OSLF.Binding.bind
      (joinSub (argsToSub (S := sig) (bs := [Srt.nm, Srt.nm])
        (.cons (Term.var (.succ .zero) : Name (.nm :: .nm :: Γ)) (.cons (.var .zero) .nil)))
        (weakenSub (S := sig) [Srt.nm] (weakenSub (S := sig) [Srt.nm] (fun _ x => .var x : Sub sig Γ Γ)))) process))) at declared
  rw [double_weaken, binary_lift, binary_swap, ← rename_bind, liftSub_var, bind_id] at declared
  exact declared

private theorem declared_repUnfold {Γ : Ctx sig} (process : Proc Γ) :
    EqClosure equations (rep process) (par process (rep process)) := by
  exact EqClosure.ax (E := equations) ⟨6, by decide⟩ (supply (Γ := Γ) nil nil) (fun _ x => .var x) (argsToSub (S := sig) (bs := [Srt.pr]) (.cons process .nil))

/-- Completeness uses the actual declared schemas for the noncongruence laws. -/
theorem structuralEq_complete {Γ : Ctx sig} {left right : Proc Γ}
    (equal : StructuralEq left right) : EqClosure equations left right := by
  induction equal with
  | refl process => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ first second => exact .trans first second
  | parComm first second => exact declared_parComm first second
  | parAssoc first second third => exact declared_parAssoc first second third
  | parUnit process => exact declared_parUnit process
  | nuUnused process => exact declared_nuUnused process
  | nuPar process frame => exact declared_nuPar process frame
  | nuSwap process => exact declared_nuSwap process
  | repUnfold process => exact declared_repUnfold process
  | par _ _ first second => exact EqClosure.cong (E := equations) Op.par (.cons first (.cons second .nil))
  | nu _ ih => exact EqClosure.cong (E := equations) Op.nu (.cons ih .nil)
  | inp1 channel _ ih => exact EqClosure.cong (E := equations) Op.inp1 (.cons (.refl channel) (.cons ih .nil))
  | inp2 channel _ ih => exact EqClosure.cong (E := equations) Op.inp2 (.cons (.refl channel) (.cons ih .nil))
  | rep _ ih => exact EqClosure.cong (E := equations) Op.rep (.cons ih .nil)

/-- The compiler's static relation is exactly the presentation's generated
equational theory at every open context. -/
theorem eqClosure_iff_structuralEq {Γ : Ctx sig} (left right : Proc Γ) :
    EqClosure presentation.eqs left right ↔ StructuralEq left right :=
  ⟨eqClosure_sound, structuralEq_complete⟩

/-- No declared scope or process equation identifies distinct name variables. -/
theorem name_eqClosure_iff {Γ : Ctx sig} (left right : Name Γ) :
    EqClosure presentation.eqs left right ↔ left = right :=
  ⟨eqClosure_sound, fun equal => equal ▸ .refl left⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.AuthoredEquations
