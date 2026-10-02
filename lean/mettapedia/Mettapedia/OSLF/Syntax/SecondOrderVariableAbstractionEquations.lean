import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionContextual
import Mettapedia.OSLF.Syntax.SecondOrderAuthoredEquationPresentation
import Mettapedia.OSLF.Syntax.SecondOrderEquationRepresentability

/-!
# Variable abstraction for contextual authored equations

Ordinary variables and fresh nullary metavariables are interchangeable in the
actual authored equation quotients. Restoration retains arbitrary captured
schema bodies, independent ambient substitutions, and all local binders. Both
round trips and naturality follow from the existing raw abstraction operations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SecondOrderContext

variable {S : Signature} {M : List (MetaArity S)}

mutual

/-- Lifting a base term and adjoining schema metavariables commute. -/
theorem liftSchema_embed (X : Object S) {K : List (MetaArity S)} :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term S Γ s),
      liftSchema X (embed (M := K) t) =
        embed (S := withMetas S X.arities) (M := K) (embed (S := S) (M := X.arities) t)
  | _, _, .var _ => rfl
  | _, _, .op op args => by
      simp only [embed, liftSchema]
      exact congrArg (Term.op (S := withMetas (withMetas S X.arities) K) (.inl (.inl op)))
        (liftSchemaArgs_embed X args)

theorem liftSchemaArgs_embed (X : Object S) {K : List (MetaArity S)} :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S} (args : Args S as Γ),
      liftSchemaArgs X (embedArgs (M := K) args) =
        embedArgs (S := withMetas S X.arities) (M := K) (embedArgs (S := S) (M := X.arities) args)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      exact congrArg₂ Args.cons (liftSchema_embed X head) (liftSchemaArgs_embed X tail)

end

mutual

/-- An empty schema layer is erased without changing any original binding operator. -/
theorem emptySchema_instance (X : Object S)
    (body : (i : Fin ([] : List (MetaArity S)).length) →
      Term (withMetas S X.arities) (([] : List (MetaArity S)).get i).1
        (([] : List (MetaArity S)).get i).2) :
    ∀ {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S []) Γ s),
      instantiate body (liftSchema X t) =
        embed (M := X.arities)
          (instantiate (S := S) (M := []) (fun i => Fin.elim0 i) t)
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl op) args => by
      simp only [liftSchema, instantiate, embed]
      exact congrArg (Term.op (S := withMetas S X.arities) (.inl op))
        (emptySchemaArgs_instance X body args)
  | _, _, .op (Sum.inr (.mk i)) _ => Fin.elim0 i

theorem emptySchemaArgs_instance (X : Object S)
    (body : (i : Fin ([] : List (MetaArity S)).length) →
      Term (withMetas S X.arities) (([] : List (MetaArity S)).get i).1
        (([] : List (MetaArity S)).get i).2) :
    ∀ {as : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S []) as Γ),
      instantiateArgs body (liftSchemaArgs X args) =
        embedArgs (M := X.arities)
          (instantiateArgs (S := S) (M := []) (fun i => Fin.elim0 i) args)
  | _, _, .nil => rfl
  | _, _, .cons head tail =>
      congrArg₂ Args.cons (emptySchema_instance X body head) (emptySchemaArgs_instance X body tail)

end

/-- Restoration acts on base-signature terms by ordinary substitution. -/
theorem restoreHead_embed {a : S.Srt} {Ξ Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Ξ Δ)
    {s : S.Srt} (t : Term S Ξ s) :
    restoreHead value env (embed (M := headMetas a M) t) =
      bind env (embed (M := M) t) := by
  have included : shift (S := S) (M := M) a (embed (M := M) t) =
      embed (M := headMetas a M) t :=
    instInto_embed (shiftAssignment (S := S) (M := M) a) t
  rw [← included]
  exact restoreHead_shift value env (embed (M := M) t)

/-- An actual lifted instance of an equation with no schema metavariables
restores to its actual instance with the restored ordinary-variable environment. -/
theorem restoreHead_emptySchema_instance {a : S.Srt} {Ξ Δ : Ctx S}
    (value : Term (withMetas S M) Δ a) (env : Sub (withMetas S M) Ξ Δ)
    (body : (i : Fin ([] : List (MetaArity S)).length) →
      Term (withMetas S (headMetas a M)) (([] : List (MetaArity S)).get i).1
        (([] : List (MetaArity S)).get i).2)
    {s : S.Srt} (t : Term (withMetas S []) Ξ s) :
    restoreHead value env (instantiate body (liftSchema (⟨headMetas a M⟩ : Object S) t)) =
      bind env (instantiate (S := withMetas S M) (M := []) (fun i => Fin.elim0 i) (liftSchema (⟨M⟩ : Object S) t)) := by
  rw [emptySchema_instance (S := S) (⟨headMetas a M⟩ : Object S) body t, restoreHead_embed]
  exact congrArg (bind env) (emptySchema_instance (S := S) (⟨M⟩ : Object S)
    (fun i => Fin.elim0 i) t).symm

/-- Adjoin a second-order context to the original authored equation list. -/
abbrev liftedEquations {K : List (MetaArity S)} (equations : List (EqAxiom S K))
    (M : List (MetaArity S)) := equations.map (liftEquation (⟨M⟩ : Object S))

abbrev emptySchemaEquations (equations : List (EqAxiom S [])) (M : List (MetaArity S)) :=
  liftedEquations equations M

/-- Restoration sends every contextual authored generator to an actual
contextual generator with the same original equation index. -/
theorem restoreHead_generator {K : List (MetaArity S)} (equations : List (EqAxiom S K))
    {a : S.Srt} {Θ Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
    (env : Sub (withMetas S M) Ξ Δ)
    (index : Fin (liftedEquations equations (headMetas a M)).length)
    (body : ContextualAssignment (withMetas S (headMetas a M)) K Θ)
    (ambient : Sub (withMetas S (headMetas a M)) Θ Ξ)
    (ordinary : Sub (withMetas S (headMetas a M))
      ((liftedEquations equations (headMetas a M)).get index).ctx Ξ) :
    EqClosure (liftedEquations equations M)
      (restoreHead value env (ContextualAssignment.instantiate body ambient ordinary
        ((liftedEquations equations (headMetas a M)).get index).lhs))
      (restoreHead value env (ContextualAssignment.instantiate body ambient ordinary
        ((liftedEquations equations (headMetas a M)).get index).rhs)) := by
  let original : Fin equations.length := ⟨index.val, by simpa using index.isLt⟩
  let target : Fin (liftedEquations equations M).length := ⟨original.val, by simp⟩
  have getSource : (liftedEquations equations (headMetas a M)).get index =
      liftEquation (⟨headMetas a M⟩ : Object S) (equations.get original) := by
    simp [liftedEquations, original, List.get_eq_getElem]
  have getTarget : (liftedEquations equations M).get target =
      liftEquation (⟨M⟩ : Object S) (equations.get original) := by
    simp [liftedEquations, target, original, List.get_eq_getElem]
  revert ordinary
  rw [getSource]
  intro ordinary
  dsimp only [liftEquation] at ordinary ⊢
  rw [restoreHead_contextual_instance value env body ambient ordinary (equations.get original).lhs,
    restoreHead_contextual_instance value env body ambient ordinary (equations.get original).rhs]
  have generated : ∀ ordinary' : Sub (withMetas S M)
      ((liftedEquations equations M).get target).ctx Δ,
      EqClosure (liftedEquations equations M)
        (ContextualAssignment.instantiate
          (restoreContextualBody value env (ContextualAssignment.mapSub ambient body))
          (fun _ v => .var v) ordinary' ((liftedEquations equations M).get target).lhs)
        (ContextualAssignment.instantiate
          (restoreContextualBody value env (ContextualAssignment.mapSub ambient body))
          (fun _ v => .var v) ordinary' ((liftedEquations equations M).get target).rhs) :=
    fun ordinary' => EqClosure.ax target
      (restoreContextualBody value env (ContextualAssignment.mapSub ambient body))
      (fun _ v => .var v) ordinary'
  rw [getTarget] at generated
  exact generated (fun s v => restoreHead value env (ordinary s v))

mutual

/-- Restoration preserves every generated contextual authored equation,
including schema bodies capturing ambient variables and arbitrary local binders. -/
theorem restoreHead_eqClosure {S : Signature} {M K : List (MetaArity S)}
    (equations : List (EqAxiom S K)) {a : S.Srt} :
    ∀ {Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ) {s : S.Srt}
      {left right : Term (withMetas S (headMetas a M)) Ξ s},
      EqClosure (liftedEquations equations (headMetas a M)) left right →
        EqClosure (liftedEquations equations M)
          (restoreHead value env left) (restoreHead value env right)
  | _, _, value, env, _, _, _, .ax i body ambient ordinary =>
      restoreHead_generator equations value env i body ambient ordinary
  | _, _, _, _, _, _, _, .refl _ => .refl _
  | _, _, value, env, _, _, _, .symm h =>
      .symm (restoreHead_eqClosure equations value env h)
  | _, _, value, env, _, _, _, .trans h h' =>
      .trans (restoreHead_eqClosure equations value env h)
        (restoreHead_eqClosure equations value env h')
  | _, _, value, env, _, _, _, .cong (Sum.inl op) h =>
      EqClosure.cong (S := withMetas S M) (E := liftedEquations equations M)
        (.inl op) (restoreHead_eqArgs equations value env h)
  | _, _, _, _, _, _, _, .cong (Sum.inr (.mk ⟨0, _⟩)) h => by
      cases h
      exact .refl _
  | _, _, value, env, _, _, _, .cong (Sum.inr (.mk ⟨n + 1, h⟩)) related =>
      EqClosure.cong (S := withMetas S M) (E := liftedEquations equations M)
        (.inr (MetaOp.mk (S := S) (M := M) ⟨n, Nat.lt_of_succ_lt_succ h⟩))
        (restoreHead_eqArgs equations value env related)

/-- Restoration preserves the equation congruence on ordered argument spines. -/
theorem restoreHead_eqArgs {S : Signature} {M K : List (MetaArity S)}
    (equations : List (EqAxiom S K)) {a : S.Srt} :
    ∀ {Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
      (env : Sub (withMetas S M) Ξ Δ) {as : List (List S.Srt × S.Srt)}
      {left right : Args (withMetas S (headMetas a M)) as Ξ},
      EqArgs (liftedEquations equations (headMetas a M)) left right →
        EqArgs (liftedEquations equations M)
          (restoreHeadArgs value env left) (restoreHeadArgs value env right)
  | _, _, _, _, _, _, _, .nil => .nil
  | _, _, value, env, _, _, _, .cons (bs := bs) head tail =>
      .cons (restoreHead_eqClosure equations (weakenFresh (T := withMetas S M) bs value)
        (liftSub env bs) head) (restoreHead_eqArgs equations value env tail)

end

/-- The empty-schema case is a specialization of contextual restoration. -/
theorem restoreHead_eqClosure_emptySchema (equations : List (EqAxiom S []))
    {a : S.Srt} {Ξ Δ : Ctx S} (value : Term (withMetas S M) Δ a)
    (env : Sub (withMetas S M) Ξ Δ) {s : S.Srt}
    {left right : Term (withMetas S (headMetas a M)) Ξ s}
    (h : EqClosure (emptySchemaEquations equations (headMetas a M)) left right) :
    EqClosure (emptySchemaEquations equations M)
      (restoreHead value env left) (restoreHead value env right) :=
  restoreHead_eqClosure equations value env h

/-- Abstraction preserves authored equations even with schema metavariables.
It is ordinary substitution after a lawful old-metavariable inclusion. -/
theorem abstractHead_eqClosure {K : List (MetaArity S)}
    (equations : List (EqAxiom S K)) {a s : S.Srt} {Γ : Ctx S}
    {left right : Term (withMetas S M) (a :: Γ) s}
    (h : EqClosure (equations.map (liftEquation (⟨M⟩ : Object S))) left right) :
    EqClosure (equations.map (liftEquation (⟨headMetas a M⟩ : Object S)))
      (abstractHead (S := S) (M := M) left) (abstractHead (S := S) (M := M) right) := by
  let P := authoredEquationPresentation S equations
  have shifted := instInto_eqClosure_generators
    (D := P.axioms (⟨headMetas a M⟩ : Object S))
    (shiftAssignment (S := S) (M := M) a)
    (P.generator_substitute (X := ⟨headMetas a M⟩) (Y := ⟨M⟩)
      (shiftAssignment (S := S) (M := M) a)) h
  exact eqClosure_bind (closeHead (S := S) (M := M) a Γ) shifted

/-- Restoration preserves the authored contextual equation presentation. -/
theorem openHead_eqClosure {K : List (MetaArity S)} (equations : List (EqAxiom S K))
    {a s : S.Srt} {Γ : Ctx S}
    {left right : Term (withMetas S (headMetas a M)) Γ s}
    (h : EqClosure (liftedEquations equations (headMetas a M)) left right) :
    EqClosure (liftedEquations equations M)
      (openHead (S := S) (M := M) left) (openHead (S := S) (M := M) right) :=
  restoreHead_eqClosure equations (.var .zero) (fun _ v => .var (.succ v)) h

/-- Full abstraction preserves every generated authored equation. -/
theorem abstractVars_eqClosure {K : List (MetaArity S)}
    (equations : List (EqAxiom S K)) (Γ : Ctx S) {s : S.Srt}
    {left right : Term (withMetas S M) Γ s}
    (h : EqClosure (equations.map (liftEquation (⟨M⟩ : Object S))) left right) :
    EqClosure (equations.map (liftEquation (⟨extendedMetas Γ M⟩ : Object S)))
      (abstractVars (S := S) (M := M) left) (abstractVars (S := S) (M := M) right) := by
  induction Γ generalizing M with
  | nil => exact h
  | cons a Γ ih =>
      change EqClosure (equations.map (liftEquation (⟨extendedMetas Γ (headMetas a M)⟩ : Object S)))
        (abstractVars (S := S) (M := headMetas a M) (abstractHead (S := S) (M := M) left))
        (abstractVars (S := S) (M := headMetas a M) (abstractHead (S := S) (M := M) right))
      exact ih (abstractHead_eqClosure equations h)

/-- Full restoration preserves contextual authored equations with arbitrary
schema metavariables, dependency contexts, and captured ambient bodies. -/
theorem restoreVars_eqClosure {K : List (MetaArity S)} (equations : List (EqAxiom S K))
    (Γ : Ctx S) {s : S.Srt}
    {left right : Term (withMetas S (extendedMetas Γ M)) [] s}
    (h : EqClosure (liftedEquations equations (extendedMetas Γ M)) left right) :
    EqClosure (liftedEquations equations M)
      (restoreVars (S := S) (M := M) (Γ := Γ) left)
      (restoreVars (S := S) (M := M) (Γ := Γ) right) := by
  induction Γ generalizing M with
  | nil => exact h
  | cons a Γ ih =>
      change EqClosure (liftedEquations equations M)
        (openHead (S := S) (M := M)
          (restoreVars (S := S) (M := headMetas a M) (Γ := Γ) left))
        (openHead (S := S) (M := M)
          (restoreVars (S := S) (M := headMetas a M) (Γ := Γ) right))
      exact openHead_eqClosure equations (ih h)

/-- Abstraction both preserves and reflects exactly the generated authored
contextual equation congruence. -/
theorem abstractVars_eqClosure_iff {K : List (MetaArity S)} (equations : List (EqAxiom S K))
    (Γ : Ctx S) {s : S.Srt} (left right : Term (withMetas S M) Γ s) :
    EqClosure (liftedEquations equations (extendedMetas Γ M))
        (abstractVars (S := S) (M := M) left) (abstractVars (S := S) (M := M) right) ↔
      EqClosure (liftedEquations equations M) left right := by
  constructor
  · intro h
    have restored := restoreVars_eqClosure equations Γ h
    simpa only [restoreVars_abstractVars] using restored
  · exact abstractVars_eqClosure equations Γ

/-- The raw variable abstraction descends to an actual equivalence of the
existing contextual authored equation quotients for arbitrary presentations. -/
def variablesQuotientEquiv {K : List (MetaArity S)} (equations : List (EqAxiom S K))
    (Γ : Ctx S) (M : List (MetaArity S)) (s : S.Srt) :
    TermQ (liftedEquations equations M) Γ s ≃
      TermQ (liftedEquations equations (extendedMetas Γ M)) [] s where
  toFun := Quotient.map (abstractVars (S := S) (M := M))
    (fun _ _ h => abstractVars_eqClosure equations Γ h)
  invFun := Quotient.map (restoreVars (S := S) (M := M) (Γ := Γ))
    (fun _ _ h => restoreVars_eqClosure equations Γ h)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h t => exact congrArg (Quotient.mk _) (restoreVars_abstractVars t)
  right_inv q := by
    induction q using Quotient.inductionOn with
    | h t => exact congrArg (Quotient.mk _) (abstractVars_restoreVars (S := S) (M := M) (Γ := Γ) t)

/-- This quotient equivalence is natural under every old-metavariable assignment,
including noninjective assignments and metavariables with local dependencies. -/
theorem variablesQuotientEquiv_natural {N : List (MetaArity S)}
    {K : List (MetaArity S)} (equations : List (EqAxiom S K)) (Γ : Ctx S) (s : S.Srt)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (q : TermQ (liftedEquations equations M) Γ s) :
    variablesQuotientEquiv equations Γ N s
        (substituteTermClass (authoredEquationPresentation S equations)
          (X := ⟨N⟩) (Y := ⟨M⟩) body q) =
      substituteTermClass (authoredEquationPresentation S equations)
        (X := ⟨extendedMetas Γ N⟩) (Y := ⟨extendedMetas Γ M⟩) (liftAssignment Γ body)
        (variablesQuotientEquiv equations Γ M s q) := by
  induction q using Quotient.inductionOn with
  | h t =>
      exact congrArg (Quotient.mk _) (abstractVars_instInto body Γ t)

/-- The forward quotient map computes on actual authored term classes. -/
theorem variablesQuotientEquiv_mk {K : List (MetaArity S)}
    (equations : List (EqAxiom S K)) (Γ : Ctx S) {s : S.Srt}
    (term : Term (withMetas S M) Γ s) :
    variablesQuotientEquiv equations Γ M s (Quotient.mk _ term) =
      Quotient.mk _ (abstractVars term) := rfl

/-- The inverse quotient map computes by the actual scoped restoration fold. -/
theorem variablesQuotientEquiv_symm_mk {K : List (MetaArity S)}
    (equations : List (EqAxiom S K)) (Γ : Ctx S) {s : S.Srt}
    (term : Term (withMetas S (extendedMetas Γ M)) [] s) :
    (variablesQuotientEquiv equations Γ M s).symm (Quotient.mk _ term) =
      Quotient.mk _ (restoreVars (Γ := Γ) term) := rfl

/-- Restoration of authored equation classes is natural under every assignment
of the old metavariables, with all fresh variables retained. -/
theorem variablesQuotientEquiv_symm_natural {N K : List (MetaArity S)}
    (equations : List (EqAxiom S K)) (Γ : Ctx S) (s : S.Srt)
    (body : (i : Fin M.length) → Term (withMetas S N) (M.get i).1 (M.get i).2)
    (q : TermQ (liftedEquations equations (extendedMetas Γ M)) [] s) :
    (variablesQuotientEquiv equations Γ N s).symm
        (substituteTermClass (authoredEquationPresentation S equations)
          (X := ⟨extendedMetas Γ N⟩) (Y := ⟨extendedMetas Γ M⟩)
          (liftAssignment Γ body) q) =
      substituteTermClass (authoredEquationPresentation S equations)
        (X := ⟨N⟩) (Y := ⟨M⟩) body
        ((variablesQuotientEquiv equations Γ M s).symm q) := by
  induction q using Quotient.inductionOn with
  | h term => exact congrArg (Quotient.mk _) (restoreVars_instInto body Γ term)

/-- The earlier empty-schema quotient interface is the corresponding case
of the general authored contextual equivalence. -/
def variablesQuotientEquiv_emptySchema (equations : List (EqAxiom S []))
    (Γ : Ctx S) (M : List (MetaArity S)) (s : S.Srt) :
    TermQ (emptySchemaEquations equations M) Γ s ≃
      TermQ (emptySchemaEquations equations (extendedMetas Γ M)) [] s :=
  variablesQuotientEquiv equations Γ M s

end Mettapedia.OSLF.Binding.SecondOrderVariableAbstraction
