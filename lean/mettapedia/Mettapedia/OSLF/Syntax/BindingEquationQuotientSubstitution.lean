import Mettapedia.OSLF.Syntax.BindingEquationInterpretation

/-!
# Semantic substitution on equation classes

The existing quotient action `bindQ` substitutes raw terms. A binding-clone
model needs to substitute arbitrary equation classes. A representative is
chosen for each value in a semantic environment; the existing pointwise
equation closure proves that the resulting action satisfies the clone laws.
No choice of representative is observable in the quotient.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationQuotientSubstitution

open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra

variable {S : Signature} {M : List (MetaArity S)}

/-- A representative of each class supplied by a semantic environment. -/
noncomputable def representativeEnv (E : List (EqAxiom S M))
    {Γ Δ : Ctx S}
    (env : Environment S (TermQ E) Γ Δ) : Sub S Γ Δ :=
  fun s v => Quotient.out (env s v)

theorem mk_representativeEnv (E : List (EqAxiom S M))
    {Γ Δ : Ctx S} (env : Environment S (TermQ E) Γ Δ)
    (s : S.Srt) (v : Var Γ s) :
    (Quotient.mk _ (representativeEnv E env s v) : TermQ E Δ s) =
      env s v :=
  Quotient.out_eq _

/-- Simultaneous substitution by arbitrary equation classes. -/
noncomputable def substitute (E : List (EqAxiom S M))
    {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (TermQ E) Γ Δ)
    (q : TermQ E Γ sort) : TermQ E Δ sort :=
  bindQ (representativeEnv E env) q

theorem substitute_mk (E : List (EqAxiom S M))
    {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (TermQ E) Γ Δ)
    (term : Term S Γ sort) :
    substitute E env (Quotient.mk _ term) =
      Quotient.mk _ (bind (representativeEnv E env) term) := rfl

theorem substitute_var (E : List (EqAxiom S M))
    {Γ Δ : Ctx S}
    (env : Environment S (TermQ E) Γ Δ)
    {sort : S.Srt} (v : Var Γ sort) :
    substitute E env (Quotient.mk _ (Term.var v)) = env sort v :=
  mk_representativeEnv E env sort v

/-- Replacing a syntactic substitution by pointwise equivalent terms does
not change the resulting equation class. -/
theorem bind_classes_eq (E : List (EqAxiom S M))
    {Γ Δ : Ctx S} {sort : S.Srt}
    (first second : Sub S Γ Δ)
    (agree : ∀ s v,
      (Quotient.mk _ (first s v) : TermQ E Δ s) =
        Quotient.mk _ (second s v))
    (term : Term S Γ sort) :
    (Quotient.mk _ (bind first term) : TermQ E Δ sort) =
      Quotient.mk _ (bind second term) := by
  apply Quotient.sound
  exact eqClosure_bind_pointwise first second
    (fun s v => Quotient.exact (agree s v)) term

/-- Substituting the quotient variables leaves each equation class fixed. -/
theorem substitute_identity (E : List (EqAxiom S M))
    {Γ : Ctx S} {sort : S.Srt} (q : TermQ E Γ sort) :
    substitute E (fun _ v =>
      (Quotient.mk _ (Term.var v) : TermQ E Γ _)) q = q := by
  induction q using Quotient.inductionOn with
  | _ term =>
      change (Quotient.mk _
          (bind (representativeEnv E
            (fun _ v => (Quotient.mk _ (Term.var v) : TermQ E Γ _))) term) :
          TermQ E Γ sort) = Quotient.mk _ term
      have h := bind_classes_eq E
        (representativeEnv E
          (fun _ v => (Quotient.mk _ (Term.var v) : TermQ E Γ _)))
        (fun _ v => Term.var v)
        (by
          intro s v
          exact mk_representativeEnv E
            (fun _ v => (Quotient.mk _ (Term.var v) : TermQ E Γ _)) s v)
        term
      simpa only [bind_id] using h

/-- The chosen representatives of two semantically composed environments
are pointwise equivalent to syntactically composing their representatives. -/
theorem representativeEnv_comp (E : List (EqAxiom S M))
    {Γ Δ Θ : Ctx S}
    (first : Environment S (TermQ E) Γ Δ)
    (later : Environment S (TermQ E) Δ Θ)
    (s : S.Srt) (v : Var Γ s) :
    (Quotient.mk _
      (bind (representativeEnv E later) (representativeEnv E first s v)) :
      TermQ E Θ s) =
    Quotient.mk _
      (representativeEnv E
        (fun s v => substitute E later (first s v)) s v) := by
  rw [mk_representativeEnv]
  change bindQ (representativeEnv E later)
    (Quotient.mk _ (representativeEnv E first s v)) =
      substitute E later (first s v)
  rw [mk_representativeEnv]
  rfl

/-- Quotient-valued simultaneous substitution is associative. -/
theorem substitute_comp (E : List (EqAxiom S M))
    {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (first : Environment S (TermQ E) Γ Δ)
    (later : Environment S (TermQ E) Δ Θ)
    (q : TermQ E Γ sort) :
    substitute E later (substitute E first q) =
      substitute E
        (fun s v => substitute E later (first s v)) q := by
  induction q using Quotient.inductionOn with
  | _ term =>
      change (Quotient.mk _
        (bind (representativeEnv E later)
          (bind (representativeEnv E first) term)) : TermQ E Θ sort) =
        Quotient.mk _
          (bind (representativeEnv E
            (fun s v => substitute E later (first s v))) term)
      rw [bind_comp]
      exact bind_classes_eq E _ _
        (representativeEnv_comp E first later) term

/-- Quotient substitution agrees with the earlier `bindQ` whenever the
semantic environment is represented pointwise by a given raw substitution. -/
theorem substitute_eq_bindQ (E : List (EqAxiom S M))
    {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (TermQ E) Γ Δ)
    (sigma : Sub S Γ Δ)
    (agree : ∀ s v,
      (Quotient.mk _ (sigma s v) : TermQ E Δ s) = env s v)
    (q : TermQ E Γ sort) :
    substitute E env q = bindQ sigma q := by
  induction q using Quotient.inductionOn with
  | _ term =>
      change (Quotient.mk _ (bind (representativeEnv E env) term) :
        TermQ E Δ sort) = Quotient.mk _ (bind sigma term)
      apply bind_classes_eq E _ _ _ term
      intro s v
      exact (mk_representativeEnv E env s v).trans (agree s v).symm

/-- The quotient fibres with their full quotient-valued substitution form a
multisorted clone. This is the substitution component of the pending full
binding-equation model. -/
noncomputable abbrev algebra (E : List (EqAxiom S M)) :
    BindingSubstitutionAlgebra.Algebra S where
  Carrier := TermQ E
  injectVar := fun v => Quotient.mk _ (Term.var v)
  substitute := substitute E
  substitute_var := substitute_var E
  substitute_identity := substitute_identity E
  substitute_comp := substitute_comp E

/-- Semantic weakening of an equation class is the old quotient renaming by
one fresh leading variable. -/
theorem algebra_weaken_eq_renameQ (E : List (EqAxiom S M))
    {Γ : Ctx S} {sort fresh : S.Srt}
    (q : TermQ E Γ sort) :
    (algebra E).weaken (fresh := fresh) q =
      renameQ (E := E) (fun _ v => Var.succ v) q := by
  change substitute E
      (fun _ v => (Quotient.mk _ (Term.var (.succ v)) :
        TermQ E (fresh :: Γ) _)) q =
    renameQ (E := E) (fun _ v => Var.succ v) q
  rw [substitute_eq_bindQ E
    (fun _ v => (Quotient.mk _ (Term.var (.succ v)) :
      TermQ E (fresh :: Γ) _))
    (fun _ v => Term.var (.succ v)) (by intro s v; rfl) q]
  induction q using Quotient.inductionOn with
  | _ term =>
      change (Quotient.mk _
        (bind (fun _ v => Term.var (.succ v)) term) :
        TermQ E (fresh :: Γ) sort) =
        Quotient.mk _ (rename (fun _ v => Var.succ v) term)
      exact congrArg (Quotient.mk _) (bind_var_eq_rename
        (fun _ v => Var.succ v) term)

/-- Representatives of a semantically lifted environment are pointwise
equivalent to the syntactic lift of its chosen representatives. -/
theorem liftEnvironment_represented (E : List (EqAxiom S M))
    {Γ Δ : Ctx S} (env : Environment S (TermQ E) Γ Δ) :
    ∀ (binders : List S.Srt) (sort : S.Srt)
      (v : Var (binders ++ Γ) sort),
      (Quotient.mk _
        (liftSub (representativeEnv E env) binders sort v) :
        TermQ E (binders ++ Δ) sort) =
      (algebra E).liftEnvironment env binders sort v
  | [], sort, v => mk_representativeEnv E env sort v
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ old => by
      change (Quotient.mk _
          (weaken (liftSub (representativeEnv E env) binders sort old)) :
          TermQ E (_ :: binders ++ Δ) sort) =
        (algebra E).weaken
          ((algebra E).liftEnvironment env binders sort old)
      rw [← liftEnvironment_represented E env binders sort old,
        algebra_weaken_eq_renameQ]
      rfl

end Mettapedia.OSLF.Binding.BindingEquationQuotientSubstitution
