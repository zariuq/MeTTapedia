import Mettapedia.OSLF.Syntax.BindingEquationQuotientSubstitution

/-!
# Binding operators on equation classes

The quotient already supports full quotient-valued semantic substitution.
Each binding operator is now descended to equation classes. The key proof
compares substitution beneath every argument's binder list with the semantic
lift in the quotient clone; no equation is assumed to preserve occurrence
counts or to have a canonical representative.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationQuotientModel

open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BindingEquationQuotientSubstitution

variable {S : Signature} {M : List (MetaArity S)}

/-- Select a representative for every semantic operator argument, at the
ambient or binder-extended context declared by its arity. -/
noncomputable def representativeArgs (E : List (EqAxiom S M)) :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
      FamilyArgs S (TermQ E) arity Γ → Args S arity Γ
  | _, _, .nil => .nil
  | _, _, .cons head tail =>
      .cons (Quotient.out head) (representativeArgs E tail)

/-- An operator applied to equation classes is the class of its application
to any selected argument representatives. -/
noncomputable def operation (E : List (EqAxiom S M))
    {Γ : Ctx S} {sort : S.Srt} (op : S.Op sort)
    (args : FamilyArgs S (TermQ E) (S.arity op) Γ) :
    TermQ E Γ sort :=
  Quotient.mk _ (Term.op op (representativeArgs E args))

/-- The representative of each semantically substituted argument is
equivalent to syntactically substituting the representative of that argument.
The comparison passes below its declared binders. -/
theorem representativeArgs_substitute
    (E : List (EqAxiom S M))
    {Γ Δ : Ctx S} (env : Environment S (TermQ E) Γ Δ) :
    ∀ {arity : List (List S.Srt × S.Srt)}
      (args : FamilyArgs S (TermQ E) arity Γ),
      EqArgs E
        (bindArgs (representativeEnv E env) (representativeArgs E args))
        (representativeArgs E
          ((BindingEquationQuotientSubstitution.algebra E).substituteArgs env args))
  | _, .nil => .nil
  | _, .cons (bs := binders) head tail => by
      apply EqArgs.cons
      · have qEq :
          (Quotient.mk _
            (bind (liftSub (representativeEnv E env) binders)
              (Quotient.out head)) : TermQ E (binders ++ Δ) _) =
          Quotient.mk _ (Quotient.out
            (substitute E
              ((BindingEquationQuotientSubstitution.algebra E).liftEnvironment
                env binders) head)) := by
          calc
          (Quotient.mk _
              (bind (liftSub (representativeEnv E env) binders)
                (Quotient.out head)) :
              TermQ E (binders ++ Δ) _) =
              bindQ (liftSub (representativeEnv E env) binders)
                (Quotient.mk _ (Quotient.out head)) := rfl
          _ = bindQ (liftSub (representativeEnv E env) binders) head := by
                rw [Quotient.out_eq]
          _ = substitute E
              ((BindingEquationQuotientSubstitution.algebra E).liftEnvironment
                env binders) head := by
                exact (substitute_eq_bindQ E
                  ((BindingEquationQuotientSubstitution.algebra E).liftEnvironment
                    env binders)
                  (liftSub (representativeEnv E env) binders)
                  (liftEnvironment_represented E env binders) head).symm
          _ = Quotient.mk _ (Quotient.out
              (substitute E
              ((BindingEquationQuotientSubstitution.algebra E).liftEnvironment
                  env binders) head)) :=
                (Quotient.out_eq _).symm
        exact Quotient.exact qEq
      · exact representativeArgs_substitute E env tail

/-- Full binding-clone model structure descends to the equation quotient.
This establishes substitution compatibility of all base operators. A separate
theorem must still prove satisfaction of each authored axiom for all semantic
metavariable valuations. -/
noncomputable abbrev algebra (E : List (EqAxiom S M)) :
    Mettapedia.OSLF.Binding.BindingCloneAlgebra.Algebra S where
  substitution := BindingEquationQuotientSubstitution.algebra E
  operation := operation E
  operation_substitute := by
    intro Γ Δ sort env op args
    change (Quotient.mk _
        (bind (representativeEnv E env)
          (Term.op op (representativeArgs E args))) : TermQ E Δ sort) =
      Quotient.mk _
        (Term.op op
          (representativeArgs E
            ((BindingEquationQuotientSubstitution.algebra E).substituteArgs env args)))
    apply Quotient.sound
    exact EqClosure.cong op (representativeArgs_substitute E env args)

/-- Representatives of the quotient images of actual arguments are
congruent to those original arguments, including arguments beneath binders. -/
theorem representativeArgs_map_mk (E : List (EqAxiom S M)) :
    ∀ {arity : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (Term S) arity Γ),
      EqArgs E
        (representativeArgs E
          (FamilyArgs.map
            (fun {Γ sort} (term : Term S Γ sort) =>
              (Quotient.mk _ term : TermQ E Γ sort)) args))
        ((FreeBindingTerms.terms.familyToSyntax S) args)
  | _, _, .nil => .nil
  | _, _, .cons head tail => by
      have qEq :
          (Quotient.mk _
            (Quotient.out (Quotient.mk _ head : TermQ E _ _)) :
            TermQ E _ _) = Quotient.mk _ head := Quotient.out_eq _
      have h : EqClosure E
          (Quotient.out (Quotient.mk _ head : TermQ E _ _)) head :=
        Quotient.exact qEq
      exact .cons h (representativeArgs_map_mk E tail)

/-- The quotient projection is a morphism of binding clones. This includes
the semantic substitution law for arbitrary syntactic substitutions, rather
than only a family of quotient maps. -/
noncomputable def projection (E : List (EqAxiom S M)) :
    FreeBindingClone.Hom (BindingCloneAlgebra.terms S) (algebra E) where
  raw :=
    { map := fun term => Quotient.mk _ term
      map_variable := by intro Γ sort v; rfl
      map_operation := by
        intro Γ sort op args
        apply Quotient.sound
        exact EqClosure.symm
          (EqClosure.cong op (representativeArgs_map_mk E args)) }
  map_substitute := by
    intro Γ Δ sort sigma term
    change (Quotient.mk _ (bind sigma term) : TermQ E Δ sort) =
      substitute E
        (fun s v => (Quotient.mk _ (sigma s v) : TermQ E Δ s))
        (Quotient.mk _ term)
    rw [substitute_eq_bindQ E
      (fun s v => (Quotient.mk _ (sigma s v) : TermQ E Δ s))
      sigma (by intro s v; rfl)]
    rfl

/-- Folding syntax into the quotient model is the existing quotient map.
This comparison is obtained from initiality of the free binding clone and the
explicit quotient projection morphism. -/
theorem interpret_eq_mk (E : List (EqAxiom S M))
    {Γ : Ctx S} {sort : S.Srt} (term : Term S Γ sort) :
    BindingCloneFoldSubstitution.interpret (algebra E) term =
      (Quotient.mk _ term : TermQ E Γ sort) := by
  have h := FreeBindingClone.hom_unique (algebra E) (projection E)
  have onTerm := congrArg
    (fun f : FreeBindingClone.Hom (BindingCloneAlgebra.terms S) (algebra E) =>
      f.raw.map term) h
  exact onTerm.symm

/-- Choose a raw representative of each semantic metavariable value. The
equation quotient will make the choice irrelevant. -/
noncomputable def valuationBodies (E : List (EqAxiom S M))
    (valuation : BindingEquationalModels.MetaValuation (algebra E) M) :
    (k : Fin M.length) → Term S (M.get k).1 (M.get k).2 :=
  fun k => Quotient.out (valuation k)

/-- Every semantic valuation of the quotient is represented by syntactic
metavariable bodies, so interpreting a schema there is the class of its
ordinary syntactic instance. -/
theorem interpretSchema_eq_mk (E : List (EqAxiom S M))
    (valuation : BindingEquationalModels.MetaValuation (algebra E) M)
    {Γ : Ctx S} {sort : S.Srt}
    (term : Term (withMetas S M) Γ sort) :
    BindingEquationInterpretation.interpretSchema (algebra E) valuation term =
      (Quotient.mk _ (instantiate (valuationBodies E valuation) term) :
        TermQ E Γ sort) := by
  have values_agree :
      (fun k => BindingCloneFoldSubstitution.interpret (algebra E)
        (valuationBodies E valuation k)) = valuation := by
    funext k
    rw [interpret_eq_mk]
    exact Quotient.out_eq _
  have first :
      BindingEquationInterpretation.interpretSchema (algebra E) valuation term =
      BindingEquationInterpretation.interpretSchema (algebra E)
        (fun k => BindingCloneFoldSubstitution.interpret (algebra E)
          (valuationBodies E valuation k)) term := by rw [values_agree]
  have second := BindingEquationInterpretation.interpretSchema_instantiate
    (algebra E) (valuationBodies E valuation) term
  have third := interpret_eq_mk E
    (instantiate (valuationBodies E valuation) term)
  exact first.trans (second.trans third)

/-- The actual equation quotient satisfies every authored equation for
arbitrary semantic metavariable values and arbitrary semantic assignments of
the axiom's ordinary variables. -/
theorem algebra_satisfies (E : List (EqAxiom S M)) :
    BindingEquationInterpretation.Satisfies (algebra E) E := by
  intro i valuation Γ env
  let body := valuationBodies E valuation
  let close := representativeEnv E env
  have close_agree : ∀ s v,
      (Quotient.mk _ (close s v) : TermQ E Γ s) = env s v := by
    intro s v
    exact mk_representativeEnv E env s v
  have left_eval :
      (algebra E).substitution.substitute env
        (BindingEquationInterpretation.interpretSchema (algebra E)
          valuation (E.get i).lhs) =
      (Quotient.mk _ (bind close (instantiate body (E.get i).lhs)) :
        TermQ E Γ (E.get i).sort) := by
    rw [interpretSchema_eq_mk]
    change substitute E env
      (Quotient.mk _ (instantiate body (E.get i).lhs)) = _
    rw [substitute_eq_bindQ E env close close_agree]
    rfl
  have right_eval :
      (algebra E).substitution.substitute env
        (BindingEquationInterpretation.interpretSchema (algebra E)
          valuation (E.get i).rhs) =
      (Quotient.mk _ (bind close (instantiate body (E.get i).rhs)) :
        TermQ E Γ (E.get i).sort) := by
    rw [interpretSchema_eq_mk]
    change substitute E env
      (Quotient.mk _ (instantiate body (E.get i).rhs)) = _
    rw [substitute_eq_bindQ E env close close_agree]
    rfl
  exact left_eval.trans
    ((Quotient.sound (EqClosure.ax i body close)).trans right_eval.symm)

end Mettapedia.OSLF.Binding.BindingEquationQuotientModel
