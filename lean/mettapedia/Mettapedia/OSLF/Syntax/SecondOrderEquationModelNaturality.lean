import Mettapedia.OSLF.Syntax.SecondOrderEquationModelFiber

/-!
# Contextual naturality of authored equation-class substitution

An assignment of second-order metavariables changes the ambient context of
an authored equation model. Its action on equation classes commutes with both
raw capture-avoiding substitution and semantic substitution by equation
classes. This is the substitution part of the comparison between the context
classifier and the binding-equation models in its fibres.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding

variable {S : Signature} {M : List (MetaArity S)}

/-- Replacing contextual metavariables commutes with substitution of ordinary
variables, including in operator arguments under binders. -/
theorem substituteTermClass_bindQ (P : EquationPresentation S M)
    {X Y : Object S} (assignment : X ⟶ Y)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Sub (withMetas S Y.arities) Γ Δ)
    (term : EquationTermClass P Y Γ sort) :
    substituteTermClass P assignment
        (bindQ (E := P.axioms Y) environment term) =
      bindQ (E := P.axioms X)
        (fun s v => instInto assignment (environment s v))
        (substituteTermClass P assignment term) := by
  induction term using Quot.ind with
  | _ representative =>
      change Quot.mk _ (instInto assignment (bind environment representative)) =
        Quot.mk _ (bind (fun s v => instInto assignment (environment s v))
          (instInto assignment representative))
      exact congrArg (Quot.mk (EqClosure (P.axioms X)))
        (instInto_bind assignment environment representative)

/-- The same naturality law holds for the quotient-valued substitution of
the actual binding-clone model, not merely for raw syntactic environments. -/
theorem substituteTermClass_semanticSubstitute
    (P : EquationPresentation S M)
    {X Y : Object S} (assignment : X ⟶ Y)
    {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : BindingSubstitutionAlgebra.Environment
      (withMetas S Y.arities)
      (fun context output => EquationTermClass P Y context output) Γ Δ)
    (term : EquationTermClass P Y Γ sort) :
    substituteTermClass P assignment
        (BindingEquationQuotientSubstitution.substitute
          (P.axioms Y) environment term) =
      BindingEquationQuotientSubstitution.substitute
        (P.axioms X)
        (fun s v => substituteTermClass P assignment (environment s v))
        (substituteTermClass P assignment term) := by
  let representatives :=
    BindingEquationQuotientSubstitution.representativeEnv (P.axioms Y)
      environment
  have agree (s : S.Srt) (v : Var Γ s) :
      (Quot.mk _ (instInto assignment (representatives s v)) :
        EquationTermClass P X Δ s) =
        substituteTermClass P assignment (environment s v) := by
    have h := BindingEquationQuotientSubstitution.mk_representativeEnv
      (P.axioms Y) environment s v
    exact congrArg (substituteTermClass P assignment) h
  rw [BindingEquationQuotientSubstitution.substitute_eq_bindQ
    (P.axioms Y) environment representatives
    (BindingEquationQuotientSubstitution.mk_representativeEnv
      (P.axioms Y) environment) term]
  rw [substituteTermClass_bindQ P assignment representatives term]
  exact (BindingEquationQuotientSubstitution.substitute_eq_bindQ
    (P.axioms X)
    (fun s v => substituteTermClass P assignment (environment s v))
    (fun s v => instInto assignment (representatives s v))
    agree (substituteTermClass P assignment term)).symm

/-- Representative vectors commute with a contextual assignment up to the
actual authored equation congruence. The result keeps the binder context of
every argument, rather than comparing only closed operator applications. -/
theorem representativeArgs_contextMap (P : EquationPresentation S M)
    {X Y : Object S} (assignment : X ⟶ Y) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FreeBindingTerms.FamilyArgs S
        (fun context output => EquationTermClass P Y context output) arities Γ),
      EqArgs (P.axioms X)
        (instIntoArgs assignment
          (BindingEquationQuotientModel.representativeArgs (P.axioms Y)
            (toAmbientArgs Y args)))
        (BindingEquationQuotientModel.representativeArgs (P.axioms X)
          (toAmbientArgs X
            (FreeBindingTerms.FamilyArgs.map (S := S)
              (fun {Γ} {s} (term : EquationTermClass P Y Γ s) =>
                substituteTermClass P assignment term) args)))
  | _, _, .nil => .nil
  | _, _, .cons head tail => by
      apply EqArgs.cons
      · let source : TermQ (P.axioms Y) _ _ := head
        let target : TermQ (P.axioms X) _ _ :=
          substituteTermClass P assignment head
        have mapped :
          (Quotient.mk _ (instInto assignment (Quotient.out source)) :
              TermQ (P.axioms X) _ _) =
            substituteTermClass P assignment head := by
          have original := Quotient.out_eq source
          exact congrArg (substituteTermClass P assignment) original
        have selected := Quotient.out_eq target
        exact Quotient.exact (mapped.trans selected.symm)
      · exact representativeArgs_contextMap P assignment tail

/-- A contextual assignment preserves every original binding operator after
quotienting by authored equations. The proof uses congruence on all semantic
arguments, including those in binder-extended contexts. -/
theorem substituteTermClass_operation (P : EquationPresentation S M)
    {X Y : Object S} (assignment : X ⟶ Y)
    {Γ : Ctx S} {sort : S.Srt} (operation : S.Op sort)
    (args : FreeBindingTerms.FamilyArgs S
      (fun context output => EquationTermClass P Y context output)
      (S.arity operation) Γ) :
    substituteTermClass P assignment
        ((restrictAlgebra Y (BindingEquationQuotientModel.algebra
          (P.axioms Y))).operation operation args) =
      (restrictAlgebra X (BindingEquationQuotientModel.algebra
        (P.axioms X))).operation operation
        (FreeBindingTerms.FamilyArgs.map (S := S)
          (fun {Γ} {s} (term : EquationTermClass P Y Γ s) =>
            substituteTermClass P assignment term) args) := by
  change Quot.mk _
      (instInto assignment
        (Term.op (S := withMetas S Y.arities) (Sum.inl operation)
          (BindingEquationQuotientModel.representativeArgs
            (P.axioms Y) (toAmbientArgs Y args)))) =
    Quot.mk _
      (Term.op (S := withMetas S X.arities) (Sum.inl operation)
        (BindingEquationQuotientModel.representativeArgs
          (P.axioms X)
          (toAmbientArgs X
            (FreeBindingTerms.FamilyArgs.map (S := S)
              (fun {Γ} {s} (term : EquationTermClass P Y Γ s) =>
                substituteTermClass P assignment term) args))))
  apply Quot.sound
  exact EqClosure.cong (E := P.axioms X)
    (S := withMetas S X.arities) (Sum.inl operation)
    (representativeArgs_contextMap P assignment args)

/-- Contextual assignment acts on the quotient binding-clone models, not
merely on their underlying sets of terms. This map preserves variables,
original binding operators and arbitrary quotient-valued substitution. -/
noncomputable def authoredEquationModelMap (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M))
    {X Y : Object S} (assignment : X ⟶ Y) :
    FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y).algebra
      (authoredEquationModelAt S equations X).algebra where
  raw := {
    map := substituteTermClass
      (authoredEquationPresentation S equations) assignment
    map_variable := by
      intro Γ sort index
      rfl
    map_operation := by
      intro Γ sort operation args
      exact substituteTermClass_operation
        (authoredEquationPresentation S equations) assignment operation args }
  map_substitute := by
    intro Γ Δ sort environment term
    exact substituteTermClass_semanticSubstitute
      (authoredEquationPresentation S equations) assignment environment term

/-- The model map for the identity contextual assignment is the identity
binding-clone map. -/
theorem authoredEquationModelMap_id (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M))
    (X : Object S) :
    authoredEquationModelMap S equations (𝟙 X) =
      FreeBindingClone.Hom.id (authoredEquationModelAt S equations X).algebra := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ sort term
  exact substituteTermClass_id
    (authoredEquationPresentation S equations) X term

/-- Two contextual assignments act on the equation models in the expected
contravariant order, with the clone homomorphism laws intact. -/
theorem authoredEquationModelMap_comp (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M))
    {X Y Z : Object S} (first : X ⟶ Y) (second : Y ⟶ Z) :
    authoredEquationModelMap S equations (first ≫ second) =
      FreeBindingClone.Hom.comp
        (authoredEquationModelMap S equations second)
        (authoredEquationModelMap S equations first) := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ sort term
  exact substituteTermClass_comp
    (authoredEquationPresentation S equations) first second term

/-- Contextual assignments identified by the authored equations induce
exactly the same map of binding-equation models. This is the descent condition
for the operational construction over the equation-class context category. -/
theorem authoredEquationModelMap_congr (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M))
    {X Y : Object S} (first second : X ⟶ Y)
    (related : (authoredEquationPresentation S equations).homRel
      first second) :
    authoredEquationModelMap S equations first =
      authoredEquationModelMap S equations second := by
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ sort term
  induction term using Quot.ind with
  | _ representative =>
      apply Quot.sound
      exact instInto_pointwise_congr
        ((authoredEquationPresentation S equations).axioms X)
        first second related representative

/-- The binding-clone map descends to an arrow of the authored equation
context category. In particular, a change of metavariable assignment by an
authored equation cannot change any interpreted equation class. -/
noncomputable def authoredEquationModelMapQuot (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M))
    {X Y : EquationContexts (authoredEquationPresentation S equations)}
    (assignment : X ⟶ Y) :
    FreeBindingClone.Hom
      (authoredEquationModelAt S equations Y.as).algebra
      (authoredEquationModelAt S equations X.as).algebra :=
  Quot.liftOn assignment
    (fun raw => authoredEquationModelMap S equations raw)
    (by
      intro first second related
      apply authoredEquationModelMap_congr S equations first second
      simpa only [HomRel.compClosure_eq_self
        (authoredEquationPresentation S equations).homRel] using related)

/-- Descent agrees with the proved model map on each concrete contextual
assignment. -/
theorem authoredEquationModelMapQuot_mk (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M))
    {X Y : Object S} (assignment : X ⟶ Y) :
    authoredEquationModelMapQuot S equations
        ((authoredEquationPresentation S equations).quotientFunctor.map
          assignment) =
      authoredEquationModelMap S equations assignment := rfl

/-- The model presheaf descends through equation classes of contextual
assignments. Its domain is the actual classifying context category, rather
than the raw syntax category before equations. -/
noncomputable def authoredEquationQuotientModelPresheaf (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M)) :
    (EquationContexts (authoredEquationPresentation S equations))ᵒᵖ ⥤
      FreeBindingEquationModel.Model equations where
  obj context := authoredEquationModelAt S equations context.unop.as
  map assignment := authoredEquationModelMapQuot S equations assignment.unop
  map_id context := by
    change authoredEquationModelMap S equations (𝟙 context.unop.as) =
      FreeBindingClone.Hom.id
        (authoredEquationModelAt S equations context.unop.as).algebra
    exact authoredEquationModelMap_id S equations context.unop.as
  map_comp first second := by
    change authoredEquationModelMapQuot S equations
        (second.unop ≫ first.unop) =
      FreeBindingClone.Hom.comp
        (authoredEquationModelMapQuot S equations first.unop)
        (authoredEquationModelMapQuot S equations second.unop)
    induction first.unop using Quot.ind with
    | _ firstRaw =>
        induction second.unop using Quot.ind with
        | _ secondRaw =>
            exact authoredEquationModelMap_comp S equations
              secondRaw firstRaw

/-- The actual authored equation models form a presheaf on second-order
contexts. This packages the identity and composition laws of contextual
metavariable instantiation at the full binding-clone level. -/
noncomputable def authoredEquationModelPresheaf (S : Signature)
    {M : List (MetaArity S)} (equations : List (EqAxiom S M)) :
    (Object S)ᵒᵖ ⥤ FreeBindingEquationModel.Model equations where
  obj context := authoredEquationModelAt S equations context.unop
  map assignment := authoredEquationModelMap S equations assignment.unop
  map_id context := by
    exact authoredEquationModelMap_id S equations context.unop
  map_comp first second := by
    exact authoredEquationModelMap_comp S equations
      second.unop first.unop

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.substituteTermClass_bindQ
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.substituteTermClass_semanticSubstitute
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.substituteTermClass_operation
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationModelMap
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationModelMap_comp
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationModelMap_congr
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationModelMapQuot
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationQuotientModelPresheaf
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.authoredEquationModelPresheaf
