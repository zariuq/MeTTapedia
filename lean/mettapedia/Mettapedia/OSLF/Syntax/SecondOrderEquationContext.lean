import Mettapedia.OSLF.Syntax.SecondOrderEquationCongruence
import Mathlib.CategoryTheory.Quotient

/-!
# Equational quotients of second-order contexts

An equation presentation assigns equations to each metavariable context.
Only its generator instances are required to be stable when metavariables are
instantiated. The derived equation closure then forms a congruence on the
second-order context category, so composition descends to equation classes.

The stability condition is still to be discharged for each authored equation
presentation; this construction does not assert that every arbitrary family
of local equations is stable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding

variable (S : Signature)

/-- A family of equation generators whose schema metavariables have the same
arity list at every ambient second-order context. Only generator stability is
required; closure under arbitrary derived equations follows by induction. -/
structure EquationPresentation (schema : List (MetaArity S)) where
  axioms : (X : Object S) →
    List (EqAxiom (withMetas S X.arities) schema)
  generator_substitute :
    ∀ {X Y : Object S} (substitution : X ⟶ Y)
      (index : Fin (axioms Y).length)
      (body : (k : Fin schema.length) →
        Term (withMetas S Y.arities)
          (schema.get k).1 (schema.get k).2),
      EqClosure (axioms X)
        (instInto substitution
          (instantiate body ((axioms Y).get index).lhs))
        (instInto substitution
          (instantiate body ((axioms Y).get index).rhs))

variable {S} {schema : List (MetaArity S)}

/-- Two arrows are equivalent exactly when every assigned metavariable body
is equivalent under the source context's authored equations. -/
def EquationPresentation.homRel (P : EquationPresentation S schema) :
    HomRel (Object S) :=
  fun {X _} first second =>
    ∀ index, EqClosure (P.axioms X) (first index) (second index)

/-- Equation closure is stable under substitution before an arrow. This
uses only the presentation's generator condition, not a presumed closure law. -/
theorem EquationPresentation.homRel_precomp
    (P : EquationPresentation S schema)
    {X Y Z : Object S} (substitution : X ⟶ Y)
    {first second : Y ⟶ Z}
    (related : P.homRel first second) :
    P.homRel (substitution ≫ first) (substitution ≫ second) := by
  intro index
  exact instInto_eqClosure_generators (D := P.axioms X)
    substitution (P.generator_substitute substitution)
    (related index)

/-- Equation closure is stable under substitution after an arrow, because
pointwise-equivalent assignments act equivalently on every scoped term. -/
theorem EquationPresentation.homRel_postcomp
    (P : EquationPresentation S schema)
    {X Y Z : Object S} {first second : X ⟶ Y}
    (after : Y ⟶ Z)
    (related : P.homRel first second) :
    P.homRel (first ≫ after) (second ≫ after) := by
  intro index
  exact instInto_pointwise_congr (P.axioms X) first second related (after index)

/-- Equation congruence on a map into a joined metavariable context is
exactly congruence on its two components. This is the compatibility needed
for categorical products to survive the equation quotient. -/
theorem EquationPresentation.homRel_pair_iff
    (P : EquationPresentation S schema)
    (source left right : Object S)
    (first first' : source ⟶ left)
    (second second' : source ⟶ right) :
    P.homRel
      (pair S source left right first second)
      (pair S source left right first' second') ↔
      P.homRel first first' ∧ P.homRel second second' := by
  constructor
  · intro related
    constructor
    · have projected := P.homRel_postcomp
        (firstProjection S left right) related
      simpa only [pair_first] using projected
    · have projected := P.homRel_postcomp
        (secondProjection S left right) related
      simpa only [pair_second] using projected
  · intro related
    exact pair_pointwise S source left right
      (fun _ _ => EqClosure (P.axioms source))
      first first' second second' related.1 related.2

/-- The pointwise generated equation relation is a categorical congruence.
The two composition directions have distinct proofs and are both needed. -/
instance EquationPresentation.congruence
    (P : EquationPresentation S schema) : Congruence P.homRel where
  equivalence := by
    intro X Y
    refine ⟨?_, ?_, ?_⟩
    · intro arrow index
      exact .refl _
    · intro first second related index
      exact .symm (related index)
    · intro first second third firstSecond secondThird index
      exact .trans (firstSecond index) (secondThird index)
  comp_left := by
    intro X Y Z substitution first second related
    exact P.homRel_precomp substitution related
  comp_right := by
    intro X Y Z first second after related
    exact P.homRel_postcomp after related

/-- The equation-class second-order context category. Its objects are
unchanged arity contexts; its arrows are classes of contextual assignments. -/
abbrev EquationContexts (P : EquationPresentation S schema) : Type :=
  _root_.CategoryTheory.Quotient P.homRel

/-- The canonical passage from raw contextual assignments to their equation
classes is a functor, with composition supplied by the congruence proof. -/
def EquationPresentation.quotientFunctor
    (P : EquationPresentation S schema) :
    Object S ⥤ EquationContexts P :=
  _root_.CategoryTheory.Quotient.functor P.homRel

/-- An equation in an ordinary variable context is a genuine presentation at
every second-order context. Its sides can be distinct raw terms; instantiation
cannot change their base operations or bound-variable positions. -/
def contextualAxioms (S : Signature) {Γ : Ctx S} {sort : S.Srt}
    (left right : Term S Γ sort) (X : Object S) :
    List (EqAxiom (withMetas S X.arities) []) :=
  [{ ctx := Γ
     sort := sort
     lhs := embed (M := []) (embed (M := X.arities) left)
     rhs := embed (M := []) (embed (M := X.arities) right) }]

/-- The family generated by any base-signature equation, including one with
ordinary free variables, satisfies the generator-substitution condition for
the quotient category. Closing substitutions are then handled by `EqClosure`. -/
def contextualPresentation (S : Signature) {Γ : Ctx S} {sort : S.Srt}
    (left right : Term S Γ sort) : EquationPresentation S [] where
  axioms := contextualAxioms S left right
  generator_substitute := by
    intro X Y substitution index body
    have zero : index.val = 0 := by
      have bound := index.isLt
      simp only [contextualAxioms, List.length_singleton] at bound
      omega
    have sameIndex : index = ⟨0, by simp [contextualAxioms]⟩ := Fin.ext zero
    subst index
    have generated := EqClosure.ax
      (E := contextualAxioms S left right X)
      (⟨0, by simp [contextualAxioms]⟩ :
        Fin (contextualAxioms S left right X).length)
      (fun i => Fin.elim0 i)
      (fun _ v => Term.var v)
    simpa [contextualAxioms, instantiate_embed, instInto_embed, bind_id]
      using generated

/-- A base-signature equation with an explicitly retained variable context.
Schema metavariables belong to the more general `EquationPresentation` layer. -/
structure BaseEquation (S : Signature) where
  context : Ctx S
  sort : S.Srt
  left : Term S context sort
  right : Term S context sort

mutual
/-- An empty metavariable extension contains only original operations;
dropping and re-embedding it changes no syntax. -/
theorem embed_instantiate_empty {S : Signature} :
    ∀ {Γ : Ctx S} {sort : S.Srt}
      (term : Term (withMetas S []) Γ sort),
      embed (M := [])
        (instantiate (M := []) (fun (i : Fin 0) => Fin.elim0 i) term) = term
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl op) args => by
      simp only [instantiate, embed]
      congr 1
      exact embedArgs_instantiate_empty args
  | _, _, .op (Sum.inr (.mk index)) _ => Fin.elim0 index

theorem embedArgs_instantiate_empty {S : Signature} :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Args (withMetas S []) arities Γ),
      embedArgs (M := [])
        (instantiateArgs (M := []) (fun (i : Fin 0) => Fin.elim0 i) args) = args
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
      simp only [instantiateArgs, embedArgs]
      congr 1
      · exact embed_instantiate_empty head
      · exact embedArgs_instantiate_empty tail
end

/-- Remove the redundant empty metavariable layer from a source equation.
This keeps its variable context, sort and exact syntax. -/
def BaseEquation.ofEmptySchema {S : Signature}
    (equation : EqAxiom S []) : BaseEquation S where
  context := equation.ctx
  sort := equation.sort
  left := instantiate (M := []) (fun (i : Fin 0) => Fin.elim0 i) equation.lhs
  right := instantiate (M := []) (fun (i : Fin 0) => Fin.elim0 i) equation.rhs

theorem BaseEquation.ofEmptySchema_left {S : Signature}
    (equation : EqAxiom S []) :
    embed (M := []) (BaseEquation.ofEmptySchema equation).left =
      equation.lhs :=
  embed_instantiate_empty equation.lhs

theorem BaseEquation.ofEmptySchema_right {S : Signature}
    (equation : EqAxiom S []) :
    embed (M := []) (BaseEquation.ofEmptySchema equation).right =
      equation.rhs :=
  embed_instantiate_empty equation.rhs

/-- Reinsert an empty schema layer around a base equation. -/
def BaseEquation.toEmptySchema {S : Signature}
    (equation : BaseEquation S) : EqAxiom S [] where
  ctx := equation.context
  sort := equation.sort
  lhs := embed (M := []) equation.left
  rhs := embed (M := []) equation.right

/-- Removing and reinserting the empty layer recovers the complete authored
equation, including its context, sort and both sides. -/
theorem BaseEquation.toEmptySchema_ofEmptySchema {S : Signature}
    (equation : EqAxiom S []) :
    (BaseEquation.ofEmptySchema equation).toEmptySchema = equation := by
  cases equation with
  | mk context sort left right =>
      simp [BaseEquation.toEmptySchema, BaseEquation.ofEmptySchema,
        embed_instantiate_empty]

/-- The conversion preserves every position in an authored list, not just
the collection of equations up to permutation. -/
theorem emptySchemaList_roundtrip {S : Signature}
    (equations : List (EqAxiom S [])) :
    (equations.map BaseEquation.ofEmptySchema).map
      BaseEquation.toEmptySchema = equations := by
  induction equations with
  | nil => rfl
  | cons equation rest ih =>
      simp only [List.map_cons]
      rw [BaseEquation.toEmptySchema_ofEmptySchema, ih]

/-- The same base equation viewed in a context with additional second-order
metavariables; those metavariables cannot occur in the written sides. -/
def BaseEquation.inContext {S : Signature} (equation : BaseEquation S)
    (X : Object S) : EqAxiom (withMetas S X.arities) [] where
  ctx := equation.context
  sort := equation.sort
  lhs := embed (M := []) (embed (M := X.arities) equation.left)
  rhs := embed (M := []) (embed (M := X.arities) equation.right)

/-- An ordered list of independently authored base equations is transported
to every second-order context without changing equation positions. -/
def baseEquationAxioms {S : Signature} (equations : List (BaseEquation S))
    (X : Object S) : List (EqAxiom (withMetas S X.arities) []) :=
  equations.map (·.inContext X)

/-- Ordinary variable-context equations, in arbitrary finite lists, define a
second-order quotient category. This includes associative, unit and
commutative presentations written with ordinary variables. -/
def baseEquationPresentation {S : Signature}
    (equations : List (BaseEquation S)) : EquationPresentation S [] where
  axioms := baseEquationAxioms equations
  generator_substitute := by
    intro X Y substitution index body
    let sourceIndex : Fin equations.length :=
      ⟨index.val, by simpa [baseEquationAxioms] using index.isLt⟩
    let targetIndex : Fin (baseEquationAxioms equations X).length :=
      ⟨sourceIndex.val, by simp [baseEquationAxioms]⟩
    have sourceGet :
        (baseEquationAxioms equations Y).get index =
          (equations.get sourceIndex).inContext Y := by
      change (equations.map (·.inContext Y))[sourceIndex.val] =
        (equations[sourceIndex.val]).inContext Y
      simp
    have targetGet :
        (baseEquationAxioms equations X).get targetIndex =
          (equations.get sourceIndex).inContext X := by
      change (equations.map (·.inContext X))[sourceIndex.val] =
        (equations[sourceIndex.val]).inContext X
      simp
    have generated := EqClosure.ax
      (E := baseEquationAxioms equations X)
      targetIndex
      (fun i => Fin.elim0 i)
      (fun _ v => Term.var v)
    rw [sourceGet]
    rw [targetGet] at generated
    simpa [BaseEquation.inContext, instantiate_embed, instInto_embed,
      bind_id] using generated

/-- Existing authored equation lists with no schema metavariables enter the
second-order quotient through an exact, position-preserving conversion. -/
def emptySchemaPresentation {S : Signature}
    (equations : List (EqAxiom S [])) : EquationPresentation S [] :=
  baseEquationPresentation
    (equations.map BaseEquation.ofEmptySchema)

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.EquationPresentation.congruence
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.baseEquationPresentation
