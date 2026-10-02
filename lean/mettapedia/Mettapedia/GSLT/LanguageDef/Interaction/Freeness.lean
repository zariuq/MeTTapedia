import Mettapedia.GSLT.LanguageDef.InteractionCut
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# A free constructor keeps its position

When no equation of a presentation can act at the head of a constructor, the
static equivalence cannot change what that constructor brings together.  A
term headed by it is equivalent only to terms headed by it, and the
equivalence acts on the operands one by one.  Position at such a constructor
is therefore invariant: no chain of equations puts a different operand next
to a given one.

The hypothesis is about heads.  Every authored equation must have, on each
side, a constructor application headed by something else, and the
presentation must declare no collection algebra.  The first excludes
equations headed by the constructor and equations with a bare variable on one
side, which would wrap or unwrap any term at all; the second excludes the
singleton law of a flattening collection, which identifies a one-element
collection with its element.

The predicate `ContactEquationFree` asks that the contact constructor occur
nowhere in an authored equation.  It is neither weaker nor stronger: it does
not exclude a collapsing equation or a collection law, and it does exclude
equations that mention the constructor below their head.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open EquationSemantics

/-- Both sides of every authored equation are constructor applications headed
by something other than `label`. -/
def EquationHeadsAvoid (language : LanguageDef) (label : String) : Prop :=
  ∀ equation : Equation, List.Mem equation language.equations →
    (∃ head arguments, equation.left = .apply head arguments ∧ head ≠ label) ∧
      (∃ head arguments, equation.right = .apply head arguments ∧ head ≠ label)

section Rigidity

variable {base : BasePremiseEvaluator} {language : LanguageDef} {label : String}

/-- A schema headed by another constructor matches no term headed by `label`. -/
theorem matchPattern_apply_eq_nil_of_ne {head : String} {schema arguments : List Pattern}
    (different : head ≠ label) (bindings : Bindings) :
    bindings ∉ matchPattern (.apply head schema) (.apply label arguments) := by
  intro matched
  have relation := matchPattern_sound matched
  cases relation with
  | apply _ _ => exact different rfl

/-- No authored equation acts at the head of a term headed by `label`. -/
theorem not_equationInstance_of_headed_source
    (avoid : EquationHeadsAvoid language label) {arguments : List Pattern}
    {target : Pattern} :
    ¬ EquationInstance base language (.apply label arguments) target := by
  rintro ⟨fuel, authored⟩
  cases authored with
  | forward membership matched _ _ =>
      obtain ⟨⟨head, schema, left, different⟩, -⟩ := avoid _ membership
      rw [left] at matched
      exact matchPattern_apply_eq_nil_of_ne different _ matched
  | reverse membership matched _ _ =>
      obtain ⟨-, head, schema, right, different⟩ := avoid _ membership
      rw [right] at matched
      exact matchPattern_apply_eq_nil_of_ne different _ matched

/-- No authored equation produces a term headed by `label`. -/
theorem not_equationInstance_of_headed_target
    (avoid : EquationHeadsAvoid language label) {arguments : List Pattern}
    {source : Pattern} :
    ¬ EquationInstance base language source (.apply label arguments) := by
  rintro ⟨fuel, authored⟩
  cases authored with
  | forward membership _ _ applied =>
      obtain ⟨-, head, schema, right, different⟩ := avoid _ membership
      rw [right] at applied
      simp only [applyBindings, Pattern.apply.injEq] at applied
      exact different applied.1
  | reverse membership _ _ applied =>
      obtain ⟨⟨head, schema, left, different⟩, -⟩ := avoid _ membership
      rw [left] at applied
      simp only [applyBindings, Pattern.apply.injEq] at applied
      exact different applied.1

/-- Without a declared collection algebra, a presentation-derived law relates
collections to collections: it neither consumes nor produces a constructor
application. -/
theorem not_derivedInstance_apply
    (noAlgebra : language.hasAlgebraDeclarations = false)
    {head : String} {arguments : List Pattern} {other : Pattern} :
    ¬ DerivedInstance language (.apply head arguments) other ∧
      ¬ DerivedInstance language other (.apply head arguments) := by
  constructor
  · intro derived
    cases derived
  · intro derived
    generalize target : Pattern.apply head arguments = produced at derived
    cases derived with
    | bagPerm _ _ _ => cases target
    | setPerm _ _ _ => cases target
    | setDedup _ _ => cases target
    | flatten algebraRule _ _ =>
        exact no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra algebraRule
    | singleton algebraRule _ _ =>
        exact no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra algebraRule
    | unitElim algebraRule _ _ =>
        exact no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra algebraRule
    | emptyUnit algebraRule _ _ =>
        exact no_algebraRule_of_hasAlgebraDeclarations_eq_false noAlgebra algebraRule

/-- One equation step out of a term headed by `label` changes one operand and
leaves the head and the other operands in place. -/
theorem contextStep_of_headed_source
    (avoid : EquationHeadsAvoid language label)
    (noAlgebra : language.hasAlgebraDeclarations = false)
    {arguments : List Pattern} {target : Pattern}
    (step : EquationContextStep base language (.apply label arguments) target) :
    ∃ (before after : List Pattern) (operand operand' : Pattern),
      arguments = before ++ operand :: after ∧
        target = .apply label (before ++ operand' :: after) ∧
          EquationContextStep base language operand operand' := by
  generalize source : Pattern.apply label arguments = start at step
  cases step with
  | inContext context generator =>
      cases context with
      | hole =>
          simp only [OneHoleContext.fill] at source
          subst source
          rcases generator with authored | derived
          · exact absurd authored (not_equationInstance_of_headed_source avoid)
          · exact absurd derived (not_derivedInstance_apply noAlgebra).1
      | apply constructor before inner after =>
          simp only [OneHoleContext.fill, Pattern.apply.injEq] at source
          obtain ⟨rfl, rfl⟩ := source
          exact ⟨before, after, _, _, rfl, rfl, .inContext inner generator⟩
      | lambda _ _ => simp [OneHoleContext.fill] at source
      | multiLambda _ _ _ => simp [OneHoleContext.fill] at source
      | substBody _ _ => simp [OneHoleContext.fill] at source
      | substReplacement _ _ => simp [OneHoleContext.fill] at source
      | collection _ _ _ _ _ => simp [OneHoleContext.fill] at source

/-- One equation step into a term headed by `label` comes from a term headed
by `label`, with one operand changed. -/
theorem contextStep_of_headed_target
    (avoid : EquationHeadsAvoid language label)
    (noAlgebra : language.hasAlgebraDeclarations = false)
    {arguments : List Pattern} {source : Pattern}
    (step : EquationContextStep base language source (.apply label arguments)) :
    ∃ (before after : List Pattern) (operand operand' : Pattern),
      source = .apply label (before ++ operand :: after) ∧
        arguments = before ++ operand' :: after ∧
          EquationContextStep base language operand operand' := by
  generalize target : Pattern.apply label arguments = finish at step
  cases step with
  | inContext context generator =>
      cases context with
      | hole =>
          simp only [OneHoleContext.fill] at target
          subst target
          rcases generator with authored | derived
          · exact absurd authored (not_equationInstance_of_headed_target avoid)
          · exact absurd derived (not_derivedInstance_apply noAlgebra).2
      | apply constructor before inner after =>
          simp only [OneHoleContext.fill, Pattern.apply.injEq] at target
          obtain ⟨rfl, rfl⟩ := target
          exact ⟨before, after, _, _, rfl, rfl, .inContext inner generator⟩
      | lambda _ _ => simp [OneHoleContext.fill] at target
      | multiLambda _ _ _ => simp [OneHoleContext.fill] at target
      | substBody _ _ => simp [OneHoleContext.fill] at target
      | substReplacement _ _ => simp [OneHoleContext.fill] at target
      | collection _ _ _ _ _ => simp [OneHoleContext.fill] at target

/-- Changing one operand by one step relates the operand lists pointwise. -/
theorem forall₂_of_one_operand {before after : List Pattern} {operand operand' : Pattern}
    (step : EquationContextStep base language operand operand') :
    List.Forall₂ (EquationEquiv base language)
      (before ++ operand :: after) (before ++ operand' :: after) := by
  induction before with
  | nil =>
      refine List.Forall₂.cons (Relation.EqvGen.rel _ _ step) ?_
      exact List.forall₂_same.mpr fun pattern _ => Relation.EqvGen.refl pattern
  | cons head tail recurse =>
      exact List.Forall₂.cons (Relation.EqvGen.refl head) recurse

/-- Pointwise relatedness composes along a transitive relation. -/
theorem forall₂_trans {α : Type*} {relation : α → α → Prop}
    (transitive : ∀ first second third,
      relation first second → relation second third → relation first third) :
    ∀ {first second third : List α},
      List.Forall₂ relation first second → List.Forall₂ relation second third →
        List.Forall₂ relation first third
  | [], [], [], _, _ => .nil
  | _ :: _, _ :: _, _ :: _, .cons headFirst tailFirst, .cons headSecond tailSecond =>
      .cons (transitive _ _ _ headFirst headSecond)
        (forall₂_trans transitive tailFirst tailSecond)

/-- **Position is unforgeable.**  A term headed by a constructor that no
equation acts on is equivalent only to terms headed by that constructor, and
then operand by operand. -/
theorem equationEquiv_of_headed
    (avoid : EquationHeadsAvoid language label)
    (noAlgebra : language.hasAlgebraDeclarations = false)
    {left right : Pattern} (equivalent : EquationEquiv base language left right) :
    (∀ arguments, left = .apply label arguments →
      ∃ arguments', right = .apply label arguments' ∧
        List.Forall₂ (EquationEquiv base language) arguments arguments') ∧
    (∀ arguments', right = .apply label arguments' →
      ∃ arguments, left = .apply label arguments ∧
        List.Forall₂ (EquationEquiv base language) arguments arguments') := by
  induction equivalent with
  | rel left right step =>
      constructor
      · rintro arguments rfl
        obtain ⟨before, after, operand, operand', rfl, rfl, inner⟩ :=
          contextStep_of_headed_source avoid noAlgebra step
        exact ⟨_, rfl, forall₂_of_one_operand inner⟩
      · rintro arguments' rfl
        obtain ⟨before, after, operand, operand', rfl, rfl, inner⟩ :=
          contextStep_of_headed_target avoid noAlgebra step
        exact ⟨_, rfl, forall₂_of_one_operand inner⟩
  | refl pattern =>
      constructor
      · rintro arguments rfl
        exact ⟨arguments, rfl,
          List.forall₂_same.mpr fun pattern _ => Relation.EqvGen.refl pattern⟩
      · rintro arguments rfl
        exact ⟨arguments, rfl,
          List.forall₂_same.mpr fun pattern _ => Relation.EqvGen.refl pattern⟩
  | symm left right _ recurse =>
      constructor
      · rintro arguments rfl
        obtain ⟨arguments', same, pointwise⟩ := recurse.2 arguments rfl
        exact ⟨arguments', same,
          (pointwise.imp fun _ _ related => Relation.EqvGen.symm _ _ related).flip⟩
      · rintro arguments' rfl
        obtain ⟨arguments, same, pointwise⟩ := recurse.1 arguments' rfl
        exact ⟨arguments, same,
          (pointwise.imp fun _ _ related => Relation.EqvGen.symm _ _ related).flip⟩
  | trans left middle right _ _ first second =>
      constructor
      · rintro arguments rfl
        obtain ⟨middleArguments, rfl, firstPointwise⟩ := first.1 arguments rfl
        obtain ⟨arguments', same, secondPointwise⟩ := second.1 middleArguments rfl
        exact ⟨arguments', same,
          forall₂_trans (fun _ _ _ => Relation.EqvGen.trans _ _ _)
            firstPointwise secondPointwise⟩
      · rintro arguments' rfl
        obtain ⟨middleArguments, rfl, secondPointwise⟩ := second.2 arguments' rfl
        obtain ⟨arguments, same, firstPointwise⟩ := first.2 middleArguments rfl
        exact ⟨arguments, same,
          forall₂_trans (fun _ _ _ => Relation.EqvGen.trans _ _ _)
            firstPointwise secondPointwise⟩

/-- The binary form: what is equivalent to a contact of two operands is a
contact of two equivalent operands. -/
theorem equationEquiv_binary_of_headed
    (avoid : EquationHeadsAvoid language label)
    (noAlgebra : language.hasAlgebraDeclarations = false)
    {program environment other : Pattern}
    (equivalent : EquationEquiv base language (.apply label [program, environment]) other) :
    ∃ program' environment', other = .apply label [program', environment'] ∧
      EquationEquiv base language program program' ∧
        EquationEquiv base language environment environment' := by
  obtain ⟨arguments', rfl, pointwise⟩ :=
    (equationEquiv_of_headed avoid noAlgebra equivalent).1 _ rfl
  match arguments', pointwise with
  | [program', environment'], .cons first (.cons second .nil) =>
      exact ⟨program', environment', rfl, first, second⟩

/-- Two contacts are equivalent exactly when their operands are, side by
side. -/
theorem equationEquiv_binary_iff
    (avoid : EquationHeadsAvoid language label)
    (noAlgebra : language.hasAlgebraDeclarations = false)
    {program environment program' environment' : Pattern} :
    EquationEquiv base language (.apply label [program, environment])
        (.apply label [program', environment']) ↔
      EquationEquiv base language program program' ∧
        EquationEquiv base language environment environment' := by
  constructor
  · intro equivalent
    obtain ⟨first, second, same, programEquivalent, environmentEquivalent⟩ :=
      equationEquiv_binary_of_headed avoid noAlgebra equivalent
    simp only [Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
    obtain ⟨rfl, rfl⟩ := same
    exact ⟨programEquivalent, environmentEquivalent⟩
  · rintro ⟨programEquivalent, environmentEquivalent⟩
    exact equationEquiv_apply_of_forall₂ label
      (.cons programEquivalent (.cons environmentEquivalent .nil))

end Rigidity

/-! ## On the interacting fibre of a presentation -/

/-- Equivalence in the interacting fibre is equivalence of the underlying
terms. -/
theorem equationEquiv_of_presentedEquationSetoid
    {base : BasePremiseEvaluator} {presentation : InteractivePresentation}
    {left right : presentation.Term}
    (equivalent : (presentedEquationSetoid base presentation).r left right) :
    EquationEquiv base presentation.presentation.language left.1 right.1 := by
  induction equivalent with
  | rel left right step => exact Relation.EqvGen.rel _ _ step
  | refl term => exact Relation.EqvGen.refl _
  | symm left right _ recurse => exact Relation.EqvGen.symm _ _ recurse
  | trans left middle right _ _ first second => exact Relation.EqvGen.trans _ _ _ first second

/-- The contact of a presentation is rigid when no equation acts at its head
and no collection algebra is declared. -/
def InteractivePresentation.RigidContact (presentation : InteractivePresentation) : Prop :=
  EquationHeadsAvoid presentation.presentation.language
      presentation.contactConstructor.1.label ∧
    presentation.presentation.language.hasAlgebraDeclarations = false

/-- **A rigid contact carries its surface by position.**  In the interacting
fibre, a term in which a program meets an environment is equivalent only to
terms in which an equivalent program meets an equivalent environment. -/
theorem InteractivePresentation.position_invariant
    {base : BasePremiseEvaluator} (presentation : InteractivePresentation)
    (rigid : presentation.RigidContact)
    {left right : presentation.Term} {program environment : Pattern}
    (contact : left.1 =
      .apply presentation.contactConstructor.1.label [program, environment])
    (equivalent : (presentedEquationSetoid base presentation).r left right) :
    ∃ program' environment',
      right.1 = .apply presentation.contactConstructor.1.label [program', environment'] ∧
        EquationEquiv base presentation.presentation.language program program' ∧
          EquationEquiv base presentation.presentation.language environment
            environment' := by
  have raw := equationEquiv_of_presentedEquationSetoid equivalent
  rw [contact] at raw
  exact equationEquiv_binary_of_headed rigid.1 rigid.2 raw

end Mettapedia.GSLT.LanguageDef
