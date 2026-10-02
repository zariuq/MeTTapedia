import Mettapedia.OSLF.Syntax.IntrinsicScopedJudgmentAction

/-!
# Free contextual substitution on event generators

An event generator is used through an arrow of the contextual judgment
category. Its arrow carries the ordinary-variable environment and the
endpoint equations. Reusing it after another substitution composes arrows;
no event occurrence is identified merely because its endpoints coincide.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (JudgmentAction)

universe v

variable {S : Signature}
variable (A : BindingCloneAlgebra.Algebra.{0} S)
variable (Seed : (sort : S.Srt) → State A sort → Type)

/-- An original event variable together with its substitution arrow to the
current contextual judgment. -/
structure Orbit {sort : S.Srt} (state : State A sort) where
  original : State A sort
  seed : Seed sort original
  arrow : original ⟶ state

/-- A generator starts at its own contextual judgment. -/
noncomputable def Orbit.unit {sort : S.Srt} {state : State A sort}
    (seed : Seed sort state) : Orbit A Seed state where
  original := state
  seed := seed
  arrow := 𝟙 state

/-- Ordinary-variable substitution composes with the recorded arrow. -/
noncomputable def Orbit.map {sort : S.Srt} {first second : State A sort}
    (event : Orbit A Seed first) (substitution : first ⟶ second) :
    Orbit A Seed second where
  original := event.original
  seed := event.seed
  arrow := event.arrow ≫ substitution

theorem Orbit.map_id {sort : S.Srt} {state : State A sort}
    (event : Orbit A Seed state) :
    event.map A Seed (𝟙 state) = event := by
  cases event with
  | mk original seed arrow =>
      change (Orbit.mk original seed (arrow ≫ 𝟙 state)) =
        Orbit.mk original seed arrow
      rw [Category.comp_id]

theorem Orbit.map_comp {sort : S.Srt}
    {first middle last : State A sort}
    (event : Orbit A Seed first)
    (one : first ⟶ middle) (two : middle ⟶ last) :
    (event.map A Seed one).map A Seed two =
      event.map A Seed (one ≫ two) := by
  cases event with
  | mk original seed arrow =>
      change (Orbit.mk original seed ((arrow ≫ one) ≫ two)) =
        Orbit.mk original seed (arrow ≫ (one ≫ two))
      rw [Category.assoc]

/-- Every substituted generator is the original generator followed by its
recorded contextual substitution arrow. -/
theorem Orbit.unit_map {sort : S.Srt} {state : State A sort}
    (event : Orbit A Seed state) :
    (Orbit.unit A Seed event.seed).map A Seed event.arrow = event := by
  cases event with
  | mk original seed arrow =>
      change Orbit.mk original seed (𝟙 original ≫ arrow) =
        Orbit.mk original seed arrow
      rw [Category.id_comp]

/-- Each fiber is the free covariant action on the chosen event generators. -/
noncomputable def freeAction (sort : S.Srt) : State A sort ⥤ Type where
  obj state := Orbit A Seed state
  map substitution := TypeCat.ofHom (fun event =>
    event.map A Seed substitution)
  map_id state := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact event.map_id A Seed
  map_comp one two := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact (event.map_comp A Seed one two).symm

/-- A substitution of one judgment gives the corresponding free action on
a retained event, including its individual generator identity. -/
noncomputable def Orbit.substitute {sort : S.Srt} {state : State A sort}
    (event : Orbit A Seed state)
    {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      A.substitution.Carrier state.context Δ) :
    Orbit A Seed (ofJudgment A (substJudgment (state.asJudgment A) σ)) :=
  event.map A Seed
    (substitutionArrow A (state.asJudgment A) σ)

/-- A substitution action interprets a generator use by acting on the
assigned original witness along the recorded arrow. -/
def Orbit.interpret (action : JudgmentAction.{0, v} A) {sort : S.Srt}
    (assigned : ∀ state : State A sort,
      Seed sort state → action.carrier (state.asJudgment A))
    {state : State A sort} (event : Orbit A Seed state) :
    action.carrier (state.asJudgment A) :=
  action.actArrow event.arrow (assigned event.original event.seed)

/-- Bare generators interpret as their assigned evidence, with no hidden
change of source, target, or event identity. -/
theorem Orbit.interpret_unit (action : JudgmentAction.{0, v} A) {sort : S.Srt}
    (assigned : ∀ state : State A sort,
      Seed sort state → action.carrier (state.asJudgment A))
    {state : State A sort} (seed : Seed sort state) :
    (Orbit.unit A Seed seed).interpret A Seed action assigned =
      assigned state seed :=
  action.actArrow_id state (assigned state seed)

/-- Interpreting an event generator after another contextual substitution
agrees with applying the substitution action. -/
theorem Orbit.interpret_map (action : JudgmentAction.{0, v} A) {sort : S.Srt}
    (assigned : ∀ state : State A sort,
      Seed sort state → action.carrier (state.asJudgment A))
    {first second : State A sort}
    (event : Orbit A Seed first) (f : first ⟶ second) :
    (event.map A Seed f).interpret A Seed action assigned =
      action.actArrow f (event.interpret A Seed action assigned) :=
  action.actArrow_comp event.arrow f (assigned event.original event.seed)

/-- Generator interpretation is a natural transformation from the free
substitution action to the target's action. -/
noncomputable def freeActionInterpretation (action : JudgmentAction.{0, 0} A)
    (sort : S.Srt)
    (assigned : ∀ state : State A sort,
      Seed sort state → action.carrier (state.asJudgment A)) :
    freeAction A Seed sort ⟶ action.functor sort where
  app state := TypeCat.ofHom (fun event =>
    event.interpret A Seed action assigned)
  naturality := by
    intro first second substitution
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact Orbit.interpret_map A Seed action assigned event substitution

/-- A natural interpretation of substituted event generators is determined
by its values on bare generators. -/
noncomputable def generatorAssignment (action : JudgmentAction.{0, 0} A)
    (sort : S.Srt) (η : freeAction A Seed sort ⟶ action.functor sort) :
    ∀ state : State A sort,
      Seed sort state → action.carrier (state.asJudgment A) :=
  fun state seed => η.app state (Orbit.unit A Seed seed)

/-- Extending an assignment and then reading its bare generators returns
that exact assignment. -/
theorem generatorAssignment_extend (action : JudgmentAction.{0, 0} A)
    (sort : S.Srt)
    (assigned : ∀ state : State A sort,
      Seed sort state → action.carrier (state.asJudgment A)) :
    generatorAssignment A Seed action sort
        (freeActionInterpretation A Seed action sort assigned) =
      assigned := by
  funext state seed
  exact Orbit.interpret_unit A Seed action assigned seed

/-- Naturality forces every substituted generator to use the substitution
action, so values on bare generators determine the map. -/
theorem freeActionInterpretation_generatorAssignment
    (action : JudgmentAction.{0, 0} A) (sort : S.Srt)
    (η : freeAction A Seed sort ⟶ action.functor sort) :
    freeActionInterpretation A Seed action sort
        (generatorAssignment A Seed action sort η) = η := by
  apply NatTrans.ext
  funext state
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext event
  change Orbit A Seed state at event
  change event.interpret A Seed action
      (generatorAssignment A Seed action sort η) = η.app state event
  have natural := η.naturality_apply event.arrow
    (Orbit.unit A Seed event.seed)
  change η.app state
      ((Orbit.unit A Seed event.seed).map A Seed event.arrow) =
    action.actArrow event.arrow
      (η.app event.original (Orbit.unit A Seed event.seed)) at natural
  rw [Orbit.unit_map] at natural
  exact natural.symm

/-- The free event action is characterized by arbitrary assignments of
bare generators to evidence of any substitution action. -/
noncomputable def freeActionUniversal (action : JudgmentAction.{0, 0} A)
    (sort : S.Srt) :
    (∀ state : State A sort,
        Seed sort state → action.carrier (state.asJudgment A)) ≃
      (freeAction A Seed sort ⟶ action.functor sort) where
  toFun := freeActionInterpretation A Seed action sort
  invFun := generatorAssignment A Seed action sort
  left_inv := generatorAssignment_extend A Seed action sort
  right_inv := freeActionInterpretation_generatorAssignment A Seed action sort

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
