import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalJudgmentCategory
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalSubstitutionModels

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

/-- A target substitution model interprets a generator use by applying its
actual evidence action to the assigned original witness. -/
def Orbit.interpret
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A)
    {sort : S.Srt}
    (assigned : ∀ state : State A sort,
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    {state : State A sort} (event : Orbit A Seed state) :
    model.evidence.carrier () (state.asJudgment A) :=
  model.act (event.original.asJudgment A)
    (assigned event.original event.seed)
    event.arrow.environment (state.asJudgment A)
    (Map.as_substitution A event.arrow)

/-- Bare generators interpret as their assigned evidence, with no hidden
change of source, target, or event identity. -/
theorem Orbit.interpret_unit
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A)
    {sort : S.Srt}
    (assigned : ∀ state : State A sort,
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    {state : State A sort}
    (seed : Seed sort state) :
    (Orbit.unit A Seed seed).interpret A Seed model assigned =
      assigned state seed := by
  change model.act (state.asJudgment A) (assigned state seed)
      (fun _ var => A.substitution.injectVar var)
      (state.asJudgment A) _ = assigned state seed
  exact model.act_identity (state.asJudgment A)
    (assigned state seed) _

/-- Interpreting an event generator after another contextual substitution
agrees with applying the target model's actual substitution action. -/
theorem Orbit.interpret_map
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A)
    {sort : S.Srt}
    (assigned : ∀ state : State A sort,
      Seed sort state → model.evidence.carrier () (state.asJudgment A))
    {first second : State A sort}
    (event : Orbit A Seed first) (f : first ⟶ second) :
    (event.map A Seed f).interpret A Seed model assigned =
      model.act (first.asJudgment A)
        (event.interpret A Seed model assigned)
        f.environment (second.asJudgment A)
        (Map.as_substitution A f) := by
  let j₀ := event.original.asJudgment A
  let j₁ := first.asJudgment A
  let j₂ := second.asJudgment A
  let σ := event.arrow.environment
  let τ := f.environment
  let τ₀ := castEnv (Map.as_substitution A event.arrow) τ
  let ρ := fun s v => A.substitution.substitute τ₀ (σ s v)
  let w := assigned event.original event.seed
  have h₁ : substJudgment j₀ σ = j₁ :=
    Map.as_substitution A event.arrow
  have h₂ : substJudgment j₁ τ = j₂ := Map.as_substitution A f
  have hSecond : substJudgment (substJudgment j₀ σ) τ₀ = j₂ :=
    (substJudgment_castEnv h₁ τ).trans h₂
  have hDirect : substJudgment j₀ ρ = j₂ :=
    (substJudgment_comp j₀ σ τ₀).symm.trans hSecond
  have envEq : τ₀ = τ := eq_of_heq (castEnv_heq h₁ τ)
  have compEnvEq : ρ = (event.arrow ≫ f).environment := by
    funext s v
    exact congrArg (fun env => A.substitution.substitute env (σ s v)) envEq
  have directToComposite : HEq
      (model.act j₀ w ρ j₂ hDirect)
      (model.act j₀ w (event.arrow ≫ f).environment j₂
        (Map.as_substitution A (event.arrow ≫ f))) :=
    SubstitutionModel.act_heq R model rfl HEq.rfl
      (heq_of_eq compEnvEq) rfl hDirect
      (Map.as_substitution A (event.arrow ≫ f))
  have innerToChosen : HEq
      (model.act j₀ w σ (substJudgment j₀ σ) rfl)
      (model.act j₀ w σ j₁ h₁) :=
    SubstitutionModel.act_heq R model rfl HEq.rfl HEq.rfl
      h₁ rfl h₁
  have twiceToSemantic : HEq
      (model.act (substJudgment j₀ σ)
        (model.act j₀ w σ (substJudgment j₀ σ) rfl)
        τ₀ j₂ hSecond)
      (model.act j₁ (model.act j₀ w σ j₁ h₁) τ j₂ h₂) :=
    SubstitutionModel.act_heq R model h₁ innerToChosen
      (castEnv_heq h₁ τ) rfl hSecond h₂
  have compLaw := model.act_comp j₀ w σ τ₀ j₂ hSecond hDirect
  exact eq_of_heq
    (directToComposite.symm.trans
      ((heq_of_eq compLaw.symm).trans twiceToSemantic))

/-- The target model's evidence action composes along the contextual
judgment category, including its endpoint proof transports. -/
theorem model_act_comp_map
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A)
    {sort : S.Srt} {first middle last : State A sort}
    (one : first ⟶ middle) (two : middle ⟶ last)
    (value : model.evidence.carrier () (first.asJudgment A)) :
    model.act (first.asJudgment A) value
        (one ≫ two).environment (last.asJudgment A)
        (Map.as_substitution A (one ≫ two)) =
      model.act (middle.asJudgment A)
        (model.act (first.asJudgment A) value one.environment
          (middle.asJudgment A) (Map.as_substitution A one))
        two.environment (last.asJudgment A)
        (Map.as_substitution A two) := by
  let Seeds : (s : S.Srt) → State A s → Type :=
    fun _ state => model.evidence.carrier () (state.asJudgment A)
  let assigned : ∀ state : State A sort,
      Seeds sort state → model.evidence.carrier () (state.asJudgment A) :=
    fun _ evidence => evidence
  let event : Orbit A Seeds first := Orbit.unit A Seeds value
  have unitEq : event.interpret A Seeds model assigned = value :=
    Orbit.interpret_unit A Seeds model assigned value
  have oneEq := Orbit.interpret_map A Seeds model assigned event one
  have twoEq := Orbit.interpret_map A Seeds model assigned
    (event.map A Seeds one) two
  have joinedEq := Orbit.interpret_map A Seeds model assigned event
    (one ≫ two)
  calc
    model.act (first.asJudgment A) value
        (one ≫ two).environment (last.asJudgment A)
        (Map.as_substitution A (one ≫ two)) =
      (event.map A Seeds (one ≫ two)).interpret A Seeds model assigned := by
        rw [joinedEq, unitEq]
    _ = ((event.map A Seeds one).map A Seeds two).interpret
        A Seeds model assigned := by
          rw [event.map_comp A Seeds one two]
    _ = model.act (middle.asJudgment A)
        ((event.map A Seeds one).interpret A Seeds model assigned)
        two.environment (last.asJudgment A)
        (Map.as_substitution A two) := twoEq
    _ = model.act (middle.asJudgment A)
        (model.act (first.asJudgment A) value one.environment
          (middle.asJudgment A) (Map.as_substitution A one))
        two.environment (last.asJudgment A)
        (Map.as_substitution A two) := by rw [oneEq, unitEq]

/-- The actual evidence action of any substitution-operational model is a
functor on contextual endpoint judgments of each sort. -/
noncomputable def modelAction
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A) (sort : S.Srt) :
    State A sort ⥤ Type where
  obj state := model.evidence.carrier () (state.asJudgment A)
  map substitution := TypeCat.ofHom (fun evidence =>
    model.act _ evidence substitution.environment _
      (Map.as_substitution A substitution))
  map_id state := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext evidence
    exact model.act_identity (state.asJudgment A) evidence
      (Map.as_substitution A (𝟙 state))
  map_comp one two := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext evidence
    exact model_act_comp_map A model one two evidence

/-- Generator interpretation is a natural transformation from the free
substitution action to the target model's actual event action. -/
noncomputable def freeActionInterpretation
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A)
    (sort : S.Srt)
    (assigned : ∀ state : State A sort,
      Seed sort state → model.evidence.carrier () (state.asJudgment A)) :
    freeAction A Seed sort ⟶ modelAction A model sort where
  app state := TypeCat.ofHom (fun event =>
    event.interpret A Seed model assigned)
  naturality := by
    intro first second substitution
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact Orbit.interpret_map A Seed model assigned event substitution

/-- A natural interpretation of substituted event generators is determined
by its values on bare generators. -/
noncomputable def generatorAssignment
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A) (sort : S.Srt)
    (η : freeAction A Seed sort ⟶ modelAction A model sort) :
    ∀ state : State A sort,
      Seed sort state → model.evidence.carrier () (state.asJudgment A) :=
  fun state seed => η.app state (Orbit.unit A Seed seed)

/-- Extending an assignment and then reading its bare generators returns
that exact assignment. -/
theorem generatorAssignment_extend
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A)
    (sort : S.Srt)
    (assigned : ∀ state : State A sort,
      Seed sort state → model.evidence.carrier () (state.asJudgment A)) :
    generatorAssignment A Seed model sort
        (freeActionInterpretation A Seed model sort assigned) =
      assigned := by
  funext state seed
  exact Orbit.interpret_unit A Seed model assigned seed

/-- Naturality forces every substituted generator to use the model's
substitution action, so values on bare generators determine the map. -/
theorem freeActionInterpretation_generatorAssignment
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A)
    (sort : S.Srt)
    (η : freeAction A Seed sort ⟶ modelAction A model sort) :
    freeActionInterpretation A Seed model sort
        (generatorAssignment A Seed model sort η) = η := by
  apply NatTrans.ext
  funext state
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext event
  change Orbit A Seed state at event
  change event.interpret A Seed model
      (generatorAssignment A Seed model sort η) = η.app state event
  have natural := η.naturality_apply event.arrow
    (Orbit.unit A Seed event.seed)
  change η.app state
      ((Orbit.unit A Seed event.seed).map A Seed event.arrow) =
    model.act (event.original.asJudgment A)
      (η.app event.original (Orbit.unit A Seed event.seed))
      event.arrow.environment (state.asJudgment A)
      (Map.as_substitution A event.arrow) at natural
  rw [Orbit.unit_map] at natural
  exact natural.symm

/-- The free event action is characterized by arbitrary assignments of
bare generators to evidence in any substitution-operational model. -/
noncomputable def freeActionUniversal
    {M : List (MetaArity S)}
    {R : List (IntrinsicScopedConditionalPolynomial.Rule S M)}
    (model : SubstitutionModel R A) (sort : S.Srt) :
    (∀ state : State A sort,
        Seed sort state → model.evidence.carrier () (state.asJudgment A)) ≃
      (freeAction A Seed sort ⟶ modelAction A model sort) where
  toFun := freeActionInterpretation A Seed model sort
  invFun := generatorAssignment A Seed model sort
  left_inv := generatorAssignment_extend A Seed model sort
  right_inv := freeActionInterpretation_generatorAssignment A Seed model sort

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
