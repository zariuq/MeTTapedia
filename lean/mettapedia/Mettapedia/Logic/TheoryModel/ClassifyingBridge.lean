import Mettapedia.Logic.TheoryModel.ArrowIdentification
import Mettapedia.OSLF.Syntax.CategoricalBindingGroupoid
import Mettapedia.OSLF.Syntax.EquationTransport
import Mettapedia.OSLF.Syntax.MonoidEquationRung

/-!
# Theories and models of a binding signature, through the classifying category

For a binding signature `S` and models in a category `D` with chosen finite
products and function objects, two satisfaction relations meet:

* sentence level: an equation between two terms at a metavariable stage is
  satisfied by a model when the model interprets both sides alike;
* arrow level: a pair of parallel arrows of the second-order context category
  `Object S` is satisfied by a functor when the functor identifies them.

The classifying construction sends a model to its classifying functor and an
equation to its pair of term arrows. It preserves and reflects satisfaction,
so the models of a set of equations are the preimage of the models of their
term arrows, and dually for theories.

For an equation presentation `P`:

* `satisfying P` is the model class of the instances of the axioms of `P`, and
  equally of all equations derivable from them;
* derivable equations are exactly the equations whose term arrows are related
  by `P.homRel`, and `respecting P` is the model class of `P.homRel` in the
  arrow polarity;
* a model satisfies `P` exactly when its classifying functor is a model of
  `P.homRel`, and `satisfyingEquivalence P` is the restriction of the
  classifying construction to these two classes;
* enlarging `P.homRel` shrinks both classes, the square of inclusions commutes
  with `satisfyingEquivalence` on the nose, and the equation-class context
  category of `P` maps to that of the larger presentation, compatibly with the
  quotient functors;
* the presentation with no equations derives only syntactic identities, is
  refined by every presentation, and every model satisfies it;
* over all functors into categories of the universe of `Object S`, `P.homRel`
  is a closed theory and the quotient functor hosts it faithfully. Faithful
  hosting by the structure-preserving functors into one fixed `D` is a
  completeness statement for the models in `D`, which is a separate question.

Controls over the monoid signature: commutativity of two variables is not
derivable from no equations, is derivable once it is an axiom, and its term
arrows are related by the commutative presentation only.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.Classifying

open CategoryTheory CategoryTheory.CartesianMonoidalCategory Set Order
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext (Object EquationPresentation EquationContexts)
open Mettapedia.Logic.TheoryModel.ParallelArrows

universe u v

variable {S : Signature}

/-! ## Sentences: equations at a metavariable stage -/

/-- An equation between two terms at a metavariable stage. -/
structure Equation (S : Signature) where
  stage : Object S
  ctx : Ctx S
  sort : S.Srt
  lhs : Term (withMetas S stage.arities) ctx sort
  rhs : Term (withMetas S stage.arities) ctx sort

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]

/-- A model satisfies an equation when it interprets both sides alike. -/
def EqSat (M : Model S D) (e : Equation S) : Prop :=
  M.interp e.stage.arities e.lhs = M.interp e.stage.arities e.rhs

/-- The pair of term arrows of an equation. -/
def termPair (e : Equation S) : ParallelArrows (Object S) :=
  ⟨e.stage, oneObj e.ctx e.sort, termArrow e.lhs, termArrow e.rhs⟩

/-- The classifying functor of a model, as a structure of the arrow polarity. -/
def classifyingStructure (M : Model S D) : Σ E : Cat.{v, u}, Object S ⥤ E :=
  ⟨Cat.of D, M.classifyingFunctor⟩

/-- **A model satisfies an equation exactly when its classifying functor
identifies the term arrows of the equation.** -/
theorem eqSat_iff_identifies (M : Model S D) (e : Equation S) :
    EqSat M e ↔ Identifies (classifyingStructure M) (termPair e) := by
  change _ ↔ M.assignHom (termArrow e.lhs) = M.assignHom (termArrow e.rhs)
  rw [M.assignHom_termArrow, M.assignHom_termArrow]
  constructor
  · intro equal
    unfold Model.generic
    unfold EqSat at equal
    rw [equal]
  · intro equal
    have curried := congrArg (fun m => m ≫ fst _ _) equal
    rw [lift_fst, lift_fst] at curried
    have generic := congrArg M.uncurry curried
    rw [M.uncurry_curry, M.uncurry_curry] at generic
    exact Preserving.elem_eq_of_generic generic

/-- Models of a set of equations are the models whose classifying functors
identify the term arrows of the equations. -/
theorem models_eqSat_eq_preimage (T : Set (Equation S)) :
    models (EqSat (D := D)) T = classifyingStructure ⁻¹' models Identifies (termPair '' T) :=
  models_eq_preimage classifyingStructure termPair eqSat_iff_identifies T

/-- The equational theory of a class of models is the preimage of the kernel of
their classifying functors. -/
theorem theoryOf_eqSat_eq_preimage (K : Set (Model S D)) :
    theoryOf EqSat K = termPair ⁻¹' theoryOf Identifies (classifyingStructure '' K) :=
  theoryOf_eq_preimage classifyingStructure termPair eqSat_iff_identifies K

/-! ## Equation presentations -/

section Presentation

variable {schema : List (MetaArity S)} (P : EquationPresentation S schema)

/-- One instance of one axiom of the presentation: bodies for the schema
metavariables over an ambient context `Θ`, a substitution for that ambient
context, and a substitution for the variables of the axiom, both into `Δ`. -/
def instanceOf (X : Object S) (i : Fin (P.axioms X).length) {Θ Δ : Ctx S}
    (body : ContextualAssignment (withMetas S X.arities) schema Θ)
    (ambient : Sub (withMetas S X.arities) Θ Δ)
    (ordinary : Sub (withMetas S X.arities) ((P.axioms X).get i).ctx Δ) : Equation S :=
  ⟨X, Δ, ((P.axioms X).get i).sort,
    ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).lhs,
    ContextualAssignment.instantiate body ambient ordinary ((P.axioms X).get i).rhs⟩

/-- All instances of the axioms of the presentation, at every stage. -/
def instances : Set (Equation S) :=
  {e | ∃ X i, ∃ (Θ Δ : Ctx S) (body : ContextualAssignment (withMetas S X.arities) schema Θ)
    (ambient : Sub (withMetas S X.arities) Θ Δ)
    (ordinary : Sub (withMetas S X.arities) ((P.axioms X).get i).ctx Δ),
      instanceOf P X i body ambient ordinary = e}

/-- The equations derivable from the presentation at their own stage. -/
def derivable : Set (Equation S) :=
  {e | EqClosure (P.axioms e.stage) e.lhs e.rhs}

variable {P}

/-- A model satisfies the presentation exactly when it is a model of its
instances. -/
theorem satisfies_iff_mem_models (M : Model S D) :
    M.Satisfies P ↔ M ∈ models EqSat (instances P) :=
  ⟨fun sat _ ⟨X, i, _, _, body, ambient, ordinary, equal⟩ =>
      equal ▸ sat X i body ambient ordinary,
    fun model X i _ _ body ambient ordinary =>
      model ⟨X, i, _, _, body, ambient, ordinary, rfl⟩⟩

theorem instances_subset_derivable : instances P ⊆ derivable P := by
  rintro _ ⟨X, i, _, _, body, ambient, ordinary, rfl⟩
  exact EqClosure.ax (E := P.axioms X) i body ambient ordinary

/-- **Soundness**: every derivable equation is a consequence of the
instances. -/
theorem derivable_subset_consequences :
    derivable P ⊆ theoryOf (EqSat (D := D)) (models EqSat (instances P)) :=
  fun _ derivation M model =>
    M.interp_eqClosure ((satisfies_iff_mem_models M).mpr model _) derivation

/-- The instances and the derivable equations have the same models. -/
theorem models_derivable :
    models (EqSat (D := D)) (derivable P) = models EqSat (instances P) :=
  Subset.antisymm (models_anti instances_subset_derivable)
    fun _ model _ derivation => derivable_subset_consequences derivation model

/-- A derivable equation is exactly a pair of term arrows related by the
presentation. -/
theorem mem_derivable_iff_homRel (e : Equation S) :
    e ∈ derivable P ↔ P.homRel (termArrow e.lhs) (termArrow e.rhs) := by
  constructor
  · intro derivation index
    obtain ⟨n, bound⟩ := index
    obtain rfl : n = 0 := Nat.lt_one_iff.mp bound
    exact derivation
  · intro related
    exact related ⟨0, Nat.zero_lt_one⟩

theorem termPair_mem_ofHomRel_iff (e : Equation S) :
    termPair e ∈ ofHomRel P.homRel ↔ e ∈ derivable P :=
  (mem_derivable_iff_homRel e).symm

/-- Respecting the presentation is being a model of `P.homRel` in the arrow
polarity. -/
theorem respecting_iff_mem_models
    (F : (preservingFunctors (S := S) (D := D)).FullSubcategory) :
    respecting P F ↔
      (⟨Cat.of D, F.obj.of⟩ : Σ E : Cat.{v, u}, Object S ⥤ E) ∈
        models Identifies (ofHomRel P.homRel) :=
  ⟨fun respects _ related => respects related,
    fun model _ _ _ _ related => model (show (⟨_, _, _, _⟩ : ParallelArrows (Object S)) ∈
      ofHomRel P.homRel from related)⟩

/-- **The model class of the presentation, three ways.** -/
theorem satisfying_iff (M : Core (Model S D)) :
    (satisfying P M ↔ M.of ∈ models EqSat (instances P)) ∧
      (satisfying P M ↔ M.of ∈ models EqSat (derivable P)) ∧
      (satisfying P M ↔ classifyingStructure M.of ∈ models Identifies (ofHomRel P.homRel)) := by
  refine ⟨satisfies_iff_mem_models M.of, ?_, ?_⟩
  · rw [models_derivable]
    exact satisfies_iff_mem_models M.of
  · rw [← respecting_classifying_iff P M]
    exact respecting_iff_mem_models (classifying.obj M)

/-- `satisfyingEquivalence P` is the classifying construction restricted to the
model class of the presentation. -/
theorem satisfyingEquivalence_functor_obj (M : (satisfying (S := S) (D := D) P).FullSubcategory) :
    ((satisfyingEquivalence P).functor.obj M).obj = classifying.obj M.obj :=
  rfl

theorem classifying_obj_of (M : Core (Model S D)) :
    (classifying.obj M).obj.of = M.of.classifyingFunctor :=
  rfl

/-- Every classifying functor of a model of `P` identifies the arrows related
by `P.homRel`: `P.homRel` is sound for the models in `D`. -/
theorem ofHomRel_subset_kernel :
    ofHomRel P.homRel ⊆
      theoryOf Identifies (classifyingStructure '' {M : Model S D | M.Satisfies P}) := by
  rintro p related _ ⟨M, sat, rfl⟩
  exact M.assignHom_congr P sat related

end Presentation

/-! ## Adding equations -/

section Refinement

variable {schema schema' : List (MetaArity S)}
  {P : EquationPresentation S schema} {P' : EquationPresentation S schema'}

/-- `P'` identifies every pair of assignments that `P` identifies. -/
def Refines (P : EquationPresentation S schema) (P' : EquationPresentation S schema') : Prop :=
  ∀ ⦃X Y : Object S⦄ ⦃σ τ : X ⟶ Y⦄, P.homRel σ τ → P'.homRel σ τ

theorem respecting_anti (refines : Refines P P') :
    respecting (S := S) (D := D) P' ≤ respecting P :=
  fun _ respects _ _ _ _ related => respects (refines related)

/-- **Adding equations shrinks the model class.** -/
theorem satisfying_anti (refines : Refines P P') :
    satisfying (S := S) (D := D) P' ≤ satisfying P := fun M sat =>
  (respecting_classifying_iff P M).mp
    (respecting_anti refines _ ((respecting_classifying_iff P' M).mpr sat))

/-- The inclusions of model classes commute with the classifying
equivalences. -/
theorem satisfyingEquivalence_comp_ιOfLE (refines : Refines P P') :
    (satisfyingEquivalence (D := D) P').functor ⋙
        ObjectProperty.ιOfLE (respecting_anti (D := D) refines) =
      ObjectProperty.ιOfLE (satisfying_anti (D := D) refines) ⋙
        (satisfyingEquivalence (D := D) P).functor :=
  rfl

/-- Adding equations refines the equation-class context category. -/
def refineQuotient (refines : Refines P P') : EquationContexts P ⥤ EquationContexts P' :=
  CategoryTheory.Quotient.lift P.homRel P'.quotientFunctor
    fun _ _ _ _ related => CategoryTheory.Quotient.sound P'.homRel (refines related)

theorem quotientFunctor_comp_refineQuotient (refines : Refines P P') :
    P.quotientFunctor ⋙ refineQuotient refines = P'.quotientFunctor :=
  rfl

end Refinement

/-! ## The presentation among all functors -/

section AllFunctors

variable {schema : List (MetaArity S)} (P : EquationPresentation S schema)

/-- Over all functors into categories of the universe of `Object S`, the
arrow theory of a presentation is closed: its consequences are itself. -/
theorem ofHomRel_isIntent :
    IsIntent (IdentifiesIn (Object S))
      (ofHomRel P.homRel) :=
  isIntent_identifies_iff.mpr (EquationPresentation.congruence P)

/-- The quotient functor hosts the arrow theory of the presentation
faithfully. -/
theorem hostsFaithfully_quotient :
    HostsFaithfully
      (IdentifiesIn (Object S))
      {quotientModel (ofHomRel P.homRel)} (ofHomRel P.homRel) :=
  hostsFaithfully_quotientModel _

/-- The functor of that structure is the quotient functor onto the
equation-class context category. -/
theorem quotientModel_functor :
    (quotientModel (ofHomRel P.homRel)).2 = P.quotientFunctor :=
  rfl

end AllFunctors

/-! ## The empty presentation -/

section Empty

/-- The presentation with no equations. -/
def emptyPresentation (S : Signature) : EquationPresentation S [] :=
  SecondOrderContext.baseEquationPresentation []

/-- Nothing but syntactic identity is derivable from no equations. -/
theorem mem_derivable_emptyPresentation_iff (e : Equation S) :
    e ∈ derivable (emptyPresentation S) ↔ e.lhs = e.rhs := by
  constructor
  · intro derivation
    exact eqClosure_empty_eq derivation
  · intro equal
    change EqClosure _ e.lhs e.rhs
    rw [← equal]
    exact EqClosure.refl _

/-- Every presentation refines the empty one. -/
theorem refines_emptyPresentation {schema : List (MetaArity S)}
    (P : EquationPresentation S schema) : Refines (emptyPresentation S) P := by
  intro X Y σ τ related
  have equal : σ = τ := funext fun index => eqClosure_empty_eq (related index)
  subst equal
  exact (EquationPresentation.congruence P).equivalence.refl σ

/-- Every model satisfies the empty presentation. -/
theorem satisfies_emptyPresentation (M : Model S D) : M.Satisfies (emptyPresentation S) :=
  fun _ i => Fin.elim0 i

/-- **The empty presentation has the largest model class**: every model, and
every presentation's class lies inside it. -/
theorem satisfying_le_emptyPresentation {schema : List (MetaArity S)}
    (P : EquationPresentation S schema) :
    satisfying (D := D) P ≤ satisfying (emptyPresentation S) ∧
      ∀ M : Core (Model S D), satisfying (emptyPresentation S) M :=
  ⟨satisfying_anti (refines_emptyPresentation P), fun M => satisfies_emptyPresentation M.of⟩

end Empty

/-! ## Controls: commutativity over the monoid signature -/

namespace Control

open Mettapedia.OSLF.Binding.MonoidEquationRung
open Mettapedia.OSLF.Binding.SecondOrderContext (BaseEquation baseEquationPresentation)

/-- The empty metavariable stage. -/
abbrev stage : Object sig := ⟨[]⟩

/-- The product of two variables, at the empty stage. -/
def product (first second : Var [Srt.element, Srt.element] Srt.element) :
    Term (withMetas sig stage.arities) [Srt.element, Srt.element] Srt.element :=
  embed (M := stage.arities) (mulT (.var first) (.var second))

/-- Commutativity of two variables. -/
def commutativity : Equation sig :=
  ⟨stage, [.element, .element], .element, product .zero (.succ .zero),
    product (.succ .zero) .zero⟩

/-- Negative control: commutativity is not derivable from no equations. -/
theorem commutativity_not_derivable : commutativity ∉ derivable (emptyPresentation sig) := by
  intro derivation
  have equal := (mem_derivable_emptyPresentation_iff commutativity).mp derivation
  cases equal

/-- Positive control: reflexivity is derivable from no equations. -/
theorem reflexivity_derivable :
    (⟨stage, [.element, .element], .element, product .zero (.succ .zero),
      product .zero (.succ .zero)⟩ : Equation sig) ∈ derivable (emptyPresentation sig) :=
  (mem_derivable_emptyPresentation_iff _).mpr rfl

/-- The commutativity axiom of the monoid signature. -/
def commEquation : BaseEquation sig :=
  ⟨[.element, .element], .element, mulT (.var .zero) (.var (.succ .zero)),
    mulT (.var (.succ .zero)) (.var .zero)⟩

/-- The presentation with commutativity as its only axiom. -/
def commPresentation : EquationPresentation sig [] :=
  baseEquationPresentation [commEquation]

/-- Positive control: commutativity is derivable once it is an axiom. -/
theorem commutativity_derivable : commutativity ∈ derivable commPresentation := by
  have generated := EqClosure.ax_closed (commPresentation.axioms stage)
    ⟨0, Nat.zero_lt_one⟩ (fun i => Fin.elim0 i) (fun _ v => Term.var v)
  rw [bind_id, bind_id] at generated
  exact generated

/-- **The identification of the two products is related by the commutative
presentation and not by the empty one**; adding it shrinks the model class. -/
theorem commutativity_termPair :
    termPair commutativity ∈ ofHomRel commPresentation.homRel ∧
      termPair commutativity ∉ ofHomRel (emptyPresentation sig).homRel ∧
      satisfying (D := D) commPresentation ≤ satisfying (emptyPresentation sig) :=
  ⟨(termPair_mem_ofHomRel_iff commutativity).mpr commutativity_derivable,
    fun related =>
      commutativity_not_derivable ((termPair_mem_ofHomRel_iff commutativity).mp related),
    (satisfying_le_emptyPresentation commPresentation).1⟩

end Control

end Mettapedia.Logic.TheoryModel.Classifying
