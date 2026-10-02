import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Package
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RootReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment

/-!
# Church–Rosser for a constructor system extended by proposition codes

Let a rule package compute by a definition by constructor patterns (a
`ConstructorPresentation`), and extend it by a package of proposition codes
(`Codes.extend`). The decoder `holds` contributes three families of equations:

* `holds (imp p q) ⟶ Π (_ : holds p). holds q`;
* `holds (a f) ⟶ Π (x : A). holds (f x)`, for each quantifier instance `a`
  over a closed carrier `A`;
* `holds (e x y) ⟶ Id A x y`, for each equation instance `e` at a closed
  carrier `A`.

Every left side is linear, and every variable of a right side occurs on its
left. The code names are kept apart from the base (`Codes.Apart`) when the
decoder is not a defined constant of the base and does not occur in its left
sides, no code constructor is a defined constant, and no equation instance is
implication. Then the union of the two families is again a constructor system
(`Codes.extendSystem`): a base left side and a decoder left side are headed by
distinct defined constants, so no term instantiates both, and two decoder left
sides unify only when they are one equation. With β, the pair projections and
the base's symmetric universe-head equality, the extended package is therefore
Church–Rosser (`Codes.extend_churchRosser`), by the complete development of
`ConstructorSystemDevelopment`, and its conversion separates dependent
function types, dependent pairs and identity types componentwise.

The condition on implication cannot be dropped. When implication is also an
equation instance, the left sides `holds (imp p q)` and `holds (e x y)` unify,
the redex `holds (imp p q)` decodes both to a dependent function type and to
an identity type, and these have no common reduct
(`Codes.extend_not_churchRosser`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace ConstructorSystem

variable {Head : Type}

/-! ## Reduction from terms that no root step starts at -/

section Shapes

variable {rules : Rules Head}
  (spine : ∀ {n : Nat} {source target : Tm Head n}, rules.computation.step source target →
    ∃ name count, spineHead source = some (name, count))

include spine

/-- When every root step starts at a constant spine, reduction from a
dependent function type stays a dependent function type. -/
theorem stepStar_pi_of_spine {n : Nat} {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    {target : Tm Head n}
    (steps : ConversionCoherence.StepStar rules (.pi domain codomain) target) :
    ∃ domain' codomain', target = .pi domain' codomain' := by
  induction steps with
  | refl => exact ⟨_, _, rfl⟩
  | tail _ step ih =>
      obtain ⟨_, _, rfl⟩ := ih
      cases step with
      | root rootStep =>
          obtain ⟨_, _, shape⟩ := spine rootStep
          cases shape
      | congPiDom _ => exact ⟨_, _, rfl⟩
      | congPiCod _ => exact ⟨_, _, rfl⟩

/-- When every root step starts at a constant spine, reduction from an
identity type stays an identity type. -/
theorem stepStar_identity_of_spine {n : Nat} {carrier left right target : Tm Head n}
    (steps : ConversionCoherence.StepStar rules (.id carrier left right) target) :
    ∃ carrier' left' right', target = .id carrier' left' right' := by
  induction steps with
  | refl => exact ⟨_, _, _, rfl⟩
  | tail _ step ih =>
      obtain ⟨_, _, _, rfl⟩ := ih
      cases step with
      | root rootStep =>
          obtain ⟨_, _, shape⟩ := spine rootStep
          cases shape
      | congIdTy _ => exact ⟨_, _, _, rfl⟩
      | congIdLeft _ => exact ⟨_, _, _, rfl⟩
      | congIdRight _ => exact ⟨_, _, _, rfl⟩

end Shapes

end ConstructorSystem

namespace TypedEquality
namespace Impredicative

open AlgebraicSchema (SchemaFamily SchemaStep variableMultiplicity)
open AlgebraicParallel (SchemaPresentation)
open ConversionCoherence (ChurchRosser StepStar)
open ConstructorSystem (Pattern LeftSide System ConstructorPresentation spineHead unifiable
  determined_of_disjoint spineHead_subst_leftSide)
open Normalization (Decoders DecoderStep)

variable {Head : Type}

/-- A decoding step starts at the decoder applied to one argument. -/
theorem decoderStep_spineHead {D : Decoders Head} {n : Nat} {source target : Tm Head n}
    (step : DecoderStep D source target) : spineHead source = some (D.holds, 1) := by
  cases step <;> rfl

namespace Codes

/-! ## The decoding equations -/

section Equations

variable (K : Codes Head)

/-- `holds (imp p q)`, over `p q`. -/
def impLeft : Tm Head 2 := K.holdsOf (K.impOf (.var 0) (.var 1))

/-- `Π (_ : holds p). holds q`, over `p q`. -/
def impRight : Tm Head 2 := .pi (K.holdsOf (.var 0)) (K.holdsOf (.var 2))

/-- `holds (a f)`, over `f`. -/
def allLeft (a : DeclName) : Tm Head 1 := K.holdsOf (.app (.const a) (.var 0))

/-- `Π (x : A). holds (f x)`, over `f`. -/
def allRight (A : Tm Head 0) : Tm Head 1 :=
  .pi (liftClosed A) (K.holdsOf (.app (.var 1) (.var 0)))

/-- `holds (e x y)`, over `x y`. -/
def eqLeft (e : DeclName) : Tm Head 2 := K.holdsOf (.app (.app (.const e) (.var 0)) (.var 1))

end Equations

/-- `Id A x y`, over `x y`. -/
def eqRight (A : Tm Head 0) : Tm Head 2 := .id (liftClosed A) (.var 0) (.var 1)

/-- The decoding equations of a package of codes. -/
inductive DecoderSchema (K : Codes Head) : SchemaFamily Head
  | imp : DecoderSchema K K.impLeft K.impRight
  | all {a : DeclName} {A : Tm Head 0} :
      K.quantifiers a = some A → DecoderSchema K (K.allLeft a) (K.allRight A)
  | eq {e : DeclName} {A : Tm Head 0} :
      K.equationCarrier e = some A → DecoderSchema K (K.eqLeft e) (eqRight A)

section Decoding

variable (K : Codes Head)

theorem subst_allRight (A : Tm Head 0) {n : Nat} (σ : Sub Head 1 n) :
    subst σ (K.allRight A) =
      .pi (liftClosed A) (K.holdsOf (.app (rename wk (σ 0)) (.var 0))) := by
  simp only [allRight, subst, subst_liftClosed, holdsOf]
  rfl

theorem subst_eqRight (A : Tm Head 0) {n : Nat} (σ : Sub Head 2 n) :
    subst σ (eqRight A) = .id (liftClosed A) (σ 0) (σ 1) := by
  simp only [eqRight, subst, subst_liftClosed]

/-- Every instance of a decoding equation is a decoding step. -/
theorem decoderSchema_sound {m n : Nat} {left right : Tm Head m}
    (rule : K.DecoderSchema left right) (σ : Sub Head m n) :
    DecoderStep K.decoders (subst σ left) (subst σ right) := by
  cases rule with
  | imp => exact DecoderStep.imp (σ 0) (σ 1)
  | all carrier =>
      rw [subst_allRight]
      exact DecoderStep.all (D := K.decoders) carrier (σ 0)
  | eq carrier =>
      rw [subst_eqRight]
      exact DecoderStep.eq (D := K.decoders) carrier (σ 0) (σ 1)

/-- Every decoding step is an instance of a decoding equation. -/
theorem decoderStep_cover {n : Nat} {source target : Tm Head n}
    (step : DecoderStep K.decoders source target) :
    ∃ (m : Nat) (left right : Tm Head m) (σ : Sub Head m n),
      K.DecoderSchema left right ∧ subst σ left = source ∧ subst σ right = target := by
  cases step with
  | imp p q => exact ⟨2, _, _, ![p, q], .imp, rfl, rfl⟩
  | all carrier f =>
      exact ⟨1, _, _, ![f], .all carrier, rfl, by rw [subst_allRight]; rfl⟩
  | eq carrier x y =>
      exact ⟨2, _, _, ![x, y], .eq carrier, rfl, by rw [subst_eqRight]; rfl⟩

/-- Every variable of a decoding left side occurs exactly once. -/
theorem decoderSchema_multiplicity {m : Nat} {left right : Tm Head m}
    (rule : K.DecoderSchema left right) (index : Fin m) :
    variableMultiplicity index left = 1 := by
  cases rule with
  | imp =>
      match index with
      | 0 => rfl
      | 1 => rfl
  | all _ =>
      match index with
      | 0 => rfl
  | eq _ =>
      match index with
      | 0 => rfl
      | 1 => rfl

/-- A decoding left side is the decoder applied to one pattern, for every
choice of defined constants that leaves the code constructors undefined. -/
theorem decoderSchema_leftSide {defined : DeclName → Prop} (impFree : ¬ defined K.imp)
    (allFree : ∀ {a : DeclName} {A : Tm Head 0}, K.quantifiers a = some A → ¬ defined a)
    (eqFree : ∀ {e : DeclName} {A : Tm Head 0}, K.equationCarrier e = some A → ¬ defined e)
    {m : Nat} {left right : Tm Head m} (rule : K.DecoderSchema left right) :
    LeftSide defined left K.holds 1 := by
  cases rule with
  | imp => exact .app (.const _) (.app (.app (.const impFree) (.var 0)) (.var 1))
  | all carrier => exact .app (.const _) (.app (.const (allFree carrier)) (.var 0))
  | eq carrier =>
      exact .app (.const _) (.app (.app (.const (eqFree carrier)) (.var 0)) (.var 1))

/-- Two decoding equations whose left sides unify are the same equation, when
no equation instance is implication. -/
theorem decoderSchema_disjoint
    (eqNotImp : ∀ {e : DeclName} {A : Tm Head 0}, K.equationCarrier e = some A → e ≠ K.imp)
    {m m' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'}
    (rule : K.DecoderSchema left right) (rule' : K.DecoderSchema left' right')
    (meet : unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tm Head arity × Tm Head arity) =
      ⟨m', (left', right')⟩ := by
  cases rule with
  | imp =>
      cases rule' with
      | imp => rfl
      | all _ => simp [unifiable, impLeft, allLeft] at meet
      | eq carrier =>
          simp only [unifiable, impLeft, eqLeft, holdsOf, impOf, decide_true, Bool.true_and,
            Bool.and_true, decide_eq_true_eq] at meet
          exact absurd meet.symm (eqNotImp carrier)
  | all carrier =>
      cases rule' with
      | imp => simp [unifiable, impLeft, allLeft] at meet
      | all carrier' =>
          simp only [unifiable, allLeft, holdsOf, decide_true, Bool.true_and, Bool.and_true,
            decide_eq_true_eq] at meet
          subst meet
          rw [carrier] at carrier'
          cases carrier'
          rfl
      | eq _ => simp [unifiable, allLeft, eqLeft] at meet
  | eq carrier =>
      cases rule' with
      | imp =>
          simp only [unifiable, impLeft, eqLeft, holdsOf, impOf, decide_true, Bool.true_and,
            Bool.and_true, decide_eq_true_eq] at meet
          exact absurd meet (eqNotImp carrier)
      | all _ => simp [unifiable, allLeft, eqLeft] at meet
      | eq carrier' =>
          simp only [unifiable, eqLeft, holdsOf, decide_true, Bool.true_and, Bool.and_true,
            decide_eq_true_eq] at meet
          subst meet
          rw [carrier] at carrier'
          cases carrier'
          rfl

end Decoding

/-! ## The base's equations and the decoder's -/

/-- The equations of a base together with the decoding equations of a package
of codes. -/
inductive ExtendedSchema (schema : SchemaFamily Head) (K : Codes Head) : SchemaFamily Head
  | base {m : Nat} {left right : Tm Head m} : schema left right → ExtendedSchema schema K left right
  | decoder {m : Nat} {left right : Tm Head m} :
      K.DecoderSchema left right → ExtendedSchema schema K left right

theorem ExtendedSchema.map {K : Codes Head} {schema schema' : SchemaFamily Head}
    (f : ∀ {m : Nat} {left right : Tm Head m}, schema left right → schema' left right)
    {m : Nat} {left right : Tm Head m} :
    ExtendedSchema schema K left right → ExtendedSchema schema' K left right
  | .base rule => .base (f rule)
  | .decoder rule => .decoder rule

/-- The code names are kept apart from a constructor system: the decoder is
not a defined constant and does not occur in a left side, no code
constructor is a defined constant or the decoder, and no equation instance
is implication. -/
structure Apart (K : Codes Head) (system : System Head) : Prop where
  holds_undefined : ¬ system.defined K.holds
  holds_absent : ∀ {m : Nat} {left right : Tm Head m}, system.schema left right →
    ConstructorSystem.mentionsConst K.holds left = false
  imp_undefined : ¬ system.defined K.imp
  imp_ne_holds : K.imp ≠ K.holds
  all_apart : ∀ {a : DeclName} {A : Tm Head 0}, K.quantifiers a = some A →
    ¬ system.defined a ∧ a ≠ K.holds
  eq_apart : ∀ {e : DeclName} {A : Tm Head 0}, K.equationCarrier e = some A →
    ¬ system.defined e ∧ e ≠ K.holds ∧ e ≠ K.imp

section System

variable (K : Codes Head) (system : System Head)

/-- The defined constants of the extension: the base's and the decoder. -/
def extendDefined (c : DeclName) : Prop := system.defined c ∨ c = K.holds

/-- Their arities: the decoder takes one argument. -/
def extendArity (c : DeclName) : Nat := if c = K.holds then 1 else system.arity c

variable {K system}

/-- The decoding equations are determined when the names are apart. -/
theorem decoderSchema_determined (apart : K.Apart system) :
    ∀ {m m' n n' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'},
      K.DecoderSchema left right → K.DecoderSchema left' right' →
      ∀ (σ : Sub Head m n) (σ' : Sub Head m' n), subst σ left = subst σ' left' →
      ∀ (develop : Tm Head n → Tm Head n'),
        subst (fun index => develop (σ index)) right =
          subst (fun index => develop (σ' index)) right' :=
  determined_of_disjoint (defined := fun c => c = K.holds)
    (fun rule => ⟨K.holds, 1, K.decoderSchema_leftSide apart.imp_ne_holds
      (fun carrier => (apart.all_apart carrier).2) (fun carrier => (apart.eq_apart carrier).2.1)
      rule⟩)
    (fun rule index _ => by rw [K.decoderSchema_multiplicity rule index]; decide)
    (K.decoderSchema_disjoint fun carrier => (apart.eq_apart carrier).2.2)

/-- No term instantiates both a base left side and a decoding left side: they
are headed by distinct defined constants. -/
theorem base_decoder_disjoint (apart : K.Apart system) {m m' n : Nat}
    {left right : Tm Head m} {left' right' : Tm Head m'}
    (rule : system.schema left right) (rule' : K.DecoderSchema left' right')
    (σ : Sub Head m n) (σ' : Sub Head m' n) (same : subst σ left = subst σ' left') : False := by
  obtain ⟨name, defined, -, side⟩ := system.left rule
  have first := spineHead_subst_leftSide side σ
  have second := spineHead_subst_leftSide (K.decoderSchema_leftSide
    (defined := fun c => c = K.holds) apart.imp_ne_holds
    (fun carrier => (apart.all_apart carrier).2) (fun carrier => (apart.eq_apart carrier).2.1)
    rule') σ'
  rw [same, second] at first
  obtain ⟨headSame, -⟩ := Prod.mk.inj (Option.some.inj first)
  rw [← headSame] at defined
  exact apart.holds_undefined defined

theorem extend_left (apart : K.Apart system) {m : Nat} {left right : Tm Head m}
    (rule : ExtendedSchema system.schema K left right) :
    ∃ name, K.extendDefined system name ∧ 0 < K.extendArity system name ∧
      LeftSide (K.extendDefined system) left name (K.extendArity system name) := by
  cases rule with
  | base rule =>
      obtain ⟨name, defined, positive, side⟩ := system.left rule
      have distinct : name ≠ K.holds := fun same => apart.holds_undefined (same ▸ defined)
      have arity : K.extendArity system name = system.arity name := if_neg distinct
      refine ⟨name, .inl defined, by rw [arity]; exact positive, ?_⟩
      rw [arity]
      exact side.of_absent (apart.holds_absent rule)
  | decoder rule =>
      have arity : K.extendArity system K.holds = 1 := if_pos rfl
      refine ⟨K.holds, .inr rfl, by rw [arity]; decide, ?_⟩
      rw [arity]
      exact K.decoderSchema_leftSide
        (fun isDefined => isDefined.elim apart.imp_undefined apart.imp_ne_holds)
        (fun carrier isDefined =>
          isDefined.elim (apart.all_apart carrier).1 (apart.all_apart carrier).2)
        (fun carrier isDefined =>
          isDefined.elim (apart.eq_apart carrier).1 (apart.eq_apart carrier).2.1) rule

theorem extend_linear : AlgebraicSchema.LeftLinearFamily (ExtendedSchema system.schema K) := by
  intro m left right rule
  cases rule with
  | base rule => exact system.linear rule
  | decoder rule =>
      intro index
      rw [K.decoderSchema_multiplicity rule index]

theorem extend_covered {m : Nat} {left right : Tm Head m}
    (rule : ExtendedSchema system.schema K left right) :
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left := by
  cases rule with
  | base rule => exact system.covered rule
  | decoder rule =>
      intro index _
      rw [K.decoderSchema_multiplicity rule index]
      decide

theorem extend_determined (apart : K.Apart system) :
    ∀ {m m' n n' : Nat} {left right : Tm Head m} {left' right' : Tm Head m'},
      ExtendedSchema system.schema K left right → ExtendedSchema system.schema K left' right' →
      ∀ (σ : Sub Head m n) (σ' : Sub Head m' n), subst σ left = subst σ' left' →
      ∀ (develop : Tm Head n → Tm Head n'),
        subst (fun index => develop (σ index)) right =
          subst (fun index => develop (σ' index)) right' := by
  intro m m' n n' left right left' right' rule rule' σ σ' same develop
  cases rule with
  | base rule =>
      cases rule' with
      | base rule' => exact system.determined rule rule' σ σ' same develop
      | decoder rule' => exact (base_decoder_disjoint apart rule rule' σ σ' same).elim
  | decoder rule =>
      cases rule' with
      | base rule' => exact (base_decoder_disjoint apart rule' rule σ' σ same.symm).elim
      | decoder rule' => exact decoderSchema_determined apart rule rule' σ σ' same develop

variable (K)

/-- **The base's equations and the decoding equations form a constructor
system** when the code names are apart from the base. -/
def extendSystem (apart : K.Apart system) : System Head where
  schema := ExtendedSchema system.schema K
  defined := K.extendDefined system
  arity := K.extendArity system
  left := extend_left apart
  linear := extend_linear
  covered := extend_covered
  determined := extend_determined apart

end System

/-! ## The extended package -/

section Package

variable (K : Codes Head) {base : Rules Head}

/-- A presentation of the base extends to the package with codes: its
equations and the decoding equations. -/
def extendPresentation (presentation : SchemaPresentation base) :
    SchemaPresentation (K.extend base) where
  schema := ExtendedSchema presentation.schema K
  sound := fun rule σ => by
    cases rule with
    | base rule => exact .inl (presentation.sound rule σ)
    | decoder rule => exact .inr (K.decoderSchema_sound rule σ)
  cover := fun step => by
    rcases step with step | step
    · obtain ⟨arity, left, right, σ, rule, rfl, rfl⟩ := presentation.cover step
      exact ⟨arity, left, right, σ, .base rule, rfl, rfl⟩
    · obtain ⟨arity, left, right, σ, rule, rfl, rfl⟩ := K.decoderStep_cover step
      exact ⟨arity, left, right, σ, .decoder rule, rfl, rfl⟩

/-- **The package with codes as a definition by constructor patterns**, when
the base is one and the code names are apart from it. -/
def extendConstructors (equations : ConstructorPresentation base)
    (apart : K.Apart equations.system) : ConstructorPresentation (K.extend base) where
  presentation := K.extendPresentation equations.presentation
  system := K.extendSystem apart
  same := fun _ _ =>
    ⟨ExtendedSchema.map fun rule => (equations.same _ _).mp rule,
      ExtendedSchema.map fun rule => (equations.same _ _).mpr rule⟩
  symmetric := equations.symmetric

/-- **Church–Rosser for a constructor system extended by proposition codes**
whose names are apart from it. -/
theorem extend_churchRosser (equations : ConstructorPresentation base)
    (apart : K.Apart equations.system) : ChurchRosser (K.extend base) :=
  (K.extendConstructors equations apart).churchRosser

theorem extend_piConversionBoundary (equations : ConstructorPresentation base)
    (apart : K.Apart equations.system) : PiConversionBoundary (K.extend base) :=
  (K.extendConstructors equations apart).piConversionBoundary

theorem extend_sigmaConversionBoundary (equations : ConstructorPresentation base)
    (apart : K.Apart equations.system) : SigmaConversionBoundary (K.extend base) :=
  (K.extendConstructors equations apart).sigmaConversionBoundary

/-! ## When implication is an equation instance -/

/-- Every root step of a package presented by constructor patterns and
extended by codes starts at a constant spine, whatever the codes. -/
theorem extend_root_spineHead (equations : ConstructorPresentation base) {n : Nat}
    {source target : Tm Head n} (step : (K.extend base).computation.step source target) :
    ∃ name count, spineHead source = some (name, count) := by
  rcases step with step | step
  · exact equations.root_spineHead step
  · exact ⟨_, _, decoderStep_spineHead step⟩

/-- `holds (imp x y)` decodes as implication. -/
theorem decode_imp {n : Nat} (x y : Tm Head n) :
    StepCore (K.extend base).computation (K.extend base).headEq (K.holdsOf (K.impOf x y))
      (.pi (K.holdsOf x) (K.holdsOf (rename wk y))) :=
  .root (K.extend_decoder_step base (DecoderStep.imp (D := K.decoders) x y))

/-- When implication is also an equation instance at `A`, `holds (imp x y)`
decodes as an identity type too. -/
theorem decode_imp_as_equation {A : Tm Head 0} (overlap : K.equationCarrier K.imp = some A)
    {n : Nat} (x y : Tm Head n) :
    StepCore (K.extend base).computation (K.extend base).headEq (K.holdsOf (K.impOf x y))
      (.id (liftClosed A) x y) :=
  .root (K.extend_decoder_step base (DecoderStep.eq (D := K.decoders) overlap x y))

/-- **Without the condition on implication, Church–Rosser fails**: if
implication is also an equation instance, the two decodings of
`holds (imp x y)`, a dependent function type and an identity type, have no
common reduct. -/
theorem extend_not_churchRosser (equations : ConstructorPresentation base) {A : Tm Head 0}
    (overlap : K.equationCarrier K.imp = some A) : ¬ ChurchRosser (K.extend base) := by
  intro churchRosser
  obtain ⟨_, first, second⟩ := churchRosser (n := 2)
    (.trans _ _ _ (.symm _ _ (.rel _ _ (K.decode_imp (base := base) (.var 0) (.var 1))))
      (.rel _ _ (K.decode_imp_as_equation overlap (.var 0) (.var 1))))
  obtain ⟨_, _, rfl⟩ :=
    ConstructorSystem.stepStar_pi_of_spine (K.extend_root_spineHead equations) first
  obtain ⟨_, _, _, same⟩ :=
    ConstructorSystem.stepStar_identity_of_spine (K.extend_root_spineHead equations) second
  cases same

end Package

end Codes

end Impredicative
end TypedEquality

/-! ## Axiom audit -/

#print axioms ConstructorSystem.Pattern.of_absent
#print axioms ConstructorSystem.LeftSide.of_absent
#print axioms TypedEquality.Impredicative.Codes.decoderSchema_disjoint
#print axioms TypedEquality.Impredicative.Codes.extendSystem
#print axioms TypedEquality.Impredicative.Codes.extendConstructors
#print axioms TypedEquality.Impredicative.Codes.extend_churchRosser
#print axioms TypedEquality.Impredicative.Codes.extend_not_churchRosser

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
