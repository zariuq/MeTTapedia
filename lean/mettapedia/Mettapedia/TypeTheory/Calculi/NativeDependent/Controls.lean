import Mettapedia.TypeTheory.Calculi.NativeDependent.PresheafInterpretation
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Dependent computation and declaration-retention controls

The object presheaf is Nat, and the atomic witness at object n has type
Fin (n + 1). The atomic family varies with the actual binder input. A
native abstraction computes that input inside the dependent witness type;
a sum retains both its supplied object and that witness. Two authored
primitive declarations with the same semantic value remain different
proof trees, marking the boundary of a value-only interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Controls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafPi
open Mettapedia.TypeTheory.DisplayedPresheafSigma
open ObjectInterpretation PresheafInterpretation

abbrev World := Discrete PUnit

abbrev objects : Worldᵒᵖ ⥤ Type := (Functor.const Worldᵒᵖ).obj Nat

def constants (name : Nat) : objects.sections where
  val _ := name
  property _ := rfl

def objectValue (point : objects.Elements) : Nat := point.2

/-- The second coordinate is genuinely indexed by the observed number. -/
def bounded : DisplayedFamily objects where
  obj point := Fin (objectValue point + 1)
  map arrow := TypeCat.ofHom fun value =>
    cast (congrArg (fun n : Nat => Fin (n + 1)) arrow.property) value
  map_id point := by ext value; rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    change cast _ value = cast _ (cast _ value)
    exact (cast_cast _ _ value).symm

abbrev predicates (_name : PUnit) : DisplayedFamily objects := bounded

abbrev input : Formula Nat PUnit 1 := .atom PUnit.unit (.var 0)

/-- Each primitive has an independently specified scoped judgment. -/
inductive Primitive : (n : Nat) → Formula Nat PUnit n → Type where
  | boundedInput : Primitive 1 input
  | closed (n : Nat) (origin : Bool) :
      Primitive 0 (.substitute input (ObjectSubstitution.instantiate (.constant n)))

def inputValue (point : (context objects 1).Elements) : Nat := point.2.2

private theorem maximal_cast {first second : Nat} (same : first = second) :
    cast (congrArg (fun number : Nat => Fin (number + 1)) same)
      (⟨first, Nat.lt_succ_self _⟩ : Fin (first + 1)) =
        (⟨second, Nat.lt_succ_self _⟩ : Fin (second + 1)) := by
  cases same
  rfl

def inputSection : (family objects constants predicates input).sections where
  val point := by
    change Fin (inputValue point + 1)
    exact ⟨point.2.2, Nat.lt_succ_self _⟩
  property := by
    intro source target arrow
    have objectsAgree : source.2.2 = target.2.2 := congrArg Sigma.snd arrow.property
    change cast _ (⟨source.2.2, Nat.lt_succ_self _⟩ : Fin (inputValue source + 1)) =
      (⟨target.2.2, Nat.lt_succ_self _⟩ : Fin (inputValue target + 1))
    exact maximal_cast objectsAgree

noncomputable def declarations : ∀ {n : Nat} {formula : Formula Nat PUnit n},
    Primitive n formula → (family objects constants predicates formula).sections
  | _, _, .boundedInput => inputSection
  | _, _, .closed number _ =>
      reindexDisplayedSection (substitution objects constants
        (ObjectSubstitution.instantiate (.constant number)))
          (family objects constants predicates input) inputSection

def testPoint : (context objects 0).Elements := ⟨Opposite.op (Discrete.mk PUnit.unit), PUnit.unit⟩

abbrev identityProof : Proof Primitive 0 (.pi input) := .lam (.declaration .boundedInput)

abbrev applicationProof (number : Nat) :
    Proof Primitive 0 (.substitute input (ObjectSubstitution.instantiate (.constant number))) :=
  .app identityProof (.constant number)

/-- This computes through a generated lambda/application node and native
Pi beta; it does not define the output by a reference calculation. -/
theorem application_computes (number : Nat) :
    (proof objects constants predicates declarations (applicationProof number)).val testPoint =
      (⟨number, Nat.lt_succ_self number⟩ : Fin (number + 1)) := by
  rw [show proof objects constants predicates declarations (applicationProof number) =
    proof objects constants predicates declarations
      (.substitute (.declaration Primitive.boundedInput)
        (ObjectSubstitution.instantiate (.constant number))) from
          beta objects constants predicates declarations _ _]
  rfl

abbrev pairProof (number : Nat) : Proof Primitive 0 (.sigma input) :=
  .pair (.constant number) (applicationProof number)

/-- The dependent pair retains n together with the actual Fin (n + 1)
certificate produced by applying the generated function. -/
theorem pair_computes (number : Nat) :
    (proof objects constants predicates declarations (pairProof number)).val testPoint =
      (⟨number, ⟨number, Nat.lt_succ_self number⟩⟩ :
        (family objects constants predicates (.sigma input)).obj testPoint) := by
  have pairValue := sigmaDisplayedPair_value_heq (objectFamily objects (context objects 0))
    (family objects constants predicates input)
    (objectSection objects constants (.constant number))
    (by
      rw [← substitution_instantiate]
      exact proof objects constants predicates declarations (applicationProof number)) testPoint
  refine eq_of_heq (pairValue.trans ?_)
  have computes := application_computes number
  exact heq_of_eq (congrArg (fun value : Fin (number + 1) =>
    (⟨number, value⟩ : (family objects constants predicates (.sigma input)).obj testPoint)) computes)

/-- Unpacking the supplied generated pair preserves both coordinates. -/
theorem pair_first_computes (number : Nat) :
    (sigmaDisplayedFst (proof objects constants predicates declarations (pairProof number))).val
      testPoint = number := by
  rw [pair_first objects constants predicates declarations]
  rfl

theorem declaration_origins_distinct (number : Nat) :
    (Proof.declaration (Primitive.closed number false)) ≠
      (Proof.declaration (Primitive.closed number true)) := by
  intro same
  cases same

/-- Beta/congruence equations preserve origins even when their values agree. -/
theorem declaration_origins_not_equated (number : Nat) :
    ¬ ProofEquation (Proof.declaration (Primitive.closed number false))
      (Proof.declaration (Primitive.closed number true)) := by
  intro equation
  have same := Proof.declaration_origin_injective (Proof.equation_origin equation)
  cases same

/-- Evaluating a certificate as a value can erase its authored origin. -/
theorem declaration_values_agree (number : Nat) :
    proof objects constants predicates declarations (.declaration (Primitive.closed number false)) =
      proof objects constants predicates declarations (.declaration (Primitive.closed number true)) := rfl

/-- Fin (n + 1) is not a fixed evidence carrier disguised as dependency. -/
theorem evidence_carriers_differ : ¬ Nonempty (Fin 1 ≃ Fin 2) := by
  rintro ⟨same⟩
  have cardinalities := Fintype.card_congr same
  simp only [Fintype.card_fin] at cardinalities
  omega

def pairFirst {point : (context objects 0).Elements}
    (value : (family objects constants predicates (.sigma input)).obj point) : Nat := value.1

def pairMeasure {point : (context objects 0).Elements}
    (value : (family objects constants predicates (.sigma input)).obj point) : Nat :=
  pairFirst value + value.2.val

/-- A dependent eliminator may inspect both the object and its certificate. -/
def pairNumber (point :
    (totalSpace (family objects constants predicates (.sigma input))).Elements) : Nat :=
  pairMeasure point.2.2

def pairCode : totalSpace (family objects constants predicates (.sigma input)) ⟶ objects where
  app world := TypeCat.ofHom fun value => pairNumber ⟨world, value⟩
  naturality _ _ _ := by ext value; rfl

noncomputable def fullPairMotive : DisplayedFamily
    (totalSpace (family objects constants predicates (.sigma input))) :=
  reindexDisplayed pairCode bounded

def maximalSection : bounded.sections where
  val point := ⟨objectValue point, Nat.lt_succ_self _⟩
  property := by intro source target arrow; exact maximal_cast arrow.property

noncomputable def unpackedBody : (reindexDisplayed
    (Mettapedia.TypeTheory.DisplayedPresheafSliceSigma.sigmaTotalIso
      (objectFamily objects (context objects 0)) (family objects constants predicates input)).inv
        fullPairMotive).sections :=
  reindexDisplayedSection
    ((Mettapedia.TypeTheory.DisplayedPresheafSliceSigma.sigmaTotalIso
      (objectFamily objects (context objects 0)) (family objects constants predicates input)).inv ≫ pairCode)
      bounded maximalSection

noncomputable def eliminatedPair (number : Nat) :
    (reindexDisplayed (sectionLift (family objects constants predicates (.sigma input))
      (proof objects constants predicates declarations (pairProof number))) fullPairMotive).sections :=
  reindexDisplayedSection
    (sectionLift (family objects constants predicates (.sigma input))
      (proof objects constants predicates declarations (pairProof number))) fullPairMotive
        (Mettapedia.TypeTheory.DisplayedPresheafSigmaElimination.eliminate
          (objectFamily objects (context objects 0)) (family objects constants predicates input)
            fullPairMotive unpackedBody)

private theorem dependent_application_heq {A : Type} {B : A → Type}
    (operation : (value : A) → B value) {first second : A} (same : first = second) :
    HEq (operation first) (operation second) := by
  cases same
  rfl

/-- This motive depends on both coordinates of the generated sum. Its
native dependent elimination computes at their supplied values. -/
theorem full_pair_elimination_computes (number : Nat) :
    HEq ((eliminatedPair number).val testPoint)
      (⟨number + number, Nat.lt_succ_self _⟩ : Fin (number + number + 1)) := by
  have computed := dependent_application_heq
    (fun value : (family objects constants predicates (.sigma input)).obj testPoint =>
      (⟨pairMeasure value, Nat.lt_succ_self _⟩ : Fin (pairMeasure value + 1))) (pair_computes number)
  exact computed

/-- Lifting protects the newly bound object rather than reusing the older replacement. -/
def replacement : ObjectSubstitution Nat 0 1 := fun _ => .constant 7

def eleven : Nat := 11
def seven : Nat := 7

def localPoint : (context objects 1).Elements :=
  ⟨testPoint.1, ⟨PUnit.unit, eleven⟩⟩

theorem lifted_binder_is_not_captured :
    (term objects constants (ObjectSubstitution.lift replacement 0)).app localPoint.1 localPoint.2 = eleven ∧
    (term objects constants (ObjectTerm.weaken (replacement 0))).app localPoint.1 localPoint.2 = seven := by
  constructor <;> rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Controls
