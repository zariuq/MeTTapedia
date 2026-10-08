import Mettapedia.TypeTheory.Calculi.NativeDependent.RuleInitiality

/-!
# A bounded-natural native model over an arbitrary small theory

The object presheaf is constant Nat but its atomic evidence family is
genuinely dependent: the witness of n has type Fin (n + 1). Generated
abstraction and application use the selected native product, over the
supplied theory category rather than a fixed auxiliary world.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.BoundedNaturalModel

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open ObjectInterpretation PresheafInterpretation RuleInitiality

variable (C : Type) [Category C]

abbrev objects : Cᵒᵖ ⥤ Type := (Functor.const Cᵒᵖ).obj Nat

def constants (name : Nat) : (objects C).sections where
  val _ := name
  property _ := rfl

def number (point : (objects C).Elements) : Nat := point.2

def bounded : DisplayedFamily (objects C) where
  obj point := Fin (number C point + 1)
  map arrow := TypeCat.ofHom fun value =>
    cast (congrArg (fun n : Nat => Fin (n + 1)) arrow.property) value
  map_id point := by ext value; rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    change cast _ value = cast _ (cast _ value)
    exact (cast_cast _ _ value).symm

abbrev predicates (_name : PUnit) : DisplayedFamily (objects C) := bounded C

abbrev input : Formula Nat PUnit 1 := .atom PUnit.unit (.var 0)

def inputValue (point : (context (objects C) 1).Elements) : Nat := point.2.2

inductive Primitive : (n : Nat) → Formula Nat PUnit n → Type where
  | boundedInput : Primitive 1 input
  | closed (n : Nat) (origin : Bool) :
      Primitive 0 (.substitute input (ObjectSubstitution.instantiate (.constant n)))

private theorem maximal_cast {first second : Nat} (same : first = second) :
    cast (congrArg (fun n : Nat => Fin (n + 1)) same)
      (⟨first, Nat.lt_succ_self _⟩ : Fin (first + 1)) =
        (⟨second, Nat.lt_succ_self _⟩ : Fin (second + 1)) := by
  cases same
  rfl

def inputSection : (family (objects C) (constants C) (predicates C) input).sections where
  val point := by
    change Fin (inputValue C point + 1)
    exact ⟨point.2.2, Nat.lt_succ_self _⟩
  property := by
    intro source target arrow
    have numbersAgree : source.2.2 = target.2.2 := congrArg Sigma.snd arrow.property
    change cast _ (⟨source.2.2, Nat.lt_succ_self _⟩ : Fin (inputValue C source + 1)) =
      (⟨target.2.2, Nat.lt_succ_self _⟩ : Fin (inputValue C target + 1))
    exact maximal_cast numbersAgree

noncomputable def declarations : ∀ {n : Nat} {formula : Formula Nat PUnit n},
    Primitive n formula → (family (objects C) (constants C) (predicates C) formula).sections
  | _, _, .boundedInput => inputSection C
  | _, _, .closed n _ =>
      reindexDisplayedSection (substitution (objects C) (constants C)
        (ObjectSubstitution.instantiate (.constant n)))
          (family (objects C) (constants C) (predicates C) input) (inputSection C)

def point (world : Cᵒᵖ) : (context (objects C) 0).Elements := ⟨world, PUnit.unit⟩

abbrev identityProof : Proof Primitive 0 (.pi input) := .lam (.declaration .boundedInput)

abbrev applicationProof (n : Nat) :
    Proof Primitive 0 (.substitute input (ObjectSubstitution.instantiate (.constant n))) :=
  .app identityProof (.constant n)

theorem application_computes (world : Cᵒᵖ) (n : Nat) :
    (proof (objects C) (constants C) (predicates C) (declarations C)
      (applicationProof n)).val (point C world) =
        (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
  rw [show proof (objects C) (constants C) (predicates C) (declarations C)
      (applicationProof n) =
    proof (objects C) (constants C) (predicates C) (declarations C)
      (.substitute (.declaration Primitive.boundedInput)
        (ObjectSubstitution.instantiate (.constant n))) from
          beta (objects C) (constants C) (predicates C) (declarations C) _ _]
  rfl

theorem declaration_origins_distinct (n : Nat) :
    (Proof.declaration (Primitive.closed n false)) ≠
      (Proof.declaration (Primitive.closed n true)) := by
  intro same
  cases same

theorem declaration_values_agree (n : Nat) :
    proof (objects C) (constants C) (predicates C) (declarations C)
        (.declaration (Primitive.closed n false)) =
      proof (objects C) (constants C) (predicates C) (declarations C)
        (.declaration (Primitive.closed n true)) := rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.BoundedNaturalModel
