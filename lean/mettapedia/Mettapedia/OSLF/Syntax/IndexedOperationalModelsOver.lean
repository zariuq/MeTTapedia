import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationCategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Proof-relevant operational models over a category of authored bases

An authored presentation may depend functorially on a base model such as a
binding clone satisfying equations. An operational model over that base
interprets every indexed rule constructor. A morphism preserves its base
interpretation and its proof-relevant rule action, with an equality witnessing
that both interpretations use the same rule-presentation map.
-/

set_option autoImplicit false
set_option linter.checkUnivs false

namespace Mettapedia.OSLF.Binding.IndexedOperationalModelsOver

open CategoryTheory CategoryTheory.Limits
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

universe uBase uIndex uShape uPosition uCat vCat

variable {Base : Type uBase} {C : Type uCat} [Category.{vCat} C]
variable (P : C ⥤ Presentation.{uBase, uIndex, uShape, uPosition} Base)

/-- A base model carrying an interpretation of its associated rule
presentation, with recursive firing evidence retained. -/
structure Model where
  base : C
  evidence : OperationalRuleModels.Model (P.obj base).rules

namespace Model

/-- Forget the base label while retaining its exact rule presentation and
chosen evidence algebra. -/
def equipped (X : Model P) :
    Equipped.{uBase, uIndex, uShape, uPosition} Base where
  presentation := P.obj X.base
  model := X.evidence

end Model

/-- A map of base models together with a compatible map of individual firing
evidence. -/
structure Hom (X Y : Model P) where
  base : X.base ⟶ Y.base
  evidence : Equipped.Map (X.equipped P) (Y.equipped P)
  presentationEq : evidence.presentation = P.map base

namespace Hom

variable {X Y Z W : Model P}

theorem ext {first second : Hom P X Y}
    (baseEq : first.base = second.base)
    (evidenceEq : first.evidence = second.evidence) :
    first = second := by
  cases first with
  | mk firstBase firstEvidence firstCompatibility =>
      cases second with
      | mk secondBase secondEvidence secondCompatibility =>
          cases baseEq
          cases evidenceEq
          rfl

def id (X : Model P) : Hom P X X where
  base := 𝟙 X.base
  evidence := Equipped.Map.id (X.equipped P)
  presentationEq := by
    change 𝟙 (P.obj X.base) = P.map (𝟙 X.base)
    exact (P.map_id X.base).symm

noncomputable def comp (first : Hom P X Y) (second : Hom P Y Z) :
    Hom P X Z where
  base := first.base ≫ second.base
  evidence := Equipped.Map.comp first.evidence second.evidence
  presentationEq := by
    change Presentation.Map.comp first.evidence.presentation
      second.evidence.presentation = P.map (first.base ≫ second.base)
    rw [first.presentationEq, second.presentationEq]
    exact (P.map_comp first.base second.base).symm

theorem id_comp (mapping : Hom P X Y) :
    comp P (id P X) mapping = mapping := by
  apply ext P (Category.id_comp mapping.base)
  exact Equipped.Map.id_comp mapping.evidence

theorem comp_id (mapping : Hom P X Y) :
    comp P mapping (id P Y) = mapping := by
  apply ext P (Category.comp_id mapping.base)
  exact Equipped.Map.comp_id mapping.evidence

theorem comp_assoc (first : Hom P X Y) (second : Hom P Y Z)
    (third : Hom P Z W) :
    comp P (comp P first second) third =
      comp P first (comp P second third) := by
  apply ext P (Category.assoc first.base second.base third.base)
  exact Equipped.Map.comp_assoc first.evidence second.evidence
    third.evidence

end Hom

/-- Models of a functorial authored rule presentation form a category. -/
noncomputable instance : Category (Model P) where
  Hom := Hom P
  id := Hom.id P
  comp := Hom.comp P
  id_comp := by intro X Y f; exact Hom.id_comp P f
  comp_id := by intro X Y f; exact Hom.comp_id P f
  assoc := by intro X Y Z W f g h; exact Hom.comp_assoc P f g h

/-- Forgetting the rule algebra retains the authored base model and its
actual interpretation map. -/
noncomputable def forget : Model P ⥤ C where
  obj X := X.base
  map f := f.base
  map_id := by intro X; rfl
  map_comp := by intro X Y Z f g; rfl

/-- The free proof-relevant rule algebra above any authored base model. -/
def free (A : C) : Model P where
  base := A
  evidence := OperationalRuleModels.free (P.obj A).rules

/-- A base interpretation acts on every free firing history through its
induced map of rule presentations. -/
noncomputable def freeMap {A B : C} (mapping : A ⟶ B) :
    Hom P (free P A) (free P B) where
  base := mapping
  evidence := IndexedOperationalPresentationCategory.freeMap (P.map mapping)
  presentationEq := rfl

/-- The free proof-relevant operational model varies functorially over the
authored base theory. -/
noncomputable def freeFunctor : C ⥤ Model P where
  obj := free P
  map := freeMap P
  map_id := by
    intro A
    change freeMap P (𝟙 A) = Hom.id P (free P A)
    apply Hom.ext P
    · rfl
    · change IndexedOperationalPresentationCategory.freeMap (P.map (𝟙 A)) =
        Equipped.Map.id (Model.equipped P (free P A))
      rw [P.map_id]
      exact (IndexedOperationalPresentationCategory.freeFunctor
        (Base := Base)).map_id (P.obj A)
  map_comp := by
    intro A B D first second
    change freeMap P (first ≫ second) =
      Hom.comp P (freeMap P first) (freeMap P second)
    apply Hom.ext P
    · rfl
    · change IndexedOperationalPresentationCategory.freeMap
          (P.map (first ≫ second)) =
        Equipped.Map.comp
          (IndexedOperationalPresentationCategory.freeMap (P.map first))
          (IndexedOperationalPresentationCategory.freeMap (P.map second))
      rw [P.map_comp]
      exact (IndexedOperationalPresentationCategory.freeFunctor
        (Base := Base)).map_comp (P.map first) (P.map second)

/-- Interpret the free rule histories along any map of authored base models. -/
noncomputable def lift {A : C} (target : Model P)
    (baseMap : A ⟶ target.base) : Hom P (free P A) target where
  base := baseMap
  evidence := IndexedOperationalPresentationCategory.lift
    (target.equipped P) (P.map baseMap)
  presentationEq := rfl

/-- An interpretation from free operational syntax is uniquely determined
by its map of authored base models. -/
theorem lift_unique {A : C} {target : Model P}
    (mapping : Hom P (free P A) target) :
    lift P target mapping.base = mapping := by
  apply Hom.ext P
  · rfl
  · have h := IndexedOperationalPresentationCategory.lift_unique
      mapping.evidence
    rw [mapping.presentationEq] at h
    exact h

/-- A simultaneous interpretation of a free rule model is exactly an
interpretation of its authored base model. -/
noncomputable def freeHomEquiv (A : C) (target : Model P) :
    (free P A ⟶ target) ≃ (A ⟶ target.base) where
  toFun mapping := mapping.base
  invFun := lift P target
  left_inv := lift_unique P
  right_inv := by intro mapping; rfl

/-- Freely adjoining proof-relevant rule histories over a functorial
authored presentation is left adjoint to forgetting those histories. -/
noncomputable def freeAdjunction :
    freeFunctor P ⊣ forget P :=
  Adjunction.mkOfHomEquiv
    { homEquiv := freeHomEquiv P
      homEquiv_naturality_left_symm := by
        intro A' A target first second
        apply (freeHomEquiv P A' target).injective
        rfl
      homEquiv_naturality_right := by
        intro A X Y first second
        rfl }

/-- The adjunction unit leaves each authored base model unchanged. -/
theorem freeAdjunction_unit_app (A : C) :
    (freeAdjunction P).unit.app A = 𝟙 A := by
  rfl

/-- The counit folds a freely generated firing history into its chosen
semantic rule action, over the identity base interpretation. -/
theorem freeAdjunction_counit_app (target : Model P) :
    (freeAdjunction P).counit.app target = lift P target (𝟙 target.base) := by
  rfl

/-- Interpret a free operational model along the unique base map out of an
initial authored model. -/
noncomputable def initialHom {A : C} (initial : IsInitial A)
    (target : Model P) : Hom P (free P A) target :=
  lift P target (initial.to target.base)

/-- Initiality of the authored base lifts to initiality of its free
proof-relevant operational model. The uniqueness law includes base maps and
all recursively generated firing histories. -/
noncomputable def freeIsInitial {A : C} (initial : IsInitial A) :
    IsInitial (free P A) :=
  IsInitial.ofUniqueHom (initialHom P initial) (fun target candidate => by
    have baseEq : candidate.base = initial.to target.base :=
      initial.hom_ext candidate.base (initial.to target.base)
    have presentationEq : candidate.evidence.presentation =
        P.map (initial.to target.base) :=
      candidate.presentationEq.trans (congrArg P.map baseEq)
    have evidenceEq : candidate.evidence =
        (initialHom P initial target).evidence := by
      have h := IndexedOperationalPresentationCategory.lift_unique
        candidate.evidence
      rw [presentationEq] at h
      exact h.symm
    exact Hom.ext P baseEq evidenceEq)

#print axioms freeIsInitial
#print axioms freeAdjunction

end Mettapedia.OSLF.Binding.IndexedOperationalModelsOver
