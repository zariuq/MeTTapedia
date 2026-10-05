import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Types.Basic

/-!
# Dependent identity elimination for coherent groupoid motives

Identity witnesses in a groupoid are its actual arrows. The identity context
is the arrow groupoid, retaining both endpoints and the witness. A motive is
a functor on that context, so it includes transport along commuting squares.
Reflexivity is the diagonal functor. Transport from the reflexive arrow
constructs dependent elimination for every such motive and every natural
reflexivity section, with computation and functorial substitution laws.

The construction neither identifies parallel arrows nor turns an arrow into
equality of its endpoint objects. This is an identity comparison model; it
does not assert a syntax interpretation or a complete groupoid CwF here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.GroupoidIdentityElimination

open CategoryTheory

universe u v w u' v' u'' v''

variable {C : Type u} [Category.{v} C]

/-- Compose with explicit functor-law proofs. This avoids a classical
dependency in the standard library's proof of functor composition. -/
@[implicit_reducible] def compose {D : Type u'} [Category.{v'} D]
    {E : Type u''} [Category.{v''} E] (first : C ⥤ D) (second : D ⥤ E) : C ⥤ E where
  obj object := second.obj (first.obj object)
  map arrow := second.map (first.map arrow)
  map_id object := by rw [first.map_id, second.map_id]
  map_comp earlier later := by rw [first.map_comp, second.map_comp]

local infixr:80 " ⋙₀ " => compose

/-- A dependent section includes its naturality evidence. -/
structure NaturalSection (family : C ⥤ Type w) where
  value : ∀ object, family.obj object
  natural : ∀ {source target} (arrow : source ⟶ target),
    family.map arrow (value source) = value target

namespace NaturalSection

@[ext] theorem ext {family : C ⥤ Type w} {first second : NaturalSection family}
    (values : first.value = second.value) : first = second := by
  cases first
  cases second
  cases values
  rfl

def reindex {D : Type u'} [Category.{v'} D] {family : C ⥤ Type w}
    (sectionValue : NaturalSection family) (σ : D ⥤ C) :
    NaturalSection (σ ⋙₀ family) where
  value object := sectionValue.value (σ.obj object)
  natural arrow := sectionValue.natural (σ.map arrow)

@[simp] theorem reindex_id {family : C ⥤ Type w} (sectionValue : NaturalSection family) :
    sectionValue.reindex (𝟭 C) = sectionValue := by
  apply ext
  rfl

theorem reindex_comp {D : Type u'} [Category.{v'} D]
    {E : Type u''} [Category.{v''} E] {family : C ⥤ Type w}
    (sectionValue : NaturalSection family) (σ : D ⥤ C) (τ : E ⥤ D) :
    (sectionValue.reindex σ).reindex τ = sectionValue.reindex (τ ⋙₀ σ) := by
  apply ext
  rfl

end NaturalSection

/-- Reflexivity keeps the actual endpoint object. -/
def diagonal : C ⥤ Arrow C where
  obj object := Arrow.mk (𝟙 object)
  map arrow := Arrow.homMk arrow arrow (by simp)
  map_id object := by apply Arrow.hom_ext <;> rfl
  map_comp first second := by apply Arrow.hom_ext <;> rfl

/-- The canonical square transports from reflexivity to the given witness. -/
def reflexivityTo (witness : Arrow C) : diagonal.obj witness.left ⟶ witness :=
  Arrow.homMk (𝟙 witness.left) witness.hom (by
    change (𝟙 witness.left) ≫ witness.hom = (𝟙 witness.left) ≫ witness.hom
    rfl)

@[simp] theorem reflexivityTo_diagonal (object : C) :
    reflexivityTo (diagonal.obj object) = 𝟙 (diagonal.obj object) := by
  apply Arrow.hom_ext <;> rfl

theorem reflexivityTo_natural {first second : Arrow C} (square : first ⟶ second) :
    diagonal.map square.left ≫ reflexivityTo second = reflexivityTo first ≫ square := by
  apply Arrow.hom_ext
  · change square.left ≫ 𝟙 second.left = 𝟙 first.left ≫ square.left
    simp
  · change square.left ≫ second.hom = first.hom ≫ square.right
    exact square.w

/-- Based elimination retains a supplied value at the original endpoint;
its motive still transports along the whole identity context. -/
def basedJ (motive : Arrow C ⥤ Type w) {origin : C}
    (atReflexivity : motive.obj (diagonal.obj origin)) {endpoint : C}
    (witness : origin ⟶ endpoint) : motive.obj (Arrow.mk witness) :=
  motive.map (reflexivityTo (Arrow.mk witness)) atReflexivity

@[simp] theorem basedJ_beta (motive : Arrow C ⥤ Type w) {origin : C}
    (atReflexivity : motive.obj (diagonal.obj origin)) :
    basedJ motive atReflexivity (𝟙 origin) = atReflexivity := by
  change motive.map (reflexivityTo (diagonal.obj origin)) atReflexivity = atReflexivity
  rw [reflexivityTo_diagonal]
  exact motive.map_id_apply _ _

/-- Substitution among based identity witnesses is a square fixing the
original endpoint. This exact square makes the dependent values commute. -/
theorem basedJ_natural (motive : Arrow C ⥤ Type w) {origin first second : C}
    (atReflexivity : motive.obj (diagonal.obj origin))
    (left : origin ⟶ first) (right : origin ⟶ second)
    (square : Arrow.mk left ⟶ Arrow.mk right) (fixes : square.left = 𝟙 origin) :
    motive.map square (basedJ motive atReflexivity left) =
      basedJ motive atReflexivity right := by
  have comparison : reflexivityTo (Arrow.mk left) ≫ square =
      reflexivityTo (Arrow.mk right) := by
    apply Arrow.hom_ext
    · change 𝟙 origin ≫ square.left = 𝟙 origin
      rw [fixes, Category.id_comp]
    · change left ≫ square.right = right
      have coherent : square.left ≫ right = left ≫ square.right := square.w
      rw [fixes] at coherent
      exact coherent.symm.trans (Category.id_comp right)
  unfold basedJ
  rw [← ConcreteCategory.comp_apply, ← motive.map_comp, comparison]

/-- Actual dependent J over both endpoints and their identity witness. -/
def J (motive : Arrow C ⥤ Type w) (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    NaturalSection motive where
  value witness := motive.map (reflexivityTo witness) (atReflexivity.value witness.left)
  natural square := by
    rw [← ConcreteCategory.comp_apply, ← motive.map_comp,
      ← reflexivityTo_natural, motive.map_comp, ConcreteCategory.comp_apply]
    exact congrArg (motive.map (reflexivityTo _)) (atReflexivity.natural square.left)

@[simp] theorem J_beta (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) (object : C) :
    (J motive atReflexivity).value (diagonal.obj object) = atReflexivity.value object := by
  change motive.map (reflexivityTo (diagonal.obj object)) (atReflexivity.value object) = _
  rw [reflexivityTo_diagonal]
  change motive.map (𝟙 (diagonal.obj object)) (atReflexivity.value object) = _
  exact motive.map_id_apply _ _

theorem J_beta_section (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    (J motive atReflexivity).reindex diagonal = atReflexivity := by
  apply NaturalSection.ext
  funext object
  exact J_beta motive atReflexivity object

/-- Naturality proves uniqueness against every endpoint-and-witness motive. -/
theorem J_unique (motive : Arrow C ⥤ Type w) (sectionValue : NaturalSection motive) :
    J motive (sectionValue.reindex diagonal) = sectionValue := by
  apply NaturalSection.ext
  funext witness
  exact sectionValue.natural (reflexivityTo witness)

/-- This is the actual equivalence of coherent dependent sections. -/
def reflexivitySectionEquiv (motive : Arrow C ⥤ Type w) :
    NaturalSection motive ≃ NaturalSection (diagonal ⋙₀ motive) where
  toFun sectionValue := sectionValue.reindex diagonal
  invFun := J motive
  left_inv := J_unique motive
  right_inv := J_beta_section motive

/-! ## Actual inverse witnesses in the identity context -/

section Groupoid

variable {G : Type u} [Groupoid.{v} G]

/-- Inverse commuting squares retain the actual inverse endpoint arrows. -/
def inverseSquare {first second : Arrow G} (square : first ⟶ second) : second ⟶ first :=
  Arrow.homMk (Groupoid.inv square.left) (Groupoid.inv square.right) (by
    calc
      Groupoid.inv square.left ≫ first.hom =
          (Groupoid.inv square.left ≫ first.hom) ≫
            (square.right ≫ Groupoid.inv square.right) := by
              rw [Groupoid.comp_inv, Category.comp_id]
      _ = ((Groupoid.inv square.left ≫ first.hom) ≫ square.right) ≫
          Groupoid.inv square.right :=
        (Category.assoc (Groupoid.inv square.left ≫ first.hom) square.right
          (Groupoid.inv square.right)).symm
      _ = (Groupoid.inv square.left ≫ (square.left ≫ second.hom)) ≫
          Groupoid.inv square.right :=
        congrArg (fun arrow => arrow ≫ Groupoid.inv square.right)
          ((Category.assoc (Groupoid.inv square.left) first.hom square.right).trans
            (congrArg (fun arrow => Groupoid.inv square.left ≫ arrow) square.w.symm))
      _ = second.hom ≫ Groupoid.inv square.right := by
        rw [← Category.assoc, Groupoid.inv_comp, Category.id_comp])

/-- The identity context is a genuine groupoid whenever its endpoints are.
Its inverse is constructed, rather than obtained from an existential IsIso. -/
@[instance_reducible] def identityContextGroupoid : CategoryTheory.Groupoid.{v} (Arrow G) where
  Hom source target := source ⟶ target
  id object := 𝟙 object
  comp first second := first ≫ second
  id_comp arrow := Category.id_comp arrow
  comp_id arrow := Category.comp_id arrow
  assoc first second third := Category.assoc first second third
  inv := inverseSquare
  inv_comp square := by
    apply Arrow.hom_ext
    · change Groupoid.inv square.left ≫ square.left = 𝟙 _
      exact Groupoid.inv_comp _
    · change Groupoid.inv square.right ≫ square.right = 𝟙 _
      exact Groupoid.inv_comp _
  comp_inv square := by
    apply Arrow.hom_ext
    · change square.left ≫ Groupoid.inv square.left = 𝟙 _
      exact Groupoid.comp_inv _
    · change square.right ≫ Groupoid.inv square.right = 𝟙 _
      exact Groupoid.comp_inv _

end Groupoid

/-! ## Commuting functorial substitution -/

variable {D : Type u'} [Category.{v'} D]

/-- Mapping an identity witness transports its reflexive boundary through
this canonical square, whose endpoint arrows are both identities. -/
def reflexivitySquare (σ : D ⥤ C) (object : D) :
    diagonal.obj (σ.obj object) ⟶ σ.mapArrow.obj (diagonal.obj object) :=
  Arrow.homMk (𝟙 _) (𝟙 _) (by
    change (𝟙 (σ.obj object)) ≫ σ.map (𝟙 object) = (𝟙 (σ.obj object)) ≫ 𝟙 (σ.obj object)
    rw [σ.map_id])

theorem reflexivitySquare_natural (σ : D ⥤ C)
    {source target : D} (arrow : source ⟶ target) :
    diagonal.map (σ.map arrow) ≫ reflexivitySquare σ target =
      reflexivitySquare σ source ≫ σ.mapArrow.map (diagonal.map arrow) := by
  apply Arrow.hom_ext
  · change σ.map arrow ≫ 𝟙 (σ.obj target) = 𝟙 (σ.obj source) ≫ σ.map arrow
    simp
  · change σ.map arrow ≫ 𝟙 (σ.obj target) = 𝟙 (σ.obj source) ≫ σ.map arrow
    simp

theorem reflexivitySquare_to (σ : D ⥤ C) (witness : Arrow D) :
    reflexivitySquare σ witness.left ≫ σ.mapArrow.map (reflexivityTo witness) =
      reflexivityTo (σ.mapArrow.obj witness) := by
  apply Arrow.hom_ext
  · change 𝟙 (σ.obj witness.left) ≫ σ.map (𝟙 witness.left) = 𝟙 (σ.obj witness.left)
    simp
  · change 𝟙 (σ.obj witness.left) ≫ σ.map witness.hom = σ.map witness.hom
    simp

/-- Reindex the reflexivity method with the actual boundary comparison. -/
def reindexReflexivity (σ : D ⥤ C) (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    NaturalSection (diagonal ⋙₀ σ.mapArrow ⋙₀ motive) where
  value object := motive.map (reflexivitySquare σ object)
    (atReflexivity.value (σ.obj object))
  natural arrow := by
    change motive.map (σ.mapArrow.map (diagonal.map arrow))
      (motive.map (reflexivitySquare σ _) (atReflexivity.value _)) = _
    rw [← ConcreteCategory.comp_apply, ← motive.map_comp,
      ← reflexivitySquare_natural, motive.map_comp, ConcreteCategory.comp_apply]
    exact congrArg (motive.map (reflexivitySquare σ _))
      (atReflexivity.natural (σ.map arrow))

/-- Dependent J commutes with every path-respecting substitution functor. -/
theorem J_sub (σ : D ⥤ C) (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) (witness : Arrow D) :
    (J (σ.mapArrow ⋙₀ motive) (reindexReflexivity σ motive atReflexivity)).value witness =
      (J motive atReflexivity).value (σ.mapArrow.obj witness) := by
  change motive.map (σ.mapArrow.map (reflexivityTo witness))
    (motive.map (reflexivitySquare σ witness.left)
      (atReflexivity.value (σ.obj witness.left))) = _
  rw [← ConcreteCategory.comp_apply, ← motive.map_comp, reflexivitySquare_to]
  rfl

theorem J_sub_section (σ : D ⥤ C) (motive : Arrow C ⥤ Type w)
    (atReflexivity : NaturalSection (diagonal ⋙₀ motive)) :
    J (σ.mapArrow ⋙₀ motive) (reindexReflexivity σ motive atReflexivity) =
      (J motive atReflexivity).reindex σ.mapArrow := by
  apply NaturalSection.ext
  funext witness
  exact J_sub σ motive atReflexivity witness

/-! ## Why raw witness-indexed motives are a stronger commitment -/

def BasedContext (origin : C) : Type (max u v) := Σ endpoint : C, origin ⟶ endpoint

def reflexiveBasedContext (origin : C) : BasedContext origin := ⟨origin, 𝟙 origin⟩

/-- An unrestricted raw motive has no transport or naturality evidence.
This is an operation to compare, not an assumed eliminator of the model. -/
abbrev RawBasedElimination (origin : C) :=
  (motive : BasedContext origin → Type (max u v)) →
    motive (reflexiveBasedContext origin) → (witness : BasedContext origin) → motive witness

/-- Raw elimination would force every based witness to be the reflexive
one. Coherent functor motives do not have this consequence. -/
theorem rawBasedElimination_collapses {origin : C}
    (eliminate : RawBasedElimination origin) (witness : BasedContext origin) :
    witness = reflexiveBasedContext origin :=
  (eliminate (fun point => ULift.{max u v, 0}
    (PLift (point = reflexiveBasedContext origin))) ⟨⟨rfl⟩⟩ witness).down.down

theorem rawBasedElimination_loopUIP {origin : C}
    (eliminate : RawBasedElimination origin) (loop : origin ⟶ origin) : loop = 𝟙 origin := by
  have same := rawBasedElimination_collapses eliminate (⟨origin, loop⟩ : BasedContext origin)
  exact eq_of_heq (Sigma.mk.inj same).2

#print axioms J
#print axioms J_beta
#print axioms J_unique
#print axioms reflexivitySectionEquiv
#print axioms J_sub
#print axioms identityContextGroupoid
#print axioms basedJ_natural
#print axioms rawBasedElimination_loopUIP

end Mettapedia.TypeTheory.GroupoidIdentityElimination
