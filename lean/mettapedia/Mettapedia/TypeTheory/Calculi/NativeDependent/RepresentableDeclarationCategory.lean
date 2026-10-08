import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationArrows

/-!
# A conservative categorical join for generated native substitutions

The relation is authored from generated substitution judgments and the
original identity and composition equations. Its categorical congruence
closure is formed independently of the semantic parser. That parser earns
descent because all three kinds of generator have the stated readouts.
The original category then acts by a genuine faithful functor.

Only the represented context image is used here. Closure of the complete
dependent context category and its families under added theory equations
requires separate constructors and comparison laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations

open _root_.CategoryTheory

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

inductive OriginalEquations : {source target : RepresentedContext C} →
    (source ⟶ target) → (source ⟶ target) → Prop where
  | generated {source target : RepresentedContext C} {first second : source ⟶ target}
      (equation : Contextual.homEquality (signature C) first second) : OriginalEquations first second
  | original_identity (object : C) :
      OriginalEquations (originalArrow (𝟙 object)) (𝟙 (⟨object⟩ : RepresentedContext C))
  | original_composition {source middle target : C}
      (earlier : source ⟶ middle) (later : middle ⟶ target) :
      OriginalEquations (originalArrow (earlier ≫ later)) (originalArrow earlier ≫ originalArrow later)

def originalRelation : HomRel (RepresentedContext C) :=
  fun {source target} first second => OriginalEquations (source := source) (target := target) first second

abbrev conservedContext (C : Type u) [Category.{u} C] :=
  _root_.CategoryTheory.Quotient (originalRelation (C := C))

def originalProjection : RepresentedContext C ⥤ conservedContext C :=
  _root_.CategoryTheory.Quotient.functor (originalRelation (C := C))

def originalFunctor : C ⥤ conservedContext C where
  obj object := originalProjection.obj ⟨object⟩
  map arrow := originalProjection.map (originalArrow arrow)
  map_id object := _root_.CategoryTheory.Quotient.sound _ (.original_identity object)
  map_comp earlier later := _root_.CategoryTheory.Quotient.sound _ (.original_composition earlier later)

theorem originalEquation_readout {source target : RepresentedContext C}
    {first second : source ⟶ target} (equation : OriginalEquations first second) :
    readArrow first = readArrow second := by
  cases equation with
  | generated admitted => exact readArrow_generated_equation admitted
  | original_identity object =>
      rw [readArrow_original, readArrow_identity, originalPresheafArrow_identity]
  | original_composition earlier later =>
      rw [readArrow_original, readArrow_composition, readArrow_original, readArrow_original,
        originalPresheafArrow_composition]

/-- Semantic descent is proved from the actual independent generators,
not included among the assumptions of the generated category. -/
def conservedReadout : conservedContext C ⥤ Cᵒᵖ ⥤ Type u :=
  _root_.CategoryTheory.Quotient.lift (originalRelation (C := C)) representedReadout
    (fun _ _ _ _ equation => originalEquation_readout equation)

theorem conservedReadout_project {source target : RepresentedContext C} (arrow : source ⟶ target) :
    conservedReadout.map (originalProjection.map arrow) = readArrow arrow := rfl

theorem conservedReadout_original {source target : C} (arrow : source ⟶ target) :
    conservedReadout.map (originalFunctor.map arrow) = originalPresheafArrow arrow :=
  readArrow_original arrow

theorem originalPresheafArrow_injective {source target : C} :
    Function.Injective (@originalPresheafArrow C _ source target) := by
  intro first second same
  have read := congrArg (fun arrow => objectNameInverse source ≫ arrow ≫ objectName target) same
  have sourceCancellation : objectNameInverse source ≫ objectName source = 𝟙 (yoneda.obj source) :=
    (objectScopeIso source).inv_hom_id
  have targetCancellation : objectNameInverse target ≫ objectName target = 𝟙 (yoneda.obj target) :=
    (objectScopeIso target).inv_hom_id
  rw [originalPresheafArrow_name, originalPresheafArrow_name] at read
  simp only [Category.assoc] at read
  rw [← Category.assoc (objectNameInverse source), sourceCancellation,
    ← Category.assoc (objectNameInverse source), sourceCancellation,
    targetCancellation] at read
  simp only [Category.id_comp, Category.comp_id] at read
  exact yoneda.map_injective read

theorem originalFunctor_map_injective {source target : C} :
    Function.Injective (fun arrow : source ⟶ target => (originalFunctor (C := C)).map arrow) := by
  intro first second same
  apply originalPresheafArrow_injective
  exact (conservedReadout_original first).symm.trans
    ((congrArg (conservedReadout.map) same).trans (conservedReadout_original second))

instance originalFunctor_faithful : (originalFunctor (C := C)).Faithful where
  map_injective {source target} {first second} same :=
    @originalFunctor_map_injective C _ source target first second same

/-- At every supplied generalized argument, the categorical join retains
the complete original arrow rather than only a terminal observation. -/
theorem originalFunctor_generalized_readout {source target world : C}
    (arrow : source ⟶ target) (argument : world ⟶ source) :
    (objectName target).app (Opposite.op world)
      ((conservedReadout.map (originalFunctor.map arrow)).app (Opposite.op world)
        ((objectNameInverse source).app (Opposite.op world) argument)) = argument ≫ arrow := by
  rw [conservedReadout_original, originalPresheafArrow_name]
  rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations
