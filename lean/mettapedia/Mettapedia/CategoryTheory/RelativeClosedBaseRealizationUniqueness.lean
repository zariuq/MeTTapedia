import Mettapedia.CategoryTheory.RelativeClosedBaseWeakInterpretation

/-!
# Uniqueness of the actual base inverse declarations

The two local inverse equations determine each complete declared arrow.
Terminal, product and equalizer forward maps use only the supplied base
functor. The exponential forward map also uses the already determined
product inverse. Thus independently realized comparison assignments over
the same actual base functor agree on every declaration, including its
endpoints. No interpretation or whole-expression comparison is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.RealizationUniqueness

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C (symbols C) D)

abbrev source (choice : Choice C) := WeakDiagram.nativeSource meanings.base choice
abbrev target (choice : Choice C) := meanings.base.obj (selected choice)

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] in
theorem source_read (choice : Choice C) :
    meanings.evaluateObject (sourceCode choice) = some (source meanings choice) := by
  cases choice with
  | terminal => rfl
  | product first second => exact meanings.evaluate_product rfl rfl
  | equalizer before after =>
      exact meanings.evaluate_equalizer (meanings.base.map before) (meanings.base.map after)
        rfl rfl rfl rfl
  | exponential argument result => exact meanings.evaluate_exponential rfl rfl

theorem target_read (choice : Choice C) :
    meanings.evaluateObject (targetCode choice) = some (target meanings choice) := rfl

variable (realized : Realization (signature (C := C)) meanings)

include realized in
theorem arrow_source (choice : Choice C) : (meanings.arrow choice).source = source meanings choice :=
  Option.some.inj ((realized.source choice).symm.trans (source_read meanings choice))

include realized in
theorem arrow_target (choice : Choice C) : (meanings.arrow choice).target = target meanings choice :=
  Option.some.inj ((realized.target choice).symm.trans (target_read meanings choice))

def inverse (choice : Choice C) : source meanings choice ⟶ target meanings choice :=
  eqToHom (arrow_source meanings realized choice).symm ≫ (meanings.arrow choice).arrow ≫
    eqToHom (arrow_target meanings realized choice)

theorem inverse_read (choice : Choice C) : meanings.evaluateArrow (.name choice) =
    some ⟨source meanings choice, target meanings choice, inverse meanings realized choice⟩ :=
  congrArg some (arrowValue_transport (meanings.arrow choice).arrow
    (arrow_source meanings realized choice) (arrow_target meanings realized choice))

omit [CartesianMonoidalCategory C] [MonoidalClosed C]
  [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem mapped_equalizer_condition {before after : C} (first second : before ⟶ after) :
    meanings.base.map (equalizer.ι first second) ≫ meanings.base.map first =
      meanings.base.map (equalizer.ι first second) ≫ meanings.base.map second := by
  rw [← meanings.base.map_comp, ← meanings.base.map_comp, equalizer.condition]

def forward : (choice : Choice C) → target meanings choice ⟶ source meanings choice
  | .terminal => CartesianMonoidalCategory.toUnit (meanings.base.obj (𝟙_ C))
  | .product first second => CartesianMonoidalCategory.lift
      (meanings.base.map (CartesianMonoidalCategory.fst first second))
      (meanings.base.map (CartesianMonoidalCategory.snd first second))
  | .equalizer first second => equalizer.lift (meanings.base.map (equalizer.ι first second))
      (mapped_equalizer_condition meanings first second)
  | .exponential argument result => Interpretation.abstraction
      (inverse meanings realized (.product (argument ⟶[C] result) argument) ≫
        meanings.base.map (Interpretation.evaluation argument result))

theorem forward_read (choice : Choice C) : meanings.evaluateArrow (forwardCode choice) =
    some ⟨target meanings choice, source meanings choice, forward meanings realized choice⟩ := by
  cases choice with
  | terminal => exact meanings.evaluate_terminal_arrow (meanings.evaluate_base_object (𝟙_ C))
  | product first second =>
      exact meanings.evaluate_pair _ _
        (meanings.evaluate_base_arrow (CartesianMonoidalCategory.fst first second))
        (meanings.evaluate_base_arrow (CartesianMonoidalCategory.snd first second))
  | equalizer first second =>
      exact meanings.evaluate_equalizer_lift (meanings.base.map first) (meanings.base.map second)
        (meanings.base.map (equalizer.ι first second)) (mapped_equalizer_condition meanings first second)
        (meanings.evaluate_base_object _) (meanings.evaluate_base_object _)
        (meanings.evaluate_base_object _) (meanings.evaluate_base_arrow first)
        (meanings.evaluate_base_arrow second) (meanings.evaluate_base_arrow (equalizer.ι first second))
  | exponential argument result =>
      exact meanings.evaluate_abstraction _ (meanings.evaluate_base_object _)
        (meanings.evaluate_base_object _) (meanings.evaluate_base_object _)
        (meanings.evaluate_compose _ _ (inverse_read meanings realized
          (.product (argument ⟶[C] result) argument))
            (meanings.evaluate_base_arrow (Interpretation.evaluation argument result)))

theorem inverse_forward (choice : Choice C) :
    inverse meanings realized choice ≫ forward meanings realized choice = 𝟙 (source meanings choice) := by
  obtain ⟨value, _, _, before, after⟩ := realized.equation (choice, true)
  have leftRead := meanings.evaluate_compose _ _
    (inverse_read meanings realized choice) (forward_read meanings realized choice)
  have rightRead := meanings.evaluate_identity (source_read meanings choice)
  exact ArrowValue.arrow_injective (Option.some.inj
    (leftRead.symm.trans (before.trans (after.symm.trans rightRead))))

theorem forward_inverse (choice : Choice C) :
    forward meanings realized choice ≫ inverse meanings realized choice = 𝟙 (target meanings choice) := by
  obtain ⟨value, _, _, before, after⟩ := realized.equation (choice, false)
  have leftRead := meanings.evaluate_compose _ _
    (forward_read meanings realized choice) (inverse_read meanings realized choice)
  have rightRead := meanings.evaluate_identity (target_read meanings choice)
  exact ArrowValue.arrow_injective (Option.some.inj
    (leftRead.symm.trans (before.trans (after.symm.trans rightRead))))

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
private theorem inverse_determined {X Y : D} {first second : X ⟶ Y} {before after : Y ⟶ X}
    (firstInverse : first ≫ before = 𝟙 X) (secondInverse : after ≫ second = 𝟙 Y)
    (sameForward : before = after) : first = second := by
  subst after
  calc
    first = first ≫ (before ≫ second) := by rw [secondInverse, Category.comp_id]
    _ = second := by rw [← Category.assoc, firstInverse, Category.id_comp]

private theorem arrow_equal_of_forward
    (other : Assignment C (symbols C) D) (second : Realization (signature (C := C)) other)
    (base : meanings.base = other.base) (choice : Choice C)
    (same : HEq (forward meanings realized choice) (forward other second choice)) :
    meanings.arrow choice = other.arrow choice := by
  cases meanings with
  | mk F objects arrows =>
    cases other with
    | mk G nextObjects nextArrows =>
      cases base
      have complete := inverse_determined (inverse_forward _ realized choice)
        (forward_inverse _ second choice) (eq_of_heq same)
      exact Option.some.inj ((inverse_read _ realized choice).trans
        ((congrArg (fun arrow => some (⟨_, _, arrow⟩ : ArrowValue D)) complete).trans
          (inverse_read _ second choice).symm))

include realized in
theorem product_arrow_equal
    (other : Assignment C (symbols C) D) (second : Realization (signature (C := C)) other)
    (base : meanings.base = other.base) (first last : C) :
    meanings.arrow (.product first last) = other.arrow (.product first last) := by
  apply arrow_equal_of_forward meanings realized other second base (.product first last)
  cases meanings
  cases other
  cases base
  rfl

include realized in
theorem arrow_equal
    (other : Assignment C (symbols C) D) (second : Realization (signature (C := C)) other)
    (base : meanings.base = other.base) (choice : Choice C) :
    meanings.arrow choice = other.arrow choice := by
  cases choice with
  | terminal =>
      apply arrow_equal_of_forward meanings realized other second base .terminal
      cases meanings
      cases other
      cases base
      rfl
  | product first last => exact product_arrow_equal meanings realized other second base first last
  | equalizer first last =>
      apply arrow_equal_of_forward meanings realized other second base (.equalizer first last)
      cases meanings
      cases other
      cases base
      rfl
  | exponential argument result =>
      have product := product_arrow_equal meanings realized other second base (argument ⟶[C] result) argument
      apply arrow_equal_of_forward meanings realized other second base (.exponential argument result)
      cases meanings
      cases other
      cases base
      dsimp only [forward]
      have equalInverse : inverse _ realized (.product (argument ⟶[C] result) argument) =
          inverse _ second (.product (argument ⟶[C] result) argument) := by
        exact ArrowValue.arrow_injective (Option.some.inj
          ((inverse_read _ realized (.product (argument ⟶[C] result) argument)).symm.trans
            ((congrArg some product).trans
              (inverse_read _ second (.product (argument ⟶[C] result) argument)))))
      rw [equalInverse]

include realized in
theorem assignment_equal
    (other : Assignment C (symbols C) D) (second : Realization (signature (C := C)) other)
    (base : meanings.base = other.base) : meanings = other := by
  have arrows := funext (arrow_equal meanings realized other second base)
  have objects : meanings.object = other.object := by
    funext origin
    exact origin.down.elim
  cases meanings
  cases other
  cases base
  cases objects
  cases arrows
  rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.RealizationUniqueness
