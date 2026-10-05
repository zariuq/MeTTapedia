import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCoalgebras

/-!
# The actual reachable contextual subcoalgebra

The reachable subfamily has the original value carrier with its proved
reachability predicate. Its inclusion is injective. Every future successor
predicate has a constructed small enumeration: generated receipts filtered
by the original coalgebra's truth at their endpoint values.

The original small generated coalgebra maps naturally onto this subcoalgebra.
Both the covering map and the inclusion satisfy whole future-coalgebra
image equations. No inverse of the cover or source representative is chosen.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReachableCoalgebras

open CategoryTheory
open PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u v w
variable {D : Type u} [Category.{u} D] (A : D ⥤ Type v)
variable (original : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable (enumerations : ∀ point value, CoveredFuturePowerFamilies.Enumeration (original.app point value).val)
variable (root : ContextualGeneratedCoalgebras.State A)

abbrev reachable := ContextualGeneratedCoalgebras.reachableFamily A original root
abbrev generated := ContextualGeneratedCoalgebras.family A original enumerations root
abbrev cover := ContextualGeneratedCoalgebras.reachabilityCover A original enumerations root

def inclusion : NaturalHom (reachable A original root) A where
  app _ argument := argument.val
  naturality _ _ := rfl

theorem inclusion_injective (point : D) :
    Function.Injective ((inclusion A original root).app point) := fun _ _ same => Subtype.ext same

theorem inclusion_cancel {parameters : D ⥤ Type w}
    (first second : NaturalHom parameters (reachable A original root))
    (same : first.comp (inclusion A original root) = second.comp (inclusion A original root)) :
    first = second := by
  apply NaturalHom.ext
  intro point parameter
  apply inclusion_injective A original root point
  exact congrArg (fun operation : NaturalHom parameters A => operation.app point parameter) same

def predicate (point : D) (source : (reachable A original root).obj point) :
    CoveredFuturePowerFamilies.Predicate (reachable A original root) point where
  holds argument := (original.app point source.val).val.holds
    ((CoveredFuturePowerFunctor.futureArguments (inclusion A original root) point).obj argument)
  closed move available := (original.app point source.val).val.closed
    ((CoveredFuturePowerFunctor.futureArguments (inclusion A original root) point).map move) available

/-- This is a genuine small carrier: it stores a generated receipt and
only propositional evidence about the larger endpoint value. -/
def smallEnumeration (point : D) (source : (reachable A original root).obj point) :
    CoveredFuturePowerFamilies.Enumeration (predicate A original root point source) where
  Carrier future := {receipt : (generated A original enumerations root).obj future.1 //
    (original.app point source.val).val.holds
      ⟨future, (ContextualGeneratedCoalgebras.endpoint A original enumerations root).app future.1 receipt⟩}
  value future code := (cover A original enumerations root).app future.1 code.val
  covered future argument := by
    constructor
    · intro available
      obtain ⟨receipt, same⟩ :=
        ContextualGeneratedCoalgebras.reachable_covered A original enumerations root
          ⟨future.1, argument.val⟩ argument.property
      have truth : (original.app point source.val).val.holds
          ⟨future, (ContextualGeneratedCoalgebras.endpoint A original enumerations root).app future.1 receipt⟩ := by
        rw [same]
        exact available
      exact ⟨⟨receipt, truth⟩, Subtype.ext same⟩
    · rintro ⟨code, same⟩
      have values := congrArg Subtype.val same
      have truth := code.property
      change (ContextualGeneratedCoalgebras.endpoint A original enumerations root).app future.1 code.val =
        argument.val at values
      rw [values] at truth
      exact truth

/-- All model fields are constructed from the original coalgebra and the
small generator; no future enumeration is selected from its existence. -/
def coalgebra : NaturalHom (reachable A original root)
    (CoveredFuturePowerFamilies.family (reachable A original root)) where
  app point source :=
    ⟨predicate A original root point source, ⟨smallEnumeration A original enumerations root point source⟩⟩
  naturality {first second} step source := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro argument
    exact Iff.of_eq (congrArg (fun value : CoveredFuturePowerFamilies.Power A second =>
      value.val.holds ⟨argument.1, argument.2.val⟩) (original.naturality step source.val))

theorem coalgebra_truth (point : D) (source : (reachable A original root).obj point)
    (argument : CoveredFuturePowerFamilies.Arguments (reachable A original root) point) :
    ((coalgebra A original enumerations root).app point source).val.holds argument ↔
      (original.app point source.val).val.holds ⟨argument.1, argument.2.val⟩ := Iff.rfl

/-- Reachability is closed under every admitted original future child. -/
theorem future_closed (point : D) (source : (reachable A original root).obj point)
    (future : Future.Objects point) (argument : A.obj future.1)
    (available : (original.app point source.val).val.holds ⟨future, argument⟩) :
    Relation.ReflTransGen (ContextualGeneratedCoalgebras.Step A original) root ⟨future.1, argument⟩ :=
  source.property.tail (.inr ⟨future.2, available⟩)

/-- The monic reachable inclusion is a genuine coalgebra morphism for the
complete small-covered future power functor. -/
theorem inclusion_square :
    (coalgebra A original enumerations root).comp
      (CoveredFuturePowerFunctor.imageHom (inclusion A original root)) =
    (inclusion A original root).comp original := by
  apply NaturalHom.ext
  intro point source
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  intro argument
  constructor
  · rintro ⟨child, same, available⟩
    change (original.app point source.val).val.holds ⟨argument.1, child.val⟩ at available
    change child.val = argument.2 at same
    rw [same] at available
    exact available
  · intro available
    exact ⟨⟨argument.2, future_closed A original root point source argument.1 argument.2 available⟩,
      rfl, available⟩

theorem cover_surjective (point : D) :
    Function.Surjective ((cover A original enumerations root).app point) :=
  ContextualGeneratedCoalgebras.reachabilityCover_surjective A original enumerations root point

theorem cover_cancel {target : D ⥤ Type w}
    (first second : NaturalHom (reachable A original root) target)
    (same : (cover A original enumerations root).comp first =
      (cover A original enumerations root).comp second) : first = second := by
  apply NaturalHom.ext
  intro point argument
  obtain ⟨receipt, rfl⟩ := cover_surjective A original enumerations root point argument
  exact congrArg (fun operation : NaturalHom (generated A original enumerations root) target =>
    operation.app point receipt) same

/-- The cover lifts each future child at the same future context. The
lift preserves the whole reachable value, including its subtype proof. -/
theorem cover_future_iff (point : D) (source : (generated A original enumerations root).obj point)
    (future : Future.Objects point) (argument : (reachable A original root).obj future.1) :
    ((coalgebra A original enumerations root).app point
      ((cover A original enumerations root).app point source)).val.holds ⟨future, argument⟩ ↔
    ∃ child : (generated A original enumerations root).obj future.1,
      ((ContextualGeneratedCoalgebras.generatedCoalgebra A original enumerations root).app point source).val.holds
        ⟨future, child⟩ ∧ (cover A original enumerations root).app future.1 child = argument := by
  constructor
  · intro available
    obtain ⟨child, available, same⟩ :=
      (ContextualGeneratedCoalgebras.forward_cover A original enumerations root
        point source future argument.val).mp available
    exact ⟨child, available, Subtype.ext same⟩
  · rintro ⟨child, available, same⟩
    have values := congrArg Subtype.val same
    exact (ContextualGeneratedCoalgebras.forward_cover A original enumerations root
      point source future argument.val).mpr ⟨child, available, values⟩

theorem cover_square :
    (ContextualGeneratedCoalgebras.generatedCoalgebra A original enumerations root).comp
      (CoveredFuturePowerFunctor.imageHom (cover A original enumerations root)) =
    (cover A original enumerations root).comp (coalgebra A original enumerations root) := by
  apply NaturalHom.ext
  intro point source
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  intro argument
  constructor
  · rintro ⟨child, same, available⟩
    exact (cover_future_iff A original enumerations root point source argument.1 argument.2).mpr
      ⟨child, available, same⟩
  · intro available
    obtain ⟨child, available, same⟩ :=
      (cover_future_iff A original enumerations root point source argument.1 argument.2).mp available
    exact ⟨child, same, available⟩

theorem cover_inclusion :
    (cover A original enumerations root).comp (inclusion A original root) =
      ContextualGeneratedCoalgebras.endpoint A original enumerations root := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem cover_context {first second : D} (step : first ⟶ second)
    (source : (generated A original enumerations root).obj first) :
    (reachable A original root).map step ((cover A original enumerations root).app first source) =
      (cover A original enumerations root).app second ((generated A original enumerations root).map step source) :=
  (cover A original enumerations root).naturality step source

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReachableCoalgebras
