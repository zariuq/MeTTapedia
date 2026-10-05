import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerFamilies
import Mettapedia.TypeTheory.ContextualWitnessCover

/-!
# The full-future Russell obstruction at the original small bound

Every stable predicate on an originally small family has a constructed small
truth enumeration. A natural right inverse to a coalgebra into this full
covered power would therefore represent the stable predicate saying that an
argument is not its own member at any later context. Naturality makes its
represented value a compatible section, and yields a contradiction.

The proof uses the complete future predicate and actual restriction arrows.
It is constructive and applies at every inhabited site. It rules out an
originally small full-power fixed point; it does not rule out the wider
receipt-covered recipients whose predicates have a separate small bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructivePowerFinalityObstruction

open CategoryTheory ContextualWitnessCover
open CoveredFuturePowerFamilies

universe u
variable {D : Type u} [Category.{u} D]
variable (A : D ⥤ Type u) (coalgebra : NaturalHom A (family A))

/-- Negated self-membership must hold after every subsequent restriction. -/
def russell (point : D) : Predicate A point where
  holds argument := ∀ (later : D) (step : argument.1.1 ⟶ later),
    ¬ (coalgebra.app later (A.map step argument.2)).val.holds
      (current A later (A.map step argument.2))
  closed {first second} move absent := by
    intro later step available
    have valueLaw : A.map move.1.1 first.2 = second.2 := move.2
    have composite : A.map (move.1.1 ≫ step) first.2 = A.map step second.2 :=
      (congrArg (fun map => map first.2) (A.map_comp move.1.1 step)).trans
        (congrArg (A.map step) valueLaw)
    apply absent later (move.1.1 ≫ step)
    rw [composite]
    exact available

theorem russell_restrict {first second : D} (step : first ⟶ second) :
    restrict A step (russell A coalgebra first) = russell A coalgebra second := by
  apply Predicate.ext
  intro argument
  exact Iff.rfl

/-- Its complete truth subtype supplies the receipt data at the original bound. -/
def russellPower (point : D) : Power A point :=
  ⟨russell A coalgebra point, ⟨smallEnumeration (russell A coalgebra point)⟩⟩

theorem russellPower_restrict {first second : D} (step : first ⟶ second) :
    restrictPower A step (russellPower A coalgebra first) =
      russellPower A coalgebra second :=
  Subtype.ext (russell_restrict A coalgebra step)

def russellSection : (family A).sections :=
  ⟨russellPower A coalgebra, fun step => russellPower_restrict A coalgebra step⟩

variable (assemble : NaturalHom (family A) A)

def representedSection : A.sections :=
  assemble.mapSection (russellSection A coalgebra)

/-- A right inverse for every full power element cannot exist at an inhabited
site. No enumeration selector, excluded middle or cardinal arithmetic is used. -/
theorem no_natural_right_inverse (point : D)
    (inverse : ∀ world (predicate : Power A world),
      coalgebra.app world (assemble.app world predicate) = predicate) : False := by
  let represented := representedSection A coalgebra assemble
  have reading (world : D) :
      coalgebra.app world (represented.val world) = russellPower A coalgebra world :=
    inverse world (russellPower A coalgebra world)
  have absent (world : D) :
      ¬ (coalgebra.app world (represented.val world)).val.holds
        (current A world (represented.val world)) := by
    intro selfMember
    have diagonal := selfMember
    rw [reading world] at diagonal
    change ∀ later (step : world ⟶ later),
      ¬ (coalgebra.app later (A.map step (represented.val world))).val.holds
        (current A later (A.map step (represented.val world))) at diagonal
    have atIdentity := diagonal world (𝟙 world)
    have identity : A.map (𝟙 world) (represented.val world) = represented.val world :=
      congrArg (fun map => map (represented.val world)) (A.map_id world)
    rw [identity] at atIdentity
    exact atIdentity selfMember
  apply absent point
  rw [reading point]
  change ∀ later (step : point ⟶ later),
    ¬ (coalgebra.app later (A.map step (represented.val point))).val.holds
      (current A later (A.map step (represented.val point)))
  intro later step
  rw [represented.property step]
  exact absent later

theorem no_natural_power_fixed_point (point : D) :
    ¬ ∃ assemble : NaturalHom (family A) A,
      ∀ world (predicate : Power A world),
        coalgebra.app world (assemble.app world predicate) = predicate := by
  rintro ⟨assemble, inverse⟩
  exact no_natural_right_inverse A coalgebra assemble point inverse

theorem no_natural_power_equivalence (point : D) :
    ¬ ∃ assemble : NaturalHom (family A) A,
      (∀ world (predicate : Power A world),
        coalgebra.app world (assemble.app world predicate) = predicate) ∧
      (∀ world (argument : A.obj world),
        assemble.app world (coalgebra.app world argument) = argument) := by
  rintro ⟨assemble, inverse, _⟩
  exact no_natural_right_inverse A coalgebra assemble point inverse

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructivePowerFinalityObstruction
