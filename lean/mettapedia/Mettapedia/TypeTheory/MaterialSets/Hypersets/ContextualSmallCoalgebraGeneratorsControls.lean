import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraGenerators
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotientControls

/-!
# Universal small-coalgebra readings on the infinite labelled context site

Infinitely many declared results have empty present children and distinct
universal readouts. A one-loop and a two-cycle have equal universal readouts
through their actual coalgebra map. Raw two-cycle receipts remain distinct.

These instantiate the general unique-map and exact-kernel theorems for
all small source coalgebras. They do not assert a final map for every
larger source or collapse the original receipt type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraGeneratorsControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open ContextualSmallCoalgebraGenerators LabelledContextPaths
open Mettapedia.TypeTheory.ContextualWitnessCover

namespace Results

abbrev states := ContextualCoalgebraQuotientControls.Results.states
abbrev original := ContextualCoalgebraQuotientControls.Results.coalgebra
abbrev result := ContextualCoalgebraQuotientControls.Results.result

def code : Code World := ⟨states, original⟩

theorem universal_results_injective : Function.Injective
    (fun tag => (canonical code).app initial (result tag)) := by
  intro first second same
  exact (ContextualCoalgebraQuotientControls.Results.result_bisimilar_iff first second).mp
    ((canonical_eq_iff code initial _ _).mp same)

theorem universal_distinguishes_declared_results :
    (canonical code).app initial (result 0) ≠ (canonical code).app initial (result 1) :=
  fun same => Nat.zero_ne_one (universal_results_injective same)

theorem distinct_results_empty_present (first second : Nat) (argument : states.obj initial) :
    ¬ (original.app initial (result first)).val.holds (current states initial argument) ∧
      ¬ (original.app initial (result second)).val.holds (current states initial argument) :=
  ⟨ContextualCoalgebraQuotientControls.Results.no_present_children first argument,
    ContextualCoalgebraQuotientControls.Results.no_present_children second argument⟩

theorem actual_result_coalgebra_square :
    original.comp (imageHom (canonical code)) = (canonical code).comp quotientCoalgebra :=
  canonical_square code

end Results

namespace Cycles

def one : World ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def two : World ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def oneChildren (point : World) : Predicate one point where
  holds _ := True
  closed _ _ := trivial

def twoChildren (point : World) (tag : Bool) : Predicate two point where
  holds argument := argument.2 = (!tag)
  closed {first second} move admitted := by
    have same : first.2 = second.2 := move.2
    exact same.symm.trans admitted

def oneCoalgebra : NaturalHom one (family one) where
  app point _ := ⟨oneChildren point, ⟨smallEnumeration (oneChildren point)⟩⟩
  naturality _ _ := rfl

def twoCoalgebra : NaturalHom two (family two) where
  app point tag := ⟨twoChildren point tag, ⟨smallEnumeration (twoChildren point tag)⟩⟩
  naturality _ _ := rfl

def collapse : NaturalHom two one where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

theorem collapse_square : twoCoalgebra.comp (imageHom collapse) = collapse.comp oneCoalgebra := by
  apply NaturalHom.ext
  intro point tag
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨(!tag), ?_, rfl⟩
    change (PUnit.unit : PUnit) = argument.2
    exact Subsingleton.elim _ _

def oneCode : Code World := ⟨one, oneCoalgebra⟩
def twoCode : Code World := ⟨two, twoCoalgebra⟩

theorem collapse_canonical_square :
    twoCoalgebra.comp (imageHom (collapse.comp (canonical oneCode))) =
      (collapse.comp (canonical oneCode)).comp quotientCoalgebra := by
  apply NaturalHom.ext
  intro point tag
  have collapsed : imagePower collapse point (twoCoalgebra.app point tag) =
      oneCoalgebra.app point PUnit.unit :=
    congrArg (fun map : NaturalHom two (family one) => map.app point tag) collapse_square
  have observed : imagePower (canonical oneCode) point (oneCoalgebra.app point PUnit.unit) =
      quotientCoalgebra.app point ((canonical oneCode).app point PUnit.unit) :=
    congrArg (fun map : NaturalHom one (family (quotient (D := World))) => map.app point PUnit.unit)
      (canonical_square oneCode)
  exact (imagePower_comp collapse (canonical oneCode) point (twoCoalgebra.app point tag)).symm.trans
    ((congrArg (imagePower (canonical oneCode) point) collapsed).trans observed)

theorem two_cycle_agrees_with_one_loop : canonical twoCode = collapse.comp (canonical oneCode) :=
  maps_equal_into_separated twoCoalgebra quotientCoalgebra (canonical twoCode)
    (collapse.comp (canonical oneCode)) (canonical_square twoCode) collapse_canonical_square quotient_separated

theorem all_cycle_readings_equal (point : World) (tag : Bool) :
    (canonical twoCode).app point tag = (canonical oneCode).app point PUnit.unit :=
  congrArg (fun map : NaturalHom two (quotient (D := World)) => map.app point tag)
    two_cycle_agrees_with_one_loop

theorem raw_cycle_receipts_distinct : (true : two.obj initial) ≠ false := by decide

theorem no_universal_decoder_recovers_both_receipts :
    ¬ ∃ decode : (quotient (D := World)).obj initial → Bool,
      ∀ tag, decode ((canonical twoCode).app initial tag) = tag := by
  rintro ⟨decode, recovers⟩
  apply raw_cycle_receipts_distinct
  exact (recovers true).symm.trans
    ((congrArg decode ((all_cycle_readings_equal initial true).trans
      (all_cycle_readings_equal initial false).symm)).trans (recovers false))

end Cycles

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraGeneratorsControls
