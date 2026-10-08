import Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionSubstitution
import Mettapedia.TypeTheory.DisplayedPresheafProductTransformationCoherenceControls

/-!
# Context-sensitive mixed-substitution controls

Context witnesses vary along multiplying world arrows. Squaring the world
arrows and multiplying the supplied program witness are genuinely different
operations. Both native Π routes retain the full argument-dependent result;
omitting the program substitution changes its readout.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionSubstitutionControls

open _root_.CategoryTheory _root_.CategoryTheory.Functor
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafPi DisplayedPresheafSlicePi DisplayedPresheafPiSubstitution
open DisplayedPresheafIndexedCwfBridge DependentProductNativeComparison
open DisplayedPresheafSliceSubstitution
open DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryRestrictionAction
open DisplayedPresheafProductRestrictionSubstitution
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open DisplayedPresheafProductTransformationCoherenceControls.Covered

abbrev Worlds := ScalarWorlds
abbrev programs := scalarContext

def squareWorlds : Worlds ⥤ Worlds := SingleObj.mapHom Nat Nat
  { toFun := fun number => number ^ 2
    map_one' := rfl
    map_mul' := fun first second => Nat.mul_pow first second 2 }

def substituteProgram (factor : Nat) : programs ⟶ programs where
  app _ := TypeCat.ofHom (fun parameter => Nat.mul factor parameter)
  naturality _ _ arrow := by
    ext parameter
    change Nat.mul factor (Nat.mul arrow.unop parameter) =
      Nat.mul arrow.unop (Nat.mul factor parameter)
    exact Nat.mul_left_comm factor arrow.unop parameter

def arguments : DisplayedFamily programs := (Functor.const _).obj Nat

def results : DisplayedFamily (totalSpace arguments) :=
  CategoryOfElements.π (totalSpace arguments) ⋙ programs

def sourceSection (point : programs.Elements) :
    DependentSection arguments (displayedToTotalElements arguments ⋙ results) point where
  app _ arrow argument := Nat.mul arrow.val.unop (Nat.mul point.2 argument)
  naturality later arrow argument := by
    change Nat.mul
        (((displayedToTotalElements arguments).map (argumentMap arguments later argument)).val.unop)
        (Nat.mul arrow.val.unop (Nat.mul point.2 argument)) = _
    rw [displayedToTotalElements_underlying]
    change Nat.mul later.val.unop (Nat.mul arrow.val.unop (Nat.mul point.2 argument)) =
      Nat.mul (Nat.mul arrow.val.unop later.val.unop) (Nat.mul point.2 argument)
    exact (Nat.mul_left_comm later.val.unop arrow.val.unop (Nat.mul point.2 argument)).trans
      (Nat.mul_assoc arrow.val.unop later.val.unop (Nat.mul point.2 argument)).symm

noncomputable def sourceFunction (point : programs.Elements) :
    (piDisplayed arguments results).obj point :=
  ((nativeIso arguments).inv.app (displayedToTotalElements arguments ⋙ results)).app
    point (sourceSection point)

theorem sourceFunction_readout (point future : programs.Elements) (arrow : point ⟶ future)
    (argument : arguments.obj future) :
    ((((nativeIso arguments).hom.app (displayedToTotalElements arguments ⋙ results)).app
      point (sourceFunction point)).app future arrow argument) =
      Nat.mul arrow.val.unop (Nat.mul point.2 argument) := by
  have inverse := congrArg (fun operation => operation.app point (sourceSection point))
    ((nativeIso arguments).inv_hom_id_app (displayedToTotalElements arguments ⋙ results))
  exact congrArg (fun functionValue :
    DependentSection arguments (displayedToTotalElements arguments ⋙ results) point =>
      functionValue.app future arrow argument) inverse

def programPoint (parameter : Nat) : (squareWorlds.op ⋙ programs).Elements :=
  ⟨Opposite.op (SingleObj.star Nat), parameter⟩

def futureArrow (parameter factor : Nat) :
    programPoint parameter ⟶ programPoint (factor ^ 2 * parameter) :=
  CategoryOfElements.homMk _ _
    ((show SingleObj.star Nat ⟶ SingleObj.star Nat from factor).op) rfl

abbrev targetDomain (factor : Nat) := restrictFamily squareWorlds programs
  (reindexDisplayed (substituteProgram factor) arguments)

abbrev targetBody (factor : Nat) := reindexDisplayed
  (totalReindexMap (whiskerLeft squareWorlds.op (substituteProgram factor))
    (restrictFamily squareWorlds programs arguments))
  ((codomainFunctor squareWorlds programs arguments).obj results)

noncomputable def programFirst (factor : Nat) :=
  (restrictionFunctor squareWorlds programs).map (piSubstitutionIso (substituteProgram factor)
    arguments results).inv ≫
  productComparison squareWorlds programs (reindexDisplayed (substituteProgram factor) arguments)
    (reindexDisplayed (totalReindexMap (substituteProgram factor) arguments) results) ≫
  (displayedProductFunctor (targetDomain factor)).map
    (eqToHom (codomain_interchange squareWorlds (substituteProgram factor) arguments results))

noncomputable def theoryFirst (factor : Nat) :=
  (reindexFunctor (whiskerLeft squareWorlds.op (substituteProgram factor))).map
    (productComparison squareWorlds programs arguments results) ≫
  (piSubstitutionIso (whiskerLeft squareWorlds.op (substituteProgram factor))
    (restrictFamily squareWorlds programs arguments)
    ((codomainFunctor squareWorlds programs arguments).obj results)).inv

theorem complete_maps_commute (factor : Nat) : programFirst factor = theoryFirst factor :=
  comparison_substitution squareWorlds (substituteProgram factor) arguments results

noncomputable def mixedReadout (factor parameter futureFactor argument : Nat) : Nat :=
  ((((nativeIso (targetDomain factor)).hom.app
      (displayedToTotalElements (targetDomain factor) ⋙ targetBody factor)).app
    (programPoint parameter)
    ((programFirst factor).app (programPoint parameter)
      (sourceFunction ((substituteProgram factor).mapElements.obj
        ((Functor.Elements.precomp squareWorlds.op programs).obj (programPoint parameter)))))).app
    (programPoint (futureFactor ^ 2 * parameter)) (futureArrow parameter futureFactor) argument)

set_option backward.isDefEq.respectTransparency false in
theorem mixedReadout_value (factor parameter futureFactor argument : Nat) :
    mixedReadout factor parameter futureFactor argument =
      futureFactor ^ 2 * (factor * parameter * argument) := by
  unfold mixedReadout programFirst
  have readout := program_then_theory_readout squareWorlds (substituteProgram factor)
    arguments results (programPoint parameter) (programPoint (futureFactor ^ 2 * parameter))
    (futureArrow parameter futureFactor)
    (sourceFunction ((substituteProgram factor).mapElements.obj
      ((Functor.Elements.precomp squareWorlds.op programs).obj (programPoint parameter)))) argument
  exact readout.trans (sourceFunction_readout _ _ _ argument)

noncomputable def theoryReadout (factor parameter futureFactor argument : Nat) : Nat :=
  ((((nativeIso (targetDomain factor)).hom.app
      (displayedToTotalElements (targetDomain factor) ⋙ targetBody factor)).app
    (programPoint parameter)
    ((theoryFirst factor).app (programPoint parameter)
      (sourceFunction ((substituteProgram factor).mapElements.obj
        ((Functor.Elements.precomp squareWorlds.op programs).obj (programPoint parameter)))))).app
    (programPoint (futureFactor ^ 2 * parameter)) (futureArrow parameter futureFactor) argument)

set_option backward.isDefEq.respectTransparency false in
/-- The second route is read directly through its own chosen comparison;
its value computation does not appeal to equality of the two routes. -/
theorem theoryReadout_value (factor parameter futureFactor argument : Nat) :
    theoryReadout factor parameter futureFactor argument =
      futureFactor ^ 2 * (factor * parameter * argument) := by
  unfold theoryReadout theoryFirst
  have readout := theory_then_program_readout squareWorlds (substituteProgram factor)
    arguments results (programPoint parameter) (programPoint (futureFactor ^ 2 * parameter))
    (futureArrow parameter futureFactor)
    (sourceFunction ((substituteProgram factor).mapElements.obj
      ((Functor.Elements.precomp squareWorlds.op programs).obj (programPoint parameter)))) argument
  exact readout.trans (sourceFunction_readout _ _ _ argument)

theorem both_actual_readouts_agree (factor parameter futureFactor argument : Nat) :
    mixedReadout factor parameter futureFactor argument =
      theoryReadout factor parameter futureFactor argument :=
  (mixedReadout_value factor parameter futureFactor argument).trans
    (theoryReadout_value factor parameter futureFactor argument).symm

theorem actual_world_route :
    (show Nat from squareWorlds.map
      (show SingleObj.star Nat ⟶ SingleObj.star Nat from (3 : Nat))) = 9 := rfl

theorem actual_program_substitution :
    (show Nat from (substituteProgram 2).app
      (Opposite.op (SingleObj.star Nat)) (3 : Nat)) = 6 := rfl

/-- A nonidentity world route and program substitution both change the
readout, while every supplied argument remains observable. -/
theorem nonconstant_mixed_readout : mixedReadout 2 3 2 5 = 120 := by
  rw [mixedReadout_value]
  decide

theorem distinct_arguments_retained : mixedReadout 2 3 2 5 ≠ mixedReadout 2 3 2 6 := by
  rw [mixedReadout_value, mixedReadout_value]
  decide

theorem distinct_program_witnesses_retained : mixedReadout 2 3 2 5 ≠ mixedReadout 2 4 2 5 := by
  rw [mixedReadout_value, mixedReadout_value]
  decide

/-- Dropping the actual program comparison gives a different function
readout. A theory-only map is insufficient for the mixed contract. -/
theorem omitting_program_substitution_changes_readout :
    mixedReadout 2 3 2 5 ≠ mixedReadout 1 3 2 5 := by
  rw [mixedReadout_value, mixedReadout_value]
  decide

/-- Keeping the original multiplying arrow instead of its actual squared
image also changes the supplied function's future-argument readout. -/
theorem omitting_theory_arrow_action_changes_readout :
    mixedReadout 2 3 2 5 ≠ 2 * (2 * 3 * 5) := by
  rw [mixedReadout_value]
  decide

end Mettapedia.TypeTheory.DisplayedPresheafProductRestrictionSubstitutionControls
