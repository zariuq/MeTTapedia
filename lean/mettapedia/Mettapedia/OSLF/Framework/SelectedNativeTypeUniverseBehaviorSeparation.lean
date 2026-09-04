import Mathlib.Data.Fintype.Prod
import Mettapedia.OSLF.Framework.CarrierUniverseSignature
import Mettapedia.OSLF.Framework.DerivedModalities

/-!
# Universe levels and behavioral modalities are independent

The selected native-type generator uses `CarrierUniverseSignature.Code.star`
and `CarrierUniverseSignature.Code.box` to fill local universe slots.  They
classify a generated former at the type or kind level.  Separately, a
reduction span induces the behavioral predicate transformers
`derivedDiamond` and `derivedBox`.

This module records the separation as a small diagnostic boundary.  The two
binary choices form four coordinates.  Projecting to either coordinate loses
information, and the behavioral operators are observably different on a
one-edge reduction span.  Consequently, interpreting the universe codes
themselves as the two behavioral operators would collapse distinct semantic
data.

No meaning for the generated formation, introduction, or elimination rules is
chosen here.  In particular, this diagnostic product does not say that both
behavioral endpoints belong in the generated profile.  It says only that a
behavioral operator cannot be selected by inspecting the universe code.  The
actual generated modality is subject to a separate semantic review.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SelectedNativeTypeUniverseBehaviorSeparation

open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities

/-- Which reduction-span predicate transformer is being observed.  This is
deliberately distinct from the generated universe-slot code. -/
inductive BehavioralEndpoint where
  | diamond
  | box
deriving Repr, DecidableEq

instance : Fintype BehavioralEndpoint :=
  Fintype.ofList [.diamond, .box] (by
    intro endpoint
    cases endpoint <;> simp)

/-- Interpret only the behavioral coordinate against a reduction span. -/
def BehavioralEndpoint.interpret {X : Type*} (span : ReductionSpan X) :
    BehavioralEndpoint -> (X -> Prop) -> X -> Prop
  | .diamond => derivedDiamond span
  | .box => derivedBox span

@[simp]
theorem BehavioralEndpoint.interpret_diamond {X : Type*}
    (span : ReductionSpan X) :
    BehavioralEndpoint.diamond.interpret span = derivedDiamond span :=
  rfl

@[simp]
theorem BehavioralEndpoint.interpret_box {X : Type*}
    (span : ReductionSpan X) :
    BehavioralEndpoint.box.interpret span = derivedBox span :=
  rfl

/-- A diagnostic coordinate keeps behavioral polarity and universe level as
independent data without asserting that both are generator inputs. -/
abbrev DiagnosticCoordinate :=
  BehavioralEndpoint × CarrierUniverseSignature.Code

def diamondStar : DiagnosticCoordinate :=
  (.diamond, .star)

def diamondBox : DiagnosticCoordinate :=
  (.diamond, .box)

def boxStar : DiagnosticCoordinate :=
  (.box, .star)

def boxBox : DiagnosticCoordinate :=
  (.box, .box)

/-- Two behavioral choices times two universe levels produce four distinct
coordinates, not two. -/
theorem diagnosticCoordinate_card : Fintype.card DiagnosticCoordinate = 4 := by
  decide

/-- Forgetting behavioral polarity collapses diamond-star and box-star. -/
theorem universeProjection_not_injective :
    ¬ (Function.Injective
      (fun coordinate : DiagnosticCoordinate => coordinate.2)) := by
  intro injective
  have equality : diamondStar = boxStar := injective rfl
  have endpointEquality := congrArg Prod.fst equality
  change BehavioralEndpoint.diamond = BehavioralEndpoint.box at endpointEquality
  cases endpointEquality

/-- Forgetting universe level collapses diamond-star and diamond-box. -/
theorem behaviorProjection_not_injective :
    ¬ (Function.Injective
      (fun coordinate : DiagnosticCoordinate => coordinate.1)) := by
  intro injective
  have equality : diamondStar = diamondBox := injective rfl
  have codeEquality := congrArg Prod.snd equality
  change CarrierUniverseSignature.Code.star =
    CarrierUniverseSignature.Code.box at codeEquality
  cases codeEquality

/-- The smallest reduction span with a genuine forward step. -/
def oneEdgeSpan : ReductionSpan Bool where
  Edge := Unit
  source _ := false
  target _ := true

/-- At the target of the one edge, diamond of truth is false: there is no
outgoing edge. -/
theorem oneEdge_diamond_true_at_target_fails :
    ¬ (BehavioralEndpoint.diamond.interpret oneEdgeSpan
      (fun _ => True) true) := by
  simp [BehavioralEndpoint.interpret, derivedDiamond, di, pb, oneEdgeSpan]

/-- At the same target, box of truth holds for its incoming edge. -/
theorem oneEdge_box_true_at_target_holds :
    BehavioralEndpoint.box.interpret oneEdgeSpan (fun _ => True) true := by
  simp [BehavioralEndpoint.interpret, derivedBox, ui, pb, oneEdgeSpan]

/-- The two behavioral operators are therefore not merely different names. -/
theorem oneEdge_behavioral_endpoints_distinct :
    BehavioralEndpoint.diamond.interpret oneEdgeSpan ≠
      BehavioralEndpoint.box.interpret oneEdgeSpan := by
  intro equality
  have pointEquality := congrArg
    (fun action => action (fun _ => True) true) equality
  exact oneEdge_diamond_true_at_target_fails
    (pointEquality.symm.mp oneEdge_box_true_at_target_holds)

/-- Changing only the universe coordinate leaves the selected behavioral
operator unchanged. -/
theorem same_diamond_different_universe {X : Type*}
    (span : ReductionSpan X) :
    diamondStar.1.interpret span = diamondBox.1.interpret span :=
  rfl

/-- Changing only the behavioral coordinate leaves the selected universe
level unchanged. -/
theorem same_star_different_behavior : diamondStar.2 = boxStar.2 :=
  rfl

#print axioms diagnosticCoordinate_card
#print axioms universeProjection_not_injective
#print axioms behaviorProjection_not_injective
#print axioms oneEdge_diamond_true_at_target_fails
#print axioms oneEdge_box_true_at_target_holds
#print axioms oneEdge_behavioral_endpoints_distinct
#print axioms same_diamond_different_universe
#print axioms same_star_different_behavior

end Mettapedia.OSLF.Framework.SelectedNativeTypeUniverseBehaviorSeparation
