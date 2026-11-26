import Mettapedia.GSLT.LanguageDef.InferenceRelationComposition

/-! # A checked transport composition with distinct premise judgments -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChainTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open InferenceChecker InferenceRelationComposition
open Mettapedia.Machines.Specialization
open RelationComposition

inductive Stop where
  | east | hub | west
  deriving DecidableEq

inductive Leg where
  | rail | ferry
  deriving DecidableEq

private def stopLabel : Stop → String
  | .east => "East"
  | .hub => "Hub"
  | .west => "West"

def stopTerm (stop : Stop) : Pattern := .apply (stopLabel stop) []

private def grammar : LanguageDef := {
  name := "transport-chain"
  types := [TypeDecl.plain "Stop"]
  terms := ([.east, .hub, .west] : List Stop).map fun stop =>
    { label := stopLabel stop, category := "Stop", params := [], syntaxPattern := [] }
  equations := []
  rewrites := [] }

private def rail (first second : Pattern) : Pattern := .apply "Transport.Rail" [first, second]
private def ferry (first second : Pattern) : Pattern := .apply "Transport.Ferry" [first, second]
private def ride (first second : Pattern) : Pattern := .apply "Transport.Ride" [first, second]

private def railRule : RuleSchema := {
  id := ⟨"rail-east-hub"⟩
  metavariables := []
  premises := []
  conclusion := rail (stopTerm .east) (stopTerm .hub) }

private def ferryRule : RuleSchema := {
  id := ⟨"ferry-hub-west"⟩
  metavariables := []
  premises := []
  conclusion := ferry (stopTerm .hub) (stopTerm .west) }

def rideRule : RuleSchema := {
  id := ⟨"rail-then-ferry"⟩
  metavariables := [("target", 0), ("source", 0), ("middle", 0)]
  premises := [ferry (.fvar "middle") (.fvar "target"), rail (.fvar "source") (.fvar "middle")]
  conclusion := ride (.fvar "source") (.fvar "target") }

private def authored : CalculusLanguageDef := CalculusLanguageDef.extend grammar {
  judgments := [⟨"Transport.Rail", 2⟩, ⟨"Transport.Ferry", 2⟩, ⟨"Transport.Ride", 2⟩]
  rules := [railRule, ferryRule, rideRule] }

def definition : ValidatedCalculusLanguageDef := ⟨authored, by decide +kernel⟩

def schema : CompositionSchema Leg Stop where
  judgment expression source target :=
    let relation := match expression with
      | .base .rail => rail
      | .base .ferry => ferry
      | .chain _ _ => ride
    relation (stopTerm source) (stopTerm target)
  instanceAt _ _ source middle target := ⟨rideRule.id, [stopTerm target, stopTerm source, stopTerm middle]⟩
  premiseOrder _ _ _ _ _ := .rightFirst

def journey : Expr Leg := .chain (.base .rail) (.base .ferry)

theorem ride_applies (source middle target : Stop) :
    schema.Applies definition (.base .rail) (.base .ferry) source middle target := by
  apply instantiateRule?_eq_some_iff_application.mp
  cases source <;> cases middle <;> cases target <;> decide +kernel

def railProof : RawProof := .node ⟨railRule.id, []⟩ []
def ferryProof : RawProof := .node ⟨ferryRule.id, []⟩ []

def rideProof (middle : Stop) : RawProof :=
  schema.node (.base .rail) (.base .ferry) .east middle .west railProof ferryProof

private theorem ride_checked :
    checkRaw definition (schema.judgment journey .east .west) (rideProof .hub) = true := by
  change checkRaw definition (schema.judgment (.chain (.base .rail) (.base .ferry)) .east .west)
    (schema.node (.base .rail) (.base .ferry) .east .hub .west railProof ferryProof) = true
  rw [schema.check_node definition (ride_applies .east .hub .west)]
  decide +kernel

abbrev Ticket := String × RawProof

private def railTickets : List (Row Stop Ticket) :=
  [⟨.east, .hub, ("rail-1", railProof)⟩, ⟨.east, .hub, ("rail-2", railProof)⟩]

private def ferryTickets : List (Row Stop Ticket) :=
  [⟨.hub, .west, ("ferry-1", ferryProof)⟩]

private def materializedTicket (left right : Row Stop Ticket) : String × String × Option RawProof :=
  let row := link (liftRow left) (liftRow right)
  (left.evidence.1, right.evidence.1,
    (schema.materialize? definition Prod.snd journey row).map Derivation.erase)

private theorem materialized_hub (leftId rightId : String) :
    materializedTicket ⟨.east, .hub, (leftId, railProof)⟩ ⟨.hub, .west, (rightId, ferryProof)⟩ =
      (leftId, rightId, some (rideProof .hub)) := by
  change (leftId, rightId,
    (((materializeProof? definition (schema.judgment journey .east .west) (rideProof .hub)).bind
      (fun checked => some checked.val)).map Derivation.erase)) = _
  rw [materializeProof?_eq_some ride_checked]
  change (leftId, rightId, some (reconstruct _ ride_checked).val.erase) = _
  rw [(reconstruct _ ride_checked).property]

/-- Two occurrences of the same rail proof remain two checked outputs. -/
theorem two_witnesses_materialized :
    ((prepared PathJoin.functional railTickets ferryTickets .east .west).map fun (left, right) =>
      materializedTicket left right) =
      [("rail-1", "ferry-1", some (rideProof .hub)), ("rail-2", "ferry-1", some (rideProof .hub))] := by
  rw [prepared_eq_compose]
  change [materializedTicket ⟨.east, .hub, ("rail-1", railProof)⟩ ⟨.hub, .west, ("ferry-1", ferryProof)⟩,
    materializedTicket ⟨.east, .hub, ("rail-2", railProof)⟩ ⟨.hub, .west, ("ferry-1", ferryProof)⟩] = _
  rw [materialized_hub, materialized_hub]

/-- The altered middle instantiates the same rule, but its ordered premises
cannot be discharged by the original rail and ferry proofs. -/
theorem wrong_middle_rejected :
    materializeProof? definition (schema.judgment journey .east .west) (rideProof .east) = none := by
  have refused : checkRaw definition (schema.judgment journey .east .west) (rideProof .east) = false := by
    change checkRaw definition (schema.judgment (.chain (.base .rail) (.base .ferry)) .east .west)
      (schema.node (.base .rail) (.base .ferry) .east .east .west railProof ferryProof) = false
    exact schema.changed_middle_rejected definition (ride_applies .east .east .west)
      (middle := .hub) ferryProof (by decide +kernel) (by decide +kernel)
  simp [materializeProof?, refused]

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.TransformChainTransport
