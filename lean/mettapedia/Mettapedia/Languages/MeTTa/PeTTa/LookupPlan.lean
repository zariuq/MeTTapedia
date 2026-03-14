import MeTTailCore

namespace Mettapedia.Languages.MeTTa.PeTTa.LookupPlan

open MeTTailCore.MeTTaIL.LookupPlan

private def argB (pos : Nat) : SignatureArg :=
  { position := pos, mode := .bound }

private def argF (pos : Nat) : SignatureArg :=
  { position := pos, mode := .free }

/-- Minimal PeTTa lookup-family contract for `match` over space facts.
This is the first shared shape for runtime indexing, not full translator parity. -/
def pettaSpaceMatchFamily : LookupFamilyPlan :=
  { family := "spaceMatch"
    logicalRelationId := "petta.space_match"
    factRelation := "selfFact"
    rawRelation := "spaceMatchRaw"
    hasRelation := "spaceMatchHas"
    resultRelation := some "spaceMatchResult"
    queryArity := 3
    payloadArity := 1
    keyPositions := [0, 1]
    demand :=
      [ { relation := "match"
          logicalRelationId := "petta.space_match.result"
          scopeSignature := "b0+b1+f2"
          arity := 3
          args := [argB 0, argB 1, argF 2]
          usageKind := .enumerate
          hotPath := true }
      , { relation := "find"
          logicalRelationId := "petta.space_match.has"
          scopeSignature := "b0+b1"
          arity := 2
          args := [argB 0, argB 1]
          usageKind := .exists
          hotPath := true }
      ]
    contracts :=
      { noFalseNegatives := true
        exactResult := false
        stratifiedNegationSafe := true } }

/-- Minimal PeTTa lookup-family contract for `(get-atoms &self)`.

This is the direct "enumerate all current facts" sibling of `spaceMatch`. -/
def pettaGetAtomsFamily : LookupFamilyPlan :=
  { family := "selfFacts"
    logicalRelationId := "petta.self_facts"
    factRelation := "selfFact"
    rawRelation := "selfFactRaw"
    hasRelation := "selfFactHas"
    resultRelation := some "selfFactResult"
    queryArity := 1
    payloadArity := 1
    keyPositions := [0]
    demand :=
      [ { relation := "get-atoms"
          logicalRelationId := "petta.self_facts.result"
          scopeSignature := "b0+f1"
          arity := 2
          args := [argB 0, argF 1]
          usageKind := .enumerate
          hotPath := true }
      , { relation := "get-atoms-has"
          logicalRelationId := "petta.self_facts.has"
          scopeSignature := "b0"
          arity := 1
          args := [argB 0]
          usageKind := .exists
          hotPath := true }
      ]
    contracts :=
      { noFalseNegatives := true
        exactResult := true
        stratifiedNegationSafe := true } }

def pettaLookupPlanArtifact : LookupPlanArtifact :=
  { schemaVersion := 2
    dialect := "petta"
    families := [pettaSpaceMatchFamily, pettaGetAtomsFamily] }

def lookupPlanByDialect? (dialect : String) : Option (String × LookupPlanArtifact) :=
  if dialect = "petta" then
    some ("petta", pettaLookupPlanArtifact)
  else
    none

end Mettapedia.Languages.MeTTa.PeTTa.LookupPlan
