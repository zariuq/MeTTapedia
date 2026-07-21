import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.BipartitePortfolio
import Lean.Data.Json.FromToJson

/-!
# Shared Python/Lean artifact conformance

The companion Python generator extracts a compact fixture from the sealed
program-corpus database.  This module parses the same JSON artifact and
independently recomputes its witness, repetition, Pareto, prefix-divergence,
and family-complementarity invariants.  The final `#eval` is a build gate: a
stale or invalid fixture raises an error rather than merely printing `false`.
-/

namespace Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery

structure FixtureProgram where
  program_id : String
  tokens : Array String
  token_count : Nat
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureObservation where
  observation_id : String
  program_id : String
  runtime : Nat
  token_count : Nat
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureCorpusMetadata where
  canonical_program_encoding : String
  key_space : String
  schema : String
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureTwoProgramsOneTarget where
  target : Nat
  programs : Array FixtureProgram
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureOneProgramTwoTargets where
  program : FixtureProgram
  targets : Array Nat
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureExactRepetition where
  authenticated_observation_id : String
  occurrences : Array String
  occurrence_count : Nat
  distinct_observation_count : Nat
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureShortestFastest where
  target : Nat
  source_lineage : String
  shortest : FixtureObservation
  fastest : FixtureObservation
  deriving Repr, DecidableEq, Lean.FromJson

structure FixturePareto where
  target : Nat
  members : Array FixtureObservation
  deriving Repr, DecidableEq, Lean.FromJson

structure FixturePrefixProgram extends FixtureProgram where
  outputs : Array Int
  deriving Repr, DecidableEq, Lean.FromJson

structure FixturePrefixDivergence where
  agreement_length : Nat
  left : FixturePrefixProgram
  right : FixturePrefixProgram
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureFamily where
  name : String
  target_coverage : Nat
  program_ids : Array String
  deriving Repr, DecidableEq, Lean.FromJson

structure FixtureFamilyComplementarity where
  target : Nat
  families : Array FixtureFamily
  ac_plus_tgad_witness_union : Nat
  ac_plus_tree_witness_union : Nat
  deriving Repr, DecidableEq, Lean.FromJson

structure ProgramDiscoveryConformanceFixture where
  schema : String
  corpus_metadata : FixtureCorpusMetadata
  two_programs_one_target : FixtureTwoProgramsOneTarget
  one_program_two_targets : FixtureOneProgramTwoTargets
  exact_repetition : FixtureExactRepetition
  shortest_fastest_disagreement : FixtureShortestFastest
  pareto_frontier : FixturePareto
  finite_prefix_divergence : FixturePrefixDivergence
  family_complementarity : FixtureFamilyComplementarity
  deriving Repr, DecidableEq, Lean.FromJson

def fixtureSchema : String := "oeis.program_discovery_conformance.v1"

def strictDominates (left right : FixtureObservation) : Bool :=
  decide (left.token_count ≤ right.token_count ∧ left.runtime ≤ right.runtime ∧
    (left.token_count < right.token_count ∨ left.runtime < right.runtime))

def paretoMembersValid (members : Array FixtureObservation) : Bool :=
  members.size ≥ 2 && members.all fun candidate ↦
    members.all fun other ↦ !(strictDominates other candidate)

def fixtureProgramValid (program : FixtureProgram) : Bool :=
  program.program_id.length = 64 && program.token_count = program.tokens.size

def familyComplementarityValid
    (value : FixtureFamilyComplementarity) : Bool :=
  match value.families[0]?, value.families[1]?, value.families[2]? with
  | some ac, some tgad, some tree =>
      value.families.size = 3 &&
      ac.name = "ac-nmt-scaled-luong-bilstm" &&
      tgad.name = "tgad" && tree.name = "tree-neural-network" &&
      value.families.all (fun family ↦ family.target_coverage = 1) &&
      value.ac_plus_tgad_witness_union =
        (ac.program_ids.toList ++ tgad.program_ids.toList).toFinset.card &&
      value.ac_plus_tree_witness_union =
        (ac.program_ids.toList ++ tree.program_ids.toList).toFinset.card &&
      value.ac_plus_tgad_witness_union ≠ value.ac_plus_tree_witness_union
  | _, _, _ => false

/-- Independent Lean validation of every invariant represented by the shared
artifact. -/
def programDiscoveryFixtureValid
    (fixture : ProgramDiscoveryConformanceFixture) : Bool :=
  let twoPrograms := fixture.two_programs_one_target.programs
  let multiTargets := fixture.one_program_two_targets.targets
  let repetition := fixture.exact_repetition
  let tradeoff := fixture.shortest_fastest_disagreement
  let divergence := fixture.finite_prefix_divergence
  fixture.schema = fixtureSchema &&
    fixture.corpus_metadata.schema = "oeis.program_corpus.sqlite.v1" &&
    twoPrograms.size = 2 && twoPrograms.all fixtureProgramValid &&
    (twoPrograms.map (fun program ↦ program.program_id)).toList.toFinset.card = 2 &&
    fixtureProgramValid fixture.one_program_two_targets.program &&
    multiTargets.toList.toFinset.card ≥ 2 &&
    repetition.occurrences.size = repetition.occurrence_count &&
    repetition.occurrences.toList.toFinset.card = repetition.distinct_observation_count &&
    repetition.occurrences.all (fun occurrence ↦
      occurrence = repetition.authenticated_observation_id) &&
    tradeoff.shortest.program_id ≠ tradeoff.fastest.program_id &&
    tradeoff.shortest.token_count < tradeoff.fastest.token_count &&
    tradeoff.fastest.runtime < tradeoff.shortest.runtime &&
    fixture.pareto_frontier.target = tradeoff.target &&
    paretoMembersValid fixture.pareto_frontier.members &&
    fixtureProgramValid divergence.left.toFixtureProgram &&
    fixtureProgramValid divergence.right.toFixtureProgram &&
    divergence.left.outputs.toList.take divergence.agreement_length =
      divergence.right.outputs.toList.take divergence.agreement_length &&
    divergence.left.outputs ≠ divergence.right.outputs &&
    familyComplementarityValid fixture.family_complementarity

def sharedFixturePath : System.FilePath :=
  "Mettapedia/MachineLearning/SearchGuidance/ProgramDiscovery/fixtures/oeis_program_discovery_v1.json"

def loadSharedProgramDiscoveryFixture : IO ProgramDiscoveryConformanceFixture := do
  let contents ← IO.FS.readFile sharedFixturePath
  let json ← IO.ofExcept (Lean.Json.parse contents)
  IO.ofExcept (Lean.fromJson? json)

def sharedProgramDiscoveryFixtureGate : IO String := do
  let fixture ← loadSharedProgramDiscoveryFixture
  if programDiscoveryFixtureValid fixture then
    pure "program-discovery shared fixture: PASS"
  else
    throw <| IO.userError "program-discovery shared fixture failed Lean conformance"

#eval sharedProgramDiscoveryFixtureGate

end Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery
