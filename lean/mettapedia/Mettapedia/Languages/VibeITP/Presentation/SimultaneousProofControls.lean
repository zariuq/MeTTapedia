import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofQualification
import Mettapedia.Languages.VibeITP.Native.ProtocolV2PresentedReadback
import Mettapedia.Languages.VibeITP.Presentation.ProofWitnessCodec
import Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch

/-! Supplied-witness, mixed-certificate and physical-export controls. Each
request's expected result is computed by the independent witness checker.
Explicit positive and negative laws additionally bind the important fixtures
to their authored results and to the actual admitted byte-run theory. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2.Controls

open ComputationalData ComputationalShift ComputationalProofs ComputationalLiterals
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

namespace Primary
abbrev theory := SimultaneousPresentation.Controls.theory
abbrev allocated := SimultaneousPresentation.Controls.allocated
abbrev hosted := SimultaneousPresentation.Controls.hosted
abbrev F := SimultaneousPresentation.Controls.F
abbrev G := SimultaneousPresentation.Controls.G
abbrev D := SimultaneousPresentation.Controls.D
abbrev f := SimultaneousPresentation.Controls.f
abbrev g := SimultaneousPresentation.Controls.g
abbrev source := SimultaneousPresentation.Controls.source
abbrev crossing := SimultaneousPresentation.Controls.crossing
end Primary

def original : SimultaneousProofs.Witness := .base (.definition 0 [0, 1])
def crossingWitness : SimultaneousProofs.Witness :=
  .instantiateMany [(Primary.F, Primary.g), (Primary.G, .natLit 7)] original
def swapWitness : SimultaneousProofs.Witness :=
  .instantiateMany [(Primary.F, Primary.g), (Primary.G, Primary.f)] original
def duplicateWitness : SimultaneousProofs.Witness :=
  .instantiateMany [(Primary.F, Primary.g), (Primary.F, .natLit 7)] original
def unformedShadow : SimultaneousProofs.Witness :=
  .instantiateMany [(Primary.F, Primary.g), (Primary.F, .app (.fresh 99) [])] original
def subsequentWitness : SimultaneousProofs.Witness :=
  .instantiateMany [(Primary.G, .natLit 8)] crossingWitness

def crossingLeaf : Leaf SimultaneousProofs.Witness Spec.Term := ⟨crossingWitness, Primary.crossing, 512⟩

theorem crossing_checked : SimultaneousProofs.Witness.check Primary.theory crossingWitness Primary.crossing = true := by
  decide +kernel

theorem crossing_query_computes :
    Applies wholeProgram productDivisionHost "vibe:proof-v2-query"
      (queryArguments Primary.theory Primary.allocated crossingWitness)
      (encodeResult (some Primary.crossing)) := by
  have sourceChecked := (SimultaneousProofs.Witness.check_iff _ _ _).mp crossing_checked
  simpa only [queryArguments, theoryOf_allocatedSnapshot Primary.hosted, sourceChecked.eval] using
    proofQuery_computes (allocatedSnapshot Primary.theory Primary.allocated)
      Primary.theory.axioms Primary.theory.definitions crossingWitness

theorem crossing_guest_checks :
    Applies wholeProgram productDivisionHost "vibe:check-proof-v2"
      (queryArguments Primary.theory Primary.allocated crossingWitness ++ [encode Primary.crossing]) (.sym "True") :=
  (authored_kernel_exact Primary.hosted crossingWitness Primary.crossing).mpr
    ((SimultaneousProofs.Witness.check_iff _ _ _).mp crossing_checked)

theorem crossing_codec_roundtrip :
    ProofWitnessCodec.simultaneous (encodeWitness crossingWitness) = some crossingWitness :=
  ProofWitnessCodec.simultaneous_encoded crossingWitness

theorem legacy_proof_outcomes_preserved (fuel : Nat) :
    apply wholeProgram productDivisionHost fuel "vibe:proof-query"
      [encodeTable (allocatedSnapshot Primary.theory Primary.allocated), encodeAxioms Primary.theory.axioms,
        encodeDefinitions Primary.theory.definitions, ComputationalProofs.encodeWitness (.definition 0 [0, 1])] =
    apply proofProgram productDivisionHost fuel "vibe:proof-query"
      [encodeTable (allocatedSnapshot Primary.theory Primary.allocated), encodeAxioms Primary.theory.axioms,
        encodeDefinitions Primary.theory.definitions, ComputationalProofs.encodeWitness (.definition 0 [0, 1])] :=
  old_proof_execution fuel "vibe:proof-query" (by decide +kernel) _

theorem legacy_simultaneous_outcomes_preserved (fuel : Nat) :
    apply wholeProgram productDivisionHost fuel "vibe:thm-instantiate-many"
      [encodeTable (allocatedSnapshot Primary.theory Primary.allocated),
        ComputationalSimultaneous.encodeReplacements SimultaneousPresentation.Controls.replacements, encode Primary.source] =
    apply ComputationalSimultaneous.simultaneousProgram computationalHost fuel "vibe:thm-instantiate-many"
      [encodeTable (allocatedSnapshot Primary.theory Primary.allocated),
        ComputationalSimultaneous.encodeReplacements SimultaneousPresentation.Controls.replacements, encode Primary.source] :=
  old_simultaneous_execution fuel "vibe:thm-instantiate-many" (by decide +kernel) _

private def primitiveGoal := jPSucc cP1 (cPO cP1)
private def primitiveReport := FirstOrderPremiseSearch.search SimultaneousPresentation.rulesV2
  primitiveGoal none ⟨100, 4, 64⟩

theorem actual_module_accepts_search_candidate :
    (FirstOrderPremiseSearch.checkedCandidate SimultaneousPresentation.fixedValidatedV2
      primitiveGoal primitiveReport).isSome = true := by decide +kernel

theorem actual_search_candidate_derives :
    Nonempty (Derivation SimultaneousPresentation.fixedValidatedV2 primitiveGoal) :=
  FirstOrderPremiseSearch.checkedCandidate_sound _ _ _ actual_module_accepts_search_candidate

theorem zero_fuel_is_exhaustion :
    SimultaneousProofs.Witness.Checks Primary.theory crossingWitness Primary.crossing ∧
      apply wholeProgram productDivisionHost 0 "vibe:proof-v2-query"
        (queryArguments Primary.theory Primary.allocated crossingWitness) = .exhausted :=
  ⟨(SimultaneousProofs.Witness.check_iff _ _ _).mp crossing_checked,
    by rw [whole_apply _ (by decide +kernel)]; rfl⟩

theorem actual_byte_run_accepts_supplied_witness :
    SimultaneousProofs.Witness.check Native.ProtocolV2LogicalControls.finalState.theory
      crossingWitness Spec.ProtocolV2.Controls.crossingResult = true :=
  Native.ProtocolV2PresentedReadback.supplied_witness_transports crossingWitness crossing_checked

def implicationLeaf : Leaf SimultaneousProofs.Witness Spec.Term :=
  ⟨.base (.axiom 0), .impl KernelControls.atomA KernelControls.atomB, 128⟩
def premiseLeaf : Leaf SimultaneousProofs.Witness Spec.Term :=
  ⟨.base (.axiom 1), KernelControls.atomA, 128⟩
def mixedProof : CompactProof (Leaf SimultaneousProofs.Witness Spec.Term) :=
  .node ⟨⟨rMp.id⟩, KernelControls.mpArguments⟩ [.computed implicationLeaf, .computed premiseLeaf]

def composedMP : SimultaneousProofs.Witness := .modusPonens
  (.instantiateMany [(.fresh 0, .natLit 5), (.fresh 1, .natLit 9)] (.base (.axiom 0)))
  (.instantiateMany [(.fresh 0, .natLit 5)] (.base (.axiom 1)))

theorem composed_children_checked :
    SimultaneousProofs.Witness.check KernelControls.controlTheory composedMP (.natLit 9) = true := by decide +kernel

structure Request where
  name : String
  head : String
  arguments : List Term
  expected : Outcome
  fuel : Nat := 512

def queryRequest (name : String) (theory : Spec.Theory) (allocated : Nat)
    (witness : SimultaneousProofs.Witness) : Request :=
  ⟨name, "vibe:proof-v2-query", queryArguments theory allocated witness,
    .value (encodeResult (witness.result theory)), 512⟩

def checkRequest (name : String) (theory : Spec.Theory) (allocated : Nat)
    (witness : SimultaneousProofs.Witness) (claimed : Spec.Term) : Request :=
  ⟨name, "vibe:check-proof-v2", queryArguments theory allocated witness ++ [encode claimed],
    .value (boolean (SimultaneousProofs.Witness.check theory witness claimed)), 512⟩

private def primary (name : String) (witness : SimultaneousProofs.Witness) : Request :=
  queryRequest name Primary.theory Primary.allocated witness

private def secondary (name : String) (witness : SimultaneousProofs.Witness) : Request :=
  queryRequest name KernelControls.controlTheory 4 witness

def requests : List Request := [
  primary "definition" original,
  primary "crossing" crossingWitness,
  primary "swap" swapWitness,
  primary "duplicate-first" duplicateWitness,
  primary "reverse-target-order" (.instantiateMany [(Primary.G, Primary.f), (Primary.F, Primary.g)] original),
  primary "zero-copy" (.instantiateMany [] original),
  primary "subsequent-instantiation" subsequentWitness,
  primary "unformed-shadow" unformedShadow,
  primary "open-shadow" (.instantiateMany [(Primary.F, Primary.g), (Primary.F, .bvar 0)] original),
  primary "constant-target" (.instantiateMany [(Primary.D, Primary.g)] original),
  primary "unknown-target" (.instantiateMany [(.fresh 99, Primary.g)] original),
  primary "missing-source" (.instantiateMany [(Primary.F, Primary.g)] (.base (.axiom 0))),
  primary "wrong-definition-hints" (.base (.definition 0 [1, 0])),
  primary "legacy-singleton" (.base (.instantiate Primary.F Primary.g (.definition 0 [0, 1]))),
  checkRequest "correct-claim" Primary.theory Primary.allocated crossingWitness Primary.crossing,
  checkRequest "sequential-collapse-refused" Primary.theory Primary.allocated crossingWitness
    SimultaneousPresentation.Controls.sequential,
  secondary "computed-mp-children" composedMP,
  secondary "reversed-mp" (.modusPonens (.base (.axiom 1)) (.base (.axiom 0))),
  secondary "missing-left" (.modusPonens (.base (.axiom 99)) composedMP),
  secondary "missing-right" (.modusPonens (.base (.axiom 0)) (.base (.axiom 99))),
  secondary "binder-substitution" (.instantiateMany [(KernelControls.parameter, .bvar 0)] (.base (.axiom 2))),
  primary "literal-is-nat" (.base (.literal (.isNat 256))),
  primary "literal-comparison" (.base (.literal (.lessThan 2 3))),
  primary "literal-add-wrap" (.base (.literal (.addition (Spec.wordBound - 1) 1))),
  primary "literal-multiply" (.base (.literal (.multiplication 6 7))),
  primary "literal-divide" (.base (.literal (.division 17 5))),
  primary "literal-length" (.base (.literal (.length (.lit [3, 7])))),
  primary "literal-get" (.base (.literal (.get (.lit [3, 7]) 1))),
  primary "literal-div-zero" (.base (.literal (.division 17 0))),
  primary "literal-get-boundary" (.base (.literal (.get (.lit [3, 7]) 2))),
  primary "literal-too-large" (.base (.literal (.isNat Spec.wordBound))),
  ⟨"zero-query-fuel", "vibe:proof-v2-query", queryArguments Primary.theory Primary.allocated crossingWitness, .exhausted, 0⟩,
  ⟨"zero-check-fuel", "vibe:check-proof-v2", queryArguments Primary.theory Primary.allocated crossingWitness ++
    [encode Primary.crossing], .exhausted, 0⟩,
  ⟨"malformed-witness", "vibe:proof-v2-query", queryArguments Primary.theory Primary.allocated original |>.take 3 |>.concat (.list []),
    .value (.sym "None"), 512⟩ ]

#print axioms actual_byte_run_accepts_supplied_witness

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2.Controls
