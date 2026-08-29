import Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionSelectedRoot

/-!
# Official ground-resolution TSTP through finite word arenas

This module relocates the official ground-resolution canary into proof-local
finite arenas and runs its compact word records through the derivation word
machine.  Runtime decoding needs no total enumeration of semantic formulae,
rules, evidence, provenance, or obligations: every word is a bounded lookup in
an arena carried by this particular compiled derivation.

The word machine is not a second proof checker.  Its decoder theorem recovers
the exact instruction program accepted by the one-pass semantic machine, and
the generic simulation theorem transports the verified result.  The final
soundness theorem reflects an accepted word execution back through that shared
semantic authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordMachine

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.Languages.TPTP

namespace Canary

open TptpOfficialGroundResolutionSelectedRoot.Canary

def formulaArena : List Formula := [
  .clause firstClause.literals,
  .clause secondClause.literals,
  .clause thirdClause.literals,
  .clause [.positive q],
  .clause []
]

def ruleArena : List Rule := [
  TptpGroundResolutionProblemAuthority.resolutionKey
]

def evidenceArena : List Evidence := [()]

def provenanceArena : List Provenance := [
  firstClause, secondClause, thirdClause
]

def obligationArena : List Obligation := [.clause []]

def finiteCodecs :
    FiniteCodecs Formula Rule Evidence Provenance Obligation :=
  finiteCodecsOfProgram validProgram

theorem formula_arena_exact : finiteCodecs.formula.entries = formulaArena := by
  rfl

theorem rule_arena_exact : finiteCodecs.rule.entries = ruleArena := by
  rfl

theorem evidence_arena_exact : finiteCodecs.evidence.entries = evidenceArena := by
  rfl

theorem provenance_arena_exact :
    finiteCodecs.provenance.entries = provenanceArena := by
  rfl

theorem obligation_arena_exact :
    finiteCodecs.obligation.entries = obligationArena := by
  rfl

theorem formula_decode_zero :
    finiteCodecs.formula.decoder.decode? 0 = some (.clause firstClause.literals) := by
  rfl

theorem formula_decode_one :
    finiteCodecs.formula.decoder.decode? 1 = some (.clause secondClause.literals) := by
  rfl

theorem formula_decode_two :
    finiteCodecs.formula.decoder.decode? 2 = some (.clause thirdClause.literals) := by
  rfl

theorem formula_decode_three :
    finiteCodecs.formula.decoder.decode? 3 = some (.clause [.positive q]) := by
  rfl

theorem formula_decode_four :
    finiteCodecs.formula.decoder.decode? 4 = some (.clause []) := by
  rfl

theorem rule_decode_zero :
    finiteCodecs.rule.decoder.decode? 0 =
      some TptpGroundResolutionProblemAuthority.resolutionKey := by
  rfl

theorem evidence_decode_zero :
    finiteCodecs.evidence.decoder.decode? 0 = some () := by
  rfl

theorem provenance_decode_zero :
    finiteCodecs.provenance.decoder.decode? 0 = some firstClause := by
  rfl

theorem provenance_decode_one :
    finiteCodecs.provenance.decoder.decode? 1 = some secondClause := by
  rfl

theorem provenance_decode_two :
    finiteCodecs.provenance.decoder.decode? 2 = some thirdClause := by
  rfl

theorem obligation_decode_zero :
    finiteCodecs.obligation.decoder.decode? 0 = some (.clause []) := by
  rfl

def decoders : Decoders Formula Rule Evidence Provenance Obligation :=
  finiteCodecs.decoders

/-- The exact compact artifact for the official canary.  Child codes use zero
for no child and `child + 1` otherwise; all semantic payloads are arena indices.
-/
def words : WordProgram := [
  [opcodeInput, 0, 0, 0, 2, 4],
  [opcodeInput, 1, 1, 1, 2, 4],
  [opcodeInput, 2, 2, 2, 1, 5],
  [opcodeInfer, 3, 0, 0, 3, 1, 5, 2, 0, 1],
  [opcodeInfer, 4, 0, 0, 4, 0, 0, 2, 3, 2],
  [opcodeRoot, 4, 0],
  [opcodeFinish]
]

theorem words_generated_exact :
    encodeProgramFinite? finiteCodecs validProgram = some words := by
  rfl

def artifact :
    FiniteProgramArtifact Formula Rule Evidence Provenance Obligation :=
  ⟨finiteCodecs, words⟩

theorem artifact_compiles_exact :
    compileFiniteProgram? validProgram = some artifact := by
  rfl

theorem words_decode_exact :
    decodeProgramUsing? decoders words = some validProgram := by
  exact compileFiniteProgram?_decodes validProgram artifact
    artifact_compiles_exact

theorem words_verify :
    executeWordUsing decoders (services problem) words =
      WordConfig.halted (.verified validRoot) := by
  change executeFiniteArtifact (services problem) artifact =
    WordConfig.halted (.verified validRoot)
  rw [executeFiniteArtifact_eq_of_compile (services problem) validProgram
    artifact artifact_compiles_exact, valid_program_verified]
  rfl

/-- A verified compact execution reflects to the semantic machine and hence to
unsatisfiability.  The word result is used to recover the semantic acceptance;
it is not discarded in favor of an unrelated certificate replay. -/
theorem verified_words_unsatisfiable
    (root : RootClaim Formula Obligation)
    (accepted : executeWordUsing decoders (services problem) words =
      WordConfig.halted (.verified root))
    (emptyRoot : root.obligation = (.clause [] : Formula)) :
    ProblemUnsatisfiable problem := by
  have simulation := executeWordUsing_eq_of_decodeProgram decoders
    (services problem) words validProgram words_decode_exact
  have mapped :
      WordConfig.ofConfig (execute (services problem) validProgram) =
        .halted (.verified root) := simulation.symm.trans accepted
  have semanticAccepted :
      execute (services problem) validProgram = .halted (.verified root) := by
    cases executed : execute (services problem) validProgram with
    | running state =>
        simp [WordConfig.ofConfig, executed] at mapped
    | halted outcome =>
        have outcomeShape : outcome = .verified root := by
          simpa [WordConfig.ofConfig, executed] using mapped
        exact congrArg Config.halted outcomeShape
  have relative : RelativeTheorem problem root.obligation := by
    change (services_sound problem).Objective root.obligation
    exact execute_verified_sound (services_sound problem) validProgram root
      semanticAccepted
  intro valuation allSatisfied
  have emptySatisfied : GroundCNFAuthority.Formula.Satisfies valuation
      (.clause []) := by
    rw [← emptyRoot]
    exact relative valuation allSatisfied
  rcases emptySatisfied with ⟨literal, membership, _⟩
  simp at membership

theorem words_establish_unsatisfiable : ProblemUnsatisfiable problem :=
  verified_words_unsatisfiable validRoot words_verify rfl

def missingFormulaCodecs :
    FiniteCodecs Formula Rule Evidence Provenance Obligation where
  formula := ⟨[
    .clause firstClause.literals,
    .clause secondClause.literals,
    .clause thirdClause.literals,
    .clause [.positive q]
  ]⟩
  rule := finiteCodecs.rule
  evidence := finiteCodecs.evidence
  provenance := finiteCodecs.provenance
  obligation := finiteCodecs.obligation

theorem missing_formula_refuses_compilation :
    encodeProgramFinite? missingFormulaCodecs validProgram = none := by
  rfl

theorem out_of_arena_formula_rejected :
    decodeInstructionUsing? decoders
      [opcodeInput, 0, formulaArena.length, 0, 0, 0] = none := by
  decide +kernel

theorem malformed_parent_count_rejected :
    decodeInstructionUsing? decoders
      [opcodeInfer, 3, 0, 0, 3, 1, 5, 3, 0, 1] = none := by
  decide +kernel

theorem out_of_arena_rule_rejected :
    decodeInstructionUsing? decoders
      [opcodeInfer, 3, 1, 0, 3, 1, 5, 2, 0, 1] = none := by
  decide +kernel

end Canary

#print axioms Canary.words_decode_exact
#print axioms Canary.words_generated_exact
#print axioms Canary.artifact_compiles_exact
#print axioms Canary.words_verify
#print axioms Canary.verified_words_unsatisfiable
#print axioms Canary.words_establish_unsatisfiable
#print axioms Canary.missing_formula_refuses_compilation
#print axioms Canary.out_of_arena_formula_rejected
#print axioms Canary.malformed_parent_count_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionWordMachine
