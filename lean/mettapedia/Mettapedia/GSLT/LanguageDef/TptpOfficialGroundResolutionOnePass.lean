import Mettapedia.GSLT.LanguageDef.DerivationCheckMachineNamed
import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionVerifier

/-!
# Official ground-resolution TSTP through the generic one-pass machine

This module is an explicit ground-resolution specialization, not the generic
`lib_tptp` verifier.  It reuses the official semantic-carrier decoder, lowers
names and graph shape through the calculus-neutral named compiler, and runs
the derivation-check machine once.  The structural compiler never reconstructs
or checks an inference.  Missing ground-resolution pivot evidence is derived
only when the corresponding `infer` instruction is executed.

The string identifying resolution is confined to the official
ground-resolution adapter imported above.  Neither the named compiler nor the
derivation-check machine contains TPTP or resolution vocabulary.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionOnePass

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCheckService
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority
open Mettapedia.Languages.TPTP
open Mettapedia.Languages.TPTP.NIKAuthority
open Mettapedia.Languages.TPTP.StatusSemantics
open Mettapedia.Languages.TPTP.GroundCNFAuthority

/-! ## Carrier-to-machine structural lowering -/

def namedDerivation
    (lowering : TptpOfficialGroundResolutionVerifier.LoweredRefutation) :
    DerivationCheckMachineNamed.NamedDerivation
      Formula Rule Evidence Provenance Obligation := {
  inputs := lowering.submission.problem.clauses.map fun clause => {
    name := clause.name
    formula := .clause clause.literals
    provenance := clause
  }
  nodes := lowering.submission.nodes.map fun node => {
    name := node.name
    rule := node.key
    parents := node.parents
    evidence := ()
    conclusion := node.inferred
  }
  root := lowering.submission.root
  obligation := lowering.submission.expected
}

def compileLowering?
    (lowering : TptpOfficialGroundResolutionVerifier.LoweredRefutation) :
    Option Program :=
  DerivationCheckMachineNamed.compile? (namedDerivation lowering)

structure VerifiedRefutation where
  source : Pattern
  lowering : TptpOfficialGroundResolutionVerifier.LoweredRefutation
  program : Program
  root : RootClaim Formula Obligation
  admitted : checkHasType
    Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
    WellSorted.FreeTypeContext.empty [] source
    (.base "TptpSemantic:derivation") = true
  lowered : TptpOfficialGroundResolutionVerifier.lowerRefutation? source =
    some lowering
  compiled : compileLowering? lowering = some program
  accepted : execute (services lowering.submission.problem) program =
    .halted (.verified root)
  emptyRoot : root.obligation = Formula.clause []

inductive VerificationResult where
  | verified (evidence : VerifiedRefutation)
  | incomplete
  | rejected

/-- The public specialization performs carrier admission, structural
lowering, and one semantic machine pass. -/
def verify (source : Pattern) : VerificationResult :=
  if admitted : checkHasType
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
      WellSorted.FreeTypeContext.empty [] source
      (.base "TptpSemantic:derivation") = true then
    match lowered : TptpOfficialGroundResolutionVerifier.lowerRefutation?
        source with
    | none => .incomplete
    | some lowering =>
        match compiled : compileLowering? lowering with
        | none => .rejected
        | some program =>
            match accepted : execute (services lowering.submission.problem)
                program with
            | .halted (.verified root) =>
                if emptyRoot : root.obligation = Formula.clause [] then
                  .verified {
                    source, lowering, program, root, admitted, lowered,
                    compiled, accepted, emptyRoot
                  }
                else .rejected
            | _ => .rejected
  else
    .rejected

theorem VerifiedRefutation.relativeTheorem (result : VerifiedRefutation) :
    RelativeTheorem result.lowering.submission.problem result.root.obligation :=
  by
    change (services_sound result.lowering.submission.problem).Objective
      result.root.obligation
    exact execute_verified_sound
      (services_sound result.lowering.submission.problem)
      result.program result.root result.accepted

theorem VerifiedRefutation.unsatisfiable (result : VerifiedRefutation) :
    ProblemUnsatisfiable result.lowering.submission.problem := by
  intro valuation allSatisfied
  have emptySatisfied : Formula.Satisfies valuation (Formula.clause []) := by
    rw [← result.emptyRoot]
    exact result.relativeTheorem valuation allSatisfied
  rcases emptySatisfied with ⟨literal, membership, _⟩
  simp at membership

/-! ## End-to-end official-carrier controls -/

namespace Canary

def valid : Pattern := TptpOfficialGroundResolutionVerifier.Canary.valid

def p : Pattern := TptpOfficialGroundResolutionVerifier.Canary.atom "p"
def q : Pattern := TptpOfficialGroundResolutionVerifier.Canary.atom "q"

def firstClause : Provenance := {
  id := 0
  name := "p_or_q"
  role := .axiom
  literals := [.positive p, .positive q]
}

def secondClause : Provenance := {
  id := 1
  name := "not_p"
  role := .axiom
  literals := [.negative p]
}

def thirdClause : Provenance := {
  id := 2
  name := "not_q"
  role := .axiom
  literals := [.negative q]
}

def problem : ParsedProblem := {
  sourceDigest := "fixture"
  clauses := [firstClause, secondClause, thirdClause]
}

theorem mismatched_input_rejected :
    (services problem).input () firstClause (.clause secondClause.literals) =
      none := by
  decide +kernel

theorem first_input_accepted :
    (services problem).input () firstClause (.clause firstClause.literals) =
      some () := by
  decide +kernel

theorem second_input_accepted :
    (services problem).input () secondClause (.clause secondClause.literals) =
      some () := by
  decide +kernel

theorem third_input_accepted :
    (services problem).input () thirdClause (.clause thirdClause.literals) =
      some () := by
  decide +kernel

theorem wrong_root_obligation_rejected :
    (services problem).root () (.clause [.positive q]) (.clause []) = false := by
  decide +kernel

theorem correct_root_obligation_accepted :
    (services problem).root () (.clause []) (.clause []) = true := by
  rfl

def validProgram : Program := [
  .input 0 (.clause firstClause.literals) firstClause
    { distance := 2, towardRoot := some 3 },
  .input 1 (.clause secondClause.literals) secondClause
    { distance := 2, towardRoot := some 3 },
  .input 2 (.clause thirdClause.literals) thirdClause
    { distance := 1, towardRoot := some 4 },
  .infer 3 TptpGroundResolutionProblemAuthority.resolutionKey [0, 1] ()
    (.clause [.positive q]) { distance := 1, towardRoot := some 4 },
  .infer 4 TptpGroundResolutionProblemAuthority.resolutionKey [3, 2] ()
    (.clause []) { distance := 0, towardRoot := none },
  .root 4 (.clause []),
  .finish]

theorem valid_compilation_exact :
    compileLowering?
      TptpOfficialGroundResolutionVerifier.Canary.validLowering =
      some validProgram := by
  rfl

theorem first_inference_accepted :
    inferAccepted TptpGroundResolutionProblemAuthority.resolutionKey
      [.clause firstClause.literals, .clause secondClause.literals]
      (.clause [.positive q]) = true := by
  have pValid : argumentValidAt 0 p = true := by decide +kernel
  have qValid : argumentValidAt 0 q = true := by decide +kernel
  simpa [inferAccepted, firstClause, secondClause] using
    synthesize_binary_positive_left p q pValid qValid

theorem second_inference_accepted :
    inferAccepted TptpGroundResolutionProblemAuthority.resolutionKey
      [.clause [.positive q], .clause thirdClause.literals]
      (.clause []) = true := by
  have qValid : argumentValidAt 0 q = true := by decide +kernel
  simpa [inferAccepted, thirdClause] using
    synthesize_binary_singletons q qValid

def validRoot : RootClaim Formula Obligation := {
  id := 4
  formula := .clause []
  obligation := .clause []
}

/-- The exact live-node receipt immediately before the final instruction.
This is exported for target-language simulations that retain the checked node
store in their halted configuration. -/
def validPrefixNodes :
    List (DerivationCheckMachine.Node Formula) := [
  { id := 4, formula := .clause [],
    relevance := { distance := 0, towardRoot := none }, linked := false },
  { id := 3, formula := .clause [.positive q],
    relevance := { distance := 1, towardRoot := some 4 }, linked := true },
  { id := 2, formula := .clause thirdClause.literals,
    relevance := { distance := 1, towardRoot := some 4 }, linked := true },
  { id := 1, formula := .clause secondClause.literals,
    relevance := { distance := 2, towardRoot := some 3 }, linked := true },
  { id := 0, formula := .clause firstClause.literals,
    relevance := { distance := 2, towardRoot := some 3 }, linked := true }
]

def validPrefixState : State Formula Rule Evidence Provenance Obligation Unit := {
  instructions := [.finish]
  nodes := validPrefixNodes
  nextId := 5
  root? := some validRoot
  serviceState := ()
}

theorem valid_prefix_exact :
    runFuel (services problem) 6 (initial (services problem) validProgram) =
      .running validPrefixState := by
  decide +kernel

theorem valid_program_verified :
    execute (services problem) validProgram =
      .halted (.verified validRoot) := by
  decide +kernel

def validEvidence : VerifiedRefutation where
  source := valid
  lowering := TptpOfficialGroundResolutionVerifier.Canary.validLowering
  program := validProgram
  root := validRoot
  admitted :=
    TptpOfficialGroundResolutionVerifier.Canary.valid_is_admitted
  lowered :=
    TptpOfficialGroundResolutionVerifier.Canary.valid_lowering_exact
  compiled := valid_compilation_exact
  accepted := valid_program_verified
  emptyRoot := rfl

theorem valid_verifies : verify valid = .verified validEvidence := by
  unfold verify
  split <;> rename_i admitted
  · split
    · rename_i lowered
      have expected :
          TptpOfficialGroundResolutionVerifier.lowerRefutation? valid =
            some TptpOfficialGroundResolutionVerifier.Canary.validLowering :=
        TptpOfficialGroundResolutionVerifier.Canary.valid_lowering_exact
      rw [expected] at lowered
      contradiction
    · rename_i lowering lowered
      have expected :
          TptpOfficialGroundResolutionVerifier.lowerRefutation? valid =
            some TptpOfficialGroundResolutionVerifier.Canary.validLowering :=
        TptpOfficialGroundResolutionVerifier.Canary.valid_lowering_exact
      have loweringShape :
          TptpOfficialGroundResolutionVerifier.Canary.validLowering = lowering :=
        Option.some.inj (expected.symm.trans lowered)
      subst lowering
      split
      · rename_i compiled
        rw [valid_compilation_exact] at compiled
        contradiction
      · rename_i program compiled
        have programShape : validProgram = program :=
          Option.some.inj (valid_compilation_exact.symm.trans compiled)
        subst program
        split
        · rename_i root accepted
          have rootShape : root = validRoot := by
            have comparison := accepted.symm.trans valid_program_verified
            cases comparison
            rfl
          subst root
          split
          · rfl
          · rename_i notEmpty
            exact (notEmpty rfl).elim
        · rename_i notVerified
          exact (notVerified validRoot valid_program_verified).elim
  · exact (admitted
      TptpOfficialGroundResolutionVerifier.Canary.valid_is_admitted).elim

theorem valid_establishes_unsatisfiable :
    ∃ evidence, verify valid = .verified evidence ∧
      ProblemUnsatisfiable evidence.lowering.submission.problem := by
  exact ⟨validEvidence, valid_verifies, validEvidence.unsatisfiable⟩

def unknownRule : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.derivationWith "unknown"

def missingParent : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.derivationWith
    "resolution" ["missing", "not_p"]

def inventedResult : Pattern :=
  TptpOfficialGroundResolutionVerifier.Canary.derivationWith
    "resolution" ["p_or_q", "not_p"]
    (TptpOfficialGroundResolutionVerifier.Canary.formula
      [TptpOfficialGroundResolutionVerifier.Canary.positive "p"])

theorem unknown_rule_is_admitted :
    checkHasType
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
      WellSorted.FreeTypeContext.empty [] unknownRule
      (.base "TptpSemantic:derivation") = true := by
  apply TptpOfficialGroundResolutionVerifier.Canary.derivationWith_is_admitted
  · exact checkHasType_sound (by decide +kernel)
  · decide +kernel

theorem missing_parent_is_admitted :
    checkHasType
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
      WellSorted.FreeTypeContext.empty [] missingParent
      (.base "TptpSemantic:derivation") = true := by
  apply TptpOfficialGroundResolutionVerifier.Canary.derivationWith_is_admitted
  · exact checkHasType_sound (by decide +kernel)
  · decide +kernel

theorem invented_result_is_admitted :
    checkHasType
      Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier.language
      WellSorted.FreeTypeContext.empty [] inventedResult
      (.base "TptpSemantic:derivation") = true := by
  apply TptpOfficialGroundResolutionVerifier.Canary.derivationWith_is_admitted
  · exact checkHasType_sound (by decide +kernel)
  · decide +kernel

theorem unknown_rule_lowering_none :
    TptpOfficialGroundResolutionVerifier.lowerRefutation? unknownRule = none := by
  rfl

def missingParentLowering :
    TptpOfficialGroundResolutionVerifier.LoweredRefutation where
  submission := {
    problem := problem
    nodes := [
      { name := "q"
        key := TptpGroundResolutionProblemAuthority.resolutionKey
        parents := ["missing", "not_p"]
        inferred := .clause [.positive q]
        evidence := .reconstruct },
      { name := "empty"
        key := TptpGroundResolutionProblemAuthority.resolutionKey
        parents := ["q", "not_q"]
        inferred := .clause []
        evidence := .reconstruct }
    ]
    root := "empty"
    expected := .clause []
  }
  expectedEmpty := rfl

theorem missing_parent_lowering_exact :
    TptpOfficialGroundResolutionVerifier.lowerRefutation? missingParent =
      some missingParentLowering := by
  rfl

theorem missing_parent_compilation_fails :
    compileLowering? missingParentLowering = none := by
  rfl

def inventedResultLowering :
    TptpOfficialGroundResolutionVerifier.LoweredRefutation where
  submission := {
    problem := problem
    nodes := [
      { name := "q"
        key := TptpGroundResolutionProblemAuthority.resolutionKey
        parents := ["p_or_q", "not_p"]
        inferred := .clause [.positive p]
        evidence := .reconstruct },
      { name := "empty"
        key := TptpGroundResolutionProblemAuthority.resolutionKey
        parents := ["q", "not_q"]
        inferred := .clause []
        evidence := .reconstruct }
    ]
    root := "empty"
    expected := .clause []
  }
  expectedEmpty := rfl

def inventedResultProgram : Program := [
  .input 0 (.clause firstClause.literals) firstClause
    { distance := 2, towardRoot := some 3 },
  .input 1 (.clause secondClause.literals) secondClause
    { distance := 2, towardRoot := some 3 },
  .input 2 (.clause thirdClause.literals) thirdClause
    { distance := 1, towardRoot := some 4 },
  .infer 3 TptpGroundResolutionProblemAuthority.resolutionKey [0, 1] ()
    (.clause [.positive p]) { distance := 1, towardRoot := some 4 },
  .infer 4 TptpGroundResolutionProblemAuthority.resolutionKey [3, 2] ()
    (.clause []) { distance := 0, towardRoot := none },
  .root 4 (.clause []),
  .finish]

theorem invented_result_lowering_exact :
    TptpOfficialGroundResolutionVerifier.lowerRefutation? inventedResult =
      some inventedResultLowering := by
  rfl

theorem invented_result_compilation_exact :
    compileLowering? inventedResultLowering = some inventedResultProgram := by
  rfl

theorem invented_result_program_rejected :
    execute (services problem) inventedResultProgram =
      .halted (.fault (.ruleRejected 3)) := by
  decide +kernel

theorem unknown_rule_is_incomplete :
    verify unknownRule = .incomplete := by
  unfold verify
  split
  · split
    · rfl
    · rename_i lowering lowered
      have impossible : none = some lowering :=
        unknown_rule_lowering_none.symm.trans lowered
      contradiction
  · rename_i notAdmitted
    exact (notAdmitted unknown_rule_is_admitted).elim

theorem missing_parent_is_rejected :
    verify missingParent = .rejected := by
  unfold verify
  split
  · split
    · rename_i lowered
      rw [missing_parent_lowering_exact] at lowered
      contradiction
    · rename_i lowering lowered
      have loweringShape : missingParentLowering = lowering :=
        Option.some.inj (missing_parent_lowering_exact.symm.trans lowered)
      subst lowering
      split
      · rfl
      · rename_i program compiled
        have impossible : none = some program :=
          missing_parent_compilation_fails.symm.trans compiled
        contradiction
  · rename_i notAdmitted
    exact (notAdmitted missing_parent_is_admitted).elim

theorem invented_result_is_rejected :
    verify inventedResult = .rejected := by
  unfold verify
  split
  · split
    · rename_i lowered
      rw [invented_result_lowering_exact] at lowered
      contradiction
    · rename_i lowering lowered
      have loweringShape : inventedResultLowering = lowering :=
        Option.some.inj (invented_result_lowering_exact.symm.trans lowered)
      subst lowering
      split
      · rename_i compiled
        rw [invented_result_compilation_exact] at compiled
      · rename_i program compiled
        have programShape : inventedResultProgram = program :=
          Option.some.inj (invented_result_compilation_exact.symm.trans compiled)
        subst program
        split
        · rename_i root accepted
          have impossible := accepted.symm.trans invented_result_program_rejected
          cases impossible
        · rfl
  · rename_i notAdmitted
    exact (notAdmitted invented_result_is_admitted).elim

end Canary

#print axioms VerifiedRefutation.relativeTheorem
#print axioms VerifiedRefutation.unsatisfiable
#print axioms Canary.valid_compilation_exact
#print axioms Canary.valid_prefix_exact
#print axioms Canary.valid_program_verified
#print axioms Canary.valid_verifies
#print axioms Canary.valid_establishes_unsatisfiable
#print axioms Canary.unknown_rule_is_incomplete
#print axioms Canary.missing_parent_is_rejected
#print axioms Canary.invented_result_is_rejected

#print axioms inferAccepted_sound
#print axioms services_sound
#print axioms VerifiedRefutation.relativeTheorem
#print axioms VerifiedRefutation.unsatisfiable

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionOnePass
