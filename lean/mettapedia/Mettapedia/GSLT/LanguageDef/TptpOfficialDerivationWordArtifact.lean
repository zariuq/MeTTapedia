import Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram

/-!
# Authenticated finite-word artifacts from official TSTP derivations

This module composes two existing, independent stages:

1. the calculus-neutral compiler from an admitted official derivation to a
   semantic derivation-check program; and
2. the finite-arena encoder from that semantic program to compact word
   records.

The resulting object retains exact equations for both stages.  It therefore
records which admitted derivation, root, and declared calculus projection
produced the words.  The word layer remains representation only: it neither
selects an inference calculus nor changes the semantic acceptance condition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationWordArtifact

open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}

/-- Failures remain separated by phase.  A structural or projection failure
comes from official-DAG compilation; a finite-encoding failure comes only from
the representation layer. -/
inductive CompileFailure where
  | semantic (failure :
      TptpOfficialDerivationProgram.CompileFailure)
  | finiteEncoding
  deriving DecidableEq, Repr

/-- A compact verification artifact together with exact evidence of its two
source-derived compilation stages. -/
structure Artifact
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (admitted : AdmittedDerivation) (rootName : String) where
  semantic : TptpOfficialDerivationProgram.Artifact
    Formula Rule Evidence Provenance Obligation
  semanticCompiled :
    compileAdmittedWhole? projection admitted rootName = .ok semantic
  finite : FiniteProgramArtifact Formula Rule Evidence Provenance Obligation
  finiteCompiled : compileFiniteProgram? semantic.program = some finite

/-- Compile an admitted whole derivation directly to compact words.  No
calculus behavior is implemented here: all semantic payloads still come from
`projection`, and all semantic decisions remain in `Services`. -/
def compile?
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (admitted : AdmittedDerivation) (rootName : String) :
    Except CompileFailure (Artifact projection admitted rootName) :=
  match semanticEq : compileAdmittedWhole? projection admitted rootName with
  | .error failure => .error (.semantic failure)
  | .ok semantic =>
      match finiteEq : compileFiniteProgram? semantic.program with
      | none => .error .finiteEncoding
      | some finite => .ok {
          semantic
          semanticCompiled := semanticEq
          finite
          finiteCompiled := finiteEq
        }

/-- Constructor equation for a successful two-stage compilation.  Keeping
this lemma beside `compile?` lets concrete calculus instances reuse the
stage equations without asking simplification to normalize either compiler. -/
theorem compile?_eq_ok_of_artifact
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection :
      TargetProjection Formula Rule Evidence Provenance Obligation}
    {admitted : AdmittedDerivation} {rootName : String}
    (artifact : Artifact projection admitted rootName)
    (semanticEq :
      compileAdmittedWhole? projection admitted rootName =
        .ok artifact.semantic)
    (finiteEq :
      compileFiniteProgram? artifact.semantic.program = some artifact.finite) :
  compile? projection admitted rootName = .ok artifact := by
  unfold compile?
  split
  case h_1 failure branchEq =>
    have impossible :
        (Except.error failure : Except
          TptpOfficialDerivationProgram.CompileFailure
          (TptpOfficialDerivationProgram.Artifact
            Formula Rule Evidence Provenance Obligation)) =
          .ok artifact.semantic := branchEq.symm.trans semanticEq
    cases impossible
  case h_2 semantic branchEq =>
    have semanticValueEq : semantic = artifact.semantic :=
      Except.ok.inj (branchEq.symm.trans semanticEq)
    subst semantic
    split
    case h_1 finiteBranchEq =>
      have impossible :
          (none : Option (FiniteProgramArtifact
            Formula Rule Evidence Provenance Obligation)) =
            some artifact.finite := finiteBranchEq.symm.trans finiteEq
      cases impossible
    case h_2 finite finiteBranchEq =>
      have finiteValueEq : finite = artifact.finite :=
        Option.some.inj (finiteBranchEq.symm.trans finiteEq)
      subst finite
      congr

/-- Every returned word stream decodes to the exact semantic program retained
in the same artifact. -/
theorem decodes_exact
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection :
      TargetProjection Formula Rule Evidence Provenance Obligation}
    {admitted : AdmittedDerivation} {rootName : String}
    (artifact : Artifact projection admitted rootName) :
    decodeProgramUsing? artifact.finite.codecs.decoders artifact.finite.words =
      some artifact.semantic.program :=
  compileFiniteProgram?_decodes artifact.semantic.program artifact.finite
    artifact.finiteCompiled

/-- Executing the compact records refines execution of the exact semantic
program compiled from the admitted derivation. -/
theorem execution_refines
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection :
      TargetProjection Formula Rule Evidence Provenance Obligation}
    {admitted : AdmittedDerivation} {rootName : String}
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (artifact : Artifact projection admitted rootName) :
    executeFiniteArtifact services artifact.finite =
      .ofConfig (execute services artifact.semantic.program) :=
  executeFiniteArtifact_eq_of_compile services artifact.semantic.program
    artifact.finite artifact.finiteCompiled

/-- Acceptance of compact words establishes exactly the objective supplied by
the declared calculus service.  The result is generic in formula, rule,
evidence, provenance, obligation, and service-state representations. -/
theorem accepted_sound
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection :
      TargetProjection Formula Rule Evidence Provenance Obligation}
    {admitted : AdmittedDerivation} {rootName : String}
    (services :
      Services Formula Rule Evidence Provenance Obligation ServiceState)
    (sound : SoundServices services)
    (artifact : Artifact projection admitted rootName)
    (root : RootClaim Formula Obligation)
    (accepted : executeFiniteArtifact services artifact.finite =
      .halted (.verified root)) :
    sound.Objective root.obligation := by
  have refinement := execution_refines services artifact
  have semanticAccepted :
      execute services artifact.semantic.program =
        .halted (.verified root) := by
    cases resultEq : execute services artifact.semantic.program with
    | running state =>
        rw [resultEq] at refinement
        rw [accepted] at refinement
        cases refinement
    | halted outcome =>
        rw [resultEq] at refinement
        rw [accepted] at refinement
        simp only [WordConfig.ofConfig] at refinement
        cases refinement
        rfl
  exact accepted_artifact_sound services sound artifact.semantic root
    semanticAccepted

#print axioms decodes_exact
#print axioms execution_refines
#print axioms accepted_sound

end Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationWordArtifact
