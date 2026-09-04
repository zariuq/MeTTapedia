import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationRefinement
import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationWordArtifact

/-!
# Authenticated word artifacts from official TPTP files

This module closes the source boundary of the generic derivation-word
compiler.  A successful artifact retains exact evidence for four distinct
stages:

1. lossless refinement of an include-resolved official file;
2. semantic-carrier and derivation-DAG admission;
3. compilation through a caller-declared calculus projection; and
4. finite-arena word encoding.

Consequently, the compact words cannot be detached from the official file,
source digest, selected root, or calculus projection that produced them.
The module supplies no inference rules and performs no proof search.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFileWordArtifact

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationProgram
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationRefinement

variable {Formula Rule Evidence Provenance Obligation ServiceState : Type}

inductive CompileFailure where
  | refinementRejected
  | admissionRejected
  | word (failure :
      TptpOfficialDerivationWordArtifact.CompileFailure)
  deriving DecidableEq, Repr

/-- The complete source-to-word witness.  Every equation is produced by the
corresponding executable stage, rather than supplied by the caller. -/
structure Artifact
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (digest : String) (officialFile : Pattern) (rootName : String) where
  refined : RefinedFile digest officialFile
  refined_exact : refine? digest officialFile = some refined
  admitted : AdmittedDerivation
  admitted_exact :
    TptpOfficialDerivationAdmission.admit? refined.semantic = some admitted
  words : TptpOfficialDerivationWordArtifact.Artifact
    projection admitted rootName
  words_exact : TptpOfficialDerivationWordArtifact.compile?
    projection admitted rootName = .ok words

def compile?
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    (projection : TargetProjection Formula Rule Evidence Provenance Obligation)
    (digest : String) (officialFile : Pattern) (rootName : String) :
    Except CompileFailure (Artifact projection digest officialFile rootName) :=
  match refinedEq : refine? digest officialFile with
  | none => .error .refinementRejected
  | some refined =>
      match admittedEq :
          TptpOfficialDerivationAdmission.admit? refined.semantic with
      | none => .error .admissionRejected
      | some admitted =>
          match wordsEq : TptpOfficialDerivationWordArtifact.compile?
              projection admitted rootName with
          | .error failure => .error (.word failure)
          | .ok words => .ok {
              refined
              refined_exact := refinedEq
              admitted
              admitted_exact := admittedEq
              words
              words_exact := wordsEq
            }

/-- Constructor equation for successful refinement, admission, and word
compilation.  It eliminates only the three outer result constructors; the
individual stage equations remain the authorities for their own work. -/
theorem compile?_eq_ok_of_artifact
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection : TargetProjection Formula Rule Evidence Provenance Obligation}
    {digest : String} {officialFile : Pattern} {rootName : String}
    (artifact : Artifact projection digest officialFile rootName)
    (refinedEq : refine? digest officialFile = some artifact.refined)
    (admittedEq :
      TptpOfficialDerivationAdmission.admit? artifact.refined.semantic =
        some artifact.admitted)
    (wordsEq : TptpOfficialDerivationWordArtifact.compile?
      projection artifact.admitted rootName = .ok artifact.words) :
    compile? projection digest officialFile rootName = .ok artifact := by
  unfold compile?
  split
  case h_1 branchEq =>
    have impossible := branchEq.symm.trans refinedEq
    cases impossible
  case h_2 refined branchEq =>
    have refinedValueEq : refined = artifact.refined :=
      Option.some.inj (branchEq.symm.trans refinedEq)
    subst refined
    split
    case h_1 branchEq =>
      have impossible := branchEq.symm.trans admittedEq
      cases impossible
    case h_2 admitted branchEq =>
      have admittedValueEq : admitted = artifact.admitted :=
        Option.some.inj (branchEq.symm.trans admittedEq)
      subst admitted
      split
      case h_1 failure branchEq =>
        have impossible := branchEq.symm.trans wordsEq
        cases impossible
      case h_2 words branchEq =>
        have wordsValueEq : words = artifact.words :=
          Except.ok.inj (branchEq.symm.trans wordsEq)
        subst words
        congr

/-- Forgetting the added semantic occurrence identities recovers the exact
official file supplied to the compiler. -/
theorem official_erasure_exact
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection : TargetProjection Formula Rule Evidence Provenance Obligation}
    {digest : String} {officialFile : Pattern} {rootName : String}
    (artifact : Artifact projection digest officialFile rootName) :
    eraseRefinedFile artifact.refined.views = officialFile :=
  artifact.refined.erases_exact

/-- The finite words decode to the exact program compiled from the admitted
derivation and selected projection. -/
theorem words_decode_exact
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection : TargetProjection Formula Rule Evidence Provenance Obligation}
    {digest : String} {officialFile : Pattern} {rootName : String}
    (artifact : Artifact projection digest officialFile rootName) :
    decodeProgramUsing? artifact.words.finite.codecs.decoders
        artifact.words.finite.words = some artifact.words.semantic.program :=
  Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationWordArtifact.decodes_exact
    artifact.words

/-- The compact executor runs precisely the program compiled from the
admitted official derivation. -/
theorem execution_refines
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection : TargetProjection Formula Rule Evidence Provenance Obligation}
    {digest : String} {officialFile : Pattern} {rootName : String}
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (artifact : Artifact projection digest officialFile rootName) :
    executeFiniteArtifact services artifact.words.finite =
      .ofConfig (execute services artifact.words.semantic.program) :=
  Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationWordArtifact.execution_refines
    services artifact.words

/-- Acceptance of words compiled from an official file establishes exactly
the objective proved by the separately supplied calculus service. -/
theorem accepted_sound
    [DecidableEq Formula] [DecidableEq Rule] [DecidableEq Evidence]
    [DecidableEq Provenance] [DecidableEq Obligation]
    {projection : TargetProjection Formula Rule Evidence Provenance Obligation}
    {digest : String} {officialFile : Pattern} {rootName : String}
    (services : Services Formula Rule Evidence Provenance Obligation ServiceState)
    (sound : SoundServices services)
    (artifact : Artifact projection digest officialFile rootName)
    (root : RootClaim Formula Obligation)
    (accepted : executeFiniteArtifact services artifact.words.finite =
      .halted (.verified root)) :
    sound.Objective root.obligation :=
  Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationWordArtifact.accepted_sound
    services sound artifact.words root accepted

#print axioms official_erasure_exact
#print axioms words_decode_exact
#print axioms execution_refines
#print axioms accepted_sound

end Mettapedia.GSLT.LanguageDef.TptpOfficialFileWordArtifact
