import Mettapedia.GSLT.LanguageDef.TptpOfficialFileWordArtifact
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedWordMachine

/-!
# Official-file ground-resolution word verification

This module instantiates the source-authenticated word compiler with the
separately proved, status-indexed ground-resolution calculus.  Its positive
canary starts from an ordinary official TPTP file AST, not from a prebuilt
semantic derivation.

The generic file compiler owns refinement, admission, selected-root
compilation, and finite encoding.  The ground-resolution layer derives the
authorized input problem and initial symbol set from the same admitted
derivation.  Acceptance therefore proves relative theoremhood and, for the
empty-clause root, unsatisfiability of the admitted problem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionFileWordMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationRefinement
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedMachine

namespace FileArtifact

abbrev Artifact :=
  TptpOfficialFileWordArtifact.Artifact
    TptpOfficialGroundResolutionStatusIndexedMachine.projection

end FileArtifact

inductive CompileFailure where
  | file (failure : TptpOfficialFileWordArtifact.CompileFailure)
  | ground (failure : TptpOfficialDerivationProgram.CompileFailure)
  deriving DecidableEq, Repr

structure CompiledGroundFile (digest : String) (officialFile : Pattern)
    (rootName : String) where
  file : FileArtifact.Artifact digest officialFile rootName
  ground : CompiledGroundRoot
  ground_exact :
    TptpOfficialGroundResolutionStatusIndexedMachine.compileWhole?
      file.admitted rootName = .ok ground
  semantic_exact : file.words.semantic = ground.artifact

def compile? (digest : String) (officialFile : Pattern) (rootName : String) :
    Except CompileFailure (CompiledGroundFile digest officialFile rootName) :=
  match fileEq : TptpOfficialFileWordArtifact.compile?
      TptpOfficialGroundResolutionStatusIndexedMachine.projection
      digest officialFile rootName with
  | .error failure => .error (.file failure)
  | .ok file =>
      match groundEq :
          TptpOfficialGroundResolutionStatusIndexedMachine.compileWhole?
            file.admitted rootName with
      | .error failure => .error (.ground failure)
      | .ok ground => .ok {
          file
          ground
          ground_exact := groundEq
          semantic_exact := by
            have fromGround :=
              TptpOfficialGroundResolutionStatusIndexedMachine.compileWhole?_semantic_exact
                groundEq
            exact Except.ok.inj
              (file.words.semanticCompiled.symm.trans fromGround)
        }

/-- Successful outer compilation follows from the exact file and
ground-calculus stage equations.  The proof eliminates only result
constructors; neither stage is recomputed by normalization. -/
theorem compile?_eq_ok_of_compiled
    {digest : String} {officialFile : Pattern} {rootName : String}
    (compiled : CompiledGroundFile digest officialFile rootName)
    (fileEq : TptpOfficialFileWordArtifact.compile?
      TptpOfficialGroundResolutionStatusIndexedMachine.projection
      digest officialFile rootName = .ok compiled.file)
    (groundEq :
      TptpOfficialGroundResolutionStatusIndexedMachine.compileWhole?
        compiled.file.admitted rootName = .ok compiled.ground) :
    compile? digest officialFile rootName = .ok compiled := by
  unfold compile?
  split
  case h_1 failure branchEq =>
    have impossible := branchEq.symm.trans fileEq
    cases impossible
  case h_2 file branchEq =>
    have fileValueEq : file = compiled.file :=
      Except.ok.inj (branchEq.symm.trans fileEq)
    subst file
    split
    case h_1 failure branchEq =>
      have impossible := branchEq.symm.trans groundEq
      cases impossible
    case h_2 ground branchEq =>
      have groundValueEq : ground = compiled.ground :=
        Except.ok.inj (branchEq.symm.trans groundEq)
      subst ground
      congr

theorem words_decode_ground_program {digest : String} {officialFile : Pattern}
    {rootName : String}
    (compiled : CompiledGroundFile digest officialFile rootName) :
    decodeProgramUsing? compiled.file.words.finite.codecs.decoders
        compiled.file.words.finite.words =
      some compiled.ground.artifact.program := by
  rw [← compiled.semantic_exact]
  exact TptpOfficialFileWordArtifact.words_decode_exact compiled.file

theorem accepted_relativeTheorem {digest : String} {officialFile : Pattern}
    {rootName : String}
    (compiled : CompiledGroundFile digest officialFile rootName)
    (root : RootClaim MachineFormula
      TptpGroundResolutionCheckService.Obligation)
    (accepted : executeFiniteArtifact
        (services compiled.ground.problem compiled.ground.initialSymbols)
        compiled.file.words.finite = .halted (.verified root)) :
    TptpGroundResolutionCheckService.RelativeTheorem
      compiled.ground.problem root.obligation :=
  TptpOfficialFileWordArtifact.accepted_sound
    (services compiled.ground.problem compiled.ground.initialSymbols)
    (servicesSound compiled.ground.problem compiled.ground.initialSymbols)
    compiled.file root accepted

theorem acceptedEmptyRoot_unsatisfiable
    {digest : String} {officialFile : Pattern} {rootName : String}
    (compiled : CompiledGroundFile digest officialFile rootName)
    (root : RootClaim MachineFormula
      TptpGroundResolutionCheckService.Obligation)
    (accepted : executeFiniteArtifact
        (services compiled.ground.problem compiled.ground.initialSymbols)
        compiled.file.words.finite = .halted (.verified root))
    (emptyRoot : root.obligation = .clause []) :
    TptpGroundResolutionCheckService.ProblemUnsatisfiable
      compiled.ground.problem := by
  intro valuation problemSatisfied
  have rootSatisfied :=
    accepted_relativeTheorem compiled root accepted valuation problemSatisfied
  rw [emptyRoot] at rootSatisfied
  rcases rootSatisfied with ⟨literal, membership, _⟩
  simp at membership

/-! ## Official-file canary -/

namespace Canary

open TptpOfficialGroundResolutionSelectedRoot.Canary

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def officialInputs : List Pattern :=
  validAdmitted.derivation.nodes.map (fun node =>
    TptpOfficialSemanticCarrier.eraseToOfficialInput
      (encodeDerivationNode node.termView))

def officialFile : Pattern :=
  a "tptp92-ast:tptp-file:alt-1" [encodeOfficialInputs officialInputs]

theorem official_file_refines :
    (TptpOfficialDerivationRefinement.refine? "fixture" officialFile).isSome =
      true := by
  rfl

def refined : RefinedFile "fixture" officialFile :=
  (TptpOfficialDerivationRefinement.refine? "fixture" officialFile).get
    official_file_refines

theorem refinement_exact :
    TptpOfficialDerivationRefinement.refine? "fixture" officialFile =
      some refined := by
  exact (Option.some_get official_file_refines).symm

theorem refined_semantic_exact : refined.semantic = valid := by
  rfl

theorem admission_exact :
    TptpOfficialDerivationAdmission.admit? refined.semantic =
      some validAdmitted := by
  rw [refined_semantic_exact]
  exact valid_admission_exact

theorem word_compilation_exact :
    TptpOfficialDerivationWordArtifact.compile?
        TptpOfficialGroundResolutionStatusIndexedMachine.projection
        validAdmitted "empty" =
      .ok TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.officialWordArtifact := by
  exact TptpOfficialDerivationWordArtifact.compile?_eq_ok_of_artifact
    TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.officialWordArtifact
    TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.genericSemanticCompilation_exact
    TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.wordArtifact_compiles

def fileArtifact : FileArtifact.Artifact "fixture" officialFile "empty" := {
  refined
  refined_exact := refinement_exact
  admitted := validAdmitted
  admitted_exact := admission_exact
  words :=
    TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.officialWordArtifact
  words_exact := word_compilation_exact
}

theorem file_compilation_exact :
    TptpOfficialFileWordArtifact.compile?
        TptpOfficialGroundResolutionStatusIndexedMachine.projection
        "fixture" officialFile "empty" = .ok fileArtifact := by
  exact TptpOfficialFileWordArtifact.compile?_eq_ok_of_artifact
    fileArtifact refinement_exact admission_exact word_compilation_exact

def compiled : CompiledGroundFile "fixture" officialFile "empty" := {
  file := fileArtifact
  ground :=
    TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.compiled
  ground_exact :=
    TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.officialCompilation_exact
  semantic_exact := rfl
}

theorem compilation_exact :
    compile? "fixture" officialFile "empty" = .ok compiled := by
  exact compile?_eq_ok_of_compiled compiled file_compilation_exact
    TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.officialCompilation_exact

theorem official_file_compiles_to_words :
    (compile? "fixture" officialFile "empty").toOption.isSome = true := by
  rw [compilation_exact]
  rfl

theorem official_file_erases_exact :
    eraseRefinedFile compiled.file.refined.views = officialFile :=
  TptpOfficialFileWordArtifact.official_erasure_exact compiled.file

theorem decoded_words_are_ground_program :
    decodeProgramUsing? compiled.file.words.finite.codecs.decoders
        compiled.file.words.finite.words =
      some compiled.ground.artifact.program :=
  words_decode_ground_program compiled

end Canary

#print axioms words_decode_ground_program
#print axioms accepted_relativeTheorem
#print axioms acceptedEmptyRoot_unsatisfiable
#print axioms Canary.official_file_refines
#print axioms Canary.official_file_compiles_to_words
#print axioms Canary.official_file_erases_exact
#print axioms Canary.decoded_words_are_ground_program

end Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionFileWordMachine
