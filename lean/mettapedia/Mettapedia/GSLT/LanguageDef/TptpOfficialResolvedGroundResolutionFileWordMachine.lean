import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
import Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionFileWordMachine

/-!
# Include-resolved ground-resolution word verification

This module closes the remaining source-loading seam of the ground-resolution
qualification vertical.  It starts from a finite loader-supplied include
environment, resolves the selected include DAG with provenance, refines the
result once, admits the resulting derivation once, compiles the declared
ground-resolution profile once, and finally encodes that exact semantic
program as finite words.

The retained equations also show that the ordinary generic word compiler
would produce the same artifact.  They are evidence about the single retained
stages, not a second execution of those stages.  File loading and relative
path resolution remain outside the trusted semantic kernel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialResolvedGroundResolutionFileWordMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachine
open Mettapedia.GSLT.LanguageDef.DerivationCheckMachineBinary
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationAdmission
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
open Mettapedia.GSLT.LanguageDef.TptpOfficialGroundResolutionStatusIndexedMachine

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

inductive CompileFailure where
  | resolution (failure : ResolutionError)
  | admissionRejected
  | ground (failure : TptpOfficialDerivationProgram.CompileFailure)
  | finiteEncoding
  deriving DecidableEq, Repr

/-- The include-resolved source receipt and the ordinary ground-file artifact
constructed from the very same retained refinement and semantic program. -/
structure Artifact (environment : SourceEnvironment)
    (rootSource resolutionDigest rootName : String) where
  resolution : RefinedResolution environment rootSource resolutionDigest
  compiled :
    TptpOfficialGroundResolutionFileWordMachine.CompiledGroundFile
      resolutionDigest resolution.resolved.officialFile rootName

/-- Resolve and compile without replaying refinement or semantic compilation.
The standard nested artifacts are assembled from the equations produced by
this one pass. -/
def compile? (environment : SourceEnvironment)
    (rootSource resolutionDigest rootName : String) :
    Except CompileFailure
      (Artifact environment rootSource resolutionDigest rootName) :=
  match _resolutionEq :
      resolveAndRefine? environment rootSource resolutionDigest with
  | .error failure => .error (.resolution failure)
  | .ok resolution =>
      match admittedEq :
          TptpOfficialDerivationAdmission.admit?
            resolution.refined.semantic with
      | none => .error .admissionRejected
      | some admitted =>
          match groundEq :
              TptpOfficialGroundResolutionStatusIndexedMachine.compileWhole?
                admitted rootName with
          | .error failure => .error (.ground failure)
          | .ok ground =>
              match finiteEq : compileFiniteProgram? ground.artifact.program with
              | none => .error .finiteEncoding
              | some finite =>
                  let semanticEq :=
                    TptpOfficialGroundResolutionStatusIndexedMachine.compileWhole?_semantic_exact
                      groundEq
                  let words : TptpOfficialDerivationWordArtifact.Artifact
                      TptpOfficialGroundResolutionStatusIndexedMachine.projection
                      admitted rootName := {
                    semantic := ground.artifact
                    semanticCompiled := semanticEq
                    finite
                    finiteCompiled := finiteEq
                  }
                  let wordsEq :=
                    TptpOfficialDerivationWordArtifact.compile?_eq_ok_of_artifact
                      words semanticEq finiteEq
                  let file :
                      TptpOfficialGroundResolutionFileWordMachine.FileArtifact.Artifact
                      resolutionDigest resolution.resolved.officialFile rootName := {
                    refined := resolution.refined
                    refined_exact := resolution.refinement_exact
                    admitted
                    admitted_exact := admittedEq
                    words
                    words_exact := wordsEq
                  }
                  .ok {
                    resolution
                    compiled := {
                      file
                      ground
                      ground_exact := groundEq
                      semantic_exact := rfl
                    }
                  }

/-- The compiled file uses exactly the refinement already retained by include
resolution. -/
theorem refinement_reused
    {environment : SourceEnvironment}
    {rootSource resolutionDigest rootName : String}
    (artifact : Artifact environment rootSource resolutionDigest rootName) :
    artifact.compiled.file.refined = artifact.resolution.refined := by
  exact Option.some.inj
    (artifact.compiled.file.refined_exact.symm.trans
      artifact.resolution.refinement_exact)

/-- Dense semantic occurrences and source provenance remain aligned after
word compilation. -/
theorem compiled_views_match_provenance_length
    {environment : SourceEnvironment}
    {rootSource resolutionDigest rootName : String}
    (artifact : Artifact environment rootSource resolutionDigest rootName) :
    artifact.compiled.file.refined.views.length =
      artifact.resolution.resolved.provenance.length := by
  rw [refinement_reused artifact]
  exact artifact.resolution.views_match_provenance_length

/-- The compact records decode to the exact status-indexed ground-resolution
program compiled from the include-resolved source. -/
theorem words_decode_ground_program
    {environment : SourceEnvironment}
    {rootSource resolutionDigest rootName : String}
    (artifact : Artifact environment rootSource resolutionDigest rootName) :
    decodeProgramUsing? artifact.compiled.file.words.finite.codecs.decoders
        artifact.compiled.file.words.finite.words =
      some artifact.compiled.ground.artifact.program :=
  TptpOfficialGroundResolutionFileWordMachine.words_decode_ground_program
    artifact.compiled

/-- Acceptance proves the objective supplied by the separately proved
ground-resolution service. -/
theorem accepted_relativeTheorem
    {environment : SourceEnvironment}
    {rootSource resolutionDigest rootName : String}
    (artifact : Artifact environment rootSource resolutionDigest rootName)
    (root : RootClaim MachineFormula
      TptpGroundResolutionCheckService.Obligation)
    (accepted : executeFiniteArtifact
        (services artifact.compiled.ground.problem
          artifact.compiled.ground.initialSymbols)
        artifact.compiled.file.words.finite = .halted (.verified root)) :
    TptpGroundResolutionCheckService.RelativeTheorem
      artifact.compiled.ground.problem root.obligation :=
  TptpOfficialGroundResolutionFileWordMachine.accepted_relativeTheorem
    artifact.compiled root accepted

/-- An accepted empty root refutes the admitted include-resolved problem. -/
theorem acceptedEmptyRoot_unsatisfiable
    {environment : SourceEnvironment}
    {rootSource resolutionDigest rootName : String}
    (artifact : Artifact environment rootSource resolutionDigest rootName)
    (root : RootClaim MachineFormula
      TptpGroundResolutionCheckService.Obligation)
    (accepted : executeFiniteArtifact
        (services artifact.compiled.ground.problem
          artifact.compiled.ground.initialSymbols)
        artifact.compiled.file.words.finite = .halted (.verified root))
    (emptyRoot : root.obligation = .clause []) :
    TptpGroundResolutionCheckService.ProblemUnsatisfiable
      artifact.compiled.ground.problem :=
  TptpOfficialGroundResolutionFileWordMachine.acceptedEmptyRoot_unsatisfiable
    artifact.compiled root accepted emptyRoot

/-! ## End-to-end include canary -/

namespace Canary

def rootDocument : SourceDocument := {
  canonicalId := "root"
  digest := "root-digest"
  officialFile := TptpOfficialIncludeResolution.Canary.file [
    TptpOfficialIncludeResolution.Canary.includeInput "proof.p" none none 0]
}

def proofDocument : SourceDocument := {
  canonicalId := "proof"
  digest := "proof-digest"
  officialFile :=
    TptpOfficialGroundResolutionFileWordMachine.Canary.officialFile
}

def environment : SourceEnvironment := {
  documents := [rootDocument, proofDocument]
  bindings := [{
    fromSource := "root"
    requestedFile := "proof.p"
    targetSource := "proof"
  }]
}

def includeEdge : IncludeEdge := {
  fromSource := "root"
  fromInputIndex := 0
  requestedFile := "proof.p"
  targetSource := "proof"
  targetDigest := "proof-digest"
  selection := .implicitAll
  spaceName := none
  directive := a "tptp92-ast:include:alt-1" [
    a "tptp92-ast:file-name:alt-1" [
      TptpOfficialIncludeResolution.Canary.quotedWord "proof.p"],
    a "tptp92-ast:include-optionals:alt-1"]
  span := TptpOfficialIncludeResolution.Canary.span 0
}

def origin (index : Nat) : FormulaOrigin := {
  sourceId := "proof"
  sourceDigest := "proof-digest"
  sourceInputIndex := index
  includePath := [includeEdge]
}

def proofFormulas : List ResolvedFormula :=
  TptpOfficialGroundResolutionFileWordMachine.Canary.officialInputs.mapIdx
    (fun index input => {
      name := (decodeFormulaName? input).getD ""
      input
      origin := origin index
    })

theorem proofFormulas_inputs :
    proofFormulas.map ResolvedFormula.input =
      TptpOfficialGroundResolutionFileWordMachine.Canary.officialInputs := by
  rw [proofFormulas, List.mapIdx_eq_zipIdx_map, List.map_map]
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0
      TptpOfficialGroundResolutionFileWordMachine.Canary.officialInputs]
  rfl

def resolved : ResolvedDocument := {
  rootSource := "root"
  rootDigest := "root-digest"
  formulas := proofFormulas
  edges := [includeEdge]
}

theorem resolution_exact : resolve? environment "root" = .ok resolved := by
  rfl

theorem resolved_file_exact :
    resolved.officialFile =
      TptpOfficialGroundResolutionFileWordMachine.Canary.officialFile := by
  change
    a "tptp92-ast:tptp-file:alt-1"
        [TptpOfficialDerivationRefinement.encodeOfficialInputs
          (proofFormulas.map ResolvedFormula.input)] =
      TptpOfficialGroundResolutionFileWordMachine.Canary.officialFile
  rw [proofFormulas_inputs]
  rfl

def transportRefinedFile {left right : Pattern}
    (equality : left = right)
    (refined : TptpOfficialDerivationRefinement.RefinedFile "fixture" right) :
    TptpOfficialDerivationRefinement.RefinedFile "fixture" left :=
  equality.symm ▸ refined

theorem transportRefinedFile_exact {left right : Pattern}
    (equality : left = right)
    (refined : TptpOfficialDerivationRefinement.RefinedFile "fixture" right)
    (exactness : TptpOfficialDerivationRefinement.refine? "fixture" right =
      some refined) :
    TptpOfficialDerivationRefinement.refine? "fixture" left =
      some (transportRefinedFile equality refined) := by
  cases equality
  exact exactness

theorem transportRefinedFile_semantic {left right : Pattern}
    (equality : left = right)
    (refined : TptpOfficialDerivationRefinement.RefinedFile "fixture" right) :
    (transportRefinedFile equality refined).semantic = refined.semantic := by
  cases equality
  rfl

def resolution : RefinedResolution environment "root" "fixture" := {
  resolved
  resolution_exact := resolution_exact
  refined := transportRefinedFile resolved_file_exact
    TptpOfficialGroundResolutionFileWordMachine.Canary.refined
  refinement_exact := transportRefinedFile_exact resolved_file_exact
    TptpOfficialGroundResolutionFileWordMachine.Canary.refined
    TptpOfficialGroundResolutionFileWordMachine.Canary.refinement_exact
}

theorem admission_exact :
    TptpOfficialDerivationAdmission.admit? resolution.refined.semantic =
      some TptpOfficialGroundResolutionSelectedRoot.Canary.validAdmitted := by
  change TptpOfficialDerivationAdmission.admit?
      (transportRefinedFile resolved_file_exact
        TptpOfficialGroundResolutionFileWordMachine.Canary.refined).semantic = _
  rw [transportRefinedFile_semantic]
  exact TptpOfficialGroundResolutionFileWordMachine.Canary.admission_exact

theorem compilation_succeeds :
    (compile? environment "root" "fixture" "empty").toOption.isSome = true := by
  unfold compile?
  split
  case h_1 failure branchEq =>
    have impossible := branchEq.symm.trans
      (resolveAndRefine?_eq_ok_of_artifact resolution)
    cases impossible
  case h_2 selected branchEq =>
    have selectedEq : selected = resolution :=
      Except.ok.inj (branchEq.symm.trans
        (resolveAndRefine?_eq_ok_of_artifact resolution))
    subst selected
    split
    case h_1 branchEq =>
      have impossible := branchEq.symm.trans admission_exact
      cases impossible
    case h_2 admitted branchEq =>
      have admittedEq : admitted =
          TptpOfficialGroundResolutionSelectedRoot.Canary.validAdmitted :=
        Option.some.inj (branchEq.symm.trans admission_exact)
      subst admitted
      split
      case h_1 failure branchEq =>
        have impossible := branchEq.symm.trans
          TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.officialCompilation_exact
        cases impossible
      case h_2 ground branchEq =>
        have groundEq : ground =
            TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.compiled :=
          Except.ok.inj (branchEq.symm.trans
            TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.officialCompilation_exact)
        subst ground
        split
        case h_1 branchEq =>
          have impossible := branchEq.symm.trans
            TptpOfficialGroundResolutionStatusIndexedWordMachine.Canary.wordArtifact_compiles
          cases impossible
        case h_2 finite branchEq =>
          rfl

def artifact : Artifact environment "root" "fixture" "empty" :=
  (compile? environment "root" "fixture" "empty").toOption.get
    compilation_succeeds

theorem compilation_exact :
    compile? environment "root" "fixture" "empty" = .ok artifact := by
  have someEq : some artifact =
      (compile? environment "root" "fixture" "empty").toOption :=
    Option.some_get compilation_succeeds
  cases resultEq : compile? environment "root" "fixture" "empty" with
  | error failure =>
      rw [resultEq] at someEq
      cases someEq
  | ok value =>
      rw [resultEq] at someEq
      have valueEq : value = artifact := (Option.some.inj someEq).symm
      rw [valueEq]

theorem artifact_resolution_exact : artifact.resolution = resolution := by
  exact Except.ok.inj
    ((resolveAndRefine?_eq_ok_of_artifact artifact.resolution).symm.trans
      (resolveAndRefine?_eq_ok_of_artifact resolution))

theorem included_official_file_is_exact :
    artifact.resolution.resolved.officialFile =
      TptpOfficialGroundResolutionFileWordMachine.Canary.officialFile := by
  rw [artifact_resolution_exact]
  exact resolved_file_exact

theorem include_edge_and_formula_provenance_are_retained :
    artifact.resolution.resolved.edges.length = 1 ∧
      artifact.resolution.resolved.provenance.length =
        TptpOfficialGroundResolutionFileWordMachine.Canary.officialInputs.length := by
  rw [artifact_resolution_exact]
  change resolved.edges.length = 1 ∧
    resolved.provenance.length =
      TptpOfficialGroundResolutionFileWordMachine.Canary.officialInputs.length
  constructor
  · rfl
  · change proofFormulas.length =
      TptpOfficialGroundResolutionFileWordMachine.Canary.officialInputs.length
    simp [proofFormulas]

theorem decoded_words_are_ground_program :
    decodeProgramUsing? artifact.compiled.file.words.finite.codecs.decoders
        artifact.compiled.file.words.finite.words =
      some artifact.compiled.ground.artifact.program :=
  words_decode_ground_program artifact

end Canary

#print axioms refinement_reused
#print axioms compiled_views_match_provenance_length
#print axioms words_decode_ground_program
#print axioms accepted_relativeTheorem
#print axioms acceptedEmptyRoot_unsatisfiable
#print axioms Canary.compilation_succeeds
#print axioms Canary.included_official_file_is_exact
#print axioms Canary.include_edge_and_formula_provenance_are_retained
#print axioms Canary.decoded_words_are_ground_program

end Mettapedia.GSLT.LanguageDef.TptpOfficialResolvedGroundResolutionFileWordMachine
