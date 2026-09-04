import Mettapedia.Languages.Metamath.MM2SourceActionExecution
import Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
import Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
import Mettapedia.Languages.Metamath.MM2NormalLabelLookup
import Mettapedia.Languages.Metamath.MM2SourceConstantDeclaration
import Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
import Mettapedia.Languages.Metamath.MM2SourceScopeExecution
import Mettapedia.Languages.Metamath.MM2SourceFloatingDeclaration
import Mettapedia.Languages.Metamath.MM2SourceDVDeclaration
import Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration
import Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
import Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
import Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
import Mettapedia.Languages.Metamath.MM2CompressedProofExecution
import Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
import Mettapedia.Languages.Metamath.MM2Transformation

/-!
# Database-independent Metamath verifier program for MM2

This module is the language-level home of the verifier transformation used by
the executable exporter.  It is independent of a Metamath database and its
proof payloads.  Normal and compressed verification rules are derived once
from the supplied verifier operation spine and are composed with passive
source data only after both transformation outputs have been constructed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2VerifierProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.Metamath.MM2NormalLabelLookup
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
open Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
open Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
open Mettapedia.Languages.Metamath.MM2SourceConstantDeclaration
open Mettapedia.Languages.Metamath.MM2SourceDVDeclaration
open Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration
open Mettapedia.Languages.Metamath.MM2SourceFloatingDeclaration
open Mettapedia.Languages.Metamath.MM2SourceFormulaValidation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTOperations

/-- Executable projection of the normal verifier transformation. -/
def baseVerifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  normalVerifierInternalRows ++
    (orderedSourceEventPreludeRules ++
      source.operations.flatMap verifierRulesForNormalSlice)

theorem baseVerifierProgram_eq_transform (source : MetamathVerifierGSLT)
    (target : MM2Target) :
    baseVerifierProgram source =
      (transformNormalVerifierSlice source target).program := by
  rfl

/-- Verifier-owned compressed source rules selected by one operation. -/
def compressedVerifierSourceRulesForOperation :
    SourceOperation → List Atom
  | .checkTheoremCompressed => compressedOrderedActivationRules
  | _ => []

/-- Verifier-owned compressed runtime rows selected by one operation. -/
def compressedVerifierRuntimeRowsForOperation :
    SourceOperation → List Atom
  | .checkTheoremCompressed =>
      compressedSpeculativeVerifierRuleRows ++
        [compressedSpeculativeVerifierRuleEnd] ++
        compressedSpeculativeVerifierStaticRows ++
        compressedNormalHandoffRuleRows ++
        [compressedNormalHandoffRuleEnd] ++
        compressedNormalDispatchBridgeRows ++
        [compressedDispatchReloadCaptureRow]
  | _ => []

/-- Compressed source-rule inventory derived from the supplied operation
spine. -/
def compressedVerifierSourceExtension
    (source : MetamathVerifierGSLT) : List Atom :=
  source.operations.flatMap compressedVerifierSourceRulesForOperation

/-- Compressed runtime inventory derived from the supplied operation spine. -/
def compressedVerifierRuntimeExtension
    (source : MetamathVerifierGSLT) : List Atom :=
  source.operations.flatMap compressedVerifierRuntimeRowsForOperation

/-- Maintained normal verifier plus the source-action and compressed
extensions. -/
def verifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  baseVerifierProgram source ++
    sourceActionVerifierExtensionProgramWith normalProofMachineRuleInventory
      (normalLabelLookupSourceRules ++
        compressedVerifierSourceExtension source) ++
      normalLabelLookupStaticRows ++
      compressedVerifierRuntimeExtension source

theorem verifierProgram_eq_transform_extension
    (source : MetamathVerifierGSLT) (target : MM2Target) :
    verifierProgram source =
      (transformNormalVerifierSlice source target).program ++
        sourceActionVerifierExtensionProgramWith
          normalProofMachineRuleInventory
          (normalLabelLookupSourceRules ++
            compressedVerifierSourceExtension source) ++
          normalLabelLookupStaticRows ++
          compressedVerifierRuntimeExtension source := by
  rw [verifierProgram, baseVerifierProgram_eq_transform source target]

/-- The single database- and proof-independent verifier transformation
output.  Normal and compressed machinery coexist in this fixed program; no
statement, proof payload, pathname, or fixture identity selects a variant. -/
def genericVerifierProgram (source : MetamathVerifierGSLT) : List Atom :=
  (normalVerifierInternalRows ++
      [sourceEventBootstrapRule, sourceEventDispatchRule,
        sourceTheoremStartRule]) ++
    compressedNormalSourceActionExtension
      (constantDeclarationRules ++ variableDeclarationOwnRules ++
        scopeExecutionRules ++ floatingDeclarationOwnRules ++
        essentialDeclarationOwnRules ++ formulaValidationRules ++
        variableTypecodeLookupRules ++
        dvDeclarationExtensionRules ++
        nativeAssertionVerifierRules ++
        normalLabelLookupSourceRules ++
        compressedVerifierSourceExtension source) ++
      objectLookupStaticRows ++ constantDeclarationStaticRows ++
      variableDeclarationStaticRows ++ scopeExecutionStaticRows ++
      floatingDeclarationStaticRows ++
      essentialDeclarationStaticRows ++
      dvDeclarationExtensionStaticRows ++
      nativeAssertionVerifierStaticRows ++
      normalLabelLookupStaticRows ++
      compressedVerifierRuntimeExtension source

#print axioms baseVerifierProgram_eq_transform
#print axioms verifierProgram_eq_transform_extension

end Mettapedia.Languages.Metamath.MM2VerifierProgram
