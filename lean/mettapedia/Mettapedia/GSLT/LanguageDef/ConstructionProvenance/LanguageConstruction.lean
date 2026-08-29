import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.CalculusLanguageExtension
import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

/-!
# Standard language-construction operations

This module instantiates many-sorted construction provenance with actual
language-engineering operations.  Operational theories, language definitions,
proof-definition layers, flat calculus languages, and append-only calculus
extensions are different artifact kinds.  Consequently, only well-sorted
construction pipelines can be represented.

The evaluated artifact remains the ordinary public value.  Its exact
construction route lives in the displayed receipt layer and may be erased
only when route-sensitive observations are not required.
-/

namespace Mettapedia.GSLT.LanguageDef.ConstructionProvenance.LanguageConstruction

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Syntax
open ManySorted

/-- Artifact kinds used by the standard language-construction algebra. -/
inductive ArtifactKind where
  | operationalTheory
  | language
  | proofCalculus
  | calculusLanguage
  | calculusExtension
deriving DecidableEq

/-- The Lean type carried by each construction kind. -/
def Artifact : ArtifactKind → Type 1
  | .operationalTheory => GSLT
  | .language => ULift.{1} LanguageDef
  | .proofCalculus => ULift.{1} ProofCalculus
  | .calculusLanguage => ULift.{1} CalculusLanguageDef
  | .calculusExtension => ULift.{1} CalculusLanguageExtension

/-- Authored roots are already checked values of their indicated kind. -/
abbrev Source := Artifact

/-- Standard operations with their complete input and output kinds. -/
inductive Operation : List ArtifactKind → ArtifactKind → Type 1 where
  | freeDocument :
      Operation [.operationalTheory] .operationalTheory
  | disjointSum :
      Operation [.operationalTheory, .operationalTheory] .operationalTheory
  | attachCalculus :
      Operation [.language, .proofCalculus] .calculusLanguage
  | eraseCalculus :
      Operation [.calculusLanguage] .language
  | applyCalculusExtension :
      Operation [.calculusExtension, .calculusLanguage] .calculusLanguage
  | composeCalculusExtensions :
      Operation [.calculusExtension, .calculusExtension] .calculusExtension

/-- Interpret every standard operation by the repository's existing
authoritative construction. -/
def interpretOperation : {inputs : List ArtifactKind} →
    {output : ArtifactKind} →
    Operation inputs output → FamilyList Artifact inputs → Artifact output
  | _, _, .freeDocument, .cons system .nil =>
      GSLT.freeDocument system
  | _, _, .disjointSum, .cons left (.cons right .nil) =>
      GSLT.disjointSum left right
  | _, _, .attachCalculus, .cons language (.cons calculus .nil) =>
      ⟨CalculusLanguageDef.extend language.down calculus.down⟩
  | _, _, .eraseCalculus, .cons language .nil =>
      ⟨language.down.toLanguageDef⟩
  | _, _, .applyCalculusExtension, .cons extension (.cons language .nil) =>
      ⟨extension.down.apply language.down⟩
  | _, _, .composeCalculusExtensions, .cons first (.cons second .nil) =>
      ⟨first.down.comp second.down⟩

/-- The standard many-sorted language-construction algebra. -/
def algebra : ManySortedConstructionAlgebra where
  Kind := ArtifactKind
  Object := Artifact
  Source := Source
  Operation := Operation
  interpretSource := fun source => source
  interpretOperation := interpretOperation

/-! ## Actual construction routes -/

namespace Canary

def unitTheory : GSLT := GSLT.discrete Unit
def boolTheory : GSLT := GSLT.discrete Bool

def documentRoute : ConstructionTree algebra .operationalTheory :=
  .apply .freeDocument (.cons (.source unitTheory) .nil)

def sumRoute : ConstructionTree algebra .operationalTheory :=
  .apply .disjointSum
    (.cons documentRoute (.cons (.source boolTheory) .nil))

/-- Positive: provenance evaluates to the real free-document construction. -/
theorem documentRoute_evaluates :
    algebra.evaluate documentRoute = GSLT.freeDocument unitTheory :=
  rfl

/-- Positive: operational-theory composition is the real disjoint sum, not a
parallel model of it. -/
theorem sumRoute_evaluates :
    algebra.evaluate sumRoute =
      GSLT.disjointSum (GSLT.freeDocument unitTheory) boolTheory :=
  rfl

def baseLanguage : LanguageDef := LanguageDef.empty "construction:base"

def proofCalculus : ProofCalculus :=
  { judgments := [{ head := "ConstructionJudgment", arity := 1 }] }

def attachedCalculusRoute : ConstructionTree algebra .calculusLanguage :=
  .apply .attachCalculus
    (.cons (.source ⟨baseLanguage⟩) (.cons (.source ⟨proofCalculus⟩) .nil))

def erasedCalculusRoute : ConstructionTree algebra .language :=
  .apply .eraseCalculus (.cons attachedCalculusRoute .nil)

/-- Positive: the flat calculus language is produced by the canonical
coGSLT-licensed extension operation. -/
theorem attachedCalculusRoute_evaluates :
    (algebra.evaluate attachedCalculusRoute).down =
      CalculusLanguageDef.extend baseLanguage proofCalculus :=
  rfl

/-- Positive: ordinary erasure recovers exactly the language coordinate. -/
theorem erasedCalculusRoute_evaluates :
    (algebra.evaluate erasedCalculusRoute).down = baseLanguage :=
  rfl

private def firstType : TypeDecl :=
  TypeDecl.plain "construction:first"

private def secondType : TypeDecl :=
  TypeDecl.plain "construction:second"

def firstExtension : CalculusLanguageExtension :=
  { newTypes := [firstType] }

def secondExtension : CalculusLanguageExtension :=
  { newTypes := [secondType] }

def emptyCalculusLanguage : CalculusLanguageDef :=
  CalculusLanguageDef.extend baseLanguage ProofCalculus.empty

def composedExtensionRoute : ConstructionTree algebra .calculusExtension :=
  .apply .composeCalculusExtensions
    (.cons (.source ⟨firstExtension⟩) (.cons (.source ⟨secondExtension⟩) .nil))

def composedThenAppliedRoute : ConstructionTree algebra .calculusLanguage :=
  .apply .applyCalculusExtension
    (.cons composedExtensionRoute (.cons (.source ⟨emptyCalculusLanguage⟩) .nil))

def firstAppliedRoute : ConstructionTree algebra .calculusLanguage :=
  .apply .applyCalculusExtension
    (.cons (.source ⟨firstExtension⟩)
      (.cons (.source ⟨emptyCalculusLanguage⟩) .nil))

def appliedSequentiallyRoute : ConstructionTree algebra .calculusLanguage :=
  .apply .applyCalculusExtension
    (.cons (.source ⟨secondExtension⟩) (.cons firstAppliedRoute .nil))

/-- Positive: composing field-aware deltas and then applying them agrees with
sequential application. -/
theorem composed_and_sequential_routes_agree :
    (algebra.evaluate composedThenAppliedRoute).down =
      (algebra.evaluate appliedSequentiallyRoute).down :=
  CalculusLanguageExtension.comp_apply
    firstExtension secondExtension emptyCalculusLanguage

/-- Positive: the lawful merger retains execution order in the flat result. -/
theorem composed_route_type_order :
    (algebra.evaluate composedThenAppliedRoute).down.types =
      [firstType, secondType] :=
  rfl

def reversedExtensionRoute : ConstructionTree algebra .calculusExtension :=
  .apply .composeCalculusExtensions
    (.cons (.source ⟨secondExtension⟩) (.cons (.source ⟨firstExtension⟩) .nil))

def reversedThenAppliedRoute : ConstructionTree algebra .calculusLanguage :=
  .apply .applyCalculusExtension
    (.cons reversedExtensionRoute (.cons (.source ⟨emptyCalculusLanguage⟩) .nil))

/-- Negative: field-aware extension composition is not silently commutative;
authored declaration order is observable. -/
theorem reversed_route_differs :
    (algebra.evaluate composedThenAppliedRoute).down ≠
      (algebra.evaluate reversedThenAppliedRoute).down := by
  intro equality
  have typeRows := congrArg
    (fun definition : CalculusLanguageDef => definition.types) equality
  change [firstType, secondType] = [secondType, firstType] at typeRows
  simp [firstType, secondType, TypeDecl.plain] at typeRows

def attachedReceipt : (constructionReceiptLayer algebra).Total :=
  constructionReceiptLayer.record algebra attachedCalculusRoute

def makeAttached : ConstructionCommand algebra :=
  .make ⟨.calculusLanguage, attachedCalculusRoute⟩

def readyAttached : ConstructionCommand algebra :=
  .ready attachedReceipt

/-- Positive: the companion construction coGSLT executes an actual language
assembly route and retains its exact receipt. -/
theorem makeAttached_step :
    (constructionProvenanceGSLT algebra).Step makeAttached readyAttached := by
  change ConstructionCommandStep algebra makeAttached readyAttached
  simpa [makeAttached, readyAttached, attachedReceipt] using
    (ConstructionCommandStep.make (algebra := algebra) attachedCalculusRoute)

#print axioms documentRoute_evaluates
#print axioms sumRoute_evaluates
#print axioms attachedCalculusRoute_evaluates
#print axioms erasedCalculusRoute_evaluates
#print axioms composed_and_sequential_routes_agree
#print axioms composed_route_type_order
#print axioms reversed_route_differs
#print axioms makeAttached_step

end Canary

end Mettapedia.GSLT.LanguageDef.ConstructionProvenance.LanguageConstruction
