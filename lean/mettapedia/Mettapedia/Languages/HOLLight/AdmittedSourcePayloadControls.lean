import Mettapedia.Languages.HOLLight.AdmittedSourcePayloads
import Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls
import Mettapedia.Languages.HOLLight.AdmittedPrimitiveModels
import Mettapedia.Tools.StageData

/-!
# Ordered payload extraction from the admitted Vector declaration

The actual admitted block and its registered reading determine the payload.
Arithmetic operations are supplied by the source environment; no constructor
field list is supplied independently to the extraction function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.AdmittedSourcePayloadControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.TypeTheory
open Mettapedia.GSLT.LanguageDef
open IndexedPolynomial.Description

noncomputable def declaredVectorFields (arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol) : List (List (HOL.Ty AtomicTy)) :=
  AdmittedSourcePayloads.fields AdmittedContainerGeneratedControls.block
    AdmittedContainerGeneratedControls.registered (IndexedInductiveHOLRealization.reading arithmetic Bool)

def vectorFields (arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol) : List (List (HOL.Ty AtomicTy)) :=
  stagedData% (stageValue% [
    Mettapedia.Languages.HOLLight.AdmittedSourcePayloads,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerGeneratedControls,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL,
    Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec,
    Mettapedia.Logic.HOL.IndexedContainerPositionTerms,
    Mettapedia.Logic.HOL.IndexedConstructorTerms,
    Mettapedia.TypeTheory, List, Fin]
      (AdmittedSourcePayloads.fields AdmittedContainerGeneratedControls.block
        AdmittedContainerGeneratedControls.registered (IndexedInductiveHOLRealization.reading arithmetic Bool)))

theorem vectorFields_declared (arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol) :
    vectorFields arithmetic = declaredVectorFields arithmetic :=
  eq_of_heq (stagedHEq% vectorFields arithmetic, declaredVectorFields arithmetic)

def vectorPayload (arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol) : Ty :=
  AdmittedSourcePayloads.payload (vectorFields arithmetic)

theorem vectorPayload_toHOL (arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol) :
    (vectorPayload arithmetic).toHOL = HOL.FiniteConstructorEncoding.payloadType (vectorFields arithmetic) :=
  AdmittedSourcePayloads.payload_toHOL _

theorem vectorFields_order (arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol) :
    vectorFields arithmetic = [[], [arithmetic.number, arithmetic.element]] := by
  rfl

theorem vectorPayload_is_encoding (arithmetic : IndexedInductiveHOLTerms.Arithmetic Symbol) :
    (vectorPayload arithmetic).toHOL =
      HOL.FiniteConstructorEncoding.payloadType [[], [arithmetic.number, arithmetic.element]] := by
  rw [vectorPayload_toHOL, vectorFields_order]

def arithmetic (operations : AdmittedPrimitiveModels.Operations) : IndexedInductiveHOLTerms.Arithmetic Symbol :=
  ⟨operations.natural.number, .prop, operations.natural.zero, operations.natural.successor, operations.addition⟩

def payloadFromSource (operations : AdmittedPrimitiveModels.Operations) : Ty :=
  vectorPayload (arithmetic operations)

theorem payloadFromSource_exact (operations : AdmittedPrimitiveModels.Operations) :
    (payloadFromSource operations).toHOL =
      HOL.FiniteConstructorEncoding.payloadType [[], [operations.natural.number, .prop]] :=
  vectorPayload_is_encoding _

#print axioms vectorFields_order
#print axioms vectorPayload_is_encoding
#print axioms payloadFromSource_exact

end Mettapedia.Languages.HOLLight.AdmittedSourcePayloadControls
