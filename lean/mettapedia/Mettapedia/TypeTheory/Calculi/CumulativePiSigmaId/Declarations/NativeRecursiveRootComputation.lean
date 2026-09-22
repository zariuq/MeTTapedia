import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativePayloadSchemaCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRecursiveSchemaCertificates

/-!
# Computed certificates for the recursive List and relational List roots

The outer eliminator supplies its parameter certificates. Recovering its
constructor argument supplies the selected heads, tails and relational
witnesses. The shared schema compiler finds the argument positions from the
open declaration data and assembles the original schema's checked substitution.
Instantiating the fixed recursive right-hand-side
certificate computes the result, including the recursive call, then replays
the source's displayed-type adjustment.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.RecursiveRootComputation

open Presentation NativeIndexedFamilies DeclarationSpineReplay

set_option maxRecDepth 10000 in
/-- Recovery from the constructor payload is compiled once, in the original
schema context, before ambient substitution can identify distinct variables. -/
def listPlan : PayloadSchemaCompilation.Plan RecursiveSchemaCertificates.listCons :=
  (PayloadSchemaCompilation.compile RecursiveSchemaCertificates.listCons
    Intrinsic.consIotaLeft 4).get (by decide +kernel)

def listPositions : Fin 6 → Nat := listPlan.positions

private def listPayload : Tower.Tm 6 := Intrinsic.consApp (.var 5) (.var 1) (.var 0)

set_option maxRecDepth 10000 in
theorem list_schema_positions :
    ∀ index : Fin 6, (combinedArguments Intrinsic.consIotaLeft listPayload).bind
        (fun entries => entries[listPositions index]?) =
      some (.var index, Ctx.lookup Intrinsic.contextAPZSHeadTail index) :=
  listPlan.rows

def listCons {n : Nat} (contextCode : ContextCode n)
    (element motive nilCase consCase head tail displayed : Tower.Tm n) (code : Code n) :
    Option (Code n) :=
  listPlan.execute contextCode displayed code
    (Intrinsic.consSchemaSubstitution element motive nilCase consCase head tail)

theorem listCons_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {element motive nilCase consCase head tail displayed : Tower.Tm n} {code : Code n}
    (accepted : check context
      (Intrinsic.eliminateApp element motive nilCase consCase (Intrinsic.consApp element head tail))
      displayed contextCode code = true) :
    ∃ output, listCons contextCode element motive nilCase consCase head tail displayed code = some output ∧
      check context (.app (.app (.app consCase head) tail)
        (Intrinsic.eliminateApp element motive nilCase consCase tail)) displayed contextCode output = true := by
  exact listPlan.execute_checked
    (Intrinsic.consSchemaSubstitution element motive nilCase consCase head tail) accepted

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def relationPlan : PayloadSchemaCompilation.Plan RecursiveSchemaCertificates.relCons :=
  (PayloadSchemaCompilation.compile RecursiveSchemaCertificates.relCons
    IntrinsicRelator.consIotaLeft 8).get (by decide +kernel)

def relationPositions : Fin 12 → Nat := relationPlan.positions

private def relationPayload : Tower.Tm 12 :=
  IntrinsicRelator.consRelApp (.var 11) (.var 10) (.var 9) (.var 5) (.var 4)
    (.var 3) (.var 2) (.var 1) (.var 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem relation_schema_positions :
    ∀ index : Fin 12, (combinedArguments IntrinsicRelator.consIotaLeft relationPayload).bind
        (fun entries => entries[relationPositions index]?) =
      some (.var index, Ctx.lookup
        IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail index) :=
  relationPlan.rows

def relCons {n : Nat} (contextCode : ContextCode n)
    (source target relation motive nilCase consCase sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence displayed : Tower.Tm n) (code : Code n) : Option (Code n) :=
  relationPlan.execute contextCode displayed code
    (FormationSensitiveNativeRelatorElimination.consSchemaSubstitution source target relation
      motive nilCase consCase sourceHead targetHead sourceTail targetTail headEvidence tailEvidence)

theorem relCons_checked {n : Nat} {context : Tower.Ctx n} {contextCode : ContextCode n}
    {source target relation motive nilCase consCase sourceHead targetHead sourceTail targetTail
      headEvidence tailEvidence displayed : Tower.Tm n} {code : Code n}
    (accepted : check context
      (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.consApp source sourceHead sourceTail) (Intrinsic.consApp target targetHead targetTail)
        (IntrinsicRelator.consRelApp source target relation sourceHead targetHead
          sourceTail targetTail headEvidence tailEvidence)) displayed contextCode code = true) :
    ∃ output, relCons contextCode source target relation motive nilCase consCase sourceHead targetHead
        sourceTail targetTail headEvidence tailEvidence displayed code = some output ∧
      check context (.app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead)
        sourceTail) targetTail) headEvidence) tailEvidence)
        (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase sourceTail targetTail tailEvidence))
        displayed contextCode output = true := by
  exact relationPlan.execute_checked
    (FormationSensitiveNativeRelatorElimination.consSchemaSubstitution source target relation
      motive nilCase consCase sourceHead targetHead sourceTail targetTail headEvidence tailEvidence) accepted

#print axioms listPlan
#print axioms relationPlan
#print axioms list_schema_positions
#print axioms listCons_checked
#print axioms relation_schema_positions
#print axioms relCons_checked

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.RecursiveRootComputation
