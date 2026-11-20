import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.SourceStorage
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMixedSourceExecution

/-!
# Retained native import composes with the actual held read execution

The imported cell is the complete original row, not just an equal payload at
one model. Loading fails as an option if the physical cell is not present. Exact
retention reconstructs the independent logical source and licenses its actual
two-step protocol, preserving the decoded live view and resource identities.
The heap/source representation relation is the explicit native boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.StorageExecution

open Interface (Frames)
open Mettapedia.Machines.ResourceOwnership
open RuleOccurrences HeldReadEncoding

universe uO uT uH uE
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O Address Owner : Type} [DecidableEq O] [DecidableEq Address]
  {E : Extensions.{uO, uH, uE} Hom}

def importSource (source : State Tm O) (heap : Heap Address (Row Tm source.frame))
    (address : O → Address) (selected : O) : Option (State Tm O) :=
  (SourceStorage.load heap address selected).map fun row =>
    { source with label := Function.update source.label selected row }

theorem import_retained (source : State Tm O) (rows : List O)
    (heap : Heap Address (Row Tm source.frame)) (address : O → Address)
    (represented : SourceStorage.RepresentsOn source rows heap address) (roots : Roots Owner Address)
    (retained : RequestBorrow.retentionCheck heap roots (rows.map address) = true)
    (selected : O) (member : selected ∈ rows) :
    importSource source (collect heap roots) address selected = some source := by
  unfold importSource
  rw [SourceStorage.retained_load_exact source rows heap address represented roots retained selected member]
  simp only [Option.map_some, Function.update_eq_self]

theorem borrowed_read_executes
    (source : State Tm O) (rows : List O)
    (heap : Heap Address (Row Tm source.frame)) (address : O → Address)
    (represented : SourceStorage.RepresentsOn source rows heap address) (roots : Roots Owner Address)
    (retained : RequestBorrow.retentionCheck heap roots (rows.map address) = true)
    (selected output : O) (member : selected ∈ rows) (extension : E.Ext source.frame)
    (ruleOpening datumOpening : Hom (closure (source.label selected)).schema.locals (E.target extension))
    (schematic : sharedTag (source.label selected) = false) (filler : Tm source.frame) (X : Frames Tm Hom)
    (temporary : O) (ambient : Set (HeldReadEncoding.Code Tm))
    (available : Sum.inr (HeldReadGenericFirings.consumeRule (closure (source.label selected)).schema) ∈ ambient)
    (temporaryFresh : temporary ∉ (encode source filler).present) (different : temporary ≠ output)
    (admitted : (HeldReadMixedSourceAdapter.direct source selected output extension
      ruleOpening datumOpening schematic).Admits X) :
    importSource source (collect heap roots) address selected = some source ∧
      ∃ run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := O) X ambient).Run (encode source filler),
        run.word.length = 2 ∧
        LiveObservations.observe
          (HeldReadMixedSourceAdapter.decodeResult source selected output extension
            ruleOpening datumOpening filler X temporary) =
          LiveObservations.observe
            ((HeldReadMixedSourceAdapter.direct source selected output extension
              ruleOpening datumOpening schematic).result X) ∧
        Disjoint run.last.present run.last.rules := by
  refine ⟨import_retained source rows heap address represented roots retained selected member, ?_⟩
  obtain ⟨run, length, _, observations, disjoint⟩ :=
    HeldReadMixedSourceAdapter.actual_execution_of_original source selected output extension
      ruleOpening datumOpening schematic filler X temporary ambient available temporaryFresh different admitted
  exact ⟨run, length, observations, disjoint⟩

#print axioms import_retained
#print axioms borrowed_read_executes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.StorageExecution
