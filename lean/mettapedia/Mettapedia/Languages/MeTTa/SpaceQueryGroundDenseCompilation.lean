import Mettapedia.GSLT.LanguageDef.GroundDenseHeadCompilation
import Mettapedia.Languages.MeTTa.SpaceQueryCompilation

/-!
# Ground-dense equation matching lifted to space/query compilation

This module connects the generic space-at-revision realization to the
independently proved ground-dense term matcher used by CeTTa's conservative
equation-template path.  A successful equation match contributes one
environment occurrence; a failed match contributes none.  Lifting with
`spaceRealization` therefore preserves exact equation order and duplicate
matches across the complete space view.
-/

namespace Mettapedia.Languages.MeTTa.SpaceQueryGroundDenseCompilation

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.LanguageDef.GroundDenseHeadCompilation
open Mettapedia.Languages.MeTTa.LeafPatchViewKernel
open Mettapedia.Languages.MeTTa.SpaceQueryCompilation

variable {Symbol : Type} [DecidableEq Symbol]

/-- Re-observe one exact optional match as its zero-or-one occurrence bag. -/
def equationOccurrenceRealization (inventory : Inventory Nat) :
    SimpleRealization
      (AdmittedGroundHead (Symbol := Symbol) inventory)
      (DensePattern Symbol inventory.Slot)
      (Tm Symbol -> List (SourceEnvironment Nat (Tm Symbol))) :=
  (groundDenseHeadRealization (Symbol := Symbol) inventory).mapObservation
    (fun _ observe query => Option.toList (observe query))

/-- The concrete ground-dense matcher, lifted from one equation to an ordered
space view.  The source and compiled views share the same revision index. -/
def groundDenseSpaceRealization (inventory : Inventory Nat) :
    Realization
      (SpaceView Unit
        (AdmittedGroundHead (Symbol := Symbol) inventory))
      (CompiledSpaceView Unit
        (DensePattern Symbol inventory.Slot))
      (fun _ => Tm Symbol -> List (SourceEnvironment Nat (Tm Symbol))) :=
  spaceRealization (equationOccurrenceRealization (Symbol := Symbol) inventory)

/-- The compiled ground-dense space view and the independent source matcher
return the same ordered occurrence bag for every query. -/
theorem groundDenseSpace_observation_adequate (inventory : Inventory Nat)
    (space : SpaceView Unit
      (AdmittedGroundHead (Symbol := Symbol) inventory) ())
    (query : Tm Symbol) :
    (groundDenseSpaceRealization (Symbol := Symbol) inventory).observeArtifact
        () ((groundDenseSpaceRealization (Symbol := Symbol) inventory).compile
          () space) query =
      (groundDenseSpaceRealization (Symbol := Symbol) inventory).observeSource
        () space query :=
  congrFun
    ((groundDenseSpaceRealization (Symbol := Symbol) inventory).adequate
      () space) query

/-! ## Concrete duplicate and rejection controls -/

private def oneSlotInventory : Inventory Nat :=
  { keys := [0]
    nodup := by simp }

private def onlySlot : oneSlotInventory.Slot :=
  ⟨0, by decide⟩

private def repeatedSource : Pat String :=
  .node (.var 0) (.var 0)

private def repeatedCompiled :
    DensePattern String oneSlotInventory.Slot :=
  .node (.variable onlySlot) (.variable onlySlot)

private def repeatedAdmitted :
    AdmittedGroundHead (Symbol := String) oneSlotInventory :=
  { source := repeatedSource
    compiled := repeatedCompiled
    compile_eq := rfl }

private def duplicateSpace :
    SpaceView Unit
      (AdmittedGroundHead (Symbol := String) oneSlotInventory) () :=
  { equations := [repeatedAdmitted, repeatedAdmitted] }

private def equalQuery : Tm String :=
  .node (.sym "same") (.sym "same")

private def unequalQuery : Tm String :=
  .node (.sym "left") (.sym "right")

/-- Positive control: two authored occurrences remain two compiled match
occurrences, even though their equations are structurally identical. -/
example :
    ((groundDenseSpaceRealization (Symbol := String) oneSlotInventory).observeArtifact
      () ((groundDenseSpaceRealization (Symbol := String)
        oneSlotInventory).compile () duplicateSpace) equalQuery).length = 2 := by
  decide

/-- Negative control: a repeated-variable mismatch contributes no occurrence
from either duplicate equation. -/
example :
    (groundDenseSpaceRealization (Symbol := String)
      oneSlotInventory).observeArtifact ()
        ((groundDenseSpaceRealization (Symbol := String)
          oneSlotInventory).compile () duplicateSpace) unequalQuery = [] := by
  decide

end Mettapedia.Languages.MeTTa.SpaceQueryGroundDenseCompilation
