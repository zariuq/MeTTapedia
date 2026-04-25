import Mettapedia.Languages.MeTTa.HE.Space

/-!
# Bulk Transfer Soundness

This file states the list-level HE law used by CeTTa's evaluator shortcut for
the default `get-atoms`/`collapse`/`add-atoms` MeTTa pattern.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

namespace BulkTransferSoundness

def logicalRows (src : Space) : List Atom :=
  src.atoms

def collapseGetAtoms (src : Space) : List Atom :=
  logicalRows src

def evalAddAtomsRows (dst : Space) (rows : List Atom) : Space :=
  rows.foldr (fun row acc => Space.add acc row) dst

def evalAddAtomsCollapseGetAtoms (dst src : Space) : Space :=
  evalAddAtomsRows dst (collapseGetAtoms src)

def evalAddAtomsGetAtomsDirect (dst src : Space) : Space :=
  evalAddAtomsRows dst (logicalRows src)

def evalLetCollapseGetAtomsAddAtoms (dst src : Space) : Space :=
  let rows := collapseGetAtoms src
  evalAddAtomsRows dst rows

def optimizedBulkTransfer (dst src : Space) : Space :=
  Space.addMany dst (logicalRows src)

theorem evalAddAtomsRows_eq_addMany (dst : Space) (rows : List Atom) :
    evalAddAtomsRows dst rows = Space.addMany dst rows := by
  have hAtoms : (evalAddAtomsRows dst rows).atoms = rows ++ dst.atoms := by
    induction rows generalizing dst with
    | nil =>
        simp [evalAddAtomsRows]
    | cons row rows ih =>
        calc
          (evalAddAtomsRows dst (row :: rows)).atoms =
              row :: (evalAddAtomsRows dst rows).atoms := by
            rfl
          _ = row :: (rows ++ dst.atoms) := by
            rw [ih dst]
          _ = (row :: rows) ++ dst.atoms := by
            rfl
  cases dst with
  | mk dstAtoms =>
      cases hRows : evalAddAtomsRows { atoms := dstAtoms } rows with
      | mk outRows =>
          rw [hRows] at hAtoms
          simp [Space.addMany] at hAtoms ⊢
          exact hAtoms

theorem collapse_get_atoms_bulk_transfer_sound (dst src : Space) :
    evalAddAtomsCollapseGetAtoms dst src = optimizedBulkTransfer dst src := by
  simpa [evalAddAtomsCollapseGetAtoms, collapseGetAtoms, optimizedBulkTransfer]
    using evalAddAtomsRows_eq_addMany dst (logicalRows src)

theorem get_atoms_direct_bulk_transfer_sound (dst src : Space) :
    evalAddAtomsGetAtomsDirect dst src = optimizedBulkTransfer dst src := by
  simpa [evalAddAtomsGetAtomsDirect, optimizedBulkTransfer]
    using evalAddAtomsRows_eq_addMany dst (logicalRows src)

theorem let_collapse_get_atoms_bulk_transfer_sound (dst src : Space) :
    evalLetCollapseGetAtomsAddAtoms dst src = optimizedBulkTransfer dst src := by
  simpa [evalLetCollapseGetAtomsAddAtoms, collapseGetAtoms, optimizedBulkTransfer]
    using evalAddAtomsRows_eq_addMany dst (logicalRows src)

inductive TransferSurface where
  | generic
  | mork
  deriving DecidableEq, Repr

structure RoutedSpace where
  surface : TransferSurface
  space : Space
  deriving Repr

def routedRows (src : RoutedSpace) : List Atom :=
  logicalRows src.space

def evalRoutedTransfer (dst src : RoutedSpace) : RoutedSpace :=
  { dst with space := evalAddAtomsRows dst.space (routedRows src) }

def optimizedRoutedTransfer (dst src : RoutedSpace) : RoutedSpace :=
  { dst with space := Space.addMany dst.space (routedRows src) }

theorem routed_bulk_transfer_sound (dst src : RoutedSpace) :
    evalRoutedTransfer dst src = optimizedRoutedTransfer dst src := by
  cases dst
  simp [evalRoutedTransfer, optimizedRoutedTransfer, routedRows,
    evalAddAtomsRows_eq_addMany]

inductive AddSurface where
  | addAtoms
  | morkAddAtoms
  | custom (name : String)
  deriving DecidableEq, Repr

inductive SourceSurface where
  | getAtoms
  | morkGetAtoms
  | custom (name : String)
  deriving DecidableEq, Repr

inductive AddAtomsEquation where
  | defaultFold
  | custom (name : String)
  deriving DecidableEq, Repr

inductive AddAtomsInputShape where
  | literalRows
  | getAtomsDirect (source : SourceSurface)
  | collapseGetAtoms (source : SourceSurface)
  | other
  deriving DecidableEq, Repr

def AddSurface.isDefault : AddSurface → Bool
  | .addAtoms => true
  | .morkAddAtoms => true
  | .custom _ => false

def SourceSurface.isDefault : SourceSurface → Bool
  | .getAtoms => true
  | .morkGetAtoms => true
  | .custom _ => false

def AddAtomsEquation.isDefaultFold : AddAtomsEquation → Bool
  | .defaultFold => true
  | .custom _ => false

def hasDefaultFold : List AddAtomsEquation → Bool
  | [] => false
  | eq :: rest => eq.isDefaultFold || hasDefaultFold rest

def allDefaultFold : List AddAtomsEquation → Bool
  | [] => true
  | eq :: rest => eq.isDefaultFold && allDefaultFold rest

def publicSurfaceHasOnlyDefault
    (visible : List AddAtomsEquation) : Bool :=
  hasDefaultFold visible && allDefaultFold visible

def AddAtomsInputShape.hasDefaultSource : AddAtomsInputShape → Bool
  | .literalRows => false
  | .getAtomsDirect source => source.isDefault
  | .collapseGetAtoms source => source.isDefault
  | .other => false

def recognizePublicAddAtomsShortcut
    (visible : List AddAtomsEquation)
    (input : AddAtomsInputShape) : Option Unit :=
  if publicSurfaceHasOnlyDefault visible && input.hasDefaultSource then
    some ()
  else
    none

inductive PublicAddAtomsDecision where
  | shortcut
  | ordinaryEquationSearch
  deriving DecidableEq, Repr

def decidePublicAddAtoms
    (visible : List AddAtomsEquation)
    (input : AddAtomsInputShape) : PublicAddAtomsDecision :=
  match recognizePublicAddAtomsShortcut visible input with
  | some () => .shortcut
  | none => .ordinaryEquationSearch

def recognizeBulkTransfer
    (addSurface : AddSurface) (sourceSurface : SourceSurface)
    (collapsed : Bool) : Option Unit :=
  let routeIsSupported := collapsed || !collapsed
  if addSurface.isDefault && sourceSurface.isDefault && routeIsSupported then
    some ()
  else
    none

example :
    recognizeBulkTransfer .addAtoms .getAtoms true = some () := by
  rfl

example :
    recognizePublicAddAtomsShortcut
      [.defaultFold] (.collapseGetAtoms .getAtoms) = some () := by
  rfl

example :
    recognizePublicAddAtomsShortcut
      [.defaultFold] (.getAtomsDirect .getAtoms) = some () := by
  rfl

example :
    recognizePublicAddAtomsShortcut
      [.defaultFold, .custom "add-atoms"] (.collapseGetAtoms .getAtoms) =
        none := by
  rfl

example :
    recognizePublicAddAtomsShortcut
      [.defaultFold, .custom "add-atoms"] (.getAtomsDirect .getAtoms) =
        none := by
  rfl

example :
    decidePublicAddAtoms
      [.defaultFold, .custom "add-atoms"] (.collapseGetAtoms .getAtoms) =
        .ordinaryEquationSearch := by
  rfl

example :
    recognizePublicAddAtomsShortcut
      [.defaultFold] (.collapseGetAtoms (.custom "guard-get-atoms")) =
        none := by
  rfl

theorem public_shortcut_implies_visible_default
    (visible : List AddAtomsEquation) (input : AddAtomsInputShape)
    (h : recognizePublicAddAtomsShortcut visible input = some ()) :
    publicSurfaceHasOnlyDefault visible = true := by
  unfold recognizePublicAddAtomsShortcut at h
  by_cases hv : publicSurfaceHasOnlyDefault visible
  · exact hv
  · simp [hv] at h

theorem public_shortcut_implies_default_source
    (visible : List AddAtomsEquation) (input : AddAtomsInputShape)
    (h : recognizePublicAddAtomsShortcut visible input = some ()) :
    input.hasDefaultSource = true := by
  unfold recognizePublicAddAtomsShortcut at h
  by_cases hv : publicSurfaceHasOnlyDefault visible
  · by_cases hi : input.hasDefaultSource
    · exact hi
    · simp [hv, hi] at h
  · simp [hv] at h

theorem visible_custom_same_head_blocks_shortcut
    (input : AddAtomsInputShape) :
    recognizePublicAddAtomsShortcut
      [.defaultFold, .custom "add-atoms"] input = none := by
  cases input <;> rfl

example :
    AddSurface.isDefault .addAtoms = true := by
  rfl

example :
    AddSurface.isDefault (.custom "add-atoms") = false := by
  rfl

example :
    recognizeBulkTransfer .morkAddAtoms .morkGetAtoms false = some () := by
  rfl

example :
    recognizeBulkTransfer (.custom "guard-add-atoms") .getAtoms true = none := by
  rfl

example :
    recognizeBulkTransfer .addAtoms (.custom "guard-get-atoms") true = none := by
  rfl

inductive EndpointStorage where
  | counted
  | structural
  deriving DecidableEq, Repr

structure RowContract where
  count : Nat
  exactContext : Bool
  deriving DecidableEq, Repr

def EndpointStorage.admitRow : EndpointStorage → RowContract → RowContract
  | .counted, row => row
  | .structural, row =>
      { count := if row.count = 0 then 0 else 1, exactContext := false }

def transferContractMatrix
    (dst src : EndpointStorage) (row : RowContract) : RowContract :=
  match src with
  | .counted => dst.admitRow row
  | .structural => dst.admitRow row

def evalDefaultEndpointInput
    (input : AddAtomsInputShape) (dst src : Space) : Option Space :=
  match input with
  | .getAtomsDirect source =>
      if source.isDefault then
        some (evalAddAtomsGetAtomsDirect dst src)
      else
        none
  | .collapseGetAtoms source =>
      if source.isDefault then
        some (evalAddAtomsCollapseGetAtoms dst src)
      else
        none
  | .literalRows => none
  | .other => none

def endpointTransferSemantics
    (dstStorage srcStorage : EndpointStorage)
    (input : AddAtomsInputShape)
    (dst src : Space)
    (rows : List RowContract) : Option (Space × List RowContract) :=
  Option.map
    (fun atomSpace =>
      (atomSpace, rows.map (transferContractMatrix dstStorage srcStorage)))
    (evalDefaultEndpointInput input dst src)

theorem counted_endpoint_preserves_row_contract (row : RowContract) :
    transferContractMatrix .counted .counted row = row := by
  rfl

theorem counted_endpoint_preserves_structural_row_contract
    (row : RowContract) :
    transferContractMatrix .counted .structural row = row := by
  rfl

theorem structural_endpoint_clears_exact_context
    (src : EndpointStorage) (row : RowContract) :
    (transferContractMatrix .structural src row).exactContext = false := by
  cases src <;> simp [transferContractMatrix, EndpointStorage.admitRow]

theorem structural_endpoint_coalesces_positive_count
    (src : EndpointStorage) (n : Nat) (ctx : Bool) :
    (transferContractMatrix .structural src
      { count := n + 1, exactContext := ctx }).count = 1 := by
  cases src <;> simp [transferContractMatrix, EndpointStorage.admitRow]

theorem structural_endpoint_preserves_zero_count
    (src : EndpointStorage) (ctx : Bool) :
    (transferContractMatrix .structural src
      { count := 0, exactContext := ctx }).count = 0 := by
  cases src <;> rfl

theorem default_endpoint_input_sound
    (input : AddAtomsInputShape) (dst src : Space)
    (h : input.hasDefaultSource = true) :
    evalDefaultEndpointInput input dst src =
      some (optimizedBulkTransfer dst src) := by
  cases input with
  | literalRows =>
      simp [AddAtomsInputShape.hasDefaultSource] at h
  | other =>
      simp [AddAtomsInputShape.hasDefaultSource] at h
  | getAtomsDirect source =>
      cases source <;>
        simp [AddAtomsInputShape.hasDefaultSource, evalDefaultEndpointInput,
          SourceSurface.isDefault, get_atoms_direct_bulk_transfer_sound] at h ⊢
  | collapseGetAtoms source =>
      cases source <;>
        simp [AddAtomsInputShape.hasDefaultSource, evalDefaultEndpointInput,
          SourceSurface.isDefault, collapse_get_atoms_bulk_transfer_sound] at h ⊢

theorem recognized_endpoint_transfer_sound
    (visible : List AddAtomsEquation)
    (input : AddAtomsInputShape)
    (dstStorage srcStorage : EndpointStorage)
    (dst src : Space)
    (rows : List RowContract)
    (h : recognizePublicAddAtomsShortcut visible input = some ()) :
    endpointTransferSemantics dstStorage srcStorage input dst src rows =
      some (optimizedBulkTransfer dst src,
            rows.map (transferContractMatrix dstStorage srcStorage)) := by
  have hSource : input.hasDefaultSource = true :=
    public_shortcut_implies_default_source visible input h
  unfold endpointTransferSemantics
  rw [default_endpoint_input_sound input dst src hSource]
  rfl

example :
    transferContractMatrix .structural .counted
      { count := 2, exactContext := true } =
        { count := 1, exactContext := false } := by
  rfl

example :
    transferContractMatrix .counted .structural
      { count := 1, exactContext := false } =
        { count := 1, exactContext := false } := by
  rfl

example :
    endpointTransferSemantics .structural .counted
      (.collapseGetAtoms .getAtoms)
      { atoms := [Atom.symbol "dst"] }
      { atoms := [Atom.symbol "src"] }
      [{ count := 2, exactContext := true }] =
        some ({ atoms := [Atom.symbol "src", Atom.symbol "dst"] },
              [{ count := 1, exactContext := false }]) := by
  simp [endpointTransferSemantics, evalDefaultEndpointInput,
    SourceSurface.isDefault, evalAddAtomsCollapseGetAtoms,
    evalAddAtomsRows_eq_addMany, collapseGetAtoms, logicalRows,
    transferContractMatrix, EndpointStorage.admitRow, Space.addMany]

end BulkTransferSoundness

end Mettapedia.Languages.MeTTa.HE
