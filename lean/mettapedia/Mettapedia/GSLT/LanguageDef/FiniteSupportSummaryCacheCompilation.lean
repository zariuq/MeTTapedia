import Mettapedia.GSLT.LanguageDef.FiniteSupportBitVecCompilation

/-!
# Certified lazy caching of finite-support summaries

A compiled rule may consult the support of the same dense substitution slot in
several side conditions.  Once a local finite-support inventory is admitted,
the slot's source list can be scanned at most once and its exact packed support
reused for the rest of that transaction.

The executable admission checks every slot support.  The refinement theorem
identifies cached membership with the source list for every slot and key.  A
separate bound proves that lazy construction performs at most one support
computation per distinct requested slot and never more computations than the
source request stream contains.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteSupportSummaryCacheCompilation

open FiniteEnvironmentCompilation
open FiniteSupportBitVecCompilation

universe uKey

variable {Key : Type uKey} [DecidableEq Key]

/-- A fixed-width dense slot vector of source support lists. -/
abbrev SupportVector (Key : Type uKey) (slotCount : Nat) :=
  Fin slotCount → List Key

/-- The cached artifact stores one exact packed summary per dense slot. -/
abbrev PackedSupportVector (inventory : Inventory Key) (slotCount : Nat) :=
  Fin slotCount → PackedSupport inventory

/-- Executable admission checks all dense slots in slot order. -/
def supportedVector? (inventory : Inventory Key) {slotCount : Nat}
    (supports : SupportVector Key slotCount) : Bool :=
  (List.ofFn supports).all fun support => supported? inventory support

/-- Compile every admitted source support to its dense bit-vector summary. -/
def encodeVector (inventory : Inventory Key) {slotCount : Nat}
    (supports : SupportVector Key slotCount) :
    PackedSupportVector inventory slotCount :=
  fun slot => encode inventory (supports slot)

/-- Admission of the whole vector supplies admission of every selected slot. -/
theorem supportedVector?_slot
    (inventory : Inventory Key) {slotCount : Nat}
    (supports : SupportVector Key slotCount)
    (accepted : supportedVector? inventory supports = true)
    (slot : Fin slotCount) :
    supported? inventory (supports slot) = true := by
  apply (List.all_eq_true.mp accepted)
  exact List.mem_ofFn.mpr ⟨slot, rfl⟩

/-- A successful source-vector admission. -/
structure AdmittedSupportVector (inventory : Inventory Key)
    (slotCount : Nat) where
  supports : SupportVector Key slotCount
  accepted : supportedVector? inventory supports = true

/-- Decidable fail-closed admission for a finite support vector. -/
def admitSupportVector (inventory : Inventory Key) {slotCount : Nat}
    (supports : SupportVector Key slotCount) :
    Option (AdmittedSupportVector inventory slotCount) :=
  if accepted : supportedVector? inventory supports = true then
    some { supports, accepted }
  else
    none

/-- Admission succeeds exactly when every dense slot has finite support in the
generated inventory. -/
theorem admitSupportVector_isSome
    (inventory : Inventory Key) {slotCount : Nat}
    (supports : SupportVector Key slotCount) :
    (admitSupportVector inventory supports).isSome = true ↔
      supportedVector? inventory supports = true := by
  simp [admitSupportVector]

/-- Cached slot summaries form a composable certified realization. -/
def supportSummaryRealization (inventory : Inventory Key)
    (slotCount : Nat) :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedSupportVector inventory slotCount)
      (PackedSupportVector inventory slotCount)
      (Fin slotCount → Key → Bool) where
  compile := fun _ admitted => encodeVector inventory admitted.supports
  observeSource := fun _ admitted slot key =>
    (admitted.supports slot).contains key
  observeArtifact := fun _ packed slot key =>
    decodeMember inventory (packed slot) key
  adequate := by
    intro _ admitted
    funext slot key
    exact decodeMember_encode inventory (admitted.supports slot)
      (supportedVector?_slot inventory admitted.supports
        admitted.accepted slot) key

/-- A support query names a dense slot and one source key observation. -/
structure SupportRequest (slotCount : Nat) (Key : Type uKey) where
  slot : Fin slotCount
  key : Key
deriving DecidableEq

/-- Repeated source execution scans the selected source support per request. -/
def runSource {slotCount : Nat} (supports : SupportVector Key slotCount)
    (requests : List (SupportRequest slotCount Key)) : List Bool :=
  requests.map fun request => (supports request.slot).contains request.key

/-- Cached execution observes the already packed slot summary. -/
def runCached (inventory : Inventory Key) {slotCount : Nat}
    (packed : PackedSupportVector inventory slotCount)
    (requests : List (SupportRequest slotCount Key)) : List Bool :=
  requests.map fun request =>
    decodeMember inventory (packed request.slot) request.key

/-- Every request stream has exactly the same source and cached result. -/
theorem runCached_encodeVector
    (inventory : Inventory Key) {slotCount : Nat}
    (supports : SupportVector Key slotCount)
    (accepted : supportedVector? inventory supports = true)
    (requests : List (SupportRequest slotCount Key)) :
    runCached inventory (encodeVector inventory supports) requests =
      runSource supports requests := by
  apply List.map_congr_left
  intro request _
  exact decodeMember_encode inventory (supports request.slot)
    (supportedVector?_slot inventory supports accepted request.slot)
    request.key

/-- Stateful cost model for lazy summary construction.  A slot already seen in
the current transaction incurs no second source-support scan. -/
def supportComputationCountAux {slotCount : Nat} (seen : List (Fin slotCount)) :
    List (SupportRequest slotCount Key) → Nat
  | [] => 0
  | request :: requests =>
      if seen.contains request.slot then
        supportComputationCountAux seen requests
      else
        1 + supportComputationCountAux (request.slot :: seen) requests

def supportComputationCount {slotCount : Nat}
    (requests : List (SupportRequest slotCount Key)) : Nat :=
  supportComputationCountAux [] requests

omit [DecidableEq Key] in
/-- Lazy support construction performs no more source scans than repeated
per-obligation support extraction. -/
theorem supportComputationCountAux_le {slotCount : Nat}
    (seen : List (Fin slotCount))
    (requests : List (SupportRequest slotCount Key)) :
    supportComputationCountAux seen requests ≤ requests.length := by
  induction requests generalizing seen with
  | nil => simp [supportComputationCountAux]
  | cons request requests ih =>
      simp only [supportComputationCountAux, List.length_cons]
      split
      · exact Nat.le_trans (ih seen) (Nat.le_succ _)
      · have bounded := Nat.succ_le_succ (ih (request.slot :: seen))
        omega

omit [DecidableEq Key] in
theorem supportComputationCount_le {slotCount : Nat}
    (requests : List (SupportRequest slotCount Key)) :
    supportComputationCount requests ≤ requests.length :=
  supportComputationCountAux_le [] requests

/-! ## Independent witnesses and rejection boundary -/

private inductive LexicalClass where
  | digit | letter | delimiter
deriving DecidableEq

private def lexicalInventory : Inventory LexicalClass where
  keys := [.digit, .letter, .delimiter]
  nodup := by decide

private def lexicalSupports : SupportVector LexicalClass 2
  | 0 => [.digit, .letter]
  | 1 => [.delimiter]

/-- A parser-like pair of dense character-class summaries is admitted. -/
example : (admitSupportVector lexicalInventory lexicalSupports).isSome = true := by
  decide

private inductive Resource where
  | channel | lock | continuation
deriving DecidableEq

private def resourceInventory : Inventory Resource where
  keys := [.channel, .lock, .continuation]
  nodup := by decide

private def resourceSupports : SupportVector Resource 2
  | 0 => [.channel, .continuation]
  | 1 => [.lock]

/-- A graph/process-like slot vector has the same exact cached observation. -/
example :
    let requests : List (SupportRequest 2 Resource) :=
      [⟨0, .continuation⟩, ⟨1, .channel⟩]
    runCached resourceInventory
        (encodeVector resourceInventory resourceSupports) requests =
      [true, false] := by
  decide

/-- Repeating one side-condition request computes its support summary once. -/
example :
    let request : SupportRequest 2 Resource := ⟨0, .channel⟩
    supportComputationCount [request, request] = 1 ∧
      [request, request].length = 2 := by
  decide

private inductive ExtendedClass where
  | known | absent
deriving DecidableEq

private def restrictedInventory : Inventory ExtendedClass where
  keys := [.known]
  nodup := by decide

private def unsupportedVector : SupportVector ExtendedClass 2
  | 0 => [.known]
  | 1 => [.absent]

/-- A single unsupported slot causes the entire cache admission to fail. -/
example :
    (admitSupportVector restrictedInventory unsupportedVector).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.FiniteSupportSummaryCacheCompilation
