import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoHistory
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoControls

/-! # Actual scoped-query controls through edits, imports and invalidation -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadScopeMemo
open NativeTypeCurrentReader (external currentOps)
open TypeReadQueryMemoControls (row root child)

def configuration : Source := TypeReadQueryMemoControls.source

def pairRow : Atom := row "Pair"
  (TypeReadQueryMemoControls.arrow [.symbol "Actual", .symbol "Actual"] (.symbol "Result"))
def changedPair : Atom := row "Pair"
  (TypeReadQueryMemoControls.arrow [.symbol "Actual", .symbol "Actual"] (.symbol "Changed"))
def boxRow : Atom := row "Box" (TypeReadQueryMemoControls.arrow [.symbol "Number"] (.symbol "Actual"))
def changedBox : Atom := row "Box" (TypeReadQueryMemoControls.arrow [.symbol "Number"] (.symbol "Other"))

def locals (id : Fin 3) : NativeTypingScopeEdits.State :=
  ⟨⟨id.val, 0, if id = 0 then [pairRow] else if id = 2 then [boxRow] else []⟩, 0, 0⟩

def imported : NativeTypingScopeImports.State 3 :=
  NativeTypingScopeImports.step (NativeTypingScopeImports.initialState 91 locals) (.importModule 0 2)

def scope : Scope 3 := ⟨imported, 0, [], 71, 0, 0⟩
def cold : Session 3 := initial scope ⟨[], 0⟩
def run (session : Session 3) := query currentOps configuration external (fun _ => true) 10000 root session
def warm : Session 3 := (run cold).2

theorem cold_query_uses_imported_constructor :
    (run cold).1 = some (.types [.symbol "Result"]) ∧ warm.inference.cache ≠ [] := by cbv; simp

theorem admitted_source : TypeReadSourceProjection.ready (rawSource configuration scope) = true := by decide

theorem warm_cache_valid : Valid currentOps configuration external warm := by
  obtain ⟨_, _, _, _, valid⟩ := query_related configuration external id
    TypeReadQueryRecursiveControls.identity_normalizers (fun _ => []) (fun _ => true)
    10000 root cold (initial_valid currentOps configuration external scope ⟨[], 0⟩)
    admitted_source TypeNormalizationNames.equality_equivariant (by decide)
  exact valid

def unrelated : List (NativeTypingScopeOverlays.Action 3) :=
  [.source (.edit 1 (.append changedPair))]

theorem unrelated_declaration_keeps_cache :
    (refresh warm unrelated).authority = warm.authority ∧
    (refresh warm unrelated).inference.cache = warm.inference.cache ∧
    (run (refresh warm unrelated)).1 = some (.types [.symbol "Result"]) := by cbv

def changedLocal : List (NativeTypingScopeOverlays.Action 3) :=
  [.source (.edit 0 (.replace 0 changedPair))]

theorem relevant_change_clears_before_query :
    (refresh warm changedLocal).authority = warm.authority + 1 ∧
    (refresh warm changedLocal).inference.cache = [] ∧
    (run (refresh warm changedLocal)).1 = some (.types [.symbol "Changed"]) := by cbv

def changedImport : List (NativeTypingScopeOverlays.Action 3) :=
  [.source (.edit 2 (.replace 0 changedBox))]

/-- The new empty family is an actually completed failed type application,
not an unfinished lookup converted into absence. -/
theorem imported_change_recomputes_completed_negative :
    (refresh warm changedImport).inference.cache = [] ∧
    (run (refresh warm changedImport)).1 = some (.types []) := by cbv

def restored : List (NativeTypingScopeOverlays.Action 3) :=
  [.source (.edit 0 (.replace 0 changedPair)), .source (.edit 0 (.replace 0 pairRow))]

theorem restored_contents_do_not_restore_authority :
    snapshot configuration (refresh warm restored).scope = snapshot configuration warm.scope ∧
    (refresh warm restored).authority = warm.authority + 1 ∧
    (refresh warm restored).inference.cache = [] := by cbv

theorem refreshed_cache_valid :
    Valid currentOps configuration external (refresh warm changedImport) :=
  refresh_valid currentOps configuration external warm warm_cache_valid changedImport

def nested : Session 3 := initial NativeTypingScopeOverlays.Controls.nested ⟨[], 0⟩
def nestedWarm : Session 3 :=
  (query currentOps configuration external (fun _ => true) 10000
    (.infer true (.expression [.symbol "a"])) nested).2
def shifted : List (NativeTypingScopeOverlays.Action 3) := [.source (.edit 0 (.erase 0))]

theorem data_only_shift_still_clears_inherited_cache :
    ((refresh nestedWarm shifted).scope.source.sources 0).typingRevision =
      (nestedWarm.scope.source.sources 0).typingRevision ∧
    (refresh nestedWarm shifted).inference.cache = [] ∧
    (refresh nestedWarm shifted).authority = nestedWarm.authority + 1 := by cbv

def unboundedScope : Scope 3 :=
  { NativeTypingScopeOverlays.Controls.nested with layers := [⟨3, ∅, []⟩] }
def unboundedWarm : Session 3 :=
  (query currentOps configuration external (fun _ => true) 10000
    (.infer true (.expression [.symbol "a"])) (initial unboundedScope ⟨[], 0⟩)).2
def appendedIntoCeiling : List (NativeTypingScopeOverlays.Action 3) :=
  [.source (.edit 0 (.append NativeTypingScopeOverlays.Controls.row))]

/-- Token equality alone is insufficient when the saved inherited ceiling
extends beyond the old source. The executable admission clears rather than
assuming that unreachable malformed metadata cannot occur. -/
theorem invalid_inherited_bound_blocks_false_reuse :
    NativeTypingScopeOverlays.check
      (NativeTypingScopeOverlays.execute unboundedWarm.scope appendedIntoCeiling)
      (NativeTypingScopeOverlays.token unboundedWarm.scope) = true ∧
    inheritedBound unboundedWarm.scope = false ∧
    (refresh unboundedWarm appendedIntoCeiling).inference.cache = [] ∧
    (query currentOps configuration external (fun _ => true) 10000
      (.infer true (.expression [.symbol "a"])) unboundedWarm).1 ≠
    (query currentOps configuration external (fun _ => true) 10000
      (.infer true (.expression [.symbol "a"])) (refresh unboundedWarm appendedIntoCeiling)).1 := by
  cbv
  simp

def mutableData : Atom := .expression [.symbol "ordinary-data", .grounded (.custom "Cell" "value")]
def withData : Source := { configuration with rows := mutableData :: configuration.rows }

theorem mutable_unrelated_data_is_admitted :
    TypeReadSourceProjection.ready withData = true ∧ ¬ NativeTypeSourcePorts.Safe withData := by
  constructor
  · decide
  · unfold NativeTypeSourcePorts.Safe
    decide

theorem admitted_projection_executes_the_same_reads (supply : TypeReadSupply.Supply) (depth : Nat) :
    NativeTypeScopedReads.evaluate currentOps (TypeReadSourceProjection.project withData)
      external depth root supply =
      NativeTypeScopedReads.evaluate currentOps withData external depth root supply :=
  TypeReadSourceProjection.evaluate_project currentOps withData external mutable_unrelated_data_is_admitted.1
    depth root supply

def opaqueRow : Atom := .grounded (.custom "Row" "value")
def revealing : RetainedTypePayloads.ExternalView := fun _ _ => row "K" (.symbol "Visible")

/-- Without the explicit outer-shape check, observing one opaque atom could
introduce a declaration that the captured raw packet did not contain. -/
theorem opaque_outer_shape_requires_decline :
    NativeTypingScopeCapture.freshScan [opaqueRow] = true ∧
    TypeReadSourceProjection.readyRows [opaqueRow] = false ∧
    getAnnotatedTypes (TypeDependencyAdmission.observedSpace revealing [opaqueRow]) (.symbol "K") =
      [.symbol "Visible"] ∧
    getAnnotatedTypes ⟨NativeTypingScopeCapture.capture [opaqueRow]⟩ (.symbol "K") = [] := by cbv

theorem caller_name_reserved_even_for_open_query :
    "caller" ∈ (reserve (.infer true (.expression [.symbol "Box", .var "caller"])) cold.inference).supply.used := by
  decide

def mixedHistory : List (TypeReadScopeMemoHistory.Event 3) :=
  [.query 10000 root, .refresh unrelated, .query 10000 root,
    .refresh changedLocal, .query 10000 root]

theorem mixed_history_bounded : ∀ event ∈ mixedHistory, TypeReadScopeMemoHistory.Bounded event := by
  intro event member
  simp only [mixedHistory, List.mem_cons] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | impossible
  · exact .query _ _ (by decide)
  · exact .refresh _
  · exact .query _ _ (by decide)
  · exact .refresh _
  · exact .query _ _ (by decide)
  · cases impossible

theorem mixed_history_keeps_earned_validity :
    Valid currentOps configuration external
      (TypeReadScopeMemoHistory.execute currentOps configuration external (fun _ => true) cold mixedHistory).2 :=
  TypeReadScopeMemoHistory.initialized_history_valid configuration external id
    TypeReadQueryRecursiveControls.identity_normalizers (fun _ => []) (fun _ => true)
    TypeNormalizationNames.equality_equivariant scope ⟨[], 0⟩ mixedHistory mixed_history_bounded

theorem mixed_history_observations :
    (TypeReadScopeMemoHistory.execute currentOps configuration external (fun _ => true) cold mixedHistory).1 =
      [.inquiry root (some (.types [.symbol "Result"])),
       .inquiry root (some (.types [.symbol "Result"])),
       .inquiry root (some (.types [.symbol "Changed"]))] := by cbv

def unsafeChange : List (NativeTypingScopeOverlays.Action 3) :=
  [.source (.edit 0 (.replace 0
    (row "Pair" (TypeReadQueryMemoControls.arrow [.symbol "Actual", .symbol "Actual"]
      (.grounded (.custom "TypeCell" "current"))))))]

theorem refused_request_is_not_a_completed_negative :
    request? currentOps configuration external (fun _ => true) 10000 root (refresh warm unsafeChange) = none ∧
    (TypeReadScopeMemoHistory.step currentOps configuration external (fun _ => true)
      (refresh warm unsafeChange) (.query 10000 root)).1 =
        some (.declined root) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoControls
