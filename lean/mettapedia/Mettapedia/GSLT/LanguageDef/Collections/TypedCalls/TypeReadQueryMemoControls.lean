import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoRefinement
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCurrentReader
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRecursiveControls

/-! # Executable source controls for recursive retained-reply reuse -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypeCallGraph NativeTypeSourcePorts
open NativeTypeCurrentReader (external currentOps number box)
open TypeReadQueryMemo (State)

def row (name : String) (type_ : Atom) : Atom :=
  .expression [.symbol ":", .symbol name, type_]

def arrow (formals : List Atom) (range : Atom) : Atom :=
  .expression (.symbol "->" :: formals ++ [range])

def source : Source where
  rows := [row "Box" (arrow [.symbol "Number"] (.symbol "Actual")),
    row "Pair" (arrow [.symbol "Actual", .symbol "Actual"] (.symbol "Result")),
    row "Poly" (arrow [.symbol "Number"] (.expression [.symbol "Open", .var "element"]))]
  intrinsicRows := []
  rename := fun _ _ name => name
  subtypeBudget := 2
  subtypeFresh := "super"
  alpha := (· == ·)

def child : Call := .infer true (box number)
def root : Call := .infer true (.expression [.symbol "Pair", box number, box number])
def openCall : Call := .infer true (.expression [.symbol "Poly", number])
def initial : State := ⟨⟨[], 0⟩, []⟩
def childOnly (call : Call) : Bool := decide (call = child)

def run (src : Source) (authority : Nat) (allow : Call → Bool) (call : Call) (state : State) :=
  TypeReadQueryMemo.evaluate currentOps src external authority allow 8 call state

theorem source_safe : NativeTypeSourcePorts.Safe source := by
  unfold NativeTypeSourcePorts.Safe
  decide

/-- The second occurrence reuses the first child's completed reply while the
parent still performs its ordinary miss and checks both arguments. -/
theorem mixed_recursive_hits_preserve_result_and_skip_allocation :
    (run source 0 childOnly root initial).1 = some (.types [.symbol "Result"]) ∧
    RevisionedQueryFacts.lookup 0 child (run source 0 childOnly root initial).2.cache =
      some [.symbol "Actual"] ∧
    (run source 0 childOnly root initial).2.supply.next <
      (NativeTypeScopedReads.evaluate currentOps source external 8 root initial.supply).2.next := by cbv

def warm : State := (run source 0 (fun _ => true) root initial).2

theorem root_hit_leaves_supply_unchanged :
    run source 0 (fun _ => true) root warm = (some (.types [.symbol "Result"]), warm) := by cbv

theorem disabled_reuse_runs_the_source :
    (run source 0 (fun _ => false) root warm).1 = some (.types [.symbol "Result"]) ∧
    warm.supply.next < (run source 0 (fun _ => false) root warm).2.supply.next := by cbv

/-- A completed open family is not a persistent instance, even with a ground
subject and enabled caching. The next read still instantiates it afresh. -/
theorem open_reply_is_not_published :
    (run source 0 (fun _ => true) openCall initial).1.isSome = true ∧
    RevisionedQueryFacts.lookup 0 openCall (run source 0 (fun _ => true) openCall initial).2.cache = none ∧
    (run source 0 (fun _ => true) openCall initial).1 ≠
      (run source 0 (fun _ => true) openCall
        (run source 0 (fun _ => true) openCall initial).2).1 := by cbv; simp

theorem unfinished_closure_is_not_cached_as_empty :
    (run { NativeTypeCurrentReader.source with subtypeBudget := 0 } 0 (fun _ => true)
      (.infer true NativeTypeCurrentReader.twice) initial).1 = none ∧
    (run { NativeTypeCurrentReader.source with subtypeBudget := 0 } 0 (fun _ => true)
      (.infer true NativeTypeCurrentReader.twice) initial).2.cache = [] := by cbv

def forged : State := ⟨initial.supply, [⟨0, root, []⟩]⟩

theorem fabricated_empty_changes_answers :
    (run source 0 (fun _ => true) root forged).1 = some (.types []) ∧
    (NativeTypeScopedReads.evaluate currentOps source external 8 root initial.supply).1 =
      some (.types [.symbol "Result"]) := by cbv

def changed : Source := { source with
  rows := [row "Box" (arrow [.symbol "Number"] (.symbol "Actual")),
    row "Pair" (arrow [.symbol "Actual", .symbol "Actual"] (.symbol "Changed"))] }

theorem governing_change_requires_new_authority :
    (run changed 0 (fun _ => true) root warm).1 = some (.types [.symbol "Result"]) ∧
    (run changed 1 (fun _ => true) root warm).1 = some (.types [.symbol "Changed"]) := by cbv

/-- The general theorem is also instantiated, rather than relying only on
finite examples of the adapter. The supplied depth is a proved ghost bound. -/
theorem arbitrary_prior_allocation_keeps_closed_ordered_duplicates (supply : TypeReadSupply.Supply) :
    (TypeReadQueryMemo.evaluate currentOps NativeTypeCurrentReader.source external 0 (fun _ => true) 10000
      (.infer true NativeTypeCurrentReader.twice) ⟨supply, []⟩).1 =
      some (.types [.symbol "Claimed", .symbol "Parent", .symbol "Actual", .symbol "Actual"]) := by
  apply TypeReadQueryMemoRefinement.retained_evaluate_equal
    NativeTypeCurrentReader.source external TypeReadQueryRecursiveControls.annotated_source_safe
    TypeNormalizationNames.equality_equivariant id TypeReadQueryRecursiveControls.identity_normalizers
    (fun _ => []) 0 (fun _ => true) (.infer true NativeTypeCurrentReader.twice) 10000 10000
    (by decide) (by decide) TypeReadQueryRecursiveControls.initialWorld ⟨[], 0⟩ ⟨supply, []⟩
  · constructor <;>
      simp [TypeReadQueryRecursiveControls.initialWorld, TypeReadQueryWorlds.questionNames,
        NativeTypeCurrentReader.twice, number, atomVariables, atomListVariables]
  · exact ⟨TypeReadQueryRecursiveControls.supplies_protected _ _,
      TypeReadQueryMemoRefinement.empty_valid currentOps NativeTypeCurrentReader.source external 0⟩
  · cbv
  · decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoControls
