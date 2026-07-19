/-
# Authenticated discrete skeleton for GSLT2GSLT

This module is the Lean source of truth for the finite `org` operator table used by
the neural synthesis stack.  Operator names are boundary data; programs and masks
use `Nat` keys throughout.  Its sixteen rows are the exact memo-profile E2 table
used by the Python harness; the first fourteen have the same structural skeleton
as E1 and the last two are the memo-profile `push`/`pop` operators.

The canonicalization flags are not assertions attached to JSON.  A row can enter
`orgCertifiedCommFlags` only together with a proof against the E2 evaluator.  In
particular, scalar E1 commutativity does not transfer to memo lists because E2
retains the left operand's tail; explicit counterexamples below keep those flags
off in the runtime export.
-/

import Mathlib.Tactic
import Mettapedia.GSLT.InternedNames
import Mettapedia.GSLT.LanguageDef.Gauthier.BigStepGSLT
import Mettapedia.GSLT.LanguageDef.Gauthier.E2

namespace Mettapedia.GSLT.LanguageDef.GauthierSkeleton

open Mettapedia.GSLT.InternedNames
open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierBigStepGSLT

/-- Boundary names in exactly the integer-token order consumed by the runtime. -/
def orgMemoNames : Table :=
  { names :=
      [ "zero", "one", "two", "addi", "diff", "mult", "divi", "modu"
      , "cond", "loop", "x", "y", "compr", "loop2", "push", "pop"
      ] }

/--
The exact 16-row grammar skeleton used by `oeis_pc_harness.dsl`.

It reuses the established table-indexed `Signature` and `Prog` types and aliases
the actual E2 signature: no second program type or evaluator is introduced here.
-/
def orgMemoSignature : Signature Mettapedia.GSLT.LanguageDef.GauthierE2.Prim :=
  Mettapedia.GSLT.LanguageDef.GauthierE2.intlSignature

theorem orgMemoSignature_length : orgMemoSignature.length = 16 := rfl

theorem orgMemoNames_length : orgMemoNames.names.length = orgMemoSignature.length := rfl

/-- The E1 prefix and the memo grammar agree on names, arities, and higher-order arities. -/
theorem orgMemoSignature_e1_prefix :
    (orgMemoSignature.take orgE1Signature.length).map
        (fun e => (e.name, e.arity, e.hoArity)) =
      orgE1Signature.map (fun e => (e.name, e.arity, e.hoArity)) := by
  rfl

/-- Child roles are computed from the leading higher-order arity of a table row. -/
inductive ChildRole where
  | code
  | value
  deriving DecidableEq, Repr

def childRole (entry : Entry σ) (index : Nat) : ChildRole :=
  if index < entry.hoArity then .code else .value

def childRoles (entry : Entry σ) : List ChildRole :=
  (List.range entry.arity).map (childRole entry)

theorem childRoles_length (entry : Entry σ) :
    (childRoles entry).length = entry.arity := by
  simp [childRoles]

theorem childRoles_getElem (entry : Entry σ) (index : Nat)
    (hindex : index < (childRoles entry).length) :
    (childRoles entry)[index] =
      if index < entry.hoArity then ChildRole.code else ChildRole.value := by
  simp only [childRoles, List.getElem_map, List.getElem_range]
  rfl

/-! ## Semantic authentication of canonicalization flags -/

/-- Addition is commutative on the scalar E1 substrate. -/
theorem scalarOrg_addi_commutativeEvalLaw : commutativeEvalLaw orgE1Signature 3 :=
  addi_commutativeEvalLaw_of_entry
    (sig := orgE1Signature) orgE1Signature_storeNeutral
    (id := 3) (name := "addi") (arity := 2) (ho := 0) rfl

/-- Multiplication is commutative on the scalar E1 substrate. -/
theorem scalarOrg_mult_commutativeEvalLaw : commutativeEvalLaw orgE1Signature 5 :=
  mult_commutativeEvalLaw_of_entry
    (sig := orgE1Signature) orgE1Signature_storeNeutral
    (id := 5) (name := "mult") (arity := 2) (ho := 0) rfl

/-- The scalar addition law reaches the public GSLT observation boundary. -/
theorem scalarOrg_addi_emitsAt_swap_iff (fuel : Nat) (a b : Prog) (k v : Int) :
    EmitsAt orgE1Signature fuel (.node 3 [a, b]) k v ↔
      EmitsAt orgE1Signature fuel (.node 3 [b, a]) k v := by
  rw [emitsAt_iff, emitsAt_iff]
  constructor
  · rintro ⟨st', h⟩
    refine ⟨st', ?_⟩
    exact (scalarOrg_addi_commutativeEvalLaw fuel a b (seed k) Store.zero).symm.trans h
  · rintro ⟨st', h⟩
    refine ⟨st', ?_⟩
    exact (scalarOrg_addi_commutativeEvalLaw fuel a b (seed k) Store.zero).trans h

/-- The scalar multiplication law reaches the public GSLT observation boundary. -/
theorem scalarOrg_mult_emitsAt_swap_iff (fuel : Nat) (a b : Prog) (k v : Int) :
    EmitsAt orgE1Signature fuel (.node 5 [a, b]) k v ↔
      EmitsAt orgE1Signature fuel (.node 5 [b, a]) k v := by
  rw [emitsAt_iff, emitsAt_iff]
  constructor
  · rintro ⟨st', h⟩
    refine ⟨st', ?_⟩
    exact (scalarOrg_mult_commutativeEvalLaw fuel a b (seed k) Store.zero).symm.trans h
  · rintro ⟨st', h⟩
    refine ⟨st', ?_⟩
    exact (scalarOrg_mult_commutativeEvalLaw fuel a b (seed k) Store.zero).trans h

/-- The law a memo-profile `comm` flag would have to prove against the real E2 evaluator. -/
def memoCommutativeEvalLaw (id : Nat) : Prop :=
  ∀ fuel a b x y world,
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval fuel orgMemoSignature
        (.node id [a, b]) x y world =
      Mettapedia.GSLT.LanguageDef.GauthierE2.eval fuel orgMemoSignature
        (.node id [b, a]) x y world

def memoTailOne : Prog :=
  .node 14 [.node 1 [], .node 1 []]

def memoTailZero : Prog :=
  .node 14 [.node 2 [], .node 0 []]

private theorem orgMemo_entry_zero :
    entryAt orgMemoSignature 0 =
      some (entry "zero" 0 0 Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.zero) := rfl

private theorem orgMemo_entry_one :
    entryAt orgMemoSignature 1 =
      some (entry "one" 0 0 Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.one) := rfl

private theorem orgMemo_entry_two :
    entryAt orgMemoSignature 2 =
      some (entry "two" 0 0 Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.two) := rfl

private theorem orgMemo_entry_addi :
    entryAt orgMemoSignature 3 =
      some (entry "addi" 2 0 Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.addi) := rfl

private theorem orgMemo_entry_mult :
    entryAt orgMemoSignature 5 =
      some (entry "mult" 2 0 Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.mult) := rfl

private theorem orgMemo_entry_push :
    entryAt orgMemoSignature 14 =
      some (entry "push" 2 0 Mettapedia.GSLT.LanguageDef.GauthierE2.Prim.push) := rfl

private theorem memoZero_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 2 orgMemoSignature
        (.node 0 []) [0] [0] Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld =
      some [0] := by
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_zero, entry]

private theorem memoOne_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 2 orgMemoSignature
        (.node 1 []) [0] [0] Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld =
      some [1] := by
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_one, entry]

private theorem memoTwo_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 2 orgMemoSignature
        (.node 2 []) [0] [0] Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld =
      some [2] := by
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_two, entry]

private theorem memoTailOne_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 3 orgMemoSignature
        memoTailOne [0] [0] Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld =
      some [1, 1] := by
  unfold memoTailOne
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_push, entry, memoOne_eval,
    Mettapedia.GSLT.LanguageDef.GauthierE2.head?]
  rfl

private theorem memoTailZero_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 3 orgMemoSignature
        memoTailZero [0] [0] Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld =
      some [2, 0] := by
  unfold memoTailZero
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_push, entry, memoTwo_eval, memoZero_eval,
    Mettapedia.GSLT.LanguageDef.GauthierE2.head?]
  rfl

private theorem memo_addi_left_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
        (.node 3 [memoTailOne, memoTailZero]) [0] [0]
        Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [3, 1] := by
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_addi, entry, memoTailOne_eval, memoTailZero_eval,
    Mettapedia.GSLT.LanguageDef.GauthierE2.mkE,
    Mettapedia.GSLT.LanguageDef.GauthierE2.add?]
  rfl

private theorem memo_addi_right_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
        (.node 3 [memoTailZero, memoTailOne]) [0] [0]
        Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [3, 0] := by
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_addi, entry, memoTailZero_eval, memoTailOne_eval,
    Mettapedia.GSLT.LanguageDef.GauthierE2.mkE,
    Mettapedia.GSLT.LanguageDef.GauthierE2.add?]
  rfl

private theorem memo_mult_left_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
        (.node 5 [memoTailOne, memoTailZero]) [0] [0]
        Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [2, 1] := by
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_mult, entry, memoTailOne_eval, memoTailZero_eval,
    Mettapedia.GSLT.LanguageDef.GauthierE2.mkE,
    Mettapedia.GSLT.LanguageDef.GauthierE2.mul?]
  rfl

private theorem memo_mult_right_eval :
    Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
        (.node 5 [memoTailZero, memoTailOne]) [0] [0]
        Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [2, 0] := by
  rw [Mettapedia.GSLT.LanguageDef.GauthierE2.eval]
  simp only [orgMemo_entry_mult, entry, memoTailZero_eval, memoTailOne_eval,
    Mettapedia.GSLT.LanguageDef.GauthierE2.mkE,
    Mettapedia.GSLT.LanguageDef.GauthierE2.mul?]
  rfl

/-- Memo addition is not globally commutative: `mkE` retains the left list tail. -/
theorem memo_addi_not_commutative : ¬ memoCommutativeEvalLaw 3 := by
  intro hlaw
  have h := hlaw 4 memoTailOne memoTailZero [0] [0]
    Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld
  have hleft :
      Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
          (.node 3 [memoTailOne, memoTailZero]) [0] [0]
          Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [3, 1] := by
    exact memo_addi_left_eval
  have hright :
      Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
          (.node 3 [memoTailZero, memoTailOne]) [0] [0]
          Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [3, 0] := by
    exact memo_addi_right_eval
  rw [hleft, hright] at h
  contradiction

/-- Memo multiplication has the same left-tail asymmetry. -/
theorem memo_mult_not_commutative : ¬ memoCommutativeEvalLaw 5 := by
  intro hlaw
  have h := hlaw 4 memoTailOne memoTailZero [0] [0]
    Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld
  have hleft :
      Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
          (.node 5 [memoTailOne, memoTailZero]) [0] [0]
          Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [2, 1] := by
    exact memo_mult_left_eval
  have hright :
      Mettapedia.GSLT.LanguageDef.GauthierE2.eval 4 orgMemoSignature
          (.node 5 [memoTailZero, memoTailOne]) [0] [0]
          Mettapedia.GSLT.LanguageDef.GauthierE2.defaultWorld = some [2, 0] := by
    exact memo_mult_right_eval
  rw [hleft, hright] at h
  contradiction

/-- A serializable flag row whose positive bit is inseparable from its semantic proof. -/
structure CertifiedCommFlag where
  opId : Key
  theoremName : String
  law : memoCommutativeEvalLaw opId

/-- No global commutativity flag survives authentication on the memo substrate. -/
def orgCertifiedCommFlags : List CertifiedCommFlag :=
  []

def exportedCommFlag (id : Key) : Bool :=
  orgCertifiedCommFlags.any (fun row => row.opId == id)

theorem orgCertifiedCommFlag_ids :
    orgCertifiedCommFlags.map (fun row => row.opId) = [] := rfl

theorem exportedCommFlag_sound (id : Key) (h : exportedCommFlag id = true) :
    memoCommutativeEvalLaw id := by
  simp [exportedCommFlag, orgCertifiedCommFlags] at h

/-! Negative canaries ensure scalar-only laws cannot leak into the memo export. -/

example : exportedCommFlag 3 = false := rfl
example : exportedCommFlag 5 = false := rfl
example : exportedCommFlag 4 = false := rfl

end Mettapedia.GSLT.LanguageDef.GauthierSkeleton
