import Mettapedia.GSLT.LanguageDef.CompiledHeadCodeTree
import Mathlib.Tactic

/-!
# Execution cost of shared equation-head programs

This extends the existing open equation-head semantics, including repeated
variables, substitutions, and the fresh supply. Two independently recursive
executors run either every compiled head or a shared code tree. Erasing charges
recovers the existing executors, which already refine equation activation.

An instruction charge may depend on both the instruction and its input state;
in particular, repeated-variable unification need not have unit cost. For live
trees, sharing never increases the sum of these charges. It does not bound
allocation, instruction dispatch, tree construction, answer-list construction,
or physical runtime. The result does not justify sharing effectful operations.

The corresponding C fragment uses OEM_M_BIND/SAME/ATOM/EXPR. This is a cost
refinement of the mathematical head machine, not a proof of that C realization.
The terms are finite first-order terms with occurs-checked unification. PeTTa's
list-representation adapters, rational terms, and attributed-variable wakeups
require separate correspondence results.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledHeadExecutionCost

open Mettapedia.Logic.LP
open CompiledTwoSidedHeadProgram CompiledHeadCodeTree

universe u r v

variable {σ : LPSignature.{u, u, r, u}} {Slot : Type u} {α : Type v}
variable [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] [DecidableEq Slot]
variable (name : Nat → σ.vars)
variable (charge : HeadOp σ Slot → HeadState σ Slot → Nat)

/-- Sequential execution counts exactly the instructions attempted, including
the first failed instruction. -/
def execCharged : List (HeadOp σ Slot) → HeadState σ Slot →
    Option (HeadState σ Slot) × Nat
  | [], state => (some state, 0)
  | instruction :: rest, state =>
    match step name instruction state with
    | none => (none, charge instruction state)
    | some next =>
      let result := execCharged rest next
      (result.1, charge instruction state + result.2)

/-- Each alternative starts from the original input state. -/
def eachCharged : List (α × List (HeadOp σ Slot)) → HeadState σ Slot →
    List (α × HeadState σ Slot) × Nat
  | [], _ => ([], 0)
  | (payload, code) :: rest, state =>
    let current := execCharged name charge code state
    let others := eachCharged rest state
    (match current.1 with
     | none => others.1
     | some final => (payload, final) :: others.1,
     current.2 + others.2)

/-- A shared instruction executes once and its resulting state feeds all
alternatives below it. Sibling alternatives retain the original state. -/
def treeCharged : CodeTree σ Slot α → HeadState σ Slot →
    List (α × HeadState σ Slot) × Nat
  | .nil, _ => ([], 0)
  | .leaf payload rest, state =>
    let others := treeCharged rest state
    ((payload, state) :: others.1, others.2)
  | .op instruction below rest, state =>
    let others := treeCharged rest state
    match step name instruction state with
    | none => (others.1, charge instruction state + others.2)
    | some next =>
      let children := treeCharged below next
      (children.1 ++ others.1, charge instruction state + children.2 + others.2)

theorem execCharged_result (code : List (HeadOp σ Slot)) (state : HeadState σ Slot) :
    (execCharged name charge code state).1 = exec name code state := by
  induction code generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [execCharged, exec]
    cases step name instruction state with
    | none => rfl
    | some next => exact ih next

theorem eachCharged_result (entries : List (α × List (HeadOp σ Slot)))
    (state : HeadState σ Slot) :
    (eachCharged name charge entries state).1 = CodeTree.runEach name entries state := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨payload, code⟩
    simp only [eachCharged, CodeTree.runEach, List.filterMap_cons, execCharged_result]
    cases exec name code state <;> simp_all [CodeTree.runEach]

theorem treeCharged_result (tree : CodeTree σ Slot α) (state : HeadState σ Slot) :
    (treeCharged name charge tree state).1 = CodeTree.run name tree state := by
  induction tree generalizing state with
  | nil => rfl
  | leaf payload rest ih => simp [treeCharged, CodeTree.run, ih]
  | op instruction below rest ihBelow ihRest =>
    simp only [treeCharged, CodeTree.run]
    cases step name instruction state <;> simp [ihBelow, ihRest]

theorem charged_results_equal (tree : CodeTree σ Slot α) (state : HeadState σ Slot) :
    (treeCharged name charge tree state).1 =
      (eachCharged name charge tree.paths state).1 := by
  rw [treeCharged_result, eachCharged_result, CodeTree.run_eq_runEach]

theorem eachCharged_cost_append (first second : List (α × List (HeadOp σ Slot)))
    (state : HeadState σ Slot) :
    (eachCharged name charge (first ++ second) state).2 =
      (eachCharged name charge first state).2 + (eachCharged name charge second state).2 := by
  induction first with
  | nil => simp [eachCharged]
  | cons entry rest ih => simp [eachCharged, ih, Nat.add_assoc]

theorem eachCharged_cost_prefix (instruction : HeadOp σ Slot)
    (entries : List (α × List (HeadOp σ Slot))) (state : HeadState σ Slot) :
    (eachCharged name charge
      (entries.map fun e => (e.1, instruction :: e.2)) state).2 =
      entries.length * charge instruction state +
        match step name instruction state with
        | none => 0
        | some next => (eachCharged name charge entries next).2 := by
  induction entries with
  | nil => cases step name instruction state <;> simp [eachCharged]
  | cons entry rest ih =>
    cases stepResult : step name instruction state <;>
      simp_all [eachCharged, execCharged, Nat.add_mul] <;> omega

/-- Liveness excludes dead instructions with no source equation underneath. -/
theorem tree_cost_le_each {tree : CodeTree σ Slot α} (live : tree.Live)
    (state : HeadState σ Slot) :
    (treeCharged name charge tree state).2 ≤
      (eachCharged name charge tree.paths state).2 := by
  induction live generalizing state with
  | nil => exact le_rfl
  | leaf payload liveRest ih => simpa [treeCharged, eachCharged, execCharged, CodeTree.paths] using ih state
  | @op instruction below rest liveBelow liveRest reaches ihBelow ihRest =>
    have count : 1 ≤ below.paths.length := List.length_pos_iff.mpr reaches
    have repeated : charge instruction state ≤ below.paths.length * charge instruction state := by
      nlinarith
    simp only [CodeTree.paths, eachCharged_cost_append, eachCharged_cost_prefix]
    cases stepResult : step name instruction state with
    | none =>
      simp only [treeCharged, stepResult]
      have h := ihRest state
      omega
    | some next =>
      simp only [treeCharged, stepResult]
      have h := ihRest state
      have k := ihBelow next
      omega

omit [DecidableEq σ.vars] in
theorem live_fold_build (entries : List (α × List (HeadOp σ Slot)))
    {tree : CodeTree σ Slot α} (live : tree.Live) :
    (entries.foldl (fun t e => CodeTree.insert e.1 t e.2) tree).Live := by
  induction entries generalizing tree with
  | nil => exact live
  | cons entry rest ih => exact ih (CodeTree.live_insert entry.1 live entry.2)

omit [DecidableEq σ.vars] in
theorem live_build (entries : List (α × List (HeadOp σ Slot))) :
    (CodeTree.build entries).Live := live_fold_build entries CodeTree.Live.nil

/-- This applies to the actual compiled-head tree constructor, without a
caller-provided liveness hypothesis. -/
theorem build_cost_le_each (entries : List (α × List (HeadOp σ Slot)))
    (state : HeadState σ Slot) :
    (treeCharged name charge (CodeTree.build entries) state).2 ≤
      (eachCharged name charge entries state).2 := by
  simpa only [CodeTree.paths_build] using tree_cost_le_each name charge (live_build entries) state

section SourceActivation

open DefunctionalizedEquationBodies

variable {τ : LPSignature.{0, 0, r, 0}} {Rel Op : Type}
variable [DecidableEq τ.vars] [DecidableEq τ.constants]
  [DecidableEq τ.functionSymbols] [DecidableEq Rel]
variable (fresh : Nat → τ.vars)
variable (cost : HeadOp τ Nat → HeadState τ Nat → Nat)

/-- Head execution is instrumented; finishing the frame uses the existing
activation semantics and is outside this charge component. -/
def activateCharged (P : EqProgram (headTemplates τ) Rel Op) (rel : Rel)
    (args : List (Term τ)) (θ : Subst τ) (supply : Nat) :
    List (Nat × Activation (headTemplates τ) Rel Op (Subst τ × Nat)) × Nat :=
  let result := treeCharged fresh cost (relationTree P rel) (initialState args θ supply)
  (result.1.filterMap fun reached =>
      (finish fresh args reached.1.2 reached.2).map (reached.1.1, ·), result.2)

theorem activateCharged_result (P : EqProgram (headTemplates τ) Rel Op) (rel : Rel)
    (args : List (Term τ)) (θ : Subst τ) (supply : Nat) :
    (activateCharged fresh cost P rel args θ supply).1 =
      treeActivate fresh (relationTree P rel) args θ supply := by
  simp only [activateCharged, treeCharged_result, treeActivate]

/-- The cost comparison applies to all heads of the original equation program. -/
theorem equation_head_cost_le (P : EqProgram (headTemplates τ) Rel Op) (rel : Rel)
    (args : List (Term τ)) (θ : Subst τ) (supply : Nat) :
    (activateCharged fresh cost P rel args θ supply).2 ≤
      (eachCharged fresh cost
        ((P.equations rel).zipIdx.map fun e => ((e.2, e.1), headCode e.1))
        (initialState args θ supply)).2 :=
  build_cost_le_each fresh cost _ _

/-- Existing source activation is the reference: matching equations and bodies
are preserved, with the established fresh-variable renaming relation. -/
theorem source_activation_refinement
    (prim : Op → List (Term τ) → Subst τ × Nat → Option (Term τ))
    (test : Op → List (Term τ) → Subst τ × Nat → Option Bool)
    (injective : Function.Injective fresh)
    (P : EqProgram (headTemplates τ) Rel Op) (rel : Rel)
    (args : List (Term τ)) (θ : Subst τ) (supply : Nat)
    (entry : EntryCondition fresh θ supply args) :
    List.Forall₂ (SameActivation fresh supply)
      ((activateCharged fresh cost P rel args θ supply).1.map Prod.snd)
      (activate (headTemplates τ) (substitutionStore fresh prim test) P (rel, args, (θ, supply))) := by
  rw [activateCharged_result]
  exact treeActivate_exact fresh prim test injective P rel args θ supply entry

end SourceActivation

/-! ## Concrete symbols and variadic expression constructors -/

namespace Controls

/-- A tuple symbol records expression length, as in the open-equation machine. -/
abbrev signature : LPSignature.{0, 0, 0, 0} where
  constants := String
  vars := Nat
  relationSymbols := String
  relationArity _ := 0
  functionSymbols := Nat
  functionArity n := n

def input (value : String) : HeadState signature Nat where
  registers n := if n = 0 then some (.const value) else none
  slots _ := none
  store := Subst.id signature
  supply := 10

def testA : HeadOp signature Nat := .constant 0 "a"

def leaves : Nat → CodeTree signature Nat String
  | 0 => .nil
  | n + 1 => .leaf "answer" (leaves n)

def shared (n : Nat) : CodeTree signature Nat String := .op testA (leaves n) .nil

theorem leaves_paths (n : Nat) :
    (leaves n).paths = List.replicate n ("answer", []) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leaves, CodeTree.paths, ih, List.replicate_succ]

theorem leaves_cost (n : Nat) (state : HeadState signature Nat) :
    (treeCharged id (fun _ _ => 1) (leaves n) state).2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [leaves, treeCharged] using ih

theorem shared_success_cost (n : Nat) :
    (treeCharged id (fun _ _ => 1) (shared n) (input "a")).2 = 1 := by
  simp [shared, treeCharged, step, testA, input, Subst.applyTerm, leaves_cost]

theorem shared_failure_cost (n : Nat) :
    (treeCharged id (fun _ _ => 1) (shared n) (input "b")).2 = 1 := by
  simp [shared, treeCharged, step, testA, input, Subst.applyTerm]

theorem independent_cost (n : Nat) (value : String) :
    (eachCharged id (fun _ _ => 1) (shared n).paths (input value)).2 = n := by
  simp only [shared, CodeTree.paths, List.append_nil, eachCharged_cost_prefix, leaves_paths,
    List.length_replicate, Nat.mul_one]
  cases step id testA (input value) with
  | none => simp
  | some next =>
    have zero : (eachCharged id (fun _ _ => 1)
        (List.replicate n ("answer", [])) next).2 = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [List.replicate_succ, eachCharged, execCharged, ih]
    simp [zero]

/-- More than one occurrence is retained even when every answer is equal. -/
theorem duplicate_answers_retained :
    ((treeCharged id (fun _ _ => 1) (shared 3) (input "a")).1.map Prod.fst) =
      ["answer", "answer", "answer"] := by
  simp [shared, leaves, treeCharged, step, testA, input, Subst.applyTerm]

theorem shared_test_strict_saving {n : Nat} (many : 1 < n) :
    (treeCharged id (fun _ _ => 1) (shared n) (input "a")).2 <
      (eachCharged id (fun _ _ => 1) (shared n).paths (input "a")).2 := by
  simpa only [shared_success_cost, independent_cost] using many

/-- Dead code would make the work comparison false, even though results agree. -/
theorem dead_test_wastes_work :
    (treeCharged id (fun _ _ => 1) (shared 0) (input "a")).2 >
      (eachCharged id (fun _ _ => 1) (shared 0).paths (input "a")).2 := by
  rw [shared_success_cost, independent_cost]
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.CompiledHeadExecutionCost
