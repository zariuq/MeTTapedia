import Mettapedia.Languages.TuringMachine.LanguageDef
import Mettapedia.OSLF.MeTTaIL.UnaryNumeralMatching
import Mettapedia.OSLF.Framework.RuleInstanceSteps
import Mettapedia.GSLT.LanguageDef.UnaryNumeralSorting
import Mettapedia.GSLT.LanguageDef.TypingInversion

/-!
# The steps of a Turing machine, and their sorts

The steps of the naive presentation of a machine are exactly the instances
of four shapes: the head moves right or left, onto a written cell or past the
last written cell.  The cells and symbols that the rule does not read are
arbitrary patterns, so the shapes describe the steps of open terms as well as
of configurations.

A step preserves sorts.  The constructors `Run`, `At` and `Cell` each have
one typing, numerals of states and symbols are terms of their sorts, and the
reduct of each shape is assembled from the sorted parts of its redex.  A term
of any interface therefore reduces only to terms of that interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.GSLT.LanguageDef.WellSorted

/-! ## Instantiating the vocabulary -/

@[simp] theorem applyBindings_run (bindings : Bindings) (control tape : Pattern) :
    applyBindings bindings (run control tape) =
      run (applyBindings bindings control) (applyBindings bindings tape) := by
  simp [run, applyBindings]

@[simp] theorem applyBindings_tapeAt (bindings : Bindings) (left scanned right : Pattern) :
    applyBindings bindings (tapeAt left scanned right) =
      tapeAt (applyBindings bindings left) (applyBindings bindings scanned)
        (applyBindings bindings right) := by
  simp [tapeAt, applyBindings]

@[simp] theorem applyBindings_cell (bindings : Bindings) (symbol rest : Pattern) :
    applyBindings bindings (cell symbol rest) =
      cell (applyBindings bindings symbol) (applyBindings bindings rest) := by
  simp [cell, applyBindings]

@[simp] theorem applyBindings_emptyCells (bindings : Bindings) :
    applyBindings bindings emptyCells = emptyCells := by
  simp [emptyCells, applyBindings]

@[simp] theorem applyBindings_stateTerm (bindings : Bindings) (index : Nat) :
    applyBindings bindings (stateTerm index) = stateTerm index :=
  applyBindings_unary bindings _ _ index

@[simp] theorem applyBindings_symbolTerm (bindings : Bindings) (index : Nat) :
    applyBindings bindings (symbolTerm index) = symbolTerm index :=
  applyBindings_unary bindings _ _ index

/-! ## The rules are plain and exact -/

/-- The rules of a machine carry no premise and bind nothing. -/
theorem rewrites_plain (machine : Machine) : PlainRules (turingMachine machine) := by
  intro rule membership
  refine ⟨rewrites_premiseFree machine rule membership, ?_⟩
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    apply ruleDepthAligned_of_binderFree <;>
      (unfold interiorRule
       split <;>
        simp [run, tapeAt, cell, stateTerm, symbolTerm, binderFree, binderFreeList])
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    apply ruleDepthAligned_of_binderFree <;>
      (unfold edgeRule
       split <;>
        simp [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm, binderFree,
          binderFreeList])

/-- The left side of every rule of a machine is matched exactly. -/
theorem rewrites_matchCorrect (machine : Machine) :
    ∀ rule ∈ (turingMachine machine).rewrites, Pattern.isMatchCorrect rule.left = true := by
  intro rule membership
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    unfold interiorRule
    split <;>
      simp [run, tapeAt, cell, stateTerm, symbolTerm, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux]
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    unfold edgeRule
    split <;>
      simp [run, tapeAt, emptyCells, stateTerm, symbolTerm, Pattern.isMatchCorrect,
        isMatchCorrectAux, isMatchCorrectListAux]

/-- The right side of every rule of a machine is matched exactly. -/
theorem rewrites_rightExact (machine : Machine) :
    ∀ rule ∈ (turingMachine machine).rewrites, isMatchCorrectAux rule.right = true := by
  intro rule membership
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    unfold interiorRule
    split <;>
      simp [run, tapeAt, cell, stateTerm, symbolTerm, isMatchCorrectAux, isMatchCorrectListAux]
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    unfold edgeRule
    split <;>
      simp [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm, isMatchCorrectAux,
        isMatchCorrectListAux]

/-- The right side of every rule of a machine mentions only variables of its
left side. -/
theorem rewrites_rightVariables (machine : Machine) :
    ∀ rule ∈ (turingMachine machine).rewrites,
      ∀ name ∈ freeVars rule.right, name ∈ freeVars rule.left := by
  intro rule membership
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    unfold interiorRule
    split <;>
      · intro name inRight
        simp [run, tapeAt, cell, stateTerm, symbolTerm, freeVars] at inRight ⊢
        tauto
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    unfold edgeRule
    split <;>
      · intro name inRight
        simp [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm, freeVars] at inRight ⊢
        tauto

/-- The interior rule of the table entry at an index is a rule of the
machine. -/
theorem interiorRule_mem (machine : Machine) {index : Nat}
    (bound : index < machine.transitions.length) :
    interiorRule index machine.transitions[index] ∈ (turingMachine machine).rewrites :=
  List.mem_append_left _ (List.mem_mapIdx.mpr ⟨index, bound, rfl⟩)

/-- So is its edge rule. -/
theorem edgeRule_mem (machine : Machine) {index : Nat}
    (bound : index < machine.transitions.length) :
    edgeRule index machine.transitions[index] ∈ (turingMachine machine).rewrites :=
  List.mem_append_right _ (List.mem_mapIdx.mpr ⟨index, bound, rfl⟩)

/-! ## The four shapes of a step -/

/-- The four shapes of a step of a machine.  The patterns `left`, `current`
and `right` are the parts of the tape that the table entry does not read. -/
inductive MachineStep (machine : Machine) : Pattern → Pattern → Prop where
  /-- The head moves right onto a written cell. -/
  | interiorRight {entry : Transition} (member : entry ∈ machine.transitions)
      (move : entry.move = .right) (left current right : Pattern) :
      MachineStep machine
        (run (stateTerm entry.state)
          (tapeAt left (symbolTerm entry.read) (cell current right)))
        (run (stateTerm entry.next)
          (tapeAt (cell (symbolTerm entry.write) left) current right))
  /-- The head moves left onto a written cell. -/
  | interiorLeft {entry : Transition} (member : entry ∈ machine.transitions)
      (move : entry.move = .left) (left current right : Pattern) :
      MachineStep machine
        (run (stateTerm entry.state)
          (tapeAt (cell current left) (symbolTerm entry.read) right))
        (run (stateTerm entry.next)
          (tapeAt left current (cell (symbolTerm entry.write) right)))
  /-- The head moves right past the last written cell and scans a blank. -/
  | edgeRight {entry : Transition} (member : entry ∈ machine.transitions)
      (move : entry.move = .right) (left : Pattern) :
      MachineStep machine
        (run (stateTerm entry.state) (tapeAt left (symbolTerm entry.read) emptyCells))
        (run (stateTerm entry.next)
          (tapeAt (cell (symbolTerm entry.write) left) (symbolTerm 0) emptyCells))
  /-- The head moves left past the last written cell and scans a blank. -/
  | edgeLeft {entry : Transition} (member : entry ∈ machine.transitions)
      (move : entry.move = .left) (right : Pattern) :
      MachineStep machine
        (run (stateTerm entry.state) (tapeAt emptyCells (symbolTerm entry.read) right))
        (run (stateTerm entry.next)
          (tapeAt emptyCells (symbolTerm 0) (cell (symbolTerm entry.write) right)))

/-- **Every step of a machine has one of the four shapes.** -/
theorem machineStep_of_step {machine : Machine} {source target : Pattern}
    (step : Step base (turingMachine machine) source target) :
    MachineStep machine source target := by
  obtain ⟨rule, membership, bindings, rfl, rfl⟩ :=
    sides_of_step (rewrites_plain machine) (rewrites_matchCorrect machine) step
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    have member : machine.transitions[index] ∈ machine.transitions := List.getElem_mem bound
    cases move : machine.transitions[index].move with
    | right =>
        simp only [interiorRule, move, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_stateTerm, applyBindings_symbolTerm]
        exact .interiorRight member move _ _ _
    | left =>
        simp only [interiorRule, move, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_stateTerm, applyBindings_symbolTerm]
        exact .interiorLeft member move _ _ _
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    have member : machine.transitions[index] ∈ machine.transitions := List.getElem_mem bound
    cases move : machine.transitions[index].move with
    | right =>
        simp only [edgeRule, move, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_emptyCells, applyBindings_stateTerm,
          applyBindings_symbolTerm]
        exact .edgeRight member move _
    | left =>
        simp only [edgeRule, move, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_emptyCells, applyBindings_stateTerm,
          applyBindings_symbolTerm]
        exact .edgeLeft member move _

/-- **Every instance of the four shapes is a step.** -/
theorem step_of_machineStep {machine : Machine} {source target : Pattern}
    (shape : MachineStep machine source target) :
    Step base (turingMachine machine) source target := by
  cases shape with
  | @interiorRight entry member move left current right =>
      obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
      have ruleMember := interiorRule_mem machine bound
      have step := step_of_instance (relEnv := RelationEnv.empty) (rewrites_plain machine)
        ruleMember (rewrites_matchCorrect machine _ ruleMember)
        (rewrites_rightExact machine _ ruleMember) (rewrites_rightVariables machine _ ruleMember)
        [("l", left), ("c", current), ("r", right)]
      simpa [interiorRule, move, applyBindings] using step
  | @interiorLeft entry member move left current right =>
      obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
      have ruleMember := interiorRule_mem machine bound
      have step := step_of_instance (relEnv := RelationEnv.empty) (rewrites_plain machine)
        ruleMember (rewrites_matchCorrect machine _ ruleMember)
        (rewrites_rightExact machine _ ruleMember) (rewrites_rightVariables machine _ ruleMember)
        [("l", left), ("c", current), ("r", right)]
      simpa [interiorRule, move, applyBindings] using step
  | @edgeRight entry member move left =>
      obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
      have ruleMember := edgeRule_mem machine bound
      have step := step_of_instance (relEnv := RelationEnv.empty) (rewrites_plain machine)
        ruleMember (rewrites_matchCorrect machine _ ruleMember)
        (rewrites_rightExact machine _ ruleMember) (rewrites_rightVariables machine _ ruleMember)
        [("l", left)]
      simpa [edgeRule, move, applyBindings] using step
  | @edgeLeft entry member move right =>
      obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
      have ruleMember := edgeRule_mem machine bound
      have step := step_of_instance (relEnv := RelationEnv.empty) (rewrites_plain machine)
        ruleMember (rewrites_matchCorrect machine _ ruleMember)
        (rewrites_rightExact machine _ ruleMember) (rewrites_rightVariables machine _ ruleMember)
        [("r", right)]
      simpa [edgeRule, move, applyBindings] using step

/-- **The steps of a machine are exactly the instances of the four shapes.** -/
theorem step_iff_machineStep {machine : Machine} {source target : Pattern} :
    Step base (turingMachine machine) source target ↔ MachineStep machine source target :=
  ⟨machineStep_of_step, step_of_machineStep⟩

/-! ## Typing the vocabulary -/

/-- The labels of the signature are distinct. -/
theorem terms_labels_nodup : (terms.map (·.label)).Nodup := by decide

/-- A declared constructor is determined by its label. -/
theorem rule_eq_of_label (machine : Machine) {rule other : GrammarRule}
    (member : rule ∈ (turingMachine machine).terms) (otherMember : other ∈ terms)
    (label : rule.label = other.label) : rule = other :=
  List.inj_on_of_nodup_map terms_labels_nodup member otherMember label

variable {machine : Machine} {free : FreeTypeContext} {bound : List TypeExpr}

/-- The numeral of a state is a term of the sort of states. -/
theorem hasType_stateTerm (index : Nat) :
    HasType (turingMachine machine) free bound (stateTerm index) (.base "State") :=
  hasType_unary (language := turingMachine machine) (zeroRule := terms[0])
    (succRule := terms[1]) (List.getElem_mem (l := terms) (by decide)) (List.getElem_mem (l := terms) (by decide)) rfl
    rfl rfl free bound index

/-- The numeral of a tape symbol is a term of the sort of symbols. -/
theorem hasType_symbolTerm (index : Nat) :
    HasType (turingMachine machine) free bound (symbolTerm index) (.base "Symbol") :=
  hasType_unary (language := turingMachine machine) (zeroRule := terms[2])
    (succRule := terms[3]) (List.getElem_mem (l := terms) (by decide)) (List.getElem_mem (l := terms) (by decide)) rfl
    rfl rfl free bound index

/-- A configuration pattern is typed exactly at the sort of configurations,
with a state and a tape. -/
theorem hasType_run_iff {control tape : Pattern} {type : TypeExpr} :
    HasType (turingMachine machine) free bound (run control tape) type ↔
      type = .base "Config" ∧
        HasType (turingMachine machine) free bound control (.base "State") ∧
          HasType (turingMachine machine) free bound tape (.base "Tape") := by
  constructor
  · intro typed
    obtain ⟨rule, member, label, sortEq, -, arguments⟩ := typed.apply_inv
    obtain rfl := rule_eq_of_label machine member (other := terms[7])
      (List.getElem_mem (l := terms) (by decide)) label
    obtain ⟨controlTyped, rest⟩ := arguments.simple_cons_inv
    obtain ⟨tapeTyped, -⟩ := rest.simple_cons_inv
    exact ⟨sortEq, controlTyped, tapeTyped⟩
  · rintro ⟨rfl, controlTyped, tapeTyped⟩
    exact HasType.constructor (rule := terms[7]) (List.getElem_mem (l := terms) (by decide))
      (by rintro ⟨name, kind, element, shape⟩; cases shape)
      (.cons trivial rfl controlTyped (.cons trivial rfl tapeTyped .nil))

/-- A tape pattern is typed exactly at the sort of tapes, with two half-tapes
around a symbol. -/
theorem hasType_tapeAt_iff {left scanned right : Pattern} {type : TypeExpr} :
    HasType (turingMachine machine) free bound (tapeAt left scanned right) type ↔
      type = .base "Tape" ∧
        HasType (turingMachine machine) free bound left (.base "Cells") ∧
          HasType (turingMachine machine) free bound scanned (.base "Symbol") ∧
            HasType (turingMachine machine) free bound right (.base "Cells") := by
  constructor
  · intro typed
    obtain ⟨rule, member, label, sortEq, -, arguments⟩ := typed.apply_inv
    obtain rfl := rule_eq_of_label machine member (other := terms[6])
      (List.getElem_mem (l := terms) (by decide)) label
    obtain ⟨leftTyped, rest⟩ := arguments.simple_cons_inv
    obtain ⟨scannedTyped, rest⟩ := rest.simple_cons_inv
    obtain ⟨rightTyped, -⟩ := rest.simple_cons_inv
    exact ⟨sortEq, leftTyped, scannedTyped, rightTyped⟩
  · rintro ⟨rfl, leftTyped, scannedTyped, rightTyped⟩
    exact HasType.constructor (rule := terms[6]) (List.getElem_mem (l := terms) (by decide))
      (by rintro ⟨name, kind, element, shape⟩; cases shape)
      (.cons trivial rfl leftTyped
        (.cons trivial rfl scannedTyped (.cons trivial rfl rightTyped .nil)))

/-- A written cell is typed exactly at the sort of half-tapes, with a symbol
in front of a half-tape. -/
theorem hasType_cell_iff {symbol rest : Pattern} {type : TypeExpr} :
    HasType (turingMachine machine) free bound (cell symbol rest) type ↔
      type = .base "Cells" ∧
        HasType (turingMachine machine) free bound symbol (.base "Symbol") ∧
          HasType (turingMachine machine) free bound rest (.base "Cells") := by
  constructor
  · intro typed
    obtain ⟨rule, member, label, sortEq, -, arguments⟩ := typed.apply_inv
    obtain rfl := rule_eq_of_label machine member (other := terms[5])
      (List.getElem_mem (l := terms) (by decide)) label
    obtain ⟨symbolTyped, remaining⟩ := arguments.simple_cons_inv
    obtain ⟨restTyped, -⟩ := remaining.simple_cons_inv
    exact ⟨sortEq, symbolTyped, restTyped⟩
  · rintro ⟨rfl, symbolTyped, restTyped⟩
    exact HasType.constructor (rule := terms[5]) (List.getElem_mem (l := terms) (by decide))
      (by rintro ⟨name, kind, element, shape⟩; cases shape)
      (.cons trivial rfl symbolTyped (.cons trivial rfl restTyped .nil))

/-- The empty half-tape is a term of the sort of half-tapes. -/
theorem hasType_emptyCells :
    HasType (turingMachine machine) free bound emptyCells (.base "Cells") :=
  HasType.constructor (rule := terms[4]) (List.getElem_mem (l := terms) (by decide))
    (by rintro ⟨name, kind, element, shape⟩; cases shape) .nil

/-! ## Steps preserve sorts -/

/-- **A step of a machine preserves sorts**: the reduct of a sorted pattern
is sorted at the same type, in the same typing contexts. -/
theorem MachineStep.sorted {type : TypeExpr} {source target : Pattern}
    (step : MachineStep machine source target)
    (sorted : OpenPatternWellSorted (turingMachine machine) free bound type source) :
    OpenPatternWellSorted (turingMachine machine) free bound type target := by
  obtain ⟨typed, canonical, object, wellScoped⟩ := sorted
  cases step with
  | interiorRight member move left current right =>
      obtain ⟨rfl, -, tapeTyped⟩ := hasType_run_iff.mp typed
      obtain ⟨-, leftTyped, -, cellTyped⟩ := hasType_tapeAt_iff.mp tapeTyped
      obtain ⟨-, currentTyped, rightTyped⟩ := hasType_cell_iff.mp cellTyped
      refine ⟨hasType_run_iff.mpr ⟨rfl, hasType_stateTerm _, hasType_tapeAt_iff.mpr
        ⟨rfl, hasType_cell_iff.mpr ⟨rfl, hasType_symbolTerm _, leftTyped⟩, currentTyped,
          rightTyped⟩⟩, ?_, ?_, ?_⟩
      · simp only [run, tapeAt, cell, stateTerm, symbolTerm, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, Pattern.hasCanonicalBinderMetadata_unary,
          Bool.and_true, Bool.true_and, Bool.and_eq_true] at canonical ⊢
        tauto
      · simp only [run, tapeAt, cell, stateTerm, symbolTerm, isObjectPattern,
          isObjectPatternList, isObjectPattern_unary, Bool.and_true, Bool.true_and,
          Bool.and_eq_true] at object ⊢
        tauto
      · simp only [ScopeSafeAt, run, tapeAt, cell, stateTerm, symbolTerm,
          Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.isWellScopedAt_unary,
          Bool.and_true, Bool.true_and, Bool.and_eq_true] at wellScoped ⊢
        tauto
  | interiorLeft member move left current right =>
      obtain ⟨rfl, -, tapeTyped⟩ := hasType_run_iff.mp typed
      obtain ⟨-, cellTyped, -, rightTyped⟩ := hasType_tapeAt_iff.mp tapeTyped
      obtain ⟨-, currentTyped, leftTyped⟩ := hasType_cell_iff.mp cellTyped
      refine ⟨hasType_run_iff.mpr ⟨rfl, hasType_stateTerm _, hasType_tapeAt_iff.mpr
        ⟨rfl, leftTyped, currentTyped,
          hasType_cell_iff.mpr ⟨rfl, hasType_symbolTerm _, rightTyped⟩⟩⟩, ?_, ?_, ?_⟩
      · simp only [run, tapeAt, cell, stateTerm, symbolTerm, Pattern.hasCanonicalBinderMetadata,
          Pattern.hasCanonicalBinderMetadataList, Pattern.hasCanonicalBinderMetadata_unary,
          Bool.and_true, Bool.true_and, Bool.and_eq_true] at canonical ⊢
        tauto
      · simp only [run, tapeAt, cell, stateTerm, symbolTerm, isObjectPattern,
          isObjectPatternList, isObjectPattern_unary, Bool.and_true, Bool.true_and,
          Bool.and_eq_true] at object ⊢
        tauto
      · simp only [ScopeSafeAt, run, tapeAt, cell, stateTerm, symbolTerm,
          Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.isWellScopedAt_unary,
          Bool.and_true, Bool.true_and, Bool.and_eq_true] at wellScoped ⊢
        tauto
  | edgeRight member move left =>
      obtain ⟨rfl, -, tapeTyped⟩ := hasType_run_iff.mp typed
      obtain ⟨-, leftTyped, -, -⟩ := hasType_tapeAt_iff.mp tapeTyped
      refine ⟨hasType_run_iff.mpr ⟨rfl, hasType_stateTerm _, hasType_tapeAt_iff.mpr
        ⟨rfl, hasType_cell_iff.mpr ⟨rfl, hasType_symbolTerm _, leftTyped⟩,
          hasType_symbolTerm _, hasType_emptyCells⟩⟩, ?_, ?_, ?_⟩
      · simp only [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm,
          Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
          Pattern.hasCanonicalBinderMetadata_unary, Bool.and_true, Bool.true_and]
          at canonical ⊢
        tauto
      · simp only [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm, isObjectPattern,
          isObjectPatternList, isObjectPattern_unary, Bool.and_true, Bool.true_and]
          at object ⊢
        tauto
      · simp only [ScopeSafeAt, run, tapeAt, cell, emptyCells, stateTerm, symbolTerm,
          Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.isWellScopedAt_unary,
          Bool.and_true, Bool.true_and] at wellScoped ⊢
        tauto
  | edgeLeft member move right =>
      obtain ⟨rfl, -, tapeTyped⟩ := hasType_run_iff.mp typed
      obtain ⟨-, -, -, rightTyped⟩ := hasType_tapeAt_iff.mp tapeTyped
      refine ⟨hasType_run_iff.mpr ⟨rfl, hasType_stateTerm _, hasType_tapeAt_iff.mpr
        ⟨rfl, hasType_emptyCells, hasType_symbolTerm _,
          hasType_cell_iff.mpr ⟨rfl, hasType_symbolTerm _, rightTyped⟩⟩⟩, ?_, ?_, ?_⟩
      · simp only [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm,
          Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList,
          Pattern.hasCanonicalBinderMetadata_unary, Bool.and_true, Bool.true_and]
          at canonical ⊢
        tauto
      · simp only [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm, isObjectPattern,
          isObjectPatternList, isObjectPattern_unary, Bool.and_true, Bool.true_and]
          at object ⊢
        tauto
      · simp only [ScopeSafeAt, run, tapeAt, cell, emptyCells, stateTerm, symbolTerm,
          Pattern.isWellScopedAt, Pattern.isWellScopedListAt, Pattern.isWellScopedAt_unary,
          Bool.and_true, Bool.true_and] at wellScoped ⊢
        tauto

/-- **Subject reduction.**  A sorted pattern reduces only to patterns sorted
at the same type. -/
theorem step_sorted {type : TypeExpr} {source target : Pattern}
    (step : Step base (turingMachine machine) source target)
    (sorted : OpenPatternWellSorted (turingMachine machine) free bound type source) :
    OpenPatternWellSorted (turingMachine machine) free bound type target :=
  (machineStep_of_step step).sorted sorted

end Mettapedia.Languages.TuringMachine
