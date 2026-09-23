import Mettapedia.GSLT.LanguageDef.GroundDenseHeadCompilation

/-!
# Compiled match programs

A compiled equation head need not walk its pattern at run time.  It can run
a flat program over registers instead: the argument sits in a register, a
node check loads the two children of a node into two fresh registers, a
symbol check compares one register with a symbol, and a variable occurrence
either binds its slot or compares with it.  Which occurrence binds is fixed
when the program is emitted: the first one in emission order binds and every
later one compares.  No run-time test decides it.

This module proves that running the emitted program observes exactly the
dense matcher of the same pattern (`run_emit`), and composes that with the
existing chain to the association-list matcher (`run_compiled_eq_matchP`).
Repeated variables are covered; linearity is not an admission condition.
Two controls show that the static first-occurrence decision is what carries
the equality check.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledMatchProgram

open Mettapedia.Logic.Unification.BinaryPatternViews
open FiniteEnvironmentCompilation
open GroundDenseHeadCompilation

variable {Symbol : Type} [DecidableEq Symbol]

/-- One instruction of a compiled match program over registers and slots. -/
inductive MatchOp (Symbol Slot : Type) where
  /-- The register's term becomes the slot's value. -/
  | bind (source : Nat) (slot : Slot)
  /-- The register's term equals the slot's value. -/
  | same (source : Nat) (slot : Slot)
  /-- The register holds this symbol. -/
  | atom (source : Nat) (value : Symbol)
  /-- The register holds a node, whose children load into registers
  `target` and `target + 1`. -/
  | node (source target : Nat)
deriving DecidableEq, Repr

/-- Registers of a running match program. -/
abbrev Registers (Symbol : Type) := Nat → Option (Tm Symbol)

/-- Load a term into one register. -/
def load (registers : Registers Symbol) (index : Nat) (term : Tm Symbol) :
    Registers Symbol :=
  fun candidate => if candidate = index then some term else registers candidate

/-- The state a match program transforms. -/
abbrev MatchState (inventory : Inventory Nat) (Symbol : Type) :=
  Registers Symbol × DenseEnvironment inventory (Tm Symbol)

/-- One instruction; `none` is a mismatch. -/
def step (inventory : Inventory Nat) :
    MatchOp Symbol inventory.Slot → MatchState inventory Symbol →
      Option (MatchState inventory Symbol)
  | .bind source slot, (registers, environment) =>
      (registers source).map fun term =>
        (registers, writeDense inventory environment (slot, term))
  | .same source slot, (registers, environment) =>
      match registers source, environment slot with
      | some term, some previous =>
          if term = previous then some (registers, environment) else none
      | _, _ => none
  | .atom source value, (registers, environment) =>
      match registers source with
      | some (.sym actual) =>
          if value = actual then some (registers, environment) else none
      | _ => none
  | .node source target, (registers, environment) =>
      match registers source with
      | some (.node left right) =>
          some (load (load registers target left) (target + 1) right,
            environment)
      | _ => none

/-- Run instructions in order, stopping at the first mismatch. -/
def run (inventory : Inventory Nat) :
    List (MatchOp Symbol inventory.Slot) → MatchState inventory Symbol →
      Option (MatchState inventory Symbol)
  | [], state => some state
  | instruction :: rest, state =>
      (step inventory instruction state).bind (run inventory rest)

/-- The program emitted for one pattern read from register `source`, with
fresh registers allocated from `next`.  `bound` lists the slots an earlier
instruction binds.  The result carries the instructions, the next free
register, and the slots bound after them. -/
def emit (inventory : Inventory Nat) :
    DensePattern Symbol inventory.Slot → Nat → Nat → List inventory.Slot →
      List (MatchOp Symbol inventory.Slot) × Nat × List inventory.Slot
  | .variable slot, source, next, bound =>
      if slot ∈ bound then ([.same source slot], next, bound)
      else ([.bind source slot], next, slot :: bound)
  | .symbol value, source, next, bound => ([.atom source value], next, bound)
  | .node left right, source, next, bound =>
      let leftCode := emit inventory left next (next + 2) bound
      let rightCode :=
        emit inventory right (next + 1) leftCode.2.1 leftCode.2.2
      (.node source next :: leftCode.1 ++ rightCode.1, rightCode.2.1,
        rightCode.2.2)

/-! ## Running composed code -/

theorem run_append (inventory : Inventory Nat)
    (first second : List (MatchOp Symbol inventory.Slot))
    (state : MatchState inventory Symbol) :
    run inventory (first ++ second) state =
      (run inventory first state).bind (run inventory second) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons instruction rest induction =>
      simp only [List.cons_append, run]
      cases step inventory instruction state with
      | none => simp
      | some next => simpa using induction next

omit [DecidableEq Symbol] in
/-- Emission never reuses a register below its allocation start. -/
theorem le_emit_next (inventory : Inventory Nat)
    (pattern : DensePattern Symbol inventory.Slot)
    (source next : Nat) (bound : List inventory.Slot) :
    next ≤ (emit inventory pattern source next bound).2.1 := by
  induction pattern generalizing source next bound with
  | «variable» slot =>
      unfold emit
      split <;> simp
  | symbol value => simp [emit]
  | node left right leftInduction rightInduction =>
      simp only [emit]
      have leftBound := leftInduction next (next + 2) bound
      have rightBound := rightInduction (next + 1)
        (emit inventory left next (next + 2) bound).2.1
        (emit inventory left next (next + 2) bound).2.2
      omega

/-! ## The emitted program runs the dense matcher -/

/-- Running the program emitted for a pattern, from a register holding the
term and an environment whose bound slots are exactly `bound`, observes the
dense matcher.  On success the registers below the allocation start are
unchanged and the returned slot list again names exactly the bound slots. -/
theorem run_emit (inventory : Inventory Nat)
    (pattern : DensePattern Symbol inventory.Slot)
    (source next : Nat) (bound : List inventory.Slot)
    (registers : Registers Symbol)
    (environment : DenseEnvironment inventory (Tm Symbol))
    (term : Tm Symbol)
    (loaded : registers source = some term)
    (boundExact : ∀ slot, slot ∈ bound ↔ (environment slot).isSome) :
    Option.map Prod.snd
        (run inventory (emit inventory pattern source next bound).1
          (registers, environment)) =
      matchDense inventory pattern term environment ∧
    ∀ final, run inventory (emit inventory pattern source next bound).1
        (registers, environment) = some final →
      (∀ index, index < next → final.1 index = registers index) ∧
      (∀ slot, slot ∈ (emit inventory pattern source next bound).2.2 ↔
        (final.2 slot).isSome) := by
  induction pattern generalizing
      source next bound registers environment term with
  | «variable» slot =>
      by_cases present : slot ∈ bound
      · have boundSlot := (boundExact slot).1 present
        cases previousEq : environment slot with
        | none => simp [previousEq] at boundSlot
        | some previous =>
            by_cases same : term = previous
            · simp [emit, present, run, step, loaded, previousEq, same,
                matchDense, boundExact]
            · simp [emit, present, run, step, loaded, previousEq, same,
                matchDense]
      · have unbound : environment slot = none := by
          cases previousEq : environment slot with
          | none => rfl
          | some previous =>
              have : slot ∈ bound := (boundExact slot).2 (by simp [previousEq])
              exact absurd this present
        refine ⟨?_, ?_⟩
        · simp [emit, present, run, step, loaded, matchDense, unbound]
        · intro final finalEq
          simp [emit, present, run, step, loaded] at finalEq
          subst final
          refine ⟨fun _ _ => rfl, ?_⟩
          intro candidate
          by_cases same : candidate = slot
          · subst candidate
            simp [emit, present, writeDense]
          · simp [emit, present, writeDense, same, boundExact candidate]
  | symbol value =>
      cases term with
      | sym actual =>
          by_cases same : value = actual
          · simp [emit, run, step, loaded, same, matchDense, boundExact]
          · simp [emit, run, step, loaded, same, matchDense]
      | node left right => simp [emit, run, step, loaded, matchDense]
  | node left right leftInduction rightInduction =>
      cases term with
      | sym actual => simp [emit, run, step, loaded, matchDense]
      | node termLeft termRight =>
          -- The node check loads both children, then the left code and the
          -- right code run in order.
          let loadedRegisters :=
            load (load registers next termLeft) (next + 1) termRight
          have leftLoaded : loadedRegisters next = some termLeft := by
            simp [loadedRegisters, load]
          have rightLoaded : loadedRegisters (next + 1) = some termRight := by
            simp [loadedRegisters, load]
          have nodeStep :
              step inventory (MatchOp.node source next)
                  (registers, environment) =
                some (loadedRegisters, environment) := by
            simp [step, loaded, loadedRegisters]
          let leftCode := emit inventory left next (next + 2) bound
          let rightCode :=
            emit inventory right (next + 1) leftCode.2.1 leftCode.2.2
          have codeEq :
              (emit inventory (.node left right) source next bound).1 =
                MatchOp.node source next :: leftCode.1 ++ rightCode.1 := by
            simp [emit, leftCode, rightCode]
          have boundEq :
              (emit inventory (.node left right) source next bound).2.2 =
                rightCode.2.2 := by
            simp [emit, leftCode, rightCode]
          have runEq :
              run inventory
                  (emit inventory (.node left right) source next bound).1
                  (registers, environment) =
                (run inventory leftCode.1 (loadedRegisters, environment)).bind
                  (run inventory rightCode.1) := by
            rw [codeEq]
            simp only [List.cons_append, run, nodeStep, Option.bind_some]
            exact run_append inventory leftCode.1 rightCode.1
              (loadedRegisters, environment)
          have leftSpec := leftInduction next (next + 2) bound
            loadedRegisters environment termLeft leftLoaded boundExact
          have allocation : next + 2 ≤ leftCode.2.1 :=
            le_emit_next inventory left next (next + 2) bound
          rw [runEq, boundEq]
          cases leftRun : run inventory leftCode.1
              (loadedRegisters, environment) with
          | none =>
              have leftNone :
                  matchDense inventory left termLeft environment = none := by
                have := leftSpec.1
                rw [leftRun] at this
                simpa using this.symm
              refine ⟨?_, ?_⟩
              · simp [matchDense, leftNone]
              · intro final finalEq
                simp at finalEq
          | some leftFinal =>
              obtain ⟨leftRegisters, leftEnvironment⟩ := leftFinal
              have leftMatch :
                  matchDense inventory left termLeft environment =
                    some leftEnvironment := by
                have := leftSpec.1
                rw [leftRun] at this
                simpa using this.symm
              obtain ⟨leftFrameAt, leftBoundExactAt⟩ :=
                leftSpec.2 (leftRegisters, leftEnvironment) leftRun
              have leftFrame :
                  ∀ index, index < next + 2 →
                    leftRegisters index = loadedRegisters index :=
                fun index below => leftFrameAt index below
              have leftBoundExact :
                  ∀ slot, slot ∈ leftCode.2.2 ↔
                    (leftEnvironment slot).isSome :=
                fun slot => leftBoundExactAt slot
              have rightStillLoaded :
                  leftRegisters (next + 1) = some termRight := by
                rw [leftFrame (next + 1) (by omega)]
                exact rightLoaded
              have rightSpec := rightInduction (next + 1) leftCode.2.1
                leftCode.2.2 leftRegisters leftEnvironment termRight
                rightStillLoaded leftBoundExact
              refine ⟨?_, ?_⟩
              · simp only [Option.bind_some]
                rw [rightSpec.1]
                simp [matchDense, leftMatch]
              · intro final finalEq
                simp only [Option.bind_some] at finalEq
                obtain ⟨rightFrame, rightBoundExact⟩ :=
                  rightSpec.2 final finalEq
                refine ⟨?_, rightBoundExact⟩
                intro index below
                rw [rightFrame index (by omega), leftFrame index (by omega)]
                have notRight : index ≠ next + 1 := by omega
                have notLeft : index ≠ next := by omega
                simp [loadedRegisters, load, notRight, notLeft]

/-! ## The compiled program refines the association-list matcher -/

/-- Registers holding one argument in register zero. -/
def argumentRegisters (term : Tm Symbol) : Registers Symbol :=
  load (fun _ => none) 0 term

/-- The program emitted for an admitted pattern, reading its argument from
register zero with fresh registers from one and no slot bound yet. -/
def programFor (inventory : Inventory Nat)
    (compiled : DensePattern Symbol inventory.Slot) :
    List (MatchOp Symbol inventory.Slot) :=
  (emit inventory compiled 0 1 []).1

/-- Running the emitted program from an empty environment observes the
association-list matcher of the source pattern. -/
theorem run_compiled_eq_matchP (inventory : Inventory Nat)
    (source : Pat Symbol)
    (compiled : DensePattern Symbol inventory.Slot)
    (accepted : compile? inventory source = some compiled)
    (term : Tm Symbol) :
    Option.map (fun final => decodeDense inventory final.2)
        (run inventory (programFor inventory compiled)
          (argumentRegisters term, emptyDenseEnvironment inventory)) =
      Option.map decodeListEnvironment (matchP source term []) := by
  have spec := run_emit inventory compiled 0 1 []
    (argumentRegisters term) (emptyDenseEnvironment inventory) term
    (by simp [argumentRegisters, load])
    (by simp [emptyDenseEnvironment])
  have dense := spec.1
  rw [← compiledMatch_eq_sourceMatch inventory source compiled accepted term,
    ← dense]
  simp [programFor, Option.map_map, Function.comp_def]

/-! ## Controls -/

private def oneSlotInventory : Inventory Nat := {
  keys := [0]
  nodup := by simp }

private def onlySlot : oneSlotInventory.Slot := ⟨0, by decide⟩

/-- A pattern repeating its only variable: `node x (node tag x)`. -/
private def repeatedCompiled : DensePattern String oneSlotInventory.Slot :=
  .node (.variable onlySlot) (.node (.symbol "tag") (.variable onlySlot))

private def equalGround : Tm String :=
  .node (.sym "same") (.node (.sym "tag") (.sym "same"))

private def unequalGround : Tm String :=
  .node (.sym "left") (.node (.sym "tag") (.sym "right"))

/-- The first occurrence binds and the second compares. -/
example : programFor oneSlotInventory repeatedCompiled =
    [.node 0 1, .bind 1 onlySlot, .node 2 3, .atom 3 "tag",
      .same 4 onlySlot] := by
  decide

/-- Equal repeated occurrences are accepted. -/
example :
    (run oneSlotInventory (programFor oneSlotInventory repeatedCompiled)
      (argumentRegisters equalGround,
        emptyDenseEnvironment oneSlotInventory)).isSome = true := by
  decide

/-- Differing repeated occurrences are refused. -/
example :
    run oneSlotInventory (programFor oneSlotInventory repeatedCompiled)
      (argumentRegisters unequalGround,
        emptyDenseEnvironment oneSlotInventory) = none := by
  decide

/-- Negative control: a program binding at every occurrence, as if the
pattern were linear, accepts the differing occurrences the dense matcher
refuses.  The static first-occurrence decision is what carries the
equality. -/
example :
    (run oneSlotInventory
      [.node 0 1, .bind 1 onlySlot, .node 2 3, .atom 3 "tag",
        .bind 4 onlySlot]
      (argumentRegisters unequalGround,
        emptyDenseEnvironment oneSlotInventory)).isSome = true ∧
    matchDense oneSlotInventory repeatedCompiled unequalGround
      (emptyDenseEnvironment oneSlotInventory) = none := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledMatchProgram
