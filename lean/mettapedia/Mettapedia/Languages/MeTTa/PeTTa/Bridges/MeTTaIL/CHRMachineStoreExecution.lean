import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineArithmeticExecution

/-! The CHR machine source executes as `Mettapedia.Languages.CHR.Machine`:
guards, the store, picks and the occurrence table. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open WireKit StrictCallKit CHRMachineSource
open Mettapedia.Languages.CHR (Value Term Environment IntOperator IntExpr Comparison ArithmeticFault Guard
  guardsEval)
open Mettapedia.Languages.CHR.Machine (Key Occ Store Pick slot put without alive removePicks ids)

/-! ## Guards -/

def guardAtom : Guard → Atom
  | .identical left right => .expression [.symbol "ChrIdentical", termAtom left, termAtom right]
  | .distinct left right => .expression [.symbol "ChrDistinct", termAtom left, termAtom right]
  | .compare operator left right =>
    .expression [.symbol "ChrCompare", comparisonAtom operator, expressionAtom left, expressionAtom right]

/-- Both sides of an equality guard, instantiated. -/
def valuesOf (environment : Environment) (left right : Term) : Except ArithmeticFault (Value × Value) := do
  let some first := left.instantiate environment | .error (.uninstantiated left)
  let some second := right.instantiate environment | .error (.uninstantiated right)
  pure (first, second)

def valuePairAtom (pair : Value × Value) : Atom := pairAtom (valueAtom pair.1) (valueAtom pair.2)

theorem instantiate_term_returns (state : State) (term : Term) (environment : Environment) (caller : Subst)
    (first second : Atom) (one : Returns caller state first (termAtom term))
    (two : Returns caller state second (environmentAtom environment)) :
    Returns caller state (apply "gslt:chr-machine:instantiate" [first, second])
      (optionAtom ((term.instantiate environment).map valueAtom)) := by
  rw [← Mettapedia.Languages.CHR.Machine.instantiateTerm_eq]
  exact instantiate_returns state term environment caller first second one two

theorem values_returns (caller : Subst) (state : State) (first second third : Atom) (left right : Term)
    (environment : Environment) (one : Returns caller state first (termAtom left))
    (two : Returns caller state second (termAtom right))
    (three : Returns caller state third (environmentAtom environment)) :
    Returns caller state (apply "gslt:chr-machine:values" [first, second, third])
      (exceptAtom valuePairAtom (valuesOf environment left right)) := by
  machine_call (.cons one (.cons two (.cons three .nil)))
  have leftInstance := instantiate_term_returns state left environment
  cases leftFound : left.instantiate environment with
  | none =>
    rw [leftFound] at leftInstance
    machine_case (leftInstance _ _ _ bound bound)
    simp only [valuesOf, leftFound, exceptAtom, faultAtom]
    exact make_returns _ _ "ChrFault" _ _ inert (.cons (make_returns _ _ "ChrUninstantiated" _ _ inert
      (.cons bound .nil)) .nil)
  | some a =>
    rw [leftFound] at leftInstance
    machine_case (leftInstance _ _ _ bound bound)
    have rightInstance := instantiate_term_returns state right environment
    cases rightFound : right.instantiate environment with
    | none =>
      rw [rightFound] at rightInstance
      machine_case (rightInstance _ _ _ bound bound)
      simp only [valuesOf, leftFound, rightFound, exceptAtom, faultAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons (make_returns _ _ "ChrUninstantiated" _ _ inert
        (.cons bound .nil)) .nil)
    | some b =>
      rw [rightFound] at rightInstance
      machine_case (rightInstance _ _ _ bound bound)
      simp only [valuesOf, leftFound, rightFound, exceptAtom, valuePairAtom, pairAtom]
      exact make_returns _ _ "ChrOk" _ _ inert (.cons (make_returns _ _ "ChrPair" _ _ inert
        (.cons bound (.cons bound .nil))) .nil)

theorem value_beq (first second : Value) : (first == second) = decide (first = second) := rfl

theorem guard_returns (caller : Subst) (state : State) (first second : Atom) (guard : Guard)
    (environment : Environment) (one : Returns caller state first (guardAtom guard))
    (two : Returns caller state second (environmentAtom environment)) :
    Returns caller state (apply "gslt:chr-machine:guard" [first, second])
      (exceptAtom Effects.boolean (guard.eval environment)) := by
  machine_call (.cons one (.cons two .nil))
  cases guard with
  | identical left right =>
    machine_case (bound) unfolding [guardAtom]
    have paired := fun (caller : Subst) (first second third : Atom) one two three =>
      values_returns caller state first second third left right environment one two three
    have unfolded : Guard.eval environment (.identical left right) =
        (valuesOf environment left right).map fun pair => pair.1 == pair.2 := by
      simp only [Guard.eval, valuesOf]
      cases left.instantiate environment <;> cases right.instantiate environment <;> rfl
    rw [unfolded]
    cases found : valuesOf environment left right with
    | error reason =>
      rw [found] at paired
      machine_case (paired _ _ _ _ bound bound bound) unfolding [exceptAtom]
      simp only [Except.map, exceptAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons bound .nil)
    | ok pair =>
      rw [found] at paired
      machine_case (paired _ _ _ _ bound bound bound) unfolding [exceptAtom, valuePairAtom, pairAtom]
      simp only [Except.map, exceptAtom, value_beq]
      rw [← valueAtom_decide]
      exact make_returns _ _ "ChrOk" _ _ inert (.cons (equal_returns _ state _ _ _ _ bound bound) .nil)
  | distinct left right =>
    machine_case (bound) unfolding [guardAtom]
    have paired := fun (caller : Subst) (first second third : Atom) one two three =>
      values_returns caller state first second third left right environment one two three
    have unfolded : Guard.eval environment (.distinct left right) =
        (valuesOf environment left right).map fun pair => pair.1 != pair.2 := by
      simp only [Guard.eval, valuesOf]
      cases left.instantiate environment <;> cases right.instantiate environment <;> rfl
    rw [unfolded]
    cases found : valuesOf environment left right with
    | error reason =>
      rw [found] at paired
      machine_case (paired _ _ _ _ bound bound bound) unfolding [exceptAtom]
      simp only [Except.map, exceptAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons bound .nil)
    | ok pair =>
      rw [found] at paired
      machine_case (paired _ _ _ _ bound bound bound) unfolding [exceptAtom, valuePairAtom, pairAtom]
      simp only [Except.map, exceptAtom, bne, value_beq]
      rw [← valueAtom_decide]
      exact make_returns _ _ "ChrOk" _ _ inert
        (.cons (not_returns _ state _ _ (equal_returns _ state _ _ _ _ bound bound)) .nil)
  | compare operator left right =>
    machine_case (bound) unfolding [guardAtom]
    have leftEval := eval_returns state left environment
    cases leftResult : left.eval environment with
    | error reason =>
      rw [leftResult] at leftEval
      machine_case (leftEval _ _ _ bound bound) unfolding [exceptAtom]
      simp only [Guard.eval, leftResult, exceptAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons bound .nil)
    | ok a =>
      rw [leftResult] at leftEval
      machine_case (leftEval _ _ _ bound bound) unfolding [exceptAtom]
      have rightEval := eval_returns state right environment
      cases rightResult : right.eval environment with
      | error reason =>
        rw [rightResult] at rightEval
        machine_case (rightEval _ _ _ bound bound) unfolding [exceptAtom]
        simp only [Guard.eval, leftResult, rightResult, exceptAtom]
        exact make_returns _ _ "ChrFault" _ _ inert (.cons bound .nil)
      | ok b =>
        rw [rightResult] at rightEval
        machine_case (rightEval _ _ _ bound bound) unfolding [exceptAtom]
        simp only [Guard.eval, leftResult, rightResult, exceptAtom]
        exact make_returns _ _ "ChrOk" _ _ inert (.cons (holds_returns _ state _ _ _ operator a b bound bound bound) .nil)

theorem guards_returns (state : State) (environment : Environment) :
    ∀ (guards : List Guard) (caller : Subst) (first second : Atom),
      Returns caller state first (listAtom (guards.map guardAtom)) →
      Returns caller state second (environmentAtom environment) →
      Returns caller state (apply "gslt:chr-machine:guards" [first, second])
        (exceptAtom Effects.boolean (guardsEval environment guards)) := by
  intro guards
  induction guards with
  | nil =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound)
    simp only [guardsEval, exceptAtom]
    exact make_returns _ _ "ChrOk" _ _ inert (.cons (grounded_returns runtime _ state (.bool true)) .nil)
  | cons guard rest ih =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound)
    have evaluated := fun (caller : Subst) (first second : Atom) one two =>
      guard_returns caller state first second guard environment one two
    cases found : guard.eval environment with
    | error reason =>
      rw [found] at evaluated
      machine_case (evaluated _ _ _ bound bound) unfolding [exceptAtom]
      simp only [guardsEval, found, exceptAtom]
      exact make_returns _ _ "ChrFault" _ _ inert (.cons bound .nil)
    | ok holds =>
      rw [found] at evaluated
      machine_case (evaluated _ _ _ bound bound) unfolding [exceptAtom, Effects.boolean]
      apply pure_if_returns _ _ _ _ holds _ _ _ bound
      cases holds with
      | true =>
        simp only [↓reduceIte, guardsEval, found]
        exact ih _ _ _ bound bound
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, guardsEval, found, exceptAtom]
        exact make_returns _ _ "ChrOk" _ _ inert (.cons (grounded_returns runtime _ state (.bool false)) .nil)

/-! ## The store -/

def keyAtom (key : Key) : Atom := .expression [.symbol "ChrKey", .grounded (.string key.1), integer key.2]
def occAtom (occurrence : Occ) : Atom :=
  .expression [.symbol "ChrOcc", integer occurrence.id, valuesAtom occurrence.values]
def occsAtom (occurrences : List Occ) : Atom := listAtom (occurrences.map occAtom)
def slotAtom (entry : Key × List Occ) : Atom := .expression [.symbol "ChrSlot", keyAtom entry.1, occsAtom entry.2]
def storeAtom (store : Store) : Atom := listAtom (store.map slotAtom)
def pickAtom (pick : Pick) : Atom := .expression [.symbol "ChrPick", keyAtom pick.key, integer pick.id]
def picksAtom (picks : List Pick) : Atom := listAtom (picks.map pickAtom)
def natAtom (id : Nat) : Atom := integer (id : Int)
def idsAtom (identifiers : List Nat) : Atom := listAtom (identifiers.map natAtom)

theorem keyAtom_decide (first second : Key) :
    decide (keyAtom first = keyAtom second) = decide (first = second) := by
  apply decide_eq_decide.mpr
  obtain ⟨name, arity⟩ := first
  obtain ⟨otherName, otherArity⟩ := second
  simp [keyAtom, integer]

theorem slot_returns (state : State) (key : Key) :
    ∀ (store : Store) (caller : Subst) (first second : Atom),
      Returns caller state first (keyAtom key) → Returns caller state second (storeAtom store) →
      Returns caller state (apply "gslt:chr-machine:slot" [first, second]) (occsAtom (slot key store)) := by
  intro store
  induction store with
  | nil =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [storeAtom]
    exact Eval.symbol_returns runtime _ state _
  | cons entry rest ih =>
    obtain ⟨other, occurrences⟩ := entry
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [storeAtom, slotAtom]
    apply pure_if_returns _ _ _ _ (decide (keyAtom other = keyAtom key)) _ _ _
      (equal_returns _ state _ _ _ _ bound bound)
    rw [keyAtom_decide]
    by_cases same : other = key
    · simp only [same, decide_true, ↓reduceIte, slot]
      exact bound
    · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, slot]
      exact ih _ _ _ bound bound

theorem put_returns (state : State) (key : Key) (occurrences : List Occ) :
    ∀ (store : Store) (caller : Subst) (first second third : Atom),
      Returns caller state first (keyAtom key) → Returns caller state second (occsAtom occurrences) →
      Returns caller state third (storeAtom store) →
      Returns caller state (apply "gslt:chr-machine:put" [first, second, third])
        (storeAtom (put key occurrences store)) := by
  intro store
  induction store with
  | nil =>
    intro caller first second third one two three
    machine_call (.cons one (.cons two (.cons three .nil)))
    machine_case (bound) unfolding [storeAtom]
    simp only [put, storeAtom, List.map, listAtom, slotAtom]
    exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSlot" _ _ inert (.cons bound (.cons bound .nil)))
      (Eval.symbol_returns runtime _ state _)
  | cons entry rest ih =>
    obtain ⟨other, old⟩ := entry
    intro caller first second third one two three
    machine_call (.cons one (.cons two (.cons three .nil)))
    machine_case (bound) unfolding [storeAtom, slotAtom]
    apply pure_if_returns _ _ _ _ (decide (keyAtom other = keyAtom key)) _ _ _
      (equal_returns _ state _ _ _ _ bound bound)
    rw [keyAtom_decide]
    by_cases same : other = key
    · simp only [same, decide_true, ↓reduceIte, put, storeAtom, List.map, listAtom, slotAtom]
      exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSlot" _ _ inert (.cons bound (.cons bound .nil))) bound
    · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, put, storeAtom, List.map, listAtom, slotAtom]
      exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrSlot" _ _ inert (.cons bound (.cons bound .nil)))
        (ih _ _ _ _ bound bound bound)

theorem without_returns (state : State) (id : Nat) :
    ∀ (occurrences : List Occ) (caller : Subst) (first second : Atom),
      Returns caller state first (integer id) → Returns caller state second (occsAtom occurrences) →
      Returns caller state (apply "gslt:chr-machine:without" [first, second]) (occsAtom (without id occurrences)) := by
  intro occurrences
  induction occurrences with
  | nil =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [occsAtom]
    exact Eval.symbol_returns runtime _ state _
  | cons occurrence rest ih =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [occsAtom, occAtom]
    apply pure_if_returns _ _ _ _ (decide (integer (occurrence.id : Int) = integer (id : Int))) _ _ _
      (equal_returns _ state _ _ _ _ bound bound)
    rw [integer_nat_decide]
    by_cases same : occurrence.id = id
    · simp only [same, decide_true, ↓reduceIte, without]
      exact bound
    · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, without, occsAtom, List.map, listAtom]
      exact cons_returns _ state _ _ _ _ (make_returns _ _ "ChrOcc" _ _ inert (.cons bound (.cons bound .nil)))
        (ih _ _ _ bound bound)

theorem alive_returns (state : State) (id : Nat) :
    ∀ (occurrences : List Occ) (caller : Subst) (first second : Atom),
      Returns caller state first (integer id) → Returns caller state second (occsAtom occurrences) →
      Returns caller state (apply "gslt:chr-machine:alive" [first, second])
        (Effects.boolean (alive id occurrences)) := by
  intro occurrences
  induction occurrences with
  | nil =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [occsAtom]
    exact grounded_returns runtime _ state (.bool false)
  | cons occurrence rest ih =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [occsAtom, occAtom]
    apply pure_if_returns _ _ _ _ (decide (integer (occurrence.id : Int) = integer (id : Int))) _ _ _
      (equal_returns _ state _ _ _ _ bound bound)
    rw [integer_nat_decide]
    by_cases same : occurrence.id = id
    · simp only [same, decide_true, ↓reduceIte, alive, beq_self_eq_true, Bool.true_or]
      exact grounded_returns runtime _ state (.bool true)
    · have different : (occurrence.id == id) = false := by simpa using same
      simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, alive, different, Bool.false_or]
      exact ih _ _ _ bound bound

theorem removePicks_returns (state : State) :
    ∀ (picks : List Pick) (store : Store) (caller : Subst) (first second : Atom),
      Returns caller state first (picksAtom picks) → Returns caller state second (storeAtom store) →
      Returns caller state (apply "gslt:chr-machine:remove-picks" [first, second])
        (storeAtom (removePicks picks store)) := by
  intro picks
  induction picks with
  | nil =>
    intro store caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [picksAtom]
    exact bound
  | cons pick rest ih =>
    intro store caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [picksAtom, pickAtom]
    exact ih _ _ _ _ bound (put_returns state pick.key _ store _ _ _ _ bound
      (without_returns state pick.id _ _ _ _ bound (slot_returns state pick.key store _ _ _ bound bound)) bound)

theorem ids_returns (state : State) :
    ∀ (picks : List Pick) (caller : Subst) (code : Atom), Returns caller state code (picksAtom picks) →
      Returns caller state (apply "gslt:chr-machine:ids" [code]) (idsAtom (ids picks)) := by
  intro picks
  induction picks with
  | nil =>
    intro caller code one
    machine_call (.cons one .nil)
    machine_case (bound) unfolding [picksAtom]
    exact Eval.symbol_returns runtime _ state _
  | cons pick rest ih =>
    intro caller code one
    machine_call (.cons one .nil)
    machine_case (bound) unfolding [picksAtom, pickAtom]
    simp only [ids, List.map, idsAtom]
    exact cons_returns _ state _ _ _ _ bound (ih _ _ bound)

/-! ## Rules and the occurrence table -/

open Mettapedia.Languages.CHR (Head Goal Rule)
open Mettapedia.Languages.CHR.Machine (At Table occurrencesOf)

def headAtom (head : Head) : Atom :=
  .expression [.symbol "ChrHead", .grounded (.string head.name), integer head.arguments.length,
    termsAtom head.arguments]

def goalAtom : Goal → Atom
  | .tell head => .expression [.symbol "ChrTell", headAtom head]
  | .assign index expression => .expression [.symbol "ChrAssign", integer index, expressionAtom expression]
  | .fail => .symbol "ChrFailGoal"

def kindAtom (rule : Rule) : Atom :=
  if rule.propagation then .symbol "ChrPropagating" else .symbol "ChrSimplifying"

def ruleAtom (rule : Rule) : Atom :=
  .expression [.symbol "ChrRule", listAtom (rule.kept.map headAtom), listAtom (rule.removed.map headAtom),
    listAtom (rule.guards.map guardAtom), listAtom (rule.body.map goalAtom), kindAtom rule]

def atAtom (occurrence : At) : Atom :=
  .expression [.symbol "ChrAt", integer occurrence.rule, integer occurrence.head, ruleAtom occurrence.body]

def tableAtom (table : Table) : Atom :=
  listAtom (table.map fun entry =>
    .expression [.symbol "ChrOccurrencesOf", keyAtom entry.1, listAtom (entry.2.map atAtom)])

theorem occurrencesOf_returns (state : State) (key : Key) :
    ∀ (table : Table) (caller : Subst) (first second : Atom),
      Returns caller state first (keyAtom key) → Returns caller state second (tableAtom table) →
      Returns caller state (apply "gslt:chr-machine:occurrences-of" [first, second])
        (listAtom ((occurrencesOf key table).map atAtom)) := by
  intro table
  induction table with
  | nil =>
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [tableAtom]
    exact Eval.symbol_returns runtime _ state _
  | cons entry rest ih =>
    obtain ⟨other, occurrences⟩ := entry
    intro caller first second one two
    machine_call (.cons one (.cons two .nil))
    machine_case (bound) unfolding [tableAtom]
    apply pure_if_returns _ _ _ _ (decide (keyAtom other = keyAtom key)) _ _ _
      (equal_returns _ state _ _ _ _ bound bound)
    rw [keyAtom_decide]
    by_cases same : other = key
    · simp only [same, decide_true, ↓reduceIte, occurrencesOf]
      exact bound
    · simp only [same, decide_false, Bool.false_eq_true, ↓reduceIte, occurrencesOf]
      exact ih _ _ _ bound bound

#print axioms values_returns
#print axioms slot_returns
#print axioms put_returns
#print axioms without_returns
#print axioms alive_returns
#print axioms removePicks_returns
#print axioms ids_returns
#print axioms occurrencesOf_returns
#print axioms guard_returns
#print axioms guards_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
