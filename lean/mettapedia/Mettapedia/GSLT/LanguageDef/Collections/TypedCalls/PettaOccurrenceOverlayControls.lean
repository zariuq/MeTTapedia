import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay

/-!
# Source producer controls for the typed occurrence overlay

The scalar Number guard below is an executable partial service, proved against
the Protocol guard kernel. All producers, effects, clause choices and returned
source equations are executed by the existing Destination owner.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1500000

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

theorem sat_two_symbols (a b : String) :
    Sat ([(Ty.sym a, Ty.sym b)] : Store) ↔ a = b := by
  constructor
  · rintro ⟨solution, solved⟩
    exact Ty.sym.inj ((solves_singleton solution _).mp solved)
  · rintro rfl
    exact ⟨fun _ => .sym "Number", (solves_singleton _ _).mpr rfl⟩

theorem literal_number_guard (index : Nat) (decls : Decls) (n : Int) :
    guard (atGuard index) [] (.sym "Number") (info decls (.grounded (.int n))) "Grounded" =
      {[(.sym "Number", .sym "Number")]} := by
  simpa using guard_literal (atGuard index) sat_nil
    (show Literal "Number" (.grounded (.int n)) from rfl) decls "Grounded"

theorem string_number_guard (index : Nat) (decls : Decls) (s : String) (store : Store) :
    guard (atGuard index) store (.sym "Number") (info decls (.grounded (.string s))) "Grounded" = 0 := by
  have noString : ¬ Sat (store ++ [(Ty.sym "String", Ty.sym "Number")]) := by
    intro sat
    have wrong := (sat_two_symbols "String" "Number").mp sat.right
    contradiction
  have noGrounded : ¬ Sat (store ++ [(Ty.sym "Grounded", Ty.sym "Number")]) := by
    intro sat
    have wrong := (sat_two_symbols "Grounded" "Number").mp sat.right
    contradiction
  simp [guard, getType, info_string, eff, classDeriv, noString, noGrounded]

def tautologicalStore (store : Store) : Bool :=
  store.all fun equation => decide (equation.1 = equation.2)

theorem tautologicalStore_sat (store : Store) (tautological : tautologicalStore store = true) :
    Sat store := by
  refine ⟨fun _ => .sym "Number", ?_⟩
  intro equation member
  have same : equation.1 = equation.2 := of_decide_eq_true (List.all_eq_true.mp tautological equation member)
  rw [same]

/-- Closed scalar Number guards, including later arguments and results, are
served over the exact accumulated tautological store. Other requests remain
explicit instead of being guessed successful. -/
def numberGuard (_world : EagerDFS.World) (_index : Nat)
    (store : Store) (expected : Ty String) (value : Atom) : Option (List Store) :=
  if tautologicalStore store && expected == .sym "Number" then
    match value with
    | .grounded (.int _) => some [store ++ [(.sym "Number", .sym "Number")]]
    | .grounded (.string _) => some []
    | _ => none
  else none

theorem numberGuard_exact (world : EagerDFS.World) (index : Nat)
    (store : Store) (expected : Ty String) (value : Atom) (stores : List Store)
    (served : numberGuard world index store expected value = some stores) :
    (stores : Multiset Store) = guard (atGuard index) store (expected.map Sum.inl)
      (info (fun _ => []) value) (metatype (fun _ => false) value) := by
  unfold numberGuard at served
  split at served
  · rename_i checked
    have checked' : tautologicalStore store = true ∧ expected = .sym "Number" := by simpa using checked
    rcases checked' with ⟨tautological, rfl⟩
    cases value with
    | grounded g =>
      cases g with
      | int n =>
        simp only [Option.some.injEq] at served
        subst stores
        simpa [metatype] using (guard_literal (atGuard index) (tautologicalStore_sat store tautological)
          (show Literal "Number" (.grounded (.int n)) from rfl) (fun _ => []) "Grounded").symm
      | string s =>
        simp only [Option.some.injEq] at served
        subst stores
        simpa [metatype] using (string_number_guard index (fun _ => []) s store).symm
      | bool b => simp at served
      | custom name payload => simp at served
    | symbol _ | var _ | expression _ => simp at served
  · simp at served

def services (rows : String → List Atom → RowLookup) : Services Unit where
  rows _ _ := rows
  declarations _ _ := []
  kind _ := metatype (fun _ => false)
  userSupport _ := ∅
  orderedGuard := numberGuard
  guard_exact := numberGuard_exact

def sym (s : String) : Atom := .symbol s
def num (n : Int) : Atom := .grounded (.int n)
def str (s : String) : Atom := .grounded (.string s)
def call (head : String) (args : List Atom) : Atom := .expression (.symbol head :: args)
def thenReturn (effect value : Atom) : Atom := call "let" [.var "discard", effect, value]
def printThen (label : String) (value : Atom) : Atom := thenReturn (call "println!" [sym label]) value

def program : SpaceSemantics.Program where
  equations := [⟨"accept", [.var "x", .var "y"], printThen "body" (.var "x")⟩]
  declarations := []

def rows (head : String) (_args : List Atom) : RowLookup :=
  if head = "accept" then .typed [⟨[.sym "Number", .sym "%Undefined%"], .sym "Number"⟩]
  else .untyped

def initial (expression : Atom) : State Unit :=
  (Allocator.empty 8 64, ⟨⟨Effects.loaded program, [], []⟩,
    [{frontier := [(⟨[], [.evaluate expression (.var "result")], .var "result", ∅, 0⟩, ⟨(), []⟩, [])]}]⟩)

def observed (fuel : Nat) (expression : Atom) : Option (List Atom × List Atom) :=
  let result := (machine (services rows) .eagerValue program).run fuel (initial expression)
  match result.2 with
  | .finished final => some (result.1.map (·.value), final.2.world.output)
  | _ => none

def producer : Atom := call "superpose" [.expression
  [printThen "bad" (str "wrong"), printThen "first" (num 1), printThen "second" (num 2)]]

def effectfulCall : Atom := call "accept" [producer, printThen "later" (num 9)]

def expectedEffects : List Atom :=
  [sym "bad", sym "first", sym "later", sym "body", sym "second", sym "later", sym "body"]

#guard observed 250 effectfulCall == some ([num 1, num 2], expectedEffects)

/-- The second producer occurrence is not evaluated before the first one's
consumer. This is precisely the ordering lost by collect-then-filter. -/
theorem batched_effect_order_is_different :
    expectedEffects ≠
      [sym "bad", sym "first", sym "second", sym "later", sym "body", sym "later", sym "body"] := by
  decide

#guard observed 250 effectfulCall != some ([num 1, num 2],
  [sym "bad", sym "first", sym "second", sym "later", sym "body", sym "later", sym "body"])

def duplicateCall : Atom := call "accept"
  [call "superpose" [.expression [num 1, num 1]], printThen "later" (num 9)]

#guard observed 150 duplicateCall == some ([num 1, num 1],
  [sym "later", sym "body", sym "later", sym "body"])

/- A nested typed producer returns to the retained outer argument frame;
the two calls must not share their type stores. -/
#guard observed 150 (call "accept" [call "accept" [num 1, num 9], num 9]) ==
  some ([num 1], [sym "body", sym "body"])

def rawRows (head : String) (_args : List Atom) : RowLookup :=
  if head = "accept" then .typed
    [⟨[.sym "Atom", .sym "%Undefined%"], .sym "%Undefined%"⟩,
     ⟨[.sym "Number", .sym "%Undefined%"], .sym "%Undefined%"⟩]
  else .untyped

def observedRows (selectedRows : String → List Atom → RowLookup)
    (fuel : Nat) (expression : Atom) : Option (List Atom × List Atom) :=
  let result := (machine (services selectedRows) .eagerValue program).run fuel (initial expression)
  match result.2 with
  | .finished final => some (result.1.map (·.value), final.2.world.output)
  | _ => none

/- The raw row receives the written producer. The evaluated row runs it.
Both are the same source call, with row-local demand and separate continuations. -/
#guard observedRows rawRows 250 (call "accept" [printThen "argument" (num 4), num 9]) ==
  some ([printThen "argument" (num 4), num 4], [sym "body", sym "argument", sym "body"])

def duplicateRows (head : String) (args : List Atom) : RowLookup :=
  match rows head args with
  | .typed selected => .typed (selected ++ selected)
  | other => other

/- Repeating a declaration is different from repeating a producer occurrence:
the former is normalized away, while the latter was preserved above. -/
#guard observedRows duplicateRows 150 (call "accept" [num 1, num 9]) ==
  some ([num 1], [sym "body"])

/- The inner collector returns one tuple to the typed argument continuation;
its two inner answers must not be mistaken for two outer arguments. -/
def collapseRows (head : String) (_args : List Atom) : RowLookup :=
  if head = "accept" then .typed
    [⟨[.sym "%Undefined%", .sym "%Undefined%"], .sym "%Undefined%"⟩]
  else .untyped

#guard observedRows collapseRows 250 (call "accept"
    [call "collapse" [call "superpose" [.expression [num 1, num 2]]], num 9]) ==
  some ([.expression [num 1, num 2]], [sym "body"])

/-- A purely mathematical service used below only where the guard has zero or
one answer, so no arbitrary `toList` ordering is observed. This is not a claim
that an unordered bag selects the native order of a multivalued query. -/
noncomputable def kernelServices : Services Unit where
  rows _ _ _ _ := .unserved
  declarations _ _ := []
  kind _ := metatype (fun _ => false)
  userSupport _ := ∅
  orderedGuard world index store expected value :=
    some ((guard (atGuard index) store (expected.map Sum.inl)
      (info (fun _ => []) value) (metatype (fun _ => false) value)).toList)
  guard_exact := by
    intro world index store expected value stores served
    cases served
    exact Multiset.coe_toList _

def boundT : Store := [(.sym "Number", .var (.inl "t"))]

theorem boundT_class_consistency (className : String) :
    Sat (boundT ++ [(Ty.sym className, .var (.inl "t"))]) ↔ className = "Number" := by
  constructor
  · rintro ⟨assignment, solved⟩
    have first := solved (.sym "Number", .var (.inl "t")) (by simp [boundT])
    have last := solved (.sym className, .var (.inl "t")) (by simp)
    simp only [Ty.bind_sym, Ty.bind_var'] at first last
    exact Ty.sym.inj (last.trans first.symm)
  · rintro rfl
    refine ⟨fun _ => .sym "Number", ?_⟩
    intro equation member
    simp [boundT] at member
    subst equation
    rfl

theorem boundT_rejects_string (index : Nat) (s : String) :
    guard (atGuard index) boundT ((Ty.var "t").map Sum.inl)
      (info (fun _ => []) (str s)) "Grounded" = 0 := by
  have stringBad : ¬ Sat (boundT ++ [(.sym "String", .var (.inl "t"))]) := by
    rw [boundT_class_consistency]
    decide
  have metaBad : ¬ Sat (boundT ++ [(.sym "Grounded", .var (.inl "t"))]) := by
    rw [boundT_class_consistency]
    decide
  simp [guard, getType, str, info_string, eff, classDeriv, stringBad, metaBad]

theorem boundT_accepts_number (index : Nat) (n : Int) :
    guard (atGuard index) boundT ((Ty.var "t").map Sum.inl)
      (info (fun _ => []) (num n)) "Grounded" =
      {boundT ++ [(.sym "Number", .var (.inl "t"))]} := by
  have good : Sat (boundT ++ [(.sym "Number", .var (.inl "t"))]) :=
    (boundT_class_consistency "Number").mpr rfl
  simp [guard, getType, num, info_int, eff, classDeriv, good]

def sharedFrame (saved : CallFrame) : CallFrame :=
  {saved with row := ⟨[.var "t"], .var "t"⟩, store := boundT, phase := .body}

/-- The actual return adapter uses the argument's store. A String body result
cannot reset the same row variable and slip through as a new String call. -/
theorem shared_type_variable_rejects_body
    (source : State Unit) (scope : Scope Unit) (parents : List (Scope Unit))
    (control : DControl) (context : Context Unit) (origins : List Nat)
    (pending : List (Work Unit)) (saved : CallFrame) (outside : List CallFrame)
    (s : String) :
    consumeBody kernelServices source scope parents control context origins pending
      (sharedFrame saved) outside (str s) =
      .silent (source.1, ⟨source.2.world, {scope with frontier := pending} :: parents⟩) := by
  apply guarded_result_refuses_only_current
  · change ResultGuarded (.var "t")
    decide
  · change some ((guard (atGuard saved.index) boundT ((Ty.var "t").map Sum.inl)
      (info (fun _ => []) (str s)) "Grounded").toList) = some []
    rw [boundT_rejects_string]
    simp

def rejectedFrame : CallFrame where
  head := "accept"
  row := ⟨[.sym "Number", .sym "%Undefined%"], .sym "Number"⟩
  remaining := [(.sym "%Undefined%", printThen "later" (num 9))]
  ready := []
  index := 0
  store := []
  callerGoals := []
  callerDestination := .var "result"
  callerCutBoundary := 0
  callDestination := .var "result"
  scopeDepth := 1
  phase := .argument (.sym "Number") (.var "argument")

def rejectedState (world : EagerDFS.World) (pending : List (Work Unit)) : State Unit :=
  (Allocator.empty 8 64, ⟨world,
    [{frontier := [(⟨[(.var "argument", str "wrong")], [], .var "argument", ∅, 0⟩,
      ⟨(), [rejectedFrame]⟩, [])] ++ pending}]⟩)

/-- A kernel-checked negative ordering control, using the actual resolved
argument record. The next argument contains a print, but this step only drops
the rejected occurrence and preserves the reached world and pending frontier. -/
theorem failed_guard_does_not_start_saved_print
    (world : EagerDFS.World) (pending : List (Work Unit)) :
    step (services rows) .eagerValue program (rejectedState world pending) =
      .silent (Allocator.empty 8 64, ⟨world, [{frontier := pending}]⟩) := by
  simp [step, rejectedState, rejectedFrame, consumeArgument, guardResult, services,
    numberGuard, tautologicalStore, demand, Unchecked, argumentContinuations, install,
    EagerDFS.Destination.resolve, EagerDFS.Destination.equations,
    EagerDFS.Destination.read, EagerDFS.Destination.encode, EagerDFS.Destination.decode,
    Mettapedia.Logic.LP.unifyTotal, Mettapedia.Logic.LP.Term.occursIn,
    Mettapedia.Logic.LP.Subst.applyEqs, Mettapedia.Logic.LP.Subst.id,
    Mettapedia.Logic.LP.Subst.single, Mettapedia.Logic.LP.Subst.comp,
    Mettapedia.Logic.LP.Subst.applyTerm, str]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay.Controls
