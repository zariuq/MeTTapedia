import Mettapedia.Machines.TIsa.Derivation.FiniteUnifier
import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurrences

/-!
# The head dispatch of finite unification

Kind and symbol are separate words. Comparing them either
discharges an equation, selects its variable side, requests
child equations, or detects incompatible heads. Neither equal
function heads nor selection of a variable is itself a solution.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.UnifierHeaders

open Mettapedia.Logic.LP
open Derivation.FiniteUnifier (Action action)
open PackedOccurrences (Codes)

inductive Kind
  | var | const | app
  deriving DecidableEq, Repr

def Kind.word : Kind → Word
  | .var => 0
  | .const => 1
  | .app => 2

inductive Exit
  | malformed
  | discard | bindLeft | bindRight | expand | clash
  deriving DecidableEq, Repr

def Exit.word : Exit → BitVec 32
  | .malformed => 0
  | .discard => 1
  | .bindLeft => 2
  | .bindRight => 3
  | .expand => 4
  | .clash => 5

universe u p
variable {σ : LPSignature.{u,u,p,u}}

inductive Head (σ : LPSignature) where
  | var (key : σ.vars)
  | const (key : σ.constants)
  | app (key : σ.functionSymbols)

def ofTerm : Term σ → Head σ
  | .var v => .var v
  | .const c => .const c
  | .app f _ => .app f

structure Header where
  tag : Word
  symbol : Word
  deriving DecidableEq, Repr

structure Symbols (σ : LPSignature) where
  vars : Codes σ.vars
  constants : Codes σ.constants
  functions : Codes σ.functionSymbols

def Symbols.pack (symbols : Symbols σ) : Head σ → Option Header
  | .var v => (symbols.vars.encode v).map (Header.mk Kind.var.word)
  | .const c => (symbols.constants.encode c).map (Header.mk Kind.const.word)
  | .app f => (symbols.functions.encode f).map (Header.mk Kind.app.word)

def Symbols.unpack (symbols : Symbols σ) (stored : Header) : Option (Head σ) :=
  if stored.tag = 0 then (symbols.vars.decode stored.symbol).map Head.var
  else if stored.tag = 1 then (symbols.constants.decode stored.symbol).map Head.const
  else if stored.tag = 2 then (symbols.functions.decode stored.symbol).map Head.app
  else none

theorem roundtrip (symbols : Symbols σ) {head : Head σ} {stored : Header}
    (ready : symbols.pack head = some stored) : symbols.unpack stored = some head := by
  cases head with
  | var name =>
    obtain ⟨word, encoded, rfl⟩ := Option.map_eq_some_iff.mp ready
    simp [Symbols.unpack, Kind.word, symbols.vars.reads encoded]
  | const name =>
    obtain ⟨word, encoded, rfl⟩ := Option.map_eq_some_iff.mp ready
    simp [Symbols.unpack, Kind.word, symbols.constants.reads encoded]
  | app name =>
    obtain ⟨word, encoded, rfl⟩ := Option.map_eq_some_iff.mp ready
    simp [Symbols.unpack, Kind.word, symbols.functions.reads encoded]

def dispatch (left right : Header) : Exit :=
  if left.tag ≤ 2 then
    if right.tag ≤ 2 then
      if left.tag = 0 then
        if right.tag = 0 then
          if left.symbol = right.symbol then .discard else .bindLeft
        else .bindLeft
      else if right.tag = 0 then .bindRight
      else if left.tag = right.tag then
        if left.symbol = right.symbol then
          if left.tag = 1 then .discard else .expand
        else .clash
      else .clash
    else .malformed
  else .malformed

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

def choose : Head σ → Head σ → Exit
  | .var v, .var w => if v = w then .discard else .bindLeft
  | .var _, _ => .bindLeft
  | _, .var _ => .bindRight
  | .const c, .const d => if c = d then .discard else .clash
  | .app f, .app g => if f = g then .expand else .clash
  | _, _ => .clash

def operation (left right : Term σ) (exit : Exit) : Option (Action σ) :=
  match exit with
  | .discard => some .discard
  | .bindLeft =>
    match left with
    | .var v =>
      some (if right.occursIn v then .refuse .occurs else .eliminate v right)
    | _ => none
  | .bindRight =>
    match right with
    | .var v =>
      some (if left.occursIn v then .refuse .occurs else .eliminate v left)
    | _ => none
  | .expand =>
    match left, right with
    | .app f args, .app g more =>
      if equal : f = g then some (.decompose (finPairsToList args (equal ▸ more))) else none
    | _, _ => none
  | .clash => some (.refuse .heads)
  | .malformed => none

theorem choose_exact (left right : Term σ) :
    operation left right (choose (ofTerm left) (ofTerm right)) = some (action left right) := by
  cases left <;> cases right
  case var.var v w =>
    by_cases same : v = w <;> simp [choose, ofTerm, operation, action, same, Term.occursIn]
  case const.const c d =>
    by_cases same : c = d <;> simp [choose, ofTerm, operation, action, same]
  case app.app f args g more =>
    by_cases same : f = g <;> simp [choose, ofTerm, operation, action, same]
  all_goals rfl

theorem equal_codes {V : Type*} (codes : Codes V) {left right : V} {l r : Word}
    (one : codes.encode left = some l) (two : codes.encode right = some r) :
    l = r ↔ left = right := by
  constructor
  · intro words
    have same := (codes.reads one).symm.trans (words.symm ▸ codes.reads two)
    exact Option.some.inj same
  · intro names
    subst right
    exact Option.some.inj (one.symm.trans two)

theorem dispatch_exact (symbols : Symbols σ) (left right : Head σ) (l r : Header)
    (one : symbols.pack left = some l) (two : symbols.pack right = some r) :
    dispatch l r = choose left right := by
  cases left <;> cases right
  all_goals
    obtain ⟨lw, lCode, rfl⟩ := Option.map_eq_some_iff.mp one
    obtain ⟨rw, rCode, rfl⟩ := Option.map_eq_some_iff.mp two
    simp [dispatch, choose, Kind.word]
  all_goals first
    | simp only [equal_codes symbols.vars lCode rCode]
    | simp only [equal_codes symbols.constants lCode rCode]
    | simp only [equal_codes symbols.functions lCode rCode]

theorem decoded_action (symbols : Symbols σ) (left right : Term σ) (l r : Header)
    (one : symbols.pack (ofTerm left) = some l) (two : symbols.pack (ofTerm right) = some r) :
    operation left right (dispatch l r) = some (action left right) := by
  rw [dispatch_exact symbols _ _ _ _ one two, choose_exact]

namespace Examples

theorem equal_symbols_of_different_kinds_do_not_match :
    dispatch ⟨1, 7⟩ ⟨2, 7⟩ = .clash := by decide +kernel

theorem an_unknown_kind_is_not_a_conflict :
    dispatch ⟨3, 7⟩ ⟨2, 7⟩ = .malformed := by decide +kernel

theorem equal_application_heads_still_need_children :
    dispatch ⟨2, 7⟩ ⟨2, 7⟩ = .expand := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.UnifierHeaders
