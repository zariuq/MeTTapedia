import Mettapedia.Machines.TIsa.StoreInstructions.PackedTermEdges
import Mettapedia.Machines.TIsa.StoreInstructions.PackedOccurs

/-!
# Selecting every unifier action without expanding terms

Dispatch reads just the two headers. Decomposition pairs handles
from the original child spans, in order. Elimination runs the
packed occurs check and returns the variable symbol and term
handle if it is safe. Malformed access remains separate from a
logical conflict.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedUnifierAction

open Mettapedia.Logic.LP
open UnifierHeaders (Symbols Exit dispatch ofTerm operation)
open Derivation.FiniteUnifier (Conflict Action action)
open PackedTerms (Arena Node lookup segment)
open PackedTermEdges (childTerms)

inductive Encoded
  | discard
  | bindVar (name root : Word)
  | decompose (pairs : List (Word × Word))
  | refuse (reason : Conflict)
  deriving DecidableEq, Repr

def binding (arena : Arena) (name root : Word) : Option Encoded :=
  (PackedOccurs.find name arena root).map (fun occurs => if occurs then .refuse .occurs else .bindVar name root)

def inspect (arena : Arena) (left right : Word) : Option Encoded := do
  let l ← arena.nodes[left.toNat]?
  let r ← arena.nodes[right.toNat]?
  match dispatch l.header r.header with
  | .malformed => none
  | .discard => some .discard
  | .bindLeft => binding arena l.header.symbol right
  | .bindRight => binding arena r.header.symbol left
  | .expand =>
    let ls ← segment arena.children l
    let rs ← segment arena.children r
    if ls.size = rs.size then some (.decompose (ls.toList.zip rs.toList)) else none
  | .clash => some (.refuse .heads)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def pair (get : Word → Option (Term σ)) (code : Word × Word) : Option (Term σ × Term σ) :=
  (get code.1).bind fun first => (get code.2).map fun second => (first, second)

def read (symbols : Symbols σ) (arena : Arena) : Encoded → Option (Action σ)
  | .discard => some .discard
  | .refuse reason => some (.refuse reason)
  | .bindVar name root => do
    let v ← symbols.vars.decode name
    if symbols.vars.encode v = some name then (lookup symbols arena root).map (Action.eliminate v)
    else none
  | .decompose pairs => (pairs.mapM (pair (lookup symbols arena))).map Action.decompose

private theorem width {V : Type*} (get : Word → Option V) (words : List Word) {terms : List V}
    (found : words.mapM get = some terms) : terms.length = words.length := by
  induction words generalizing terms with
  | nil =>
    obtain rfl := Option.some.inj found
    rfl
  | cons word rest ih =>
    rw [List.mapM_cons] at found
    obtain ⟨value, _, tail⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨later, read, returned⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj returned
    simp only [List.length_cons, ih read]

private theorem zip_reads (get : Word → Option (Term σ)) (left right : List Word)
    {l r : List (Term σ)} (foundLeft : left.mapM get = some l) (foundRight : right.mapM get = some r) :
    (left.zip right).mapM (pair get) = some (l.zip r) := by
  induction left generalizing right l r with
  | nil =>
    obtain rfl := Option.some.inj foundLeft
    rfl
  | cons first tail ih =>
    cases right with
    | nil =>
      obtain rfl := Option.some.inj foundRight
      simp
    | cons second rest =>
      rw [List.mapM_cons] at foundLeft foundRight
      obtain ⟨p, leftHead, moreLeft⟩ := Option.bind_eq_some_iff.mp foundLeft
      obtain ⟨q, rightHead, moreRight⟩ := Option.bind_eq_some_iff.mp foundRight
      obtain ⟨ps, leftTail, returnedLeft⟩ := Option.bind_eq_some_iff.mp moreLeft
      obtain ⟨qs, rightTail, returnedRight⟩ := Option.bind_eq_some_iff.mp moreRight
      obtain rfl := Option.some.inj returnedLeft
      obtain rfl := Option.some.inj returnedRight
      simp only [List.zip_cons_cons, List.mapM_cons, pair, leftHead, rightHead, Option.bind_some, Option.map_some,
        bind, ih rest leftTail rightTail]
      rfl

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem read_binding (symbols : Symbols σ) (arena : Arena) (v : σ.vars) (name root : Word)
    (term : Term σ) (encoding : symbols.vars.encode v = some name) (target : lookup symbols arena root = some term) :
    (binding arena name root).bind (read symbols arena) =
      some (if term.occursIn v then .refuse .occurs else .eliminate v term) := by
  have test := PackedOccurs.find_exact symbols arena v name encoding root term target
  by_cases occurs : term.occursIn v = true <;>
    simp [binding, read, test, occurs, target, symbols.vars.reads encoding, encoding]

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem variable_code (symbols : Symbols σ) (v : σ.vars) (node : Node)
    (encoded : symbols.pack (.var v) = some node.header) :
    symbols.vars.encode v = some node.header.symbol := by
  obtain ⟨word, found, same⟩ := Option.map_eq_some_iff.mp encoded
  exact (congrArg UnifierHeaders.Header.symbol same) ▸ found

/-- All packed outcomes are the next action of finite-tree
unification. In particular a binding is offered only after the
actual packed occurs check. -/
theorem inspect_exact (symbols : Symbols σ) (arena : Arena) (left right : Word) (l r : Term σ)
    (hasLeft : lookup symbols arena left = some l) (hasRight : lookup symbols arena right = some r) :
    (inspect arena left right).bind (read symbols arena) = some (action l r) := by
  obtain ⟨leftNode, leftFound⟩ := PackedTermEdges.node_at symbols arena left l hasLeft
  obtain ⟨rightNode, rightFound⟩ := PackedTermEdges.node_at symbols arena right r hasRight
  have leftPacked := PackedTerms.lookup_header symbols arena left l leftNode hasLeft leftFound
  have rightPacked := PackedTerms.lookup_header symbols arena right r rightNode hasRight rightFound
  have clause := UnifierHeaders.decoded_action symbols l r leftNode.header rightNode.header leftPacked rightPacked
  simp only [inspect, leftFound, rightFound, bind, Option.bind_some]
  generalize selected : dispatch leftNode.header rightNode.header = exit at clause ⊢
  cases exit with
  | malformed => cases clause
  | discard => exact clause
  | clash => exact clause
  | bindLeft =>
    cases l with
    | var v =>
      have candidate := read_binding symbols arena v leftNode.header.symbol right r
        (variable_code symbols v leftNode leftPacked) hasRight
      exact candidate.trans clause
    | const c => cases clause
    | app f args => cases clause
  | bindRight =>
    cases r with
    | var v =>
      have candidate := read_binding symbols arena v rightNode.header.symbol left l
        (variable_code symbols v rightNode rightPacked) hasLeft
      exact candidate.trans clause
    | const c => cases clause
    | app f args => cases clause
  | expand =>
    cases l with
    | var v => cases clause
    | const c => cases clause
    | app f lArgs =>
      cases r with
      | var v => cases clause
      | const c => cases clause
      | app g rArgs =>
        by_cases same : f = g
        · subst g
          obtain ⟨ls, leftSpan, leftArgs⟩ :=
            PackedTermEdges.children_exact symbols arena left f lArgs leftNode hasLeft leftFound
          obtain ⟨rs, rightSpan, rightArgs⟩ :=
            PackedTermEdges.children_exact symbols arena right f rArgs rightNode hasRight rightFound
          have leftWidth : ls.size = σ.functionArity f := by
            have length := width (lookup symbols arena) ls.toList leftArgs
            simpa only [childTerms, List.length_map, List.length_finRange, Array.length_toList] using length.symm
          have rightWidth : rs.size = σ.functionArity f := by
            have length := width (lookup symbols arena) rs.toList rightArgs
            simpa only [childTerms, List.length_map, List.length_finRange, Array.length_toList] using length.symm
          have arguments := zip_reads (lookup symbols arena) ls.toList rs.toList leftArgs rightArgs
          have order : (childTerms (.app f lArgs)).zip (childTerms (.app f rArgs)) = finPairsToList lArgs rArgs := by
            simp only [childTerms, List.zip_map', finPairsToList]
          simp only [leftSpan, rightSpan, Option.bind_some, if_pos (leftWidth.trans rightWidth.symm), read, arguments,
            Option.map_some, order]
          simpa [operation] using clause
        · simp [operation, same] at clause

namespace Examples

private def arena : Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 42⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩, ⟨⟨2, 1⟩, 1, 1⟩], #[0, 1]⟩

theorem application_equality_visits_the_children :
    inspect arena 2 3 = some (.decompose [(0, 1)]) := by decide +kernel

theorem unrelated_application_can_be_bound :
    inspect arena 0 3 = some (.bindVar 7 3) := by decide +kernel

theorem a_cycle_is_refused_instead_of_bound :
    inspect arena 0 2 = some (.refuse .occurs) := by decide +kernel

theorem an_invalid_handle_is_not_a_logical_conflict :
    inspect arena 4 0 = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedUnifierAction
