import Mettapedia.Languages.MeTTa.PeTTa.Bridges.OnceQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ClosedQueryAdmission

/-!
# Closed literal first-witness requests

The pattern is arbitrary finite literal syntax, not a fixed relation schema.
The selected space is an explicit source handle. Literal matching excludes
the special cons view recursively; its reference result is exact structural
membership in the selected complete row list. Missing reads are not absence.
The inert scalar payload is retained exactly, including symbols and false;
only a separately justified consumer may forget its value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiteralQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

/-- At the query boundary, comma is an active conjunction form, not a data
constructor. A comma below an ordinary outer constructor remains data. -/
def ordinaryQuery : Atom → Bool
  | .expression (.symbol "," :: _) => false
  | _ => true

structure Request where
  handle : NamedSpaces.Handle
  pattern : Atom
  literal : SpaceSemantics.Literal pattern
  payload : Atom
  scalar : ConstantQuerySource.Scalar payload
  ordinary : ordinaryQuery pattern = true

def query (request : Request) : Atom :=
  .expression [.symbol "match", Effects.handleValue request.handle, request.pattern, request.payload]

def expression (request : Request) : Atom := .expression [.symbol "once", query request]

theorem read_literal (pattern : Atom) (literal : SpaceSemantics.Literal pattern) (environment : Environment) :
    EagerDFS.Destination.read environment pattern = pattern := by
  induction literal with
  | symbol => simp [EagerDFS.Destination.read, encode, decode]
  | grounded => simp [EagerDFS.Destination.read, encode, decode]
  | expression items _ _ ih =>
      rw [read_eq_applyTypeValuation]
      simp only [HE.Spec.Type.RuntimeRefinement.applyTypeValuation]
      congr 1
      conv_rhs => rw [← List.map_id items]
      apply List.map_congr_left
      intro item member
      simpa only [read_eq_applyTypeValuation, id_eq] using ih item member

theorem read_pattern (request : Request) (environment : Environment) :
    EagerDFS.Destination.read environment request.pattern = request.pattern :=
  read_literal request.pattern request.literal environment

theorem read_true (environment : Environment) :
    EagerDFS.Destination.read environment (Effects.boolean true) = Effects.boolean true := by
  simp [EagerDFS.Destination.read, Effects.boolean, encode, decode]

theorem read_payload (request : Request) (environment : Environment) :
    EagerDFS.Destination.read environment request.payload = request.payload := request.scalar.read environment

theorem read_handle (handle : NamedSpaces.Handle) (environment : Environment) :
    EagerDFS.Destination.read environment (Effects.handleValue handle) = Effects.handleValue handle := by
  cases handle <;> simp [Effects.handleValue, EagerDFS.Destination.read, encode, decode]

theorem handle_freeVars (handle : NamedSpaces.Handle) :
    (encode (Effects.handleValue handle)).freeVars = ∅ := by
  cases handle <;> simp [Effects.handleValue, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem reference_absent (request : Request) (rows : List Atom) :
    FirstQueryCursor.reference [] request.pattern (0, rows) = none ↔ request.pattern ∉ rows := by
  rw [FirstQueryCursor.absent_iff]
  simp [SpaceSemantics.matchValue_literal request.literal]
  constructor
  · intro absent member
    exact absent _ member rfl
  · intro absent row member same
    exact absent (same.symm ▸ member)

def consView : List Atom → Bool
  | [.symbol "cons", _, _] => true
  | _ => false

theorem consView_false (items : List Atom) :
    consView items = false ↔ ∀ first rest, items ≠ [.symbol "cons", first, rest] := by
  unfold consView
  split <;> simp_all

def checkLiteral : Atom → Bool
  | .var _ => false
  | .symbol _ | .grounded _ => true
  | .expression items => !consView items && items.attach.all (fun item => checkLiteral item.val)
termination_by atom => sizeOf atom
decreasing_by
  have smaller := List.sizeOf_lt_of_mem item.property
  simp_wf
  omega

theorem checkLiteral_iff (atom : Atom) : checkLiteral atom = true ↔ SpaceSemantics.Literal atom := by
  cases atom with
  | var name =>
      constructor
      · simp [checkLiteral]
      · intro literal; cases literal
  | symbol name => simp [checkLiteral, SpaceSemantics.Literal.symbol]
  | grounded value => simp [checkLiteral, SpaceSemantics.Literal.grounded]
  | expression items =>
      rw [checkLiteral, Bool.and_eq_true, Bool.not_eq_true', consView_false]
      constructor
      · rintro ⟨ordinary, all⟩
        apply SpaceSemantics.Literal.expression _ ordinary
        intro item member
        exact (checkLiteral_iff item).mp (List.all_eq_true.mp all ⟨item, member⟩ (by simp))
      · intro literal
        cases literal with
        | expression _ ordinary members =>
            refine ⟨ordinary, List.all_eq_true.mpr ?_⟩
            intro item _
            exact (checkLiteral_iff item.val).mpr (members item.val item.property)
termination_by sizeOf atom
decreasing_by
  · have smaller := List.sizeOf_lt_of_mem member
    simp_wf
    omega
  · have smaller := List.sizeOf_lt_of_mem item.property
    simp_wf
    omega

def ofPattern (handle : NamedSpaces.Handle) (pattern : Atom) (payload : Atom := Effects.boolean true) : Option Request :=
  if ordinary : ordinaryQuery pattern = true then
    if checked : checkLiteral pattern = true then
      if scalar : ConstantQuerySource.isScalar payload = true then
        some ⟨handle, pattern, (checkLiteral_iff pattern).mp checked, payload,
          (ConstantQuerySource.isScalar_iff payload).mp scalar, ordinary⟩ else none
    else none
  else none

theorem ofPattern_complete (handle : NamedSpaces.Handle) (pattern : Atom)
    (literal : SpaceSemantics.Literal pattern) (ordinary : ordinaryQuery pattern = true)
    (payload : Atom) (scalar : ConstantQuerySource.Scalar payload) :
    ofPattern handle pattern payload = some ⟨handle, pattern, literal, payload, scalar, ordinary⟩ := by
  simp [ofPattern, ordinary, (checkLiteral_iff pattern).mpr literal, (ConstantQuerySource.isScalar_iff payload).mpr scalar]

theorem conjunction_refuses (handle : NamedSpaces.Handle) (patterns : List Atom) (payload : Atom) :
    ofPattern handle (.expression (.symbol "," :: patterns)) payload = none := rfl

theorem handle_readback (value : Atom) (handle : NamedSpaces.Handle)
    (read : Effects.readHandle value = some handle) : Effects.handleValue handle = value := by
  unfold Effects.readHandle at read
  split at read
  · cases Option.some.inj read
    rfl
  · split at read
    · rename_i token equal
      cases Option.some.inj read
      change Atom.grounded (.custom "PeTTa.Space" (String.replicate token.length '#')) =
        Atom.grounded (.custom "PeTTa.Space" token)
      exact congrArg (fun text => Atom.grounded (.custom "PeTTa.Space" text)) equal.symm
    · contradiction
  · contradiction

/-- Recognition retains the exact source syntax. Dynamic handle expressions
and nonliteral patterns require a separate operand-evaluation certificate. -/
def parse : Atom → Option Request
  | .expression [.symbol "once", .expression [.symbol "match", location, pattern, payload]] => do
      let handle ← Effects.readHandle location
      ofPattern handle pattern payload
  | _ => none

theorem parse_exact (atom : Atom) (request : Request) (parsed : parse atom = some request) :
    expression request = atom := by
  unfold parse at parsed
  split at parsed
  · rename_i location pattern payload
    obtain ⟨handle, found, selected⟩ := Option.bind_eq_some_iff.mp parsed
    unfold ofPattern at selected
    split at selected
    · split at selected
      · split at selected
        · cases Option.some.inj selected
          simp only [expression, query, handle_readback location handle found]
        · contradiction
      · contradiction
    · contradiction
  · contradiction

theorem parse_complete (request : Request) : parse (expression request) = some request := by
  simp only [expression, query, parse, Effects.readHandle_handleValue]
  change ofPattern request.handle request.pattern request.payload = some request
  exact ofPattern_complete request.handle request.pattern request.literal request.ordinary request.payload request.scalar

/-- Current complete-domain evidence, with the separate native open-fact
admission kept visible. Capturing this evidence may scan the entire domain. -/
structure PreparedRead (request : Request) (state : Effects.State) where
  rows : List Atom
  snapshot : state.read request.handle = some rows
  closedCandidates : ClosedQueryAdmission.rowsReady request.pattern rows = true

def prepareRead (request : Request) (state : Effects.State) : Option (PreparedRead request state) :=
  match snapshot : state.read request.handle with
  | none => none
  | some rows =>
      if closed : ClosedQueryAdmission.rowsReady request.pattern rows = true then
        some ⟨rows, snapshot, closed⟩ else none

theorem missing_read_refuses (request : Request) (state : Effects.State)
    (missing : state.read request.handle = none) : prepareRead request state = none := by
  unfold prepareRead
  split
  · rfl
  · rename_i rows found
    rw [missing] at found
    contradiction

theorem unsupported_rows_refuse (request : Request) (state : Effects.State) (rows : List Atom)
    (snapshot : state.read request.handle = some rows)
    (unsupported : ClosedQueryAdmission.rowsReady request.pattern rows = false) :
    prepareRead request state = none := by
  unfold prepareRead
  split
  · rfl
  · rename_i actual found
    have same := Option.some.inj (snapshot.symm.trans found)
    subst actual
    simp [unsupported]

theorem prepared_empty_iff (request : Request) (state : Effects.State) (reading : PreparedRead request state) :
    StdLib.apply state "match" [Effects.handleValue request.handle, request.pattern, request.payload] =
      .ok (state, []) ↔ request.pattern ∉ reading.rows := by
  rw [ConstantQuerySource.primitive_query state request.handle reading.rows request.pattern request.payload reading.snapshot]
  simp only [Except.ok.injEq, Prod.mk.injEq, true_and]
  have heads : (SpaceSemantics.query reading.rows request.pattern request.payload).head? = none ↔
      request.pattern ∉ reading.rows := by
    rw [FirstQueryCursor.query_first, ← reference_absent request reading.rows]
    cases found : FirstQueryCursor.reference [] request.pattern (0, reading.rows) <;> simp
  simpa using heads

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiteralQuerySource
