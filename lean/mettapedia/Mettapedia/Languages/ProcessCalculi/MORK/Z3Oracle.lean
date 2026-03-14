import Mettapedia.Languages.ProcessCalculi.MORK.Space
import Mettapedia.Languages.MeTTa.RuntimeExec

/-!
# MORK: Z3 Oracle Semantics

The first concrete witness of the existing oracle runtime kernel class.
This file connects the abstract oracle syntax (`OracleQuery`, `OracleResponse`,
`ResourceRequest`, `MeTTaRuntimeOracleSurface`) to concrete Z3 behavior:
query environments, payload-to-space conversion, pattern matching over oracle
payloads, and conformance theorems against a mock Z3 oracle.

## Architecture

Z3 lives under the **oracle** seam, separate from the query seam:
- exec  → `matchPattern` / `fireRule`
- query → `matchOneInSpace` / `matchSourceFactor`
- spaceEffect → `applySink` / `applySinks`
- **oracle → `oracleMatchPattern` / `oraclePayloadSpace`** (this file)

Positive example:
- Z3 model atoms are converted to a `Space` via `oraclePayloadSpace`, then
  queried by `matchOneInSpace` through a dedicated `oracleMatchPattern` helper.
  The query seam (`SourceFactor` / `matchSourceFactor`) is untouched.

Negative example:
- This file does NOT add `.z3Query` to `SourceFactor` or thread a
  `ResourceEnv` through `matchSourceFactor`. That would collapse the
  oracle and query seams.

## MORK Rust Z3 protocol (reference)

1. **Sink side** (`Z3Sink`): Buffers SMT-LIB statements, writes to Z3 stdin.
   MM2 syntax: `(O (z3 instance_name smt_statement))`

2. **Source side** (`Z3Source`): Sends `(check-sat)\n(get-model)\n`, reads response.
   If `sat`: parses model S-expression → PathMap → ReadZipperOwned → pattern match.
   If `unsat`: returns empty PathMap (no matches).
   MM2 syntax: `(I (z3 instance_name pattern))`

3. **Concrete test** (`main.rs:3478`): Declares `a,b : Int`, asserts `a > 0, b < 0`,
   queries `(define-fun a $_ Int $v)`, gets `$v = 1`.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.Z3Oracle

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK

/-! ## 1. Oracle environment -/

/-- An oracle environment provides responses to oracle queries.
    In the MORK runtime, this is the Z3 subprocess interaction.
    In the formalization, it's a pure function parameter.

    Positive example: `mockZ3Env` below returns `.sat` and `.model` responses
    for a named Z3 instance, matching the behavior of MORK's `sink_z3_basic` test.

    Negative example: this does NOT model the Z3 subprocess lifecycle (spawn/kill),
    SMT-LIB parsing, or the PathMap zipper internals. Z3 is an oracle. -/
abbrev OracleEnv := OracleQuery → OracleResponse

/-! ## 2. Payload-to-space conversion -/

/-- Convert an oracle response's payload atoms to a Space (`Finset Atom`).
    This is the key bridge: oracle payloads become a finite set of atoms
    that can be pattern-matched using existing `matchOneInSpace` infrastructure.

    In the MORK Rust runtime, this corresponds to parsing Z3's model S-expression
    into a `ReadZipperOwned<()>` (PathMap zipper) whose leaves are ground atoms. -/
noncomputable def oraclePayloadSpace (resp : OracleResponse) : Space :=
  resp.payloadAtoms.toFinset

/-- Query an oracle environment and get the payload space directly. -/
noncomputable def oracleQuerySpace (env : OracleEnv) (q : OracleQuery) : Space :=
  oraclePayloadSpace (env q)

/-! ## 3. Oracle-level pattern matching -/

/-- Match a pattern against an oracle response's payload space.
    Reuses the existing `matchOneInSpace` infrastructure from `Space.lean`.
    This is the oracle analogue of BTM workspace matching.

    In the MORK Rust runtime, this corresponds to `Z3Source::query()` which
    matches a user-provided pattern against the parsed Z3 model atoms. -/
noncomputable def oracleMatchPattern (σ : Subst) (resp : OracleResponse)
    (pat : Atom) : List (Subst × Atom) :=
  matchOneInSpace σ pat (oraclePayloadSpace resp)

/-! ## 4. Oracle routing theorems -/

section Routing

theorem z3CheckSat_routes_to_z3 (name : String) (assertions : List Atom) :
    (OracleQuery.z3CheckSat name assertions).resourceRequest = .z3 name := rfl

theorem z3GetModel_routes_to_z3 (name : String) (assertions : List Atom) :
    (OracleQuery.z3GetModel name assertions).resourceRequest = .z3 name := rfl

theorem actMatch_routes_to_act (name : String) (pat : Atom) :
    (OracleQuery.actMatch name pat).resourceRequest = .act name := rfl

end Routing

/-! ## 5. Payload semantics theorems -/

section PayloadSemantics

theorem sat_payload_empty :
    oraclePayloadSpace .sat = ∅ := by
  simp [oraclePayloadSpace, OracleResponse.payloadAtoms]

theorem unsat_payload_empty :
    oraclePayloadSpace .unsat = ∅ := by
  simp [oraclePayloadSpace, OracleResponse.payloadAtoms]

theorem model_payload_eq (atoms : List Atom) :
    oraclePayloadSpace (.model atoms) = atoms.toFinset := by
  simp [oraclePayloadSpace, OracleResponse.payloadAtoms]

theorem factSet_payload_eq (atoms : List Atom) :
    oraclePayloadSpace (.factSet atoms) = atoms.toFinset := by
  simp [oraclePayloadSpace, OracleResponse.payloadAtoms]

/-- Sat response has no payload atoms. -/
theorem sat_has_no_payload : OracleResponse.sat.hasPayload = false := rfl

/-- Unsat response has no payload atoms. -/
theorem unsat_has_no_payload : OracleResponse.unsat.hasPayload = false := rfl

/-- Model response always has payload. -/
theorem model_has_payload (atoms : List Atom) :
    (OracleResponse.model atoms).hasPayload = true := rfl

end PayloadSemantics

/-! ## 6. Oracle matching soundness -/

section MatchingSoundness

/-- If `a` is in the oracle response payload and `matchAtom σ pat a = some σ'`,
    then `(σ', a)` appears in `oracleMatchPattern`.
    This is the oracle analogue of `matchOneInSpace_mem`. -/
theorem oracleMatchPattern_mem (σ : Subst) (resp : OracleResponse) (pat a : Atom)
    (σ' : Subst) (ha : a ∈ oraclePayloadSpace resp) (hm : matchAtom σ pat a = some σ') :
    (σ', a) ∈ oracleMatchPattern σ resp pat :=
  matchOneInSpace_mem σ pat (oraclePayloadSpace resp) a ha σ' hm

/-- Reverse: if `(σ', a) ∈ oracleMatchPattern`, then `a` is in the payload
    and the pattern matched.
    This is the oracle analogue of `matchOneInSpace_spec`. -/
theorem oracleMatchPattern_spec (σ : Subst) (resp : OracleResponse) (pat : Atom)
    (σ' : Subst) (a : Atom) (h : (σ', a) ∈ oracleMatchPattern σ resp pat) :
    a ∈ oraclePayloadSpace resp ∧ matchAtom σ pat a = some σ' :=
  matchOneInSpace_spec σ pat (oraclePayloadSpace resp) σ' a h

/-- `oracleMatchPattern` against a sat response always returns empty. -/
theorem oracleMatchPattern_sat_empty (σ : Subst) (pat : Atom) :
    oracleMatchPattern σ .sat pat = [] := by
  unfold oracleMatchPattern oraclePayloadSpace
  simp [OracleResponse.payloadAtoms, matchOneInSpace]

/-- `oracleMatchPattern` against an unsat response always returns empty. -/
theorem oracleMatchPattern_unsat_empty (σ : Subst) (pat : Atom) :
    oracleMatchPattern σ .unsat pat = [] := by
  unfold oracleMatchPattern oraclePayloadSpace
  simp [OracleResponse.payloadAtoms, matchOneInSpace]

end MatchingSoundness

/-! ## 7. Bridge to `MeTTaRuntimeOracleSurface` -/

section OracleSurfaceBridge

open Mettapedia.Languages.MeTTa.RuntimeExec

/-- The canonical oracle surface's `responsePayload` agrees with
    `oraclePayloadSpace` up to `List.toFinset`. -/
theorem morkOraclePayload_eq (resp : OracleResponse) :
    (morkRuntimeOracleExec0.responsePayload resp).toFinset =
    oraclePayloadSpace resp := by
  simp [oraclePayloadSpace, morkRuntimeOracleExec0, OracleResponse.payloadAtoms]

/-- The canonical oracle surface routes Z3 check-sat to `.z3`. -/
theorem morkOracle_z3CheckSat_routes (name : String) (assertions : List Atom) :
    morkRuntimeOracleExec0.requestEncoding (.z3CheckSat name assertions) = .z3 name :=
  rfl

/-- The canonical oracle surface routes Z3 get-model to `.z3`. -/
theorem morkOracle_z3GetModel_routes (name : String) (assertions : List Atom) :
    morkRuntimeOracleExec0.requestEncoding (.z3GetModel name assertions) = .z3 name :=
  rfl

/-- The canonical oracle surface extracts model payload faithfully. -/
theorem morkOracle_model_payload (atoms : List Atom) :
    morkRuntimeOracleExec0.responsePayload (.model atoms) = atoms := rfl

end OracleSurfaceBridge

/-! ## 8. Mock Z3 oracle + conformance -/

section MockZ3

/-- The Z3 model atom for `(define-fun a () Int 1)`. -/
def defineFunA : Atom :=
  .expression [.symbol "define-fun", .symbol "a",
               .expression [], .symbol "Int", .grounded (.int 1)]

/-- The Z3 model atom for `(define-fun b () Int (- 1))`. -/
def defineFunB : Atom :=
  .expression [.symbol "define-fun", .symbol "b",
               .expression [], .symbol "Int", .grounded (.int (-1))]

/-- Mock Z3 oracle environment based on MORK's `sink_z3_basic` test (`main.rs:3478`).

    For instance "ins":
    - `z3GetModel` returns a model with `define-fun` entries for `a=1` and `b=-1`
    - `z3CheckSat` returns `sat`

    For all other instances/queries: returns `unsat`. -/
def mockZ3Env : OracleEnv
  | .z3GetModel "ins" _ => .model [defineFunA, defineFunB]
  | .z3CheckSat "ins" _ => .sat
  | _ => .unsat

/-- Mock Z3 check-sat returns sat for instance "ins". -/
theorem mock_z3_checksat :
    mockZ3Env (.z3CheckSat "ins" []) = .sat := rfl

/-- Mock Z3 check-sat returns unsat for unknown instances. -/
theorem mock_z3_checksat_unknown :
    mockZ3Env (.z3CheckSat "unknown" []) = .unsat := rfl

/-- Mock Z3 get-model returns model with payload for instance "ins". -/
theorem mock_z3_model_has_payload :
    (mockZ3Env (.z3GetModel "ins" [])).hasPayload = true := rfl

/-- Mock Z3 get-model returns unsat (no payload) for unknown instances. -/
theorem mock_z3_model_unknown_no_payload :
    (mockZ3Env (.z3GetModel "unknown" [])).hasPayload = false := rfl

/-- Mock Z3 model payload contains exactly two define-fun entries. -/
theorem mock_z3_model_payload_atoms :
    (mockZ3Env (.z3GetModel "ins" [])).payloadAtoms = [defineFunA, defineFunB] := rfl

/-- Mock Z3 routes through the canonical oracle surface correctly. -/
theorem mock_z3_routes_correctly :
    (OracleQuery.z3GetModel "ins" []).resourceRequest = .z3 "ins" := rfl

end MockZ3

/-! ## 9. Z3 sink effects -/

section SinkEffects

/-- Z3 sink effects accumulated during rule firing.
    In the MORK runtime, `Z3Sink` buffers SMT-LIB statements and writes them
    to Z3's stdin on `finalize`. We model the accumulated statements.

    Positive example: a rule that asserts `(> a 0)` produces
    `Z3SinkEffects` with `statements = [("ins", .expression [...])]`.

    Negative example: this does NOT model the Z3 subprocess stdin/stdout
    protocol or SMT-LIB parsing. -/
structure Z3SinkEffects where
  statements : List (String × Atom)   -- (instance_name, smt_statement) pairs
  deriving Repr, DecidableEq

/-- Empty Z3 sink effects (no statements buffered). -/
def Z3SinkEffects.empty : Z3SinkEffects := ⟨[]⟩

/-- Append a statement to Z3 sink effects. -/
def Z3SinkEffects.addStatement (effs : Z3SinkEffects) (inst : String) (stmt : Atom) :
    Z3SinkEffects := ⟨effs.statements ++ [(inst, stmt)]⟩

/-- Number of buffered statements. -/
def Z3SinkEffects.count (effs : Z3SinkEffects) : Nat :=
  effs.statements.length

/-- Empty effects have zero statements. -/
theorem Z3SinkEffects.empty_count : Z3SinkEffects.empty.count = 0 := rfl

/-- Adding a statement increments the count. -/
theorem Z3SinkEffects.addStatement_count (effs : Z3SinkEffects) (inst : String) (stmt : Atom) :
    (effs.addStatement inst stmt).count = effs.count + 1 := by
  simp [addStatement, count, List.length_append]

/-- Example: buffering two assertions for the mock Z3 test scenario. -/
def exampleZ3Sinks : Z3SinkEffects :=
  Z3SinkEffects.empty
    |>.addStatement "ins" (.expression [.symbol "declare-const", .symbol "a", .symbol "Int"])
    |>.addStatement "ins" (.expression [.symbol "assert",
        .expression [.symbol ">", .symbol "a", .grounded (.int 0)]])

/-- The example has exactly 2 buffered statements. -/
theorem exampleZ3Sinks_count : exampleZ3Sinks.count = 2 := rfl

end SinkEffects

/-! ## Canaries -/

section Canaries
#check @OracleEnv
#check @oraclePayloadSpace
#check @oracleQuerySpace
#check @oracleMatchPattern
#check @z3CheckSat_routes_to_z3
#check @z3GetModel_routes_to_z3
#check @sat_payload_empty
#check @unsat_payload_empty
#check @model_payload_eq
#check @oracleMatchPattern_mem
#check @oracleMatchPattern_spec
#check @oracleMatchPattern_sat_empty
#check @oracleMatchPattern_unsat_empty
#check @morkOraclePayload_eq
#check @mockZ3Env
#check @mock_z3_checksat
#check @mock_z3_model_has_payload
#check @Z3SinkEffects
#check @Z3SinkEffects.empty
#check @Z3SinkEffects.addStatement
#check @exampleZ3Sinks
end Canaries

/-! ## Axiom audit -/

section AxiomAudit
#print axioms z3CheckSat_routes_to_z3
#print axioms z3GetModel_routes_to_z3
#print axioms sat_payload_empty
#print axioms unsat_payload_empty
#print axioms model_payload_eq
#print axioms oracleMatchPattern_mem
#print axioms oracleMatchPattern_spec
#print axioms oracleMatchPattern_sat_empty
#print axioms oracleMatchPattern_unsat_empty
#print axioms morkOraclePayload_eq
#print axioms mock_z3_checksat
#print axioms mock_z3_model_has_payload
#print axioms mock_z3_model_payload_atoms
#print axioms Z3SinkEffects.empty_count
#print axioms Z3SinkEffects.addStatement_count
#print axioms exampleZ3Sinks_count
end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.Z3Oracle
