import Mettapedia.Languages.VibeITP.Spec.Derivation
import Mettapedia.Languages.VibeITP.Spec.Instr

/-!
# Vibe-ITP specification: the checker protocol

The checker is a state machine over four mutable slot spaces (symbols, terms,
theorems, challenges) and a phase.  Files given before the proof boundary run
in the setup phase; the proof phase begins immediately before the first file
after the boundary, if there is one.

Protocol facts this module fixes:

* Every symbol creation allocates a fresh identity.
* Source operands must name occupied slots; destination operands must name
  empty slots.  Swaps accept empty slots.  Freeing requires an occupied slot,
  and symbol slots below 13 can never be freed, whatever they hold.
* Axioms may only be added in the setup phase.  Inference steps, literal
  theorems, the execution primitive, and challenge satisfaction may only run
  in the proof phase.  Definitions, challenge registration, theorem exchange,
  and slot management run in either phase.  (The published format text says
  that challenges are registered only before the proof phase; the reference
  checker accepts registration in either phase and counts proof-phase
  registrations separately, which this specification records.)
* A challenge is satisfied by a theorem whose statement is syntactically the
  registered statement; the challenge slot is then cleared.
* Operands are checked in stream order, so the first failing check of an
  instruction determines its error.
* Reaching the execution primitive `THM_JIT` ends the run with the verdict
  `unsupported`: it is neither accepted nor rejected.

Ghost fields record the admitted axioms and definitions and the statements of
satisfied challenges; they connect runs to `Derives`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec

inductive Phase where
  | setup
  | proofs
deriving DecidableEq, Repr

/-- Content of a symbol slot.  Slots 0 and 1 initially hold the markers of
bound variables and literals, which can be moved but never applied. -/
inductive SlotSymbol where
  | bvarMarker
  | literalMarker
  | sym (id : SymId)
deriving DecidableEq, Repr

inductive Space where
  | symbol
  | term
  | theorem
  | challenge
deriving DecidableEq, Repr

/-- Phase-restricted primitives. -/
inductive Primitive where
  | modusPonens
  | instantiate
  | litIsNat
  | litLt
  | litAdd
  | litMul
  | litDiv
  | litLength
  | litGet
  | jit
deriving DecidableEq, Repr

/-- Protocol and kernel errors, one per reference checker error class. -/
inductive StepError where
  /-- A source slot is empty. -/
  | missing (space : Space)
  /-- A destination slot is occupied. -/
  | occupied (space : Space)
  /-- Freeing an empty symbol, term, or theorem slot. -/
  | alreadyEmpty (space : Space)
  /-- Freeing a symbol slot below 13. -/
  | protectedSymbol
  /-- Satisfying an empty challenge slot. -/
  | noChallenge
  | axiomInProofs
  | satisfyInSetup
  | inferenceInSetup (op : Primitive)
  /-- Applying a slot that holds a bound-variable or literal marker. -/
  | notApplicable
  /-- The announced argument count differs from the symbol's arity. -/
  | arityMismatch
  /-- The kernel refused to build a term. -/
  | termBuildFailed
  /-- The kernel refused to build a theorem. -/
  | theoremFailed
  /-- The kernel refused a definition. -/
  | definitionFailed
  | exchangeMismatch
  | challengeMismatch
deriving DecidableEq, Repr

/-- Functional update of a slot space. -/
def setSlot {α : Type} (slots : Nat → Option α) (i : Nat) (v : Option α) :
    Nat → Option α :=
  fun j => if j = i then v else slots j

def swapSlots {α : Type} (slots : Nat → Option α) (i j : Nat) : Nat → Option α :=
  fun k => if k = i then slots j else if k = j then slots i else slots k

structure State where
  phase : Phase
  symbols : Nat → Option SlotSymbol
  terms : Nat → Option Term
  theorems : Nat → Option Term
  challenges : Nat → Option Term
  /-- Data of the `n`-th allocated symbol. -/
  fresh : Nat → Option SymInfo
  nextFresh : Nat
  /-- Number of occupied challenge slots. -/
  openChallenges : Nat
  /-- Open challenges when the proof phase began. -/
  setupChallenges : Nat
  /-- Challenges registered during the proof phase. -/
  proofChallenges : Nat
  axioms : List Term
  definitions : List Definition
  satisfied : List Term

namespace State

def sig (st : State) : Sig := sigOf st.fresh

def theory (st : State) : Theory :=
  { sig := st.sig, axioms := st.axioms, definitions := st.definitions }

end State

/-- Symbol slots at the start of a run. -/
def initialSymbols : Nat → Option SlotSymbol
  | 0 => some .bvarMarker
  | 1 => some .literalMarker
  | 2 => some (.sym (.builtin .impl))
  | 3 => some (.sym (.builtin .eq))
  | 4 => some (.sym (.builtin .litIsNat))
  | 5 => some (.sym (.builtin .litLt))
  | 6 => some (.sym (.builtin .litAdd))
  | 7 => some (.sym (.builtin .litMul))
  | 8 => some (.sym (.builtin .litDiv))
  | 9 => some (.sym (.builtin .litLength))
  | 10 => some (.sym (.builtin .litGet))
  | 11 => some (.sym (.builtin .isSafeCode))
  | 12 => some (.sym (.builtin .executedTo))
  | _ => none

def initialState : State :=
  { phase := .setup
    symbols := initialSymbols
    terms := fun _ => none
    theorems := fun _ => none
    challenges := fun _ => none
    fresh := fun _ => none
    nextFresh := 0
    openChallenges := 0
    setupChallenges := 0
    proofChallenges := 0
    axioms := []
    definitions := []
    satisfied := [] }

abbrev StepM := Except StepError

/-- Read an occupied source slot. -/
def need {α : Type} (space : Space) (value : Option α) : StepM α :=
  match value with
  | some a => .ok a
  | none => .error (.missing space)

namespace State

def placeSymbol (st : State) (i : Nat) (s : SlotSymbol) : StepM State :=
  if (st.symbols i).isSome then .error (.occupied .symbol)
  else .ok { st with symbols := setSlot st.symbols i (some s) }

def placeTerm (st : State) (i : Nat) (t : Term) : StepM State :=
  if (st.terms i).isSome then .error (.occupied .term)
  else .ok { st with terms := setSlot st.terms i (some t) }

def placeTheorem (st : State) (i : Nat) (φ : Term) : StepM State :=
  if (st.theorems i).isSome then .error (.occupied .theorem)
  else .ok { st with theorems := setSlot st.theorems i (some φ) }

def placeChallenge (st : State) (i : Nat) (φ : Term) : StepM State :=
  if (st.challenges i).isSome then .error (.occupied .challenge)
  else .ok { st with challenges := setSlot st.challenges i (some φ) }

/-- Allocate a fresh symbol with the given data. -/
def allocate (st : State) (info : SymInfo) : SymId × State :=
  (.fresh st.nextFresh,
    { st with fresh := setSlot st.fresh st.nextFresh (some info),
              nextFresh := st.nextFresh + 1 })

/-- Guard for primitives that run only in the proof phase. -/
def inProofs (st : State) (op : Primitive) : StepM Unit :=
  match st.phase with
  | .proofs => .ok ()
  | .setup => .error (.inferenceInSetup op)

end State

/-- Symbol identities of slot contents; markers are not symbols. -/
def slotIds : List SlotSymbol → Option (List SymId)
  | [] => some []
  | .sym id :: rest => (slotIds rest).map (id :: ·)
  | _ :: _ => none

/-- One instruction.  The result is `none` exactly for the execution
primitive `THM_JIT`, which this specification does not interpret. -/
def execute (st : State) : Instr → Option (StepM State)
  | .fvarNew arity dst => some <|
      let (id, st') := st.allocate (SymInfo.fvarOf arity)
      st'.placeSymbol dst (.sym id)
  | .constNew binders dst => some <|
      let (id, st') := st.allocate { kind := .constant, binders := binders }
      st'.placeSymbol dst (.sym id)
  | .symbolSwap i j => some <|
      .ok { st with symbols := swapSlots st.symbols i j }
  | .symbolFree i => some <|
      if i < protectedSymbolSlots then .error .protectedSymbol
      else if (st.symbols i).isNone then .error (.alreadyEmpty .symbol)
      else .ok { st with symbols := setSlot st.symbols i none }
  | .termNewBVar index dst => some <|
      if index + 1 < wordBound then st.placeTerm dst (.bvar index)
      else .error .termBuildFailed
  | .termNewLiteral bytes dst => some <|
      if bytes.length + 8 < wordBound then st.placeTerm dst (.lit bytes)
      else .error .termBuildFailed
  | .termNewApp s args dst => some <|
      do
      let head ← need .symbol (st.symbols s)
      match head with
      | .sym id =>
          if args.length = symArity st.sig id then do
            let ts ← args.mapM fun i => need .term (st.terms i)
            st.placeTerm dst (.app id ts)
          else .error .arityMismatch
      | _ => .error .notApplicable
  | .termSwap i j => some <|
      .ok { st with terms := swapSlots st.terms i j }
  | .termFree i => some <|
      if (st.terms i).isNone then .error (.alreadyEmpty .term)
      else .ok { st with terms := setSlot st.terms i none }
  | .addAxiom statement dst => some <|
      match st.phase with
      | .proofs => .error .axiomInProofs
      | .setup => do
          let φ ← need .term (st.terms statement)
          if depth st.sig φ = 0 then do
            let st' ← st.placeTheorem dst φ
            pure { st' with axioms := st'.axioms ++ [φ] }
          else .error .theoremFailed
  | .thmExchange h t => some <|
      do
      let φ ← need .theorem (st.theorems h)
      let ψ ← need .term (st.terms t)
      if φ = ψ then pure st else .error .exchangeMismatch
  | .thmFree i => some <|
      if (st.theorems i).isNone then .error (.alreadyEmpty .theorem)
      else .ok { st with theorems := setSlot st.theorems i none }
  | .thmSwap i j => some <|
      .ok { st with theorems := swapSlots st.theorems i j }
  | .challengeAdd statement dst => some <|
      do
      let φ ← need .term (st.terms statement)
      let st' ← st.placeChallenge dst φ
      pure { st' with
        openChallenges := st'.openChallenges + 1
        proofChallenges :=
          match st.phase with
          | .proofs => st'.proofChallenges + 1
          | .setup => st'.proofChallenges }
  | .challengeSatisfy c h => some <|
      match st.phase with
      | .setup => .error .satisfyInSetup
      | .proofs => do
          let φ ← need .theorem (st.theorems h)
          match st.challenges c with
          | none => .error .noChallenge
          | some χ =>
              if χ = φ then
                pure { st with
                  challenges := setSlot st.challenges c none
                  openChallenges := st.openChallenges - 1
                  satisfied := st.satisfied ++ [φ] }
              else .error .challengeMismatch
  | .modusPonens i p dst => some <|
      do
      st.inProofs .modusPonens
      let φ ← need .theorem (st.theorems i)
      let α ← need .theorem (st.theorems p)
      match φ with
      | .app (.builtin .impl) [a, b] =>
          if a = α then st.placeTheorem dst b else .error .theoremFailed
      | _ => .error .theoremFailed
  | .thmInstantiate h f v dst => some <|
      do
      st.inProofs .instantiate
      let φ ← need .theorem (st.theorems h)
      let head ← need .symbol (st.symbols f)
      let value ← need .term (st.terms v)
      match head with
      | .sym F =>
          match instantiateStatement st.sig F value φ with
          | some ψ => st.placeTheorem dst ψ
          | none => .error .theoremFailed
      | _ => .error .theoremFailed
  | .defineConst fvars hints v dstSymbol dstThm => some <|
      do
      let heads ← fvars.mapM fun i => need .symbol (st.symbols i)
      let value ← need .term (st.terms v)
      match slotIds heads with
      | none => .error .definitionFailed
      | some ids =>
          if definitionAdmissible st.sig ids hints value then do
            let (c, st₁) := st.allocate (definitionInfo st.sig ids)
            let st₂ ← st₁.placeSymbol dstSymbol (.sym c)
            let st₃ ← st₂.placeTheorem dstThm (definitionStatement st.sig c ids value)
            pure { st₃ with definitions := st₃.definitions ++ [⟨c, ids, value⟩] }
          else .error .definitionFailed
  | .litIsNat n dst => some <|
      do
      st.inProofs .litIsNat
      st.placeTheorem dst (litIsNatStatement n)
  | .litLt a b dst => some <|
      do
      st.inProofs .litLt
      if a < b then st.placeTheorem dst (litLtStatement a b) else .error .theoremFailed
  | .litAdd a b dst => some <|
      do
      st.inProofs .litAdd
      st.placeTheorem dst (litAddStatement a b)
  | .litMul a b dst => some <|
      do
      st.inProofs .litMul
      st.placeTheorem dst (litMulStatement a b)
  | .litDiv a b dst => some <|
      do
      st.inProofs .litDiv
      if b = 0 then .error .theoremFailed else st.placeTheorem dst (litDivStatement a b)
  | .litLength t dst => some <|
      do
      st.inProofs .litLength
      let τ ← need .term (st.terms t)
      match τ with
      | .lit bytes => st.placeTheorem dst (litLengthStatement bytes)
      | _ => .error .theoremFailed
  | .litGet t index dst => some <|
      do
      st.inProofs .litGet
      let τ ← need .term (st.terms t)
      match τ with
      | .lit bytes =>
          if index < bytes.length then st.placeTheorem dst (litGetStatement bytes index)
          else .error .theoremFailed
      | _ => .error .theoremFailed
  | .jit _ _ _ => none

/-! ## Runs -/

inductive RunResult where
  | ok (st : State)
  | error (instr : Nat) (e : StepError)
  | unsupported (instr : Nat)

/-- Execute the instructions of one file; `index` numbers them from zero. -/
def runInstrs : State → Nat → List Instr → RunResult
  | st, _, [] => .ok st
  | st, index, instr :: rest =>
      match execute st instr with
      | none => .unsupported index
      | some (.ok st') => runInstrs st' (index + 1) rest
      | some (.error e) => .error index e

/-- Checker verdicts.  Only `proofs s p 0` with `s + p > 0` is the
reference checker's full success; `proofs s p k` with `k > 0` completes
without error while `k` challenges remain open. -/
inductive Verdict where
  | malformed (file : Nat) (e : DecodeError)
  | rejected (file instr : Nat) (e : StepError)
  | unsupported (file instr : Nat)
  | setupOnly (openChallenges : Nat)
  | proofs (setupChallenges proofChallenges openChallenges : Nat)
deriving DecidableEq, Repr

inductive FilesResult where
  | ok (st : State)
  | stop (verdict : Verdict)

/-- Execute files in order; `file` numbers them across the whole run. -/
def runFiles : State → Nat → List (List Instr) → FilesResult
  | st, _, [] => .ok st
  | st, file, instrs :: rest =>
      match runInstrs st 0 instrs with
      | .ok st' => runFiles st' (file + 1) rest
      | .error index e => .stop (.rejected file index e)
      | .unsupported index => .stop (.unsupported file index)

/-- Decode every file first, in order. -/
def decodeFiles : Nat → List (List UInt8) → Except (Nat × DecodeError) (List (List Instr))
  | _, [] => .ok []
  | file, bytes :: rest =>
      match decodeFile bytes with
      | .error e => .error (file, e)
      | .ok instrs =>
          match decodeFiles (file + 1) rest with
          | .error e => .error e
          | .ok decoded => .ok (instrs :: decoded)

def enterProofs (st : State) : State :=
  { st with phase := .proofs, setupChallenges := st.openChallenges }

/-- The checker on setup files followed by proof files. -/
def checkRun (setup proofs : List (List UInt8)) : Verdict :=
  match decodeFiles 0 (setup ++ proofs) with
  | .error (file, e) => .malformed file e
  | .ok decoded =>
      match runFiles initialState 0 (decoded.take setup.length) with
      | .stop verdict => verdict
      | .ok st =>
          if proofs.isEmpty then .setupOnly st.openChallenges
          else
            match runFiles (enterProofs st) setup.length (decoded.drop setup.length) with
            | .stop verdict => verdict
            | .ok final =>
                .proofs final.setupChallenges final.proofChallenges final.openChallenges

/-- Full success of a run: the proof phase was reached, some challenge was
registered, and none remains open. -/
def Verdict.success : Verdict → Bool
  | .proofs s p 0 => decide (0 < s + p)
  | _ => false

end Mettapedia.Languages.VibeITP.Spec
