import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueOrder

/-!
# MM2 Work-Queue Core

An executable abstraction of MORK's valid-exec work queue, with read-copy
matching and support-valued updates.

## Real runtime behaviour (from Rust `metta_calculus` + `transform_multi_multi_o`)

1. **Pop** the next `(exec ...)` fact from the PathMap (sorted by serialized path)
2. **Remove** it from live space
3. **Read copy**: `live_after_remove ∪ {exec_fact}` — re-insert so the rule can match itself
4. **Match** the pattern against the read copy (all matches simultaneously)
5. **Apply** template outputs (add/remove) to live space (NOT to read copy)
6. **Repeat** until no more exec facts or the selected fuel observer stops

## Design decisions

- **Exact scheduler key**: this module orders the complete `(exec ...)` atom by
  `morkCompactKey?`, the byte-exact compact-expression encoding.  This matches
  selection under MORK's `exec` PathMap prefix.  The fallback applies only to
  abstract atoms that cannot occur in a physical MM2 space; physical adequacy
  is stated on `MorkCompactRepresentable` spaces.

- **`ExecFact`**: an exec fact is just an `Atom` in the space that happens to be an
  `(exec loc pattern template)` expression.  We define `ExecFact` as a structured
  extraction from such an atom, mirroring the Rust `destruct!(rt, ("exec" loc pat tpl))`.

- **Read copy**: explicit in the formalization, matching the Rust
  `let mut read_copy = self.btm.clone(); read_copy.insert(add.span(), ());`.

## Relationship to ThreePhaseExec

`ThreePhaseExec.lean` defines an authored phase-band protocol (priority ranges
0..31 / 32..63 / 64..95). The work queue is the more fundamental MM2 layer;
`ThreePhaseRefinement.lean` proves restricted firing correspondences under
explicit pattern, template, and grounding hypotheses. It does not assert that
raw MORK assigns phase semantics to those bands.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Exec fact extraction -/

/-- A structured exec fact extracted from an `(exec (priority name) pattern template)` atom.
    Mirrors the Rust `destruct!(rt, ("exec" loc pat_expr tpl_expr))`. -/
structure ExecFact where
  /-- The original atom in the space (for removal). -/
  atom     : Atom
  /-- The raw location term (for ordering). Preserved from the original atom. -/
  loc      : Atom
  /-- The structured rule extracted from the atom. -/
  rule     : ExecRule
  deriving Repr, DecidableEq

/-- Convert a digit character to its numeric value. -/
private def digitToNat : Char → Nat
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9
  | _ => 0

/-- Kernel-reducible natural number parser over `List Char`.
    (`String.foldl` is C-backed and does not reduce definitionally.) -/
private def parseNatAux : List Char → Nat → Nat
  | [], acc => acc
  | c :: cs, acc => parseNatAux cs (acc * 10 + digitToNat c)

/-- Parse a numeric string to ℕ (returns 0 on failure). -/
private def parseNat (s : String) : Nat := parseNatAux s.toList 0

/-- Parse the positive decimal count required by MORK's `head` and `tail`
sinks.  Their runtime constructors reject zero and non-decimal counts.  This
syntax primitive is public so parser correspondence can include extrema
validation rather than treating it as an opaque implementation detail. -/
def parsePositiveNat? (s : String) : Option Nat :=
  if s.isEmpty then none
  else if s.toList.all fun c =>
      c = '0' || c = '1' || c = '2' || c = '3' || c = '4' ||
      c = '5' || c = '6' || c = '7' || c = '8' || c = '9' then
    let count := parseNat s
    if count = 0 then none else some count
  else none

/-- Parse a physical two-argument extrema sink.  This parser primitive is
public so syntax-to-rule correspondence theorems can account for every sink
form admitted by `parseSupportedSink`. -/
def parseExtremaSink (isHead : Bool) (count body : Atom) : Option Sink :=
  match count with
  | .symbol digits => do
      let limit ← parsePositiveNat? digits
      if isHead then pure (.head limit body) else pure (.tail limit body)
  | _ => none

/-- Successful extrema parsing preserves its authored body exactly. -/
theorem parseExtremaSink_atom_eq_body
    (isHead : Bool) (count body : Atom) (sink : Sink)
    (parsed : parseExtremaSink isHead count body = some sink) :
    sink.atom = body := by
  cases isHead with
  | false =>
      cases count with
      | symbol digits =>
          cases limit : parsePositiveNat? digits with
          | none => simp [parseExtremaSink, limit] at parsed
          | some value =>
              simp [parseExtremaSink, limit] at parsed
              subst sink
              rfl
      | var name => simp [parseExtremaSink] at parsed
      | grounded value => simp [parseExtremaSink] at parsed
      | expression children => simp [parseExtremaSink] at parsed
  | true =>
      cases count with
      | symbol digits =>
          cases limit : parsePositiveNat? digits with
          | none => simp [parseExtremaSink, limit] at parsed
          | some value =>
              simp [parseExtremaSink, limit] at parsed
              subst sink
              rfl
      | var name => simp [parseExtremaSink] at parsed
      | grounded value => simp [parseExtremaSink] at parsed
      | expression children => simp [parseExtremaSink] at parsed

/-- Try to extract an `ExecFact` from an atom.
    Recognises the shape `(exec (priority name) (, p₁ ... pₙ) (O s₁ ... sₙ))`.

    This is a simplified extractor that handles the subset of exec atoms used in
    the conformance test suite.  A full extractor would parse arbitrary priority
    terms and sink types. -/
def extractExecFact (a : Atom) : Option ExecFact :=
  match a with
  | .expression (.symbol "exec" :: loc :: patExpr :: tplExpr :: []) =>
    -- Extract priority and name from loc
    let (prio, name) := match loc with
      | .expression [.grounded (.int p), .symbol n] => (p.toNat, n)
      | .expression [.symbol p, .symbol n]          => (parseNat p, n)
      | _ => (0, "unnamed")
    -- Extract pattern atoms (skip the leading `,` functor)
    let patAtoms := match patExpr with
      | .expression (.symbol "," :: rest) => rest
      | _ => []
    -- Extract sinks (skip the leading `O` functor)
    let sinks := match tplExpr with
      | .expression (.symbol "O" :: rest) =>
        rest.filterMap fun s => match s with
          | .expression [.symbol "+", body] => some (.add body)
          | .expression [.symbol "-", body] => some (.remove body)
          | .expression [.symbol "head", count, body] =>
              parseExtremaSink true count body
          | .expression [.symbol "tail", count, body] =>
              parseExtremaSink false count body
          | _ => none
      | _ => []
    some {
      atom := a
      loc  := loc
      rule := mkExecRule prio name (mkPattern patAtoms) (mkTemplate sinks)
    }
  | _ => none

/-- An exec fact with source-aware input specification. -/
structure SourceExecFact where
  /-- The original exec atom in the space. -/
  atom : Atom
  /-- The location term (priority + name). -/
  loc  : Atom
  /-- The structured source-aware rule. -/
  rule : SourceExecRule
  deriving Repr, DecidableEq

/-- The scheduler-visible shell of an MM2 directive.

This is deliberately weaker than a successfully interpreted directive.  The
upstream loop selects every atom with the four-field `(exec ...)` shell,
removes it, and only then asks the interpreter whether its input and output
forms are supported.  Keeping the shell separate lets the formalization state
both the lawful supported fragment and that remove-before-interpret boundary
without pretending that an unknown source or sink has known semantics. -/
structure RawExecFact where
  atom : Atom
  loc : Atom
  inputExpr : Atom
  templateExpr : Atom
  deriving Repr, DecidableEq

/-- Recognize exactly the scheduler-visible four-field `(exec ...)` shell. -/
def extractRawExecFact (a : Atom) : Option RawExecFact :=
  match a with
  | .expression [.symbol "exec", loc, inputExpr, templateExpr] =>
      some ⟨a, loc, inputExpr, templateExpr⟩
  | _ => none

/-- Successful extraction retains the exact scheduler-visible atom. -/
theorem extractRawExecFact_atom_eq
    {atom : Atom} {raw : RawExecFact}
    (extracted : extractRawExecFact atom = some raw) :
    raw.atom = atom := by
  unfold extractRawExecFact at extracted
  split at extracted <;> try contradiction
  next _ =>
    injection extracted with rawEqual
    exact congrArg RawExecFact.atom rawEqual.symm

/-- Parse a list of source factors from `(I src₁ src₂ ...)` body. -/
def parseSourceFactors (args : List Atom) : List SourceFactor :=
  args.filterMap fun arg => match arg with
    | .expression [.symbol "BTM", pat] => some (.btm pat)
    | .expression [.symbol "==", pat, witness] => some (.eqConstraint pat witness)
    | .expression [.symbol "!=", pat, witness] => some (.neqConstraint pat witness)
    | _ => none

/-- Parse sinks from a template expression `(O sink₁ ...)`. -/
def parseSinks (tplExpr : Atom) : List Sink :=
  match tplExpr with
  | .expression (.symbol "O" :: rest) =>
    rest.filterMap fun s => match s with
      | .expression [.symbol "+", body] => some (.add body)
      | .expression [.symbol "-", body] => some (.remove body)
      | .expression [.symbol "head", count, body] =>
          parseExtremaSink true count body
      | .expression [.symbol "tail", count, body] =>
          parseExtremaSink false count body
      | _ => none
  | _ => match tplExpr with
    | .expression (.symbol "," :: rest) =>
      rest.map (.add ·)
    | _ => []

/-! ## Strict parser for the modeled source/sink fragment

The older compatibility parser above is intentionally permissive: it filters
unknown factors and sinks so bridge experiments can project a larger interface
onto the small Lean model.  It must not decide whether an MM2 directive is
well formed.  The option-valued parser below rejects the whole directive when
any source or sink is outside the explicitly modeled vocabulary. -/

/-- Parse one source factor supported by the current Lean semantics. -/
def parseSupportedSourceFactor : Atom → Option SourceFactor
  | .expression [.symbol "BTM", pat] => some (.btm pat)
  | .expression [.symbol "==", pat, witness] =>
      some (.eqConstraint pat witness)
  | .expression [.symbol "!=", pat, witness] =>
      some (.neqConstraint pat witness)
  | _ => none

/-- Parse every source factor, failing rather than dropping an unknown one. -/
def parseSupportedSourceFactors : List Atom → Option (List SourceFactor)
  | [] => some []
  | factor :: rest => do
      let parsed ← parseSupportedSourceFactor factor
      let parsedRest ← parseSupportedSourceFactors rest
      pure (parsed :: parsedRest)

/-- Parse one sink supported by the current Lean semantics. -/
def parseSupportedSink : Atom → Option Sink
  | .expression [.symbol "+", body] => some (.add body)
  | .expression [.symbol "-", body] => some (.remove body)
  | .expression [.symbol "head", count, body] =>
      parseExtremaSink true count body
  | .expression [.symbol "tail", count, body] =>
      parseExtremaSink false count body
  | _ => none

/-- Parse every explicit sink, failing rather than dropping an unknown one. -/
def parseSupportedSinkList : List Atom → Option (List Sink)
  | [] => some []
  | sink :: rest => do
      let parsed ← parseSupportedSink sink
      let parsedRest ← parseSupportedSinkList rest
      pure (parsed :: parsedRest)

/-- Parse the two input modes whose behavior is modeled in `Space.lean`. -/
def parseSupportedInput : Atom → Option InputSpec
  | .expression (.symbol "," :: patterns) =>
      some (.compat (mkPattern patterns))
  | .expression (.symbol "I" :: factors) => do
      pure (.explicit (← parseSupportedSourceFactors factors))
  | _ => none

/-- Parse the two output modes whose behavior is modeled in `Space.lean`.

Comma output is the pure multi-add form; `O` is the explicit sink form. -/
def parseSupportedTemplate : Atom → Option Template
  | .expression (.symbol "," :: outputs) =>
      some (mkTemplate (outputs.map Sink.add))
  | .expression (.symbol "O" :: sinks) => do
      pure (mkTemplate (← parseSupportedSinkList sinks))
  | _ => none

/-- Decode a raw scheduler shell only when all of its input and output
vocabulary has semantics in the current Lean model. -/
def decodeSupportedSourceExec (raw : RawExecFact) : Option SourceExecFact := do
  let input ← parseSupportedInput raw.inputExpr
  let tmpl ← parseSupportedTemplate raw.templateExpr
  let (priority, name) := match raw.loc with
    | .expression [.grounded (.int p), .symbol n] => (p.toNat, n)
    | .expression [.symbol p, .symbol n] => (parseNat p, n)
    | _ => (0, "unnamed")
  pure {
    atom := raw.atom
    loc := raw.loc
    rule := ⟨priority, name, input, [], tmpl⟩
  }

/-- Strictly decode a supported source-exec atom. -/
def extractSupportedSourceExecFact (a : Atom) : Option SourceExecFact := do
  decodeSupportedSourceExec (← extractRawExecFact a)

/-- Try to extract a `SourceExecFact` from an atom.
    Recognises both compat-mode `(exec loc (, ...) (O ...))` and
    explicit-source `(exec loc (I ...) (O ...))`.  -/
def extractSourceExecFact (a : Atom) : Option SourceExecFact :=
  match a with
  | .expression (.symbol "exec" :: loc :: inputExpr :: tplExpr :: []) =>
    let (prio, name) := match loc with
      | .expression [.grounded (.int p), .symbol n] => (p.toNat, n)
      | .expression [.symbol p, .symbol n]          => (parseNat p, n)
      | _ => (0, "unnamed")
    let sinks := parseSinks tplExpr
    let input := match inputExpr with
      | .expression (.symbol "I" :: rest) =>
        InputSpec.explicit (parseSourceFactors rest)
      | .expression (.symbol "," :: rest) =>
        InputSpec.compat (mkPattern rest)
      | _ => InputSpec.compat (mkPattern [])
    some {
      atom := a
      loc  := loc
      rule := ⟨prio, name, input, [], mkTemplate sinks⟩
    }
  | _ => none

/-- Convert a `SourceExecFact` to an `ExecFact` when the input is compat-mode. -/
def SourceExecFact.toExecFact? (sef : SourceExecFact) : Option ExecFact :=
  match sef.rule.input with
  | .compat pat => some ⟨sef.atom, sef.loc, mkExecRule sef.rule.priority sef.rule.name pat sef.rule.tmpl⟩
  | .explicit _ => none

/-! ## Abstract scheduler key -/

/-- A scheduler key assigns a lexicographic ordering to exec facts.
    In the real runtime, this is the serialized PathMap path (shortlex byte order).
    We abstract it as a `List ℕ` to avoid committing to byte-level details. -/
class SchedulerKey (α : Type) where
  key : α → List ℕ

/-- Total extension of MORK's exact compact-expression key.

Representable MM2 atoms use their exact physical bytes.  The `0x100` fallback
is outside the byte range and gives abstract, non-MM2 host atoms a deterministic
order without pretending that they have a PathMap representation. -/
def totalMorkCompactKey (atom : Atom) : List Nat :=
  (morkCompactKey? atom).getD (0x100 :: atomKey atom)

/-! ## The built-in support sink provider -/

/-- Insert one atom into a list presentation of finite support. -/
def insertSupport (support : List Atom) (atom : Atom) : List Atom :=
  if atom ∈ support then support else support ++ [atom]

/-- Instantiate and stage one successful match for a built-in MM2 sink.

The stage is support-valued, mirroring the private `PathMap<()>` used by MORK
sinks.  This admitted fragment requires produced insertion/extrema values to be
ground.  Removing a value retains the historical exact-key behavior of the
support model. -/
def stageSupportSink (sink : Sink) (staged : List Atom) (substitution : Subst) :
    List Atom :=
  let instantiated := applySubst substitution sink.atom
  match sink with
  | .remove _ => insertSupport staged instantiated
  | .add _ | .head _ _ | .tail _ _ =>
      if isGroundAtom instantiated then insertSupport staged instantiated
      else staged

/-- Sort staged support by the exact compact-expression key.  `head` keeps the
least paths and `tail` the greatest paths, matching MORK's extrema sink. -/
def compactExtremaList (least : Bool) (count : Nat) (staged : List Atom) :
    List Atom :=
  let ordered := staged.mergeSort fun left right =>
    if least then
      lexLt (totalMorkCompactKey left) (totalMorkCompactKey right)
    else
      lexLt (totalMorkCompactKey right) (totalMorkCompactKey left)
  ordered.take count

/-- Finite-support view of `compactExtremaList`. -/
def compactExtrema (least : Bool) (count : Nat) (staged : List Atom) :
    Finset Atom :=
  (compactExtremaList least count staged).toFinset

/-- Finalize one independently staged built-in sink into the live space. -/
def finalizeSupportSink (sink : Sink) (staged : List Atom) (space : Space) :
    Space :=
  match sink with
  | .add _ => space ∪ staged.toFinset
  | .remove _ => space \ staged.toFinset
  | .head count _ => space ∪ compactExtrema true count staged
  | .tail count _ => space ∪ compactExtrema false count staged

/-- The exact batched provider for the currently admitted, support-valued MM2
sink fragment.  Native Rust and C realizations may use different data
structures; adequacy depends only on these stage/finalize operations. -/
def morkSupportSinkProvider : BatchSinkProvider Sink where
  Stage := fun _ => List Atom
  init := fun _ => []
  stage := stageSupportSink
  finalize := finalizeSupportSink

/-- Apply every authored sink after staging all match substitutions. -/
def applyMorkSinkBatch (space : Space) (rows : List Subst)
    (template : Template) : Space :=
  morkSupportSinkProvider.run rows space template.sinks

/-- Duplicate rows do not duplicate a support-valued staged result. -/
theorem stageSupportSink_duplicate (sink : Sink) (substitution : Subst) :
    stageSupportSink sink
        (stageSupportSink sink [] substitution) substitution =
      stageSupportSink sink [] substitution := by
  cases sink <;> simp [stageSupportSink, insertSupport]

/-- Positive ordering canary used by physical `head`: `a` precedes `b`. -/
theorem compact_symbol_order_canary :
    lexLt (totalMorkCompactKey (.symbol "a"))
      (totalMorkCompactKey (.symbol "b")) = true := by
  decide

/-- A singleton head batch retains its one staged path. -/
theorem compactExtrema_singleton_canary :
    compactExtrema true 1 [.symbol "a"] =
      ({.symbol "a"} : Finset Atom) := by
  simp [compactExtrema, compactExtremaList]

/-- A zero-sized extrema request retains no paths.  The strict physical parser
rejects this case; the semantic totalization remains explicit. -/
theorem compactExtrema_zero_canary (least : Bool) (staged : List Atom) :
    compactExtrema least 0 staged = ∅ := by
  simp [compactExtrema, compactExtremaList]

@[simp] theorem compactExtrema_nil (least : Bool) (count : Nat) :
    compactExtrema least count [] = ∅ := by
  simp [compactExtrema, compactExtremaList]

/-- Extrema over one staged value retain that value exactly when the requested
count is positive. -/
theorem compactExtrema_singleton (least : Bool) (count : Nat) (atom : Atom) :
    compactExtrema least count [atom] =
      if count = 0 then ∅ else {atom} := by
  cases count with
  | zero => simp [compactExtrema, compactExtremaList]
  | succ count => simp [compactExtrema, compactExtremaList]

/-- Staging and finalizing one row agrees with the historical one-row sink
projection. -/
theorem finalizeSupportSink_singleton (space : Space) (substitution : Subst)
    (sink : Sink) :
    finalizeSupportSink sink (stageSupportSink sink [] substitution) space =
      applySink space substitution sink := by
  cases sink with
  | add atom =>
      by_cases ground : isGroundAtom (applySubst substitution atom) = true
      · simp [stageSupportSink, finalizeSupportSink, insertSupport, applySink,
          Sink.atom, ground]
      · simp [stageSupportSink, finalizeSupportSink, applySink,
          Sink.atom, ground]
  | remove atom =>
      ext candidate
      simp [stageSupportSink, finalizeSupportSink, insertSupport, applySink,
        Sink.atom, and_comm]
  | head count atom =>
      cases count with
      | zero =>
          simp [stageSupportSink, finalizeSupportSink, applySink,
            Sink.atom, compactExtrema_zero_canary]
      | succ count =>
          cases ground : isGroundAtom (applySubst substitution atom) <;>
            simp [stageSupportSink, finalizeSupportSink, applySink, Sink.atom,
              ground, insertSupport, compactExtrema_singleton,
              compactExtrema_nil]
  | tail count atom =>
      cases count with
      | zero =>
          simp [stageSupportSink, finalizeSupportSink, applySink,
            Sink.atom, compactExtrema_zero_canary]
      | succ count =>
          cases ground : isGroundAtom (applySubst substitution atom) <;>
            simp [stageSupportSink, finalizeSupportSink, applySink, Sink.atom,
              ground, insertSupport, compactExtrema_singleton,
              compactExtrema_nil]

/-- A whole singleton-row batch agrees with row-local `applySinks`. -/
theorem applyMorkSinkBatch_singleton (space : Space) (substitution : Subst)
    (template : Template) :
    applyMorkSinkBatch space [substitution] template =
      applySinks space substitution template := by
  unfold applyMorkSinkBatch applySinks
  induction template.sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      simp only [BatchSinkProvider.run_cons, List.foldl_cons]
      rw [show morkSupportSinkProvider.stageAll sink [substitution] =
          stageSupportSink sink [] substitution from rfl]
      rw [show morkSupportSinkProvider.finalize sink
          (stageSupportSink sink [] substitution) space =
          finalizeSupportSink sink (stageSupportSink sink [] substitution) space from rfl]
      rw [finalizeSupportSink_singleton]
      exact induction (applySink space substitution sink)

/-- With no matching rows, every built-in staged state is empty and the batch
leaves the live space unchanged. -/
theorem applyMorkSinkBatch_empty (space : Space) (template : Template) :
    applyMorkSinkBatch space [] template = space := by
  unfold applyMorkSinkBatch
  induction template.sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      simp only [BatchSinkProvider.run_cons]
      have emptyFinalize : morkSupportSinkProvider.finalize sink
          (morkSupportSinkProvider.stageAll sink []) space = space := by
        cases sink <;> simp [morkSupportSinkProvider,
          BatchSinkProvider.stageAll, finalizeSupportSink, compactExtrema,
          compactExtremaList]
      rw [emptyFinalize]
      exact induction space

instance : SchedulerKey ExecFact where
  key ef := totalMorkCompactKey ef.atom

instance : SchedulerKey SourceExecFact where
  key ef := totalMorkCompactKey ef.atom

instance : SchedulerKey RawExecFact where
  key ef := totalMorkCompactKey ef.atom

/-- Generic least-key selection used by the source-aware and raw envelopes. -/
def selectNextScheduled [SchedulerKey α] (facts : List α) : Option α :=
  facts.foldl (fun best fact =>
    match best with
    | none => some fact
    | some current =>
      if lexLt (SchedulerKey.key fact) (SchedulerKey.key current)
      then some fact
      else some current
  ) none

/-- Select the minimum exec fact from a list by scheduler key. -/
def selectNextExec (facts : List ExecFact) : Option ExecFact :=
  selectNextScheduled facts

/-! ## Work-queue step -/

/-- Extract all exec facts from a space.
    Scans all atoms, returns those successfully parsed as exec facts. -/
noncomputable def execFactsOfSpace (s : Space) : List ExecFact :=
  s.toList.filterMap extractExecFact

/-- Strictly supported source-aware directives in a space. -/
noncomputable def supportedSourceExecFactsOfSpace (s : Space) :
    List SourceExecFact :=
  s.toList.filterMap extractSupportedSourceExecFact

/-- All scheduler-visible raw exec shells in a space. -/
noncomputable def rawExecFactsOfSpace (s : Space) : List RawExecFact :=
  s.toList.filterMap extractRawExecFact

/-- Remove an atom from the space (consume the exec fact from live). -/
def consumeExec (s : Space) (ef : ExecFact) : Space :=
  s.erase ef.atom

/-- Construct the read copy: live space (with exec removed) plus the exec fact re-inserted.
    This is the space against which patterns are matched.

    Mirrors Rust: `let mut read_copy = self.btm.clone(); read_copy.insert(add.span(), ());`
    where `add` is the exec fact that was just removed. -/
def readCopy (s : Space) (ef : ExecFact) : Space :=
  consumeExec s ef ∪ {ef.atom}

/-- Fire all matches of an exec fact's rule against the read copy,
    then apply template outputs to the live space (after exec removal).

    Returns the new live space.

    Key semantic point: matching happens against `readCopy`, but mutations
    apply to `consumeExec s ef` (the live space with exec consumed). -/
noncomputable def fireExecFact (s : Space) (ef : ExecFact) : Space :=
  let live := consumeExec s ef
  let rc := readCopy s ef
  let ms := matchPattern [] rc ef.rule.pat
  applyMorkSinkBatch live (ms.map Prod.fst) ef.rule.tmpl

/-- One step of the work-queue scheduler:
    1. Extract exec facts from the space
    2. Select the one with minimum scheduler key
    3. Consume it from live
    4. Match against read copy
    5. Apply outputs to live

    Returns `none` if no exec facts remain (termination). -/
noncomputable def workQueueStep (s : Space) : Option Space :=
  let facts := execFactsOfSpace s
  match selectNextExec facts with
  | none => none
  | some ef => some (fireExecFact s ef)

/-- Lawful exact-fuel work-queue execution.

    `workQueueRunN fuel` interprets at most `fuel` exec facts, and zero fuel is
    the identity. This is the intended bounded observer used by the GSLT
    theory. It does **not** identify the current upstream Rust loop, which
    checks its bound after interpreting a candidate; that implementation is
    represented separately by `upstreamMettaCalculusRunN` below. -/
noncomputable def workQueueRunN : ℕ → Space → Space × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    match workQueueStep s with
    | none => (s, 0)
    | some s' =>
      let (final, n) := workQueueRunN fuel s'
      (final, n + 1)

/-! ## Source-aware work-queue firing

When exec facts carry `SourceExecRule`s, the firing path uses
`matchInputSpec` instead of `matchPattern`. -/

/-- Consume an atom from the space (generalized: only needs the atom). -/
noncomputable def consumeAtom (s : Space) (a : Atom) : Space := s.erase a

/-- Read copy from consuming an atom. -/
noncomputable def readCopyAtom (s : Space) (a : Atom) : Space :=
  consumeAtom s a ∪ {a}

/-- Fire a source-exec-fact: match its input spec against the read copy,
    then apply template sinks to the live space. -/
noncomputable def fireSourceExecFact (s : Space) (sef : SourceExecFact) : Space :=
  let live := consumeAtom s sef.atom
  let rc := readCopyAtom s sef.atom
  let ms := matchInputSpec [] rc sef.rule.input
  applyMorkSinkBatch live (ms.map Prod.fst) sef.rule.tmpl

/-- Source-aware firing restricts exactly to compatible firing whenever the
source directive has a compatible `ExecFact` projection. -/
theorem fireSourceExecFact_eq_fireExecFact_of_toExecFact
    (s : Space) (sourceFact : SourceExecFact) (execFact : ExecFact)
    (projected : sourceFact.toExecFact? = some execFact) :
    fireSourceExecFact s sourceFact = fireExecFact s execFact := by
  rcases sourceFact with ⟨atom, loc, rule⟩
  rcases rule with ⟨priority, name, input, guards, tmpl⟩
  cases input with
  | compat pattern =>
      simp only [SourceExecFact.toExecFact?, Option.some.injEq] at projected
      subst execFact
      rfl
  | explicit factors =>
      simp [SourceExecFact.toExecFact?] at projected

/-! ## Source-aware execution profiles -/

/-- What the work queue does with a scheduler-visible directive that the
selected interpreter does not understand.

`leaveInert` is the open-world language policy: unknown atoms remain data and
are not scheduled.  `consume` applies the current upstream boundary shape to
the selected Lean interpreter: the raw shell is selected and removed before
interpretation, so failed interpretation does not restore it.  It does not
assert that source/sink cases absent from the Lean decoder are also absent
from upstream's larger factory. -/
inductive UnsupportedExecPolicy where
  | leaveInert
  | consume
  deriving Repr, DecidableEq

/-- One source-aware MM2 work-queue step, indexed by its unsupported-directive
policy.  Both profiles use the same source/sink interpreter and scheduler key.
They differ only in whether scheduler selection ranges over supported
directives or over all raw exec shells. -/
noncomputable def sourceWorkQueueStep
    (policy : UnsupportedExecPolicy) (s : Space) : Option Space :=
  match policy with
  | .leaveInert =>
      match selectNextScheduled (supportedSourceExecFactsOfSpace s) with
      | none => none
      | some directive => some (fireSourceExecFact s directive)
  | .consume =>
      match selectNextScheduled (rawExecFactsOfSpace s) with
      | none => none
      | some raw =>
          match decodeSupportedSourceExec raw with
          | some directive => some (fireSourceExecFact s directive)
          | none => some (s.erase raw.atom)

/-- Exact-fuel source-aware execution for either unsupported-directive
policy.  Zero fuel is the identity and the returned counter is the number of
successful profile steps. -/
noncomputable def sourceWorkQueueRunN (policy : UnsupportedExecPolicy) :
    Nat → Space → Space × Nat
  | 0, space => (space, 0)
  | fuel + 1, space =>
      match sourceWorkQueueStep policy space with
      | none => (space, 0)
      | some next =>
          let (final, used) := sourceWorkQueueRunN policy fuel next
          (final, used + 1)

/-- The open-world profile is quiescent exactly when no supported source-exec
directive can be selected. -/
theorem sourceWorkQueueStep_leaveInert_none_iff (s : Space) :
    sourceWorkQueueStep .leaveInert s = none ↔
      selectNextScheduled (supportedSourceExecFactsOfSpace s) = none := by
  cases selected : selectNextScheduled (supportedSourceExecFactsOfSpace s) <;>
    simp [sourceWorkQueueStep, selected]

/-- The consuming profile is quiescent exactly when no raw exec shell exists.
This distinguishes absence of work from failed interpretation. -/
theorem sourceWorkQueueStep_consume_none_iff (s : Space) :
    sourceWorkQueueStep .consume s = none ↔
      selectNextScheduled (rawExecFactsOfSpace s) = none := by
  cases selected : selectNextScheduled (rawExecFactsOfSpace s) with
  | none => simp [sourceWorkQueueStep, selected]
  | some raw =>
      cases decoded : decodeSupportedSourceExec raw <;>
        simp [sourceWorkQueueStep, selected, decoded]

/-- A selected supported directive fires normally at the consuming boundary. -/
theorem sourceWorkQueueStep_consume_supported
    {s : Space} {raw : RawExecFact} {directive : SourceExecFact}
    (selected : selectNextScheduled (rawExecFactsOfSpace s) = some raw)
    (decoded : decodeSupportedSourceExec raw = some directive) :
    sourceWorkQueueStep .consume s = some (fireSourceExecFact s directive) := by
  simp [sourceWorkQueueStep, selected, decoded]

/-- A selected unsupported raw shell is consumed and nothing else is
interpreted.  This is the exact remove-before-interpret behavior of the
modeled upstream boundary. -/
theorem sourceWorkQueueStep_consume_unsupported
    {s : Space} {raw : RawExecFact}
    (selected : selectNextScheduled (rawExecFactsOfSpace s) = some raw)
    (unsupported : decodeSupportedSourceExec raw = none) :
    sourceWorkQueueStep .consume s = some (s.erase raw.atom) := by
  simp [sourceWorkQueueStep, selected, unsupported]

/-- On a selected compatible directive, the strict source-aware profile and
the historical compatible profile take the same step.  The two selection
hypotheses expose the remaining parser/scheduler-fragment obligation rather
than silently identifying their candidate sets. -/
theorem sourceWorkQueueStep_leaveInert_eq_workQueueStep_of_selected
    {s : Space} {sourceFact : SourceExecFact} {execFact : ExecFact}
    (sourceSelected :
      selectNextScheduled (supportedSourceExecFactsOfSpace s) = some sourceFact)
    (execSelected : selectNextExec (execFactsOfSpace s) = some execFact)
    (projected : sourceFact.toExecFact? = some execFact) :
    sourceWorkQueueStep .leaveInert s = workQueueStep s := by
  simp only [sourceWorkQueueStep, sourceSelected, workQueueStep, execSelected]
  rw [fireSourceExecFact_eq_fireExecFact_of_toExecFact s sourceFact execFact
    projected]

/-! ## Basic structural lemmas -/

/-- The read copy always contains the exec fact itself. -/
theorem readCopy_mem_exec (s : Space) (ef : ExecFact) :
    ef.atom ∈ readCopy s ef := by
  simp [readCopy]

/-- Consuming an exec fact removes it from the space (when present). -/
theorem consumeExec_not_mem (s : Space) (ef : ExecFact) :
    ef.atom ∉ consumeExec s ef := by
  simp [consumeExec]

/-- Consuming an exec fact preserves all other atoms. -/
theorem consumeExec_mem_other (s : Space) (ef : ExecFact) (a : Atom)
    (ha : a ∈ s) (hne : a ≠ ef.atom) :
    a ∈ consumeExec s ef := by
  simp [consumeExec]
  exact ⟨hne, ha⟩

/-- The read copy preserves all non-exec atoms from the original space. -/
theorem readCopy_mem_other (s : Space) (ef : ExecFact) (a : Atom)
    (ha : a ∈ s) (hne : a ≠ ef.atom) :
    a ∈ readCopy s ef := by
  simp [readCopy]
  exact Or.inr (consumeExec_mem_other s ef a ha hne)

/-- If the exec fact was in the space, the read copy has the same elements.
    (Removing then re-inserting = identity on membership.) -/
theorem readCopy_eq_of_mem (s : Space) (ef : ExecFact) (hm : ef.atom ∈ s) :
    readCopy s ef = s := by
  simp [readCopy, consumeExec]
  ext a
  simp [Finset.mem_erase]
  constructor
  · rintro (rfl | ⟨_, ha⟩)
    · exact hm
    · exact ha
  · intro ha
    by_cases h : a = ef.atom
    · left; exact h
    · right; exact ⟨h, ha⟩

/-- `workQueueStep` returns `none` iff no exec facts are in the space. -/
theorem workQueueStep_none_iff (s : Space) :
    workQueueStep s = none ↔ selectNextExec (execFactsOfSpace s) = none := by
  simp [workQueueStep]
  split <;> simp_all

/-- `workQueueRunN 0` is the identity. -/
theorem workQueueRunN_zero (s : Space) :
    workQueueRunN 0 s = (s, 0) := rfl

/-! ## Pinned upstream post-check fuel behavior -/

/-- Current upstream `Space::metta_calculus(steps)` on the valid-exec fragment.

    The Rust loop interprets a selected exec in its `while` condition and only
    then tests `done < steps`. Hence it may change the space `steps + 1` times
    while reporting at most `steps`. This definition records that behavior
    without weakening the lawful exact-fuel observer above.

    The model is restricted to valid exec facts accepted by `workQueueStep`.
    Upstream's separate remove-before-parse behavior for malformed `exec`
    atoms remains outside this fragment. -/
noncomputable def upstreamMettaCalculusRunN (steps : ℕ) (s : Space) : Space × ℕ :=
  let run := workQueueRunN (steps + 1) s
  (run.1, min run.2 steps)

/-- Upstream state is the exact-fuel state after one additional allowance. -/
theorem upstreamMettaCalculusRunN_state (steps : ℕ) (s : Space) :
    (upstreamMettaCalculusRunN steps s).1 =
      (workQueueRunN (steps + 1) s).1 := rfl

/-- Upstream's reported counter remains bounded by its argument even though
    the state may have taken one additional step. -/
theorem upstreamMettaCalculusRunN_reported_le (steps : ℕ) (s : Space) :
    (upstreamMettaCalculusRunN steps s).2 ≤ steps := by
  simp [upstreamMettaCalculusRunN]

/-- With zero requested steps, an available exec is nevertheless interpreted
    once while the returned counter remains zero. -/
theorem upstreamMettaCalculusRunN_zero_of_step (s s' : Space)
    (hstep : workQueueStep s = some s') :
    upstreamMettaCalculusRunN 0 s = (s', 0) := by
  simp [upstreamMettaCalculusRunN, workQueueRunN, hstep]

/-- A changing first step separates upstream post-check behavior from the
    lawful zero-fuel observer. -/
theorem upstream_zero_differs_from_exact_fuel (s s' : Space)
    (hstep : workQueueStep s = some s') (hne : s' ≠ s) :
    upstreamMettaCalculusRunN 0 s ≠ workQueueRunN 0 s := by
  rw [upstreamMettaCalculusRunN_zero_of_step s s' hstep, workQueueRunN_zero]
  simp [hne]

/-! ## Cardinality lemmas -/

/-- Consuming an exec fact strictly decreases space cardinality. -/
theorem consumeExec_card_lt (s : Space) (ef : ExecFact) (hm : ef.atom ∈ s) :
    (consumeExec s ef).card < s.card := by
  simp only [consumeExec]
  exact Finset.card_erase_lt_of_mem hm

/-- A template is remove-only (no add or head sinks). -/
def Template.isRemoveOnly (tmpl : Template) : Prop :=
  ∀ sink ∈ tmpl.sinks, ∃ a, sink = .remove a

/-- A single remove sink cannot increase space cardinality. -/
private theorem applySink_remove_card_le (s : Space) (σ : Subst) (a : Atom) :
    (applySink s σ (.remove a)).card ≤ s.card := by
  simp only [applySink]
  exact Finset.card_erase_le

/-- Remove-only templates cannot increase space cardinality. -/
theorem applySinks_removeOnly_card_le (s : Space) (σ : Subst) (sinks : List Sink)
    (hro : ∀ sink ∈ sinks, ∃ a, sink = .remove a) :
    (sinks.foldl (applySink · σ) s).card ≤ s.card := by
  induction sinks generalizing s with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨a, ha⟩ := hro hd (by simp)
    subst ha
    calc (tl.foldl (applySink · σ) (applySink s σ (.remove a))).card
        ≤ (applySink s σ (.remove a)).card :=
          ih _ (fun sink hs => hro sink (List.mem_cons_of_mem _ hs))
      _ ≤ s.card := applySink_remove_card_le s σ a

/-- Batched support finalization of a remove-only sink list is
cardinality-nonincreasing. -/
theorem applyMorkSinkBatch_removeOnly_card_le (rows : List Subst)
    (space : Space) (sinks : List Sink)
    (removeOnly : ∀ sink ∈ sinks, ∃ atom, sink = .remove atom) :
    (morkSupportSinkProvider.run rows space sinks).card ≤ space.card := by
  induction sinks generalizing space with
  | nil => simp
  | cons sink rest induction =>
      obtain ⟨atom, equal⟩ := removeOnly sink (by simp)
      subst sink
      simp only [BatchSinkProvider.run_cons, morkSupportSinkProvider,
        BatchSinkProvider.stageAll, finalizeSupportSink]
      exact le_trans
        (induction (space \ (rows.foldl (stageSupportSink (.remove atom)) []).toFinset)
          (fun candidate present =>
            removeOnly candidate (List.mem_cons_of_mem _ present)))
        (Finset.card_le_card (Finset.sdiff_subset))

/-! ## Termination under remove-only templates -/

/-- Under remove-only templates, `fireExecFact` strictly decreases cardinality.
    This guarantees scheduler termination: the space shrinks at every step,
    so the scheduler must halt within `s.card` steps.

    The proof combines exec consumption with the batched provider's
    remove-only monotonicity. -/
theorem fireExecFact_card_lt_of_removeOnly (s : Space) (ef : ExecFact)
    (hm : ef.atom ∈ s)
    (hro : Template.isRemoveOnly ef.rule.tmpl) :
    (fireExecFact s ef).card < s.card := by
  simp only [fireExecFact, applyMorkSinkBatch]
  exact Nat.lt_of_le_of_lt
    (applyMorkSinkBatch_removeOnly_card_le
      ((matchPattern [] (readCopy s ef) ef.rule.pat).map Prod.fst)
      (consumeExec s ef) ef.rule.tmpl.sinks hro)
    (consumeExec_card_lt s ef hm)

/-- `workQueueRunN` takes at most `fuel` steps (general bound). -/
theorem workQueueRunN_steps_le_fuel (fuel : ℕ) (s : Space) :
    (workQueueRunN fuel s).2 ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [workQueueRunN]
  | succ n ih =>
    simp only [workQueueRunN]
    match workQueueStep s with
    | none => simp
    | some s' =>
      simp only
      exact Nat.succ_le_succ (ih s')

/-! ## Computable reference scheduler

The spec-level `workQueueStep` uses `Finset.toList` and is noncomputable.
For conformance testing, we mirror the scheduler over `List Atom`. -/

namespace WQComputable

open Conformance.Computable (CSpace cmatchPattern capplySinks cmatchAtom cmatchAtomList
  cmatchInputSpec)

/-- Union staged support into a computable list-space without introducing
duplicate occurrences. -/
def cUnionSupport : List Atom → List Atom → List Atom
  | space, [] => space
  | space, atom :: rest => cUnionSupport (insertSupport space atom) rest

/-- Remove every staged support atom from a computable list-space. -/
def cSubtractSupport (space staged : List Atom) : List Atom :=
  space.filter fun atom => atom ∉ staged

/-- Computable list realization of one support-sink finalization. -/
def cFinalizeSupportSink (sink : Sink) (staged : List Atom)
    (space : List Atom) : List Atom :=
  match sink with
  | .add _ => cUnionSupport space staged
  | .remove _ => cSubtractSupport space staged
  | .head count _ =>
      cUnionSupport space (compactExtremaList true count staged)
  | .tail count _ =>
      cUnionSupport space (compactExtremaList false count staged)

/-- Computable batched support-sink realization. -/
def cApplyMorkSinkBatch (rows : List Subst) : List Atom → List Sink → List Atom
  | space, [] => space
  | space, sink :: rest =>
      let staged := rows.foldl (stageSupportSink sink) []
      cApplyMorkSinkBatch rows (cFinalizeSupportSink sink staged space) rest

/-- Apply a computable template through the same stage-all/finalize-left-to-
right boundary as the mathematical provider. -/
def cApplyMorkTemplate (space : List Atom) (rows : List Subst)
    (template : Template) : List Atom :=
  cApplyMorkSinkBatch rows space template.sinks

/-- Extract exec facts from a computable (List Atom) space. -/
def cExecFacts (s : List Atom) : List ExecFact :=
  s.filterMap extractExecFact

/-- Consume an exec fact from a computable space (removes first occurrence). -/
def cConsumeExec (s : List Atom) (ef : ExecFact) : List Atom :=
  s.erase ef.atom

/-- Computable read copy: remove exec fact, then re-add it at the head. -/
def cReadCopy (s : List Atom) (ef : ExecFact) : List Atom :=
  ef.atom :: cConsumeExec s ef

/-- Fire all matches of an exec fact against the read copy,
    applying template outputs to the live space. -/
def cFireExecFact (s : List Atom) (ef : ExecFact) : List Atom :=
  let live := cConsumeExec s ef
  let rc := cReadCopy s ef
  let ms := cmatchPattern [] rc ef.rule.pat
  cApplyMorkTemplate live (ms.map Prod.fst) ef.rule.tmpl

/-- One computable work-queue step. -/
def cWorkQueueStep (s : List Atom) : Option (List Atom) :=
  match selectNextExec (cExecFacts s) with
  | none => none
  | some ef => some (cFireExecFact s ef)

/-- Fuel-bounded computable work-queue execution. -/
def cWorkQueueRunN : ℕ → List Atom → List Atom × ℕ
  | 0, s => (s, 0)
  | fuel + 1, s =>
    match cWorkQueueStep s with
    | none => (s, 0)
    | some s' =>
      let (final, n) := cWorkQueueRunN fuel s'
      (final, n + 1)

/-- Computable: extract all source-exec-facts from a list space. -/
def cSourceExecFacts (s : List Atom) : List SourceExecFact :=
  s.filterMap extractSourceExecFact

/-- Computable strict candidate set: only fully supported source/sink
directives. -/
def cSupportedSourceExecFacts (s : List Atom) : List SourceExecFact :=
  s.filterMap extractSupportedSourceExecFact

/-- Computable raw candidate set: every four-field `exec` shell. -/
def cRawExecFacts (s : List Atom) : List RawExecFact :=
  s.filterMap extractRawExecFact

/-- Computable: fire a source-exec-fact against the read copy. -/
def cFireSourceExecFact (s : List Atom) (sef : SourceExecFact) : List Atom :=
  let live := s.erase sef.atom
  let rc := sef.atom :: live
  let ms := cmatchInputSpec [] rc sef.rule.input
  cApplyMorkTemplate live (ms.map Prod.fst) sef.rule.tmpl

/-- Computable source-aware queue step for either unsupported-directive
policy. -/
def cSourceWorkQueueStep (policy : UnsupportedExecPolicy)
    (space : List Atom) : Option (List Atom) :=
  match policy with
  | .leaveInert =>
      match selectNextScheduled (cSupportedSourceExecFacts space) with
      | none => none
      | some directive => some (cFireSourceExecFact space directive)
  | .consume =>
      match selectNextScheduled (cRawExecFacts space) with
      | none => none
      | some raw =>
          match decodeSupportedSourceExec raw with
          | some directive => some (cFireSourceExecFact space directive)
          | none => some (space.erase raw.atom)

/-- Exact-fuel computable source-aware execution. -/
def cSourceWorkQueueRunN (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom × Nat
  | 0, space => (space, 0)
  | fuel + 1, space =>
      match cSourceWorkQueueStep policy space with
      | none => (space, 0)
      | some next =>
          let (final, used) := cSourceWorkQueueRunN policy fuel next
          (final, used + 1)

end WQComputable

/-! ## Scheduler correspondence

The computable `cWorkQueueStep` and the spec-level `workQueueStep` compute
the same result (up to `toFinset`) when exec-fact extraction produces the
same elements.  The key invariant: `selectNextExec` picks the minimum by
`lexLt`, which is permutation-invariant. -/

section SchedulerCorrespondence

open WQComputable

/-- Key injectivity: no two distinct scheduled values share a scheduler key. -/
def KeyInjective {α : Type} [SchedulerKey α] (l : List α) : Prop :=
  ∀ a b, a ∈ l → b ∈ l → SchedulerKey.key a = SchedulerKey.key b → a = b

/-- The generic fold step used by `selectNextScheduled`. -/
private def sneFold {α : Type} [SchedulerKey α]
    (best : Option α) (candidate : α) : Option α :=
  match best with
  | none => some candidate
  | some current =>
      if lexLt (SchedulerKey.key candidate) (SchedulerKey.key current)
      then some candidate else some current

@[simp] private theorem sneFold_none {α : Type} [SchedulerKey α]
    (candidate : α) : sneFold none candidate = some candidate := rfl
@[simp] private theorem sneFold_some {α : Type} [SchedulerKey α]
    (current candidate : α) :
    sneFold (some current) candidate =
      if lexLt (SchedulerKey.key candidate) (SchedulerKey.key current)
      then some candidate else some current := rfl

/-- Helper: the foldl step picks the minimum by lexLt. Two adjacent elements
    can be swapped without changing the result, provided distinct keys.

    This is the key commutativity lemma for permutation invariance of `selectNextExec`. -/
private theorem sneFold_comm {α : Type} [SchedulerKey α] (x y : α)
    (hdist : SchedulerKey.key x ≠ SchedulerKey.key y ∨ x = y)
    (init : Option α) :
    sneFold (sneFold init x) y = sneFold (sneFold init y) x := by
  cases init with
  | none =>
    dsimp only [sneFold]
    cases hyx : lexLt (SchedulerKey.key y) (SchedulerKey.key x) <;>
    cases hxy : lexLt (SchedulerKey.key x) (SchedulerKey.key y) <;>
    simp_all
    · exact hdist.elim (absurd (lexLt_eq_of_not_both _ _ hxy hyx)) id
    · exact absurd (lexLt_asymm _ _ hyx) (by simp [hxy])
  | some b =>
    dsimp only [sneFold]
    cases hxb : lexLt (SchedulerKey.key x) (SchedulerKey.key b) <;>
    cases hyb : lexLt (SchedulerKey.key y) (SchedulerKey.key b) <;>
    cases hyx : lexLt (SchedulerKey.key y) (SchedulerKey.key x) <;>
    cases hxy : lexLt (SchedulerKey.key x) (SchedulerKey.key y) <;>
    simp_all <;>
    first
    | (rw [lexLt_asymm _ _ hxy] at hyx; exact Bool.noConfusion hyx)
    | (rw [lexLt_trans _ _ _ hxy hyb] at hxb; exact Bool.noConfusion hxb)
    | (rw [lexLt_trans _ _ _ hyx hxb] at hyb; exact Bool.noConfusion hyb)
    | (exact hdist.elim (absurd (lexLt_eq_of_not_both _ _ hxy hyx)) id)

/-- Helper: foldl with `sneFold` is permutation-invariant under key injectivity. -/
private theorem selectNextScheduled_foldl_perm_aux {α : Type} [SchedulerKey α]
    (l₁ l₂ : List α) (hp : l₁.Perm l₂)
    (hinj : KeyInjective l₁)
    (init : Option α) :
    l₁.foldl sneFold init = l₂.foldl sneFold init := by
  induction hp generalizing init with
  | nil => rfl
  | cons x _ ih =>
    simp only [List.foldl]
    apply ih
    intro a b ha hb
    exact hinj a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)
  | swap x y l =>
    simp only [List.foldl]
    have hdist : SchedulerKey.key x ≠ SchedulerKey.key y ∨ x = y := by
      by_cases h : SchedulerKey.key x = SchedulerKey.key y
      · right
        exact hinj x y (by simp) (by simp) h
      · left; exact h
    rw [sneFold_comm x y hdist init]
  | trans hp1 hp2 ih1 ih2 =>
    rename_i la lb lc
    have hinj_mid : KeyInjective lb := by
      intro a b ha hb
      exact hinj a b (hp1.mem_iff.mpr ha) (hp1.mem_iff.mpr hb)
    exact (ih1 hinj init).trans (ih2 hinj_mid init)

/-- Generic least-key selection is permutation-invariant under key
injectivity. -/
theorem selectNextScheduled_perm {α : Type} [SchedulerKey α]
    (l₁ l₂ : List α) (hp : l₁.Perm l₂)
    (hinj : KeyInjective l₁) :
    selectNextScheduled l₁ = selectNextScheduled l₂ := by
  unfold selectNextScheduled
  exact selectNextScheduled_foldl_perm_aux l₁ l₂ hp hinj none

/-- Compatibility wrapper for exec-fact selection. -/
theorem selectNextExec_perm (l₁ l₂ : List ExecFact) (hp : l₁.Perm l₂)
    (hinj : KeyInjective l₁) :
    selectNextExec l₁ = selectNextExec l₂ := by
  exact selectNextScheduled_perm l₁ l₂ hp hinj

/-- Filtering a duplicate-free list presentation and filtering the canonical
finite-support presentation produce the same candidates up to permutation. -/
theorem filterMap_toFinset_perm (s : List Atom) (hnd : s.Nodup)
    (decode : Atom → Option α) :
    (s.filterMap decode).Perm (s.toFinset.toList.filterMap decode) := by
  exact (List.toFinset_toList hnd).filterMap decode |>.symm

/-- Under `Nodup`, the computable exec-fact list is a permutation of the
    spec-level exec-fact list.  This bridges `cExecFacts s` (computable) with
    `execFactsOfSpace s.toFinset` (noncomputable, uses `Finset.toList`). -/
theorem cExecFacts_perm_execFacts (s : List Atom) (hnd : s.Nodup) :
    (cExecFacts s).Perm (execFactsOfSpace s.toFinset) := by
  exact filterMap_toFinset_perm s hnd extractExecFact

/-- Strictly supported source candidates agree up to presentation order. -/
theorem cSupportedSourceExecFacts_perm (s : List Atom) (hnd : s.Nodup) :
    (cSupportedSourceExecFacts s).Perm
      (supportedSourceExecFactsOfSpace s.toFinset) := by
  exact filterMap_toFinset_perm s hnd extractSupportedSourceExecFact

/-- Raw scheduler-visible exec shells agree up to presentation order. -/
theorem cRawExecFacts_perm (s : List Atom) (hnd : s.Nodup) :
    (cRawExecFacts s).Perm (rawExecFactsOfSpace s.toFinset) := by
  exact filterMap_toFinset_perm s hnd extractRawExecFact

/-- The computable scheduler selects the same exec fact as the spec-level
    scheduler, provided the input space has no duplicates and all exec facts
    have distinct scheduler keys. -/
theorem cWorkQueueStep_selectExec_eq (s : List Atom) (hnd : s.Nodup)
    (hinj : KeyInjective (cExecFacts s)) :
    selectNextExec (cExecFacts s) = selectNextExec (execFactsOfSpace s.toFinset) := by
  exact selectNextExec_perm _ _ (cExecFacts_perm_execFacts s hnd) hinj

/-- The native list scheduler and support-level scheduler select the same
strictly supported source directive. -/
theorem cSourceWorkQueueStep_selectSupported_eq (s : List Atom) (hnd : s.Nodup)
    (hinj : KeyInjective (cSupportedSourceExecFacts s)) :
    selectNextScheduled (cSupportedSourceExecFacts s) =
      selectNextScheduled (supportedSourceExecFactsOfSpace s.toFinset) := by
  exact selectNextScheduled_perm _ _ (cSupportedSourceExecFacts_perm s hnd) hinj

/-- The native list scheduler and support-level scheduler select the same raw
exec shell under the consuming policy. -/
theorem cSourceWorkQueueStep_selectRaw_eq (s : List Atom) (hnd : s.Nodup)
    (hinj : KeyInjective (cRawExecFacts s)) :
    selectNextScheduled (cRawExecFacts s) =
      selectNextScheduled (rawExecFactsOfSpace s.toFinset) := by
  exact selectNextScheduled_perm _ _ (cRawExecFacts_perm s hnd) hinj

/-- `extractExecFact` preserves the original atom in the `.atom` field. -/
theorem extractExecFact_atom (a : Atom) (ef : ExecFact)
    (h : extractExecFact a = some ef) : ef.atom = a := by
  unfold extractExecFact at h
  split at h
  · simp at h; exact congr_arg ExecFact.atom h.symm
  · simp at h

/-- Two atoms extracting to the same ExecFact must be identical. -/
theorem extractExecFact_injective (a₁ a₂ : Atom) (ef : ExecFact)
    (h1 : extractExecFact a₁ = some ef) (h2 : extractExecFact a₂ = some ef) :
    a₁ = a₂ :=
  (extractExecFact_atom a₁ ef h1).symm.trans (extractExecFact_atom a₂ ef h2)

/-! ## Batched support-provider correspondence -/

/-- `insertSupport` realizes finite-set insertion. -/
theorem insertSupport_toFinset (space : List Atom) (atom : Atom) :
    (insertSupport space atom).toFinset = insert atom space.toFinset := by
  unfold insertSupport
  split_ifs with present
  · ext candidate
    simp only [List.mem_toFinset, Finset.mem_insert]
    constructor
    · exact Or.inr
    · intro membership
      rcases membership with rfl | membership
      · exact present
      · exact membership
  · rw [List.toFinset_append]
    ext candidate
    simp

/-- Computable support union realizes finite-set union. -/
theorem cUnionSupport_toFinset (space staged : List Atom) :
    (cUnionSupport space staged).toFinset =
      space.toFinset ∪ staged.toFinset := by
  induction staged generalizing space with
  | nil => simp [cUnionSupport]
  | cons atom rest induction =>
      simp only [cUnionSupport]
      rw [induction, insertSupport_toFinset]
      ext candidate
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
        List.mem_cons]
      aesop

/-- Computable support subtraction realizes finite-set difference. -/
theorem cSubtractSupport_toFinset (space staged : List Atom) :
    (cSubtractSupport space staged).toFinset =
      space.toFinset \ staged.toFinset := by
  ext candidate
  simp [cSubtractSupport]

/-- Each computable sink finalization realizes its provider-level
finalization. -/
theorem cFinalizeSupportSink_toFinset (sink : Sink) (staged space : List Atom) :
    (cFinalizeSupportSink sink staged space).toFinset =
      finalizeSupportSink sink staged space.toFinset := by
  cases sink with
  | add atom =>
      exact cUnionSupport_toFinset space staged
  | remove atom =>
      exact cSubtractSupport_toFinset space staged
  | head count atom =>
      simpa [cFinalizeSupportSink, finalizeSupportSink, compactExtrema] using
        cUnionSupport_toFinset space (compactExtremaList true count staged)
  | tail count atom =>
      simpa [cFinalizeSupportSink, finalizeSupportSink, compactExtrema] using
        cUnionSupport_toFinset space (compactExtremaList false count staged)

/-- The computable list implementation and mathematical batch provider agree
for any row sequence and sink sequence. -/
theorem cApplyMorkSinkBatch_toFinset (rows : List Subst)
    (space : List Atom) (sinks : List Sink) :
    (cApplyMorkSinkBatch rows space sinks).toFinset =
      morkSupportSinkProvider.run rows space.toFinset sinks := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      simp only [cApplyMorkSinkBatch, BatchSinkProvider.run_cons]
      rw [induction, cFinalizeSupportSink_toFinset]
      rfl

/-- Template-level form of batched support-provider adequacy. -/
theorem cApplyMorkTemplate_toFinset (space : List Atom) (rows : List Subst)
    (template : Template) :
    (cApplyMorkTemplate space rows template).toFinset =
      applyMorkSinkBatch space.toFinset rows template := by
  exact cApplyMorkSinkBatch_toFinset rows space template.sinks

/-! ## cConsumeExec / cReadCopy correspondence -/

/-- List erasure realizes finite-support erasure when the list presentation
contains no duplicate occurrences. -/
theorem listErase_toFinset (s : List Atom) (atom : Atom) (hnd : s.Nodup) :
    (s.erase atom).toFinset = s.toFinset.erase atom := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_erase]
  constructor
  · intro hx
    exact ⟨fun heq => absurd (heq ▸ hx) (List.Nodup.not_mem_erase hnd),
           List.mem_of_mem_erase hx⟩
  · intro ⟨hne, hx_mem⟩
    exact (List.mem_erase_of_ne hne).mpr hx_mem

/-- Consuming an exec fact in the list realization implements support
erasure. -/
theorem cConsumeExec_toFinset (s : List Atom) (ef : ExecFact) (hnd : s.Nodup) :
    (cConsumeExec s ef).toFinset = consumeExec s.toFinset ef := by
  exact listErase_toFinset s ef.atom hnd

/-- Computable read copy = spec read copy under Nodup. -/
theorem cReadCopy_toFinset (s : List Atom) (ef : ExecFact) (hnd : s.Nodup) :
    (cReadCopy s ef).toFinset = readCopy s.toFinset ef := by
  simp only [cReadCopy, readCopy]
  rw [List.toFinset_cons, cConsumeExec_toFinset s ef hnd]
  ext x; simp [Finset.mem_insert]

/-- The source-aware list read copy realizes the mathematical read copy. -/
theorem cReadCopyAtom_toFinset (s : List Atom) (atom : Atom) (hnd : s.Nodup) :
    (atom :: s.erase atom).toFinset = readCopyAtom s.toFinset atom := by
  simp only [readCopyAtom, consumeAtom, List.toFinset_cons]
  rw [listErase_toFinset s atom hnd]
  ext candidate
  simp [Finset.mem_insert]

/-! ## Batched firing correspondence -/

open Conformance.Computable (cmatchPattern cmatchInputSpec capplySinks)
open Conformance (NodupSafe FoldNodupSafe)

/-- Single-match correspondence: when the computable matcher returns exactly one
    result, `cFireExecFact` and `fireExecFact` agree at the `toFinset` level.

    The key precondition is that the spec-level matcher also returns exactly one
    result that corresponds to the computable result. This is ensured by
    `hmatch_spec_eq` which states the spec match result is the singleton list
    containing the `toFinset`-lifted computable result. -/
theorem cFireExecFact_toFinset_single (s : List Atom) (ef : ExecFact)
    (hnd : s.Nodup) (hm : ef.atom ∈ s)
    (σ : Subst) (consumed : List Atom)
    (hmatch_c : cmatchPattern [] (cReadCopy s ef) ef.rule.pat = [(σ, consumed)])
    (hmatch_spec_eq : matchPattern [] s.toFinset ef.rule.pat = [(σ, consumed.toFinset)]) :
    (cFireExecFact s ef).toFinset = fireExecFact s.toFinset ef := by
  simp only [cFireExecFact, fireExecFact]
  rw [hmatch_c]
  rw [readCopy_eq_of_mem s.toFinset ef (by rwa [List.mem_toFinset])]
  rw [hmatch_spec_eq, cApplyMorkTemplate_toFinset,
    cConsumeExec_toFinset s ef hnd]
  rfl

/-- No-match case: when the computable matcher returns no results,
    both `cFireExecFact` and `fireExecFact` reduce to consuming the exec fact. -/
theorem cFireExecFact_toFinset_empty (s : List Atom) (ef : ExecFact)
    (hnd : s.Nodup) (hm : ef.atom ∈ s)
    (hmatch_c : cmatchPattern [] (cReadCopy s ef) ef.rule.pat = [])
    (hmatch_spec_eq : matchPattern [] s.toFinset ef.rule.pat = []) :
    (cFireExecFact s ef).toFinset = fireExecFact s.toFinset ef := by
  simp only [cFireExecFact, fireExecFact]
  rw [hmatch_c]
  rw [readCopy_eq_of_mem s.toFinset ef (by rwa [List.mem_toFinset])]
  rw [hmatch_spec_eq, cApplyMorkTemplate_toFinset,
    cConsumeExec_toFinset s ef hnd]
  rfl

/-! ## General multi-match cFireExecFact correspondence

The general case lifts the single-match theorem to arbitrarily many match
results.  Because every sink stages into private support before finalization,
no row-by-row `NodupSafe` premise is needed. -/

/-- General multi-match `cFireExecFact` correspondence.  The only matcher
alignment required by the batch executor is equality of its substitution rows. -/
theorem cFireExecFact_toFinset (s : List Atom) (ef : ExecFact)
    (hnd : s.Nodup) (hm : ef.atom ∈ s)
    (hcorr : let cms := cmatchPattern [] (cReadCopy s ef) ef.rule.pat
             let sms := matchPattern [] s.toFinset ef.rule.pat
             cms.length = sms.length ∧
             ∀ (i : ℕ) (hi_c : i < cms.length) (hi_s : i < sms.length),
               cms[i].1 = sms[i].1) :
    (cFireExecFact s ef).toFinset = fireExecFact s.toFinset ef := by
  have rowEquality :
      (cmatchPattern [] (cReadCopy s ef) ef.rule.pat).map Prod.fst =
        (matchPattern [] s.toFinset ef.rule.pat).map Prod.fst := by
    apply List.ext_getElem
    · simpa using hcorr.1
    · intro index computableBound specificationBound
      simp only [List.getElem_map]
      exact hcorr.2 index (by simpa using computableBound)
        (by simpa using specificationBound)
  simp only [cFireExecFact, fireExecFact]
  rw [readCopy_eq_of_mem s.toFinset ef (by rwa [List.mem_toFinset])]
  rw [cApplyMorkTemplate_toFinset, cConsumeExec_toFinset s ef hnd,
    rowEquality]

/-- Source-aware batched firing correspondence.  The matcher obligation is
stated on substitution rows because consumed-witness bookkeeping is not an
input to MM2 sink finalization. -/
theorem cFireSourceExecFact_toFinset (s : List Atom) (sef : SourceExecFact)
    (hnd : s.Nodup)
    (rowAlignment :
      (cmatchInputSpec [] (sef.atom :: s.erase sef.atom) sef.rule.input).map
          Prod.fst =
        (matchInputSpec [] (readCopyAtom s.toFinset sef.atom)
          sef.rule.input).map Prod.fst) :
    (cFireSourceExecFact s sef).toFinset =
      fireSourceExecFact s.toFinset sef := by
  simp only [cFireSourceExecFact, fireSourceExecFact]
  rw [cApplyMorkTemplate_toFinset]
  rw [listErase_toFinset s sef.atom hnd]
  rw [rowAlignment]
  rfl

/-! ## Work-queue step correspondence -/

/-- Work-queue step correspondence: if the per-firing invariants hold for the
    selected exec fact, the computable and spec work-queue steps agree. -/
theorem cWorkQueueStep_toFinset (s : List Atom) (hnd : s.Nodup)
    (hinj : KeyInjective (cExecFacts s))
    (hfire : ∀ ef, selectNextExec (cExecFacts s) = some ef →
      ef.atom ∈ s ∧
      (let cms := cmatchPattern [] (cReadCopy s ef) ef.rule.pat
       let sms := matchPattern [] s.toFinset ef.rule.pat
       cms.length = sms.length ∧
       ∀ (i : ℕ) (hi_c : i < cms.length) (hi_s : i < sms.length),
         cms[i].1 = sms[i].1)) :
    (cWorkQueueStep s).map List.toFinset = workQueueStep s.toFinset := by
  simp only [cWorkQueueStep, workQueueStep]
  rw [← cWorkQueueStep_selectExec_eq s hnd hinj]
  match h : selectNextExec (cExecFacts s) with
  | none => simp
  | some ef =>
    simp only [Option.map]
    obtain ⟨hm, hcorr⟩ := hfire ef h
    exact congrArg some (cFireExecFact_toFinset s ef hnd hm ⟨hcorr.1, hcorr.2⟩)

/-! ## Source-aware work-queue correspondence -/

/-- The exact matcher obligation needed by source-aware batched firing.  It
mentions only substitution rows: witness collections are observationally
irrelevant to the declared support-sink provider. -/
def SourceRowAlignment (s : List Atom) (sef : SourceExecFact) : Prop :=
  (cmatchInputSpec [] (sef.atom :: s.erase sef.atom) sef.rule.input).map
      Prod.fst =
    (matchInputSpec [] (readCopyAtom s.toFinset sef.atom)
      sef.rule.input).map Prod.fst

/-- One source-aware native list step refines the corresponding support-level
MM2 step for either unsupported-directive policy.  The two alignment premises
cover the distinct candidate domains without pretending that an unsupported
raw shell has source semantics. -/
theorem cSourceWorkQueueStep_toFinset
    (policy : UnsupportedExecPolicy) (s : List Atom) (hnd : s.Nodup)
    (supportedKeyInj : KeyInjective (cSupportedSourceExecFacts s))
    (rawKeyInj : KeyInjective (cRawExecFacts s))
    (supportedAlignment : ∀ sef,
      selectNextScheduled (cSupportedSourceExecFacts s) = some sef →
      SourceRowAlignment s sef)
    (rawAlignment : ∀ raw sef,
      selectNextScheduled (cRawExecFacts s) = some raw →
      decodeSupportedSourceExec raw = some sef →
      SourceRowAlignment s sef) :
    (cSourceWorkQueueStep policy s).map List.toFinset =
      sourceWorkQueueStep policy s.toFinset := by
  cases policy with
  | leaveInert =>
      simp only [cSourceWorkQueueStep, sourceWorkQueueStep]
      rw [← cSourceWorkQueueStep_selectSupported_eq s hnd supportedKeyInj]
      cases selected : selectNextScheduled (cSupportedSourceExecFacts s) with
      | none => rfl
      | some sef =>
          simp only [Option.map]
          exact congrArg some
            (cFireSourceExecFact_toFinset s sef hnd
              (supportedAlignment sef selected))
  | consume =>
      simp only [cSourceWorkQueueStep, sourceWorkQueueStep]
      rw [← cSourceWorkQueueStep_selectRaw_eq s hnd rawKeyInj]
      cases selected : selectNextScheduled (cRawExecFacts s) with
      | none => rfl
      | some raw =>
          cases decoded : decodeSupportedSourceExec raw with
          | none =>
              simp only [decoded, Option.map]
              exact congrArg some (listErase_toFinset s raw.atom hnd)
          | some sef =>
              simp only [decoded, Option.map]
              exact congrArg some
                (cFireSourceExecFact_toFinset s sef hnd
                  (rawAlignment raw sef selected decoded))

/-! ## Work-queue bounded-run correspondence -/

/-- Invariant for work-queue step correspondence.
    Bundles all per-step requirements: Nodup, KeyInjective, and firing alignment. -/
structure WorkQueueInvariant (s : List Atom) : Prop where
  nodup : s.Nodup
  keyInj : KeyInjective (cExecFacts s)
  fire : ∀ ef, selectNextExec (cExecFacts s) = some ef →
    ef.atom ∈ s ∧
    (let cms := cmatchPattern [] (cReadCopy s ef) ef.rule.pat
     let sms := matchPattern [] s.toFinset ef.rule.pat
     cms.length = sms.length ∧
     ∀ (i : ℕ) (hi_c : i < cms.length) (hi_s : i < sms.length),
       cms[i].1 = sms[i].1)

/-- The set of list-spaces reachable from `s₀` in at most `fuel` computable steps. -/
inductive CReachable : ℕ → List Atom → List Atom → Prop where
  | refl : CReachable fuel s s
  | step {fuel s s' s''} :
      cWorkQueueStep s = some s' → CReachable fuel s' s'' →
      CReachable (fuel + 1) s s''

/-- Bounded-run correspondence: if the `WorkQueueInvariant` holds at every
    reachable state, computable and spec schedulers produce corresponding results.

    This makes the invariant-maintenance burden explicit: the caller must show that
    every intermediate state satisfies `WorkQueueInvariant`.  For finite-state MORK
    programs (the common case), this can be verified by exhaustive enumeration. -/
theorem cWorkQueueRunN_toFinset (fuel : ℕ) (s : List Atom)
    (hinv : ∀ s', CReachable fuel s s' → WorkQueueInvariant s') :
    (cWorkQueueRunN fuel s).1.toFinset = (workQueueRunN fuel s.toFinset).1 ∧
    (cWorkQueueRunN fuel s).2 = (workQueueRunN fuel s.toFinset).2 := by
  induction fuel generalizing s with
  | zero => simp [cWorkQueueRunN, workQueueRunN]
  | succ fuel ih =>
    simp only [cWorkQueueRunN, workQueueRunN]
    have winv := hinv s .refl
    have hstep := cWorkQueueStep_toFinset s winv.nodup winv.keyInj winv.fire
    match hc : cWorkQueueStep s with
    | none =>
      simp only [hc] at hstep
      simp only [Option.map] at hstep ⊢
      rw [← hstep]; exact ⟨rfl, rfl⟩
    | some s' =>
      simp only [hc, Option.map] at hstep
      have hspec : workQueueStep s.toFinset = some s'.toFinset := by rw [← hstep]
      simp only [hspec]
      have hinv' : ∀ s'', CReachable fuel s' s'' → WorkQueueInvariant s'' :=
        fun s'' hreach => hinv s'' (.step hc hreach)
      obtain ⟨h1, h2⟩ := ih s' hinv'
      exact ⟨h1, congrArg (· + 1) h2⟩

/-! ## Source-aware bounded-run correspondence -/

/-- Per-state obligations for the source-aware native realization.  Keeping
supported and raw scheduler invariants separate is essential: the open-world
profile never assigns semantics to an unsupported raw shell. -/
structure SourceWorkQueueInvariant (s : List Atom) : Prop where
  nodup : s.Nodup
  supportedKeyInj : KeyInjective (cSupportedSourceExecFacts s)
  rawKeyInj : KeyInjective (cRawExecFacts s)
  supportedAlignment : ∀ sef,
    selectNextScheduled (cSupportedSourceExecFacts s) = some sef →
    SourceRowAlignment s sef
  rawAlignment : ∀ raw sef,
    selectNextScheduled (cRawExecFacts s) = some raw →
    decodeSupportedSourceExec raw = some sef →
    SourceRowAlignment s sef

/-- List states reachable by at most the stated number of source-aware
computable steps. -/
inductive CSourceReachable (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom → Prop where
  | refl : CSourceReachable policy fuel s s
  | step {fuel s s' s''} :
      cSourceWorkQueueStep policy s = some s' →
      CSourceReachable policy fuel s' s'' →
      CSourceReachable policy (fuel + 1) s s''

/-- Exact-fuel native/source-GSLT correspondence.  Invariant maintenance is
required at every reachable residual, so adequacy cannot silently assume that
generated atoms remain canonical or matcher-aligned. -/
theorem cSourceWorkQueueRunN_toFinset
    (policy : UnsupportedExecPolicy) (fuel : Nat) (s : List Atom)
    (invariant : ∀ s', CSourceReachable policy fuel s s' →
      SourceWorkQueueInvariant s') :
    (cSourceWorkQueueRunN policy fuel s).1.toFinset =
        (sourceWorkQueueRunN policy fuel s.toFinset).1 ∧
      (cSourceWorkQueueRunN policy fuel s).2 =
        (sourceWorkQueueRunN policy fuel s.toFinset).2 := by
  induction fuel generalizing s with
  | zero => simp [cSourceWorkQueueRunN, sourceWorkQueueRunN]
  | succ fuel induction =>
      simp only [cSourceWorkQueueRunN, sourceWorkQueueRunN]
      have current := invariant s .refl
      have stepAgreement := cSourceWorkQueueStep_toFinset policy s
        current.nodup current.supportedKeyInj current.rawKeyInj
        current.supportedAlignment current.rawAlignment
      cases nativeStep : cSourceWorkQueueStep policy s with
      | none =>
          simp only [nativeStep] at stepAgreement
          simp only [Option.map] at stepAgreement ⊢
          rw [← stepAgreement]
          exact ⟨rfl, rfl⟩
      | some next =>
          simp only [nativeStep, Option.map] at stepAgreement
          have semanticStep :
              sourceWorkQueueStep policy s.toFinset = some next.toFinset := by
            rw [← stepAgreement]
          simp only [semanticStep]
          have nextInvariant : ∀ residual,
              CSourceReachable policy fuel next residual →
              SourceWorkQueueInvariant residual :=
            fun residual reachable => invariant residual (.step nativeStep reachable)
          obtain ⟨termAgreement, countAgreement⟩ :=
            induction next nextInvariant
          exact ⟨termAgreement, congrArg (· + 1) countAgreement⟩

end SchedulerCorrespondence

/-! ## Conformance canaries

These test the work-queue scheduler against known MORK outputs.
All proofs are `rfl` (kernel-checked). -/

section Canaries

-- API typechecks
#check @extractExecFact
#check @selectNextExec
#check @workQueueStep
#check @workQueueRunN
#check @readCopy_mem_exec
#check @readCopy_eq_of_mem

open WQComputable

/-! ### Canary 1: exec fact extraction

An `(exec (0 process) (, (task $x)) (O (+ (done $x)) (- (task $x))))` atom
is correctly parsed into an `ExecFact`. -/

private def canary1_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "process"],
    .expression [.symbol ",", .expression [.symbol "task", .var "x"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "done", .var "x"]],
      .expression [.symbol "-", .expression [.symbol "task", .var "x"]]]]

/-- Exec fact extraction succeeds on a well-formed exec atom. -/
theorem canary1_extract_some :
    (extractExecFact canary1_exec).isSome = true := rfl

/-- Extracted rule has correct name. -/
theorem canary1_name :
    (extractExecFact canary1_exec).map (·.rule.name) = some "process" := rfl

/-- Extracted rule has correct priority. -/
theorem canary1_priority :
    (extractExecFact canary1_exec).map (·.rule.priority) = some 0 := rfl

/-- Non-exec atoms are not extracted. -/
theorem canary1_non_exec :
    extractExecFact (.expression [.symbol "task", .symbol "a"]) = none := rfl

/-! ### Canary 2: Single-step work-queue execution

Space: `(task a)` + the exec rule.
One work-queue step should consume the exec fact, match `(task a)`, and produce `(done a)`.

This tests the full pipeline: extraction → selection → read-copy → match → apply. -/

private def canary2_task : Atom := .expression [.symbol "task", .symbol "a"]

private def canary2_space : List Atom := [canary2_task, canary1_exec]

/-- The work-queue scheduler fires the exec rule and produces `(done a)`. -/
theorem canary2_one_step :
    cWorkQueueStep canary2_space =
      some [.expression [.symbol "done", .symbol "a"]] := rfl

/-! ### Canary 3: Read-copy self-matching

A self-respawning rule pattern-matches its own exec atom via the read copy.

```mm2
(exec (0 self)
  (, (exec (0 self) $ps $cs) (trigger))
  (O (+ (exec (0 self) $ps $cs))
     (+ (fired))
     (- (trigger))))
```

The rule matches itself because the exec atom is re-inserted into the read copy.
Without read-copy, the rule would never match (it was removed from live). -/

private def canary3_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "self"],
    .expression [.symbol ",",
      .expression [.symbol "exec",
        .expression [.symbol "0", .symbol "self"],
        .var "ps", .var "cs"],
      .expression [.symbol "trigger"]],
    .expression [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "exec",
          .expression [.symbol "0", .symbol "self"],
          .var "ps", .var "cs"]],
      .expression [.symbol "+", .expression [.symbol "fired"]],
      .expression [.symbol "-", .expression [.symbol "trigger"]]]]

private def canary3_space : List Atom :=
  [canary3_exec, .expression [.symbol "trigger"]]

/-- Read copy contains the exec atom after consumption.
    We extract the exec fact and verify the read copy has it. -/
theorem canary3_readcopy_has_exec :
    match cExecFacts canary3_space with
    | ef :: _ => (cReadCopy canary3_space ef).contains canary3_exec = true
    | [] => False := rfl

/-- The self-referential rule fires and produces `(fired)`, but the respawned exec
    is rejected by `isGroundAtom` because `$ps`/`$cs` substitute to atoms containing
    `.var` nodes. In MORK's byte representation, captured bytes are always ground.
    This is a known modeling gap: coreferential byte-capture is not faithfully
    represented by Lean's `Atom.var` constructor. -/
theorem canary3_coreferential_gap :
    cWorkQueueStep canary3_space =
      some [.expression [.symbol "fired"]] := rfl

/-! ### Canary 4: Priority ordering

Two exec rules at different priorities. The lower-priority rule fires first.
After consuming `(ready)`, the higher-priority rule fires but finds no match. -/

private def canary4_rule0 : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "first"],
    .expression [.symbol ",", .expression [.symbol "ready"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "result", .symbol "first"]],
      .expression [.symbol "-", .expression [.symbol "ready"]]]]

private def canary4_rule1 : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "1", .symbol "second"],
    .expression [.symbol ",", .expression [.symbol "ready"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "result", .symbol "second"]],
      .expression [.symbol "-", .expression [.symbol "ready"]]]]

private def canary4_space : List Atom :=
  [.expression [.symbol "ready"], canary4_rule1, canary4_rule0]

/-- Priority 0 fires first, producing `(result first)` and consuming `(ready)`. -/
theorem canary4_priority_step1 :
    cWorkQueueStep canary4_space =
      some [canary4_rule1,
            .expression [.symbol "result", .symbol "first"]] := rfl

/-- After both rules are consumed, only the first result remains.
    Priority 1 fired but found no match (ready already consumed). -/
theorem canary4_priority_full :
    cWorkQueueRunN 2 canary4_space =
      ([.expression [.symbol "result", .symbol "first"]], 2) := rfl

/-! ### Canary 5: Conjunctive match via work queue

An exec rule with a conjunctive pattern `(, (left $x) (right $y))` fires
against the read copy. Both data atoms are consumed; only the joined result
remains.  Tests full pipeline: extraction → scheduling → read-copy → match → apply. -/

private def canary5_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "join"],
    .expression [.symbol ",",
      .expression [.symbol "left", .var "x"],
      .expression [.symbol "right", .var "y"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "pair", .var "x", .var "y"]],
      .expression [.symbol "-", .expression [.symbol "left", .var "x"]],
      .expression [.symbol "-", .expression [.symbol "right", .var "y"]]]]

private def canary5_space : List Atom :=
  [canary5_exec,
   .expression [.symbol "left", .symbol "a"],
   .expression [.symbol "right", .symbol "b"]]

/-- Full pipeline: exec consumed, conjunctive match fires, result is `(pair a b)`. -/
theorem canary5_conjunctive_wq :
    cWorkQueueStep canary5_space =
      some [.expression [.symbol "pair", .symbol "a", .symbol "b"]] := rfl

/-- `cWorkQueueRunN` terminates after 1 step (no more exec facts). -/
theorem canary5_terminates :
    cWorkQueueRunN 10 canary5_space =
      ([.expression [.symbol "pair", .symbol "a", .symbol "b"]], 1) := rfl

/-! ### Canary 6: Read-copy enables self-matching

The read copy re-inserts the exec atom after consumption, making the consumed
list strictly shorter than the read copy. This is what enables the bootstrap
pattern: the rule can match itself through the read copy. -/

/-- Read copy re-inserts the exec atom: the first extracted exec fact's read copy
    contains the exec fact itself (checked via `List.contains`). -/
theorem canary3_readcopy_contains_exec :
    match cExecFacts canary3_space with
    | ef :: _ => (cReadCopy canary3_space ef).contains ef.atom = true
    | [] => True := rfl

/-! ### Canary 7: Exact full-directive ordering

The physical scheduler key is the complete compact encoding of the selected
`exec` atom.  Locations remain available as authored data, but do not replace
the remaining pattern and template bytes in the physical order. -/

/-- Extracted exec fact preserves the raw location term. -/
theorem canary1_loc :
    (extractExecFact canary1_exec).map (·.loc) =
      some (.expression [.symbol "0", .symbol "process"]) := rfl

/-- The complete compact key selects the first directive in the canary pair. -/
theorem canary4_full_directive_order :
    lexLt (totalMorkCompactKey canary4_rule0)
          (totalMorkCompactKey canary4_rule1) = true := by decide

/-! ### Canary 8: Ground self-respawn

A rule that matches `(trigger)`, removes it, adds `(fired)`, and re-adds itself
as a ground literal (no variables in the re-add sink). This models the ground
self-respawn pattern: the exec atom persists after firing.

Unlike canary 3 (coreferential self-matching via `$ps`/`$cs`), this rule uses
a fully ground `(+)` sink that literally re-adds the entire exec atom. The
exec atom is ground because the pattern only contains `(trigger)` (no variables
captured into the re-add sink).

```mm2
(exec (0 persist)
  (, (trigger))
  (O (+ (fired))
     (- (trigger))
     (+ (exec (0 persist) (, (trigger)) (O (+ (fired)) (- (trigger)) (+ ...))))))
```

We approximate with a simpler ground rule where the re-add is the full exec atom. -/

private def canary8_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "persist"],
    .expression [.symbol ",", .expression [.symbol "trigger"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "fired"]],
      .expression [.symbol "-", .expression [.symbol "trigger"]]]]

private def canary8_exec_with_respawn : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "persist"],
    .expression [.symbol ",", .expression [.symbol "trigger"]],
    .expression [.symbol "O",
      .expression [.symbol "+", .expression [.symbol "fired"]],
      .expression [.symbol "-", .expression [.symbol "trigger"]],
      .expression [.symbol "+", canary8_exec]]]

private def canary8_space : List Atom :=
  [canary8_exec_with_respawn, .expression [.symbol "trigger"]]

/-- Ground self-respawn: after one step, `(fired)` is added and the exec atom
    `canary8_exec` is re-added by the ground `(+)` sink.  The re-added exec lacks
    the respawn sink (it's `canary8_exec`, not `canary8_exec_with_respawn`), so this
    models a one-shot ground respawn. -/
theorem canary8_ground_self_respawn :
    cWorkQueueStep canary8_space =
      some [.expression [.symbol "fired"], canary8_exec] := rfl

/-- After a second step, the re-added `canary8_exec` fires but finds no `(trigger)`.
    No match → exec consumed with no replacement.  Only `(fired)` remains. -/
theorem canary8_second_step_no_match :
    cWorkQueueRunN 2 canary8_space =
      ([.expression [.symbol "fired"]], 2) := rfl

/-! ### Canary 9: Source-aware extraction

Verify that `extractSourceExecFact` correctly parses both compat-mode `(, ...)`
and explicit-mode `(I ...)` exec atoms. -/

/-- Compat-mode exec atom extracts with `InputSpec.compat`. -/
theorem canary9_compat_extraction :
    (extractSourceExecFact canary1_exec).isSome = true := rfl

/-- Compat-mode extraction produces a compat InputSpec. -/
theorem canary9_compat_input :
    (extractSourceExecFact canary1_exec).bind
      (fun sef => match sef.rule.input with
        | .compat _ => some true
        | .explicit _ => some false) = some true := rfl

/-- Explicit-mode `(I (BTM pat))` exec atom. -/
private def canary9_explicit_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "src-test"],
    .expression [.symbol "I",
      .expression [.symbol "BTM",
        .expression [.symbol "data", .var "x"]]],
    .expression [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "found", .var "x"]]]]

/-- Explicit-mode extracts successfully. -/
theorem canary9_explicit_extraction :
    (extractSourceExecFact canary9_explicit_exec).isSome = true := rfl

/-- Explicit-mode extraction produces an explicit InputSpec. -/
theorem canary9_explicit_input :
    (extractSourceExecFact canary9_explicit_exec).bind
      (fun sef => match sef.rule.input with
        | .compat _ => some false
        | .explicit _ => some true) = some true := rfl

/-! ### Canary 10: Source-aware firing via cFireSourceExecFact

Exercise the full source-aware firing pipeline: extract, match via
`cmatchInputSpec`, apply sinks. -/

/-- Fire the explicit-source rule against a space with `(data hello)`. -/
theorem canary10_source_fire :
    match extractSourceExecFact canary9_explicit_exec with
    | some sef =>
      cFireSourceExecFact
        [canary9_explicit_exec, .expression [.symbol "data", .symbol "hello"]]
        sef =
        [.expression [.symbol "data", .symbol "hello"],
         .expression [.symbol "found", .symbol "hello"]]
    | none => False := rfl

/-- Explicit `(I (BTM ...) (== ...))` exec atom with equality constraint. -/
private def canary10_eq_exec : Atom :=
  .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "eq-test"],
    .expression [.symbol "I",
      .expression [.symbol "BTM",
        .expression [.symbol "key", .var "k"]],
      .expression [.symbol "==",
        .expression [.symbol "val", .var "k"],
        .var "v"]],
    .expression [.symbol "O",
      .expression [.symbol "+",
        .expression [.symbol "pair", .var "k", .var "v"]],
      .expression [.symbol "-",
        .expression [.symbol "key", .var "k"]]]]

/-- `==` constraint: match `(key k)`, then lookup `(val $k)` in space.
    Space: `[(key a), (val a)]` → binds `k=a`, finds `(val a)`, binds `v=(val a)`.
    Result: `(pair a (val a))` added, `(key a)` removed. -/
theorem canary10_eq_fire :
    match extractSourceExecFact canary10_eq_exec with
    | some sef =>
      cFireSourceExecFact
        [canary10_eq_exec,
         .expression [.symbol "key", .symbol "a"],
         .expression [.symbol "val", .symbol "a"]]
        sef =
        [.expression [.symbol "val", .symbol "a"],
         .expression [.symbol "pair", .symbol "a",
           .expression [.symbol "val", .symbol "a"]]]
    | none => False := rfl

/-- `==` constraint with no match: `(val b)` not in space when `k=a`. -/
theorem canary10_eq_nomatch :
    match extractSourceExecFact canary10_eq_exec with
    | some sef =>
      cFireSourceExecFact
        [canary10_eq_exec,
         .expression [.symbol "key", .symbol "a"],
         .expression [.symbol "val", .symbol "b"]]
        sef =
        [.expression [.symbol "key", .symbol "a"],
         .expression [.symbol "val", .symbol "b"]]
    | none => False := rfl

/-! ### Canary 11: `!=` constraint through cFireSourceExecFact

Exercise `neqConstraint` through the source-aware firing pipeline. -/

/-- `!=` source exec fact (constructed directly to avoid kernel reduction of parser). -/
private def canary11_sef : SourceExecFact where
  atom := .expression [.symbol "exec",
    .expression [.symbol "0", .symbol "neq-wq"],
    .symbol "I-body", .symbol "O-body"]  -- placeholder atom
  loc  := .expression [.symbol "0", .symbol "neq-wq"]
  rule := ⟨0, "neq-wq",
    .explicit [
      .btm (.expression [.symbol "skip", .var "x"]),
      .neqConstraint (.expression [.symbol "data", .var "x"])
                     (.expression [.symbol "data", .var "y"])],
    [],
    mkTemplate [mkAdd (.expression [.symbol "found", .var "y"])]⟩

/-- `!=` through cFireSourceExecFact: skip `(data a)`, match remaining `(data b)`. -/
theorem canary11_neq_fire :
    cFireSourceExecFact
      [canary11_sef.atom,
       .expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"],
       .expression [.symbol "data", .symbol "b"]]
      canary11_sef =
      [.expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"],
       .expression [.symbol "data", .symbol "b"],
       .expression [.symbol "found", .symbol "b"]] := rfl

/-- `!=` with no remaining match: only `(data a)` exists, excluded. -/
theorem canary11_neq_nomatch :
    cFireSourceExecFact
      [canary11_sef.atom,
       .expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"]]
      canary11_sef =
      [.expression [.symbol "skip", .symbol "a"],
       .expression [.symbol "data", .symbol "a"]] := rfl

/-- Extraction roundtrip: `extractSourceExecFact` parses the `!=` source. -/
theorem canary11_extraction_parses :
    (extractSourceExecFact
      (.expression [.symbol "exec",
        .expression [.symbol "0", .symbol "neq-wq"],
        .expression [.symbol "I",
          .expression [.symbol "BTM",
            .expression [.symbol "skip", .var "x"]],
          .expression [.symbol "!=",
            .expression [.symbol "data", .var "x"],
            .expression [.symbol "data", .var "y"]]],
        .expression [.symbol "O",
          .expression [.symbol "+",
            .expression [.symbol "found", .var "y"]]]])).isSome = true := rfl

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
