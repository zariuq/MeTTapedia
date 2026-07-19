import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GrammarDerives

/-!
# Derived expression grammar: `MMDb → TypecodeInfo → LanguageDef`

The compiled mode (mode A) of Metamath expression hosting: the expression
grammar is a **function of the database value** — floats become leaf
productions, syntax axioms become productions with holes — so nothing
Metamath-specific is ever hand-authored into a grammar. The generic core
(`SigRow`/`sigRowsToLanguageDef`) is language-agnostic and is the curriculum
template; Metamath is instance #1.

Design pins (from the 2026-07-09 dual review):
* **String floor:** Metamath proof checking is defined on symbol strings; this
  derived grammar is a certified *enrichment* for typing/NTT work, never a
  soundness dependency. Unambiguity must not become a soundness assumption.
* **`TypecodeInfo` is an explicit parameter.** The provable-typecode pairing
  (e.g. `|-` bodies parse at `wff`) lives in `$j` comments in real databases —
  outside the spec, invisible to honest parsers. An untrusted scraper may
  *propose* a `TypecodeInfo`; checked properties validate it; trusted code
  never reads comments.
* **Loud well-formedness, no silent skips:** a would-be syntax axiom carrying
  `$e` hypotheses, a repeated variable in a conclusion (breaks tree↔string
  invertibility), `$d` on a syntax axiom, or an undeclared variable is a
  reported error, not a silently dropped row.
* **Syntax theorems (`$p` at a grammar typecode) do not extend the grammar**;
  they are surfaced as notes.
* **No frozen outputs:** this generator is meant to (re)run per database load;
  committing its output for a fixed database would be hand-encoding with
  provenance theater.
* **Certificates, not decisions:** grammar unambiguity is undecidable in
  general. The honest per-database statement is a constructed-parser
  determinism certificate (O5 follow-on) or per-string singleton-forest
  parse-certs (realized today by the CeTTa-side engine). Neither is claimed
  here; no hollow certificate type is defined.

Mode B (interpretive) is the runtime twin: the CeTTa engine consults the same
rows live (`syntax-rows`), authenticated against mm-lean4 on real files. The
consistency lemma `axiomRows_eq_interpreterRows` below is the v0 brick of the
A≡B equivalence target (Futamura-correctness); it grows real content when the
Lean `RelationEnv` twin lands.

Fixtures: `demo0Db` below is a **test fixture** transcribed from the real
`demo0.mm` (sha256 b68d7488bdbf…); the authenticated ingestion path today is
the CeTTa reader, and a verified Lean reader is the leg-3 direction.
-/

namespace Mettapedia.Languages.Metamath.ExprDerive

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Minimal typed database view (string tokens; interning is the
correspondence layer's business, not the grammar generator's) -/

inductive MMStmtKind where
  | ax   -- $a
  | thm  -- $p
deriving DecidableEq, Repr

structure MMFloat where
  label : String
  typecode : String
  var : String
deriving DecidableEq, Repr

structure MMAssertion where
  kind : MMStmtKind
  label : String
  typecode : String            -- head of the conclusion math string
  body : List String           -- conclusion minus its typecode
  essHyps : List (List String) := []
  dvPairs : List (String × String) := []
deriving DecidableEq, Repr

structure MMDb where
  /-- Declared `$c` tokens. Needed so an undeclared or unfloated token in a
  syntax-axiom body is a LOUD error, never a silent terminal (the worst
  silent-massage vector at scale: one missing `$f` in an ingested view would
  otherwise turn a variable into a phantom terminal, changing every dependent
  parse with zero errors). -/
  constants : List String
  /-- Declared `$v` tokens. -/
  vars : List String
  floats : List MMFloat
  assertions : List MMAssertion
deriving DecidableEq, Repr

/-- The explicit typecode parameter (never scraped from comments by trusted
code): which typecodes are provability judgments, and how their statement
bodies map to grammar typecodes. -/
structure TypecodeInfo where
  provable : List String
  pairing : List (String × String) := []
deriving DecidableEq, Repr

def MMDb.varTypecode? (db : MMDb) (tok : String) : Option String :=
  (db.floats.find? (fun f => f.var == tok)).map (·.typecode)

def MMDb.isVar (db : MMDb) (tok : String) : Bool :=
  (db.varTypecode? tok).isSome

/-- Syntax axioms: `$a` assertions whose typecode is not a provability
judgment. (`$p` at a grammar typecode is a syntax THEOREM — never a grammar
row; see notes.) -/
def MMDb.syntaxAxioms (db : MMDb) (info : TypecodeInfo) : List MMAssertion :=
  db.assertions.filter (fun a =>
    a.kind == .ax && !(info.provable.contains a.typecode))

/-! ## Generic core: typed signature rows → grammar (curriculum template) -/

/-- Signature-row items. Extension shape (pinned now, added only when a
binder-bearing instance drives it): holes grow a binding arity in the
Fiore–Plotkin–Turi second-order-signature sense — `hole (name) (binds :
List (String × String) := []) (sort)` — mapping onto the DSL's existing
`TermParam.abstractionNamed`. Consumers must not assume holes are first-order.
Grammar rows carry NO premises/side-conditions, ever: DV and freshness belong
to the proof language — side conditions on grammar rows are how unambiguity
quietly becomes a soundness assumption. -/
inductive SigItem where
  | terminal (tok : String)
  | hole (name : String) (sort : String)
deriving DecidableEq, Repr

structure SigRow where
  label : String
  sort : String
  items : List SigItem
deriving DecidableEq, Repr

def sigRowToGrammarRule (r : SigRow) : GrammarRule :=
  { label := r.label
    category := r.sort
    params := r.items.filterMap (fun
      | .hole n s => some (.simple n (.base s))
      | .terminal _ => none)
    syntaxPattern := r.items.map (fun
      | .terminal t => .terminal t
      | .hole n _ => .nonTerminal n) }

def sigRowsToLanguageDef (name : String) (sorts : List String)
    (rows : List SigRow) : LanguageDef :=
  { name := name
    types := sorts.map TypeDecl.plain
    terms := rows.map sigRowToGrammarRule
    equations := []
    rewrites := [] }

/-! ## Metamath instance -/

/-- A float `$f tc v` is a leaf production `tc → v`. Parse-tree leaves are
`$f` labels and nodes are `$a` labels — a parse tree IS a Metamath syntax
proof, which is what makes the derived grammar proof-relevant. -/
def floatRow (f : MMFloat) : SigRow :=
  { label := f.label, sort := f.typecode, items := [.terminal f.var] }

def axiomRow (db : MMDb) (a : MMAssertion) : SigRow :=
  { label := a.label
    sort := a.typecode
    items := a.body.map (fun tok =>
      match db.varTypecode? tok with
      | some tc => .hole tok tc
      | none => .terminal tok) }

def mmSigRows (db : MMDb) (info : TypecodeInfo) : List SigRow :=
  db.floats.map floatRow ++ (db.syntaxAxioms info).map (axiomRow db)

def MMDb.grammarTypecodes (db : MMDb) (info : TypecodeInfo) : List String :=
  ((db.floats.map (·.typecode)) ++ (db.syntaxAxioms info).map (·.typecode)).eraseDups

def mmExprLanguageDef (db : MMDb) (info : TypecodeInfo) : LanguageDef :=
  sigRowsToLanguageDef "MMExpr" (db.grammarTypecodes info) (mmSigRows db info)

/-! ## Loud well-formedness (errors) and exclusions (notes) -/

def countOccurrences (tok : String) (body : List String) : Nat :=
  (body.filter (· == tok)).length

/-- Declaration integrity: the flat view is well-posed only when every
grammar-relevant float is unique per variable and every token in a
syntax-axiom body is accounted for. A declared variable without a `$f`, or an
undeclared token, must be an ERROR — the alternative is `axiomRow` silently
classifying it as a terminal, which changes parse meaning with no report. -/
def declarationErrors (db : MMDb) (info : TypecodeInfo) : List String :=
  (db.floats.filterMap (fun f =>
    if (db.floats.filter (fun g => g.var == f.var)).length != 1 then
      some s!"multiple $f for variable {f.var}"
    else none)).eraseDups ++
  db.floats.filterMap (fun f =>
    if !(db.vars.contains f.var) then
      some s!"$f {f.label} types undeclared variable {f.var}"
    else none) ++
  db.floats.filterMap (fun f =>
    if info.provable.contains f.typecode then
      some s!"$f {f.label} sits at provable typecode {f.typecode}"
    else none) ++
  ((db.syntaxAxioms info).flatMap (fun a =>
    a.body.filterMap (fun tok =>
      if db.vars.contains tok && !(db.isVar tok) then
        some s!"variable {tok} in {a.label} has no active $f"
      else if !(db.vars.contains tok) && !(db.constants.contains tok) then
        some s!"undeclared token {tok} in {a.label}"
      else none))).eraseDups

/-- CFG hygiene on the derived rows. ε-productions (`$a wff $.` with empty
body) are legal Metamath but unsupported by this v0 generator — fail-closed
domain gate, policy pinned here. Duplicate production shapes at one sort are
trivial per-string ambiguity. (Unit-production cycle detection is the named
next item in this suite.) -/
def grammarHygieneErrors (db : MMDb) (info : TypecodeInfo) : List String :=
  (db.syntaxAxioms info).filterMap (fun a =>
    if a.body.isEmpty then
      some s!"epsilon production {a.label} (empty body): unsupported in v0"
    else none) ++
  (let rows := mmSigRows db info
   (rows.filterMap (fun r =>
     if (rows.filter (fun r' => r'.sort == r.sort && r'.items == r.items)).length != 1 then
       some s!"duplicate production shape at {r.sort} (label {r.label})"
     else none)).eraseDups)

def syntaxAxiomErrors (db : MMDb) (info : TypecodeInfo) : List String :=
  (db.syntaxAxioms info).flatMap (fun a =>
    (if a.essHyps.isEmpty then [] else
      [s!"syntax axiom {a.label} carries $e hypotheses"]) ++
    (if a.dvPairs.isEmpty then [] else
      [s!"syntax axiom {a.label} carries $d conditions"]) ++
    (a.body.filterMap (fun tok =>
      if db.isVar tok && countOccurrences tok a.body != 1 then
        some s!"variable {tok} occurs {countOccurrences tok a.body} times in syntax axiom {a.label}"
      else none)).eraseDups)

def pairingErrors (db : MMDb) (info : TypecodeInfo) : List String :=
  info.pairing.filterMap (fun (p, g) =>
    if !(info.provable.contains p) then
      some s!"pairing maps non-provable typecode {p}"
    else if !(db.grammarTypecodes info).contains g then
      some s!"pairing targets unknown grammar typecode {g}"
    else none) ++
  (info.pairing.filterMap (fun (p, _) =>
    if (info.pairing.filter (fun q => q.1 == p)).length != 1 then
      some s!"pairing is not functional at {p}"
    else none)).eraseDups

def wellFormedErrors (db : MMDb) (info : TypecodeInfo) : List String :=
  declarationErrors db info ++ syntaxAxiomErrors db info ++
    pairingErrors db info ++ grammarHygieneErrors db info

/-- Excluded-by-design rows, surfaced (never silent): syntax theorems. -/
def exclusionNotes (db : MMDb) (info : TypecodeInfo) : List String :=
  db.assertions.filterMap (fun a =>
    if a.kind == .thm && !(info.provable.contains a.typecode) then
      some s!"syntax theorem {a.label} (typecode {a.typecode}) does not extend the grammar"
    else none)

/-! ## Mode A ≡ mode B, v0 brick

The interpretive mode (CeTTa `syntax-rows`) consults, at parse time, exactly
the assertion rows with the queried conclusion typecode. `interpreterRows`
mirrors that selection; the lemma pins that the compiled generator's
axiom-row image is the same selection, uniformly. (Float/variable handling
corresponds to the interpreter's `var-forest`/`db-isvar` path — recorded here,
formalized when the Lean RelationEnv twin lands.) -/

def interpreterRows (db : MMDb) (info : TypecodeInfo) (tc : String) :
    List SigRow :=
  ((db.syntaxAxioms info).filter (fun a => a.typecode == tc)).map (axiomRow db)

theorem axiomRows_eq_interpreterRows (db : MMDb) (info : TypecodeInfo)
    (tc : String) :
    ((db.syntaxAxioms info).map (axiomRow db)).filter (fun r => r.sort == tc)
      = interpreterRows db info tc := by
  unfold interpreterRows
  induction db.syntaxAxioms info with
  | nil => rfl
  | cons a rest ih =>
      by_cases h : a.typecode == tc
      · simp [axiomRow, List.filter, List.map, h, ih]
      · simp [axiomRow, List.filter, List.map, h, ih]

/-! ## Extension functoriality (the meta-GSLT direction, mode A side)

"Appending statements only appends rows" is FALSE without a freshness
hypothesis: a new `$f` whose variable token occurs in an OLD syntax-axiom
body would retroactively re-classify that token (terminal → hole), silently
mutating the old row. Real Metamath forbids this via declaration/activeness
rules; the flat view carries the prohibition explicitly as `FreshFloats`,
discharged by construction from a legal database (the outer→expr
extraction's job). Given it, old rows survive extension verbatim — the lax
(forward-only) functorial action, and the parse-stability input. -/

structure MMDbExt where
  constants : List String := []
  vars : List String := []
  floats : List MMFloat := []
  assertions : List MMAssertion := []

def MMDb.extend (db : MMDb) (Δ : MMDbExt) : MMDb :=
  { constants := db.constants ++ Δ.constants
    vars := db.vars ++ Δ.vars
    floats := db.floats ++ Δ.floats
    assertions := db.assertions ++ Δ.assertions }

/-- No new float re-classifies a token that an old syntax axiom uses. -/
def FreshFloats (db : MMDb) (info : TypecodeInfo) (Δ : MMDbExt) : Prop :=
  ∀ f ∈ Δ.floats, ∀ a ∈ db.syntaxAxioms info, !(a.body.contains f.var)

theorem floatRows_extend (db : MMDb) (Δ : MMDbExt) :
    (db.extend Δ).floats.map floatRow
      = db.floats.map floatRow ++ Δ.floats.map floatRow := by
  simp [MMDb.extend]

theorem varTypecode?_extend_stable (db : MMDb) (Δ : MMDbExt) (tok : String)
    (h : ∀ f ∈ Δ.floats, f.var ≠ tok) :
    (db.extend Δ).varTypecode? tok = db.varTypecode? tok := by
  unfold MMDb.varTypecode? MMDb.extend
  induction db.floats with
  | nil =>
      have hnone : Δ.floats.find? (fun f => f.var == tok) = none := by
        apply List.find?_eq_none.mpr
        intro f hf
        simpa using h f hf
      simp [hnone]
  | cons f fs ih =>
      by_cases hfv : f.var == tok
      · simp [hfv]
      · simpa [List.find?_cons, hfv] using ih

theorem axiomRow_extend_stable (db : MMDb) (Δ : MMDbExt) (a : MMAssertion)
    (h : ∀ f ∈ Δ.floats, !(a.body.contains f.var)) :
    axiomRow (db.extend Δ) a = axiomRow db a := by
  unfold axiomRow
  simp only [SigRow.mk.injEq, true_and]
  apply List.map_congr_left
  intro tok htok
  have hstable : (db.extend Δ).varTypecode? tok = db.varTypecode? tok := by
    apply varTypecode?_extend_stable
    intro f hf heq
    have := h f hf
    rw [heq] at this
    simp at this
    exact this htok
  rw [hstable]

/-- Old syntax axioms remain syntax axioms of the extension (filter over an
appended list keeps the left part). -/
theorem syntaxAxioms_extend_mem (db : MMDb) (Δ : MMDbExt)
    (info : TypecodeInfo) (a : MMAssertion)
    (ha : a ∈ db.syntaxAxioms info) :
    a ∈ (db.extend Δ).syntaxAxioms info := by
  unfold MMDb.syntaxAxioms MMDb.extend at *
  simp only [List.mem_filter, List.mem_append] at *
  exact ⟨Or.inl ha.1, ha.2⟩

/-- THE lax functorial action: under freshness, every derived row of the base
database is a derived row of the extension, verbatim. (Old parse trees
survive extension unchanged; unambiguity, being antitone, does not — that is
the certificate's business, not this lemma's.) -/
theorem mmSigRows_extend_mem (db : MMDb) (Δ : MMDbExt) (info : TypecodeInfo)
    (hfresh : FreshFloats db info Δ)
    (r : SigRow) (hr : r ∈ mmSigRows db info) :
    r ∈ mmSigRows (db.extend Δ) info := by
  unfold mmSigRows at *
  rw [List.mem_append] at hr
  cases hr with
  | inl hfloat =>
      apply List.mem_append_left
      rw [floatRows_extend]
      exact List.mem_append_left _ hfloat
  | inr hax =>
      apply List.mem_append_right
      rw [List.mem_map] at hax
      obtain ⟨a, ha, rfl⟩ := hax
      rw [List.mem_map]
      refine ⟨a, syntaxAxioms_extend_mem db Δ info a ha, ?_⟩
      exact axiomRow_extend_stable db Δ a (fun f hf => hfresh f hf a ha)

/-! ## demo0 instance (test fixture; real ingestion is the CeTTa reader,
authenticated vs mm-lean4 on the actual file, sha256 b68d7488bdbf…) -/

def demo0Db : MMDb :=
  { constants := ["0", "+", "=", "->", "(", ")", "term", "wff", "|-"]
    vars := ["t", "r", "s", "P", "Q"]
    floats :=
      [ ⟨"tt", "term", "t"⟩, ⟨"tr", "term", "r"⟩, ⟨"ts", "term", "s"⟩
      , ⟨"wp", "wff", "P"⟩, ⟨"wq", "wff", "Q"⟩ ]
    assertions :=
      [ ⟨.ax, "tze", "term", ["0"], [], []⟩
      , ⟨.ax, "tpl", "term", ["(", "t", "+", "r", ")"], [], []⟩
      , ⟨.ax, "weq", "wff", ["t", "=", "r"], [], []⟩
      , ⟨.ax, "wim", "wff", ["(", "P", "->", "Q", ")"], [], []⟩
      , ⟨.ax, "a1", "|-", ["(", "t", "=", "r", "->", "(", "t", "=", "s", "->", "r", "=", "s", ")", ")"], [], []⟩
      , ⟨.ax, "a2", "|-", ["(", "t", "+", "0", ")", "=", "t"], [], []⟩
      , ⟨.ax, "mp", "|-", ["Q"], [["|-", "P"], ["|-", "(", "P", "->", "Q", ")"]], []⟩
      , ⟨.thm, "th1", "|-", ["t", "=", "t"], [], []⟩ ] }

def demo0Tc : TypecodeInfo := { provable := ["|-"], pairing := [("|-", "wff")] }

-- well-posed: no errors, no surprise exclusions
#guard wellFormedErrors demo0Db demo0Tc == []
#guard exclusionNotes demo0Db demo0Tc == []

-- the derived rows: five float leaves + the four syntax axioms, nothing else
#guard (mmSigRows demo0Db demo0Tc).map (·.label)
    == ["tt", "tr", "ts", "wp", "wq", "tze", "tpl", "weq", "wim"]
#guard (demo0Db.grammarTypecodes demo0Tc) == ["term", "wff"]

-- provable-judgment rows (a1/a2/mp/th1) are NOT grammar rows
#guard !((mmSigRows demo0Db demo0Tc).any (fun r => r.label == "a1" || r.label == "mp"))

-- a generated rule, concretely: weq = [hole t:term, "=", hole r:term] at wff
#guard (mmSigRows demo0Db demo0Tc).any (fun r =>
    r.label == "weq" && r.sort == "wff" &&
    r.items == [.hole "t" "term", .terminal "=", .hole "r" "term"])

-- the derived languageDef validates and its grammar has 9 rules over 2 sorts
#guard (LanguageDef.validate (mmExprLanguageDef demo0Db demo0Tc)).isEmpty
#guard (mmExprLanguageDef demo0Db demo0Tc).terms.length == 9

-- negative fixtures: a corrupt database is REJECTED loudly, not massaged.
-- (1) repeated variable in a syntax axiom breaks tree↔string invertibility
def badDbRepeatedVar : MMDb :=
  { demo0Db with assertions :=
      ⟨.ax, "wbad", "wff", ["t", "=", "t"], [], []⟩ :: demo0Db.assertions }
#guard wellFormedErrors badDbRepeatedVar demo0Tc ≠ []

-- (2) a declared variable WITHOUT an active $f in a syntax-axiom body would
-- silently become a phantom terminal — must be an error
def badDbUnfloatedVar : MMDb :=
  { demo0Db with
    vars := "x" :: demo0Db.vars
    assertions :=
      ⟨.ax, "wux", "wff", ["x", "=", "x"], [], []⟩ :: demo0Db.assertions }
#guard (declarationErrors badDbUnfloatedVar demo0Tc).any
    (fun e => e.startsWith "variable x")

-- (3) an undeclared token in a syntax-axiom body is an error, not a terminal
def badDbUndeclared : MMDb :=
  { demo0Db with assertions :=
      ⟨.ax, "wtypo", "wff", ["t", "==", "r"], [], []⟩ :: demo0Db.assertions }
#guard (declarationErrors badDbUndeclared demo0Tc).any
    (fun e => e.startsWith "undeclared token ==")

-- (4) duplicate active $f for one variable destroys leaf invertibility
def badDbDupFloat : MMDb :=
  { demo0Db with floats := ⟨"tt2", "wff", "t"⟩ :: demo0Db.floats }
#guard (declarationErrors badDbDupFloat demo0Tc).any
    (fun e => e.startsWith "multiple $f")

-- (5) epsilon production: legal Metamath, fail-closed here (pinned policy)
def badDbEpsilon : MMDb :=
  { demo0Db with assertions :=
      ⟨.ax, "weps", "wff", [], [], []⟩ :: demo0Db.assertions }
#guard (grammarHygieneErrors badDbEpsilon demo0Tc).any
    (fun e => e.startsWith "epsilon production")

/-- The derived languageDef runs through the standard OSLF derivation — the
pipe fires on a computed grammar exactly as on an authored one.

HONESTY FLAG (modal vacuity): this languageDef has `rewrites := []`, so
`langReduces` is empty — here ◇φ is uniformly False and □φ uniformly True.
The OSLF content of a rewrite-free grammar definition lives in the
constructor category (sorts, crossings), NOT the modal layer; the modal layer
becomes contentful when the interpretive parse-state rows (mode B) land. Do
not cite this as "modal types derived for Metamath expressions." -/
def demo0ExprOSLF :
    OSLFTypeSystem (langRewriteSystem (mmExprLanguageDef demo0Db demo0Tc) "wff") :=
  langOSLF (mmExprLanguageDef demo0Db demo0Tc) "wff"

/-! ## Mode B: the interpretive relation environment (v1 of the A≡B ladder)

`dbRelationEnv` exposes the database as RAW facts — labels, typecodes, and
token lists — with NO hole/terminal classification baked in (classification
is the interpreter's parse-time business, mirroring the CeTTa engine's
`db-isvar`/`var-forest`; pre-classifying here would compile half of mode A
into mode B and hollow the equivalence out). Bodies ride as one compound
`Pattern` argument; the function-free `DatalogClause` fact encoding (per-token
positional facts in the `logic` field) is the stated follow-up, to be proven
equal to this environment.

`decodeRows` reconstructs signature rows FROM THE FACTS ALONE (variable
status looked up in the `mm-float` tuples, not in the database). The v1
adequacy theorem `decodeRows_dbRelationEnv` is then two independent
computations agreeing — the first non-definitional rung of the ladder. Next
rungs: step agreement (one compiled `GrammarRule` application ≡ one
interpretive parse step), then `Derives`-level agreement, then grounding of
`Derives`-trees into mm-lean4 acceptance. -/

section ModeB

open Mettapedia.OSLF.MeTTaIL.Engine

def tokPattern (s : String) : Pattern := .fvar s

def encFloat (f : MMFloat) : List Pattern :=
  [tokPattern f.label, tokPattern f.typecode, tokPattern f.var]

def encSynAx (a : MMAssertion) : List Pattern :=
  [tokPattern a.label, tokPattern a.typecode, .apply "mm-toks" (a.body.map tokPattern)]

/-- Raw-fact relation environment of a database (mode B's data). -/
def dbRelationEnv (db : MMDb) (info : TypecodeInfo) : RelationEnv where
  tuples rel _queryArgs :=
    if rel = "mm-float" then db.floats.map encFloat
    else if rel = "mm-syn-ax" then (db.syntaxAxioms info).map encSynAx
    else if rel = "mm-provable" then info.provable.map (fun tc => [tokPattern tc])
    else []

/-- Variable classification FROM THE FACTS (not from the database). -/
def envVarTypecode? (env : RelationEnv) (tok : String) : Option String :=
  (env.tuples "mm-float" []).findSome? (fun t =>
    match t with
    | [.fvar _, .fvar tc, .fvar v] => if v == tok then some tc else none
    | _ => none)

def decodeFloatRow? : List Pattern → Option SigRow
  | [.fvar l, .fvar tc, .fvar v] => some ⟨l, tc, [.terminal v]⟩
  | _ => none

def decodeItems (isVar : String → Option String) : List Pattern → Option (List SigItem)
  | [] => some []
  | .fvar s :: rest =>
      (decodeItems isVar rest).map (fun items =>
        (match isVar s with
         | some vtc => SigItem.hole s vtc
         | none => SigItem.terminal s) :: items)
  | _ => none

def decodeAxRow? (isVar : String → Option String) : List Pattern → Option SigRow
  | [.fvar l, .fvar tc, .apply "mm-toks" toks] =>
      (decodeItems isVar toks).map (fun items => ⟨l, tc, items⟩)
  | _ => none

/-- Rows reconstructed from the facts alone. -/
def decodeRows (env : RelationEnv) : List SigRow :=
  (env.tuples "mm-float" []).filterMap decodeFloatRow? ++
    (env.tuples "mm-syn-ax" []).filterMap (decodeAxRow? (envVarTypecode? env))

theorem envVarTypecode?_dbRelationEnv (db : MMDb) (info : TypecodeInfo)
    (tok : String) :
    envVarTypecode? (dbRelationEnv db info) tok = db.varTypecode? tok := by
  show (db.floats.map encFloat).findSome? (fun t =>
      match t with
      | [.fvar _, .fvar tc, .fvar v] => if v == tok then some tc else none
      | _ => none)
    = (db.floats.find? (fun f => f.var == tok)).map (·.typecode)
  induction db.floats with
  | nil => rfl
  | cons f fs ih =>
      by_cases hfv : f.var = tok
      · simp [encFloat, tokPattern, hfv]
      · simpa [List.findSome?_cons, List.find?_cons, encFloat, tokPattern, hfv]
          using ih

theorem decodeItems_body (db : MMDb) (info : TypecodeInfo)
    (body : List String) :
    decodeItems (envVarTypecode? (dbRelationEnv db info)) (body.map tokPattern)
      = some (body.map (fun tok =>
          match db.varTypecode? tok with
          | some tc => SigItem.hole tok tc
          | none => SigItem.terminal tok)) := by
  induction body with
  | nil => rfl
  | cons tok rest ih =>
      simp only [List.map_cons, decodeItems, tokPattern, ih, Option.map_some,
        envVarTypecode?_dbRelationEnv]

/-- v1 adequacy: the facts decode to exactly the compiled rows — two
independently defined computations agree. -/
theorem decodeRows_dbRelationEnv (db : MMDb) (info : TypecodeInfo) :
    decodeRows (dbRelationEnv db info) = mmSigRows db info := by
  unfold decodeRows mmSigRows
  congr 1
  · -- float leg
    show ((dbRelationEnv db info).tuples "mm-float" []).filterMap decodeFloatRow?
        = db.floats.map floatRow
    unfold dbRelationEnv
    induction db.floats with
    | nil => rfl
    | cons f fs _ =>
        simp only [List.map_cons]
        simp [encFloat, tokPattern, decodeFloatRow?, floatRow]
  · -- axiom leg
    show ((dbRelationEnv db info).tuples "mm-syn-ax" []).filterMap
          (decodeAxRow? (envVarTypecode? (dbRelationEnv db info)))
        = (db.syntaxAxioms info).map (axiomRow db)
    conv_lhs =>
      rw [show (dbRelationEnv db info).tuples "mm-syn-ax" []
            = (db.syntaxAxioms info).map encSynAx from rfl]
    induction db.syntaxAxioms info with
    | nil => rfl
    | cons a rest ih =>
        simp only [List.map_cons, List.filterMap_cons]
        rw [show decodeAxRow? (envVarTypecode? (dbRelationEnv db info)) (encSynAx a)
              = some (axiomRow db a) by
            unfold decodeAxRow? encSynAx
            simp [tokPattern, decodeItems_body db info a.body, axiomRow]]
        simp [ih]

-- executable confirmation on the fixture (theorem above is general)
#guard decodeRows (dbRelationEnv demo0Db demo0Tc) == mmSigRows demo0Db demo0Tc

end ModeB

/-! ## Derivability over the derived grammar

A `Derives`-tree over the generated rows IS a Metamath syntax proof: leaves
are `$f` labels, internal nodes are syntax-`$a` labels. (Mapping such trees
to mm-lean4 acceptance is the grounding leg of the correspondence ladder.)
The witness below is the first end-to-end use of the generic relation on a
COMPUTED grammar: `t = r` derives at `wff` with tree `weq(tt, tr)`. -/

section DerivesDemo

open Mettapedia.OSLF.Framework.GrammarDerives

private def ttRule : GrammarRule := sigRowToGrammarRule (floatRow ⟨"tt", "term", "t"⟩)
private def trRule : GrammarRule := sigRowToGrammarRule (floatRow ⟨"tr", "term", "r"⟩)
private def weqRule : GrammarRule :=
  sigRowToGrammarRule
    { label := "weq", sort := "wff"
      items := [.hole "t" "term", .terminal "=", .hole "r" "term"] }

example :
    Derives (mmExprLanguageDef demo0Db demo0Tc) "wff" ["t", "=", "r"]
      (.apply "weq" [.apply "tt" [], .apply "tr" []]) := by
  -- rule membership positionally, by computation (tt=row 0, tr=row 1, weq=row 7)
  have m0 : (mmExprLanguageDef demo0Db demo0Tc).terms[0]? = some ttRule := rfl
  have m1 : (mmExprLanguageDef demo0Db demo0Tc).terms[1]? = some trRule := rfl
  have m7 : (mmExprLanguageDef demo0Db demo0Tc).terms[7]? = some weqRule := rfl
  have htt : Derives (mmExprLanguageDef demo0Db demo0Tc) "term" ["t"]
      (.apply "tt" []) :=
    Derives.rule ttRule (List.mem_of_getElem? m0) _ rfl _ _
      (DerivesItems.terminal _ "t" [] [] [] (DerivesItems.nil _))
  have htr : Derives (mmExprLanguageDef demo0Db demo0Tc) "term" ["r"]
      (.apply "tr" []) :=
    Derives.rule trRule (List.mem_of_getElem? m1) _ rfl _ _
      (DerivesItems.terminal _ "r" [] [] [] (DerivesItems.nil _))
  exact Derives.rule weqRule (List.mem_of_getElem? m7) _ rfl _ _
    (DerivesItems.nonTerminal _ "t" "term" rfl ["t"] _ htt _ _ _
      (DerivesItems.terminal _ "=" _ _ _
        (DerivesItems.nonTerminal _ "r" "term" rfl ["r"] _ htr [] [] []
          (DerivesItems.nil _))))

end DerivesDemo

/-! ## Bounded-enumeration gates (generic `enumDerives` on the computed grammar)

Instance checks for the framework enumerator: per-string enumeration on the
derived demo0 grammar returns exactly the expected singleton forest (matching
the `Derives` witness above) or nothing for a non-string, the grammar is
consuming (floats are terminal leaves; ε-productions are rejected by the loud
well-formedness gate), and the certificate corollary fires end-to-end,
yielding unconditional per-string uniqueness. -/

section EnumGates

open Mettapedia.OSLF.Framework.GrammarDerives

-- `t = r` at wff enumerates to exactly the weq tree — the singleton forest
-- whose sole element is the `Derives` witness of the section above
#guard enumDerives (mmExprLanguageDef demo0Db demo0Tc) 8 "wff" ["t", "=", "r"]
    == [.apply "weq" [.apply "tt" [], .apply "tr" []]]

-- a second corpus string: `( t + r )` at term is exactly the tpl tree
#guard enumDerives (mmExprLanguageDef demo0Db demo0Tc) 8 "term"
    ["(", "t", "+", "r", ")"]
    == [.apply "tpl" [.apply "tt" [], .apply "tr" []]]

-- NEGATIVE: a non-string enumerates to nothing
#guard enumDerives (mmExprLanguageDef demo0Db demo0Tc) 8 "wff" ["t", "="] == []

-- NEGATIVE: fuel 0 finds nothing, even for a derivable string
#guard enumDerives (mmExprLanguageDef demo0Db demo0Tc) 0 "wff" ["t", "=", "r"]
    == []

-- the computed grammar is consuming, so the unconditional bridge applies
#guard consumingGrammarB (mmExprLanguageDef demo0Db demo0Tc)

/-- The certificate corollary fired on the instance: singleton enumeration at
fuel = `toks.length` + consuming grammar ⇒ unconditional `UniqueDerivation` —
every `Derives`-tree for `t = r` at `wff` over the computed grammar IS the weq
tree, with no fuel qualifier left in the conclusion. -/
theorem demo0_weq_unique :
    UniqueDerivation (mmExprLanguageDef demo0Db demo0Tc) "wff" ["t", "=", "r"] :=
  uniqueDerivation_of_enum (fuel := 3)
    (consumingGrammarB_sound (by rfl))
    (by simp)
    (.apply "weq" [.apply "tt" [], .apply "tr" []])
    (fun t ht => by
      rw [show enumDerives (mmExprLanguageDef demo0Db demo0Tc) 3 "wff"
            ["t", "=", "r"]
          = [.apply "weq" [.apply "tt" [], .apply "tr" []]] from rfl] at ht
      simpa using ht)

end EnumGates

end Mettapedia.Languages.Metamath.ExprDerive
