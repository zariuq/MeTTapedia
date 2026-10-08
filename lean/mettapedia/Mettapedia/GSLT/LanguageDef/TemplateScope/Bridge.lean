import Lean.Data.Json
import Mettapedia.GSLT.LanguageDef.TemplateScope.Surface
import Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus

/-!
# Template scope, part 11: the reference export for the C scope matrix

The Lean side of the bridge between this model and Prime's C runtime.  For
every row of the spectrum corpus and every configuration, one record holds:
the row and the configuration (as the model names it and as
`docs/prime/scope-policy-spectrum-20261006.md` names it), the MeTTa program
(`printSrc`), the model's answer bag with multiplicity in Prime's notation
(`printAns`), and the aliasing classes of every answer.

* `corpus` — the 46 rows whose six-configuration tables `SpectrumCorpus`
  proves (`corpus_tabled`); `extras` — further programs the criterion
  theorems of `SpectrumCorpus` and `ListsCorpus` use.
* `columns` — the six configurations of the matrix (`six_columns`).  Lexical
  inventory (ii) is no column of its own: with crossing sets overriding under
  every profile it is query-wide with crossing sets written (`ansII_eq_Q`),
  and its rows (`…ii`) carry those sets under every column.
* `records` — every row under every column; `exportJson` writes them.

## Main results

* `record_bag`, `records_bag` — **the export carries the model's answers**:
  the bag of every exported record is the model's `ans` of its row and
  column, the very function the table and criterion theorems are about.
* `records_firstOrder` — every exported bag is defined (the fuel suffices)
  and consists of first-order answers, checked by the kernel.  With
  `printAns_bag_faithful` the printed form of each answer determines it.
* `rows_noPQuote`, `programs_read_back` — no exported query or equation has
  a pattern quotation, so every printed program form reads back to the
  model's term (`readSrc_printSrc`).

The program text is the model's term, printed: an equation is the nullary
equation `(= (F) body)` whose body is curried, a template of `map-atom` is a
lambda applied per element, `unify` has the else branch `(empty)`, and a
construct's crossing set is a brace set touching it, `(lam z body){$t}`, the
reader's wrapper `(meta T {$t})`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge

open Lean (Json)
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus

/-! ## Names -/

/-- Every symbol of the corpus. -/
def allSy : List Sy :=
  [.Pair, .g, .d, .ok, .n1, .n2, .n3, .n4, .n5, .n7, .list2, .Got, .ca, .cb, .cc, .mk, .second,
    .lifted, .Lf, .unit, .Left, .Right]

theorem mem_allSy (c : Sy) : c ∈ allSy := by
  cases c <;> simp [allSy]

/-- Every spelling of the corpus. -/
def allSp : List Sp :=
  [.f, .y, .y2, .z, .w, .x, .r, .t, .a, .e, .s, .p, .tm, .u, .p1, .p2, .hole, .b]

theorem mem_allSp (q : Sp) : q ∈ allSp := by
  cases q <;> simp [allSp]

/-- How the surface writes a symbol.  `ca`, `cb`, `cc` are the spectrum
document's `a`, `b`, `c`; the numerals are numbers. -/
def symText : Sy → String
  | .Pair => "Pair" | .g => "g" | .d => "d" | .ok => "ok"
  | .n1 => "1" | .n2 => "2" | .n3 => "3" | .n4 => "4" | .n5 => "5" | .n7 => "7"
  | .list2 => "list2" | .Got => "Got" | .ca => "a" | .cb => "b" | .cc => "c"
  | .mk => "mk" | .second => "second" | .lifted => "lifted" | .Lf => "Lf" | .unit => "unit"
  | .Left => "Left" | .Right => "Right"

/-- How the surface writes a spelling (after `$` for a store name). -/
def spText : Sp → String
  | .f => "f" | .y => "y" | .y2 => "y2" | .z => "z" | .w => "w" | .x => "x" | .r => "r"
  | .t => "t" | .a => "a" | .e => "e" | .s => "s" | .p => "p" | .tm => "tm" | .u => "u"
  | .p1 => "p1" | .p2 => "p2" | .hole => "hole" | .b => "b"

/-- How the surface writes a keyword. -/
def kwText : Kw → String
  | .lam => "lam" | .let_ => "let" | .unify => "unify" | .superpose => "superpose"
  | .quote => "quote" | .empty => "empty" | .eq => "=" | .meta_ => "meta" | .new_ => "new"
  | .form => "form"

/-- How the surface writes an atom. -/
def atomText : SAtom Sy Sp → String
  | .sym c => symText c
  | .kw k => kwText k
  | .var v => "$" ++ spText v
  | .fresh v k => "$" ++ spText v ++ "#" ++ toString k
  | .par v => spText v

/-- The head of the crossing-set wrapper `(meta T {…})`. -/
def isMetaAtom : SAtom Sy Sp → Bool
  | .kw .meta_ => true
  | _ => false

/-- The text of an S-expression; a crossing-set wrapper is written `T{…}`. -/
def text (e : SExp (SAtom Sy Sp)) : String := e.render atomText isMetaAtom

/-! ## Rows -/

/-- The equation sets of the corpus. -/
inductive ClauseSet where
  /-- `SpectrumCorpus.clauses`. -/
  | base
  /-- `SpectrumCorpus.clausesU`: `unify` in place of the inner `let`. -/
  | unify
  /-- `ListsCorpus.clausesII`: `mk` returns `Lii`. -/
  | inventory
  deriving DecidableEq, Repr

/-- The equations of a set. -/
def ClauseSet.cl : ClauseSet → Sy → Option A
  | .base => clauses
  | .unify => clausesU
  | .inventory => clausesII

/-- The Lean name of a set. -/
def ClauseSet.lean : ClauseSet → String
  | .base => "SpectrumCorpus.clauses"
  | .unify => "SpectrumCorpus.clausesU"
  | .inventory => "ListsCorpus.clausesII"

/-- A row: an authored query with its equations. -/
structure Row where
  /-- The row's id, as the spectrum document numbers it. -/
  id : String
  /-- The Lean term of the query. -/
  lean : String
  /-- The equations. -/
  clauseSet : ClauseSet
  /-- The query. -/
  src : A
  /-- The theorem of `SpectrumCorpus` that tabulates this row, if one does. -/
  table : Option String
  /-- What the row probes. -/
  probes : String

/-- Make a row of the tabulated corpus (equations `clauses`). -/
def tabled (id lean probes : String) (src : A) : Row :=
  ⟨id, lean, .base, src, some (lean ++ "_table"), probes⟩

/-- **The corpus**: the 46 rows whose answers under the six configurations
`SpectrumCorpus` proves, one table theorem each. -/
def corpus : List Row := [
  tabled "1" "row1" "independent locals across calls" row1,
  tabled "2" "row2" "side-by-side inlining" row2,
  tabled "3" "row3" "the same argument twice" row3,
  tabled "4" "row4" "a same-spelled outsider, read" row4,
  tabled "4w" "row4w" "row 4 with the outsider renamed" row4w,
  tabled "5" "row5" "an outsider bound before definition" row5,
  tabled "5w" "row5w" "row 5 with the outsider renamed" row5w,
  tabled "6" "row6" "an outsider bound elsewhere in the scope" row6,
  tabled "6w" "row6w" "row 6 with the outsider renamed" row6w,
  tabled "7" "row7" "capture: the call before $y := 5" row7,
  tabled "8" "row8" "capture: the call after $y := 5" row8,
  tabled "7u" "row7u" "row 7, explicit unify" row7u,
  tabled "8u" "row8u" "row 8, explicit unify" row8u,
  tabled "7ec" "row7ec" "row 7, K shares $y: {$y}" row7ec,
  tabled "8ec" "row8ec" "row 8, K shares $y: {$y}" row8ec,
  tabled "9" "row9" "an intentional captured hole" row9,
  tabled "9w" "row9w" "row 9 with the outsider renamed to $u" row9w,
  tabled "9u" "row9u" "row 9, explicit unify" row9u,
  tabled "10a" "row10a" "nested templates, applied to 3" row10a,
  tabled "10b" "row10b" "nested templates, applied to 4" row10b,
  tabled "11" "row11" "inlining with hygiene: the let form" row11,
  tabled "11i" "row11i" "row 11 inlined as text" row11i,
  tabled "11h" "row11h" "row 11 inlined hygienically (L's $y renamed apart)" row11h,
  tabled "11ec" "row11ec" "row 11, lam w shares $f: {$f}" row11ec,
  tabled "11eci" "row11eci" "row 11ec inlined as text" row11eci,
  tabled "12a" "row12a" "template capture, binding after (the template as a lambda)" row12a,
  tabled "12b" "row12b" "template capture, binding before" row12b,
  tabled "12au" "row12au" "row 12a, explicit unify" row12au,
  tabled "12bu" "row12bu" "row 12b, explicit unify" row12bu,
  tabled "12aec" "row12aec" "row 12a, the template shares $y: {$y}" row12aec,
  tabled "12bec" "row12bec" "row 12b, the template shares $y: {$y}" row12bec,
  tabled "13a" "row13a" "a returned closure, two calls" row13a,
  tabled "13b" "row13b" "library immunity" row13b,
  tabled "mk2" "rowmk2" "two closures from two calls of (mk)" rowmk2,
  tabled "14" "row14" "row 9 with the lambda sharing $t: {$t}" row14,
  tabled "16" "row16" "partial application" row16,
  tabled "18" "row18" "Need sharing: one application, read twice" row18,
  tabled "22a" "row22a" "caller refinement through an equation" row22a,
  tabled "22b" "row22b" "caller refinement: conflict" row22b,
  tabled "23a" "row23a" "one slot or two: sibling lets" row23a,
  tabled "23b" "row23b" "independent local slots printing the same name" row23b,
  tabled "23c" "row23c" "a nested let of the same spelling" row23c,
  tabled "23cu" "row23cu" "row 23c, explicit unify" row23cu,
  tabled "LfEq" "rowLfEq" "the per-call lifted equation of L, called twice" rowLfEq,
  tabled "H1" "rowH1" "a body-only name, introduced by no pattern: one hole or two" rowH1,
  tabled "H2" "rowH2" "the holes of H1 refined to Left and Right (let* as nested lets, no else branch)"
    rowH2]

/-- The corpus is the 46 tabulated rows: the bridge's six-configuration
answers of each row are `six clauses rowN`, whose value the theorem
`rowN_table` of `SpectrumCorpus` states. -/
theorem corpus_tabled :
    corpus.map (fun r => six r.clauseSet.cl r.src) =
      [six clauses row1, six clauses row2, six clauses row3, six clauses row4,
        six clauses row4w, six clauses row5, six clauses row5w, six clauses row6,
        six clauses row6w, six clauses row7, six clauses row8, six clauses row7u,
        six clauses row8u, six clauses row7ec, six clauses row8ec, six clauses row9,
        six clauses row9w, six clauses row9u, six clauses row10a, six clauses row10b,
        six clauses row11, six clauses row11i, six clauses row11h, six clauses row11ec,
        six clauses row11eci, six clauses row12a, six clauses row12b, six clauses row12au,
        six clauses row12bu, six clauses row12aec, six clauses row12bec, six clauses row13a,
        six clauses row13b, six clauses rowmk2, six clauses row14, six clauses row16,
        six clauses row18, six clauses row22a, six clauses row22b, six clauses row23a,
        six clauses row23b, six clauses row23c, six clauses row23cu, six clauses rowLfEq,
        six clauses rowH1, six clauses rowH2] :=
  rfl

theorem corpus_length : corpus.length = 46 := rfl

/-- Make a row of the criterion programs. -/
def extra (id lean : String) (cs : ClauseSet) (probes : String) (src : A) : Row :=
  ⟨id, lean, cs, src, none, probes⟩

/-- **Further programs** of the criterion theorems (`crit1_matrix`,
`crit4_matrix`, `crit5_matrix`, `crit10_matrix`, `lexicalInventory_ii`,
`lexicalInventory_ii_criteria`, `written_override_matrix`).  Only
`written_override_matrix` states six-column tables for some of them;
`records_bag` makes every one the model's `ans`. -/
def extras : List Row := [
  extra "4ec" "row4ec" .base "row 4, L shares $y: {$y}" row4ec,
  extra "4u" "row4u" .unify "row 4, L refines by unify" row4u,
  extra "4L2" "row4L2" .base "row 4, L's private name renamed" row4L2,
  extra "17" "row17eq" .base "the lifted equation of row 4's lambda, called" row17eq,
  extra "17u" "row17eq" .unify "row 17 with the unify equations" row17eq,
  extra "22au" "row22a" .unify "row 22a with the unify equations" row22a,
  extra "22bu" "row22b" .unify "row 22b with the unify equations" row22b,
  extra "25" "row25 Lp Kc" .base "two private locals and a connecting lambda, unannotated"
    (row25 Lp Kc),
  extra "25ec" "row25 Lp KcEC" .base "row 25, the connecting lambda shares $t: {$t}" (row25 Lp KcEC),
  extra "25u" "row25 Lp KcLF" .base "row 25, the connecting lambda refines by unify"
    (row25 Lp KcLF),
  extra "25ii" "row25 LpII Kc" .base "row 25, the private local shares nothing: {}" (row25 LpII Kc),
  extra "26" "row26 row9 row9" .base "two associations as alternatives: 9 and 9" (row26 row9 row9),
  extra "26ec" "row26 row14 row9" .base "two associations as alternatives: 14 and 9"
    (row26 row14 row9),
  extra "26u" "row26 row9u row9" .base "two associations as alternatives: 9u and 9"
    (row26 row9u row9),
  extra "26ii" "row26 row9 row9ii" .base
    "two associations as alternatives: 9, and 9 with the lambda sharing nothing" (row26 row9 row9ii),
  extra "28" "row28" .base "the built closure of (mk) extended with a same-spelled outsider"
    row28,
  extra "1ii" "lt .f Lii (pair f1 f2)" .base "row 1, L shares nothing: {}" (lt .f Lii (pair f1 f2)),
  extra "2ii" "pair (ap Lii (k .n1)) (ap Lii (k .n2))" .base "row 2, L shares nothing: {}"
    (pair (ap Lii (k .n1)) (ap Lii (k .n2))),
  extra "3ii" "lt .f Lii (pair f1 f1)" .base "row 3, L shares nothing: {}" (lt .f Lii (pair f1 f1)),
  extra "4ii" "row4ii" .base "row 4, L shares nothing: {}" row4ii,
  extra "5ii" "lt .y (k .n5) (lt .f Lii f1)" .base "row 5, L shares nothing: {}"
    (lt .y (k .n5) (lt .f Lii f1)),
  extra "6ii" "lt .f Lii (pair f1 (lt .y (k .n5) (sv .y)))" .base "row 6, L shares nothing: {}"
    (lt .f Lii (pair f1 (lt .y (k .n5) (sv .y)))),
  extra "9ii" "row9ii" .base "row 9, the lambda shares nothing: {}" row9ii,
  extra "11ii" "lt .f Lii (ap LiiW (k .n5))" .base "row 11, L shares nothing, lam w shares $f"
    (lt .f Lii (ap LiiW (k .n5))),
  extra "11iii" "ap (lsh .w [] (pair (ap Lii (k .n1)) (lt .y (pr .w) (sv .y)))) (k .n5)" .base
    "row 11ii inlined as text" (ap (lsh .w [] (pair (ap Lii (k .n1)) (lt .y (pr .w) (sv .y))))
      (k .n5)),
  extra "13aii" "row13a" .inventory "row 13a, (mk) returns L sharing nothing" row13a,
  extra "13bii" "row13b" .inventory "row 13b, (mk) returns L sharing nothing" row13b,
  extra "16ii" "row 16, the inner lambda sharing nothing" .base
    "row 16, the inner lambda shares nothing: {}"
    (lt .p (ap (lm .z (lsh .w [] (lt .y (pair (pr .z) (pr .w)) (sv .y)))) (k .n1))
      (pair (ap (sv .p) (k .n2)) (ap (sv .p) (k .n3)))),
  extra "18ii" "lt .f Lii (lt .a f1 (pair (sv .a) (sv .a)))" .base "row 18, L shares nothing: {}"
    (lt .f Lii (lt .a f1 (pair (sv .a) (sv .a)))),
  extra "1s" "row1s" .base "row 1, L shares its $y: {$y}" row1s,
  extra "7a" "row7a" .base "row 7, K shares nothing: {}" row7a,
  extra "23cf" "row23cf" .base "row 23c, the inner let fresh: {}" row23cf,
  extra "23cs" "row23cs" .base "row 23c, the inner let sharing $y: {$y}" row23cs,
  extra "23cw" "row23cw" .base "row 23c, both lets fresh: every construct carries its set" row23cw]

/-- Every row of the export. -/
def rows : List Row := corpus ++ extras

/-- The texts are well formed and tell the atoms of the export apart: no
text is empty or holds a delimiter, symbols are written injectively and
spellings too, and no symbol, and no spelling written bare as a parameter, is
written like a keyword or like a symbol.  (A store name is written after `$`,
which no symbol or parameter text contains.)  Checked when the export is
written. -/
def checkTexts : Except String Unit := do
  let bad : List Char := [' ', '\t', '\n', '(', ')', '{', '}', '[', ']', '"', ',', '#', '$', ';']
  let words := allSy.map symText ++ allSp.map spText
  for w in words do
    if w.isEmpty || w.any (· ∈ bad) then throw s!"ill-formed name '{w}'"
  let syms := allSy.map symText
  let sps := allSp.map spText
  let kws := [Kw.lam, .let_, .unify, .superpose, .quote, .empty, .eq, .meta_, .new_, .form].map kwText
  unless syms.Nodup do throw "two symbols share a name"
  unless sps.Nodup do throw "two spellings share a name"
  for w in syms do
    if w ∈ kws then throw s!"symbol '{w}' is written like a keyword"
  let bodies := rows.flatMap fun r =>
    r.src :: allSy.filterMap fun F => r.clauseSet.cl F
  for q in bodies.flatMap Src.params do
    if spText q ∈ kws ++ syms then throw s!"parameter '{spText q}' is written like a symbol"

/-! ## Columns -/

/-- A column with its names. -/
structure ColumnInfo where
  /-- The configuration. -/
  cfg : Config
  /-- The model's name. -/
  model : String
  /-- The Lean definition. -/
  lean : String
  /-- The spectrum document's name. -/
  spectrum : String
  ownership : String
  lifetime : String
  readout : String
  /-- How the column reads a construct's crossing set. -/
  writtenList : String

/-- How every column reads the crossing sets: they override its default. -/
def writtenOverrides : String :=
  "the crossing set, T{$t}, overrides the default: a lambda owns every other name its " ++
    "region uses; a let makes every other name of its pattern fresh"

/-- The columns: the six configurations, in the order of `six`. -/
def columns : List ColumnInfo := [
  ⟨cfgM, "M", "cfgM", "mercury-implicit / per-call / reference", "mercury-implicit",
    "per-call", "reference", writtenOverrides⟩,
  ⟨cfgLF, "LF", "cfgLF", "lexical-fresh / per-call / reference", "lexical-fresh",
    "per-call", "reference", writtenOverrides⟩,
  ⟨cfgEC, "EC", "cfgEC", "explicit-capture / per-call / reference", "explicit-capture",
    "per-call", "reference", writtenOverrides⟩,
  ⟨cfgQ, "Q", "cfgQ", "query-wide", "query-wide", "per-call", "reference", writtenOverrides⟩,
  ⟨cfgPC, "PC", "cfgPC", "mercury-implicit / per-closure / reference", "mercury-implicit",
    "per-closure", "reference", writtenOverrides⟩,
  ⟨cfgSN, "SN", "cfgSN", "mercury-implicit / per-call / snapshot", "mercury-implicit",
    "per-call", "snapshot", writtenOverrides⟩]

/-- The columns are the configurations of `six`, in its order. -/
theorem six_columns (cl : Sy → Option A) (t : A) :
    columns.map (fun c => SpectrumCorpus.ans c.cfg cl t) = six cl t := rfl

/-! ## Records -/

/-- A record: a row under a column, with the model's answer bag. -/
structure Record where
  row : Row
  col : ColumnInfo
  bag : Option (List T)

/-- The record of a row under a column. -/
def record (r : Row) (c : ColumnInfo) : Record := ⟨r, c, SpectrumCorpus.ans c.cfg r.clauseSet.cl r.src⟩

/-- Every row under every column. -/
def records : List Record := rows.flatMap fun r => columns.map (record r)

/-- **The export carries the model's answers**, record by record. -/
theorem record_bag (r : Row) (c : ColumnInfo) :
    (record r c).bag = SpectrumCorpus.ans c.cfg r.clauseSet.cl r.src := rfl

/-- **The export carries the model's answers**: every exported record is a row
under a column, and its bag is the model's answer bag `SpectrumCorpus.ans`
there. -/
theorem records_bag : ∀ x ∈ records, x.row ∈ rows ∧ x.col ∈ columns ∧
    x.bag = SpectrumCorpus.ans x.col.cfg x.row.clauseSet.cl x.row.src := by
  intro x hx
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  exact ⟨hr, hc, rfl⟩

/-- Every row appears under every column. -/
theorem record_mem {r : Row} (hr : r ∈ rows) {c : ColumnInfo} (hc : c ∈ columns) :
    record r c ∈ records :=
  List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨c, hc, rfl⟩⟩

/-- No exported query or equation body has a quotation in pattern position
(kernel-checked). -/
theorem rows_noPQuote :
    rows.all (fun r => r.src.NoPQuote && (allSy.filterMap r.clauseSet.cl).all Src.NoPQuote) =
      true := by
  decide +kernel

/-- **Every exported program reads back**: the query and every equation body
of every row, printed with its crossing sets, read back to the model's
terms. -/
theorem programs_read_back {r : Row} (hr : r ∈ rows) :
    readSrc (printSrc r.src) = some r.src ∧
      ∀ F body, r.clauseSet.cl F = some body → readSrc (printSrc body) = some body := by
  have h := List.all_eq_true.1 rows_noPQuote r hr
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨readSrc_printSrc h.1, fun F body hF => readSrc_printSrc (h.2 body ?_)⟩
  exact List.mem_filterMap.2 ⟨F, mem_allSy F, hF⟩

/-- A bag that is defined and first-order. -/
def definedFirstOrder : Option (List T) → Bool
  | some bag => bag.all Tm.FirstOrder
  | none => false

/-- **Every exported bag is defined and first-order** (kernel-checked). -/
theorem records_firstOrder : records.all (fun x => definedFirstOrder x.bag) = true := by
  decide +kernel

/-! ## Examples of the naming -/

/-- Parameters, in answers that are not first-order, print by spelling. -/
def parName (n : Nm (Slot Sp)) : SAtom Sy Sp := .par n.spelling

/-- Positive: row 7 under explicit capture.  `K`'s own `$y`, copied by the
activation at path `[0, 2]`, is the bag's first allocated name and prints as
`$y#1`. -/
theorem row7_EC_printed :
    SpectrumCorpus.ans cfgEC clauses row7 = some [pairT (kT .n1) (fv [0, 2] [1, 0] .y)] ∧
    printAns (bagNaming (allocated [pairT (kT .n1) (fv [0, 2] [1, 0] .y)])) parName
        (pairT (kT .n1) (fv [0, 2] [1, 0] .y)) =
      .list [.atom (.sym .Pair), .atom (.sym .n1), .atom (.fresh .y 1)] := by
  decide +kernel

/-- Negative: naming store names by spelling alone is not faithful.  The
query's `$y` beside a copy of `$y` prints like the query's `$y` twice, although
the two answers differ; the bag's naming tells them apart. -/
theorem spelling_naming_not_faithful :
    let byName : Nm (Slot Sp) → SAtom Sy Sp := fun n => .var n.spelling
    let a := pairT (qv .y) (fv [0, 2] [] .y)
    let b := pairT (qv .y) (qv .y)
    a ≠ b ∧ printAns byName parName a = printAns byName parName b ∧
      printAns (bagNaming (allocated [a, b])) parName a ≠
        printAns (bagNaming (allocated [a, b])) parName b := by
  decide +kernel

/-! ## JSON -/

/-- The slot a store name copies. -/
def Nm.slot : Nm (Slot Sp) → Slot Sp
  | .src o => o
  | .inst _ n => Nm.slot n

/-- The activations that copied a store name, outermost first. -/
def Nm.copies : Nm (Slot Sp) → List Path
  | .src _ => []
  | .inst ρ n => ρ :: Nm.copies n

mutual
/-- An S-expression as JSON: an atom as its text, a list as an array, a brace
set as `{"braces": [...]}`. -/
def sexpJson : SExp (SAtom Sy Sp) → Json
  | .atom a => .str (atomText a)
  | .list items => .arr (sexpsJson items).toArray
  | .braces items => Json.mkObj [("braces", .arr (sexpsJson items).toArray)]

/-- A sequence of S-expressions as JSON. -/
def sexpsJson : List (SExp (SAtom Sy Sp)) → List Json
  | [] => []
  | e :: es => sexpJson e :: sexpsJson es
end

mutual
/-- The positions of an atom in an S-expression: paths of item indices. -/
def positions (x : SAtom Sy Sp) (path : List ℕ) : SExp (SAtom Sy Sp) → List (List ℕ)
  | .atom a => if a = x then [path] else []
  | .list items => positionsSeq x path 0 items
  | .braces items => positionsSeq x path 0 items

/-- The positions of an atom in a sequence of items, the first at index `i`. -/
def positionsSeq (x : SAtom Sy Sp) (path : List ℕ) (i : ℕ) :
    List (SExp (SAtom Sy Sp)) → List (List ℕ)
  | [] => []
  | e :: es => positions x (path ++ [i]) e ++ positionsSeq x path (i + 1) es
end

/-- A list of numbers as JSON. -/
def natsJson (l : List ℕ) : Json := .arr (l.map fun n => Json.num (n : Int)).toArray

/-- The aliasing classes of an answer: one class per store name, in order of
first occurrence, with its printed name, its slot, and the positions of its
occurrences.  The naming is injective (`bagNaming_injOn`), so the classes are
also the classes of printed names. -/
def aliasingJson (ν : Nm (Slot Sp) → SAtom Sy Sp) (t : T) (e : SExp (SAtom Sy Sp)) : Json :=
  .arr (t.vars.eraseDups.map fun n =>
    Json.mkObj [
      ("name", .str (atomText (ν n))),
      ("kind", .str (if n.querySpelling?.isSome then "query" else "allocated")),
      ("spelling", .str (spText n.spelling)),
      ("owner", natsJson (Nm.slot n).1),
      ("copies", .arr ((Nm.copies n).map natsJson).toArray),
      ("positions", .arr ((positions (ν n) [] e).map natsJson).toArray)]).toArray

/-- One answer: its text, its S-expression, and its aliasing classes. -/
def answerJson (ν : Nm (Slot Sp) → SAtom Sy Sp) (t : T) : Json :=
  let e := printAns ν parName t
  Json.mkObj [("text", .str (text e)), ("sexp", sexpJson e), ("aliasing", aliasingJson ν t e)]

/-- A bag in Prime's notation, `[a, b]`. -/
def bagText (ν : Nm (Slot Sp) → SAtom Sy Sp) (bag : List T) : String :=
  "[" ++ ", ".intercalate (bag.map fun t => text (printAns ν parName t)) ++ "]"

/-- The equations a query reaches, by the fixed point of one step of
reference. -/
def reachable (cl : Sy → Option A) (t : A) : List Sy :=
  Nat.iterate (fun fs => fs ++ fs.flatMap fun F => ((cl F).map Src.fns).getD []) allSy.length
    t.fns

/-- The program of a row: the equations its query reaches, in the order of
`allSy`, then the query. -/
def programText (r : Row) : String :=
  let reach := reachable r.clauseSet.cl r.src
  let eqs := allSy.filterMap fun F =>
    if F ∈ reach then (r.clauseSet.cl F).map fun b => text (printClause F b) else none
  String.intercalate "\n" (eqs ++ ["!" ++ text (printSrc r.src)]) ++ "\n"

/-- The JSON of a record. -/
def recordJson (x : Record) : Json :=
  let base := [
    ("row", Json.str x.row.id),
    ("config", .str x.col.model),
    ("spectrum_config", .str x.col.spectrum),
    ("program", .str (programText x.row)),
    ("program_capture_braces", .str (programText x.row)),
    ("defined", .bool x.bag.isSome)]
  match x.bag with
  | some bag =>
      let ν := bagNaming (allocated bag)
      Json.mkObj (base ++ [
        ("expected_bag", .str (bagText ν bag)),
        ("expected", .arr (bag.map (answerJson ν)).toArray)])
  | none => Json.mkObj (base ++ [("expected_bag", .null), ("expected", .null)])

/-- The JSON of a row. -/
def rowJson (group : String) (r : Row) : Json :=
  Json.mkObj [
    ("row", .str r.id),
    ("group", .str group),
    ("lean", .str r.lean),
    ("clauses", .str r.clauseSet.lean),
    ("table_theorem", match r.table with
      | some n => .str ("SpectrumCorpus." ++ n)
      | none => .null),
    ("probes", .str r.probes),
    ("program", .str (programText r)),
    ("program_capture_braces", .str (programText r))]

/-- The JSON of a column. -/
def columnJson (c : ColumnInfo) : Json :=
  Json.mkObj [
    ("config", .str c.model), ("lean", .str c.lean), ("spectrum_config", .str c.spectrum),
    ("ownership", .str c.ownership), ("lifetime", .str c.lifetime), ("readout", .str c.readout),
    ("written_list", .str c.writtenList)]

/-- Strings as a JSON array. -/
def strsJson (l : List String) : Json := .arr (l.map Json.str).toArray

/-- **The export.** -/
def exportJson : Json :=
  Json.mkObj [
    ("schema", .str "scope-spectrum-lean-reference/2"),
    ("source", Json.mkObj [
      ("module", .str "Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge"),
      ("export", .str "Bridge.exportJson, written by scripts/ExportScopeSpectrumReference.lean"),
      ("theorems", strsJson [
        "Bridge.records_bag: every record's bag is the model's ans of its row and column",
        "Bridge.corpus_tabled: the 46 corpus rows are the rows SpectrumCorpus tabulates",
        "Bridge.records_firstOrder: every bag is defined and first-order",
        "TemplateScope.printAns_bag_faithful: the printed answer determines the answer",
        "Bridge.programs_read_back: every printed query and equation reads back to the model's term, crossing sets included (TemplateScope.readSrc_printSrc)",
        "Lists.elabWith_lam_crossing, Lists.elabWith_let_crossing: a crossing set overrides the default under every profile"]),
      ("fuel", Json.num 80),
      ("model", .str "SpectrumCorpus.ans c cl t = answersCfg c (progOf c cl) 80 t")]),
    ("notation", Json.mkObj [
      ("store_names", .str "$y is the query's own slot y, left unbound; $y#k is the k-th name the configuration allocated (an activation copy, or a per-closure slot left free), numbered from 1 by first occurrence in the bag; its spelling is kept"),
      ("parameters", .str "lambda parameters are written bare: (lam z body)"),
      ("data_and_calls", .str "an application whose spine starts with a symbol is data and is written flat, (Pair a b); every other application is a call and is written binary, (((second) a) $t)"),
      ("equations", .str "each equation is nullary, (= (F) body); a k-ary equation is a nullary one whose body is k nested lambdas, its head variables bound by let from the parameters; only the equations the query reaches are written"),
      ("templates", .str "rows 12*: the map-atom template is a lambda applied per element, (let $tm T (list2 ($tm 1) ($tm 2)))"),
      ("unify", .str "(unify p v b (empty)): the model's unify has no else branch, and a failed match gives no answer"),
      ("alternatives", .str "(superpose (t1 t2))"),
      ("crossing_sets", .str "(lam z body){$t}, (let p v body){$t}: a brace set touching a lambda or a let is its crossing set, the names it shares with the outside (the reader's wrapper (meta T {$t})); a lambda owns every other name its region uses, a let makes every other name of its pattern fresh; {} is the empty set; the set overrides every configuration's default; inferred own lists are never printed"),
      ("program_capture_braces", .str "kept for the comparison script's --capture-style option: under the decided convention a program has one spelling, so it equals program"),
      ("symbols", .str "a, b, c are the model's ca, cb, cc; numerals are numbers; list2 is a constructor")]),
    ("observations", Json.mkObj [
      ("compared", strsJson [
        "the answer bag, as a multiset: one entry per answer, with multiplicity",
        "each answer up to a consistent renaming of its store names (alpha-equivalence)",
        "aliasing: which positions of an answer hold one store name",
        "definedness: an empty bag means no answer, not an error or a timeout"]),
      ("not_compared", strsJson [
        "residual constraints: the model's store is ground and is applied to every answer; nothing else of the final store is observed",
        "effects and their order (criterion 9 is not modeled)",
        "timing, fuel and cost",
        "whether a store name is printed with or without a #suffix, and its spelling (reported, not required)",
        "the order of answers within a bag"])]),
    ("configurations", .arr (columns.map columnJson).toArray),
    ("rows", .arr ((corpus.map (rowJson "corpus")) ++ (extras.map (rowJson "criteria"))).toArray),
    ("records", .arr (records.map recordJson).toArray)]

/-- The export as text. -/
def exportText : String := exportJson.pretty ++ "\n"

end Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge
