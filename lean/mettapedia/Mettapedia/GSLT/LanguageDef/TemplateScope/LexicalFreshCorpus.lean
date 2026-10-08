import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFresh
import Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCone
import Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge

/-!
# Lexical fresh and its translator on the corpus

The identity-based elaborations of `TemplateScope.LexicalFresh` on the rows of
the scope corpus (`Bridge.rows`: 80 programs, each with its equations), by
kernel-checked computation.

* `translation_exact_rows` — on every row, lexical fresh runs the translated
  program to the very bag of results rule M gives the source (an instance of
  `run_toLexical`; no computation).
* `body_only_translated` — rows H1 and H2: `$hole` is written only in a body.
  The census finds one un-introduced name and no refining pattern; the
  translation declares it, `(lam z (new ($hole) $hole))`.
* `refining_translated` — rows 4, 9, 23a, 23c and the equation `second` of row
  22: the refining patterns and the crossing sets the translation writes.
* `agreement_rows`, `agreement_negative` — rows with an empty census elaborate
  alike under both options (`agreement`); row 4 does not, and differs.
* `census_table` — the census of every row's query.
* `identity_matches_slots` — **the identity model reproduces the slot model**:
  on all 80 rows, both identity-based elaborations answer, printed with each
  bag's naming, what `SpectrumCorpus.ans` answers under M and LF.
* `slot_model_translation` — **the translation in the slot model**: the slot
  model's LF configuration (activation per `let` and per `new` block) runs every
  translated row to the printed bag that rule M gives the source.
* `shadowing_is_not_overwriting`, `crossing_refines` — the cone law on two
  rows: lexical fresh keeps the outer `$y` of row 23c beside the inner one,
  and a crossing set refines (row 23cs fails on its conflict).
* `exportJson` — the corpus translations, for `docs/prime`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus

open Lean (Json)
open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.Bridge

/-- Terms of the identity model. -/
abbrev TI := Tm Sy (BId Sp)

/-- Answers of a query under rule M, with binder identities. -/
def ansMI (cl : Sy → Option A) (t : A) : Option (List TI) :=
  answers .static (progM .u .unit cl) 80 (elabMFormAt [] t)

/-- Answers of a query under lexical fresh, with binder identities. -/
def ansLFI (cl : Sy → Option A) (t : A) : Option (List TI) :=
  answers .static (progLF .u .unit cl) 80 (elabLFFormAt [] t)

/-- The translated equations. -/
def clT (cl : Sy → Option A) : Sy → Option A := toLexicalProg cl

/-- **The translation is exact on every row**: lexical fresh on the translated
program answers exactly what rule M answers on the source. -/
theorem translation_exact_rows (cl : Sy → Option A) (t : A) :
    ansLFI (clT cl) (toLexical t) = ansMI cl t :=
  answers_toLexical Sp.u Sy.unit cl t .static 80

/-! ## Printing answers of the identity model -/

/-- The spelling a name prints with. -/
def spellI : Nm (BId Sp) → Sp
  | .src (.slot k) => k.spell
  | .src (.par v _) => v
  | .src (.code v _) => v
  | .inst _ n => spellI n

/-- The query's own slots: the root's head slots. -/
def isQueryI : Nm (BId Sp) → Bool
  | .src (.slot ⟨_, [], [], .head⟩) => true
  | _ => false

/-- The names a bag allocates, by first occurrence. -/
def allocatedI (bag : List TI) : List (Nm (BId Sp)) :=
  ((bag.flatMap Tm.vars).filter fun n => !isQueryI n).eraseDups

/-- The naming of a bag: the query's own slots as `$y`, the `k`-th allocated
name as `$y#k`, as `bagNaming` does for the slot model. -/
def bagNamingI (names : List (Nm (BId Sp))) (n : Nm (BId Sp)) : SAtom Sy Sp :=
  if isQueryI n then .var (spellI n) else .fresh (spellI n) (names.idxOf n + 1)

/-- Parameters print by spelling. -/
def parNameI (n : Nm (BId Sp)) : SAtom Sy Sp := .par (spellI n)

/-- A bag of the identity model, printed. -/
def printedI (bag : Option (List TI)) : Option (List (SExp (SAtom Sy Sp))) :=
  bag.map fun b => b.map (printAns (bagNamingI (allocatedI b)) parNameI)

/-- A bag of the slot model, printed. -/
def printedS (bag : Option (List T)) : Option (List (SExp (SAtom Sy Sp))) :=
  bag.map fun b => b.map (printAns (bagNaming (allocated b)) Bridge.parName)

/-- A printed bag as text. -/
def bagTextP : Option (List (SExp (SAtom Sy Sp))) → String
  | some b => "[" ++ ", ".intercalate (b.map text) ++ "]"
  | none => "undefined"

/-- Data in answers of the identity model. -/
def kI (c : Sy) : TI := .sym c
def pairI (a b : TI) : TI := .app (.app (.sym .Pair) a) b
def gI (a : TI) : TI := .app (.sym .g) a
/-- The query's own slot `$y`. -/
def qI (v : Sp) : TI := .var (.src (.slot ⟨v, [], [], .head⟩))

/-! ## Rows H1 and H2: a body-only name -/

/-- `(lam z $hole)` as the translation writes it: `(lam z (new ($hole) $hole))`. -/
def holeT : A := lm .z (.new [.hole] (sv .hole))

/-- **Rows H1 and H2.**  The census of H1 finds no refining pattern and one
un-introduced name, `$hole`, owned by the lambda at position `[1]`.  The
translation declares it.  Rule M answers H1 with two holes and H2 with
`(Pair Left Right)`; lexical fresh on the source answers one hole twice, and
no answer for H2 (w11's `fail-second` path: H2 is w11's program, the model's
`unify` having no else branch); lexical fresh on the translation answers as
rule M does. -/
theorem body_only_translated :
    refining [] rowH1 = [] ∧ unintroduced [] rowH1 = [([1], .hole)] ∧
    toLexical rowH1 = lt .f holeT (pair f1 f2) ∧
    printedI (ansMI clauses rowH1) =
      some [.list [.atom (.sym .Pair), .atom (.fresh .hole 1), .atom (.fresh .hole 2)]] ∧
    printedI (ansLFI clauses rowH1) =
      some [.list [.atom (.sym .Pair), .atom (.var .hole), .atom (.var .hole)]] ∧
    printedI (ansLFI (clT clauses) (toLexical rowH1)) =
      some [.list [.atom (.sym .Pair), .atom (.fresh .hole 1), .atom (.fresh .hole 2)]] ∧
    refining [] rowH2 = [] ∧ unintroduced [] rowH2 = [([1], .hole)] ∧
    ansMI clauses rowH2 = some [pairI (kI .Left) (kI .Right)] ∧
    ansLFI clauses rowH2 = some [] ∧
    ansLFI (clT clauses) (toLexical rowH2) = some [pairI (kI .Left) (kI .Right)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Refining patterns -/

/-- **Refining patterns and their crossing sets.**
* Row 4: `L`'s `$y` refines the outsider under rule M; the translation writes
  `(let $y z (g $y)){$y}`, and lexical fresh then answers `(Pair (g 1) 1)`.
* Row 9: the lambda's pattern `(d $t)` refines the query's `$t`.
* Row 23a: two sibling `let`s of one query slot `$x` both refine it.
* Row 23c: the outer `let` covers `$y`; the inner one refines it.
* The equation `second` of row 22: its pattern `(d $s $t)` refines the head
  variables. -/
theorem refining_translated :
    refining [] row4 = [([1, 0], .y)] ∧
    toLexical row4 = lt .f (lm .z (lts .y (pr .z) (ap (k .g) (sv .y)) [.y])) (pair f1 (sv .y)) ∧
    ansLFI clauses row4 = some [pairI (gI (kI .n1)) (qI .y)] ∧
    ansMI clauses row4 = some [pairI (gI (kI .n1)) (kI .n1)] ∧
    refining [] row9 = [([1, 0], .t)] ∧
    refining [] row23a = [([0, 1], .x), ([1], .x)] ∧
    toLexical row23a = pair (lts .x (k .n1) (sv .x) [.x]) (lts .x (k .n2) (sv .x) [.x]) ∧
    refining [] row23c = [([2, 1], .y)] ∧
    toLexical row23c = lt .y (k .n1) (pair (sv .y) (lts .y (k .n2) (sv .y) [.y])) ∧
    ((clauses .second).map (refining [5])) = some [([5, 0, 0, 2, 2], .s), ([5, 0, 0, 2, 2], .t)] ∧
    ansLFI clauses row22a ≠ ansMI clauses row22a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The census of the corpus -/

/-- **The census of every row's query**: `(refining patterns, un-introduced
names)`.  24 of the 80 queries have a non-empty census: 45 refining
pattern names and 5 un-introduced names in all. -/
theorem census_table :
    rows.map (fun r => (r.id, census [] r.src)) =
      [("1", 0, 0), ("2", 0, 0), ("3", 0, 0), ("4", 1, 0), ("4w", 0, 0), ("5", 1, 0), ("5w", 0, 0),
        ("6", 2, 0), ("6w", 0, 0), ("7", 1, 0), ("8", 1, 0), ("7u", 0, 0), ("8u", 0, 0), ("7ec", 1, 0),
        ("8ec", 1, 0), ("9", 1, 0), ("9w", 0, 0), ("9u", 0, 0), ("10a", 2, 1), ("10b", 2, 1), ("11", 0, 0),
        ("11i", 2, 1), ("11h", 0, 0), ("11ec", 0, 0), ("11eci", 2, 0), ("12a", 1, 0), ("12b", 0, 0),
        ("12au", 0, 0), ("12bu", 0, 0), ("12aec", 1, 0), ("12bec", 0, 0), ("13a", 0, 0), ("13b", 0, 0),
        ("mk2", 0, 0), ("14", 0, 0), ("16", 0, 0), ("18", 0, 0), ("22a", 0, 0), ("22b", 0, 0),
        ("23a", 2, 0), ("23b", 0, 0), ("23c", 1, 0), ("23cu", 0, 0), ("LfEq", 0, 0), ("H1", 0, 1),
        ("H2", 0, 1), ("4ec", 0, 0), ("4u", 0, 0), ("4L2", 0, 0), ("17", 0, 0), ("17u", 0, 0),
        ("22au", 0, 0), ("22bu", 0, 0), ("25", 1, 0), ("25ec", 0, 0), ("25u", 0, 0), ("25ii", 1, 0),
        ("26", 6, 0), ("26ec", 5, 0), ("26u", 5, 0), ("26ii", 5, 0), ("28", 0, 0), ("1ii", 0, 0),
        ("2ii", 0, 0), ("3ii", 0, 0), ("4ii", 0, 0), ("5ii", 0, 0), ("6ii", 0, 0), ("9ii", 0, 0),
        ("11ii", 0, 0), ("11iii", 0, 0), ("13aii", 0, 0), ("13bii", 0, 0), ("16ii", 0, 0), ("18ii", 0, 0),
        ("1s", 0, 0), ("7a", 0, 0), ("23cf", 0, 0), ("23cs", 0, 0), ("23cw", 0, 0)] := by
  decide +kernel

/-- **The census of the equations**: in `clauses` (and `clausesII`), `second`
has two refining patterns (its pattern `(d $s $t)` refines the head variables)
and `lifted` one; with `unify` in their place (`clausesU`) none remain. -/
theorem equation_census :
    ([clauses, clausesU, clausesII].map fun cl =>
      allSy.filterMap fun F => (cl F).map fun b => (F, census [5] b)) =
      [[(.mk, 0, 0), (.second, 2, 0), (.lifted, 1, 0), (.Lf, 0, 0)],
       [(.mk, 0, 0), (.second, 0, 0), (.lifted, 0, 0), (.Lf, 0, 0)],
       [(.mk, 0, 0), (.second, 2, 0), (.lifted, 1, 0), (.Lf, 0, 0)]] := by
  decide +kernel

/-- Whether a row has an empty census: its query and every equation it
reaches. -/
def censusEmpty (r : Row) : Bool :=
  decide (census [] r.src = (0, 0)) &&
    (reachable r.clauseSet.cl r.src).all fun F =>
      match r.clauseSet.cl F with
      | some b => decide (census [5] b = (0, 0))
      | none => true

/-- **Agreement on the corpus**: every row whose query and reached equations
have an empty census answers alike under lexical fresh and rule M, with no
translation (the general statement is `agreement` and `run_agreement`). -/
theorem agreement_rows :
    rows.all (fun r => !censusEmpty r ||
      decide (ansLFI r.clauseSet.cl r.src = ansMI r.clauseSet.cl r.src)) = true := by
  decide +kernel

/-- An empty census is the general theorem's hypothesis: on row 1 the two
elaborations are equal terms. -/
theorem agreement_row1 : elabLFFormAt ([] : Owner) row1 = elabMFormAt [] row1 :=
  agreement (by decide +kernel) (by decide +kernel)

/-- **The condition is needed**: row 4 has a refining pattern, the two
elaborations differ, and so do the answers. -/
theorem agreement_negative :
    refining [] row4 ≠ [] ∧ elabLFFormAt ([] : Owner) row4 ≠ elabMFormAt [] row4 ∧
      ansLFI clauses row4 ≠ ansMI clauses row4 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The identity model against the slot model -/

/-- **The identity model reproduces the slot model.**  On all 80 rows, the
identity-based elaborations answer, printed with each bag's naming, exactly
what `SpectrumCorpus.ans` answers under rule M and under lexical fresh (the
slot model of the exported reference, whose `let`s are activations). -/
theorem identity_matches_slots :
    rows.all (fun r =>
      decide (printedI (ansMI r.clauseSet.cl r.src) = printedS (SpectrumCorpus.ans cfgM r.clauseSet.cl r.src)) &&
      decide (printedI (ansLFI r.clauseSet.cl r.src) =
        printedS (SpectrumCorpus.ans cfgLF r.clauseSet.cl r.src))) = true := by
  decide +kernel

/-- **The translation in the slot model.**  The slot model's lexical-fresh
configuration (activation per `let` and per `new` block) runs every translated
row to the printed bag that rule M gives the source. -/
theorem slot_model_translation :
    rows.all (fun r =>
      decide (printedS (SpectrumCorpus.ans cfgLF (clT r.clauseSet.cl) (toLexical r.src)) =
        printedS (SpectrumCorpus.ans cfgM r.clauseSet.cl r.src))) = true := by
  decide +kernel

/-! ## The cone law on the corpus -/

/-- **Lexical fresh never overwrites a slot**: on every program and query it
elaborates, every binding of the initial store survives in every result store
(the 8/07 cone law, `run_preserves_binding`). -/
theorem lexicalFresh_never_overwrites (cl : Sy → Option A) (t : A) (d : Disc) (n : ℕ) (π : Path)
    (σ : GStore Sy (BId Sp)) {L : Result Sy (BId Sp)}
    (h : run d (progLF .u .unit cl) n π σ (elabLFFormAt [] t) = some L)
    {x : TI × GStore Sy (BId Sp)} (hx : x ∈ L) {k : Nm (BId Sp)} {g : GVal Sy (BId Sp)}
    (hk : σ k = some g) : x.2 k = some g :=
  run_preserves_binding d _ h hx hk

/-- The slot of row 23c's outer `let`, and of its inner `let`. -/
def outerY : Nm (BId Sp) := .src (.slot ⟨.y, [], [], .pat⟩)
def innerY : Nm (BId Sp) := .src (.slot ⟨.y, [], [2, 1], .pat⟩)

/-- **Shadowing is not overwriting.**  Row 23c,
`(let $y 1 (Pair $y (let $y 2 $y)))`: lexical fresh gives the inner pattern a
new slot, so the final store keeps `$y = 1` beside the inner `$y = 2`, and the
answer is `(Pair 1 2)`.  Rule M gives both one slot, and the second equation
conflicts: no answer.  The 8/07 shadow step on one key would instead
overwrite `1` (`shadow_breaks_cone`). -/
theorem shadowing_is_not_overwriting :
    ((run .static (progLF .u .unit clauses) 80 [] Store.empty (elabLFFormAt [] row23c)).getD []).any
        (fun x => decide (x.2 outerY = some (.sym .n1)) && decide (x.2 innerY = some (.sym .n2))) = true ∧
      ansLFI clauses row23c = some [pairI (kI .n1) (kI .n2)] ∧
      ansMI clauses row23c = some [] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **A crossing set refines** (8/07 refinement on an existing slot): row 23cs
shares `$y` with the outside, `(let $y 2 $y){$y}`, so the inner pattern refines
the outer slot and the conflict leaves no answer; with `{}` (row 23cf) it is
fresh and the answer is `(Pair 1 2)`, under both options. -/
theorem crossing_refines :
    ansLFI clauses row23cs = some [] ∧ ansMI clauses row23cs = some [] ∧
      ansLFI clauses row23cf = some [pairI (kI .n1) (kI .n2)] ∧
      ansMI clauses row23cf = some [pairI (kI .n1) (kI .n2)] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Export -/

/-- Positions and names as JSON. -/
def censusJson (l : List (Owner × Sp)) : Json :=
  .arr (l.map fun e => Json.mkObj [("position", natsJson e.1), ("name", .str ("$" ++ spText e.2))]).toArray

/-- A program's text: the equations its query reaches, then the query. -/
def programTextOf (cl : Sy → Option A) (t : A) : String :=
  let reach := reachable cl t
  let eqs := allSy.filterMap fun F =>
    if F ∈ reach then (cl F).map fun b => text (printClause F b) else none
  String.intercalate "\n" (eqs ++ ["!" ++ text (printSrc t)]) ++ "\n"

/-- The census of the equations a query reaches, with their translations. -/
def equationsJson (cl : Sy → Option A) (t : A) : Json :=
  .arr (allSy.filterMap fun F =>
    if F ∈ reachable cl t then
      (cl F).map fun b => Json.mkObj [
        ("equation", .str (symText F)),
        ("refining", censusJson (refining [5] b)),
        ("unintroduced", censusJson (unintroduced [5] b)),
        ("translated", .str (text (printClause F (toLexicalAt [5] b))))]
    else none).toArray

/-- The record of a row. -/
def rowRecord (group : String) (r : Row) : Json :=
  let cl := r.clauseSet.cl
  Json.mkObj [
    ("row", .str r.id),
    ("group", .str group),
    ("clauses", .str r.clauseSet.lean),
    ("probes", .str r.probes),
    ("program", .str (programText r)),
    ("translated_program", .str (programTextOf (clT cl) (toLexical r.src))),
    ("census_empty", .bool (censusEmpty r)),
    ("query_census", Json.mkObj [
      ("refining", censusJson (refining [] r.src)),
      ("unintroduced", censusJson (unintroduced [] r.src))]),
    ("equation_census", equationsJson cl r.src),
    ("bags", Json.mkObj [
      ("M", .str (bagTextP (printedI (ansMI cl r.src)))),
      ("LF", .str (bagTextP (printedI (ansLFI cl r.src)))),
      ("LF_of_translation", .str (bagTextP (printedI (ansLFI (clT cl) (toLexical r.src))))),
      ("slot_model_M", .str (bagTextP (printedS (SpectrumCorpus.ans cfgM cl r.src)))),
      ("slot_model_LF", .str (bagTextP (printedS (SpectrumCorpus.ans cfgLF cl r.src)))),
      ("slot_model_LF_of_translation",
        .str (bagTextP (printedS (SpectrumCorpus.ans cfgLF (clT cl) (toLexical r.src)))))])]

/-- **The export of the corpus translations.** -/
def exportJson : Json :=
  Json.mkObj [
    ("schema", .str "scope-lexical-fresh-translations/1"),
    ("source", Json.mkObj [
      ("module", .str "Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus"),
      ("export", .str "LexicalFreshCorpus.exportJson, written by scripts/ExportLexicalFreshTranslations.lean"),
      ("theorems", strsJson [
        "LexicalFresh.elabLFFormAt_toLexicalAt: lexical fresh elaborates the translation to the term rule M elaborates the source to",
        "LexicalFresh.run_toLexical: hence the same bag of results with final stores, at every fuel, path, store and discipline",
        "LexicalFresh.agreement, run_agreement: with an empty census the translation is the identity and the two options agree",
        "LexicalFreshCorpus.identity_matches_slots: the identity model's bags print as the slot model's on all 80 rows",
        "LexicalFreshCorpus.slot_model_translation: the slot model's LF runs every translated row to rule M's printed bag",
        "LexicalFreshCorpus.census_table, equation_census: the censuses below"])]),
    ("notation", Json.mkObj [
      ("translated_program", .str "the source with a crossing set {...} on every refining pattern and (new ($h ...) body) around every lambda body with un-introduced names; equations are translated as forms of their own"),
      ("refining", .str "a plain let (by position in its form) and a pattern name lexical fresh would make fresh where rule M refines a slot that it does not introduce there"),
      ("unintroduced", .str "a lambda (by position) and a name it owns by rule M that occurs in its body and has no covering pattern: a plain let at the lambda's level that writes the name in its pattern, may introduce it, and holds every occurrence of the slot"),
      ("positions", .str "child indices from the form's root: a lambda's body 0; an application's function 0 and argument 1; a let's pattern 0, value 1, body 2; alternatives 0 and 1; a new block is transparent"),
      ("bags", .str "M and LF are the identity model (binder identities, LexicalFresh); slot_model_* are SpectrumCorpus.ans (the exported reference model); names print as in scope-spectrum-lean-reference.json")]),
    ("rows", .arr ((corpus.map (rowRecord "corpus")) ++ (extras.map (rowRecord "criteria"))).toArray)]

/-- The export as text. -/
def exportText : String := exportJson.pretty ++ "\n"

end Mettapedia.GSLT.LanguageDef.TemplateScope.LexicalFreshCorpus
