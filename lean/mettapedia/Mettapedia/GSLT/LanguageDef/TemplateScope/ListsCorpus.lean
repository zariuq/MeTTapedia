import Mettapedia.GSLT.LanguageDef.TemplateScope.Lists
import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

/-!
# Template scope, part 9: lexical inventory, stored lists, criterion 10

* `ansP_M`, `ansP_EC`, `ansP_Q`, `ansP_LF` — the profile representation
  reproduces the four ownership configurations exactly; lexical inventory
  (i) is explicit capture and (i') is rule M (`profLIi`, `profLIc`).
* Lexical inventory (ii), explicit introduction, on the corpus: crossing sets
  over query-wide's default (`ansII_eq_Q`), the mirror image of explicit
  capture.  A crossing spelling connects without annotation (row 9), and a
  private name needs a crossing set that leaves it out (rows 1, 4).
* `written_override_matrix` — a crossing set overrides the default under
  every configuration: `L{}` is private under rule M too (row 4ii), `L{$y}`
  shares its `$y` everywhere (row 1s), `K{}` owns its `$y` everywhere (row 7a),
  and a `let` with `{}` is fresh, with `{$y}` refining, under all six (rows
  23cf, 23cs).
* `metadata_determines_meaning` — M and explicit capture store the same lists
  on rows 1 and 14, so the general theorem `answers_eq_of_agree` gives equal
  observations; on row 4 they store different lists and differ.
* `region_names_both` — for names introduced by a region (clause head
  variables constrained by a body `let`, a slot constrained twice), lexical
  inventory refines implicitly and stays modular; `crossing_needs_rule` —
  for a spelling crossing a lambda boundary, (i) needs the shared list and
  (ii) needs a crossing set that leaves the private name out.
* Criterion 10 (rows 24–28): `crit10_matrix`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

/-- A query elaborated under a profile: the query quantifies what it writes
directly. -/
def elabTopWith (P : Profile Sy Sp) (t : A) : T := elabWith P (Src.direct t) [] (fun _ => []) [] t

/-- An equation clause elaborated under a profile, as `clauseOf` does. -/
def clauseWith (P : Profile Sy Sp) (body : A) : T :=
  .app (.lam (.src ([5] ++ [9], .u)) ((rootSpellings body).map fun m => ([5], m))
      (elabWith P (Src.direct body) [] (fun _ => [5]) [5] body))
    (.sym .unit)

/-- The program of a profile. -/
def progP (P : Profile Sy Sp) (cl : Sy → Option A) : Sy → Option T :=
  fun F => (cl F).map (clauseWith P)

/-- Answers under a profile and a readout. -/
def ansP (P : Profile Sy Sp) (d : Disc) (cl : Sy → Option A) (t : A) : Option (List T) :=
  answers d (progP P cl) 80 (elabTopWith P t)

/-! ## The profiles reproduce the configurations -/

theorem ansP_M (cl : Sy → Option A) (t : A) : ansP profM .static cl t = ans cfgM cl t := by
  have hprog : progP profM cl = progOf cfgM cl := by
    funext F
    simp only [progP, progOf]
    cases cl F with
    | none => rfl
    | some body =>
        simp only [Option.map_some, clauseWith, clauseOf, elabCfgX, elabCfg, cfgM, elabForm,
          List.append_nil]
        rw [elabMS_eq body (Src.direct body) []]
  simp only [ansP, ans, answersCfg, hprog, elabTopWith, elabCfg, elabCfgX, cfgM, elabForm,
    Config.disc]
  rw [elabMS_eq t (Src.direct t) []]

theorem ansP_EC (cl : Sy → Option A) (t : A) : ansP profEC .static cl t = ans cfgEC cl t := by
  have hprog : progP profEC cl = progOf cfgEC cl := by
    funext F
    simp only [progP, progOf]
    cases cl F with
    | none => rfl
    | some body =>
        simp only [Option.map_some, clauseWith, clauseOf, elabCfgX, elabCfg, cfgEC, elabForm,
          List.append_nil]
        rw [elabEC_eq body (Src.direct body) []]
  simp only [ansP, ans, answersCfg, hprog, elabTopWith, elabCfg, elabCfgX, cfgEC, elabForm,
    Config.disc]
  rw [elabEC_eq t (Src.direct t) []]

theorem ansP_Q (cl : Sy → Option A) (t : A) : ansP profQ .static cl t = ans cfgQ cl t := by
  have hprog : progP profQ cl = progOf cfgQ cl := by
    funext F
    simp only [progP, progOf]
    cases cl F with
    | none => rfl
    | some body =>
        simp only [Option.map_some, clauseWith, clauseOf, elabCfgX, elabCfg, cfgQ, elabForm,
          List.append_nil]
        rw [elabQ_eq body (Src.direct body) [] (fun _ => [5]) [5]]
  simp only [ansP, ans, answersCfg, hprog, elabTopWith, elabCfg, elabCfgX, cfgQ, elabForm,
    Config.disc]
  rw [elabQ_eq t (Src.direct t) [] (fun _ => []) []]

theorem ansP_LF (cl : Sy → Option A) (t : A) : ansP profLF .static cl t = ans cfgLF cl t := by
  have hprog : progP profLF cl = progOf cfgLF cl := by
    funext F
    simp only [progP, progOf]
    cases cl F with
    | none => rfl
    | some body =>
        simp only [Option.map_some, clauseWith, clauseOf, elabCfgX, elabCfg, cfgLF, elabForm,
          List.append_nil]
        rw [elabLF_eq body (Src.direct body)]
  simp only [ansP, ans, answersCfg, hprog, elabTopWith, elabCfg, elabCfgX, cfgLF, elabForm,
    Config.disc]
  rw [elabLF_eq t (Src.direct t)]

/-! ## Lexical inventory (ii): explicit introduction -/

/-- `L` sharing nothing, `(lam z (let $y z (g $y))){}`: it owns `$y`. -/
def Lii : A := lsh .z [] (lt .y (pr .z) (ap (k .g) (sv .y)))

/-- The equations, with `mk` returning `Lii`. -/
def clausesII : Sy → Option A
  | .mk => some Lii
  | F => clauses F

/-- Answers under explicit introduction. -/
def ansII (cl : Sy → Option A) (t : A) : Option (List T) := ansP profLIii .static cl t

/-- Explicit introduction is query-wide's default with the crossing sets the
program writes: crossing sets override under every profile. -/
theorem ansII_eq_Q (cl : Sy → Option A) (t : A) : ansII cl t = ans cfgQ cl t := ansP_Q cl t

/-- Lexical inventory (ii) on the corpus.  With no list, `L`'s `$y` refers
outward: the calls share it (row 1) and an outsider captures it (row 4).
With `{}`, `L` owns `$y`: it is private and independent (rows 1, 4, 5, 6), the library
closure keeps its slot, and the crossing hole of row 9 connects with no
annotation. -/
theorem lexicalInventory_ii :
    same (ansII clauses row1) (some []) = true ∧
    same (ansII clauses row4) (some [pairT (gT (kT .n1)) (kT .n1)]) = true ∧
    same (ansII clauses (lt .f Lii (pair f1 f2)))
      (some [pairT (gT (kT .n1)) (gT (kT .n2))]) = true ∧
    same (ansII clauses (lt .f Lii (pair f1 (sv .y))))
      (some [pairT (gT (kT .n1)) (qv .y)]) = true ∧
    same (ansII clauses (lt .y (k .n5) (lt .f Lii f1))) (some [gT (kT .n1)]) = true ∧
    same (ansII clauses (lt .f Lii (pair f1 (lt .y (k .n5) (sv .y)))))
      (some [pairT (gT (kT .n1)) (kT .n5)]) = true ∧
    same (ansII clauses row9) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ansII clausesII row13a) (some [pairT (gT (kT .n1)) (gT (kT .n2))]) = true ∧
    same (ansII clausesII row13b) (some [pairT (gT (kT .n1)) (kT .n5)]) = true := by
  decide +kernel

/-! ## Elaborated metadata determines meaning, on the corpus -/

/-- M and explicit capture store the same lists on row 1 (`L` owns `$y` in
both) and on row 14 (M infers the capture that row 14 writes), so their
observations agree by `answers_eq_of_agree`.  On row 4 they store different
lists (M captures `$y`, explicit capture keeps it apart) and differ. -/
theorem metadata_determines_meaning :
    agree profM profEC (Src.direct row1) [] row1 = true ∧
    agree profM profEC (Src.direct row14) [] row14 = true ∧
    agree profM profEC (Src.direct row4) [] row4 = false ∧
    same (ans cfgM clauses row4) (ans cfgEC clauses row4) = false := by
  decide +kernel

/-- The general theorem, applied to row 1: same lists, same observation, for
every readout, program and fuel. -/
theorem row1_M_EC_same (d : Disc) (prog : Sy → Option T) (n : ℕ) :
    answers d prog n (elabWith profM (Src.direct row1) [] (fun _ => []) [] row1) =
      answers d prog n (elabWith profEC (Src.direct row1) [] (fun _ => []) [] row1) :=
  answers_eq_of_agree profM profEC row1 _ _ _ _ (by decide +kernel) d prog n

/-! ## Lexical inventory: region names and crossing spellings -/

/-- **Names introduced by a region keep both properties.**  Under lexical
inventory (i) (= explicit capture): the clause region introduces its head
variables and the body `let` constrains them implicitly, refining the
caller (row 22 with no `unify`, which is row 24), with the conflict of
row 22b; a slot constrained twice in one region conflicts (row 23c); and the
region's own names are immune to same-spelled outsiders (rows 4–6). -/
theorem region_names_both :
    same (ansP profLIi .static clauses row22a)
      (some [pairT (kT .cb) (apT (kT .Got) (kT .cb))]) = true ∧
    same (ansP profLIi .static clauses row22b) (some []) = true ∧
    same (ansP profLIi .static clauses row23c) (some []) = true ∧
    same (ansP profLIi .static clauses row5) (ansP profLIi .static clauses row5w) = true ∧
    same (ansP profLIi .static clauses row6) (ansP profLIi .static clauses row6w) = true := by
  decide +kernel

/-- **A crossing spelling needs a boundary rule.**  Row 9's `$t` crosses the
lambda boundary.  Inventory (i) keeps it apart unless shared (rows 9, 14);
inventory (ii) connects it unless a crossing set leaves it out; connecting by spelling
(i' = M) refines it but lets an outsider capture `L`'s `$y` (row 4). -/
theorem crossing_needs_rule :
    same (ansP profLIi .static clauses row9) (some [pairT (qv .t) (kT .ok)]) = true ∧
    same (ansP profLIi .static clauses row14) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ansII clauses row9) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ansII clauses (progV .t)) (ansII clauses row9) = true ∧
    same (ansP profLIc .static clauses row9) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ansP profLIc .static clauses row4) (some [pairT (gT (kT .n1)) (kT .n1)]) = true := by
  decide +kernel

/-! ## Criterion 10: connecting power and annotation burden -/

/-- Row 25: two private same-spelled locals, and one connected pair.  The
connecting lambda is written per profile. -/
def row25 (Lp Kc : A) : A :=
  pair (pair (ap Lp (k .n1)) (ap Lp (k .n2))) (lt .f Kc (lt .r (ap (sv .f) (k .n3))
    (pair (sv .r) (sv .t))))

/-- A private local. -/
def Lp : A := lm .z (lt .y (pr .z) (sv .y))
/-- The private local, its `$y` owned under the crossing set `{}`. -/
def LpII : A := lsh .z [] (lt .y (pr .z) (sv .y))
/-- The connecting lambda, unannotated. -/
def Kc : A := lm .z (lt .t (pr .z) (k .ok))
/-- The connecting lambda, sharing `$t` by its crossing set. -/
def KcEC : A := lsh .z [.t] (lt .t (pr .z) (k .ok))
/-- The connecting lambda, by `unify` (lexical fresh). -/
def KcLF : A := lm .z (un .t (pr .z) (k .ok))

/-- Row 9 with the lambda sharing nothing, `(lam z (let (d $t) z ok)){}`: it
owns `$t`. -/
def row9ii : A := lt .f (lsh .z [] (.letS (ap (k .d) (sv .t)) (pr .z) (k .ok) none))
  (lt .r (ap (sv .f) (ap (k .d) (k .n7))) (pair (sv .t) (sv .r)))

/-- The answer of row 25 that keeps the locals apart and connects the pair. -/
def row25goal : Option (List T) :=
  some [pairT (pairT (kT .n1) (kT .n2)) (pairT (kT .ok) (kT .n3))]

/-- Row 26: two candidate associations kept open as alternatives. -/
def row26 (connected apart : A) : A := .alt connected apart

/-- Row 28: the already elaborated closure of `(mk)`, extended with a
same-spelled outsider; it is not re-elaborated. -/
def row28 : A := lt .f (.fn .mk) (pair f1 (sv .y))

/-- **Criterion 10.**
* Row 24 (implicit caller refinement through `let`): every profile but
  lexical fresh.
* Row 25: M and explicit capture keep the locals apart and connect the pair
  with no list in M and the shared `$t` in explicit capture; lexical fresh
  needs `unify`; explicit introduction needs `{}` on the private local;
  query-wide cannot keep the locals apart.
* Row 26: both associations stay open as alternatives (one answer each) in
  explicit capture, lexical fresh and explicit introduction; under M the
  same-spelled "apart" branch connects as well.
* Row 27 (a built closure connected to a later binding): rows 7–8 under M,
  with the list under explicit capture, `unify` under lexical fresh; not
  under snapshot.
* Row 28: extending the authored query re-elaborates and M captures (row 4);
  extending the built closure of `(mk)` does not. -/
theorem crit10_matrix :
    same (ans cfgM clauses row22a) (some [pairT (kT .cb) (apT (kT .Got) (kT .cb))]) = true ∧
    same (ans cfgEC clauses row22a) (ans cfgM clauses row22a) = true ∧
    same (ansII clauses row22a) (ans cfgM clauses row22a) = true ∧
    same (ans cfgLF clauses row22a) (ans cfgM clauses row22a) = false ∧
    same (ans cfgM clauses (row25 Lp Kc)) row25goal = true ∧
    same (ans cfgEC clauses (row25 Lp KcEC)) row25goal = true ∧
    same (ans cfgEC clauses (row25 Lp Kc)) row25goal = false ∧
    same (ans cfgLF clauses (row25 Lp KcLF)) row25goal = true ∧
    same (ans cfgLF clauses (row25 Lp Kc)) row25goal = false ∧
    same (ansII clauses (row25 LpII Kc)) row25goal = true ∧
    same (ansII clauses (row25 Lp Kc)) row25goal = false ∧
    same (ans cfgQ clauses (row25 Lp Kc)) (some []) = true ∧
    same (ans cfgEC clauses (row26 row14 row9))
      (some [pairT (kT .n7) (kT .ok), pairT (qv .t) (kT .ok)]) = true ∧
    same (ans cfgLF clauses (row26 row9u row9))
      (some [pairT (kT .n7) (kT .ok), pairT (qv .t) (kT .ok)]) = true ∧
    same (ansII clauses (row26 row9 row9ii))
      (some [pairT (kT .n7) (kT .ok), pairT (qv .t) (kT .ok)]) = true ∧
    same (ans cfgM clauses (row26 row9 row9))
      (some [pairT (kT .n7) (kT .ok), pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgM clauses row8) (some [pairT (kT .n1) (kT .n5)]) = true ∧
    same (ans cfgEC clauses row8ec) (some [pairT (kT .n1) (kT .n5)]) = true ∧
    same (ans cfgLF clauses row8u) (some [pairT (kT .n1) (kT .n5)]) = true ∧
    same (ans cfgSN clauses row7) (some [pairT (kT .n1) (kT .n5)]) = false ∧
    same (ans cfgM clauses row4) (some [pairT (gT (kT .n1)) (kT .n1)]) = true ∧
    same (ans cfgM clauses row28) (some [pairT (gT (kT .n1)) (qv .y)]) = true := by
  decide +kernel

/-! ## Lexical inventory (ii) on the criteria rows -/

/-- `lam w` of row 11, sharing only `$f`: it owns its `$y`. -/
def LiiW : A := lsh .w [.f] (pair f1 (lt .y (pr .w) (sv .y)))

/-- **Explicit introduction, criteria 2, 3, 7, 8, 5.**  With the private
names owned under crossing sets: inlining side by side (rows 1, 2) and with
hygiene (row 11 and its inlined text); independent calls (rows 3, 16, 18; row
16 without a crossing set shares its slot); order independence of capture with no
annotation (rows 7/8, 12a/12b); relational coherence (23a and 23c conflict in
one region slot, 23b keeps two activations apart); caller refinement through
an equation (row 22). -/
theorem lexicalInventory_ii_criteria :
    same (ansII clauses (pair (ap Lii (k .n1)) (ap Lii (k .n2))))
      (ansII clauses (lt .f Lii (pair f1 f2))) = true ∧
    same (ansII clauses (lt .f Lii (ap LiiW (k .n5))))
      (ansII clauses (ap (lsh .w [] (pair (ap Lii (k .n1)) (lt .y (pr .w) (sv .y))))
        (k .n5))) = true ∧
    same (ansII clauses (lt .f Lii (ap LiiW (k .n5))))
      (some [pairT (gT (kT .n1)) (kT .n5)]) = true ∧
    same (ansII clauses (lt .f Lii (pair f1 f1)))
      (some [pairT (gT (kT .n1)) (gT (kT .n1))]) = true ∧
    same (ansII clauses (lt .p (ap (lm .z (lsh .w [] (lt .y (pair (pr .z) (pr .w)) (sv .y))))
        (k .n1)) (pair (ap (sv .p) (k .n2)) (ap (sv .p) (k .n3)))))
      (some [pairT (pairT (kT .n1) (kT .n2)) (pairT (kT .n1) (kT .n3))]) = true ∧
    same (ansII clauses row16) (some []) = true ∧
    same (ansII clauses (lt .f Lii (lt .a f1 (pair (sv .a) (sv .a)))))
      (some [pairT (gT (kT .n1)) (gT (kT .n1))]) = true ∧
    same (ansII clauses row7) (ansII clauses row8) = true ∧
    same (ansII clauses row7) (some [pairT (kT .n1) (kT .n5)]) = true ∧
    same (ansII clauses row12a) (ansII clauses row12b) = true ∧
    same (ansII clauses row23a) (some []) = true ∧
    same (ansII clauses row23c) (some []) = true ∧
    same (ansII clauses (pair (ap Lii (k .n1)) (ap Lii (k .n2))))
      (some [pairT (gT (kT .n1)) (gT (kT .n2))]) = true ∧
    same (ansII clauses row22a) (some [pairT (kT .cb) (apT (kT .Got) (kT .cb))]) = true ∧
    same (ansII clauses row22b) (some []) = true := by
  decide +kernel

/-! ## A crossing set overrides the default under every configuration -/

/-- Row 4 with `L` sharing nothing:
`(let $f (lam z (let $y z (g $y))){} (Pair ($f 1) $y))`. -/
def row4ii : A := lt .f Lii (pair f1 (sv .y))

/-- Row 1 with `L` sharing its `$y`: `(lam z (let $y z (g $y))){$y}`. -/
def row1s : A := lt .f Lec (pair f1 f2)

/-- Row 7 with `K` sharing nothing: `(lam z (Pair z $y)){}`. -/
def row7a : A := lt .f (lsh .z [] (pair (pr .z) (sv .y))) (lt .r f1 (lt .y (k .n5) (sv .r)))

/-- Row 23c with the inner `let` fresh: `(let $y 1 (Pair $y (let $y 2 $y){}))`. -/
def row23cf : A := lt .y (k .n1) (pair (sv .y) (lts .y (k .n2) (sv .y) []))

/-- Row 23c with the inner `let` sharing `$y`:
`(let $y 1 (Pair $y (let $y 2 $y){$y}))`. -/
def row23cs : A := lt .y (k .n1) (pair (sv .y) (lts .y (k .n2) (sv .y) [.y]))

/-- Row 23c with both `let`s fresh: every construct carries a crossing set. -/
def row23cw : A := lts .y (k .n1) (pair (sv .y) (lts .y (k .n2) (sv .y) [])) []

/-- **A crossing set overrides the default under every configuration**, in the
order `[M, LF, EC, Q, PC, SN]`.
* `{}` on `L`: its `$y` is private under all six, rule M included (row 4
  without the set: M, Q and PC capture the outsider); `{}` on row 9's lambda:
  the hole stays apart under all six.
* `{$y}` on `L`: `L` owns nothing and no pattern inside makes `$y` fresh, so
  its two calls share `$y` and conflict under every ownership, lexical fresh
  included; only snapshot separates them, copying the unbound name at each
  call.
* `{}` on `K`: `K` owns `$y` under all six, so the later `$y := 5` does not
  reach it (row 7 without the set: M, Q, PC give `(Pair 1 5)`).
* On a `let`: `{}` makes the inner `$y` fresh under every configuration, as
  lexical fresh does by default; `{$y}` makes it refine the outer `$y`, as
  `unify` does, and the two constraints conflict under all six. -/
theorem written_override_matrix :
    six clauses row4ii = List.replicate 6 (some [pairT (gT (kT .n1)) (qv .y)]) ∧
    six clauses row9ii = List.replicate 6 (some [pairT (qv .t) (kT .ok)]) ∧
    six clauses row1s = [some [], some [], some [], some [], some [],
      some [pairT (gT (kT .n1)) (gT (kT .n2))]] ∧
    six clauses row7a = [some [pairT (kT .n1) (fv [0, 2] [1, 0] .y)],
      some [pairT (kT .n1) (fv [2, 1, 2] [1, 0] .y)], some [pairT (kT .n1) (fv [0, 2] [1, 0] .y)],
      some [pairT (kT .n1) (fv [0, 2] [1, 0] .y)], some [pairT (kT .n1) (.var (.src ([1, 0], .y)))],
      some [pairT (kT .n1) (fv [0, 2] [1, 0] .y)]] ∧
    six clauses row23cf = List.replicate 6 (some [pairT (kT .n1) (kT .n2)]) ∧
    six clauses row23cs = List.replicate 6 (some []) ∧
    same (ans cfgM clauses row4) (ans cfgM clauses row4ii) = false ∧
    same (ans cfgEC clauses row1) (ans cfgEC clauses row1s) = false ∧
    same (ans cfgM clauses row7) (ans cfgM clauses row7a) = false ∧
    same (ans cfgM clauses row23c) (ans cfgM clauses row23cf) = false ∧
    same (ans cfgLF clauses row23c) (ans cfgLF clauses row23cs) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Row 4ii is fully written, so rule M, explicit capture and query-wide
elaborate its query to the same term (`elabWith_fullyWritten_profile`), and
rule M's elaboration no longer reads the enclosing context
(`elabWith_fullyWritten_context`).  Row 23cw writes every construct's
crossing set, so even lexical fresh elaborates it as rule M does
(`elabWith_allWritten_profile`). -/
theorem written_profile_independent (E : List Sp) :
    elabTopWith profM row4ii = elabTopWith profEC row4ii ∧
    elabTopWith profM row4ii = elabTopWith profQ row4ii ∧
    elabWith profM E [] (fun _ => []) [] row4ii = elabTopWith profM row4ii ∧
    elabTopWith profM row23cw = elabTopWith profLF row23cw ∧
    six clauses row23cw = List.replicate 6 (some [pairT (kT .n1) (kT .n2)]) := by
  have hw : row4ii.FullyWritten = true := by decide
  have ha : row23cw.AllWritten = true := by decide
  refine ⟨elabWith_fullyWritten_profile _ _ (fun _ _ => rfl) _ _ _ _ _ hw,
    elabWith_fullyWritten_profile _ _ (fun _ _ => rfl) _ _ _ _ _ hw,
    elabWith_fullyWritten_context _ _ _ _ _ _ _ hw,
    elabWith_allWritten_profile _ _ _ _ _ _ _ ha, by decide +kernel⟩

/-! ## Lifetime as replication and restriction (remark)

Lybech (2024, section 4) separates `P₁ = !(ν z)u⟨z⟩`, a fresh name per
replica, from `P₂ = (ν z)!u⟨z⟩`, one name shared by all replicas.  The
lifetime axis is the same distinction, with a closure's calls as the
replicas.  Per call, the own binder stays on the lambda and every activation
renames it to the copy tagged by its own path (`activate_static_own`), so
two calls send different names, as in `P₁`.  Per closure, `hoistOwn` moves
the binder to the scope that creates the closure (`hoistOwn_lam`): the
restriction sits outside the replication, as in `P₂`, and all calls share
one name.  Row 1 separates them (`lifetime_separation`). -/

theorem activate_static_own (σ : GStore Sy (Slot Sp)) (ρ : Path) (x : Nm (Slot Sp))
    (own : List (Slot Sp)) (body arg : T) :
    activate .static σ ρ x own body arg = subst (renameOwn ρ own) (Sub.single x arg) body :=
  rfl

theorem hoistOwn_lam (x : Nm (Slot Sp)) (own : List (Slot Sp)) (b : T) :
    hoistOwn (Tm.lam x own b) = (Tm.lam x (hoistOwn b).2 (hoistOwn b).1, own) := rfl

/-- One closure called twice: per call, two independent names; per closure,
one shared name, whose two constraints conflict. -/
theorem lifetime_separation :
    same (ans cfgM clauses row1) (some [pairT (gT (kT .n1)) (gT (kT .n2))]) = true ∧
    same (ans cfgPC clauses row1) (some []) = true ∧
    same (ans cfgPC clauses row2) (some [pairT (gT (kT .n1)) (gT (kT .n2))]) = true := by
  decide +kernel

/-! ## Quotation -/

/-- **Quotation forgets what the model does not run.**  Sealed code is the
authored text read by `codeOf`, which keeps no crossing set and reads a `let`
and a `unify` alike.  The model has no operation that opens code, so no answer
depends on it; a lossless quotation needs code values that are authored
syntax. -/
theorem quotation_forgets_crossing :
    Lec ≠ L ∧ (codeOf Lec : T) = codeOf L ∧
    (codeOf (lts .y (k .n1) (sv .y) []) : T) = codeOf (un .y (k .n1) (sv .y)) := by
  decide

end Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus
