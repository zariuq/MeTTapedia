import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
import Mettapedia.GSLT.LanguageDef.TemplateScope.Query

/-!
# Template scope: the query rules on the spectrum corpus

The rows of `TemplateScope.SpectrumCorpus` (lambdas, `let`, templates,
equations; no queries) under the rules of `TemplateScope.Query`, elaborated
under lexical fresh.

* `ansR_eq_LF` — every rule whose lambdas are not `clause` answers every row
  exactly as lexical fresh: the criteria proved for lexical fresh in
  `SpectrumCorpus` (`crit1_matrix` … `crit8_matrix`) hold for `H0`, `H1`, `H2`
  and `H2q` unchanged.
* `cu_agrees` and `cu_differs` — clause units (`ruleCU`) answer as lexical
  fresh on every row but the ten where a lambda or template uses a name that
  no enclosing binder introduced (rows 7, 8, 7u, 8u, 9u, 12a, 12au, H1, H2,
  4u): there the lambda owns it, as under explicit capture.
* `cu_criteria` — clause units keep criteria 1, 2 (inlining, without listing
  `$f`), 3 and 5 with a crossing set, 4 (modularity), 6, 7 and 8.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCriteria

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

/-- The program of a rule: each clause translated by the rule, then elaborated
under lexical fresh. -/
def progR (r : QRule) (cl : Sy → Option A) : Sy → Option T :=
  fun F => (cl F).map fun body => clauseOf cfgLF [5] .u .unit (QSrc.toSrc r [] (QSrc.ofSrc body))

/-- Answers of a spectrum row under a rule. -/
def ansR (r : QRule) (cl : Sy → Option A) (t : A) : Option (List T) :=
  answersCfg cfgLF (progR r cl) 80 (QSrc.toSrc r [] (QSrc.ofSrc t))

/-- **Conservativity on the corpus.**  A rule whose lambdas are not `clause`
answers every spectrum row, with every clause set, exactly as lexical fresh. -/
theorem ansR_eq_LF {r : QRule} (hr : r.lam ≠ .clause) (cl : Sy → Option A) (t : A) :
    ansR r cl t = ans cfgLF cl t := by
  have hp : progR r cl = progOf cfgLF cl := by
    funext F
    simp only [progR, progOf, QSrc.toSrc_ofSrc hr]
  simp only [ansR, ans, hp, QSrc.toSrc_ofSrc hr]

/-- Outsider invariance under a rule (criterion 4). -/
def outsiderInvariantR (r : QRule) (t tw : A) : Bool :=
  decide ((ansR r clauses t).map (List.map (renameQ .y .w)) = ansR r clauses tw)

/-- The rows on which clause units answer as lexical fresh. -/
def cuSameRows : List A :=
  [row1, row2, row3, row4, row4w, row5, row5w, row6, row6w, row7ec, row8ec, row9, row9w,
    row10a, row10b, row11, row11i, row11h, row11ec, row12b, row12bu, row12aec, row12bec,
    row13a, row13b, rowmk2, row14, row16, row18, row22a, row22b, row23a, row23b, row23c,
    row23cu, rowLfEq, row4ec, row4L2, row17eq]

/-- The rows on which a lambda or template uses a name that no enclosing
binder introduced. -/
def cuOwnRows : List A := [row7, row8, row7u, row8u, row9u, row12a, row12au, rowH1, rowH2, row4u]

/-- **Clause units agree with lexical fresh** on every row of `cuSameRows`. -/
theorem cu_agrees :
    cuSameRows.all (fun t => same (ansR ruleCU clauses t) (ans cfgLF clauses t)) = true := by
  decide +kernel

/-- **Clause units differ from lexical fresh** on every row of `cuOwnRows`; on
rows 9u, H2 and 4u they answer as explicit capture. -/
theorem cu_differs :
    cuOwnRows.all (fun t => !same (ansR ruleCU clauses t) (ans cfgLF clauses t)) = true ∧
    [row9u, rowH2, row4u].all (fun t => same (ansR ruleCU clauses t) (ans cfgEC clauses t)) =
      true := by
  decide +kernel

/-- **The criteria under clause units.**  Criterion 1 (row 4 against the
lifted equation of row 17); criterion 2 (side by side, hygienic, and as text,
without listing `$f`); criterion 3 with the crossing set (rows 7ec/8ec);
criterion 4 (outsiders and renaming); criterion 5 with the crossing set (row
14 answers `(Pair 7 ok)`, while row 9u, refining by `unify` without it, does
not); criteria 6, 7 and 8 as lexical fresh (`cu_agrees`). -/
theorem cu_criteria :
    same (ansR ruleCU clauses row4) (ansR ruleCU clauses row17eq) = true ∧
    same (ansR ruleCU clauses row1) (ansR ruleCU clauses row2) = true ∧
    same (ansR ruleCU clauses row11) (ansR ruleCU clauses row11h) = true ∧
    same (ansR ruleCU clauses row11) (ansR ruleCU clauses row11i) = true ∧
    same (ansR ruleCU clauses row7ec) (ansR ruleCU clauses row8ec) = true ∧
    outsiderInvariantR ruleCU row4 row4w = true ∧
    outsiderInvariantR ruleCU row5 row5w = true ∧
    outsiderInvariantR ruleCU row6 row6w = true ∧
    same (ansR ruleCU clauses row4) (ansR ruleCU clauses row4L2) = true ∧
    same (ansR ruleCU clauses row14) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ansR ruleCU clauses row9u) (some [pairT (kT .n7) (kT .ok)]) = false := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCriteria
