import Mathlib.Tactic

/-!
# `cons` in PeTTa: code builds cells, data stays data

SWI-PeTTa runs on Prolog terms: a MeTTa expression `(x1 ... xn)` is the
Prolog list `[x1, ..., xn]`, built from cells `[H|T]` ending in `[]`.  Its
translator reads a written `(cons H T)` in a pattern as the cell `[H|T]`;
stored atoms are not translated, so a stored `(cons a b)` is the
three-element list `[cons, a, b]`.

CeTTa holds expressions as sequences, and a cell whose tail is no list as a
tagged cell.  This file relates the two readings:
* `ofValue`: what a CeTTa value is as a Prolog term (a written `cons` is
  data, an expression);
* `ofPattern`: what SWI-PeTTa's translator makes of a pattern (a written
  `cons` is a cell);
* `lower`: CeTTa's replacement of a pattern's written `cons` by cells, used
  when a value's variable is bound to pattern syntax.

Proved:
* `ofValue_lower`: the lowered pattern, read as a value, is the term the
  translator makes of the pattern, so a variable bound to it holds what
  SWI-PeTTa would bind;
* `ofPattern_eq_ofValue`: a pattern that writes no `cons` reads the same
  either way;
* `spelled_ne_cell`: a stored `(cons a b)` and the cell `[a|b]` are
  different terms, which is the distinction that reading values honestly
  keeps;
* `cell_text_reads_as_data`: the text a cell prints as, `(cons a b)`, reads
  back as data, so print and read do not round-trip on cells (as in
  SWI-PeTTa).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PeTTaConsAsData

/-- Prolog terms: atoms, variables, the empty list and cells. -/
inductive PT
  | atom (s : ℕ)
  | var (x : ℕ)
  | nil
  | cell (h t : PT)
  deriving DecidableEq

/-- CeTTa terms: symbols, variables, expressions and tagged cells. -/
inductive CT
  | sym (s : ℕ)
  | var (x : ℕ)
  | expr (xs : List CT)
  | tcell (h t : CT)

/-- The symbol `cons`. -/
def consSym : ℕ := 0

/-- A Prolog list of the given elements. -/
def plist : List PT → PT
  | [] => .nil
  | x :: xs => .cell x (plist xs)

mutual
/-- A CeTTa value as a Prolog term: expressions are lists, tagged cells are
cells, and a written `cons` is an ordinary expression. -/
def ofValue : CT → PT
  | .sym s => .atom s
  | .var x => .var x
  | .expr xs => ofValues xs
  | .tcell h t => .cell (ofValue h) (ofValue t)

def ofValues : List CT → PT
  | [] => .nil
  | x :: xs => .cell (ofValue x) (ofValues xs)
end

mutual
/-- A pattern as SWI-PeTTa's translator reads it: a written `(cons H T)`
is the cell `[H|T]`. -/
def ofPattern : CT → PT
  | .sym s => .atom s
  | .var x => .var x
  | .expr [.sym s, h, t] =>
      if s = consSym then .cell (ofPattern h) (ofPattern t)
      else .cell (.atom s) (.cell (ofPattern h) (.cell (ofPattern t) .nil))
  | .expr xs => ofPatterns xs
  | .tcell h t => .cell (ofPattern h) (ofPattern t)

def ofPatterns : List CT → PT
  | [] => .nil
  | x :: xs => .cell (ofPattern x) (ofPatterns xs)
end

mutual
/-- CeTTa's lowering of pattern syntax: each written `(cons H T)` becomes the
tagged cell. -/
def lower : CT → CT
  | .sym s => .sym s
  | .var x => .var x
  | .expr [.sym s, h, t] =>
      if s = consSym then .tcell (lower h) (lower t)
      else .expr [.sym s, lower h, lower t]
  | .expr xs => .expr (lowers xs)
  | .tcell h t => .tcell (lower h) (lower t)

def lowers : List CT → List CT
  | [] => []
  | x :: xs => lower x :: lowers xs
end

mutual
theorem ofValue_lower : ∀ p : CT, ofValue (lower p) = ofPattern p
  | .sym s => rfl
  | .var x => rfl
  | .expr [] => rfl
  | .expr [x] => by
      simp [lower, lowers, ofValue, ofValues, ofPattern, ofPatterns, ofValue_lower x]
  | .expr [.sym s, h, t] => by
      by_cases hs : s = consSym
      · simp [lower, ofPattern, hs, ofValue, ofValue_lower h, ofValue_lower t]
      · simp [lower, ofPattern, hs, ofValue, ofValues, ofValue_lower h, ofValue_lower t]
  | .expr [.var x, h, t] => by
      simp [lower, lowers, ofValue, ofValues, ofPattern, ofPatterns,
        ofValue_lower h, ofValue_lower t]
  | .expr [.expr ys, h, t] => by
      have e := ofValue_lower (.expr ys)
      simp only [lower, lowers, ofValue, ofValues, ofPattern, ofPatterns] at e ⊢
      rw [e, ofValue_lower h, ofValue_lower t]
  | .expr [.tcell a b, h, t] => by
      simp [lower, lowers, ofValue, ofValues, ofPattern, ofPatterns,
        ofValue_lower a, ofValue_lower b, ofValue_lower h, ofValue_lower t]
  | .expr (x :: y :: z :: w :: rest) => by
      have e := ofValues_lowers (x :: y :: z :: w :: rest)
      simp only [lower, ofValue, ofPattern]
      exact e
  | .expr [x, y] => by
      simp [lower, lowers, ofValue, ofValues, ofPattern, ofPatterns,
        ofValue_lower x, ofValue_lower y]
  | .tcell h t => by
      simp [lower, ofValue, ofPattern, ofValue_lower h, ofValue_lower t]

theorem ofValues_lowers : ∀ xs : List CT, ofValues (lowers xs) = ofPatterns xs
  | [] => rfl
  | x :: xs => by
      simp [lowers, ofValues, ofPatterns, ofValue_lower x, ofValues_lowers xs]
end

/-- A pattern its lowering leaves as it is (it writes no `cons`) reads the
same as pattern and as value. -/
theorem ofPattern_eq_ofValue (p : CT) (h : lower p = p) :
    ofPattern p = ofValue p := by
  rw [← ofValue_lower, h]

/-- The size of a Prolog term. -/
def PT.size : PT → ℕ
  | .atom _ => 1
  | .var _ => 1
  | .nil => 1
  | .cell h t => 1 + h.size + t.size

/-- A stored `(cons a b)` is the three-element list `[cons, a, b]`, never the
cell `[a|b]`. -/
theorem spelled_ne_cell (a b : CT) :
    ofValue (.expr [.sym consSym, a, b]) ≠ ofValue (.tcell a b) := by
  intro h
  have := congrArg PT.size h
  simp [ofValue, ofValues, PT.size] at this
  omega

mutual
/-- What reading a value's printed text gives back: a cell prints as
`(cons H T)`, which reads as that expression. -/
def viaText : CT → CT
  | .sym s => .sym s
  | .var x => .var x
  | .expr xs => .expr (viaTexts xs)
  | .tcell h t => .expr [.sym consSym, viaText h, viaText t]

def viaTexts : List CT → List CT
  | [] => []
  | x :: xs => viaText x :: viaTexts xs
end

/-- The text of a cell reads back as data, not as the cell: print and read do
not round-trip on cells, as in SWI-PeTTa. -/
theorem cell_text_reads_as_data (a b : CT) :
    ofValue (viaText (.tcell a b)) ≠ ofValue (.tcell (viaText a) (viaText b)) := by
  simpa [viaText] using spelled_ne_cell (viaText a) (viaText b)

end Mettapedia.Machines.PeTTaConsAsData
