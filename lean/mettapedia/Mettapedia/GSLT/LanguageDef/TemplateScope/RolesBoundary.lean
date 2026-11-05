import Mettapedia.GSLT.LanguageDef.TemplateScope.RolesMeTTa

/-!
# Binding by role: the boundary checks and the open decisions

The second study of the scope question (Gödel's report of 2026-11-03 and its
specification candidate) left nine boundary checks and five open decisions,
A to E.  Here they are restated in the generic model.

## The nine checks

All nine programs lie in the fragment of `RolesMeTTa.inFragment`, so the
principle's signature answers them exactly as clause units do
(`godel_checks_are_CU`), with the values the study computed
(`godel_checks`).

## Decisions

* **A, introduction versus reference in `case`.**  The principle: a `case`
  pattern tests the names that binders on its path introduced and introduces
  the others; it never picks up an unknown of the frame implicitly.  Its
  reason is L4: `policyB_breaks_stability` shows the alternative (a pattern
  refers to frame unknowns written elsewhere in the frame, the study's inferred
  policy) lets an unrelated sibling query change what a `case` means — the
  product `(Pair query cases)` loses every answer — while the principle keeps
  the product (`principle_keeps_product`).  The cost: a `case` after a sibling
  query does not see that query's name (`case_after_cost`); `(new ($x) …)` or a
  crossing set `{$x}` correlates it.
* **B, capture across nested reusable units.**  The principle: a nested frame
  owns what it writes that no binder on its path introduced; the enclosing
  frame's unknowns are not binders.  Its reason is L4 again:
  `RolesLawsNecessity.not_L4_capture` (any signature with implicit nested
  capture) and `laws_iff`.  `QSrc.toSrc`'s lambda branch, which does not pass
  `unitNames` into `B`, is exactly `capture = false`.  The cost: a closure that
  returns a query's value writes `{$y}` (`nested_capture_cost`); binders on the
  path stay captured lexically (`bound_capture_kept`).
* **C, aggregation** — `TemplateScope.RolesCollection`.
* **D, quotation.**  `RSrc.quote` holds the full language and is resolved where
  it is written (`Roles.ann`), and every law covers it.  The slot model's
  sealed code resolves holes to the form's root instead
  (`Corpus.quote_holes_root`).
* **E, standing propagation.**  The role model fixes only the binding part: one
  firing is one run of a frame, so its ports, which are relations, join
  (`RolesLawsNecessity.sibling_relations_join`), and two firings share nothing
  private (`RolesLaws.private_inside`).  Which firings happen, and what a
  history key remembers, is a scheduling contract the binding roles do not
  decide (`firing_ports_join`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Boundary

open Mettapedia.GSLT.LanguageDef.TemplateScope
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles
open Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Corpus
open Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCorpus

/-! ## The study's programs -/

/-- An explicit introduction around the `case` after a query. -/
def caseNew : A := .new [.x] caseAfter

/-- An explicit crossing set on the `case` after a query. -/
def caseCapture : A :=
  lt .r (qry (ap (k .p) (sv .x)) ps (sv .x)) (.caseS (k .n2) (sv .x) (ap (k .hit) (sv .r)) (some [.x]))

/-- A closure formed after a query that writes `$y`, with or without capture. -/
def queryClosure (crossing : Option (List QSp)) : A :=
  lt .f (ap (lm .z (lt .a (qry (ap (k .p) (sv .y)) ps (k .ok)) (.lam .r crossing (sv .y))))
      (k .ok))
    (ap (sv .f) (k .ok))

/-- A closure over a `let`-bound parameter, called twice. -/
def boundClosure : A :=
  lt .f (ap (lm .z (lt .u (pr .z) (lm .r (sv .u)))) (k .n1))
    (pair (ap (sv .f) (k .ka)) (ap (sv .f) (k .kb)))

/-- A lambda formed from parts after a query. -/
def formedClosure : A :=
  lt .f (ap (lm .z (lt .a (qry (ap (k .p) (sv .y)) ps (k .ok)) (.form .r (sv .y)))) (k .ok))
    (ap (sv .f) (k .ok))

/-- The sibling `case`s beside an unrelated query that writes `$u`. -/
def outsideCaseName : A := pair (qry (ap (k .p) (sv .u)) ps (sv .u)) siblingCases

/-- An unbound answer: a variable. -/
def isVar : T → Bool
  | .var _ => true
  | _ => false

def godelPrograms : List A :=
  [caseAfter, caseNew, caseCapture, queryClosure none, queryClosure (some [.y]), boundClosure,
    formedClosure, outsideCaseName, siblingCases]

theorem godel_in_fragment : godelPrograms.all (fun t => inFragment sigMeTTa [] t) = true := by
  decide

/-- **The checks are clause units' answers**: on every program of the study the
principle's signature answers as `ruleCU`. -/
theorem godel_checks_are_CU : ∀ t ∈ godelPrograms, ansR sigMeTTa (embedQ t) = ans ruleCU t := by
  intro t ht
  exact ansR_eq_ans t (List.all_eq_true.1 godel_in_fragment t ht)

/-- **The nine checks under the principle's signature.**
1. a `case` after a query introduces its own `$x`: `(hit 1) (hit 2)`;
2. an explicit `(new ($x) …)` makes it test the query's `$x`: `(hit 2)`;
3. so does an explicit crossing set: `(hit 2)`;
4. a nested closure does not capture the query's `$y` implicitly: two unbound
   answers;
5. it does with `{$y}`: `(1 2)`;
6. a `let`-bound outer name survives both calls of a nested closure:
   `(Pair 1 1)`;
7. a closure formed from parts keeps the query's `$y`: `(1 2)`;
8. under `H1` a crossing set on the consumer does not export a query-private
   name: two unbound answers;
9. implicit and explicit nested capture differ. -/
theorem godel_checks :
    ansR sigMeTTa (embedQ caseAfter) = some [apT (kT .hit) (kT .n1), apT (kT .hit) (kT .n2)] ∧
      ansR sigMeTTa (embedQ caseNew) = some [apT (kT .hit) (kT .n2)] ∧
      ansR sigMeTTa (embedQ caseCapture) = some [apT (kT .hit) (kT .n2)] ∧
      (ansR sigMeTTa (embedQ (queryClosure none))).map (fun l => l.length == 2 && l.all isVar) =
        some true ∧
      ansR sigMeTTa (embedQ (queryClosure (some [.y]))) = some [kT .n1, kT .n2] ∧
      ansR sigMeTTa (embedQ boundClosure) = some [pairT (kT .n1) (kT .n1)] ∧
      ansR sigMeTTa (embedQ formedClosure) = some [kT .n1, kT .n2] ∧
      (ansR (sigOfRule ruleH1) (embedQ (queryClosure (some [.y])))).map
          (fun l => l.length == 2 && l.all isVar) = some true ∧
      ansR sigMeTTa (embedQ (queryClosure none)) ≠ ansR sigMeTTa (embedQ (queryClosure (some [.y]))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## Decision A -/

/-! The study's inferred policy, re-stated from its scratch experiment
(`ExplicitBoundaryExperiment`): a unit collects the names written in it that no
lexical binder introduced (`unitFree`, which skips arrow patterns), nested
lambdas capture them, and they count as bound for every pattern inside, so a
`case` pattern refers to a frame unknown written elsewhere. -/
namespace PolicyB

variable {S X : Type} [DecidableEq X]

def unitFree (B : List X) : QSrc S X → List X
  | .sym _ => []
  | .fn _ => []
  | .sv y => if y ∈ B then [] else [y]
  | .par _ => []
  | .lam _ xs _ => (xs.getD []).filter (fun y => decide (y ∉ B))
  | .app f a => unitFree B f ++ unitFree B a
  | .quote _ => []
  | .pquote c => (Src.codeSvs c).filter (fun y => decide (y ∉ B))
  | .letS p w b xs => unitFree B w ++ unitFree (B ++ QSrc.patNames p ++ xs.getD []) b
  | .unify p w b => unitFree B p ++ unitFree B w ++ unitFree B b
  | .alt a b => unitFree B a ++ unitFree B b
  | .new ys b => unitFree (B ++ ys) b
  | .form _ b => unitFree B b
  | .query p s t none => unitFree B p ++ unitFree B s ++ unitFree B t
  | .query p s t (some sh) =>
      sh.filter (fun y => decide (y ∉ B)) ++ unitFree B s ++ unitFree (B ++ QSrc.patNames p ++ sh) t
  | .caseS w p b xs => unitFree B w ++ unitFree (B ++ QSrc.patNames p ++ xs.getD []) b

def lower (r : QRule) (B : List X) : QSrc S X → Src S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .lam z none b => lamWith z (unitFree B b).dedup (lower r (B ++ (unitFree B b).dedup) b)
  | .lam z (some sh) b => .lam z (some sh) (lower r (B ++ sh) b)
  | .app f a => .app (lower r B f) (lower r B a)
  | .quote c => .quote c
  | .pquote c => .pquote c
  | .letS p w b xs =>
      .letS (lower r B p) (lower r B w) (lower r (B ++ QSrc.patNames p ++ xs.getD []) b) xs
  | .unify p w b => .unify (lower r B p) (lower r B w) (lower r (B ++ QSrc.patNames p) b)
  | .alt t₁ t₂ => .alt (lower r B t₁) (lower r B t₂)
  | .new ys b => .new ys (lower r (B ++ ys) b)
  | .form z b => .form z (lower r B b)
  | .query p s t xs =>
      patConstruct r.query B (QSrc.patNames p) xs (lower r B p) (lower r B s)
        (lower r (B ++ QSrc.patNames p ++ xs.getD []) t)
  | .caseS w p b xs =>
      patConstruct r.case B (QSrc.patNames p) xs (lower r B p) (lower r B w)
        (lower r (B ++ QSrc.patNames p ++ xs.getD []) b)

end PolicyB

/-- The inferred policy with the study's root frame. -/
def lowerB (t : A) : Src QSy QSp :=
  .new (PolicyB.unitFree [] t).dedup (PolicyB.lower ruleCU (PolicyB.unitFree [] t).dedup t)

def progB : QSy → Option T :=
  fun f => (clauses f).map fun body => clauseOf cfgLF [5] .uu .unit (lowerB body)

def ansB (t : A) : Option (List T) := answersCfg cfgLF progB 80 (lowerB t)

/-- **The inferred policy breaks context stability.**  Alone, the sibling
`case`s answer `(Pair 1 2)`; beside an unrelated query that writes `$u`, both
`case` catch-alls refer to that query's `$u` and every answer is lost. -/
theorem policyB_breaks_stability :
    ansB siblingCases = some [pairT (kT .n1) (kT .n2)] ∧ ansB outsideCaseName = some [] := by
  constructor <;> decide +kernel

/-- **The principle keeps the product**: the query's two answers, each paired
with the `case`s' one. -/
theorem principle_keeps_product :
    ansR sigMeTTa (embedQ siblingCases) = some [pairT (kT .n1) (kT .n2)] ∧
      ansR sigMeTTa (embedQ outsideCaseName) =
        some [pairT (kT .n1) (pairT (kT .n1) (kT .n2)), pairT (kT .n2) (pairT (kT .n1) (kT .n2))] := by
  constructor <;> decide +kernel

/-- **The cost of A**: the inferred policy correlates a `case` with an earlier
sibling query (`(hit 2)`); the principle needs `new` or a crossing set for it
(`godel_checks` 2 and 3). -/
theorem case_after_cost :
    ansB caseAfter = some [apT (kT .hit) (kT .n2)] ∧
      ansR sigMeTTa (embedQ caseAfter) = some [apT (kT .hit) (kT .n1), apT (kT .hit) (kT .n2)] := by
  constructor <;> decide +kernel

/-! ## Decision B -/

/-- **The cost of B**: the inferred policy lets a nested closure keep a query's
`$y` implicitly (`(1 2)`); under the principle it writes `{$y}`. -/
theorem nested_capture_cost :
    ansB (queryClosure none) = some [kT .n1, kT .n2] ∧
      ansR sigMeTTa (embedQ (queryClosure (some [.y]))) = some [kT .n1, kT .n2] := by
  constructor <;> decide +kernel

/-- Lexical capture of names that binders introduced stays: a nested closure
over a `let`-bound parameter keeps it across calls. -/
theorem bound_capture_kept : ansR sigMeTTa (embedQ boundClosure) = some [pairT (kT .n1) (kT .n1)] := by
  decide +kernel

/-- **B as a law**: implicit nested capture of frame-owned names breaks L4 for
every signature with the clause policy, so the principle's signature has none. -/
theorem decision_B {C X : Type} [DecidableEq X] (σ : Signature C) (S : Type) (y : X)
    (hσ : σ.frame = .clause) (hc : σ.capture = true) : ¬ L4Holds (X := X) σ S :=
  not_L4_capture hσ hc y

/-! ## Decision E -/

/-- **One firing, one frame.**  The ports of a firing are relations of one frame,
so they join on every name they share; a second firing is a second run, whose
private names are its own (`private_inside`). -/
theorem firing_ports_join (n : QSp) (E : REnv QSp) (w : RSrc MC QSy QSp) :
    ann sigMeTTa E [] [] [] (.app (.pat .portR (.sv n) w w none) (.pat .portR (.sv n) w w none)) =
      .app (.pat .portR (.sv (E n, n)) (ann sigMeTTa E [] [] ([] ++ [0] ++ [1]) w)
          (ann sigMeTTa E (patB [] (RSrc.sv n : RSrc MC QSy QSp) none) (patR [] none [])
            ([] ++ [0] ++ [2]) w) none)
        (.pat .portR (.sv (E n, n)) (ann sigMeTTa E [] [] ([] ++ [1] ++ [1]) w)
          (ann sigMeTTa E (patB [] (RSrc.sv n : RSrc MC QSy QSp) none) (patR [] none [])
            ([] ++ [1] ++ [2]) w) none) :=
  sibling_relations_join sigMeTTa .portR rfl n E [] [] [] w

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles.Boundary
