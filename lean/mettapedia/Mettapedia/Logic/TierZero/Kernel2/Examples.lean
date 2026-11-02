import Mettapedia.Logic.TierZero.Kernel2.Render

/-!
# The kernel-v2 test worlds as Lean data

Each world is the message sequence of one MeTTa kernel-v2 test (`G2-gslt-readers/kernel-v2/tests`)
or of a finding probe, written as Lean data: the admissions in `A`, the claims in `W`. The Lean
kernel runs it (`runWorld`), and `renderWorld` prints the same messages as a MeTTa program, so the
two kernels are run on identical inputs (differential test).

* `hilbert` (v2_01): `id` (10 nodes, labels and children only), `id-use` (the accepted claim used
  as a rule), `refl-use` (a formal cited from the term store); negatives `bad-swap`, `bad-few`,
  `bad-term`, `bad-goal`, `id-cut`; the rule `undetermined` is refused.
* `order` (v2_04, F1), `reserved` (v2_05, F2), `binders` (v2_06, F3), `terms` (v2_07, F4).
* `f5Honest`, `f5Absent` (F5): a proof that decides `differ`/`absent-from` on its own fresh names
  is accepted, but does not become a rule; the claims that would use it as one are not accepted.
  The declared twins (the side condition among the claim's hypotheses) become rules, which refuse
  the instance where the condition fails and fire where it holds.

`Controls` checks some verdicts by the kernel (`decide +kernel`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.Examples

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
open Mettapedia.Logic.TierZero.Kernel2

/-- A judgment pattern. -/
abbrev J := pjd

/-- An application pattern `(f p₁ … pₙ)` with a symbol head. -/
def ap (f : String) (ps : List Pat) : Pat := pex (psym f :: ps)

/-- A claim with name formals, no dummies, no locals, no local pairs. -/
def claim (id : String) (nformals : ℕ) (hyps : List Premise) (concl : Pat) (terms : List (ℕ × Pat))
    (proof : List (ℕ × String × List CKid)) (root : CKid) : Claim String :=
  ⟨id, List.replicate nformals .name, [], hyps, [], [], concl, terms,
    proof.map fun x => ⟨x.1, x.2.1, x.2.2⟩, root⟩

/-- A world from its admissions and claims. -/
def world (adms : List (Admission String)) (claims : List (Claim String)) : World String :=
  ⟨⟨[], [], []⟩, [], adms, claims, []⟩

/-- The accepted board after running the kernel. -/
def accepted (w : World String) : List String := (runWorld 10000 w).T

/-! ## v2_01: a Metamath-shaped presentation -/

def wi (a b : Pat) : Pat := ap "wi" [a, b]

def hilbertRules : List (Admission String) :=
  [ .judgment "wff" 1, .judgment "|-" 1, .judgment "eqj" 2,
    .rule "wi" ⟨2, [.judg (J "wff" [pv 0]), .judg (J "wff" [pv 1])], J "wff" [wi (pv 0) (pv 1)]⟩,
    .rule "ax-1" ⟨2, [.judg (J "wff" [pv 0]), .judg (J "wff" [pv 1])],
      J "|-" [wi (pv 0) (wi (pv 1) (pv 0))]⟩,
    .rule "ax-2" ⟨3, [.judg (J "wff" [pv 0]), .judg (J "wff" [pv 1]), .judg (J "wff" [pv 2])],
      J "|-" [wi (wi (pv 0) (wi (pv 1) (pv 2))) (wi (wi (pv 0) (pv 1)) (wi (pv 0) (pv 2)))]⟩,
    .rule "ax-mp" ⟨2, [.judg (J "wff" [pv 0]), .judg (J "wff" [pv 1]), .judg (J "|-" [pv 0]),
      .judg (J "|-" [wi (pv 0) (pv 1)])], J "|-" [pv 1]⟩,
    .rule "refl" ⟨1, [.given (pv 0)], J "eqj" [pv 0, pv 0]⟩,
    .rule "undetermined" ⟨2, [.judg (J "wff" [pv 0])], J "|-" [wi (pv 0) (pv 1)]⟩,
    .rule "wq" ⟨0, [], J "wff" [psym "q"]⟩ ]

/-- The nodes of `id`: `|- (ph → ph)` from `wff ph`. -/
def idNodes : List (ℕ × String × List CKid) :=
  [ (2, "wi", [.hyp 0, .hyp 0]), (3, "wi", [.hyp 0, .node 2]), (4, "wi", [.node 2, .hyp 0]),
    (5, "ax-2", [.hyp 0, .node 2, .hyp 0]), (6, "ax-1", [.hyp 0, .node 2]), (7, "wi", [.hyp 0, .node 4]),
    (8, "wi", [.node 3, .node 2]), (9, "ax-mp", [.node 7, .node 8, .node 6, .node 5]),
    (10, "ax-1", [.hyp 0, .hyp 0]), (11, "ax-mp", [.node 3, .node 2, .node 10, .node 9]) ]

def fgc : Pat := ap "f" [ap "g" [psym "c"], ap "g" [psym "c"]]

def hilbertClaims : List (Claim String) :=
  [ claim "id" 1 [.judg (J "wff" [pv 0])] (J "|-" [wi (pv 0) (pv 0)]) [] idNodes (.node 11),
    claim "id-use" 0 [] (J "|-" [wi (psym "q") (psym "q")]) []
      [(1, "wq", []), (2, "id", [.node 1])] (.node 2),
    claim "refl-use" 0 [] (J "eqj" [fgc, fgc]) [(1, fgc)] [(1, "refl", [.term 1])] (.node 1),
    claim "bad-swap" 1 [.judg (J "wff" [pv 0])] (J "|-" [wi (pv 0) (pv 0)]) []
      (idNodes.take 9 ++ [(11, "ax-mp", [.node 3, .node 2, .node 9, .node 10])]) (.node 11),
    claim "bad-few" 1 [.judg (J "wff" [pv 0])] (J "|-" [wi (pv 0) (wi (pv 0) (pv 0))]) []
      [(1, "ax-1", [.hyp 0])] (.node 1),
    claim "bad-term" 0 [] (J "eqj" [psym "c", psym "c"]) [(1, psym "d")] [(1, "refl", [.term 2])] (.node 1),
    claim "bad-goal" 0 [] (J "eqj" [psym "c", psym "c"]) [(1, psym "d")] [(1, "refl", [.term 1])] (.node 1),
    claim "id-chunked" 1 [.judg (J "wff" [pv 0])] (J "|-" [wi (pv 0) (pv 0)]) [] idNodes (.node 11),
    claim "id-cut" 1 [.judg (J "wff" [pv 0])] (J "|-" [wi (pv 0) (pv 0)]) [] (idNodes.take 2) (.node 11) ]

def hilbert : World String := world hilbertRules hilbertClaims

/-! ## v2_04: side conditions after the premises that bind their inputs (F1) -/

def order : World String := world
  [ .judgment "wff" 1, .judgment "set" 1, .judgment "|-" 1,
    .rule "weq" ⟨2, [.judg (J "set" [pv 0]), .judg (J "set" [pv 1])], J "wff" [ap "weq" [pv 0, pv 1]]⟩,
    .rule "ax-dv-first" ⟨2, [.dv (pv 0) (pv 1), .judg (J "wff" [pv 0]), .judg (J "set" [pv 1])],
      J "|-" [ap "wal" [pv 1, pv 0]]⟩,
    .rule "ax-dv-last" ⟨2, [.judg (J "wff" [pv 0]), .judg (J "set" [pv 1]), .dv (pv 0) (pv 1)],
      J "|-" [ap "wal" [pv 1, pv 0]]⟩,
    .rule "differ-first" ⟨2, [.differ (pv 0) (pv 1), .judg (J "set" [pv 0]), .judg (J "set" [pv 1])],
      J "wff" [ap "weq" [pv 0, pv 1]]⟩ ]
  [ claim "violate" 2 [.judg (J "set" [pv 0]), .judg (J "set" [pv 1])]
      (J "|-" [ap "wal" [pv 0, ap "weq" [pv 0, pv 1]]]) []
      [(1, "weq", [.hyp 0, .hyp 1]), (2, "ax-dv-first", [.node 1, .hyp 0])] (.node 2),
    claim "dv-first-claim" 2 [.dv (pv 0) (pv 1), .judg (J "set" [pv 0]), .judg (J "set" [pv 1])]
      (J "wff" [ap "weq" [pv 0, pv 1]]) [] [(1, "weq", [.hyp 1, .hyp 2])] (.node 1),
    claim "dv-last-claim" 2 [.judg (J "set" [pv 0]), .judg (J "set" [pv 1]), .dv (pv 0) (pv 1)]
      (J "wff" [ap "weq" [pv 0, pv 1]]) [] [(1, "weq", [.hyp 0, .hyp 1])] (.node 1) ]

/-! ## v2_05: side conditions are no judgments (F2) -/

def needsDiff : Admission String :=
  .rule "needs-diff" ⟨2, [.judg (J "set" [pv 0]), .judg (J "set" [pv 1]), .differ (pv 0) (pv 1)],
    J "|-" [ap "ne" [pv 0, pv 1]]⟩

def reserved : World String := world
  [ .judgment "set" 1, .judgment "|-" 1, .judgment "differ" 2, .judgment "given" 1, needsDiff ]
  [ claim "cheat" 1 [.judg (J "set" [pv 0]), .differ (pv 0) (pv 0)] (J "|-" [ap "ne" [pv 0, pv 0]]) []
      [(1, "needs-diff", [.hyp 0, .hyp 0, .hyp 1])] (.node 1),
    claim "bad-concl" 2 [.judg (J "set" [pv 0]), .judg (J "set" [pv 1])] (J "differ" [pv 0, pv 1]) []
      [(1, "needs-diff", [.hyp 0, .hyp 1])] (.node 1),
    claim "honest" 2 [.judg (J "set" [pv 0]), .judg (J "set" [pv 1])] (J "|-" [ap "ne" [pv 0, pv 1]]) []
      [(1, "needs-diff", [.hyp 0, .hyp 1])] (.node 1) ]

/-! ## v2_06: binders (F3) -/

def lam (b : Pat) : Pat := ap "lam" [b]
def app (f x : Pat) : Pat := ap "app" [f, x]

/-- `(f (bv 0) (bind a (g (bv 0) (bv 1))))`. -/
def betaBody : Pat := ap "f" [.idx 0, pbnd (psym "a") (ap "g" [.idx 0, .idx 1])]

def binders : World String := world
  [ .judgment "tm" 1, .judgment "eqb" 2,
    .rule "beta" ⟨3, [.judg (J "tm" [lam (pv 0)]), .judg (J "tm" [pv 1]), .isOpen (pv 2) (pv 0) (pv 1)],
      J "eqb" [app (lam (pv 0)) (pv 1), pv 2]⟩,
    .rule "abs" ⟨3, [.judg (J "tm" [pv 0]), .judg (J "tm" [pv 1]), .isAbstract (pv 2) (pv 0) (pv 1)],
      J "eqb" [lam (pv 2), lam (pv 2)]⟩ ]
  [ claim "beta-ok" 0 [.judg (J "tm" [lam betaBody]), .judg (J "tm" [psym "c"])]
      (J "eqb" [app (lam betaBody) (psym "c"),
        ap "f" [psym "c", pbnd (psym "a") (ap "g" [.idx 0, psym "c"])]]) []
      [(1, "beta", [.hyp 0, .hyp 1])] (.node 1),
    claim "beta-dangling" 0 [.judg (J "tm" [lam (ap "f" [.idx 0])]), .judg (J "tm" [.idx 0])]
      (J "eqb" [app (lam (ap "f" [.idx 0])) (.idx 0), ap "f" [.idx 0]]) []
      [(1, "beta", [.hyp 0, .hyp 1])] (.node 1),
    claim "abs-ok" 1 [.judg (J "tm" [pv 0]),
        .judg (J "tm" [ap "f" [pv 0, pbnd (psym "a") (ap "g" [pv 0, .idx 0])]])]
      (J "eqb" [lam (ap "f" [.idx 0, pbnd (psym "a") (ap "g" [.idx 1, .idx 0])]),
        lam (ap "f" [.idx 0, pbnd (psym "a") (ap "g" [.idx 1, .idx 0])])]) []
      [(1, "abs", [.hyp 0, .hyp 1])] (.node 1),
    claim "abs-dangling" 1 [.judg (J "tm" [pv 0]), .judg (J "tm" [ap "f" [pv 0, .idx 0]])]
      (J "eqb" [lam (ap "f" [.idx 0, .idx 0]), lam (ap "f" [.idx 0, .idx 0])]) []
      [(1, "abs", [.hyp 0, .hyp 1])] (.node 1) ]

/-! ## v2_07: term ids name one term each (F4) -/

def terms : World String := world
  [ .judgment "eqj" 2, .rule "refl" ⟨1, [.given (pv 0)], J "eqj" [pv 0, pv 0]⟩ ]
  [ claim "dup-ids" 0 [] (J "eqj" [psym "a", psym "a"]) [(1, psym "a"), (1, psym "b")]
      [(1, "refl", [.term 1])] (.node 1),
    claim "unique-ids" 0 [] (J "eqj" [psym "a", psym "a"]) [(1, psym "a"), (2, psym "b")]
      [(1, "refl", [.term 1])] (.node 1) ]

/-! ## F5: a decision on a claim's own names becomes a rule only when declared

`honest` decides `(differ x y)` on its two fresh names: accepted, no rule. Its twin `honest-d` has
the hypothesis `(differ x y)`: accepted and a rule, which refuses `x = y` (`via-honest-d`) and fires
on distinct values (`via-honest-d-ab`). The same with `absent-from` (`gen`, `gen-d`). -/

def f5Honest : World String := world
  [ .judgment "set" 1, .judgment "|-" 1, needsDiff, .rule "set-a" ⟨0, [], J "set" [psym "a"]⟩,
    .rule "set-b" ⟨0, [], J "set" [psym "b"]⟩ ]
  [ claim "honest" 2 [.judg (J "set" [pv 0]), .judg (J "set" [pv 1])] (J "|-" [ap "ne" [pv 0, pv 1]]) []
      [(1, "needs-diff", [.hyp 0, .hyp 1])] (.node 1),
    claim "direct" 0 [] (J "|-" [ap "ne" [psym "a", psym "a"]]) []
      [(1, "set-a", []), (2, "needs-diff", [.node 1, .node 1])] (.node 2),
    claim "via-honest" 0 [] (J "|-" [ap "ne" [psym "a", psym "a"]]) []
      [(1, "set-a", []), (2, "honest", [.node 1, .node 1])] (.node 2),
    claim "honest-d" 2 [.judg (J "set" [pv 0]), .judg (J "set" [pv 1]), .differ (pv 0) (pv 1)]
      (J "|-" [ap "ne" [pv 0, pv 1]]) [] [(1, "needs-diff", [.hyp 0, .hyp 1])] (.node 1),
    claim "via-honest-d" 0 [] (J "|-" [ap "ne" [psym "a", psym "a"]]) []
      [(1, "set-a", []), (2, "honest-d", [.node 1, .node 1])] (.node 2),
    claim "via-honest-d-ab" 0 [] (J "|-" [ap "ne" [psym "a", psym "b"]]) []
      [(1, "set-a", []), (2, "set-b", []), (3, "honest-d", [.node 1, .node 2])] (.node 3) ]

def f5Absent : World String := world
  [ .judgment "set" 1, .judgment "wff" 1, .judgment "|-" 1,
    .rule "nf" ⟨2, [.judg (J "set" [pv 0]), .judg (J "wff" [pv 1]), .absent (pv 0) (pv 1)],
      J "|-" [ap "nf" [pv 0, pv 1]]⟩,
    .rule "set-a" ⟨0, [], J "set" [psym "a"]⟩, .rule "wff-a" ⟨0, [], J "wff" [psym "a"]⟩,
    .rule "wff-b" ⟨0, [], J "wff" [psym "b"]⟩ ]
  [ claim "gen" 2 [.judg (J "set" [pv 0]), .judg (J "wff" [pv 1])] (J "|-" [ap "nf" [pv 0, pv 1]]) []
      [(1, "nf", [.hyp 0, .hyp 1])] (.node 1),
    claim "direct" 0 [] (J "|-" [ap "nf" [psym "a", psym "a"]]) []
      [(1, "set-a", []), (2, "wff-a", []), (3, "nf", [.node 1, .node 2])] (.node 3),
    claim "via-gen" 0 [] (J "|-" [ap "nf" [psym "a", psym "a"]]) []
      [(1, "set-a", []), (2, "wff-a", []), (3, "gen", [.node 1, .node 2])] (.node 3),
    claim "gen-d" 2 [.judg (J "set" [pv 0]), .judg (J "wff" [pv 1]), .absent (pv 0) (pv 1)]
      (J "|-" [ap "nf" [pv 0, pv 1]]) [] [(1, "nf", [.hyp 0, .hyp 1])] (.node 1),
    claim "via-gen-d" 0 [] (J "|-" [ap "nf" [psym "a", psym "a"]]) []
      [(1, "set-a", []), (2, "wff-a", []), (3, "gen-d", [.node 1, .node 2])] (.node 3),
    claim "via-gen-d-ab" 0 [] (J "|-" [ap "nf" [psym "a", psym "b"]]) []
      [(1, "set-a", []), (2, "wff-b", []), (3, "gen-d", [.node 1, .node 2])] (.node 3) ]

/-- The names of the rules on the board after running the kernel. -/
def ruleNames (w : World String) : List String := (runWorld 10000 w).L.rules.map Prod.fst

/-! ## Formal kinds (v2_10), opaque values (v2_11), and binders never capturing a claim variable (F6) -/

/-- A claim whose formals have the given kinds, no dummies, no locals, no local pairs. -/
def claimK (id : String) (kinds : List FormalKind) (hyps : List Premise) (concl : Pat)
    (terms : List (ℕ × Pat)) (proof : List (ℕ × String × List CKid)) (root : CKid) : Claim String :=
  ⟨id, kinds, [], hyps, [], [], concl, terms, proof.map fun x => ⟨x.1, x.2.1, x.2.2⟩, root⟩

/-- MM0's `all` and the axiom `ax5`, `φ → ∀x φ` for a `φ` independent of `x`. -/
def bvTyRules : List (Admission String) :=
  [ .judgment "bv" 1, .judgment "ty" 1, .judgment "pf" 1,
    .rule "all" ⟨2, [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1])], J "ty" [ap "all" [pv 0, pv 1]]⟩,
    .rule "ax5" ⟨2, [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1]), .absent (pv 0) (pv 1)],
      J "pf" [ap "im" [pv 1, ap "all" [pv 0, pv 1]]]⟩ ]

/-- `φ → ∀x φ`, over formals `x` (0) and `φ` (1). -/
def ax5Concl : Pat := J "pf" [ap "im" [pv 1, ap "all" [pv 0, pv 1]]]

/-- v2_10: `nf-accepted` (`q` independent of `x`, undeclared: a verdict only), `nf-refused` (`p`
over `x`), `nf-declared` (the independence declared: a rule), `dep-term` (no side condition: a
rule), `bad-kind` (a dependency on a name: refused at admission). -/
def kinds : World String := world bvTyRules
  [ claimK "nf-accepted" [.scope, .dep []] [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1])] ax5Concl []
      [(1, "ax5", [.hyp 0, .hyp 1])] (.node 1),
    claimK "nf-refused" [.scope, .dep [0]] [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1])] ax5Concl []
      [(1, "ax5", [.hyp 0, .hyp 1])] (.node 1),
    claimK "nf-declared" [.scope, .dep []]
      [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1]), .absent (pv 0) (pv 1)] ax5Concl []
      [(1, "ax5", [.hyp 0, .hyp 1])] (.node 1),
    claimK "dep-term" [.scope, .dep [0]] [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1])]
      (J "ty" [ap "all" [pv 0, pv 1]]) [] [(1, "all", [.hyp 0, .hyp 1])] (.node 1),
    claimK "bad-kind" [.name, .dep [0]] [.judg (J "ty" [pv 0]), .judg (J "ty" [pv 1])] ax5Concl []
      [(1, "ax5", [.hyp 0, .hyp 1])] (.node 1) ]

/-- v2_11: `proj` (a variable head) and `proj-over` (`over` as a head) are refused at admission;
`whole` uses a dep formal's value whole; `var-head` has a hypothesis headed by a formal. -/
def opaqueHeads : World String := world
  [ .judgment "bv" 1, .judgment "ty" 1,
    .rule "all" ⟨2, [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1])], J "ty" [ap "all" [pv 0, pv 1]]⟩,
    .rule "proj" ⟨3, [.judg (J "ty" [pex [pv 0, pv 1, pv 2]])], J "ty" [pv 2]⟩,
    .rule "proj-over" ⟨2, [.judg (J "ty" [ap "over" [pv 0, pv 1]])], J "ty" [pv 1]⟩ ]
  [ claimK "whole" [.scope, .dep [0]] [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1])]
      (J "ty" [ap "all" [pv 0, pv 1]]) [] [(1, "all", [.hyp 0, .hyp 1])] (.node 1),
    claim "var-head" 2 [.judg (J "bv" [pv 1]), .judg (J "ty" [pex [pv 0, pv 1]])]
      (J "ty" [ap "all" [pv 1, pex [pv 0, pv 1]]]) [] [(1, "all", [.hyp 0, .hyp 1])] (.node 1) ]

/-- F6: a rule's binder never captures a claim variable. `B` proves `(p (bind T (bv 0)))`; `cap`
claims `(p (bind T x))` for a scope variable `x` from `(tm x)` with `B`. Were `x` the bound variable
`idx 0`, the goal would be `B`'s conclusion, and `cap` as a rule would prove `(p (bind T c))` from
`(tm c)` (`via-cap`), which nothing derives. `x` is a name, so `cap` is refused. -/
def capture : World String := world
  [ .judgment "tm" 1, .judgment "p" 1,
    .rule "B" ⟨0, [], J "p" [pbnd (psym "T") (.idx 0)]⟩,
    .rule "tmc" ⟨0, [], J "tm" [psym "c"]⟩ ]
  [ claimK "cap" [.scope] [.judg (J "tm" [pv 0])] (J "p" [pbnd (psym "T") (pv 0)]) []
      [(1, "B", [])] (.node 1),
    claim "via-cap" 0 [] (J "p" [pbnd (psym "T") (psym "c")]) []
      [(1, "tmc", []), (2, "cap", [.node 1])] (.node 2) ]

/-! ## Sets the claim supplies (v2_12), and singleton, image, atom kinds (v2_13) -/

/-- A set pattern `(set p₁ … pₙ)`. -/
def pset (ps : List Pat) : Pat := pex (psym "set" :: ps)

/-- v2_12: `join` checks `(union-of U G D)`, `drop` checks `(remove-of R X G)`; the sets come from the
term store, in any order. -/
def sets : World String := world
  [ .judgment "hs" 1,
    .rule "hs-a" ⟨0, [], J "hs" [pset [psym "a"]]⟩,
    .rule "hs-bc" ⟨0, [], J "hs" [pset [psym "b", psym "c"]]⟩,
    .rule "join" ⟨3, [.judg (J "hs" [pv 0]), .judg (J "hs" [pv 1]), .given (pv 2), .unionOf (pv 2) (pv 0) (pv 1)],
      J "hs" [pv 2]⟩,
    .rule "drop" ⟨3, [.judg (J "hs" [pv 0]), .given (pv 1), .given (pv 2), .removeOf (pv 2) (pv 1) (pv 0)],
      J "hs" [pv 2]⟩,
    .rule "bad-join" ⟨3, [.unionOf (pv 2) (pv 0) (pv 1), .judg (J "hs" [pv 0]), .judg (J "hs" [pv 1]),
      .given (pv 2)], J "hs" [pv 2]⟩ ]
  [ claim "union-ok" 0 [] (J "hs" [pset [psym "c", psym "a", psym "b"]]) [(1, pset [psym "c", psym "a", psym "b"])]
      [(1, "hs-a", []), (2, "hs-bc", []), (3, "join", [.node 1, .node 2, .term 1])] (.node 3),
    claim "union-dup" 0 [] (J "hs" [pset [psym "a", psym "b", psym "c", psym "a"]])
      [(1, pset [psym "a", psym "b", psym "c", psym "a"])]
      [(1, "hs-a", []), (2, "hs-bc", []), (3, "join", [.node 1, .node 2, .term 1])] (.node 3),
    claim "union-missing" 0 [] (J "hs" [pset [psym "a", psym "b"]]) [(1, pset [psym "a", psym "b"])]
      [(1, "hs-a", []), (2, "hs-bc", []), (3, "join", [.node 1, .node 2, .term 1])] (.node 3),
    claim "union-extra" 0 [] (J "hs" [pset [psym "a", psym "b", psym "c", psym "d"]])
      [(1, pset [psym "a", psym "b", psym "c", psym "d"])]
      [(1, "hs-a", []), (2, "hs-bc", []), (3, "join", [.node 1, .node 2, .term 1])] (.node 3),
    claim "remove-ok" 0 [] (J "hs" [pset [psym "c"]]) [(1, psym "b"), (2, pset [psym "c"])]
      [(1, "hs-bc", []), (2, "drop", [.node 1, .term 1, .term 2])] (.node 2),
    claim "remove-kept" 0 [] (J "hs" [pset [psym "b", psym "c"]]) [(1, psym "b"), (2, pset [psym "b", psym "c"])]
      [(1, "hs-bc", []), (2, "drop", [.node 1, .term 1, .term 2])] (.node 2),
    claim "remove-lost" 0 [] (J "hs" [pset []]) [(1, psym "b"), (2, pset [])]
      [(1, "hs-bc", []), (2, "drop", [.node 1, .term 1, .term 2])] (.node 2),
    claim "drop-own" 2 [.judg (J "hs" [pset [pv 0, pv 1]])] (J "hs" [pset [pv 1]]) [(1, pv 0), (2, pset [pv 1])]
      [(2, "drop", [.hyp 0, .term 1, .term 2])] (.node 2),
    claim "drop-declared" 2 [.judg (J "hs" [pset [pv 0, pv 1]]), .removeOf (pset [pv 1]) (pv 0) (pset [pv 0, pv 1])]
      (J "hs" [pset [pv 1]]) [(1, pv 0), (2, pset [pv 1])]
      [(2, "drop", [.hyp 0, .term 1, .term 2])] (.node 2) ]

/-- The substitution `((a c) (b c))`. -/
def acbc : Pat := pex [pex [psym "a", psym "c"], pex [psym "b", psym "c"]]

/-- v2_13: `(singleton-of S X)`, `(image-of H2 S H)`, `(atom-kind X K)`. -/
def forms : World String := world
  [ .judgment "hs" 1, .judgment "tm" 1,
    .rule "tm-a" ⟨0, [], J "tm" [psym "a"]⟩,
    .rule "sing" ⟨2, [.judg (J "tm" [pv 0]), .given (pv 1), .singletonOf (pv 1) (pv 0)], J "hs" [pv 1]⟩,
    .rule "hs-fab" ⟨0, [], J "hs" [pset [ap "f" [psym "a"], ap "f" [psym "b"], psym "b"]]⟩,
    .rule "image" ⟨3, [.judg (J "hs" [pv 0]), .given (pv 1), .given (pv 2), .imageOf (pv 2) (pv 1) (pv 0)],
      J "hs" [pv 2]⟩,
    .rule "sym-tm" ⟨1, [.given (pv 0), .atomKind (pv 0) (psym "symbol")], J "tm" [pv 0]⟩,
    .rule "num-tm" ⟨1, [.given (pv 0), .atomKind (pv 0) (psym "number")], J "tm" [pv 0]⟩,
    .rule "name-tm" ⟨1, [.given (pv 0), .atomKind (pv 0) (psym "name")], J "tm" [pv 0]⟩ ]
  [ claim "sing-ok" 0 [] (J "hs" [pset [psym "a"]]) [(1, pset [psym "a"])]
      [(1, "tm-a", []), (2, "sing", [.node 1, .term 1])] (.node 2),
    claim "sing-dup" 0 [] (J "hs" [pset [psym "a", psym "a"]]) [(1, pset [psym "a", psym "a"])]
      [(1, "tm-a", []), (2, "sing", [.node 1, .term 1])] (.node 2),
    claim "sing-two" 0 [] (J "hs" [pset [psym "a", psym "b"]]) [(1, pset [psym "a", psym "b"])]
      [(1, "tm-a", []), (2, "sing", [.node 1, .term 1])] (.node 2),
    claim "sing-empty" 0 [] (J "hs" [pset []]) [(1, pset [])]
      [(1, "tm-a", []), (2, "sing", [.node 1, .term 1])] (.node 2),
    claim "image-ok" 0 [] (J "hs" [pset [psym "c", ap "f" [psym "c"]]])
      [(1, acbc), (2, pset [psym "c", ap "f" [psym "c"]])]
      [(1, "hs-fab", []), (2, "image", [.node 1, .term 1, .term 2])] (.node 2),
    claim "image-missing" 0 [] (J "hs" [pset [ap "f" [psym "c"]]]) [(1, acbc), (2, pset [ap "f" [psym "c"]])]
      [(1, "hs-fab", []), (2, "image", [.node 1, .term 1, .term 2])] (.node 2),
    claim "image-extra" 0 [] (J "hs" [pset [psym "c", ap "f" [psym "c"], psym "d"]])
      [(1, acbc), (2, pset [psym "c", ap "f" [psym "c"], psym "d"])]
      [(1, "hs-fab", []), (2, "image", [.node 1, .term 1, .term 2])] (.node 2),
    claim "sym-ok" 0 [] (J "tm" [psym "b"]) [(1, psym "b")] [(1, "sym-tm", [.term 1])] (.node 1),
    claim "sym-num" 0 [] (J "tm" [pnum 3]) [(1, pnum 3)] [(1, "sym-tm", [.term 1])] (.node 1),
    claim "num-ok" 0 [] (J "tm" [pnum 3]) [(1, pnum 3)] [(1, "num-tm", [.term 1])] (.node 1),
    claim "name-own" 1 [.given (pv 0)] (J "tm" [pv 0]) [(1, pv 0)] [(1, "name-tm", [.term 1])] (.node 1),
    claim "name-declared" 1 [.given (pv 0), .atomKind (pv 0) (psym "name")] (J "tm" [pv 0]) [(1, pv 0)]
      [(1, "name-tm", [.term 1])] (.node 1),
    claim "via-name-a" 0 [] (J "tm" [psym "a"]) [(1, psym "a")] [(1, "name-declared", [.term 1])] (.node 1) ]

/-! ## List premises (v2_14) -/

/-- The list `(p₁ … pₙ)`. -/
def plist (ps : List Pat) : Pat := pex ps

/-- v2_14: `all` asks one child `(tm E)` per element `E` of its list, through the list premise
`(each x L (tm x))` whose `x` (formal `1`) is local; `bad-local` uses `x` in its conclusion and
`bad-input` checks the list before binding it: both are refused at admission. -/
def eachWorld : World String := world
  [ .judgment "tm" 1, .judgment "all-tm" 1,
    .rule "tm-a" ⟨0, [], J "tm" [psym "a"]⟩,
    .rule "tm-b" ⟨0, [], J "tm" [psym "b"]⟩,
    .rule "all" ⟨1, [.given (pv 0), .each 1 (pv 0) (J "tm" [pv 1])], J "all-tm" [pv 0]⟩,
    .rule "bad-local" ⟨1, [.given (pv 0), .each 1 (pv 0) (J "tm" [pv 1])], J "all-tm" [pv 1]⟩,
    .rule "bad-input" ⟨1, [.each 1 (pv 0) (J "tm" [pv 1]), .given (pv 0)], J "all-tm" [pv 0]⟩ ]
  [ claim "each-ok" 0 [] (J "all-tm" [plist [psym "a", psym "b"]]) [(1, plist [psym "a", psym "b"])]
      [(1, "tm-a", []), (2, "tm-b", []), (3, "all", [.term 1, .node 1, .node 2])] (.node 3),
    claim "each-empty" 0 [] (J "all-tm" [plist []]) [(1, plist [])] [(1, "all", [.term 1])] (.node 1),
    claim "each-swapped" 0 [] (J "all-tm" [plist [psym "a", psym "b"]]) [(1, plist [psym "a", psym "b"])]
      [(1, "tm-a", []), (2, "tm-b", []), (3, "all", [.term 1, .node 2, .node 1])] (.node 3),
    claim "each-few" 0 [] (J "all-tm" [plist [psym "a", psym "b"]]) [(1, plist [psym "a", psym "b"])]
      [(1, "tm-a", []), (2, "tm-b", []), (3, "all", [.term 1, .node 1])] (.node 3),
    claim "each-many" 0 [] (J "all-tm" [plist [psym "a", psym "b"]]) [(1, plist [psym "a", psym "b"])]
      [(1, "tm-a", []), (2, "tm-b", []), (3, "all", [.term 1, .node 1, .node 2, .node 1])] (.node 3),
    claim "each-hyp" 2 [.given (pv 0), .each 1 (pv 0) (J "tm" [pv 1])] (J "all-tm" [pv 0]) [(1, pv 0)]
      [(1, "all", [.term 1])] (.node 1) ]

/-! ## `absent-from` derived by structure (v2_15) -/

/-- `φ → ∀x φ` at `φ := (f p q)`, over formals `x` (0), `p` (1), `q` (2). -/
def nfFConcl : Pat := J "pf" [ap "im" [ap "f" [pv 1, pv 2], ap "all" [pv 0, ap "f" [pv 1, pv 2]]]]

/-- The hypotheses of `nf-f`: `x` bound, `p` and `q` formulas independent of `x`. -/
def nfFHyps : List Premise :=
  [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1]), .judg (J "ty" [pv 2]), .absent (pv 0) (pv 1),
    .absent (pv 0) (pv 2)]

/-- v2_15: `nf-f` decides `(absent-from x (f p q))` from its declared `(absent-from x p)` and
`(absent-from x q)`; only `nf-f-named`, which also declares `x` a name, becomes a rule, and that rule
refuses `x := (f c d)`, where the base rules refuse too (`direct`). -/
def absStructWorld : World String := world
  [ .judgment "bv" 1, .judgment "ty" 1, .judgment "pf" 1,
    .rule "ax5" ⟨2, [.judg (J "bv" [pv 0]), .judg (J "ty" [pv 1]), .absent (pv 0) (pv 1)],
      J "pf" [ap "im" [pv 1, ap "all" [pv 0, pv 1]]]⟩,
    .rule "f-ty" ⟨2, [.judg (J "ty" [pv 0]), .judg (J "ty" [pv 1])], J "ty" [ap "f" [pv 0, pv 1]]⟩,
    .rule "ty-c" ⟨0, [], J "ty" [psym "c"]⟩,
    .rule "ty-d" ⟨0, [], J "ty" [psym "d"]⟩,
    .rule "bv-fcd" ⟨0, [], J "bv" [ap "f" [psym "c", psym "d"]]⟩ ]
  [ claimK "nf-f" [.scope, .dep [], .dep []] nfFHyps nfFConcl []
      [(1, "f-ty", [.hyp 1, .hyp 2]), (2, "ax5", [.hyp 0, .node 1])] (.node 2),
    claimK "nf-f-named" [.scope, .dep [], .dep []] (nfFHyps ++ [.atomKind (pv 0) (psym "name")]) nfFConcl []
      [(1, "f-ty", [.hyp 1, .hyp 2]), (2, "ax5", [.hyp 0, .node 1])] (.node 2),
    claim "via-compound" 0 []
      (J "pf" [ap "im" [ap "f" [psym "c", psym "d"], ap "all" [ap "f" [psym "c", psym "d"], ap "f" [psym "c", psym "d"]]]])
      [] [(1, "bv-fcd", []), (2, "ty-c", []), (3, "ty-d", []), (4, "nf-f-named", [.node 1, .node 2, .node 3])]
      (.node 4),
    claim "direct" 0 []
      (J "pf" [ap "im" [ap "f" [psym "c", psym "d"], ap "all" [ap "f" [psym "c", psym "d"], ap "f" [psym "c", psym "d"]]]])
      [] [(1, "bv-fcd", []), (2, "ty-c", []), (3, "ty-d", []), (4, "f-ty", [.node 2, .node 3]),
        (5, "ax5", [.node 1, .node 4])] (.node 5) ]

/-! ## Controls, decided by the kernel -/

namespace Controls

/-- v2_07: the claim with two terms named `t1` is refused, the one with unique ids accepted. -/
theorem terms_accepted : accepted terms = ["unique-ids"] := by decide +kernel

/-- v2_05: only `honest` is accepted; `cheat` cites a side-condition hypothesis, `bad-concl` has a
reserved head; `differ` and `given` are refused as judgments. -/
theorem reserved_accepted : accepted reserved = ["honest"] := by decide +kernel

/-- F5: `honest` is accepted and is no rule, so `via-honest` is not accepted; `direct` is refused by
the base rules. Its declared twin `honest-d` is a rule: refused at `a, a`, used at `a, b`. -/
theorem f5_honest_accepted : accepted f5Honest = ["honest", "honest-d", "via-honest-d-ab"] := by
  decide +kernel

/-- F5: of `honest` and `honest-d`, only the declared twin is on the rules board (with the accepted
claim that used it, a rule of no formals). -/
theorem f5_honest_rules :
    ruleNames f5Honest = ["needs-diff", "set-a", "set-b", "honest-d", "via-honest-d-ab"] := by
  decide +kernel

/-- F5 with `absent-from`: `gen` is accepted and is no rule; `gen-d` is a rule, refused at `a, a`
and used at `a, b`. -/
theorem f5_absent_accepted : accepted f5Absent = ["gen", "gen-d", "via-gen-d-ab"] := by
  decide +kernel

theorem f5_absent_rules :
    ruleNames f5Absent = ["nf", "set-a", "wff-a", "wff-b", "gen-d", "via-gen-d-ab"] := by
  decide +kernel

/-- v2_01: `id`, its use as a rule, a formal cited from the term store, and the same proof under
another name are accepted; the five negatives are not. -/
theorem hilbert_accepted : accepted hilbert = ["id", "id-use", "refl-use", "id-chunked"] := by
  decide +kernel

/-- v2_04 (F1): only the claim whose `dv` comes after the premises binding its variables. -/
theorem order_accepted : accepted order = ["dv-last-claim"] := by decide +kernel

/-- v2_06 (F3): an open and an abstraction with locally closed inputs; the dangling ones refused. -/
theorem binders_accepted : accepted binders = ["beta-ok", "abs-ok"] := by decide +kernel

/-- v2_10: the undeclared independence `nf-accepted` is a verdict only; `nf-declared` and the term over
`x` are rules; `nf-refused` (its formula over `x`) and `bad-kind` (a dependency on a name) are refused. -/
theorem kinds_accepted : accepted kinds = ["nf-accepted", "nf-declared", "dep-term"] := by decide +kernel

theorem kinds_rules : ruleNames kinds = ["all", "ax5", "nf-declared", "dep-term"] := by decide +kernel

/-- v2_11: `proj` and `proj-over` are refused at admission, `var-head` too; `whole` is a rule. -/
theorem opaque_accepted : accepted opaqueHeads = ["whole"] := by decide +kernel

theorem opaque_rules : ruleNames opaqueHeads = ["all", "whole"] := by decide +kernel

/-- v2_12: the right unions and removals are accepted in any order and with duplicates; the wrong ones
are refused; `drop-own` decides a removal on its own names and is a verdict only, `drop-declared`
is a rule; `bad-join` is refused at admission. -/
theorem sets_accepted :
    accepted sets = ["union-ok", "union-dup", "remove-ok", "drop-own", "drop-declared"] := by
  decide +kernel

theorem sets_rules : ruleNames sets =
    ["hs-a", "hs-bc", "join", "drop", "union-ok", "union-dup", "remove-ok", "drop-declared"] := by
  decide +kernel

/-- v2_13: singletons, images under a substitution and atom kinds; `via-name-a` is refused because
the declared `(atom-kind x name)` fails at `x := a`. -/
theorem forms_accepted : accepted forms =
    ["sing-ok", "sing-dup", "image-ok", "sym-ok", "num-ok", "name-own", "name-declared"] := by
  decide +kernel

theorem forms_rules : ruleNames forms =
    ["tm-a", "sing", "hs-fab", "image", "sym-tm", "num-tm", "name-tm", "sing-ok", "sing-dup", "image-ok",
      "sym-ok", "num-ok", "name-declared"] := by
  decide +kernel

/-- v2_14: one child per element, in order; the empty list asks none; wrong order, too few and too
many children are refused, and so is a claim with a list hypothesis. -/
theorem each_accepted : accepted eachWorld = ["each-ok", "each-empty"] := by decide +kernel

theorem each_rules : ruleNames eachWorld = ["tm-a", "tm-b", "all", "each-ok", "each-empty"] := by
  decide +kernel

/-- v2_15: the structural derivation makes `nf-f-named` a rule and leaves `nf-f` a verdict; the rule
refuses `x := (f c d)`. -/
theorem absStruct_accepted : accepted absStructWorld = ["nf-f", "nf-f-named"] := by decide +kernel

theorem absStruct_rules :
    ruleNames absStructWorld = ["ax5", "f-ty", "ty-c", "ty-d", "bv-fcd", "nf-f-named"] := by
  decide +kernel

/-- F6: a scope variable is a name, so `B`'s bound variable does not stand for it: `cap` is refused, and
`via-cap` has no rule `cap` to cite. -/
theorem capture_refused : accepted capture = [] := by decide +kernel

end Controls

end Mettapedia.Logic.TierZero.Kernel2.Examples
