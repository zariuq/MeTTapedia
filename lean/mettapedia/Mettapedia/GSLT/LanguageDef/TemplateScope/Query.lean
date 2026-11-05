import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum

/-!
# Template scope: queries, `case`, and where a pattern's names live

The scope-policy spectrum (`TemplateScope.Spectrum`) has lambdas, `let`,
`unify` and `new`, but no query.  This module adds two pattern constructs to
the authored text and states, as an elaboration into `Src`, every way of
scoping their names that the study compares.

* `QSrc.query p src t xs` — `(match src p t)`: the pattern `p` is matched
  against each value of `src` (a space is the choice `alt` of its facts), and
  the template `t` runs for each match.
* `QSrc.caseS v p b xs` — a one-branch `(case v ((p b)))`: the pattern `p` is
  matched against the value of `v`.

`xs` is a written crossing set, which keeps its meaning under every rule.  Where
none is written, a pattern's names are placed by a **pattern mode**:

* `fresh` — every name is new to the construct (the draft's default, `H0`);
* `correlated` — a name an enclosing binder introduced is that name; every
  other name is new to the construct (`H1`; SQL's correlated subqueries);
* `unit` — every name is the enclosing unit's, as for `unify`: siblings in the
  same unit join on it (`H2`, clause-level sharing).

A lambda without a crossing set is placed by a **lambda mode**: `lexical` (it
introduces nothing; lexical fresh), `queryNames` (it introduces the names its
`unit` patterns write that no enclosing binder introduced), `clause` (it
introduces every name it writes that no enclosing binder introduced: a lambda
is a clause).

Enclosing binders are the explicit ones: an equation head (a `let` from the
parameters), a `let` pattern, a `unify` pattern, a query or `case` pattern for
its template, a `new` block, and a crossing set.  The names a unit introduces
implicitly are not among them.

## Main results

* `toSrc_ofSrc` — **conservativity**: on text without queries and `case`, every
  rule whose lambda mode is not `clause` is the identity, so it elaborates
  exactly as lexical fresh, and every law proved for lexical fresh holds
  unchanged.
* `elabLF_eq_elabQ_of_letFree` — on text without `let`, lexical fresh and
  query-wide elaborate identically: the profiles differ only in `let`.
* `elabLF_toSrc_unit` — a rule whose patterns are `unit` elaborates first-order
  text (no lambda, `let` or `new`) exactly as the query-wide profile, the
  clause-level reading of HE and PeTTa.
* `correlated_intro` — a `correlated` pattern introduces exactly the pattern
  names that no enclosing binder introduced, the binder rule of the PeTTa scope
  contract (`boundNamesFromPattern bound pattern` in
  `Languages/MeTTa/PeTTa/ScopeContract.lean`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

/-- Authored text with queries and one-branch `case`.  Code in a quotation is
`Src`: a query is not written inside code. -/
inductive QSrc (S : Type u) (X : Type v) where
  | sym (s : S)
  | fn (F : S)
  | sv (y : X)
  | par (z : X)
  | lam (z : X) (crossing : Option (List X)) (body : QSrc S X)
  | app (f a : QSrc S X)
  | quote (c : Src S X)
  | pquote (c : Src S X)
  | letS (p w b : QSrc S X) (crossing : Option (List X))
  | unify (p w b : QSrc S X)
  | alt (t₁ t₂ : QSrc S X)
  | new (names : List X) (body : QSrc S X)
  | form (z : X) (body : QSrc S X)
  /-- `(match src p t)`, with its written crossing set. -/
  | query (p src t : QSrc S X) (crossing : Option (List X))
  /-- `(case v ((p b)))`, with its written crossing set. -/
  | caseS (v p b : QSrc S X) (crossing : Option (List X))
  deriving DecidableEq, Repr

/-- How a pattern of a query or `case` without a crossing set places its names. -/
inductive PatMode where
  | fresh
  | correlated
  | unit
  deriving DecidableEq, Repr

/-- What a lambda without a crossing set introduces. -/
inductive LamMode where
  | lexical
  | queryNames
  | clause
  deriving DecidableEq, Repr

/-- A scope rule: a mode for query patterns, one for `case` patterns, and one
for lambdas. -/
structure QRule where
  query : PatMode
  case : PatMode
  lam : LamMode
  deriving DecidableEq, Repr

/-- `H0`, the draft's default: every pattern is fresh. -/
def ruleH0 : QRule := ⟨.fresh, .fresh, .lexical⟩
/-- `H1`: patterns are correlated with the enclosing binders. -/
def ruleH1 : QRule := ⟨.correlated, .correlated, .lexical⟩
/-- `H2`: query and `case` patterns are the clause's, lambdas lexical. -/
def ruleH2 : QRule := ⟨.unit, .unit, .lexical⟩
/-- `H2` where a lambda introduces the names its queries write. -/
def ruleH2q : QRule := ⟨.unit, .unit, .queryNames⟩
/-- Clause units: queries are the unit's, `case` is correlated, a lambda is a
clause. -/
def ruleCU : QRule := ⟨.unit, .correlated, .clause⟩

variable {S : Type u} {X : Type v}

namespace QSrc

/-- Text without queries and `case`. -/
def ofSrc : Src S X → QSrc S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .lam z xs b => .lam z xs (ofSrc b)
  | .app f a => .app (ofSrc f) (ofSrc a)
  | .quote c => .quote c
  | .pquote c => .pquote c
  | .letS p w b xs => .letS (ofSrc p) (ofSrc w) (ofSrc b) xs
  | .unify p w b => .unify (ofSrc p) (ofSrc w) (ofSrc b)
  | .alt t₁ t₂ => .alt (ofSrc t₁) (ofSrc t₂)
  | .new ys b => .new ys (ofSrc b)
  | .form z b => .form z (ofSrc b)

/-- Store names written in a pattern. -/
def patNames : QSrc S X → List X
  | .sv y => [y]
  | .app f a => patNames f ++ patNames a
  | _ => []

/-- Spellings written at the current scope level: outside nested lambdas; a
`new` block, a query and a `case` are not levels of their own. -/
def direct : QSrc S X → List X
  | .sv y => [y]
  | .app f a => direct f ++ direct a
  | .pquote c => Src.codeSvs c
  | .letS p w b _ => direct p ++ direct w ++ direct b
  | .unify p w b => direct p ++ direct w ++ direct b
  | .alt t₁ t₂ => direct t₁ ++ direct t₂
  | .new _ b => direct b
  | .form _ b => direct b
  | .query p s t _ => direct p ++ direct s ++ direct t
  | .caseS w p b _ => direct w ++ direct p ++ direct b
  | _ => []

/-- The names written at the current level in the patterns that a rule places
in the unit: queries and `case`s without a crossing set whose mode is `unit`. -/
def unitPats (r : QRule) : QSrc S X → List X
  | .app f a => unitPats r f ++ unitPats r a
  | .letS p w b _ => unitPats r p ++ unitPats r w ++ unitPats r b
  | .unify p w b => unitPats r p ++ unitPats r w ++ unitPats r b
  | .alt t₁ t₂ => unitPats r t₁ ++ unitPats r t₂
  | .new _ b => unitPats r b
  | .form _ b => unitPats r b
  | .query p s t xs =>
      (if r.query = .unit ∧ xs = none then patNames p else []) ++ unitPats r s ++ unitPats r t
  | .caseS w p b xs =>
      (if r.case = .unit ∧ xs = none then patNames p else []) ++ unitPats r w ++ unitPats r b
  | _ => []

end QSrc

variable [DecidableEq X]

namespace QSrc

/-- The names a lambda without a crossing set introduces, given the names `B`
that enclosing binders introduced. -/
def unitNames (r : QRule) (B : List X) (b : QSrc S X) : List X :=
  match r.lam with
  | .lexical => []
  | .queryNames => ((unitPats r b).filter fun y => decide (y ∉ B)).dedup
  | .clause => ((direct b).filter fun y => decide (y ∉ B)).dedup

end QSrc

/-- A pattern construct, elaborated into `Src` by its mode: a written crossing
set is kept; `fresh` is a plain `let`; `correlated` is a `let` whose crossing set
is the pattern's names that `B` holds; `unit` is `unify`. -/
def patConstruct (m : PatMode) (B pn : List X) (xs : Option (List X)) (p w b : Src S X) :
    Src S X :=
  match xs with
  | some sh => .letS p w b (some sh)
  | none =>
      match m with
      | .fresh => .letS p w b none
      | .correlated => .letS p w b (some (pn.filter fun y => decide (y ∈ B)))
      | .unit => .unify p w b

/-- A lambda without a crossing set: wrap its body in a `new` block for the
names it introduces, if any. -/
def lamWith (z : X) (U : List X) (body : Src S X) : Src S X :=
  match U with
  | [] => .lam z none body
  | y₀ :: ys => .lam z none (.new (y₀ :: ys) body)

namespace QSrc

/-- **The elaboration of a rule into `Src`.**  `B` lists the names enclosing
binders introduced. -/
def toSrc (r : QRule) (B : List X) : QSrc S X → Src S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .lam z none b => lamWith z (unitNames r B b) (toSrc r B b)
  | .lam z (some sh) b => .lam z (some sh) (toSrc r (B ++ sh) b)
  | .app f a => .app (toSrc r B f) (toSrc r B a)
  | .quote c => .quote c
  | .pquote c => .pquote c
  | .letS p w b xs =>
      .letS (toSrc r B p) (toSrc r B w) (toSrc r (B ++ patNames p ++ xs.getD []) b) xs
  | .unify p w b => .unify (toSrc r B p) (toSrc r B w) (toSrc r (B ++ patNames p) b)
  | .alt t₁ t₂ => .alt (toSrc r B t₁) (toSrc r B t₂)
  | .new ys b => .new ys (toSrc r (B ++ ys) b)
  | .form z b => .form z (toSrc r B b)
  | .query p s t xs =>
      patConstruct r.query B (patNames p) xs (toSrc r B p) (toSrc r B s)
        (toSrc r (B ++ patNames p ++ xs.getD []) t)
  | .caseS w p b xs =>
      patConstruct r.case B (patNames p) xs (toSrc r B p) (toSrc r B w)
        (toSrc r (B ++ patNames p ++ xs.getD []) b)

omit [DecidableEq X] in
/-- Text without queries writes no `unit` pattern. -/
theorem unitPats_ofSrc (r : QRule) : ∀ t : Src S X, unitPats r (ofSrc t) = []
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .lam _ _ _ => rfl
  | .app f a => by simp [ofSrc, unitPats, unitPats_ofSrc r f, unitPats_ofSrc r a]
  | .quote _ => rfl
  | .pquote _ => rfl
  | .letS p w b _ => by
      simp [ofSrc, unitPats, unitPats_ofSrc r p, unitPats_ofSrc r w, unitPats_ofSrc r b]
  | .unify p w b => by
      simp [ofSrc, unitPats, unitPats_ofSrc r p, unitPats_ofSrc r w, unitPats_ofSrc r b]
  | .alt t₁ t₂ => by simp [ofSrc, unitPats, unitPats_ofSrc r t₁, unitPats_ofSrc r t₂]
  | .new _ b => by simp [ofSrc, unitPats, unitPats_ofSrc r b]
  | .form _ b => by simp [ofSrc, unitPats, unitPats_ofSrc r b]

/-- On text without queries, a lambda introduces nothing under every lambda
mode but `clause`. -/
theorem unitNames_ofSrc {r : QRule} (hr : r.lam ≠ .clause) (B : List X) (b : Src S X) :
    unitNames r B (ofSrc b) = [] := by
  unfold unitNames
  cases h : r.lam with
  | lexical => rfl
  | queryNames => simp [unitPats_ofSrc]
  | clause => exact absurd h hr

/-- **Conservativity.**  On text without queries and `case`, every rule whose
lambda mode is not `clause` is the identity.  Hence it elaborates every such
form exactly as lexical fresh does, under every configuration, and every law
proved for lexical fresh (modularity, inlining, formed lambdas, independent
calls) holds for it unchanged. -/
theorem toSrc_ofSrc {r : QRule} (hr : r.lam ≠ .clause) :
    ∀ (B : List X) (t : Src S X), toSrc r B (ofSrc t) = t
  | _, .sym _ => rfl
  | _, .fn _ => rfl
  | _, .sv _ => rfl
  | _, .par _ => rfl
  | B, .lam z none b => by
      simp only [ofSrc, toSrc, unitNames_ofSrc hr, lamWith, toSrc_ofSrc hr B b]
  | B, .lam z (some sh) b => by
      simp only [ofSrc, toSrc, toSrc_ofSrc hr (B ++ sh) b]
  | B, .app f a => by simp only [ofSrc, toSrc, toSrc_ofSrc hr B f, toSrc_ofSrc hr B a]
  | _, .quote _ => rfl
  | _, .pquote _ => rfl
  | B, .letS p w b xs => by
      simp only [ofSrc, toSrc, toSrc_ofSrc hr B p, toSrc_ofSrc hr B w, toSrc_ofSrc hr _ b]
  | B, .unify p w b => by
      simp only [ofSrc, toSrc, toSrc_ofSrc hr B p, toSrc_ofSrc hr B w, toSrc_ofSrc hr _ b]
  | B, .alt t₁ t₂ => by simp only [ofSrc, toSrc, toSrc_ofSrc hr B t₁, toSrc_ofSrc hr B t₂]
  | B, .new ys b => by simp only [ofSrc, toSrc, toSrc_ofSrc hr (B ++ ys) b]
  | B, .form z b => by simp only [ofSrc, toSrc, toSrc_ofSrc hr B b]

/-- Conservativity at the level of the elaborated term, for every ownership
profile of the spectrum. -/
theorem elabForm_toSrc_ofSrc {r : QRule} (hr : r.lam ≠ .clause) (o : Ownership) (root : Owner)
    (t : Src S X) : elabForm o root (toSrc r [] (ofSrc t)) = elabForm o root t := by
  rw [toSrc_ofSrc hr]

end QSrc

/-! ## The correlated mode is the scope contract's binder rule -/

/-- The names a written or computed crossing set leaves new to a pattern:
`lfIntro` with a crossing set written. -/
theorem lfIntro_some (sh : List X) (p : Src S X) (cr : List X) :
    lfIntro (some sh) p cr = ((Src.patNames p).filter fun y => decide (y ∉ sh)).dedup := rfl

theorem patNames_toSrc (r : QRule) (B : List X) :
    ∀ p : QSrc S X, Src.patNames (QSrc.toSrc r B p) = QSrc.patNames p := by
  intro p
  induction p generalizing B with
  | sym _ => rfl
  | fn _ => rfl
  | sv _ => rfl
  | par _ => rfl
  | lam z xs b _ =>
      cases xs with
      | none =>
          simp only [QSrc.toSrc, QSrc.patNames]
          unfold lamWith
          split <;> rfl
      | some _ => rfl
  | app f a ihf iha => simp [QSrc.toSrc, QSrc.patNames, Src.patNames, ihf, iha]
  | quote _ => rfl
  | pquote _ => rfl
  | letS _ _ _ _ _ _ _ => rfl
  | unify _ _ _ _ _ _ => rfl
  | alt _ _ _ _ => rfl
  | new _ _ _ => rfl
  | form _ _ _ => rfl
  | query p s t xs _ _ _ =>
      cases xs with
      | some _ => rfl
      | none =>
          cases h : r.query <;> simp [QSrc.toSrc, patConstruct, h, QSrc.patNames, Src.patNames]
  | caseS w p b xs _ _ _ =>
      cases xs with
      | some _ => rfl
      | none =>
          cases h : r.case <;> simp [QSrc.toSrc, patConstruct, h, QSrc.patNames, Src.patNames]

/-- **The correlated mode introduces exactly the contract's binder names.**  A
query without a crossing set, under a `correlated` rule, elaborates to a `let`
whose new names (`lfIntro`, in every context `cr`) are its pattern's names that
no enclosing binder introduced: the rule `boundNamesFromPattern bound binder`
of the PeTTa scope contract, where `bound` lists the names enclosing binders
introduced. -/
theorem correlated_intro (r : QRule) (hq : r.query = .correlated) (B : List X)
    (p s t : QSrc S X) (cr : List X) :
    QSrc.toSrc r B (.query p s t none) =
        .letS (QSrc.toSrc r B p) (QSrc.toSrc r B s) (QSrc.toSrc r (B ++ QSrc.patNames p) t)
          (some ((QSrc.patNames p).filter fun y => decide (y ∈ B))) ∧
      lfIntro (some ((QSrc.patNames p).filter fun y => decide (y ∈ B))) (QSrc.toSrc r B p) cr =
        ((QSrc.patNames p).filter fun y => decide (y ∉ B)).dedup := by
  refine ⟨by simp [QSrc.toSrc, patConstruct, hq], ?_⟩
  rw [lfIntro_some, patNames_toSrc]
  congr 1
  apply List.filter_congr
  intro y hy
  by_cases hB : y ∈ B <;> simp [hB, hy]

/-! ## Lexical fresh and query-wide differ only in `let` -/

namespace Src

/-- Text without `let`. -/
def letFree : Src S X → Bool
  | .lam _ _ b => letFree b
  | .app f a => letFree f && letFree a
  | .letS _ _ _ _ => false
  | .unify p w b => letFree p && letFree w && letFree b
  | .alt t₁ t₂ => letFree t₁ && letFree t₂
  | .new _ b => letFree b
  | .form _ b => letFree b
  | _ => true

end Src

/-- **On text without `let`, lexical fresh and query-wide elaborate
identically**, whatever the names in force: the two profiles differ only in
how a `let` pattern places its names. -/
theorem elabLF_eq_elabQ_of_letFree (R : Owner) :
    ∀ (t : Src S X) (env : REnv X) (cr : List X) (pos : Owner), t.letFree = true →
      elabLF R env cr pos t = elabQ R env pos t
  | .sym _, _, _, _, _ => rfl
  | .fn _, _, _, _, _ => rfl
  | .sv _, _, _, _, _ => rfl
  | .par _, _, _, _, _ => rfl
  | .lam z xs b, env, cr, pos, h => by
      simp only [Src.letFree] at h
      simp only [elabLF, elabQ]
      rw [elabLF_eq_elabQ_of_letFree R b _ _ _ h]
  | .app f a, env, cr, pos, h => by
      simp only [Src.letFree, Bool.and_eq_true] at h
      simp only [elabLF, elabQ]
      rw [elabLF_eq_elabQ_of_letFree R f _ _ _ h.1, elabLF_eq_elabQ_of_letFree R a _ _ _ h.2]
  | .quote _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _ => rfl
  | .letS _ _ _ _, _, _, _, h => by simp [Src.letFree] at h
  | .unify p w b, env, cr, pos, h => by
      simp only [Src.letFree, Bool.and_eq_true] at h
      simp only [elabLF, elabQ]
      rw [elabLF_eq_elabQ_of_letFree R p _ _ _ h.1.1, elabLF_eq_elabQ_of_letFree R w _ _ _ h.1.2,
        elabLF_eq_elabQ_of_letFree R b _ _ _ h.2]
  | .alt t₁ t₂, env, cr, pos, h => by
      simp only [Src.letFree, Bool.and_eq_true] at h
      simp only [elabLF, elabQ]
      rw [elabLF_eq_elabQ_of_letFree R t₁ _ _ _ h.1, elabLF_eq_elabQ_of_letFree R t₂ _ _ _ h.2]
  | .new [] b, env, cr, pos, h => by
      simp only [Src.letFree] at h
      simp only [elabLF, elabQ]
      exact elabLF_eq_elabQ_of_letFree R b _ _ _ h
  | .new (y₀ :: ys) b, env, cr, pos, h => by
      simp only [Src.letFree] at h
      simp only [elabLF, elabQ]
      rw [elabLF_eq_elabQ_of_letFree R b _ _ _ h]
  | .form z b, env, cr, pos, h => by
      simp only [Src.letFree] at h
      simp only [elabLF, elabQ]
      rw [elabLF_eq_elabQ_of_letFree R b _ _ _ h]

/-! ## Clause-level agreement of the `unit` mode on first-order text -/

namespace QSrc

/-- First-order text: no lambda, `let`, `new`, formed lambda or quotation. -/
def firstOrder : QSrc S X → Bool
  | .sym _ => true
  | .fn _ => true
  | .sv _ => true
  | .par _ => true
  | .app f a => firstOrder f && firstOrder a
  | .unify p w b => firstOrder p && firstOrder w && firstOrder b
  | .alt t₁ t₂ => firstOrder t₁ && firstOrder t₂
  | .query p s t xs => xs.isNone && firstOrder p && firstOrder s && firstOrder t
  | .caseS w p b xs => xs.isNone && firstOrder w && firstOrder p && firstOrder b
  | _ => false

/-- Under a rule whose query and `case` modes are `unit`, first-order text
elaborates into text without `let`. -/
theorem letFree_toSrc_unit {r : QRule} (hq : r.query = .unit) (hc : r.case = .unit) :
    ∀ (B : List X) (t : QSrc S X), t.firstOrder = true → (toSrc r B t).letFree = true
  | _, .sym _, _ => rfl
  | _, .fn _, _ => rfl
  | _, .sv _, _ => rfl
  | _, .par _, _ => rfl
  | B, .app f a, h => by
      simp only [firstOrder, Bool.and_eq_true] at h
      simp only [toSrc, Src.letFree, Bool.and_eq_true]
      exact ⟨letFree_toSrc_unit hq hc B f h.1, letFree_toSrc_unit hq hc B a h.2⟩
  | B, .unify p w b, h => by
      simp only [firstOrder, Bool.and_eq_true] at h
      simp only [toSrc, Src.letFree, Bool.and_eq_true]
      exact ⟨⟨letFree_toSrc_unit hq hc B p h.1.1, letFree_toSrc_unit hq hc B w h.1.2⟩,
        letFree_toSrc_unit hq hc _ b h.2⟩
  | B, .alt t₁ t₂, h => by
      simp only [firstOrder, Bool.and_eq_true] at h
      simp only [toSrc, Src.letFree, Bool.and_eq_true]
      exact ⟨letFree_toSrc_unit hq hc B t₁ h.1, letFree_toSrc_unit hq hc B t₂ h.2⟩
  | B, .query p s t xs, h => by
      simp only [firstOrder, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨⟨hx, hp⟩, hs⟩, ht⟩ := h
      subst hx
      simp only [toSrc, patConstruct, hq, Src.letFree, Bool.and_eq_true]
      exact ⟨⟨letFree_toSrc_unit hq hc B p hp, letFree_toSrc_unit hq hc B s hs⟩,
        letFree_toSrc_unit hq hc _ t ht⟩
  | B, .caseS w p b xs, h => by
      simp only [firstOrder, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨⟨hx, hw⟩, hp⟩, hb⟩ := h
      subst hx
      simp only [toSrc, patConstruct, hc, Src.letFree, Bool.and_eq_true]
      exact ⟨⟨letFree_toSrc_unit hq hc B p hp, letFree_toSrc_unit hq hc B w hw⟩,
        letFree_toSrc_unit hq hc _ b hb⟩
  | _, .lam _ _ _, h => by simp [firstOrder] at h
  | _, .quote _, h => by simp [firstOrder] at h
  | _, .pquote _, h => by simp [firstOrder] at h
  | _, .letS _ _ _ _, h => by simp [firstOrder] at h
  | _, .new _ _, h => by simp [firstOrder] at h
  | _, .form _ _, h => by simp [firstOrder] at h

/-- **Clause-level agreement of the `unit` mode.**  A rule whose query and `case`
patterns are the unit's elaborates first-order text, under lexical fresh,
exactly as the query-wide profile does: one slot per spelling per form, every
pattern refining it, the clause-level reading that HE and PeTTa run. -/
theorem elabLF_toSrc_unit {r : QRule} (hq : r.query = .unit) (hc : r.case = .unit)
    (R : Owner) (env : REnv X) (cr : List X) (pos : Owner) (B : List X) (t : QSrc S X)
    (h : t.firstOrder = true) :
    elabLF R env cr pos (toSrc r B t) = elabQ R env pos (toSrc r B t) :=
  elabLF_eq_elabQ_of_letFree R _ env cr pos (letFree_toSrc_unit hq hc B t h)

end QSrc

end Mettapedia.GSLT.LanguageDef.TemplateScope
