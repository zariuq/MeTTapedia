import Mettapedia.GSLT.LanguageDef.TemplateScope.RolesLawsNecessity
import Mettapedia.GSLT.LanguageDef.TemplateScope.QueryCorpus

/-!
# Binding by role: MeTTa as one signature, the query rules as instances

* `sigMeTTa` — MeTTa's constructs as one binding signature: `match`, `unify` and
  transform ports are relations; `case` and `switch` branches are testing
  arrows; `let` and `chain` are shadowing arrows; lambdas, templates, equations
  and standing rules are frames under the clause policy, without implicit
  nested capture.
* `sigOfRule` — every rule `QRule` of the query study is a signature on the
  same constructs (`PatMode` gives the role, `LamMode` the frame policy), and
  `sigOfRule ruleCU = sigMeTTa`: clause units are the principle's signature.
* `toSrcR_embedQ` — **the generic lowering equals `QSrc.toSrc`** for every rule
  whose lambdas are lexical or clause, on the fragment `inFragment`: no
  quotation; under the clause policy, no lambda reads a name only through a
  crossing set; no sealed lambda reads a name only through nested closures.
* Each excluded feature is a place where the principle and the query model
  differ, with a separating example computed by the evaluator of
  `TemplateScope.Evaluation`:
  - `nested_crossing_separates` — a name passed into a nested lambda by its
    crossing set is shared by all calls of the enclosing lambda under `ruleCU`
    (no answer), and private per call under the principle;
  - `sealed_transitive_separates` — a sealed lambda `{}` under `ruleCU` lets a
    nested closure see an outer `let`; under the principle sealing covers
    nested closures; and under `ruleCU` the nested closure's meaning changes
    when `$u` is written at the sealed level (a binder of the context moves);
  - quotation: `quote_holes_root` — the slot model resolves every hole of
    sealed code to the form's root, so two calls of a lambda that quotes `$y`
    quote one `$y`; the resolution gives the lambda's own `$y`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles

open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

/-- MeTTa's pattern constructs. -/
inductive MC where
  /-- `(match space pattern template)` -/
  | matchQ
  /-- `(unify value pattern then …)` -/
  | unifyR
  /-- a port of a transform -/
  | portR
  /-- one branch of `(case value ((pattern body) …))` -/
  | caseB
  /-- one branch of `switch` -/
  | switchB
  /-- `(let pattern value body)` -/
  | letA
  /-- `(chain value $x body)` -/
  | chainA
  deriving DecidableEq, Repr

/-- **MeTTa's binding signature under the principle.** -/
def sigMeTTa : Signature MC where
  role
    | .matchQ => .rel
    | .unifyR => .rel
    | .portR => .rel
    | .caseB => .arrow .test
    | .switchB => .arrow .test
    | .letA => .arrow .shadow
    | .chainA => .arrow .shadow
  order
    | .caseB => .valueFirst
    | .switchB => .valueFirst
    | _ => .patternFirst
  frame := .clause
  capture := false

/-- The role of a pattern mode of the query study. -/
def roleOfMode : PatMode → PatRole
  | .fresh => .arrow .shadow
  | .correlated => .arrow .test
  | .unit => .rel

/-- The frame policy of a lambda mode of the query study. -/
def policyOfLam : LamMode → FramePolicy
  | .lexical => .lexical
  | .queryNames => .relNames
  | .clause => .clause

/-- **A rule of the query study as a signature.**  Queries and `case` take the
rule's modes; `let` is a shadowing arrow and `unify` a relation under every
rule. -/
def sigOfRule (r : QRule) : Signature MC where
  role
    | .matchQ => roleOfMode r.query
    | .portR => roleOfMode r.query
    | .caseB => roleOfMode r.case
    | .switchB => roleOfMode r.case
    | .letA => .arrow .shadow
    | .chainA => .arrow .shadow
    | .unifyR => .rel
  order := sigMeTTa.order
  frame := policyOfLam r.lam
  capture := false

/-- **Clause units are the principle's signature.** -/
theorem sigOfRule_CU : sigOfRule ruleCU = sigMeTTa := by
  simp only [sigOfRule, sigMeTTa, ruleCU, policyOfLam, Signature.mk.injEq, and_true]
  funext c
  cases c <;> rfl

theorem stable_sigMeTTa : Stable sigMeTTa := ⟨Or.inr rfl, rfl⟩

@[simp] theorem sigOfRule_order (r : QRule) (c : MC) : (sigOfRule r).order c = sigMeTTa.order c :=
  rfl

@[simp] theorem sigOfRule_capture (r : QRule) : (sigOfRule r).capture = false := rfl

/-- `H0`, `H1`, `H2` and clause units are stable; `H2q` is not. -/
theorem stable_sigOfRule (r : QRule) (hr : r.lam ≠ .queryNames) : Stable (sigOfRule r) := by
  refine ⟨?_, rfl⟩
  cases h : r.lam with
  | lexical => exact Or.inl (by simp [sigOfRule, policyOfLam, h])
  | queryNames => exact absurd h hr
  | clause => exact Or.inr (by simp [sigOfRule, policyOfLam, h])

variable {S : Type u} {X : Type v}

/-! ## The query model inside the generic one -/

/-- Text without queries, with `let` a shadowing arrow and `unify` a relation. -/
def embedSrc : Src S X → RSrc MC S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .lam z xs b => .frame z xs (embedSrc b)
  | .app f a => .app (embedSrc f) (embedSrc a)
  | .quote c => .quote (embedSrc c)
  | .pquote c => .pquote (embedSrc c)
  | .letS p w b xs => .pat .letA (embedSrc p) (embedSrc w) (embedSrc b) xs
  | .unify p w b => .pat .unifyR (embedSrc p) (embedSrc w) (embedSrc b) none
  | .alt t₁ t₂ => .alt (embedSrc t₁) (embedSrc t₂)
  | .new ys b => .new ys (embedSrc b)
  | .form z b => .form z (embedSrc b)

/-- The query model's text, with queries and `case` as their constructs. -/
def embedQ : QSrc S X → RSrc MC S X
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => .sv y
  | .par z => .par z
  | .lam z xs b => .frame z xs (embedQ b)
  | .app f a => .app (embedQ f) (embedQ a)
  | .quote c => .quote (embedSrc c)
  | .pquote c => .pquote (embedSrc c)
  | .letS p w b xs => .pat .letA (embedQ p) (embedQ w) (embedQ b) xs
  | .unify p w b => .pat .unifyR (embedQ p) (embedQ w) (embedQ b) none
  | .alt t₁ t₂ => .alt (embedQ t₁) (embedQ t₂)
  | .new ys b => .new ys (embedQ b)
  | .form z b => .form z (embedQ b)
  | .query p s t xs => .pat .matchQ (embedQ p) (embedQ s) (embedQ t) xs
  | .caseS w p b xs => .pat .caseB (embedQ p) (embedQ w) (embedQ b) xs

theorem patNames_embedQ : ∀ p : QSrc S X, (embedQ p).patNames = QSrc.patNames p
  | .sv _ => rfl
  | .app f a => by simp [embedQ, RSrc.patNames, QSrc.patNames, patNames_embedQ f, patNames_embedQ a]
  | .sym _ => rfl
  | .fn _ => rfl
  | .par _ => rfl
  | .lam _ _ _ => rfl
  | .quote _ => rfl
  | .pquote _ => rfl
  | .letS _ _ _ _ => rfl
  | .unify _ _ _ => rfl
  | .alt _ _ => rfl
  | .new _ _ => rfl
  | .form _ _ => rfl
  | .query _ _ _ _ => rfl
  | .caseS _ _ _ _ => rfl

/-- Text without quotation. -/
def qFree : QSrc S X → Bool
  | .quote _ => false
  | .pquote _ => false
  | .lam _ _ b => qFree b
  | .app f a => qFree f && qFree a
  | .letS p w b _ => qFree p && qFree w && qFree b
  | .unify p w b => qFree p && qFree w && qFree b
  | .alt t₁ t₂ => qFree t₁ && qFree t₂
  | .new _ b => qFree b
  | .form _ b => qFree b
  | .query p s t _ => qFree p && qFree s && qFree t
  | .caseS w p b _ => qFree w && qFree p && qFree b
  | _ => true

/-- On text without quotation, the names written at a level are the query
model's `direct`. -/
theorem dir_embedQ (r : QRule) :
    ∀ q : QSrc S X, qFree q = true → (embedQ q).dir (sigOfRule r) = QSrc.direct q
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .lam _ _ _, _ => rfl
  | .app f a, h => by
      simp only [qFree, Bool.and_eq_true] at h
      simp [embedQ, RSrc.dir, QSrc.direct, dir_embedQ r f h.1, dir_embedQ r a h.2]
  | .quote _, h => by simp [qFree] at h
  | .pquote _, h => by simp [qFree] at h
  | .letS p w b _, h => by
      simp only [qFree, Bool.and_eq_true] at h
      simp [embedQ, RSrc.dir, QSrc.direct, sigOfRule_order, sigMeTTa, dir_embedQ r p h.1.1,
        dir_embedQ r w h.1.2, dir_embedQ r b h.2]
  | .unify p w b, h => by
      simp only [qFree, Bool.and_eq_true] at h
      simp [embedQ, RSrc.dir, QSrc.direct, sigOfRule_order, sigMeTTa, dir_embedQ r p h.1.1,
        dir_embedQ r w h.1.2, dir_embedQ r b h.2]
  | .alt t₁ t₂, h => by
      simp only [qFree, Bool.and_eq_true] at h
      simp [embedQ, RSrc.dir, QSrc.direct, dir_embedQ r t₁ h.1, dir_embedQ r t₂ h.2]
  | .new _ b, h => by
      simp only [qFree] at h
      simp [embedQ, RSrc.dir, QSrc.direct, dir_embedQ r b h]
  | .form _ b, h => by
      simp only [qFree] at h
      simp [embedQ, RSrc.dir, QSrc.direct, dir_embedQ r b h]
  | .query p s t _, h => by
      simp only [qFree, Bool.and_eq_true] at h
      simp [embedQ, RSrc.dir, QSrc.direct, sigOfRule_order, sigMeTTa, dir_embedQ r p h.1.1,
        dir_embedQ r s h.1.2, dir_embedQ r t h.2]
  | .caseS w p b _, h => by
      simp only [qFree, Bool.and_eq_true] at h
      simp [embedQ, RSrc.dir, QSrc.direct, sigOfRule_order, sigMeTTa, dir_embedQ r w h.1.1,
        dir_embedQ r p h.1.2, dir_embedQ r b h.2]

variable [DecidableEq X]

/-- The part of a clause frame's own list beyond the query model's: crossing
names written at its level and nowhere else at it. -/
def crossExtras (σ : Signature MC) (B : List X) (b : RSrc MC S X) : List X :=
  ((b.crs.filter fun y => decide (y ∉ B ∧ y ∉ ((b.dir σ).filter fun y => decide (y ∉ B)).dedup))).dedup

theorem own_clause_split {σ : Signature MC} (hσ : σ.frame = .clause) (B : List X)
    (b : RSrc MC S X) :
    own σ B b = ((b.dir σ).filter fun y => decide (y ∉ B)).dedup ++ crossExtras σ B b := by
  simp [own, hσ, crossExtras]

/-- **The fragment on which the query model and the principle agree.**  No
quotation; under the clause policy no lambda reads a name only through a
crossing set; no sealed lambda reads a name only through nested closures. -/
def inFragment (σ : Signature MC) : List X → QSrc S X → Bool
  | _, .quote _ => false
  | _, .pquote _ => false
  | B, .lam _ none b =>
      qFree b && (σ.frame != .clause || (crossExtras σ B (embedQ b)).isEmpty) && inFragment σ B b
  | B, .lam _ (some sh) b =>
      (sealExtra σ B sh (embedQ b) (toSrcR σ (B ++ sh) (embedQ b))).isEmpty &&
        inFragment σ (B ++ sh) b
  | B, .app f a => inFragment σ B f && inFragment σ B a
  | B, .letS p w b xs =>
      inFragment σ B p && inFragment σ B w && inFragment σ (B ++ QSrc.patNames p ++ xs.getD []) b
  | B, .unify p w b =>
      inFragment σ B p && inFragment σ B w && inFragment σ (B ++ QSrc.patNames p) b
  | B, .alt t₁ t₂ => inFragment σ B t₁ && inFragment σ B t₂
  | B, .new ys b => inFragment σ (B ++ ys) b
  | B, .form _ b => inFragment σ B b
  | B, .query p s t xs =>
      inFragment σ B p && inFragment σ B s && inFragment σ (B ++ QSrc.patNames p ++ xs.getD []) t
  | B, .caseS w p b xs =>
      inFragment σ B w && inFragment σ B p && inFragment σ (B ++ QSrc.patNames p ++ xs.getD []) b
  | _, _ => true

theorem lowerPat_roleOfMode (m : PatMode) (B pn : List X) (xs : Option (List X))
    (p w b : Src S X) : lowerPat (roleOfMode m) B pn xs p w b = patConstruct m B pn xs p w b := by
  cases xs with
  | some _ => rfl
  | none => cases m <;> rfl

/-- **T3: the generic lowering is the query model's elaboration**, for every
rule whose lambdas are lexical or clause units, on the fragment. -/
theorem toSrcR_embedQ (r : QRule) (hr : r.lam ≠ .queryNames) :
    ∀ (B : List X) (q : QSrc S X), inFragment (sigOfRule r) B q = true →
      toSrcR (sigOfRule r) B (embedQ q) = QSrc.toSrc r B q
  | _, .sym _, _ => rfl
  | _, .fn _, _ => rfl
  | _, .sv _, _ => rfl
  | _, .par _, _ => rfl
  | _, .quote _, h => by simp [inFragment] at h
  | _, .pquote _, h => by simp [inFragment] at h
  | B, .lam z none b, h => by
      simp only [inFragment, Bool.and_eq_true] at h
      obtain ⟨⟨hq, hx⟩, hb⟩ := h
      have hown : own (sigOfRule r) B (embedQ b) = QSrc.unitNames r B b := by
        cases hl : r.lam with
        | lexical =>
            rw [own_lexical (by simp [sigOfRule, policyOfLam, hl])]
            simp [QSrc.unitNames, hl]
        | queryNames => exact absurd hl hr
        | clause =>
            have hσ : (sigOfRule r).frame = .clause := by simp [sigOfRule, policyOfLam, hl]
            rw [own_clause_split hσ, dir_embedQ r b hq]
            have he : crossExtras (sigOfRule r) B (embedQ b) = [] := by
              simpa [hσ] using hx
            rw [he, List.append_nil]
            simp [QSrc.unitNames, hl]
      simp only [embedQ, toSrcR, QSrc.toSrc, hown, bodyB_of_capture (sigOfRule_capture r)]
      rw [toSrcR_embedQ r hr B b hb]
  | B, .lam z (some sh) b, h => by
      simp only [inFragment, Bool.and_eq_true, List.isEmpty_iff] at h
      obtain ⟨he, hb⟩ := h
      simp only [embedQ, toSrcR, QSrc.toSrc, he, newWrap]
      rw [toSrcR_embedQ r hr (B ++ sh) b hb]
  | B, .app f a, h => by
      simp only [inFragment, Bool.and_eq_true] at h
      simp only [embedQ, toSrcR, QSrc.toSrc, toSrcR_embedQ r hr B f h.1,
        toSrcR_embedQ r hr B a h.2]
  | B, .alt t₁ t₂, h => by
      simp only [inFragment, Bool.and_eq_true] at h
      simp only [embedQ, toSrcR, QSrc.toSrc, toSrcR_embedQ r hr B t₁ h.1,
        toSrcR_embedQ r hr B t₂ h.2]
  | B, .new ys b, h => by
      simp only [inFragment] at h
      simp only [embedQ, toSrcR, QSrc.toSrc, toSrcR_embedQ r hr (B ++ ys) b h]
  | B, .form z b, h => by
      simp only [inFragment] at h
      simp only [embedQ, toSrcR, QSrc.toSrc, toSrcR_embedQ r hr B b h]
  | B, .letS p w b xs, h => by
      simp only [inFragment, Bool.and_eq_true] at h
      have hp := toSrcR_embedQ r hr B p h.1.1
      have hw := toSrcR_embedQ r hr B w h.1.2
      have hb := toSrcR_embedQ r hr _ b h.2
      simp only [embedQ, toSrcR, QSrc.toSrc, patB, patNames_embedQ, hp, hw, hb]
      cases xs <;> rfl
  | B, .unify p w b, h => by
      simp only [inFragment, Bool.and_eq_true] at h
      have hp := toSrcR_embedQ r hr B p h.1.1
      have hw := toSrcR_embedQ r hr B w h.1.2
      have hb := toSrcR_embedQ r hr _ b h.2
      simp only [embedQ, toSrcR, QSrc.toSrc, patB, patNames_embedQ, Option.getD_none,
        List.append_nil, hp, hw, hb]
      rfl
  | B, .query p s t xs, h => by
      simp only [inFragment, Bool.and_eq_true] at h
      have hp := toSrcR_embedQ r hr B p h.1.1
      have hs := toSrcR_embedQ r hr B s h.1.2
      have ht := toSrcR_embedQ r hr _ t h.2
      simp only [embedQ, toSrcR, QSrc.toSrc, patB, patNames_embedQ, hp, hs, ht]
      exact lowerPat_roleOfMode _ _ _ _ _ _ _
  | B, .caseS w p b xs, h => by
      simp only [inFragment, Bool.and_eq_true] at h
      have hw := toSrcR_embedQ r hr B w h.1.1
      have hp := toSrcR_embedQ r hr B p h.1.2
      have hb := toSrcR_embedQ r hr _ b h.2
      simp only [embedQ, toSrcR, QSrc.toSrc, patB, patNames_embedQ, hp, hw, hb]
      exact lowerPat_roleOfMode _ _ _ _ _ _ _

/-- **Clause units, as the principle's signature**, on the fragment. -/
theorem toSrcR_embedQ_CU (B : List X) (q : QSrc S X) (h : inFragment sigMeTTa B q = true) :
    toSrcR sigMeTTa B (embedQ q) = QSrc.toSrc ruleCU B q := by
  rw [← sigOfRule_CU] at h ⊢
  exact toSrcR_embedQ ruleCU (by decide) B q h

/-! ## The query corpus under the principle's signature -/

namespace Corpus

open QueryCorpus

/-- The program of a signature: each clause of the query corpus lowered. -/
def progR (σ : Signature MC) : QSy → Option T :=
  fun F => (clauses F).map fun body => clauseOf cfgLF [5] .uu .unit (toSrcR σ [] (embedQ body))

/-- Answers of authored text under a signature. -/
def ansR (σ : Signature MC) (t : RSrc MC QSy QSp) : Option (List T) :=
  answersCfg cfgLF (progR σ) 80 (toSrcR σ [] t)

theorem progR_CU : progR sigMeTTa = progOf ruleCU := by
  funext F
  cases F <;> rfl

/-- On the fragment, the principle's signature answers as clause units. -/
theorem ansR_eq_ans (t : A) (ht : inFragment sigMeTTa [] t = true) :
    ansR sigMeTTa (embedQ t) = ans ruleCU t := by
  simp only [ansR, ans, progR_CU, toSrcR_embedQ_CU [] t ht]

/-- The probe battery of the query study. -/
def battery : List A :=
  [lookupB, nested, siblings, siblingsNew, usedAfter, twoCalls, siblingCases, isbA, heldPattern,
    stabilityCtx holeOk, stabilityCtx holeQuery, letArrow, caseAfter]

/-- **The battery lies in the fragment**, so on every row the principle's
signature answers exactly as clause units (`QueryCorpus.transparency` …
`case_after`, fifth column). -/
theorem battery_in_fragment : battery.all (fun t => inFragment sigMeTTa [] t) = true := by
  decide

theorem battery_CU : ∀ t ∈ battery, ansR sigMeTTa (embedQ t) = ans ruleCU t := by
  intro t ht
  have := List.all_eq_true.1 battery_in_fragment t ht
  exact ansR_eq_ans t this

/-! ## Where the query model and the principle differ -/

/-- `(let $f (lam z (let $d (lam r {$y} (unify $y r $y)) ($d z))) (Pair ($f a) ($f b)))`:
the inner lambda passes `$y` in from the enclosing lambda. -/
def nestedCross : A :=
  lt .f (lm .z (lt .d (.lam .r (some [.y]) (.unify (sv .y) (pr .r) (sv .y))) (ap (sv .d) (pr .z))))
    (pair (ap (sv .f) (k .ka)) (ap (sv .f) (k .kb)))

/-- **A nested crossing set separates clause units from the principle.**  Under
`ruleCU` the enclosing lambda does not own `$y`, which it writes only in the
inner lambda's crossing set: both calls share it and there is no answer.  Under
the principle it owns `$y`, fresh per call: `(Pair a b)`.  This is an L3
failure of `ruleCU`. -/
theorem nested_crossing_separates :
    inFragment sigMeTTa [] nestedCross = false ∧
      ans ruleCU nestedCross = some [] ∧
      ansR sigMeTTa (embedQ nestedCross) = some [pairT (kT .ka) (kT .kb)] := by
  decide +kernel

/-- `(let $u 1 (let $f (lam z {} (Pair HOLE ((lam r $u) ok))) ($f ok)))`: a sealed
lambda with a nested closure that reads `$u`. -/
def sealedAt (hole : A) : A :=
  lt .u (k .n1) (lt .f (.lam .z (some []) (pair hole (ap (lm .r (sv .u)) (k .ok))))
    (ap (sv .f) (k .ok)))

/-- The sealed lambda's own `$u`, unbound, in the slot model's activation. -/
def sealedU : T := .var (.inst [2, 1, 2, 2] (.src ([2, 1, 0], .u)))

/-- The same, where the principle declares it in a `new` block. -/
def sealedU' : T := .var (.inst [2, 1, 2, 2, 2] (.src ([2, 1, 0, 0], .u)))

/-- **Sealing is transitive under the principle, not under clause units.**
Under `ruleCU` the nested closure's `$u` is the outer `let`'s 1 when the hole
holds `ok`, and the sealed lambda's own unbound `$u` when the hole holds `$u`:
what the context's occurrence denotes depends on the fragment plugged beside
it (an L4 failure of the slot model's sealing).  Under the principle the sealed
lambda owns `$u` in both, and the nested closure reads it. -/
theorem sealed_transitive_separates :
    ans ruleCU (sealedAt (k .ok)) = some [pairT (kT .ok) (kT .n1)] ∧
      ans ruleCU (sealedAt (sv .u)) = some [pairT sealedU sealedU] ∧
      ansR sigMeTTa (embedQ (sealedAt (k .ok))) = some [pairT (kT .ok) sealedU'] ∧
      ansR sigMeTTa (embedQ (sealedAt (sv .u))) = some [pairT sealedU sealedU] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Quoted holes.**  The resolution gives a lambda's quoted `$y` to the
lambda (owner `[5]`, where it stands); the slot model writes every hole of
sealed code as the form's root slot `([], y)`, below the `new` block that
declares the lambda's own `$y` at `[0, 0]`: two calls quote one `$y`. -/
theorem quote_holes_root :
    ann sigMeTTa (fun _ => [9]) [] [] [5]
        (.frame .z none (.quote (.sv .y)) : RSrc MC QSy QSp) =
      .frame ([5], .z) none (.quote (.sv ([5], .y))) ∧
    elabForm .lexicalFresh []
        (toSrcR sigMeTTa [] (.frame .z none (.quote (.sv .y)) : RSrc MC QSy QSp)) =
      .lam (parName .z) []
        (newBlock [0] .y [] (.quote (.var (.src ([], .y))))) := by
  constructor <;> rfl

end Corpus

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles
