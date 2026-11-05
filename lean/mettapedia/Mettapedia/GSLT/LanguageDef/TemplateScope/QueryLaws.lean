import Mettapedia.GSLT.LanguageDef.TemplateScope.Query

/-!
# Template scope: context stability of the query rules

A scope rule assigns each name occurrence to a binder.  **Context stability**
asks that plugging a fragment into a context never moves an occurrence of the
context to another binder: the context's elaboration outside the hole is fixed
before anything is plugged in.

* `toSrc_plugAll` — under every rule whose lambdas are `lexical` (`H0`, `H1`,
  `H2`), the elaboration of a plugged context is a fixed `Src` context, which
  depends only on the rule, the context and the binders around it, around the
  elaboration of the plugged fragment in the binders at the hole.
* `context_stable` — hence there is one translated context that serves every
  fragment.
* `queryNames_moves_binder` — under `H2q` it fails: a query plugged into
  `(lam z (□ $y))` makes the lambda introduce `$y`, so the context's own `$y`
  moves from the scope around into a `new` block of the lambda.
  `QueryCorpus.context_stability_query` observes the move in the answers.
* `elabLF_toSrc_H1_eq_H0` — `H1` and the draft's default `H0` elaborate a text
  to the same term unless a query or `case` without a crossing set writes, in
  its pattern, a name an enclosing binder introduced (`QSrc.correlates`): the
  sites the draft's shadowing census reports.  Every program whose meaning
  `H1` changes has such a site.
* `QSrc.elabLF_toSrc_unitQuery` — a rule whose queries are the unit's (clause
  units among them) elaborates first-order text without `case` exactly as the
  query-wide profile, the clause-level reading of HE and PeTTa.

Holes sit at expression positions, never inside a pattern: a binder's pattern
decides what the binder introduces, so a fragment plugged into a pattern is
part of the binder by definition.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

variable {S : Type u} {X : Type v}

/-- One frame of a context of authored text with queries, with its hole at an
expression position. -/
inductive QFrame (S : Type u) (X : Type v) where
  | lamB (z : X) (xs : Option (List X))
  | appL (a : QSrc S X)
  | appR (f : QSrc S X)
  | letV (p b : QSrc S X) (xs : Option (List X))
  | letB (p w : QSrc S X) (xs : Option (List X))
  | unV (p b : QSrc S X)
  | unB (p w : QSrc S X)
  | altL (t₂ : QSrc S X)
  | altR (t₁ : QSrc S X)
  | newB (ys : List X)
  | formB (z : X)
  /-- The hole is the source of a query. -/
  | qS (p t : QSrc S X) (xs : Option (List X))
  /-- The hole is the template of a query. -/
  | qT (p s : QSrc S X) (xs : Option (List X))
  /-- The hole is the value a `case` inspects. -/
  | cV (p b : QSrc S X) (xs : Option (List X))
  /-- The hole is the body of a `case` branch. -/
  | cB (w p : QSrc S X) (xs : Option (List X))

/-- One frame of a context of `Src`. -/
inductive SFrame (S : Type u) (X : Type v) where
  | lamB (z : X) (xs : Option (List X))
  | appL (a : Src S X)
  | appR (f : Src S X)
  | letV (p b : Src S X) (xs : Option (List X))
  | letB (p w : Src S X) (xs : Option (List X))
  | unV (p b : Src S X)
  | unB (p w : Src S X)
  | altL (t₂ : Src S X)
  | altR (t₁ : Src S X)
  | newB (ys : List X)
  | formB (z : X)

namespace QFrame

/-- Put a fragment into the hole of a frame. -/
def plug : QFrame S X → QSrc S X → QSrc S X
  | .lamB z xs, t => .lam z xs t
  | .appL a, t => .app t a
  | .appR f, t => .app f t
  | .letV p b xs, t => .letS p t b xs
  | .letB p w xs, t => .letS p w t xs
  | .unV p b, t => .unify p t b
  | .unB p w, t => .unify p w t
  | .altL t₂, t => .alt t t₂
  | .altR t₁, t => .alt t₁ t
  | .newB ys, t => .new ys t
  | .formB z, t => .form z t
  | .qS p tm xs, t => .query p t tm xs
  | .qT p s xs, t => .query p s t xs
  | .cV p b xs, t => .caseS t p b xs
  | .cB w p xs, t => .caseS w p t xs

/-- A context, outermost frame first. -/
def plugAll : List (QFrame S X) → QSrc S X → QSrc S X
  | [], t => t
  | F :: K, t => F.plug (plugAll K t)

/-- The names the enclosing binders introduced at the hole of a frame, from
those `B` around it. -/
def bindIn (B : List X) : QFrame S X → List X
  | .lamB _ none => B
  | .lamB _ (some sh) => B ++ sh
  | .letB p _ xs => B ++ QSrc.patNames p ++ xs.getD []
  | .unB p _ => B ++ QSrc.patNames p
  | .newB ys => B ++ ys
  | .qT p _ xs => B ++ QSrc.patNames p ++ xs.getD []
  | .cB _ p xs => B ++ QSrc.patNames p ++ xs.getD []
  | _ => B

/-- The names the enclosing binders introduced at the hole of a context. -/
def holeB (B : List X) : List (QFrame S X) → List X
  | [] => B
  | F :: K => holeB (F.bindIn B) K

end QFrame

namespace SFrame

/-- Put a term into the hole of a frame. -/
def plug : SFrame S X → Src S X → Src S X
  | .lamB z xs, t => .lam z xs t
  | .appL a, t => .app t a
  | .appR f, t => .app f t
  | .letV p b xs, t => .letS p t b xs
  | .letB p w xs, t => .letS p w t xs
  | .unV p b, t => .unify p t b
  | .unB p w, t => .unify p w t
  | .altL t₂, t => .alt t t₂
  | .altR t₁, t => .alt t₁ t
  | .newB ys, t => .new ys t
  | .formB z, t => .form z t

/-- A context of `Src`, outermost frame first. -/
def plugAll : List (SFrame S X) → Src S X → Src S X
  | [], t => t
  | F :: K, t => F.plug (plugAll K t)

end SFrame

variable [DecidableEq X]

/-- The frame of a pattern construct whose hole is the value it inspects. -/
def patFrameV (m : PatMode) (B pn : List X) (xs : Option (List X)) (p b : Src S X) :
    SFrame S X :=
  match xs with
  | some sh => .letV p b (some sh)
  | none =>
      match m with
      | .fresh => .letV p b none
      | .correlated => .letV p b (some (pn.filter fun y => decide (y ∈ B)))
      | .unit => .unV p b

/-- The frame of a pattern construct whose hole is its body. -/
def patFrameB (m : PatMode) (B pn : List X) (xs : Option (List X)) (p w : Src S X) :
    SFrame S X :=
  match xs with
  | some sh => .letB p w (some sh)
  | none =>
      match m with
      | .fresh => .letB p w none
      | .correlated => .letB p w (some (pn.filter fun y => decide (y ∈ B)))
      | .unit => .unB p w

theorem patConstruct_value (m : PatMode) (B pn : List X) (xs : Option (List X))
    (p w b : Src S X) : patConstruct m B pn xs p w b = (patFrameV m B pn xs p b).plug w := by
  cases xs with
  | some sh => rfl
  | none => cases m <;> rfl

theorem patConstruct_body (m : PatMode) (B pn : List X) (xs : Option (List X))
    (p w b : Src S X) : patConstruct m B pn xs p w b = (patFrameB m B pn xs p w).plug b := by
  cases xs with
  | some sh => rfl
  | none => cases m <;> rfl

namespace QFrame

/-- **The elaboration of a frame**, given the rule and the names `B` that the
enclosing binders introduced around it.  It does not mention the hole. -/
def trans (r : QRule) (B : List X) : QFrame S X → SFrame S X
  | .lamB z xs => .lamB z xs
  | .appL a => .appL (QSrc.toSrc r B a)
  | .appR f => .appR (QSrc.toSrc r B f)
  | .letV p b xs =>
      .letV (QSrc.toSrc r B p) (QSrc.toSrc r (B ++ QSrc.patNames p ++ xs.getD []) b) xs
  | .letB p w xs => .letB (QSrc.toSrc r B p) (QSrc.toSrc r B w) xs
  | .unV p b => .unV (QSrc.toSrc r B p) (QSrc.toSrc r (B ++ QSrc.patNames p) b)
  | .unB p w => .unB (QSrc.toSrc r B p) (QSrc.toSrc r B w)
  | .altL t₂ => .altL (QSrc.toSrc r B t₂)
  | .altR t₁ => .altR (QSrc.toSrc r B t₁)
  | .newB ys => .newB ys
  | .formB z => .formB z
  | .qS p t xs =>
      patFrameV r.query B (QSrc.patNames p) xs (QSrc.toSrc r B p)
        (QSrc.toSrc r (B ++ QSrc.patNames p ++ xs.getD []) t)
  | .qT p s xs => patFrameB r.query B (QSrc.patNames p) xs (QSrc.toSrc r B p) (QSrc.toSrc r B s)
  | .cV p b xs =>
      patFrameV r.case B (QSrc.patNames p) xs (QSrc.toSrc r B p)
        (QSrc.toSrc r (B ++ QSrc.patNames p ++ xs.getD []) b)
  | .cB w p xs => patFrameB r.case B (QSrc.patNames p) xs (QSrc.toSrc r B p) (QSrc.toSrc r B w)

/-- The elaboration of a context, frame by frame from the outside in. -/
def transAll (r : QRule) (B : List X) : List (QFrame S X) → List (SFrame S X)
  | [] => []
  | F :: K => F.trans r B :: transAll r (F.bindIn B) K

/-- **One frame.**  Under a rule with lexical lambdas, elaborating a plugged
frame is plugging the frame's elaboration with the elaboration of the fragment
in the binders at the hole. -/
theorem toSrc_plug {r : QRule} (hr : r.lam = .lexical) (B : List X) :
    ∀ (F : QFrame S X) (t : QSrc S X),
      QSrc.toSrc r B (F.plug t) = (F.trans r B).plug (QSrc.toSrc r (F.bindIn B) t)
  | .lamB z none, t => by
      simp only [plug, QSrc.toSrc, QSrc.unitNames, hr, lamWith, trans, bindIn, SFrame.plug]
  | .lamB z (some sh), t => rfl
  | .appL a, t => rfl
  | .appR f, t => rfl
  | .letV p b xs, t => rfl
  | .letB p w xs, t => rfl
  | .unV p b, t => rfl
  | .unB p w, t => rfl
  | .altL t₂, t => rfl
  | .altR t₁, t => rfl
  | .newB ys, t => rfl
  | .formB z, t => rfl
  | .qS p tm xs, t => by
      simp only [plug, QSrc.toSrc, trans, bindIn]
      exact patConstruct_value _ _ _ _ _ _ _
  | .qT p s xs, t => by
      simp only [plug, QSrc.toSrc, trans, bindIn]
      exact patConstruct_body _ _ _ _ _ _ _
  | .cV p b xs, t => by
      simp only [plug, QSrc.toSrc, trans, bindIn]
      exact patConstruct_value _ _ _ _ _ _ _
  | .cB w p xs, t => by
      simp only [plug, QSrc.toSrc, trans, bindIn]
      exact patConstruct_body _ _ _ _ _ _ _

/-- **Context stability.**  Under a rule with lexical lambdas (`H0`, `H1`,
`H2`), the elaboration of a plugged context is the elaboration of the context,
which does not depend on the fragment, around the elaboration of the fragment
in the binders at the hole, which do not depend on it either. -/
theorem toSrc_plugAll {r : QRule} (hr : r.lam = .lexical) :
    ∀ (K : List (QFrame S X)) (B : List X) (t : QSrc S X),
      QSrc.toSrc r B (plugAll K t) = SFrame.plugAll (transAll r B K) (QSrc.toSrc r (holeB B K) t)
  | [], _, _ => rfl
  | F :: K, B, t => by
      simp only [plugAll, transAll, holeB, SFrame.plugAll]
      rw [toSrc_plug hr B F, toSrc_plugAll hr K (F.bindIn B) t]

/-- One elaborated context and one hole environment serve every fragment. -/
theorem context_stable {r : QRule} (hr : r.lam = .lexical) (K : List (QFrame S X))
    (B : List X) :
    ∃ (K' : List (SFrame S X)) (B' : List X),
      ∀ t : QSrc S X, QSrc.toSrc r B (plugAll K t) = SFrame.plugAll K' (QSrc.toSrc r B' t) :=
  ⟨transAll r B K, holeB B K, toSrc_plugAll hr K B⟩

end QFrame

/-- **`H2q` moves a binder of the context.**  In the context `(lam z (□ $y))`,
the hole `ok` leaves the context's `$y` to the scope around; a query that writes
`$y`, plugged into the same hole, makes the lambda introduce `$y`, and the
context's `$y` now sits inside the lambda's `new` block. -/
theorem queryNames_moves_binder (z y : X) (s ok : S) :
    QSrc.toSrc ruleH2q [] (.lam z none (.app (.sym ok) (.sv y))) =
        .lam z none (.app (.sym ok) (.sv y)) ∧
      QSrc.toSrc ruleH2q [] (.lam z none (.app (.query (.sv y) (.sym s) (.sym ok) none) (.sv y))) =
        .lam z none (.new [y] (.app (.unify (.sv y) (.sym s) (.sym ok)) (.sv y))) := by
  constructor
  · rfl
  · simp [QSrc.toSrc, QSrc.unitNames, ruleH2q, QSrc.unitPats, QSrc.patNames, lamWith,
      patConstruct]

/-! ## Where `H1` changes the meaning of the draft's default -/

namespace QSrc

/-- A pattern written as data: symbols, names and applications. -/
def plain : QSrc S X → Bool
  | .sym _ => true
  | .fn _ => true
  | .sv _ => true
  | .par _ => true
  | .app f a => plain f && plain a
  | _ => false

/-- Every pattern of a `let`, `unify`, query or `case` in the text is plain. -/
def patsPlain : QSrc S X → Bool
  | .lam _ _ b => patsPlain b
  | .app f a => patsPlain f && patsPlain a
  | .letS p w b _ => plain p && patsPlain w && patsPlain b
  | .unify p w b => plain p && patsPlain w && patsPlain b
  | .alt t₁ t₂ => patsPlain t₁ && patsPlain t₂
  | .new _ b => patsPlain b
  | .form _ b => patsPlain b
  | .query p s t _ => plain p && patsPlain s && patsPlain t
  | .caseS w p b _ => patsPlain w && plain p && patsPlain b
  | _ => true

/-- **A site of the shadowing census.**  Some query or `case` without a crossing
set writes, in its pattern, a name that an enclosing binder introduced (`B`
lists them).  The draft's `CETTA_PRIME_SCOPE_CENSUS=shadowing` reports these
names (`prime_lex_report_shadowing`). -/
def correlates (B : List X) : QSrc S X → Bool
  | .lam _ none b => correlates B b
  | .lam _ (some sh) b => correlates (B ++ sh) b
  | .app f a => correlates B f || correlates B a
  | .letS p w b xs => correlates B w || correlates (B ++ patNames p ++ xs.getD []) b
  | .unify p w b => correlates B w || correlates (B ++ patNames p) b
  | .alt t₁ t₂ => correlates B t₁ || correlates B t₂
  | .new ys b => correlates (B ++ ys) b
  | .form _ b => correlates B b
  | .query p s t xs =>
      (xs.isNone && (patNames p).any fun y => decide (y ∈ B)) || correlates B s ||
        correlates (B ++ patNames p ++ xs.getD []) t
  | .caseS w p b xs =>
      (xs.isNone && (patNames p).any fun y => decide (y ∈ B)) || correlates B w ||
        correlates (B ++ patNames p ++ xs.getD []) b
  | _ => false

/-- A plain pattern is elaborated alike by every rule. -/
theorem toSrc_plain (r r' : QRule) (B B' : List X) :
    ∀ p : QSrc S X, p.plain = true → toSrc r B p = toSrc r' B' p
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .sv _, _ => rfl
  | .par _, _ => rfl
  | .app f a, h => by
      simp only [plain, Bool.and_eq_true] at h
      simp only [toSrc, toSrc_plain r r' B B' f h.1, toSrc_plain r r' B B' a h.2]
  | .lam _ _ _, h => by simp [plain] at h
  | .quote _, h => by simp [plain] at h
  | .pquote _, h => by simp [plain] at h
  | .letS _ _ _ _, h => by simp [plain] at h
  | .unify _ _ _, h => by simp [plain] at h
  | .alt _ _, h => by simp [plain] at h
  | .new _ _, h => by simp [plain] at h
  | .form _ _, h => by simp [plain] at h
  | .query _ _ _ _, h => by simp [plain] at h
  | .caseS _ _ _ _, h => by simp [plain] at h

end QSrc

omit [DecidableEq X] in
theorem direct_patConstruct [DecidableEq X] (m : PatMode) (B pn : List X) (xs : Option (List X))
    (p w b : Src S X) :
    Src.direct (patConstruct m B pn xs p w b) = Src.direct p ++ Src.direct w ++ Src.direct b ∧
      Src.sharedUp (patConstruct m B pn xs p w b) =
        Src.sharedUp p ++ Src.sharedUp w ++ Src.sharedUp b := by
  cases xs with
  | some _ => exact ⟨rfl, rfl⟩
  | none => cases m <;> exact ⟨rfl, rfl⟩

/-- Rules with lexical lambdas elaborate text into terms that write the same
names at each level and share the same names upward. -/
theorem direct_sharedUp_toSrc {r r' : QRule} (hr : r.lam = .lexical) (hr' : r'.lam = .lexical) :
    ∀ (B : List X) (t : QSrc S X),
      Src.direct (QSrc.toSrc r B t) = Src.direct (QSrc.toSrc r' B t) ∧
        Src.sharedUp (QSrc.toSrc r B t) = Src.sharedUp (QSrc.toSrc r' B t)
  | _, .sym _ => ⟨rfl, rfl⟩
  | _, .fn _ => ⟨rfl, rfl⟩
  | _, .sv _ => ⟨rfl, rfl⟩
  | _, .par _ => ⟨rfl, rfl⟩
  | B, .lam z none b => by
      simp only [QSrc.toSrc, QSrc.unitNames, hr, hr', lamWith]
      exact ⟨rfl, rfl⟩
  | _, .lam z (some sh) b => ⟨rfl, rfl⟩
  | B, .app f a => by
      obtain ⟨hf1, hf2⟩ := direct_sharedUp_toSrc hr hr' B f
      obtain ⟨ha1, ha2⟩ := direct_sharedUp_toSrc hr hr' B a
      simp only [QSrc.toSrc, Src.direct, Src.sharedUp, hf1, hf2, ha1, ha2]
      exact ⟨trivial, trivial⟩
  | _, .quote _ => ⟨rfl, rfl⟩
  | _, .pquote _ => ⟨rfl, rfl⟩
  | B, .letS p w b xs => by
      obtain ⟨hp1, hp2⟩ := direct_sharedUp_toSrc hr hr' B p
      obtain ⟨hw1, hw2⟩ := direct_sharedUp_toSrc hr hr' B w
      obtain ⟨hb1, hb2⟩ := direct_sharedUp_toSrc hr hr' (B ++ QSrc.patNames p ++ xs.getD []) b
      simp only [QSrc.toSrc, Src.direct, Src.sharedUp, hp1, hp2, hw1, hw2, hb1, hb2]
      exact ⟨trivial, trivial⟩
  | B, .unify p w b => by
      obtain ⟨hp1, hp2⟩ := direct_sharedUp_toSrc hr hr' B p
      obtain ⟨hw1, hw2⟩ := direct_sharedUp_toSrc hr hr' B w
      obtain ⟨hb1, hb2⟩ := direct_sharedUp_toSrc hr hr' (B ++ QSrc.patNames p) b
      simp only [QSrc.toSrc, Src.direct, Src.sharedUp, hp1, hp2, hw1, hw2, hb1, hb2]
      exact ⟨trivial, trivial⟩
  | B, .alt t₁ t₂ => by
      obtain ⟨h11, h12⟩ := direct_sharedUp_toSrc hr hr' B t₁
      obtain ⟨h21, h22⟩ := direct_sharedUp_toSrc hr hr' B t₂
      simp only [QSrc.toSrc, Src.direct, Src.sharedUp, h11, h12, h21, h22]
      exact ⟨trivial, trivial⟩
  | B, .new ys b => by
      obtain ⟨hb1, hb2⟩ := direct_sharedUp_toSrc hr hr' (B ++ ys) b
      simp only [QSrc.toSrc, Src.direct, Src.sharedUp, hb1, hb2]
      exact ⟨trivial, trivial⟩
  | B, .form z b => by
      obtain ⟨hb1, hb2⟩ := direct_sharedUp_toSrc hr hr' B b
      simp only [QSrc.toSrc, Src.direct, Src.sharedUp, hb1, hb2]
      exact ⟨trivial, trivial⟩
  | B, .query p s t xs => by
      obtain ⟨hp1, hp2⟩ := direct_sharedUp_toSrc hr hr' B p
      obtain ⟨hs1, hs2⟩ := direct_sharedUp_toSrc hr hr' B s
      obtain ⟨ht1, ht2⟩ := direct_sharedUp_toSrc hr hr' (B ++ QSrc.patNames p ++ xs.getD []) t
      simp only [QSrc.toSrc, (direct_patConstruct _ _ _ _ _ _ _).1,
        (direct_patConstruct _ _ _ _ _ _ _).2, hp1, hp2, hs1, hs2, ht1, ht2]
      exact ⟨trivial, trivial⟩
  | B, .caseS w p b xs => by
      obtain ⟨hp1, hp2⟩ := direct_sharedUp_toSrc hr hr' B p
      obtain ⟨hw1, hw2⟩ := direct_sharedUp_toSrc hr hr' B w
      obtain ⟨hb1, hb2⟩ := direct_sharedUp_toSrc hr hr' (B ++ QSrc.patNames p ++ xs.getD []) b
      simp only [QSrc.toSrc, (direct_patConstruct _ _ _ _ _ _ _).1,
        (direct_patConstruct _ _ _ _ _ _ _).2, hp1, hp2, hw1, hw2, hb1, hb2]
      exact ⟨trivial, trivial⟩

/-- Names in force inside a binder body are names the enclosing binders, with
the body's own crossing set, introduced. -/
theorem crossIn_sub {xs : Option (List X)} {L cr B : List X} (hcr : ∀ y ∈ cr, y ∈ B) :
    ∀ y ∈ crossIn xs L cr, y ∈ B ++ xs.getD [] := by
  intro y hy
  simp only [crossIn, List.mem_append, List.mem_filter, decide_eq_true_eq] at hy
  rcases hy with h | ⟨h, _⟩
  · exact List.mem_append_right _ h
  · exact List.mem_append_left _ (hcr y h)

/-- A crossing set with nothing in it introduces what no crossing set does, when
no pattern name is in force. -/
theorem lfIntro_some_nil {p : Src S X} {cr : List X} (h : ∀ y ∈ Src.patNames p, y ∉ cr) :
    lfIntro (some []) p cr = lfIntro none p cr := by
  simp only [lfIntro, crossOwn]
  congr 1
  apply List.filter_congr
  intro y hy
  simp [h y hy]

theorem filter_mem_nil_of_any {l B : List X} (h : (l.any fun y => decide (y ∈ B)) = false) :
    l.filter (fun y => decide (y ∈ B)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro y hy
  have := List.any_eq_false.1 h y hy
  simpa using this

theorem not_mem_of_any {l B : List X} (h : (l.any fun y => decide (y ∈ B)) = false) :
    ∀ y ∈ l, y ∉ B := by
  intro y hy hB
  have := List.any_eq_false.1 h y hy
  simp [hB] at this

/-- **`H1` changes the draft's default only at the census sites.**  If no query
or `case` without a crossing set writes, in its pattern, a name that an
enclosing binder introduced (`correlates B t = false`), then `H1` and `H0`
elaborate the text to the same term under lexical fresh, for every
environment, position and set of names in force that enclosing binders
introduced.  So every program whose meaning `H1` changes has a site of the
draft's shadowing census on a query or a `case`. -/
theorem elabLF_toSrc_H1_eq_H0 (R : Owner) :
    ∀ (t : QSrc S X) (B : List X) (env : REnv X) (cr : List X) (pos : Owner),
      t.patsPlain = true → t.correlates B = false → (∀ y ∈ cr, y ∈ B) →
      elabLF R env cr pos (QSrc.toSrc ruleH1 B t) = elabLF R env cr pos (QSrc.toSrc ruleH0 B t)
  | .sym _, _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _, _, _ => rfl
  | .lam z none b, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain] at hp
      simp only [QSrc.correlates] at hc
      simp only [QSrc.toSrc, QSrc.unitNames, ruleH1, ruleH0, lamWith, elabLF, crossOwn_none]
      congr 1
      apply elabLF_toSrc_H1_eq_H0 R b B _ _ _ hp hc
      intro y hy
      simpa using crossIn_sub hcr y hy
  | .lam z (some sh) b, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain] at hp
      simp only [QSrc.correlates] at hc
      have hu : Src.uses (QSrc.toSrc ruleH1 (B ++ sh) b) = Src.uses (QSrc.toSrc ruleH0 (B ++ sh) b) := by
        simp only [Src.uses, (direct_sharedUp_toSrc (r := ruleH1) (r' := ruleH0) rfl rfl (B ++ sh) b).1,
          (direct_sharedUp_toSrc (r := ruleH1) (r' := ruleH0) rfl rfl (B ++ sh) b).2]
      simp only [QSrc.toSrc, elabLF, hu]
      congr 1
      apply elabLF_toSrc_H1_eq_H0 R b (B ++ sh) _ _ _ hp hc
      intro y hy
      simpa using crossIn_sub hcr y hy
  | .app f a, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Bool.or_eq_false_iff] at hc
      simp only [QSrc.toSrc, elabLF]
      rw [elabLF_toSrc_H1_eq_H0 R f B env cr _ hp.1 hc.1 hcr,
        elabLF_toSrc_H1_eq_H0 R a B env cr _ hp.2 hc.2 hcr]
  | .alt t₁ t₂, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Bool.or_eq_false_iff] at hc
      simp only [QSrc.toSrc, elabLF]
      rw [elabLF_toSrc_H1_eq_H0 R t₁ B env cr _ hp.1 hc.1 hcr,
        elabLF_toSrc_H1_eq_H0 R t₂ B env cr _ hp.2 hc.2 hcr]
  | .unify p w b, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Bool.or_eq_false_iff] at hc
      have hpe : QSrc.toSrc ruleH1 B p = QSrc.toSrc ruleH0 B p :=
        QSrc.toSrc_plain _ _ _ _ p hp.1.1
      simp only [QSrc.toSrc, elabLF, hpe]
      rw [elabLF_toSrc_H1_eq_H0 R w B env cr _ hp.1.2 hc.1 hcr,
        elabLF_toSrc_H1_eq_H0 R b (B ++ QSrc.patNames p) env cr _ hp.2 hc.2
          (fun y hy => List.mem_append_left _ (hcr y hy))]
  | .new [] b, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain] at hp
      simp only [QSrc.correlates] at hc
      simp only [QSrc.toSrc, elabLF]
      exact elabLF_toSrc_H1_eq_H0 R b (B ++ []) env cr _ hp hc
        (fun y hy => List.mem_append_left _ (hcr y hy))
  | .new (y₀ :: ys) b, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain] at hp
      simp only [QSrc.correlates] at hc
      simp only [QSrc.toSrc, elabLF]
      rw [elabLF_toSrc_H1_eq_H0 R b (B ++ y₀ :: ys) _ _ _ hp hc]
      intro y hy
      simp only [List.mem_filter] at hy
      exact List.mem_append_left _ (hcr y hy.1)
  | .form z b, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain] at hp
      simp only [QSrc.correlates] at hc
      simp only [QSrc.toSrc, elabLF]
      rw [elabLF_toSrc_H1_eq_H0 R b B _ cr _ hp hc hcr]
  | .letS p w b xs, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Bool.or_eq_false_iff] at hc
      have hpe : QSrc.toSrc ruleH1 B p = QSrc.toSrc ruleH0 B p :=
        QSrc.toSrc_plain _ _ _ _ p hp.1.1
      have hb := fun env' L (pos' : Owner) =>
        elabLF_toSrc_H1_eq_H0 R b (B ++ QSrc.patNames p ++ xs.getD []) env' (crossIn xs L cr) pos'
          hp.2 hc.2 (fun y hy => by
            have := crossIn_sub hcr y hy
            simp only [List.mem_append] at this ⊢
            tauto)
      simp only [QSrc.toSrc, hpe]
      simp only [elabLF]
      split
      · rw [elabLF_toSrc_H1_eq_H0 R w B env cr _ hp.1.2 hc.1 hcr, hb]
      · rw [elabLF_toSrc_H1_eq_H0 R w B env cr _ hp.1.2 hc.1 hcr, hb]
  | .query p s t (some sh), B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Option.isNone_some, Bool.false_and, Bool.false_or,
        Bool.or_eq_false_iff] at hc
      have hpe : QSrc.toSrc ruleH1 B p = QSrc.toSrc ruleH0 B p :=
        QSrc.toSrc_plain _ _ _ _ p hp.1.1
      have hb := fun env' L (pos' : Owner) =>
        elabLF_toSrc_H1_eq_H0 R t (B ++ QSrc.patNames p ++ (some sh).getD []) env'
          (crossIn (some sh) L cr) pos' hp.2 hc.2 (fun y hy => by
            have := crossIn_sub hcr y hy
            simp only [List.mem_append] at this ⊢
            tauto)
      simp only [QSrc.toSrc, patConstruct, hpe]
      simp only [elabLF]
      split
      · rw [elabLF_toSrc_H1_eq_H0 R s B env cr _ hp.1.2 hc.1 hcr, hb]
      · rw [elabLF_toSrc_H1_eq_H0 R s B env cr _ hp.1.2 hc.1 hcr, hb]
  | .query p s t none, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Option.isNone_none, Bool.true_and, Bool.or_eq_false_iff] at hc
      obtain ⟨⟨hany, hcs⟩, hct⟩ := hc
      have hpe : QSrc.toSrc ruleH1 B p = QSrc.toSrc ruleH0 B p :=
        QSrc.toSrc_plain _ _ _ _ p hp.1.1
      have hnil := filter_mem_nil_of_any hany
      have hfree : ∀ y ∈ Src.patNames (QSrc.toSrc ruleH0 B p), y ∉ cr := by
        intro y hy hycr
        rw [patNames_toSrc] at hy
        exact not_mem_of_any hany y hy (hcr y hycr)
      have hb := fun env' L (pos' : Owner) =>
        elabLF_toSrc_H1_eq_H0 R t (B ++ QSrc.patNames p ++ (none : Option (List X)).getD []) env'
          (crossIn none L cr) pos' hp.2 hct (fun y hy => by
            have := crossIn_sub hcr y hy
            simp only [List.mem_append] at this ⊢
            tauto)
      have h1 : QSrc.toSrc ruleH1 B (.query p s t none) =
          .letS (QSrc.toSrc ruleH1 B p) (QSrc.toSrc ruleH1 B s)
            (QSrc.toSrc ruleH1 (B ++ QSrc.patNames p ++ (none : Option (List X)).getD []) t)
            (some ((QSrc.patNames p).filter fun y => decide (y ∈ B))) := rfl
      have h0 : QSrc.toSrc ruleH0 B (.query p s t none) =
          .letS (QSrc.toSrc ruleH0 B p) (QSrc.toSrc ruleH0 B s)
            (QSrc.toSrc ruleH0 (B ++ QSrc.patNames p ++ (none : Option (List X)).getD []) t) none :=
        rfl
      have hcx : ∀ L : List X, crossIn (some []) L cr = crossIn none L cr := fun _ => rfl
      rw [h1, h0, hnil, hpe]
      simp only [elabLF]
      rw [lfIntro_some_nil hfree]
      simp only [hcx]
      split
      · rw [elabLF_toSrc_H1_eq_H0 R s B env cr _ hp.1.2 hcs hcr, hb]
      · rw [elabLF_toSrc_H1_eq_H0 R s B env cr _ hp.1.2 hcs hcr, hb]
  | .caseS w p b (some sh), B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Option.isNone_some, Bool.false_and, Bool.false_or,
        Bool.or_eq_false_iff] at hc
      have hpe : QSrc.toSrc ruleH1 B p = QSrc.toSrc ruleH0 B p :=
        QSrc.toSrc_plain _ _ _ _ p hp.1.2
      have hb := fun env' L (pos' : Owner) =>
        elabLF_toSrc_H1_eq_H0 R b (B ++ QSrc.patNames p ++ (some sh).getD []) env'
          (crossIn (some sh) L cr) pos' hp.2 hc.2 (fun y hy => by
            have := crossIn_sub hcr y hy
            simp only [List.mem_append] at this ⊢
            tauto)
      simp only [QSrc.toSrc, patConstruct, hpe]
      simp only [elabLF]
      split
      · rw [elabLF_toSrc_H1_eq_H0 R w B env cr _ hp.1.1 hc.1 hcr, hb]
      · rw [elabLF_toSrc_H1_eq_H0 R w B env cr _ hp.1.1 hc.1 hcr, hb]
  | .caseS w p b none, B, env, cr, pos, hp, hc, hcr => by
      simp only [QSrc.patsPlain, Bool.and_eq_true] at hp
      simp only [QSrc.correlates, Option.isNone_none, Bool.true_and, Bool.or_eq_false_iff] at hc
      obtain ⟨⟨hany, hcw⟩, hcb⟩ := hc
      have hpe : QSrc.toSrc ruleH1 B p = QSrc.toSrc ruleH0 B p :=
        QSrc.toSrc_plain _ _ _ _ p hp.1.2
      have hnil := filter_mem_nil_of_any hany
      have hfree : ∀ y ∈ Src.patNames (QSrc.toSrc ruleH0 B p), y ∉ cr := by
        intro y hy hycr
        rw [patNames_toSrc] at hy
        exact not_mem_of_any hany y hy (hcr y hycr)
      have hb := fun env' L (pos' : Owner) =>
        elabLF_toSrc_H1_eq_H0 R b (B ++ QSrc.patNames p ++ (none : Option (List X)).getD []) env'
          (crossIn none L cr) pos' hp.2 hcb (fun y hy => by
            have := crossIn_sub hcr y hy
            simp only [List.mem_append] at this ⊢
            tauto)
      have h1 : QSrc.toSrc ruleH1 B (.caseS w p b none) =
          .letS (QSrc.toSrc ruleH1 B p) (QSrc.toSrc ruleH1 B w)
            (QSrc.toSrc ruleH1 (B ++ QSrc.patNames p ++ (none : Option (List X)).getD []) b)
            (some ((QSrc.patNames p).filter fun y => decide (y ∈ B))) := rfl
      have h0 : QSrc.toSrc ruleH0 B (.caseS w p b none) =
          .letS (QSrc.toSrc ruleH0 B p) (QSrc.toSrc ruleH0 B w)
            (QSrc.toSrc ruleH0 (B ++ QSrc.patNames p ++ (none : Option (List X)).getD []) b) none :=
        rfl
      have hcx : ∀ L : List X, crossIn (some []) L cr = crossIn none L cr := fun _ => rfl
      rw [h1, h0, hnil, hpe]
      simp only [elabLF]
      rw [lfIntro_some_nil hfree]
      simp only [hcx]
      split
      · rw [elabLF_toSrc_H1_eq_H0 R w B env cr _ hp.1.1 hcw hcr, hb]
      · rw [elabLF_toSrc_H1_eq_H0 R w B env cr _ hp.1.1 hcw hcr, hb]

/-! ## Clause-level agreement of unit queries without `case` -/

namespace QSrc

/-- First-order text without `case`: symbols, names, applications, choice,
`unify` and queries without a crossing set. -/
def queryOnly : QSrc S X → Bool
  | .sym _ => true
  | .fn _ => true
  | .sv _ => true
  | .par _ => true
  | .app f a => queryOnly f && queryOnly a
  | .unify p w b => queryOnly p && queryOnly w && queryOnly b
  | .alt t₁ t₂ => queryOnly t₁ && queryOnly t₂
  | .query p s t xs => xs.isNone && queryOnly p && queryOnly s && queryOnly t
  | _ => false

/-- A rule whose queries are the unit's elaborates first-order text without
`case` into text without `let`, whatever its `case` and lambda modes. -/
theorem letFree_toSrc_unitQuery {r : QRule} (hq : r.query = .unit) :
    ∀ (B : List X) (t : QSrc S X), t.queryOnly = true → (toSrc r B t).letFree = true
  | _, .sym _, _ => rfl
  | _, .fn _, _ => rfl
  | _, .sv _, _ => rfl
  | _, .par _, _ => rfl
  | B, .app f a, h => by
      simp only [queryOnly, Bool.and_eq_true] at h
      simp only [toSrc, Src.letFree, Bool.and_eq_true]
      exact ⟨letFree_toSrc_unitQuery hq B f h.1, letFree_toSrc_unitQuery hq B a h.2⟩
  | B, .unify p w b, h => by
      simp only [queryOnly, Bool.and_eq_true] at h
      simp only [toSrc, Src.letFree, Bool.and_eq_true]
      exact ⟨⟨letFree_toSrc_unitQuery hq B p h.1.1, letFree_toSrc_unitQuery hq B w h.1.2⟩,
        letFree_toSrc_unitQuery hq _ b h.2⟩
  | B, .alt t₁ t₂, h => by
      simp only [queryOnly, Bool.and_eq_true] at h
      simp only [toSrc, Src.letFree, Bool.and_eq_true]
      exact ⟨letFree_toSrc_unitQuery hq B t₁ h.1, letFree_toSrc_unitQuery hq B t₂ h.2⟩
  | B, .query p s t xs, h => by
      simp only [queryOnly, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨⟨hx, hp⟩, hs⟩, ht⟩ := h
      subst hx
      simp only [toSrc, patConstruct, hq, Src.letFree, Bool.and_eq_true]
      exact ⟨⟨letFree_toSrc_unitQuery hq B p hp, letFree_toSrc_unitQuery hq B s hs⟩,
        letFree_toSrc_unitQuery hq _ t ht⟩
  | _, .lam _ _ _, h => by simp [queryOnly] at h
  | _, .quote _, h => by simp [queryOnly] at h
  | _, .pquote _, h => by simp [queryOnly] at h
  | _, .letS _ _ _ _, h => by simp [queryOnly] at h
  | _, .new _ _, h => by simp [queryOnly] at h
  | _, .form _ _, h => by simp [queryOnly] at h
  | _, .caseS _ _ _ _, h => by simp [queryOnly] at h

/-- **Clause-level agreement of unit queries.**  A rule whose queries are the
unit's (`H2`, `H2q`, clause units) elaborates first-order text without `case`,
under lexical fresh, exactly as the query-wide profile: the clause-level
reading HE and PeTTa run. -/
theorem elabLF_toSrc_unitQuery {r : QRule} (hq : r.query = .unit) (R : Owner) (env : REnv X)
    (cr : List X) (pos : Owner) (B : List X) (t : QSrc S X) (h : t.queryOnly = true) :
    elabLF R env cr pos (toSrc r B t) = elabQ R env pos (toSrc r B t) :=
  elabLF_eq_elabQ_of_letFree R _ env cr pos (letFree_toSrc_unitQuery hq B t h)

end QSrc

end Mettapedia.GSLT.LanguageDef.TemplateScope
