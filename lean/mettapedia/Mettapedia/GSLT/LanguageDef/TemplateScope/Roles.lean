import Mettapedia.GSLT.LanguageDef.TemplateScope.QueryLaws

/-!
# Binding by role: one generic elaboration

The query model of `TemplateScope.Query` fixes two pattern constructs (a query
and a one-branch `case`) and scopes them by a `QRule`.  This module states the
same question for **any** construct, once.

A construct declares a **binding signature**: the role of each of its
positions.

* A *relation* position (`PatRole.rel`) holds a pattern that is matched
  against a space or an equation: `match`, a transform port, `unify`.  Its
  pattern refers to the names bound by binders on its path and to the unknowns
  of the current frame; its other names *become* unknowns of the frame.  It
  introduces nothing, so sibling relations in one frame join.
* An *arrow* position (`PatRole.arrow m`) holds a pattern that destructures one
  value and selects a body: `let`, `case`, `chain`, a lambda parameter, a
  template variable.  It introduces its own names; a name that a binder on its
  path introduced is either introduced again (`shadow`) or tested (`test`).  It
  never picks up an unknown of the frame implicitly: a written crossing set
  `{$x}` does that explicitly.
* A *frame body* (`RSrc.frame`) is reusable code: a lambda, a template, an
  equation, a standing rule, a stored row.  Every run gets fresh unknowns for
  the names the frame owns (`own`).
* An *expression* position reads names (`RSrc.sv`).
* A *quotation* position (`RSrc.quote`) holds code of the **full** language,
  resolved where it is written: built code keeps identities.

The binding structure is given by role-formers: a construct is a label `c : C`
written with `RSrc.pat`, and the signature gives its role.  The pattern
construct always lists its positions as pattern, value, body; `order` records
the order in which the construct writes them (it orders own lists only).

## What a frame owns

* Without a crossing set, under the clause policy: every name written at its
  level that no binder on its path introduced, the names it writes only in the
  crossing sets of nested constructs included (`own`).
* With a crossing set `{xs}`: every name its body reads from outside except
  `xs`, the names nested closures capture included (`sealOwn`).
* Its owned names are binders for what it contains only under implicit nested
  capture (`Signature.capture`), which L4 excludes.

The names passed in explicitly by crossing sets (`R`, the crossing names in
force) are never introduced again by a shadowing arrow: a `let` inside
`(lam z body){$t}` refines the shared `$t`, as in the query model.

## The two functions

* `ann` — **the resolution**: every name occurrence is annotated with the owner
  (the position of the binder or frame) whose unknown it denotes.  The laws of
  `TemplateScope.RolesLaws` are theorems about `ann`.
* `toSrcR` — **the lowering** into `Src`, so that the slot elaboration and the
  evaluator of `TemplateScope.Spectrum` give answers.  It writes only crossing
  sets, `new` blocks and `unify`, as `QSrc.toSrc` does.

Both use the same `own` and `intro`: the `new` block of a lowered frame declares
`own` (`toSrcR_frame`), the `let` of a lowered arrow makes fresh slots for
exactly `intro` with the crossing names in force (`lowerPat_lfIntro`), and a
lowered sealed frame declares, besides what its crossing set leaves to the slot
model, what its nested closures capture (`sealExtra`).  That the slot model then
assigns every occurrence the slot the resolution predicts is not proved here;
`RolesMeTTa` checks it on the separating programs.

## The rules of the query study are signatures

`PatMode.fresh`, `correlated`, `unit` are the roles `arrow shadow`,
`arrow test`, `rel`; `LamMode.lexical` and `clause` are the frame policies of
the same names (`RolesMeTTa` proves the elaborations equal).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.Roles

open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v w

/-- What an arrow does with a pattern name that a binder on its path already
introduced. -/
inductive ArrowMode where
  /-- introduce it again (lexical shadowing) -/
  | shadow
  /-- test it: the pattern refers to the bound name -/
  | test
  deriving DecidableEq, Repr

/-- The role of the pattern position of a pattern construct. -/
inductive PatRole where
  /-- a relation: constrains the frame, introduces nothing -/
  | rel
  /-- an arrow: introduces its own names -/
  | arrow (m : ArrowMode)
  deriving DecidableEq, Repr

/-- What a frame without a crossing set owns. -/
inductive FramePolicy where
  /-- nothing: names no binder introduced belong to the enclosing scope -/
  | lexical
  /-- the names its relations write -/
  | relNames
  /-- every name written at its level that no binder on its path introduced -/
  | clause
  deriving DecidableEq, Repr

/-- The order in which a pattern construct writes its positions. -/
inductive PosOrder where
  | patternFirst
  | valueFirst
  deriving DecidableEq, Repr

/-- **A binding signature** over the construct labels `C`: the role of each
pattern construct, the order of its positions, the frame policy, and whether a
frame's owned names count as binders on the path inside it (implicit nested
capture). -/
structure Signature (C : Type w) where
  role : C → PatRole
  order : C → PosOrder
  frame : FramePolicy
  capture : Bool

/-- Authored text with role-formers.  Quotation holds the full language. -/
inductive RSrc (C : Type w) (S : Type u) (X : Type v) where
  | sym (s : S)
  | fn (F : S)
  /-- an expression occurrence of a store name -/
  | sv (y : X)
  /-- a lambda-parameter occurrence -/
  | par (z : X)
  | app (f a : RSrc C S X)
  | alt (t₁ t₂ : RSrc C S X)
  /-- `(new (ys…) body)`: an explicit introduction -/
  | new (names : List X) (body : RSrc C S X)
  /-- reusable code with parameter `z`; a written crossing set seals it -/
  | frame (z : X) (crossing : Option (List X)) (body : RSrc C S X)
  /-- code formed from parts while the program runs: it owns nothing -/
  | form (z : X) (body : RSrc C S X)
  /-- a pattern construct `c`: pattern `p`, value `w`, body `b` -/
  | pat (c : C) (p w b : RSrc C S X) (crossing : Option (List X))
  /-- held code of the full language -/
  | quote (c : RSrc C S X)
  /-- a quotation in pattern position -/
  | pquote (c : RSrc C S X)
  deriving DecidableEq, Repr

variable {C : Type w} {S : Type u} {X : Type v}

namespace RSrc

/-- Store names written in a pattern. -/
def patNames : RSrc C S X → List X
  | .sv y => [y]
  | .app f a => patNames f ++ patNames a
  | _ => []

/-- The names written at the current frame level, outside crossing sets: a
nested frame is a level of its own; `new`, a pattern construct, formed code
and quotations are not. -/
def dir (σ : Signature C) : RSrc C S X → List X
  | .sv y => [y]
  | .app f a => dir σ f ++ dir σ a
  | .alt t₁ t₂ => dir σ t₁ ++ dir σ t₂
  | .new _ b => dir σ b
  | .form _ b => dir σ b
  | .pat c p w b _ =>
      match σ.order c with
      | .patternFirst => dir σ p ++ dir σ w ++ dir σ b
      | .valueFirst => dir σ w ++ dir σ p ++ dir σ b
  | .quote c => dir σ c
  | .pquote c => dir σ c
  | _ => []

/-- The crossing names written at the current frame level: those of nested
frames and of pattern constructs. -/
def crs : RSrc C S X → List X
  | .app f a => crs f ++ crs a
  | .alt t₁ t₂ => crs t₁ ++ crs t₂
  | .new _ b => crs b
  | .frame _ xs _ => xs.getD []
  | .form _ b => crs b
  | .pat _ p w b xs => xs.getD [] ++ crs p ++ crs w ++ crs b
  | .quote c => crs c
  | .pquote c => crs c
  | _ => []

/-- The names the relations at the current level write (crossing set absent). -/
def relUses (σ : Signature C) : RSrc C S X → List X
  | .app f a => relUses σ f ++ relUses σ a
  | .alt t₁ t₂ => relUses σ t₁ ++ relUses σ t₂
  | .new _ b => relUses σ b
  | .form _ b => relUses σ b
  | .pat c p w b xs =>
      (if σ.role c = .rel ∧ xs = none then patNames p else []) ++ relUses σ w ++ relUses σ b
  | .quote c => relUses σ c
  | .pquote c => relUses σ c
  | _ => []

end RSrc

variable [DecidableEq X]

/-- **What a frame without a crossing set owns**, given the names `B` that
binders on its path introduced. -/
def own (σ : Signature C) (B : List X) (b : RSrc C S X) : List X :=
  match σ.frame with
  | .lexical => []
  | .relNames => ((b.relUses σ).filter fun y => decide (y ∉ B)).dedup
  | .clause =>
      let d := ((b.dir σ).filter fun y => decide (y ∉ B)).dedup
      d ++ ((b.crs.filter fun y => decide (y ∉ B ∧ y ∉ d))).dedup

/-- The binders in force inside a frame body without a crossing set. -/
def bodyB (σ : Signature C) (B : List X) (b : RSrc C S X) : List X :=
  if σ.capture then B ++ own σ B b else B

/-- **What a pattern construct introduces**: a written crossing set keeps its
names and introduces the rest; otherwise a relation introduces nothing, a
shadowing arrow every pattern name but the names passed in explicitly (`R`,
the crossing names in force), and a testing arrow the pattern names that no
binder on its path introduced (`B`). -/
def intro (σ : Signature C) (B R : List X) (c : C) (p : RSrc C S X) (xs : Option (List X)) :
    List X :=
  match xs with
  | some sh => ((p.patNames).filter fun y => decide (y ∉ sh)).dedup
  | none =>
      match σ.role c with
      | .rel => []
      | .arrow .shadow => ((p.patNames).filter fun y => decide (y ∉ R)).dedup
      | .arrow .test => ((p.patNames).filter fun y => decide (y ∉ B)).dedup

/-- The names of `R` outside `ys`. -/
def without (R ys : List X) : List X :=
  R.filter fun y => decide (y ∉ ys)

/-- The binders in force in the body of a pattern construct. -/
def patB (B : List X) (p : RSrc C S X) (xs : Option (List X)) : List X :=
  B ++ p.patNames ++ xs.getD []

/-- The crossing names in force in the pattern and body of a pattern construct. -/
def patR (R : List X) (xs : Option (List X)) (I : List X) : List X :=
  xs.getD [] ++ without R I

/-- **The names a resolution reads from its environment.**  A name is read when
an occurrence resolves to it and no binder between introduced it.  Inside a
sealed frame only its shared names are crossing names in force. -/
def cons (σ : Signature C) : List X → List X → RSrc C S X → List X
  | _, _, .sv y => [y]
  | B, R, .app f a => cons σ B R f ++ cons σ B R a
  | B, R, .alt t₁ t₂ => cons σ B R t₁ ++ cons σ B R t₂
  | B, R, .new ys b =>
      (cons σ (B ++ ys) (without R ys) b).filter fun y => decide (y ∉ ys)
  | B, R, .frame _ none b =>
      (cons σ (bodyB σ B b) (without R (own σ B b)) b).filter
        fun y => decide (y ∉ own σ B b)
  | B, _, .frame _ (some sh) b => sh ++ (cons σ (B ++ sh) sh b).filter fun y => decide (y ∈ sh)
  | B, R, .form _ b => cons σ B R b
  | B, R, .pat c p w b xs =>
      (cons σ B (patR R xs (intro σ B R c p xs)) p ++
          cons σ (patB B p xs) (patR R xs (intro σ B R c p xs)) b).filter
          (fun y => decide (y ∉ intro σ B R c p xs)) ++
        cons σ B R w ++ xs.getD []
  | B, R, .quote c => cons σ B R c
  | B, R, .pquote c => cons σ B R c
  | _, _, _ => []

/-- **What a sealed frame owns**: every name its body reads from outside but
the shared names.  Sealing covers the names nested closures capture. -/
def sealOwn (σ : Signature C) (B sh : List X) (b : RSrc C S X) : List X :=
  ((cons σ (B ++ sh) sh b).filter fun y => decide (y ∉ sh)).dedup

/-- **The resolution.**  `E` gives the owner of the unknown each spelling
denotes, `B` the names binders on the path introduced, `R` the names passed in
explicitly (the crossing names in force), `π` the position.  Every store-name
occurrence is annotated with its owner; a binder's own names are annotated with
its position. -/
def ann (σ : Signature C) :
    REnv X → List X → List X → Owner → RSrc C S X → RSrc C S (Owner × X)
  | _, _, _, _, .sym s => .sym s
  | _, _, _, _, .fn F => .fn F
  | E, _, _, _, .sv y => .sv (E y, y)
  | _, _, _, _, .par z => .par ([], z)
  | E, B, R, π, .app f a => .app (ann σ E B R (π ++ [0]) f) (ann σ E B R (π ++ [1]) a)
  | E, B, R, π, .alt t₁ t₂ => .alt (ann σ E B R (π ++ [0]) t₁) (ann σ E B R (π ++ [1]) t₂)
  | E, B, R, π, .new ys b =>
      .new (ys.map fun y => (π, y))
        (ann σ (E.update ys π) (B ++ ys) (without R ys) (π ++ [0]) b)
  | E, B, R, π, .frame z none b =>
      .frame (π, z) none
        (ann σ (E.update (own σ B b) π) (bodyB σ B b)
          (without R (own σ B b)) (π ++ [0]) b)
  | E, B, _, π, .frame z (some sh) b =>
      .frame (π, z) (some (sh.map fun y => (E y, y)))
        (ann σ (E.update (sealOwn σ B sh b) π) (B ++ sh) sh (π ++ [0]) b)
  | E, B, R, π, .form z b => .form (π, z) (ann σ E B R (π ++ [0]) b)
  | E, B, R, π, .pat c p w b xs =>
      .pat c
        (ann σ (E.update (intro σ B R c p xs) π) B (patR R xs (intro σ B R c p xs)) (π ++ [0]) p)
        (ann σ E B R (π ++ [1]) w)
        (ann σ (E.update (intro σ B R c p xs) π) (patB B p xs) (patR R xs (intro σ B R c p xs))
          (π ++ [2]) b)
        (xs.map (List.map fun y => (E y, y)))
  | E, B, R, π, .quote c => .quote (ann σ E B R (π ++ [0]) c)
  | E, B, R, π, .pquote c => .pquote (ann σ E B R (π ++ [0]) c)

/-! ## The lowering into `Src` -/

/-- A pattern construct lowered by its role: a written crossing set is kept; a
relation is `unify`; a shadowing arrow a plain `let`; a testing arrow a `let`
whose crossing set is the pattern names that binders on its path introduced. -/
def lowerPat (r : PatRole) (B pn : List X) (xs : Option (List X)) (p w b : Src S X) : Src S X :=
  match xs with
  | some sh => .letS p w b (some sh)
  | none =>
      match r with
      | .rel => .unify p w b
      | .arrow .shadow => .letS p w b none
      | .arrow .test => .letS p w b (some (pn.filter fun y => decide (y ∈ B)))

/-- Wrap a lowered body in a `new` block, unless there is nothing to declare. -/
def newWrap (ys : List X) (b : Src S X) : Src S X :=
  match ys with
  | [] => b
  | y₀ :: rest => .new (y₀ :: rest) b

/-- The names a sealed frame owns that the slot model's crossing set does not
reach: those its body reads only through nested closures. -/
def sealExtra (σ : Signature C) (B sh : List X) (b : RSrc C S X) (lowered : Src S X) : List X :=
  (sealOwn σ B sh b).filter fun y => decide (y ∉ Src.uses lowered)

/-- **The lowering of a signature into `Src`**, defined once for every
signature.  A frame runs its body in a `new` block of what it owns; a sealed
frame keeps its crossing set and declares in a `new` block what its nested
closures capture. -/
def toSrcR (σ : Signature C) : List X → RSrc C S X → Src S X
  | _, .sym s => .sym s
  | _, .fn F => .fn F
  | _, .sv y => .sv y
  | _, .par z => .par z
  | B, .app f a => .app (toSrcR σ B f) (toSrcR σ B a)
  | B, .alt t₁ t₂ => .alt (toSrcR σ B t₁) (toSrcR σ B t₂)
  | B, .new ys b => .new ys (toSrcR σ (B ++ ys) b)
  | B, .frame z none b => lamWith z (own σ B b) (toSrcR σ (bodyB σ B b) b)
  | B, .frame z (some sh) b =>
      .lam z (some sh) (newWrap (sealExtra σ B sh b (toSrcR σ (B ++ sh) b)) (toSrcR σ (B ++ sh) b))
  | B, .form z b => .form z (toSrcR σ B b)
  | B, .pat c p w b xs =>
      lowerPat (σ.role c) B p.patNames xs (toSrcR σ B p) (toSrcR σ B w)
        (toSrcR σ (patB B p xs) b)
  | B, .quote c => .quote (toSrcR σ B c)
  | B, .pquote c => .pquote (toSrcR σ B c)

/-! ## The lowering declares what the resolution resolves -/

/-- Lowering keeps the names written in a pattern. -/
theorem patNames_toSrcR (σ : Signature C) (B : List X) :
    ∀ p : RSrc C S X, Src.patNames (toSrcR σ B p) = p.patNames
  | .sym _ => rfl
  | .fn _ => rfl
  | .sv _ => rfl
  | .par _ => rfl
  | .app f a => by
      simp [toSrcR, RSrc.patNames, Src.patNames, patNames_toSrcR σ B f, patNames_toSrcR σ B a]
  | .alt _ _ => rfl
  | .new _ _ => rfl
  | .frame _ none _ => by
      simp only [toSrcR, RSrc.patNames]
      unfold lamWith
      split <;> rfl
  | .frame _ (some _) _ => rfl
  | .form _ _ => rfl
  | .pat c _ _ _ xs => by
      simp only [toSrcR, RSrc.patNames, lowerPat]
      cases xs with
      | some _ => rfl
      | none =>
          cases h : σ.role c with
          | rel => rfl
          | arrow m => cases m <;> rfl
  | .quote _ => rfl
  | .pquote _ => rfl

/-- **The lowered pattern construct introduces exactly `intro`**: with the
crossing names `R` in force, the `let` it writes makes fresh slots (`lfIntro`)
for exactly the names the resolution gives the construct, and a relation
writes `unify`, which makes none. -/
theorem lowerPat_lfIntro (σ : Signature C) (B R : List X) (c : C) (p w b : RSrc C S X)
    (xs : Option (List X)) :
    (∃ p' w' b' xs', toSrcR σ B (.pat c p w b xs) = .letS p' w' b' xs' ∧
        Src.patNames p' = p.patNames ∧ lfIntro xs' p' R = intro σ B R c p xs) ∨
      (σ.role c = .rel ∧ xs = none ∧ intro σ B R c p xs = []) := by
  have hpn := patNames_toSrcR σ B p
  cases xs with
  | some sh =>
      left
      refine ⟨_, _, _, some sh, rfl, hpn, ?_⟩
      simp only [lfIntro, crossOwn, intro, hpn]
  | none =>
      cases h : σ.role c with
      | rel => exact Or.inr ⟨rfl, rfl, by simp [intro, h]⟩
      | arrow m =>
          left
          cases m with
          | shadow =>
              refine ⟨toSrcR σ B p, toSrcR σ B w, toSrcR σ (patB B p none) b, none,
                by simp [toSrcR, lowerPat, h], hpn, ?_⟩
              simp [lfIntro, crossOwn, intro, h, hpn]
          | test =>
              refine ⟨toSrcR σ B p, toSrcR σ B w, toSrcR σ (patB B p none) b,
                some (p.patNames.filter fun y => decide (y ∈ B)), by simp [toSrcR, lowerPat, h], hpn, ?_⟩
              simp only [lfIntro, crossOwn, intro, h, hpn]
              congr 1
              apply List.filter_congr
              intro y hyp
              by_cases hy : y ∈ B <;> simp [hy, hyp]

/-- **A lowered frame declares exactly what the frame owns**: its body runs in
a `new` block of `own` (none when `own` is empty). -/
theorem toSrcR_frame (σ : Signature C) (B : List X) (z : X) (b : RSrc C S X) :
    toSrcR σ B (.frame z none b) = lamWith z (own σ B b) (toSrcR σ (bodyB σ B b) b) := rfl

end Mettapedia.GSLT.LanguageDef.TemplateScope.Roles
