import Mettapedia.GSLT.LanguageDef.TemplateScope.Surface

/-!
# Template scope: lexical fresh with binder identities, and the translator from rule M

Rule M (Mercury) and lexical fresh resolve the same authored text differently.
Rule M lets a lambda own every spelling it writes that no enclosing scope
quantifies, one slot per call, and a pattern only refines the slot its names
denote.  Lexical fresh introduces a slot at each pattern, scoped to the `let`,
and lets a lambda own nothing.  This module puts both on binders that carry
identities, never spellings, and proves that a translation makes rule M's
binding structure explicit in lexical fresh, exactly.

## Binder identities

A slot is `SlotId`: its spelling, its **frame** (the position of the body of
the lambda whose activation copies it, or the form's root), the **site** of
the construct that introduces it, and how it is introduced (`head`, `pat`,
`new`).  A lambda's frame is its body's position, never the form's root, so a
lambda at the root of a form does not take over the form's slots.  A parameter is named by its lambda's position.  Every binder is
allocated in its frame: a lambda's own list is the list of its frame's slots
that occur in its body (`frameSlots`), so a `let` adds no activation.  Each
construct runs at most once per activation of its frame, so a slot of the
frame is fresh per run of the construct, as lexical fresh requires.

## The two elaborations

* `elabLFId` — lexical fresh: a `let` introduces the pattern names that are not
  in force (`lfIntro`) at its own site; `unify` refines; a lambda owns nothing
  unless it carries a crossing set; `new ys` introduces `ys` at its site.
* `elabMId` — rule M: a lambda owns `ownRuleMDefault` (or its crossing set's
  complement); a plain `let` introduces nothing.  A slot a lambda (or the
  form's root) owns is named after the construct that introduces it in the
  translation: its covering pattern (`findCover`) when it has one, else a
  `new` at the frame's body (`mKey`), the lambda's head under a crossing set
  (`cKey`), the root's head at the root (`mRootEnv`).  The names are identities
  only: which occurrences share a slot, and which frame copies it, are rule
  M's.  (`cr` is bookkeeping for those names: the names lexical fresh would
  have in force in the translated text.)

Both elaborations agree with the slot model of `TemplateScope.Spectrum` on
the 80 rows of the corpus (`LexicalFreshCorpus.identity_matches_slots`).

## The translator

`toLexical` writes rule M's binding structure into lexical fresh's surface:

* a crossing set `{…}` on every plain `let` with a pattern name that lexical
  fresh would make fresh where rule M refines a slot it does not introduce
  there (`tMarks`: the **refining patterns**);
* `(new ($h …) body)` around a lambda body for every name the lambda owns by
  rule M that occurs in the body and has no covering pattern (`mNews`: the
  **un-introduced names**, among them names written only in the body and
  introduced by no pattern).

A pattern **covers** a slot when it is a plain `let` at the slot's frame
level that writes the slot's spelling in its pattern, can introduce it (the
name is not in force there), and holds every rule-M occurrence of the slot in
its pattern and body.

## Main results

* `elabLFId_toLexAt` — **the translation is exact**: lexical fresh elaborates
  the translated text to the very term rule M elaborates the source to, for
  every form, frame and context satisfying the invariant (`Corr`).
* `elabLFFormAt_toLexicalAt`, `progLF_toLexicalProg`, `run_toLexical` — at a
  form, for the equations of a program, and on the whole observation: the
  same bag of results with final stores, at every fuel, path, store and
  discipline.  No renaming or normalization of names is involved.
* `refining`, `unintroduced`, `census` — the two conditions, syntactic and
  computable.  `toLexAt_eq_self_iff`: the census is empty exactly when the
  translation changes nothing.
* `agreement`, `run_agreement` — **agreement under the corrected condition**:
  on a program with no refining pattern and no un-introduced name, lexical
  fresh and rule M elaborate every form to the same term, so they agree on
  every observation.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

/-! ## Binder identities -/

/-- How a slot is introduced: by its frame's head (a lambda's own name, or the
form's root), by a `let` pattern, or by a `new` block. -/
inductive Intro where
  | head
  | pat
  | new
  deriving DecidableEq, Repr

/-- A slot: its spelling, its frame (the position of the body of the lambda
whose activations copy it, or the form's root), the site of the construct that
introduces it, and how. -/
structure SlotId (X : Type v) where
  spell : X
  frame : Owner
  site : Owner
  intro : Intro
  deriving DecidableEq, Repr

/-- Binder identities: slots, parameters (named by their lambda's position),
and names inside sealed code. -/
inductive BId (X : Type v) where
  | slot (k : SlotId X)
  | par (z : X) (site : Owner)
  | code (y : X) (owner : Owner)
  deriving DecidableEq, Repr

variable {S : Type u} {X : Type v}

/-- An occurrence of a slot. -/
def iVar (k : SlotId X) : Tm S (BId X) := .var (.src (.slot k))

/-- Resolution environments: the slot each spelling denotes. -/
abbrev IEnv (X : Type v) := X → SlotId X

variable [DecidableEq X]

/-- Code at a quotation-relative position.  `holes` is the scope environment
whose slots a free store name denotes, when the code is a pattern; `none`
seals those names as code names of the query.  A use of a name bound inside
this quotation is a parameter of the code.  A nested quotation is sealed and
starts again at the root. -/
def codeIAt (holes : Option (IEnv X)) (penv senv : List (X × Owner)) (pos : Owner) :
    Src S X → Tm S (BId X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .par z =>
      match codeLookup penv z with
      | some p => .pvar (.src (.code z p))
      | none => .pvar (.src (.code z codeFreeParam))
  | .sv y =>
      match codeLookup senv y with
      | some p => .pvar (.src (.code y p))
      | none =>
          match holes with
          | some env => iVar (env y)
          | none => iVar ⟨y, [], [], .head⟩
  | .lam z _ b =>
      let o := codeBinder pos
      .lam (.src (.code z o)) [] (codeIAt holes ((z, o) :: penv) senv (pos ++ [0]) b)
  | .form z b =>
      let o := codeBinder pos
      .lam (.src (.code z o)) [] (codeIAt holes ((z, o) :: penv) senv (pos ++ [0]) b)
  | .app f a =>
      .app (codeIAt holes penv senv (pos ++ [0]) f) (codeIAt holes penv senv (pos ++ [1]) a)
  | .quote c => .quote (sealParams (codeIAt none [] [] [] c))
  | .pquote c => .pquote (codeIAt holes [] [] [] c)
  | .letS p w b _ =>
      let binds := svBinds (pos ++ [0]) p
      .letP (codeIAt holes penv (binds ++ senv) (pos ++ [0]) p)
        (codeIAt holes penv senv (pos ++ [1]) w)
        (codeIAt holes penv (binds ++ senv) (pos ++ [2]) b)
  | .unify p w b =>
      let binds := svBinds (pos ++ [0]) p
      .letP (codeIAt holes penv (binds ++ senv) (pos ++ [0]) p)
        (codeIAt holes penv senv (pos ++ [1]) w)
        (codeIAt holes penv (binds ++ senv) (pos ++ [2]) b)
  | .alt t₁ t₂ =>
      .alt (codeIAt holes penv senv (pos ++ [0]) t₁) (codeIAt holes penv senv (pos ++ [1]) t₂)
  | .new _ b => codeIAt holes penv senv (pos ++ [0]) b

/-- Sealed code.  Binders carry their quotation-relative position.  A free
parameter of the code, including a store name bound inside it, is bound by a
lambda of this quotation.  A free store name keeps the query owner `[]`.
The spelling is display data. -/
def codeI (s : Src S X) : Tm S (BId X) := sealParams (codeIAt none [] [] [] s)

/-- An identity is a hole unless it is a binder of code. An activation copy
keeps the hole bit of the name it copies. A slot and a scope parameter are
holes. -/
def bIdHole : Nm (BId X) → Bool
  | .src (.code _ o) => !codeBound o
  | .src (.slot _) => true
  | .src (.par _ _) => true
  | .inst _ n => bIdHole n

/-- Inside code, a bound name is identified by its position and a free code
name of the free-parameter owner by its spelling.  A slot or a parameter of
the surrounding scope is a hole. -/
instance : CodeId (BId X) where
  same
    | .src (.code y₁ o₁), .src (.code y₂ o₂) =>
        if codeBound o₁ && codeBound o₂ then decide (o₁ = o₂)
        else if o₁ = codeFreeParam && o₂ = codeFreeParam then decide (y₁ = y₂)
        else decide ((.src (.code y₁ o₁) : Nm (BId X)) = .src (.code y₂ o₂))
    | a, b => decide (a = b)
  hole := bIdHole

/-- The slot of frame `fr` a store name denotes, if it is one. -/
def frameSlotOf (fr : Owner) : Nm (BId X) → Option (BId X)
  | .src (.slot k) => if k.frame = fr then some (.slot k) else none
  | _ => none

/-- **The own list of a frame**: its slots that occur in the elaborated body,
in order of first occurrence. -/
def frameSlots (fr : Owner) (b : Tm S (BId X)) : List (BId X) :=
  ((Tm.vars b).filterMap (frameSlotOf fr)).eraseDups

/-- Point the spellings `ys` at the slots `k`. -/
def IEnv.set (env : IEnv X) (ys : List X) (k : X → SlotId X) : IEnv X :=
  fun y => if y ∈ ys then k y else env y

/-- Point the parameter `z` at the lambda at `o`. -/
def pvSet (pv : X → Owner) (z : X) (o : Owner) : X → Owner :=
  fun z' => if z' = z then o else pv z'

/-! ## Rule-M occurrences and covering patterns -/

/-- The names a lambda owns under rule M: its crossing set's complement, or rule
M's default. -/
def mOwn (E : List X) (xs : Option (List X)) (b : Src S X) : List X :=
  crossOwn xs (Src.uses b) (ownRuleMDefault E b)

/-- The names a `let` introduces under rule M: only with a crossing set. -/
def mIntro (xs : Option (List X)) (p : Src S X) : List X := crossOwn xs (Src.patNames p) []

/-- Store names a pattern quotation reads from the surrounding scope.
A binder of the code, a nested sealed quotation, and a name already bound in
`senv` are not among them.  `pos` is the quotation-relative position, the same
one `codeIAt` uses, so a `let` binds the same spellings here as in the code. -/
def codeHoleOcc (senv : List (X × Owner)) (pos : Owner) (y : X) : Src S X → ℕ
  | .sv y' =>
      if y' = y then
        match codeLookup senv y with
        | some _ => 0
        | none => 1
      else 0
  | .lam _ _ b => codeHoleOcc senv (pos ++ [0]) y b
  | .form _ b => codeHoleOcc senv (pos ++ [0]) y b
  | .app f a => codeHoleOcc senv (pos ++ [0]) y f + codeHoleOcc senv (pos ++ [1]) y a
  | .quote _ => 0
  | .pquote c => codeHoleOcc [] [] y c
  | .letS p w b _ =>
      codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
        codeHoleOcc senv (pos ++ [1]) y w +
        codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b
  | .unify p w b =>
      codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
        codeHoleOcc senv (pos ++ [1]) y w +
        codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b
  | .alt t₁ t₂ => codeHoleOcc senv (pos ++ [0]) y t₁ + codeHoleOcc senv (pos ++ [1]) y t₂
  | .new _ b => codeHoleOcc senv (pos ++ [0]) y b
  | _ => 0

/-- **Rule-M occurrences** of the slot `y` denotes at a term, `E` being the
names quantified at the enclosing scopes: occurrences of `y` that no rule-M
binder inside the term takes over (a lambda owning `y`, a `let` with a
crossing set introducing it, a `new` declaring it).  A sealed quotation has
none.  A pattern quotation contributes the store names its code leaves free:
a lambda inside the code binds a parameter, not a store name. -/
def occM (E : List X) (y : X) : Src S X → ℕ
  | .sv y' => if y' = y then 1 else 0
  | .lam _ xs b => if y ∈ mOwn E xs b then 0 else occM (mOwn E xs b ++ Src.direct b ++ E) y b
  | .app f a => occM E y f + occM E y a
  | .pquote c => codeHoleOcc [] [] y c
  | .letS p w b xs =>
      (if y ∈ mIntro xs p then 0 else occM (mIntro xs p ++ E) y p + occM (mIntro xs p ++ E) y b) +
        occM E y w
  | .unify p w b => occM E y p + occM E y w + occM E y b
  | .alt t₁ t₂ => occM E y t₁ + occM E y t₂
  | .new ys b => if y ∈ ys then 0 else occM (ys ++ E) y b
  | .form _ b => occM E y b
  | _ => 0

/-- The child of a binary node that holds every occurrence. -/
def pick2 (n₁ n₂ : ℕ) (r₁ r₂ : Option Owner) : Option Owner :=
  if n₂ = 0 then r₁.map (0 :: ·) else if n₁ = 0 then r₂.map (1 :: ·) else none

/-- The child of a ternary node that holds every occurrence. -/
def pick3 (n₁ n₂ n₃ : ℕ) (r₁ r₂ r₃ : Option Owner) : Option Owner :=
  if n₂ = 0 ∧ n₃ = 0 then r₁.map (0 :: ·)
  else if n₁ = 0 ∧ n₃ = 0 then r₂.map (1 :: ·)
  else if n₁ = 0 ∧ n₂ = 0 then r₃.map (2 :: ·)
  else none

/-- A store spelling written anywhere in authored text. -/
def mentionsSv (y : X) : Src S X → Bool
  | .sv y' => decide (y' = y)
  | .lam _ _ b => mentionsSv y b
  | .app f a => mentionsSv y f || mentionsSv y a
  | .quote c => mentionsSv y c
  | .pquote c => mentionsSv y c
  | .letS p w b _ => mentionsSv y p || mentionsSv y w || mentionsSv y b
  | .unify p w b => mentionsSv y p || mentionsSv y w || mentionsSv y b
  | .alt a b => mentionsSv y a || mentionsSv y b
  | .new _ b => mentionsSv y b
  | .form _ b => mentionsSv y b
  | _ => false

/-- `y` occurs as a store name inside a quotation. Such a name is the query's
root cell in both models, not a pattern slot: the quotation is sealed at that
cell, and a covering pattern would give the two models different owners. -/
def quoteMentions (y : X) : Src S X → Bool
  | .quote c => mentionsSv y c
  | .pquote c => mentionsSv y c
  | .lam _ _ b => quoteMentions y b
  | .app f a => quoteMentions y f || quoteMentions y a
  | .letS p w b _ => quoteMentions y p || quoteMentions y w || quoteMentions y b
  | .unify p w b => quoteMentions y p || quoteMentions y w || quoteMentions y b
  | .alt a b => quoteMentions y a || quoteMentions y b
  | .new _ b => quoteMentions y b
  | .form _ b => quoteMentions y b
  | _ => false

/-- **The covering pattern** of the slot `y` denotes at a term: the position,
relative to the term, of the plain `let` at the term's frame level that writes
`y` in its pattern, can introduce it under lexical fresh (`f`: whether `y` is
in force), and holds every rule-M occurrence of the slot in its pattern and
body.  The search descends into the one child that holds every occurrence; it
never enters a lambda (another frame) or a construct that takes `y` over. A
name that occurs inside a quotation has no cover: both models keep the root cell. -/
def findCover (E : List X) (y : X) (f : Bool) : Src S X → Option Owner
  | .app a b => pick2 (occM E y a) (occM E y b) (findCover E y f a) (findCover E y f b)
  | .alt a b => pick2 (occM E y a) (occM E y b) (findCover E y f a) (findCover E y f b)
  | .unify p w b =>
      pick3 (occM E y p) (occM E y w) (occM E y b)
        (findCover E y f p) (findCover E y f w) (findCover E y f b)
  | .letS p w b none =>
      if y ∈ Src.patNames p then
        (if f = false ∧ occM E y w = 0 ∧ quoteMentions y w = false ∧ quoteMentions y b = false
          then some [] else none)
      else
        pick3 (occM E y p) (occM E y w) (occM E y b)
          (findCover E y f p) (findCover E y f w) (findCover E y f b)
  | .letS p w b (some sh) =>
      if y ∈ mIntro (some sh) p then (findCover E y f w).map (1 :: ·)
      else
        pick3 (occM (mIntro (some sh) p ++ E) y p) (occM E y w) (occM (mIntro (some sh) p ++ E) y b)
          (findCover (mIntro (some sh) p ++ E) y (f || decide (y ∈ sh)) p) (findCover E y f w)
          (findCover (mIntro (some sh) p ++ E) y (f || decide (y ∈ sh)) b)
  | .new ys b => if y ∈ ys then none else findCover (ys ++ E) y f b
  | _ => none

/-- **The identity of a name a frame owns by rule M**: named after its covering
pattern, when it has one; else after the `new` the translation puts at the
frame's body.  `fr` is the frame: the position of the lambda's body; `E` and
`cr` are those inside it. -/
def mKey (E cr : List X) (fr : Owner) (b : Src S X) (y : X) : SlotId X :=
  match findCover E y (decide (y ∈ cr)) b with
  | some P => ⟨y, fr, fr ++ P, .pat⟩
  | none => ⟨y, fr, fr, .new⟩

/-- The identity of a name a lambda owns by its crossing set: named after its
covering pattern, when it has one (lexical fresh then introduces it there);
else after the lambda's head. -/
def cKey (E cr : List X) (fr : Owner) (b : Src S X) (y : X) : SlotId X :=
  match findCover E y (decide (y ∈ cr)) b with
  | some P => ⟨y, fr, fr ++ P, .pat⟩
  | none => ⟨y, fr, fr, .head⟩

/-- **Un-introduced names**: the names a frame owns by rule M that occur in its
body and have no covering pattern.  Lexical fresh needs `new` for them. -/
def mNews (E cr : List X) (b : Src S X) (own : List X) : List X :=
  own.filter fun y => decide (0 < occM E y b) && (findCover E y (decide (y ∈ cr)) b).isNone

/-! ## The translation of a plain `let` -/

/-- The names the translated plain `let` at `pos` introduces: its pattern names
not in force that rule M names after it. -/
def tIntro (cr : List X) (env : IEnv X) (fr pos : Owner) (p : Src S X) : List X :=
  ((Src.patNames p).filter fun y =>
    decide (y ∉ cr) && decide (env y = ⟨y, fr, pos, .pat⟩)).dedup

/-- **Refining patterns** of a plain `let`: pattern names lexical fresh would
make fresh (not in force) that rule M does not introduce here. -/
def tMarks (cr : List X) (env : IEnv X) (fr pos : Owner) (p : Src S X) : List X :=
  (Src.patNames p).filter fun y => decide (y ∉ cr) && !decide (env y = ⟨y, fr, pos, .pat⟩)

/-- The crossing set the translation writes on a plain `let`: none when nothing
refines, else every pattern name it does not introduce. -/
def tCross (cr : List X) (env : IEnv X) (fr pos : Owner) (p : Src S X) : Option (List X) :=
  if tMarks cr env fr pos p = [] then none
  else some (((Src.patNames p).filter fun y => decide (y ∉ tIntro cr env fr pos p)).dedup)

/-- The names in force inside the translated plain `let`. -/
def letCr (cr : List X) (env : IEnv X) (fr pos : Owner) (p : Src S X) : List X :=
  crossIn (tCross cr env fr pos p) (tIntro cr env fr pos p) cr

/-- Wrap a body in a `new` block, unless nothing is declared. -/
def wrapNew (ys : List X) (b : Src S X) : Src S X :=
  match ys with
  | [] => b
  | _ :: _ => .new ys b

/-! ## The elaborations -/

/-- **Lexical fresh with binder identities.** -/
def elabLFId (cr : List X) (env : IEnv X) (pv : X → Owner) (fr pos : Owner) :
    Src S X → Tm S (BId X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => iVar (env y)
  | .par z => .pvar (.src (.par z (pv z)))
  | .lam z xs b =>
      let b' := elabLFId (crossIn xs (crossOwn xs (Src.uses b) []) cr)
        (env.set (crossOwn xs (Src.uses b) []) fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩) (pvSet pv z pos)
        (pos ++ [0]) (pos ++ [0]) b
      .lam (.src (.par z pos)) (frameSlots (pos ++ [0]) b') b'
  | .app f a => .app (elabLFId cr env pv fr (pos ++ [0]) f) (elabLFId cr env pv fr (pos ++ [1]) a)
  | .quote c => .quote (codeI c)
  | .pquote c => .pquote (sealParams (codeIAt (some env) [] [] [] c))
  | .letS p w b xs =>
      .letP
        (elabLFId (crossIn xs (lfIntro xs p cr) cr)
          (env.set (lfIntro xs p cr) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [0]) p)
        (elabLFId cr env pv fr (pos ++ [1]) w)
        (elabLFId (crossIn xs (lfIntro xs p cr) cr)
          (env.set (lfIntro xs p cr) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [2]) b)
  | .unify p w b =>
      .letP (elabLFId cr env pv fr (pos ++ [0]) p) (elabLFId cr env pv fr (pos ++ [1]) w)
        (elabLFId cr env pv fr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (elabLFId cr env pv fr (pos ++ [0]) t₁) (elabLFId cr env pv fr (pos ++ [1]) t₂)
  | .new ys b =>
      elabLFId (cr.filter fun y => decide (y ∉ ys)) (env.set ys fun y => ⟨y, fr, pos, .new⟩) pv fr pos b
  | .form z b =>
      let b' := elabLFId cr (env.set [] (fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩))
        (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b
      .lam (.src (.par z pos)) (frameSlots (pos ++ [0]) b') b'

/-- **Rule M with binder identities.**  `cr` is bookkeeping for the names only:
the names in force lexical fresh would have in the translated text, which
decide whether a name has a covering pattern. -/
def elabMId (E cr : List X) (env : IEnv X) (pv : X → Owner) (fr pos : Owner) :
    Src S X → Tm S (BId X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => iVar (env y)
  | .par z => .pvar (.src (.par z (pv z)))
  | .lam z none b =>
      let b' := elabMId (ownRuleMDefault E b ++ Src.direct b ++ E)
        (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
          (ownRuleMDefault E b)))
        (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
        (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b
      .lam (.src (.par z pos)) (frameSlots (pos ++ [0]) b') b'
  | .lam z (some sh) b =>
      let b' := elabMId (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
        (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
        (env.set (crossOwn (some sh) (Src.uses b) [])
          (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
            (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
        (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b
      .lam (.src (.par z pos)) (frameSlots (pos ++ [0]) b') b'
  | .app f a => .app (elabMId E cr env pv fr (pos ++ [0]) f) (elabMId E cr env pv fr (pos ++ [1]) a)
  | .quote c => .quote (codeI c)
  | .pquote c => .pquote (sealParams (codeIAt (some env) [] [] [] c))
  | .letS p w b none =>
      .letP (elabMId E (letCr cr env fr pos p) env pv fr (pos ++ [0]) p)
        (elabMId E cr env pv fr (pos ++ [1]) w)
        (elabMId E (letCr cr env fr pos p) env pv fr (pos ++ [2]) b)
  | .letS p w b (some sh) =>
      .letP
        (elabMId (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [0]) p)
        (elabMId E cr env pv fr (pos ++ [1]) w)
        (elabMId (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) pv fr (pos ++ [2]) b)
  | .unify p w b =>
      .letP (elabMId E cr env pv fr (pos ++ [0]) p) (elabMId E cr env pv fr (pos ++ [1]) w)
        (elabMId E cr env pv fr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (elabMId E cr env pv fr (pos ++ [0]) t₁) (elabMId E cr env pv fr (pos ++ [1]) t₂)
  | .new ys b =>
      elabMId (ys ++ E) (cr.filter fun y => decide (y ∉ ys)) (env.set ys fun y => ⟨y, fr, pos, .new⟩)
        pv fr pos b
  | .form z b =>
      let b' := elabMId E cr (env.set [] (fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩))
        (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) b
      .lam (.src (.par z pos)) (frameSlots (pos ++ [0]) b') b'

/-! ## The translator -/

/-- **The translator from rule M to lexical fresh**, at a position with rule M's
context `E`, `env` and lexical fresh's names in force `cr`: crossing sets on
the refining patterns, `new` around the bodies with un-introduced names. -/
def toLexAt (E cr : List X) (env : IEnv X) (fr pos : Owner) : Src S X → Src S X
  | .lam z none b =>
      .lam z none (wrapNew (mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b (ownRuleMDefault E b))
        (toLexAt (ownRuleMDefault E b ++ Src.direct b ++ E)
          (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
            (ownRuleMDefault E b)))
          (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
          (pos ++ [0]) (pos ++ [0]) b))
  | .lam z (some sh) b =>
      .lam z (some sh)
        (toLexAt (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
          (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
          (env.set (crossOwn (some sh) (Src.uses b) [])
          (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
            (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
          (pos ++ [0]) (pos ++ [0]) b)
  | .app f a => .app (toLexAt E cr env fr (pos ++ [0]) f) (toLexAt E cr env fr (pos ++ [1]) a)
  | .letS p w b none =>
      .letS (toLexAt E (letCr cr env fr pos p) env fr (pos ++ [0]) p)
        (toLexAt E cr env fr (pos ++ [1]) w)
        (toLexAt E (letCr cr env fr pos p) env fr (pos ++ [2]) b) (tCross cr env fr pos p)
  | .letS p w b (some sh) =>
      .letS
        (toLexAt (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0]) p)
        (toLexAt E cr env fr (pos ++ [1]) w)
        (toLexAt (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2]) b) (some sh)
  | .unify p w b =>
      .unify (toLexAt E cr env fr (pos ++ [0]) p) (toLexAt E cr env fr (pos ++ [1]) w)
        (toLexAt E cr env fr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (toLexAt E cr env fr (pos ++ [0]) t₁) (toLexAt E cr env fr (pos ++ [1]) t₂)
  | .new ys b =>
      .new ys (toLexAt (ys ++ E) (cr.filter fun y => decide (y ∉ ys))
        (env.set ys fun y => ⟨y, fr, pos, .new⟩) fr pos b)
  | .form z b => .form z (toLexAt E cr env (pos ++ [0]) (pos ++ [0]) b)
  | t => t

/-! ## The translation preserves what the elaborations read -/

theorem IEnv.set_nil (env : IEnv X) (k : X → SlotId X) : env.set [] k = env := by
  funext y
  simp [IEnv.set]

theorem IEnv.set_of_mem {env : IEnv X} {ys : List X} {k : X → SlotId X} {y : X} (h : y ∈ ys) :
    env.set ys k y = k y := by
  simp [IEnv.set, h]

theorem IEnv.set_of_not_mem {env : IEnv X} {ys : List X} {k : X → SlotId X} {y : X} (h : y ∉ ys) :
    env.set ys k y = env y := by
  simp [IEnv.set, h]

theorem filter_not_mem_nil (cr : List X) : (cr.filter fun y => decide (y ∉ ([] : List X))) = cr := by
  simp

theorem crossIn_none_nil (cr : List X) : crossIn none ([] : List X) cr = cr := by
  simp [crossIn]

theorem patNames_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    Src.patNames (toLexAt E cr env fr pos t) = Src.patNames t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, _, _ => rfl
  | .lam _ (some _) _, _, _, _, _, _ => rfl
  | .app f a, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.patNames, patNames_toLexAt f, patNames_toLexAt a]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS _ _ _ none, _, _, _, _, _ => rfl
  | .letS _ _ _ (some _), _, _, _, _, _ => rfl
  | .unify _ _ _, _, _, _, _, _ => rfl
  | .alt _ _, _, _, _, _, _ => rfl
  | .new _ _, _, _, _, _, _ => rfl
  | .form _ _, _, _, _, _, _ => rfl

omit [DecidableEq X] in
theorem direct_wrapNew (ys : List X) (b : Src S X) : Src.direct (wrapNew ys b) = Src.direct b := by
  cases ys <;> rfl

omit [DecidableEq X] in
theorem sharedUp_wrapNew (ys : List X) (b : Src S X) :
    Src.sharedUp (wrapNew ys b) = Src.sharedUp b := by
  cases ys <;> rfl

/-- The translation keeps the names written at each level. -/
theorem direct_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    Src.direct (toLexAt E cr env fr pos t) = Src.direct t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, _, _ => rfl
  | .lam _ (some _) _, _, _, _, _, _ => rfl
  | .app f a, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.direct, direct_toLexAt f, direct_toLexAt a]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b none, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.direct, direct_toLexAt p, direct_toLexAt w, direct_toLexAt b]
  | .letS p w b (some _), E, cr, env, fr, pos => by
      simp only [toLexAt, Src.direct, direct_toLexAt p, direct_toLexAt w, direct_toLexAt b]
  | .unify p w b, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.direct, direct_toLexAt p, direct_toLexAt w, direct_toLexAt b]
  | .alt t₁ t₂, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.direct, direct_toLexAt t₁, direct_toLexAt t₂]
  | .new ys b, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.direct, direct_toLexAt b]
  | .form _ b, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.direct, direct_toLexAt b]

/-- The translation keeps the names nested lambdas share. -/
theorem sharedUp_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    Src.sharedUp (toLexAt E cr env fr pos t) = Src.sharedUp t
  | .sym _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _ => rfl
  | .lam _ none _, _, _, _, _, _ => rfl
  | .lam _ (some _) _, _, _, _, _, _ => rfl
  | .app f a, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.sharedUp, sharedUp_toLexAt f, sharedUp_toLexAt a]
  | .quote _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _ => rfl
  | .letS p w b none, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.sharedUp, sharedUp_toLexAt p, sharedUp_toLexAt w, sharedUp_toLexAt b]
  | .letS p w b (some _), E, cr, env, fr, pos => by
      simp only [toLexAt, Src.sharedUp, sharedUp_toLexAt p, sharedUp_toLexAt w, sharedUp_toLexAt b]
  | .unify p w b, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.sharedUp, sharedUp_toLexAt p, sharedUp_toLexAt w, sharedUp_toLexAt b]
  | .alt t₁ t₂, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.sharedUp, sharedUp_toLexAt t₁, sharedUp_toLexAt t₂]
  | .new ys b, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.sharedUp, sharedUp_toLexAt b]
  | .form _ b, E, cr, env, fr, pos => by
      simp only [toLexAt, Src.sharedUp, sharedUp_toLexAt b]

theorem uses_toLexAt (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner) :
    Src.uses (toLexAt E cr env fr pos t) = Src.uses t := by
  simp only [Src.uses, direct_toLexAt, sharedUp_toLexAt]

/-! ## The translated `let` introduces what rule M names after it -/

theorem mem_tIntro {cr : List X} {env : IEnv X} {fr pos : Owner} {p : Src S X} {y : X} :
    y ∈ tIntro cr env fr pos p ↔
      y ∈ Src.patNames p ∧ y ∉ cr ∧ env y = ⟨y, fr, pos, .pat⟩ := by
  simp [tIntro, List.mem_dedup, List.mem_filter]

theorem tMarks_eq_nil {cr : List X} {env : IEnv X} {fr pos : Owner} {p : Src S X} :
    tMarks cr env fr pos p = [] ↔
      ∀ y ∈ Src.patNames p, y ∉ cr → env y = ⟨y, fr, pos, .pat⟩ := by
  simp only [tMarks, List.filter_eq_nil_iff, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, not_and, not_not]

/-- **The translated `let` introduces exactly `tIntro`.** -/
theorem lfIntro_tCross {cr : List X} {env : IEnv X} {fr pos : Owner} {p p' : Src S X}
    (hp : Src.patNames p' = Src.patNames p) :
    lfIntro (tCross cr env fr pos p) p' cr = tIntro cr env fr pos p := by
  have hT : tIntro cr env fr pos p = ((Src.patNames p).filter fun y =>
      decide (y ∉ cr) && decide (env y = ⟨y, fr, pos, .pat⟩)).dedup := rfl
  unfold tCross
  split
  · next hm =>
      have hall := tMarks_eq_nil.1 hm
      simp only [lfIntro, crossOwn, hp]
      rw [hT]
      congr 1
      apply List.filter_congr
      intro y hy
      by_cases hc : y ∈ cr
      · simp [hc]
      · simp [hc, hall y hy hc]
  · simp only [lfIntro, crossOwn, hp]
    conv_rhs => rw [hT]
    congr 1
    apply List.filter_congr
    intro y hy
    have h2 : y ∈ tIntro cr env fr pos p ↔ y ∉ cr ∧ env y = ⟨y, fr, pos, .pat⟩ := by
      rw [mem_tIntro]
      simp [hy]
    by_cases hT' : y ∈ tIntro cr env fr pos p
    · obtain ⟨hc, he⟩ := h2.1 hT'
      simp [hT', hc, he, hy]
    · have hn : ¬ (y ∉ cr ∧ env y = ⟨y, fr, pos, .pat⟩) := fun h => hT' (h2.2 h)
      by_cases hc : y ∈ cr
      · simp [hT', hc, hy]
      · have he : env y ≠ ⟨y, fr, pos, .pat⟩ := fun he => hn ⟨hc, he⟩
        simp [hT', hc, he, hy]

/-- A name the pattern does not write is in force inside the translated `let`
exactly when it is in force outside. -/
theorem mem_letCr_of_not_mem {cr : List X} {env : IEnv X} {fr pos : Owner} {p : Src S X} {y : X}
    (hy : y ∉ Src.patNames p) : y ∈ letCr cr env fr pos p ↔ y ∈ cr := by
  have hi : y ∉ tIntro cr env fr pos p := fun h => hy (mem_tIntro.1 h).1
  unfold letCr crossIn tCross
  split
  · simp [hi]
  · simp [List.mem_dedup, hy, hi]

/-- A name a crossing `let` does not introduce is in force inside it when it is
in force outside or written in the set. -/
theorem mem_crossIn_some {sh intro cr : List X} {y : X} (hy : y ∉ intro) :
    decide (y ∈ crossIn (some sh) intro cr) = (decide (y ∈ cr) || decide (y ∈ sh)) := by
  by_cases h1 : y ∈ sh <;> by_cases h2 : y ∈ cr <;> simp [crossIn, h1, h2, hy]

theorem mem_filter_not_mem {cr ys : List X} {y : X} (hy : y ∉ ys) :
    decide (y ∈ cr.filter fun y => decide (y ∉ ys)) = decide (y ∈ cr) := by
  by_cases h : y ∈ cr <;> simp [h, hy]

/-! ## Covering patterns: the search descends into one child -/

theorem pick2_left {n₁ n₂ : ℕ} {r₁ r₂ : Option Owner} {P : Owner} (h₁ : 0 < n₁)
    (h : pick2 n₁ n₂ r₁ r₂ = some P) : ∃ P', P = 0 :: P' ∧ r₁ = some P' := by
  unfold pick2 at h
  split at h
  · cases hr : r₁ with
    | none => rw [hr] at h; cases h
    | some P' => rw [hr] at h; cases h; exact ⟨P', rfl, rfl⟩
  · rw [if_neg (by omega)] at h
    cases h

theorem pick2_right {n₁ n₂ : ℕ} {r₁ r₂ : Option Owner} {P : Owner} (h₂ : 0 < n₂)
    (h : pick2 n₁ n₂ r₁ r₂ = some P) : ∃ P', P = 1 :: P' ∧ r₂ = some P' := by
  unfold pick2 at h
  rw [if_neg (by omega)] at h
  split at h
  · cases hr : r₂ with
    | none => rw [hr] at h; cases h
    | some P' => rw [hr] at h; cases h; exact ⟨P', rfl, rfl⟩
  · cases h

theorem pick3_one {n₁ n₂ n₃ : ℕ} {r₁ r₂ r₃ : Option Owner} {P : Owner} (h₁ : 0 < n₁)
    (h : pick3 n₁ n₂ n₃ r₁ r₂ r₃ = some P) : ∃ P', P = 0 :: P' ∧ r₁ = some P' := by
  unfold pick3 at h
  split at h
  · cases hr : r₁ with
    | none => rw [hr] at h; cases h
    | some P' => rw [hr] at h; cases h; exact ⟨P', rfl, rfl⟩
  · rw [if_neg (by omega), if_neg (by omega)] at h
    cases h

theorem pick3_two {n₁ n₂ n₃ : ℕ} {r₁ r₂ r₃ : Option Owner} {P : Owner} (h₂ : 0 < n₂)
    (h : pick3 n₁ n₂ n₃ r₁ r₂ r₃ = some P) : ∃ P', P = 1 :: P' ∧ r₂ = some P' := by
  unfold pick3 at h
  rw [if_neg (by omega)] at h
  split at h
  · cases hr : r₂ with
    | none => rw [hr] at h; cases h
    | some P' => rw [hr] at h; cases h; exact ⟨P', rfl, rfl⟩
  · rw [if_neg (by omega)] at h
    cases h

theorem pick3_three {n₁ n₂ n₃ : ℕ} {r₁ r₂ r₃ : Option Owner} {P : Owner} (h₃ : 0 < n₃)
    (h : pick3 n₁ n₂ n₃ r₁ r₂ r₃ = some P) : ∃ P', P = 2 :: P' ∧ r₃ = some P' := by
  unfold pick3 at h
  rw [if_neg (by omega), if_neg (by omega)] at h
  split at h
  · cases hr : r₃ with
    | none => rw [hr] at h; cases h
    | some P' => rw [hr] at h; cases h; exact ⟨P', rfl, rfl⟩
  · cases h

/-! ## The invariant and the main theorem -/

/-- **The invariant** between rule M's and lexical fresh's environments at a
term: every name with a rule-M occurrence there denotes the same slot under
both, or rule M names it after a covering pattern inside the term, which
lexical fresh has not reached yet. -/
def Corr (E cr : List X) (envM envL : IEnv X) (fr pos : Owner) (t : Src S X) : Prop :=
  ∀ y, 0 < occM E y t → envL y = envM y ∨
    ∃ P, findCover E y (decide (y ∈ cr)) t = some P ∧ envM y = ⟨y, fr, pos ++ P, .pat⟩

theorem mNews_sub {E cr : List X} {b : Src S X} {own : List X} {y : X}
    (h : y ∈ mNews E cr b own) : y ∈ own := (List.mem_filter.1 h).1

theorem mem_mNews {E cr : List X} {b : Src S X} {own : List X} {y : X} :
    y ∈ mNews E cr b own ↔ y ∈ own ∧ 0 < occM E y b ∧ findCover E y (decide (y ∈ cr)) b = none := by
  simp [mNews, Option.isNone_iff_eq_none]

/-- Lexical fresh elaborates a `new` block written by `wrapNew` as the block. -/
theorem elabLFId_wrapNew (ys cr : List X) (env : IEnv X) (pv : X → Owner) (fr pos : Owner)
    (b : Src S X) :
    elabLFId cr env pv fr pos (wrapNew ys b) =
      elabLFId (cr.filter fun y => decide (y ∉ ys)) (env.set ys fun y => ⟨y, fr, pos, .new⟩) pv fr pos b := by
  cases ys with
  | nil => simp [wrapNew, IEnv.set_nil]
  | cons y ys => rfl

/-- Pattern code reads a scope environment only at the store names it leaves
free.  Environments that agree on those names give the same code. -/
theorem codeIAt_holeEnv (env₁ env₂ : IEnv X) (penv senv : List (X × Owner)) (pos : Owner) :
    ∀ s : Src S X, (∀ y, 0 < codeHoleOcc senv pos y s → env₁ y = env₂ y) →
      codeIAt (some env₁) penv senv pos s = codeIAt (some env₂) penv senv pos s
  | .sym _, _ => rfl
  | .fn _, _ => rfl
  | .par _, _ => rfl
  | .quote _, _ => rfl
  | .sv y, h => by
      simp only [codeIAt]
      cases hl : codeLookup senv y with
      | some _ => rfl
      | none =>
          have he : env₁ y = env₂ y := h y (by
            simp only [codeHoleOcc, hl]
            decide)
          simp [iVar, he]
  | .lam z _ b, h => by
      simp only [codeIAt]
      exact congrArg (fun t => Tm.lam (.src (.code z (codeBinder pos))) [] t)
        (codeIAt_holeEnv env₁ env₂ ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b
          (fun y hy => h y (by simpa [codeHoleOcc] using hy)))
  | .form z b, h => by
      simp only [codeIAt]
      exact congrArg (fun t => Tm.lam (.src (.code z (codeBinder pos))) [] t)
        (codeIAt_holeEnv env₁ env₂ ((z, codeBinder pos) :: penv) senv (pos ++ [0]) b
          (fun y hy => h y hy))
  | .app f a, h => by
      have hf := codeIAt_holeEnv env₁ env₂ penv senv (pos ++ [0]) f (fun y hy => h y <| by
        simpa [codeHoleOcc] using Nat.lt_add_right (codeHoleOcc senv (pos ++ [1]) y a) hy)
      have ha := codeIAt_holeEnv env₁ env₂ penv senv (pos ++ [1]) a (fun y hy => h y <| by
        simpa [codeHoleOcc] using Nat.lt_add_left (codeHoleOcc senv (pos ++ [0]) y f) hy)
      simp only [codeIAt, hf, ha]
  | .pquote c, h => by
      simp only [codeIAt]
      exact congrArg Tm.pquote (codeIAt_holeEnv env₁ env₂ [] [] [] c
        (fun y hy => h y (by simpa [codeHoleOcc] using hy)))
  | .letS p w b _, h => by
      simp only [codeIAt]
      have hp := codeIAt_holeEnv env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p
        (fun y hy => h y <| by
          have : 0 < codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
              codeHoleOcc senv (pos ++ [1]) y w +
              codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b := by omega
          simpa [codeHoleOcc] using this)
      have hw := codeIAt_holeEnv env₁ env₂ penv senv (pos ++ [1]) w (fun y hy => h y <| by
        have : 0 < codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
            codeHoleOcc senv (pos ++ [1]) y w +
            codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b := by omega
        simpa [codeHoleOcc] using this)
      have hb := codeIAt_holeEnv env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b
        (fun y hy => h y <| by
          have : 0 < codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
              codeHoleOcc senv (pos ++ [1]) y w +
              codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b := by omega
          simpa [codeHoleOcc] using this)
      simp only [hp, hw, hb]
  | .unify p w b, h => by
      simp only [codeIAt]
      have hp := codeIAt_holeEnv env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) p
        (fun y hy => h y <| by
          have : 0 < codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
              codeHoleOcc senv (pos ++ [1]) y w +
              codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b := by omega
          simpa [codeHoleOcc] using this)
      have hw := codeIAt_holeEnv env₁ env₂ penv senv (pos ++ [1]) w (fun y hy => h y <| by
        have : 0 < codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
            codeHoleOcc senv (pos ++ [1]) y w +
            codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b := by omega
        simpa [codeHoleOcc] using this)
      have hb := codeIAt_holeEnv env₁ env₂ penv (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) b
        (fun y hy => h y <| by
          have : 0 < codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [0]) y p +
              codeHoleOcc senv (pos ++ [1]) y w +
              codeHoleOcc (svBinds (pos ++ [0]) p ++ senv) (pos ++ [2]) y b := by omega
          simpa [codeHoleOcc] using this)
      simp only [hp, hw, hb]
  | .alt t₁ t₂, h => by
      have h₁ := codeIAt_holeEnv env₁ env₂ penv senv (pos ++ [0]) t₁ (fun y hy => h y <| by
        simpa [codeHoleOcc] using Nat.lt_add_right (codeHoleOcc senv (pos ++ [1]) y t₂) hy)
      have h₂ := codeIAt_holeEnv env₁ env₂ penv senv (pos ++ [1]) t₂ (fun y hy => h y <| by
        simpa [codeHoleOcc] using Nat.lt_add_left (codeHoleOcc senv (pos ++ [0]) y t₁) hy)
      simp only [codeIAt, h₁, h₂]
  | .new _ b, h => by
      simp only [codeIAt]
      exact codeIAt_holeEnv env₁ env₂ penv senv (pos ++ [0]) b
        (fun y hy => h y (by simpa [codeHoleOcc] using hy))

/-- **The translation is exact.**  Under the invariant `Corr`, lexical fresh
elaborates the translated text to the very term that rule M elaborates the
source to: same constructors, same binder identities, same own lists. -/
theorem elabLFId_toLexAt : ∀ (t : Src S X) (E cr : List X) (envM envL : IEnv X)
    (pv : X → Owner) (fr pos : Owner), Corr E cr envM envL fr pos t →
    elabLFId cr envL pv fr pos (toLexAt E cr envM fr pos t) = elabMId E cr envM pv fr pos t
  | .sym _, _, _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _, _, _ => rfl
  | .sv y, E, cr, envM, envL, pv, fr, pos, h => by
      rcases h y (by simp [occM]) with h' | ⟨P, hP, _⟩
      · show iVar (envL y) = iVar (envM y)
        rw [h']
      · simp [findCover] at hP
  | .par _, _, _, _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _, _, _, _ => rfl
  | .lam z none b, E, cr, envM, envL, pv, fr, pos, h => by
      have hcorr : Corr (ownRuleMDefault E b ++ Src.direct b ++ E)
          (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
            (ownRuleMDefault E b)))
          (envM.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
          (envL.set (mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b (ownRuleMDefault E b))
            fun y => ⟨y, pos ++ [0], pos ++ [0], .new⟩)
          (pos ++ [0]) (pos ++ [0]) b := by
        intro y hy
        by_cases hyo : y ∈ ownRuleMDefault E b
        · rw [IEnv.set_of_mem hyo]
          by_cases hyn : y ∈ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b (ownRuleMDefault E b)
          · left
            rw [IEnv.set_of_mem hyn]
            have hnone := (mem_mNews.1 hyn).2.2
            simp only [mKey, hnone]
          · right
            cases hf : findCover (ownRuleMDefault E b ++ Src.direct b ++ E) y (decide (y ∈ cr)) b with
            | none => exact absurd (mem_mNews.2 ⟨hyo, hy, hf⟩) hyn
            | some P =>
                refine ⟨P, ?_, ?_⟩
                · rw [mem_filter_not_mem hyn]
                  exact hf
                · simp only [mKey, hf]
        · rw [IEnv.set_of_not_mem hyo, IEnv.set_of_not_mem (fun hn => hyo (mNews_sub hn))]
          have hocc : 0 < occM E y (.lam z none b) := by
            simpa [occM, mOwn, hyo] using hy
          rcases h y hocc with h' | ⟨P, hP, _⟩
          · exact Or.inl h'
          · simp [findCover] at hP
      have hb := elabLFId_toLexAt b _ _ _ _ (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) hcorr
      simp only [toLexAt, elabMId, elabLFId, crossOwn_none, crossIn_none_nil, IEnv.set_nil,
        elabLFId_wrapNew]
      rw [hb]
  | .lam z (some sh) b, E, cr, envM, envL, pv, fr, pos, h => by
      have hcorr : Corr (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
          (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
          (envM.set (crossOwn (some sh) (Src.uses b) [])
            (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
              (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
          (envL.set (crossOwn (some sh) (Src.uses b) []) fun y => ⟨y, pos ++ [0], pos ++ [0], .head⟩)
          (pos ++ [0]) (pos ++ [0]) b := by
        intro y hy
        by_cases hyo : y ∈ crossOwn (some sh) (Src.uses b) []
        · rw [IEnv.set_of_mem hyo, IEnv.set_of_mem hyo]
          cases hf : findCover (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E) y
              (decide (y ∈ crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)) b with
          | none =>
              left
              simp only [cKey, hf]
          | some P =>
              right
              exact ⟨P, rfl, by simp only [cKey, hf]⟩
        · rw [IEnv.set_of_not_mem hyo, IEnv.set_of_not_mem hyo]
          have hmo : mOwn E (some sh) b = crossOwn (some sh) (Src.uses b) [] := rfl
          have hocc : 0 < occM E y (.lam z (some sh) b) := by
            simp only [occM, hmo, hyo, if_false]
            exact hy
          rcases h y hocc with h' | ⟨P, hP, _⟩
          · exact Or.inl h'
          · simp [findCover] at hP
      have hb := elabLFId_toLexAt b _ _ _ _ (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) hcorr
      simp only [toLexAt, elabMId, elabLFId, uses_toLexAt]
      rw [hb]
  | .app f a, E, cr, envM, envL, pv, fr, pos, h => by
      have hf : Corr E cr envM envL fr (pos ++ [0]) f := by
        intro y hy
        rcases h y (by simp only [occM]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          simp only [findCover] at hP
          obtain ⟨P', rfl, hP'⟩ := pick2_left hy hP
          exact ⟨P', hP', by rw [hk]; simp⟩
      have ha : Corr E cr envM envL fr (pos ++ [1]) a := by
        intro y hy
        rcases h y (by simp only [occM]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          simp only [findCover] at hP
          obtain ⟨P', rfl, hP'⟩ := pick2_right hy hP
          exact ⟨P', hP', by rw [hk]; simp⟩
      simp only [toLexAt, elabLFId, elabMId]
      rw [elabLFId_toLexAt f E cr envM envL pv fr _ hf, elabLFId_toLexAt a E cr envM envL pv fr _ ha]
  | .pquote c, E, cr, envM, envL, pv, fr, pos, h => by
      simp only [toLexAt, elabLFId, elabMId, Tm.pquote.injEq]
      apply congrArg sealParams
      apply codeIAt_holeEnv envL envM [] [] [] c
      intro y hy
      have hocc : 0 < occM E y (.pquote c) := by simpa [occM] using hy
      rcases h y hocc with h' | ⟨_, hP, _⟩
      · exact h'
      · simp [findCover] at hP
  | .letS p w b none, E, cr, envM, envL, pv, fr, pos, h => by
      have hocc : ∀ y, occM E y (.letS p w b none) = occM E y p + occM E y b + occM E y w := by
        intro y
        simp [occM, mIntro]
      have hfc : ∀ y, y ∈ Src.patNames p → ∀ P, findCover E y (decide (y ∈ cr)) (.letS p w b none) =
          some P → P = [] ∧ y ∉ cr ∧ occM E y w = 0 := by
        intro y hpn P hP
        simp only [findCover, hpn, if_true] at hP
        split at hP
        · next hcond =>
            cases hP
            exact ⟨rfl, by simpa using hcond.1, hcond.2.1⟩
        · cases hP
      have hp : Corr E (letCr cr envM fr pos p) envM
          (envL.set (tIntro cr envM fr pos p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0]) p := by
        intro y hy
        by_cases hyi : y ∈ tIntro cr envM fr pos p
        · left
          rw [IEnv.set_of_mem hyi]
          exact ((mem_tIntro.1 hyi).2.2).symm
        · rw [IEnv.set_of_not_mem hyi]
          rcases h y (by rw [hocc]; omega) with h' | ⟨P, hP, hk⟩
          · exact Or.inl h'
          · right
            by_cases hpn : y ∈ Src.patNames p
            · exfalso
              obtain ⟨rfl, hc, -⟩ := hfc y hpn P hP
              exact hyi (mem_tIntro.2 ⟨hpn, hc, by simpa using hk⟩)
            · simp only [findCover, hpn, if_false] at hP
              obtain ⟨P', rfl, hP'⟩ := pick3_one hy hP
              refine ⟨P', ?_, by rw [hk]; simp⟩
              have hd : decide (y ∈ letCr cr envM fr pos p) = decide (y ∈ cr) := by
                simp [mem_letCr_of_not_mem hpn]
              rw [hd]
              exact hP'
      have hw : Corr E cr envM envL fr (pos ++ [1]) w := by
        intro y hy
        rcases h y (by rw [hocc]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          by_cases hpn : y ∈ Src.patNames p
          · exfalso
            obtain ⟨-, -, hw0⟩ := hfc y hpn P hP
            omega
          · simp only [findCover, hpn, if_false] at hP
            obtain ⟨P', rfl, hP'⟩ := pick3_two hy hP
            exact ⟨P', hP', by rw [hk]; simp⟩
      have hb : Corr E (letCr cr envM fr pos p) envM
          (envL.set (tIntro cr envM fr pos p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2]) b := by
        intro y hy
        by_cases hyi : y ∈ tIntro cr envM fr pos p
        · left
          rw [IEnv.set_of_mem hyi]
          exact ((mem_tIntro.1 hyi).2.2).symm
        · rw [IEnv.set_of_not_mem hyi]
          rcases h y (by rw [hocc]; omega) with h' | ⟨P, hP, hk⟩
          · exact Or.inl h'
          · right
            by_cases hpn : y ∈ Src.patNames p
            · exfalso
              obtain ⟨rfl, hc, -⟩ := hfc y hpn P hP
              exact hyi (mem_tIntro.2 ⟨hpn, hc, by simpa using hk⟩)
            · simp only [findCover, hpn, if_false] at hP
              obtain ⟨P', rfl, hP'⟩ := pick3_three hy hP
              refine ⟨P', ?_, by rw [hk]; simp⟩
              have hd : decide (y ∈ letCr cr envM fr pos p) = decide (y ∈ cr) := by
                simp [mem_letCr_of_not_mem hpn]
              rw [hd]
              exact hP'
      simp only [toLexAt, elabLFId, elabMId]
      rw [lfIntro_tCross (patNames_toLexAt p E (letCr cr envM fr pos p) envM fr (pos ++ [0]))]
      rw [show crossIn (tCross cr envM fr pos p) (tIntro cr envM fr pos p) cr =
        letCr cr envM fr pos p from rfl]
      rw [elabLFId_toLexAt p E _ envM _ pv fr _ hp, elabLFId_toLexAt w E cr envM envL pv fr _ hw,
        elabLFId_toLexAt b E _ envM _ pv fr _ hb]
  | .letS p w b (some sh), E, cr, envM, envL, pv, fr, pos, h => by
      have hp : Corr (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (envM.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩)
          (envL.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0]) p := by
        intro y hy
        by_cases hyi : y ∈ mIntro (some sh) p
        · left
          rw [IEnv.set_of_mem hyi, IEnv.set_of_mem hyi]
        · rw [IEnv.set_of_not_mem hyi, IEnv.set_of_not_mem hyi]
          have hocc : 0 < occM E y (.letS p w b (some sh)) := by
            simp only [occM, hyi, if_false]
            omega
          rcases h y hocc with h' | ⟨P, hP, hk⟩
          · exact Or.inl h'
          · right
            simp only [findCover, hyi, if_false] at hP
            obtain ⟨P', rfl, hP'⟩ := pick3_one hy hP
            refine ⟨P', ?_, by rw [hk]; simp⟩
            rw [mem_crossIn_some hyi]
            exact hP'
      have hw : Corr E cr envM envL fr (pos ++ [1]) w := by
        intro y hy
        have hocc : 0 < occM E y (.letS p w b (some sh)) := by
          simp only [occM]
          omega
        rcases h y hocc with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          by_cases hyi : y ∈ mIntro (some sh) p
          · simp only [findCover, hyi, if_true, Option.map_eq_some_iff] at hP
            obtain ⟨P', hP', rfl⟩ := hP
            exact ⟨P', hP', by rw [hk]; simp⟩
          · simp only [findCover, hyi, if_false] at hP
            obtain ⟨P', rfl, hP'⟩ := pick3_two hy hP
            exact ⟨P', hP', by rw [hk]; simp⟩
      have hb : Corr (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (envM.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩)
          (envL.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2]) b := by
        intro y hy
        by_cases hyi : y ∈ mIntro (some sh) p
        · left
          rw [IEnv.set_of_mem hyi, IEnv.set_of_mem hyi]
        · rw [IEnv.set_of_not_mem hyi, IEnv.set_of_not_mem hyi]
          have hocc : 0 < occM E y (.letS p w b (some sh)) := by
            simp only [occM, hyi, if_false]
            omega
          rcases h y hocc with h' | ⟨P, hP, hk⟩
          · exact Or.inl h'
          · right
            simp only [findCover, hyi, if_false] at hP
            obtain ⟨P', rfl, hP'⟩ := pick3_three hy hP
            refine ⟨P', ?_, by rw [hk]; simp⟩
            rw [mem_crossIn_some hyi]
            exact hP'
      have hi : lfIntro (some sh) (toLexAt (mIntro (some sh) p ++ E)
          (crossIn (some sh) (mIntro (some sh) p) cr)
          (envM.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0]) p) cr =
          mIntro (some sh) p := by
        simp only [lfIntro, mIntro, crossOwn, patNames_toLexAt]
      simp only [toLexAt, elabLFId, elabMId]
      rw [hi, elabLFId_toLexAt p _ _ _ _ pv fr _ hp, elabLFId_toLexAt w E cr envM envL pv fr _ hw,
        elabLFId_toLexAt b _ _ _ _ pv fr _ hb]
  | .unify p w b, E, cr, envM, envL, pv, fr, pos, h => by
      have hp : Corr E cr envM envL fr (pos ++ [0]) p := by
        intro y hy
        rcases h y (by simp only [occM]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          simp only [findCover] at hP
          obtain ⟨P', rfl, hP'⟩ := pick3_one hy hP
          exact ⟨P', hP', by rw [hk]; simp⟩
      have hw : Corr E cr envM envL fr (pos ++ [1]) w := by
        intro y hy
        rcases h y (by simp only [occM]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          simp only [findCover] at hP
          obtain ⟨P', rfl, hP'⟩ := pick3_two hy hP
          exact ⟨P', hP', by rw [hk]; simp⟩
      have hb : Corr E cr envM envL fr (pos ++ [2]) b := by
        intro y hy
        rcases h y (by simp only [occM]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          simp only [findCover] at hP
          obtain ⟨P', rfl, hP'⟩ := pick3_three hy hP
          exact ⟨P', hP', by rw [hk]; simp⟩
      simp only [toLexAt, elabLFId, elabMId]
      rw [elabLFId_toLexAt p E cr envM envL pv fr _ hp, elabLFId_toLexAt w E cr envM envL pv fr _ hw,
        elabLFId_toLexAt b E cr envM envL pv fr _ hb]
  | .alt t₁ t₂, E, cr, envM, envL, pv, fr, pos, h => by
      have h₁ : Corr E cr envM envL fr (pos ++ [0]) t₁ := by
        intro y hy
        rcases h y (by simp only [occM]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          simp only [findCover] at hP
          obtain ⟨P', rfl, hP'⟩ := pick2_left hy hP
          exact ⟨P', hP', by rw [hk]; simp⟩
      have h₂ : Corr E cr envM envL fr (pos ++ [1]) t₂ := by
        intro y hy
        rcases h y (by simp only [occM]; omega) with h' | ⟨P, hP, hk⟩
        · exact Or.inl h'
        · right
          simp only [findCover] at hP
          obtain ⟨P', rfl, hP'⟩ := pick2_right hy hP
          exact ⟨P', hP', by rw [hk]; simp⟩
      simp only [toLexAt, elabLFId, elabMId]
      rw [elabLFId_toLexAt t₁ E cr envM envL pv fr _ h₁, elabLFId_toLexAt t₂ E cr envM envL pv fr _ h₂]
  | .form z b, E, cr, envM, envL, pv, fr, pos, h => by
      have hcorr : Corr E cr envM envL (pos ++ [0]) (pos ++ [0]) b := by
        intro y hy
        rcases h y hy with h' | ⟨P, hP, _⟩
        · exact Or.inl h'
        · simp [findCover] at hP
      have hb := elabLFId_toLexAt b E cr envM envL (pvSet pv z pos) (pos ++ [0]) (pos ++ [0]) hcorr
      simp only [toLexAt, elabMId, elabLFId, IEnv.set_nil]
      rw [hb]
  | .new ys b, E, cr, envM, envL, pv, fr, pos, h => by
      have hb : Corr (ys ++ E) (cr.filter fun y => decide (y ∉ ys))
          (envM.set ys fun y => ⟨y, fr, pos, .new⟩) (envL.set ys fun y => ⟨y, fr, pos, .new⟩)
          fr pos b := by
        intro y hy
        by_cases hyi : y ∈ ys
        · left
          rw [IEnv.set_of_mem hyi, IEnv.set_of_mem hyi]
        · rw [IEnv.set_of_not_mem hyi, IEnv.set_of_not_mem hyi]
          have hocc : 0 < occM E y (.new ys b) := by
            simp only [occM, hyi, if_false]
            exact hy
          rcases h y hocc with h' | ⟨P, hP, hk⟩
          · exact Or.inl h'
          · right
            simp only [findCover, hyi, if_false] at hP
            refine ⟨P, ?_, hk⟩
            rw [mem_filter_not_mem hyi]
            exact hP
      simp only [toLexAt, elabLFId, elabMId]
      exact elabLFId_toLexAt b _ _ _ _ pv fr pos hb

/-! ## Forms, equations and programs -/

/-- Rule M's environment at the root `R` of a form: a name the form's root
quantifies is named after its covering pattern when it has one, else it is the
root's own slot. -/
def mRootEnv (R : Owner) (t : Src S X) : IEnv X := fun y =>
  match findCover (Src.direct t) y false t with
  | some P => ⟨y, R, R ++ P, .pat⟩
  | none => ⟨y, R, R, .head⟩

/-- Lexical fresh's environment at the root `R` of a form: every name is the
root's own slot until a pattern introduces it. -/
def lfRootEnv (R : Owner) : IEnv X := fun y => ⟨y, R, R, .head⟩

/-- No lambda binds a parameter at the root. -/
def pvRoot (R : Owner) : X → Owner := fun _ => R

/-- Rule M with binder identities, at a form rooted at `R` (the query: `[]`; an
equation: `[5]`). -/
def elabMFormAt (R : Owner) (t : Src S X) : Tm S (BId X) :=
  elabMId (Src.direct t) [] (mRootEnv R t) (pvRoot R) R R t

/-- Lexical fresh with binder identities, at a form rooted at `R`. -/
def elabLFFormAt (R : Owner) (t : Src S X) : Tm S (BId X) :=
  elabLFId [] (lfRootEnv R) (pvRoot R) R R t

/-- **The translator**, at a form rooted at `R`. -/
def toLexicalAt (R : Owner) (t : Src S X) : Src S X :=
  toLexAt (Src.direct t) [] (mRootEnv R t) R R t

/-- **The translator** of a query. -/
def toLexical (t : Src S X) : Src S X := toLexicalAt [] t

/-- The two root environments satisfy the invariant. -/
theorem corr_root (R : Owner) (t : Src S X) :
    Corr (Src.direct t) [] (mRootEnv R t) (lfRootEnv R) R R t := by
  intro y _
  cases hf : findCover (Src.direct t) y false t with
  | none =>
      left
      simp only [lfRootEnv, mRootEnv, hf]
  | some P =>
      right
      exact ⟨P, by simpa using hf, by simp only [mRootEnv, hf]⟩

/-- **The translation is exact, at a form.** -/
theorem elabLFFormAt_toLexicalAt (R : Owner) (t : Src S X) :
    elabLFFormAt R (toLexicalAt R t) = elabMFormAt R t :=
  elabLFId_toLexAt t _ _ _ _ _ _ _ (corr_root R t)

/-- An equation `(= (F) body)` rooted at `R`: its root slots are the clause's
variables, renamed per call by a wrapper activation applied to `unit`; `u`
spells the wrapper's unused parameter. -/
def clauseId (R : Owner) (u : X) (unit : S) (body : Tm S (BId X)) : Tm S (BId X) :=
  .app (.lam (.src (.par u (R ++ [9]))) (frameSlots R body) body) (.sym unit)

/-- The equations of a program under rule M, each elaborated as its own form at
the root `[5]`. -/
def progM (u : X) (unit : S) (cl : S → Option (Src S X)) : S → Option (Tm S (BId X)) :=
  fun F => (cl F).map fun body => clauseId [5] u unit (elabMFormAt [5] body)

/-- The equations of a program under lexical fresh. -/
def progLF (u : X) (unit : S) (cl : S → Option (Src S X)) : S → Option (Tm S (BId X)) :=
  fun F => (cl F).map fun body => clauseId [5] u unit (elabLFFormAt [5] body)

/-- The translation of a program's equations. -/
def toLexicalProg (cl : S → Option (Src S X)) : S → Option (Src S X) :=
  fun F => (cl F).map (toLexicalAt [5])

/-- **The translated equations are rule M's equations**, term for term. -/
theorem progLF_toLexicalProg (u : X) (unit : S) (cl : S → Option (Src S X)) :
    progLF u unit (toLexicalProg cl) = progM u unit cl := by
  funext F
  simp only [progLF, progM, toLexicalProg, Option.map_map, Function.comp_def,
    elabLFFormAt_toLexicalAt]

/-- **Translation correctness on the whole observation.**  For every program,
every activation discipline, fuel, path and store, running the translated
query against the translated equations under lexical fresh gives exactly the
bag of results with final stores that rule M gives on the source: the same
answers with multiplicity, the same stores, the same aliasing.  No renaming or
normalization of names is involved: the elaborated terms are equal. -/
theorem run_toLexical [DecidableEq S] (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (d : Disc) (n : ℕ) (π : Path) (σ : GStore S (BId X)) :
    run d (progLF u unit (toLexicalProg cl)) n π σ (elabLFFormAt [] (toLexical t)) =
      run d (progM u unit cl) n π σ (elabMFormAt [] t) := by
  rw [progLF_toLexicalProg, toLexical, elabLFFormAt_toLexicalAt]

/-- The answers, as a corollary. -/
theorem answers_toLexical [DecidableEq S] (u : X) (unit : S) (cl : S → Option (Src S X))
    (t : Src S X) (d : Disc) (n : ℕ) :
    answers d (progLF u unit (toLexicalProg cl)) n (elabLFFormAt [] (toLexical t)) =
      answers d (progM u unit cl) n (elabMFormAt [] t) := by
  rw [progLF_toLexicalProg, toLexical, elabLFFormAt_toLexicalAt]

/-! ## The census, and agreement under the corrected condition -/

/-- **The refining patterns** of a form: each plain `let` (by position) with the
pattern names lexical fresh would make fresh where rule M refines. -/
def refiningAt (E cr : List X) (env : IEnv X) (fr pos : Owner) : Src S X → List (Owner × X)
  | .lam _ none b =>
      refiningAt (ownRuleMDefault E b ++ Src.direct b ++ E)
        (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
          (ownRuleMDefault E b)))
        (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0]) b
  | .lam _ (some sh) b =>
      refiningAt (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
        (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
        (env.set (crossOwn (some sh) (Src.uses b) [])
          (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
            (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0]) b
  | .app f a => refiningAt E cr env fr (pos ++ [0]) f ++ refiningAt E cr env fr (pos ++ [1]) a
  | .letS p w b none =>
      (tMarks cr env fr pos p).map (fun y => (pos, y)) ++
        refiningAt E (letCr cr env fr pos p) env fr (pos ++ [0]) p ++
        refiningAt E cr env fr (pos ++ [1]) w ++
        refiningAt E (letCr cr env fr pos p) env fr (pos ++ [2]) b
  | .letS p w b (some sh) =>
      refiningAt (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0]) p ++
        refiningAt E cr env fr (pos ++ [1]) w ++
        refiningAt (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2]) b
  | .unify p w b =>
      refiningAt E cr env fr (pos ++ [0]) p ++ refiningAt E cr env fr (pos ++ [1]) w ++
        refiningAt E cr env fr (pos ++ [2]) b
  | .alt t₁ t₂ => refiningAt E cr env fr (pos ++ [0]) t₁ ++ refiningAt E cr env fr (pos ++ [1]) t₂
  | .new ys b =>
      refiningAt (ys ++ E) (cr.filter fun y => decide (y ∉ ys)) (env.set ys fun y => ⟨y, fr, pos, .new⟩)
        fr pos b
  | .form _ b => refiningAt E cr env (pos ++ [0]) (pos ++ [0]) b
  | _ => []

/-- **The un-introduced names** of a form: each lambda (by position) with the
names it owns by rule M that occur in its body and have no covering pattern,
among them the names written only in the body and introduced by no pattern. -/
def unintroducedAt (E cr : List X) (env : IEnv X) (fr pos : Owner) : Src S X → List (Owner × X)
  | .lam _ none b =>
      (mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b (ownRuleMDefault E b)).map
          (fun y => (pos, y)) ++
        unintroducedAt (ownRuleMDefault E b ++ Src.direct b ++ E)
          (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
            (ownRuleMDefault E b)))
          (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
          (pos ++ [0]) (pos ++ [0]) b
  | .lam _ (some sh) b =>
      unintroducedAt (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
        (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
        (env.set (crossOwn (some sh) (Src.uses b) [])
          (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
            (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0]) b
  | .app f a => unintroducedAt E cr env fr (pos ++ [0]) f ++ unintroducedAt E cr env fr (pos ++ [1]) a
  | .letS p w b none =>
      unintroducedAt E (letCr cr env fr pos p) env fr (pos ++ [0]) p ++
        unintroducedAt E cr env fr (pos ++ [1]) w ++
        unintroducedAt E (letCr cr env fr pos p) env fr (pos ++ [2]) b
  | .letS p w b (some sh) =>
      unintroducedAt (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0]) p ++
        unintroducedAt E cr env fr (pos ++ [1]) w ++
        unintroducedAt (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
          (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2]) b
  | .unify p w b =>
      unintroducedAt E cr env fr (pos ++ [0]) p ++ unintroducedAt E cr env fr (pos ++ [1]) w ++
        unintroducedAt E cr env fr (pos ++ [2]) b
  | .alt t₁ t₂ =>
      unintroducedAt E cr env fr (pos ++ [0]) t₁ ++ unintroducedAt E cr env fr (pos ++ [1]) t₂
  | .new ys b =>
      unintroducedAt (ys ++ E) (cr.filter fun y => decide (y ∉ ys))
        (env.set ys fun y => ⟨y, fr, pos, .new⟩) fr pos b
  | .form _ b => unintroducedAt E cr env (pos ++ [0]) (pos ++ [0]) b
  | _ => []

/-- **With nothing to mark and nothing to declare, the translation is the
identity.** -/
theorem toLexAt_eq_self : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    refiningAt E cr env fr pos t = [] → unintroducedAt E cr env fr pos t = [] →
    toLexAt E cr env fr pos t = t
  | .sym _, _, _, _, _, _, _, _ => rfl
  | .fn _, _, _, _, _, _, _, _ => rfl
  | .sv _, _, _, _, _, _, _, _ => rfl
  | .par _, _, _, _, _, _, _, _ => rfl
  | .quote _, _, _, _, _, _, _, _ => rfl
  | .pquote _, _, _, _, _, _, _, _ => rfl
  | .lam z none b, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt] at hr
      simp only [unintroducedAt, List.append_eq_nil_iff, List.map_eq_nil_iff] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self b _ _ _ _ _ hr hu.2, hu.1]
      rfl
  | .lam z (some sh) b, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt] at hr
      simp only [unintroducedAt] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self b _ _ _ _ _ hr hu]
  | .app f a, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt, List.append_eq_nil_iff] at hr
      simp only [unintroducedAt, List.append_eq_nil_iff] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self f _ _ _ _ _ hr.1 hu.1, toLexAt_eq_self a _ _ _ _ _ hr.2 hu.2]
  | .letS p w b none, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt, List.append_eq_nil_iff, List.map_eq_nil_iff] at hr
      simp only [unintroducedAt, List.append_eq_nil_iff] at hu
      have hc : tCross cr env fr pos p = none := by simp [tCross, hr.1.1.1]
      simp only [toLexAt]
      rw [toLexAt_eq_self p _ _ _ _ _ hr.1.1.2 hu.1.1, toLexAt_eq_self w _ _ _ _ _ hr.1.2 hu.1.2,
        toLexAt_eq_self b _ _ _ _ _ hr.2 hu.2, hc]
  | .letS p w b (some sh), E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt, List.append_eq_nil_iff] at hr
      simp only [unintroducedAt, List.append_eq_nil_iff] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self p _ _ _ _ _ hr.1.1 hu.1.1, toLexAt_eq_self w _ _ _ _ _ hr.1.2 hu.1.2,
        toLexAt_eq_self b _ _ _ _ _ hr.2 hu.2]
  | .unify p w b, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt, List.append_eq_nil_iff] at hr
      simp only [unintroducedAt, List.append_eq_nil_iff] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self p _ _ _ _ _ hr.1.1 hu.1.1, toLexAt_eq_self w _ _ _ _ _ hr.1.2 hu.1.2,
        toLexAt_eq_self b _ _ _ _ _ hr.2 hu.2]
  | .alt t₁ t₂, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt, List.append_eq_nil_iff] at hr
      simp only [unintroducedAt, List.append_eq_nil_iff] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self t₁ _ _ _ _ _ hr.1 hu.1, toLexAt_eq_self t₂ _ _ _ _ _ hr.2 hu.2]
  | .new ys b, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt] at hr
      simp only [unintroducedAt] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self b _ _ _ _ _ hr hu]
  | .form _ b, E, cr, env, fr, pos, hr, hu => by
      simp only [refiningAt] at hr
      simp only [unintroducedAt] at hu
      simp only [toLexAt]
      rw [toLexAt_eq_self b _ _ _ _ _ hr hu]

/-- The translation never shrinks a term. -/
theorem sizeOf_le_toLexAt : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    sizeOf t ≤ sizeOf (toLexAt E cr env fr pos t)
  | .sym _, _, _, _, _, _ => le_refl _
  | .fn _, _, _, _, _, _ => le_refl _
  | .sv _, _, _, _, _, _ => le_refl _
  | .par _, _, _, _, _, _ => le_refl _
  | .quote _, _, _, _, _, _ => le_refl _
  | .pquote _, _, _, _, _, _ => le_refl _
  | .lam z none b, E, cr, env, fr, pos => by
      have ih := sizeOf_le_toLexAt b (ownRuleMDefault E b ++ Src.direct b ++ E)
        (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
          (ownRuleMDefault E b)))
        (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0])
      simp only [toLexAt]
      cases hn : mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b (ownRuleMDefault E b) with
      | nil =>
          rw [hn] at ih
          simp only [wrapNew, Src.lam.sizeOf_spec]
          omega
      | cons y ys =>
          rw [hn] at ih
          simp only [wrapNew, Src.lam.sizeOf_spec, Src.new.sizeOf_spec]
          omega
  | .lam z (some sh) b, E, cr, env, fr, pos => by
      have ih := sizeOf_le_toLexAt b (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
        (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
        (env.set (crossOwn (some sh) (Src.uses b) [])
          (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
            (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0])
      simp only [toLexAt, Src.lam.sizeOf_spec]
      omega
  | .app f a, E, cr, env, fr, pos => by
      have h₁ := sizeOf_le_toLexAt f E cr env fr (pos ++ [0])
      have h₂ := sizeOf_le_toLexAt a E cr env fr (pos ++ [1])
      simp only [toLexAt, Src.app.sizeOf_spec]
      omega
  | .letS p w b none, E, cr, env, fr, pos => by
      have h₁ := sizeOf_le_toLexAt p E (letCr cr env fr pos p) env fr (pos ++ [0])
      have h₂ := sizeOf_le_toLexAt w E cr env fr (pos ++ [1])
      have h₃ := sizeOf_le_toLexAt b E (letCr cr env fr pos p) env fr (pos ++ [2])
      simp only [toLexAt, Src.letS.sizeOf_spec]
      cases tCross cr env fr pos p with
      | none => simp only [Option.none.sizeOf_spec]; omega
      | some sh => simp only [Option.none.sizeOf_spec, Option.some.sizeOf_spec]; omega
  | .letS p w b (some sh), E, cr, env, fr, pos => by
      have h₁ := sizeOf_le_toLexAt p (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
        (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0])
      have h₂ := sizeOf_le_toLexAt w E cr env fr (pos ++ [1])
      have h₃ := sizeOf_le_toLexAt b (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
        (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2])
      simp only [toLexAt, Src.letS.sizeOf_spec]
      omega
  | .unify p w b, E, cr, env, fr, pos => by
      have h₁ := sizeOf_le_toLexAt p E cr env fr (pos ++ [0])
      have h₂ := sizeOf_le_toLexAt w E cr env fr (pos ++ [1])
      have h₃ := sizeOf_le_toLexAt b E cr env fr (pos ++ [2])
      simp only [toLexAt, Src.unify.sizeOf_spec]
      omega
  | .alt t₁ t₂, E, cr, env, fr, pos => by
      have h₁ := sizeOf_le_toLexAt t₁ E cr env fr (pos ++ [0])
      have h₂ := sizeOf_le_toLexAt t₂ E cr env fr (pos ++ [1])
      simp only [toLexAt, Src.alt.sizeOf_spec]
      omega
  | .new ys b, E, cr, env, fr, pos => by
      have h₁ := sizeOf_le_toLexAt b (ys ++ E) (cr.filter fun y => decide (y ∉ ys))
        (env.set ys fun y => ⟨y, fr, pos, .new⟩) fr pos
      simp only [toLexAt, Src.new.sizeOf_spec]
      omega
  | .form _ b, E, cr, env, fr, pos => by
      have ih := sizeOf_le_toLexAt b E cr env (pos ++ [0]) (pos ++ [0])
      simp only [toLexAt, Src.form.sizeOf_spec]
      omega

/-- **The census is exact**: the translation changes nothing exactly when
there is no refining pattern and no un-introduced name. -/
theorem toLexAt_eq_self_iff : ∀ (t : Src S X) (E cr : List X) (env : IEnv X) (fr pos : Owner),
    toLexAt E cr env fr pos t = t ↔
      refiningAt E cr env fr pos t = [] ∧ unintroducedAt E cr env fr pos t = []
  | .sym _, _, _, _, _, _ => by simp [toLexAt, refiningAt, unintroducedAt]
  | .fn _, _, _, _, _, _ => by simp [toLexAt, refiningAt, unintroducedAt]
  | .sv _, _, _, _, _, _ => by simp [toLexAt, refiningAt, unintroducedAt]
  | .par _, _, _, _, _, _ => by simp [toLexAt, refiningAt, unintroducedAt]
  | .quote _, _, _, _, _, _ => by simp [toLexAt, refiningAt, unintroducedAt]
  | .pquote _, _, _, _, _, _ => by simp [toLexAt, refiningAt, unintroducedAt]
  | .lam z none b, E, cr, env, fr, pos => by
      have ih := toLexAt_eq_self_iff b (ownRuleMDefault E b ++ Src.direct b ++ E)
        (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
          (ownRuleMDefault E b)))
        (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0])
      have hsz := sizeOf_le_toLexAt b (ownRuleMDefault E b ++ Src.direct b ++ E)
        (cr.filter fun y => decide (y ∉ mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b
          (ownRuleMDefault E b)))
        (env.set (ownRuleMDefault E b) (mKey (ownRuleMDefault E b ++ Src.direct b ++ E) cr (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0])
      simp only [toLexAt, refiningAt, unintroducedAt, Src.lam.injEq, true_and, List.append_eq_nil_iff,
        List.map_eq_nil_iff]
      cases hn : mNews (ownRuleMDefault E b ++ Src.direct b ++ E) cr b (ownRuleMDefault E b) with
      | nil =>
          simp only [wrapNew, true_and]
          rw [hn] at ih
          exact ih
      | cons y ys =>
          rw [hn] at hsz
          simp only [wrapNew, reduceCtorEq, false_and, and_false, iff_false]
          intro he
          have := congrArg sizeOf he
          simp only [Src.new.sizeOf_spec] at this
          omega
  | .lam z (some sh) b, E, cr, env, fr, pos => by
      have ih := toLexAt_eq_self_iff b (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
        (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr)
        (env.set (crossOwn (some sh) (Src.uses b) [])
          (cKey (crossOwn (some sh) (Src.uses b) [] ++ Src.direct b ++ E)
            (crossIn (some sh) (crossOwn (some sh) (Src.uses b) []) cr) (pos ++ [0]) b))
        (pos ++ [0]) (pos ++ [0])
      simp only [toLexAt, refiningAt, unintroducedAt, Src.lam.injEq, true_and]
      exact ih
  | .app f a, E, cr, env, fr, pos => by
      have h₁ := toLexAt_eq_self_iff f E cr env fr (pos ++ [0])
      have h₂ := toLexAt_eq_self_iff a E cr env fr (pos ++ [1])
      simp only [toLexAt, refiningAt, unintroducedAt, Src.app.injEq, List.append_eq_nil_iff, h₁, h₂]
      tauto
  | .letS p w b none, E, cr, env, fr, pos => by
      have h₁ := toLexAt_eq_self_iff p E (letCr cr env fr pos p) env fr (pos ++ [0])
      have h₂ := toLexAt_eq_self_iff w E cr env fr (pos ++ [1])
      have h₃ := toLexAt_eq_self_iff b E (letCr cr env fr pos p) env fr (pos ++ [2])
      have hc : tCross cr env fr pos p = none ↔ tMarks cr env fr pos p = [] := by
        unfold tCross
        split <;> simp_all
      simp only [toLexAt, refiningAt, unintroducedAt, Src.letS.injEq, List.append_eq_nil_iff,
        List.map_eq_nil_iff, h₁, h₂, h₃, hc]
      tauto
  | .letS p w b (some sh), E, cr, env, fr, pos => by
      have h₁ := toLexAt_eq_self_iff p (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
        (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [0])
      have h₂ := toLexAt_eq_self_iff w E cr env fr (pos ++ [1])
      have h₃ := toLexAt_eq_self_iff b (mIntro (some sh) p ++ E) (crossIn (some sh) (mIntro (some sh) p) cr)
        (env.set (mIntro (some sh) p) fun y => ⟨y, fr, pos, .pat⟩) fr (pos ++ [2])
      simp only [toLexAt, refiningAt, unintroducedAt, Src.letS.injEq, List.append_eq_nil_iff, h₁, h₂, h₃,
        and_true]
      tauto
  | .unify p w b, E, cr, env, fr, pos => by
      have h₁ := toLexAt_eq_self_iff p E cr env fr (pos ++ [0])
      have h₂ := toLexAt_eq_self_iff w E cr env fr (pos ++ [1])
      have h₃ := toLexAt_eq_self_iff b E cr env fr (pos ++ [2])
      simp only [toLexAt, refiningAt, unintroducedAt, Src.unify.injEq, List.append_eq_nil_iff, h₁, h₂, h₃]
      tauto
  | .alt t₁ t₂, E, cr, env, fr, pos => by
      have h₁ := toLexAt_eq_self_iff t₁ E cr env fr (pos ++ [0])
      have h₂ := toLexAt_eq_self_iff t₂ E cr env fr (pos ++ [1])
      simp only [toLexAt, refiningAt, unintroducedAt, Src.alt.injEq, List.append_eq_nil_iff, h₁, h₂]
      tauto
  | .new ys b, E, cr, env, fr, pos => by
      have h₁ := toLexAt_eq_self_iff b (ys ++ E) (cr.filter fun y => decide (y ∉ ys))
        (env.set ys fun y => ⟨y, fr, pos, .new⟩) fr pos
      simp only [toLexAt, refiningAt, unintroducedAt, Src.new.injEq, true_and, h₁]
  | .form _ b, E, cr, env, fr, pos => by
      have ih := toLexAt_eq_self_iff b E cr env (pos ++ [0]) (pos ++ [0])
      simp only [toLexAt, refiningAt, unintroducedAt, Src.form.injEq, true_and]
      exact ih

/-- The refining patterns of a form rooted at `R`. -/
def refining (R : Owner) (t : Src S X) : List (Owner × X) :=
  refiningAt (Src.direct t) [] (mRootEnv R t) R R t

/-- The un-introduced names of a form rooted at `R`. -/
def unintroduced (R : Owner) (t : Src S X) : List (Owner × X) :=
  unintroducedAt (Src.direct t) [] (mRootEnv R t) R R t

/-- **The census** of a form: how many refining patterns, and how many
un-introduced names. -/
def census (R : Owner) (t : Src S X) : ℕ × ℕ := ((refining R t).length, (unintroduced R t).length)

theorem toLexicalAt_eq_self {R : Owner} {t : Src S X} (hr : refining R t = [])
    (hu : unintroduced R t = []) : toLexicalAt R t = t :=
  toLexAt_eq_self t _ _ _ _ _ hr hu

/-- The census of a form is empty exactly when the translation leaves it
unchanged. -/
theorem toLexicalAt_eq_self_iff (R : Owner) (t : Src S X) :
    toLexicalAt R t = t ↔ refining R t = [] ∧ unintroduced R t = [] :=
  toLexAt_eq_self_iff t _ _ _ _ _

/-- **Agreement under the corrected condition.**  On a form with no refining
pattern and no un-introduced name, lexical fresh and rule M elaborate it to
the same term. -/
theorem agreement {R : Owner} {t : Src S X} (hr : refining R t = []) (hu : unintroduced R t = []) :
    elabLFFormAt R t = elabMFormAt R t := by
  have h := elabLFFormAt_toLexicalAt R t
  rwa [toLexicalAt_eq_self hr hu] at h

/-- **Agreement on the whole observation.**  If the query and every equation
have no refining pattern and no un-introduced name, lexical fresh and rule M
give the same bag of results with final stores, at every fuel, path, store
and discipline. -/
theorem run_agreement [DecidableEq S] (u : X) (unit : S) (cl : S → Option (Src S X)) (t : Src S X)
    (hr : refining [] t = []) (hu : unintroduced [] t = [])
    (hcl : ∀ F body, cl F = some body → refining [5] body = [] ∧ unintroduced [5] body = [])
    (d : Disc) (n : ℕ) (π : Path) (σ : GStore S (BId X)) :
    run d (progLF u unit cl) n π σ (elabLFFormAt [] t) = run d (progM u unit cl) n π σ (elabMFormAt [] t) := by
  have hp : progLF u unit cl = progM u unit cl := by
    funext F
    simp only [progLF, progM]
    cases hF : cl F with
    | none => rfl
    | some body =>
        obtain ⟨h1, h2⟩ := hcl F body hF
        simp only [Option.map_some, agreement h1 h2]
  rw [hp, agreement hr hu]

end Mettapedia.GSLT.LanguageDef.TemplateScope
