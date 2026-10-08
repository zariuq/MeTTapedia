import Mettapedia.GSLT.LanguageDef.ScopedAuthoritativeSlotCompilation
import Mettapedia.GSLT.LanguageDef.TemplateScope.Evaluation

/-!
# Template scope, part 5: the scope-policy spectrum

The three axes of `docs/prime/scope-policy-spectrum-20261006.md`, on the
same small language.

* **Identity is a slot.**  Every profile elaborates authored text (`Src`,
  spellings only) into scope-bearing terms whose store names are slots
  `(owner, spelling)`: the owner is the static position of the scope that
  declares the slot (`[]` for the query).  Two slots never conflict merely
  because they print the same name; substitution cannot capture, because a
  binder only binds its own owner's slots.  At run time an activation copies
  the slots it declares (`Nm.inst`), so a runtime slot is
  (activation, owner, spelling).
* **Ownership** (an elaboration): `queryWide` (lambdas own nothing),
  `mercury` (rule M), `lexicalFresh` (every `let` pattern allocates fresh
  slots scoped to the `let` body; `unify` refines what is in scope),
  `explicitCapture` (a lambda owns every name its region uses).  Each is a
  default.  **A construct's written crossing set overrides it under every
  profile** (`crossOwn`): the crossing set names what a lambda or a `let`
  shares with the outside, `(lam z body){$t}`, `(let p v body){$t}`; a lambda
  owns every other name its region uses, and a `let` makes every other name of
  its pattern fresh.  Inferred lists are metadata, not surface.
* **Private names** (`new ys body`): an explicit introduction under every
  profile.  The block is an activation (`newBlock`) that owns the declared
  names, so each run of it makes fresh slots; nothing is matched.
* **Lifetime**: `perCall`, or `perClosure` — a lambda's own slots are
  hoisted to the scope that creates the closure, so all calls of one closure
  share them (`hoistOwn`).
* **Readout**: `reference` (the static discipline), or `snapshot` — rule B's
  copy at the call of every name unbound at that moment.

`frame_read_eq` connects activation renaming to the activation-local slot
frames of `ScopedAuthoritativeSlotCompilation`: the flat store with fresh
activation slots is exactly the materialized frame, and a declared-unbound
local shields the outer slot of the same spelling.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

universe u v

/-- Static scope owners: the position of the scope's body (`[]` = the query). -/
abbrev Owner := List ℕ

/-- A slot: the owner scope and the spelling it declares. -/
abbrev Slot (X : Type v) := Owner × X

/-- Authored text: spellings only.  A lambda and a `let` carry their written
crossing set, if any (`some xs`: the names the construct shares with the
outside, `(lam z body){$t}`, `(let p v body){$t}`); `unify` is the explicit
refining equation.  `new ys body` declares private names, `(new ($h …) body)`:
a fresh slot for each name at every activation of the construct, scoped to
`body`, under every profile.  It is an explicit introduction, distinct from a
pattern: nothing is matched. -/
inductive Src (S : Type u) (X : Type v) where
  | sym (s : S)
  | fn (F : S)
  | sv (y : X)
  | par (z : X)
  | lam (z : X) (crossing : Option (List X)) (body : Src S X)
  | app (f a : Src S X)
  | quote (c : Src S X)
  | pquote (c : Src S X)
  | letS (p w b : Src S X) (crossing : Option (List X))
  | unify (p w b : Src S X)
  | alt (t₁ t₂ : Src S X)
  | new (names : List X) (body : Src S X)
  /-- A lambda formed from parts while the program runs. The binder spelling
  `z` receives its identity at this formation site: the identity model
  allocates `.par z pos` there, and inside a quotation the binder is
  `codeBinder pos`. The slot model binds `parName z`, the parameter every
  slot lambda binds, so the shipped beta matches the parameter the body
  wrote. The body was written in the surrounding scope. Formation stores an
  empty own list: it does not own the body's store names and does not decide
  their scope again.

  This one former is the ownership outcome of cons-atom, union-atom, a
  substitution head, and a beta head. It is not an interpreter of those four
  heads. Each of them, under rule M, builds a lambda whose parts' store names
  keep the scope they had where written, so a `let` written in a part is
  captured. A lambda written whole (`lam`) owns its names where written.
  `new` in a formed body owns. The former does not interpret `parse`, `let*`,
  `case`, `match`, `superpose`, `collapse`, `*`, lift-let, or lift-app. -/
  | form (z : X) (body : Src S X)
  deriving DecidableEq, Repr

variable {S : Type u} {X : Type v}

namespace Src

/-- Store names written in code.  A nested sealed quotation does not read the
surrounding scope, so its names are not among them. -/
def codeSvs : Src S X → List X
  | .sv y => [y]
  | .lam _ _ b => codeSvs b
  | .form _ b => codeSvs b
  | .app f a => codeSvs f ++ codeSvs a
  | .quote _ => []
  | .pquote c => codeSvs c
  | .letS p w b _ => codeSvs p ++ codeSvs w ++ codeSvs b
  | .unify p w b => codeSvs p ++ codeSvs w ++ codeSvs b
  | .alt t₁ t₂ => codeSvs t₁ ++ codeSvs t₂
  | .new _ b => codeSvs b
  | _ => []

/-- Spellings written at the current scope level.  A `new` block is not a
level of its own: what it writes counts here (a name it declares then has its
own slot inside it, and the enclosing slot has no occurrence there).  A
pattern quotation writes the store names of its code. -/
def direct : Src S X → List X
  | .sv y => [y]
  | .app f a => direct f ++ direct a
  | .pquote c => codeSvs c
  | .letS p w b _ => direct p ++ direct w ++ direct b
  | .unify p w b => direct p ++ direct w ++ direct b
  | .alt t₁ t₂ => direct t₁ ++ direct t₂
  | .new _ b => direct b
  | .form _ b => direct b
  | _ => []

/-- Store names written in a pattern. -/
def patNames : Src S X → List X
  | .sv y => [y]
  | .app f a => patNames f ++ patNames a
  | _ => []

/-- All spellings written, at any depth, outside sealed quotations. -/
def names : Src S X → List X
  | .sv y => [y]
  | .lam _ _ b => names b
  | .form _ b => names b
  | .app f a => names f ++ names a
  | .pquote c => names c
  | .letS p w b _ => names p ++ names w ++ names b
  | .unify p w b => names p ++ names w ++ names b
  | .alt t₁ t₂ => names t₁ ++ names t₂
  | .new _ b => names b
  | _ => []

/-- Drop every written crossing set. -/
def strip : Src S X → Src S X
  | .lam z _ b => .lam z none (strip b)
  | .app f a => .app (strip f) (strip a)
  | .quote c => .quote c
  | .pquote c => .pquote (strip c)
  | .letS p w b _ => .letS (strip p) (strip w) (strip b) none
  | .unify p w b => .unify (strip p) (strip w) (strip b)
  | .alt t₁ t₂ => .alt (strip t₁) (strip t₂)
  | .new ys b => .new ys (strip b)
  | .form z b => .form z (strip b)
  | t => t

end Src

variable [DecidableEq X]

/-- **The own list of a construct under its crossing set**: with a crossing
set written, every name its region uses (`U`: a lambda's used names, a
`let`'s pattern names) outside the set; with none written, the profile's
default `dflt`.  The crossing set overrides the default under every
profile. -/
def crossOwn (xs : Option (List X)) (U dflt : List X) : List X :=
  match xs with
  | some sh => (U.filter fun y => decide (y ∉ sh)).dedup
  | none => dflt

@[simp] theorem crossOwn_none (U dflt : List X) : crossOwn none U dflt = dflt := rfl

/-- The crossing names in force inside a construct: its own crossing set, and
the names in force around it that it does not bind.  No pattern inside makes
a fresh slot for a name in force. -/
def crossIn (xs : Option (List X)) (bound cr : List X) : List X :=
  xs.getD [] ++ cr.filter fun y => decide (y ∉ bound)

/-- A written crossing set makes the own list independent of the default. -/
theorem crossOwn_of_isSome {xs : Option (List X)} (h : xs.isSome = true) (U d d' : List X) :
    crossOwn xs U d = crossOwn xs U d' := by
  cases xs with
  | none => cases h
  | some _ => rfl

namespace Src

/-- The names the maximal nested lambdas share with this scope: their
crossing sets. -/
def sharedUp : Src S X → List X
  | .lam _ xs _ => xs.getD []
  | .app f a => sharedUp f ++ sharedUp a
  | .letS p w b _ => sharedUp p ++ sharedUp w ++ sharedUp b
  | .unify p w b => sharedUp p ++ sharedUp w ++ sharedUp b
  | .alt t₁ t₂ => sharedUp t₁ ++ sharedUp t₂
  | .new _ b => sharedUp b
  | .form _ b => sharedUp b
  | _ => []

/-- The names a lambda region uses: written at its own level, or shared with
it by a nested lambda. -/
def uses (b : Src S X) : List X := direct b ++ sharedUp b

end Src

/-- Owner of a free parameter inside code.  It is not a scope owner: scope
owners do not start with `9`.  Bound names use a longer owner, so a free
parameter and a binder never share an identity. -/
def codeFreeParam : Owner := [9]

/-- Owner of the binder at a quotation-relative position.  The spelling written
on the binder is display data; this owner is the binder's identity. -/
def codeBinder (pos : Owner) : Owner := 9 :: 1 :: pos

/-- A code owner that belongs to a binder, rather than to a free name. -/
def codeBound (o : Owner) : Bool :=
  match o with
  | 9 :: 1 :: _ => true
  | _ => false

/-- The most recent binding of a spelling in a quotation, if it has one. -/
def codeLookup : List (X × Owner) → X → Option Owner
  | [], _ => none
  | (y, o) :: rest, z => if y = z then some o else codeLookup rest z

/-- The store names a quotation pattern binds, each at its own position.
A name under a lambda, a quotation or a nested `let` is not bound here. -/
def svBinds (pos : Owner) : Src S X → List (X × Owner)
  | .sv y => [(y, codeBinder pos)]
  | .app f a => svBinds (pos ++ [0]) f ++ svBinds (pos ++ [1]) a
  | .alt t₁ t₂ => svBinds (pos ++ [0]) t₁ ++ svBinds (pos ++ [1]) t₂
  | _ => []

/-- Parameter occurrences a term does not bind.  A lambda binds its parameter.
A sealed quotation contributes none: its parameters belong to that quotation. -/
def paramOcc : Tm S X → List (Nm X)
  | .pvar x => [x]
  | .lam x _ b => (paramOcc b).filter fun p => decide (p ≠ x)
  | .app f a => paramOcc f ++ paramOcc a
  | .pquote c => paramOcc c
  | .letP p w b => paramOcc p ++ paramOcc w ++ paramOcc b
  | .alt t₁ t₂ => paramOcc t₁ ++ paramOcc t₂
  | _ => []

/-- Bind every free parameter of a term by a lambda with an empty own list.
The first free parameter is the outermost binder.  A term with none is
returned unchanged. -/
def sealParams (t : Tm S X) : Tm S X :=
  (paramOcc t).foldr (fun p acc => .lam p [] acc) t

/-- Code at a quotation-relative position.  `holes` is the scope environment
whose slots a free store name denotes, when the code is a pattern; `none`
seals those names as the query's own slots.  Parameters and store names in
`penv` and `senv` are bound by an enclosing binder of this quotation, most
recent first, and a use of one is a parameter of the code.  A nested
quotation is sealed and starts again at the root. -/
def codeAt (holes : Option (X → Owner)) (penv senv : List (X × Owner)) (pos : Owner) :
    Src S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .par z =>
      match codeLookup penv z with
      | some p => .pvar (.src (p, z))
      | none => .pvar (.src (codeFreeParam, z))
  | .sv y =>
      match codeLookup senv y with
      | some p => .pvar (.src (p, y))
      | none =>
          match holes with
          | some env => .var (.src (env y, y))
          | none => .var (.src ([], y))
  | .lam z _ b =>
      let o := codeBinder pos
      .lam (.src (o, z)) [] (codeAt holes ((z, o) :: penv) senv (pos ++ [0]) b)
  | .form z b =>
      let o := codeBinder pos
      .lam (.src (o, z)) [] (codeAt holes ((z, o) :: penv) senv (pos ++ [0]) b)
  | .app f a =>
      .app (codeAt holes penv senv (pos ++ [0]) f) (codeAt holes penv senv (pos ++ [1]) a)
  | .quote c => .quote (sealParams (codeAt none [] [] [] c))
  | .pquote c => .pquote (codeAt holes [] [] [] c)
  | .letS p w b _ =>
      let binds := svBinds (pos ++ [0]) p
      .letP (codeAt holes penv (binds ++ senv) (pos ++ [0]) p)
        (codeAt holes penv senv (pos ++ [1]) w)
        (codeAt holes penv (binds ++ senv) (pos ++ [2]) b)
  | .unify p w b =>
      let binds := svBinds (pos ++ [0]) p
      .letP (codeAt holes penv (binds ++ senv) (pos ++ [0]) p)
        (codeAt holes penv senv (pos ++ [1]) w)
        (codeAt holes penv (binds ++ senv) (pos ++ [2]) b)
  | .alt t₁ t₂ =>
      .alt (codeAt holes penv senv (pos ++ [0]) t₁) (codeAt holes penv senv (pos ++ [1]) t₂)
  | .new _ b => codeAt holes penv senv (pos ++ [0]) b

/-- Sealed code.  Binders carry their quotation-relative position.  A free
parameter of the code, including a store name bound inside it, is bound by a
lambda of this quotation; a free store name is the query's own slot of that
spelling.  The code of a `new` block is the code of its body. -/
def codeOf (s : Src S X) : Tm S (Slot X) := sealParams (codeAt none [] [] [] s)

/-- A slot name is a hole unless it is a binder of code. An activation copy
keeps the hole bit of the name it copies, so a copy of a binder stays a
binder. -/
def slotHole : Nm (Slot X) → Bool
  | .src (o, _) => !codeBound o
  | .inst _ n => slotHole n

/-- Inside code, a bound name is identified by its position and a free
parameter by its spelling.  Any other name, including a query slot and a
store name bound by the surrounding scope, is a hole. -/
instance : CodeId (Slot X) where
  same
    | .src (o₁, y₁), .src (o₂, y₂) =>
        if codeBound o₁ && codeBound o₂ then decide (o₁ = o₂)
        else if o₁ = codeFreeParam && o₂ = codeFreeParam then decide (y₁ = y₂)
        else decide ((.src (o₁, y₁) : Nm (Slot X)) = .src (o₂, y₂))
    | a, b => decide (a = b)
  hole := slotHole

/-- Resolution environment: the owner of the slot each spelling denotes. -/
abbrev REnv (X : Type v) := X → Owner

/-- Point the spellings `ys` at the owner `o`. -/
def REnv.update (env : REnv X) (ys : List X) (o : Owner) : REnv X :=
  fun y => if y ∈ ys then o else env y

/-- A slot reference. -/
def slotVar (env : REnv X) (y : X) : Tm S (Slot X) := .var (.src (env y, y))

/-- Parameters are lexical and never captured; they keep their spelling. -/
def parName (z : X) : Nm (Slot X) := .src ([], z)

/-- A lambda formed from parts, as the slot model runs it. The own list is
empty: formation does not decide which store names the body owns. The
parameter is `parName z`, so beta matches the parameter the body wrote. The
identity model allocates a different binder, `.par z pos`, at the formation
site (`elabMId`, `elabLFId`). -/
def formedLam (z : X) (body : Tm S (Slot X)) : Tm S (Slot X) :=
  .lam (parName z) [] body

/-- The parameter through which a fresh `let` scope receives its value. -/
def letParam (o : Owner) (y : X) : Nm (Slot X) := .src (o ++ [7], y)

/-- The unused parameter of the activation of a `new` block at `o`, spelled by
its first declared name. -/
def newParam (o : Owner) (y : X) : Nm (Slot X) := .src (o ++ [8], y)

/-- The activation of a `new` block at `o` declaring `y₀ :: ys`: a lambda that
owns the declared names as slots of owner `o ++ [0]` (its body's position),
applied to a closed value.  Every run of the block renames them afresh. -/
def newBlock (o : Owner) (y₀ : X) (ys : List X) (body : Tm S (Slot X)) : Tm S (Slot X) :=
  .app (.lam (newParam o y₀) ((y₀ :: ys).map fun y => (o ++ [0], y)) body)
    (.lam (newParam o y₀) [] (.pvar (newParam o y₀)))

/-! ## Ownership profiles -/

/-- `queryWide`: one slot per spelling per authored form; a lambda owns
nothing and a `let` introduces nothing, unless a crossing set written on it
says otherwise. -/
def elabQ (env : REnv X) (pos : Owner) : Src S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => slotVar env y
  | .par z => .pvar (parName z)
  | .lam z xs b =>
      let own := crossOwn xs (Src.uses b) []
      .lam (parName z) (own.map fun y => (pos ++ [0], y))
        (elabQ (env.update own (pos ++ [0])) (pos ++ [0]) b)
  | .app f a => .app (elabQ env (pos ++ [0]) f) (elabQ env (pos ++ [1]) a)
  | .quote c => .quote (codeOf c)
  | .pquote c => .pquote (sealParams (codeAt (some env) [] [] [] c))
  | .letS p w b xs =>
      match crossOwn xs (Src.patNames p) [] with
      | [] =>
          .letP (elabQ env (pos ++ [0]) p) (elabQ env (pos ++ [1]) w) (elabQ env (pos ++ [2]) b)
      | y₀ :: ys =>
          .app
            (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
              (.letP (elabQ (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [0]) p)
                (.pvar (letParam (pos ++ [2]) y₀))
                (elabQ (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [2]) b)))
            (elabQ env (pos ++ [1]) w)
  | .unify p w b =>
      .letP (elabQ env (pos ++ [0]) p) (elabQ env (pos ++ [1]) w) (elabQ env (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (elabQ env (pos ++ [0]) t₁) (elabQ env (pos ++ [1]) t₂)
  | .new [] b => elabQ env (pos ++ [0]) b
  | .new (y₀ :: ys) b =>
      newBlock pos y₀ ys (elabQ (env.update (y₀ :: ys) (pos ++ [0])) (pos ++ [0]) b)
  | .form z b =>
      formedLam z (elabQ (env.update [] (pos ++ [0])) (pos ++ [0]) b)

/-- Rule M's default for a lambda body: the spellings written directly that
no enclosing scope quantifies. -/
def ownRuleMDefault (E : List X) (b : Src S X) : List X :=
  ((Src.direct b).filter fun y => decide (y ∉ E)).dedup

/-- `mercury`: rule M with slots.  `E` lists the spellings quantified at the
enclosing scopes; a lambda at `pos` owns, by default, its directly written
spellings not in `E`, as slots of owner `pos ++ [0]`.  Inside it, every
spelling it owns or writes directly is quantified (`own ++ direct b ++ E`).
A `let` introduces nothing by default. -/
def elabMS (E : List X) (env : REnv X) (pos : Owner) : Src S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => slotVar env y
  | .par z => .pvar (parName z)
  | .lam z xs b =>
      let own := crossOwn xs (Src.uses b) (ownRuleMDefault E b)
      .lam (parName z) (own.map fun y => (pos ++ [0], y))
        (elabMS (own ++ Src.direct b ++ E) (env.update own (pos ++ [0])) (pos ++ [0]) b)
  | .app f a => .app (elabMS E env (pos ++ [0]) f) (elabMS E env (pos ++ [1]) a)
  | .quote c => .quote (codeOf c)
  | .pquote c => .pquote (sealParams (codeAt (some env) [] [] [] c))
  | .letS p w b xs =>
      match crossOwn xs (Src.patNames p) [] with
      | [] =>
          .letP (elabMS E env (pos ++ [0]) p) (elabMS E env (pos ++ [1]) w)
            (elabMS E env (pos ++ [2]) b)
      | y₀ :: ys =>
          .app
            (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
              (.letP (elabMS ((y₀ :: ys) ++ E) (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [0]) p)
                (.pvar (letParam (pos ++ [2]) y₀))
                (elabMS ((y₀ :: ys) ++ E) (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [2]) b)))
            (elabMS E env (pos ++ [1]) w)
  | .unify p w b =>
      .letP (elabMS E env (pos ++ [0]) p) (elabMS E env (pos ++ [1]) w)
        (elabMS E env (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (elabMS E env (pos ++ [0]) t₁) (elabMS E env (pos ++ [1]) t₂)
  | .new [] b => elabMS E env (pos ++ [0]) b
  | .new (y₀ :: ys) b =>
      newBlock pos y₀ ys
        (elabMS ((y₀ :: ys) ++ E) (env.update (y₀ :: ys) (pos ++ [0])) (pos ++ [0]) b)
  | .form z b =>
      formedLam z (elabMS E (env.update [] (pos ++ [0])) (pos ++ [0]) b)

/-- `explicitCapture`: a lambda owns, by default, every spelling its region
uses (written directly, or shared with it by a nested lambda); its crossing
set connects names.  A `let` introduces nothing by default. -/
def elabEC (env : REnv X) (pos : Owner) : Src S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => slotVar env y
  | .par z => .pvar (parName z)
  | .lam z xs b =>
      let own := crossOwn xs (Src.uses b) (Src.uses b).dedup
      .lam (parName z) (own.map fun y => (pos ++ [0], y))
        (elabEC (env.update own (pos ++ [0])) (pos ++ [0]) b)
  | .app f a => .app (elabEC env (pos ++ [0]) f) (elabEC env (pos ++ [1]) a)
  | .quote c => .quote (codeOf c)
  | .pquote c => .pquote (sealParams (codeAt (some env) [] [] [] c))
  | .letS p w b xs =>
      match crossOwn xs (Src.patNames p) [] with
      | [] =>
          .letP (elabEC env (pos ++ [0]) p) (elabEC env (pos ++ [1]) w)
            (elabEC env (pos ++ [2]) b)
      | y₀ :: ys =>
          .app
            (.lam (letParam (pos ++ [2]) y₀) ((y₀ :: ys).map fun y => (pos ++ [2], y))
              (.letP (elabEC (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [0]) p)
                (.pvar (letParam (pos ++ [2]) y₀))
                (elabEC (env.update (y₀ :: ys) (pos ++ [2])) (pos ++ [2]) b)))
            (elabEC env (pos ++ [1]) w)
  | .unify p w b =>
      .letP (elabEC env (pos ++ [0]) p) (elabEC env (pos ++ [1]) w)
        (elabEC env (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (elabEC env (pos ++ [0]) t₁) (elabEC env (pos ++ [1]) t₂)
  | .new [] b => elabEC env (pos ++ [0]) b
  | .new (y₀ :: ys) b =>
      newBlock pos y₀ ys (elabEC (env.update (y₀ :: ys) (pos ++ [0])) (pos ++ [0]) b)
  | .form z b =>
      formedLam z (elabEC (env.update [] (pos ++ [0])) (pos ++ [0]) b)

/-- The names a `let` introduces under lexical fresh: by its crossing set when
one is written; else its pattern's names that are not in force. -/
def lfIntro (xs : Option (List X)) (p : Src S X) (cr : List X) : List X :=
  crossOwn xs (Src.patNames p) ((Src.patNames p).filter fun y => decide (y ∉ cr)).dedup

/-- `lexicalFresh`: a `let` pattern allocates fresh slots (owner: the `let`
body position) for its spellings, scoped to the body; inner wins.  The fresh
scope is an activation, `((lam u own (let p u b)) v)`, so the value is
evaluated outside it.  `unify` refines the slots in scope.  A lambda owns
nothing by default.  A crossing set decides what a lambda owns and which
pattern names of a `let` stay shared; inside a construct, its crossing names
are in force (`cr`): no pattern there makes a fresh slot for them, since they
are shared with the outside instead of owned or fresh. -/
def elabLF (env : REnv X) (cr : List X) (pos : Owner) : Src S X → Tm S (Slot X)
  | .sym s => .sym s
  | .fn F => .fn F
  | .sv y => slotVar env y
  | .par z => .pvar (parName z)
  | .lam z xs b =>
      let own := crossOwn xs (Src.uses b) []
      .lam (parName z) (own.map fun y => (pos ++ [0], y))
        (elabLF (env.update own (pos ++ [0])) (crossIn xs own cr) (pos ++ [0]) b)
  | .app f a => .app (elabLF env cr (pos ++ [0]) f) (elabLF env cr (pos ++ [1]) a)
  | .quote c => .quote (codeOf c)
  | .pquote c => .pquote (sealParams (codeAt (some env) [] [] [] c))
  | .letS p w b xs =>
      match lfIntro xs p cr with
      | [] =>
          .letP (elabLF env (crossIn xs [] cr) (pos ++ [0]) p) (elabLF env cr (pos ++ [1]) w)
            (elabLF env (crossIn xs [] cr) (pos ++ [2]) b)
      | y₀ :: ys =>
          let o := pos ++ [2]
          let env' := env.update (y₀ :: ys) o
          .app
            (.lam (letParam o y₀) ((y₀ :: ys).map fun y => (o, y))
              (.letP (elabLF env' (crossIn xs (y₀ :: ys) cr) (pos ++ [0]) p)
                (.pvar (letParam o y₀))
                (elabLF env' (crossIn xs (y₀ :: ys) cr) o b)))
            (elabLF env cr (pos ++ [1]) w)
  | .unify p w b =>
      .letP (elabLF env cr (pos ++ [0]) p) (elabLF env cr (pos ++ [1]) w)
        (elabLF env cr (pos ++ [2]) b)
  | .alt t₁ t₂ => .alt (elabLF env cr (pos ++ [0]) t₁) (elabLF env cr (pos ++ [1]) t₂)
  | .new [] b => elabLF env cr (pos ++ [0]) b
  | .new (y₀ :: ys) b =>
      newBlock pos y₀ ys (elabLF (env.update (y₀ :: ys) (pos ++ [0]))
        (cr.filter fun y => decide (y ∉ y₀ :: ys)) (pos ++ [0]) b)
  | .form z b =>
      formedLam z (elabLF (env.update [] (pos ++ [0])) cr (pos ++ [0]) b)

/-- Per-closure lifetime: each lambda's own slots are bound by the nearest
enclosing lambda (created once per activation of the scope that creates the
closure) or, at the top, left free (one persistent slot).  Returns the term
and the slots exported upward. -/
def hoistOwn : Tm S X → Tm S X × List X
  | .lam x own b =>
      let r := hoistOwn b
      (.lam x r.2 r.1, own)
  | .app f a =>
      let rf := hoistOwn f
      let ra := hoistOwn a
      (.app rf.1 ra.1, rf.2 ++ ra.2)
  | .pquote c =>
      let r := hoistOwn c
      (.pquote r.1, r.2)
  | .letP p w b =>
      let rp := hoistOwn p
      let rw := hoistOwn w
      let rb := hoistOwn b
      (.letP rp.1 rw.1 rb.1, rp.2 ++ rw.2 ++ rb.2)
  | .alt t₁ t₂ =>
      let r₁ := hoistOwn t₁
      let r₂ := hoistOwn t₂
      (.alt r₁.1 r₂.1, r₁.2 ++ r₂.2)
  | t => (t, [])

/-! ## Configurations -/

inductive Ownership where
  | queryWide | mercury | lexicalFresh | explicitCapture
  deriving DecidableEq, Repr

inductive Lifetime where
  | perCall | perClosure
  deriving DecidableEq, Repr

inductive Readout where
  | reference | snapshot
  deriving DecidableEq, Repr

/-- A point in the spectrum. -/
structure Config where
  ownership : Ownership
  lifetime : Lifetime
  readout : Readout
  deriving DecidableEq, Repr

/-- Elaborate an authored form whose root scope is `root`. -/
def elabForm (o : Ownership) (root : Owner) (t : Src S X) : Tm S (Slot X) :=
  match o with
  | .queryWide => elabQ (fun _ => root) root t
  | .mercury => elabMS (Src.direct t) (fun _ => root) root t
  | .lexicalFresh => elabLF (fun _ => root) [] root t
  | .explicitCapture => elabEC (fun _ => root) root t

/-- Elaborate under a configuration: ownership, then the lifetime.  The
second component lists the slots exported by top-level lambdas under
`perClosure`: the form's own activation creates those closures. -/
def elabCfgX (c : Config) (root : Owner) (t : Src S X) : Tm S (Slot X) × List (Slot X) :=
  match c.lifetime with
  | .perCall => (elabForm c.ownership root t, [])
  | .perClosure => hoistOwn (elabForm c.ownership root t)

/-- The elaborated form.  At the query, exported per-closure slots stay free:
the query runs once, so each is one persistent slot. -/
def elabCfg (c : Config) (root : Owner) (t : Src S X) : Tm S (Slot X) :=
  (elabCfgX c root t).1

/-- The activation discipline of a readout. -/
def Config.disc (c : Config) : Disc :=
  match c.readout with
  | .reference => .static
  | .snapshot => .copyAtCall

/-- The spellings an authored form may declare at its root (a superset is
harmless: a binder whose slot never occurs renames nothing). -/
def rootSpellings (t : Src S X) : List X := (Src.names t).dedup

/-- An equation clause `(= (F) body)`: its root slots are the clause's
variables, renamed per call by a wrapper activation, together with the
per-closure slots of the closures the clause creates; `u` names the
wrapper's unused parameter and `unit` its argument.  Curried clauses
`(= (F $p₁ … $pₖ) body)` are written as lambdas whose head variables are
bound by `let`s from the parameters. -/
def clauseOf (c : Config) (root : Owner) (u : X) (unit : S) (body : Src S X) :
    Tm S (Slot X) :=
  .app (.lam (.src (root ++ [9], u))
      ((rootSpellings body).map (fun y => (root, y)) ++ (elabCfgX c root body).2)
      (elabCfg c root body))
    (.sym unit)

variable [DecidableEq S]

/-- Answers of an authored query under a configuration. -/
def answersCfg (c : Config) (prog : S → Option (Tm S (Slot X))) (n : ℕ) (t : Src S X) :
    Option (List (Tm S (Slot X))) :=
  answers c.disc prog n (elabCfg c [] t)

/-! ## The six configurations of the matrix -/

def cfgM : Config := ⟨.mercury, .perCall, .reference⟩
def cfgLF : Config := ⟨.lexicalFresh, .perCall, .reference⟩
def cfgEC : Config := ⟨.explicitCapture, .perCall, .reference⟩
def cfgQ : Config := ⟨.queryWide, .perCall, .reference⟩
def cfgPC : Config := ⟨.mercury, .perClosure, .reference⟩
def cfgSN : Config := ⟨.mercury, .perCall, .snapshot⟩

/-! ## Activation frames: the slot substrate -/

open FiniteEnvironmentCompilation ScopedAuthoritativeSlotCompilation

/-- The frame of an activation: its declared spellings. -/
def frameInventory (own : List X) (h : own.Nodup) : Inventory X := ⟨own, h⟩

/-- The frame's cells, read from the flat store at the activation's fresh
slots. -/
def frameCells (ρ : Path) (own : List X) (h : own.Nodup) (σ : GStore S X) :
    SlotEnvironment (frameInventory own h) (GVal S X) :=
  fun slot => (σ (.inst ρ (.src ((frameInventory own h).reify slot)))).map SlotPayload.value

/-- Where the flat store keeps the slot a spelling denotes inside an
activation at `ρ` of a scope declaring `own`. -/
def frameKey (ρ : Path) (own : List X) (y : X) : Nm X :=
  if y ∈ own then .inst ρ (.src y) else .src y

omit [DecidableEq S] in
/-- **Frame adequacy.**  Reading a spelling through the activation frame of
`ScopedAuthoritativeSlotCompilation` (declared locals in the frame, the rest
outside) is reading the flat store at the activation's fresh slot.  Hence
activation renaming implements the slot frame, and a declared-unbound local
shields the outer slot of the same spelling (`frame_shields`). -/
theorem frame_read_eq (ρ : Path) (own : List X) (h : own.Nodup) (σ : GStore S X) (y : X) :
    readBoundary (frameInventory own h) (fun x => σ (.src x)) (frameCells ρ own h σ) y =
      some (σ (frameKey ρ own y)) := by
  unfold readBoundary frameKey
  by_cases hy : y ∈ own
  · obtain ⟨slot, hslot⟩ :=
      ((frameInventory own h).exists_resolve?_eq_some_iff y).2 hy
    have hreify : (frameInventory own h).reify slot = y :=
      ((frameInventory own h).resolve?_eq_some_iff y slot).1 hslot
    rw [hslot, if_pos hy]
    simp only [lookupLocal, resolveLocal, frameCells, hreify]
    cases σ (.inst ρ (.src y)) <;> rfl
  · have hnone : (frameInventory own h).resolve? y = none := by
      cases hr : (frameInventory own h).resolve? y with
      | none => rfl
      | some slot =>
          exact absurd (((frameInventory own h).exists_resolve?_eq_some_iff y).1
            ⟨slot, hr⟩) hy
    rw [hnone, if_neg hy]

omit [DecidableEq S] in
/-- Right after activation the fresh slots are unbound: the frame reads a
declared spelling as declared-unbound even where the outer store binds the
same spelling. -/
theorem frame_shields (ρ : Path) (own : List X) (h : own.Nodup) (σ : GStore S X) (y : X)
    (hy : y ∈ own) (hfresh : σ (.inst ρ (.src y)) = Option.none) :
    readBoundary (frameInventory own h) (fun x => σ (.src x)) (frameCells ρ own h σ) y =
      some Option.none := by
  rw [frame_read_eq, frameKey, if_pos hy, hfresh]

end Mettapedia.GSLT.LanguageDef.TemplateScope
