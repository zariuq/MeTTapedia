import Mathlib.Data.List.Basic
import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum

/-!
# Template scope, part 10: surface syntax

Printers from the model to Prime's surface syntax, as S-expressions over
structured atoms (`SAtom`); turning atoms into text is the last step.

* `printSrc` — authored text (`Src`) to a MeTTa form: `let`, `lam`, each with
  its crossing set when one is written, `(new ($h …) body)`, the wrapper `(meta T {$t})` whose
  surface spelling is a brace set touching the term, `(lam z body){$t}`;
  application, `unify` (its else branch `(empty)`: the model's `unify` has
  none, and a failed match gives no answer), alternatives as `superpose`,
  quotations as `quote`, store names as `$y`, parameters bare, and an
  equation reference as the nullary call `(F)`.
* `printAns` — answers (`Tm S (Slot X)`) to Prime's answer notation, through a
  naming of store names.  `bagNaming` prints the query's own slots as `$y` and
  every name a configuration allocates (an activation copy, or a per-closure
  slot left free) as `$y#k`, numbered by first occurrence in the bag.
* An application whose spine starts with a symbol is data and prints flat,
  `(Pair a b)`; every other application is a call and prints binary,
  `(((second) a) $t)`, `($f 1)`.  The evaluator builds data application
  curried, and calls are curried, so this is the one reading of each.

## Main results

* `readSrc_printSrc` — on terms without pattern quotations, the reader
  `readSrc` inverts `printSrc`, crossing sets included; hence
  `printSrc_injective`: the printed program determines the authored term.
* `printAns_injective` — on first-order answers (symbols, data application
  and store names) the printed form determines the answer, for any naming
  that is injective on the names that occur and never prints a symbol.
* `bagNaming_injOn` — the naming of a bag gives the query's slots and the
  names the bag allocates atoms that no other name gets.
* `printAns_bag_faithful` — hence a first-order term that prints like a
  first-order answer of a bag, under the bag's naming, is that answer.

All of this is about S-expressions over structured atoms; turning atoms into
text (`SExp.render`) is a table lookup, checked where the export is written.
Inferred own lists are metadata: no surface printer shows them.  The
canonical form of elaborated terms (`printCanon`) keeps them, losslessly
(`readCanon_printCanon`), and substitution keeps them (`lamMeta_subst_sublist`).
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v w

/-! ## S-expressions -/

/-- Keywords of the surface syntax. -/
inductive Kw where
  | lam | let_ | unify | superpose | quote | empty | eq | meta_ | new_ | form
  deriving DecidableEq, Repr

/-- Atoms of the surface syntax, before they become text. -/
inductive SAtom (S : Type u) (X : Type v) where
  /-- A symbol or numeral. -/
  | sym (s : S)
  /-- A keyword. -/
  | kw (k : Kw)
  /-- A store name as written, `$y`. -/
  | var (y : X)
  /-- The `k`-th name a configuration allocated, spelled `y`: `$y#k`. -/
  | fresh (y : X) (k : ℕ)
  /-- A lambda parameter, written bare. -/
  | par (z : X)
  deriving DecidableEq, Repr

/-- S-expressions: atoms, parenthesized lists, and brace sets. -/
inductive SExp (α : Type w) where
  | atom (a : α)
  | list (items : List (SExp α))
  | braces (items : List (SExp α))
  deriving Repr

namespace SExp

variable {α : Type w}

mutual
/-- Decide equality of S-expressions. -/
def decEq [DecidableEq α] : (a b : SExp α) → Decidable (a = b)
  | .atom x, .atom y =>
      if h : x = y then isTrue (h ▸ rfl) else isFalse fun e => h (SExp.atom.inj e)
  | .list xs, .list ys =>
      match decEqItems xs ys with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (SExp.list.inj e)
  | .braces xs, .braces ys =>
      match decEqItems xs ys with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse fun e => h (SExp.braces.inj e)
  | .atom _, .list _ => isFalse (by intro e; cases e)
  | .atom _, .braces _ => isFalse (by intro e; cases e)
  | .list _, .atom _ => isFalse (by intro e; cases e)
  | .list _, .braces _ => isFalse (by intro e; cases e)
  | .braces _, .atom _ => isFalse (by intro e; cases e)
  | .braces _, .list _ => isFalse (by intro e; cases e)

/-- Decide equality of sequences of S-expressions. -/
def decEqItems [DecidableEq α] : (xs ys : List (SExp α)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
      match decEq x y, decEqItems xs ys with
      | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
      | _, isFalse h' => isFalse fun e => h' (List.cons.inj e).2
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
end

instance [DecidableEq α] : DecidableEq (SExp α) := decEq

/-- The items an application extends.  A symbol-headed spine (`sh`) that is
already a list grows flat; anything else becomes the head of a new list. -/
def applyItems : Bool → SExp α → List (SExp α)
  | true, .list items => items
  | _, f => [f]

/-- Extend an application: data spines grow flat, calls print binary. -/
def apply (sh : Bool) (f a : SExp α) : SExp α := .list (applyItems sh f ++ [a])

mutual
/-- Render as text: atoms through `r`, lists in parentheses, sets in braces,
items one space apart.  A wrapper `(m T {…})` whose head `m` satisfies
`isMeta` is written as its surface spelling, the brace set touching the term:
`T{…}`. -/
def render (r : α → String) (isMeta : α → Bool) : SExp α → String
  | .atom a => r a
  | .list items => renderList r isMeta items
  | .braces items => "{" ++ renderSeq r isMeta items ++ "}"

/-- Render the items of a parenthesized form. -/
def renderList (r : α → String) (isMeta : α → Bool) : List (SExp α) → String
  | [.atom m, t, .braces items] =>
      if isMeta m then render r isMeta t ++ "{" ++ renderSeq r isMeta items ++ "}"
      else "(" ++ r m ++ " " ++ render r isMeta t ++ " {" ++ renderSeq r isMeta items ++ "})"
  | items => "(" ++ renderSeq r isMeta items ++ ")"

/-- Render a sequence of items, one space apart. -/
def renderSeq (r : α → String) (isMeta : α → Bool) : List (SExp α) → String
  | [] => ""
  | [e] => render r isMeta e
  | e :: es => render r isMeta e ++ " " ++ renderSeq r isMeta es
end

end SExp

/-! ## Authored text -/

variable {S : Type u} {X : Type v}

namespace Src

/-- Whether the application spine of a term starts with a symbol. -/
def symHeaded : Src S X → Bool
  | .sym _ => true
  | .app f _ => f.symHeaded
  | _ => false

/-- The spellings a term writes bare: its parameters and lambda binders. -/
def params : Src S X → List X
  | .par z => [z]
  | .lam z _ b => z :: params b
  | .form z b => z :: params b
  | .app f a => params f ++ params a
  | .quote c => params c
  | .pquote c => params c
  | .letS p w b _ => params p ++ params w ++ params b
  | .unify p w b => params p ++ params w ++ params b
  | .alt t₁ t₂ => params t₁ ++ params t₂
  | .new _ b => params b
  | _ => []

/-- The equations a term refers to. -/
def fns : Src S X → List S
  | .fn F => [F]
  | .lam _ _ b => fns b
  | .form _ b => fns b
  | .app f a => fns f ++ fns a
  | .quote c => fns c
  | .pquote c => fns c
  | .letS p w b _ => fns p ++ fns w ++ fns b
  | .unify p w b => fns p ++ fns w ++ fns b
  | .alt t₁ t₂ => fns t₁ ++ fns t₂
  | .new _ b => fns b
  | _ => []

end Src

/-- Store names as atoms. -/
def nameAtoms (ys : List X) : List (SExp (SAtom S X)) := ys.map fun y => .atom (.var y)

/-- A construct with its crossing set, when one is written: the wrapper
`(meta T {$t})`, written `T{$t}`.  An empty set prints as `T{}`. -/
def crossForm : Option (List X) → SExp (SAtom S X) → SExp (SAtom S X)
  | none, e => e
  | some xs, e => .list [.atom (.kw .meta_), e, .braces (nameAtoms xs)]

/-- **The printer of authored text.** -/
def printSrc : Src S X → SExp (SAtom S X)
  | .sym s => .atom (.sym s)
  | .fn F => .list [.atom (.sym F)]
  | .sv y => .atom (.var y)
  | .par z => .atom (.par z)
  | .lam z xs b => crossForm xs (.list [.atom (.kw .lam), .atom (.par z), printSrc b])
  | .app f a => SExp.apply f.symHeaded (printSrc f) (printSrc a)
  | .quote c => .list [.atom (.kw .quote), printSrc c]
  | .pquote c => .list [.atom (.kw .quote), printSrc c]
  | .letS p w b xs =>
      crossForm xs (.list [.atom (.kw .let_), printSrc p, printSrc w, printSrc b])
  | .unify p w b =>
      .list [.atom (.kw .unify), printSrc p, printSrc w, printSrc b,
        .list [.atom (.kw .empty)]]
  | .alt t₁ t₂ => .list [.atom (.kw .superpose), .list [printSrc t₁, printSrc t₂]]
  | .new ys b => .list [.atom (.kw .new_), .list (nameAtoms ys), printSrc b]
  | .form z b => .list [.atom (.kw .form), .atom (.par z), printSrc b]

/-- An equation `(= (F) body)`.  The model's equations are nullary: a `k`-ary
equation is a nullary one whose body is `k` nested lambdas, its head variables
bound by `let`s from the parameters. -/
def printClause (F : S) (body : Src S X) : SExp (SAtom S X) :=
  .list [.atom (.kw .eq), .list [.atom (.sym F)], printSrc body]

/-! ## Reading authored text back -/

namespace Src

/-- Terms without a quotation in pattern position.  The surface writes both
quotations `quote`; their role is their position, and the reader takes a
quotation for sealed code. -/
def NoPQuote : Src S X → Bool
  | .pquote _ => false
  | .lam _ _ b => b.NoPQuote
  | .form _ b => b.NoPQuote
  | .app f a => f.NoPQuote && a.NoPQuote
  | .quote c => c.NoPQuote
  | .letS p w b _ => p.NoPQuote && w.NoPQuote && b.NoPQuote
  | .unify p w b => p.NoPQuote && w.NoPQuote && b.NoPQuote
  | .alt t₁ t₂ => t₁.NoPQuote && t₂.NoPQuote
  | .new _ b => b.NoPQuote
  | _ => true

end Src

/-- Read a crossing set back: store-name atoms. -/
def readNames : List (SExp (SAtom S X)) → Option (List X)
  | [] => some []
  | .atom (.var y) :: rest => (readNames rest).map (y :: ·)
  | _ => none

mutual
/-- **The reader of authored text**: the inverse of `printSrc` on terms
without pattern quotations (`readSrc_printSrc`). -/
def readSrc : SExp (SAtom S X) → Option (Src S X)
  | .atom (.sym s) => some (.sym s)
  | .atom (.var y) => some (.sv y)
  | .atom (.par z) => some (.par z)
  | .atom _ => none
  | .braces _ => none
  | .list items => readList items

/-- Read a parenthesized form. -/
def readList : List (SExp (SAtom S X)) → Option (Src S X)
  | [.atom (.sym F)] => some (.fn F)
  | [.atom (.kw .lam), .atom (.par z), b] => (readSrc b).map (.lam z none)
  | [.atom (.kw .let_), p, w, b] =>
      match readSrc p, readSrc w, readSrc b with
      | some p', some w', some b' => some (.letS p' w' b' none)
      | _, _, _ => none
  | [.atom (.kw .meta_), t, .braces xs] =>
      match readNames xs, readSrc t with
      | some xs', some (.lam z none b) => some (.lam z (some xs') b)
      | some xs', some (.letS p w b none) => some (.letS p w b (some xs'))
      | _, _ => none
  | [.atom (.kw .unify), p, w, b, .list [.atom (.kw .empty)]] =>
      match readSrc p, readSrc w, readSrc b with
      | some p', some w', some b' => some (.unify p' w' b')
      | _, _, _ => none
  | [.atom (.kw .superpose), .list [t₁, t₂]] =>
      match readSrc t₁, readSrc t₂ with
      | some a, some b => some (.alt a b)
      | _, _ => none
  | [.atom (.kw .quote), c] => (readSrc c).map .quote
  | [.atom (.kw .new_), .list xs, b] =>
      match readNames xs, readSrc b with
      | some ys, some b' => some (.new ys b')
      | _, _ => none
  | [.atom (.kw .form), .atom (.par z), b] => (readSrc b).map (.form z)
  | .atom (.sym s) :: a :: args => readSpine (.sym s) (a :: args)
  | [f, a] =>
      match readSrc f, readSrc a with
      | some f', some a' => some (.app f' a')
      | _, _ => none
  | _ => none

/-- Read the arguments of a data spine, applying them in order. -/
def readSpine (head : Src S X) : List (SExp (SAtom S X)) → Option (Src S X)
  | [] => some head
  | a :: args =>
      match readSrc a with
      | some a' => readSpine (.app head a') args
      | none => none
end

theorem readNames_nameAtoms (ys : List X) :
    readNames (nameAtoms ys : List (SExp (SAtom S X))) = some ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [nameAtoms, readNames] at ih ⊢; simp [ih]

theorem readSpine_append :
    ∀ (h : Src S X) (xs ys : List (SExp (SAtom S X))),
      readSpine h (xs ++ ys) = (readSpine h xs).bind fun h' => readSpine h' ys
  | h, [], ys => by simp [readSpine]
  | h, x :: xs, ys => by
      simp only [List.cons_append, readSpine]
      cases readSrc x with
      | none => rfl
      | some a => exact readSpine_append _ xs ys

/-- A two-item form whose head is neither a symbol nor a keyword is a call. -/
theorem readList_pair (f a : SExp (SAtom S X))
    (hs : ∀ s, f ≠ .atom (.sym s)) (hk : ∀ k, f ≠ .atom (.kw k)) :
    readList [f, a] =
      match readSrc f, readSrc a with
      | some f', some a' => some (.app f' a')
      | _, _ => none := by
  cases f with
  | atom x =>
      cases x with
      | sym s => exact absurd rfl (hs s)
      | kw k => exact absurd rfl (hk k)
      | var y => simp [readList]
      | fresh y k => simp [readList]
      | par z => simp [readList]
  | list items => simp [readList]
  | braces items => simp [readList]

/-- A lambda printed with its crossing set reads back with it. -/
theorem readSrc_lamForm (z : X) (xs : Option (List X)) (b : Src S X)
    (hb : readSrc (printSrc b) = some b) :
    readSrc (crossForm xs (.list [.atom (.kw .lam), .atom (.par z), printSrc b]) :
      SExp (SAtom S X)) = some (.lam z xs b) := by
  cases xs <;> simp [crossForm, readSrc, readList, hb, readNames_nameAtoms]

/-- A `let` printed with its crossing set reads back with it. -/
theorem readSrc_letForm (p w b : Src S X) (xs : Option (List X))
    (hp : readSrc (printSrc p) = some p) (hw : readSrc (printSrc w) = some w)
    (hb : readSrc (printSrc b) = some b) :
    readSrc (crossForm xs (.list [.atom (.kw .let_), printSrc p, printSrc w, printSrc b]) :
      SExp (SAtom S X)) = some (.letS p w b xs) := by
  cases xs <;> simp [crossForm, readSrc, readList, hp, hw, hb, readNames_nameAtoms]

/-- A form, with or without its crossing set, is no atom. -/
theorem crossForm_list_ne_atom (xs : Option (List X)) (items : List (SExp (SAtom S X)))
    (a : SAtom S X) : crossForm xs (.list items) ≠ .atom a := by
  cases xs <;> simp [crossForm]

/-- The printed term and, for a data spine, its symbol and the printed
arguments, which read back as the spine. -/
theorem readSrc_printSrc_spine :
    ∀ (t : Src S X), t.NoPQuote = true →
      readSrc (printSrc t) = some t ∧
      (t.symHeaded = true → ∃ s args, SExp.applyItems true (printSrc t) = .atom (.sym s) :: args ∧
        readSpine (.sym s) args = some t) ∧
      (t.symHeaded = false → (∀ s, printSrc t ≠ .atom (.sym s)) ∧
        ∀ k, printSrc t ≠ .atom (.kw k))
  | .sym s, _ => ⟨rfl, fun _ => ⟨s, [], rfl, rfl⟩, by simp [Src.symHeaded]⟩
  | .fn F, _ => ⟨rfl, by simp [Src.symHeaded], fun _ => by simp [printSrc]⟩
  | .sv y, _ => ⟨rfl, by simp [Src.symHeaded], fun _ => by simp [printSrc]⟩
  | .par z, _ => ⟨rfl, by simp [Src.symHeaded], fun _ => by simp [printSrc]⟩
  | .lam z xs b, h => by
      simp only [Src.NoPQuote] at h
      have ihb := (readSrc_printSrc_spine b h).1
      refine ⟨readSrc_lamForm z xs b ihb, by simp [Src.symHeaded], fun _ => ⟨?_, ?_⟩⟩
      · intro s
        exact crossForm_list_ne_atom xs _ _
      · intro k
        exact crossForm_list_ne_atom xs _ _
  | .app f a, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      obtain ⟨ihf, ihfs, ihfn⟩ := readSrc_printSrc_spine f h.1
      have iha := (readSrc_printSrc_spine a h.2).1
      cases hsh : f.symHeaded
      · -- a call: `(f a)`
        have hp : printSrc (.app f a) = .list [printSrc f, printSrc a] := by
          simp [printSrc, SExp.apply, SExp.applyItems, hsh]
        obtain ⟨hs, hk⟩ := ihfn hsh
        refine ⟨?_, by simp [Src.symHeaded, hsh], fun _ => ⟨?_, ?_⟩⟩
        · rw [hp, readSrc, readList_pair _ _ hs hk, ihf, iha]
        · intro s; rw [hp]; simp
        · intro k; rw [hp]; simp
      · -- data: `(s args… a)`
        obtain ⟨s, args, hargs, hspine⟩ := ihfs hsh
        have hp : printSrc (.app f a) = .list (.atom (.sym s) :: (args ++ [printSrc a])) := by
          simp [printSrc, SExp.apply, hsh, hargs]
        have hread : readSpine (.sym s) (args ++ [printSrc a]) = some (.app f a) := by
          rw [readSpine_append, hspine]
          simp [readSpine, iha]
        refine ⟨?_, fun _ => ⟨s, args ++ [printSrc a], ?_, hread⟩, by simp [Src.symHeaded, hsh]⟩
        · rw [hp, readSrc]
          cases args with
          | nil => simpa [readList] using hread
          | cons x xs => simpa [readList] using hread
        · rw [hp]
          rfl
  | .quote c, h => by
      simp only [Src.NoPQuote] at h
      have ihc := (readSrc_printSrc_spine c h).1
      exact ⟨by simp [printSrc, readSrc, readList, ihc], by simp [Src.symHeaded],
        fun _ => by simp [printSrc]⟩
  | .pquote _, h => by simp [Src.NoPQuote] at h
  | .letS p w b xs, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      have ihp := (readSrc_printSrc_spine p h.1.1).1
      have ihw := (readSrc_printSrc_spine w h.1.2).1
      have ihb := (readSrc_printSrc_spine b h.2).1
      exact ⟨readSrc_letForm p w b xs ihp ihw ihb, by simp [Src.symHeaded],
        fun _ => ⟨fun _ => crossForm_list_ne_atom xs _ _, fun _ => crossForm_list_ne_atom xs _ _⟩⟩
  | .unify p w b, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      have ihp := (readSrc_printSrc_spine p h.1.1).1
      have ihw := (readSrc_printSrc_spine w h.1.2).1
      have ihb := (readSrc_printSrc_spine b h.2).1
      exact ⟨by simp [printSrc, readSrc, readList, ihp, ihw, ihb], by simp [Src.symHeaded],
        fun _ => by simp [printSrc]⟩
  | .alt t₁ t₂, h => by
      simp only [Src.NoPQuote, Bool.and_eq_true] at h
      have ih₁ := (readSrc_printSrc_spine t₁ h.1).1
      have ih₂ := (readSrc_printSrc_spine t₂ h.2).1
      exact ⟨by simp [printSrc, readSrc, readList, ih₁, ih₂], by simp [Src.symHeaded],
        fun _ => by simp [printSrc]⟩
  | .new ys b, h => by
      simp only [Src.NoPQuote] at h
      have ihb := (readSrc_printSrc_spine b h).1
      exact ⟨by simp [printSrc, readSrc, readList, ihb, readNames_nameAtoms], by simp [Src.symHeaded],
        fun _ => by simp [printSrc]⟩
  | .form z b, h => by
      simp only [Src.NoPQuote] at h
      have ihb := (readSrc_printSrc_spine b h).1
      exact ⟨by simp [printSrc, readSrc, readList, ihb], by simp [Src.symHeaded],
        fun _ => by simp [printSrc]⟩

/-- **The program text reads back**: on terms without pattern quotations,
`readSrc` inverts `printSrc`, crossing sets included. -/
theorem readSrc_printSrc {t : Src S X} (h : t.NoPQuote = true) :
    readSrc (printSrc t) = some t :=
  (readSrc_printSrc_spine t h).1

/-- **The printed program determines the term** (no pattern quotations). -/
theorem printSrc_injective {t t' : Src S X} (h : t.NoPQuote = true)
    (h' : t'.NoPQuote = true) (he : printSrc t = printSrc t') : t = t' := by
  have := readSrc_printSrc h
  rw [he, readSrc_printSrc h'] at this
  exact (Option.some.inj this).symm

/-! ## Answers -/

namespace Tm

variable {Y : Type v}

/-- Whether the application spine of a term starts with a symbol. -/
def symHeaded : Tm S Y → Bool
  | .sym _ => true
  | .app f _ => f.symHeaded
  | _ => false

/-- First-order terms: symbols, data application and store names. -/
def FirstOrder : Tm S Y → Bool
  | .sym _ => true
  | .var _ => true
  | .app f a => f.FirstOrder && a.FirstOrder
  | _ => false

/-- The store names of a term, in printing order. -/
def vars : Tm S Y → List (Nm Y)
  | .var n => [n]
  | .lam _ _ b => vars b
  | .app f a => vars f ++ vars a
  | .quote c => vars c
  | .pquote c => vars c
  | .letP p w b => vars p ++ vars w ++ vars b
  | .alt t₁ t₂ => vars t₁ ++ vars t₂
  | _ => []

end Tm

/-- **The printer of answers**, through a naming `ν` of store names and a
naming `π` of parameters (parameters occur only in answers that are not
first-order).  A lambda's own list is inferred metadata and is not
printed.  Contextual code prints as `(quote body (k …))`, binders through `π`. -/
def printAns {Y : Type v} (ν : Nm Y → SAtom S X) (π : Nm Y → SAtom S X) :
    Tm S Y → SExp (SAtom S X)
  | .sym s => .atom (.sym s)
  | .fn F => .list [.atom (.sym F)]
  | .var n => .atom (ν n)
  | .pvar x => .atom (π x)
  | .lam x _ b => .list [.atom (.kw .lam), .atom (π x), printAns ν π b]
  | .app f a => SExp.apply f.symHeaded (printAns ν π f) (printAns ν π a)
  | .quote c => .list [.atom (.kw .quote), printAns ν π c]
  | .ctx ks c =>
      .list [.atom (.kw .quote), printAns ν π c, .list (ks.map fun k => .atom (π k))]
  | .pquote c => .list [.atom (.kw .quote), printAns ν π c]
  | .letP p w b => .list [.atom (.kw .let_), printAns ν π p, printAns ν π w, printAns ν π b]
  | .alt t₁ t₂ => .list [.atom (.kw .superpose), .list [printAns ν π t₁, printAns ν π t₂]]

/-! ## The printed answer determines the answer -/

section Injective

variable {Y : Type v} {ν π : Nm Y → SAtom S X}

/-- The items an application of a first-order term extends: its symbol, the
items of its data spine (at least two), or the term itself. -/
theorem applyItems_printAns (hsym : ∀ n s, ν n ≠ .sym s) :
    ∀ (t : Tm S Y), t.FirstOrder = true →
      (∃ s, t = .sym s ∧ SExp.applyItems t.symHeaded (printAns ν π t) = [.atom (.sym s)]) ∨
      (∃ f a, t = .app f a ∧ t.symHeaded = true ∧
        ∃ items, printAns ν π t = .list items ∧ 2 ≤ items.length ∧
          SExp.applyItems t.symHeaded (printAns ν π t) = items) ∨
      (t.symHeaded = false ∧ SExp.applyItems t.symHeaded (printAns ν π t) = [printAns ν π t] ∧
        ∀ s, printAns ν π t ≠ .atom (.sym s))
  | .sym s, _ => Or.inl ⟨s, rfl, rfl⟩
  | .var n, _ => Or.inr (Or.inr ⟨rfl, rfl, fun s h => hsym n s (by
      simp only [printAns, SExp.atom.injEq] at h
      exact h)⟩)
  | .app f a, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at h
      cases hf : f.symHeaded
      · refine Or.inr (Or.inr ⟨by simp [Tm.symHeaded, hf], ?_, ?_⟩)
        · simp only [Tm.symHeaded, hf, SExp.applyItems]
        · intro s hs
          simp [printAns, SExp.apply] at hs
      · refine Or.inr (Or.inl ⟨f, a, rfl, by simp [Tm.symHeaded, hf], ?_⟩)
        refine ⟨SExp.applyItems true (printAns ν π f) ++ [printAns ν π a], ?_, ?_, ?_⟩
        · simp [printAns, SExp.apply, hf]
        · rcases applyItems_printAns hsym f h.1 with ⟨s, rfl, _⟩ | ⟨g, b, rfl, _, items, hp, hl, _⟩ |
            ⟨hf', _, _⟩
          · simp [printAns, SExp.applyItems]
          · rw [hp]
            simp only [SExp.applyItems, List.length_append, List.length_singleton]
            omega
          · rw [hf] at hf'
            cases hf'
        · simp [Tm.symHeaded, hf, printAns, SExp.apply, SExp.applyItems]

/-- The printed form of an application is a list. -/
theorem printAns_app (f a : Tm S Y) :
    printAns ν π (.app f a) =
      .list (SExp.applyItems f.symHeaded (printAns ν π f) ++ [printAns ν π a]) := rfl

/-- The items an application extends determine its function part, given that
the printed function determines it. -/
theorem applyItems_inj (hsym : ∀ n s, ν n ≠ .sym s) {f f' : Tm S Y}
    (hf : f.FirstOrder = true) (hf' : f'.FirstOrder = true)
    (ih : printAns ν π f = printAns ν π f' → f = f')
    (h : SExp.applyItems f.symHeaded (printAns ν π f) =
      SExp.applyItems f'.symHeaded (printAns ν π f')) : f = f' := by
  rcases applyItems_printAns (π := π) hsym f hf with ⟨s, hfs, hs⟩ |
      ⟨g, b, hfa, hsh, items, hp, hl, hi⟩ | ⟨hsh, hi, hns⟩ <;>
    rcases applyItems_printAns (π := π) hsym f' hf' with ⟨s', hfs', hs'⟩ |
      ⟨g', b', hfa', hsh', items', hp', hl', hi'⟩ | ⟨hsh', hi', hns'⟩
  · rw [hs, hs'] at h
    simp only [List.cons.injEq, SExp.atom.injEq, SAtom.sym.injEq, and_true] at h
    rw [hfs, hfs', h]
  · rw [hs, hi'] at h
    rw [← h] at hl'
    simp at hl'
  · rw [hs, hi'] at h
    simp only [List.cons.injEq, and_true] at h
    exact absurd h.symm (hns' s)
  · rw [hi, hs'] at h
    rw [h] at hl
    simp at hl
  · rw [hi, hi'] at h
    exact ih (hp.trans (h ▸ hp'.symm))
  · rw [hi, hi'] at h
    rw [h] at hl
    simp at hl
  · rw [hi, hs'] at h
    simp only [List.cons.injEq, and_true] at h
    exact absurd h (hns s')
  · rw [hi, hi'] at h
    rw [← h] at hl'
    simp at hl'
  · rw [hi, hi'] at h
    simp only [List.cons.injEq, and_true] at h
    exact ih h

/-- **The printed answer determines the answer** (first-order answers). -/
theorem printAns_injective (hsym : ∀ n s, ν n ≠ .sym s) :
    ∀ (t t' : Tm S Y), t.FirstOrder = true → t'.FirstOrder = true →
      (∀ n ∈ t.vars, ∀ m ∈ t'.vars, ν n = ν m → n = m) →
      printAns ν π t = printAns ν π t' → t = t'
  | .sym s, .sym s', _, _, _, h => by
      simp only [printAns, SExp.atom.injEq, SAtom.sym.injEq] at h
      rw [h]
  | .sym s, .var m, _, _, _, h => by
      simp only [printAns, SExp.atom.injEq] at h
      exact absurd h.symm (hsym m s)
  | .sym s, .app f a, _, _, _, h => by simp [printAns, SExp.apply] at h
  | .var n, .sym s, _, _, _, h => by
      simp only [printAns, SExp.atom.injEq] at h
      exact absurd h (hsym n s)
  | .var n, .var m, _, _, hν, h => by
      simp only [printAns, SExp.atom.injEq] at h
      rw [hν n (by simp [Tm.vars]) m (by simp [Tm.vars]) h]
  | .var n, .app f a, _, _, _, h => by simp [printAns, SExp.apply] at h
  | .app f a, .sym s, _, _, _, h => by simp [printAns, SExp.apply] at h
  | .app f a, .var m, _, _, _, h => by simp [printAns, SExp.apply] at h
  | .app f a, .app f' a', ht, ht', hν, h => by
      simp only [Tm.FirstOrder, Bool.and_eq_true] at ht ht'
      have hνf : ∀ n ∈ f.vars, ∀ m ∈ f'.vars, ν n = ν m → n = m := fun n hn m hm =>
        hν n (by simp [Tm.vars, hn]) m (by simp [Tm.vars, hm])
      have hνa : ∀ n ∈ a.vars, ∀ m ∈ a'.vars, ν n = ν m → n = m := fun n hn m hm =>
        hν n (by simp [Tm.vars, hn]) m (by simp [Tm.vars, hm])
      rw [printAns_app, printAns_app, SExp.list.injEq] at h
      obtain ⟨hI, hA⟩ := List.append_inj' h rfl
      simp only [List.cons.injEq, and_true] at hA
      rw [applyItems_inj hsym ht.1 ht'.1 (printAns_injective hsym f f' ht.1 ht'.1 hνf) hI,
        printAns_injective hsym a a' ht.2 ht'.2 hνa hA]
  | .sym _, .fn _, _, h, _, _ | .sym _, .pvar _, _, h, _, _ | .sym _, .lam _ _ _, _, h, _, _
  | .sym _, .quote _, _, h, _, _ | .sym _, .ctx _ _, _, h, _, _ | .sym _, .pquote _, _, h, _, _
  | .sym _, .letP _ _ _, _, h, _, _ | .sym _, .alt _ _, _, h, _, _
  | .var _, .fn _, _, h, _, _ | .var _, .pvar _, _, h, _, _ | .var _, .lam _ _ _, _, h, _, _
  | .var _, .quote _, _, h, _, _ | .var _, .ctx _ _, _, h, _, _ | .var _, .pquote _, _, h, _, _
  | .var _, .letP _ _ _, _, h, _, _ | .var _, .alt _ _, _, h, _, _
  | .app _ _, .fn _, _, h, _, _ | .app _ _, .pvar _, _, h, _, _
  | .app _ _, .lam _ _ _, _, h, _, _ | .app _ _, .quote _, _, h, _, _
  | .app _ _, .ctx _ _, _, h, _, _ | .app _ _, .pquote _, _, h, _, _
  | .app _ _, .letP _ _ _, _, h, _, _ | .app _ _, .alt _ _, _, h, _, _ => by simp [Tm.FirstOrder] at h
  | .fn _, _, h, _, _, _ | .pvar _, _, h, _, _, _ | .lam _ _ _, _, h, _, _, _
  | .quote _, _, h, _, _, _ | .ctx _ _, _, h, _, _, _ | .pquote _, _, h, _, _, _
  | .letP _ _ _, _, h, _, _, _ | .alt _ _, _, h, _, _, _ => by simp [Tm.FirstOrder] at h

end Injective

/-! ## Naming the names of a bag -/

section Naming

variable [DecidableEq X]

namespace Nm

/-- The spelling a store name prints with. -/
def spelling : Nm (Slot X) → X
  | .src (_, y) => y
  | .inst _ n => spelling n

/-- The query's own slot `([], y)`: the spelling, if the name is one. -/
def querySpelling? : Nm (Slot X) → Option X
  | .src ([], y) => some y
  | _ => none

omit [DecidableEq X] in
theorem querySpelling?_eq_some {n : Nm (Slot X)} {y : X} :
    n.querySpelling? = some y ↔ n = .src ([], y) := by
  constructor
  · intro h
    cases n with
    | src p =>
        obtain ⟨o, y'⟩ := p
        cases o with
        | nil =>
            simp only [querySpelling?, Option.some.injEq] at h
            rw [h]
        | cons _ _ => simp [querySpelling?] at h
    | inst _ _ => simp [querySpelling?] at h
  · rintro rfl
    rfl

end Nm

/-- The names a bag allocates (store names other than the query's own
slots), by first occurrence. -/
def allocated (bag : List (Tm S (Slot X))) : List (Nm (Slot X)) :=
  ((bag.flatMap Tm.vars).filter fun n => n.querySpelling?.isNone).eraseDups

/-- The naming of a bag: the query's own slots print as `$y`, the `k`-th
allocated name as `$y#k`. -/
def bagNaming (names : List (Nm (Slot X))) (n : Nm (Slot X)) : SAtom S X :=
  match n.querySpelling? with
  | some y => .var y
  | none => .fresh n.spelling (names.idxOf n + 1)

/-- A naming never prints a symbol. -/
theorem bagNaming_ne_sym (names : List (Nm (Slot X))) (n : Nm (Slot X)) (s : S) :
    bagNaming names n ≠ .sym s := by
  unfold bagNaming
  split <;> simp

/-- The names a naming must keep apart: the query's slots and the listed
allocated names. -/
def Named (names : List (Nm (Slot X))) (n : Nm (Slot X)) : Prop :=
  n.querySpelling?.isSome ∨ n ∈ names

/-- **The naming of a bag is injective** on the query's slots and the listed
names: a named name shares its printed atom with no other name. -/
theorem bagNaming_injOn (names : List (Nm (Slot X))) {n m : Nm (Slot X)}
    (hn : Named names n) (h : (bagNaming names n : SAtom S X) = bagNaming names m) :
    n = m := by
  unfold bagNaming at h
  cases hqn : n.querySpelling? with
  | some y =>
      cases hqm : m.querySpelling? with
      | some y' =>
          rw [hqn, hqm] at h
          simp only [SAtom.var.injEq] at h
          subst h
          rw [Nm.querySpelling?_eq_some.1 hqn, Nm.querySpelling?_eq_some.1 hqm]
      | none =>
          rw [hqn, hqm] at h
          simp at h
  | none =>
      cases hqm : m.querySpelling? with
      | some y' =>
          rw [hqn, hqm] at h
          simp at h
      | none =>
          rw [hqn, hqm] at h
          simp only [SAtom.fresh.injEq, Nat.add_right_cancel_iff] at h
          have hn' : n ∈ names := by
            rcases hn with hn | hn
            · rw [hqn] at hn
              simp at hn
            · exact hn
          exact (List.idxOf_inj hn').1 h.2

/-- Every store name of a bag's answers is named. -/
theorem named_of_mem (bag : List (Tm S (Slot X))) {t : Tm S (Slot X)} (ht : t ∈ bag)
    {n : Nm (Slot X)} (hn : n ∈ t.vars) : Named (allocated bag) n := by
  unfold Named allocated
  cases hq : n.querySpelling? with
  | some y => exact Or.inl (by simp)
  | none =>
      refine Or.inr (List.mem_eraseDups.2 (List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨t, ht, hn⟩, ?_⟩))
      simp [hq]

/-- **Printing a bag is faithful.**  If an answer of a bag is first-order, then
every first-order term that prints like it, under the bag's naming, is that
answer. -/
theorem printAns_bag_faithful (π : Nm (Slot X) → SAtom S X) (bag : List (Tm S (Slot X)))
    {t : Tm S (Slot X)} (ht : t ∈ bag) (hto : t.FirstOrder = true) {t' : Tm S (Slot X)}
    (ht'o : t'.FirstOrder = true)
    (h : printAns (bagNaming (allocated bag)) π t' = printAns (bagNaming (allocated bag)) π t) :
    t' = t :=
  printAns_injective (bagNaming_ne_sym _) t' t ht'o hto
    (fun _ _ _ hm hnm => (bagNaming_injOn _ (named_of_mem bag ht hm) hnm.symm).symm) h

end Naming

/-! ## The canonical form of elaborated terms

The surface printers show authored text and answers; inferred own lists and
slot identities are metadata and do not appear there.  The canonical form is
lossless: every constructor, every name with its identity (activation copies
included), and every lambda's own list, so that printing and reading back is
the identity on elaborated terms (`readCanon_printCanon`).  Substitution, and
with it activation and the evaluator's `let`, never drops or alters the
parameter and own list of a lambda of the term (`lamMeta_subst_sublist`). -/

/-- Constructor tags of the canonical form. -/
inductive CTag where
  | fn | var | pvar | lam | app | quote | ctx | pquote | letP | alt
  deriving DecidableEq, Repr

/-- Atoms of the canonical form: tags, symbols, names with their identity, and
the entries of own lists. -/
inductive CAtom (S : Type u) (Y : Type v) where
  | tag (t : CTag)
  | sym (s : S)
  | name (n : Nm Y)
  | own (y : Y)
  deriving DecidableEq, Repr

section Canonical

variable {Y : Type v}

/-- **The canonical printer**: lossless on every term. -/
def printCanon : Tm S Y → SExp (CAtom S Y)
  | .sym s => .atom (.sym s)
  | .fn F => .list [.atom (.tag .fn), .atom (.sym F)]
  | .var n => .list [.atom (.tag .var), .atom (.name n)]
  | .pvar n => .list [.atom (.tag .pvar), .atom (.name n)]
  | .lam x own b =>
      .list [.atom (.tag .lam), .atom (.name x), .list (own.map fun y => .atom (.own y)),
        printCanon b]
  | .app f a => .list [.atom (.tag .app), printCanon f, printCanon a]
  | .quote c => .list [.atom (.tag .quote), printCanon c]
  | .ctx ks c =>
      .list [.atom (.tag .ctx), .list (ks.map fun k => .atom (.name k)), printCanon c]
  | .pquote c => .list [.atom (.tag .pquote), printCanon c]
  | .letP p w b => .list [.atom (.tag .letP), printCanon p, printCanon w, printCanon b]
  | .alt t₁ t₂ => .list [.atom (.tag .alt), printCanon t₁, printCanon t₂]

/-- Read an own list back. -/
def readOwn : List (SExp (CAtom S Y)) → Option (List Y)
  | [] => some []
  | .atom (.own y) :: rest => (readOwn rest).map (y :: ·)
  | _ => none

/-- Read a contextual-code binder list back. -/
def readCNames : List (SExp (CAtom S Y)) → Option (List (Nm Y))
  | [] => some []
  | .atom (.name n) :: rest => (readCNames rest).map (n :: ·)
  | _ => none

/-- **The canonical reader.** -/
def readCanon : SExp (CAtom S Y) → Option (Tm S Y)
  | .atom (.sym s) => some (.sym s)
  | .list [.atom (.tag .fn), .atom (.sym F)] => some (.fn F)
  | .list [.atom (.tag .var), .atom (.name n)] => some (.var n)
  | .list [.atom (.tag .pvar), .atom (.name n)] => some (.pvar n)
  | .list [.atom (.tag .lam), .atom (.name x), .list own, b] =>
      match readOwn own, readCanon b with
      | some own', some b' => some (.lam x own' b')
      | _, _ => none
  | .list [.atom (.tag .app), f, a] =>
      match readCanon f, readCanon a with
      | some f', some a' => some (.app f' a')
      | _, _ => none
  | .list [.atom (.tag .quote), c] => (readCanon c).map .quote
  | .list [.atom (.tag .ctx), .list ks, c] =>
      match readCNames ks, readCanon c with
      | some ks', some c' => some (.ctx ks' c')
      | _, _ => none
  | .list [.atom (.tag .pquote), c] => (readCanon c).map .pquote
  | .list [.atom (.tag .letP), p, w, b] =>
      match readCanon p, readCanon w, readCanon b with
      | some p', some w', some b' => some (.letP p' w' b')
      | _, _, _ => none
  | .list [.atom (.tag .alt), t₁, t₂] =>
      match readCanon t₁, readCanon t₂ with
      | some a, some b => some (.alt a b)
      | _, _ => none
  | _ => none

theorem readOwn_map (own : List Y) :
    readOwn (own.map fun y => (.atom (.own y) : SExp (CAtom S Y))) = some own := by
  induction own with
  | nil => rfl
  | cons y ys ih => simp [readOwn, ih]

theorem readCNames_map (ks : List (Nm Y)) :
    readCNames (ks.map fun k => (.atom (.name k) : SExp (CAtom S Y))) = some ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [readCNames, ih]

/-- **The canonical form is lossless**: reading back the canonical print of
any term gives the term, own lists and name identities included. -/
theorem readCanon_printCanon : ∀ t : Tm S Y, readCanon (printCanon t) = some t
  | .sym _ => rfl
  | .fn _ => rfl
  | .var _ => rfl
  | .pvar _ => rfl
  | .lam x own b => by simp [printCanon, readCanon, readOwn_map, readCanon_printCanon b]
  | .app f a => by simp [printCanon, readCanon, readCanon_printCanon f, readCanon_printCanon a]
  | .quote c => by simp [printCanon, readCanon, readCanon_printCanon c]
  | .ctx ks c => by simp [printCanon, readCanon, readCNames_map, readCanon_printCanon c]
  | .pquote c => by simp [printCanon, readCanon, readCanon_printCanon c]
  | .letP p w b => by
      simp [printCanon, readCanon, readCanon_printCanon p, readCanon_printCanon w,
        readCanon_printCanon b]
  | .alt t₁ t₂ => by simp [printCanon, readCanon, readCanon_printCanon t₁, readCanon_printCanon t₂]

/-- The canonical form determines the term. -/
theorem printCanon_injective {t t' : Tm S Y} (h : printCanon t = printCanon t') : t = t' := by
  have := readCanon_printCanon t
  rw [h, readCanon_printCanon t'] at this
  exact (Option.some.inj this).symm

/-- The parameters and own lists of the lambdas of a term, outside sealed
quotations, in order. -/
def lamMeta : Tm S Y → List (Nm Y × List Y)
  | .lam x own b => (x, own) :: lamMeta b
  | .app f a => lamMeta f ++ lamMeta a
  | .pquote c => lamMeta c
  | .letP p w b => lamMeta p ++ lamMeta w ++ lamMeta b
  | .alt t₁ t₂ => lamMeta t₁ ++ lamMeta t₂
  | _ => []

variable [DecidableEq Y]

/-- **Substitution keeps the metadata**: the parameters and own lists of a
term's lambdas occur, in order and unchanged, among those of every
substitution instance (activation and the evaluator's `let` are
substitutions; inserted values only add lambdas). -/
theorem lamMeta_subst_sublist : ∀ (t : Tm S Y) (θ φ : Sub S Y),
    (lamMeta t).Sublist (lamMeta (subst θ φ t))
  | .sym _, _, _ => List.nil_sublist _
  | .fn _, _, _ => List.nil_sublist _
  | .var _, _, _ => List.nil_sublist _
  | .pvar _, _, _ => List.nil_sublist _
  | .lam x own b, θ, φ => by
      simp only [lamMeta, subst]
      exact (lamMeta_subst_sublist b _ _).cons_cons _
  | .app f a, θ, φ => by
      simp only [lamMeta, subst]
      exact (lamMeta_subst_sublist f θ φ).append (lamMeta_subst_sublist a θ φ)
  | .quote _, _, _ => List.nil_sublist _
  | .ctx _ _, _, _ => List.nil_sublist _
  | .pquote c, θ, φ => by
      simp only [lamMeta, subst]
      exact lamMeta_subst_sublist c θ φ
  | .letP p w b, θ, φ => by
      simp only [lamMeta, subst]
      exact ((lamMeta_subst_sublist p θ φ).append (lamMeta_subst_sublist w θ φ)).append
        (lamMeta_subst_sublist b θ φ)
  | .alt t₁ t₂, θ, φ => by
      simp only [lamMeta, subst]
      exact (lamMeta_subst_sublist t₁ θ φ).append (lamMeta_subst_sublist t₂ θ φ)

end Canonical

end Mettapedia.GSLT.LanguageDef.TemplateScope
