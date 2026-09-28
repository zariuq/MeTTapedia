import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Canonical terms of a lowered grammar, with tokens and lists

The canonical-term reader works on a grammar after its EBNF lowering: a list
of productions whose right-hand-side symbols are rules, tokens (terminals
carrying a lexeme of their token class) and fixed terminals.  The lowering
adds helper rules for repetitions, options and groups.  A derivation tree
names the production at each node and ends in token leaves.

Every production is classified once, as the implementation does: a
production of exactly one rule or token is *transparent* and denotes its
child; one made only of fixed terminals is *literal* and denotes their text;
a repetition, an option or a separated-list rule makes a *list*; every other
production is a *constructor*.  A token denotes the node of its class over
its lexeme.  A child's value reaches its parent by an action: as one
*argument*, *spliced* into the parent's list (the recursion of a list), or
*extending* the previous argument into one list (`x (sep x)*`).  A list is
named by its key where it is delivered as an argument.

`canon` is the builder as a function of the tree.  `Prints` writes a
canonical term at a symbol as the printer does: through transparent
productions to the production that accepts the term's head, then that
production's terminals around its printed arguments, a list's elements with
the terminals of its position, and a token's lexeme.

For a classification given concretely, both invariants the theorems assume,
well-formedness and settledness, are established by finite checks: a check
that passes proves its invariant.  The checks are sound; they are not shown
to accept every classification that has the invariant.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalGrammar

/-! ## Grammars and derivations -/

/-- A right-hand-side symbol: a rule, a token class, or a fixed terminal by
its text. -/
inductive Sym where
  | rule (name : String)
  | token (name : String)
  | fixed (text : String)
  deriving DecidableEq, Repr

/-- A rule or a token: a symbol with a value. -/
def Sym.isValue : Sym → Bool
  | .fixed _ => false
  | _ => true

/-- A production of the lowered grammar. -/
structure Production where
  label : String
  lhs : String
  rhs : List Sym
  deriving DecidableEq, Repr

/-- A grammar: its productions and the lexemes of each token class. -/
structure Grammar where
  productions : List Production
  lexeme : String → String → Prop

/-- A token of the input: a lexeme of a token class, or a fixed text. -/
inductive Tok where
  | lexeme (cls text : String)
  | fixed (text : String)
  deriving DecidableEq, Repr

/-- A derivation tree: a node names its production, a leaf is a token. -/
inductive Tree where
  | node (label : String) (kids : List Tree)
  | leaf (cls text : String)
  deriving Repr

mutual

/-- `toks` derives at the rule `sort` with tree `tree`. -/
inductive Derives (G : Grammar) : String → List Tok → Tree → Prop where
  | node (p : Production) (hp : p ∈ G.productions) (toks : List Tok) (kids : List Tree)
      (h : DerivesItems G p.rhs toks kids) :
      Derives G p.lhs toks (.node p.label kids)

/-- The symbols of a right-hand side derive `toks` with one tree per rule or
token, in order. -/
inductive DerivesItems (G : Grammar) : List Sym → List Tok → List Tree → Prop where
  | nil : DerivesItems G [] [] []
  | fixed (text : String) (rest : List Sym) (toks : List Tok) (kids : List Tree)
      (h : DerivesItems G rest toks kids) :
      DerivesItems G (.fixed text :: rest) (.fixed text :: toks) kids
  | token (cls s : String) (hs : G.lexeme cls s) (rest : List Sym) (toks : List Tok)
      (kids : List Tree) (h : DerivesItems G rest toks kids) :
      DerivesItems G (.token cls :: rest) (.lexeme cls s :: toks) (.leaf cls s :: kids)
  | rule (n : String) (sub : List Tok) (t : Tree) (hsub : Derives G n sub t)
      (rest : List Sym) (toks : List Tok) (kids : List Tree)
      (h : DerivesItems G rest toks kids) :
      DerivesItems G (.rule n :: rest) (sub ++ toks) (t :: kids)

end

/-- The production a label names: the first production with that label. -/
def Grammar.production? (G : Grammar) (label : String) : Option Production :=
  G.productions.find? (fun p => p.label == label)

/-! ## Canonical terms and the classification -/

/-- A canonical term: a node (a constructor over its arguments, a token over
its lexeme, or a list node over its list), a literal text, or the list
inside a list node. -/
inductive CanonicalTerm where
  | node (name : String) (children : List CanonicalTerm)
  | text (spelling : String)
  | seq (elements : List CanonicalTerm)
  deriving Repr

/-- What a production denotes.  A list production carries the key that names
its list and, when its body has no child, the text each occurrence lists,
before (`false`) or after (`true`) the elements of its recursion. -/
inductive Kind where
  | transparent
  | literal (text : String)
  | constructor (name : String)
  | list (key : String) (text : Option (Bool × String))
  deriving DecidableEq, Repr

/-- How a child's value reaches its parent. -/
inductive Action where
  | arg
  | splice
  | extend
  deriving DecidableEq, Repr

/-- A classification of the productions: each production's kind and the
action at each of its value positions. -/
structure Classification where
  kind : Production → Kind
  action : Production → Nat → Action

/-- The key of a list production. -/
def Kind.key? : Kind → Option String
  | .list key _ => some key
  | _ => none

/-! ## The builder -/

/-- A value delivered as an argument: a list is named by the key of the
production that made it. -/
def named (key? : Option String) (v : CanonicalTerm) : CanonicalTerm :=
  match key? with
  | some key => .node key [v]
  | none => v

/-- Deliver a child's value, made by a production with list key `key?`, by
action `a` to the values delivered so far.  A splice needs a list; an
extension turns the previous value and a list into one list node; anything
else is an argument. -/
def deliver (key? : Option String) (a : Action) (vals : List CanonicalTerm)
    (v : CanonicalTerm) : Option (List CanonicalTerm) :=
  match a, v with
  | .splice, .seq es => some (vals ++ es)
  | .splice, _ => none
  | .extend, .seq es =>
    match vals.getLast?, key? with
    | some h, some key => some (vals.dropLast ++ [.node key [.seq (h :: es)]])
    | some _, none => none
    | none, _ => some (vals ++ [named key? v])
  | _, _ => some (vals ++ [named key? v])

/-- The value a production finishes to from its delivered values. -/
def finish : Kind → List CanonicalTerm → Option CanonicalTerm
  | .transparent, [v] => some v
  | .transparent, _ => none
  | .literal s, _ => some (.text s)
  | .constructor name, vals => some (.node name vals)
  | .list _ none, vals => some (.seq vals)
  | .list _ (some (false, s)), vals => some (.seq (.text s :: vals))
  | .list _ (some (true, s)), vals => some (.seq (vals ++ [.text s]))

mutual

/-- The value the builder finishes a tree to, a list bare, with the list key
of the tree's production. -/
def finishTree (G : Grammar) (C : Classification) :
    Tree → Option (CanonicalTerm × Option String)
  | .leaf cls s => some (.node cls [.text s], none)
  | .node label kids =>
    match G.production? label with
    | none => none
    | some p =>
      match deliverKids G C p 0 [] kids with
      | none => none
      | some vals => (finish (C.kind p) vals).map (fun v => (v, (C.kind p).key?))

/-- The values of a production's children, delivered from its value
position `i` on. -/
def deliverKids (G : Grammar) (C : Classification) (p : Production) :
    Nat → List CanonicalTerm → List Tree → Option (List CanonicalTerm)
  | _, vals, [] => some vals
  | i, vals, t :: ts =>
    match finishTree G C t with
    | none => none
    | some (v, key?) =>
      match deliver key? (C.action p i) vals v with
      | none => none
      | some vals' => deliverKids G C p (i + 1) vals' ts

end

/-- The canonical term of a tree: its value as an argument. -/
def canon (G : Grammar) (C : Classification) (t : Tree) : Option CanonicalTerm :=
  (finishTree G C t).map (fun r => named r.2 r.1)

/-! ## List rules

A list rule is a repetition or option helper of the lowering, or an authored
rule with a separated-list shape.  Its productions are fixed by its form:
`option b` is `H → ε | b`, `star b` is `H → ε | H b`, `plus b` is
`H → b | H b` (repetition helpers are left recursive), and
`separated x sep right` is `R → x | x sep R` when `right`, else
`R → x | R sep x`. -/

inductive ListForm where
  | option (body : Sym)
  | star (body : Sym)
  | plus (body : Sym)
  | separated (item : Sym) (sep : List String) (right : Bool)
  deriving DecidableEq, Repr

/-- The fixed terminals of a separator. -/
def fixedSyms (sep : List String) : List Sym := sep.map Sym.fixed

/-- The input tokens of a separator. -/
def fixedToks (sep : List String) : List Tok := sep.map Tok.fixed

/-- The right-hand sides of a list rule `r` of a form. -/
def ListForm.rhss (r : String) : ListForm → List (List Sym)
  | .option b => [[], [b]]
  | .star b => [[], [.rule r, b]]
  | .plus b => [[b], [.rule r, b]]
  | .separated x sep true => [[x], x :: fixedSyms sep ++ [.rule r]]
  | .separated x sep false => [[x], .rule r :: fixedSyms sep ++ [x]]

/-- The texts of the fixed terminals of a right-hand side, in order. -/
def fixedTexts : List Sym → List String
  | [] => []
  | .fixed t :: rest => t :: fixedTexts rest
  | _ :: rest => fixedTexts rest

/-- The kind and actions a production of a list rule of form `f` and key
`key` has, by its right-hand side: a body with no child lists its text, before
the recursion's elements in `H → t` and after them in `H → H t`; the
recursion is spliced and every other child is an argument. -/
def ListForm.Spec (r key : String) (f : ListForm) (q : Production) (C : Classification) : Prop :=
  match f with
  | .option b | .star b | .plus b =>
    b ≠ .rule r ∧
    (q.rhs = [] → C.kind q = .list key none) ∧
    (q.rhs = [b] →
      (b.isValue = true → C.kind q = .list key none ∧ C.action q 0 = .arg) ∧
      (∀ t, b = .fixed t → C.kind q = .list key (some (false, t)))) ∧
    (q.rhs = [.rule r, b] →
      C.action q 0 = .splice ∧
      (b.isValue = true → C.kind q = .list key none ∧ C.action q 1 = .arg) ∧
      (∀ t, b = .fixed t → C.kind q = .list key (some (true, t))))
  | .separated x _ right =>
    x.isValue = true ∧ x ≠ .rule r ∧ C.kind q = .list key none ∧
    (q.rhs = [x] → C.action q 0 = .arg) ∧
    (q.rhs ≠ [x] →
      if right then C.action q 0 = .arg ∧ C.action q 1 = .splice
      else C.action q 0 = .splice ∧ C.action q 1 = .arg)

/-- The value symbols of a right-hand side, in order. -/
def values (rhs : List Sym) : List Sym := rhs.filter Sym.isValue

/-- An extension position of a constructor: the value symbol at position
`i + 1` immediately follows the one at `i` in the right-hand side, is a
star or plus list rule, and position `i` is not itself an extension. -/
def ExtensionAt (C : Classification) (L : String → Option (ListForm × String))
    (p : Production) (i : Nat) : Prop :=
  ∃ pre x h rest, p.rhs = pre ++ x :: .rule h :: rest ∧ (values pre).length = i ∧
    x.isValue = true ∧ C.action p i ≠ .extend ∧
    ∃ b key, (L h = some (.star b, key) ∨ L h = some (.plus b, key))

/-- A classification of a grammar is well formed when it has the invariants
the implementation's classification establishes. -/
structure WellFormed (G : Grammar) (C : Classification)
    (L : String → Option (ListForm × String)) : Prop where
  /-- Distinct productions have distinct labels. -/
  labels : (G.productions.map Production.label).Nodup
  /-- A transparent production is exactly one rule or token, an argument. -/
  transparent : ∀ p ∈ G.productions, C.kind p = .transparent →
    ∃ v, p.rhs = [v] ∧ v.isValue = true ∧ C.action p 0 = .arg
  /-- A literal production is a nonempty run of fixed terminals. -/
  literal : ∀ p ∈ G.productions, ∀ s, C.kind p = .literal s →
    p.rhs ≠ [] ∧ (∀ x ∈ p.rhs, x.isValue = false) ∧ s = String.join (fixedTexts p.rhs)
  /-- A constructor's children are arguments, or extensions as marked. -/
  constructor : ∀ p ∈ G.productions, ∀ n, C.kind p = .constructor n →
    ∀ i, C.action p i = .arg ∨ (C.action p i = .extend ∧ ∃ j, i = j + 1 ∧ ExtensionAt C L p j)
  /-- A list production belongs to a list rule. -/
  list : ∀ p ∈ G.productions, ∀ key text, C.kind p = .list key text → (L p.lhs).isSome
  /-- A list rule's productions are those of its form, each once, with the
  kind and actions of its form, and nothing else of its left-hand side. -/
  rule : ∀ r f key, L r = some (f, key) →
    (∀ q ∈ G.productions, q.lhs = r → q.rhs ∈ ListForm.rhss r f ∧ f.Spec r key q C) ∧
    (∀ rhs ∈ ListForm.rhss r f, ∃ q ∈ G.productions, q.lhs = r ∧ q.rhs = rhs) ∧
    (∀ q ∈ G.productions, ∀ q' ∈ G.productions, q.lhs = r → q'.lhs = r → q.rhs = q'.rhs →
      q = q')

/-! ## The printer -/

mutual

/-- Printing a term at a symbol: a token position prints a token of its class
by its lexeme, a fixed position its text (the element of a list whose body is
a text), and a rule position through one of the rule's productions. -/
inductive Prints (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    Sym → CanonicalTerm → List Tok → Prop where
  | token (cls s : String) (hs : G.lexeme cls s) :
      Prints G C L (.token cls) (.node cls [.text s]) [.lexeme cls s]
  | fixed (t : String) : Prints G C L (.fixed t) (.text t) [.fixed t]
  | rule (p : Production) (hp : p ∈ G.productions) (c : CanonicalTerm) (toks : List Tok)
      (h : PrintsAt G C L p c toks) : Prints G C L (.rule p.lhs) c toks

/-- A production prints a term whose head it accepts: a transparent production
prints it at its child, a literal production prints its terminals for its
text, a constructor its right-hand side around its arguments, and a list
production a list node of its key by its rule's list form. -/
inductive PrintsAt (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    Production → CanonicalTerm → List Tok → Prop where
  | transparent (p : Production) (hk : C.kind p = .transparent) (v : Sym) (hv : p.rhs = [v])
      (c : CanonicalTerm) (toks : List Tok) (h : Prints G C L v c toks) :
      PrintsAt G C L p c toks
  | literal (p : Production) (s : String) (hk : C.kind p = .literal s) :
      PrintsAt G C L p (.text s) (fixedToks (fixedTexts p.rhs))
  | constructor (p : Production) (n : String) (hk : C.kind p = .constructor n)
      (args : List CanonicalTerm) (toks : List Tok) (h : PrintsRhs G C L p 0 p.rhs args toks) :
      PrintsAt G C L p (.node n args) toks
  | list (p : Production) (key : String) (text : Option (Bool × String))
      (hk : C.kind p = .list key text) (f : ListForm) (hf : L p.lhs = some (f, key))
      (es : List CanonicalTerm) (toks : List Tok) (h : PrintsList G C L f es toks) :
      PrintsAt G C L p (.node key [.seq es]) toks

/-- The right-hand side of a constructor from value position `i` prints its
arguments: fixed terminals by their text, a value by its argument, and an
extended pair by one list node whose first element prints at the first
symbol and whose rest prints as the list rule of the second. -/
inductive PrintsRhs (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    Production → Nat → List Sym → List CanonicalTerm → List Tok → Prop where
  | nil (p : Production) (i : Nat) : PrintsRhs G C L p i [] [] []
  | fixed (p : Production) (i : Nat) (t : String) (rest : List Sym) (args : List CanonicalTerm) (toks : List Tok)
      (h : PrintsRhs G C L p i rest args toks) :
      PrintsRhs G C L p i (.fixed t :: rest) args (.fixed t :: toks)
  | value (p : Production) (i : Nat) (v : Sym) (hv : v.isValue = true) (rest : List Sym)
      (hnext : C.action p (i + 1) ≠ .extend) (a : CanonicalTerm) (sub : List Tok)
      (ha : Prints G C L v a sub) (args : List CanonicalTerm) (toks : List Tok)
      (h : PrintsRhs G C L p (i + 1) rest args toks) :
      PrintsRhs G C L p i (v :: rest) (a :: args) (sub ++ toks)
  | extended (p : Production) (i : Nat) (v : Sym) (hv : v.isValue = true) (hr : String) (rest : List Sym)
      (hext : C.action p (i + 1) = .extend) (f : ListForm) (key : String)
      (hf : L hr = some (f, key)) (e : CanonicalTerm) (tail : List CanonicalTerm)
      (sub₁ sub₂ : List Tok) (he : Prints G C L v e sub₁) (htail : PrintsList G C L f tail sub₂)
      (hnext : C.action p (i + 2) ≠ .extend) (args : List CanonicalTerm) (toks : List Tok)
      (h : PrintsRhs G C L p (i + 2) rest args toks) :
      PrintsRhs G C L p i (v :: .rule hr :: rest) (.node key [.seq (e :: tail)] :: args)
        (sub₁ ++ sub₂ ++ toks)

/-- A list of elements prints by its rule's form, element by element with the
terminals of the form. -/
inductive PrintsList (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    ListForm → List CanonicalTerm → List Tok → Prop where
  | optionNone (b : Sym) : PrintsList G C L (.option b) [] []
  | optionSome (b : Sym) (e : CanonicalTerm) (toks : List Tok) (h : Prints G C L b e toks) :
      PrintsList G C L (.option b) [e] toks
  | starNil (b : Sym) : PrintsList G C L (.star b) [] []
  | starSnoc (b : Sym) (es : List CanonicalTerm) (e : CanonicalTerm) (toks₁ toks₂ : List Tok)
      (hs : PrintsList G C L (.star b) es toks₁) (h : Prints G C L b e toks₂) :
      PrintsList G C L (.star b) (es ++ [e]) (toks₁ ++ toks₂)
  | plusOne (b : Sym) (e : CanonicalTerm) (toks : List Tok) (h : Prints G C L b e toks) :
      PrintsList G C L (.plus b) [e] toks
  | plusSnoc (b : Sym) (es : List CanonicalTerm) (e : CanonicalTerm) (toks₁ toks₂ : List Tok)
      (hs : PrintsList G C L (.plus b) es toks₁) (h : Prints G C L b e toks₂) :
      PrintsList G C L (.plus b) (es ++ [e]) (toks₁ ++ toks₂)
  | sepOne (x : Sym) (sep : List String) (right : Bool) (e : CanonicalTerm) (toks : List Tok)
      (h : Prints G C L x e toks) : PrintsList G C L (.separated x sep right) [e] toks
  | sepCons (x : Sym) (sep : List String) (e : CanonicalTerm) (es : List CanonicalTerm)
      (toks₁ toks₂ : List Tok) (h : Prints G C L x e toks₁)
      (hs : PrintsList G C L (.separated x sep true) es toks₂) :
      PrintsList G C L (.separated x sep true) (e :: es) (toks₁ ++ fixedToks sep ++ toks₂)
  | sepSnoc (x : Sym) (sep : List String) (es : List CanonicalTerm) (e : CanonicalTerm)
      (toks₁ toks₂ : List Tok) (hs : PrintsList G C L (.separated x sep false) es toks₁)
      (h : Prints G C L x e toks₂) :
      PrintsList G C L (.separated x sep false) (es ++ [e]) (toks₁ ++ fixedToks sep ++ toks₂)

end

/-! ## Derivations with facts about their children -/

/-- The items of a derivation with a fact about each rule child's
derivation. -/
inductive ItemsWith (G : Grammar) (P : String → List Tok → Tree → Prop) :
    List Sym → List Tok → List Tree → Prop where
  | nil : ItemsWith G P [] [] []
  | fixed (t : String) (rest : List Sym) (toks : List Tok) (kids : List Tree)
      (h : ItemsWith G P rest toks kids) :
      ItemsWith G P (.fixed t :: rest) (.fixed t :: toks) kids
  | token (cls s : String) (hs : G.lexeme cls s) (rest : List Sym) (toks : List Tok)
      (kids : List Tree) (h : ItemsWith G P rest toks kids) :
      ItemsWith G P (.token cls :: rest) (.lexeme cls s :: toks) (.leaf cls s :: kids)
  | rule (n : String) (sub : List Tok) (t : Tree) (hsub : Derives G n sub t) (hP : P n sub t)
      (rest : List Sym) (toks : List Tok) (kids : List Tree)
      (h : ItemsWith G P rest toks kids) :
      ItemsWith G P (.rule n :: rest) (sub ++ toks) (t :: kids)

/-- Induction on derivations: a fact that holds of a node whenever it holds of
the node's rule children holds of every derivation. -/
theorem Derives.induction_with {G : Grammar} (P : String → List Tok → Tree → Prop)
    (hnode : ∀ p ∈ G.productions, ∀ toks kids, DerivesItems G p.rhs toks kids →
      ItemsWith G P p.rhs toks kids → P p.lhs toks (.node p.label kids)) :
    ∀ {n toks t}, Derives G n toks t → P n toks t := by
  intro n toks t h
  induction h using Derives.rec (motive_2 := fun rhs toks kids _ => ItemsWith G P rhs toks kids) with
  | node p hp toks kids h ih => exact hnode p hp toks kids h ih
  | nil => exact .nil
  | fixed t rest toks kids _ ih => exact .fixed t rest toks kids ih
  | token cls s hs rest toks kids _ ih => exact .token cls s hs rest toks kids ih
  | rule n sub t hsub rest toks kids _ ihsub ih => exact .rule n sub t hsub ihsub rest toks kids ih

/-! ## The builder on derivations -/

section Builder

variable {G : Grammar} {C : Classification} {L : String → Option (ListForm × String)}

/-- String equality tests itself true. -/
theorem string_beq_self (x : String) : (x == x) = true := decide_eq_true rfl

/-- In a well-formed classification a production's label names it. -/
theorem production?_eq (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions) :
    G.production? p.label = some p := by
  unfold Grammar.production?
  have hsome : (G.productions.find? (fun q => q.label == p.label)).isSome :=
    List.find?_isSome.2 ⟨p, hp, string_beq_self _⟩
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hsome
  have hqm : q ∈ G.productions := List.mem_of_find?_eq_some hq
  have hql : q.label = p.label :=
    of_decide_eq_true (List.find?_some (p := fun q : Production => q.label == p.label) hq)
  rw [hq]
  exact congrArg some (List.inj_on_of_nodup_map hwf.labels hqm hp hql)

/-- What a tree at a rule finishes to: at a list rule a bare list with the
rule's key, at any other rule a value that is not a list, with no key. -/
def Finished (L : String → Option (ListForm × String)) (n : String) (v : CanonicalTerm)
    (k? : Option String) : Prop :=
  match L n with
  | some (_, key) => k? = some key ∧ ∃ es, v = .seq es
  | none => k? = none ∧ ∀ es, v ≠ .seq es

/-- The fact a rule child has for the builder: it finishes, as its rule
says. -/
def FinishesAt (G : Grammar) (C : Classification) (L : String → Option (ListForm × String))
    (n : String) (_toks : List Tok) (t : Tree) : Prop :=
  ∃ v k?, finishTree G C t = some (v, k?) ∧ Finished L n v k?

/-- The fact a child has at its symbol: a rule child finishes, a token child
is a leaf of its class. -/
def KidFinishes (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    Sym → Tree → Prop
  | .rule n, t => ∃ v k?, finishTree G C t = some (v, k?) ∧ Finished L n v k?
  | .token cls, t => ∃ s, t = .leaf cls s
  | .fixed _, _ => False

theorem kids_finish {toks : List Tok} :
    ∀ {rhs kids}, ItemsWith G (FinishesAt G C L) rhs toks kids →
      List.Forall₂ (KidFinishes G C L) (values rhs) kids := by
  intro rhs kids h
  induction h with
  | nil => exact .nil
  | fixed _ _ _ _ _ ih => exact ih
  | token cls s _ _ _ _ _ ih => exact .cons ⟨s, rfl⟩ ih
  | rule n _ _ _ hP _ _ _ _ ih => exact .cons hP ih

theorem finishTree_leaf (cls s : String) :
    finishTree G C (.leaf cls s) = some (.node cls [.text s], none) := by
  rw [finishTree]

theorem deliverKids_nil (p : Production) (i : Nat) (vals : List CanonicalTerm) :
    deliverKids G C p i vals [] = some vals := by
  rw [deliverKids]

theorem deliverKids_cons (p : Production) (i : Nat) (vals : List CanonicalTerm) (t : Tree)
    (ts : List Tree) :
    deliverKids G C p i vals (t :: ts) =
      match finishTree G C t with
      | none => none
      | some (v, key?) =>
        match deliver key? (C.action p i) vals v with
        | none => none
        | some vals' => deliverKids G C p (i + 1) vals' ts := by
  rw [deliverKids]

theorem finishTree_node (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions)
    (kids : List Tree) :
    finishTree G C (.node p.label kids) =
      match deliverKids G C p 0 [] kids with
      | none => none
      | some vals => (finish (C.kind p) vals).map (fun v => (v, (C.kind p).key?)) := by
  rw [finishTree, production?_eq hwf hp]

/-- A delivery succeeds unless a splice meets a value that is not a list, or
an extension a list with no key. -/
theorem deliver_isSome {key? : Option String} {a : Action} {vals : List CanonicalTerm}
    {v : CanonicalTerm} (hs : a = .splice → ∃ es, v = .seq es)
    (hk : (∃ es, v = .seq es) → key?.isSome) : (deliver key? a vals v).isSome := by
  unfold deliver
  split
  · rfl
  · rename_i hv
    obtain ⟨es, rfl⟩ := hs rfl
    exact absurd rfl (hv es)
  · split
    · rfl
    · exact hk ⟨_, rfl⟩
    · rfl
  · rfl

theorem kid_finishTree {sym : Sym} {t : Tree} (h : KidFinishes G C L sym t) :
    ∃ v k?, finishTree G C t = some (v, k?) ∧
      ((∃ es, v = .seq es) → ∃ n, sym = .rule n ∧ (L n).isSome ∧ k?.isSome) := by
  cases sym with
  | rule n =>
    obtain ⟨v, k?, hv, hfin⟩ := h
    refine ⟨v, k?, hv, fun hseq => ⟨n, rfl, ?_⟩⟩
    unfold Finished at hfin
    split at hfin
    · rename_i hL
      rw [hL, hfin.1]
      exact ⟨rfl, rfl⟩
    · obtain ⟨es, rfl⟩ := hseq
      exact absurd rfl (hfin.2 es)
  | token cls =>
    obtain ⟨s, rfl⟩ := h
    refine ⟨_, _, finishTree_leaf cls s, fun ⟨es, hes⟩ => ?_⟩
    cases hes
  | fixed _ => exact h.elim

/-- The builder delivers every child of a derivation whose splices take list
rules. -/
theorem deliverKids_some (p : Production) :
    ∀ (syms : List Sym) (kids : List Tree) (i : Nat) (vals : List CanonicalTerm),
      List.Forall₂ (KidFinishes G C L) syms kids →
      (∀ j sym, syms[j]? = some sym → C.action p (i + j) = .splice →
        ∃ n, sym = .rule n ∧ (L n).isSome) →
      (deliverKids G C p i vals kids).isSome := by
  intro syms kids i vals h
  induction h generalizing i vals with
  | nil => intro _; rw [deliverKids_nil]; rfl
  | @cons sym t syms' ts hkid _ ih =>
    intro hsp
    obtain ⟨v, k?, hv, hseq⟩ := kid_finishTree hkid
    rw [deliverKids_cons, hv]
    simp only []
    have hd : (deliver k? (C.action p i) vals v).isSome := by
      refine deliver_isSome (fun ha => ?_) (fun hs => ?_)
      · obtain ⟨n, rfl, hLn⟩ := hsp 0 sym rfl (by simpa using ha)
        obtain ⟨w, k?', hw, hfin⟩ := hkid
        rw [hv] at hw
        injection hw with hw
        injection hw with hw₁ hw₂
        subst hw₁
        subst hw₂
        unfold Finished at hfin
        split at hfin
        · exact hfin.2
        · rename_i hnone
          rw [hnone] at hLn
          cases hLn
      · obtain ⟨_, _, _, hk⟩ := hseq hs
        exact hk
    obtain ⟨vals', hvals'⟩ := Option.isSome_iff_exists.1 hd
    rw [hvals']
    simp only []
    exact ih (i + 1) vals' (fun j sym' hj ha => hsp (j + 1) sym' (by simpa using hj)
      (by rw [show i + (j + 1) = i + 1 + j by omega]; exact ha))

theorem values_fixedSyms (sep : List String) : values (fixedSyms sep) = [] := by
  induction sep with
  | nil => rfl
  | cons t sep ih =>
    show List.filter Sym.isValue (Sym.fixed t :: fixedSyms sep) = []
    rw [List.filter_cons_of_neg (by simp [Sym.isValue])]
    exact ih

theorem values_append (a b : List Sym) : values (a ++ b) = values a ++ values b :=
  List.filter_append a b

theorem values_value {x : Sym} (hx : x.isValue = true) (rest : List Sym) :
    values (x :: rest) = x :: values rest :=
  List.filter_cons_of_pos hx

theorem values_fixed (t : String) (rest : List Sym) :
    values (.fixed t :: rest) = values rest :=
  List.filter_cons_of_neg (by simp [Sym.isValue])

theorem values_nil : values [] = [] := rfl

/-- Every production of a list rule makes a list of the rule's key. -/
theorem rule_kind_list (hwf : WellFormed G C L) {r : String} {f : ListForm} {key : String}
    (hL : L r = some (f, key)) {q : Production} (hq : q ∈ G.productions) (hlhs : q.lhs = r) :
    ∃ text, C.kind q = .list key text := by
  obtain ⟨hrhs, hspec⟩ := (hwf.rule r f key hL).1 q hq hlhs
  cases f with
  | option b | star b | plus b =>
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, h0, h1, h2⟩ := hspec
    simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
    rcases hrhs with h | h
    all_goals first
      | exact ⟨none, h0 h⟩
      | (cases hb : b.isValue
         · cases b with
           | fixed t =>
             first
               | exact ⟨_, (h1 h).2 t rfl⟩
               | exact ⟨_, (h2 h).2.2 t rfl⟩
           | _ => simp [Sym.isValue] at hb
         · first
             | exact ⟨none, ((h1 h).1 hb).1⟩
             | exact ⟨none, ((h2 h).2.1 hb).1⟩)
  | separated x sep right =>
    simp only [ListForm.Spec] at hspec
    exact ⟨none, hspec.2.2.1⟩

/-- A production that makes no list belongs to no list rule. -/
theorem not_list_rule (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions)
    (hk : ∀ key text, C.kind p ≠ .list key text) : L p.lhs = none := by
  cases hL : L p.lhs with
  | none => rfl
  | some fk =>
    obtain ⟨f, key⟩ := fk
    obtain ⟨text, htext⟩ := rule_kind_list hwf hL hp rfl
    exact absurd htext (hk key text)

theorem values_all_fixed : ∀ {rhs : List Sym}, (∀ x ∈ rhs, x.isValue = false) →
    values rhs = []
  | [], _ => rfl
  | x :: rest, h => by
    have e : values (x :: rest) = values rest :=
      List.filter_cons_of_neg (by simp [h x List.mem_cons_self])
    rw [e]
    exact values_all_fixed (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A splice takes a child of a list rule. -/
theorem splice_ok (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions) :
    ∀ j sym, (values p.rhs)[j]? = some sym → C.action p j = .splice →
      ∃ n, sym = .rule n ∧ (L n).isSome := by
  intro j sym hj ha
  cases hkind : C.kind p with
  | transparent =>
    obtain ⟨v, hrhs, hvv, ha0⟩ := hwf.transparent p hp hkind
    rw [hrhs, values_value hvv, values_nil] at hj
    rcases j with _ | j
    · rw [ha0] at ha
      cases ha
    · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
      cases hj
  | literal s =>
    obtain ⟨_, hall, _⟩ := hwf.literal p hp s hkind
    rw [values_all_fixed hall] at hj
    simp only [List.getElem?_nil] at hj
    cases hj
  | constructor n =>
    rcases hwf.constructor p hp n hkind j with h | ⟨h, _⟩ <;> rw [h] at ha <;> cases ha
  | list key text =>
    obtain ⟨fk, hfk⟩ := Option.isSome_iff_exists.1 (hwf.list p hp key text hkind)
    obtain ⟨f, key'⟩ := fk
    obtain ⟨hrhs, hspec⟩ := (hwf.rule p.lhs f key' hfk).1 p hp rfl
    have hLr : (L p.lhs).isSome := by rw [hfk]; rfl
    cases f with
    | option b | star b | plus b =>
      obtain ⟨_, _, h1, h2⟩ := hspec
      simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
      rcases hrhs with h | h
      all_goals rw [h] at hj
      all_goals first
        | (simp only [values_nil, List.getElem?_nil] at hj; cases hj)
        | (cases hb : b.isValue
           · cases b with
             | fixed t =>
               first
                 | (rw [values_fixed, values_nil] at hj
                    simp only [List.getElem?_nil] at hj
                    cases hj)
                 | (rw [values_value (by rfl), values_fixed, values_nil] at hj
                    rcases j with _ | j
                    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                      exact ⟨_, hj.symm, hLr⟩
                    · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
                      cases hj)
             | _ => simp [Sym.isValue] at hb
           · first
               | (rw [values_value hb, values_nil] at hj
                  rcases j with _ | j
                  · rw [((h1 h).1 hb).2] at ha
                    cases ha
                  · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
                    cases hj)
               | (rw [values_value (by rfl), values_value hb, values_nil] at hj
                  rcases j with _ | _ | j
                  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
                    exact ⟨_, hj.symm, hLr⟩
                  · rw [((h2 h).2.1 hb).2] at ha
                    cases ha
                  · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
                    cases hj))
    | separated x sep right =>
      obtain ⟨hx, _, _, h1, h2⟩ := hspec
      cases right with
      | true =>
        simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
        rcases hrhs with h | h
        · rw [h, values_value hx, values_nil] at hj
          rcases j with _ | j
          · rw [h1 h] at ha
            cases ha
          · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
            cases hj
        · have hne : p.rhs ≠ [x] := by rw [h]; simp
          have hacts := h2 hne
          simp only [if_true] at hacts
          rw [h, values_append, values_value hx, values_fixedSyms,
            values_value (x := .rule p.lhs) rfl, values_nil] at hj
          simp only [List.cons_append, List.nil_append] at hj
          rcases j with _ | _ | j
          · rw [hacts.1] at ha
            cases ha
          · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hj
            exact ⟨_, hj.symm, hLr⟩
          · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
            cases hj
      | false =>
        simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
        rcases hrhs with h | h
        · rw [h, values_value hx, values_nil] at hj
          rcases j with _ | j
          · rw [h1 h] at ha
            cases ha
          · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
            cases hj
        · have hne : p.rhs ≠ [x] := by rw [h]; simp
          have hacts := h2 hne
          simp only [Bool.false_eq_true, if_false] at hacts
          rw [h, values_append, values_value (x := .rule p.lhs) rfl, values_fixedSyms,
            values_value hx, values_nil] at hj
          simp only [List.cons_append, List.nil_append] at hj
          rcases j with _ | _ | j
          · simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
            exact ⟨_, hj.symm, hLr⟩
          · rw [hacts.2] at ha
            cases ha
          · simp only [List.getElem?_cons_succ, List.getElem?_nil] at hj
            cases hj

theorem deliver_arg (key? : Option String) (vals : List CanonicalTerm) (v : CanonicalTerm) :
    deliver key? .arg vals v = some (vals ++ [named key? v]) := by
  cases v <;> rfl

/-- Every derivation's tree finishes, as its rule says. -/
theorem finishes (hwf : WellFormed G C L) :
    ∀ {n toks t}, Derives G n toks t → FinishesAt G C L n toks t := by
  refine Derives.induction_with (FinishesAt G C L) ?_
  intro p hp toks kids _ hw
  have hk := kids_finish hw
  have hd := deliverKids_some p (values p.rhs) kids 0 [] hk
    (fun j sym hj ha => splice_ok hwf hp j sym hj (by rw [Nat.zero_add] at ha; exact ha))
  obtain ⟨vals, hvals⟩ := Option.isSome_iff_exists.1 hd
  unfold FinishesAt
  rw [finishTree_node hwf hp, hvals]
  simp only []
  cases hkind : C.kind p with
  | transparent =>
    obtain ⟨v, hrhs, hvv, ha0⟩ := hwf.transparent p hp hkind
    rw [hrhs, values_value hvv, values_nil] at hk
    obtain ⟨t, rfl, hkid⟩ : ∃ t, kids = [t] ∧ KidFinishes G C L v t := by
      cases hk with
      | cons hkid hnil =>
        cases hnil
        exact ⟨_, rfl, hkid⟩
    obtain ⟨w, k?, hw', hseq⟩ := kid_finishTree hkid
    rw [deliverKids_cons, hw'] at hvals
    simp only [] at hvals
    rw [ha0, deliver_arg] at hvals
    simp only [] at hvals
    rw [deliverKids_nil] at hvals
    injection hvals with hvals
    subst hvals
    refine ⟨named k? w, none, rfl, ?_⟩
    unfold Finished
    rw [not_list_rule hwf hp (fun key text h => by rw [hkind] at h; cases h)]
    refine ⟨rfl, fun es hes => ?_⟩
    cases k? with
    | some key => cases hes
    | none =>
      obtain ⟨_, _, _, hsome⟩ := hseq ⟨es, hes⟩
      cases hsome
  | literal s =>
    refine ⟨.text s, none, rfl, ?_⟩
    unfold Finished
    rw [not_list_rule hwf hp (fun key text h => by rw [hkind] at h; cases h)]
    exact ⟨rfl, fun es hes => by cases hes⟩
  | constructor n =>
    refine ⟨.node n vals, none, rfl, ?_⟩
    unfold Finished
    rw [not_list_rule hwf hp (fun key text h => by rw [hkind] at h; cases h)]
    exact ⟨rfl, fun es hes => by cases hes⟩
  | list key text =>
    obtain ⟨fk, hfk⟩ := Option.isSome_iff_exists.1 (hwf.list p hp key text hkind)
    obtain ⟨f, key'⟩ := fk
    obtain ⟨text', htext'⟩ := rule_kind_list hwf hfk hp rfl
    rw [hkind] at htext'
    injection htext' with hkey _
    subst hkey
    have hL : L p.lhs = some (f, key) := hfk
    rcases text with _ | ⟨_ | _, t⟩
    all_goals
      refine ⟨_, some key, rfl, ?_⟩
      unfold Finished
      rw [hL]
      exact ⟨rfl, _, rfl⟩

/-- The projection is total on derivations. -/
theorem canon_exists (hwf : WellFormed G C L) {n : String} {toks : List Tok} {t : Tree}
    (h : Derives G n toks t) : ∃ c, canon G C t = some c := by
  obtain ⟨v, k?, hv, _⟩ := finishes hwf h
  exact ⟨named k? v, by simp only [canon, hv, Option.map_some]⟩

end Builder

/-! ## Printing the projection of a derivation recovers its tokens -/

section PrintsCanon

variable {G : Grammar} {C : Classification} {L : String → Option (ListForm × String)}

/-- What printing does with a rule child's derivation: its term prints its
tokens, and at a list rule its list prints them by the rule's form. -/
def PrintsFact (G : Grammar) (C : Classification) (L : String → Option (ListForm × String))
    (n : String) (toks : List Tok) (t : Tree) : Prop :=
  (∀ v k?, finishTree G C t = some (v, k?) → Prints G C L (.rule n) (named k? v) toks) ∧
  (∀ f key es, L n = some (f, key) → finishTree G C t = some (.seq es, some key) →
    PrintsList G C L f es toks)

/-- Two splits of one right-hand side at value symbols after the same number
of value symbols are one split. -/
theorem split_unique : ∀ (pre pre' : List Sym) {v x : Sym} {rest rest' : List Sym},
    v.isValue = true → x.isValue = true → pre ++ v :: rest = pre' ++ x :: rest' →
    (values pre).length = (values pre').length → pre = pre' ∧ v = x ∧ rest = rest'
  | [], [], _, _, _, _, _, _, h, _ => by
    simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1, h.2⟩
  | [], y :: pre', _, _, _, _, hv, _, h, hlen => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rw [values_value hv] at hlen
    simp only [values_nil, List.length_nil, List.length_cons] at hlen
    omega
  | y :: pre, [], _, _, _, _, _, hx, h, hlen => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rw [values_value hx] at hlen
    simp only [values_nil, List.length_nil, List.length_cons] at hlen
    omega
  | y :: pre, y' :: pre', _, _, _, _, hv, hx, h, hlen => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have hlen' : (values pre).length = (values pre').length := by
      cases hy : y.isValue
      · have e1 : values (y :: pre) = values pre := List.filter_cons_of_neg (by simp [hy])
        have e2 : values (y :: pre') = values pre' := List.filter_cons_of_neg (by simp [hy])
        rw [e1, e2] at hlen
        exact hlen
      · rw [values_value hy, values_value hy] at hlen
        simp only [List.length_cons] at hlen
        omega
    obtain ⟨h1, h2, h3⟩ := split_unique pre pre' hv hx h hlen'
    exact ⟨by rw [h1], h2, h3⟩

/-- The first rule or token of a right-hand side derives its child. -/
theorem items_head {P : String → List Tok → Tree → Prop} {v : Sym} (hv : v.isValue = true)
    {rest : List Sym} {toks : List Tok} {kids : List Tree}
    (h : ItemsWith G P (v :: rest) toks kids) :
    ∃ t kids' sub toks', kids = t :: kids' ∧ toks = sub ++ toks' ∧
      ItemsWith G P rest toks' kids' ∧
      ((∃ n, v = .rule n ∧ Derives G n sub t ∧ P n sub t) ∨
       (∃ cls s, v = .token cls ∧ t = .leaf cls s ∧ sub = [.lexeme cls s] ∧ G.lexeme cls s)) := by
  cases h with
  | fixed t _ _ _ _ => simp [Sym.isValue] at hv
  | token cls s hs _ toks' kids' h' =>
    exact ⟨_, kids', [.lexeme cls s], toks', rfl, rfl, h', .inr ⟨cls, s, rfl, rfl, rfl, hs⟩⟩
  | rule n sub t hsub hP _ toks' kids' h' =>
    exact ⟨t, kids', sub, toks', rfl, rfl, h', .inl ⟨n, rfl, hsub, hP⟩⟩

/-- A value child prints its delivered term at its symbol. -/
theorem kid_prints (hwf : WellFormed G C L) {v : Sym} {t : Tree} {sub : List Tok}
    (h : (∃ n, v = .rule n ∧ Derives G n sub t ∧ PrintsFact G C L n sub t) ∨
       (∃ cls s, v = .token cls ∧ t = .leaf cls s ∧ sub = [.lexeme cls s] ∧ G.lexeme cls s)) :
    ∃ w k?, finishTree G C t = some (w, k?) ∧ Prints G C L v (named k? w) sub := by
  rcases h with ⟨n, rfl, hd, hP⟩ | ⟨cls, s, rfl, rfl, rfl, hs⟩
  · obtain ⟨w, k?, hw, _⟩ := finishes hwf hd
    exact ⟨w, k?, hw, hP.1 w k? hw⟩
  · exact ⟨_, none, finishTree_leaf cls s, .token cls s hs⟩

/-- The right-hand side of a constructor, from a value position that is not an
extension, prints the arguments the builder delivers for its children. -/
theorem printsRhs_walk (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions)
    {n : String} (hkind : C.kind p = .constructor n) :
    ∀ (N : Nat) (rest : List Sym), rest.length ≤ N →
    ∀ (i : Nat) (pre : List Sym) (toks : List Tok) (kids : List Tree),
      p.rhs = pre ++ rest → (values pre).length = i → C.action p i ≠ .extend →
      ItemsWith G (PrintsFact G C L) rest toks kids →
      ∀ vals vals', deliverKids G C p i vals kids = some vals' →
        ∃ args, vals' = vals ++ args ∧ PrintsRhs G C L p i rest args toks := by
  intro N
  induction N with
  | zero =>
    intro rest hlen i _ _ _ _ _ _ hw vals vals' hd
    obtain rfl := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
    cases hw
    rw [deliverKids_nil] at hd
    injection hd with hd
    subst hd
    exact ⟨[], by simp, .nil p i⟩
  | succ N ih =>
    intro rest hlen i pre toks kids hrhs hpre hne hw vals vals' hd
    rcases rest with _ | ⟨v, rest⟩
    · cases hw
      rw [deliverKids_nil] at hd
      injection hd with hd
      subst hd
      exact ⟨[], by simp, .nil p i⟩
    have hlen' : rest.length ≤ N := by simp at hlen; omega
    cases hvf : v.isValue with
    | false =>
      cases v with
      | fixed t =>
        cases hw with
        | fixed _ _ toks' _ hw1 =>
          obtain ⟨args, h1, h2⟩ := ih rest hlen' i (pre ++ [.fixed t]) toks' kids
            (by rw [hrhs]; simp) (by rw [values_append, values_fixed, values_nil]; simpa using hpre)
            hne hw1 vals vals' hd
          exact ⟨args, h1, .fixed p i t rest args toks' h2⟩
      | _ => simp [Sym.isValue] at hvf
    | true =>
      obtain ⟨t, kids1, sub, toks1, rfl, rfl, hw1, hkid⟩ := items_head hvf hw
      obtain ⟨w, k?, hwt, hprint⟩ := kid_prints hwf hkid
      have harg : C.action p i = .arg := by
        rcases hwf.constructor p hp n hkind i with h | ⟨h, _⟩
        · exact h
        · exact absurd h hne
      rw [deliverKids_cons, hwt] at hd
      simp only [] at hd
      rw [harg, deliver_arg] at hd
      simp only [] at hd
      by_cases hext : C.action p (i + 1) = .extend
      · -- the next value is an extension of this one
        obtain ⟨j, hj, pre', x, h, rest2, hsplit, hpre', hx, hnj, b, key, hform⟩ :
            ∃ j, i + 1 = j + 1 ∧ ∃ pre' x h rest2, p.rhs = pre' ++ x :: .rule h :: rest2 ∧
              (values pre').length = j ∧ x.isValue = true ∧ C.action p j ≠ .extend ∧
              ∃ b key, (L h = some (.star b, key) ∨ L h = some (.plus b, key)) := by
          rcases hwf.constructor p hp n hkind (i + 1) with h | ⟨_, j, hj, hat⟩
          · rw [hext] at h
            cases h
          · obtain ⟨pre', x, h, rest2, h1, h2, h3, h4, h5⟩ := hat
            exact ⟨j, hj, pre', x, h, rest2, h1, h2, h3, h4, h5⟩
        have hji : i = j := by omega
        subst hji
        obtain ⟨_, hvx, hrest⟩ := split_unique pre pre' hvf hx (hrhs.symm.trans hsplit)
          (by rw [hpre, hpre'])
        subst hrest
        subst hvx
        obtain ⟨th, kids2, subh, toks2, rfl, rfl, hw2, hkidh⟩ := items_head rfl hw1
        rcases hkidh with ⟨m, hm, hdh, hPh⟩ | ⟨_, _, hm, _⟩
        · cases hm
          have hL : ∃ f, L h = some (f, key) := by
            rcases hform with hf | hf <;> exact ⟨_, hf⟩
          obtain ⟨f, hf⟩ := hL
          obtain ⟨wh, kh, hwh, hfinh⟩ := finishes hwf hdh
          unfold Finished at hfinh
          rw [hf] at hfinh
          obtain ⟨rfl, es, rfl⟩ := hfinh
          rw [deliverKids_cons, hwh] at hd
          simp only [] at hd
          rw [hext] at hd
          have hmerge : deliver (some key) .extend (vals ++ [named k? w]) (.seq es) =
              some (vals ++ [.node key [.seq (named k? w :: es)]]) := by
            simp only [deliver, List.getLast?_append, List.getLast?_singleton, Option.some_or,
              List.dropLast_concat]
          rw [hmerge] at hd
          simp only [] at hd
          have hnext2 : C.action p (i + 1 + 1) ≠ .extend := by
            intro h2
            rcases hwf.constructor p hp n hkind (i + 1 + 1) with h' | ⟨_, j, hj, hat⟩
            · rw [h2] at h'
              cases h'
            · obtain ⟨_, _, _, _, _, _, _, hne', _⟩ := hat
              have : j = i + 1 := by omega
              subst this
              exact hne' hext
          obtain ⟨args, h1, h2⟩ := ih rest2 (by simp at hlen'; omega) (i + 1 + 1)
            (pre ++ [v, .rule h]) toks2 kids2
            (by rw [hrhs]; simp) (by
              rw [values_append, values_value hvf, values_value (x := .rule h) rfl, values_nil]
              simp [hpre])
            hnext2 hw2 _ vals' hd
          refine ⟨.node key [.seq (named k? w :: es)] :: args, by rw [h1]; simp, ?_⟩
          have := PrintsRhs.extended p i v hvf h rest2 hext f key hf (named k? w) es sub subh
            hprint (hPh.2 f key es hf hwh) hnext2 args toks2 h2
          simpa [List.append_assoc] using this
        · cases hm
      · obtain ⟨args, h1, h2⟩ := ih rest hlen' (i + 1) (pre ++ [v]) toks1 kids1
          (by rw [hrhs]; simp) (by rw [values_append, values_value hvf, values_nil]; simp [hpre])
          hext hw1 _ vals' hd
        exact ⟨named k? w :: args, by rw [h1]; simp,
          .value p i v hvf rest hext (named k? w) sub hprint args toks1 h2⟩

/-- The elements of a list production's value: its delivered values with its
text before or after them. -/
def arrange : Option (Bool × String) → List CanonicalTerm → List CanonicalTerm
  | none, vals => vals
  | some (false, s), vals => .text s :: vals
  | some (true, s), vals => vals ++ [.text s]

theorem finish_list (key : String) (text : Option (Bool × String)) (vals : List CanonicalTerm) :
    finish (.list key text) vals = some (.seq (arrange text vals)) := by
  rcases text with _ | ⟨_ | _, s⟩ <;> rfl

theorem finishTree_list_node (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions)
    {key : String} {text : Option (Bool × String)} (hkind : C.kind p = .list key text)
    {kids : List Tree} {vals : List CanonicalTerm} (hdel : deliverKids G C p 0 [] kids = some vals) :
    finishTree G C (.node p.label kids) = some (.seq (arrange text vals), some key) := by
  rw [finishTree_node hwf hp, hdel]
  simp only [hkind, finish_list, Option.map_some, Kind.key?]

theorem items_fixedSyms {P : String → List Tok → Tree → Prop} :
    ∀ (sep : List String) {rest : List Sym} {toks : List Tok} {kids : List Tree},
      ItemsWith G P (fixedSyms sep ++ rest) toks kids →
      ∃ toks', toks = fixedToks sep ++ toks' ∧ ItemsWith G P rest toks' kids
  | [], _, _, _, h => ⟨_, rfl, h⟩
  | t :: sep, _, _, _, h => by
    cases h with
    | fixed _ _ toks' _ h' =>
      obtain ⟨toks'', rfl, h''⟩ := items_fixedSyms sep h'
      exact ⟨toks'', rfl, h''⟩

theorem items_all_fixed {P : String → List Tok → Tree → Prop} :
    ∀ {rhs : List Sym} {toks : List Tok} {kids : List Tree}, (∀ x ∈ rhs, x.isValue = false) →
      ItemsWith G P rhs toks kids → toks = fixedToks (fixedTexts rhs) ∧ kids = []
  | [], _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | .fixed t :: rest, _, _, hall, h => by
    cases h with
    | fixed _ _ toks' _ h' =>
      obtain ⟨rfl, rfl⟩ := items_all_fixed (fun x hx => hall x (List.mem_cons_of_mem _ hx)) h'
      exact ⟨rfl, rfl⟩
  | .rule _ :: _, _, _, hall, _ => by simpa [Sym.isValue] using hall _ List.mem_cons_self
  | .token _ :: _, _, _, hall, _ => by simpa [Sym.isValue] using hall _ List.mem_cons_self

/-- A list rule's child prints its list by the rule's form. -/
theorem list_kid_prints (hwf : WellFormed G C L) {r : String} {f : ListForm} {key : String}
    (hL : L r = some (f, key)) {sub : List Tok} {t : Tree} (hd : Derives G r sub t)
    (hP : PrintsFact G C L r sub t) :
    ∃ es, finishTree G C t = some (.seq es, some key) ∧ PrintsList G C L f es sub := by
  obtain ⟨w, k, hw, hfin⟩ := finishes hwf hd
  unfold Finished at hfin
  rw [hL] at hfin
  obtain ⟨rfl, es, rfl⟩ := hfin
  exact ⟨es, hw, hP.2 f key es hL hw⟩

/-- Delivering one argument child after the given values. -/
theorem deliver_one_arg {p : Production} {i : Nat} {vals : List CanonicalTerm} {t : Tree}
    {w : CanonicalTerm} {k? : Option String} (hwt : finishTree G C t = some (w, k?))
    (ha : C.action p i = .arg) :
    deliverKids G C p i vals [t] = some (vals ++ [named k? w]) := by
  rw [deliverKids_cons, hwt]
  simp only []
  rw [ha, deliver_arg]
  simp only []
  rw [deliverKids_nil]

/-- A production of a list rule prints its derivation's list by the rule's
form. -/
theorem list_prints (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions)
    {f : ListForm} {key : String} (hL : L p.lhs = some (f, key)) {toks : List Tok}
    {kids : List Tree} (hw : ItemsWith G (PrintsFact G C L) p.rhs toks kids) :
    ∃ es, finishTree G C (.node p.label kids) = some (.seq es, some key) ∧
      PrintsList G C L f es toks := by
  obtain ⟨hrhs, hspec⟩ := (hwf.rule p.lhs f key hL).1 p hp rfl
  obtain ⟨text, hkind⟩ := rule_kind_list hwf hL hp rfl
  -- the empty production
  have hempty : p.rhs = [] → C.kind p = .list key none →
      ∃ es, finishTree G C (.node p.label kids) = some (.seq es, some key) ∧ es = [] ∧
        toks = [] := by
    intro h hk
    rw [h] at hw
    cases hw
    exact ⟨[], finishTree_list_node hwf hp hk (deliverKids_nil p 0 []), rfl, rfl⟩
  -- one body `b`
  have hone : ∀ b, p.rhs = [b] → (b.isValue = true → C.kind p = .list key none ∧
        C.action p 0 = .arg) → (∀ t, b = .fixed t → C.kind p = .list key (some (false, t))) →
      ∃ e, finishTree G C (.node p.label kids) = some (.seq [e], some key) ∧
        Prints G C L b e toks := by
    intro b h hval hfix
    rw [h] at hw
    cases hb : b.isValue
    · cases b with
      | fixed t =>
        cases hw with
        | fixed _ _ _ _ hw' =>
          cases hw'
          exact ⟨.text t, finishTree_list_node hwf hp (hfix t rfl) (deliverKids_nil p 0 []),
            .fixed t⟩
      | _ => simp [Sym.isValue] at hb
    · obtain ⟨hk, ha0⟩ := hval hb
      obtain ⟨t, kids', sub, toks', rfl, rfl, hw', hkid⟩ := items_head hb hw
      cases hw'
      obtain ⟨w, k?, hwt, hprint⟩ := kid_prints hwf hkid
      refine ⟨named k? w, finishTree_list_node hwf hp hk (deliver_one_arg hwt ha0), ?_⟩
      simpa using hprint
  -- the recursion and a body `b`
  have hrec : ∀ b, p.rhs = [.rule p.lhs, b] → C.action p 0 = .splice →
      (b.isValue = true → C.kind p = .list key none ∧ C.action p 1 = .arg) →
      (∀ t, b = .fixed t → C.kind p = .list key (some (true, t))) →
      ∃ esr e toksr toksb, finishTree G C (.node p.label kids) = some (.seq (esr ++ [e]), some key) ∧
        PrintsList G C L f esr toksr ∧ Prints G C L b e toksb ∧ toks = toksr ++ toksb := by
    intro b h hs0 hval hfix
    rw [h] at hw
    obtain ⟨tr, kids', subr, toks', rfl, rfl, hw', hkidr⟩ := items_head rfl hw
    rcases hkidr with ⟨m, hm, hdr, hPr⟩ | ⟨_, _, hm, _⟩
    · cases hm
      obtain ⟨esr, hwr, hpr⟩ := list_kid_prints hwf hL hdr hPr
      have hsplice : ∀ rest, deliverKids G C p 0 [] (tr :: rest) =
          deliverKids G C p 1 esr rest := by
        intro rest
        rw [deliverKids_cons, hwr]
        simp only []
        rw [hs0]
        simp only [deliver, List.nil_append]
      cases hb : b.isValue
      · cases b with
        | fixed t =>
          cases hw' with
          | fixed _ _ _ _ hw'' =>
            cases hw''
            have hdel : deliverKids G C p 0 [] [tr] = some esr := by
              rw [hsplice, deliverKids_nil]
            refine ⟨esr, .text t, subr, [.fixed t], ?_, hpr, .fixed t, rfl⟩
            have := finishTree_list_node hwf hp (hfix t rfl) hdel
            simpa [arrange] using this
        | _ => simp [Sym.isValue] at hb
      · obtain ⟨hk, ha1⟩ := hval hb
        obtain ⟨t, kids'', sub, toks'', rfl, rfl, hw'', hkid⟩ := items_head hb hw'
        cases hw''
        obtain ⟨w, k?, hwt, hprint⟩ := kid_prints hwf hkid
        have hdel : deliverKids G C p 0 [] [tr, t] = some (esr ++ [named k? w]) := by
          rw [hsplice, deliver_one_arg hwt ha1]
        refine ⟨esr, named k? w, subr, sub, ?_, hpr, hprint, by simp⟩
        have := finishTree_list_node hwf hp hk hdel
        simpa [arrange] using this
    · cases hm
  cases f with
  | option b =>
    obtain ⟨_, h0, h1, _⟩ := hspec
    simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
    rcases hrhs with h | h
    · obtain ⟨_, hes, rfl, rfl⟩ := hempty h (h0 h)
      exact ⟨[], hes, .optionNone b⟩
    · obtain ⟨e, he, hpe⟩ := hone b h (h1 h).1 (h1 h).2
      exact ⟨[e], he, .optionSome b e toks hpe⟩
  | star b =>
    obtain ⟨_, h0, _, h2⟩ := hspec
    simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
    rcases hrhs with h | h
    · obtain ⟨_, hes, rfl, rfl⟩ := hempty h (h0 h)
      exact ⟨[], hes, .starNil b⟩
    · obtain ⟨esr, e, toksr, toksb, he, hpr, hpe, rfl⟩ := hrec b h (h2 h).1 (h2 h).2.1 (h2 h).2.2
      exact ⟨esr ++ [e], he, .starSnoc b esr e toksr toksb hpr hpe⟩
  | plus b =>
    obtain ⟨_, _, h1, h2⟩ := hspec
    simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
    rcases hrhs with h | h
    · obtain ⟨e, he, hpe⟩ := hone b h (h1 h).1 (h1 h).2
      exact ⟨[e], he, .plusOne b e toks hpe⟩
    · obtain ⟨esr, e, toksr, toksb, he, hpr, hpe, rfl⟩ := hrec b h (h2 h).1 (h2 h).2.1 (h2 h).2.2
      exact ⟨esr ++ [e], he, .plusSnoc b esr e toksr toksb hpr hpe⟩
  | separated x sep right =>
    obtain ⟨hx, _, hk, h1, h2⟩ := hspec
    simp only [ListForm.rhss] at hrhs
    cases right with
    | true =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrhs
      rcases hrhs with h | h
      · rw [h] at hw
        obtain ⟨t, kids', sub, toks', rfl, rfl, hw', hkid⟩ := items_head hx hw
        cases hw'
        obtain ⟨w, k?, hwt, hprint⟩ := kid_prints hwf hkid
        refine ⟨[named k? w], ?_, by simpa using PrintsList.sepOne x sep true _ _ hprint⟩
        have := finishTree_list_node hwf hp hk (deliver_one_arg hwt (h1 h))
        simpa [arrange] using this
      · have hne : p.rhs ≠ [x] := by rw [h]; simp
        have hacts := h2 hne
        simp only [if_true] at hacts
        rw [h, List.cons_append] at hw
        obtain ⟨t, kids', sub, toks', rfl, rfl, hw', hkid⟩ := items_head hx hw
        obtain ⟨toks2, rfl, hw2⟩ := items_fixedSyms sep hw'
        obtain ⟨tr, kids2, subr, toks3, rfl, rfl, hw3, hkidr⟩ := items_head rfl hw2
        cases hw3
        rcases hkidr with ⟨m, hm, hdr, hPr⟩ | ⟨_, _, hm, _⟩
        · cases hm
          obtain ⟨esr, hwr, hpr⟩ := list_kid_prints hwf hL hdr hPr
          obtain ⟨w, k?, hwt, hprint⟩ := kid_prints hwf hkid
          have hdel : deliverKids G C p 0 [] [t, tr] = some (named k? w :: esr) := by
            rw [deliverKids_cons, hwt]
            simp only []
            rw [hacts.1, deliver_arg]
            simp only [List.nil_append]
            rw [deliverKids_cons, hwr]
            simp only []
            rw [hacts.2]
            simp only [deliver]
            rw [deliverKids_nil]
            rfl
          refine ⟨named k? w :: esr, ?_, by
            simpa [List.append_assoc] using PrintsList.sepCons x sep _ _ _ _ hprint hpr⟩
          have := finishTree_list_node hwf hp hk hdel
          simpa [arrange] using this
        · cases hm
    | false =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hrhs
      rcases hrhs with h | h
      · rw [h] at hw
        obtain ⟨t, kids', sub, toks', rfl, rfl, hw', hkid⟩ := items_head hx hw
        cases hw'
        obtain ⟨w, k?, hwt, hprint⟩ := kid_prints hwf hkid
        refine ⟨[named k? w], ?_, by simpa using PrintsList.sepOne x sep false _ _ hprint⟩
        have := finishTree_list_node hwf hp hk (deliver_one_arg hwt (h1 h))
        simpa [arrange] using this
      · have hne : p.rhs ≠ [x] := by rw [h]; simp
        have hacts := h2 hne
        simp only [Bool.false_eq_true, if_false] at hacts
        rw [h, List.cons_append] at hw
        obtain ⟨tr, kids', subr, toks', rfl, rfl, hw', hkidr⟩ := items_head rfl hw
        obtain ⟨toks2, rfl, hw2⟩ := items_fixedSyms sep hw'
        obtain ⟨t, kids2, sub, toks3, rfl, rfl, hw3, hkid⟩ := items_head hx hw2
        cases hw3
        rcases hkidr with ⟨m, hm, hdr, hPr⟩ | ⟨_, _, hm, _⟩
        · cases hm
          obtain ⟨esr, hwr, hpr⟩ := list_kid_prints hwf hL hdr hPr
          obtain ⟨w, k?, hwt, hprint⟩ := kid_prints hwf hkid
          have hdel : deliverKids G C p 0 [] [tr, t] = some (esr ++ [named k? w]) := by
            rw [deliverKids_cons, hwr]
            simp only []
            rw [hacts.1]
            simp only [deliver, List.nil_append]
            rw [deliver_one_arg hwt hacts.2]
          refine ⟨esr ++ [named k? w], ?_, by
            simpa [List.append_assoc] using PrintsList.sepSnoc x sep _ _ _ _ hpr hprint⟩
          have := finishTree_list_node hwf hp hk hdel
          simpa [arrange] using this
        · cases hm

/-- Every derivation has the printing fact: its tree's value prints its
tokens at its rule, and at a list rule its list prints them by the rule's
form. -/
theorem prints_fact (hwf : WellFormed G C L) :
    ∀ {n toks t}, Derives G n toks t → PrintsFact G C L n toks t := by
  refine Derives.induction_with (PrintsFact G C L) ?_
  intro p hp toks kids _ hw
  refine ⟨fun v k? hv => ?_, fun f key es hL hes => ?_⟩
  · cases hkind : C.kind p with
    | transparent =>
      obtain ⟨v0, hrhs, hvv, ha0⟩ := hwf.transparent p hp hkind
      rw [hrhs] at hw
      obtain ⟨t, kids', sub, toks', rfl, rfl, hw', hkid⟩ := items_head hvv hw
      cases hw'
      obtain ⟨w, k'?, hwt, hprint⟩ := kid_prints hwf hkid
      have hfin := finishTree_node hwf hp [t]
      rw [deliver_one_arg hwt ha0] at hfin
      simp only [List.nil_append, hkind, finish, Option.map_some, Kind.key?] at hfin
      rw [hfin] at hv
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .rule p hp _ _ (.transparent p hkind v0 hrhs _ _ (by simpa [named] using hprint))
    | literal s =>
      obtain ⟨_, hall, _⟩ := hwf.literal p hp s hkind
      obtain ⟨rfl, rfl⟩ := items_all_fixed hall hw
      have hfin := finishTree_node hwf hp []
      rw [deliverKids_nil] at hfin
      simp only [hkind, finish, Option.map_some, Kind.key?] at hfin
      rw [hfin] at hv
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .rule p hp _ _ (.literal p s hkind)
    | constructor n =>
      have hne : C.action p 0 ≠ .extend := by
        intro h
        rcases hwf.constructor p hp n hkind 0 with h' | ⟨_, j, hj, _⟩
        · rw [h] at h'
          cases h'
        · omega
      have hfin := finishTree_node hwf hp kids
      cases hd : deliverKids G C p 0 [] kids with
      | none =>
        rw [hd] at hfin
        rw [hfin] at hv
        cases hv
      | some vals =>
        obtain ⟨args, hargs, hpr⟩ := printsRhs_walk hwf hp hkind p.rhs.length p.rhs (Nat.le_refl _) 0 []
          toks kids (by simp) rfl hne hw [] vals hd
        rw [hd] at hfin
        simp only [hkind, finish, Option.map_some, Kind.key?] at hfin
        rw [hfin] at hv
        simp only [Option.some.injEq, Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        simp only [List.nil_append] at hargs
        subst hargs
        exact .rule p hp _ _ (.constructor p n hkind _ _ hpr)
    | list key text =>
      obtain ⟨fk, hfk⟩ := Option.isSome_iff_exists.1 (hwf.list p hp key text hkind)
      obtain ⟨f, key'⟩ := fk
      obtain ⟨text', htext'⟩ := rule_kind_list hwf hfk hp rfl
      rw [hkind] at htext'
      injection htext' with hkey _
      subst hkey
      have hL : L p.lhs = some (f, key) := hfk
      obtain ⟨es, hes, hpl⟩ := list_prints hwf hp hL hw
      rw [hes] at hv
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .rule p hp _ _ (.list p key text hkind f hL es toks hpl)
  · obtain ⟨es', hes', hpl⟩ := list_prints hwf hp hL hw
    rw [hes'] at hes
    simp only [Option.some.injEq, Prod.mk.injEq, CanonicalTerm.seq.injEq] at hes
    obtain ⟨rfl, _⟩ := hes
    exact hpl

/-- The projection of a derivation prints its tokens at its rule. -/
theorem prints_canon (hwf : WellFormed G C L) {n : String} {toks : List Tok} {t : Tree}
    (h : Derives G n toks t) : ∃ c, canon G C t = some c ∧ Prints G C L (.rule n) c toks := by
  obtain ⟨v, k?, hv, _⟩ := finishes hwf h
  exact ⟨named k? v, by simp only [canon, hv, Option.map_some], (prints_fact hwf h).1 v k? hv⟩

end PrintsCanon

/-! ## The printed text of a term derives to it -/

section DerivesOfPrints

variable {G : Grammar} {C : Classification} {L : String → Option (ListForm × String)}

/-- What a term printed at a symbol gives the reader: at a rule a derivation
of the printed tokens whose value, delivered as an argument, is the term; at a
token its lexeme; at a fixed terminal its text. -/
def Printed (G : Grammar) (C : Classification) : Sym → CanonicalTerm → List Tok → Prop
  | .rule n, c, toks =>
    ∃ t, Derives G n toks t ∧ ∃ w k?, finishTree G C t = some (w, k?) ∧ named k? w = c
  | .token cls, c, toks => ∃ s, G.lexeme cls s ∧ toks = [.lexeme cls s] ∧ c = .node cls [.text s]
  | .fixed t, c, toks => toks = [.fixed t] ∧ c = .text t

/-- A value symbol printed a term: its child tree delivers the term. -/
theorem printed_kid {v : Sym} (hv : v.isValue = true) {c : CanonicalTerm} {sub : List Tok}
    (h : Printed G C v c sub) :
    ∃ t w k?, finishTree G C t = some (w, k?) ∧ named k? w = c ∧
      ∀ rest toks kids, DerivesItems G rest toks kids →
        DerivesItems G (v :: rest) (sub ++ toks) (t :: kids) := by
  cases v with
  | rule n =>
    obtain ⟨t, hd, w, k?, hw, hc⟩ := h
    exact ⟨t, w, k?, hw, hc, fun rest toks kids hk => .rule n sub t hd rest toks kids hk⟩
  | token cls =>
    obtain ⟨s, hs, rfl, rfl⟩ := h
    exact ⟨.leaf cls s, _, none, finishTree_leaf cls s, rfl,
      fun rest toks kids hk => .token cls s hs rest toks kids hk⟩
  | fixed _ => simp [Sym.isValue] at hv

theorem derivesItems_fixedSyms :
    ∀ (sep : List String) {rest : List Sym} {toks : List Tok} {kids : List Tree},
      DerivesItems G rest toks kids → DerivesItems G (fixedSyms sep ++ rest) (fixedToks sep ++ toks) kids
  | [], _, _, _, h => h
  | t :: sep, _, _, _, h => .fixed t _ _ _ (derivesItems_fixedSyms sep h)

theorem derivesItems_all_fixed :
    ∀ {rhs : List Sym}, (∀ x ∈ rhs, x.isValue = false) →
      DerivesItems G rhs (fixedToks (fixedTexts rhs)) []
  | [], _ => .nil
  | .fixed t :: rest, hall =>
    .fixed t rest _ _ (derivesItems_all_fixed (fun x hx => hall x (List.mem_cons_of_mem _ hx)))
  | .rule _ :: _, hall => by simpa [Sym.isValue] using hall _ List.mem_cons_self
  | .token _ :: _, hall => by simpa [Sym.isValue] using hall _ List.mem_cons_self

/-- Delivering a spliced list child after the given values. -/
theorem deliver_splice {p : Production} {i : Nat} {vals : List CanonicalTerm} {t : Tree}
    {ts : List Tree} {es : List CanonicalTerm} {key : String}
    (hwt : finishTree G C t = some (.seq es, some key)) (ha : C.action p i = .splice) :
    deliverKids G C p i vals (t :: ts) = deliverKids G C p (i + 1) (vals ++ es) ts := by
  rw [deliverKids_cons, hwt]
  simp only []
  rw [ha]
  simp only [deliver]

/-- A right-hand side of a list rule is the right-hand side of one of its
productions, with the kind and actions of its form. -/
theorem list_production (hwf : WellFormed G C L) {r : String} {f : ListForm} {key : String}
    (hL : L r = some (f, key)) {rhs : List Sym} (hrhs : rhs ∈ ListForm.rhss r f) :
    ∃ q ∈ G.productions, q.lhs = r ∧ q.rhs = rhs ∧ f.Spec r key q C := by
  obtain ⟨q, hq, hlhs, hqr⟩ := (hwf.rule r f key hL).2.1 rhs hrhs
  exact ⟨q, hq, hlhs, hqr, ((hwf.rule r f key hL).1 q hq hlhs).2⟩

/-- A list production's node over derived children derives at its rule. -/
theorem list_node_derives (hwf : WellFormed G C L) {q : Production} (hq : q ∈ G.productions)
    {r : String} (hlhs : q.lhs = r) {key : String} {text : Option (Bool × String)}
    (hkind : C.kind q = .list key text) {toks : List Tok} {kids : List Tree}
    (hk : DerivesItems G q.rhs toks kids) {vals : List CanonicalTerm}
    (hdel : deliverKids G C q 0 [] kids = some vals) :
    ∃ t, Derives G r toks t ∧ finishTree G C t = some (.seq (arrange text vals), some key) := by
  subst hlhs
  exact ⟨_, .node q hq toks kids hk, finishTree_list_node hwf hq hkind hdel⟩

/-- A list production of one body over its printed element derives to that
one element. -/
theorem list_one_derives (hwf : WellFormed G C L) {q : Production} (hq : q ∈ G.productions)
    {r : String} (hlhs : q.lhs = r) {b : Sym} (hqr : q.rhs = [b]) {key : String}
    (h1 : (b.isValue = true → C.kind q = .list key none ∧ C.action q 0 = .arg) ∧
      (∀ t, b = .fixed t → C.kind q = .list key (some (false, t))))
    {e : CanonicalTerm} {toks : List Tok} (ih : Printed G C b e toks) :
    ∃ t, Derives G r toks t ∧ finishTree G C t = some (.seq [e], some key) := by
  cases hb : b.isValue
  · cases b with
    | fixed t =>
      obtain ⟨rfl, rfl⟩ := ih
      have hk : DerivesItems G q.rhs [.fixed t] [] := by
        rw [hqr]
        exact .fixed t [] [] [] .nil
      exact list_node_derives hwf hq hlhs (h1.2 t rfl) hk (deliverKids_nil q 0 [])
    | _ => simp [Sym.isValue] at hb
  · obtain ⟨hk1, ha0⟩ := h1.1 hb
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hb ih
    have hk : DerivesItems G q.rhs toks [t] := by
      rw [hqr]
      simpa using hitems [] [] [] .nil
    obtain ⟨t', hd, ht⟩ := list_node_derives hwf hq hlhs hk1 hk (deliver_one_arg hwt ha0)
    refine ⟨t', hd, ?_⟩
    rw [ht]
    simp [arrange, hc]

/-- A list production of the recursion and a body, over a derived list and a
printed element, derives to the list with the element after it. -/
theorem list_snoc_derives (hwf : WellFormed G C L) {q : Production} (hq : q ∈ G.productions)
    {r : String} (hlhs : q.lhs = r) {b : Sym} (hqr : q.rhs = [.rule r, b]) {key : String}
    (h2 : C.action q 0 = .splice ∧
      (b.isValue = true → C.kind q = .list key none ∧ C.action q 1 = .arg) ∧
      (∀ t, b = .fixed t → C.kind q = .list key (some (true, t))))
    {es : List CanonicalTerm} {e : CanonicalTerm} {toks₁ toks₂ : List Tok}
    (hs : ∃ t, Derives G r toks₁ t ∧ finishTree G C t = some (.seq es, some key))
    (ih : Printed G C b e toks₂) :
    ∃ t, Derives G r (toks₁ ++ toks₂) t ∧ finishTree G C t = some (.seq (es ++ [e]), some key) := by
  obtain ⟨hs0, hval, hfix⟩ := h2
  obtain ⟨tr, hdr, hwr⟩ := hs
  cases hb : b.isValue
  · cases b with
    | fixed t =>
      obtain ⟨rfl, rfl⟩ := ih
      have hk : DerivesItems G q.rhs (toks₁ ++ [.fixed t]) [tr] := by
        rw [hqr]
        exact .rule r toks₁ tr hdr [.fixed t] [.fixed t] [] (.fixed t [] [] [] .nil)
      have hdel : deliverKids G C q 0 [] [tr] = some es := by
        rw [deliver_splice hwr hs0, deliverKids_nil, List.nil_append]
      exact list_node_derives hwf hq hlhs (hfix t rfl) hk hdel
    | _ => simp [Sym.isValue] at hb
  · obtain ⟨hk1, ha1⟩ := hval hb
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hb ih
    have hk : DerivesItems G q.rhs (toks₁ ++ toks₂) [tr, t] := by
      rw [hqr]
      have := DerivesItems.rule r toks₁ tr hdr [b] (toks₂ ++ []) [t] (hitems [] [] [] .nil)
      simpa using this
    have hdel : deliverKids G C q 0 [] [tr, t] = some (es ++ [e]) := by
      rw [deliver_splice hwr hs0]
      simp only [List.nil_append]
      rw [deliver_one_arg hwt ha1, hc]
    exact list_node_derives hwf hq hlhs hk1 hk hdel

/-- Printing is read back: a term printed at a symbol is what the reader
finds there, and a list printed by a rule's form derives at that rule to the
list. -/
theorem printed_of_prints (hwf : WellFormed G C L) :
    ∀ {sym c toks}, Prints G C L sym c toks → Printed G C sym c toks := by
  intro sym c toks h
  refine Prints.rec
    (motive_1 := fun sym c toks _ => Printed G C sym c toks)
    (motive_2 := fun p c toks _ => p ∈ G.productions → Printed G C (.rule p.lhs) c toks)
    (motive_3 := fun p i rest args toks _ => p ∈ G.productions →
      (∃ n, C.kind p = .constructor n) → C.action p i ≠ .extend →
      ∃ kids, DerivesItems G rest toks kids ∧
        ∀ vals, deliverKids G C p i vals kids = some (vals ++ args))
    (motive_4 := fun f es toks _ => ∀ r key, L r = some (f, key) →
      ∃ t, Derives G r toks t ∧ finishTree G C t = some (.seq es, some key))
    ?token ?fixed ?rule ?transparent ?literal ?constructor ?list
    ?rnil ?rfixed ?rvalue ?rextended
    ?optionNone ?optionSome ?starNil ?starSnoc ?plusOne ?plusSnoc ?sepOne ?sepCons ?sepSnoc h
  case token => exact fun cls s hs => ⟨s, hs, rfl, rfl⟩
  case fixed => exact fun t => ⟨rfl, rfl⟩
  case rule => exact fun p hp _ _ _ ih => ih hp
  case transparent =>
    intro p hk v hv c toks _ ih hp
    obtain ⟨v0, hrhs, hvv, ha0⟩ := hwf.transparent p hp hk
    rw [hv, List.cons.injEq] at hrhs
    obtain ⟨rfl, -⟩ := hrhs
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hvv ih
    refine ⟨.node p.label [t], ?_, named k? w, none, ?_, hc⟩
    · have := Derives.node p hp (toks ++ []) [t] (by rw [hv]; exact hitems [] [] [] .nil)
      simpa using this
    · rw [finishTree_node hwf hp, deliver_one_arg hwt ha0]
      simp only [List.nil_append, hk, finish, Option.map_some, Kind.key?]
  case literal =>
    intro p s hk hp
    obtain ⟨_, hall, _⟩ := hwf.literal p hp s hk
    refine ⟨.node p.label [], .node p hp _ [] (derivesItems_all_fixed hall), .text s, none, ?_, rfl⟩
    rw [finishTree_node hwf hp, deliverKids_nil]
    simp only [hk, finish, Option.map_some, Kind.key?]
  case constructor =>
    intro p n hk args toks _ ih hp
    have hne : C.action p 0 ≠ .extend := by
      intro h
      rcases hwf.constructor p hp n hk 0 with h' | ⟨_, j, hj, _⟩
      · rw [h] at h'
        cases h'
      · omega
    obtain ⟨kids, hkids, hdel⟩ := ih hp ⟨n, hk⟩ hne
    refine ⟨.node p.label kids, .node p hp toks kids hkids, .node n args, none, ?_, rfl⟩
    rw [finishTree_node hwf hp, hdel []]
    simp only [List.nil_append, hk, finish, Option.map_some, Kind.key?]
  case list =>
    intro p key _ _ f hf es toks _ ih _
    obtain ⟨t, hd, ht⟩ := ih p.lhs key hf
    exact ⟨t, hd, .seq es, some key, ht, rfl⟩
  case rnil =>
    intro p i _ _ _
    exact ⟨[], .nil, fun vals => by rw [deliverKids_nil, List.append_nil]⟩
  case rfixed =>
    intro p i t rest args toks _ ih hp hn hne
    obtain ⟨kids, hkids, hdel⟩ := ih hp hn hne
    exact ⟨kids, .fixed t rest toks kids hkids, hdel⟩
  case rvalue =>
    intro p i v hv rest hnext a sub _ args toks _ iha ih hp hn hne
    obtain ⟨n, hkn⟩ := hn
    have harg : C.action p i = .arg :=
      (hwf.constructor p hp n hkn i).resolve_right (fun h => hne h.1)
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hv iha
    obtain ⟨kids, hkids, hdel⟩ := ih hp ⟨n, hkn⟩ hnext
    refine ⟨t :: kids, hitems rest toks kids hkids, fun vals => ?_⟩
    rw [deliverKids_cons, hwt]
    simp only []
    rw [harg, deliver_arg]
    simp only []
    rw [hdel, hc]
    simp
  case rextended =>
    intro p i v hv hr rest hext f key hf e tail sub₁ sub₂ _ _ hnext args toks _ ihe ihtail ih
      hp hn hne
    obtain ⟨n, hkn⟩ := hn
    have harg : C.action p i = .arg :=
      (hwf.constructor p hp n hkn i).resolve_right (fun h => hne h.1)
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hv ihe
    obtain ⟨tr, hdr, hwr⟩ := ihtail hr key hf
    obtain ⟨kids, hkids, hdel⟩ := ih hp ⟨n, hkn⟩ hnext
    refine ⟨t :: tr :: kids, ?_, fun vals => ?_⟩
    · have := hitems (.rule hr :: rest) (sub₂ ++ toks) (tr :: kids)
        (.rule hr sub₂ tr hdr rest toks kids hkids)
      simpa [List.append_assoc] using this
    · rw [deliverKids_cons, hwt]
      simp only []
      rw [harg, deliver_arg]
      simp only []
      rw [deliverKids_cons, hwr]
      simp only []
      rw [hext]
      have hmerge : deliver (some key) .extend (vals ++ [named k? w]) (.seq tail) =
          some (vals ++ [.node key [.seq (named k? w :: tail)]]) := by
        simp only [deliver, List.getLast?_append, List.getLast?_singleton, Option.some_or,
          List.dropLast_concat]
      rw [hmerge]
      simp only []
      rw [show i + 1 + 1 = i + 2 from rfl, hdel, hc]
      simp
  case optionNone =>
    intro b r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ := list_production hwf hL (rhs := []) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, h0, _, _⟩ := hspec
    have hk : DerivesItems G q.rhs [] [] := by
      rw [hqr]
      exact .nil
    exact list_node_derives hwf hq hlhs (h0 hqr) hk (deliverKids_nil q 0 [])
  case starNil =>
    intro b r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ := list_production hwf hL (rhs := []) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, h0, _, _⟩ := hspec
    have hk : DerivesItems G q.rhs [] [] := by
      rw [hqr]
      exact .nil
    exact list_node_derives hwf hq hlhs (h0 hqr) hk (deliverKids_nil q 0 [])
  case optionSome =>
    intro b e toks _ ih r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ := list_production hwf hL (rhs := [b]) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, _, h1, _⟩ := hspec
    exact list_one_derives hwf hq hlhs hqr (h1 hqr) ih
  case plusOne =>
    intro b e toks _ ih r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ := list_production hwf hL (rhs := [b]) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, _, h1, _⟩ := hspec
    exact list_one_derives hwf hq hlhs hqr (h1 hqr) ih
  case starSnoc =>
    intro b es e toks₁ toks₂ _ _ ihs ih r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ :=
      list_production hwf hL (rhs := [.rule r, b]) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, _, _, h2⟩ := hspec
    exact list_snoc_derives hwf hq hlhs hqr (h2 hqr) (ihs r key hL) ih
  case plusSnoc =>
    intro b es e toks₁ toks₂ _ _ ihs ih r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ :=
      list_production hwf hL (rhs := [.rule r, b]) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, _, _, h2⟩ := hspec
    exact list_snoc_derives hwf hq hlhs hqr (h2 hqr) (ihs r key hL) ih
  case sepOne =>
    intro x sep right e toks _ ih r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ :=
      list_production hwf hL (rhs := [x]) (by cases right <;> simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨hx, _, hk1, h1, _⟩ := hspec
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hx ih
    have hk : DerivesItems G q.rhs toks [t] := by
      rw [hqr]
      simpa using hitems [] [] [] .nil
    obtain ⟨t', hd, ht⟩ := list_node_derives hwf hq hlhs hk1 hk (deliver_one_arg hwt (h1 hqr))
    refine ⟨t', hd, ?_⟩
    rw [ht]
    simp [arrange, hc]
  case sepCons =>
    intro x sep e es toks₁ toks₂ _ _ ih ihs r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ :=
      list_production hwf hL (rhs := x :: fixedSyms sep ++ [.rule r]) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨hx, _, hk1, _, h2⟩ := hspec
    have hacts := h2 (by rw [hqr]; simp)
    simp only [if_true] at hacts
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hx ih
    obtain ⟨tr, hdr, hwr⟩ := ihs r key hL
    have hk : DerivesItems G q.rhs (toks₁ ++ fixedToks sep ++ toks₂) [t, tr] := by
      rw [hqr]
      have := hitems (fixedSyms sep ++ [.rule r]) (fixedToks sep ++ (toks₂ ++ [])) [tr]
        (derivesItems_fixedSyms sep (.rule r toks₂ tr hdr [] [] [] .nil))
      simpa [List.append_assoc] using this
    have hdel : deliverKids G C q 0 [] [t, tr] = some (e :: es) := by
      rw [deliverKids_cons, hwt]
      simp only []
      rw [hacts.1, deliver_arg]
      simp only [List.nil_append]
      rw [deliver_splice hwr hacts.2, deliverKids_nil, hc]
      rfl
    exact list_node_derives hwf hq hlhs hk1 hk hdel
  case sepSnoc =>
    intro x sep es e toks₁ toks₂ _ _ ihs ih r key hL
    obtain ⟨q, hq, hlhs, hqr, hspec⟩ :=
      list_production hwf hL (rhs := .rule r :: fixedSyms sep ++ [x]) (by simp [ListForm.rhss])
    simp only [ListForm.Spec] at hspec
    obtain ⟨hx, _, hk1, _, h2⟩ := hspec
    have hacts := h2 (by rw [hqr]; simp)
    simp only [Bool.false_eq_true, if_false] at hacts
    obtain ⟨t, w, k?, hwt, hc, hitems⟩ := printed_kid hx ih
    obtain ⟨tr, hdr, hwr⟩ := ihs r key hL
    have hk : DerivesItems G q.rhs (toks₁ ++ fixedToks sep ++ toks₂) [tr, t] := by
      rw [hqr]
      have := DerivesItems.rule r toks₁ tr hdr (fixedSyms sep ++ [x]) (fixedToks sep ++ (toks₂ ++ []))
        [t] (derivesItems_fixedSyms sep (hitems [] [] [] .nil))
      simpa [List.append_assoc] using this
    have hdel : deliverKids G C q 0 [] [tr, t] = some (es ++ [e]) := by
      rw [deliver_splice hwr hacts.1]
      simp only [List.nil_append]
      rw [deliver_one_arg hwt hacts.2, hc]
    exact list_node_derives hwf hq hlhs hk1 hk hdel

/-- The printed text of a canonical term derives at its rule to a tree whose
projection is that term: the term is among the parses of its text. -/
theorem derives_of_prints (hwf : WellFormed G C L) {n : String} {c : CanonicalTerm}
    {toks : List Tok} (h : Prints G C L (.rule n) c toks) :
    ∃ t, Derives G n toks t ∧ canon G C t = some c := by
  obtain ⟨t, hd, w, k?, hw, hc⟩ := printed_of_prints hwf h
  exact ⟨t, hd, by simp only [canon, hw, Option.map_some, hc]⟩

end DerivesOfPrints

/-! ## Settled classifications

From a rule that is not a list rule, the builder passes through transparent
productions until it reaches a production that names the value (a literal or
a constructor), a token class, or a list rule.  The classification is
*settled* when, from every rule, one chain only reaches an end showing a given
head: a literal's text, or the name of a constructor, token class or list.
The implementation's naming pass establishes this by turning the transparent
and literal productions of every sort where two chains meet into
constructors; here a finite check establishes it. -/

section Settled

variable {G : Grammar} {C : Classification} {L : String → Option (ListForm × String)}

/-- Where a chain of transparent productions ends. -/
inductive End where
  | production (p : Production)
  | token (cls : String)
  | list (r : String)
  deriving DecidableEq, Repr

/-- What a value shows at its root. -/
inductive Head where
  | text (s : String)
  | name (s : String)
  | seq
  deriving DecidableEq, Repr

/-- The head of the values an end makes. -/
def End.head (C : Classification) (L : String → Option (ListForm × String)) : End → Head
  | .production p =>
    match C.kind p with
    | .literal s => .text s
    | .constructor n => .name n
    | .list key _ => .name key
    | .transparent => .seq
  | .token cls => .name cls
  | .list r =>
    match L r with
    | some (_, key) => .name key
    | none => .seq

/-- The head of a value. -/
def CanonicalTerm.head : CanonicalTerm → Head
  | .text s => .text s
  | .node n _ => .name n
  | .seq _ => .seq

/-- A chain of transparent productions from a rule that is not a list rule to
its end. -/
inductive TPath (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    String → List Production → End → Prop where
  | stop (q : Production) (hq : q ∈ G.productions) (hL : L q.lhs = none)
      (hk : C.kind q ≠ .transparent) : TPath G C L q.lhs [] (.production q)
  | token (t : Production) (ht : t ∈ G.productions) (hL : L t.lhs = none)
      (hk : C.kind t = .transparent) (cls : String) (hv : t.rhs = [.token cls]) :
      TPath G C L t.lhs [t] (.token cls)
  | list (t : Production) (ht : t ∈ G.productions) (hL : L t.lhs = none)
      (hk : C.kind t = .transparent) (m : String) (hv : t.rhs = [.rule m]) (hm : (L m).isSome) :
      TPath G C L t.lhs [t] (.list m)
  | step (t : Production) (ht : t ∈ G.productions) (hL : L t.lhs = none)
      (hk : C.kind t = .transparent) (m : String) (hv : t.rhs = [.rule m]) (hm : L m = none)
      (chain : List Production) (e : End) (h : TPath G C L m chain e) :
      TPath G C L t.lhs (t :: chain) e

/-- From every rule, chains to ends of one head are one chain to one end. -/
def Settled (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    Prop :=
  ∀ n chain₁ chain₂ e₁ e₂, TPath G C L n chain₁ e₁ → TPath G C L n chain₂ e₂ →
    e₁.head C L = e₂.head C L → chain₁ = chain₂ ∧ e₁ = e₂

/-- The ends one production leads to, given the ends of the rules below. -/
def stepEnds (C : Classification) (L : String → Option (ListForm × String))
    (below : String → List (List Production × End)) (q : Production) :
    List (List Production × End) :=
  match C.kind q with
  | .transparent =>
    match q.rhs with
    | [.token cls] => [([q], .token cls)]
    | [.rule m] =>
      match L m with
      | some _ => [([q], .list m)]
      | none => (below m).map (fun x => (q :: x.1, x.2))
    | _ => []
  | _ => [([], .production q)]

/-- The chains from a rule, with their ends, up to a depth. -/
def ends (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    Nat → String → List (List Production × End)
  | 0, _ => []
  | fuel + 1, n =>
    match L n with
    | some _ => []
    | none => (G.productions.filter (fun q => q.lhs == n)).flatMap
        (stepEnds C L (ends G C L fuel))

/-- Every chain from a rule is shorter than a depth. -/
def deep (G : Grammar) (C : Classification) (L : String → Option (ListForm × String)) :
    Nat → String → Bool
  | 0, _ => false
  | fuel + 1, n =>
    (G.productions.filter (fun q => q.lhs == n)).all (fun q =>
      match C.kind q, q.rhs with
      | .transparent, [.rule m] => (L m).isSome || deep G C L fuel m
      | _, _ => true)

/-- The finite check: from every left-hand side, the chains are shorter than
the depth and their ends show distinct heads. -/
def settledCheck (G : Grammar) (C : Classification) (L : String → Option (ListForm × String))
    (fuel : Nat) : Bool :=
  G.productions.all (fun p => deep G C L fuel p.lhs &&
    decide (((ends G C L fuel p.lhs).map (fun x => x.2.head C L)).Nodup))

theorem mem_filter_lhs {q : Production} (hq : q ∈ G.productions) :
    q ∈ G.productions.filter (fun q' => q'.lhs == q.lhs) :=
  List.mem_filter.2 ⟨hq, string_beq_self _⟩

/-- A chain within the depth is among the enumerated chains. -/
theorem ends_complete : ∀ {n chain e}, TPath G C L n chain e →
    ∀ fuel, deep G C L fuel n = true → (chain, e) ∈ ends G C L fuel n := by
  intro n chain e h
  induction h with
  | stop q hq hL hk =>
    intro fuel hdeep
    cases fuel with
    | zero => simp [deep] at hdeep
    | succ fuel =>
      simp only [ends, hL]
      refine List.mem_flatMap.2 ⟨q, mem_filter_lhs hq, ?_⟩
      unfold stepEnds
      cases hkq : C.kind q with
      | transparent => exact absurd hkq hk
      | _ => exact List.mem_singleton_self _
  | token t ht hL hk cls hv =>
    intro fuel hdeep
    cases fuel with
    | zero => simp [deep] at hdeep
    | succ fuel =>
      simp only [ends, hL]
      refine List.mem_flatMap.2 ⟨t, mem_filter_lhs ht, ?_⟩
      unfold stepEnds
      rw [hk, hv]
      exact List.mem_singleton_self _
  | list t ht hL hk m hv hm =>
    intro fuel hdeep
    cases fuel with
    | zero => simp [deep] at hdeep
    | succ fuel =>
      simp only [ends, hL]
      refine List.mem_flatMap.2 ⟨t, mem_filter_lhs ht, ?_⟩
      unfold stepEnds
      rw [hk, hv]
      obtain ⟨fk, hfk⟩ := Option.isSome_iff_exists.1 hm
      simp only [hfk, List.mem_singleton]
  | step t ht hL hk m hv hm chain e _ ih =>
    intro fuel hdeep
    cases fuel with
    | zero => simp [deep] at hdeep
    | succ fuel =>
      have hdm : deep G C L fuel m = true := by
        have := List.all_eq_true.1 hdeep t (mem_filter_lhs ht)
        simp only [hk, hv, hm, Option.isSome_none, Bool.false_or] at this
        exact this
      simp only [ends, hL]
      refine List.mem_flatMap.2 ⟨t, mem_filter_lhs ht, ?_⟩
      unfold stepEnds
      rw [hk, hv]
      simp only [hm]
      exact List.mem_map.2 ⟨(chain, e), ih fuel hdm, rfl⟩

/-- A chain starts at the left-hand side of a production. -/
theorem TPath.lhs_mem {n : String} {chain : List Production} {e : End}
    (h : TPath G C L n chain e) : ∃ p ∈ G.productions, p.lhs = n := by
  cases h with
  | stop q hq _ _ => exact ⟨q, hq, rfl⟩
  | token t ht _ _ _ _ => exact ⟨t, ht, rfl⟩
  | list t ht _ _ _ _ _ => exact ⟨t, ht, rfl⟩
  | step t ht _ _ _ _ _ _ _ _ => exact ⟨t, ht, rfl⟩

/-- The finite check establishes a settled classification. -/
theorem settled_of_check {fuel : Nat} (h : settledCheck G C L fuel = true) : Settled G C L := by
  intro n chain₁ chain₂ e₁ e₂ h₁ h₂ hhead
  obtain ⟨p, hp, rfl⟩ := h₁.lhs_mem
  have hc := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hdeep, hnodup⟩ := hc
  have hm₁ := ends_complete h₁ fuel hdeep
  have hm₂ := ends_complete h₂ fuel hdeep
  have := List.inj_on_of_nodup_map hnodup hm₁ hm₂ hhead
  simp only [Prod.mk.injEq] at this
  exact this

/-! ### Chains in derivations -/

mutual

/-- The height of a derivation tree. -/
def Tree.height : Tree → Nat
  | .leaf _ _ => 0
  | .node _ kids => Tree.heights kids + 1

/-- The greatest height of a list of trees. -/
def Tree.heights : List Tree → Nat
  | [] => 0
  | t :: ts => max (Tree.height t) (Tree.heights ts)

end

theorem Tree.height_le_heights {t : Tree} : ∀ {ts : List Tree}, t ∈ ts → t.height ≤ Tree.heights ts
  | _ :: _, .head _ => by simp only [Tree.heights]; omega
  | _ :: _, .tail _ h => by
    have := Tree.height_le_heights h
    simp only [Tree.heights]
    omega

theorem Tree.height_kid {t : Tree} {label : String} {kids : List Tree} (h : t ∈ kids) :
    t.height < (Tree.node label kids).height := by
  have := Tree.height_le_heights h
  simp only [Tree.height]
  omega

/-- A tree along a chain of transparent productions. -/
def wrap : List Production → Tree → Tree
  | [], x => x
  | t :: chain, x => .node t.label [wrap chain x]

/-- What an end derives: a production's node over derived items, a token's
leaf, or a list rule's derivation. -/
def EndDerives (G : Grammar) : End → Tree → Prop
  | .production q, x => ∃ sub kids, x = .node q.label kids ∧ DerivesItems G q.rhs sub kids
  | .token cls, x => ∃ s, x = .leaf cls s
  | .list m, x => ∃ sub, Derives G m sub x

/-- A derivation at a rule that is not a list rule is a chain of transparent
productions over its end, and its value is the end's value delivered as an
argument. -/
theorem path_of_derives (hwf : WellFormed G C L) :
    ∀ {n toks t}, Derives G n toks t → L n = none →
      ∃ chain e x, TPath G C L n chain e ∧ t = wrap chain x ∧ EndDerives G e x ∧
        x.height ≤ t.height ∧ (chain ≠ [] → x.height < t.height) ∧
        finishTree G C t = (finishTree G C x).map (fun r => (named r.2 r.1, none)) := by
  refine Derives.induction_with
    (fun n _ t => L n = none → ∃ chain e x, TPath G C L n chain e ∧ t = wrap chain x ∧
      EndDerives G e x ∧ x.height ≤ t.height ∧ (chain ≠ [] → x.height < t.height) ∧
      finishTree G C t = (finishTree G C x).map (fun r => (named r.2 r.1, none))) ?_
  intro p hp toks kids hitems hw hL
  cases hk : C.kind p with
  | transparent =>
    obtain ⟨v, hrhs, hvv, ha0⟩ := hwf.transparent p hp hk
    rw [hrhs] at hw
    obtain ⟨k, kids', sub, toks', rfl, rfl, hw', hkid⟩ := items_head hvv hw
    cases hw'
    have hfin : finishTree G C (.node p.label [k]) =
        (finishTree G C k).map (fun r => (named r.2 r.1, none)) := by
      rw [finishTree_node hwf hp]
      cases hwk : finishTree G C k with
      | none =>
        rw [deliverKids_cons, hwk]
        rfl
      | some r =>
        obtain ⟨w, k?⟩ := r
        rw [deliver_one_arg hwk ha0]
        simp only [List.nil_append, hk, finish, Option.map_some, Kind.key?]
    have hkh : k.height < (Tree.node p.label [k]).height := Tree.height_kid List.mem_cons_self
    rcases hkid with ⟨m, rfl, hdm, ih⟩ | ⟨cls, s, rfl, rfl, rfl, _⟩
    · cases hLm : L m with
      | some fk =>
        refine ⟨[p], .list m, k, .list p hp hL hk m hrhs (by rw [hLm]; rfl), rfl, ⟨sub, hdm⟩,
          Nat.le_of_lt hkh, fun _ => hkh, hfin⟩
      | none =>
        obtain ⟨chain, e, x, hpath, rfl, hend, hxh, _, hxfin⟩ := ih hLm
        refine ⟨p :: chain, e, x, .step p hp hL hk m hrhs hLm chain e hpath, rfl, hend,
          by omega, fun _ => by omega, ?_⟩
        rw [hfin, hxfin]
        cases finishTree G C x <;> rfl
    · exact ⟨[p], .token cls, .leaf cls s, .token p hp hL hk cls hrhs, rfl, ⟨s, rfl⟩,
        Nat.le_of_lt hkh, fun _ => hkh, hfin⟩
  | list key text =>
    have := hwf.list p hp key text hk
    rw [hL] at this
    cases this
  | _ =>
    refine ⟨[], .production p, .node p.label kids, .stop p hp hL (by rw [hk]; simp), rfl,
      ⟨toks, kids, rfl, hitems⟩, Nat.le_refl _, fun h => absurd rfl h, ?_⟩
    rw [finishTree_node hwf hp]
    cases deliverKids G C p 0 [] kids with
    | none => rfl
    | some vals =>
      simp only [hk]
      cases h : finish _ vals <;> simp [Kind.key?, named]

/-! ### What children deliver -/

theorem derives_inv {n : String} {toks : List Tok} {t : Tree} (h : Derives G n toks t) :
    ∃ q kids, q ∈ G.productions ∧ q.lhs = n ∧ t = .node q.label kids ∧
      DerivesItems G q.rhs toks kids := by
  cases h with
  | node q hq toks kids h => exact ⟨q, kids, hq, rfl, rfl, h⟩

theorem items_finishing (hwf : WellFormed G C L) :
    ∀ {rhs : List Sym} {toks : List Tok} {kids : List Tree}, DerivesItems G rhs toks kids →
      ItemsWith G (FinishesAt G C L) rhs toks kids
  | _, _, _, .nil => .nil
  | _, _, _, .fixed t rest toks kids h => .fixed t rest toks kids (items_finishing hwf h)
  | _, _, _, .token cls s hs rest toks kids h =>
    .token cls s hs rest toks kids (items_finishing hwf h)
  | _, _, _, .rule n sub t hsub rest toks kids h =>
    .rule n sub t hsub (finishes hwf hsub) rest toks kids (items_finishing hwf h)

theorem named_inj {k? : Option String} {w₁ w₂ : CanonicalTerm} (h : named k? w₁ = named k? w₂) :
    w₁ = w₂ := by
  cases k? with
  | none => exact h
  | some key =>
    simp only [named, CanonicalTerm.node.injEq, List.cons.injEq, and_true, true_and] at h
    exact h

/-- The arguments a constructor's children deliver from a value position on: a
value child its value, and a value child followed by an extension one list node
of the extension's key with the child's value before the extension's list. -/
inductive Delivers (G : Grammar) (C : Classification) (p : Production) :
    Nat → List Sym → List Tree → List CanonicalTerm → Prop where
  | nil (i : Nat) : Delivers G C p i [] [] []
  | fixed (i : Nat) (t : String) (rest : List Sym) (kids : List Tree) (args : List CanonicalTerm)
      (h : Delivers G C p i rest kids args) : Delivers G C p i (.fixed t :: rest) kids args
  | value (i : Nat) (v : Sym) (hv : v.isValue = true) (rest : List Sym)
      (hnext : C.action p (i + 1) ≠ .extend) (k : Tree) (w : CanonicalTerm) (k? : Option String)
      (hw : finishTree G C k = some (w, k?)) (kids : List Tree) (args : List CanonicalTerm)
      (h : Delivers G C p (i + 1) rest kids args) :
      Delivers G C p i (v :: rest) (k :: kids) (named k? w :: args)
  | extended (i : Nat) (v : Sym) (hv : v.isValue = true) (hr : String) (rest : List Sym)
      (hext : C.action p (i + 1) = .extend) (k : Tree) (w : CanonicalTerm) (k? : Option String)
      (hw : finishTree G C k = some (w, k?)) (kh : Tree) (es : List CanonicalTerm) (key : String)
      (hh : finishTree G C kh = some (.seq es, some key)) (hnext : C.action p (i + 2) ≠ .extend)
      (kids : List Tree) (args : List CanonicalTerm) (h : Delivers G C p (i + 2) rest kids args) :
      Delivers G C p i (v :: .rule hr :: rest) (k :: kh :: kids)
        (.node key [.seq (named k? w :: es)] :: args)

/-- A constructor's children, from a value position that is not an extension,
deliver their arguments after the values delivered so far. -/
theorem delivers_walk (hwf : WellFormed G C L) {p : Production} (hp : p ∈ G.productions)
    {n : String} (hkind : C.kind p = .constructor n) :
    ∀ (N : Nat) (rest : List Sym), rest.length ≤ N →
    ∀ (i : Nat) (pre : List Sym) (toks : List Tok) (kids : List Tree),
      p.rhs = pre ++ rest → (values pre).length = i → C.action p i ≠ .extend →
      ItemsWith G (FinishesAt G C L) rest toks kids →
      ∀ vals vals', deliverKids G C p i vals kids = some vals' →
        ∃ args, vals' = vals ++ args ∧ Delivers G C p i rest kids args := by
  intro N
  induction N with
  | zero =>
    intro rest hlen i _ _ _ _ _ _ hw vals vals' hd
    obtain rfl := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
    cases hw
    rw [deliverKids_nil] at hd
    injection hd with hd
    subst hd
    exact ⟨[], by simp, .nil i⟩
  | succ N ih =>
    intro rest hlen i pre toks kids hrhs hpre hne hw vals vals' hd
    rcases rest with _ | ⟨v, rest⟩
    · cases hw
      rw [deliverKids_nil] at hd
      injection hd with hd
      subst hd
      exact ⟨[], by simp, .nil i⟩
    have hlen' : rest.length ≤ N := by simp at hlen; omega
    cases hvf : v.isValue with
    | false =>
      cases v with
      | fixed t =>
        cases hw with
        | fixed _ _ toks' _ hw1 =>
          obtain ⟨args, h1, h2⟩ := ih rest hlen' i (pre ++ [.fixed t]) toks' kids
            (by rw [hrhs]; simp) (by rw [values_append, values_fixed, values_nil]; simpa using hpre)
            hne hw1 vals vals' hd
          exact ⟨args, h1, .fixed i t rest kids args h2⟩
      | _ => simp [Sym.isValue] at hvf
    | true =>
      obtain ⟨t, kids1, sub, toks1, rfl, rfl, hw1, hkid⟩ := items_head hvf hw
      have hkf : KidFinishes G C L v t := by
        rcases hkid with ⟨m, rfl, _, hP⟩ | ⟨cls, s, rfl, rfl, rfl, _⟩
        · exact hP
        · exact ⟨s, rfl⟩
      obtain ⟨w, k?, hwt, _⟩ := kid_finishTree hkf
      have harg : C.action p i = .arg := by
        rcases hwf.constructor p hp n hkind i with h | ⟨h, _⟩
        · exact h
        · exact absurd h hne
      rw [deliverKids_cons, hwt] at hd
      simp only [] at hd
      rw [harg, deliver_arg] at hd
      simp only [] at hd
      by_cases hext : C.action p (i + 1) = .extend
      · obtain ⟨j, hj, pre', x, h, rest2, hsplit, hpre', hx, _, b, key, hform⟩ :
            ∃ j, i + 1 = j + 1 ∧ ∃ pre' x h rest2, p.rhs = pre' ++ x :: .rule h :: rest2 ∧
              (values pre').length = j ∧ x.isValue = true ∧ C.action p j ≠ .extend ∧
              ∃ b key, (L h = some (.star b, key) ∨ L h = some (.plus b, key)) := by
          rcases hwf.constructor p hp n hkind (i + 1) with h | ⟨_, j, hj, hat⟩
          · rw [hext] at h
            cases h
          · obtain ⟨pre', x, h, rest2, h1, h2, h3, h4, h5⟩ := hat
            exact ⟨j, hj, pre', x, h, rest2, h1, h2, h3, h4, h5⟩
        have hji : i = j := by omega
        subst hji
        obtain ⟨_, hvx, hrest⟩ := split_unique pre pre' hvf hx (hrhs.symm.trans hsplit)
          (by rw [hpre, hpre'])
        subst hrest
        subst hvx
        obtain ⟨th, kids2, subh, toks2, rfl, rfl, hw2, hkidh⟩ := items_head rfl hw1
        rcases hkidh with ⟨m, hm, _, hPh⟩ | ⟨_, _, hm, _⟩
        · cases hm
          have hL : ∃ f, L h = some (f, key) := by
            rcases hform with hf | hf <;> exact ⟨_, hf⟩
          obtain ⟨f, hf⟩ := hL
          obtain ⟨wh, kh, hwh, hfinh⟩ := hPh
          unfold Finished at hfinh
          rw [hf] at hfinh
          obtain ⟨rfl, es, rfl⟩ := hfinh
          rw [deliverKids_cons, hwh] at hd
          simp only [] at hd
          rw [hext] at hd
          have hmerge : deliver (some key) .extend (vals ++ [named k? w]) (.seq es) =
              some (vals ++ [.node key [.seq (named k? w :: es)]]) := by
            simp only [deliver, List.getLast?_append, List.getLast?_singleton, Option.some_or,
              List.dropLast_concat]
          rw [hmerge] at hd
          simp only [] at hd
          have hnext2 : C.action p (i + 1 + 1) ≠ .extend := by
            intro h2
            rcases hwf.constructor p hp n hkind (i + 1 + 1) with h' | ⟨_, j, hj, hat⟩
            · rw [h2] at h'
              cases h'
            · obtain ⟨_, _, _, _, _, _, _, hne', _⟩ := hat
              have : j = i + 1 := by omega
              subst this
              exact hne' hext
          obtain ⟨args, h1, h2⟩ := ih rest2 (by simp at hlen'; omega) (i + 1 + 1)
            (pre ++ [v, .rule h]) toks2 kids2
            (by rw [hrhs]; simp) (by
              rw [values_append, values_value hvf, values_value (x := .rule h) rfl, values_nil]
              simp [hpre])
            hnext2 hw2 _ vals' hd
          refine ⟨.node key [.seq (named k? w :: es)] :: args, by rw [h1]; simp, ?_⟩
          exact .extended i v hvf h rest2 hext t w k? hwt th es key hwh hnext2 kids2 args h2
        · cases hm
      · obtain ⟨args, h1, h2⟩ := ih rest hlen' (i + 1) (pre ++ [v]) toks1 kids1
          (by rw [hrhs]; simp) (by rw [values_append, values_value hvf, values_nil]; simp [hpre])
          hext hw1 _ vals' hd
        exact ⟨named k? w :: args, by rw [h1]; simp, .value i v hvf rest hext t w k? hwt kids1 args h2⟩

/-- A child at a value symbol finishes with the key its symbol fixes. -/
theorem kid_key (hwf : WellFormed G C L) {v : Sym} {rest : List Sym} {toks : List Tok}
    {k : Tree} {kids : List Tree} (hv : v.isValue = true)
    (h : DerivesItems G (v :: rest) toks (k :: kids)) {w : CanonicalTerm} {k? : Option String}
    (hw : finishTree G C k = some (w, k?)) :
    (∃ m sub, v = .rule m ∧ Derives G m sub k ∧ Finished L m w k?) ∨
      (∃ cls s, v = .token cls ∧ k = .leaf cls s ∧ k? = none ∧ w = .node cls [.text s]) := by
  cases h with
  | fixed _ _ _ _ _ => simp [Sym.isValue] at hv
  | token cls s _ _ _ _ _ =>
    rw [finishTree_leaf] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    exact .inr ⟨cls, s, rfl, rfl, hw.2.symm, hw.1.symm⟩
  | rule m sub _ hsub _ _ _ _ =>
    obtain ⟨w', k', hw', hfin⟩ := finishes hwf hsub
    rw [hw] at hw'
    simp only [Option.some.injEq, Prod.mk.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    exact .inl ⟨m, sub, rfl, hsub, hfin⟩

/-- Finished values at one rule carry one key. -/
theorem finished_key {n : String} {w₁ w₂ : CanonicalTerm} {k₁ k₂ : Option String}
    (h₁ : Finished L n w₁ k₁) (h₂ : Finished L n w₂ k₂) : k₁ = k₂ := by
  unfold Finished at h₁ h₂
  cases hL : L n with
  | none =>
    rw [hL] at h₁ h₂
    rw [h₁.1, h₂.1]
  | some fk =>
    obtain ⟨f, key⟩ := fk
    rw [hL] at h₁ h₂
    rw [h₁.1, h₂.1]

/-- A child at a value symbol is determined by the value it delivers, when a
rule child is determined by its value. -/
theorem kid_inj (hwf : WellFormed G C L) {v : Sym} (hv : v.isValue = true)
    {rest₁ rest₂ : List Sym} {toks₁ toks₂ : List Tok} {k₁ k₂ : Tree} {kids₁ kids₂ : List Tree}
    (hd₁ : DerivesItems G (v :: rest₁) toks₁ (k₁ :: kids₁))
    (hd₂ : DerivesItems G (v :: rest₂) toks₂ (k₂ :: kids₂))
    {w₁ w₂ : CanonicalTerm} {k₁? k₂? : Option String}
    (hw₁ : finishTree G C k₁ = some (w₁, k₁?)) (hw₂ : finishTree G C k₂ = some (w₂, k₂?))
    (hnamed : named k₁? w₁ = named k₂? w₂)
    (hih : ∀ k' m sub₁ sub₂, Derives G m sub₁ k₁ → Derives G m sub₂ k' →
      finishTree G C k₁ = finishTree G C k' → k₁ = k') : k₁ = k₂ := by
  rcases kid_key hwf hv hd₁ hw₁ with ⟨m, sub, rfl, hdm, hfin⟩ | ⟨cls, s, rfl, rfl, rfl, rfl⟩
  · rcases kid_key hwf hv hd₂ hw₂ with ⟨m', sub', hmm, hdm', hfin'⟩ | ⟨_, _, hmm, _⟩
    · cases hmm
      obtain rfl := finished_key hfin hfin'
      obtain rfl := named_inj hnamed
      exact hih k₂ m sub sub' hdm hdm' (by rw [hw₁, hw₂])
    · cases hmm
  · rcases kid_key hwf hv hd₂ hw₂ with ⟨_, _, hmm, _⟩ | ⟨cls', s', hmm, rfl, rfl, rfl⟩
    · cases hmm
    · cases hmm
      simp only [named, CanonicalTerm.node.injEq, List.cons.injEq, CanonicalTerm.text.injEq,
        and_true, true_and] at hnamed
      rw [hnamed]

/-- Children delivering one list of arguments at one right-hand side are one
list of children, when each rule child is determined by its value. -/
theorem delivers_inj (hwf : WellFormed G C L) {p : Production} :
    ∀ {i : Nat} {rest : List Sym} {kids₁ kids₂ : List Tree} {args : List CanonicalTerm}
      {toks₁ toks₂ : List Tok},
      Delivers G C p i rest kids₁ args → ∀ {args₂ : List CanonicalTerm},
      Delivers G C p i rest kids₂ args₂ → args = args₂ →
      DerivesItems G rest toks₁ kids₁ → DerivesItems G rest toks₂ kids₂ →
      (∀ k₁ ∈ kids₁, ∀ k₂ m sub₁ sub₂, Derives G m sub₁ k₁ → Derives G m sub₂ k₂ →
        finishTree G C k₁ = finishTree G C k₂ → k₁ = k₂) →
      kids₁ = kids₂ := by
  intro i rest kids₁ kids₂ args toks₁ toks₂ h₁
  induction h₁ generalizing kids₂ toks₁ toks₂ with
  | nil i =>
    intro _ h₂ _ _ _ _
    cases h₂
    rfl
  | fixed i t rest kids args _ ih =>
    intro _ h₂ hargs hd₁ hd₂ hih
    cases h₂ with
    | fixed _ _ _ _ _ h₂ =>
      cases hd₁ with
      | fixed _ _ _ _ hd₁ =>
        cases hd₂ with
        | fixed _ _ _ _ hd₂ => exact ih h₂ hargs hd₁ hd₂ hih
    | value _ _ hv => simp [Sym.isValue] at hv
    | extended _ _ hv => simp [Sym.isValue] at hv
  | value i v hv rest hnext k w k? hw kids args _ ih =>
    intro _ h₂ hargs hd₁ hd₂ hih
    cases h₂ with
    | value _ _ _ _ _ k' w' k'? hw' kids' args' h₂ =>
      simp only [List.cons.injEq] at hargs
      obtain ⟨hnamed, hargs⟩ := hargs
      have hkk : k = k' := kid_inj hwf hv hd₁ hd₂ hw hw' hnamed (hih k List.mem_cons_self)
      subst hkk
      cases hd₁ with
      | token _ _ _ _ _ _ hd₁ =>
        cases hd₂ with
        | token _ _ _ _ _ _ hd₂ =>
          rw [ih h₂ hargs hd₁ hd₂ (fun k₁ hk₁ => hih k₁ (List.mem_cons_of_mem _ hk₁))]
      | rule _ _ _ _ _ _ _ hd₁ =>
        cases hd₂ with
        | rule _ _ _ _ _ _ _ hd₂ =>
          rw [ih h₂ hargs hd₁ hd₂ (fun k₁ hk₁ => hih k₁ (List.mem_cons_of_mem _ hk₁))]
      | fixed _ _ _ _ _ => simp [Sym.isValue] at hv
    | extended _ _ _ _ _ hext => exact absurd hext hnext
    | fixed => simp [Sym.isValue] at hv
  | extended i v hv hr rest hext k w k? hw kh es key hh hnext kids args _ ih =>
    intro _ h₂ hargs hd₁ hd₂ hih
    cases h₂ with
    | fixed => simp [Sym.isValue] at hv
    | value _ _ _ _ hnext' => exact absurd hext hnext'
    | extended _ _ _ _ _ _ k' w' k'? hw' kh' es' key' hh' _ kids' args' h₂ =>
      simp only [List.cons.injEq, CanonicalTerm.node.injEq, CanonicalTerm.seq.injEq, and_true]
        at hargs
      obtain ⟨⟨rfl, hnamed, rfl⟩, hargs⟩ := hargs
      have hkk : k = k' := kid_inj hwf hv hd₁ hd₂ hw hw' hnamed (hih k List.mem_cons_self)
      subst hkk
      have hrest₁ : ∃ subh toks', DerivesItems G (.rule hr :: rest) (subh ++ toks') (kh :: kids) ∧
          Derives G hr subh kh ∧ DerivesItems G rest toks' kids := by
        cases hd₁ with
        | token _ _ _ _ _ _ hd₁ =>
          cases hd₁ with
          | rule _ subh _ hsub _ toks' _ h => exact ⟨subh, toks', .rule hr subh kh hsub rest toks' kids h, hsub, h⟩
        | rule _ _ _ _ _ _ _ hd₁ =>
          cases hd₁ with
          | rule _ subh _ hsub _ toks' _ h => exact ⟨subh, toks', .rule hr subh kh hsub rest toks' kids h, hsub, h⟩
        | fixed _ _ _ _ _ => simp [Sym.isValue] at hv
      have hrest₂ : ∃ subh toks', Derives G hr subh kh' ∧ DerivesItems G rest toks' kids' := by
        cases hd₂ with
        | token _ _ _ _ _ _ hd₂ =>
          cases hd₂ with
          | rule _ subh _ hsub _ toks' _ h => exact ⟨subh, toks', hsub, h⟩
        | rule _ _ _ _ _ _ _ hd₂ =>
          cases hd₂ with
          | rule _ subh _ hsub _ toks' _ h => exact ⟨subh, toks', hsub, h⟩
        | fixed _ _ _ _ _ => simp [Sym.isValue] at hv
      obtain ⟨subh, toks', _, hdh, hdr⟩ := hrest₁
      obtain ⟨subh', toks'', hdh', hdr'⟩ := hrest₂
      have hkh : kh = kh' :=
        hih kh (List.mem_cons_of_mem _ List.mem_cons_self) kh' hr subh subh' hdh hdh'
          (by rw [hh, hh'])
      subst hkh
      rw [ih h₂ hargs hdr hdr' (fun k₁ hk₁ =>
        hih k₁ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hk₁)))]

/-! ### The lists of list rules -/

/-- An element of a list at its body symbol: a value child's value, or a fixed
body's text with no child. -/
inductive Element (G : Grammar) (C : Classification) : Sym → List Tree → CanonicalTerm → Prop where
  | value (b : Sym) (hb : b.isValue = true) (k : Tree) (w : CanonicalTerm) (k? : Option String)
      (hw : finishTree G C k = some (w, k?)) (sub : List Tok) (hd : DerivesItems G [b] sub [k]) :
      Element G C b [k] (named k? w)
  | fixed (t : String) : Element G C (.fixed t) [] (.text t)

/-- The list a list production's node makes, by the rule's form: its
right-hand side, its children and its elements. -/
inductive ListShape (G : Grammar) (C : Classification) (r key : String) :
    ListForm → List Sym → List Tree → List CanonicalTerm → Prop where
  | optionNone (b : Sym) : ListShape G C r key (.option b) [] [] []
  | optionSome (b : Sym) (kids : List Tree) (e : CanonicalTerm) (h : Element G C b kids e) :
      ListShape G C r key (.option b) [b] kids [e]
  | starNil (b : Sym) : ListShape G C r key (.star b) [] [] []
  | starSnoc (b : Sym) (tr : Tree) (esr : List CanonicalTerm) (sub : List Tok)
      (hdr : Derives G r sub tr) (hr : finishTree G C tr = some (.seq esr, some key))
      (kids : List Tree) (e : CanonicalTerm) (h : Element G C b kids e) :
      ListShape G C r key (.star b) [.rule r, b] (tr :: kids) (esr ++ [e])
  | plusOne (b : Sym) (kids : List Tree) (e : CanonicalTerm) (h : Element G C b kids e) :
      ListShape G C r key (.plus b) [b] kids [e]
  | plusSnoc (b : Sym) (tr : Tree) (esr : List CanonicalTerm) (sub : List Tok)
      (hdr : Derives G r sub tr) (hr : finishTree G C tr = some (.seq esr, some key))
      (kids : List Tree) (e : CanonicalTerm) (h : Element G C b kids e) :
      ListShape G C r key (.plus b) [.rule r, b] (tr :: kids) (esr ++ [e])
  | sepOne (x : Sym) (sep : List String) (right : Bool) (kids : List Tree) (e : CanonicalTerm)
      (h : Element G C x kids e) : ListShape G C r key (.separated x sep right) [x] kids [e]
  | sepCons (x : Sym) (sep : List String) (kids : List Tree) (e : CanonicalTerm)
      (h : Element G C x kids e) (tr : Tree) (esr : List CanonicalTerm) (sub : List Tok)
      (hdr : Derives G r sub tr) (hr : finishTree G C tr = some (.seq esr, some key)) :
      ListShape G C r key (.separated x sep true) (x :: fixedSyms sep ++ [.rule r])
        (kids ++ [tr]) (e :: esr)
  | sepSnoc (x : Sym) (sep : List String) (tr : Tree) (esr : List CanonicalTerm) (sub : List Tok)
      (hdr : Derives G r sub tr) (hr : finishTree G C tr = some (.seq esr, some key))
      (kids : List Tree) (e : CanonicalTerm) (h : Element G C x kids e) :
      ListShape G C r key (.separated x sep false) (.rule r :: fixedSyms sep ++ [x])
        (tr :: kids) (esr ++ [e])

/-- A one-symbol body over its derived items is an element. -/
theorem element_of_items (hwf : WellFormed G C L) {b : Sym} {toks : List Tok} {kids : List Tree}
    (hd : DerivesItems G [b] toks kids) :
    (b.isValue = true → ∃ k w k?, kids = [k] ∧ finishTree G C k = some (w, k?) ∧
      Element G C b [k] (named k? w)) ∧
    (∀ t, b = .fixed t → kids = [] ∧ Element G C b [] (.text t)) := by
  refine ⟨fun hb => ?_, fun t ht => ?_⟩
  · have hw := items_finishing hwf hd
    obtain ⟨k, kids', sub, toks', rfl, rfl, hw', hkid⟩ := items_head hb hw
    cases hw'
    have hkf : KidFinishes G C L b k := by
      rcases hkid with ⟨m, rfl, _, hP⟩ | ⟨cls, s, rfl, rfl, rfl, _⟩
      · exact hP
      · exact ⟨s, rfl⟩
    obtain ⟨w, k?, hwk, _⟩ := kid_finishTree hkf
    exact ⟨k, w, k?, rfl, hwk, .value b hb k w k? hwk _ (by simpa using hd)⟩
  · subst ht
    cases hd with
    | fixed _ _ _ _ h =>
      cases h
      exact ⟨rfl, .fixed t⟩

theorem derivesItems_fixedSyms_inv :
    ∀ (sep : List String) {rest : List Sym} {toks : List Tok} {kids : List Tree},
      DerivesItems G (fixedSyms sep ++ rest) toks kids →
      ∃ toks', toks = fixedToks sep ++ toks' ∧ DerivesItems G rest toks' kids
  | [], _, _, _, h => ⟨_, rfl, h⟩
  | t :: sep, _, _, _, h => by
    cases h with
    | fixed _ _ toks' _ h' =>
      obtain ⟨toks'', rfl, h''⟩ := derivesItems_fixedSyms_inv sep h'
      exact ⟨toks'', rfl, h''⟩

/-- The items of a right-hand side starting with a value symbol: its first
child derives at the symbol alone. -/
theorem items_split_value {x : Sym} (hx : x.isValue = true) {rest : List Sym} {toks : List Tok}
    {kids : List Tree} (hd : DerivesItems G (x :: rest) toks kids) :
    ∃ k kids' sub toks', kids = k :: kids' ∧ toks = sub ++ toks' ∧
      DerivesItems G [x] sub [k] ∧ DerivesItems G rest toks' kids' := by
  cases hd with
  | fixed _ _ _ _ _ => simp [Sym.isValue] at hx
  | token cls s hs _ toks' kids' h =>
    exact ⟨_, kids', [.lexeme cls s], toks', rfl, rfl, .token cls s hs [] [] [] .nil, h⟩
  | rule m sub k hsub _ toks' kids' h =>
    have hk : DerivesItems G [.rule m] (sub ++ []) [k] := .rule m sub k hsub [] [] [] .nil
    rw [List.append_nil] at hk
    exact ⟨k, kids', sub, toks', rfl, rfl, hk, h⟩

/-- A spliced list child at a list rule: its derivation and list. -/
theorem splice_kid (hwf : WellFormed G C L) {r : String} {f : ListForm} {key : String}
    (hL : L r = some (f, key)) {rest : List Sym} {toks : List Tok} {tr : Tree} {kids : List Tree}
    (hd : DerivesItems G (.rule r :: rest) toks (tr :: kids)) :
    ∃ sub toks' esr, toks = sub ++ toks' ∧ Derives G r sub tr ∧
      finishTree G C tr = some (.seq esr, some key) ∧ DerivesItems G rest toks' kids := by
  cases hd with
  | rule _ sub _ hsub _ toks' _ h =>
    obtain ⟨w, k, hw, hfin⟩ := finishes hwf hsub
    unfold Finished at hfin
    rw [hL] at hfin
    obtain ⟨rfl, esr, rfl⟩ := hfin
    exact ⟨sub, toks', esr, rfl, hsub, hw, h⟩

/-- Every list production's node makes a list of the rule's form. -/
theorem list_shape (hwf : WellFormed G C L) {q : Production} (hq : q ∈ G.productions)
    {f : ListForm} {key : String} (hL : L q.lhs = some (f, key)) {toks : List Tok}
    {kids : List Tree} (hd : DerivesItems G q.rhs toks kids) {v : CanonicalTerm}
    {k? : Option String} (hfin : finishTree G C (.node q.label kids) = some (v, k?)) :
    ∃ es, v = .seq es ∧ k? = some key ∧ ListShape G C q.lhs key f q.rhs kids es := by
  obtain ⟨hrhs, hspec⟩ := (hwf.rule q.lhs f key hL).1 q hq rfl
  -- the node's value from its delivered values and the production's kind
  have hnode : ∀ text vals, C.kind q = .list key text →
      deliverKids G C q 0 [] kids = some vals → v = .seq (arrange text vals) ∧ k? = some key := by
    intro text vals hk hdel
    rw [finishTree_list_node hwf hq hk hdel] at hfin
    simp only [Option.some.injEq, Prod.mk.injEq] at hfin
    exact ⟨hfin.1.symm, hfin.2.symm⟩
  cases f with
  | option b =>
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, h0, h1, _⟩ := hspec
    simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
    rcases hrhs with h | h
    · rw [h] at hd
      cases hd
      obtain ⟨rfl, rfl⟩ := hnode none [] (h0 h) (deliverKids_nil q 0 [])
      exact ⟨[], rfl, rfl, h ▸ .optionNone b⟩
    · rw [h] at hd
      obtain ⟨hval, hfix⟩ := element_of_items hwf hd
      cases hb : b.isValue
      · cases b with
        | fixed t =>
          obtain ⟨rfl, he⟩ := hfix t rfl
          obtain ⟨rfl, rfl⟩ := hnode _ [] ((h1 h).2 t rfl) (deliverKids_nil q 0 [])
          exact ⟨[.text t], rfl, rfl, h ▸ .optionSome _ [] _ he⟩
        | _ => simp [Sym.isValue] at hb
      · obtain ⟨k, w, k'?, rfl, hwk, he⟩ := hval hb
        obtain ⟨hk, ha⟩ := (h1 h).1 hb
        obtain ⟨rfl, rfl⟩ := hnode none _ hk (deliver_one_arg hwk ha)
        exact ⟨[named k'? w], rfl, rfl, h ▸ .optionSome _ [k] _ he⟩
  | star b =>
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, h0, _, h2⟩ := hspec
    simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
    rcases hrhs with h | h
    · rw [h] at hd
      cases hd
      obtain ⟨rfl, rfl⟩ := hnode none [] (h0 h) (deliverKids_nil q 0 [])
      exact ⟨[], rfl, rfl, h ▸ .starNil b⟩
    · obtain ⟨hs0, hval, hfix⟩ := h2 h
      rw [h] at hd
      cases kids with
      | nil => cases hd
      | cons tr kids =>
        obtain ⟨sub, toks', esr, rfl, hdr, hwr, hd'⟩ := splice_kid hwf hL hd
        obtain ⟨hv, hf⟩ := element_of_items hwf hd'
        cases hb : b.isValue
        · cases b with
          | fixed t =>
            obtain ⟨rfl, he⟩ := hf t rfl
            obtain ⟨rfl, rfl⟩ := hnode _ esr (hfix t rfl) (by
              rw [deliver_splice hwr hs0, deliverKids_nil, List.nil_append])
            exact ⟨esr ++ [.text t], rfl, rfl, h ▸ .starSnoc _ tr esr sub hdr hwr [] _ he⟩
          | _ => simp [Sym.isValue] at hb
        · obtain ⟨k, w, k'?, rfl, hwk, he⟩ := hv hb
          obtain ⟨hk, ha⟩ := hval hb
          obtain ⟨rfl, rfl⟩ := hnode none (esr ++ [named k'? w]) hk (by
            rw [deliver_splice hwr hs0]
            simp only [List.nil_append]
            rw [deliver_one_arg hwk ha])
          exact ⟨esr ++ [named k'? w], rfl, rfl, h ▸ .starSnoc _ tr esr sub hdr hwr [k] _ he⟩
  | plus b =>
    simp only [ListForm.Spec] at hspec
    obtain ⟨_, _, h1, h2⟩ := hspec
    simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
    rcases hrhs with h | h
    · rw [h] at hd
      obtain ⟨hval, hfix⟩ := element_of_items hwf hd
      cases hb : b.isValue
      · cases b with
        | fixed t =>
          obtain ⟨rfl, he⟩ := hfix t rfl
          obtain ⟨rfl, rfl⟩ := hnode _ [] ((h1 h).2 t rfl) (deliverKids_nil q 0 [])
          exact ⟨[.text t], rfl, rfl, h ▸ .plusOne _ [] _ he⟩
        | _ => simp [Sym.isValue] at hb
      · obtain ⟨k, w, k'?, rfl, hwk, he⟩ := hval hb
        obtain ⟨hk, ha⟩ := (h1 h).1 hb
        obtain ⟨rfl, rfl⟩ := hnode none _ hk (deliver_one_arg hwk ha)
        exact ⟨[named k'? w], rfl, rfl, h ▸ .plusOne _ [k] _ he⟩
    · obtain ⟨hs0, hval, hfix⟩ := h2 h
      rw [h] at hd
      cases kids with
      | nil => cases hd
      | cons tr kids =>
        obtain ⟨sub, toks', esr, rfl, hdr, hwr, hd'⟩ := splice_kid hwf hL hd
        obtain ⟨hv, hf⟩ := element_of_items hwf hd'
        cases hb : b.isValue
        · cases b with
          | fixed t =>
            obtain ⟨rfl, he⟩ := hf t rfl
            obtain ⟨rfl, rfl⟩ := hnode _ esr (hfix t rfl) (by
              rw [deliver_splice hwr hs0, deliverKids_nil, List.nil_append])
            exact ⟨esr ++ [.text t], rfl, rfl, h ▸ .plusSnoc _ tr esr sub hdr hwr [] _ he⟩
          | _ => simp [Sym.isValue] at hb
        · obtain ⟨k, w, k'?, rfl, hwk, he⟩ := hv hb
          obtain ⟨hk, ha⟩ := hval hb
          obtain ⟨rfl, rfl⟩ := hnode none (esr ++ [named k'? w]) hk (by
            rw [deliver_splice hwr hs0]
            simp only [List.nil_append]
            rw [deliver_one_arg hwk ha])
          exact ⟨esr ++ [named k'? w], rfl, rfl, h ▸ .plusSnoc _ tr esr sub hdr hwr [k] _ he⟩
  | separated x sep right =>
    simp only [ListForm.Spec] at hspec
    obtain ⟨hx, _, hk, h1, h2⟩ := hspec
    cases right with
    | true =>
      simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
      rcases hrhs with h | h
      · rw [h] at hd
        obtain ⟨k, w, k'?, rfl, hwk, he⟩ := (element_of_items hwf hd).1 hx
        obtain ⟨rfl, rfl⟩ := hnode none _ hk (deliver_one_arg hwk (h1 h))
        exact ⟨[named k'? w], rfl, rfl, h ▸ .sepOne _ sep true [k] _ he⟩
      · have hacts := h2 (by rw [h]; simp)
        simp only [if_true] at hacts
        rw [h] at hd
        obtain ⟨k, kids', sub₀, toks', rfl, rfl, hdx, hd'⟩ := items_split_value hx hd
        obtain ⟨toks2, rfl, hd2⟩ := derivesItems_fixedSyms_inv sep hd'
        cases kids' with
        | nil => cases hd2
        | cons tr kids'' =>
          obtain ⟨sub, toks3, esr, rfl, hdr, hwr, hd3⟩ := splice_kid hwf hL hd2
          cases hd3
          obtain ⟨k', w, k'?, hkk, hwk, he⟩ := (element_of_items hwf hdx).1 hx
          simp only [List.cons.injEq, and_true] at hkk
          subst hkk
          obtain ⟨rfl, rfl⟩ := hnode none (named k'? w :: esr) hk (by
            rw [deliverKids_cons, hwk]
            simp only []
            rw [hacts.1, deliver_arg]
            simp only [List.nil_append]
            rw [deliver_splice hwr hacts.2, deliverKids_nil]
            rfl)
          exact ⟨_, rfl, rfl, h ▸ .sepCons _ sep [k] _ he tr esr sub hdr hwr⟩
    | false =>
      simp only [ListForm.rhss, List.mem_cons, List.not_mem_nil, or_false] at hrhs
      rcases hrhs with h | h
      · rw [h] at hd
        obtain ⟨k, w, k'?, rfl, hwk, he⟩ := (element_of_items hwf hd).1 hx
        obtain ⟨rfl, rfl⟩ := hnode none _ hk (deliver_one_arg hwk (h1 h))
        exact ⟨[named k'? w], rfl, rfl, h ▸ .sepOne _ sep false [k] _ he⟩
      · have hacts := h2 (by rw [h]; simp)
        simp only [Bool.false_eq_true, if_false] at hacts
        rw [h] at hd
        cases kids with
        | nil => cases hd
        | cons tr kids =>
          obtain ⟨sub, toks', esr, rfl, hdr, hwr, hd'⟩ := splice_kid hwf hL hd
          obtain ⟨toks2, rfl, hd2⟩ := derivesItems_fixedSyms_inv sep hd'
          obtain ⟨k, w, k'?, rfl, hwk, he⟩ := (element_of_items hwf hd2).1 hx
          obtain ⟨rfl, rfl⟩ := hnode none (esr ++ [named k'? w]) hk (by
            rw [deliver_splice hwr hacts.1]
            simp only [List.nil_append]
            rw [deliver_one_arg hwk hacts.2])
          exact ⟨_, rfl, rfl, h ▸ .sepSnoc _ sep tr esr sub hdr hwr [k] _ he⟩

/-- An element is determined by its value, when a rule child is. -/
theorem element_inj (hwf : WellFormed G C L) {b : Sym} {kids₁ kids₂ : List Tree}
    {e₁ e₂ : CanonicalTerm} (h₁ : Element G C b kids₁ e₁) (h₂ : Element G C b kids₂ e₂)
    (he : e₁ = e₂)
    (hih : ∀ k₁ ∈ kids₁, ∀ k₂ m sub₁ sub₂, Derives G m sub₁ k₁ → Derives G m sub₂ k₂ →
      finishTree G C k₁ = finishTree G C k₂ → k₁ = k₂) : kids₁ = kids₂ := by
  cases h₁ with
  | value _ hb k w k? hw sub hd =>
    cases h₂ with
    | value _ _ k' w' k'? hw' sub' hd' =>
      rw [kid_inj hwf hb hd hd' hw hw' he (hih k List.mem_cons_self)]
    | fixed => simp [Sym.isValue] at hb
  | fixed t =>
    cases h₂ with
    | value _ hb => simp [Sym.isValue] at hb
    | fixed => rfl

/-- A list of a form without an empty production is not empty. -/
theorem ListShape.nonempty {r key : String} {f : ListForm} {rhs : List Sym} {kids : List Tree}
    {es : List CanonicalTerm} (h : ListShape G C r key f rhs kids es)
    (hf : ∀ b, f ≠ .option b ∧ f ≠ .star b) : es ≠ [] := by
  cases h with
  | optionNone b => exact absurd rfl (hf b).1
  | starNil b => exact absurd rfl (hf b).2
  | optionSome => simp
  | starSnoc => simp
  | plusOne => simp
  | plusSnoc => simp
  | sepOne => simp
  | sepCons => simp
  | sepSnoc => simp

/-- The list a derivation at a list rule of such a form finishes to is not
empty. -/
theorem list_nonempty (hwf : WellFormed G C L) {r : String} {f : ListForm} {key : String}
    (hL : L r = some (f, key)) (hf : ∀ b, f ≠ .option b ∧ f ≠ .star b) {sub : List Tok}
    {t : Tree} (hd : Derives G r sub t) {es : List CanonicalTerm}
    (hw : finishTree G C t = some (.seq es, some key)) : es ≠ [] := by
  obtain ⟨q, kids, hq, rfl, rfl, hitems⟩ := derives_inv hd
  obtain ⟨es', hes, _, hshape⟩ := list_shape hwf hq hL hitems hw
  cases hes
  exact hshape.nonempty hf

theorem snoc_inj {l₁ l₂ : List CanonicalTerm} {a₁ a₂ : CanonicalTerm}
    (h : l₁ ++ [a₁] = l₂ ++ [a₂]) : l₁ = l₂ ∧ a₁ = a₂ := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simpa using congrArg List.length h)
  exact ⟨h1, by simpa using h2⟩

/-- Two lists of one list rule's form that are equal come from one production
over one list of children, when every child is determined by its value. -/
theorem list_inj (hwf : WellFormed G C L) {r : String} {f : ListForm} {key : String}
    (hL : L r = some (f, key)) {rhs₁ rhs₂ : List Sym} {kids₁ kids₂ : List Tree}
    {es₁ es₂ : List CanonicalTerm} (h₁ : ListShape G C r key f rhs₁ kids₁ es₁)
    (h₂ : ListShape G C r key f rhs₂ kids₂ es₂) (hes : es₁ = es₂)
    (hih : ∀ k₁ ∈ kids₁, ∀ k₂ m sub₁ sub₂, Derives G m sub₁ k₁ → Derives G m sub₂ k₂ →
      finishTree G C k₁ = finishTree G C k₂ → k₁ = k₂) : rhs₁ = rhs₂ ∧ kids₁ = kids₂ := by
  -- a one-element list against a longer one: the longer one's recursion is empty
  have hshort : ∀ {esr : List CanonicalTerm} {a b : CanonicalTerm}, [a] = esr ++ [b] → esr = [] := by
    intro esr a b h
    have := congrArg List.length h
    simp only [List.length_cons, List.length_nil, List.length_append] at this
    exact List.length_eq_zero_iff.1 (by omega)
  have hpl : ∀ b b', (ListForm.plus b ≠ .option b' ∧ ListForm.plus b ≠ .star b') :=
    fun _ _ => ⟨by simp, by simp⟩
  have hsp : ∀ x sep right b, (ListForm.separated x sep right ≠ .option b ∧
      ListForm.separated x sep right ≠ .star b) := fun _ _ _ _ => ⟨by simp, by simp⟩
  -- two elements of one body, with one value
  have hel : ∀ {b : Sym} {k₁ k₂ : List Tree} {e₁ e₂ : CanonicalTerm}, Element G C b k₁ e₁ →
      Element G C b k₂ e₂ → e₁ = e₂ → (∀ k ∈ k₁, k ∈ kids₁) → k₁ = k₂ :=
    fun he he' heq hsub => element_inj hwf he he' heq (fun k hk => hih k (hsub k hk))
  cases h₁ with
  | optionNone b =>
    cases h₂ with
    | optionNone => exact ⟨rfl, rfl⟩
    | optionSome => simp at hes
  | optionSome b kids e he =>
    cases h₂ with
    | optionNone => simp at hes
    | optionSome _ kids' e' he' =>
      simp only [List.cons.injEq, and_true] at hes
      exact ⟨rfl, hel he he' hes (fun _ hk => hk)⟩
  | starNil b =>
    cases h₂ with
    | starNil => exact ⟨rfl, rfl⟩
    | starSnoc => simp at hes
  | starSnoc b tr esr sub hdr hr kids e he =>
    cases h₂ with
    | starNil => simp at hes
    | starSnoc _ tr' esr' sub' hdr' hr' kids' e' he' =>
      obtain ⟨rfl, rfl⟩ := snoc_inj hes
      have htr : tr = tr' := hih tr List.mem_cons_self tr' r sub sub' hdr hdr' (by rw [hr, hr'])
      subst htr
      rw [hel he he' rfl (fun k hk => List.mem_cons_of_mem _ hk)]
      exact ⟨rfl, rfl⟩
  | plusOne b kids e he =>
    cases h₂ with
    | plusOne _ kids' e' he' =>
      simp only [List.cons.injEq, and_true] at hes
      exact ⟨rfl, hel he he' hes (fun _ hk => hk)⟩
    | plusSnoc _ tr' esr' sub' hdr' hr' =>
      exact absurd (hshort hes) (list_nonempty hwf hL (hpl b) hdr' hr')
  | plusSnoc b tr esr sub hdr hr kids e he =>
    cases h₂ with
    | plusOne =>
      exact absurd (hshort hes.symm) (list_nonempty hwf hL (hpl b) hdr hr)
    | plusSnoc _ tr' esr' sub' hdr' hr' kids' e' he' =>
      obtain ⟨rfl, rfl⟩ := snoc_inj hes
      have htr : tr = tr' := hih tr List.mem_cons_self tr' r sub sub' hdr hdr' (by rw [hr, hr'])
      subst htr
      rw [hel he he' rfl (fun k hk => List.mem_cons_of_mem _ hk)]
      exact ⟨rfl, rfl⟩
  | sepOne x sep right kids e he =>
    cases h₂ with
    | sepOne _ _ _ kids' e' he' =>
      simp only [List.cons.injEq, and_true] at hes
      exact ⟨rfl, hel he he' hes (fun _ hk => hk)⟩
    | sepCons _ _ kids' e' he' tr' esr' sub' hdr' hr' =>
      simp only [List.cons.injEq] at hes
      exact absurd hes.2.symm (list_nonempty hwf hL (hsp x sep true) hdr' hr')
    | sepSnoc _ _ tr' esr' sub' hdr' hr' =>
      exact absurd (hshort hes) (list_nonempty hwf hL (hsp x sep false) hdr' hr')
  | sepCons x sep kids e he tr esr sub hdr hr =>
    cases h₂ with
    | sepOne =>
      simp only [List.cons.injEq] at hes
      exact absurd hes.2 (list_nonempty hwf hL (hsp x sep true) hdr hr)
    | sepCons _ _ kids' e' he' tr' esr' sub' hdr' hr' =>
      simp only [List.cons.injEq] at hes
      obtain ⟨he₀, rfl⟩ := hes
      have hkids : kids = kids' := hel he he' he₀ (fun k hk => List.mem_append_left _ hk)
      subst hkids
      have htr : tr = tr' :=
        hih tr (List.mem_append_right _ List.mem_cons_self) tr' r sub sub' hdr hdr'
          (by rw [hr, hr'])
      subst htr
      exact ⟨rfl, rfl⟩
  | sepSnoc x sep tr esr sub hdr hr kids e he =>
    cases h₂ with
    | sepOne =>
      exact absurd (hshort hes.symm) (list_nonempty hwf hL (hsp x sep false) hdr hr)
    | sepSnoc _ _ tr' esr' sub' hdr' hr' kids' e' he' =>
      obtain ⟨rfl, rfl⟩ := snoc_inj hes
      have htr : tr = tr' := hih tr List.mem_cons_self tr' r sub sub' hdr hdr' (by rw [hr, hr'])
      subst htr
      rw [hel he he' rfl (fun k hk => List.mem_cons_of_mem _ hk)]
      exact ⟨rfl, rfl⟩

/-! ### Under a settled classification the builder is injective on derivations -/

/-- The key an end's value is delivered with. -/
def End.key? (L : String → Option (ListForm × String)) : End → Option String
  | .list m => (L m).map Prod.snd
  | _ => none

theorem TPath.production_end {n : String} {chain : List Production} {q : Production}
    (h : TPath G C L n chain (.production q)) :
    q ∈ G.productions ∧ L q.lhs = none ∧ C.kind q ≠ .transparent := by
  generalize he : End.production q = e at h
  induction h with
  | stop q' hq hL hk =>
    cases he
    exact ⟨hq, hL, hk⟩
  | token => cases he
  | list => cases he
  | step _ _ _ _ _ _ _ _ _ _ ih => exact ih he

theorem TPath.list_end {n : String} {chain : List Production} {m : String}
    (h : TPath G C L n chain (.list m)) : (L m).isSome ∧ chain ≠ [] := by
  generalize he : End.list m = e at h
  induction h with
  | stop => cases he
  | token => cases he
  | list _ _ _ _ _ _ hm =>
    cases he
    exact ⟨hm, by simp⟩
  | step _ _ _ _ _ _ _ _ _ _ ih => exact ⟨(ih he).1, by simp⟩

/-- The value an end finishes to shows the end's head and carries its key. -/
theorem end_value (hwf : WellFormed G C L) {n : String} {chain : List Production} {e : End}
    {x : Tree} (hp : TPath G C L n chain e) (hx : EndDerives G e x) {w : CanonicalTerm}
    {k? : Option String} (hw : finishTree G C x = some (w, k?)) :
    (named k? w).head = e.head C L ∧ k? = e.key? L := by
  cases e with
  | production q =>
    obtain ⟨hq, hL, hk⟩ := hp.production_end
    obtain ⟨sub, kids, rfl, _⟩ := hx
    rw [finishTree_node hwf hq] at hw
    cases hd : deliverKids G C q 0 [] kids with
    | none =>
      rw [hd] at hw
      cases hw
    | some vals =>
      rw [hd] at hw
      cases hkq : C.kind q with
      | transparent => exact absurd hkq hk
      | literal s =>
        simp only [hkq, finish, Option.map_some, Option.some.injEq, Prod.mk.injEq, Kind.key?] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simp [named, CanonicalTerm.head, End.head, hkq, End.key?]
      | constructor c =>
        simp only [hkq, finish, Option.map_some, Option.some.injEq, Prod.mk.injEq, Kind.key?] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simp [named, CanonicalTerm.head, End.head, hkq, End.key?]
      | list key text =>
        have := hwf.list q hq key text hkq
        rw [hL] at this
        cases this
  | token cls =>
    obtain ⟨s, rfl⟩ := hx
    rw [finishTree_leaf] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    simp [named, CanonicalTerm.head, End.head, End.key?]
  | list m =>
    obtain ⟨hm, _⟩ := hp.list_end
    obtain ⟨sub, hd⟩ := hx
    obtain ⟨w', k', hw', hfin⟩ := finishes hwf hd
    rw [hw] at hw'
    simp only [Option.some.injEq, Prod.mk.injEq] at hw'
    obtain ⟨rfl, rfl⟩ := hw'
    obtain ⟨⟨f, key⟩, hfk⟩ := Option.isSome_iff_exists.1 hm
    unfold Finished at hfin
    rw [hfk] at hfin
    obtain ⟨rfl, es, rfl⟩ := hfin
    simp [named, CanonicalTerm.head, End.head, End.key?, hfk]

theorem wrap_height_le (x : Tree) : ∀ chain : List Production, x.height ≤ (wrap chain x).height
  | [] => Nat.le_refl _
  | t :: chain => by
    have := wrap_height_le x chain
    simp only [wrap, Tree.height, Tree.heights]
    omega

theorem finish_injective_bounded (hwf : WellFormed G C L) (hset : Settled G C L) :
    ∀ (N : Nat) {n : String} {toks₁ toks₂ : List Tok} {t₁ t₂ : Tree}, t₁.height ≤ N →
      Derives G n toks₁ t₁ → Derives G n toks₂ t₂ → finishTree G C t₁ = finishTree G C t₂ →
      t₁ = t₂ := by
  intro N
  induction N with
  | zero =>
    intro n toks₁ toks₂ t₁ t₂ hh hd₁ _ _
    obtain ⟨q, kids, _, _, rfl, _⟩ := derives_inv hd₁
    simp [Tree.height] at hh
  | succ N ih =>
    intro n toks₁ toks₂ t₁ t₂ hh hd₁ hd₂ heq
    have hkid : ∀ {k : Tree}, k.height < t₁.height → ∀ k₂ m sub₁ sub₂, Derives G m sub₁ k →
        Derives G m sub₂ k₂ → finishTree G C k = finishTree G C k₂ → k = k₂ :=
      fun hk k₂ m sub₁ sub₂ h₁ h₂ he => ih (by omega) h₁ h₂ he
    cases hLn : L n with
    | some fk =>
      obtain ⟨f, key⟩ := fk
      obtain ⟨q₁, kids₁, hq₁, rfl, rfl, hit₁⟩ := derives_inv hd₁
      obtain ⟨q₂, kids₂, hq₂, hl₂, rfl, hit₂⟩ := derives_inv hd₂
      obtain ⟨v₁, k₁, hw₁, _⟩ := finishes hwf hd₁
      have hw₂ : finishTree G C (.node q₂.label kids₂) = some (v₁, k₁) := heq ▸ hw₁
      obtain ⟨es₁, rfl, _, hs₁⟩ := list_shape hwf hq₁ hLn hit₁ hw₁
      obtain ⟨es₂, hv, _, hs₂⟩ := list_shape hwf hq₂ (by rw [hl₂]; exact hLn) hit₂ hw₂
      rw [hl₂] at hs₂
      obtain ⟨hrhs, rfl⟩ := list_inj hwf hLn hs₁ hs₂ (by cases hv; rfl)
        (fun k hk => hkid (Tree.height_kid hk))
      obtain rfl := (hwf.rule q₁.lhs f key hLn).2.2 q₁ hq₁ q₂ hq₂ rfl hl₂ hrhs
      rfl
    | none =>
      obtain ⟨c₁, e₁, x₁, hp₁, rfl, hx₁, hxh₁, hlt₁, hf₁⟩ := path_of_derives hwf hd₁ hLn
      obtain ⟨c₂, e₂, x₂, hp₂, rfl, hx₂, _, _, hf₂⟩ := path_of_derives hwf hd₂ hLn
      obtain ⟨v, k, hv, _⟩ := finishes hwf hd₁
      rw [hf₁] at hv
      obtain ⟨⟨w₁, k₁⟩, hw₁, hvk₁⟩ := Option.map_eq_some_iff.1 hv
      rw [hf₁, hf₂, hw₁] at heq
      obtain ⟨⟨w₂, k₂⟩, hw₂, hvk₂⟩ := Option.map_eq_some_iff.1 heq.symm
      simp only [Prod.mk.injEq, and_true] at hvk₂
      obtain ⟨hh₁, hk₁⟩ := end_value hwf hp₁ hx₁ hw₁
      obtain ⟨hh₂, hk₂⟩ := end_value hwf hp₂ hx₂ hw₂
      obtain ⟨rfl, rfl⟩ := hset _ c₁ c₂ e₁ e₂ hp₁ hp₂ (by rw [← hh₁, ← hh₂, hvk₂])
      obtain rfl : k₁ = k₂ := hk₁.trans hk₂.symm
      obtain rfl : w₁ = w₂ := (named_inj hvk₂).symm
      suffices x₁ = x₂ by rw [this]
      cases e₁ with
      | production q =>
        obtain ⟨hq, hL, hk⟩ := hp₁.production_end
        obtain ⟨sub₁, kids₁, rfl, hit₁⟩ := hx₁
        obtain ⟨sub₂, kids₂, rfl, hit₂⟩ := hx₂
        cases hkq : C.kind q with
        | transparent => exact absurd hkq hk
        | literal s =>
          obtain ⟨_, hall, _⟩ := hwf.literal q hq s hkq
          rw [(items_all_fixed hall (items_finishing hwf hit₁)).2,
            (items_all_fixed hall (items_finishing hwf hit₂)).2]
        | list key text =>
          have := hwf.list q hq key text hkq
          rw [hL] at this
          cases this
        | constructor cn =>
          have hne : C.action q 0 ≠ .extend := by
            intro h
            rcases hwf.constructor q hq cn hkq 0 with h' | ⟨_, j, hj, _⟩
            · rw [h] at h'
              cases h'
            · omega
          rw [finishTree_node hwf hq] at hw₁ hw₂
          cases hd₁' : deliverKids G C q 0 [] kids₁ with
          | none =>
            rw [hd₁'] at hw₁
            cases hw₁
          | some vals₁ =>
            cases hd₂' : deliverKids G C q 0 [] kids₂ with
            | none =>
              rw [hd₂'] at hw₂
              cases hw₂
            | some vals₂ =>
              rw [hd₁'] at hw₁
              rw [hd₂'] at hw₂
              simp only [hkq, finish, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw₁ hw₂
              have hvals : vals₁ = vals₂ := by
                have := hw₁.1.trans hw₂.1.symm
                simpa using this
              obtain ⟨a₁, ha₁, hdl₁⟩ := delivers_walk hwf hq hkq q.rhs.length q.rhs
                (Nat.le_refl _) 0 [] sub₁ kids₁ (by simp) rfl hne (items_finishing hwf hit₁) [] vals₁ hd₁'
              obtain ⟨a₂, ha₂, hdl₂⟩ := delivers_walk hwf hq hkq q.rhs.length q.rhs
                (Nat.le_refl _) 0 [] sub₂ kids₂ (by simp) rfl hne (items_finishing hwf hit₂) [] vals₂ hd₂'
              simp only [List.nil_append] at ha₁ ha₂
              subst ha₁ ha₂
              rw [delivers_inj hwf hdl₁ hdl₂ hvals hit₁ hit₂ (fun k hk k₂ m sub sub' h₁ h₂ he =>
                hkid (Nat.lt_of_lt_of_le (Tree.height_kid hk) hxh₁) k₂ m sub sub' h₁ h₂ he)]
      | token cls =>
        obtain ⟨s₁, rfl⟩ := hx₁
        obtain ⟨s₂, rfl⟩ := hx₂
        rw [finishTree_leaf] at hw₁ hw₂
        simp only [Option.some.injEq, Prod.mk.injEq] at hw₁ hw₂
        have := hw₁.1.trans hw₂.1.symm
        simp only [CanonicalTerm.node.injEq, List.cons.injEq, CanonicalTerm.text.injEq, and_true,
          true_and] at this
        rw [this]
      | list m =>
        obtain ⟨_, hne⟩ := hp₁.list_end
        obtain ⟨sub₁, hdx₁⟩ := hx₁
        obtain ⟨sub₂, hdx₂⟩ := hx₂
        exact hkid (hlt₁ hne) x₂ m sub₁ sub₂ hdx₁ hdx₂ (by rw [hw₁, hw₂])

/-- Under a settled classification, derivations at one rule with one value are
one derivation. -/
theorem finish_injective (hwf : WellFormed G C L) (hset : Settled G C L) {n : String}
    {toks₁ toks₂ : List Tok} {t₁ t₂ : Tree} (hd₁ : Derives G n toks₁ t₁)
    (hd₂ : Derives G n toks₂ t₂) (heq : finishTree G C t₁ = finishTree G C t₂) : t₁ = t₂ :=
  finish_injective_bounded hwf hset _ (Nat.le_refl _) hd₁ hd₂ heq

/-- Under a settled classification the projection is injective on derivations
at one rule. -/
theorem canon_injective (hwf : WellFormed G C L) (hset : Settled G C L) {n : String}
    {toks₁ toks₂ : List Tok} {t₁ t₂ : Tree} (hd₁ : Derives G n toks₁ t₁)
    (hd₂ : Derives G n toks₂ t₂) (hc : canon G C t₁ = canon G C t₂) : t₁ = t₂ := by
  obtain ⟨v₁, k₁, hw₁, hf₁⟩ := finishes hwf hd₁
  obtain ⟨v₂, k₂, hw₂, hf₂⟩ := finishes hwf hd₂
  obtain rfl := finished_key hf₁ hf₂
  simp only [canon, hw₁, hw₂, Option.map_some, Option.some.injEq] at hc
  obtain rfl := named_inj hc
  exact finish_injective hwf hset hd₁ hd₂ (by rw [hw₁, hw₂])

/-- A derivation tree determines its tokens: its labels name the productions,
which fix the terminals, and its leaves carry the lexemes. -/
theorem derives_tokens_unique (hwf : WellFormed G C L) {n : String} {toks : List Tok}
    {t : Tree} (h : Derives G n toks t) :
    ∀ {n' : String} {toks' : List Tok}, Derives G n' toks' t → toks = toks' := by
  refine Derives.induction_with
    (fun _ toks t => ∀ {n' : String} {toks' : List Tok}, Derives G n' toks' t → toks = toks')
    ?_ h
  intro p hp toks kids hdi hw n' toks' h'
  obtain ⟨q, kids', hq, _, heq, hit⟩ := derives_inv h'
  simp only [Tree.node.injEq] at heq
  obtain ⟨hlab, rfl⟩ := heq
  obtain rfl : p = q := List.inj_on_of_nodup_map hwf.labels hp hq hlab
  clear h' hdi
  generalize p.rhs = rhs at hw hit
  induction hw generalizing toks' with
  | nil =>
    cases hit
    rfl
  | fixed t rest toks kids _ ih =>
    cases hit with
    | fixed _ _ toks'' _ hit => rw [ih hit]
  | token cls s _ rest toks kids _ ih =>
    cases hit with
    | token _ _ _ _ toks'' _ hit => rw [ih hit]
  | rule m sub t _ hP rest toks kids _ ih =>
    cases hit with
    | rule _ sub' _ hsub' _ toks'' _ hit => rw [hP hsub', ih hit]

/-- Where a text has one derivation at a rule, that derivation projects to the
term it prints. -/
theorem canon_of_unique (hwf : WellFormed G C L) {n : String} {toks : List Tok}
    (hu : ∀ t₁ t₂, Derives G n toks t₁ → Derives G n toks t₂ → t₁ = t₂) {c : CanonicalTerm}
    (hp : Prints G C L (.rule n) c toks) {t : Tree} (hd : Derives G n toks t) :
    canon G C t = some c := by
  obtain ⟨t', hd', hc'⟩ := derives_of_prints hwf hp
  obtain rfl := hu t t' hd hd'
  exact hc'

/-- Under a settled classification printing is functional: two printings of
one term at one rule are one text. -/
theorem prints_unique (hwf : WellFormed G C L) (hset : Settled G C L) {n : String}
    {c : CanonicalTerm} {toks₁ toks₂ : List Tok} (h₁ : Prints G C L (.rule n) c toks₁)
    (h₂ : Prints G C L (.rule n) c toks₂) : toks₁ = toks₂ := by
  obtain ⟨t₁, hd₁, hc₁⟩ := derives_of_prints hwf h₁
  obtain ⟨t₂, hd₂, hc₂⟩ := derives_of_prints hwf h₂
  obtain rfl := canon_injective hwf hset hd₁ hd₂ (by rw [hc₁, hc₂])
  exact derives_tokens_unique hwf hd₁ hd₂

/-- The projection names the end of a chain from the rule: a derivation at a
rule that is not a list rule has a value whose head is the head of the end one
chain of transparent productions from the rule reaches. -/
theorem canon_head (hwf : WellFormed G C L) {n : String} {toks : List Tok} {t : Tree}
    (hd : Derives G n toks t) (hL : L n = none) {c : CanonicalTerm}
    (hc : canon G C t = some c) : ∃ chain e, TPath G C L n chain e ∧ c.head = e.head C L := by
  obtain ⟨chain, e, x, hp, _, hx, _, _, hf⟩ := path_of_derives hwf hd hL
  obtain ⟨v, k, hv, _⟩ := finishes hwf hd
  rw [hf] at hv
  obtain ⟨⟨w, k'⟩, hw, hvk⟩ := Option.map_eq_some_iff.1 hv
  simp only [Prod.mk.injEq] at hvk
  obtain ⟨rfl, rfl⟩ := hvk
  simp only [canon, hf, hw, Option.map_some, Option.some.injEq] at hc
  subst hc
  exact ⟨chain, e, hp, (end_value hwf hp hx hw).1⟩

end Settled

/-! ## A finite check for well-formedness

The implementation classifies once, from finite data: a kind per production,
the actions it marks at some value positions (every other position is an
argument), and the table of list rules its lowering made.  For a
classification given that way, a finite check establishes `WellFormed`, as
another establishes `Settled`. -/

section WellFormedCheck

/-- A classification from a kind per production and the actions marked at
some value positions; every unmarked position is an argument. -/
def Classification.ofMarks (kind : Production → Kind)
    (marks : Production → List (Nat × Action)) : Classification :=
  ⟨kind, fun p i => ((marks p).lookup i).getD .arg⟩

/-- The list rules of a lowering, as a table of rule, form and key. -/
def listRules (table : List (String × ListForm × String)) (r : String) :
    Option (ListForm × String) :=
  table.lookup r

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → ∃ e ∈ l, e.1 = a
  | [], h => by cases h
  | (k, v) :: t, h => by
    unfold List.lookup at h
    cases hak : a == k with
    | true =>
      exact ⟨(k, v), List.mem_cons_self, (eq_of_beq hak).symm⟩
    | false =>
      rw [hak] at h
      obtain ⟨e, he, hea⟩ := lookup_mem h
      exact ⟨e, List.mem_cons_of_mem _ he, hea⟩

/-- Whether a list rule is a repetition (star or plus). -/
def isRepetition : Option (ListForm × String) → Bool
  | some (.star _, _) => true
  | some (.plus _, _) => true
  | _ => false

theorem isRepetition_spec {o : Option (ListForm × String)} (h : isRepetition o = true) :
    ∃ b key, o = some (.star b, key) ∨ o = some (.plus b, key) := by
  match o, h with
  | some (.star b, key), _ => exact ⟨b, key, .inl rfl⟩
  | some (.plus b, key), _ => exact ⟨b, key, .inr rfl⟩

/-- Search the right-hand side for an extension position `i`. -/
def extensionSearch (C : Classification) (L : String → Option (ListForm × String))
    (p : Production) (i : Nat) : List Sym → List Sym → Bool
  | _, [] => false
  | pre, x :: rest =>
    (match rest with
     | .rule h :: _ =>
       decide ((values pre).length = i) && x.isValue && decide (C.action p i ≠ .extend) &&
         isRepetition (L h)
     | _ => false) || extensionSearch C L p i (pre ++ [x]) rest

theorem extensionSearch_sound {C : Classification} {L : String → Option (ListForm × String)}
    {p : Production} {i : Nat} :
    ∀ {pre l : List Sym}, extensionSearch C L p i pre l = true →
      ∃ pre' x h rest, pre ++ l = pre' ++ x :: .rule h :: rest ∧ (values pre').length = i ∧
        x.isValue = true ∧ C.action p i ≠ .extend ∧
        ∃ b key, (L h = some (.star b, key) ∨ L h = some (.plus b, key))
  | _, [], h => by cases h
  | pre, x :: rest, h => by
    unfold extensionSearch at h
    rcases Bool.or_eq_true_iff.1 h with here | later
    · match rest, here with
      | .rule m :: rest', here =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at here
        obtain ⟨⟨⟨hlen, hx⟩, hne⟩, hrep⟩ := here
        exact ⟨pre, x, m, rest', rfl, hlen, hx, hne, isRepetition_spec hrep⟩
    · obtain ⟨pre', y, m, rest', heq, rest_ok⟩ := extensionSearch_sound later
      refine ⟨pre', y, m, rest', ?_, rest_ok⟩
      rw [← heq, List.append_assoc]
      rfl

theorem extensionAt_of_search {C : Classification} {L : String → Option (ListForm × String)}
    {p : Production} {i : Nat} (h : extensionSearch C L p i [] p.rhs = true) :
    ExtensionAt C L p i := by
  obtain ⟨pre, x, m, rest, heq, hlen, hx, hne, hrep⟩ := extensionSearch_sound h
  exact ⟨pre, x, m, rest, heq, hlen, hx, hne, hrep⟩

/-- A transparent production is one value, an argument. -/
def transparentOk (C : Classification) (p : Production) : Bool :=
  match C.kind p, p.rhs with
  | .transparent, [v] => v.isValue && decide (C.action p 0 = .arg)
  | .transparent, _ => false
  | _, _ => true

/-- A literal production is a nonempty run of fixed terminals, its text. -/
def literalOk (C : Classification) (p : Production) : Bool :=
  match C.kind p with
  | .literal s =>
    !p.rhs.isEmpty && p.rhs.all (fun x => !x.isValue) &&
      decide (s = String.join (fixedTexts p.rhs))
  | _ => true

/-- The marked positions of a constructor are arguments or extensions. -/
def constructorOk (C : Classification) (L : String → Option (ListForm × String))
    (p : Production) (positions : List Nat) : Bool :=
  match C.kind p with
  | .constructor _ =>
    positions.all (fun i =>
      decide (C.action p i = .arg) ||
        (decide (C.action p i = .extend) &&
          match i with
          | 0 => false
          | j + 1 => extensionSearch C L p j [] p.rhs))
  | _ => true

/-- A list production belongs to a list rule. -/
def listOk (C : Classification) (L : String → Option (ListForm × String)) (p : Production) :
    Bool :=
  match C.kind p with
  | .list _ _ => (L p.lhs).isSome
  | _ => true

/-- `ListForm.Spec`, checked. -/
def specOk (r key : String) (f : ListForm) (q : Production) (C : Classification) : Bool :=
  match f with
  | .option b | .star b | .plus b =>
    decide (b ≠ .rule r) &&
    decide (q.rhs = [] → C.kind q = .list key none) &&
    decide (q.rhs = [b] → b.isValue = true → C.kind q = .list key none ∧ C.action q 0 = .arg) &&
    (match b with
     | .fixed t => decide (q.rhs = [b] → C.kind q = .list key (some (false, t)))
     | _ => true) &&
    decide (q.rhs = [.rule r, b] → C.action q 0 = .splice) &&
    decide (q.rhs = [.rule r, b] → b.isValue = true →
      C.kind q = .list key none ∧ C.action q 1 = .arg) &&
    (match b with
     | .fixed t => decide (q.rhs = [.rule r, b] → C.kind q = .list key (some (true, t)))
     | _ => true)
  | .separated x _ right =>
    x.isValue && decide (x ≠ .rule r) && decide (C.kind q = .list key none) &&
    decide (q.rhs = [x] → C.action q 0 = .arg) &&
    decide (q.rhs ≠ [x] →
      if right then C.action q 0 = .arg ∧ C.action q 1 = .splice
      else C.action q 0 = .splice ∧ C.action q 1 = .arg)

theorem spec_of_ok {r key : String} {f : ListForm} {q : Production} {C : Classification}
    (h : specOk r key f q C = true) : f.Spec r key q C := by
  cases f with
  | option b | star b | plus b =>
    simp only [specOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hb, hnil⟩, hone⟩, hfix₁⟩, hspl⟩, hsnoc⟩, hfix₂⟩ := h
    refine ⟨hb, hnil, fun hq => ⟨fun hv => hone hq hv, ?_⟩,
      fun hq => ⟨hspl hq, fun hv => hsnoc hq hv, ?_⟩⟩
    · intro t ht
      subst ht
      exact (of_decide_eq_true hfix₁) hq
    · intro t ht
      subst ht
      exact (of_decide_eq_true hfix₂) hq
  | separated x sep right =>
    simp only [specOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hx, hne⟩, hk⟩, hone⟩, hmany⟩ := h
    exact ⟨hx, hne, hk, hone, hmany⟩

/-- A list rule's productions: those of its form, each once, with its kinds and
actions. -/
def ruleOk (G : Grammar) (C : Classification) (L : String → Option (ListForm × String))
    (r : String) : Bool :=
  match L r with
  | some (f, key) =>
    G.productions.all (fun q =>
      !decide (q.lhs = r) || (decide (q.rhs ∈ f.rhss r) && specOk r key f q C)) &&
    (f.rhss r).all (fun rhs =>
      G.productions.any (fun q => decide (q.lhs = r) && decide (q.rhs = rhs))) &&
    G.productions.all (fun q => G.productions.all (fun q' =>
      !(decide (q.lhs = r) && decide (q'.lhs = r) && decide (q.rhs = q'.rhs)) ||
        decide (q = q')))
  | none => true

/-- The finite check of a classification given by kinds, marks and a list-rule
table. -/
def wellFormedCheck (G : Grammar) (kind : Production → Kind)
    (marks : Production → List (Nat × Action)) (table : List (String × ListForm × String)) :
    Bool :=
  decide ((G.productions.map Production.label).Nodup) &&
  G.productions.all (fun p =>
    transparentOk (.ofMarks kind marks) p && literalOk (.ofMarks kind marks) p &&
      constructorOk (.ofMarks kind marks) (listRules table) p ((marks p).map Prod.fst) &&
      listOk (.ofMarks kind marks) (listRules table) p) &&
  table.all (fun e => ruleOk G (.ofMarks kind marks) (listRules table) e.1)

/-- The finite check establishes well-formedness. -/
theorem wellFormed_of_check {G : Grammar} {kind : Production → Kind}
    {marks : Production → List (Nat × Action)} {table : List (String × ListForm × String)}
    (h : wellFormedCheck G kind marks table = true) :
    WellFormed G (.ofMarks kind marks) (listRules table) := by
  simp only [wellFormedCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlabels, hprods⟩, hrules⟩ := h
  have hp : ∀ p ∈ G.productions, _ := fun p hp => List.all_eq_true.1 hprods p hp
  refine ⟨hlabels, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hmem hk
    have hc := (hp p hmem)
    simp only [Bool.and_eq_true] at hc
    have ht := hc.1.1.1
    unfold transparentOk at ht
    rw [hk] at ht
    match hr : p.rhs, ht with
    | [v], ht =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ⟨v, rfl, ht.1, ht.2⟩
  · intro p hmem s hk
    have hc := (hp p hmem)
    simp only [Bool.and_eq_true] at hc
    have hl := hc.1.1.2
    unfold literalOk at hl
    rw [hk] at hl
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at hl
    obtain ⟨⟨hne, hall⟩, hs⟩ := hl
    refine ⟨hne, fun x hx => ?_, hs⟩
    have := List.all_eq_true.1 hall x hx
    simpa using this
  · intro p hmem n hk i
    have hc := (hp p hmem)
    simp only [Bool.and_eq_true] at hc
    have hcon := hc.1.2
    unfold constructorOk at hcon
    rw [hk] at hcon
    cases hlook : (marks p).lookup i with
    | none =>
      left
      show ((marks p).lookup i).getD .arg = .arg
      rw [hlook]
      rfl
    | some a =>
      obtain ⟨e, he, hei⟩ := lookup_mem hlook
      have hi : i ∈ (marks p).map Prod.fst := List.mem_map.2 ⟨e, he, hei⟩
      have hpos := List.all_eq_true.1 hcon i hi
      rcases Bool.or_eq_true_iff.1 hpos with harg | hext
      · exact .inl (of_decide_eq_true harg)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hext
        obtain ⟨hex, hsearch⟩ := hext
        cases i with
        | zero => cases hsearch
        | succ j => exact .inr ⟨hex, j, rfl, extensionAt_of_search hsearch⟩
  · intro p hmem key text hk
    have hc := (hp p hmem)
    simp only [Bool.and_eq_true] at hc
    have hl := hc.2
    unfold listOk at hl
    rw [hk] at hl
    exact hl
  · intro r f key hL
    obtain ⟨e, he, her⟩ := lookup_mem hL
    have hr := List.all_eq_true.1 hrules e he
    rw [her] at hr
    unfold ruleOk at hr
    rw [show listRules table r = some (f, key) from hL] at hr
    simp only [Bool.and_eq_true] at hr
    obtain ⟨⟨hforms, hpresent⟩, hunique⟩ := hr
    refine ⟨fun q hq hlhs => ?_, fun rhs hrhs => ?_, fun q hq q' hq' hl hl' hrhs => ?_⟩
    · have := List.all_eq_true.1 hforms q hq
      simp only [hlhs, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        decide_eq_true_eq] at this
      exact ⟨this.1, spec_of_ok this.2⟩
    · obtain ⟨q, hq, hqr⟩ := List.any_eq_true.1 (List.all_eq_true.1 hpresent rhs hrhs)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hqr
      exact ⟨q, hq, hqr.1, hqr.2⟩
    · have := List.all_eq_true.1 (List.all_eq_true.1 hunique q hq) q' hq'
      simp only [hl, hl', hrhs, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
        decide_eq_true_eq] at this
      exact this

end WellFormedCheck

/-! ## Examples

A settled classification: sums of numbers, `S → NUM | S "+" S`, where the
number alternative is transparent to its token.  An unsettled one: `S → T | U`
with `T → "x"` and `U → "x"`, where two chains from `S` reach the literal
text `x`; the naming pass makes both alternatives of `S` constructors. -/

namespace Examples

/-- `S → NUM | S "+" S`. -/
def sumNum : Production := ⟨"S.num", "S", [.token "NUM"]⟩
def sumAdd : Production := ⟨"S.add", "S", [.rule "S", .fixed "+", .rule "S"]⟩
def sums : Grammar := ⟨[sumNum, sumAdd], fun _ _ => True⟩
def sumsC : Classification :=
  ⟨fun p => if p.label = "S.num" then .transparent else .constructor "S", fun _ _ => .arg⟩

theorem sums_checked : settledCheck sums sumsC (fun _ => none) 3 = true := by decide

theorem sums_settled : Settled sums sumsC (fun _ => none) := settled_of_check sums_checked

/-- `S → T | U`, `T → "x"`, `U → "x"`. -/
def ambT : Production := ⟨"S.t", "S", [.rule "T"]⟩
def ambU : Production := ⟨"S.u", "S", [.rule "U"]⟩
def litT : Production := ⟨"T.x", "T", [.fixed "x"]⟩
def litU : Production := ⟨"U.x", "U", [.fixed "x"]⟩
def ambiguous : Grammar := ⟨[ambT, ambU, litT, litU], fun _ _ => True⟩
def ambiguousC : Classification :=
  ⟨fun p => if p.label = "S.t" ∨ p.label = "S.u" then .transparent else .literal "x",
    fun _ _ => .arg⟩

theorem ambiguous_unchecked : settledCheck ambiguous ambiguousC (fun _ => none) 3 = false := by
  decide

theorem ambiguous_not_settled : ¬ Settled ambiguous ambiguousC (fun _ => none) := by
  intro h
  have hT : TPath ambiguous ambiguousC (fun _ => none) "S" [ambT] (.production litT) :=
    .step ambT (by decide) rfl (by decide) "T" rfl rfl [] _
      (.stop litT (by decide) rfl (by decide))
  have hU : TPath ambiguous ambiguousC (fun _ => none) "S" [ambU] (.production litU) :=
    .step ambU (by decide) rfl (by decide) "U" rfl rfl [] _
      (.stop litU (by decide) rfl (by decide))
  have hchain := (h "S" _ _ _ _ hT hU (by decide)).1
  have hlabel : ambT.label = ambU.label := congrArg Production.label (List.head_eq_of_cons_eq hchain)
  exact absurd hlabel (by decide)

end Examples

/-! ## The theorems on checked grammars

Both examples are well formed and settled by the finite checks, so injectivity
and functional printing hold for them.  The second has a list rule.  A
classification that splices a constructor's child fails the check and is not
well formed. -/

namespace WellFormedExamples

open Examples

/-- The sums classification of the examples, from its kinds alone. -/
def sumsKind (p : Production) : Kind :=
  if p.label = "S.num" then .transparent else .constructor "S"

abbrev sumsMarked : Classification := .ofMarks sumsKind (fun _ => [])

theorem sums_wellFormed : WellFormed sums sumsMarked (listRules []) :=
  wellFormed_of_check (by decide)

theorem sums_settled_marked : Settled sums sumsMarked (listRules []) :=
  settled_of_check (fuel := 3) (by decide)

/-- Two derivations of sums with one canonical term are one derivation. -/
theorem sums_canon_injective {toks₁ toks₂ : List Tok} {t₁ t₂ : Tree}
    (hd₁ : Derives sums "S" toks₁ t₁) (hd₂ : Derives sums "S" toks₂ t₂)
    (hc : canon sums sumsMarked t₁ = canon sums sumsMarked t₂) : t₁ = t₂ :=
  canon_injective sums_wellFormed sums_settled_marked hd₁ hd₂ hc

/-- A canonical sum prints as one text. -/
theorem sums_prints_unique {c : CanonicalTerm} {toks₁ toks₂ : List Tok}
    (h₁ : Prints sums sumsMarked (listRules []) (.rule "S") c toks₁)
    (h₂ : Prints sums sumsMarked (listRules []) (.rule "S") c toks₂) : toks₁ = toks₂ :=
  prints_unique sums_wellFormed sums_settled_marked h₁ h₂

/-- `S → "[" H "]"`, where `H → ε | H NUM` is the star list of numbers. -/
def bracket : Production := ⟨"S.bracket", "S", [.fixed "[", .rule "H", .fixed "]"]⟩
def itemsNil : Production := ⟨"H.nil", "H", []⟩
def itemsSnoc : Production := ⟨"H.snoc", "H", [.rule "H", .token "NUM"]⟩
def brackets : Grammar := ⟨[bracket, itemsNil, itemsSnoc], fun _ _ => True⟩

def bracketsTable : List (String × ListForm × String) := [("H", .star (.token "NUM"), "items")]

def bracketsKind (p : Production) : Kind :=
  if p.lhs = "H" then .list "items" none else .constructor "bracket"

/-- The recursion of the list is spliced; every other child is an argument. -/
def bracketsMarks (p : Production) : List (Nat × Action) :=
  if p.label = "H.snoc" then [(0, .splice)] else []

abbrev bracketsC : Classification := .ofMarks bracketsKind bracketsMarks

theorem brackets_wellFormed : WellFormed brackets bracketsC (listRules bracketsTable) :=
  wellFormed_of_check (by decide)

theorem brackets_settled : Settled brackets bracketsC (listRules bracketsTable) :=
  settled_of_check (fuel := 2) (by decide)

theorem brackets_canon_injective {toks₁ toks₂ : List Tok} {t₁ t₂ : Tree}
    (hd₁ : Derives brackets "S" toks₁ t₁) (hd₂ : Derives brackets "S" toks₂ t₂)
    (hc : canon brackets bracketsC t₁ = canon brackets bracketsC t₂) : t₁ = t₂ :=
  canon_injective brackets_wellFormed brackets_settled hd₁ hd₂ hc

theorem brackets_prints_unique {c : CanonicalTerm} {toks₁ toks₂ : List Tok}
    (h₁ : Prints brackets bracketsC (listRules bracketsTable) (.rule "S") c toks₁)
    (h₂ : Prints brackets bracketsC (listRules bracketsTable) (.rule "S") c toks₂) :
    toks₁ = toks₂ :=
  prints_unique brackets_wellFormed brackets_settled h₁ h₂

/-- Marking the bracket's child as spliced into the constructor: a constructor
delivers arguments and extensions only. -/
def splicedMarks (p : Production) : List (Nat × Action) :=
  if p.label = "H.snoc" ∨ p.label = "S.bracket" then [(0, .splice)] else []

theorem brackets_spliced_unchecked :
    wellFormedCheck brackets bracketsKind splicedMarks bracketsTable = false := by
  decide

theorem brackets_spliced_not_wellFormed :
    ¬ WellFormed brackets (.ofMarks bracketsKind splicedMarks) (listRules bracketsTable) := by
  intro hwf
  rcases hwf.constructor bracket (by decide) "bracket" (by decide) 0 with h | ⟨h, _⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end WellFormedExamples

end Mettapedia.GSLT.Parsing.CanonicalGrammar
