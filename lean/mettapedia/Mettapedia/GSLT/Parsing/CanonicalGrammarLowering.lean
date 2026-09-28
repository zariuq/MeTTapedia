import Mettapedia.GSLT.Parsing.CanonicalGrammar
import Mettapedia.OSLF.Framework.GrammarDerives

/-!
# Authored grammar rows as a lowered grammar

A `LanguageDef`'s grammar rows derive text by `GrammarDerives.Derives`:
terminals and named nonterminal parameters.  Lowering a row gives a
production of the canonical-grammar model: a terminal is a fixed terminal and
a parameter is the rule of its sort.  A row with other syntax items has no
lowering, as it has no derivation.

Derivations correspond both ways (`lower_derives`, `derives_of_lower`), and
the derivation tree of a row is determined by its lowered tree
(`treeOf_injective`).  So the canonical-term theorems of the lowered grammar
hold for the authored rows: the projection of a derivation exists
(`canon_exists_rows`), prints back to its text (`prints_canon_rows`), and a
printed text derives from the rows to its term (`derives_of_prints_rows`);
the projection names the end of a transparent chain (`canon_head_rows`); a
per-text uniqueness certificate of the rows makes the parse the printed term
(`canon_of_unique_rows`); and under a settled classification the projection
is injective on the rows' derivations (`canon_injective_rows`), which then
derive one text per term (`canon_text_unique_rows`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.CanonicalGrammar.Lowering

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework

/-- The lowering of one syntax item of a row. -/
def lowerItem (r : GrammarRule) : SyntaxItem → Option Sym
  | .terminal t => some (.fixed t)
  | .nonTerminal n => (GrammarDerives.paramSort? r n).map Sym.rule
  | _ => none

/-- The lowering of a row's syntax items, when every item has one. -/
def lowerItems (r : GrammarRule) : List SyntaxItem → Option (List Sym)
  | [] => some []
  | it :: rest =>
    match lowerItem r it, lowerItems r rest with
    | some s, some ss => some (s :: ss)
    | _, _ => none

/-- The production a row lowers to. -/
def lowerRule (r : GrammarRule) : Option Production :=
  (lowerItems r r.syntaxPattern).map (fun rhs => ⟨r.label, r.category, rhs⟩)

/-- The lowered grammar of a language's rows.  It has no token classes. -/
def lower (lang : LanguageDef) : Grammar :=
  ⟨lang.terms.filterMap lowerRule, fun _ _ => False⟩

mutual

/-- A derivation tree of the rows as a lowered tree. -/
def treeOf : Pattern → Tree
  | .apply label kids => .node label (treesOf kids)
  | _ => .leaf "" ""

def treesOf : List Pattern → List Tree
  | [] => []
  | p :: ps => treeOf p :: treesOf ps

end

mutual

/-- A lowered tree as a derivation tree of the rows. -/
def patternOf : Tree → Pattern
  | .node label kids => .apply label (patternsOf kids)
  | .leaf _ _ => .fvar ""

def patternsOf : List Tree → List Pattern
  | [] => []
  | t :: ts => patternOf t :: patternsOf ts

end

theorem lowerItems_cons {r : GrammarRule} {it : SyntaxItem} {rest : List SyntaxItem}
    {s : Sym} {ss : List Sym} (hs : lowerItem r it = some s) (hss : lowerItems r rest = some ss) :
    lowerItems r (it :: rest) = some (s :: ss) := by
  simp only [lowerItems, hs, hss]

variable {lang : LanguageDef}

/-- A derivation of the rows is a derivation of the lowered grammar, of the
same text, with the lowered tree. -/
theorem lower_derives {sort : String} {toks : List String} {p : Pattern}
    (h : GrammarDerives.Derives lang sort toks p) :
    Derives (lower lang) sort (toks.map Tok.fixed) (treeOf p) := by
  induction h using GrammarDerives.Derives.rec (motive_2 := fun r items toks kids _ =>
    ∃ rhs, lowerItems r items = some rhs ∧
      DerivesItems (lower lang) rhs (toks.map Tok.fixed) (treesOf kids)) with
  | rule r hr sort hsort toks kids _ ih =>
    obtain ⟨rhs, hlow, hitems⟩ := ih
    subst hsort
    have hq : (⟨r.label, r.category, rhs⟩ : Production) ∈ (lower lang).productions :=
      List.mem_filterMap.2 ⟨r, hr, by simp only [lowerRule, hlow, Option.map_some]⟩
    exact Derives.node ⟨r.label, r.category, rhs⟩ hq _ _ hitems
  | nil r => exact ⟨[], rfl, .nil⟩
  | terminal r tok rest toks kids _ ih =>
    obtain ⟨rhs, hlow, hitems⟩ := ih
    exact ⟨.fixed tok :: rhs, lowerItems_cons rfl hlow, .fixed tok rhs _ _ hitems⟩
  | nonTerminal r n sort hsort sub tree _ rest toks kids _ ihsub ih =>
    obtain ⟨rhs, hlow, hitems⟩ := ih
    refine ⟨.rule sort :: rhs, lowerItems_cons (by simp only [lowerItem, hsort,
      Option.map_some]) hlow, ?_⟩
    rw [List.map_append]
    exact .rule sort _ _ ihsub rhs _ _ hitems

/-- The items of a lowered row derive only what the row's items derive. -/
theorem items_of_lower {r : GrammarRule}
    {P : String → List Tok → Tree → Prop}
    (hP : ∀ {n ts t}, P n ts t →
      ∃ toks p, ts = toks.map Tok.fixed ∧ t = treeOf p ∧ GrammarDerives.Derives lang n toks p) :
    ∀ {items : List SyntaxItem} {rhs : List Sym} {ts : List Tok} {kids : List Tree},
      lowerItems r items = some rhs → ItemsWith (lower lang) P rhs ts kids →
      ∃ toks kids', ts = toks.map Tok.fixed ∧ kids = treesOf kids' ∧
        GrammarDerives.DerivesItems lang r items toks kids'
  | [], rhs, ts, kids, hlow, hw => by
    simp only [lowerItems, Option.some.injEq] at hlow
    subst hlow
    cases hw
    exact ⟨[], [], rfl, rfl, .nil r⟩
  | it :: rest, rhs, ts, kids, hlow, hw => by
    unfold lowerItems at hlow
    cases hit : lowerItem r it with
    | none => rw [hit] at hlow; cases hlow
    | some s =>
      cases hrest : lowerItems r rest with
      | none => rw [hit, hrest] at hlow; cases hlow
      | some ss =>
        rw [hit, hrest] at hlow
        cases hlow
        cases it with
        | terminal tok =>
          cases hit
          cases hw with
          | fixed _ _ ts' kids' hw' =>
            obtain ⟨toks, kids'', rfl, rfl, hd⟩ := items_of_lower hP hrest hw'
            exact ⟨tok :: toks, kids'', rfl, rfl, .terminal r tok rest toks kids'' hd⟩
        | nonTerminal n =>
          cases hsort : GrammarDerives.paramSort? r n with
          | none => simp only [lowerItem, hsort, Option.map_none] at hit; cases hit
          | some sort =>
            simp only [lowerItem, hsort, Option.map_some, Option.some.injEq] at hit
            subst hit
            cases hw with
            | rule _ sub t _ hPt _ ts' kids' hw' =>
              obtain ⟨subToks, p, rfl, rfl, hdp⟩ := hP hPt
              obtain ⟨toks, kids'', rfl, rfl, hd⟩ := items_of_lower hP hrest hw'
              refine ⟨subToks ++ toks, p :: kids'', by rw [List.map_append], rfl, ?_⟩
              exact .nonTerminal r n sort hsort subToks p hdp rest toks kids'' hd
        | separator _ => cases hit
        | delimiter _ _ => cases hit
        | op _ => cases hit

/-- A derivation of the lowered grammar is the lowering of a derivation of the
rows. -/
theorem derives_of_lower {n : String} {ts : List Tok} {t : Tree}
    (h : Derives (lower lang) n ts t) :
    ∃ toks p, ts = toks.map Tok.fixed ∧ t = treeOf p ∧ GrammarDerives.Derives lang n toks p := by
  refine Derives.induction_with
    (fun n ts t => ∃ toks p, ts = toks.map Tok.fixed ∧ t = treeOf p ∧
      GrammarDerives.Derives lang n toks p) ?_ h
  intro q hq ts kids _ hw
  obtain ⟨r, hr, hlow⟩ := List.mem_filterMap.1 hq
  unfold lowerRule at hlow
  cases hrhs : lowerItems r r.syntaxPattern with
  | none => rw [hrhs] at hlow; cases hlow
  | some rhs =>
    rw [hrhs] at hlow
    simp only [Option.map_some, Option.some.injEq] at hlow
    subst hlow
    obtain ⟨toks, kids', rfl, rfl, hd⟩ := items_of_lower (fun h => h) hrhs hw
    exact ⟨toks, .apply r.label kids', rfl, rfl, .rule r hr _ rfl toks kids' hd⟩

/-- A derivation tree of the rows is recovered from its lowered tree. -/
theorem patternOf_treeOf {sort : String} {toks : List String} {p : Pattern}
    (h : GrammarDerives.Derives lang sort toks p) : patternOf (treeOf p) = p := by
  induction h using GrammarDerives.Derives.rec (motive_2 := fun _ _ _ kids _ =>
    patternsOf (treesOf kids) = kids) with
  | rule r _ _ _ _ kids _ ih =>
    show Pattern.apply r.label (patternsOf (treesOf kids)) = .apply r.label kids
    rw [ih]
  | nil => rfl
  | terminal _ _ _ _ _ _ ih => exact ih
  | nonTerminal _ _ _ _ _ tree _ _ _ kids _ ihsub ih =>
    show patternOf (treeOf tree) :: patternsOf (treesOf kids) = tree :: kids
    rw [ihsub, ih]

/-- Two derivations of the rows with one lowered tree are one derivation. -/
theorem treeOf_injective {s₁ s₂ : String} {toks₁ toks₂ : List String} {p₁ p₂ : Pattern}
    (h₁ : GrammarDerives.Derives lang s₁ toks₁ p₁) (h₂ : GrammarDerives.Derives lang s₂ toks₂ p₂)
    (h : treeOf p₁ = treeOf p₂) : p₁ = p₂ := by
  rw [← patternOf_treeOf h₁, ← patternOf_treeOf h₂, h]

/-! ## The canonical-term theorems for the rows -/

section Rows

variable {C : Classification} {L : String → Option (ListForm × String)}

/-- Every derivation of the rows has a canonical term. -/
theorem canon_exists_rows (hwf : WellFormed (lower lang) C L) {sort : String}
    {toks : List String} {p : Pattern} (h : GrammarDerives.Derives lang sort toks p) :
    ∃ c, canon (lower lang) C (treeOf p) = some c :=
  canon_exists hwf (lower_derives h)

/-- The canonical term of a derivation of the rows prints its text. -/
theorem prints_canon_rows (hwf : WellFormed (lower lang) C L) {sort : String}
    {toks : List String} {p : Pattern} (h : GrammarDerives.Derives lang sort toks p) :
    ∃ c, canon (lower lang) C (treeOf p) = some c ∧
      Prints (lower lang) C L (.rule sort) c (toks.map Tok.fixed) :=
  prints_canon hwf (lower_derives h)

/-- A printed text of a canonical term derives from the rows to a tree whose
canonical term it is. -/
theorem derives_of_prints_rows (hwf : WellFormed (lower lang) C L) {sort : String}
    {c : CanonicalTerm} {ts : List Tok} (hp : Prints (lower lang) C L (.rule sort) c ts) :
    ∃ toks p, ts = toks.map Tok.fixed ∧ GrammarDerives.Derives lang sort toks p ∧
      canon (lower lang) C (treeOf p) = some c := by
  obtain ⟨t, hd, hc⟩ := derives_of_prints hwf hp
  obtain ⟨toks, p, rfl, rfl, hdp⟩ := derives_of_lower hd
  exact ⟨toks, p, rfl, hdp, hc⟩

/-- Under a settled classification, two derivations of the rows at one sort
with one canonical term are one derivation. -/
theorem canon_injective_rows (hwf : WellFormed (lower lang) C L) (hset : Settled (lower lang) C L)
    {sort : String} {toks₁ toks₂ : List String} {p₁ p₂ : Pattern}
    (h₁ : GrammarDerives.Derives lang sort toks₁ p₁) (h₂ : GrammarDerives.Derives lang sort toks₂ p₂)
    (hc : canon (lower lang) C (treeOf p₁) = canon (lower lang) C (treeOf p₂)) : p₁ = p₂ :=
  treeOf_injective h₁ h₂ (canon_injective hwf hset (lower_derives h₁) (lower_derives h₂) hc)

/-- Under a settled classification, derivations of the rows with one canonical
term derive one text. -/
theorem canon_text_unique_rows (hwf : WellFormed (lower lang) C L)
    (hset : Settled (lower lang) C L) {sort : String} {toks₁ toks₂ : List String}
    {p₁ p₂ : Pattern} (h₁ : GrammarDerives.Derives lang sort toks₁ p₁)
    (h₂ : GrammarDerives.Derives lang sort toks₂ p₂)
    (hc : canon (lower lang) C (treeOf p₁) = canon (lower lang) C (treeOf p₂)) :
    toks₁ = toks₂ := by
  obtain rfl := canon_injective_rows hwf hset h₁ h₂ hc
  have := derives_tokens_unique hwf (lower_derives h₁) (lower_derives h₂)
  exact List.map_injective_iff.2 (fun _ _ h => Tok.fixed.inj h) this

/-- The canonical term of a derivation of the rows at a sort that is not a
list rule shows the head of the end one chain of transparent productions from
the sort reaches. -/
theorem canon_head_rows (hwf : WellFormed (lower lang) C L) {sort : String}
    {toks : List String} {p : Pattern} (h : GrammarDerives.Derives lang sort toks p)
    (hL : L sort = none) {c : CanonicalTerm} (hc : canon (lower lang) C (treeOf p) = some c) :
    ∃ chain e, TPath (lower lang) C L sort chain e ∧ c.head = e.head C L :=
  canon_head hwf (lower_derives h) hL hc

/-- Where the rows derive a text in one way, its derivation projects to the
term it prints, as a per-text uniqueness certificate of `GrammarDerives`
licenses. -/
theorem canon_of_unique_rows (hwf : WellFormed (lower lang) C L) {sort : String}
    {toks : List String} (hu : GrammarDerives.UniqueDerivation lang sort toks)
    {c : CanonicalTerm} (hp : Prints (lower lang) C L (.rule sort) c (toks.map Tok.fixed))
    {p : Pattern} (hd : GrammarDerives.Derives lang sort toks p) :
    canon (lower lang) C (treeOf p) = some c := by
  obtain ⟨toks', p', htoks, hd', hc⟩ := derives_of_prints_rows hwf hp
  obtain rfl : toks = toks' :=
    List.map_injective_iff.2 (fun _ _ h => Tok.fixed.inj h) htoks
  rw [hu p p' hd hd']
  exact hc

end Rows

/-! ## Examples

Sums as authored rows, `S → "1" | S "+" S`: the lowering is well formed and
settled by the finite checks, so the theorems hold for the rows.  Ambiguous
rows, `S → T | U` with `T → "x"` and `U → "x"`: two derivations of `x` have
one canonical term, and the settled check fails. -/

namespace Examples

def oneRow : GrammarRule :=
  { label := "S.one", category := "S", params := [], syntaxPattern := [.terminal "1"] }
def addRow : GrammarRule :=
  { label := "S.add", category := "S",
    params := [.simple "a" (.base "S"), .simple "b" (.base "S")],
    syntaxPattern := [.nonTerminal "a", .terminal "+", .nonTerminal "b"] }
def sumRows : LanguageDef := LanguageDef.ofCore "SumRows" [] [oneRow, addRow] [] []

def sumRowsKind (p : Production) : Kind :=
  if p.label = "S.one" then .literal "1" else .constructor "S"

abbrev sumRowsC : Classification := .ofMarks sumRowsKind (fun _ => [])

theorem sumRows_wellFormed : WellFormed (lower sumRows) sumRowsC (listRules []) :=
  wellFormed_of_check (by decide)

theorem sumRows_settled : Settled (lower sumRows) sumRowsC (listRules []) :=
  settled_of_check (fuel := 2) (by decide)

/-- Two derivations of sums from the rows with one canonical term are one
derivation. -/
theorem sumRows_canon_injective {toks₁ toks₂ : List String} {p₁ p₂ : Pattern}
    (h₁ : GrammarDerives.Derives sumRows "S" toks₁ p₁)
    (h₂ : GrammarDerives.Derives sumRows "S" toks₂ p₂)
    (hc : canon (lower sumRows) sumRowsC (treeOf p₁) = canon (lower sumRows) sumRowsC (treeOf p₂)) :
    p₁ = p₂ :=
  canon_injective_rows sumRows_wellFormed sumRows_settled h₁ h₂ hc

def onePlusOne : Pattern := .apply "S.add" [.apply "S.one" [], .apply "S.one" []]

theorem one_derives : GrammarDerives.Derives sumRows "S" ["1"] (.apply "S.one" []) :=
  .rule oneRow List.mem_cons_self "S" rfl ["1"] [] (.terminal oneRow "1" [] [] [] (.nil oneRow))

theorem onePlusOne_derives : GrammarDerives.Derives sumRows "S" ["1", "+", "1"] onePlusOne :=
  .rule addRow (List.mem_cons_of_mem _ List.mem_cons_self) "S" rfl _ _
    (.nonTerminal addRow "a" "S" rfl ["1"] _ one_derives _ _ _
      (.terminal addRow "+" _ _ _
        (.nonTerminal addRow "b" "S" rfl ["1"] _ one_derives _ [] [] (.nil addRow))))

theorem onePlusOne_canon :
    canon (lower sumRows) sumRowsC (treeOf onePlusOne) = some (.node "S" [.text "1", .text "1"]) :=
  rfl

def tRow : GrammarRule :=
  { label := "S.t", category := "S", params := [.simple "t" (.base "T")],
    syntaxPattern := [.nonTerminal "t"] }
def uRow : GrammarRule :=
  { label := "S.u", category := "S", params := [.simple "u" (.base "U")],
    syntaxPattern := [.nonTerminal "u"] }
def xT : GrammarRule := { label := "T.x", category := "T", params := [], syntaxPattern := [.terminal "x"] }
def xU : GrammarRule := { label := "U.x", category := "U", params := [], syntaxPattern := [.terminal "x"] }
def ambRows : LanguageDef := LanguageDef.ofCore "AmbRows" [] [tRow, uRow, xT, xU] [] []

def ambKind (p : Production) : Kind :=
  if p.label = "S.t" ∨ p.label = "S.u" then .transparent else .literal "x"

abbrev ambC : Classification := .ofMarks ambKind (fun _ => [])

def viaT : Pattern := .apply "S.t" [.apply "T.x" []]
def viaU : Pattern := .apply "S.u" [.apply "U.x" []]

theorem viaT_derives : GrammarDerives.Derives ambRows "S" ["x"] viaT :=
  .rule tRow List.mem_cons_self "S" rfl _ _
    (.nonTerminal tRow "t" "T" rfl ["x"] _
      (.rule xT (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) "T" rfl ["x"] [] (.terminal xT "x" [] [] [] (.nil xT))) [] [] []
      (.nil tRow))

theorem viaU_derives : GrammarDerives.Derives ambRows "S" ["x"] viaU :=
  .rule uRow (List.mem_cons_of_mem _ List.mem_cons_self) "S" rfl _ _
    (.nonTerminal uRow "u" "U" rfl ["x"] _
      (.rule xU (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) "U" rfl ["x"] [] (.terminal xU "x" [] [] [] (.nil xU))) [] [] []
      (.nil uRow))

/-- The ambiguous rows are well formed but not settled: two derivations of
`x` have one canonical term. -/
theorem ambRows_wellFormed : WellFormed (lower ambRows) ambC (listRules []) :=
  wellFormed_of_check (by decide)

theorem ambRows_unchecked : settledCheck (lower ambRows) ambC (listRules []) 3 = false := by
  decide

theorem ambRows_same_canon :
    canon (lower ambRows) ambC (treeOf viaT) = canon (lower ambRows) ambC (treeOf viaU) :=
  rfl

theorem ambRows_not_injective : viaT ≠ viaU := by
  intro h
  have hl := congrArg (fun p => match p with | Pattern.apply l _ => l | _ => "") h
  exact absurd hl (by decide)

theorem ambRows_not_settled : ¬ Settled (lower ambRows) ambC (listRules []) := fun hset =>
  ambRows_not_injective
    (canon_injective_rows ambRows_wellFormed hset viaT_derives viaU_derives ambRows_same_canon)

end Examples

end Mettapedia.GSLT.Parsing.CanonicalGrammar.Lowering
