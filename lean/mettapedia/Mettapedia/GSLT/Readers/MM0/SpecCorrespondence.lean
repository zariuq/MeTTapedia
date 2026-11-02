import Mettapedia.GSLT.Readers.MM0.SpecTables
import Mettapedia.GSLT.Readers.GrammarCorrespondence

/-!
# The `.mm0` reader's check reads exactly the `.module` grammar

The generated readers (MeTTa and C) cut an `.mm0` file into tokens with the version-2 profile of
`MM0Syntax.module` (math strings are quoted tokens), parse with the SLR tables of `SpecTables`,
and accept a statement tree only if the tree check of `TreeCheck` passes. This file instantiates
the generic results, as `Correspondence` does for `.mmu` files:

* `check_iff`: the tree check accepts exactly the token-level derivations of the lowered grammar;
* `reader_sound`, `reader_complete`: those derivations are exactly the derivations of the
  `.module` rows with the input's leaf rows (`GrammarCorrespondence`).

What is inside a math string is read afterwards, under the file's notations (`MM0.Math`). Not
proved here: that the SLR engine finds a tree whenever one exists (the tables are untrusted), and
the agreement of the generated engines' tokenizers with `TokenProfileV2.tokenize` (they are
checked against each other on files).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.MM0.SpecCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile (codes)
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.MM0

def tokenSorts : List String := SpecTables.spec.tokenSorts

/-- A token of a token sort, by the `.module`'s lexical layer. -/
def inSort (c x : String) : Bool := Spec.profile.tokenHasSort c (codes x)

def rows? : Option (List Prod) := Spec.grammar.terms.mapM (lowerRow tokenSorts)

def rows : List Prod := rows?.get (by decide +kernel)

theorem rows_lowered : Spec.grammar.terms.mapM (lowerRow tokenSorts) = some rows :=
  (Option.some_get _).symm

/-- The `.mm0` setting: the `.module` rows, their token sorts, and their lowering. -/
def setting : Setting :=
  { lang := Spec.grammar, tokenSorts, inSort, prods := rows, lowering := rows_lowered }

theorem rows_count : rows.length = 66 := by decide +kernel

theorem admissible : setting.Admissible where
  token_sorts_have_no_rows := by
    intro r hr
    have : ∀ r ∈ Spec.grammar.terms, tokenSorts.contains r.category = false := by decide +kernel
    exact this r hr
  labels_name_productions := by
    intro p hp
    have : ∀ p ∈ rows, (setting.grammar).prodOf? p.label = some p := by decide +kernel
    exact this p hp

def ntSorts (p : Prod) : List String := p.rhs.filterMap fun sym => match sym with
  | .nt n => some n
  | _ => none

theorem wellFormed : WellFormed setting.grammar := by
  intro p hp n hn
  have hall : ∀ p ∈ rows, ∀ m ∈ ntSorts p, tokenSorts.contains m = false := by decide +kernel
  exact hall p hp n (by simp only [ntSorts, List.mem_filterMap]; exact ⟨.nt n, hn, rfl⟩)

/-- The tree check accepts exactly the derivations of the lowered `.mm0` grammar. -/
theorem check_iff (t : Tree) (s : String) (toks : List String) :
    check setting.grammar s toks t = true ↔ Derives setting.grammar s toks t :=
  TreeCheck.check_iff setting.grammar wellFormed t s toks

/-- A tree the check accepts is a derivation of the `.module` rows with the leaf rows of its
tokens. -/
theorem reader_sound (t : Tree) (s : String) (toks : List String)
    (h : check setting.grammar s toks t = true) :
    GDerives (setting.leaves toks) s toks (toPattern t) :=
  (reader_correspondence setting admissible toks s toks (fun _ hx => hx)).1 t ((check_iff t s toks).mp h)

/-- Every derivation of the `.module` rows with the leaf rows of the tokens is a tree the check
accepts. -/
theorem reader_complete (P : Pattern) (s : String) (toks : List String)
    (h : GDerives (setting.leaves toks) s toks P) :
    ∃ t, toPattern t = P ∧ check setting.grammar s toks t = true := by
  obtain ⟨t, ht, hd⟩ := (reader_correspondence setting admissible toks s toks (fun _ hx => hx)).2 P h
  exact ⟨t, ht, (check_iff t s toks).mpr hd⟩

/-! ## Controls -/

/-- Positive control: `provable sort wff;` with its modifiers in MM0's order. -/
theorem control_sort :
    check setting.grammar "statement" ["provable", "sort", "wff", ";"]
      (.node "statement_sort" [.node "pure_no" [], .node "strict_no" [], .node "provable_yes" [],
        .node "free_no" [], .leaf "id_tok" "wff"]) = true := by
  decide +kernel

/-- Positive control: an axiom whose formula is one math-string token. -/
theorem control_axiom :
    check setting.grammar "statement" ["axiom", "a1", ":", "$ a -> a $", ";"]
      (.node "statement_axiom" [.leaf "id_tok" "a1", .node "fbinders_empty" [],
        .node "farrow_last" [.leaf "math_tok" "$ a -> a $"]]) = true := by
  decide +kernel

/-- Negative control: modifiers out of MM0's order (`provable strict`) have no tree. -/
theorem control_modifier_order :
    check setting.grammar "statement" ["provable", "strict", "sort", "wff", ";"]
      (.node "statement_sort" [.node "pure_no" [], .node "strict_yes" [], .node "provable_yes" [],
        .node "free_no" [], .leaf "id_tok" "wff"]) = false := by
  decide +kernel

/-- Negative control: an unclosed math string is no `math_tok`. -/
theorem control_unclosed_math :
    check setting.grammar "statement" ["axiom", "a1", ":", "$ a -> a", ";"]
      (.node "statement_axiom" [.leaf "id_tok" "a1", .node "fbinders_empty" [],
        .node "farrow_last" [.leaf "math_tok" "$ a -> a"]]) = false := by
  decide +kernel

end Mettapedia.GSLT.Readers.MM0.SpecCorrespondence
