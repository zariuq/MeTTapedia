import Mettapedia.GSLT.Readers.MM0.Tables
import Mettapedia.GSLT.Readers.GrammarCorrespondence

/-!
# The `.mmu` reader's check reads exactly the `.module` grammar

The generated readers (MeTTa and C) cut an `.mmu` file into tokens with the version-2 profile of
`MMUSyntax.module`, parse with the SLR tables of `Tables.lean`, and accept a statement tree only if
the tree check of `TreeCheck` passes. This file instantiates the generic results:

* `check_iff`: the tree check accepts exactly the token-level derivations of the lowered grammar;
* `reader_sound`, `reader_complete`: those derivations are exactly the derivations of the
  `.module` rows with the input's leaf rows (`GrammarCorrespondence`).

These are the same generic theorems the Metamath reader instantiates; nothing here is specific to
MM0 but the grammar and the lexical layer. Not proved here: that the SLR engine finds a tree
whenever one exists (the tables are untrusted), and the agreement of the generated engines'
tokenizers with `TokenProfileV2.tokenize` (they are checked against each other on files).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.MM0.Correspondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile (codes)
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.MM0

def tokenSorts : List String := Tables.spec.tokenSorts

/-- A token of a token sort, by the `.module`'s lexical layer. -/
def inSort (c x : String) : Bool := profile.tokenHasSort c (codes x)

def rows? : Option (List Prod) := grammar.terms.mapM (lowerRow tokenSorts)

def rows : List Prod := rows?.get (by decide +kernel)

theorem rows_lowered : grammar.terms.mapM (lowerRow tokenSorts) = some rows :=
  (Option.some_get _).symm

/-- The `.mmu` setting: the `.module` rows, their token sorts, and their lowering. -/
def setting : Setting :=
  { lang := grammar, tokenSorts, inSort, prods := rows, lowering := rows_lowered }

theorem rows_count : rows.length = 48 := by decide +kernel

theorem admissible : setting.Admissible where
  token_sorts_have_no_rows := by
    intro r hr
    have : ∀ r ∈ grammar.terms, tokenSorts.contains r.category = false := by decide +kernel
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

/-- The tree check accepts exactly the derivations of the lowered `.mmu` grammar. -/
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

/-- Positive control: `(sort s strict)` is a checked statement. -/
theorem control_sort :
    check setting.grammar "statement" ["(", "sort", "s", "strict", ")"]
      (.node "statement_sort" [.leaf "id_tok" "s", .node "pure_no" [], .node "strict_yes" [],
        .node "provable_no" [], .node "free_no" []]) = true := by
  decide +kernel

/-- Negative control: modifiers out of MM0's order (`strict pure`) have no tree. -/
theorem control_modifier_order :
    check setting.grammar "statement" ["(", "sort", "s", "strict", "pure", ")"]
      (.node "statement_sort" [.leaf "id_tok" "s", .node "pure_yes" [], .node "strict_yes" [],
        .node "provable_no" [], .node "free_no" []]) = false := by
  decide +kernel

/-- Negative control: `_` is no identifier, so it names no sort. -/
theorem control_blank_sort :
    check setting.grammar "statement" ["(", "sort", "_", ")"]
      (.node "statement_sort" [.leaf "id_tok" "_", .node "pure_no" [], .node "strict_no" [],
        .node "provable_no" [], .node "free_no" []]) = false := by
  decide +kernel

/-- Positive control: a blank binder. -/
theorem control_blank_binder :
    check setting.grammar "binder" ["(", "_", "hex", "(", ")", ")"]
      (.node "binder_regular_blank" [.leaf "id_tok" "hex", .node "ids_empty" []]) = true := by
  decide +kernel

end Mettapedia.GSLT.Readers.MM0.Correspondence
