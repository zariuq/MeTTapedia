import Mettapedia.GSLT.Readers.Metamath.Tables
import Mettapedia.GSLT.Readers.GrammarCorrespondence

/-!
# The Metamath reader's check reads exactly Metamath's database grammar

The generated readers (MeTTa and C) cut a `.mm` file into tokens, parse with the SLR tables of
`Tables.lean`, and accept a statement tree only if the tree check of `TreeCheck` passes. This file
instantiates the generic results for the grammar of `MetamathSyntax.module`:

* `check_iff`: the tree check accepts exactly the token-level derivations of the lowered grammar;
* `reader_sound`, `reader_complete`: those derivations are exactly the derivations of the
  `.module` rows with the input's leaf rows (`GrammarCorrespondence`);
* `source_sound`, `source_complete`: and of the authored Lean root `SourceGSLT.sourceGrammar`, whose
  derivations the existing Metamath development aligns with the verified reader of mm-lean4.

What is not proved here: that the SLR engine finds a tree whenever one exists (the tables are
untrusted; their completeness for conflict-free SLR(1) tables is the classical theorem, not
formalized), and the agreement of the byte-level tokenizer with mm-lean4's tokenizer.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Metamath.Correspondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.RowShape
open Mettapedia.GSLT.Readers.Metamath

def tokenSorts : List String := Tables.tokenSorts

/-- A token of a token sort, by the `.module`'s lexical layer. -/
def inSort (c x : String) : Bool := profile.tokenHasSort c (codes x)

def rows? : Option (List Prod) := grammar.terms.mapM (lowerRow tokenSorts)

def rows : List Prod := rows?.get (by decide +kernel)

theorem rows_lowered : grammar.terms.mapM (lowerRow tokenSorts) = some rows :=
  (Option.some_get _).symm

/-- The Metamath setting: the `.module` rows, their token sorts, and their lowering. -/
def setting : Setting :=
  { lang := grammar, tokenSorts, inSort, prods := rows, lowering := rows_lowered }

theorem rows_count : rows.length = 27 := by decide +kernel

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

/-- The tree check accepts exactly the derivations of the lowered Metamath grammar. -/
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

/-! ## The authored Lean root -/

private def source : LanguageDef := Mettapedia.Languages.Metamath.SourceGSLT.sourceGrammar

/-- The root with the same leaf rows. -/
def sourceLeaves (toks : List String) : LanguageDef :=
  withLeaves source tokenSorts inSort toks

theorem leaves_shapes (toks : List String) :
    (setting.leaves toks).terms.map rowShape = (sourceLeaves toks).terms.map rowShape := by
  simp only [Setting.leaves, setting, sourceLeaves, withLeaves, List.map_append]
  rw [grammar_shapes]
  rfl

/-- A tree the Metamath reader's check accepts is a derivation of the authored Lean root
`SourceGSLT.sourceGrammar` with the leaf rows of its tokens. -/
theorem source_sound (t : Tree) (s : String) (toks : List String)
    (h : check setting.grammar s toks t = true) :
    GDerives (sourceLeaves toks) s toks (toPattern t) :=
  (derives_iff_of_shapes (leaves_shapes toks) s toks (toPattern t)).mp (reader_sound t s toks h)

/-- Every derivation of the authored Lean root with the leaf rows of the tokens is a tree the
Metamath reader's check accepts. -/
theorem source_complete (P : Pattern) (s : String) (toks : List String)
    (h : GDerives (sourceLeaves toks) s toks P) :
    ∃ t, toPattern t = P ∧ check setting.grammar s toks t = true :=
  reader_complete P s toks ((derives_iff_of_shapes (leaves_shapes toks) s toks P).mpr h)

/-! ## Controls -/

/-- Positive control: `$c x $.` is a checked outer statement. -/
theorem control_const :
    check setting.grammar "outer_statement" ["$c", "x", "$."]
      (.node "statement_const" [.node "symbols_one" [.leaf "symbol_tok" "x"]]) = true := by
  decide +kernel

/-- Negative control: a label token where a math symbol is required (`$` is no symbol byte). -/
theorem control_dollar_symbol :
    check setting.grammar "outer_statement" ["$c", "$x", "$."]
      (.node "statement_const" [.node "symbols_one" [.leaf "symbol_tok" "$x"]]) = false := by
  decide +kernel

/-- Negative control: the right tree for other tokens. -/
theorem control_wrong_tokens :
    check setting.grammar "outer_statement" ["$v", "x", "$."]
      (.node "statement_const" [.node "symbols_one" [.leaf "symbol_tok" "x"]]) = false := by
  decide +kernel

end Mettapedia.GSLT.Readers.Metamath.Correspondence
