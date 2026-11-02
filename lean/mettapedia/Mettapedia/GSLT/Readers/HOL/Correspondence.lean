import Mettapedia.GSLT.Readers.HOL.Tables
import Mettapedia.GSLT.Readers.GrammarCorrespondence

/-!
# The ProofTrace reader's check reads exactly the `.module` grammar

The generated readers (MeTTa and C) cut a ProofTrace file into tokens with the version-2 profile of
`ProofTraceSyntax.module`, parse with the SLR tables of `Tables.lean`, and accept a record tree only
if the tree check of `TreeCheck` passes. This file instantiates the generic results:

* `check_iff`: the tree check accepts exactly the token-level derivations of the lowered grammar;
* `reader_sound`, `reader_complete`: those derivations are exactly the derivations of the
  `.module` rows with the input's leaf rows (`GrammarCorrespondence`).

These are the generic theorems the Metamath and MM0 readers instantiate; nothing here is specific to
HOL Light but the grammar and the lexical layer. Not proved here: that the SLR engine finds a tree
whenever one exists (the tables are untrusted), and the agreement of the generated engines'
tokenizers with `TokenProfileV2.tokenize` (they are checked against each other on files).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.HOL.Correspondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile (codes)
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.HOL

def tokenSorts : List String := Tables.spec.tokenSorts

/-- A token of a token sort, by the `.module`'s lexical layer. -/
def inSort (c x : String) : Bool := profile.tokenHasSort c (codes x)

def rows? : Option (List Prod) := grammar.terms.mapM (lowerRow tokenSorts)

def rows : List Prod := rows?.get (by decide +kernel)

theorem rows_lowered : grammar.terms.mapM (lowerRow tokenSorts) = some rows :=
  (Option.some_get _).symm

/-- The ProofTrace setting: the `.module` rows, their token sorts, and their lowering. -/
def setting : Setting :=
  { lang := grammar, tokenSorts, inSort, prods := rows, lowering := rows_lowered }

theorem rows_count : rows.length = 43 := by decide +kernel

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

/-- The tree check accepts exactly the derivations of the lowered ProofTrace grammar. -/
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

private def q : Tree := .leaf "quote_tok" "\""

private def bool : Tree := .node "ty_app" [.leaf "name_tok" "bool", .node "args_empty" []]

/-- Positive control: `{"id": 4, "pr": ["MK_COMB", 3, 0]}` is a checked proof record. -/
theorem control_mk_comb :
    check setting.grammar "record"
      ["{", "\"", "id", "\"", ":", "4", ",", "\"", "pr", "\"", ":", "[", "\"", "MK_COMB", "\"", ",",
        "3", ",", "0", "]", "}"]
      (.node "record_proof" [q, q, .leaf "num_tok" "4", q, q,
        .node "step_mk_comb" [q, q, .leaf "num_tok" "3", .leaf "num_tok" "0"]]) = true := by
  decide +kernel

/-- Positive control: the type `c[bool][]`, and the abstraction `A(v(p)(c[bool][]))(v(p)(c[bool][]))`
(the identity on `bool`). -/
theorem control_abstraction :
    check setting.grammar "hol_term"
      ["A", "(", "v", "(", "p", ")", "(", "c", "[", "bool", "]", "[", "]", ")", ")", "(",
        "v", "(", "p", ")", "(", "c", "[", "bool", "]", "[", "]", ")", ")"]
      (.node "tm_abs" [.leaf "name_tok" "p", bool,
        .node "tm_var" [.leaf "name_tok" "p", bool]]) = true := by
  decide +kernel

/-- Negative control: an abstraction binds a variable; reading `A(c(T)(..))(..)` as binding `T`
with `tm_abs` does not check. -/
theorem control_abstraction_binds_variable :
    check setting.grammar "hol_term"
      ["A", "(", "c", "(", "T", ")", "(", "c", "[", "bool", "]", "[", "]", ")", ")", "(",
        "v", "(", "p", ")", "(", "c", "[", "bool", "]", "[", "]", ")", ")"]
      (.node "tm_abs" [.leaf "name_tok" "T", bool,
        .node "tm_var" [.leaf "name_tok" "p", bool]]) = false := by
  decide +kernel

/-- Positive control: a keyword is a name where a name stands: a variable called `REFL`, and the
pair constant called `,`. -/
theorem control_keyword_names :
    check setting.grammar "hol_term" ["v", "(", "REFL", ")", "(", "c", "[", "bool", "]", "[", "]", ")"]
        (.node "tm_var" [.leaf "name_tok" "REFL", bool]) = true ∧
      check setting.grammar "hol_term" ["c", "(", ",", ")", "(", "c", "[", "bool", "]", "[", "]", ")"]
        (.node "tm_const" [.leaf "name_tok" ",", bool]) = true := by
  decide +kernel

/-- Negative control: a step that is not one of the thirteen (`SYM`) does not check as `TRANS`. -/
theorem control_unknown_step :
    check setting.grammar "step" ["\"", "SYM", "\"", ",", "3"]
      (.node "step_trans" [q, q, .leaf "num_tok" "3", .leaf "num_tok" "3"]) = false := by
  decide +kernel

end Mettapedia.GSLT.Readers.HOL.Correspondence
