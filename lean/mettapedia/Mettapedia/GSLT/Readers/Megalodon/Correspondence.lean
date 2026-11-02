import Mettapedia.GSLT.Readers.Megalodon.Tables
import Mettapedia.GSLT.Readers.GrammarCorrespondence

/-!
# The reader of Megalodon's record checks exactly the `.module` grammar

The generated readers (MeTTa and C) cut a `-sexprinfo` record into tokens with the version-2
profile of `SexprInfoSyntax.module`, parse with the SLR tables of `Tables.lean`, and accept an item
tree only if the tree check of `TreeCheck` passes. This file instantiates the generic results:

* `check_iff`: the tree check accepts exactly the token-level derivations of the lowered grammar;
* `reader_sound`, `reader_complete`: those derivations are exactly the derivations of the `.module`
  rows with the input's leaf rows (`GrammarCorrespondence`).

Controls: a declaration line, a theorem with its known, its unfolded definition, its proof and QED
(lines Megalodon printed for its own example), and refusals: a proof with its QED missing, an
unfolded definition after the proof, a known after an unfolded definition, and a proof term under
the wrong constructor. Not proved here: that the SLR engine finds a tree whenever one exists (the
tables are untrusted), and the agreement of the engines' tokenizers with `TokenProfileV2.tokenize`
(they are checked against each other on files).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Megalodon.Correspondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile (codes)
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.Megalodon

def tokenSorts : List String := Tables.spec.tokenSorts

/-- A token of a token sort, by the `.module`'s lexical layer. -/
def inSort (c x : String) : Bool := profile.tokenHasSort c (codes x)

def rows? : Option (List Prod) := grammar.terms.mapM (lowerRow tokenSorts)

def rows : List Prod := rows?.get (by decide +kernel)

theorem rows_lowered : grammar.terms.mapM (lowerRow tokenSorts) = some rows :=
  (Option.some_get _).symm

/-- The setting of Megalodon's record: the `.module` rows, their token sorts, and their lowering. -/
def setting : Setting :=
  { lang := grammar, tokenSorts, inSort, prods := rows, lowering := rows_lowered }

theorem rows_count : rows.length = 35 := by decide +kernel

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

/-- The tree check accepts exactly the derivations of the lowered grammar of Megalodon's record. -/
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

private def str (x : String) : Tree := .leaf "str_tok" ("\"" ++ x ++ "\"")
private def num (n : String) : Tree :=
  if n == "0" then .node "nat_zero" [.leaf "zero_tok" "0"] else .node "nat_pos" [.leaf "pos_tok" n]

/-- Positive control: `(DEF "False" "5bf6" 0 (PROP) (ALL (PROP) (DB 0)) 5)` (the definition of
`False`, its identity shortened) is a checked item. -/
theorem control_def :
    check setting.grammar "item"
      ["(", "DEF", "\"False\"", "\"5bf6\"", "0", "(", "PROP", ")", "(", "ALL", "(", "PROP", ")", "(",
        "DB", "0", ")", ")", "5", ")"]
      (.node "item_def" [str "False", str "5bf6", num "0", .node "tp_prop" [],
        .node "tm_all" [.node "tp_prop" [], .node "tm_db" [num "0"]], num "5"]) = true := by
  decide +kernel

private def thmLine : List String :=
  ["(", "THM", "\"t\"", "\"a1\"", "\"none\"", "0", "(", "IMP", "(", "TMH", "\"c3\"", ")", "(", "TMH",
    "\"c3\"", ")", ")", "1", ")"]

private def thmStatement : Tree :=
  .node "tm_imp" [.node "tm_tmh" [str "c3"], .node "tm_tmh" [str "c3"]]

private def identity : Tree := .node "pf_plam" [.node "tm_tmh" [str "c3"], .node "pf_hyp" [num "0"]]

private def identityToks : List String :=
  ["(", "PLAM", "(", "TMH", "\"c3\"", ")", "(", "HYP", "0", ")", ")"]

/-- Positive control: a theorem `c3 -> c3`, the known its check used, the definition it unfolded,
its proof `PLAM c3 (HYP 0)` and QED, in the order Megalodon prints them. -/
theorem control_theorem :
    check setting.grammar "item"
      (thmLine ++ ["(", "USESKNOWN", "\"k9\"", ")", "(", "DELTA", "\"c3\"", ")", "(", "PROOF", "\"t\""] ++
        identityToks ++ [")", "(", "QED", ")"])
      (.node "item_thm" [str "t", str "a1", str "none", num "0", thmStatement, num "1",
        .node "tail_uses" [str "k9",
          .node "tail_delta" [str "c3", .node "delta_proof" [str "t", identity]]]]) = true := by
  decide +kernel

/-- Negative control: the same theorem without its `(QED)` line is no item. -/
theorem control_missing_qed :
    check setting.grammar "item"
      (thmLine ++ ["(", "PROOF", "\"t\""] ++ identityToks ++ [")"])
      (.node "item_thm" [str "t", str "a1", str "none", num "0", thmStatement, num "1",
        .node "tail_proof" [str "t", identity]]) = false := by
  decide +kernel

/-- Negative control: an unfolded definition is listed before the proof, never after it; and a
known the check used is never listed after an unfolded definition (`delta_tail` has no
`USESKNOWN` row). -/
theorem control_order :
    check setting.grammar "thm_tail"
      (["(", "PROOF", "\"t\""] ++ identityToks ++ [")", "(", "DELTA", "\"c3\"", ")", "(", "QED", ")"])
      (.node "tail_proof" [str "t", identity]) = false ∧
    check setting.grammar "thm_tail"
      (["(", "DELTA", "\"c3\"", ")", "(", "USESKNOWN", "\"k9\"", ")", "(", "PROOF", "\"t\""] ++
        identityToks ++ [")", "(", "QED", ")"])
      (.node "tail_delta" [str "c3",
        .node "tail_uses" [str "k9", .node "tail_proof" [str "t", identity]]]) = false := by
  decide +kernel

/-- Negative control: a proof is not a term; `(PLAM (TMH "c3") (HYP 0))` does not check as an
implication term. -/
theorem control_proof_not_term :
    check setting.grammar "mg_term" identityToks
      (.node "tm_imp" [.node "tm_tmh" [str "c3"], .node "pf_hyp" [num "0"]]) = false := by
  decide +kernel

/-- Negative control: `007` is no number (OCaml's `string_of_int` never writes a leading zero), and
`0` is a number only as itself. -/
theorem control_numerals :
    check setting.grammar "mg_nat" ["007"] (.node "nat_pos" [.leaf "pos_tok" "007"]) = false ∧
      check setting.grammar "mg_nat" ["0"] (.node "nat_pos" [.leaf "pos_tok" "0"]) = false ∧
      check setting.grammar "mg_nat" ["0"] (.node "nat_zero" [.leaf "zero_tok" "0"]) = true ∧
      check setting.grammar "mg_nat" ["70"] (.node "nat_pos" [.leaf "pos_tok" "70"]) = true := by
  decide +kernel

end Mettapedia.GSLT.Readers.Megalodon.Correspondence
