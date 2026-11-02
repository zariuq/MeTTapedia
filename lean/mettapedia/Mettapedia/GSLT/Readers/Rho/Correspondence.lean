import Mettapedia.GSLT.Readers.Rho.Tables
import Mettapedia.GSLT.Readers.GrammarCorrespondence

/-!
# The mrho reader checks exactly the `.module` grammar

The generated readers (MeTTa and C) cut an mrho file into tokens with the version-2 profile of
`MrhoSyntax.module`, parse with the SLR tables of `Tables.lean`, and accept an item tree only if the
tree check of `TreeCheck` passes. This file instantiates the generic results:

* `check_iff`: the tree check accepts exactly the token-level derivations of the lowered grammar;
* `reader_sound`, `reader_complete`: those derivations are exactly the derivations of the `.module`
  rows with the input's leaf rows (`GrammarCorrespondence`).

Controls: the reference's own first example (a send and a receive on `@0`), an empty parallel
composition, and refusals: a send with a third component, a name in a process position, a variable
in a process position, a quote in a binder position, and `(rho:nil)`; each is a program the
reference refuses. Not proved here: that the SLR engine finds a tree whenever one exists (the
tables are untrusted), and the agreement of the engines' tokenizers with `TokenProfileV2.tokenize`
(they are checked against each other on files).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Rho.Correspondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile (codes)
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.Rho

def tokenSorts : List String := Tables.spec.tokenSorts

/-- A token of a token sort, by the `.module`'s lexical layer. -/
def inSort (c x : String) : Bool := profile.tokenHasSort c (codes x)

def rows? : Option (List Prod) := grammar.terms.mapM (lowerRow tokenSorts)

def rows : List Prod := rows?.get (by decide +kernel)

theorem rows_lowered : grammar.terms.mapM (lowerRow tokenSorts) = some rows :=
  (Option.some_get _).symm

/-- The setting of the mrho syntax: the `.module` rows, their token sorts, and their lowering. -/
def setting : Setting :=
  { lang := grammar, tokenSorts, inSort, prods := rows, lowering := rows_lowered }

theorem rows_count : rows.length = 12 := by decide +kernel

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

/-- The tree check accepts exactly the derivations of the lowered mrho grammar. -/
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

private def var (x : String) : Tree := .leaf "var_tok" x
private def nil : Tree := .node "proc_nil" []
private def at0 : Tree := .node "name_quote" [nil]

/-- The reference's first example, `tests/rhocalc_run/core_comm_run.mrho`: a send on `@0` beside a
receive on `@0` that drops what it receives. -/
private def coreCommToks : List String :=
  ["(", "rho:par", "(", "rho:send", "(", "rho:quote", "rho:nil", ")", "rho:nil", ")", "(", "rho:recv",
    "(", "rho:quote", "rho:nil", ")", "$x", "(", "rho:drop", "$x", ")", ")", ")"]

private def coreCommTree : Tree :=
  .node "item_proc" [.node "proc_par" [.node "procs_more" [.node "proc_send" [at0, nil],
    .node "procs_more" [.node "proc_recv" [at0, var "$x", .node "proc_drop" [.node "name_var" [var "$x"]]],
      .node "procs_end" []]]]]

/-- Positive control: the reference's first example is a checked item, with the tree the C and
MeTTa readers print for it. -/
theorem control_core_comm : check setting.grammar "rho_item" coreCommToks coreCommTree = true := by
  decide +kernel

/-- Positive control: a parallel composition may have no component (the reference reads it as
`rho:nil`). -/
theorem control_par_empty :
    check setting.grammar "rho_proc" ["(", "rho:par", ")"]
      (.node "proc_par" [.node "procs_end" []]) = true := by
  decide +kernel

/-- Negative control: a send has a channel and one process; a third component is no send. -/
theorem control_send_extra :
    check setting.grammar "rho_proc" ["(", "rho:send", "$c", "rho:nil", "rho:nil", ")"]
      (.node "proc_send" [.node "name_var" [var "$c"], nil]) = false := by
  decide +kernel

/-- Negative controls: a name (a quoted process, or a variable) is no process. -/
theorem control_name_not_process :
    check setting.grammar "rho_proc" ["(", "rho:quote", "rho:nil", ")"]
        (.node "name_quote" [nil]) = false ∧
      check setting.grammar "rho_proc" ["$x"] (.node "name_var" [var "$x"]) = false := by
  decide +kernel

/-- Negative control: the binder of a receive is a variable, never a quoted process. -/
theorem control_quote_binder :
    check setting.grammar "rho_proc"
      ["(", "rho:recv", "$c", "(", "rho:quote", "rho:nil", ")", "rho:nil", ")"]
      (.node "proc_recv" [.node "name_var" [var "$c"], at0, nil]) = false := by
  decide +kernel

/-- Negative control: `rho:nil` is a symbol, not a form; `(rho:nil)` is no process. -/
theorem control_nil_paren :
    check setting.grammar "rho_proc" ["(", "rho:nil", ")"] nil = false := by
  decide +kernel

end Mettapedia.GSLT.Readers.Rho.Correspondence
