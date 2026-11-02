import Mettapedia.GSLT.Readers.Vibe.Tables
import Mettapedia.GSLT.Readers.GrammarCorrespondence

/-!
# The reader of Vibe's checker input checks exactly the `.module` grammar, byte for byte

The generated readers (MeTTa and C) cut a checker file into tokens with the binary profile of
`CheckStreamSyntax.module` (context-aware: the next token is cut with the token sorts the parser
can use), parse with the SLR tables of `Tables.lean`, and accept an instruction tree only if the
binary check `BinaryTokens.readB` passes: the tree prints back from the rows to tokens whose bytes
are the input, and every row's counts hold. This file instantiates the generic results:

* `check_iff`: the tree check accepts exactly the token-level derivations of the lowered grammar;
* `reader_sound`, `reader_complete`: those derivations are exactly the derivations of the `.module`
  rows with the input's leaf rows (`GrammarCorrespondence`);
* `readB_iff`: the binary check accepts exactly the derivations whose tokens spell the input bytes
  and whose rows' counts hold.

Controls: instructions as `check_test` writes them (a literal, an application, simultaneous
instantiation with one count governing two lists, a definition with empty lists), and refusals: a
count that disagrees with its list or its bytes, a list with no count before it, a word written with
more bytes than it needs, a tree whose tokens spell other bytes, and an axiom read as a proof-file
instruction.

Not proved here: that the SLR engine finds a tree whenever one exists (the tables are untrusted),
and that the engines' scanners equal `BinaryTokens.Kind.scanLen?` (they are checked against each
other and against the `.module`'s tables on files).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Vibe.Correspondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.BinaryTokens
open Mettapedia.GSLT.Readers.Vibe

def tokenSorts : List String := Tables.proofSpec.tokenSorts

/-- A token of a token sort, the counts aside, by the `.module`'s binary profile. -/
def inSort (c x : String) : Bool := profile.inSort c x

def rows? : Option (List Prod) := grammar.terms.mapM (lowerRow tokenSorts)

def rows : List Prod := rows?.get (by decide +kernel)

theorem rows_lowered : grammar.terms.mapM (lowerRow tokenSorts) = some rows :=
  (Option.some_get _).symm

/-- The setting of Vibe's checker input: the `.module` rows, their token sorts, their lowering. -/
def setting : Setting :=
  { lang := grammar, tokenSorts, inSort, prods := rows, lowering := rows_lowered }

theorem rows_count : rows.length = 33 := by decide +kernel

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

/-- The grammar the readers check against. -/
abbrev G : Grammar := setting.grammar

/-- The tree check accepts exactly the derivations of the lowered grammar of the checker input. -/
theorem check_iff (t : Tree) (s : String) (toks : List String) :
    check G s toks t = true ↔ Derives G s toks t :=
  TreeCheck.check_iff G wellFormed t s toks

/-- A tree the check accepts is a derivation of the `.module` rows with the leaf rows of its
tokens. -/
theorem reader_sound (t : Tree) (s : String) (toks : List String) (h : check G s toks t = true) :
    GDerives (setting.leaves toks) s toks (toPattern t) :=
  (reader_correspondence setting admissible toks s toks (fun _ hx => hx)).1 t ((check_iff t s toks).mp h)

/-- Every derivation of the `.module` rows with the leaf rows of the tokens is a tree the check
accepts. -/
theorem reader_complete (P : Pattern) (s : String) (toks : List String)
    (h : GDerives (setting.leaves toks) s toks P) :
    ∃ t, toPattern t = P ∧ check G s toks t = true := by
  obtain ⟨t, ht, hd⟩ := (reader_correspondence setting admissible toks s toks (fun _ hx => hx)).2 P h
  exact ⟨t, ht, (check_iff t s toks).mpr hd⟩

/-- The binary check: a tree reads the bytes `bs` at sort `s` exactly when it derives tokens that
spell `bs` and every row's counts hold. -/
theorem readB_iff (s : String) (bs : List Nat) (t : Tree) :
    readB G profile s bs t = true ↔
      ∃ toks, Derives G s toks t ∧ joinBytes toks = bs ∧ countsTree profile t = true :=
  BinaryTokens.readB_iff G wellFormed profile s bs t

/-! ## Controls -/

private def leaf (c : String) (bs : List Nat) : Tree := .leaf c (strOf bs)

/-- Positive control: `5 2 104 105 7` is TERM_NEW_LITERAL of the two bytes `hi` into term slot 7. -/
theorem control_literal :
    readB G profile "instr" [5, 2, 104, 105, 7]
      (.node "term_new_literal" [leaf "op5" [5], leaf "u_count" [2], leaf "u_bytes" [104, 105],
        leaf "u_dst_term" [7]]) = true := by
  decide +kernel

/-- Positive control: `6 3 2 2 1 3` (check_test's `define_challenge`) applies symbol 3 to terms 2
and 1, into term slot 3. -/
theorem control_app :
    readB G profile "instr" [6, 3, 2, 2, 1, 3]
      (.node "term_new_app" [leaf "op6" [6], leaf "u_sym" [3], leaf "u_count" [2],
        leaf "u_terms" [2, 1], leaf "u_dst_term" [3]]) = true := by
  decide +kernel

/-- Positive control: one count governs both lists of THM_INSTANTIATE_N, after the theorem operand:
`26 2 1 13 14 2 3 9`. -/
theorem control_instantiate_n :
    readB G profile "proof_instr" [26, 2, 1, 13, 14, 2, 3, 9]
      (.node "thm_instantiate_n" [leaf "op26" [26], leaf "u_count" [2], leaf "u_thm" [1],
        leaf "u_syms" [13, 14], leaf "u_terms" [2, 3], leaf "u_dst_thm" [9]]) = true := by
  decide +kernel

/-- Positive control: DEFINE_CONST with two empty lists (check_test's `define_challenge`):
`17 0 0 1 13 1`. -/
theorem control_define :
    readB G profile "instr" [17, 0, 0, 1, 13, 1]
      (.node "define_const" [leaf "op17" [17], leaf "u_count" [0], leaf "u_syms" [],
        leaf "u_count" [0], leaf "u_nats" [], leaf "u_term" [1], leaf "u_dst_sym" [13],
        leaf "u_dst_thm" [1]]) = true := by
  decide +kernel

/-- Positive control: a word of three bytes, `249 44 1` (300), as LITISNAT's value. -/
theorem control_long_word :
    readB G profile "proof_instr" [18, 249, 44, 1, 9]
      (.node "thm_lit_is_nat" [leaf "op18" [18], leaf "u_nat" [249, 44, 1],
        leaf "u_dst_thm" [9]]) = true := by
  decide +kernel

/-- Negative controls: the counts. A literal whose count says 3 but whose bytes are two; a list of
two terms under a count of one; the second list of THM_INSTANTIATE_N shorter than the count. -/
theorem control_counts :
    readB G profile "instr" [5, 3, 104, 105, 7]
      (.node "term_new_literal" [leaf "op5" [5], leaf "u_count" [3], leaf "u_bytes" [104, 105],
        leaf "u_dst_term" [7]]) = false ∧
    readB G profile "instr" [6, 3, 1, 2, 1, 3]
      (.node "term_new_app" [leaf "op6" [6], leaf "u_sym" [3], leaf "u_count" [1],
        leaf "u_terms" [2, 1], leaf "u_dst_term" [3]]) = false ∧
    readB G profile "proof_instr" [26, 2, 1, 13, 14, 2, 9]
      (.node "thm_instantiate_n" [leaf "op26" [26], leaf "u_count" [2], leaf "u_thm" [1],
        leaf "u_syms" [13, 14], leaf "u_terms" [2], leaf "u_dst_thm" [9]]) = false := by
  decide +kernel

/-- Negative controls: words. `248 5` writes five with a header (five fits in one byte); `249 1 0`
ends its payload in a zero byte. -/
theorem control_noncanonical :
    readB G profile "proof_instr" [18, 248, 5, 9]
      (.node "thm_lit_is_nat" [leaf "op18" [18], leaf "u_nat" [248, 5], leaf "u_dst_thm" [9]]) = false ∧
    readB G profile "proof_instr" [18, 249, 1, 0, 9]
      (.node "thm_lit_is_nat" [leaf "op18" [18], leaf "u_nat" [249, 1, 0], leaf "u_dst_thm" [9]]) = false := by
  decide +kernel

/-- Negative controls: a tree whose tokens spell other bytes than the input; an axiom is no
proof-file instruction (ADD_AXIOM's row has the sort `setup_instr`). -/
theorem control_other :
    readB G profile "instr" [5, 2, 104, 105, 8]
      (.node "term_new_literal" [leaf "op5" [5], leaf "u_count" [2], leaf "u_bytes" [104, 105],
        leaf "u_dst_term" [7]]) = false ∧
    readB G profile "proof_instr" [9, 1, 3]
      (.node "add_axiom" [leaf "op9" [9], leaf "u_term" [1], leaf "u_dst_thm" [3]]) = false ∧
    readB G profile "setup_instr" [9, 1, 3]
      (.node "add_axiom" [leaf "op9" [9], leaf "u_term" [1], leaf "u_dst_thm" [3]]) = true := by
  decide +kernel

end Mettapedia.GSLT.Readers.Vibe.Correspondence
