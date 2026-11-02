import Mettapedia.GSLT.Readers.Megalodon.RecordUnique

/-!
# Every line of Megalodon's record is read as the line Megalodon printed

`Record.lean` and `RecordUnique.lean` read Megalodon's types, terms and proof terms exactly. This file
does the same for the record's lines: the declaration lines PRIM, PARAM, DEF, AXIOM, and a THM line
with what follows it (the knowns the check used, the definitions it unfolded, the proof and QED, or
QEDWITHADMITS, or ADMITTED), as `megalodon.ml` prints them with `-sexprinfo`. The check accepts
Megalodon's printing of every line with the line's own tree (`Item.reads`, `Item.checks`), and that
tree is the only one (`Item.reading_is_tree`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Megalodon.Record

open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.Megalodon.Correspondence
open Mettapedia.GSLT.Readers.Megalodon
open Mettapedia.GSLT.Readers.GrammarCorrespondence

/-! ## The record's lines -/

/-- What follows a theorem's first DELTA line: more unfolded definitions, then the proof and QED. -/
inductive DeltaTail where
  | more (h : String) (rest : DeltaTail)
  | proof (x : String) (d : Pf)
  deriving DecidableEq, Repr

/-- What follows a THM line. -/
inductive ThmTail where
  | uses (h : String) (rest : ThmTail)
  | delta (h : String) (rest : DeltaTail)
  | proof (x : String) (d : Pf)
  | admits
  | admitted
  deriving DecidableEq, Repr

/-- A declaration line, or a theorem with what follows its THM line. -/
inductive Item where
  | prim (i : Nat) (x h : String) (a : Tp) (ln : Nat)
  | param (x h : String) (k : Nat) (a : Tp) (ln : Nat)
  | defn (x h : String) (k : Nat) (a : Tp) (m : Tm) (ln : Nat)
  | ax (x h : String) (k : Nat) (p : Tm) (ln : Nat)
  | thm (x h g : String) (k : Nat) (p : Tm) (ln : Nat) (rest : ThmTail)
  deriving DecidableEq, Repr

/-! ## Megalodon's printing of them (the `-sexprinfo` lines of `megalodon.ml`) -/

def proofLines (x : String) (d : Pf) : List String :=
  ["(", "PROOF", quoted x] ++ d.toks ++ [")", "(", "QED", ")"]

def DeltaTail.toks : DeltaTail → List String
  | .more h rest => ["(", "DELTA", quoted h, ")"] ++ rest.toks
  | .proof x d => proofLines x d

def ThmTail.toks : ThmTail → List String
  | .uses h rest => ["(", "USESKNOWN", quoted h, ")"] ++ rest.toks
  | .delta h rest => ["(", "DELTA", quoted h, ")"] ++ rest.toks
  | .proof x d => proofLines x d
  | .admits => ["(", "QEDWITHADMITS", ")"]
  | .admitted => ["(", "ADMITTED", ")"]

def Item.toks : Item → List String
  | .prim i x h a ln => ["(", "PRIM", toString i, quoted x, quoted h] ++ a.toks ++ [toString ln, ")"]
  | .param x h k a ln => ["(", "PARAM", quoted x, quoted h, toString k] ++ a.toks ++ [toString ln, ")"]
  | .defn x h k a m ln =>
      ["(", "DEF", quoted x, quoted h, toString k] ++ a.toks ++ m.toks ++ [toString ln, ")"]
  | .ax x h k p ln => ["(", "AXIOM", quoted x, quoted h, toString k] ++ p.toks ++ [toString ln, ")"]
  | .thm x h g k p ln rest =>
      ["(", "THM", quoted x, quoted h, quoted g, toString k] ++ p.toks ++ [toString ln, ")"] ++ rest.toks

def DeltaTail.plain : DeltaTail → Bool
  | .more h rest => plainText h && rest.plain
  | .proof x d => plainText x && d.plain

def ThmTail.plain : ThmTail → Bool
  | .uses h rest => plainText h && rest.plain
  | .delta h rest => plainText h && rest.plain
  | .proof x d => plainText x && d.plain
  | .admits => true
  | .admitted => true

def Item.plain : Item → Bool
  | .prim _ x h _ _ => plainText x && plainText h
  | .param x h _ _ _ => plainText x && plainText h
  | .defn x h _ _ m _ => plainText x && plainText h && m.plain
  | .ax x h _ p _ => plainText x && plainText h && p.plain
  | .thm x h g _ p _ rest => plainText x && plainText h && plainText g && p.plain && rest.plain

/-! ## Their reader trees -/

def strLeaf (h : String) : Tree := .leaf "str_tok" (quoted h)

def DeltaTail.tree : DeltaTail → Tree
  | .more h rest => .node "delta_more" [strLeaf h, rest.tree]
  | .proof x d => .node "delta_proof" [strLeaf x, d.tree]

def ThmTail.tree : ThmTail → Tree
  | .uses h rest => .node "tail_uses" [strLeaf h, rest.tree]
  | .delta h rest => .node "tail_delta" [strLeaf h, rest.tree]
  | .proof x d => .node "tail_proof" [strLeaf x, d.tree]
  | .admits => .node "tail_admits" []
  | .admitted => .node "tail_admitted" []

def Item.tree : Item → Tree
  | .prim i x h a ln => .node "item_prim" [natTree i, strLeaf x, strLeaf h, a.tree, natTree ln]
  | .param x h k a ln => .node "item_param" [strLeaf x, strLeaf h, natTree k, a.tree, natTree ln]
  | .defn x h k a m ln => .node "item_def" [strLeaf x, strLeaf h, natTree k, a.tree, m.tree, natTree ln]
  | .ax x h k p ln => .node "item_axiom" [strLeaf x, strLeaf h, natTree k, p.tree, natTree ln]
  | .thm x h g k p ln rest =>
      .node "item_thm" [strLeaf x, strLeaf h, strLeaf g, natTree k, p.tree, natTree ln, rest.tree]

/-! ## The rows of the lines -/

theorem prod_item_prim : G.prodOf? "item_prim" = some ⟨"item_prim", "item", [.lit "(", .lit "PRIM",
    .nt "mg_nat", .tok "str_tok", .tok "str_tok", .nt "mg_type", .nt "mg_nat", .lit ")"]⟩ := by
  decide +kernel
theorem prod_item_param : G.prodOf? "item_param" = some ⟨"item_param", "item", [.lit "(", .lit "PARAM",
    .tok "str_tok", .tok "str_tok", .nt "mg_nat", .nt "mg_type", .nt "mg_nat", .lit ")"]⟩ := by
  decide +kernel
theorem prod_item_def : G.prodOf? "item_def" = some ⟨"item_def", "item", [.lit "(", .lit "DEF",
    .tok "str_tok", .tok "str_tok", .nt "mg_nat", .nt "mg_type", .nt "mg_term", .nt "mg_nat",
    .lit ")"]⟩ := by
  decide +kernel
theorem prod_item_axiom : G.prodOf? "item_axiom" = some ⟨"item_axiom", "item", [.lit "(", .lit "AXIOM",
    .tok "str_tok", .tok "str_tok", .nt "mg_nat", .nt "mg_term", .nt "mg_nat", .lit ")"]⟩ := by
  decide +kernel
theorem prod_item_thm : G.prodOf? "item_thm" = some ⟨"item_thm", "item", [.lit "(", .lit "THM",
    .tok "str_tok", .tok "str_tok", .tok "str_tok", .nt "mg_nat", .nt "mg_term", .nt "mg_nat",
    .lit ")", .nt "thm_tail"]⟩ := by
  decide +kernel
theorem prod_tail_uses : G.prodOf? "tail_uses" = some ⟨"tail_uses", "thm_tail", [.lit "(",
    .lit "USESKNOWN", .tok "str_tok", .lit ")", .nt "thm_tail"]⟩ := by
  decide +kernel
theorem prod_tail_delta : G.prodOf? "tail_delta" = some ⟨"tail_delta", "thm_tail", [.lit "(",
    .lit "DELTA", .tok "str_tok", .lit ")", .nt "delta_tail"]⟩ := by
  decide +kernel
theorem prod_tail_proof : G.prodOf? "tail_proof" = some ⟨"tail_proof", "thm_tail", [.lit "(",
    .lit "PROOF", .tok "str_tok", .nt "mg_proof", .lit ")", .lit "(", .lit "QED", .lit ")"]⟩ := by
  decide +kernel
theorem prod_tail_admits : G.prodOf? "tail_admits" = some ⟨"tail_admits", "thm_tail", [.lit "(",
    .lit "QEDWITHADMITS", .lit ")"]⟩ := by
  decide +kernel
theorem prod_tail_admitted : G.prodOf? "tail_admitted" = some ⟨"tail_admitted", "thm_tail", [.lit "(",
    .lit "ADMITTED", .lit ")"]⟩ := by
  decide +kernel
theorem prod_delta_more : G.prodOf? "delta_more" = some ⟨"delta_more", "delta_tail", [.lit "(",
    .lit "DELTA", .tok "str_tok", .lit ")", .nt "delta_tail"]⟩ := by
  decide +kernel
theorem prod_delta_proof : G.prodOf? "delta_proof" = some ⟨"delta_proof", "delta_tail", [.lit "(",
    .lit "PROOF", .tok "str_tok", .nt "mg_proof", .lit ")", .lit "(", .lit "QED", .lit ")"]⟩ := by
  decide +kernel

theorem str_sort : G.tokenSorts.contains "str_tok" = true := by rw [tokenSorts_G]; decide

/-! ## Completeness: Megalodon's printing of a line is read as that line -/

theorem DeltaTail.reads (t : DeltaTail) (ht : t.plain = true) :
    ∃ lb ks, t.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("delta_tail", t.toks) := by
  induction t with
  | more h rest ih =>
    simp only [DeltaTail.plain, Bool.and_eq_true] at ht
    obtain ⟨lr, kr, hr, hpr⟩ := ih ht.2
    refine ⟨"delta_more", [strLeaf h, rest.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_delta_more, strLeaf, hr, printItems_lit, printItems_lit,
      printItems_tok _ _ _ _ _ str_sort (inSort_str h ht.1), printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpr, printItems_nil]
    simp [DeltaTail.toks]
  | proof x d =>
    simp only [DeltaTail.plain, Bool.and_eq_true] at ht
    obtain ⟨ld, kd, hd, hpd⟩ := Pf.reads d ht.2
    refine ⟨"delta_proof", [strLeaf x, d.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_delta_proof, strLeaf, hd, printItems_lit, printItems_lit,
      printItems_tok _ _ _ _ _ str_sort (inSort_str x ht.1), printItems_nt _ _ _ _ _ _ _ hpd,
      printItems_lit, printItems_lit, printItems_lit, printItems_lit, printItems_nil]
    simp [DeltaTail.toks, proofLines]

theorem ThmTail.reads (t : ThmTail) (ht : t.plain = true) :
    ∃ lb ks, t.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("thm_tail", t.toks) := by
  induction t with
  | uses h rest ih =>
    simp only [ThmTail.plain, Bool.and_eq_true] at ht
    obtain ⟨lr, kr, hr, hpr⟩ := ih ht.2
    refine ⟨"tail_uses", [strLeaf h, rest.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tail_uses, strLeaf, hr, printItems_lit, printItems_lit,
      printItems_tok _ _ _ _ _ str_sort (inSort_str h ht.1), printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpr, printItems_nil]
    simp [ThmTail.toks]
  | delta h rest =>
    simp only [ThmTail.plain, Bool.and_eq_true] at ht
    obtain ⟨lr, kr, hr, hpr⟩ := DeltaTail.reads rest ht.2
    refine ⟨"tail_delta", [strLeaf h, rest.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tail_delta, strLeaf, hr, printItems_lit, printItems_lit,
      printItems_tok _ _ _ _ _ str_sort (inSort_str h ht.1), printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpr, printItems_nil]
    simp [ThmTail.toks]
  | proof x d =>
    simp only [ThmTail.plain, Bool.and_eq_true] at ht
    obtain ⟨ld, kd, hd, hpd⟩ := Pf.reads d ht.2
    refine ⟨"tail_proof", [strLeaf x, d.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tail_proof, strLeaf, hd, printItems_lit, printItems_lit,
      printItems_tok _ _ _ _ _ str_sort (inSort_str x ht.1), printItems_nt _ _ _ _ _ _ _ hpd,
      printItems_lit, printItems_lit, printItems_lit, printItems_lit, printItems_nil]
    simp [ThmTail.toks, proofLines]
  | admits => exact ⟨"tail_admits", [], rfl, by decide +kernel⟩
  | admitted => exact ⟨"tail_admitted", [], rfl, by decide +kernel⟩

theorem Item.reads (it : Item) (hi : it.plain = true) :
    ∃ lb ks, it.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("item", it.toks) := by
  cases it with
  | prim i x h a ln =>
    simp only [Item.plain, Bool.and_eq_true] at hi
    obtain ⟨li, ki, hni, hpi⟩ := nat_reads i
    obtain ⟨ll, kl, hnl, hpl⟩ := nat_reads ln
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    refine ⟨"item_prim", _, rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_item_prim, strLeaf, strLeaf, hni, hnl, ha, printItems_lit,
      printItems_lit, printItems_nt _ _ _ _ _ _ _ hpi,
      printItems_tok _ _ _ _ _ str_sort (inSort_str x hi.1),
      printItems_tok _ _ _ _ _ str_sort (inSort_str h hi.2), printItems_nt _ _ _ _ _ _ _ hpa,
      printItems_nt _ _ _ _ _ _ _ hpl, printItems_lit, printItems_nil]
    simp [Item.toks]
  | param x h k a ln =>
    simp only [Item.plain, Bool.and_eq_true] at hi
    obtain ⟨lk, kk, hnk, hpk⟩ := nat_reads k
    obtain ⟨ll, kl, hnl, hpl⟩ := nat_reads ln
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    refine ⟨"item_param", _, rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_item_param, strLeaf, strLeaf, hnk, hnl, ha, printItems_lit,
      printItems_lit, printItems_tok _ _ _ _ _ str_sort (inSort_str x hi.1),
      printItems_tok _ _ _ _ _ str_sort (inSort_str h hi.2), printItems_nt _ _ _ _ _ _ _ hpk,
      printItems_nt _ _ _ _ _ _ _ hpa, printItems_nt _ _ _ _ _ _ _ hpl, printItems_lit, printItems_nil]
    simp [Item.toks]
  | defn x h k a m ln =>
    simp only [Item.plain, Bool.and_eq_true] at hi
    obtain ⟨lk, kk, hnk, hpk⟩ := nat_reads k
    obtain ⟨ll, kl, hnl, hpl⟩ := nat_reads ln
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    obtain ⟨lm, km, hm, hpm⟩ := Tm.reads m hi.2
    refine ⟨"item_def", _, rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_item_def, strLeaf, strLeaf, hnk, hnl, ha, hm, printItems_lit,
      printItems_lit, printItems_tok _ _ _ _ _ str_sort (inSort_str x hi.1.1),
      printItems_tok _ _ _ _ _ str_sort (inSort_str h hi.1.2), printItems_nt _ _ _ _ _ _ _ hpk,
      printItems_nt _ _ _ _ _ _ _ hpa, printItems_nt _ _ _ _ _ _ _ hpm,
      printItems_nt _ _ _ _ _ _ _ hpl, printItems_lit, printItems_nil]
    simp [Item.toks]
  | ax x h k p ln =>
    simp only [Item.plain, Bool.and_eq_true] at hi
    obtain ⟨lk, kk, hnk, hpk⟩ := nat_reads k
    obtain ⟨ll, kl, hnl, hpl⟩ := nat_reads ln
    obtain ⟨lp, kp, hp, hpp⟩ := Tm.reads p hi.2
    refine ⟨"item_axiom", _, rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_item_axiom, strLeaf, strLeaf, hnk, hnl, hp, printItems_lit,
      printItems_lit, printItems_tok _ _ _ _ _ str_sort (inSort_str x hi.1.1),
      printItems_tok _ _ _ _ _ str_sort (inSort_str h hi.1.2), printItems_nt _ _ _ _ _ _ _ hpk,
      printItems_nt _ _ _ _ _ _ _ hpp, printItems_nt _ _ _ _ _ _ _ hpl, printItems_lit, printItems_nil]
    simp [Item.toks]
  | thm x h g k p ln rest =>
    simp only [Item.plain, Bool.and_eq_true] at hi
    obtain ⟨⟨⟨⟨hx, hh⟩, hg⟩, hp'⟩, hr'⟩ := hi
    obtain ⟨lk, kk, hnk, hpk⟩ := nat_reads k
    obtain ⟨ll, kl, hnl, hpl⟩ := nat_reads ln
    obtain ⟨lp, kp, hp, hpp⟩ := Tm.reads p hp'
    obtain ⟨lr, kr, hr, hpr⟩ := ThmTail.reads rest hr'
    refine ⟨"item_thm", _, rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_item_thm, strLeaf, strLeaf, strLeaf, hnk, hnl, hp, hr,
      printItems_lit, printItems_lit, printItems_tok _ _ _ _ _ str_sort (inSort_str x hx),
      printItems_tok _ _ _ _ _ str_sort (inSort_str h hh),
      printItems_tok _ _ _ _ _ str_sort (inSort_str g hg), printItems_nt _ _ _ _ _ _ _ hpk,
      printItems_nt _ _ _ _ _ _ _ hpp, printItems_nt _ _ _ _ _ _ _ hpl, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpr, printItems_nil]
    simp [Item.toks]

theorem Item.checks (it : Item) (hi : it.plain = true) : check G "item" it.toks it.tree = true := by
  obtain ⟨lb, ks, h, hp⟩ := Item.reads it hi
  simp [check, h, hp]

/-- The tree an engine returns for Megalodon's printing of a record line, once checked, is that
line's tree. -/
theorem Item.reading_is_tree (it : Item) (hi : it.plain = true) (t : Tree)
    (h : check G "item" it.toks t = true) : t = it.tree := by
  obtain ⟨lb, ks, hit, hp⟩ := Item.reads it hi
  have ht : printTree G t = some ("item", it.toks) := by
    simpa [check] using h
  rw [hit]
  exact (reads_unique (t.height + 1) t (.node lb ks) "item" it.toks it.toks [] []
    (Nat.lt_succ_self _) (by simp [objSorts, keywordSorts]) ht hp rfl).1

end Mettapedia.GSLT.Readers.Megalodon.Record
