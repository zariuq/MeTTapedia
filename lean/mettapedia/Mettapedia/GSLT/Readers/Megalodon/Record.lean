import Mettapedia.GSLT.Readers.Megalodon.Correspondence

/-!
# Reading Megalodon's record gives back the objects Megalodon printed

`Correspondence.lean` proves that the readers' tree check accepts exactly the derivations of the
`.module` rows. This file ties those rows to Megalodon itself: it states Megalodon's types, terms
and proof terms (`tp`, `tm`, `pf` of `syntax.ml`), its printers token by token (`tp_to_sexpr`,
`tm_to_sexpr`, `pf_to_sexpr`, which `-sexprinfo` uses), and proves that the check accepts
Megalodon's printing of every such object, with that object's own tree (`Tp.reads`, `Tm.reads`,
`Pf.reads`; `Tm.checks`, `Pf.checks`).

Numbers are printed as OCaml's `string_of_int` prints a natural number (`toString` here): the
`.module` reads exactly those, `0` or a nonzero digit followed by digits (`inSort_pos`,
`toDigits_head_ne_zero`). Names and identities are printed between double quotes, unescaped
(`quoted`); the reader reads any string without a double quote of printable bytes, spaces and
newlines (`plainText`, `inSort_str`), and Megalodon's names and identities are such strings.

The generic facts about the check's printer (`printItems_lit`, `printItems_nt`, `printItems_tok`,
`printItems_nil`, `printTree_node`) hold for every grammar.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Megalodon.Record

open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.TokenProfile (codes ByteSet)
open Mettapedia.GSLT.Readers.TokenProfileV2
open Mettapedia.GSLT.Readers.Megalodon.Correspondence
open Mettapedia.GSLT.Readers.Megalodon
open Mettapedia.GSLT.Readers.GrammarCorrespondence

/-! ## The printer of the tree check, item by item -/

theorem printItems_lit (g : Grammar) (s : String) (rest : List Sym) (kids : List Tree) :
    printItems g (.lit s :: rest) kids = (printItems g rest kids).map (s :: ·) := by
  cases kids with
  | nil =>
    simp only [printItems, leadingLits]
    by_cases h : (leadingLits rest).2 = [] <;> simp [h]
  | cons kid kids =>
    simp only [printItems, leadingLits]
    rcases hr : (leadingLits rest).2 with _ | ⟨sym, rest'⟩
    · simp
    · cases sym with
      | lit t => simp
      | eof => simp
      | tok c =>
        cases kid with
        | node l ks => simp
        | leaf c' x =>
          simp only
          split
          · cases printItems g rest' kids <;> simp
          · simp
      | nt n =>
        cases kid with
        | leaf c' x => simp
        | node l ks =>
          simp only
          rcases hp : printTree g (.node l ks) with _ | ⟨s', sub⟩
          · simp
          · simp only
            split
            · cases printItems g rest' kids <;> simp
            · simp

theorem printItems_nt (g : Grammar) (n : String) (rest : List Sym) (l : String) (ks kids : List Tree)
    (sub : List String) (h : printTree g (.node l ks) = some (n, sub)) :
    printItems g (.nt n :: rest) (.node l ks :: kids) = (printItems g rest kids).map (sub ++ ·) := by
  simp only [printItems, leadingLits, h]
  cases printItems g rest kids <;> simp

theorem printItems_tok (g : Grammar) (c x : String) (rest : List Sym) (kids : List Tree)
    (hc : g.tokenSorts.contains c = true) (hx : g.inSort c x = true) :
    printItems g (.tok c :: rest) (.leaf c x :: kids) = (printItems g rest kids).map (x :: ·) := by
  simp only [printItems, leadingLits, hc, hx]
  cases printItems g rest kids <;> simp

theorem printItems_nil (g : Grammar) : printItems g [] [] = some [] := by
  simp [printItems, leadingLits]

theorem printTree_node (g : Grammar) (l : String) (ks : List Tree) (p : Prod)
    (hp : g.prodOf? l = some p) :
    printTree g (.node l ks) = (printItems g p.rhs ks).map (fun toks => (p.lhs, toks)) := by
  simp only [printTree, hp]
  cases printItems g p.rhs ks <;> simp

/-! ## Megalodon's objects (syntax.ml: `tp`, `tm`, `pf`) -/

/-- Megalodon's simple types. -/
inductive Tp where
  | var (i : Nat)
  | prop
  | set
  | ar (a b : Tp)
  deriving DecidableEq, Repr

/-- Megalodon's terms: de Bruijn indices, declared constants by identity, primitives, type
application, application, abstraction, implication, universal quantification. -/
inductive Tm where
  | db (i : Nat)
  | tmh (h : String)
  | prim (i : Nat)
  | tpap (m : Tm) (a : Tp)
  | ap (m n : Tm)
  | lam (a : Tp) (m : Tm)
  | imp (m n : Tm)
  | all (a : Tp) (m : Tm)
  deriving DecidableEq, Repr

/-- Megalodon's proof terms: the seven cases its kernel checks. -/
inductive Pf where
  | hyp (i : Nat)
  | known (h : String)
  | tpap (d : Pf) (a : Tp)
  | tmap (d : Pf) (m : Tm)
  | pfap (d e : Pf)
  | plam (p : Tm) (d : Pf)
  | tlam (a : Tp) (d : Pf)
  deriving DecidableEq, Repr

/-! ## Megalodon's printers, token by token (`tp_to_sexpr`, `tm_to_sexpr`, `pf_to_sexpr`) -/

/-- A name or an identity as Megalodon prints it: between double quotes, unescaped. -/
def quoted (h : String) : String := "\"" ++ h ++ "\""

/-- A byte that can stand inside a printed string: no double quote; a printable byte, a space or a
newline. -/
def plainByte (n : Nat) : Bool := n != 34 && ((33 ≤ n && n ≤ 126) || n == 32 || n == 10)

def plainText (h : String) : Bool := h.toList.all (fun c => plainByte c.toNat)

def Tp.toks : Tp → List String
  | .var i => ["(", "TPVAR", toString i, ")"]
  | .prop => ["(", "PROP", ")"]
  | .set => ["(", "SET", ")"]
  | .ar a b => ["(", "AR"] ++ a.toks ++ b.toks ++ [")"]

def Tm.toks : Tm → List String
  | .db i => ["(", "DB", toString i, ")"]
  | .tmh h => ["(", "TMH", quoted h, ")"]
  | .prim i => ["(", "PRIM", toString i, ")"]
  | .tpap m a => ["(", "TPAP"] ++ m.toks ++ a.toks ++ [")"]
  | .ap m n => ["(", "AP"] ++ m.toks ++ n.toks ++ [")"]
  | .lam a m => ["(", "LAM"] ++ a.toks ++ m.toks ++ [")"]
  | .imp m n => ["(", "IMP"] ++ m.toks ++ n.toks ++ [")"]
  | .all a m => ["(", "ALL"] ++ a.toks ++ m.toks ++ [")"]

def Pf.toks : Pf → List String
  | .hyp i => ["(", "HYP", toString i, ")"]
  | .known h => ["(", "KNOWN", quoted h, ")"]
  | .tpap d a => ["(", "PTPAP"] ++ d.toks ++ a.toks ++ [")"]
  | .tmap d m => ["(", "PTMAP"] ++ d.toks ++ m.toks ++ [")"]
  | .pfap d e => ["(", "PPFAP"] ++ d.toks ++ e.toks ++ [")"]
  | .plam p d => ["(", "PLAM"] ++ p.toks ++ d.toks ++ [")"]
  | .tlam a d => ["(", "TLAM"] ++ a.toks ++ d.toks ++ [")"]

/-- Every string a term prints is plain. -/
def Tm.plain : Tm → Bool
  | .tmh h => plainText h
  | .tpap m _ => m.plain
  | .ap m n => m.plain && n.plain
  | .lam _ m => m.plain
  | .imp m n => m.plain && n.plain
  | .all _ m => m.plain
  | _ => true

def Pf.plain : Pf → Bool
  | .known h => plainText h
  | .tpap d _ => d.plain
  | .tmap d m => d.plain && m.plain
  | .pfap d e => d.plain && e.plain
  | .plam p d => p.plain && d.plain
  | .tlam _ d => d.plain
  | .hyp _ => true

/-! ## The reader's trees of Megalodon's objects -/

def natTree (i : Nat) : Tree :=
  if i = 0 then .node "nat_zero" [.leaf "zero_tok" "0"] else .node "nat_pos" [.leaf "pos_tok" (toString i)]

def Tp.tree : Tp → Tree
  | .var i => .node "tp_var" [natTree i]
  | .prop => .node "tp_prop" []
  | .set => .node "tp_set" []
  | .ar a b => .node "tp_ar" [a.tree, b.tree]

def Tm.tree : Tm → Tree
  | .db i => .node "tm_db" [natTree i]
  | .tmh h => .node "tm_tmh" [.leaf "str_tok" (quoted h)]
  | .prim i => .node "tm_prim" [natTree i]
  | .tpap m a => .node "tm_tpap" [m.tree, a.tree]
  | .ap m n => .node "tm_ap" [m.tree, n.tree]
  | .lam a m => .node "tm_lam" [a.tree, m.tree]
  | .imp m n => .node "tm_imp" [m.tree, n.tree]
  | .all a m => .node "tm_all" [a.tree, m.tree]

def Pf.tree : Pf → Tree
  | .hyp i => .node "pf_hyp" [natTree i]
  | .known h => .node "pf_known" [.leaf "str_tok" (quoted h)]
  | .tpap d a => .node "pf_tpap" [d.tree, a.tree]
  | .tmap d m => .node "pf_tmap" [d.tree, m.tree]
  | .pfap d e => .node "pf_pfap" [d.tree, e.tree]
  | .plam p d => .node "pf_plam" [p.tree, d.tree]
  | .tlam a d => .node "pf_tlam" [a.tree, d.tree]

/-! ## The grammar's rows for these objects -/

/-- The grammar the readers check against. -/
abbrev G : Grammar := setting.grammar

theorem tokenSorts_G : G.tokenSorts = ["zero_tok", "pos_tok", "str_tok"] := by decide +kernel

private abbrev l (s : String) : Sym := .lit s
private abbrev n (s : String) : Sym := .nt s

theorem prod_nat_zero : G.prodOf? "nat_zero" = some ⟨"nat_zero", "mg_nat", [.tok "zero_tok"]⟩ := by decide +kernel
theorem prod_nat_pos : G.prodOf? "nat_pos" = some ⟨"nat_pos", "mg_nat", [.tok "pos_tok"]⟩ := by decide +kernel
theorem prod_tp_var : G.prodOf? "tp_var" = some ⟨"tp_var", "mg_type", [l "(", l "TPVAR", n "mg_nat", l ")"]⟩ := by decide +kernel
theorem prod_tp_prop : G.prodOf? "tp_prop" = some ⟨"tp_prop", "mg_type", [l "(", l "PROP", l ")"]⟩ := by decide +kernel
theorem prod_tp_set : G.prodOf? "tp_set" = some ⟨"tp_set", "mg_type", [l "(", l "SET", l ")"]⟩ := by decide +kernel
theorem prod_tp_ar : G.prodOf? "tp_ar" = some ⟨"tp_ar", "mg_type", [l "(", l "AR", n "mg_type", n "mg_type", l ")"]⟩ := by decide +kernel
theorem prod_tm_db : G.prodOf? "tm_db" = some ⟨"tm_db", "mg_term", [l "(", l "DB", n "mg_nat", l ")"]⟩ := by decide +kernel
theorem prod_tm_tmh : G.prodOf? "tm_tmh" = some ⟨"tm_tmh", "mg_term", [l "(", l "TMH", .tok "str_tok", l ")"]⟩ := by decide +kernel
theorem prod_tm_prim : G.prodOf? "tm_prim" = some ⟨"tm_prim", "mg_term", [l "(", l "PRIM", n "mg_nat", l ")"]⟩ := by decide +kernel
theorem prod_tm_tpap : G.prodOf? "tm_tpap" = some ⟨"tm_tpap", "mg_term", [l "(", l "TPAP", n "mg_term", n "mg_type", l ")"]⟩ := by decide +kernel
theorem prod_tm_ap : G.prodOf? "tm_ap" = some ⟨"tm_ap", "mg_term", [l "(", l "AP", n "mg_term", n "mg_term", l ")"]⟩ := by decide +kernel
theorem prod_tm_lam : G.prodOf? "tm_lam" = some ⟨"tm_lam", "mg_term", [l "(", l "LAM", n "mg_type", n "mg_term", l ")"]⟩ := by decide +kernel
theorem prod_tm_imp : G.prodOf? "tm_imp" = some ⟨"tm_imp", "mg_term", [l "(", l "IMP", n "mg_term", n "mg_term", l ")"]⟩ := by decide +kernel
theorem prod_tm_all : G.prodOf? "tm_all" = some ⟨"tm_all", "mg_term", [l "(", l "ALL", n "mg_type", n "mg_term", l ")"]⟩ := by decide +kernel
theorem prod_pf_hyp : G.prodOf? "pf_hyp" = some ⟨"pf_hyp", "mg_proof", [l "(", l "HYP", n "mg_nat", l ")"]⟩ := by decide +kernel
theorem prod_pf_known : G.prodOf? "pf_known" = some ⟨"pf_known", "mg_proof", [l "(", l "KNOWN", .tok "str_tok", l ")"]⟩ := by decide +kernel
theorem prod_pf_tpap : G.prodOf? "pf_tpap" = some ⟨"pf_tpap", "mg_proof", [l "(", l "PTPAP", n "mg_proof", n "mg_type", l ")"]⟩ := by decide +kernel
theorem prod_pf_tmap : G.prodOf? "pf_tmap" = some ⟨"pf_tmap", "mg_proof", [l "(", l "PTMAP", n "mg_proof", n "mg_term", l ")"]⟩ := by decide +kernel
theorem prod_pf_pfap : G.prodOf? "pf_pfap" = some ⟨"pf_pfap", "mg_proof", [l "(", l "PPFAP", n "mg_proof", n "mg_proof", l ")"]⟩ := by decide +kernel
theorem prod_pf_plam : G.prodOf? "pf_plam" = some ⟨"pf_plam", "mg_proof", [l "(", l "PLAM", n "mg_term", n "mg_proof", l ")"]⟩ := by decide +kernel
theorem prod_pf_tlam : G.prodOf? "pf_tlam" = some ⟨"pf_tlam", "mg_proof", [l "(", l "TLAM", n "mg_type", n "mg_proof", l ")"]⟩ := by decide +kernel

/-! ## Printed numbers and strings are tokens of their sorts -/

theorem str_class : profile.classOf? "str_tok" = some ⟨"str_tok", .points [34],
    .minus (.union (.range 33 126) (.points [32, 10])) (.points [34]), [], some 34⟩ := by
  decide +kernel

theorem pos_class :
    profile.classOf? "pos_tok" = some ⟨"pos_tok", .range 49 57, .range 48 57, [], none⟩ := by
  decide +kernel

theorem inSort_str (h : String) (hp : plainText h = true) : G.inSort "str_tok" (quoted h) = true := by
  simp only [G, setting, Setting.grammar, Correspondence.inSort, Profile.tokenHasSort, str_class,
    quoted, codes, String.toList_append]
  simp only [TokenClass.has, List.map_append, List.map_nil]
  simp [ByteSet.contains, ByteSet.members, List.dropLast_append_of_ne_nil, List.getLast?_append]
  intro x hx
  simp only [plainText, List.all_eq_true] at hp
  have := hp x hx
  simp only [plainByte, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at this
  rcases this with ⟨h34, (⟨h1, h2⟩ | h32) | h10⟩
  · exact Or.inl ⟨⟨x.toNat - 33, by omega, by omega⟩, h34⟩
  · exact Or.inr (Or.inl h32)
  · exact Or.inr (Or.inr h10)

theorem digit_bounds (c : Char) (h : c.isDigit = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  unfold Char.isDigit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

/-- The leading digit of a positive number is not `0` (`string_of_int` writes no leading zero). -/
theorem toDigits_head_ne_zero : ∀ (n : Nat), n ≠ 0 → ∀ c cs, Nat.toDigits 10 n = c :: cs → c ≠ '0' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn c cs h
    rw [Nat.toDigits_eq_if (by decide)] at h
    split at h
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have : n ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · have hpos : n / 10 ≠ 0 := by omega
      obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 (n / 10) = d :: ds := by
        cases hq : Nat.toDigits 10 (n / 10) with
        | nil => exact absurd hq Nat.toDigits_ne_nil
        | cons d ds => exact ⟨d, ds, rfl⟩
      rw [hd] at h
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ih (n / 10) (by omega) hpos d ds hd

theorem inSort_pos (i : Nat) (hi : i ≠ 0) : G.inSort "pos_tok" (toString i) = true := by
  simp only [G, setting, Setting.grammar, Correspondence.inSort, Profile.tokenHasSort, pos_class, codes]
  have hl : (toString i).toList = Nat.toDigits 10 i := by simp [toString, Nat.repr]
  rw [hl]
  obtain ⟨c, cs, hc⟩ : ∃ c cs, Nat.toDigits 10 i = c :: cs := by
    cases hq : Nat.toDigits 10 i with
    | nil => exact absurd hq Nat.toDigits_ne_nil
    | cons d ds => exact ⟨d, ds, rfl⟩
  have hdig : ∀ d ∈ Nat.toDigits 10 i, 48 ≤ d.toNat ∧ d.toNat ≤ 57 :=
    fun d hd => digit_bounds d (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hd)
  have hne := toDigits_head_ne_zero i hi c cs hc
  rw [hc] at hdig ⊢
  simp only [TokenClass.has, List.map_cons]
  have hc0 : c.toNat ≠ 48 := by
    intro h
    apply hne
    have := Char.ofNat_toNat c
    rw [h] at this
    rw [← this]
  have hb := hdig c (by simp)
  simp [ByteSet.contains, ByteSet.members]
  refine ⟨⟨c.toNat - 49, by omega, by omega⟩, ?_⟩
  intro d hd
  have := hdig d (by simp [hd])
  exact ⟨d.toNat - 48, by omega, by omega⟩

/-! ## Completeness: Megalodon's printing of an object is read as that object -/

theorem nat_reads (i : Nat) :
    ∃ lb ks, natTree i = .node lb ks ∧ printTree G (.node lb ks) = some ("mg_nat", [toString i]) := by
  by_cases hi : i = 0
  · subst hi
    exact ⟨"nat_zero", [.leaf "zero_tok" "0"], by simp [natTree], by decide +kernel⟩
  · refine ⟨"nat_pos", [.leaf "pos_tok" (toString i)], by simp [natTree, hi], ?_⟩
    rw [printTree_node _ _ _ _ prod_nat_pos]
    rw [printItems_tok _ _ _ _ _ (by rw [tokenSorts_G]; decide) (inSort_pos i hi), printItems_nil]
    rfl

theorem Tp.reads (a : Tp) :
    ∃ lb ks, a.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("mg_type", a.toks) := by
  induction a with
  | var i =>
    obtain ⟨lb, ks, hn, hp⟩ := nat_reads i
    refine ⟨"tp_var", [natTree i], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tp_var, hn, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hp, printItems_lit, printItems_nil]
    simp [Tp.toks]
  | prop => exact ⟨"tp_prop", [], rfl, by decide +kernel⟩
  | set => exact ⟨"tp_set", [], rfl, by decide +kernel⟩
  | ar a b iha ihb =>
    obtain ⟨la, ka, ha, hpa⟩ := iha
    obtain ⟨lb, kb, hb, hpb⟩ := ihb
    refine ⟨"tp_ar", [a.tree, b.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tp_ar, ha, hb, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpa, printItems_nt _ _ _ _ _ _ _ hpb, printItems_lit, printItems_nil]
    simp [Tp.toks]

theorem Tm.reads (m : Tm) (hm : m.plain = true) :
    ∃ lb ks, m.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("mg_term", m.toks) := by
  induction m with
  | db i =>
    obtain ⟨lb, ks, hn, hp⟩ := nat_reads i
    refine ⟨"tm_db", [natTree i], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_db, hn, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hp, printItems_lit, printItems_nil]
    simp [Tm.toks]
  | tmh h =>
    refine ⟨"tm_tmh", [.leaf "str_tok" (quoted h)], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_tmh, printItems_lit, printItems_lit,
      printItems_tok _ _ _ _ _ (by rw [tokenSorts_G]; decide) (inSort_str h (by simpa [Tm.plain] using hm)),
      printItems_lit, printItems_nil]
    simp [Tm.toks]
  | prim i =>
    obtain ⟨lb, ks, hn, hp⟩ := nat_reads i
    refine ⟨"tm_prim", [natTree i], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_prim, hn, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hp, printItems_lit, printItems_nil]
    simp [Tm.toks]
  | tpap m a ihm =>
    obtain ⟨lm, km, hm', hpm⟩ := ihm (by simpa [Tm.plain] using hm)
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    refine ⟨"tm_tpap", [m.tree, a.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_tpap, hm', ha, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpm, printItems_nt _ _ _ _ _ _ _ hpa, printItems_lit, printItems_nil]
    simp [Tm.toks]
  | ap m k ihm ihk =>
    simp only [Tm.plain, Bool.and_eq_true] at hm
    obtain ⟨lm, km, hm', hpm⟩ := ihm hm.1
    obtain ⟨lk, kk, hk, hpk⟩ := ihk hm.2
    refine ⟨"tm_ap", [m.tree, k.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_ap, hm', hk, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpm, printItems_nt _ _ _ _ _ _ _ hpk, printItems_lit, printItems_nil]
    simp [Tm.toks]
  | lam a m ihm =>
    obtain ⟨lm, km, hm', hpm⟩ := ihm (by simpa [Tm.plain] using hm)
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    refine ⟨"tm_lam", [a.tree, m.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_lam, hm', ha, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpa, printItems_nt _ _ _ _ _ _ _ hpm, printItems_lit, printItems_nil]
    simp [Tm.toks]
  | imp m k ihm ihk =>
    simp only [Tm.plain, Bool.and_eq_true] at hm
    obtain ⟨lm, km, hm', hpm⟩ := ihm hm.1
    obtain ⟨lk, kk, hk, hpk⟩ := ihk hm.2
    refine ⟨"tm_imp", [m.tree, k.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_imp, hm', hk, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpm, printItems_nt _ _ _ _ _ _ _ hpk, printItems_lit, printItems_nil]
    simp [Tm.toks]
  | all a m ihm =>
    obtain ⟨lm, km, hm', hpm⟩ := ihm (by simpa [Tm.plain] using hm)
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    refine ⟨"tm_all", [a.tree, m.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_tm_all, hm', ha, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpa, printItems_nt _ _ _ _ _ _ _ hpm, printItems_lit, printItems_nil]
    simp [Tm.toks]

theorem Pf.reads (d : Pf) (hd : d.plain = true) :
    ∃ lb ks, d.tree = .node lb ks ∧ printTree G (.node lb ks) = some ("mg_proof", d.toks) := by
  induction d with
  | hyp i =>
    obtain ⟨lb, ks, hn, hp⟩ := nat_reads i
    refine ⟨"pf_hyp", [natTree i], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_pf_hyp, hn, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hp, printItems_lit, printItems_nil]
    simp [Pf.toks]
  | known h =>
    refine ⟨"pf_known", [.leaf "str_tok" (quoted h)], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_pf_known, printItems_lit, printItems_lit,
      printItems_tok _ _ _ _ _ (by rw [tokenSorts_G]; decide) (inSort_str h (by simpa [Pf.plain] using hd)),
      printItems_lit, printItems_nil]
    simp [Pf.toks]
  | tpap d a ihd =>
    obtain ⟨ld, kd, hd', hpd⟩ := ihd (by simpa [Pf.plain] using hd)
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    refine ⟨"pf_tpap", [d.tree, a.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_pf_tpap, hd', ha, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpd, printItems_nt _ _ _ _ _ _ _ hpa, printItems_lit, printItems_nil]
    simp [Pf.toks]
  | tmap d m ihd =>
    simp only [Pf.plain, Bool.and_eq_true] at hd
    obtain ⟨ld, kd, hd', hpd⟩ := ihd hd.1
    obtain ⟨lm, km, hm, hpm⟩ := Tm.reads m hd.2
    refine ⟨"pf_tmap", [d.tree, m.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_pf_tmap, hd', hm, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpd, printItems_nt _ _ _ _ _ _ _ hpm, printItems_lit, printItems_nil]
    simp [Pf.toks]
  | pfap d e ihd ihe =>
    simp only [Pf.plain, Bool.and_eq_true] at hd
    obtain ⟨ld, kd, hd', hpd⟩ := ihd hd.1
    obtain ⟨le, ke, he, hpe⟩ := ihe hd.2
    refine ⟨"pf_pfap", [d.tree, e.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_pf_pfap, hd', he, printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpd, printItems_nt _ _ _ _ _ _ _ hpe, printItems_lit, printItems_nil]
    simp [Pf.toks]
  | plam p d ihd =>
    simp only [Pf.plain, Bool.and_eq_true] at hd
    obtain ⟨lp, kp, hp, hpp⟩ := Tm.reads p hd.1
    obtain ⟨ld, kd, hd', hpd⟩ := ihd hd.2
    refine ⟨"pf_plam", [p.tree, d.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_pf_plam, hp, hd', printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpp, printItems_nt _ _ _ _ _ _ _ hpd, printItems_lit, printItems_nil]
    simp [Pf.toks]
  | tlam a d ihd =>
    obtain ⟨ld, kd, hd', hpd⟩ := ihd (by simpa [Pf.plain] using hd)
    obtain ⟨la, ka, ha, hpa⟩ := Tp.reads a
    refine ⟨"pf_tlam", [a.tree, d.tree], rfl, ?_⟩
    rw [printTree_node _ _ _ _ prod_pf_tlam, ha, hd', printItems_lit, printItems_lit,
      printItems_nt _ _ _ _ _ _ _ hpa, printItems_nt _ _ _ _ _ _ _ hpd, printItems_lit, printItems_nil]
    simp [Pf.toks]

/-- The check the engines run accepts Megalodon's printing of every proof term at its sort, with
the proof's own tree. -/
theorem Pf.checks (d : Pf) (hd : d.plain = true) : check G "mg_proof" d.toks d.tree = true := by
  obtain ⟨lb, ks, h, hp⟩ := Pf.reads d hd
  simp [check, h, hp]

theorem Tm.checks (m : Tm) (hm : m.plain = true) : check G "mg_term" m.toks m.tree = true := by
  obtain ⟨lb, ks, h, hp⟩ := Tm.reads m hm
  simp [check, h, hp]

end Mettapedia.GSLT.Readers.Megalodon.Record
