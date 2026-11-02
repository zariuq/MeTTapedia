import Mettapedia.GSLT.Readers.Megalodon.Record

/-!
# Megalodon's printing of an object has exactly one reading

`Record.lean` proves that the readers' tree check accepts Megalodon's printing of every type, term
and proof term with that object's own tree. This file proves that it is the only tree: at the sorts
of numbers, types, terms, proof terms, record lines and what follows a theorem line, two checked
trees whose token lists are prefixes of one token stream are equal and cover the same tokens
(`reads_unique`). So the tree an engine returns for Megalodon's printing of a proof term is that
proof term's tree (`Pf.reading_is_tree`), whatever the (untrusted) parse did.

The argument is unique readability of prefix notation: every row of these sorts begins with `(` and
a keyword no other row of its sort has, or is a single number token, and `0` is no positive number
(`head_rows`, `rows_by_head`, `nat_rows`, `zero_not_pos`); the children then follow in order
(`items_unique`). Only the sort of whole files is left out: its empty row is a prefix of every file.
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

/-- The phrase sorts whose rows begin with `(` and a keyword. -/
def keywordSorts : List String :=
  ["mg_type", "mg_term", "mg_proof", "item", "thm_tail", "delta_tail"]

/-- The phrase sorts of Megalodon's objects and record lines: numbers and the keyword sorts. -/
def objSorts : List String := "mg_nat" :: keywordSorts

/-! ## Facts about the rows, decided -/

/-- A row of a keyword sort begins with `(` and a keyword. -/
def openKeyword (p : Prod) : Bool :=
  match p.rhs with
  | .lit "(" :: .lit _ :: _ => true
  | _ => false

theorem head_rows : ∀ p ∈ G.prods, p.lhs ∈ keywordSorts → openKeyword p = true := by
  decide +kernel

/-- Two rows of one sort with the same first two items are the same row. -/
theorem rows_by_head : ∀ p ∈ G.prods, ∀ q ∈ G.prods, p.lhs = q.lhs →
    p.rhs.take 2 = q.rhs.take 2 → p = q := by
  decide +kernel

theorem nat_rows : ∀ p ∈ G.prods, p.lhs = "mg_nat" →
    p.rhs = [.tok "zero_tok"] ∨ p.rhs = [.tok "pos_tok"] := by
  decide +kernel

/-- The children of the rows of these sorts are of these sorts. -/
theorem kid_sorts : ∀ p ∈ G.prods, p.lhs ∈ objSorts → ∀ m, .nt m ∈ p.rhs → m ∈ objSorts := by
  have h : ∀ p ∈ G.prods, p.lhs ∈ objSorts →
      (p.rhs.all fun sym => match sym with | .nt m => objSorts.contains m | _ => true) = true := by
    decide +kernel
  intro p hp hs m hm
  have := h p hp hs
  rw [List.all_eq_true] at this
  have := this (.nt m) hm
  simpa using this

theorem objSorts_not_tokens : ∀ s ∈ objSorts, G.tokenSorts.contains s = false := by
  decide +kernel

theorem zero_class :
    profile.classOf? "zero_tok" = some ⟨"zero_tok", .points [48], .minus (.points [48]) (.points [48]), [], none⟩ := by
  decide +kernel

/-- `0` is no positive number. -/
theorem zero_not_pos (x : String) (hz : G.inSort "zero_tok" x = true)
    (hp : G.inSort "pos_tok" x = true) : False := by
  simp only [G, setting, Setting.grammar, Correspondence.inSort, Profile.tokenHasSort, zero_class,
    pos_class] at hz hp
  cases hx : codes x with
  | nil => rw [hx] at hz; simp [TokenClass.has] at hz
  | cons b bs =>
    rw [hx] at hz hp
    simp [TokenClass.has, ByteSet.contains, ByteSet.members] at hz hp
    omega

/-! ## Inverting the check's printer -/

theorem prodOf_mem (g : Grammar) (lb : String) (p : Prod) (h : g.prodOf? lb = some p) :
    p ∈ g.prods ∧ p.label = lb := by
  unfold Grammar.prodOf? at h
  split at h
  · rename_i q hq
    simp only [Option.some.injEq] at h
    subst h
    have : q ∈ g.prods.filter (·.label == lb) := by rw [hq]; simp
    simp only [List.mem_filter, beq_iff_eq] at this
    exact this
  · simp at h

theorem printTree_node_inv (g : Grammar) (lb : String) (ks : List Tree) (s : String)
    (u : List String) (h : printTree g (.node lb ks) = some (s, u)) :
    ∃ p, g.prodOf? lb = some p ∧ p.lhs = s ∧ printItems g p.rhs ks = some u := by
  cases hp : g.prodOf? lb with
  | none => simp [printTree, hp] at h
  | some p =>
    rw [printTree_node g lb ks p hp] at h
    cases hi : printItems g p.rhs ks with
    | none => simp [hi] at h
    | some u' =>
      simp only [hi, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p, rfl, h.1, by rw [hi, h.2]⟩

theorem printTree_leaf_inv (g : Grammar) (c x s : String) (u : List String)
    (h : printTree g (.leaf c x) = some (s, u)) : s = c ∧ g.tokenSorts.contains c = true := by
  simp only [printTree] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    simp only [Bool.and_eq_true] at hc
    exact ⟨h.1.symm, hc.1⟩
  · simp at h

theorem printItems_nil_inv (g : Grammar) (kids : List Tree) (u : List String)
    (h : printItems g [] kids = some u) : kids = [] ∧ u = [] := by
  cases kids with
  | nil => simp [printItems, leadingLits] at h; exact ⟨rfl, h⟩
  | cons k ks => simp [printItems, leadingLits] at h

theorem printItems_eof (g : Grammar) (rest : List Sym) (kids : List Tree) :
    printItems g (.eof :: rest) kids = none := by
  cases kids with
  | nil => simp [printItems, leadingLits]
  | cons k ks => simp [printItems, leadingLits]

theorem printItems_lit_inv (g : Grammar) (s : String) (rest : List Sym) (kids : List Tree)
    (u : List String) (h : printItems g (.lit s :: rest) kids = some u) :
    ∃ u', printItems g rest kids = some u' ∧ u = s :: u' := by
  rw [printItems_lit] at h
  cases h' : printItems g rest kids with
  | none => simp [h'] at h
  | some u' =>
    simp only [h', Option.map_some, Option.some.injEq] at h
    exact ⟨u', rfl, h.symm⟩

theorem printItems_tok_inv (g : Grammar) (c : String) (rest : List Sym) (kids : List Tree)
    (u : List String) (h : printItems g (.tok c :: rest) kids = some u) :
    ∃ x kids' u', kids = .leaf c x :: kids' ∧ g.inSort c x = true ∧
      printItems g rest kids' = some u' ∧ u = x :: u' := by
  cases kids with
  | nil => simp [printItems, leadingLits] at h
  | cons kid kids' =>
    cases kid with
    | node lb ks => simp [printItems, leadingLits] at h
    | leaf c' x =>
      simp only [printItems, leadingLits] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨rfl, -⟩, hx⟩ := hc
        cases h' : printItems g rest kids' with
        | none => simp [h'] at h
        | some u' =>
          simp only [h', Option.some.injEq, List.nil_append] at h
          exact ⟨x, kids', u', rfl, hx, h', h.symm⟩
      · simp at h

theorem printItems_nt_inv (g : Grammar) (n : String) (rest : List Sym) (kids : List Tree)
    (u : List String) (h : printItems g (.nt n :: rest) kids = some u) :
    ∃ k kids' sub u', kids = k :: kids' ∧ printTree g k = some (n, sub) ∧
      printItems g rest kids' = some u' ∧ u = sub ++ u' := by
  cases kids with
  | nil => simp [printItems, leadingLits] at h
  | cons kid kids' =>
    cases kid with
    | leaf c x => simp [printItems, leadingLits] at h
    | node lb ks =>
      simp only [printItems, leadingLits] at h
      cases hp : printTree g (.node lb ks) with
      | none => simp [hp] at h
      | some r =>
        obtain ⟨s', sub⟩ := r
        simp only [hp] at h
        split at h
        · rename_i hs
          cases h' : printItems g rest kids' with
          | none => simp [h'] at h
          | some u' =>
            simp only [h', Option.some.injEq, List.nil_append] at h
            exact ⟨.node lb ks, kids', sub, u', rfl, by rw [hp]; rw [beq_iff_eq] at hs; rw [hs], h', h.symm⟩
        · simp at h

/-! ## Unique reading -/

theorem height_le_of_mem : ∀ (kids : List Tree) (k : Tree), k ∈ kids → k.height ≤ heights kids
  | [], _, h => by simp at h
  | t :: ts, k, h => by
      simp only [List.mem_cons] at h
      simp only [heights]
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (height_le_of_mem ts k h) (Nat.le_max_right _ _)

/-- The children of one row: equal when their printings are prefixes of one stream, given that
their subtrees read uniquely. -/
theorem items_unique (rhs : List Sym) (hrhs : ∀ m, .nt m ∈ rhs → m ∈ objSorts) :
    ∀ (ks1 ks2 : List Tree) (u1 u2 r1 r2 : List String),
    (∀ k ∈ ks1, ∀ (t2 : Tree) (s : String) (v1 v2 q1 q2 : List String), s ∈ objSorts →
      printTree G k = some (s, v1) → printTree G t2 = some (s, v2) → v1 ++ q1 = v2 ++ q2 →
      k = t2 ∧ v1 = v2) →
    printItems G rhs ks1 = some u1 → printItems G rhs ks2 = some u2 → u1 ++ r1 = u2 ++ r2 →
    ks1 = ks2 ∧ u1 = u2 := by
  induction rhs with
  | nil =>
    intro ks1 ks2 u1 u2 r1 r2 _ h1 h2 _
    obtain ⟨rfl, rfl⟩ := printItems_nil_inv G ks1 u1 h1
    obtain ⟨rfl, rfl⟩ := printItems_nil_inv G ks2 u2 h2
    exact ⟨rfl, rfl⟩
  | cons sym rest ih =>
    intro ks1 ks2 u1 u2 r1 r2 hk h1 h2 he
    have hrest : ∀ m, .nt m ∈ rest → m ∈ objSorts := fun m hm => hrhs m (List.mem_cons_of_mem _ hm)
    cases sym with
    | eof => rw [printItems_eof] at h1; cases h1
    | lit s =>
      obtain ⟨u1', h1', rfl⟩ := printItems_lit_inv G s rest ks1 u1 h1
      obtain ⟨u2', h2', rfl⟩ := printItems_lit_inv G s rest ks2 u2 h2
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨hks, hu⟩ := ih hrest ks1 ks2 u1' u2' r1 r2 hk h1' h2' he
      exact ⟨hks, by rw [hu]⟩
    | tok c =>
      obtain ⟨x1, ks1', u1', rfl, -, h1', rfl⟩ := printItems_tok_inv G c rest ks1 u1 h1
      obtain ⟨x2, ks2', u2', rfl, -, h2', rfl⟩ := printItems_tok_inv G c rest ks2 u2 h2
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he'⟩ := he
      have hk' : ∀ k ∈ ks1', ∀ (t2 : Tree) (s : String) (v1 v2 q1 q2 : List String), s ∈ objSorts →
          printTree G k = some (s, v1) → printTree G t2 = some (s, v2) → v1 ++ q1 = v2 ++ q2 →
          k = t2 ∧ v1 = v2 := fun k hk2 => hk k (List.mem_cons_of_mem _ hk2)
      obtain ⟨hks, hu⟩ := ih hrest ks1' ks2' u1' u2' r1 r2 hk' h1' h2' he'
      exact ⟨by rw [hks], by rw [hu]⟩
    | nt m =>
      obtain ⟨k1, ks1', sub1, u1', rfl, hp1, h1', rfl⟩ := printItems_nt_inv G m rest ks1 u1 h1
      obtain ⟨k2, ks2', sub2, u2', rfl, hp2, h2', rfl⟩ := printItems_nt_inv G m rest ks2 u2 h2
      have hm : m ∈ objSorts := hrhs m (List.mem_cons_self)
      have he1 : sub1 ++ (u1' ++ r1) = sub2 ++ (u2' ++ r2) := by
        simpa only [List.append_assoc] using he
      obtain ⟨rfl, rfl⟩ := hk k1 List.mem_cons_self k2 m sub1 sub2 (u1' ++ r1) (u2' ++ r2) hm hp1 hp2 he1
      have he' : u1' ++ r1 = u2' ++ r2 := List.append_cancel_left he1
      have hk' : ∀ k ∈ ks1', ∀ (t2 : Tree) (s : String) (v1 v2 q1 q2 : List String), s ∈ objSorts →
          printTree G k = some (s, v1) → printTree G t2 = some (s, v2) → v1 ++ q1 = v2 ++ q2 →
          k = t2 ∧ v1 = v2 := fun k hk2 => hk k (List.mem_cons_of_mem _ hk2)
      obtain ⟨hks, hu⟩ := ih hrest ks1' ks2' u1' u2' r1 r2 hk' h1' h2' he'
      exact ⟨by rw [hks], by rw [hu]⟩

/-- Two rows of one of these sorts whose printings are prefixes of one stream are the same row. -/
theorem row_unique (p1 p2 : Prod) (hp1 : p1 ∈ G.prods) (hp2 : p2 ∈ G.prods) (s : String)
    (hs : s ∈ objSorts) (hl1 : p1.lhs = s) (hl2 : p2.lhs = s) (ks1 ks2 : List Tree)
    (u1 u2 r1 r2 : List String) (h1 : printItems G p1.rhs ks1 = some u1)
    (h2 : printItems G p2.rhs ks2 = some u2) (he : u1 ++ r1 = u2 ++ r2) : p1 = p2 := by
  have hlhs : p1.lhs = p2.lhs := by rw [hl1, hl2]
  by_cases hnat : s = "mg_nat"
  · subst hnat
    rcases nat_rows p1 hp1 hl1 with e1 | e1 <;> rcases nat_rows p2 hp2 hl2 with e2 | e2
    · exact rows_by_head p1 hp1 p2 hp2 hlhs (by rw [e1, e2])
    · rw [e1] at h1; rw [e2] at h2
      obtain ⟨x1, _, u1', rfl, hx1, _, rfl⟩ := printItems_tok_inv G _ _ ks1 u1 h1
      obtain ⟨x2, _, u2', rfl, hx2, _, rfl⟩ := printItems_tok_inv G _ _ ks2 u2 h2
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact (zero_not_pos x1 hx1 hx2).elim
    · rw [e1] at h1; rw [e2] at h2
      obtain ⟨x1, _, u1', rfl, hx1, _, rfl⟩ := printItems_tok_inv G _ _ ks1 u1 h1
      obtain ⟨x2, _, u2', rfl, hx2, _, rfl⟩ := printItems_tok_inv G _ _ ks2 u2 h2
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      exact (zero_not_pos x1 hx2 hx1).elim
    · exact rows_by_head p1 hp1 p2 hp2 hlhs (by rw [e1, e2])
  · have hs' : s ∈ keywordSorts := (List.mem_cons.mp hs).resolve_left hnat
    have o1 := head_rows p1 hp1 (by rw [hl1]; exact hs')
    have o2 := head_rows p2 hp2 (by rw [hl2]; exact hs')
    obtain ⟨k1, rest1, e1⟩ : ∃ k rest, p1.rhs = .lit "(" :: .lit k :: rest := by
      unfold openKeyword at o1
      split at o1
      · rename_i k rest heq; exact ⟨k, rest, heq⟩
      · simp at o1
    obtain ⟨k2, rest2, e2⟩ : ∃ k rest, p2.rhs = .lit "(" :: .lit k :: rest := by
      unfold openKeyword at o2
      split at o2
      · rename_i k rest heq; exact ⟨k, rest, heq⟩
      · simp at o2
    rw [e1] at h1; rw [e2] at h2
    obtain ⟨a1, h1a, rfl⟩ := printItems_lit_inv G _ _ ks1 u1 h1
    obtain ⟨b1, _, rfl⟩ := printItems_lit_inv G _ _ ks1 a1 h1a
    obtain ⟨a2, h2a, rfl⟩ := printItems_lit_inv G _ _ ks2 u2 h2
    obtain ⟨b2, _, rfl⟩ := printItems_lit_inv G _ _ ks2 a2 h2a
    simp only [List.cons_append, List.cons.injEq, true_and] at he
    obtain ⟨rfl, -⟩ := he
    exact rows_by_head p1 hp1 p2 hp2 hlhs (by rw [e1, e2]; rfl)

/-- Unique reading: at the sorts of numbers, types, terms and proof terms, two checked trees whose
token lists are prefixes of one stream are equal and cover the same tokens. -/
theorem reads_unique : ∀ (n : Nat) (t1 t2 : Tree) (s : String) (u1 u2 r1 r2 : List String),
    t1.height < n → s ∈ objSorts →
    printTree G t1 = some (s, u1) → printTree G t2 = some (s, u2) → u1 ++ r1 = u2 ++ r2 →
    t1 = t2 ∧ u1 = u2 := by
  intro n
  induction n with
  | zero => intro t1 _ _ _ _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro t1 t2 s u1 u2 r1 r2 hn hs h1 h2 he
    cases t1 with
    | leaf c x =>
      obtain ⟨rfl, hc⟩ := printTree_leaf_inv G c x s u1 h1
      rw [objSorts_not_tokens s hs] at hc; cases hc
    | node lb1 ks1 =>
      cases t2 with
      | leaf c x =>
        obtain ⟨rfl, hc⟩ := printTree_leaf_inv G c x s u2 h2
        rw [objSorts_not_tokens s hs] at hc; cases hc
      | node lb2 ks2 =>
        obtain ⟨p1, hq1, hl1, hi1⟩ := printTree_node_inv G lb1 ks1 s u1 h1
        obtain ⟨p2, hq2, hl2, hi2⟩ := printTree_node_inv G lb2 ks2 s u2 h2
        obtain ⟨hm1, hlab1⟩ := prodOf_mem G lb1 p1 hq1
        obtain ⟨hm2, hlab2⟩ := prodOf_mem G lb2 p2 hq2
        have hp : p1 = p2 := row_unique p1 p2 hm1 hm2 s hs hl1 hl2 ks1 ks2 u1 u2 r1 r2 hi1 hi2 he
        subst hp
        have hkids : ∀ k ∈ ks1, ∀ (t2 : Tree) (s : String) (v1 v2 q1 q2 : List String), s ∈ objSorts →
            printTree G k = some (s, v1) → printTree G t2 = some (s, v2) → v1 ++ q1 = v2 ++ q2 →
            k = t2 ∧ v1 = v2 := by
          intro k hk t2 s' v1 v2 q1 q2 hs' hk1 hk2 hq
          have hh : k.height < n := by
            have := height_le_of_mem ks1 k hk
            simp only [Tree.height] at hn
            omega
          exact ih k t2 s' v1 v2 q1 q2 hh hs' hk1 hk2 hq
        have hrhs := kid_sorts p1 hm1 (by rw [hl1]; exact hs)
        obtain ⟨rfl, rfl⟩ := items_unique p1.rhs hrhs ks1 ks2 u1 u2 r1 r2 hkids hi1 hi2 he
        exact ⟨by rw [← hlab1, ← hlab2], rfl⟩

/-- The tree an engine returns for Megalodon's printing of a proof term, once checked, is that proof
term's tree: the reading is unique. -/
theorem Pf.reading_is_tree (d : Pf) (hd : d.plain = true) (t : Tree)
    (h : check G "mg_proof" d.toks t = true) : t = d.tree := by
  obtain ⟨lb, ks, hdt, hp⟩ := Pf.reads d hd
  have ht : printTree G t = some ("mg_proof", d.toks) := by
    simpa [check] using h
  rw [hdt]
  exact (reads_unique (t.height + 1) t (.node lb ks) "mg_proof" d.toks d.toks [] []
    (Nat.lt_succ_self _) (by simp [objSorts, keywordSorts]) ht hp rfl).1

theorem Tm.reading_is_tree (m : Tm) (hm : m.plain = true) (t : Tree)
    (h : check G "mg_term" m.toks t = true) : t = m.tree := by
  obtain ⟨lb, ks, hmt, hp⟩ := Tm.reads m hm
  have ht : printTree G t = some ("mg_term", m.toks) := by
    simpa [check] using h
  rw [hmt]
  exact (reads_unique (t.height + 1) t (.node lb ks) "mg_term" m.toks m.toks [] []
    (Nat.lt_succ_self _) (by simp [objSorts, keywordSorts]) ht hp rfl).1

end Mettapedia.GSLT.Readers.Megalodon.Record
