import Mettapedia.GSLT.Readers.Rho.Record
import Mettapedia.GSLT.Readers.Megalodon.RecordUnique

/-!
# The reference's printing of a rho process has exactly one reading

`Record.lean` proves that the readers' tree check accepts the reference's printing of every process
with that process's own tree. This file proves that it is the only tree: at the sorts of names,
processes, component lists and items, two checked trees whose token lists are prefixes of one token
stream are equal and cover the same tokens (`reads_unique`). So the tree an engine returns for the
reference's printing of a process, once checked, is that process's tree
(`RProc.reading_is_tree`, `RProc.item_reading_is_tree`), whatever the untrusted parse did.

The argument is unique readability of prefix notation. Every row of these sorts has a lead: a
fixed spelling, `(` and a keyword, a variable, or a process (`lead`, `rows_have_leads`); two rows of
one sort with the same lead are the same row (`rows_by_lead`); and two rows of one sort with different
leads begin with tokens that cannot be equal (`leads_apart`, `disjoint_heads`): `rho:nil`, `(` and
`)` are no variables, and a process begins with `rho:nil` or `(` (`proc_head`). The children then
follow in order (`items_unique`). Every sort here is prefix-free because a parallel composition's
component list runs up to and including its `)`; only whole files are left out, whose empty row is a
prefix of every file.

The inversion lemmas of the check's printer hold for every grammar; they are taken from the
Megalodon reader's file. `items_unique` is the Megalodon reader's argument stated for any grammar and
any set of prefix-free sorts.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Readers.Rho.Record

open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TreeCheck
open Mettapedia.GSLT.Readers.Rho.Correspondence
open Mettapedia.GSLT.Readers.Rho
open Mettapedia.GSLT.Readers.GrammarCorrespondence
open Mettapedia.GSLT.Readers.Megalodon.Record (prodOf_mem printTree_node_inv printTree_leaf_inv
  printItems_nil_inv printItems_eof printItems_lit_inv printItems_tok_inv printItems_nt_inv
  height_le_of_mem)

/-- The phrase sorts of names, processes, component lists and items. -/
def objSorts : List String := ["rho_name", "rho_proc", "rho_procs", "rho_item"]

/-! ## Facts about the rows, decided -/

/-- How a row's printing begins. -/
inductive Lead where
  | lit (s : String)
  | lit2 (k : String)
  | var
  | proc
  deriving DecidableEq

def lead (p : Prod) : Option Lead :=
  match p.rhs with
  | .lit "(" :: .lit k :: _ => some (.lit2 k)
  | .lit s :: _ => some (.lit s)
  | .tok "var_tok" :: _ => some .var
  | .nt "rho_proc" :: _ => some .proc
  | _ => none

/-- Two leads whose printings can never begin alike. -/
def headsDisjoint : Lead → Lead → Bool
  | .lit s, .lit s' => s != s'
  | .lit s, .lit2 _ => s != "("
  | .lit2 _, .lit s => s != "("
  | .lit s, .var => !G.inSort "var_tok" s
  | .var, .lit s => !G.inSort "var_tok" s
  | .lit s, .proc => s != "rho:nil" && s != "("
  | .proc, .lit s => s != "rho:nil" && s != "("
  | .lit2 k, .lit2 k' => k != k'
  | .lit2 _, .var => !G.inSort "var_tok" "("
  | .var, .lit2 _ => !G.inSort "var_tok" "("
  | .lit2 _, .proc => false
  | .proc, .lit2 _ => false
  | .var, .var => false
  | .var, .proc => !G.inSort "var_tok" "rho:nil" && !G.inSort "var_tok" "("
  | .proc, .var => !G.inSort "var_tok" "rho:nil" && !G.inSort "var_tok" "("
  | .proc, .proc => false

theorem rows_have_leads : ∀ p ∈ G.prods, p.lhs ∈ objSorts → (lead p).isSome = true := by
  decide +kernel

theorem rows_by_lead : ∀ p1 ∈ G.prods, ∀ p2 ∈ G.prods, p1.lhs = p2.lhs → (lead p1).isSome = true →
    lead p1 = lead p2 → p1 = p2 := by
  decide +kernel

/-- Two rows of one of these sorts have the same lead, or leads that never begin alike. -/
theorem leads_apart : ∀ p1 ∈ G.prods, ∀ p2 ∈ G.prods, p1.lhs = p2.lhs → p1.lhs ∈ objSorts →
    lead p1 = lead p2 ∨
      (match lead p1, lead p2 with
        | some a, some b => headsDisjoint a b
        | _, _ => false) = true := by
  decide +kernel

theorem proc_rows : ∀ p ∈ G.prods, p.lhs = "rho_proc" →
    p.rhs.head? = some (.lit "rho:nil") ∨ p.rhs.head? = some (.lit "(") := by
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

/-! ## How a printing begins -/

/-- A printed process begins with `rho:nil` or `(`. -/
theorem proc_head (t : Tree) (u : List String) (h : printTree G t = some ("rho_proc", u)) :
    ∃ x rest, u = x :: rest ∧ (x = "rho:nil" ∨ x = "(") := by
  cases t with
  | leaf c x =>
    obtain ⟨rfl, hc⟩ := printTree_leaf_inv G c x "rho_proc" u h
    rw [objSorts_not_tokens "rho_proc" (by simp [objSorts])] at hc; cases hc
  | node lb ks =>
    obtain ⟨p, hq, hl, hi⟩ := printTree_node_inv G lb ks "rho_proc" u h
    obtain ⟨hm, -⟩ := prodOf_mem G lb p hq
    rcases proc_rows p hm hl with hr | hr
    · obtain ⟨rest, hrest⟩ : ∃ rest, p.rhs = .lit "rho:nil" :: rest := by
        cases hx : p.rhs with
        | nil => rw [hx] at hr; simp at hr
        | cons a rest => rw [hx] at hr; simp only [List.head?_cons, Option.some.injEq] at hr; exact ⟨rest, by rw [hr]⟩
      rw [hrest] at hi
      obtain ⟨u', -, rfl⟩ := printItems_lit_inv G _ _ ks u hi
      exact ⟨"rho:nil", u', rfl, Or.inl rfl⟩
    · obtain ⟨rest, hrest⟩ : ∃ rest, p.rhs = .lit "(" :: rest := by
        cases hx : p.rhs with
        | nil => rw [hx] at hr; simp at hr
        | cons a rest => rw [hx] at hr; simp only [List.head?_cons, Option.some.injEq] at hr; exact ⟨rest, by rw [hr]⟩
      rw [hrest] at hi
      obtain ⟨u', -, rfl⟩ := printItems_lit_inv G _ _ ks u hi
      exact ⟨"(", u', rfl, Or.inr rfl⟩

/-- What the printing of a row with a given lead begins with. -/
def HeadOK : Lead → List String → Prop
  | .lit s, u => ∃ rest, u = s :: rest
  | .lit2 k, u => ∃ rest, u = "(" :: k :: rest
  | .var, u => ∃ x rest, u = x :: rest ∧ G.inSort "var_tok" x = true
  | .proc, u => ∃ x rest, u = x :: rest ∧ (x = "rho:nil" ∨ x = "(")

theorem lead_head (p : Prod) (L : Lead) (hL : lead p = some L) (ks : List Tree) (u : List String)
    (h : printItems G p.rhs ks = some u) : HeadOK L u := by
  unfold lead at hL
  split at hL
  · rename_i k rest hrhs
    simp only [Option.some.injEq] at hL
    subst hL
    rw [hrhs] at h
    obtain ⟨a, ha, rfl⟩ := printItems_lit_inv G _ _ ks u h
    obtain ⟨b, -, rfl⟩ := printItems_lit_inv G _ _ ks a ha
    exact ⟨b, rfl⟩
  · rename_i s rest _ hrhs
    simp only [Option.some.injEq] at hL
    subst hL
    rw [hrhs] at h
    obtain ⟨a, -, rfl⟩ := printItems_lit_inv G _ _ ks u h
    exact ⟨a, rfl⟩
  · rename_i rest hrhs
    simp only [Option.some.injEq] at hL
    subst hL
    rw [hrhs] at h
    obtain ⟨x, ks', u', -, hx, -, rfl⟩ := printItems_tok_inv G _ _ ks u h
    exact ⟨x, u', rfl, hx⟩
  · rename_i rest hrhs
    simp only [Option.some.injEq] at hL
    subst hL
    rw [hrhs] at h
    obtain ⟨k, ks', sub, u', -, hk, -, rfl⟩ := printItems_nt_inv G _ _ ks u h
    obtain ⟨x, r, rfl, hx⟩ := proc_head k sub hk
    exact ⟨x, r ++ u', rfl, hx⟩
  · simp at hL

theorem disjoint_heads (a b : Lead) (u1 u2 r1 r2 : List String) (h1 : HeadOK a u1) (h2 : HeadOK b u2)
    (he : u1 ++ r1 = u2 ++ r2) (hd : headsDisjoint a b = true) : False := by
  cases a <;> cases b <;> simp only [HeadOK] at h1 h2 <;> simp only [headsDisjoint] at hd
  all_goals first
    | (obtain ⟨_, _, rfl, (rfl | rfl)⟩ := h1)
    | (obtain ⟨_, _, rfl, _⟩ := h1)
  all_goals first
    | (obtain ⟨_, _, rfl, (rfl | rfl)⟩ := h2)
    | (obtain ⟨_, _, rfl, _⟩ := h2)
  all_goals simp_all

/-- Two rows of one of these sorts whose printings are prefixes of one stream are the same row. -/
theorem row_unique (p1 p2 : Prod) (hp1 : p1 ∈ G.prods) (hp2 : p2 ∈ G.prods) (s : String)
    (hs : s ∈ objSorts) (hl1 : p1.lhs = s) (hl2 : p2.lhs = s) (ks1 ks2 : List Tree)
    (u1 u2 r1 r2 : List String) (h1 : printItems G p1.rhs ks1 = some u1)
    (h2 : printItems G p2.rhs ks2 = some u2) (he : u1 ++ r1 = u2 ++ r2) : p1 = p2 := by
  have hlhs : p1.lhs = p2.lhs := by rw [hl1, hl2]
  have hs1 : p1.lhs ∈ objSorts := by rw [hl1]; exact hs
  have hsome1 := rows_have_leads p1 hp1 hs1
  rcases leads_apart p1 hp1 p2 hp2 hlhs hs1 with heq | hdis
  · exact rows_by_lead p1 hp1 p2 hp2 hlhs hsome1 heq
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome1
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (rows_have_leads p2 hp2 (by rw [hl2]; exact hs))
    rw [ha, hb] at hdis
    exact (disjoint_heads a b u1 u2 r1 r2 (lead_head p1 a ha ks1 u1 h1) (lead_head p2 b hb ks2 u2 h2)
      he hdis).elim

/-! ## Unique reading -/

/-- The children of one row: equal when their printings are prefixes of one stream, given that
their subtrees read uniquely (the Megalodon reader's argument, for any grammar and sorts). -/
theorem items_unique (g : Grammar) (S : List String) (rhs : List Sym)
    (hrhs : ∀ m, .nt m ∈ rhs → m ∈ S) :
    ∀ (ks1 ks2 : List Tree) (u1 u2 r1 r2 : List String),
    (∀ k ∈ ks1, ∀ (t2 : Tree) (s : String) (v1 v2 q1 q2 : List String), s ∈ S →
      printTree g k = some (s, v1) → printTree g t2 = some (s, v2) → v1 ++ q1 = v2 ++ q2 →
      k = t2 ∧ v1 = v2) →
    printItems g rhs ks1 = some u1 → printItems g rhs ks2 = some u2 → u1 ++ r1 = u2 ++ r2 →
    ks1 = ks2 ∧ u1 = u2 := by
  induction rhs with
  | nil =>
    intro ks1 ks2 u1 u2 r1 r2 _ h1 h2 _
    obtain ⟨rfl, rfl⟩ := printItems_nil_inv g ks1 u1 h1
    obtain ⟨rfl, rfl⟩ := printItems_nil_inv g ks2 u2 h2
    exact ⟨rfl, rfl⟩
  | cons sym rest ih =>
    intro ks1 ks2 u1 u2 r1 r2 hk h1 h2 he
    have hrest : ∀ m, .nt m ∈ rest → m ∈ S := fun m hm => hrhs m (List.mem_cons_of_mem _ hm)
    cases sym with
    | eof => rw [printItems_eof] at h1; cases h1
    | lit s =>
      obtain ⟨u1', h1', rfl⟩ := printItems_lit_inv g s rest ks1 u1 h1
      obtain ⟨u2', h2', rfl⟩ := printItems_lit_inv g s rest ks2 u2 h2
      simp only [List.cons_append, List.cons.injEq, true_and] at he
      obtain ⟨hks, hu⟩ := ih hrest ks1 ks2 u1' u2' r1 r2 hk h1' h2' he
      exact ⟨hks, by rw [hu]⟩
    | tok c =>
      obtain ⟨x1, ks1', u1', rfl, -, h1', rfl⟩ := printItems_tok_inv g c rest ks1 u1 h1
      obtain ⟨x2, ks2', u2', rfl, -, h2', rfl⟩ := printItems_tok_inv g c rest ks2 u2 h2
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he'⟩ := he
      have hk' : ∀ k ∈ ks1', ∀ (t2 : Tree) (s : String) (v1 v2 q1 q2 : List String), s ∈ S →
          printTree g k = some (s, v1) → printTree g t2 = some (s, v2) → v1 ++ q1 = v2 ++ q2 →
          k = t2 ∧ v1 = v2 := fun k hk2 => hk k (List.mem_cons_of_mem _ hk2)
      obtain ⟨hks, hu⟩ := ih hrest ks1' ks2' u1' u2' r1 r2 hk' h1' h2' he'
      exact ⟨by rw [hks], by rw [hu]⟩
    | nt m =>
      obtain ⟨k1, ks1', sub1, u1', rfl, hp1, h1', rfl⟩ := printItems_nt_inv g m rest ks1 u1 h1
      obtain ⟨k2, ks2', sub2, u2', rfl, hp2, h2', rfl⟩ := printItems_nt_inv g m rest ks2 u2 h2
      have hm : m ∈ S := hrhs m (List.mem_cons_self)
      have he1 : sub1 ++ (u1' ++ r1) = sub2 ++ (u2' ++ r2) := by
        simpa only [List.append_assoc] using he
      obtain ⟨rfl, rfl⟩ := hk k1 List.mem_cons_self k2 m sub1 sub2 (u1' ++ r1) (u2' ++ r2) hm hp1 hp2 he1
      have he' : u1' ++ r1 = u2' ++ r2 := List.append_cancel_left he1
      have hk' : ∀ k ∈ ks1', ∀ (t2 : Tree) (s : String) (v1 v2 q1 q2 : List String), s ∈ S →
          printTree g k = some (s, v1) → printTree g t2 = some (s, v2) → v1 ++ q1 = v2 ++ q2 →
          k = t2 ∧ v1 = v2 := fun k hk2 => hk k (List.mem_cons_of_mem _ hk2)
      obtain ⟨hks, hu⟩ := ih hrest ks1' ks2' u1' u2' r1 r2 hk' h1' h2' he'
      exact ⟨by rw [hks], by rw [hu]⟩

/-- Unique reading: at the sorts of names, processes, component lists and items, two checked trees
whose token lists are prefixes of one stream are equal and cover the same tokens. -/
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
        obtain ⟨rfl, rfl⟩ := items_unique G objSorts p1.rhs hrhs ks1 ks2 u1 u2 r1 r2 hkids hi1 hi2 he
        exact ⟨by rw [← hlab1, ← hlab2], rfl⟩

/-- The tree an engine returns for the reference's printing of a process, once checked, is that
process's tree: the reading is unique. -/
theorem RProc.reading_is_tree (p : RProc) (hp : p.plain = true) (t : Tree)
    (h : check G "rho_proc" p.toks t = true) : t = p.tree := by
  obtain ⟨lb, ks, hpt, hpr⟩ := RProc.reads p hp
  have ht : printTree G t = some ("rho_proc", p.toks) := by
    simpa [check] using h
  rw [hpt]
  exact (reads_unique (t.height + 1) t (.node lb ks) "rho_proc" p.toks p.toks [] []
    (Nat.lt_succ_self _) (by simp [objSorts]) ht hpr rfl).1

/-- A residual line of the reference, once checked as an item, is the item of that process. -/
theorem RProc.item_reading_is_tree (p : RProc) (hp : p.plain = true) (t : Tree)
    (h : check G "rho_item" p.toks t = true) : t = .node "item_proc" [p.tree] := by
  have hi := RProc.checks_item p hp
  have ht : printTree G t = some ("rho_item", p.toks) := by simpa [check] using h
  have hi' : printTree G (.node "item_proc" [p.tree]) = some ("rho_item", p.toks) := by
    simpa [check] using hi
  exact (reads_unique (t.height + 1) t _ "rho_item" p.toks p.toks [] []
    (Nat.lt_succ_self _) (by simp [objSorts]) ht hi' rfl).1

end Mettapedia.GSLT.Readers.Rho.Record
