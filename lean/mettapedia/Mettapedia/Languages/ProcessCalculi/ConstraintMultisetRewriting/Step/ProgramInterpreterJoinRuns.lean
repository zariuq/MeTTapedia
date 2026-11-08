import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramMGURenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramCompiledInterpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedMatcher

/-!
# An interpreter for calls with variables: renaming apart by allocation, unification by the store

The interpreter of `ProgramCompiledInterpreter` matches by code and is joined with the compiled
form on ground calls. For calls with variables, matching is two-way unification, and a fixed family
of rules cannot rename an equation apart in one firing (`ProgramCompiledObstruction`). This
interpreter, `joinMeta`, is a program of thirteen pattern equations, independent of the program it
runs. For a stored equation it

1. **allocates fresh variables** (`jAlloc`), one administrative firing per variable slot: the
   rule's right-hand side has a variable its left-hand side lacks, so each firing makes one fresh
   variable of its own scope (`alloc_run`);
2. **builds the renamed-apart copy** of the left- and right-hand sides from their postfix code,
   reading the allocated variables by position (`build_run`);
3. **lets the store unify**: one firing `(= (app $l $r $l) (ans $r))` equates the copied left-hand
   side with the call, two ways, and answers the copied right-hand side.

Steps 1 and 2 only match: every row they meet is an instance of the rule's pattern, and the
matcher is a most general unifier binding only the rule's fresh variables (`meta_step`). This file
proves the administrative runs; `ProgramInterpreterJoin` joins the last firing with the compiled
answer up to renaming.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded getD_mem)

/-! ## Terms for the interpreter's states -/

def tseq : List Tm → Tm
  | [] => .const 0
  | a :: l => node a (tseq l)

/-- A tagged tuple of terms. -/
def ttup (k : ℕ) (l : List Tm) : Tm := node (.const k) (tseq l)

def tkons (a l : Tm) : Tm := ttup 90 [a, l]
def tnil : Tm := ttup 91 []

/-- A list of terms as a term. -/
def tlist : List Tm → Tm
  | [] => tnil
  | a :: l => tkons a (tlist l)

theorem embed_seq : ∀ l : List Sx, embed (seq l) = tseq (l.map embed)
  | [] => rfl
  | a :: l => by
      show node (embed a) (embed (seq l)) = _
      rw [embed_seq l]
      rfl

theorem embed_tup (k : ℕ) (l : List Sx) : embed (tup k l) = ttup k (l.map embed) := by
  show node (.const k) (embed (seq l)) = _
  rw [embed_seq]
  rfl

theorem embed_codeOf : ∀ l : List Sx, embed (codeOf l) = tlist (l.map embed)
  | [] => rfl
  | a :: l => by
      show embed (tup 90 [a, codeOf l]) = _
      rw [embed_tup, List.map_cons, List.map_cons, List.map_nil, embed_codeOf l]
      rfl

theorem bounded_node {n : ℕ} {a b : Tm} (ha : Bounded n a) (hb : Bounded n b) : Bounded n (node a b) :=
  fun v hv => (mem_freeVars_node.mp hv).elim (ha v) (hb v)

theorem bounded_const (n k : ℕ) : Bounded n (.const k) := fun v hv => by simp [Term.freeVars] at hv

theorem bounded_tseq {n : ℕ} : ∀ {l : List Tm}, (∀ t ∈ l, Bounded n t) → Bounded n (tseq l)
  | [], _ => bounded_const n 0
  | a :: _, h => bounded_node (h a List.mem_cons_self) (bounded_tseq fun t m => h t (List.mem_cons_of_mem _ m))

theorem bounded_ttup {n k : ℕ} {l : List Tm} (h : ∀ t ∈ l, Bounded n t) : Bounded n (ttup k l) :=
  bounded_node (bounded_const n k) (bounded_tseq h)

theorem bounded_tlist {n : ℕ} : ∀ {l : List Tm}, (∀ t ∈ l, Bounded n t) → Bounded n (tlist l)
  | [], _ => bounded_ttup (by simp)
  | a :: l, h => bounded_ttup (by
      intro t m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact h _ List.mem_cons_self
      · exact bounded_tlist fun t m => h t (List.mem_cons_of_mem _ m))

theorem bounded_thread {n : ℕ} {t : Tm} (h : Bounded n t) : Bounded n (thread t) := fun v hv =>
  h v (by rwa [thread, freeVars_tagged] at hv)

/-! ## The interpreter -/

section Rules

private def pv (i : ℕ) : Pat := .var i
def pkons (a l : Pat) : Pat := ptup 90 [a, l]
def pnil : Pat := ptup 91 []
def pz : Pat := ptup 96 []
def ps (p : Pat) : Pat := ptup 97 [p]

/-- Choose a stored equation… -/
def jTry : ProgramEquations.Equation := ⟨ptup 160 [pkons (pv 0) (pv 1), pv 2], ptup 162 [pv 0, pv 2]⟩
/-- …or skip it. -/
def jSkip : ProgramEquations.Equation := ⟨ptup 160 [pkons (pv 0) (pv 1), pv 2], ptup 160 [pv 1, pv 2]⟩
/-- Start allocating the equation's variable slots. -/
def jInst : ProgramEquations.Equation :=
  ⟨ptup 162 [ptup 163 [pv 0, pv 1, pv 2], pv 3], ptup 164 [pv 0, pnil, pv 1, pv 2, pv 3]⟩
/-- **Allocate one fresh variable**: `$5` occurs only on the right. -/
def jAlloc : ProgramEquations.Equation :=
  ⟨ptup 164 [ps (pv 0), pv 1, pv 2, pv 3, pv 4], ptup 164 [pv 0, pkons (pv 5) (pv 1), pv 2, pv 3, pv 4]⟩
/-- Start building the left-hand side. -/
def jStart : ProgramEquations.Equation :=
  ⟨ptup 164 [pz, pv 0, pv 1, pv 2, pv 3], ptup 165 [pv 1, pnil, pv 0, ptup 167 [pv 2, pv 3]]⟩
/-- Push a symbol. -/
def jSym : ProgramEquations.Equation :=
  ⟨ptup 165 [pkons (ptup 170 [pv 0]) (pv 1), pv 2, pv 3, pv 4], ptup 165 [pv 1, pkons (pv 0) (pv 2), pv 3, pv 4]⟩
/-- Build a cell from the two topmost terms. -/
def jCell : ProgramEquations.Equation :=
  ⟨ptup 165 [pkons (ptup 172 []) (pv 0), pkons (pv 1) (pkons (pv 2) (pv 3)), pv 4, pv 5],
    ptup 165 [pv 0, pkons (.cell (pv 2) (pv 1)) (pv 3), pv 4, pv 5]⟩
/-- Read an allocated variable by position. -/
def jVar : ProgramEquations.Equation :=
  ⟨ptup 165 [pkons (ptup 171 [pv 0]) (pv 1), pv 2, pv 3, pv 4], ptup 166 [pv 0, pv 3, pv 1, pv 2, pv 3, pv 4]⟩
def jRdSucc : ProgramEquations.Equation :=
  ⟨ptup 166 [ps (pv 0), pkons (pv 1) (pv 2), pv 3, pv 4, pv 5, pv 6], ptup 166 [pv 0, pv 2, pv 3, pv 4, pv 5, pv 6]⟩
def jRdZero : ProgramEquations.Equation :=
  ⟨ptup 166 [pz, pkons (pv 0) (pv 1), pv 2, pv 3, pv 4, pv 5], ptup 165 [pv 2, pkons (pv 0) (pv 3), pv 4, pv 5]⟩
/-- The left-hand side is built: build the right-hand side. -/
def jDoneL : ProgramEquations.Equation :=
  ⟨ptup 165 [pnil, pkons (pv 0) pnil, pv 1, ptup 167 [pv 2, pv 3]],
    ptup 165 [pv 2, pnil, pv 1, ptup 168 [pv 0, pv 3]]⟩
/-- Both sides are built: hand them to the store. -/
def jDoneR : ProgramEquations.Equation :=
  ⟨ptup 165 [pnil, pkons (pv 0) pnil, pv 1, ptup 168 [pv 2, pv 3]], ptup 169 [pv 2, pv 0, pv 3]⟩
/-- **Unify by the store**: the copied left-hand side and the call are the same `$0`. -/
def jApply : ProgramEquations.Equation := ⟨ptup 169 [pv 0, pv 1, pv 0], ptup 173 [pv 1]⟩

end Rules

/-- **The interpreter**: thirteen equations, independent of the program it runs. -/
def joinMeta : Program :=
  [jTry, jSkip, jInst, jAlloc, jStart, jSym, jCell, jVar, jRdSucc, jRdZero, jDoneL, jDoneR, jApply]

/-! ## Equations as data -/

/-- Postfix building code; a variable is read at the position of its slot. -/
def bcode : Pat → List Sx
  | .var x => [tup 171 [nat x]]
  | .sym k => [tup 170 [.sym k]]
  | .cell a b => bcode a ++ bcode b ++ [tup 172 []]

/-- The number of variable slots of an equation. -/
def slots (e : ProgramEquations.Equation) : ℕ := (e.lhs.vars ++ e.rhs.vars).sum + 1

/-- **An equation stored as data**: its slot count and the building codes of both sides. -/
def eqData (e : ProgramEquations.Equation) : Sx := tup 163 [nat (slots e), codeOf (bcode e.lhs), codeOf (bcode e.rhs)]

/-- A program stored as data. -/
def progData (prog : Program) : Sx := codeOf (prog.map eqData)

/-! ## One administrative firing -/

theorem fixes_rows {n : ℕ} {vals : List Tm} {F : Multiset Tm} (bounded : ∀ f ∈ F, Bounded n f) :
    F.map (matcher n vals).applyTerm = F :=
  (Multiset.map_congr rfl fun f member => matcher_fixes (bounded f member)).trans (Multiset.map_id' F)

/-- **An administrative firing**: on an instance of a rule's pattern, the matcher is a most general
unifier, the result is the instantiated right-hand side, and the other rows are untouched. -/
theorem meta_step {e : ProgramEquations.Equation} (member : e ∈ joinMeta) {n : ℕ} {vals : List Tm} {k : ℕ}
    (length : vals.length = k) (covers : ∀ x < k, x ∈ e.lhs.vars) (within : ∀ x ∈ e.lhs.vars, x < k)
    (bounded : ∀ t ∈ vals, Bounded n t) {F : Multiset Tm} (rowsBounded : ∀ f ∈ F, Bounded n f)
    {row row' : Tm} (source : Pat.fill vals e.lhs = row)
    (target : (matcher n vals).applyTerm (e.rhs.at n) = row') :
    EqStep joinMeta (thread row ::ₘ F, n) (thread row' ::ₘ F, n + 1) := by
  subst length source target
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp member
  have step := EqStep.call j (Pat.fill vals (joinMeta.get j).lhs) F n (matcher n vals)
    (matcher_isMGU bounded covers within)
  rwa [fixes_rows rowsBounded] at step

/-- The instance of a right-hand side whose variables are among the matched ones. -/
theorem target_of {n : ℕ} {vals : List Tm} {p : Pat} (within : ∀ x ∈ p.vars, x < vals.length) :
    (matcher n vals).applyTerm (p.at n) = Pat.fill vals p := matcher_at p within

/-- The instance of a right-hand side with one variable beyond the matched ones: it is the fresh
variable of the firing's scope. -/
theorem target_fresh {n : ℕ} {vals : List Tm} : ∀ (p : Pat), (∀ x ∈ p.vars, x ≤ vals.length) →
    (matcher n vals).applyTerm (p.at n) = Pat.fill (vals ++ [(Term.var (n, vals.length) : Tm)]) p
  | .var x, within => by
      have le := within x (by simp [Pat.vars])
      show matcher n vals (n, x) = (vals ++ [(Term.var (n, vals.length) : Tm)]).getD x (.const 0)
      rcases lt_or_eq_of_le le with lt | rfl
      · rw [matcher, if_pos ⟨rfl, lt⟩]
        show vals.getD x (.const 0) = _
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left lt]
      · rw [matcher, if_neg fun h => lt_irrefl _ h.2, List.getD_eq_getElem?_getD,
          List.getElem?_append_right le_rfl, Nat.sub_self]
        rfl
  | .sym _, _ => rfl
  | .cell a b, within => by
      rw [Pat.at, apply_node, target_fresh a fun x hx => within x (by simp [Pat.vars, hx]),
        target_fresh b fun x hx => within x (by simp [Pat.vars, hx])]
      rfl

theorem target_k {n : ℕ} {vals : List Tm} {k : ℕ} (length : vals.length = k) {p : Pat}
    (within : ∀ x ∈ p.vars, x < k) : (matcher n vals).applyTerm (p.at n) = Pat.fill vals p := by
  subst length
  exact matcher_at p within

theorem target_fresh_k {n : ℕ} {vals : List Tm} {k : ℕ} (length : vals.length = k) {p : Pat}
    (within : ∀ x ∈ p.vars, x ≤ k) :
    (matcher n vals).applyTerm (p.at n) = Pat.fill (vals ++ [(Term.var (n, k) : Tm)]) p := by
  subst length
  exact target_fresh p within

theorem bounded_vals {n : ℕ} {vals : List Tm} (h : ∀ t ∈ vals, Bounded n t) : ∀ t ∈ vals, Bounded n t := h

theorem all_bounded {n : ℕ} : ∀ {l : List Tm}, (∀ t ∈ l, Bounded n t) → ∀ t ∈ l, Bounded n t :=
  fun h => h

/-! ## Choosing a stored equation -/

/-- **From the stored program, `j + 1` firings choose its `j`-th equation.** -/
theorem select_run (t : Tm) (F : Multiset Tm) :
    ∀ (eqs : List Sx) (j : Fin eqs.length) (n : ℕ), Bounded n t → (∀ f ∈ F, Bounded n f) →
      Relation.ReflTransGen (EqStep joinMeta) (thread (ttup 160 [embed (codeOf eqs), t]) ::ₘ F, n)
        (thread (ttup 162 [embed (eqs.get j), t]) ::ₘ F, n + j + 1)
  | [], j, _, _, _ => absurd j.2 (Nat.not_lt_zero _)
  | a :: l, ⟨0, _⟩, n, tB, FB => by
      have vb : ∀ s ∈ [embed a, embed (codeOf l), t], Bounded n s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl
        · exact embed_bounded n a
        · exact embed_bounded n _
        · exact tB
      exact .single (meta_step (e := jTry) (k := 3) (by simp [joinMeta]) rfl (by decide) (by decide) vb FB
        rfl
        (by rw [target_k (p := jTry.rhs) (k := 3) rfl (by decide)]; rfl))
  | a :: l, ⟨j + 1, lt⟩, n, tB, FB => by
      have vb : ∀ s ∈ [embed a, embed (codeOf l), t], Bounded n s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl
        · exact embed_bounded n a
        · exact embed_bounded n _
        · exact tB
      have first := meta_step (e := jSkip) (k := 3) (by simp [joinMeta]) rfl (by decide) (by decide) vb FB
        (row' := ttup 160 [embed (codeOf l), t])
        rfl
        (by rw [target_k (p := jSkip.rhs) (k := 3) rfl (by decide)]; rfl)
      have rest := select_run t F l ⟨j, Nat.lt_of_succ_lt_succ lt⟩ (n + 1) (tB.mono (Nat.le_succ n))
        fun f m => (FB f m).mono (Nat.le_succ n)
      have scopes : n + 1 + j + 1 = n + (j + 1) + 1 := by omega
      rw [scopes] at rest
      exact Relation.ReflTransGen.head first rest

/-! ## Allocating fresh variables -/

/-- The variables allocated from scope `n`, newest first: one per firing, of the firing's scope. -/
def freshVars (n : ℕ) : ℕ → List Tm
  | 0 => []
  | k + 1 => .var (n + k, 5) :: freshVars n k

theorem freshVars_succ (n : ℕ) : ∀ k, freshVars n (k + 1) = freshVars (n + 1) k ++ [.var (n, 5)]
  | 0 => rfl
  | k + 1 => by
      show Term.var (n + (k + 1), 5) :: freshVars n (k + 1) =
        (Term.var (n + 1 + k, 5) :: freshVars (n + 1) k) ++ [.var (n, 5)]
      rw [freshVars_succ n k, List.cons_append, show n + 1 + k = n + (k + 1) by omega]

theorem freshVars_length (n : ℕ) : ∀ k, (freshVars n k).length = k
  | 0 => rfl
  | k + 1 => by rw [freshVars, List.length_cons, freshVars_length n k]

theorem freshVars_bounded (n : ℕ) : ∀ k, ∀ t ∈ freshVars n k, Bounded (n + k) t
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, t, h => by
      rcases List.mem_cons.mp h with rfl | h
      · intro v hv
        rw [Term.mem_freeVars_var (σ := rows)] at hv
        subst hv
        show n + k < n + (k + 1)
        omega
      · exact (freshVars_bounded n k t h).mono (by omega)

/-- **`k` administrative firings allocate `k` fresh variables.** -/
theorem alloc_run (L R t : Tm) (F : Multiset Tm) : ∀ (k : ℕ) (env : List Tm) (n : ℕ),
    (∀ s ∈ env, Bounded n s) → Bounded n L → Bounded n R → Bounded n t → (∀ f ∈ F, Bounded n f) →
      Relation.ReflTransGen (EqStep joinMeta)
        (thread (ttup 164 [embed (nat k), tlist env, L, R, t]) ::ₘ F, n)
        (thread (ttup 164 [embed (nat 0), tlist (freshVars n k ++ env), L, R, t]) ::ₘ F, n + k)
  | 0, env, n, _, _, _, _, _ => .refl
  | k + 1, env, n, envB, LB, RB, tB, FB => by
      have vb : ∀ s ∈ [embed (nat k), tlist env, L, R, t], Bounded n s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl | rfl | rfl
        · exact embed_bounded n _
        · exact bounded_tlist envB
        · exact LB
        · exact RB
        · exact tB
      have first := meta_step (e := jAlloc) (k := 5) (by simp [joinMeta]) rfl (by decide) (by decide) vb FB
        (row' := ttup 164 [embed (nat k), tlist (.var (n, 5) :: env), L, R, t])
        rfl (by rw [target_fresh_k (p := jAlloc.rhs) (k := 5) rfl (by decide)]; rfl)
      have mono : ∀ {s : Tm}, Bounded n s → Bounded (n + 1) s := fun h => h.mono (Nat.le_succ n)
      have rest := alloc_run L R t F k (.var (n, 5) :: env) (n + 1) (by
        intro s m
        rcases List.mem_cons.mp m with rfl | m
        · intro v hv
          rw [Term.mem_freeVars_var (σ := rows)] at hv
          subst hv
          exact Nat.lt_succ_self n
        · exact mono (envB s m)) (mono LB) (mono RB) (mono tB) fun f m => mono (FB f m)
      rw [show freshVars (n + 1) k ++ .var (n, 5) :: env = freshVars n (k + 1) ++ env by
        rw [freshVars_succ, List.append_assoc]; rfl, show n + 1 + k = n + (k + 1) by omega] at rest
      exact Relation.ReflTransGen.head first rest

/-! ## Building the copy -/

theorem embed_nat_succ (d : ℕ) : embed (nat (d + 1)) = ttup 97 [embed (nat d)] := by
  rw [show nat (d + 1) = tup 97 [nat d] from rfl, embed_tup]
  rfl

theorem embed_nat_zero : embed (nat 0) = ttup 96 [] := rfl

/-- Walking the read position down the allocated variables. -/
theorem read_walk (C S env K : Tm) (F : Multiset Tm) :
    ∀ (d : ℕ) (W : List Tm) (n : ℕ), d < W.length → (∀ s ∈ W, Bounded n s) → Bounded n C →
      Bounded n S → Bounded n env → Bounded n K → (∀ f ∈ F, Bounded n f) →
        Relation.ReflTransGen (EqStep joinMeta) (thread (ttup 166 [embed (nat d), tlist W, C, S, env, K]) ::ₘ F, n)
          (thread (ttup 166 [embed (nat 0), tlist (W.drop d), C, S, env, K]) ::ₘ F, n + d)
  | 0, _, _, _, _, _, _, _, _, _ => .refl
  | d + 1, w :: W, n, lt, WB, CB, SB, envB, KB, FB => by
      have vb : ∀ s ∈ [embed (nat d), w, tlist W, C, S, env, K], Bounded n s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact embed_bounded n _
        · exact WB _ List.mem_cons_self
        · exact bounded_tlist fun s m => WB s (List.mem_cons_of_mem _ m)
        · exact CB
        · exact SB
        · exact envB
        · exact KB
      have first := meta_step (e := jRdSucc) (k := 7) (by simp [joinMeta]) rfl (by decide) (by decide) vb FB
        (row' := ttup 166 [embed (nat d), tlist W, C, S, env, K])
        rfl (by rw [target_k (p := jRdSucc.rhs) (k := 7) rfl (by decide)]; rfl)
      have mono : ∀ {s : Tm}, Bounded n s → Bounded (n + 1) s := fun h => h.mono (Nat.le_succ n)
      have rest := read_walk C S env K F d W (n + 1) (by simpa using lt)
        (fun s m => mono (WB s (List.mem_cons_of_mem _ m))) (mono CB) (mono SB) (mono envB) (mono KB)
        fun f m => mono (FB f m)
      rw [show n + 1 + d = n + (d + 1) by omega] at rest
      exact Relation.ReflTransGen.head first rest

/-- **Building code pushes the copy of its pattern**, reading each variable from the allocated
ones. -/
theorem build_run (env : List Tm) (K : Tm) (F : Multiset Tm) :
    ∀ (q : Pat), (∀ x ∈ q.vars, x < env.length) → ∀ (C : List Sx) (S : Tm) (n : ℕ),
      (∀ s ∈ env, Bounded n s) → Bounded n S → Bounded n K → (∀ f ∈ F, Bounded n f) →
        ∃ i, Relation.ReflTransGen (EqStep joinMeta)
          (thread (ttup 165 [embed (codeOf (bcode q ++ C)), S, tlist env, K]) ::ₘ F, n)
          (thread (ttup 165 [embed (codeOf C), tkons (Pat.fill env q) S, tlist env, K]) ::ₘ F, n + i)
  | .var x, within, C, S, n, envB, SB, KB, FB => by
      have lt := within x (by simp [Pat.vars])
      have eB := bounded_tlist envB
      have vb : ∀ s ∈ [embed (nat x), embed (codeOf C), S, tlist env, K], Bounded n s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl | rfl | rfl
        · exact embed_bounded n _
        · exact embed_bounded n _
        · exact SB
        · exact eB
        · exact KB
      have first := meta_step (e := jVar) (k := 5) (by simp [joinMeta]) rfl (by decide) (by decide) vb FB
        (row' := ttup 166 [embed (nat x), tlist env, embed (codeOf C), S, tlist env, K])
        rfl (by rw [target_k (p := jVar.rhs) (k := 5) rfl (by decide)]; rfl)
      have mono : ∀ {s : Tm}, Bounded n s → Bounded (n + 1) s := fun h => h.mono (Nat.le_succ n)
      have walk := read_walk (embed (codeOf C)) S (tlist env) K F x env (n + 1) lt
        (fun s m => mono (envB s m)) (embed_bounded _ _) (mono SB) (mono eB) (mono KB) fun f m => mono (FB f m)
      obtain ⟨rest, split⟩ : ∃ rest, env.drop x = env.getD x (.const 0) :: rest := by
        refine ⟨env.drop (x + 1), ?_⟩
        rw [List.drop_eq_getElem_cons lt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt,
          Option.getD_some]
      rw [split] at walk
      have m2 : ∀ {s : Tm}, Bounded n s → Bounded (n + 1 + x) s := fun h => h.mono (by omega)
      have entryB : Bounded (n + 1 + x) (env.getD x (.const 0)) := m2 (envB _ (getD_mem lt _))
      have restB : Bounded (n + 1 + x) (tlist rest) := by
        have : Bounded n (tlist (env.drop x)) := bounded_tlist fun s m => envB s (List.mem_of_mem_drop m)
        rw [split] at this
        exact m2 (fun v hv => this v (by
          show v ∈ (node (.const 90) (tseq [_, tlist rest])).freeVars
          rw [mem_freeVars_node]
          exact .inr (mem_freeVars_node.mpr (.inr (mem_freeVars_node.mpr (.inl hv))))))
      have vb' : ∀ s ∈ [env.getD x (.const 0), tlist rest, embed (codeOf C), S, tlist env, K],
          Bounded (n + 1 + x) s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl | rfl | rfl | rfl
        · exact entryB
        · exact restB
        · exact embed_bounded _ _
        · exact m2 SB
        · exact m2 eB
        · exact m2 KB
      have last := meta_step (e := jRdZero) (k := 6) (by simp [joinMeta]) rfl (by decide) (by decide) vb'
        (fun f m => m2 (FB f m))
        (row' := ttup 165 [embed (codeOf C), tkons (env.getD x (.const 0)) S, tlist env, K])
        rfl (by rw [target_k (p := jRdZero.rhs) (k := 6) rfl (by decide)]; rfl)
      exact ⟨1 + x + 1, by
        rw [show n + (1 + x + 1) = n + 1 + x + 1 by omega]
        exact (Relation.ReflTransGen.head first walk).tail last⟩
  | .sym k, _, C, S, n, envB, SB, KB, FB => by
      have vb : ∀ s ∈ [.const k, embed (codeOf C), S, tlist env, K], Bounded n s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl | rfl | rfl
        · exact bounded_const n k
        · exact embed_bounded n _
        · exact SB
        · exact bounded_tlist envB
        · exact KB
      refine ⟨1, .single (meta_step (e := jSym) (k := 5) (by simp [joinMeta]) rfl (by decide) (by decide) vb FB
        rfl (by rw [target_k (p := jSym.rhs) (k := 5) rfl (by decide)]; rfl))⟩
  | .cell a b, within, C, S, n, envB, SB, KB, FB => by
      have wa : ∀ x ∈ a.vars, x < env.length := fun x hx => within x (by simp [Pat.vars, hx])
      have wb : ∀ x ∈ b.vars, x < env.length := fun x hx => within x (by simp [Pat.vars, hx])
      obtain ⟨i, first⟩ := build_run env K F a wa (bcode b ++ tup 172 [] :: C) S n envB SB KB FB
      have aB : Bounded n (Pat.fill env a) := fill_bounded envB a
      have mono : ∀ {s : Tm}, Bounded n s → Bounded (n + i) s := fun h => h.mono (by omega)
      have SB' : Bounded (n + i) (tkons (Pat.fill env a) S) :=
        mono (bounded_ttup (by
          intro s m
          simp only [List.mem_cons, List.not_mem_nil, or_false] at m
          rcases m with rfl | rfl
          · exact aB
          · exact SB))
      obtain ⟨i', second⟩ := build_run env K F b wb (tup 172 [] :: C) (tkons (Pat.fill env a) S) (n + i)
        (fun s m => mono (envB s m)) SB' (mono KB) fun f m => mono (FB f m)
      have m2 : ∀ {s : Tm}, Bounded n s → Bounded (n + i + i') s := fun h => h.mono (by omega)
      have vb : ∀ s ∈ [embed (codeOf C), Pat.fill env b, Pat.fill env a, S, tlist env, K],
          Bounded (n + i + i') s := by
        intro s m
        simp only [List.mem_cons, List.not_mem_nil, or_false] at m
        rcases m with rfl | rfl | rfl | rfl | rfl | rfl
        · exact embed_bounded _ _
        · exact m2 (fill_bounded envB b)
        · exact m2 aB
        · exact m2 SB
        · exact m2 (bounded_tlist envB)
        · exact m2 KB
      have last := meta_step (e := jCell) (k := 6) (by simp [joinMeta]) rfl (by decide) (by decide) vb
        (fun f m => m2 (FB f m))
        (row' := ttup 165 [embed (codeOf C), tkons (Pat.fill env (.cell a b)) S, tlist env, K])
        rfl (by rw [target_k (p := jCell.rhs) (k := 6) rfl (by decide)]; rfl)
      refine ⟨i + i' + 1, ?_⟩
      rw [show bcode (.cell a b) ++ C = bcode a ++ (bcode b ++ tup 172 [] :: C) by
        simp [bcode, List.append_assoc], show n + (i + i' + 1) = n + i + i' + 1 by omega]
      exact (first.trans second).tail last

#print axioms embed_codeOf
#print axioms meta_step
#print axioms target_fresh
#print axioms select_run
#print axioms freshVars_succ
#print axioms alloc_run
#print axioms read_walk
#print axioms build_run

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
