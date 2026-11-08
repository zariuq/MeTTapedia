import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterConverse

/-!
# The interpreter-join converse: forcing, renamed copies, building code, and the store's firing

The converse of `interpreter_answers` follows every run of the interpreter `joinMeta`, under any
most general unifier at every firing. This file proves the pieces each stage uses.

* **Forcing** (`Clash`, `clash_apart`, `forced`): a rule whose left-hand side clashes with the
  shape of the thread never fires. The shapes of the interpreter's stages are patterns, so which
  rules can fire at a stage is decided once, by `decide`.
* **A renamed administrative firing with its scopes** (`admin_renamed`): R100's
  `admin_step_renames`, with the renaming invertible on every variable below the firing's scope and
  on its fresh variables, and the results bounded by the next scope.
* **Renamed copies** (`Copy`, `FreshFor`, `copy_comp`, `fresh_map`, `fresh_cons`): the caller's
  variables renamed invertibly, and allocated variables kept distinct and apart from the caller's,
  under every later renaming.
* **The building code's meaning** (`Ins`, `icode`, `exec`): the postfix code `bcode` run on a stack;
  it builds the copy (`exec_icode`) and commutes with every substitution (`exec_apply`).
* **The store's firing on any renamed copy** (`store_renamed`, `store_unifiable_renamed`): R95's
  `store_answer_renames`, generalized from the allocation `freshVars n₀` to any list of distinct
  variables apart from the caller's, and from the call to any invertible renaming of it. The answer
  and the other rows are the compiled ones under a renaming, and the compiled ones are theirs under
  another.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded getD_mem fill_vars_sub)

/-! ## Substitutions through the interpreter's terms -/

theorem getD_map_apply (σ : Subst rows) (l : List Tm) (x : ℕ) :
    (l.map σ.applyTerm).getD x (.const 0) = σ.applyTerm (l.getD x (.const 0)) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[x]? <;> rfl

theorem fill_apply (σ : Subst rows) (vals : List Tm) : ∀ p : Pat,
    σ.applyTerm (Pat.fill vals p) = Pat.fill (vals.map σ.applyTerm) p
  | .var x => (getD_map_apply σ vals x).symm
  | .sym _ => rfl
  | .cell a b => by
      show σ.applyTerm (node (Pat.fill vals a) (Pat.fill vals b)) = node _ _
      rw [apply_node, fill_apply σ vals a, fill_apply σ vals b]

theorem tseq_apply (σ : Subst rows) : ∀ l : List Tm, σ.applyTerm (tseq l) = tseq (l.map σ.applyTerm)
  | [] => rfl
  | a :: l => by
      show σ.applyTerm (node a (tseq l)) = node (σ.applyTerm a) (tseq (l.map σ.applyTerm))
      rw [apply_node, tseq_apply σ l]

theorem ttup_apply (σ : Subst rows) (k : ℕ) (l : List Tm) :
    σ.applyTerm (ttup k l) = ttup k (l.map σ.applyTerm) := by
  show σ.applyTerm (node (.const k) (tseq l)) = node (.const k) (tseq (l.map σ.applyTerm))
  rw [apply_node, tseq_apply]
  rfl

theorem tlist_apply (σ : Subst rows) : ∀ l : List Tm, σ.applyTerm (tlist l) = tlist (l.map σ.applyTerm)
  | [] => by
      show σ.applyTerm (ttup 91 []) = ttup 91 []
      rw [ttup_apply]
      rfl
  | a :: l => by
      show σ.applyTerm (ttup 90 [a, tlist l]) = ttup 90 [σ.applyTerm a, tlist (l.map σ.applyTerm)]
      rw [ttup_apply, List.map_cons, List.map_cons, List.map_nil, tlist_apply σ l]

theorem bounded_of_tseq {m : ℕ} : ∀ {l : List Tm}, Bounded m (tseq l) → ∀ u ∈ l, Bounded m u
  | [], _, _, h => absurd h List.not_mem_nil
  | _ :: _, b, u, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact fun v hv => b v (mem_freeVars_node.mpr (.inl hv))
      · exact bounded_of_tseq (fun v hv => b v (mem_freeVars_node.mpr (.inr hv))) u h

theorem bounded_of_ttup {m k : ℕ} {l : List Tm} (b : Bounded m (ttup k l)) : ∀ u ∈ l, Bounded m u :=
  bounded_of_tseq fun v hv => b v (mem_freeVars_node.mpr (.inr hv))

theorem bounded_of_tlist {m : ℕ} : ∀ {l : List Tm}, Bounded m (tlist l) → ∀ u ∈ l, Bounded m u
  | [], _, _, h => absurd h List.not_mem_nil
  | a :: l, b, u, h => by
      have parts := bounded_of_ttup (k := 90) (l := [a, tlist l]) b
      rcases List.mem_cons.mp h with rfl | h
      · exact parts _ List.mem_cons_self
      · exact bounded_of_tlist (parts _ (by simp)) u h

/-! ## Forcing -/

/-- **Two patterns clash**: at a position where both have a symbol or a cell, they differ. -/
def Clash : Pat → Pat → Bool
  | .var _, _ => false
  | .sym _, .var _ => false
  | .sym k, .sym k' => k != k'
  | .sym _, .cell _ _ => true
  | .cell _ _, .var _ => false
  | .cell _ _, .sym _ => true
  | .cell a b, .cell c d => Clash a c || Clash b d

/-- **Clashing patterns never unify**, whatever fills the second one's variables. -/
theorem clash_apart {σ : Subst rows} {n : ℕ} {vals : List Tm} :
    ∀ {p q : Pat}, Clash p q = true → σ.applyTerm (p.at n) ≠ σ.applyTerm (Pat.fill vals q)
  | .var _, _, h, _ => by simp [Clash] at h
  | .sym _, .var _, h, _ => by simp [Clash] at h
  | .sym k, .sym k', h, same => by
      have ne : k ≠ k' := by simpa [Clash] using h
      change (Term.const k : Tm) = Term.const k' at same
      exact ne (Term.const.inj same)
  | .sym k, .cell c d, _, same => by
      change (Term.const k : Tm) = σ.applyTerm (node (Pat.fill vals c) (Pat.fill vals d)) at same
      rw [apply_node] at same
      exact node_ne_const same.symm
  | .cell _ _, .var _, h, _ => by simp [Clash] at h
  | .cell a b, .sym k, _, same => by
      change σ.applyTerm (node (a.at n) (b.at n)) = (Term.const k : Tm) at same
      rw [apply_node] at same
      exact node_ne_const same
  | .cell a b, .cell c d, h, same => by
      change σ.applyTerm (node (a.at n) (b.at n)) =
        σ.applyTerm (node (Pat.fill vals c) (Pat.fill vals d)) at same
      rw [apply_node, apply_node, node_inj] at same
      simp only [Clash, Bool.or_eq_true] at h
      rcases h with h | h
      · exact clash_apart h same.1
      · exact clash_apart h same.2

/-- **Forcing**: a step from a thread of the shape of `q` fires a rule whose left-hand side does not
clash with `q`, under a most general unifier. -/
theorem forced {q : Pat} {vals : List Tm} {F : Multiset Tm} {n : ℕ} (free : ThreadFree F)
    {target : Multiset Tm × ℕ} (step : EqStep joinMeta (thread (Pat.fill vals q) ::ₘ F, n) target) :
    ∃ (j : Fin joinMeta.length) (θ : Subst rows), Clash (joinMeta.get j).lhs q = false ∧
      IsMGU [((joinMeta.get j).lhs.at n, Pat.fill vals q)] θ ∧
      target = (thread (θ.applyTerm ((joinMeta.get j).rhs.at n)) ::ₘ F.map θ.applyTerm, n + 1) := by
  obtain ⟨j, θ, mgu, rfl⟩ := eqStep_inversion free step
  refine ⟨j, θ, ?_, mgu, rfl⟩
  cases h : Clash (joinMeta.get j).lhs q
  · rfl
  · exact absurd ((unifies_single θ _ _).mp mgu.unifies) (clash_apart h)

/-! ## A renamed administrative firing, with its scopes -/

/-- A most general unifier whose problem names only scopes below `n` keeps terms below `n`. -/
theorem bounded_after {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) {n : ℕ}
    (scopes : ∀ v ∈ eqVars P, v.1 < n) {u : Tm} (bounded : Bounded n u) : Bounded n (θ.applyTerm u) := by
  intro x hx
  obtain ⟨v, hv, hx⟩ := (Subst.mem_freeVars_applyTerm (σ := rows)).mp hx
  by_cases fixed : θ v = .var v
  · rw [fixed, Term.mem_freeVars_var (σ := rows)] at hx
    subst hx
    exact bounded x hv
  · have member : v ∈ eqVars P := by
      by_contra out
      exact fixed (mgu.relevant.fixes v out)
    exact scopes x (mgu.relevant.range v member hx)

/-- **A renamed administrative firing.** On an instance of a rule's left-hand side, every most
general unifier is the matcher followed by a renaming `κ`, invertible on every variable below the
firing's scope and on the scope's variables beyond the matched ones; the results lie below the next
scope. -/
theorem admin_renamed {e : ProgramEquations.Equation} {n : ℕ} {vals : List Tm}
    (bounded : ∀ t ∈ vals, Bounded n t) (covers : ∀ x < vals.length, x ∈ e.lhs.vars)
    (within : ∀ x ∈ e.lhs.vars, x < vals.length)
    {θ : Subst rows} (mgu : IsMGU [(e.lhs.at n, Pat.fill vals e.lhs)] θ) :
    ∃ κ κ' : Subst rows, IsRenaming κ ∧ IsRenaming κ' ∧
      (∀ x : ℕ × ℕ, (x.1 < n ∨ (x.1 = n ∧ vals.length ≤ x.2)) → κ'.applyTerm (κ x) = .var x) ∧
      θ.applyTerm (e.rhs.at n) = κ.applyTerm ((matcher n vals).applyTerm (e.rhs.at n)) ∧
      (∀ u, Bounded n u → θ.applyTerm u = κ.applyTerm u) ∧
      Bounded (n + 1) (θ.applyTerm (e.rhs.at n)) ∧ ∀ u, Bounded n u → Bounded (n + 1) (κ.applyTerm u) := by
  obtain ⟨κ, κ', isRen, isRen', toθ, -, back, -⟩ :=
    mgu_unique_up_to_renaming (matcher_isMGU bounded covers within) mgu
  have below : ∀ u, Bounded n u → θ.applyTerm u = κ.applyTerm u := fun u hu => by
    rw [apply_comp_congr toθ u, matcher_fixes hu]
  have scopes : ∀ v ∈ eqVars [(e.lhs.at n, Pat.fill vals e.lhs)], v.1 < n + 1 := by
    intro v hv
    simp only [eqVars, Finset.union_empty, Finset.mem_union] at hv
    rcases hv with hv | hv
    · rw [at_scope n _ v hv]
      exact Nat.lt_succ_self n
    · exact Nat.lt_succ_of_lt (fill_bounded bounded _ v hv)
  refine ⟨κ, κ', isRen, isRen', fun x hx => back x ⟨x, ?_⟩, apply_comp_congr toθ _, below,
    bounded_after mgu scopes (at_bounded n _), fun u hu => ?_⟩
  · rw [matcher, if_neg (by rintro ⟨h₁, h₂⟩; rcases hx with h | ⟨h, h'⟩ <;> omega),
      Term.mem_freeVars_var (σ := rows)]
  · rw [← below u hu]
    exact bounded_after mgu scopes (hu.mono (Nat.le_succ n))

/-! ## Renamed copies -/

/-- The caller's variables: those of the call and of the other rows. -/
def CallerVar (t : Tm) (F : Multiset Tm) (x : ℕ × ℕ) : Prop :=
  x ∈ t.freeVars ∨ ∃ f ∈ F, x ∈ f.freeVars

/-- `ρ` renames the caller's variables, invertibly. -/
def Copy (ρ : Subst rows) (t : Tm) (F : Multiset Tm) : Prop :=
  IsRenaming ρ ∧ ∃ ρ' : Subst rows, ∀ x, CallerVar t F x → ρ'.applyTerm (ρ x) = .var x

/-- `env` is a list of distinct variables, none of them the caller's. -/
def FreshFor (env : List Tm) (t : Tm) (F : Multiset Tm) : Prop :=
  (∀ w ∈ env, ∃ x, w = .var x) ∧ env.Nodup ∧ ∀ w ∈ env, ∀ x ∈ w.freeVars, ¬ CallerVar t F x

theorem copy_id (t : Tm) (F : Multiset Tm) : Copy (Subst.id rows) t F :=
  ⟨fun x => ⟨x, rfl⟩, Subst.id rows, fun _ _ => rfl⟩

theorem callerVar_map {ρ : Subst rows} {t : Tm} {F : Multiset Tm} {x y : ℕ × ℕ} (caller : CallerVar t F x)
    (hy : ρ x = .var y) : CallerVar (ρ.applyTerm t) (F.map ρ.applyTerm) y := by
  have occurs : y ∈ (ρ x).freeVars := by rw [hy]; exact (Term.mem_freeVars_var (σ := rows)).mpr rfl
  rcases caller with hx | ⟨f, member, hx⟩
  · exact .inl ((Subst.mem_freeVars_applyTerm (σ := rows)).mpr ⟨x, hx, occurs⟩)
  · exact .inr ⟨ρ.applyTerm f, Multiset.mem_map_of_mem _ member,
      (Subst.mem_freeVars_applyTerm (σ := rows)).mpr ⟨x, hx, occurs⟩⟩

theorem callerVar_of_map {κ : Subst rows} {t : Tm} {F : Multiset Tm} {y : ℕ × ℕ}
    (caller : CallerVar (κ.applyTerm t) (F.map κ.applyTerm) y) :
    ∃ x, CallerVar t F x ∧ y ∈ (κ x).freeVars := by
  rcases caller with hy | ⟨g, member, hy⟩
  · obtain ⟨x, hx, occurs⟩ := (Subst.mem_freeVars_applyTerm (σ := rows)).mp hy
    exact ⟨x, .inl hx, occurs⟩
  · obtain ⟨f, fm, rfl⟩ := Multiset.mem_map.mp member
    obtain ⟨x, hx, occurs⟩ := (Subst.mem_freeVars_applyTerm (σ := rows)).mp hy
    exact ⟨x, .inr ⟨f, fm, hx⟩, occurs⟩

/-- **Renamings compose on the caller.** -/
theorem copy_comp {ρ κ κ' : Subst rows} {t : Tm} {F : Multiset Tm} (copy : Copy ρ t F)
    (ren : IsRenaming κ) {Q : ℕ × ℕ → Prop}
    (inQ : ∀ x, CallerVar (ρ.applyTerm t) (F.map ρ.applyTerm) x → Q x)
    (back : ∀ x, Q x → κ'.applyTerm (κ x) = .var x) : Copy (κ ∘ₛ ρ) t F := by
  obtain ⟨renρ, ρ', inv⟩ := copy
  refine ⟨fun x => ?_, ρ' ∘ₛ κ', fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := renρ x
    obtain ⟨z, hz⟩ := ren y
    exact ⟨z, by rw [Subst.comp_apply, hy, Subst.applyTerm_var, hz]⟩
  · obtain ⟨y, hy⟩ := renρ x
    have cy := callerVar_map hx hy
    have invx := inv x hx
    rw [hy, Subst.applyTerm_var] at invx
    rw [Subst.comp_apply, hy, Subst.applyTerm_var, Subst.applyTerm_comp, back y (inQ y cy),
      Subst.applyTerm_var, invx]

/-- **Allocated variables stay distinct and apart from the caller's** under a renaming invertible on
them and on the caller's. -/
theorem fresh_map {env : List Tm} {t : Tm} {F : Multiset Tm} (fresh : FreshFor env t F)
    {κ κ' : Subst rows} (ren : IsRenaming κ) {Q : ℕ × ℕ → Prop}
    (envQ : ∀ w ∈ env, ∀ x ∈ w.freeVars, Q x) (callerQ : ∀ x, CallerVar t F x → Q x)
    (back : ∀ x, Q x → κ'.applyTerm (κ x) = .var x) :
    FreshFor (env.map κ.applyTerm) (κ.applyTerm t) (F.map κ.applyTerm) := by
  obtain ⟨vars, nodup, apart⟩ := fresh
  have self : ∀ x : ℕ × ℕ, x ∈ (Term.var x : Tm).freeVars := fun x => (Term.mem_freeVars_var (σ := rows)).mpr rfl
  refine ⟨?_, ?_, ?_⟩
  · intro w member
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp member
    obtain ⟨x, rfl⟩ := vars u hu
    obtain ⟨y, hy⟩ := ren x
    exact ⟨y, by rw [Subst.applyTerm_var, hy]⟩
  · refine List.Nodup.map_on (fun u hu u' hu' same => ?_) nodup
    obtain ⟨x, rfl⟩ := vars u hu
    obtain ⟨x', rfl⟩ := vars u' hu'
    have h := congrArg κ'.applyTerm same
    rw [Subst.applyTerm_var, Subst.applyTerm_var, back x (envQ _ hu x (self x)),
      back x' (envQ _ hu' x' (self x'))] at h
    exact h
  · intro w member z hz caller
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp member
    obtain ⟨x, rfl⟩ := vars u hu
    obtain ⟨v, cv, hzv⟩ := callerVar_of_map caller
    obtain ⟨y, hy⟩ := ren x
    obtain ⟨y', hy'⟩ := ren v
    rw [Subst.applyTerm_var, hy, Term.mem_freeVars_var (σ := rows)] at hz
    rw [hy', Term.mem_freeVars_var (σ := rows)] at hzv
    have same : κ'.applyTerm (κ x) = κ'.applyTerm (κ v) := by rw [hy, hy', ← hz, ← hzv]
    rw [back x (envQ _ hu x (self x)), back v (callerQ v cv)] at same
    have hxv : x = v := Term.var.inj same
    rw [← hxv] at cv
    exact apart _ hu x (self x) cv

theorem fresh_cons {env : List Tm} {t : Tm} {F : Multiset Tm} (fresh : FreshFor env t F) {x : ℕ × ℕ}
    (newEnv : ∀ w ∈ env, x ∉ w.freeVars) (newCaller : ¬ CallerVar t F x) :
    FreshFor (.var x :: env) t F := by
  obtain ⟨vars, nodup, apart⟩ := fresh
  have self : x ∈ (Term.var x : Tm).freeVars := (Term.mem_freeVars_var (σ := rows)).mpr rfl
  refine ⟨?_, List.nodup_cons.mpr ⟨fun member => newEnv _ member self, nodup⟩, ?_⟩
  · intro w member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨x, rfl⟩
    · exact vars w member
  · intro w member z hz
    rcases List.mem_cons.mp member with rfl | member
    · rw [Term.mem_freeVars_var (σ := rows)] at hz
      subst hz
      exact newCaller
    · exact apart w member z hz

theorem fresh_nil (t : Tm) (F : Multiset Tm) : FreshFor [] t F :=
  ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩

/-! ## The building code's meaning -/

/-- Building instructions: push a symbol, push the allocated variable of a slot, build a cell. -/
inductive Ins where
  | sym (k : ℕ)
  | var (x : ℕ)
  | cell

/-- The instruction as data, as `bcode` writes it. -/
def Ins.enc : Ins → Sx
  | .sym k => tup 170 [.sym k]
  | .var x => tup 171 [nat x]
  | .cell => tup 172 []

/-- The building code of a pattern, as instructions. -/
def icode : Pat → List Ins
  | .var x => [.var x]
  | .sym k => [.sym k]
  | .cell a b => icode a ++ icode b ++ [.cell]

theorem bcode_eq : ∀ p : Pat, bcode p = (icode p).map Ins.enc
  | .var _ => rfl
  | .sym _ => rfl
  | .cell a b => by
      rw [bcode, icode, bcode_eq a, bcode_eq b, List.map_append, List.map_append]
      rfl

/-- **The building code run on a stack**, reading the allocated variables from `env`. -/
def exec (env : List Tm) : List Ins → List Tm → Option (List Tm)
  | [], S => some S
  | .sym k :: C, S => exec env C (.const k :: S)
  | .var x :: C, S => if x < env.length then exec env C (env.getD x (.const 0) :: S) else none
  | .cell :: _, [] => none
  | .cell :: _, [_] => none
  | .cell :: C, a :: b :: S => exec env C (node b a :: S)

/-- **The code of a pattern pushes its copy.** -/
theorem exec_icode (env : List Tm) : ∀ (p : Pat), (∀ x ∈ p.vars, x < env.length) →
    ∀ (C : List Ins) (S : List Tm), exec env (icode p ++ C) S = exec env C (Pat.fill env p :: S)
  | .var x, within, C, S => by
      have lt := within x (by simp [Pat.vars])
      show exec env (.var x :: C) S = _
      rw [exec, if_pos lt]
      rfl
  | .sym _, _, _, _ => rfl
  | .cell a b, within, C, S => by
      rw [icode, List.append_assoc, List.append_assoc,
        exec_icode env a (fun x hx => within x (by simp [Pat.vars, hx])),
        exec_icode env b (fun x hx => within x (by simp [Pat.vars, hx]))]
      rfl

/-- **The building code commutes with every substitution.** -/
theorem exec_apply (σ : Subst rows) (env : List Tm) : ∀ (C : List Ins) (S R : List Tm),
    exec env C S = some R → exec (env.map σ.applyTerm) C (S.map σ.applyTerm) = some (R.map σ.applyTerm)
  | [], S, R, h => by
      rw [exec, Option.some.injEq] at h
      rw [h]
      rfl
  | .sym k :: C, S, R, h => exec_apply σ env C (.const k :: S) R h
  | .var x :: C, S, R, h => by
      rw [exec] at h
      by_cases lt : x < env.length
      · rw [if_pos lt] at h
        have := exec_apply σ env C _ R h
        rw [List.map_cons, ← getD_map_apply] at this
        rw [exec, if_pos (by rw [List.length_map]; exact lt)]
        exact this
      · rw [if_neg lt] at h
        cases h
  | .cell :: _, [], _, h => by rw [exec] at h; cases h
  | .cell :: _, [_], _, h => by rw [exec] at h; cases h
  | .cell :: C, a :: b :: S, R, h => by
      have := exec_apply σ env C _ R h
      rw [List.map_cons, apply_node] at this
      exact this

/-! ## The store's firing on any renamed copy -/

open Classical in
/-- Send the copy back: each allocated variable to its slot at scope `n`, every other variable
through `ρ'`. -/
noncomputable def uncopy (n : ℕ) (env : List Tm) (ρ' : Subst rows) : Subst rows := fun w =>
  if h : ∃ i, i < env.length ∧ env.getD i (.const 0) = .var w then .var (n, h.choose) else ρ' w

theorem uncopy_slot {n : ℕ} {env : List Tm} {ρ' : Subst rows} (nodup : env.Nodup) {i : ℕ}
    (lt : i < env.length) {w : ℕ × ℕ} (at_i : env.getD i (.const 0) = .var w) :
    uncopy n env ρ' w = .var (n, i) := by
  have h : ∃ i, i < env.length ∧ env.getD i (.const 0) = .var w := ⟨i, lt, at_i⟩
  rw [uncopy, dif_pos h]
  obtain ⟨lt', at'⟩ := h.choose_spec
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt', Option.getD_some] at at'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt, Option.getD_some] at at_i
  rw [(List.Nodup.getElem_inj_iff nodup).mp (at'.trans at_i.symm)]

theorem uncopy_other {n : ℕ} {env : List Tm} {ρ' : Subst rows} {w : ℕ × ℕ} (out : (Term.var w : Tm) ∉ env) :
    uncopy n env ρ' w = ρ' w := by
  have none : ¬ ∃ i, i < env.length ∧ env.getD i (.const 0) = .var w := by
    rintro ⟨i, lt, at_i⟩
    exact out (at_i ▸ getD_mem lt _)
  rw [uncopy, dif_neg none]

/-- The copy: each slot of scope `n` to its allocated variable, every other variable through `ρ`. -/
def copyOf (n : ℕ) (env : List Tm) (ρ : Subst rows) : Subst rows := fun v =>
  if v.1 = n ∧ v.2 < env.length then env.getD v.2 (.const 0) else ρ v

theorem copyOf_at {n : ℕ} {env : List Tm} {ρ : Subst rows} : ∀ (p : Pat), (∀ x ∈ p.vars, x < env.length) →
    (copyOf n env ρ).applyTerm (p.at n) = Pat.fill env p
  | .var x, within => by
      show copyOf n env ρ (n, x) = env.getD x (.const 0)
      rw [copyOf, if_pos ⟨rfl, within x (by simp [Pat.vars])⟩]
  | .sym _, _ => rfl
  | .cell a b, within => by
      rw [Pat.at, apply_node, copyOf_at a fun x hx => within x (by simp [Pat.vars, hx]),
        copyOf_at b fun x hx => within x (by simp [Pat.vars, hx])]
      rfl

theorem copyOf_below {n : ℕ} {env : List Tm} {ρ : Subst rows} {u : Tm} (bounded : Bounded n u) :
    (copyOf n env ρ).applyTerm u = ρ.applyTerm u :=
  Subst.applyTerm_congr fun v hv => by
    rw [copyOf, if_neg fun h => absurd h.1 (Nat.ne_of_lt (bounded v hv))]

theorem caller_var_out {env : List Tm} {t : Tm} {F : Multiset Tm} (fresh : FreshFor env t F) {y : ℕ × ℕ}
    (caller : CallerVar t F y) : (Term.var y : Tm) ∉ env := fun member =>
  fresh.2.2 _ member y ((Term.mem_freeVars_var (σ := rows)).mpr rfl) caller

theorem uncopy_fill {n : ℕ} {env : List Tm} {ρ' : Subst rows} (vars : ∀ w ∈ env, ∃ x, w = .var x)
    (nodup : env.Nodup) : ∀ (p : Pat), (∀ x ∈ p.vars, x < env.length) →
      (uncopy n env ρ').applyTerm (Pat.fill env p) = p.at n
  | .var x, within => by
      have lt := within x (by simp [Pat.vars])
      obtain ⟨w, hw⟩ := vars _ (getD_mem lt (.const 0))
      show (uncopy n env ρ').applyTerm (env.getD x (.const 0)) = .var (n, x)
      rw [hw, Subst.applyTerm_var, uncopy_slot nodup lt hw]
  | .sym _, _ => rfl
  | .cell a b, within => by
      show (uncopy n env ρ').applyTerm (node (Pat.fill env a) (Pat.fill env b)) = node (a.at n) (b.at n)
      rw [apply_node, uncopy_fill vars nodup a fun x hx => within x (by simp [Pat.vars, hx]),
        uncopy_fill vars nodup b fun x hx => within x (by simp [Pat.vars, hx])]

theorem uncopy_caller {n : ℕ} {env : List Tm} {ρ ρ' : Subst rows} {t : Tm} {F : Multiset Tm}
    (copy : IsRenaming ρ) (inv : ∀ x, CallerVar t F x → ρ'.applyTerm (ρ x) = .var x)
    (fresh : FreshFor env (ρ.applyTerm t) (F.map ρ.applyTerm)) {u : Tm} (callerU : ∀ x ∈ u.freeVars, CallerVar t F x) :
    (uncopy n env ρ').applyTerm (ρ.applyTerm u) = u := by
  rw [← Subst.applyTerm_comp]
  refine Subst.applyTerm_eq_self fun v hv => ?_
  obtain ⟨y, hy⟩ := copy v
  have cy := callerVar_map (callerU v hv) hy
  have iv := inv v (callerU v hv)
  rw [hy, Subst.applyTerm_var] at iv
  rw [Subst.comp_apply, hy, Subst.applyTerm_var, uncopy_other (caller_var_out fresh cy), iv]

/-- A variable of a copied slot is a variable of the fill. -/
theorem slot_in_fill {env : List Tm} {p : Pat} {i : ℕ} (hi : i ∈ p.vars) {w : ℕ × ℕ}
    (hw : env.getD i (.const 0) = .var w) : w ∈ (Pat.fill env p).freeVars :=
  fill_vars_sub p hi (by rw [hw]; exact (Term.mem_freeVars_var (σ := rows)).mpr rfl)

/-- The variables of `θ` and `θ'` that matter for the store's firing. -/
def StoreVar (e : ProgramEquations.Equation) (n : ℕ) (t : Tm) (F : Multiset Tm) (v : ℕ × ℕ) : Prop :=
  (v.1 = n ∧ (v.2 ∈ e.lhs.vars ∨ v.2 ∈ e.rhs.vars)) ∨ CallerVar t F v

/-- **The store's firing on any renamed copy.** The thread holds a copy of an equation's two sides,
built from distinct variables apart from the caller's, and an invertible renaming of the call; the
other rows are renamed the same way. For every most general unifier of the compiled problem and of
the store's firing, the answer and the other rows are the compiled ones under a renaming `κ`, and the
compiled ones are theirs under a renaming `κ'`. -/
theorem store_renamed {e : ProgramEquations.Equation} {t : Tm} {F : Multiset Tm} {n m : ℕ}
    (tB : Bounded n t) (FB : ∀ f ∈ F, Bounded n f) {ρ : Subst rows} (copy : Copy ρ t F)
    {env : List Tm} (fresh : FreshFor env (ρ.applyTerm t) (F.map ρ.applyTerm)) (len : env.length = slots e)
    (rowB : Bounded m (ttup 169 [Pat.fill env e.lhs, Pat.fill env e.rhs, ρ.applyTerm t]))
    (FB' : ∀ f ∈ F, Bounded m (ρ.applyTerm f))
    {θc : Subst rows} (mgu : IsMGU [(e.lhs.at n, t)] θc) {θ' : Subst rows}
    (mgu' : IsMGU [(jApply.lhs.at m, ttup 169 [Pat.fill env e.lhs, Pat.fill env e.rhs, ρ.applyTerm t])] θ') :
    ∃ κ κ' : Subst rows, IsRenaming κ ∧ IsRenaming κ' ∧
      θ' (m, 1) = κ.applyTerm (θc.applyTerm (e.rhs.at n)) ∧
      θc.applyTerm (e.rhs.at n) = κ'.applyTerm (θ' (m, 1)) ∧
      ∀ f ∈ F, θ'.applyTerm (ρ.applyTerm f) = κ.applyTerm (θc.applyTerm f) ∧
        θc.applyTerm f = κ'.applyTerm (θ'.applyTerm (ρ.applyTerm f)) := by
  obtain ⟨renρ, ρ', inv⟩ := copy
  have vars := fresh.1
  have nodup := fresh.2.1
  have withinL : ∀ x ∈ e.lhs.vars, x < env.length := fun x hx => by
    rw [len]; exact lt_slots (List.mem_append_left _ hx)
  have withinR : ∀ x ∈ e.rhs.vars, x < env.length := fun x hx => by
    rw [len]; exact lt_slots (List.mem_append_right _ hx)
  have parts := bounded_of_ttup rowB
  have LB : Bounded m (Pat.fill env e.lhs) := parts _ List.mem_cons_self
  have RB : Bounded m (Pat.fill env e.rhs) := parts _ (by simp)
  have tB' : Bounded m (ρ.applyTerm t) := parts _ (by simp)
  -- the store's unifier, componentwise
  have storeEq : θ'.applyTerm (ttup 169 [.var (m, 0), .var (m, 1), .var (m, 0)]) =
      θ'.applyTerm (ttup 169 [Pat.fill env e.lhs, Pat.fill env e.rhs, ρ.applyTerm t]) :=
    mgu'.unifies _ List.mem_cons_self
  obtain ⟨atL, atR, atT⟩ := ttup_forced storeEq
  rw [Subst.applyTerm_var] at atL atR atT
  -- the compiled unifier is more general than the store's, read through the copy
  have unifies₂ : Unifies (θ' ∘ₛ copyOf n env ρ) [(e.lhs.at n, t)] := by
    rw [unifies_single, Subst.applyTerm_comp, Subst.applyTerm_comp, copyOf_at _ withinL,
      copyOf_below tB, ← atL, atT]
  obtain ⟨α, hα⟩ := mgu.general _ unifies₂
  -- and the store's is more general than the compiled one, on the variables that matter
  let δ : Subst rows := fun w =>
    if w = (m, 0) then θc.applyTerm t else if w = (m, 1) then θc.applyTerm (e.rhs.at n)
      else θc.applyTerm (uncopy n env ρ' w)
  have δbelow : ∀ u : Tm, Bounded m u → δ.applyTerm u = θc.applyTerm ((uncopy n env ρ').applyTerm u) := by
    intro u hu
    rw [← Subst.applyTerm_comp]
    refine Subst.applyTerm_congr fun w hw => ?_
    have lt := hu w hw
    have ne₀ : w ≠ (m, 0) := fun h => by rw [h] at lt; exact lt_irrefl m lt
    have ne₁ : w ≠ (m, 1) := fun h => by rw [h] at lt; exact lt_irrefl m lt
    simp only [δ, if_neg ne₀, if_neg ne₁]
    rfl
  have callerT : ∀ x ∈ t.freeVars, CallerVar t F x := fun x hx => .inl hx
  have unifiesδ : Unifies δ [(jApply.lhs.at m, ttup 169 [Pat.fill env e.lhs, Pat.fill env e.rhs, ρ.applyTerm t])] := by
    rw [unifies_single, show (jApply.lhs.at m) = ttup 169 [.var (m, 0), .var (m, 1), .var (m, 0)] from rfl]
    have v0 : δ (m, 0) = θc.applyTerm t := by simp [δ]
    have v1 : δ (m, 1) = θc.applyTerm (e.rhs.at n) := by simp [δ]
    have dL : δ.applyTerm (Pat.fill env e.lhs) = θc.applyTerm (e.lhs.at n) := by
      rw [δbelow _ LB, uncopy_fill vars nodup _ withinL]
    have dR : δ.applyTerm (Pat.fill env e.rhs) = θc.applyTerm (e.rhs.at n) := by
      rw [δbelow _ RB, uncopy_fill vars nodup _ withinR]
    have dt : δ.applyTerm (ρ.applyTerm t) = θc.applyTerm t := by
      rw [δbelow _ tB', uncopy_caller renρ inv fresh callerT]
    have compiled : θc.applyTerm (e.lhs.at n) = θc.applyTerm t := (unifies_single θc _ _).mp mgu.unifies
    simp only [ttup, tseq, apply_node, Subst.applyTerm_var, Subst.applyTerm_const, v0, v1, dL, dR, dt,
      compiled]
  obtain ⟨β, hβ⟩ := mgu'.general δ unifiesδ
  have h₁ : ∀ v, StoreVar e n t F v → (θ' ∘ₛ copyOf n env ρ) v = α.applyTerm (θc v) := fun v _ => hα v
  have h₂ : ∀ v, StoreVar e n t F v → θc v = β.applyTerm ((θ' ∘ₛ copyOf n env ρ) v) := by
    intro v hv
    rw [Subst.comp_apply, ← Subst.applyTerm_comp]
    rcases hv with ⟨scope, used⟩ | caller
    · have lt : v.2 < env.length := used.elim (withinL _) (withinR _)
      obtain ⟨w, hw⟩ := vars _ (getD_mem lt (.const 0))
      have wB : w.1 < m := used.elim (fun h => LB w (slot_in_fill h hw)) (fun h => RB w (slot_in_fill h hw))
      have slot : copyOf n env ρ v = .var w := by rw [copyOf, if_pos ⟨scope, lt⟩, hw]
      rw [slot, Subst.applyTerm_var, Subst.comp_apply, ← hβ]
      have ne₀ : w ≠ (m, 0) := fun h => by rw [h] at wB; exact lt_irrefl m wB
      have ne₁ : w ≠ (m, 1) := fun h => by rw [h] at wB; exact lt_irrefl m wB
      simp only [δ, if_neg ne₀, if_neg ne₁]
      rw [uncopy_slot nodup lt hw, Subst.applyTerm_var, show ((n, v.2) : ℕ × ℕ) = v from Prod.ext scope.symm rfl]
    · have below : v.1 < n := by
        rcases caller with hx | ⟨f, member, hx⟩
        · exact tB v hx
        · exact FB f member v hx
      obtain ⟨y, hy⟩ := renρ v
      have cy := callerVar_map caller hy
      have yB : y.1 < m := by
        rcases cy with hx | ⟨g, member, hx⟩
        · exact tB' y hx
        · obtain ⟨f, fm, rfl⟩ := Multiset.mem_map.mp member
          exact FB' f fm y hx
      have other : copyOf n env ρ v = .var y := by
        rw [copyOf, if_neg fun h => absurd h.1 (Nat.ne_of_lt below), hy]
      have iv := inv v caller
      rw [hy, Subst.applyTerm_var] at iv
      rw [other, Subst.applyTerm_var, Subst.comp_apply, ← hβ]
      have ne₀ : y ≠ (m, 0) := fun h => by rw [h] at yB; exact lt_irrefl m yB
      have ne₁ : y ≠ (m, 1) := fun h => by rw [h] at yB; exact lt_irrefl m yB
      simp only [δ, if_neg ne₀, if_neg ne₁]
      rw [uncopy_other (caller_var_out fresh cy), iv, Subst.applyTerm_var]
  obtain ⟨κ, κ', ren, ren', there, back, -, -⟩ := renaming_on h₁ h₂
  have onV : ∀ u : Tm, (∀ v ∈ u.freeVars, StoreVar e n t F v) →
      θ'.applyTerm ((copyOf n env ρ).applyTerm u) = κ.applyTerm (θc.applyTerm u) ∧
        θc.applyTerm u = κ'.applyTerm (θ'.applyTerm ((copyOf n env ρ).applyTerm u)) := by
    intro u hu
    refine ⟨?_, ?_⟩
    · rw [← Subst.applyTerm_comp θ' (copyOf n env ρ), ← Subst.applyTerm_comp κ θc]
      exact Subst.applyTerm_congr fun v hv => there v (hu v hv)
    · rw [← Subst.applyTerm_comp θ' (copyOf n env ρ), ← Subst.applyTerm_comp κ' (θ' ∘ₛ copyOf n env ρ)]
      exact Subst.applyTerm_congr fun v hv => back v (hu v hv)
  have rhsV : ∀ v ∈ (e.rhs.at n).freeVars, StoreVar e n t F v := fun v hv =>
    .inl ⟨at_scope n _ v hv, .inr (vars_of_at _ hv)⟩
  obtain ⟨ans, ans'⟩ := onV _ rhsV
  rw [copyOf_at _ withinR, ← atR] at ans ans'
  refine ⟨κ, κ', ren, ren', ans, ans', fun f member => ?_⟩
  obtain ⟨row, row'⟩ := onV f fun v hv => .inr (.inr ⟨f, member, hv⟩)
  rw [copyOf_below (FB f member)] at row row'
  exact ⟨row, row'⟩

/-- **The compiled problem is solvable whenever the store's is.** -/
theorem store_unifiable_renamed {e : ProgramEquations.Equation} {t : Tm} {n m : ℕ} (tB : Bounded n t)
    {ρ : Subst rows} {env : List Tm} (len : env.length = slots e) {θ' : Subst rows}
    (unifies : Unifies θ' [(jApply.lhs.at m, ttup 169 [Pat.fill env e.lhs, Pat.fill env e.rhs, ρ.applyTerm t])]) :
    ∃ θc, IsMGU [(e.lhs.at n, t)] θc := by
  have withinL : ∀ x ∈ e.lhs.vars, x < env.length := fun x hx => by
    rw [len]; exact lt_slots (List.mem_append_left _ hx)
  have storeEq : θ'.applyTerm (ttup 169 [.var (m, 0), .var (m, 1), .var (m, 0)]) =
      θ'.applyTerm (ttup 169 [Pat.fill env e.lhs, Pat.fill env e.rhs, ρ.applyTerm t]) :=
    unifies _ List.mem_cons_self
  obtain ⟨atL, -, atT⟩ := ttup_forced storeEq
  rw [Subst.applyTerm_var] at atL atT
  refine exists_isMGU ⟨θ' ∘ₛ copyOf n env ρ, ?_⟩
  rw [unifies_single, Subst.applyTerm_comp, Subst.applyTerm_comp, copyOf_at _ withinL,
    copyOf_below tB, ← atL, atT]

#print axioms fill_apply
#print axioms tlist_apply
#print axioms clash_apart
#print axioms forced
#print axioms bounded_after
#print axioms admin_renamed
#print axioms copy_comp
#print axioms fresh_map
#print axioms fresh_cons
#print axioms exec_icode
#print axioms exec_apply
#print axioms uncopy_slot
#print axioms store_renamed
#print axioms store_unifiable_renamed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
