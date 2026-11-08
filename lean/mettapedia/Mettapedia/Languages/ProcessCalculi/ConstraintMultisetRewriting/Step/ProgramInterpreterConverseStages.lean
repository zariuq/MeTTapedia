import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterConverseStore

/-!
# The interpreter-join converse: the stage invariant

Every state the interpreter `joinMeta` reaches from a stored program and a call is one of its
stages (`Stage`), for an invertible renaming of the caller (`Reached`):

* **select**: a suffix of the stored program is left to choose from;
* **chosen**: one stored equation is chosen;
* **alloc**: `k` slots are left to allocate, and the allocated variables are distinct and apart from
  the caller's;
* **build**, **read**: the building code of one side runs on a stack; what is left of it, run on the
  stack, builds exactly the copy of that side from the allocated variables (`exec`);
* **store**: both copies are built, and the store's firing is next.

`ProgramInterpreterConverseSteps` shows the invariant is kept by every step, under every most
general unifier. This file defines the stages and proves the step lemmas they share: a forced rule
fires as the matcher followed by a renaming (`single_step`), and the renamings compose on the caller
(`reached_next`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded getD_mem vals_bounded_of_fill)

/-! ## Stages -/

/-- The side being built: the left-hand side first, then the right-hand side. -/
def side (e : ProgramEquations.Equation) : Bool → Pat
  | false => e.lhs
  | true => e.rhs

/-- What follows the build: the right-hand side's code after the left-hand side; the built
left-hand side kept while the right-hand side is built. -/
def cont (e : ProgramEquations.Equation) (env : List Tm) (t' : Tm) : Bool → Tm
  | false => ttup 167 [embed (codeOf (bcode e.rhs)), t']
  | true => ttup 168 [Pat.fill env e.lhs, t']

theorem cont_apply (σ : Subst rows) (e : ProgramEquations.Equation) (env : List Tm) (t' : Tm) :
    ∀ b, σ.applyTerm (cont e env t' b) = cont e (env.map σ.applyTerm) (σ.applyTerm t') b
  | false => by
      rw [cont, cont, ttup_apply, List.map_cons, List.map_cons, List.map_nil, apply_embed]
  | true => by
      rw [cont, cont, ttup_apply, List.map_cons, List.map_cons, List.map_nil, fill_apply]

/-- **The interpreter's stages** for the renamed call `t'` and rows `F'`. -/
inductive Stage (prog : Program) (t' : Tm) (F' : Multiset Tm) : Tm → Prop
  | select (i : ℕ) : Stage prog t' F' (ttup 160 [embed (codeOf ((prog.map eqData).drop i)), t'])
  | chosen (j : Fin prog.length) : Stage prog t' F' (ttup 162 [embed (eqData (prog.get j)), t'])
  | alloc (j : Fin prog.length) (k : ℕ) (env : List Tm) (count : k + env.length = slots (prog.get j))
      (fresh : FreshFor env t' F') :
      Stage prog t' F' (ttup 164 [embed (nat k), tlist env, embed (codeOf (bcode (prog.get j).lhs)),
        embed (codeOf (bcode (prog.get j).rhs)), t'])
  | build (j : Fin prog.length) (b : Bool) (env : List Tm) (C : List Ins) (S : List Tm)
      (len : env.length = slots (prog.get j)) (fresh : FreshFor env t' F')
      (runs : exec env C S = some [Pat.fill env (side (prog.get j) b)]) :
      Stage prog t' F' (ttup 165 [embed (codeOf (C.map Ins.enc)), tlist S, tlist env,
        cont (prog.get j) env t' b])
  | read (j : Fin prog.length) (b : Bool) (env : List Tm) (d : ℕ) (W : List Tm) (C : List Ins)
      (S : List Tm) (len : env.length = slots (prog.get j)) (fresh : FreshFor env t' F')
      (lt : d < W.length)
      (runs : exec env C (W.getD d (.const 0) :: S) = some [Pat.fill env (side (prog.get j) b)]) :
      Stage prog t' F' (ttup 166 [embed (nat d), tlist W, embed (codeOf (C.map Ins.enc)), tlist S,
        tlist env, cont (prog.get j) env t' b])
  | store (j : Fin prog.length) (env : List Tm) (len : env.length = slots (prog.get j))
      (fresh : FreshFor env t' F') :
      Stage prog t' F' (ttup 169 [Pat.fill env (prog.get j).lhs, Pat.fill env (prog.get j).rhs, t'])

/-- **A reached state**: a stage of the interpreter for an invertible renaming `ρ` of the caller,
with every row below the current scope. -/
def Reached (prog : Program) (t : Tm) (F : Multiset Tm) (s : Tm) (F' : Multiset Tm) (m : ℕ) : Prop :=
  ∃ ρ : Subst rows, Copy ρ t F ∧ F' = F.map ρ.applyTerm ∧ Bounded m (ρ.applyTerm t) ∧ Bounded m s ∧
    (∀ f ∈ F', Bounded m f) ∧ Stage prog (ρ.applyTerm t) F' s

/-- Data rows: each is tagged by a constant other than the thread's, so no substitution makes it a
thread. -/
def DataRows (F : Multiset Tm) : Prop := ∀ f ∈ F, ∃ k s, k ≠ 40 ∧ f = tagged k s

theorem DataRows.free {F : Multiset Tm} (data : DataRows F) : ThreadFree F := by
  intro f member s same
  obtain ⟨k, s', ne, rfl⟩ := data f member
  exact ne (tagged_inj.mp same).1

theorem DataRows.map {F : Multiset Tm} (data : DataRows F) (σ : Subst rows) :
    DataRows (F.map σ.applyTerm) := by
  intro g member
  obtain ⟨f, fm, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨k, s, ne, rfl⟩ := data f fm
  exact ⟨k, σ.applyTerm s, ne, apply_tagged σ k s⟩

/-- **A compiled answer and an interpreted answer agree up to renaming, both ways.** -/
def RenamedAnswer (a : Tm) (G : Multiset Tm) (a' : Tm) (G' : Multiset Tm) : Prop :=
  ∃ κ κ' : Subst rows, IsRenaming κ ∧ IsRenaming κ' ∧ a' = κ.applyTerm a ∧ a = κ'.applyTerm a' ∧
    G' = G.map κ.applyTerm ∧ G = G'.map κ'.applyTerm

/-- The interpreted answer `a'` with rows `G'` is a renamed compiled answer to the call. -/
def CompiledAnswer (prog : Program) (t : Tm) (F : Multiset Tm) (n : ℕ) (a' : Tm) (G' : Multiset Tm) : Prop :=
  ∃ a G, EqStep prog (thread t ::ₘ F, n) (thread a ::ₘ G, n + 1) ∧ RenamedAnswer a G a' G'

/-- What a step from a reached state leads to: the next reached state, or a renamed compiled
answer. -/
abbrev Next (prog : Program) (t : Tm) (F : Multiset Tm) (n m : ℕ) (target : Multiset Tm × ℕ) : Prop :=
  (∃ s' F'', target = (thread s' ::ₘ F'', m + 1) ∧ Reached prog t F s' F'' (m + 1)) ∨
    ∃ a' G', target = (thread (ttup 173 [a']) ::ₘ G', m + 1) ∧ DataRows G' ∧
      CompiledAnswer prog t F n a' G'

/-! ## One renamed firing -/

/-- **A renamed firing at a stage**: the rule `e` fires on an instance of its left-hand side, under
any most general unifier; the result is the matcher's under a renaming `κ`. -/
theorem renamed_by {e : ProgramEquations.Equation} {vals : List Tm} {m k : ℕ}
    (rowB : Bounded m (Pat.fill vals e.lhs)) (length : vals.length = k) (covers : ∀ x < k, x ∈ e.lhs.vars)
    (within : ∀ x ∈ e.lhs.vars, x < k) {F : Multiset Tm} (FB : ∀ f ∈ F, Bounded m f) {θ : Subst rows}
    (mgu : IsMGU [(e.lhs.at m, Pat.fill vals e.lhs)] θ) :
    ∃ κ κ' : Subst rows, IsRenaming κ ∧ IsRenaming κ' ∧
      (∀ x : ℕ × ℕ, (x.1 < m ∨ (x.1 = m ∧ k ≤ x.2)) → κ'.applyTerm (κ x) = .var x) ∧
      (∀ u, Bounded m u → Bounded (m + 1) (κ.applyTerm u)) ∧
      Bounded (m + 1) (κ.applyTerm ((matcher m vals).applyTerm (e.rhs.at m))) ∧
      (thread (θ.applyTerm (e.rhs.at m)) ::ₘ F.map θ.applyTerm, m + 1) =
        (thread (κ.applyTerm ((matcher m vals).applyTerm (e.rhs.at m))) ::ₘ F.map κ.applyTerm, m + 1) := by
  subst length
  have bounded := vals_bounded_of_fill rowB covers
  obtain ⟨κ, κ', ren, ren', back, result, below, newB, κB⟩ := admin_renamed bounded covers within mgu
  refine ⟨κ, κ', ren, ren', back, κB, result ▸ newB, ?_⟩
  rw [result, Multiset.map_congr rfl fun f hf => below f (FB f hf)]

/-- **A forced renamed firing**: when only the rule `e` does not clash with the stage. -/
theorem single_step {e : ProgramEquations.Equation} {r : Fin joinMeta.length} (er : joinMeta.get r = e)
    (only : ∀ i : Fin joinMeta.length, Clash (joinMeta.get i).lhs e.lhs = false → i = r)
    {vals : List Tm} {m k : ℕ} (rowB : Bounded m (Pat.fill vals e.lhs)) (length : vals.length = k)
    (covers : ∀ x < k, x ∈ e.lhs.vars) (within : ∀ x ∈ e.lhs.vars, x < k) {F : Multiset Tm}
    (FB : ∀ f ∈ F, Bounded m f) (free : ThreadFree F) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (Pat.fill vals e.lhs) ::ₘ F, m) target) :
    ∃ κ κ' : Subst rows, IsRenaming κ ∧ IsRenaming κ' ∧
      (∀ x : ℕ × ℕ, (x.1 < m ∨ (x.1 = m ∧ k ≤ x.2)) → κ'.applyTerm (κ x) = .var x) ∧
      (∀ u, Bounded m u → Bounded (m + 1) (κ.applyTerm u)) ∧
      Bounded (m + 1) (κ.applyTerm ((matcher m vals).applyTerm (e.rhs.at m))) ∧
      target = (thread (κ.applyTerm ((matcher m vals).applyTerm (e.rhs.at m))) ::ₘ F.map κ.applyTerm, m + 1) := by
  obtain ⟨i, θ, clash, mgu, rfl⟩ := forced free step
  have same := only i clash
  subst same
  rw [er] at mgu ⊢
  exact renamed_by rowB length covers within FB mgu

/-- **The next stage is reached**: the renamings compose on the caller. -/
theorem reached_next {prog : Program} {t : Tm} {F : Multiset Tm} {ρ κ κ' : Subst rows} {m : ℕ}
    (copy : Copy ρ t F) (tB : Bounded m (ρ.applyTerm t)) (FB : ∀ f ∈ F.map ρ.applyTerm, Bounded m f)
    (ren : IsRenaming κ) (back : ∀ x : ℕ × ℕ, x.1 < m → κ'.applyTerm (κ x) = .var x)
    (κB : ∀ u, Bounded m u → Bounded (m + 1) (κ.applyTerm u)) {s' : Tm} (sB : Bounded (m + 1) s')
    (stage : Stage prog (κ.applyTerm (ρ.applyTerm t)) ((F.map ρ.applyTerm).map κ.applyTerm) s') :
    Reached prog t F s' ((F.map ρ.applyTerm).map κ.applyTerm) (m + 1) := by
  have callerQ : ∀ x, CallerVar (ρ.applyTerm t) (F.map ρ.applyTerm) x → x.1 < m := by
    rintro x (hx | ⟨f, member, hx⟩)
    · exact tB x hx
    · exact FB f member x hx
  have rowsEq : (F.map ρ.applyTerm).map κ.applyTerm = F.map (κ ∘ₛ ρ).applyTerm := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun f _ => (Subst.applyTerm_comp κ ρ f).symm
  refine ⟨κ ∘ₛ ρ, copy_comp copy ren callerQ back, rowsEq, ?_, sB, ?_, ?_⟩
  · rw [Subst.applyTerm_comp]
    exact κB _ tB
  · intro g member
    obtain ⟨f, fm, rfl⟩ := Multiset.mem_map.mp member
    exact κB f (FB f fm)
  · rw [Subst.applyTerm_comp]
    exact stage

theorem fresh_next {env : List Tm} {t' : Tm} {F' : Multiset Tm} (fresh : FreshFor env t' F') {m : ℕ}
    (envB : ∀ w ∈ env, Bounded m w) (tB : Bounded m t') (FB : ∀ f ∈ F', Bounded m f)
    {κ κ' : Subst rows} (ren : IsRenaming κ) (back : ∀ x : ℕ × ℕ, x.1 < m → κ'.applyTerm (κ x) = .var x) :
    FreshFor (env.map κ.applyTerm) (κ.applyTerm t') (F'.map κ.applyTerm) :=
  fresh_map fresh ren (Q := fun x => x.1 < m) (fun w hw x hx => envB w hw x hx)
    (by
      rintro x (hx | ⟨f, member, hx⟩)
      · exact tB x hx
      · exact FB f member x hx) back

theorem runs_next {env : List Tm} {C : List Ins} {S : List Tm} {p : Pat} (σ : Subst rows)
    (runs : exec env C S = some [Pat.fill env p]) :
    exec (env.map σ.applyTerm) C (S.map σ.applyTerm) = some [Pat.fill (env.map σ.applyTerm) p] := by
  have := exec_apply σ env C S _ runs
  rw [List.map_cons, List.map_nil, fill_apply] at this
  exact this

theorem runs_start {env : List Tm} {p : Pat} (within : ∀ x ∈ p.vars, x < env.length) :
    exec env (icode p) [] = some [Pat.fill env p] := by
  have := exec_icode env p within [] []
  rw [List.append_nil] at this
  rw [this]
  rfl

theorem within_side (e : ProgramEquations.Equation) (b : Bool) {env : List Tm} (len : env.length = slots e) :
    ∀ x ∈ (side e b).vars, x < env.length := by
  intro x hx
  rw [len]
  cases b
  · exact lt_slots (List.mem_append_left _ hx)
  · exact lt_slots (List.mem_append_right _ hx)

theorem ttup_ne {k k' : ℕ} {l l' : List Tm} (ne : k ≠ k') : ttup k l ≠ ttup k' l' := by
  intro same
  rw [ttup, ttup, node_inj] at same
  exact ne (Term.const.inj same.1)

theorem stage_not_answer {prog : Program} {t' : Tm} {F' : Multiset Tm} {s : Tm} (stage : Stage prog t' F' s)
    (a : Tm) : s ≠ ttup 173 [a] := by
  cases stage <;> exact ttup_ne (by decide)

#print axioms cont_apply
#print axioms DataRows.free
#print axioms DataRows.map
#print axioms renamed_by
#print axioms single_step
#print axioms reached_next
#print axioms fresh_next
#print axioms runs_next
#print axioms runs_start
#print axioms stage_not_answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
