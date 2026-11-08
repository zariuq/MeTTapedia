import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterJoinRuns

/-!
# The two-way interpreter join, up to renaming

For a call with variables, one firing of the compiled equation answers by a most general unifier
of the call with the left-hand side renamed into the firing's scope
(`ProgramEquations.EqStep`). The interpreter `joinMeta` reaches the same answer by administrative
firings that choose the equation, allocate one fresh variable per slot and build the renamed copy,
followed by one firing in which the store unifies the copy with the call
(`ProgramInterpreterJoinRuns`).

* **Eder's lemma on a set of variables** (`renaming_on`): substitutions each more general than the
  other on the variables that matter differ there by a renaming.
* **The last firing answers the compiled answer up to renaming** (`store_answer_renames`): for
  every most general unifier of the interpreter's last firing, its answer and the other rows are
  the images of the compiled answer and rows under one renaming.
* **The join** (`interpreter_join`, `interpreter_answers`): for every compiled answer to a call
  with variables, the interpreter, a fixed family of thirteen schemas, has a run whose
  administrative firings allocate the fresh variables, and whose answer, under any most general
  unifier, is a renaming of the compiled one; the other rows are renamed by the same renaming.

No range restriction is needed: the interpreter allocates a slot for every variable of the
equation, those of the right-hand side alone included, so `(= g $y)` (which the matching
interpreter of `ProgramCompiledInterpreter` cannot answer) is answered here, by a fresh variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded getD_mem)

/-! ## Eder's lemma on a set of variables -/

/-- A variable of the range of `θ` on `V`. -/
def RangeOn (V : ℕ × ℕ → Prop) (θ : Subst rows) (x : ℕ × ℕ) : Prop := ∃ v, V v ∧ x ∈ (θ v).freeVars

open Classical in
noncomputable def restrictOn (V : ℕ × ℕ → Prop) (θ α : Subst rows) : Subst rows := fun x =>
  if RangeOn V θ x then α x else .var x

/-- **Substitutions each more general than the other on `V` differ there by a renaming.** -/
theorem renaming_on {V : ℕ × ℕ → Prop} {θ₁ θ₂ α β : Subst rows}
    (h₁ : ∀ v, V v → θ₂ v = α.applyTerm (θ₁ v)) (h₂ : ∀ v, V v → θ₁ v = β.applyTerm (θ₂ v)) :
    ∃ κ κ' : Subst rows, IsRenaming κ ∧ IsRenaming κ' ∧
      (∀ v, V v → θ₂ v = κ.applyTerm (θ₁ v)) ∧ (∀ v, V v → θ₁ v = κ'.applyTerm (θ₂ v)) ∧
      (∀ x, RangeOn V θ₁ x → κ'.applyTerm (κ x) = .var x) ∧
      (∀ x, RangeOn V θ₂ x → κ.applyTerm (κ' x) = .var x) := by
  have back : ∀ {θa θb αa βa : Subst rows}, (∀ v, V v → θb v = αa.applyTerm (θa v)) →
      (∀ v, V v → θa v = βa.applyTerm (θb v)) → ∀ x, RangeOn V θa x → βa.applyTerm (αa x) = .var x := by
    intro θa θb αa βa ha hb x ⟨v, hv, hx⟩
    have fixed : (βa ∘ₛ αa).applyTerm (θa v) = θa v := by
      rw [Subst.applyTerm_comp, ← ha v hv, ← hb v hv]
    exact Subst.var_fixed_of_applyTerm_eq_self fixed x hx
  have toRange : ∀ {θa θb αa βa : Subst rows}, (∀ v, V v → θb v = αa.applyTerm (θa v)) →
      (∀ v, V v → θa v = βa.applyTerm (θb v)) → ∀ x, RangeOn V θa x →
        ∃ y, αa x = .var y ∧ RangeOn V θb y := by
    intro θa θb αa βa ha hb x ⟨v, hv, hx⟩
    obtain ⟨y, hy⟩ := var_of_apply_eq_var (back ha hb x ⟨v, hv, hx⟩)
    refine ⟨y, hy, v, hv, ?_⟩
    rw [ha v hv]
    exact (Subst.mem_freeVars_applyTerm (σ := rows)).mpr
      ⟨x, hx, by rw [hy]; exact (Term.mem_freeVars_var (σ := rows)).mpr rfl⟩
  have isRen : ∀ {θa θb αa βa : Subst rows}, (∀ v, V v → θb v = αa.applyTerm (θa v)) →
      (∀ v, V v → θa v = βa.applyTerm (θb v)) → IsRenaming (restrictOn V θa αa) := by
    intro θa θb αa βa ha hb x
    unfold restrictOn
    split_ifs with h
    · obtain ⟨y, hy, -⟩ := toRange ha hb x h
      exact ⟨y, hy⟩
    · exact ⟨x, rfl⟩
  have factor : ∀ {θa θb αa : Subst rows}, (∀ v, V v → θb v = αa.applyTerm (θa v)) →
      ∀ v, V v → θb v = (restrictOn V θa αa).applyTerm (θa v) := by
    intro θa θb αa ha v hv
    rw [ha v hv]
    refine Subst.applyTerm_congr fun x hx => ?_
    unfold restrictOn
    rw [if_pos ⟨v, hv, hx⟩]
  have inverse : ∀ {θa θb αa βa : Subst rows}, (∀ v, V v → θb v = αa.applyTerm (θa v)) →
      (∀ v, V v → θa v = βa.applyTerm (θb v)) → ∀ x, RangeOn V θa x →
        (restrictOn V θb βa).applyTerm (restrictOn V θa αa x) = .var x := by
    intro θa θb αa βa ha hb x hx
    obtain ⟨y, hy, hy'⟩ := toRange ha hb x hx
    have step : restrictOn V θa αa x = .var y := by
      unfold restrictOn
      rw [if_pos hx, hy]
    rw [step, Subst.applyTerm_var]
    unfold restrictOn
    rw [if_pos hy', show βa y = βa.applyTerm (αa x) by rw [hy]; rfl]
    exact back ha hb x hx
  exact ⟨restrictOn V θ₁ α, restrictOn V θ₂ β, isRen h₁ h₂, isRen h₂ h₁, factor h₁, factor h₂,
    inverse h₁ h₂, inverse h₂ h₁⟩

theorem vars_of_at {n : ℕ} : ∀ (p : Pat) {v : ℕ × ℕ}, v ∈ (p.at n).freeVars → v.2 ∈ p.vars
  | .var x, v, hv => by
      rw [Pat.at, Term.mem_freeVars_var (σ := rows)] at hv
      subst hv
      simp [Pat.vars]
  | .sym _, _, hv => by simp [Pat.at, Term.freeVars] at hv
  | .cell a b, v, hv => by
      rcases mem_freeVars_node.mp hv with hv | hv
      · exact List.mem_append_left _ (vars_of_at a hv)
      · exact List.mem_append_right _ (vars_of_at b hv)

/-! ## Undoing the allocation -/

theorem lt_slots {e : ProgramEquations.Equation} {x : ℕ} (h : x ∈ e.lhs.vars ++ e.rhs.vars) :
    x < slots e := by
  unfold slots
  generalize e.lhs.vars ++ e.rhs.vars = l at h
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a l ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp only [List.sum_cons]
        omega
      · have := ih h
        simp only [List.sum_cons]
        omega

theorem freshVars_getD (n₀ : ℕ) : ∀ (k x : ℕ), x < k →
    (freshVars n₀ k).getD x (.const 0) = .var (n₀ + (k - 1 - x), 5)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, 0, _ => by
      show (Term.var (n₀ + k, 5) : Tm) = _
      rw [show n₀ + (k + 1 - 1 - 0) = n₀ + k by omega]
  | k + 1, x + 1, h => by
      show (freshVars n₀ k).getD x (.const 0) = _
      rw [freshVars_getD n₀ k x (by omega), show n₀ + (k + 1 - 1 - (x + 1)) = n₀ + (k - 1 - x) by omega]

open Classical in
/-- Send each allocated variable back to the slot it was allocated for, at scope `n`. -/
noncomputable def unfresh (n n₀ k : ℕ) : Subst rows := fun w =>
  if w.2 = 5 ∧ n₀ ≤ w.1 ∧ w.1 < n₀ + k then .var (n, n₀ + k - 1 - w.1) else .var w

theorem unfresh_slot {n n₀ k x : ℕ} (lt : x < k) :
    unfresh n n₀ k (n₀ + (k - 1 - x), 5) = .var (n, x) := by
  rw [unfresh, if_pos ⟨rfl, Nat.le_add_right _ _, show n₀ + (k - 1 - x) < n₀ + k by omega⟩]
  show (Term.var (n, n₀ + k - 1 - (n₀ + (k - 1 - x))) : Tm) = _
  rw [show n₀ + k - 1 - (n₀ + (k - 1 - x)) = x by omega]

theorem unfresh_below {n n₀ k : ℕ} {w : ℕ × ℕ} (lt : w.1 < n₀) : unfresh n n₀ k w = .var w := by
  rw [unfresh, if_neg fun h => absurd h.2.1 (by omega)]

theorem copy_undone {n n₀ k : ℕ} : ∀ (p : Pat), (∀ x ∈ p.vars, x < k) →
    (unfresh n n₀ k).applyTerm ((matcher n (freshVars n₀ k)).applyTerm (p.at n)) = p.at n := by
  intro p within
  rw [← Subst.applyTerm_comp]
  refine Subst.applyTerm_eq_self fun v hv => ?_
  have scope := at_scope n p v hv
  have name := vars_of_at p hv
  have lt := within v.2 name
  have hv' : v = (n, v.2) := Prod.ext scope rfl
  change (unfresh n n₀ k).applyTerm (matcher n (freshVars n₀ k) v) = .var v
  rw [matcher, if_pos ⟨scope, by rw [freshVars_length]; exact lt⟩, freshVars_getD n₀ k v.2 lt,
    Subst.applyTerm_var, unfresh_slot lt, ← hv']

/-! ## The last firing -/

theorem ttup_forced {σ : Subst rows} {k : ℕ} {a b c a' b' c' : Tm}
    (same : σ.applyTerm (ttup k [a, b, c]) = σ.applyTerm (ttup k [a', b', c'])) :
    σ.applyTerm a = σ.applyTerm a' ∧ σ.applyTerm b = σ.applyTerm b' ∧ σ.applyTerm c = σ.applyTerm c' := by
  simp only [ttup, tseq, apply_node, node_inj] at same
  exact ⟨same.2.1, same.2.2.1, same.2.2.2.1⟩

/-- **For every most general unifier of the store's firing, the answer and the other rows are the
compiled ones under one renaming.** -/
theorem store_answer_renames {e : ProgramEquations.Equation} {t : Tm} {F : Multiset Tm} {n n₀ m : ℕ}
    (tB : Bounded n t) (FB : ∀ f ∈ F, Bounded n f) (below : n ≤ n₀) (above : n₀ + slots e ≤ m)
    {θc : Subst rows} (mgu : IsMGU [(e.lhs.at n, t)] θc) {θ' : Subst rows}
    (mgu' : IsMGU [(jApply.lhs.at m, ttup 169 [Pat.fill (freshVars n₀ (slots e)) e.lhs,
      Pat.fill (freshVars n₀ (slots e)) e.rhs, t])] θ') :
    ∃ κ : Subst rows, IsRenaming κ ∧ θ' (m, 1) = κ.applyTerm (θc.applyTerm (e.rhs.at n)) ∧
      ∀ f ∈ F, θ'.applyTerm f = κ.applyTerm (θc.applyTerm f) := by
  have envLength : (freshVars n₀ (slots e)).length = slots e := freshVars_length n₀ _
  have withinL : ∀ x ∈ e.lhs.vars, x < (freshVars n₀ (slots e)).length := fun x hx =>
    by rw [envLength]; exact lt_slots (List.mem_append_left _ hx)
  have withinR : ∀ x ∈ e.rhs.vars, x < (freshVars n₀ (slots e)).length := fun x hx =>
    by rw [envLength]; exact lt_slots (List.mem_append_right _ hx)
  have ρL : (matcher n (freshVars n₀ (slots e))).applyTerm (e.lhs.at n) =
      Pat.fill (freshVars n₀ (slots e)) e.lhs := matcher_at _ withinL
  have ρR : (matcher n (freshVars n₀ (slots e))).applyTerm (e.rhs.at n) =
      Pat.fill (freshVars n₀ (slots e)) e.rhs := matcher_at _ withinR
  have ρt : (matcher n (freshVars n₀ (slots e))).applyTerm t = t := matcher_fixes tB
  -- the store's unifier
  have parts : θ'.applyTerm (.var (m, 0)) = θ'.applyTerm (Pat.fill (freshVars n₀ (slots e)) e.lhs) ∧
      θ'.applyTerm (.var (m, 1)) = θ'.applyTerm (Pat.fill (freshVars n₀ (slots e)) e.rhs) ∧
      θ'.applyTerm (.var (m, 0)) = θ'.applyTerm t :=
    ttup_forced (k := 169) (mgu'.unifies _ List.mem_cons_self)
  obtain ⟨atL, atR, atT⟩ := parts
  rw [Subst.applyTerm_var] at atL atR atT
  -- the compiled unifier is more general than the store's, read through the copy
  have unifies₂ : Unifies (θ' ∘ₛ matcher n (freshVars n₀ (slots e))) [(e.lhs.at n, t)] := by
    rw [unifies_single, Subst.applyTerm_comp, Subst.applyTerm_comp, ρL, ρt, ← atL, atT]
  obtain ⟨α, hα⟩ := mgu.general _ unifies₂
  -- and the store's is more general than the compiled one, on the variables that matter
  let δ : Subst rows := fun w =>
    if w = (m, 0) then θc.applyTerm t else if w = (m, 1) then θc.applyTerm (e.rhs.at n)
      else θc.applyTerm (unfresh n n₀ (slots e) w)
  have copyBounded : Bounded (n₀ + slots e) (Pat.fill (freshVars n₀ (slots e)) e.lhs) ∧
      Bounded (n₀ + slots e) (Pat.fill (freshVars n₀ (slots e)) e.rhs) :=
    ⟨fill_bounded (freshVars_bounded n₀ _) _, fill_bounded (freshVars_bounded n₀ _) _⟩
  have δcopy : ∀ u : Tm, (∀ w ∈ u.freeVars, w.1 < m) →
      δ.applyTerm u = θc.applyTerm ((unfresh n n₀ (slots e)).applyTerm u) := by
    intro u hu
    rw [← Subst.applyTerm_comp]
    refine Subst.applyTerm_congr fun w hw => ?_
    have lt := hu w hw
    have ne₀ : w ≠ (m, 0) := fun h => by rw [h] at lt; exact lt_irrefl m lt
    have ne₁ : w ≠ (m, 1) := fun h => by rw [h] at lt; exact lt_irrefl m lt
    simp only [δ, if_neg ne₀, if_neg ne₁]
    rfl
  have tBelow : ∀ w ∈ t.freeVars, w.1 < m := fun w hw => by
    have := tB w hw
    omega
  have unfreshT : (unfresh n n₀ (slots e)).applyTerm t = t :=
    Subst.applyTerm_eq_self fun w hw => unfresh_below (lt_of_lt_of_le (tB w hw) below)
  have undoneL : (unfresh n n₀ (slots e)).applyTerm (Pat.fill (freshVars n₀ (slots e)) e.lhs) =
      e.lhs.at n := by
    rw [← ρL]
    exact copy_undone _ fun x hx => envLength ▸ withinL x hx
  have undoneR : (unfresh n n₀ (slots e)).applyTerm (Pat.fill (freshVars n₀ (slots e)) e.rhs) =
      e.rhs.at n := by
    rw [← ρR]
    exact copy_undone _ fun x hx => envLength ▸ withinR x hx
  have unifiesδ : Unifies δ [(jApply.lhs.at m, ttup 169 [Pat.fill (freshVars n₀ (slots e)) e.lhs,
      Pat.fill (freshVars n₀ (slots e)) e.rhs, t])] := by
    rw [unifies_single,
      show (jApply.lhs.at m) = ttup 169 [.var (m, 0), .var (m, 1), .var (m, 0)] from rfl]
    have v0 : δ (m, 0) = θc.applyTerm t := by simp [δ]
    have v1 : δ (m, 1) = θc.applyTerm (e.rhs.at n) := by simp [δ]
    have dL : δ.applyTerm (Pat.fill (freshVars n₀ (slots e)) e.lhs) = θc.applyTerm (e.lhs.at n) := by
      rw [δcopy _ fun w hw => lt_of_lt_of_le (copyBounded.1 w hw) above, undoneL]
    have dR : δ.applyTerm (Pat.fill (freshVars n₀ (slots e)) e.rhs) = θc.applyTerm (e.rhs.at n) := by
      rw [δcopy _ fun w hw => lt_of_lt_of_le (copyBounded.2 w hw) above, undoneR]
    have dt : δ.applyTerm t = θc.applyTerm t := by rw [δcopy t tBelow, unfreshT]
    have compiled : θc.applyTerm (e.lhs.at n) = θc.applyTerm t := (unifies_single θc _ _).mp mgu.unifies
    simp only [ttup, tseq, apply_node, Subst.applyTerm_var, Subst.applyTerm_const, v0, v1, dL, dR, dt,
      compiled]
  obtain ⟨β, hβ⟩ := mgu'.general δ unifiesδ
  -- the variables that matter: the equation's at scope `n`, and the earlier ones
  have h₁ : ∀ v, ((v.1 = n ∧ v.2 < slots e) ∨ v.1 < n) →
      (θ' ∘ₛ matcher n (freshVars n₀ (slots e))) v = α.applyTerm (θc v) := fun v _ => hα v
  have h₂ : ∀ v, ((v.1 = n ∧ v.2 < slots e) ∨ v.1 < n) →
      θc v = β.applyTerm ((θ' ∘ₛ matcher n (freshVars n₀ (slots e))) v) := by
    intro v hv
    rcases hv with ⟨scope, lt⟩ | lt
    · have hv' : v = (n, v.2) := Prod.ext scope rfl
      have slot : matcher n (freshVars n₀ (slots e)) v = .var (n₀ + (slots e - 1 - v.2), 5) := by
        rw [hv']
        show matcher n (freshVars n₀ (slots e)) (n, v.2) = _
        rw [matcher, if_pos ⟨rfl, by rw [envLength]; exact lt⟩, freshVars_getD n₀ _ v.2 lt]
      change θc v = β.applyTerm (θ'.applyTerm (matcher n (freshVars n₀ (slots e)) v))
      rw [slot, Subst.applyTerm_var, ← hβ]
      have ne₀ : ((n₀ + (slots e - 1 - v.2), 5) : ℕ × ℕ) ≠ (m, 0) := fun h => by
        have h₁ : n₀ + (slots e - 1 - v.2) = m := congrArg Prod.fst h
        omega
      have ne₁ : ((n₀ + (slots e - 1 - v.2), 5) : ℕ × ℕ) ≠ (m, 1) := fun h => by
        have h₁ : n₀ + (slots e - 1 - v.2) = m := congrArg Prod.fst h
        omega
      simp only [δ, if_neg ne₀, if_neg ne₁]
      rw [unfresh_slot lt, Subst.applyTerm_var, ← hv']
    · have fixed : matcher n (freshVars n₀ (slots e)) v = .var v := by
        rw [matcher, if_neg fun h => by omega]
      change θc v = β.applyTerm (θ'.applyTerm (matcher n (freshVars n₀ (slots e)) v))
      rw [fixed, Subst.applyTerm_var, ← hβ]
      have ne₀ : v ≠ (m, 0) := fun h => by
        have h₁ : v.1 = m := congrArg Prod.fst h
        omega
      have ne₁ : v ≠ (m, 1) := fun h => by
        have h₁ : v.1 = m := congrArg Prod.fst h
        omega
      simp only [δ, if_neg ne₀, if_neg ne₁]
      rw [unfresh_below (by omega), Subst.applyTerm_var]
  obtain ⟨κ, -, ren, -, there, -, -, -⟩ := renaming_on h₁ h₂
  have onV : ∀ u : Tm, (∀ v ∈ u.freeVars, (v.1 = n ∧ v.2 < slots e) ∨ v.1 < n) →
      θ'.applyTerm ((matcher n (freshVars n₀ (slots e))).applyTerm u) = κ.applyTerm (θc.applyTerm u) := by
    intro u hu
    rw [← Subst.applyTerm_comp, ← Subst.applyTerm_comp]
    exact Subst.applyTerm_congr fun v hv => there v (hu v hv)
  refine ⟨κ, ren, ?_, fun f member => ?_⟩
  · rw [atR, ← ρR]
    refine onV _ fun v hv => .inl ⟨at_scope n _ v hv, ?_⟩
    exact by rw [← envLength]; exact withinR v.2 (vars_of_at _ hv)
  · rw [← onV f fun v hv => .inr (FB f member v hv), matcher_fixes (FB f member)]

#print axioms renaming_on
#print axioms freshVars_getD
#print axioms unfresh_slot
#print axioms copy_undone
#print axioms store_answer_renames

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
