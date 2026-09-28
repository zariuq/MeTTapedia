import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Program

/-!
# The norm of values and the overhead of patterns

The norm measures a value for the descent of deterministic equations: an atom
is 1; a cell `(LCons h t)` is `1 + |h| + |t|`; a value view `(W x)`, `W` one
of the constructors of `langdef:value-view`, is `|x|`; any other expression or
list value of `n` elements is `1 + n` plus the norms of its elements.  So the
norm-keeping primitives of the host (an expression and its list of elements,
a list value and its list, a value and its view) keep it, and every value has
norm at least 1 (`one_le_norm`).

A pattern is *headed* when a symbol heads each of its expressions.  Such a
pattern fixes the kind of every value it matches, so the norm of a matched
value is the pattern's *overhead*, its norm with variables counted 0, plus the
norms of the values of its variables (`norm_of_matchTerm`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-- The constructors of `langdef:value-view`. -/
def viewHeads : List String :=
  ["LangDef:ExpressionValue", "LangDef:ListValue", "LangDef:SymbolValue",
   "LangDef:StringValue", "LangDef:IntegerValue", "LangDef:FloatValue"]

/-- A value view constructor. -/
def isView (s : String) : Bool := viewHeads.contains s

mutual

/-- The norm of a term. -/
def norm : Term → Nat
  | .sym _ => 1
  | .lit _ => 1
  | .var _ => 1
  | .expr items => normItems items
  | .list items => 1 + items.length + normList items
termination_by t => (sizeOf t, 1)

/-- The norm of an expression of the given elements. -/
def normItems (items : List Term) : Nat :=
  match hi : items with
  | [.sym s, h, t] =>
    if s = "LCons" then 1 + norm h + norm t
    else 1 + 3 + (1 + (norm h + (norm t + 0)))
  | [.sym s, x] => if isView s then norm x else 1 + 2 + (1 + (norm x + 0))
  | _ => 1 + items.length + normList items
termination_by (sizeOf items, 2)
decreasing_by all_goals (subst hi; simp_wf; omega)

/-- The sum of the norms of a list of terms. -/
def normList : List Term → Nat
  | [] => 0
  | t :: ts => norm t + normList ts
termination_by ts => (sizeOf ts, 0)

end

mutual

/-- The norm of a pattern with its variables counted 0. -/
def overhead : Term → Nat
  | .sym _ => 1
  | .lit _ => 1
  | .var _ => 0
  | .expr items => overheadItems items
  | .list items => 1 + items.length + overheadList items
termination_by t => (sizeOf t, 1)

/-- The overhead of an expression pattern of the given elements. -/
def overheadItems (items : List Term) : Nat :=
  match hi : items with
  | [.sym s, h, t] =>
    if s = "LCons" then 1 + overhead h + overhead t
    else 1 + 3 + (1 + (overhead h + (overhead t + 0)))
  | [.sym s, x] => if isView s then overhead x else 1 + 2 + (1 + (overhead x + 0))
  | _ => 1 + items.length + overheadList items
termination_by (sizeOf items, 2)
decreasing_by all_goals (subst hi; simp_wf; omega)

/-- The sum of the overheads of a list of patterns. -/
def overheadList : List Term → Nat
  | [] => 0
  | t :: ts => overhead t + overheadList ts
termination_by ts => (sizeOf ts, 0)

end

mutual

/-- A symbol heads each expression of the pattern. -/
def headed : Term → Bool
  | .sym _ => true
  | .lit _ => true
  | .var _ => true
  | .expr [] => true
  | .expr (.sym _ :: rest) => headedList rest
  | .expr (_ :: _) => false
  | .list items => headedList items

/-- Each pattern of a list is headed. -/
def headedList : List Term → Bool
  | [] => true
  | t :: ts => headed t && headedList ts

end

/-- The sum of the norms of the values an environment binds, one per
binding. -/
def envNorm (σ : Env) : Nat := (σ.map (fun b => norm b.2)).sum

theorem envNorm_append (σ₁ σ₂ : Env) : envNorm (σ₁ ++ σ₂) = envNorm σ₁ + envNorm σ₂ := by
  simp [envNorm, List.map_append, List.sum_append]


theorem norm_sym (s : String) : norm (.sym s) = 1 := by rw [norm]
theorem norm_lit (s : String) : norm (.lit s) = 1 := by rw [norm]
theorem norm_var (s : String) : norm (.var s) = 1 := by rw [norm]
theorem norm_expr (items : List Term) : norm (.expr items) = normItems items := by rw [norm]
theorem norm_list (items : List Term) :
    norm (.list items) = 1 + items.length + normList items := by rw [norm]

/-- An expression's norm is at least 1 when its elements' norms are. -/
theorem one_le_normItems (items : List Term) (h : ∀ x ∈ items, 1 ≤ norm x) :
    1 ≤ normItems items := by
  unfold normItems
  split
  · split <;> omega
  · rename_i s x
    split
    · exact h x (by simp)
    · omega
  · omega

/-- Every value has norm at least 1. -/
theorem one_le_norm : ∀ t : Term, 1 ≤ norm t
  | .sym _ => by simp [norm_sym]
  | .lit _ => by simp [norm_lit]
  | .var _ => by simp [norm_var]
  | .list items => by rw [norm_list]; omega
  | .expr items => by
    rw [norm_expr]
    exact one_le_normItems items (fun x _ => one_le_norm x)
termination_by t => sizeOf t
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹x ∈ items›
  omega

/-! ## Matching inverted -/

theorem matchTerm_var {x : String} {v : Term} {σ : Env}
    (h : matchTerm (.var x) v = some σ) : σ = [(x, v)] := by
  rw [matchTerm] at h
  exact (Option.some.inj h).symm

theorem matchTerm_sym {a : String} {v : Term} {σ : Env}
    (h : matchTerm (.sym a) v = some σ) : v = .sym a ∧ σ = [] := by
  cases v <;> simp [matchTerm] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem matchTerm_lit {a : String} {v : Term} {σ : Env}
    (h : matchTerm (.lit a) v = some σ) : v = .lit a ∧ σ = [] := by
  cases v <;> simp [matchTerm] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

theorem matchTerm_expr {ps : List Term} {v : Term} {σ : Env}
    (h : matchTerm (.expr ps) v = some σ) :
    ∃ vs, v = .expr vs ∧ matchTerms ps vs = some σ := by
  cases v <;> simp [matchTerm] at h
  exact ⟨_, rfl, h⟩

theorem matchTerm_list {ps : List Term} {v : Term} {σ : Env}
    (h : matchTerm (.list ps) v = some σ) :
    ∃ vs, v = .list vs ∧ matchTerms ps vs = some σ := by
  cases v <;> simp [matchTerm] at h
  exact ⟨_, rfl, h⟩

theorem matchTerms_nil {vs : List Term} {σ : Env}
    (h : matchTerms [] vs = some σ) : vs = [] ∧ σ = [] := by
  cases vs <;> simp [matchTerms] at h
  exact ⟨rfl, h⟩

theorem matchTerms_cons {p : Term} {ps vs : List Term} {σ : Env}
    (h : matchTerms (p :: ps) vs = some σ) :
    ∃ v vs' σ₁ σ₂, vs = v :: vs' ∧ matchTerm p v = some σ₁ ∧
      matchTerms ps vs' = some σ₂ ∧ σ = σ₁ ++ σ₂ := by
  cases vs with
  | nil => simp [matchTerms] at h
  | cons v vs' =>
    simp only [matchTerms] at h
    split at h
    · rename_i σ₁ σ₂ h₁ h₂
      exact ⟨v, vs', σ₁, σ₂, rfl, h₁, h₂, (Option.some.inj h).symm⟩
    · simp at h

theorem matchTerms_length {ps vs : List Term} {σ : Env}
    (h : matchTerms ps vs = some σ) : ps.length = vs.length := by
  induction ps generalizing vs σ with
  | nil => rw [(matchTerms_nil h).1]
  | cons p ps ih =>
    obtain ⟨v, vs', σ₁, σ₂, rfl, _, h₂, _⟩ := matchTerms_cons h
    simp [ih h₂]

/-! ## The shapes of expressions -/

theorem overhead_sym (s : String) : overhead (.sym s) = 1 := by rw [overhead]
theorem overhead_lit (s : String) : overhead (.lit s) = 1 := by rw [overhead]
theorem overhead_var (s : String) : overhead (.var s) = 0 := by rw [overhead]
theorem overhead_expr (items : List Term) :
    overhead (.expr items) = overheadItems items := by rw [overhead]
theorem overhead_list (items : List Term) :
    overhead (.list items) = 1 + items.length + overheadList items := by rw [overhead]

theorem normList_nil : normList [] = 0 := by rw [normList]
theorem normList_cons (t : Term) (ts : List Term) :
    normList (t :: ts) = norm t + normList ts := by rw [normList]
theorem overheadList_nil : overheadList [] = 0 := by rw [overheadList]
theorem overheadList_cons (t : Term) (ts : List Term) :
    overheadList (t :: ts) = overhead t + overheadList ts := by rw [overheadList]

theorem normItems_three (s : String) (h t : Term) :
    normItems [.sym s, h, t] =
      if s = "LCons" then 1 + norm h + norm t
      else 1 + 3 + (1 + (norm h + (norm t + 0))) := by
  rw [normItems]

theorem normItems_two (s : String) (x : Term) :
    normItems [.sym s, x] =
      if isView s then norm x else 1 + 2 + (1 + (norm x + 0)) := by
  rw [normItems]

theorem overheadItems_three (s : String) (h t : Term) :
    overheadItems [.sym s, h, t] =
      if s = "LCons" then 1 + overhead h + overhead t
      else 1 + 3 + (1 + (overhead h + (overhead t + 0))) := by
  rw [overheadItems]

theorem overheadItems_two (s : String) (x : Term) :
    overheadItems [.sym s, x] =
      if isView s then overhead x else 1 + 2 + (1 + (overhead x + 0)) := by
  rw [overheadItems]

/-- An expression that is neither a cell nor a view is measured by its
elements. -/
theorem normItems_other (items : List Term)
    (h3 : ∀ s h t, items ≠ [.sym s, h, t]) (h2 : ∀ s x, items ≠ [.sym s, x]) :
    normItems items = 1 + items.length + normList items := by
  unfold normItems
  split
  · rename_i s h t
    exact absurd rfl (h3 s h t)
  · rename_i s x
    exact absurd rfl (h2 s x)
  · rfl

theorem overheadItems_other (items : List Term)
    (h3 : ∀ s h t, items ≠ [.sym s, h, t]) (h2 : ∀ s x, items ≠ [.sym s, x]) :
    overheadItems items = 1 + items.length + overheadList items := by
  unfold overheadItems
  split
  · rename_i s h t
    exact absurd rfl (h3 s h t)
  · rename_i s x
    exact absurd rfl (h2 s x)
  · rfl

/-! ## Norms of matched values -/

mutual

/-- The norm of a value a headed pattern matches is the pattern's overhead
plus the norms of the values of its variables. -/
theorem norm_of_matchTerm : ∀ (p v : Term) (σ : Env),
    headed p = true → matchTerm p v = some σ → norm v = overhead p + envNorm σ
  | .var x, v, σ, _, h => by
    rw [matchTerm_var h, overhead_var]
    simp only [envNorm, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.zero_add]
  | .sym a, v, σ, _, h => by
    obtain ⟨rfl, rfl⟩ := matchTerm_sym h
    simp only [norm_sym, overhead_sym, envNorm, List.map_nil, List.sum_nil, Nat.add_zero]
  | .lit a, v, σ, _, h => by
    obtain ⟨rfl, rfl⟩ := matchTerm_lit h
    simp only [norm_lit, overhead_lit, envNorm, List.map_nil, List.sum_nil, Nat.add_zero]
  | .expr ps, v, σ, hp, h => by
    obtain ⟨vs, rfl, hm⟩ := matchTerm_expr h
    rw [norm_expr, overhead_expr]
    exact normItems_of_matchTerms ps vs σ hp hm
  | .list ps, v, σ, hp, h => by
    obtain ⟨vs, rfl, hm⟩ := matchTerm_list h
    have hps : headedList ps = true := by simpa only [headed] using hp
    rw [norm_list, overhead_list, normList_of_matchTerms ps vs σ hps hm,
      matchTerms_length hm]
    omega

/-- The same for the elements of an expression, whatever its shape. -/
theorem normItems_of_matchTerms : ∀ (ps vs : List Term) (σ : Env),
    headed (.expr ps) = true → matchTerms ps vs = some σ →
      normItems vs = overheadItems ps + envNorm σ
  | [], vs, σ, _, h => by
    obtain ⟨rfl, rfl⟩ := matchTerms_nil h
    rw [normItems_other [] (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h),
      overheadItems_other [] (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)]
    simp only [List.length_nil, Nat.add_zero, normList_nil, overheadList_nil, envNorm,
      List.map_nil, List.sum_nil]
  | .sym s :: rest, vs, σ, hp, h => by
    obtain ⟨v0, vrest, σ0, σr, rfl, h0, hr, rfl⟩ := matchTerms_cons h
    obtain ⟨rfl, rfl⟩ := matchTerm_sym h0
    have hrest : headedList rest = true := by simpa only [headed] using hp
    have hl := matchTerms_length hr
    have hlist := normList_of_matchTerms rest vrest σr hrest hr
    simp only [List.nil_append]
    match rest, vrest, hl, hlist with
    | [], [], _, hlist =>
      rw [normItems_other [.sym s] (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h),
        overheadItems_other [.sym s] (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)]
      simp only [normList_cons, normList_nil, overheadList_cons, overheadList_nil,
        norm_sym, overhead_sym, List.length_cons, List.length_nil] at hlist ⊢
      omega
    | [ph], [vh], _, hlist =>
      rw [normItems_two, overheadItems_two]
      simp only [normList_cons, normList_nil, overheadList_cons, overheadList_nil] at hlist
      split <;> omega
    | [ph, pt], [vh, vt], _, hlist =>
      rw [normItems_three, overheadItems_three]
      simp only [normList_cons, normList_nil, overheadList_cons, overheadList_nil] at hlist
      split <;> omega
    | ph :: pt :: pu :: more, vh :: vt :: vu :: vmore, hl, hlist =>
      rw [normItems_other (.sym s :: vh :: vt :: vu :: vmore) (fun _ _ _ h => nomatch h)
          (fun _ _ h => nomatch h),
        overheadItems_other (.sym s :: ph :: pt :: pu :: more) (fun _ _ _ h => nomatch h)
          (fun _ _ h => nomatch h)]
      simp only [normList_cons, overheadList_cons, norm_sym, overhead_sym,
        List.length_cons] at hlist hl ⊢
      omega
  | .var _ :: _, _, _, hp, _ => by simp only [headed, Bool.false_eq_true] at hp
  | .lit _ :: _, _, _, hp, _ => by simp only [headed, Bool.false_eq_true] at hp
  | .expr _ :: _, _, _, hp, _ => by simp only [headed, Bool.false_eq_true] at hp
  | .list _ :: _, _, _, hp, _ => by simp only [headed, Bool.false_eq_true] at hp

/-- The same for a list of patterns. -/
theorem normList_of_matchTerms : ∀ (ps vs : List Term) (σ : Env),
    headedList ps = true → matchTerms ps vs = some σ →
      normList vs = overheadList ps + envNorm σ
  | [], vs, σ, _, h => by
    obtain ⟨rfl, rfl⟩ := matchTerms_nil h
    simp only [normList_nil, overheadList_nil, envNorm, List.map_nil, List.sum_nil, Nat.add_zero]
  | p :: ps, vs, σ, hp, h => by
    obtain ⟨v, vs', σ₁, σ₂, rfl, h₁, h₂, rfl⟩ := matchTerms_cons h
    simp only [headedList, Bool.and_eq_true] at hp
    rw [normList_cons, overheadList_cons, envNorm_append,
      norm_of_matchTerm p v σ₁ hp.1 h₁, normList_of_matchTerms ps vs' σ₂ hp.2 h₂]
    omega

end

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
