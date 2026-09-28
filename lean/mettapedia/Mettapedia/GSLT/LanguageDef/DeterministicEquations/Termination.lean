import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Descent
import Mathlib.Order.RelClasses
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Perm.Subperm

/-!
# Descending programs end

Under a program with a descent certificate, and a host that keeps its
vocabulary's promises, every call ends: some fuel gives it an outcome other
than running out (`apply_terminates`).

The measure of a call is the vector, over the certificate's levels, of the
sum of the norms of its arguments at the level's positions plus the level's
potential.  Every call an equation's right side makes has a smaller measure
than the call that selected the equation, lexicographically, and the
lexicographic order on vectors of one length is well founded.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

/-! ## The lexicographic order -/

/-- Lexicographic order on vectors of naturals: the first entry that differs
is smaller. -/
def LexLt : List Nat → List Nat → Prop
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLt as bs)
  | _, _ => False

/-- The lexicographic order on vectors of one length is well founded. -/
theorem lexLt_wf : ∀ L : Nat,
    WellFounded (fun a b : {l : List Nat // l.length = L} => LexLt a.1 b.1)
  | 0 => by
    refine ⟨fun a => ⟨a, fun b hb => ?_⟩⟩
    obtain ⟨_ | _, hb'⟩ := b
    · obtain ⟨_ | _, ha'⟩ := a
      · exact absurd hb (by simp only [LexLt, not_false_eq_true])
      · exact absurd ha' (Nat.succ_ne_zero _)
    · exact absurd hb' (Nat.succ_ne_zero _)
  | L + 1 => by
    let f : {l : List Nat // l.length = L + 1} → Nat × {l : List Nat // l.length = L} :=
      fun a => match a with
        | ⟨x :: xs, h⟩ => (x, ⟨xs, Nat.succ.inj h⟩)
        | ⟨[], h⟩ => absurd h (Nat.succ_ne_zero L).symm
    have hwf : WellFounded (Prod.Lex (· < ·)
        (fun a b : {l : List Nat // l.length = L} => LexLt a.1 b.1)) :=
      WellFounded.prod_lex Nat.lt_wfRel.wf (lexLt_wf L)
    refine Subrelation.wf (r := InvImage (Prod.Lex (· < ·)
        (fun a b : {l : List Nat // l.length = L} => LexLt a.1 b.1)) f) ?_
      (InvImage.wf f hwf)
    intro a b hab
    obtain ⟨_ | ⟨x, xs⟩, ha⟩ := a
    · exact absurd ha (Nat.succ_ne_zero L).symm
    obtain ⟨_ | ⟨y, ys⟩, hb⟩ := b
    · exact absurd hb (Nat.succ_ne_zero L).symm
    simp only [LexLt] at hab
    show Prod.Lex _ _ (x, _) (y, _)
    rcases hab with h | ⟨rfl, h⟩
    · exact Prod.Lex.left _ _ h
    · exact Prod.Lex.right _ h

/-! ## The measure of a call -/

/-- The norm of a call's argument at a position. -/
def argNorm (vs : List Term) (i : Nat) : Nat := norm (vs.getD i (.expr []))

/-- The positions of a set that a list of the given length has, in order. -/
def positions (len : Nat) (S : List Nat) : List Nat :=
  (List.range len).filter (fun i => S.contains i)

/-- The sum of the norms of a call's arguments at the positions of a set. -/
def sumAt (vs : List Term) (S : List Nat) : Nat :=
  ((positions vs.length S).map (argNorm vs)).sum

/-- The measure of a call under a certificate, one entry per level. -/
def measure (c : Certificate) (f : String) (vs : List Term) : List Nat :=
  c.levels.map (fun l => sumAt vs (l.set f vs.length) + l.potential f vs.length)

theorem measure_length (c : Certificate) (f : String) (vs : List Term) :
    (measure c f vs).length = c.levels.length := by
  simp [measure]

/-- A decided site decreases the measure lexicographically, given at each
level the bound its weight states. -/
theorem lexLt_of_decides (P : Program) (V : Vocabulary) (e : Equation) (site : Site)
    (ws vs : List Term) :
    ∀ levels : List Level,
    decides P V e site levels = true →
    (∀ l ∈ levels, ∀ w, weigh P V e.params (l.set e.head e.params.length)
        (l.set site.callee site.args.length) site = some w →
      (sumAt ws (l.set site.callee site.args.length) : Int) ≤
        sumAt vs (l.set e.head e.params.length) + w) →
    LexLt
      (levels.map (fun l => sumAt ws (l.set site.callee site.args.length) +
        l.potential site.callee site.args.length))
      (levels.map (fun l => sumAt vs (l.set e.head e.params.length) +
        l.potential e.head e.params.length))
  | [], h, _ => by simp [decides] at h
  | l :: ls, h, hb => by
    simp only [decides] at h
    split at h
    · simp at h
    · rename_i w hw
      have hbound := hb l (List.mem_cons_self) w hw
      simp only [List.map_cons, LexLt]
      split at h
      · left
        omega
      · split at h
        · have hrest := lexLt_of_decides P V e site ws vs ls h
            (fun l' hl' w' hw' => hb l' (List.mem_cons_of_mem _ hl') w' hw')
          by_cases hlt : sumAt ws (l.set site.callee site.args.length) +
              l.potential site.callee site.args.length <
              sumAt vs (l.set e.head e.params.length) + l.potential e.head e.params.length
          · exact Or.inl hlt
          · right
            exact ⟨by omega, hrest⟩
        · simp at h

/-! ## Fuel -/

theorem eval_refines_add (P : Program) (H : Host) (n k : Nat) (env : Env) (t : Term) :
    Refines (eval P H n env t) (eval P H (n + k) env t) := by
  cases h : eval P H n env t with
  | exhausted => exact Or.inl rfl
  | value v =>
    exact Or.inr (by rw [eval_mono P H n k env t (by rw [h]; intro h'; cases h'), h])
  | failure =>
    exact Or.inr (by rw [eval_mono P H n k env t (by rw [h]; intro h'; cases h'), h])

theorem eval_le {P : Program} {H : Host} {n m : Nat} {env : Env} {t : Term} (hnm : n ≤ m)
    (h : eval P H n env t ≠ .exhausted) : eval P H m env t = eval P H n env t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact eval_mono P H n k env t h

theorem evalItems_le {P : Program} {H : Host} {n m : Nat} {env : Env} {ts : List Term}
    (hnm : n ≤ m) (h : evalItems P H n env ts ≠ .stop .exhausted) :
    evalItems P H m env ts = evalItems P H n env ts := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rcases evalItemsWith_refines (eval_refines_add P H n k) env ts with h' | h'
  · exact h'.symm
  · exact absurd h' h

theorem apply_le {P : Program} {H : Host} {n m : Nat} {f : String} {vs : List Term}
    (hnm : n ≤ m) (h : apply P H n f vs ≠ .exhausted) :
    apply P H m f vs = apply P H n f vs := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact ((applyWith_refines P H (eval_refines_add P H n k) f vs).eq h).symm

/-! ## Evaluation of elements and special forms -/

theorem evalItemsWith_forall₂ {ev : Env → Term → Outcome} {env : Env} :
    ∀ {ts vs : List Term}, evalItemsWith ev env ts = .values vs →
      List.Forall₂ (fun t v => ev env t = .value v) ts vs
  | [], vs, h => by
    simp only [evalItemsWith, ItemsOutcome.values.injEq] at h
    subst h
    exact .nil
  | t :: ts, vs, h => by
    simp only [evalItemsWith] at h
    split at h
    · rename_i v hv
      split at h
      · rename_i ws hws
        cases h
        exact .cons hv (evalItemsWith_forall₂ hws)
      · cases h
    · cases h

theorem evalItemsWith_stop {ev : Env → Term → Outcome} {env : Env} :
    ∀ {ts : List Term} {o : Outcome}, evalItemsWith ev env ts = .stop o → ∀ v, o ≠ .value v
  | [], o, h => by simp [evalItemsWith] at h
  | t :: ts, o, h => by
    simp only [evalItemsWith] at h
    split at h
    · split at h
      · cases h
      · rename_i o' h'
        cases h
        exact evalItemsWith_stop h'
    · rename_i _ hne
      cases h
      intro v hv
      exact hne v hv

theorem Forall₂.getD {R : Term → Term → Prop} :
    ∀ {l₁ l₂ : List Term}, List.Forall₂ R l₁ l₂ → ∀ {j : Nat}, j < l₁.length →
      R (l₁.getD j (.expr [])) (l₂.getD j (.expr []))
  | _, _, .nil, _, h => absurd h (Nat.not_lt_zero _)
  | _, _, .cons hr _, 0, _ => hr
  | _, _, .cons _ hs, j + 1, h => Forall₂.getD hs (j := j) (Nat.lt_of_succ_lt_succ h)

/-- A symbol-headed expression evaluation treats as a special form: a `let` of
three arguments or a `metta-nullary` of one. -/
def Special (f : String) (args : List Term) : Prop :=
  (f = "let" ∧ args.length = 3) ∨ (f = "metta-nullary" ∧ args.length = 1)

instance (f : String) (args : List Term) : Decidable (Special f args) :=
  inferInstanceAs (Decidable ((f = "let" ∧ args.length = 3) ∨
    (f = "metta-nullary" ∧ args.length = 1)))

instance (t : Term) : Decidable (∃ s, t = .sym s) :=
  match t with
  | .sym s => isTrue ⟨s, rfl⟩
  | .lit _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h
  | .var _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h
  | .expr _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h
  | .list _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h

instance (t : Term) : Decidable (∃ x, t = .var x) :=
  match t with
  | .var x => isTrue ⟨x, rfl⟩
  | .sym _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h
  | .lit _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h
  | .expr _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h
  | .list _ => isFalse fun ⟨_, h⟩ => Term.noConfusion h

theorem not_special_let {f : String} {args : List Term} (hs : ¬ Special f args) :
    ∀ a b d : Term, args = [a, b, d] → f = "let" → False :=
  fun _ _ _ h1 h2 => hs (Or.inl ⟨h2, by simp [h1]⟩)

theorem not_special_let_var {f : String} {args : List Term} (hs : ¬ Special f args) :
    ∀ (x : String) (b d : Term), args = [.var x, b, d] → f = "let" → False :=
  fun _ _ _ h1 h2 => hs (Or.inl ⟨h2, by simp [h1]⟩)

theorem not_special_nullary {f : String} {args : List Term} (hs : ¬ Special f args) :
    ∀ a : Term, args = [a] → f = "metta-nullary" → False :=
  fun _ h1 h2 => hs (Or.inr ⟨h2, by simp [h1]⟩)

theorem not_special_nullary_sym {f : String} {args : List Term} (hs : ¬ Special f args) :
    ∀ s : String, args = [.sym s] → f = "metta-nullary" → False :=
  fun _ h1 h2 => hs (Or.inr ⟨h2, by simp [h1]⟩)

theorem evalStep_head {ev : Env → Term → Outcome} {call : String → List Term → Outcome}
    {env : Env} {f : String} {args : List Term} (hs : ¬ Special f args) :
    evalStep ev call env (.expr (.sym f :: args)) =
      match evalItemsWith ev env args with
      | .values vs => call f vs
      | .stop o => o :=
  evalStep.eq_10 ev call env f args (not_special_let_var hs) (not_special_let hs)
    (not_special_nullary_sym hs) (not_special_nullary hs)

theorem evalStep_items {ev : Env → Term → Outcome} {call : String → List Term → Outcome}
    {env : Env} {hd : Term} {items : List Term} (hh : ∀ s, hd ≠ .sym s) :
    evalStep ev call env (.expr (hd :: items)) =
      match evalItemsWith ev env (hd :: items) with
      | .values vs => .value (.expr vs)
      | .stop o => o :=
  evalStep.eq_11 ev call env (hd :: items) (by simp)
    (fun _ _ _ h => hh _ (List.cons.inj h).1) (fun _ _ _ h => hh _ (List.cons.inj h).1)
    (fun _ h => hh _ (List.cons.inj h).1) (fun _ h => hh _ (List.cons.inj h).1)
    (fun _ _ h => hh _ (List.cons.inj h).1)

/-! ## Heads -/

theorem headKind_atom {P : Program} {V : Vocabulary} {f : String} {n : Nat}
    (h : headKind P V f n = .atom) :
    P.definesAt f n = false ∧ P.defines f = false ∧ V.classify f n = .atom := by
  unfold headKind at h
  by_cases h1 : P.definesAt f n = true
  · simp [h1] at h
  by_cases h2 : P.defines f = true
  · simp [h1, h2] at h
  cases h3 : V.classify f n <;> simp only [h1, h2, h3, Bool.false_eq_true, if_false] at h <;>
    (try split_ifs at h) <;> simp_all

theorem headKind_preserving {P : Program} {V : Vocabulary} {f : String} {n : Nat}
    (h : headKind P V f n = .preserving) :
    P.definesAt f n = false ∧ P.defines f = false ∧ V.classify f n = .preserving ∧ n = 1 := by
  unfold headKind at h
  by_cases h1 : P.definesAt f n = true
  · simp [h1] at h
  by_cases h2 : P.defines f = true
  · simp [h1, h2] at h
  cases h3 : V.classify f n <;> simp only [h1, h2, h3, Bool.false_eq_true, if_false] at h <;>
    (try split_ifs at h) <;> simp_all

theorem headKind_cell {P : Program} {V : Vocabulary} {f : String} {n : Nat}
    (h : headKind P V f n = .cell) :
    P.definesAt f n = false ∧ P.defines f = false ∧ V.classify f n = .none ∧
      n = 2 ∧ f = "LCons" := by
  unfold headKind at h
  by_cases h1 : P.definesAt f n = true
  · simp [h1] at h
  by_cases h2 : P.defines f = true
  · simp [h1, h2] at h
  cases h3 : V.classify f n <;> simp only [h1, h2, h3, Bool.false_eq_true, if_false] at h <;>
    (try split_ifs at h) <;> simp_all

theorem headKind_view {P : Program} {V : Vocabulary} {f : String} {n : Nat}
    (h : headKind P V f n = .view) :
    P.definesAt f n = false ∧ P.defines f = false ∧ V.classify f n = .none ∧
      n = 1 ∧ isView f = true := by
  unfold headKind at h
  by_cases h1 : P.definesAt f n = true
  · simp [h1] at h
  by_cases h2 : P.defines f = true
  · simp [h1, h2] at h
  cases h3 : V.classify f n <;> simp only [h1, h2, h3, Bool.false_eq_true, if_false] at h <;>
    (try split_ifs at h) <;> simp_all

theorem headKind_constructor {P : Program} {V : Vocabulary} {f : String} {n : Nat}
    (h : headKind P V f n = .constructor) :
    P.definesAt f n = false ∧ P.defines f = false ∧ V.classify f n = .none ∧
      ¬ (n = 2 ∧ f = "LCons") ∧ ¬ (n = 1 ∧ isView f = true) := by
  unfold headKind at h
  by_cases h1 : P.definesAt f n = true
  · simp [h1] at h
  by_cases h2 : P.defines f = true
  · simp [h1, h2] at h
  cases h3 : V.classify f n <;> simp only [h1, h2, h3, Bool.false_eq_true, if_false] at h <;>
    (try split_ifs at h) <;> simp_all

theorem applyWith_primitive {P : Program} {H : Host} {ev : Env → Term → Outcome}
    {f : String} {vs : List Term} (hd : P.definesAt f vs.length = false)
    (hf : P.defines f = false) :
    applyWith P H ev f vs =
      match H.primitive f vs with
      | .fault => .failure
      | .value v => .value v
      | .unhandled => .value (.expr (.sym f :: vs)) := by
  unfold applyWith
  rw [if_neg (by simp [hd]), if_neg (by simp [hf])]
  cases H.primitive f vs <;> rfl

/-! ## Claimed uses -/

/-- The norm of the value a match binds a variable to, 0 when it binds none. -/
def bindNorm (σ : Env) (y : String) : Nat :=
  match σ.lookup y with
  | some u => norm u
  | none => 0

/-- What an argument claims: `uses'` extends `uses` by new distinct variables
of the caller's measured patterns, and the norm `m` of its value is at most
its cost `c` plus the norms of the new variables' values. -/
def Claims (params : List Term) (S : List Nat) (σ : Env) (uses uses' : List String)
    (c m : Nat) : Prop :=
  ∃ new, uses' = new ++ uses ∧ new.Nodup ∧
    (∀ y ∈ new, measuredVar params S y = true ∧ y ∉ uses) ∧
    m ≤ c + (new.map (bindNorm σ)).sum

theorem Claims.none {params : List Term} {S : List Nat} {σ : Env} {uses : List String}
    {c m : Nat} (h : m ≤ c) : Claims params S σ uses uses c m :=
  ⟨[], by simp, List.nodup_nil, by simp, by simpa using h⟩

theorem Claims.mono {params : List Term} {S : List Nat} {σ : Env} {uses uses' : List String}
    {c m c' m' : Nat} (h : Claims params S σ uses uses' c m) (hc : c ≤ c') (hm : m' ≤ m) :
    Claims params S σ uses uses' c' m' := by
  obtain ⟨new, h1, h2, h3, h4⟩ := h
  exact ⟨new, h1, h2, h3, by omega⟩

theorem Claims.add {params : List Term} {S : List Nat} {σ : Env} {uses uses' : List String}
    {c m : Nat} (h : Claims params S σ uses uses' c m) (d : Nat) :
    Claims params S σ uses uses' (d + c) (d + m) := by
  obtain ⟨new, h1, h2, h3, h4⟩ := h
  exact ⟨new, h1, h2, h3, by omega⟩

theorem Claims.trans {params : List Term} {S : List Nat} {σ : Env}
    {u₀ u₁ u₂ : List String} {c₁ c₂ m₁ m₂ : Nat}
    (h₁ : Claims params S σ u₀ u₁ c₁ m₁) (h₂ : Claims params S σ u₁ u₂ c₂ m₂) :
    Claims params S σ u₀ u₂ (c₁ + c₂) (m₁ + m₂) := by
  obtain ⟨n₁, rfl, hn₁, hm₁, hb₁⟩ := h₁
  obtain ⟨n₂, rfl, hn₂, hm₂, hb₂⟩ := h₂
  refine ⟨n₂ ++ n₁, by simp, ?_, ?_, ?_⟩
  · refine List.nodup_append.2 ⟨hn₂, hn₁, ?_⟩
    intro a ha b hb hab
    subst hab
    exact (hm₂ a ha).2 (List.mem_append_left _ hb)
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact ⟨(hm₂ y hy).1, fun h => (hm₂ y hy).2 (List.mem_append_right _ h)⟩
    · exact hm₁ y hy
  · simp only [List.map_append, List.sum_append]
    omega

/-! ## The environment of a right side -/

/-- String equality tests itself true; `BEq.rfl` would go through a classical
instance. -/
theorem string_beq_self (x : String) : (x == x) = true := decide_eq_true rfl

theorem Env.lookup_cons_self (x : String) (v : Term) (ρ : Env) :
    Env.lookup ((x, v) :: ρ) x = some v := by
  have h : (fun b : String × Term => b.1 == x) (x, v) = true := string_beq_self x
  unfold Env.lookup
  rw [List.find?_cons_of_pos (p := fun b : String × Term => b.1 == x) (a := (x, v)) h]
  rfl

theorem Env.lookup_cons_ne {x y : String} (v : Term) (ρ : Env) (h : x ≠ y) :
    Env.lookup ((x, v) :: ρ) y = ρ.lookup y := by
  simp only [Env.lookup, beq_iff_eq, h, not_false_eq_true, List.find?_cons_of_neg]

theorem lookupBinder_cons (x : String) (cy : Option String) (env : List Binder) (y : String) :
    lookupBinder (⟨x, cy⟩ :: env) y = if x = y then some ⟨x, cy⟩ else lookupBinder env y := by
  by_cases h : x = y
  · subst h
    have h : (fun b : Binder => b.var == x) ⟨x, cy⟩ = true := string_beq_self x
    unfold lookupBinder
    rw [List.find?_cons_of_pos (p := fun b : Binder => b.var == x) (a := ⟨x, cy⟩) h, if_pos rfl]
  · simp only [lookupBinder, beq_iff_eq, h, not_false_eq_true, List.find?_cons_of_neg, ↓reduceIte]

/-- The dynamic environment of a right side agrees with its static binders:
a variable no binder covers has its value under the match `σ`, and a binder
that carries a variable holds a value of norm at most that variable's. -/
structure Inv (σ : Env) (benv : List Binder) (ρ : Env) : Prop where
  free : ∀ x, lookupBinder benv x = none → ρ.lookup x = σ.lookup x
  carries : ∀ x b y v, lookupBinder benv x = some b → b.carried = some y →
    ρ.lookup x = some v → norm v ≤ bindNorm σ y

theorem Inv.init (σ : Env) : Inv σ [] σ :=
  ⟨fun _ _ => rfl, fun _ _ _ _ h => by simp [lookupBinder] at h⟩

theorem Inv.extend {σ ρ : Env} {benv : List Binder} (hI : Inv σ benv ρ) (x : String)
    (v : Term) (cy : Option String) (hc : ∀ y, cy = some y → norm v ≤ bindNorm σ y) :
    Inv σ (⟨x, cy⟩ :: benv) ((x, v) :: ρ) where
  free x' h := by
    rw [lookupBinder_cons] at h
    split at h
    · cases h
    · rename_i hne
      rw [Env.lookup_cons_ne v ρ hne]
      exact hI.free x' h
  carries x' b y w hb hy hw := by
    rw [lookupBinder_cons] at hb
    split at hb
    · rename_i heq
      cases hb
      subst heq
      rw [Env.lookup_cons_self] at hw
      cases hw
      exact hc y hy
    · rename_i hne
      rw [Env.lookup_cons_ne v ρ hne] at hw
      exact hI.carries x' b y w hb hy hw

theorem strip_of_view {P : Program} {V : Vocabulary} {t x : Term}
    (h : viewArgument P V t = some x) : strip P V t = strip P V x := by
  rw [strip]
  split <;> simp_all

theorem strip_of_not_view {P : Program} {V : Vocabulary} {t : Term}
    (h : viewArgument P V t = none) : strip P V t = t := by
  rw [strip]
  split <;> simp_all

theorem viewArgument_some {P : Program} {V : Vocabulary} {t x : Term}
    (h : viewArgument P V t = some x) :
    ∃ f, t = .expr [.sym f, x] ∧ (headKind P V f 1 = .view ∨ headKind P V f 1 = .preserving) := by
  unfold viewArgument at h
  split at h
  · rename_i f y
    split at h
    · rename_i hk
      cases h
      exact ⟨f, rfl, Or.inl hk⟩
    · rename_i hk
      cases h
      exact ⟨f, rfl, Or.inr hk⟩
    · cases h
  · cases h

theorem bindNorm_of_lookup {σ : Env} {y : String} {u : Term} (h : σ.lookup y = some u) :
    bindNorm σ y = norm u := by
  simp [bindNorm, h]

/-- A term that carries a variable has a value of norm at most the variable's. -/
theorem carried_bound {P : Program} {H : Host} {V : Vocabulary} (hK : Keeps V H) {σ ρ : Env}
    {benv : List Binder} (hI : Inv σ benv ρ) :
    ∀ (n : Nat) (t : Term) (y : String) (v : Term), carried P V benv t = some y →
      eval P H n ρ t = .value v → norm v ≤ bindNorm σ y
  | 0, _, _, _, _, he => by simp [eval] at he
  | k + 1, t, y, v, hc, he => by
    cases hv : viewArgument P V t with
    | some x =>
      obtain ⟨f, rfl, hk⟩ := viewArgument_some hv
      have hcx : carried P V benv x = some y := by
        unfold carried at hc ⊢
        rw [strip_of_view hv] at hc
        exact hc
      rw [eval] at he
      by_cases hs : Special f [x]
      · rcases hs with ⟨_, h3⟩ | ⟨rfl, _⟩
        · simp at h3
        · by_cases hx : ∃ s, x = .sym s
          · obtain ⟨s, rfl⟩ := hx
            unfold carried at hcx
            rw [strip_of_not_view (by simp [viewArgument])] at hcx
            simp at hcx
          · rw [evalStep.eq_9 _ _ _ _ (fun s h => hx ⟨s, h⟩)] at he
            cases he
      · rw [evalStep_head hs] at he
        split at he
        · rename_i ws hws
          obtain ⟨w, hw⟩ : ∃ w, ws = [w] ∧ eval P H k ρ x = .value w := by
            cases evalItemsWith_forall₂ hws with
            | cons hw hrest =>
              cases hrest
              exact ⟨_, rfl, hw⟩
          obtain ⟨rfl, hw⟩ := hw
          have ih := carried_bound hK hI k x y w hcx hw
          rcases hk with hk | hk
          · obtain ⟨hd, hf, hcl, _, hview⟩ := headKind_view hk
            rw [applyWith_primitive hd hf, hK.unclassified f [w] hcl] at he
            cases he
            rw [norm_expr, normItems_two, if_pos hview]
            exact ih
          · obtain ⟨hd, hf, hcl, _⟩ := headKind_preserving hk
            rw [applyWith_primitive hd hf] at he
            cases hp : H.primitive f [w] with
            | unhandled => exact absurd hp (hK.handled f [w] (by simp [hcl]))
            | fault =>
              rw [hp] at he
              cases he
            | value u =>
              rw [hp] at he
              cases he
              obtain ⟨u', hu', hle⟩ := hK.preserving f [w] _ hcl hp
              cases hu'
              omega
        · rename_i o ho
          exact absurd he (evalItemsWith_stop ho v)
    | none =>
      unfold carried at hc
      rw [strip_of_not_view hv] at hc
      split at hc
      · rename_i x
        simp only [eval, evalStep] at he
        split at he
        · rename_i u hu
          cases he
          cases hb : lookupBinder benv x with
          | none =>
            simp only [hb, Option.some.injEq] at hc
            subst hc
            rw [hI.free x hb] at hu
            rw [bindNorm_of_lookup hu]
          | some b =>
            simp only [hb] at hc
            exact hI.carries x b y _ hb hc hu
        · cases he
      · cases hc

/-! ## Costs bound values -/

theorem normItems_le (vs : List Term) : normItems vs ≤ 1 + vs.length + normList vs := by
  unfold normItems
  split
  · simp only [normList_cons, normList_nil, norm_sym, List.length_cons, List.length_nil]
    split <;> omega
  · simp only [normList_cons, normList_nil, norm_sym, List.length_cons, List.length_nil]
    split <;> omega
  · exact Nat.le_refl _

theorem costList_bound {P : Program} {H : Host} {V : Vocabulary} {params : List Term}
    {S : List Nat} {σ ρ : Env} {benv : List Binder} {k : Nat}
    (ih : ∀ t uses c uses' v, cost P V params S benv t uses = some (c, uses') →
      eval P H k ρ t = .value v → Claims params S σ uses uses' c (norm v)) :
    ∀ ts uses c uses' ws, costList P V params S benv ts uses = some (c, uses') →
      evalItemsWith (eval P H k) ρ ts = .values ws → Claims params S σ uses uses' c (normList ws)
  | [], uses, c, uses', ws, hc, he => by
    rw [costList.eq_1] at hc
    simp only [evalItemsWith, ItemsOutcome.values.injEq] at he
    subst he
    cases hc
    exact Claims.none (by simp [normList_nil])
  | t :: ts, uses, c, uses', ws, hc, he => by
    rw [costList.eq_2] at hc
    simp only [evalItemsWith] at he
    split at hc
    · rename_i c₁ u₁ h₁
      split at hc
      · rename_i cs u₂ h₂
        cases hc
        split at he
        · rename_i v hv
          split at he
          · rename_i vs hvs
            cases he
            have := (ih t uses c₁ u₁ v h₁ hv).trans (costList_bound ih ts u₁ cs _ vs h₂ hvs)
            simpa [normList_cons] using this
          · cases he
        · cases he
      · cases hc
    · cases hc

theorem cost_no_bound {P : Program} {V : Vocabulary} {params : List Term} {S : List Nat}
    {env : List Binder} {uses : List String} {f : String} {args : List Term}
    (hs : ¬ Special f args)
    (hk : headKind P V f args.length = .call ∨ headKind P V f args.length = .fails ∨
      headKind P V f args.length = .structure) :
    cost P V params S env (.expr (.sym f :: args)) uses = none := by
  have h1 : headKind P V f args.length ≠ .atom := by rcases hk with h | h | h <;> simp [h]
  have h2 : headKind P V f args.length ≠ .constructor := by rcases hk with h | h | h <;> simp [h]
  have h3 : headKind P V f args.length ≠ .preserving := by rcases hk with h | h | h <;> simp [h]
  have h4 : headKind P V f args.length ≠ .view := by rcases hk with h | h | h <;> simp [h]
  have h5 : headKind P V f args.length ≠ .cell := by rcases hk with h | h | h <;> simp [h]
  exact cost.eq_14 P V params S env uses f args (not_special_let hs)
    (not_special_nullary_sym hs) (not_special_nullary hs) h1 h2
    (fun _ h _ => h3 h) (fun _ h _ => h4 h) (fun _ _ h _ => h5 h)

theorem cost_bound_items {P : Program} {H : Host} {V : Vocabulary} {params : List Term}
    {S : List Nat} {σ ρ : Env} {benv : List Binder} {k : Nat}
    (ih : ∀ t uses c uses' v, cost P V params S benv t uses = some (c, uses') →
      eval P H k ρ t = .value v → Claims params S σ uses uses' c (norm v))
    {hd : Term} {items : List Term} (hh : ∀ s, hd ≠ .sym s) {uses : List String} {c : Nat}
    {uses' : List String} {v : Term}
    (hc : cost P V params S benv (.expr (hd :: items)) uses = some (c, uses'))
    (he : eval P H (k + 1) ρ (.expr (hd :: items)) = .value v) :
    Claims params S σ uses uses' c (norm v) := by
  rw [cost.eq_15 P V params S benv uses (hd :: items) (by simp)
    (fun _ _ _ h => hh _ (List.cons.inj h).1) (fun _ h => hh _ (List.cons.inj h).1)
    (fun _ h => hh _ (List.cons.inj h).1) (fun _ _ h => hh _ (List.cons.inj h).1)] at hc
  rw [eval, evalStep_items hh] at he
  split at he
  · rename_i ws hws
    cases he
    cases hcl : costList P V params S benv (hd :: items) uses with
    | none => simp [hcl] at hc
    | some r =>
      obtain ⟨r1, r2⟩ := r
      simp only [hcl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hlen := (evalItemsWith_forall₂ hws).length_eq
      have hb := (costList_bound ih _ uses r1 r2 ws hcl hws).add (1 + (hd :: items).length)
      rw [norm_expr]
      refine hb.mono (Nat.le_refl _) ?_
      have := normItems_le ws
      rw [← hlen] at this
      omega
  · rename_i o ho
    exact absurd he (evalItemsWith_stop ho v)

/-- The cost of an argument bounds the norm of its value. -/
theorem cost_bound {P : Program} {H : Host} {V : Vocabulary} (hK : Keeps V H)
    {params : List Term} {S : List Nat} {σ ρ : Env} {benv : List Binder}
    (hI : Inv σ benv ρ) :
    ∀ (n : Nat) (t : Term) (uses : List String) (c : Nat) (uses' : List String) (v : Term),
      cost P V params S benv t uses = some (c, uses') → eval P H n ρ t = .value v →
      Claims params S σ uses uses' c (norm v)
  | 0, _, _, _, _, _, _, he => by simp [eval] at he
  | k + 1, .var x, uses, c, uses', v, hc, he => by
    rw [cost.eq_1] at hc
    simp only [eval, evalStep] at he
    split at he
    · rename_i u hu
      cases he
      cases hb : lookupBinder benv x with
      | none =>
        simp only [hb] at hc
        split at hc
        · rename_i hm
          cases hc
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hm
          refine ⟨[x], rfl, by simp, ?_, ?_⟩
          · intro y hy
            rw [List.mem_singleton] at hy
            subst hy
            exact ⟨hm.1, by simpa using hm.2⟩
          · rw [hI.free x hb] at hu
            simp [bindNorm_of_lookup hu]
        · cases hc
      | some b =>
        simp only [hb] at hc
        cases hcy : b.carried with
        | none => simp [hcy] at hc
        | some y =>
          simp only [hcy] at hc
          split at hc
          · rename_i hm
            cases hc
            simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hm
            refine ⟨[y], rfl, by simp, ?_, ?_⟩
            · intro y' hy'
              rw [List.mem_singleton] at hy'
              subst hy'
              exact ⟨hm.1, by simpa using hm.2⟩
            · simpa using hI.carries x b y _ hb hcy hu
          · cases hc
    · cases he
  | k + 1, .sym s, uses, c, uses', v, hc, he => by
    rw [cost.eq_2] at hc
    cases hc
    simp only [eval, evalStep, Outcome.value.injEq] at he
    subst he
    exact Claims.none (by simp [norm_sym])
  | k + 1, .lit s, uses, c, uses', v, hc, he => by
    rw [cost.eq_3] at hc
    cases hc
    simp only [eval, evalStep, Outcome.value.injEq] at he
    subst he
    exact Claims.none (by simp [norm_lit])
  | k + 1, .list items, uses, c, uses', v, hc, he => by
    rw [cost.eq_4] at hc
    simp only [eval, evalStep] at he
    split at he
    · rename_i ws hws
      cases he
      cases hcl : costList P V params S benv items uses with
      | none => simp [hcl] at hc
      | some r =>
        obtain ⟨r1, r2⟩ := r
        simp only [hcl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hlen := (evalItemsWith_forall₂ hws).length_eq
        have hb := (costList_bound (cost_bound hK hI k) items uses r1 r2 ws hcl hws).add
          (1 + items.length)
        rw [norm_list, ← hlen]
        exact hb
    · rename_i o ho
      exact absurd he (evalItemsWith_stop ho v)
  | k + 1, .expr [], uses, c, uses', v, hc, he => by
    rw [cost.eq_5] at hc
    cases hc
    simp only [eval, evalStep, Outcome.value.injEq] at he
    subst he
    refine Claims.none ?_
    rw [norm_expr, normItems_other [] (by simp) (by simp)]
    simp [normList_nil]
  | k + 1, .expr (.sym f :: args), uses, c, uses', v, hc, he => by
    rw [eval] at he
    by_cases hs : Special f args
    · rcases hs with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
      · obtain ⟨a, b, d, rfl⟩ := List.length_eq_three.1 hl
        rw [cost.eq_6] at hc
        cases hc
      · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl
        by_cases ha : ∃ s, a = .sym s
        · obtain ⟨s, rfl⟩ := ha
          rw [cost.eq_7] at hc
          cases hc
          rw [evalStep.eq_8] at he
          cases he
          refine Claims.none ?_
          rw [norm_expr, normItems_other _ (by simp) (by simp)]
          simp [normList_cons, normList_nil, norm_sym]
        · rw [cost.eq_8 P V params S benv uses a (fun s h => ha ⟨s, h⟩)] at hc
          cases hc
    · rw [evalStep_head hs] at he
      split at he
      · rename_i ws hws
        have h2 := evalItemsWith_forall₂ hws
        have hlen := h2.length_eq
        cases hk : headKind P V f args.length with
        | call =>
          rw [cost_no_bound hs (Or.inl hk)] at hc
          cases hc
        | fails =>
          rw [cost_no_bound hs (Or.inr (Or.inl hk))] at hc
          cases hc
        | «structure» =>
          rw [cost_no_bound hs (Or.inr (Or.inr hk))] at hc
          cases hc
        | atom =>
          rw [cost.eq_9 P V params S benv uses f args (not_special_let hs)
            (not_special_nullary_sym hs) (not_special_nullary hs) hk] at hc
          cases hc
          obtain ⟨hd, hf, hcl⟩ := headKind_atom hk
          rw [hlen] at hd hcl
          rw [applyWith_primitive hd hf] at he
          cases hp : H.primitive f ws with
          | unhandled => exact absurd hp (hK.handled f ws (by simp [hcl]))
          | fault =>
            rw [hp] at he
            cases he
          | value u =>
            rw [hp] at he
            cases he
            exact Claims.none (by rw [hK.atom f ws _ hcl hp])
        | preserving =>
          obtain ⟨hd, hf, hcl, h1⟩ := headKind_preserving hk
          obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 h1
          rw [cost.eq_10 P V params S benv uses f x (not_special_let hs)
            (not_special_nullary_sym hs) (not_special_nullary hs) hk] at hc
          obtain ⟨w, rfl, hw⟩ : ∃ w, ws = [w] ∧ eval P H k ρ x = .value w := by
            cases h2 with
            | cons hw hrest =>
              cases hrest
              exact ⟨_, rfl, hw⟩
          have ih := cost_bound hK hI k x uses c uses' w hc hw
          rw [applyWith_primitive (vs := [w]) hd hf] at he
          have hcl' : V.classify f [w].length = .preserving := hcl
          cases hp : H.primitive f [w] with
          | unhandled => exact absurd hp (hK.handled f [w] (by rw [hcl']; simp))
          | fault =>
            rw [hp] at he
            cases he
          | value u =>
            rw [hp] at he
            cases he
            obtain ⟨u', hu', hle⟩ := hK.preserving f [w] _ hcl' hp
            cases hu'
            exact ih.mono (Nat.le_refl _) hle
        | cell =>
          obtain ⟨hd, hf, hcl, h2', rfl⟩ := headKind_cell hk
          obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 h2'
          rw [cost.eq_12 P V params S benv uses "LCons" a b (not_special_let hs)
            (not_special_nullary_sym hs) (not_special_nullary hs) hk] at hc
          obtain ⟨wa, wb, rfl, hwa, hwb⟩ : ∃ wa wb, ws = [wa, wb] ∧
              eval P H k ρ a = .value wa ∧ eval P H k ρ b = .value wb := by
            cases h2 with
            | cons hwa hrest =>
              cases hrest with
              | cons hwb hrest' =>
                cases hrest'
                exact ⟨_, _, rfl, hwa, hwb⟩
          split at hc
          · rename_i ca u₁ hca
            split at hc
            · rename_i cb u₂ hcb
              cases hc
              have hb := ((cost_bound hK hI k a uses ca u₁ wa hca hwa).trans
                (cost_bound hK hI k b u₁ cb _ wb hcb hwb)).add 1
              rw [applyWith_primitive (vs := [wa, wb]) hd hf,
                hK.unclassified "LCons" [wa, wb] hcl] at he
              cases he
              rw [norm_expr, normItems_three, if_pos rfl]
              exact hb.mono (by omega) (by omega)
            · cases hc
          · cases hc
        | view =>
          obtain ⟨hd, hf, hcl, h1, hview⟩ := headKind_view hk
          obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 h1
          rw [cost.eq_11 P V params S benv uses f x (not_special_let hs)
            (not_special_nullary_sym hs) (not_special_nullary hs) hk] at hc
          obtain ⟨w, rfl, hw⟩ : ∃ w, ws = [w] ∧ eval P H k ρ x = .value w := by
            cases h2 with
            | cons hw hrest =>
              cases hrest
              exact ⟨_, rfl, hw⟩
          have ih := cost_bound hK hI k x uses c uses' w hc hw
          rw [applyWith_primitive (vs := [w]) hd hf, hK.unclassified f [w] hcl] at he
          cases he
          rw [norm_expr, normItems_two, if_pos hview]
          exact ih
        | constructor =>
          obtain ⟨hd, hf, hcl, _, _⟩ := headKind_constructor hk
          rw [cost.eq_13 P V params S benv uses f args (not_special_let hs)
            (not_special_nullary_sym hs) (not_special_nullary hs) hk] at hc
          cases hcl' : costList P V params S benv args uses with
          | none => simp [hcl'] at hc
          | some r =>
            obtain ⟨r1, r2⟩ := r
            simp only [hcl', Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            obtain ⟨rfl, rfl⟩ := hc
            have hb := (costList_bound (cost_bound hK hI k) args uses r1 r2 ws hcl' hws).add
              (1 + (args.length + 1) + 1)
            rw [hlen] at hd hcl
            rw [applyWith_primitive hd hf, hK.unclassified _ _ hcl] at he
            cases he
            rw [norm_expr]
            refine hb.mono (Nat.le_refl _) ?_
            have := normItems_le (.sym f :: ws)
            simp only [normList_cons, norm_sym, List.length_cons] at this
            omega
      · rename_i o ho
        exact absurd he (evalItemsWith_stop ho v)
  | k + 1, .expr (.var x :: items), uses, c, uses', v, hc, he =>
    cost_bound_items (cost_bound hK hI k) (by simp) hc he
  | k + 1, .expr (.lit x :: items), uses, c, uses', v, hc, he =>
    cost_bound_items (cost_bound hK hI k) (by simp) hc he
  | k + 1, .expr (.expr x :: items), uses, c, uses', v, hc, he =>
    cost_bound_items (cost_bound hK hI k) (by simp) hc he
  | k + 1, .expr (.list x :: items), uses, c, uses', v, hc, he =>
    cost_bound_items (cost_bound hK hI k) (by simp) hc he

/-! ## Matches bind the variables of their patterns -/

theorem patternVarsList_nil : patternVarsList [] = [] := by rw [patternVarsList]
theorem patternVarsList_cons (t : Term) (ts : List Term) :
    patternVarsList (t :: ts) = patternVars t ++ patternVarsList ts := by rw [patternVarsList]
theorem patternVars_var (x : String) : patternVars (.var x) = [x] := by rw [patternVars]
theorem patternVars_sym (s : String) : patternVars (.sym s) = [] := by
  rw [patternVars] <;> simp
theorem patternVars_lit (s : String) : patternVars (.lit s) = [] := by
  rw [patternVars] <;> simp
theorem patternVars_expr (ps : List Term) : patternVars (.expr ps) = patternVarsList ps := by
  rw [patternVars]
theorem patternVars_list (ps : List Term) : patternVars (.list ps) = patternVarsList ps := by
  rw [patternVars]

mutual

theorem matchTerm_keys : ∀ (p v : Term) (σ : Env), matchTerm p v = some σ →
    σ.map Prod.fst = patternVars p
  | .var x, v, σ, h => by
    rw [matchTerm_var h, patternVars_var]
    rfl
  | .sym a, v, σ, h => by
    obtain ⟨rfl, rfl⟩ := matchTerm_sym h
    simp only [List.map_nil, patternVars_sym]
  | .lit a, v, σ, h => by
    obtain ⟨rfl, rfl⟩ := matchTerm_lit h
    simp only [List.map_nil, patternVars_lit]
  | .expr ps, v, σ, h => by
    obtain ⟨vs, rfl, hm⟩ := matchTerm_expr h
    rw [patternVars_expr]
    exact matchTerms_keys ps vs σ hm
  | .list ps, v, σ, h => by
    obtain ⟨vs, rfl, hm⟩ := matchTerm_list h
    rw [patternVars_list]
    exact matchTerms_keys ps vs σ hm

theorem matchTerms_keys : ∀ (ps vs : List Term) (σ : Env), matchTerms ps vs = some σ →
    σ.map Prod.fst = patternVarsList ps
  | [], vs, σ, h => by
    obtain ⟨rfl, rfl⟩ := matchTerms_nil h
    simp [patternVarsList_nil]
  | p :: ps, vs, σ, h => by
    obtain ⟨v, vs', σ₁, σ₂, rfl, h₁, h₂, rfl⟩ := matchTerms_cons h
    rw [List.map_append, matchTerm_keys p v σ₁ h₁, matchTerms_keys ps vs' σ₂ h₂,
      patternVarsList_cons]

end

theorem Env.lookup_of_mem_keys {σ : Env} {y : String} (h : y ∈ σ.map Prod.fst) :
    ∃ u, σ.lookup y = some u := by
  unfold Env.lookup
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
  have : (σ.find? (fun b' => b'.1 == b.1)).isSome :=
    List.find?_isSome.2 ⟨b, hb, string_beq_self _⟩
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 this
  exact ⟨b'.2, by simp only [hb', Option.map_some]⟩

theorem Env.lookup_append_of_mem {σ₁ σ₂ : Env} {y : String} (h : y ∈ σ₁.map Prod.fst) :
    (σ₁ ++ σ₂).lookup y = σ₁.lookup y := by
  unfold Env.lookup
  rw [List.find?_append]
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
  have : (σ₁.find? (fun b' => b'.1 == b.1)).isSome :=
    List.find?_isSome.2 ⟨b, hb, string_beq_self _⟩
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 this
  simp only [hb', Option.some_or, Option.map_some]

theorem Env.lookup_append_of_not_mem {σ₁ σ₂ : Env} {y : String} (h : y ∉ σ₁.map Prod.fst) :
    (σ₁ ++ σ₂).lookup y = σ₂.lookup y := by
  unfold Env.lookup
  rw [List.find?_append]
  have : σ₁.find? (fun b => b.1 == y) = none := by
    rw [List.find?_eq_none]
    intro b hb hby
    exact h (List.mem_map.2 ⟨b, hb, by simpa using hby⟩)
  simp [this]

theorem bindNorm_append_of_mem {σ₁ σ₂ : Env} {y : String} (h : y ∈ σ₁.map Prod.fst) :
    bindNorm (σ₁ ++ σ₂) y = bindNorm σ₁ y := by
  simp only [bindNorm, Env.lookup_append_of_mem h]

theorem bindNorm_append_of_not_mem {σ₁ σ₂ : Env} {y : String} (h : y ∉ σ₁.map Prod.fst) :
    bindNorm (σ₁ ++ σ₂) y = bindNorm σ₂ y := by
  simp only [bindNorm, Env.lookup_append_of_not_mem h]

theorem one_le_bindNorm {σ : Env} {y : String} (h : y ∈ σ.map Prod.fst) : 1 ≤ bindNorm σ y := by
  obtain ⟨u, hu⟩ := Env.lookup_of_mem_keys h
  rw [bindNorm_of_lookup hu]
  exact one_le_norm u

theorem envNorm_eq_keys : ∀ σ : Env, (σ.map Prod.fst).Nodup →
    envNorm σ = ((σ.map Prod.fst).map (bindNorm σ)).sum
  | [], _ => by simp only [envNorm, List.map_nil, List.sum_nil]
  | (x, v) :: σ, h => by
    rw [List.map_cons, List.nodup_cons] at h
    have ih := envNorm_eq_keys σ h.2
    have hx : bindNorm ((x, v) :: σ) x = norm v := bindNorm_of_lookup (Env.lookup_cons_self x v σ)
    have hrest : (σ.map Prod.fst).map (bindNorm ((x, v) :: σ)) =
        (σ.map Prod.fst).map (bindNorm σ) := by
      apply List.map_congr_left
      intro y hy
      have hne : x ≠ y := fun e => h.1 (e ▸ hy)
      simp only [bindNorm, Env.lookup_cons_ne v σ hne]
    have hσ : envNorm ((x, v) :: σ) = norm v + envNorm σ := by
      simp only [envNorm, List.map_cons, List.sum_cons]
    rw [hσ, ih, List.map_cons, List.map_cons, List.sum_cons, hx, hrest]

theorem mem_patternVarsList_of_getD : ∀ {ps : List Term} {j : Nat} {y : String},
    j < ps.length → y ∈ patternVars (ps.getD j (.expr [])) → y ∈ patternVarsList ps
  | [], _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | p :: ps, 0, y, _, hy => by
    rw [patternVarsList_cons]
    exact List.mem_append_left _ hy
  | p :: ps, j + 1, y, hj, hy => by
    rw [patternVarsList_cons]
    exact List.mem_append_right _
      (mem_patternVarsList_of_getD (Nat.lt_of_succ_lt_succ hj) hy)

/-- Under a left-linear match, the norm of the value at a headed position is its
pattern's overhead plus the norms of the values of its variables. -/
theorem norm_at_of_matchTerms : ∀ (ps vs : List Term) (σ : Env), matchTerms ps vs = some σ →
    (patternVarsList ps).Nodup → ∀ i, i < ps.length → headed (ps.getD i (.expr [])) = true →
    norm (vs.getD i (.expr [])) = overhead (ps.getD i (.expr [])) +
      ((patternVars (ps.getD i (.expr []))).map (bindNorm σ)).sum
  | [], _, _, _, _, i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | p :: ps, vs, σ, h, hnd, i, hi, hh => by
    obtain ⟨v, vs', σ₁, σ₂, rfl, h₁, h₂, rfl⟩ := matchTerms_cons h
    rw [patternVarsList_cons] at hnd
    obtain ⟨hnd₁, hnd₂, hdisj⟩ := List.nodup_append.1 hnd
    have hk₁ := matchTerm_keys p v σ₁ h₁
    cases i with
    | zero =>
      simp only [List.getD_cons_zero] at hh ⊢
      rw [norm_of_matchTerm p v σ₁ hh h₁, envNorm_eq_keys σ₁ (by rw [hk₁]; exact hnd₁), hk₁]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro y hy
      exact (bindNorm_append_of_mem (by rw [hk₁]; exact hy)).symm
    | succ j =>
      simp only [List.getD_cons_succ] at hh ⊢
      have hj : j < ps.length := Nat.lt_of_succ_lt_succ hi
      rw [norm_at_of_matchTerms ps vs' σ₂ h₂ hnd₂ j hj hh]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro y hy
      have hy' : y ∈ patternVarsList ps := mem_patternVarsList_of_getD hj hy
      have hny : y ∉ σ₁.map Prod.fst := by
        rw [hk₁]
        intro hy1
        exact hdisj y hy1 y hy' rfl
      exact (bindNorm_append_of_not_mem hny).symm

/-! ## The slack of the caller's patterns -/

theorem sum_filter_split {l : List String} {f : String → Nat} (p : String → Bool)
    (h : ∀ y ∈ l, 1 ≤ f y) :
    (l.filter (fun y => !p y)).length + ((l.filter p).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have ih' := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have hy := h y List.mem_cons_self
    cases hp : p y <;> simp [hp] <;> omega

theorem sum_le_of_subperm {l₁ l₂ : List String} {f : String → Nat} (h : l₁.Subperm l₂) :
    (l₁.map f).sum ≤ (l₂.map f).sum := by
  obtain ⟨l, hperm, hsub⟩ := h
  rw [← (hperm.map f).sum_nat]
  exact (hsub.map f).sum_le_sum (fun _ _ => Nat.zero_le _)

/-- The norms of the used variables' values and the slack of the caller's
patterns at its positions are at most the sum of the norms of its arguments
there. -/
theorem slack_bound {params vs : List Term} {σ : Env} {Sf : List Nat}
    (hmatch : matchTerms params vs = some σ) (hlin : (patternVarsList params).Nodup)
    (hmeas : ∀ i ∈ Sf, ∃ p, params[i]? = some p ∧ headed p = true)
    {U : List String} (hU : U.Nodup) (hUm : ∀ y ∈ U, measuredVar params Sf y = true) :
    (U.map (bindNorm σ)).sum + slack params Sf U ≤ sumAt vs Sf := by
  have hlen := matchTerms_length hmatch
  have hkeys := matchTerms_keys params vs σ hmatch
  have hPf : ∀ i ∈ (List.range params.length).filter (fun i => Sf.contains i),
      i < params.length ∧ headed (params.getD i (.expr [])) = true := by
    intro i hi
    simp only [List.mem_filter, List.mem_range, List.contains_iff_mem] at hi
    obtain ⟨hlt, hS⟩ := hi
    obtain ⟨p, hp, hh⟩ := hmeas i hS
    refine ⟨hlt, ?_⟩
    rw [List.getD_eq_getElem?_getD, hp]
    exact hh
  have hper : ∀ i ∈ (List.range params.length).filter (fun i => Sf.contains i),
      (overhead (params.getD i (.expr [])) + unused (params.getD i (.expr [])) U) +
        (((patternVars (params.getD i (.expr []))).filter (fun y => U.contains y)).map
          (bindNorm σ)).sum ≤ argNorm vs i := by
    intro i hi
    obtain ⟨hlt, hh⟩ := hPf i hi
    have hn := norm_at_of_matchTerms params vs σ hmatch hlin i hlt hh
    have hsplit := sum_filter_split (l := patternVars (params.getD i (.expr [])))
      (f := bindNorm σ) (fun y => U.contains y)
      (fun y hy => one_le_bindNorm (by rw [hkeys]; exact mem_patternVarsList_of_getD hlt hy))
    simp only [argNorm]
    rw [hn]
    unfold unused
    omega
  have hle := List.sum_le_sum hper
  rw [List.sum_map_add] at hle
  have hU' : (U.map (bindNorm σ)).sum ≤
      (((List.range params.length).filter (fun i => Sf.contains i)).map (fun i =>
        (((patternVars (params.getD i (.expr []))).filter (fun y => U.contains y)).map
          (bindNorm σ)).sum)).sum := by
    have hsub : U ⊆ (((List.range params.length).filter (fun i => Sf.contains i)).map
        (fun i => (patternVars (params.getD i (.expr []))).filter (fun y => U.contains y))).flatten := by
      intro y hy
      have hm := hUm y hy
      unfold measuredVar at hm
      obtain ⟨i, hiS, hi⟩ := List.any_eq_true.1 hm
      cases hp : params[i]? with
      | none => simp [hp] at hi
      | some p =>
        simp only [hp, List.contains_iff_mem] at hi
        have hlt : i < params.length := by
          by_contra hge
          rw [List.getElem?_eq_none (by omega)] at hp
          cases hp
        refine List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨i, ?_, rfl⟩, ?_⟩
        · simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
          exact ⟨hlt, hiS⟩
        · rw [List.getD_eq_getElem?_getD, hp, Option.getD_some]
          simp only [List.mem_filter, List.contains_iff_mem]
          exact ⟨hi, hy⟩
    have := sum_le_of_subperm (f := bindNorm σ) (hU.subperm hsub)
    rw [List.map_flatten, List.sum_flatten, List.map_map, List.map_map] at this
    exact this
  have hsum : sumAt vs Sf = (((List.range params.length).filter
      (fun i => Sf.contains i)).map (argNorm vs)).sum := by
    simp only [sumAt, positions, hlen]
  unfold slack
  rw [hsum]
  omega

/-! ## Weights bound calls -/

theorem costAt_bound {P : Program} {H : Host} {V : Vocabulary} (hK : Keeps V H)
    {params : List Term} {Sf : List Nat} {σ ρ : Env} {site : Site} (hI : Inv σ site.env ρ)
    {n : Nat} {ws : List Term}
    (hws : List.Forall₂ (fun t w => eval P H n ρ t = .value w) site.args ws) :
    ∀ (js : List Nat) (total : Nat) (uses : List String) (total' : Nat) (uses' : List String),
      (∀ j ∈ js, j < site.args.length) →
      costAt P V params Sf site js total uses = some (total', uses') →
      ∃ c, total' = total + c ∧ Claims params Sf σ uses uses' c ((js.map (argNorm ws)).sum)
  | [], total, uses, total', uses', _, h => by
    rw [costAt] at h
    cases h
    exact ⟨0, rfl, Claims.none (by simp)⟩
  | j :: js, total, uses, total', uses', hj, h => by
    rw [costAt] at h
    split at h
    · rename_i c₁ u₁ hc
      obtain ⟨c₂, hc₂, hcl⟩ := costAt_bound hK hI hws js (total + c₁) u₁ total' uses'
        (fun j' hj' => hj j' (List.mem_cons_of_mem _ hj')) h
      have hjl : j < site.args.length := hj j List.mem_cons_self
      have hcj := cost_bound hK hI n _ uses c₁ u₁ _ hc (Forall₂.getD hws hjl)
      refine ⟨c₁ + c₂, by omega, ?_⟩
      have := hcj.trans hcl
      simpa [argNorm] using this
    · cases h

/-- The weight of a site bounds the sum at the callee's positions of the
arguments it is called with by the caller's sum plus the weight. -/
theorem weigh_bound {P : Program} {H : Host} {V : Vocabulary} (hK : Keeps V H)
    {params vs : List Term} {σ ρ : Env} {Sf Sg : List Nat}
    (hmatch : matchTerms params vs = some σ) (hlin : (patternVarsList params).Nodup)
    (hmeas : ∀ i ∈ Sf, ∃ p, params[i]? = some p ∧ headed p = true)
    {site : Site} (hI : Inv σ site.env ρ) {n : Nat} {ws : List Term}
    (hws : evalItems P H n ρ site.args = .values ws) {w : Int}
    (hw : weigh P V params Sf Sg site = some w) :
    (sumAt ws Sg : Int) ≤ sumAt vs Sf + w := by
  have h2 := evalItemsWith_forall₂ hws
  have hlen := h2.length_eq
  unfold weigh at hw
  simp only at hw
  split at hw
  · rename_i total U hcost
    simp only [Option.some.injEq] at hw
    subst hw
    obtain ⟨c, hc, hcl⟩ := costAt_bound hK hI h2 _ 0 [] total U (by
      intro j hj
      simp only [List.mem_append, List.mem_filter, List.mem_range] at hj
      rcases hj with ⟨⟨h, _⟩, _⟩ | ⟨⟨h, _⟩, _⟩ <;> exact h) hcost
    obtain ⟨new, hU, hnd, hm, hb⟩ := hcl
    simp only [List.append_nil] at hU
    subst hU
    have hperm := List.filter_append_perm
      (fun j => (carried P V site.env (site.args.getD j (.expr []))).isSome)
      ((List.range site.args.length).filter (fun j => Sg.contains j))
    have hord := (hperm.map (argNorm ws)).sum_nat
    have hsg : sumAt ws Sg = (((List.range site.args.length).filter
        (fun j => Sg.contains j)).map (argNorm ws)).sum := by
      simp only [sumAt, positions, hlen]
    have hsl := slack_bound hmatch hlin hmeas hnd (fun y hy => (hm y hy).1)
    omega
  · cases hw

/-! ## Evaluations whose calls end -/

theorem applyWith_ends_of_not_defines {P : Program} {H : Host} {ev : Env → Term → Outcome}
    {f : String} {vs : List Term} (hd : P.definesAt f vs.length = false) :
    applyWith P H ev f vs ≠ .exhausted := by
  unfold applyWith
  rw [if_neg (by simp [hd])]
  split
  · simp
  · split <;> simp

theorem select_spec {P : Program} {f : String} {vs : List Term} {e : Equation} {σ : Env}
    (h : P.select f vs = some (e, σ)) :
    e ∈ P ∧ e.head = f ∧ matchTerms e.params vs = some σ := by
  unfold Program.select at h
  obtain ⟨e', he', h'⟩ := List.exists_of_findSome?_eq_some h
  split at h'
  · rename_i hc
    cases hm : matchTerms e'.params vs with
    | none => simp [hm] at h'
    | some σ' =>
      simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      exact ⟨he', hc.1, hm⟩
  · cases h'

theorem eval_items_ends {P : Program} {H : Host} {ρ : Env} {hd : Term} {items : List Term}
    (hh : ∀ s, hd ≠ .sym s) (hl : ∃ n, evalItems P H n ρ (hd :: items) ≠ .stop .exhausted) :
    ∃ n, eval P H n ρ (.expr (hd :: items)) ≠ .exhausted := by
  obtain ⟨n, hn⟩ := hl
  refine ⟨n + 1, ?_⟩
  rw [eval, evalStep_items hh]
  split
  · simp
  · rename_i o ho
    intro h
    subst h
    exact hn ho

section Ends

variable {P : Program} {H : Host} {V : Vocabulary}
  {Q : List Binder → Env → Prop} {R : Site → Prop}

/-- An evaluation ends when the calls of its sites end: `Q` is an invariant of
the static binders and the dynamic environment that `let`s keep, and every site
`R` admits calls, once its arguments have values, a call that ends. -/
theorem ends_of_calls
    (hQ : ∀ benv ρ x e v n, Q benv ρ → eval P H n ρ e = .value v →
      Q (⟨x, carried P V benv e⟩ :: benv) ((x, v) :: ρ))
    (hcall : ∀ benv ρ f args ws n, Q benv ρ → P.definesAt f args.length = true →
      R ⟨f, args, benv⟩ → evalItems P H n ρ args = .values ws →
      ∃ m, apply P H m f ws ≠ .exhausted) :
    ∀ (t : Term) (benv : List Binder) (ρ : Env), Q benv ρ →
      (∀ s ∈ sites P V benv t, R s) → ∃ n, eval P H n ρ t ≠ .exhausted := by
  intro t
  refine (InvImage.wf (sizeOf : Term → Nat) Nat.lt_wfRel.wf).induction
    (C := fun t => ∀ (benv : List Binder) (ρ : Env), Q benv ρ →
      (∀ s ∈ sites P V benv t, R s) → ∃ n, eval P H n ρ t ≠ .exhausted) t ?_
  intro t ih
  have hlist : ∀ (ts : List Term), sizeOf ts < sizeOf t → ∀ benv ρ, Q benv ρ →
      (∀ s ∈ sitesList P V benv ts, R s) → ∃ n, evalItems P H n ρ ts ≠ .stop .exhausted := by
    intro ts
    induction ts with
    | nil => exact fun _ _ _ _ _ => ⟨0, by simp only [evalItems, evalItemsWith]; intro h; cases h⟩
    | cons u us ihl =>
      intro hlt benv ρ hq hs
      rw [List.cons.sizeOf_spec] at hlt
      rw [sitesList.eq_2] at hs
      obtain ⟨n₁, hn₁⟩ := ih u (by show sizeOf u < sizeOf t; omega) benv ρ hq
        (fun s hsm => hs s (List.mem_append_left _ hsm))
      obtain ⟨n₂, hn₂⟩ := ihl (by omega) benv ρ hq
        (fun s hsm => hs s (List.mem_append_right _ hsm))
      refine ⟨max n₁ n₂, ?_⟩
      have h2 := evalItems_le (le_max_right n₁ n₂) hn₂
      simp only [evalItems] at h2 hn₂ ⊢
      simp only [evalItemsWith]
      rw [eval_le (le_max_left n₁ n₂) hn₁]
      split
      · rw [h2]
        split
        · intro h
          cases h
        · rename_i o ho
          intro h
          cases h
          exact hn₂ ho
      · intro h
        injection h with h
        exact hn₁ h
  intro benv ρ hq hs
  cases t with
  | var x => exact ⟨1, by
      simp only [eval, evalStep]
      split <;> (intro h; cases h)⟩
  | sym _ => exact ⟨1, by simp only [eval, evalStep]; intro h; cases h⟩
  | lit _ => exact ⟨1, by simp only [eval, evalStep]; intro h; cases h⟩
  | list items =>
    obtain ⟨n, hn⟩ := hlist items (by rw [Term.list.sizeOf_spec]; omega) benv ρ hq (by
      intro s hsm
      exact hs s (by rw [sites.eq_7]; exact hsm))
    refine ⟨n + 1, ?_⟩
    simp only [eval, evalStep]
    split
    · intro h
      cases h
    · rename_i o ho
      intro h
      subst h
      exact hn ho
  | expr items =>
    cases items with
    | nil => exact ⟨1, by simp only [eval, evalStep]; intro h; cases h⟩
    | cons hd args =>
      have hsz : sizeOf args < sizeOf (Term.expr (hd :: args)) := by
        rw [Term.expr.sizeOf_spec, List.cons.sizeOf_spec]
        omega
      cases hd with
      | sym f =>
        by_cases hsp : Special f args
        · rcases hsp with ⟨rfl, hl⟩ | ⟨rfl, hl⟩
          · obtain ⟨b, e, body, rfl⟩ := List.length_eq_three.1 hl
            have hse : sizeOf e < sizeOf (Term.expr [.sym "let", b, e, body]) := by
              simp only [Term.expr.sizeOf_spec, List.cons.sizeOf_spec]
              omega
            have hsb : sizeOf body < sizeOf (Term.expr [.sym "let", b, e, body]) := by
              simp only [Term.expr.sizeOf_spec, List.cons.sizeOf_spec]
              omega
            by_cases hb : ∃ x, b = .var x
            · obtain ⟨x, rfl⟩ := hb
              rw [sites.eq_2] at hs
              obtain ⟨n₁, hn₁⟩ := ih e hse benv ρ hq
                (fun s hsm => hs s (List.mem_append_left _ hsm))
              cases hev : eval P H n₁ ρ e with
              | value v =>
                obtain ⟨n₂, hn₂⟩ := ih body hsb _ _ (hQ benv ρ x e v n₁ hq hev)
                  (fun s hsm => hs s (List.mem_append_right _ hsm))
                refine ⟨max n₁ n₂ + 1, ?_⟩
                rw [eval, evalStep.eq_6, eval_le (le_max_left n₁ n₂) hn₁, hev]
                simp only []
                rw [eval_le (le_max_right n₁ n₂) hn₂]
                exact hn₂
              | failure =>
                refine ⟨n₁ + 1, ?_⟩
                rw [eval, evalStep.eq_6, hev]
                intro h
                cases h
              | exhausted => exact absurd hev hn₁
            · refine ⟨1, ?_⟩
              rw [eval, evalStep.eq_7 _ _ _ _ _ _ (fun x h => hb ⟨x, h⟩)]
              intro h
              cases h
          · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hl
            refine ⟨1, ?_⟩
            by_cases ha : ∃ s, a = .sym s
            · obtain ⟨s, rfl⟩ := ha
              rw [eval, evalStep.eq_8]
              intro h
              cases h
            · rw [eval, evalStep.eq_9 _ _ _ _ (fun s h => ha ⟨s, h⟩)]
              intro h
              cases h
        · rw [sites.eq_5 P V benv f args
            (fun b e body h1 h2 => hsp (Or.inl ⟨h2, by rw [h1]; rfl⟩))
            (fun a h1 h2 => hsp (Or.inr ⟨h2, by rw [h1]; rfl⟩))] at hs
          obtain ⟨n₁, hn₁⟩ := hlist args hsz benv ρ hq
            (fun s hsm => hs s (List.mem_append_right _ hsm))
          cases hev : evalItems P H n₁ ρ args with
          | stop o =>
            refine ⟨n₁ + 1, ?_⟩
            rw [eval, evalStep_head hsp]
            simp only [evalItems] at hev hn₁
            rw [hev]
            intro h
            subst h
            exact hn₁ hev
          | values ws =>
            have hlen := (evalItemsWith_forall₂ hev).length_eq
            by_cases hdef : P.definesAt f args.length = true
            · obtain ⟨n₂, hn₂⟩ := hcall benv ρ f args ws n₁ hq hdef
                (hs _ (List.mem_append_left _ (by rw [if_pos hdef]; exact List.mem_singleton_self _)))
                hev
              refine ⟨max n₁ n₂ + 1, ?_⟩
              have h1 := evalItems_le (le_max_left n₁ n₂) hn₁
              have h2 := apply_le (le_max_right n₁ n₂) hn₂
              simp only [evalItems, apply] at h1 h2 hev hn₂
              rw [eval, evalStep_head hsp, h1, hev]
              simp only []
              rw [h2]
              exact hn₂
            · refine ⟨n₁ + 1, ?_⟩
              rw [eval, evalStep_head hsp]
              simp only [evalItems] at hev
              rw [hev]
              exact applyWith_ends_of_not_defines (by
                rw [← hlen]
                cases h : P.definesAt f args.length
                · rfl
                · exact absurd h hdef)
      | var x =>
        refine eval_items_ends (fun s h => Term.noConfusion h) (hlist _ ?_ benv ρ hq ?_)
        · rw [Term.expr.sizeOf_spec]
          omega
        · intro s hsm
          exact hs s (by
            rw [sites.eq_6 _ _ _ _ (List.cons_ne_nil _ _)
              (fun _ _ _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ _ h => Term.noConfusion (List.cons.inj h).1)]
            exact hsm)
      | lit x =>
        refine eval_items_ends (fun s h => Term.noConfusion h) (hlist _ ?_ benv ρ hq ?_)
        · rw [Term.expr.sizeOf_spec]
          omega
        · intro s hsm
          exact hs s (by
            rw [sites.eq_6 _ _ _ _ (List.cons_ne_nil _ _)
              (fun _ _ _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ _ h => Term.noConfusion (List.cons.inj h).1)]
            exact hsm)
      | expr x =>
        refine eval_items_ends (fun s h => Term.noConfusion h) (hlist _ ?_ benv ρ hq ?_)
        · rw [Term.expr.sizeOf_spec]
          omega
        · intro s hsm
          exact hs s (by
            rw [sites.eq_6 _ _ _ _ (List.cons_ne_nil _ _)
              (fun _ _ _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ _ h => Term.noConfusion (List.cons.inj h).1)]
            exact hsm)
      | list x =>
        refine eval_items_ends (fun s h => Term.noConfusion h) (hlist _ ?_ benv ρ hq ?_)
        · rw [Term.expr.sizeOf_spec]
          omega
        · intro s hsm
          exact hs s (by
            rw [sites.eq_6 _ _ _ _ (List.cons_ne_nil _ _)
              (fun _ _ _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ h => Term.noConfusion (List.cons.inj h).1)
              (fun _ _ h => Term.noConfusion (List.cons.inj h).1)]
            exact hsm)

end Ends

/-! ## Descending programs end -/

/-- Under a program with a descent certificate and a host that keeps its
vocabulary's promises, every call ends. -/
theorem apply_terminates {P : Program} {H : Host} {V : Vocabulary} {c : Certificate}
    (hD : Descends P V c) (hK : Keeps V H) (f : String) (vs : List Term) :
    ∃ n, apply P H n f vs ≠ .exhausted := by
  have hwf : WellFounded (fun a b : String × List Term =>
      LexLt (measure c a.1 a.2) (measure c b.1 b.2)) :=
    InvImage.wf (fun a : String × List Term =>
      (⟨measure c a.1 a.2, measure_length c a.1 a.2⟩ :
        {l : List Nat // l.length = c.levels.length})) (lexLt_wf c.levels.length)
  refine hwf.induction (C := fun a => ∃ n, apply P H n a.1 a.2 ≠ .exhausted) (f, vs) ?_
  rintro ⟨f, vs⟩ ih
  by_cases hdef : P.definesAt f vs.length = true
  · cases hsel : P.select f vs with
    | none => exact ⟨0, by simp [apply, applyWith, hdef, hsel]⟩
    | some es =>
      obtain ⟨e, σ⟩ := es
      obtain ⟨he, hhead, hmatch⟩ := select_spec hsel
      have hlin := hD.1 e he
      obtain ⟨n, hn⟩ := ends_of_calls (P := P) (H := H) (V := V)
        (Q := fun benv ρ => Inv σ benv ρ) (R := fun s => decides P V e s c.levels = true)
        (fun benv ρ x e' v n hq hev => hq.extend x v _
          (fun y hy => carried_bound hK hq n e' y v hy hev))
        (fun benv ρ g args ws n hq _ hr hev => by
          have hlex := lexLt_of_decides P V e ⟨g, args, benv⟩ ws vs c.levels hr
            (fun l hl w hw => weigh_bound hK hmatch hlin (hD.2.1 l hl e he) hq hev hw)
          have hlen := (evalItemsWith_forall₂ hev).length_eq
          refine ih (g, ws) ?_
          show LexLt (measure c g ws) (measure c f vs)
          unfold measure
          rw [← hlen, ← matchTerms_length hmatch, ← hhead]
          exact hlex)
        e.body [] σ (Inv.init σ) (hD.2.2 e he)
      refine ⟨n, ?_⟩
      simp only [apply, applyWith, hdef, if_true, hsel]
      exact hn
  · exact ⟨0, applyWith_ends_of_not_defines (by simpa using hdef)⟩

/-- Under a program with a descent certificate and a host that keeps its
vocabulary's promises, the evaluation of every term ends. -/
theorem eval_terminates {P : Program} {H : Host} {V : Vocabulary} {c : Certificate}
    (hD : Descends P V c) (hK : Keeps V H) (t : Term) (ρ : Env) :
    ∃ n, eval P H n ρ t ≠ .exhausted :=
  ends_of_calls (P := P) (H := H) (V := V) (Q := fun _ _ => True) (R := fun _ => True)
    (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ f _ ws _ _ _ _ _ => apply_terminates hD hK f ws) t [] ρ trivial
    (fun _ _ => trivial)

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
