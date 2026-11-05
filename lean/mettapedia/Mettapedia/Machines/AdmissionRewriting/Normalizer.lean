import Mettapedia.Machines.AdmissionRewriting.Syntax

/-!
# The admission normalizer: one bottom-up pass, invariant under every step

`N Γ` normalizes children first, then applies the root rules once to the rebuilt node
(`mkLet`, `mkCall`, `mkSup`, `mkCase`, and the `once` wrapper).  The root rebuilders
already contain the completion rules: `mkLet` applies `sizeVar` and `letEta`, and every
`once` is wrapped, the wrapper being dissolved by `letEta` wherever the `once` ends up as a
`let` source.

This file proves:
* `step_N`: a step never changes the normal form (this is where every critical pair of
  `Syntax` is joined);
* `reduces`: every term rewrites to its normal form (`Step true`), and a `let` source
  rewrites to it up to the wrapper (`reduces_flag`);
* `confluent`, `canonical`, `normalForm_unique`: rewriting is confluent, convertible terms
  share one normal form, and a term's irreducible reducts are all its normal form.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting

open Relation

/-- A `let` at the root, with `sizeVar` and `letEta` applied. -/
def mkLet : Tm → Tm → Tm
  | .var j, .call .size [.var 0] => .call .size [.var j]
  | .let_ e (.var 0), b => mkLet e b
  | e, b => .let_ e b

/-- A strict call at the root, with `id`, `size` and `min` applied. -/
def mkCall (Γ : Facts) : Name → List Tm → Tm
  | .id, [x] => x
  | .size, [e] => mkLet e (.call .size [.var 0])
  | .min, [a, b] =>
    if IntAtom Γ a && IntAtom Γ b then .if3 (.call .lt [a, b]) a b else .call .min [a, b]
  | f, args => .call f args

/-- A `superpose` at the root, with `sup1` applied. -/
def mkSup : List Tm → Tm
  | [x] => x
  | xs => .sup xs

/-- A `case` at the root, with `case1` applied. -/
def mkCase : Tm → List (Pat × Tm) → Tm
  | e, [(.bind, b)] => mkLet e b
  | e, alts => .case_ e alts

mutual
/-- The normalizer. -/
def N (Γ : Facts) : Tm → Tm
  | .var k => .var k
  | .lit l => .lit l
  | .quote t => .quote t
  | .tup xs => .tup (Ns Γ xs)
  | .empty => .empty
  | .if3 c t e => .if3 (N Γ c) (N Γ t) (N Γ e)
  | .if2 c t => .if3 (N Γ c) (N Γ t) .empty
  | .let_ e b => mkLet (N Γ e) (N (push Γ) b)
  | .letStar es b => NLS Γ es (fun Γ' => N Γ' b)
  | .case_ e alts => mkCase (N Γ e) (NAlts Γ alts)
  | .sup xs => mkSup (Ns Γ xs)
  | .once b => .let_ (.once (N Γ b)) (.var 0)
  | .call f args => mkCall Γ f (Ns Γ args)
  | .iterC k ops f => .iterB k (Ns Γ ops) (mkCall (pushN k.binders Γ) f k.vars)
  | .iterB k ops b => .iterB k (Ns Γ ops) (N (pushN k.binders Γ) b)
/-- The normalizer on a list of terms at one depth. -/
def Ns (Γ : Facts) : List Tm → List Tm
  | [] => []
  | x :: xs => N Γ x :: Ns Γ xs
/-- The normalizer on branches. -/
def NAlts (Γ : Facts) : List (Pat × Tm) → List (Pat × Tm)
  | [] => []
  | (p, b) :: rest => (p, N (p.scope Γ) b) :: NAlts Γ rest
/-- The normalizer on `let*` sources, each one binder deeper, closed by `kb`. -/
def NLS (Γ : Facts) : List Tm → (Facts → Tm) → Tm
  | [], kb => kb Γ
  | e :: es, kb => mkLet (N Γ e) (NLS (push Γ) es kb)
end

/-! ## Algebra of the rebuilders -/

theorem Ns_eq_map (Γ : Facts) (xs : List Tm) : Ns Γ xs = xs.map (N Γ) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Ns, ih]

theorem Ns_append (Γ : Facts) (xs ys : List Tm) : Ns Γ (xs ++ ys) = Ns Γ xs ++ Ns Γ ys := by
  simp [Ns_eq_map]

theorem NAlts_eq_map (Γ : Facts) (alts : List (Pat × Tm)) :
    NAlts Γ alts = alts.map (fun a => (a.1, N (a.1.scope Γ) a.2)) := by
  induction alts with
  | nil => rfl
  | cons a alts ih => obtain ⟨p, b⟩ := a; simp [NAlts, ih]

theorem NAlts_append (Γ : Facts) (xs ys : List (Pat × Tm)) :
    NAlts Γ (xs ++ ys) = NAlts Γ xs ++ NAlts Γ ys := by
  simp [NAlts_eq_map]

theorem NLS_append (Γ : Facts) (pre rest : List Tm) (kb : Facts → Tm) :
    NLS Γ (pre ++ rest) kb = NLS Γ pre (fun Γ' => NLS Γ' rest kb) := by
  induction pre generalizing Γ with
  | nil => rfl
  | cons e pre ih => simp only [List.cons_append, NLS, ih]

theorem pushN_succ (n : ℕ) (Γ : Facts) : pushN (n + 1) Γ = pushN n (push Γ) := rfl

theorem NLS_congr_kb (Γ : Facts) (es : List Tm) (k₁ k₂ : Facts → Tm)
    (h : k₁ (pushN es.length Γ) = k₂ (pushN es.length Γ)) : NLS Γ es k₁ = NLS Γ es k₂ := by
  induction es generalizing Γ with
  | nil => exact h
  | cons e es ih => simp only [NLS]; rw [ih (push Γ) h]

theorem N_nest (Γ : Facts) (es : List Tm) (b : Tm) :
    N Γ (nest es b) = NLS Γ es (fun Γ' => N Γ' b) := by
  induction es generalizing Γ with
  | nil => rfl
  | cons e es ih => simp only [nest, N, NLS, ih]

theorem Ns_vars (Γ : Facts) (k : Iter) : Ns Γ k.vars = k.vars := by
  cases k <;> rfl

theorem N_of_intAtom {Γ : Facts} {a : Tm} (h : IntAtom Γ a = true) (Γ' : Facts) : N Γ' a = a := by
  cases a with
  | var k => rfl
  | lit l => rfl
  | _ => simp [IntAtom] at h

theorem mkLet_var_size (j : ℕ) : mkLet (.var j) (.call .size [.var 0]) = .call .size [.var j] := by
  simp [mkLet]

theorem mkLet_letEta (e b : Tm) : mkLet (.let_ e (.var 0)) b = mkLet e b := by
  simp [mkLet]

/-- `mkLet` of a source that is neither a variable nor an eta-`let` is a plain `let`. -/
theorem mkLet_plain (e b : Tm) (hv : ∀ j, e ≠ .var j) (hl : ∀ e', e ≠ .let_ e' (.var 0)) :
    mkLet e b = .let_ e b := by
  unfold mkLet
  split
  · exact absurd rfl (hv _)
  · exact absurd rfl (hl _)
  · rfl

theorem mkLet_var_of_ne (j : ℕ) (b : Tm) (hb : b ≠ .call .size [.var 0]) :
    mkLet (.var j) b = .let_ (.var j) b := by
  unfold mkLet
  split <;> simp_all

/-- The wrapper of an eta-`let` source dissolves. -/
theorem mkLet_eta : ∀ (x b : Tm), mkLet (mkLet x (.var 0)) b = mkLet x b
  | .var j, b => by rw [mkLet_var_of_ne j (.var 0) (by simp), mkLet_letEta]
  | .let_ e c, b => by
    by_cases hc : c = .var 0
    · subst hc; rw [mkLet_letEta, mkLet_letEta, mkLet_eta e b]
    · rw [mkLet_plain (.let_ e c) (.var 0) (by simp) (by simp [hc]), mkLet_letEta]
  | .lit _, b | .quote _, b | .tup _, b | .empty, b | .if3 _ _ _, b | .if2 _ _, b
  | .letStar _ _, b | .case_ _ _, b | .sup _, b | .once _, b | .call _ _, b
  | .iterC _ _ _, b | .iterB _ _ _, b => by
    rw [mkLet_plain _ (.var 0) (by simp) (by simp), mkLet_letEta]

/-! ## Invariance under steps -/

theorem rule_N {Γ : Facts} {t t' : Tm} (h : Rule Γ t t') : N Γ t = N Γ t' := by
  cases h with
  | if2 c t => rfl
  | letStar es b => rw [N_nest]; rfl
  | case1 e b => simp [N, NAlts, mkCase, Pat.scope]
  | id => simp [N, Ns, mkCall]
  | sup1 => simp [N, Ns, mkSup]
  | callable k ops f => simp only [N]; rw [Ns_vars]
  | size e he =>
    simp only [N, Ns, mkCall]
    rw [mkLet_var_size]
  | min a b ha hb =>
    simp only [N, Ns, mkCall, N_of_intAtom ha, N_of_intAtom hb, ha, hb, Bool.and_self,
      if_true]
  | sizeVar j => simp only [N, Ns, mkCall]; rw [mkLet_var_size, mkLet_var_size]
  | letEta e b => simp only [N]; exact mkLet_eta _ _

/-- A step never changes the normal form. -/
theorem step_N {top : Bool} {Γ : Facts} {t t' : Tm} (h : Step top Γ t t') : N Γ t = N Γ t' := by
  induction h with
  | rule r => exact rule_N r
  | wrap b =>
    simp only [N]
    rw [mkLet_letEta, mkLet_plain _ _ (by simp) (by simp)]
  | tup pre post _ ih => simp only [N, Ns_append, Ns, ih]
  | if3c t e _ ih => simp only [N, ih]
  | if3t c e _ ih => simp only [N, ih]
  | if3e c t _ ih => simp only [N, ih]
  | if2c t _ ih => simp only [N, ih]
  | if2t c _ ih => simp only [N, ih]
  | letE b _ ih => simp only [N, ih]
  | letB e _ ih => simp only [N, ih]
  | letStarE pre post b _ ih =>
    simp only [N, NLS_append]
    apply NLS_congr_kb
    simp only [NLS, ih]
  | letStarB es _ ih =>
    simp only [N]
    exact NLS_congr_kb _ _ _ _ ih
  | caseE alts _ ih => simp only [N, ih]
  | caseB e pre post p _ ih => simp only [N, NAlts_append, NAlts, ih]
  | sup pre post _ ih => simp only [N, Ns_append, Ns, ih]
  | once _ ih => simp only [N, ih]
  | call f pre post _ ih => simp only [N, Ns_append, Ns, ih]
  | iterCOps k pre post f _ ih => simp only [N, Ns_append, Ns, ih]
  | iterBOps k pre post b _ ih => simp only [N, Ns_append, Ns, ih]
  | iterBBody k ops _ ih => simp only [N, ih]

theorem star_N {top : Bool} {Γ : Facts} {t t' : Tm} (h : ReflTransGen (Step top Γ) t t') :
    N Γ t = N Γ t' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, step_N hs]

/-! ## Every term rewrites to its normal form -/

theorem pushN_succ' (n : ℕ) (Γ : Facts) : pushN (n + 1) Γ = push (pushN n Γ) := by
  induction n generalizing Γ with
  | zero => rfl
  | succ n ih => rw [pushN_succ, ih, ← pushN_succ]

/-- `let` sources normalized at their depths. -/
def NsD : Facts → List Tm → List Tm
  | _, [] => []
  | Γ, e :: es => N Γ e :: NsD (push Γ) es

/-- Nested `mkLet`s. -/
def mkLetChain : List Tm → Tm → Tm
  | [], b => b
  | x :: xs, b => mkLet x (mkLetChain xs b)

theorem NLS_eq (Γ : Facts) (es : List Tm) (kb : Facts → Tm) :
    NLS Γ es kb = mkLetChain (NsD Γ es) (kb (pushN es.length Γ)) := by
  induction es generalizing Γ with
  | nil => rfl
  | cons e es ih => simp only [NLS, NsD, mkLetChain, ih, List.length_cons, pushN_succ]

theorem NsD_length (Γ : Facts) (es : List Tm) : (NsD Γ es).length = es.length := by
  induction es generalizing Γ with
  | nil => rfl
  | cons e es ih => simp [NsD, ih]

/-- The normal form a position reaches: at a `let` source a `once` is not wrapped. -/
def Nflag : Bool → Facts → Tm → Tm
  | false, Γ, .once b => .once (N Γ b)
  | _, Γ, t => N Γ t

theorem Nflag_true (Γ : Facts) (t : Tm) : Nflag true Γ t = N Γ t := by
  simp [Nflag]

theorem Nflag_of_ne (top : Bool) (Γ : Facts) (t : Tm) (h : ∀ b, t ≠ .once b) :
    Nflag top Γ t = N Γ t := by
  unfold Nflag
  split
  · exact absurd rfl (h _)
  · rfl

theorem mkLet_Nflag (top : Bool) (Γ : Facts) (e B : Tm) :
    mkLet (Nflag top Γ e) B = mkLet (N Γ e) B := by
  cases top
  · cases e with
    | once b =>
      simp only [Nflag, N]
      rw [mkLet_letEta]
    | _ => rfl
  · rw [Nflag_true]

theorem star_single {top : Bool} {Γ : Facts} {a b : Tm} (h : Step top Γ a b) :
    ReflTransGen (Step top Γ) a b := ReflTransGen.single h

/-- Reductions lift through a context. -/
theorem star_map {r p : Tm → Tm → Prop} (f : Tm → Tm) (h : ∀ a b, r a b → p (f a) (f b))
    {a b : Tm} (hab : ReflTransGen r a b) : ReflTransGen p (f a) (f b) :=
  ReflTransGen.lift f h a b hab

/-- `mkLet` is realized by root steps. -/
theorem mkLet_reduces (top : Bool) (Γ : Facts) :
    ∀ (x B : Tm), ReflTransGen (Step top Γ) (.let_ x B) (mkLet x B)
  | .var j, B => by
    by_cases hB : B = .call .size [.var 0]
    · subst hB; rw [mkLet_var_size]; exact star_single (.rule (.sizeVar j))
    · rw [mkLet_var_of_ne j B hB]
  | .let_ e c, B => by
    by_cases hc : c = .var 0
    · subst hc
      rw [mkLet_letEta]
      exact (star_single (.rule (.letEta e B))).trans (mkLet_reduces top Γ e B)
    · rw [mkLet_plain (.let_ e c) B (by simp) (by simp [hc])]
  | .lit _, B | .quote _, B | .tup _, B | .empty, B | .if3 _ _ _, B | .if2 _ _, B
  | .letStar _ _, B | .case_ _ _, B | .sup _, B | .once _, B | .call _ _, B
  | .iterC _ _ _, B | .iterB _ _ _, B => by
    rw [mkLet_plain _ B (by simp) (by simp)]

/-- `mkCall` is realized by root steps. -/
theorem mkCall_reduces (top : Bool) (Γ : Facts) (f : Name) (args : List Tm) :
    ReflTransGen (Step top Γ) (.call f args) (mkCall Γ f args) := by
  unfold mkCall
  split
  · exact star_single (.rule (.id _))
  · rename_i e
    by_cases he : ∃ j, e = .var j
    · obtain ⟨j, rfl⟩ := he; rw [mkLet_var_size]
    · simp only [not_exists] at he
      exact (star_single (.rule (.size e he))).trans (mkLet_reduces top Γ e _)
  · rename_i a b
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact star_single (.rule (.min a b h.1 h.2))
    · exact .refl
  · exact .refl

theorem mkSup_reduces (top : Bool) (Γ : Facts) (xs : List Tm) :
    ReflTransGen (Step top Γ) (.sup xs) (mkSup xs) := by
  unfold mkSup
  split
  · exact star_single (.rule (.sup1 _))
  · exact .refl

theorem mkCase_reduces (top : Bool) (Γ : Facts) (e : Tm) (alts : List (Pat × Tm)) :
    ReflTransGen (Step top Γ) (.case_ e alts) (mkCase e alts) := by
  unfold mkCase
  split
  · exact (star_single (.rule (.case1 _ _))).trans (mkLet_reduces top Γ _ _)
  · exact .refl

theorem nest_reduces (top : Bool) :
    ∀ (Γ : Facts) (xs : List Tm) (B : Tm), ReflTransGen (Step top Γ) (nest xs B) (mkLetChain xs B)
  | Γ, [], B => .refl
  | Γ, x :: xs, B => by
    simp only [nest, mkLetChain]
    have h1 : ReflTransGen (Step top Γ) (.let_ x (nest xs B)) (.let_ x (mkLetChain xs B)) :=
      star_map (fun y => Tm.let_ x y) (fun _ _ h => .letB x h.toTrue)
        (nest_reduces true (push Γ) xs B)
    exact h1.trans (mkLet_reduces top Γ x _)

/-- A list position: reductions of the elements lift to the list node. -/
theorem star_list {top : Bool} {Γ Γx : Facts} (C : List Tm → Tm)
    (hC : ∀ (pre post : List Tm) (x x' : Tm), Step true Γx x x' →
      Step top Γ (C (pre ++ x :: post)) (C (pre ++ x' :: post)))
    (f : Tm → Tm) :
    ∀ (pre xs : List Tm), (∀ x ∈ xs, ReflTransGen (Step true Γx) x (f x)) →
      ReflTransGen (Step top Γ) (C (pre ++ xs)) (C (pre ++ xs.map f))
  | pre, [], _ => by simpa using ReflTransGen.refl
  | pre, x :: xs, h => by
    have h1 : ReflTransGen (Step top Γ) (C (pre ++ x :: xs)) (C (pre ++ f x :: xs)) :=
      star_map (fun y => C (pre ++ y :: xs)) (fun a b hab => hC pre xs a b hab)
        (h x (by simp))
    have h2 := star_list C hC f (pre ++ [f x]) xs (fun y hy => h y (by simp [hy]))
    simp only [List.append_assoc, List.singleton_append] at h2
    simpa using h1.trans h2

/-- Branch bodies: reductions lift to the `case` node. -/
theorem star_alts {top : Bool} {Γ : Facts} (e : Tm) :
    ∀ (pre alts : List (Pat × Tm)),
      (∀ a ∈ alts, ReflTransGen (Step true (a.1.scope Γ)) a.2 (N (a.1.scope Γ) a.2)) →
      ReflTransGen (Step top Γ) (.case_ e (pre ++ alts)) (.case_ e (pre ++ NAlts Γ alts))
  | pre, [], _ => by simpa [NAlts] using ReflTransGen.refl
  | pre, (p, b) :: alts, h => by
    have h1 : ReflTransGen (Step top Γ) (.case_ e (pre ++ (p, b) :: alts))
        (.case_ e (pre ++ (p, N (p.scope Γ) b) :: alts)) :=
      star_map (fun y => Tm.case_ e (pre ++ (p, y) :: alts))
        (fun a b hab => .caseB e pre alts p hab) (h (p, b) (by simp))
    have h2 := star_alts (top := top) (Γ := Γ) e (pre ++ [(p, N (p.scope Γ) b)]) alts (fun a ha => h a (by simp [ha]))
    simp only [List.append_assoc, List.singleton_append] at h2
    simpa [NAlts] using h1.trans h2

/-- `let*` sources: reductions at their depths lift to the `let*` node. -/
theorem star_ls {top : Bool} {Γ0 : Facts} (b : Tm) :
    ∀ (Γ : Facts) (pre es : List Tm), pushN pre.length Γ0 = Γ →
      (∀ (i : ℕ) (hi : i < es.length),
        ReflTransGen (Step true (pushN i Γ)) es[i] (N (pushN i Γ) es[i])) →
      ReflTransGen (Step top Γ0) (.letStar (pre ++ es) b) (.letStar (pre ++ NsD Γ es) b)
  | Γ, pre, [], _, _ => by simpa [NsD] using ReflTransGen.refl
  | Γ, pre, e :: es, hΓ, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, pushN] at h0
    have h1 : ReflTransGen (Step top Γ0) (.letStar (pre ++ e :: es) b)
        (.letStar (pre ++ N Γ e :: es) b) :=
      star_map (fun y => Tm.letStar (pre ++ y :: es) b)
        (fun x x' hx => .letStarE pre es b (by rw [hΓ]; exact hx)) h0
    have h2 := star_ls (top := top) (Γ0 := Γ0) b (push Γ) (pre ++ [N Γ e]) es
      (by simp [pushN_succ', hΓ])
      (fun i hi => by
        have := h (i + 1) (by simp; omega)
        simpa [pushN_succ] using this)
    simp only [List.append_assoc, List.singleton_append] at h2
    simpa [NsD] using h1.trans h2

mutual
/-- Every term rewrites to its normal form; a `let` source, up to the `once` wrapper. -/
theorem reduces_flag : ∀ (top : Bool) (Γ : Facts) (t : Tm),
    ReflTransGen (Step top Γ) t (Nflag top Γ t)
  | top, Γ, .var k => by rw [Nflag_of_ne top Γ _ (by simp)]; exact .refl
  | top, Γ, .lit l => by rw [Nflag_of_ne top Γ _ (by simp)]; exact .refl
  | top, Γ, .quote t => by rw [Nflag_of_ne top Γ _ (by simp)]; exact .refl
  | top, Γ, .empty => by rw [Nflag_of_ne top Γ _ (by simp)]; exact .refl
  | top, Γ, .tup xs => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    simp only [N, Ns_eq_map]
    simpa using star_list (top := top) (Γ := Γ) (Γx := Γ) Tm.tup
      (fun pre post x x' h => .tup pre post h) (N Γ) [] xs (reduces_list Γ xs)
  | top, Γ, .if3 c t e => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have hc := star_map (fun y => Tm.if3 y t e)
      (fun _ _ h => Step.if3c (top := top) (Γ := Γ) t e h) (by simpa [Nflag_true] using reduces_flag true Γ c)
    have ht := star_map (fun y => Tm.if3 (N Γ c) y e)
      (fun _ _ h => Step.if3t (top := top) (Γ := Γ) (N Γ c) e h)
      (by simpa [Nflag_true] using reduces_flag true Γ t)
    have he := star_map (fun y => Tm.if3 (N Γ c) (N Γ t) y)
      (fun _ _ h => Step.if3e (top := top) (Γ := Γ) (N Γ c) (N Γ t) h)
      (by simpa [Nflag_true] using reduces_flag true Γ e)
    exact (hc.trans ht).trans he
  | top, Γ, .if2 c t => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have hc := star_map (fun y => Tm.if2 y t)
      (fun _ _ h => Step.if2c (top := top) (Γ := Γ) t h) (by simpa [Nflag_true] using reduces_flag true Γ c)
    have ht := star_map (fun y => Tm.if2 (N Γ c) y)
      (fun _ _ h => Step.if2t (top := top) (Γ := Γ) (N Γ c) h)
      (by simpa [Nflag_true] using reduces_flag true Γ t)
    exact (hc.trans ht).trans (star_single (.rule (.if2 _ _)))
  | top, Γ, .let_ e b => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have he := star_map (fun y => Tm.let_ y b)
      (fun _ _ h => Step.letE (top := top) (Γ := Γ) b h) (reduces_flag false Γ e)
    have hb := star_map (fun y => Tm.let_ (Nflag false Γ e) y)
      (fun _ _ h => Step.letB (top := top) (Γ := Γ) (Nflag false Γ e) h)
      (by simpa [Nflag_true] using reduces_flag true (push Γ) b)
    have hl := mkLet_reduces top Γ (Nflag false Γ e) (N (push Γ) b)
    rw [mkLet_Nflag] at hl
    exact (he.trans hb).trans hl
  | top, Γ, .letStar es b => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have hs := star_ls (top := top) (Γ0 := Γ) b Γ [] es rfl (reduces_ls Γ es)
    have hb := star_map (fun y => Tm.letStar (NsD Γ es) y)
      (fun _ _ h => Step.letStarB (top := top) (Γ := Γ) (NsD Γ es) h)
      (by simpa [Nflag_true, NsD_length] using reduces_flag true (pushN es.length Γ) b)
    have hn := nest_reduces top Γ (NsD Γ es) (N (pushN es.length Γ) b)
    simp only [List.nil_append] at hs
    simp only [N, NLS_eq]
    exact ((hs.trans hb).trans (star_single (.rule (.letStar _ _)))).trans hn
  | top, Γ, .case_ e alts => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have he := star_map (fun y => Tm.case_ y alts)
      (fun _ _ h => Step.caseE (top := top) (Γ := Γ) alts h)
      (by simpa [Nflag_true] using reduces_flag true Γ e)
    have ha := star_alts (top := top) (Γ := Γ) (N Γ e) [] alts (reduces_alts Γ alts)
    simp only [List.nil_append] at ha
    exact (he.trans ha).trans (mkCase_reduces top Γ _ _)
  | top, Γ, .sup xs => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have hx : ReflTransGen (Step top Γ) (.sup xs) (.sup (Ns Γ xs)) := by
      rw [Ns_eq_map]
      simpa using star_list (top := top) (Γ := Γ) (Γx := Γ) Tm.sup
        (fun pre post x x' h => .sup pre post h) (N Γ) [] xs (reduces_list Γ xs)
    exact hx.trans (mkSup_reduces top Γ _)
  | top, Γ, .once b => by
    have hb : ReflTransGen (Step top Γ) (.once b) (.once (N Γ b)) :=
      star_map (fun y => Tm.once y) (fun _ _ h => Step.once (top := top) (Γ := Γ) h)
        (by simpa [Nflag_true] using reduces_flag true Γ b)
    cases top
    · simpa [Nflag] using hb
    · simp only [Nflag_true, N]
      exact hb.trans (star_single (.wrap _))
  | top, Γ, .call f args => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have hx : ReflTransGen (Step top Γ) (.call f args) (.call f (Ns Γ args)) := by
      rw [Ns_eq_map]
      simpa using star_list (top := top) (Γ := Γ) (Γx := Γ) (Tm.call f)
        (fun pre post x x' h => .call f pre post h) (N Γ) [] args (reduces_list Γ args)
    exact hx.trans (mkCall_reduces top Γ f _)
  | top, Γ, .iterC k ops f => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have hx : ReflTransGen (Step top Γ) (.iterC k ops f) (.iterC k (Ns Γ ops) f) := by
      rw [Ns_eq_map]
      simpa using star_list (top := top) (Γ := Γ) (Γx := Γ) (fun ys => Tm.iterC k ys f)
        (fun pre post x x' h => .iterCOps k pre post f h) (N Γ) [] ops (reduces_list Γ ops)
    have hc := star_map (fun y => Tm.iterB k (Ns Γ ops) y)
      (fun _ _ h => Step.iterBBody (top := top) (Γ := Γ) k (Ns Γ ops) h)
      (mkCall_reduces true (pushN k.binders Γ) f k.vars)
    exact (hx.trans (star_single (.rule (.callable _ _ _)))).trans hc
  | top, Γ, .iterB k ops b => by
    rw [Nflag_of_ne top Γ _ (by simp)]
    have hx : ReflTransGen (Step top Γ) (.iterB k ops b) (.iterB k (Ns Γ ops) b) := by
      rw [Ns_eq_map]
      simpa using star_list (top := top) (Γ := Γ) (Γx := Γ) (fun ys => Tm.iterB k ys b)
        (fun pre post x x' h => .iterBOps k pre post b h) (N Γ) [] ops (reduces_list Γ ops)
    have hb := star_map (fun y => Tm.iterB k (Ns Γ ops) y)
      (fun _ _ h => Step.iterBBody (top := top) (Γ := Γ) k (Ns Γ ops) h)
      (by simpa [Nflag_true] using reduces_flag true (pushN k.binders Γ) b)
    exact hx.trans hb
/-- The list version. -/
theorem reduces_list : ∀ (Γ : Facts) (xs : List Tm),
    ∀ x ∈ xs, ReflTransGen (Step true Γ) x (N Γ x)
  | _, [] => by simp
  | Γ, x :: xs => by
    have hx := reduces_flag true Γ x
    have hxs := reduces_list Γ xs
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · simpa [Nflag_true] using hx
    · exact hxs y hy
/-- The branch version. -/
theorem reduces_alts : ∀ (Γ : Facts) (alts : List (Pat × Tm)),
    ∀ a ∈ alts, ReflTransGen (Step true (a.1.scope Γ)) a.2 (N (a.1.scope Γ) a.2)
  | _, [] => by simp
  | Γ, (p, b) :: alts => by
    have hb := reduces_flag true (p.scope Γ) b
    have halts := reduces_alts Γ alts
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · simpa [Nflag_true] using hb
    · exact halts a ha
/-- The `let*` source version. -/
theorem reduces_ls : ∀ (Γ : Facts) (es : List Tm) (i : ℕ) (hi : i < es.length),
    ReflTransGen (Step true (pushN i Γ)) es[i] (N (pushN i Γ) es[i])
  | _, [], i, hi => by simp at hi
  | Γ, e :: es, 0, _ => by simpa [Nflag_true, pushN] using reduces_flag true Γ e
  | Γ, e :: es, i + 1, hi => by
    simpa [pushN_succ] using reduces_ls (push Γ) es i (by simp at hi; omega)
end

/-- Every term rewrites to its normal form. -/
theorem reduces (Γ : Facts) (t : Tm) : ReflTransGen (Step true Γ) t (N Γ t) := by
  simpa [Nflag_true] using reduces_flag true Γ t

/-! ## Confluence and canonicity -/

/-- Rewriting is confluent. -/
theorem confluent {Γ : Facts} {t a b : Tm} (ha : ReflTransGen (Step true Γ) t a)
    (hb : ReflTransGen (Step true Γ) t b) :
    ∃ d, ReflTransGen (Step true Γ) a d ∧ ReflTransGen (Step true Γ) b d :=
  ⟨N Γ t, by rw [star_N ha]; exact reduces Γ a, by rw [star_N hb]; exact reduces Γ b⟩

/-- Convertible terms share one normal form. -/
theorem canonical {Γ : Facts} {t t' : Tm} (h : EqvGen (Step true Γ) t t') : N Γ t = N Γ t' := by
  induction h with
  | rel _ _ h => exact step_N h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem eqvGen_of_star {r : Tm → Tm → Prop} {a b : Tm} (h : ReflTransGen r a b) : EqvGen r a b := by
  induction h with
  | refl => exact EqvGen.refl _
  | tail _ hs ih => exact EqvGen.trans _ _ _ ih (EqvGen.rel _ _ hs)

/-- A term converts to its normal form. -/
theorem conv_N (Γ : Facts) (t : Tm) : EqvGen (Step true Γ) (N Γ t) t :=
  EqvGen.symm _ _ (eqvGen_of_star (reduces Γ t))

/-- Irreducible reducts are the normal form. -/
theorem normalForm_unique {Γ : Facts} {t a : Tm} (h : ReflTransGen (Step true Γ) t a)
    (hirr : ∀ a', ¬ Step true Γ a a') : a = N Γ t := by
  rw [star_N h]
  rcases (reduces Γ a).cases_head with h0 | ⟨c, hc, _⟩
  · exact h0
  · exact absurd hc (hirr c)

/-- Every term has an irreducible reduct (rewriting terminates). -/
theorem exists_irreducible (Γ : Facts) (t : Tm) :
    ∃ a, ReflTransGen (Step true Γ) t a ∧ ∀ a', ¬ Step true Γ a a' := by
  induction t using (step_wellFounded true Γ).induction with
  | _ t ih =>
    by_cases h : ∃ t', Step true Γ t t'
    · obtain ⟨t', ht⟩ := h
      obtain ⟨a, ha, hirr⟩ := ih t' ht
      exact ⟨a, ReflTransGen.head ht ha, hirr⟩
    · exact ⟨t, .refl, fun a' ha' => h ⟨a', ha'⟩⟩

/-- Normalizing twice is normalizing once. -/
theorem N_idem (Γ : Facts) (t : Tm) : N Γ (N Γ t) = N Γ t :=
  (star_N (reduces Γ t)).symm

/-- The normalizer's output is irreducible: no rule applies anywhere in it. -/
theorem N_irreducible (Γ : Facts) (t : Tm) (t' : Tm) : ¬ Step true Γ (N Γ t) t' := by
  obtain ⟨a, ha, hirr⟩ := exists_irreducible Γ t
  rw [← normalForm_unique ha hirr]
  exact hirr t'

/-! ## The two critical pairs that need completion

Without `sizeVar`, `(size-atom (id $x))` has two normal forms; without `letEta`,
`(case (once b) (($x B)))` has two.  The forks below are steps of the system; their
joins are exactly the completion rules. -/

theorem var_irreducible {top : Bool} {Γ : Facts} {k : ℕ} {t : Tm} : ¬ Step top Γ (.var k) t := by
  intro h; cases h with
  | rule r => cases r

theorem size_var_irreducible {top : Bool} {Γ : Facts} {k : ℕ} {t : Tm} :
    ¬ Step top Γ (.call .size [.var k]) t := by
  intro h
  generalize hargs : [Tm.var k] = args at h
  cases h with
  | rule r =>
    cases r with
    | size e he =>
      simp only [List.cons.injEq, and_true] at hargs
      exact he k hargs.symm
  | call f pre post hx =>
    rcases pre with _ | ⟨p, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at hargs
      obtain ⟨rfl, -⟩ := hargs
      exact var_irreducible hx
    · simp at hargs

/-- `(let $v $x (size-atom $v))` has one step, and it is `sizeVar`. -/
theorem only_sizeVar {top : Bool} {Γ : Facts} {j : ℕ} {t : Tm}
    (h : Step top Γ (.let_ (.var j) (.call .size [.var 0])) t) : t = .call .size [.var j] := by
  cases h with
  | rule r => cases r with
    | sizeVar => rfl
  | letE b h => exact absurd h var_irreducible
  | letB e h => exact absurd h size_var_irreducible

/-- The fork of `size` and `id`, joined by `sizeVar`. -/
theorem critical_size_id (Γ : Facts) (j : ℕ) :
    ReflTransGen (Step true Γ) (.call .size [.call .id [.var j]])
        (.let_ (.var j) (.call .size [.var 0])) ∧
      Step true Γ (.call .size [.call .id [.var j]]) (.call .size [.var j]) ∧
      Step true Γ (.let_ (.var j) (.call .size [.var 0])) (.call .size [.var j]) := by
  refine ⟨?_, ?_, .rule (.sizeVar j)⟩
  · refine (star_single (.rule (.size _ (by simp)))).trans (star_single ?_)
    exact .letE _ (.rule (.id _))
  · exact .call .size [] [] (.rule (.id _))

/-- The fork of `wrap` and `case1`, joined by `letEta`. -/
theorem critical_wrap_case (Γ : Facts) (b B : Tm) :
    Step true Γ (.case_ (.once b) [(.bind, B)]) (.let_ (.once b) B) ∧
      ReflTransGen (Step true Γ) (.case_ (.once b) [(.bind, B)])
        (.let_ (.let_ (.once b) (.var 0)) B) ∧
      Step true Γ (.let_ (.let_ (.once b) (.var 0)) B) (.let_ (.once b) B) := by
  refine ⟨.rule (.case1 _ _), ?_, .rule (.letEta _ _)⟩
  exact (star_single (.caseE _ (.wrap b))).trans (star_single (.rule (.case1 _ _)))

/-! ## The normalizer on the cliff spellings

`gt` and `plus` stand for `>` and `+`; `noFacts` knows nothing about any index. -/

namespace Examples

/-- `>` -/
abbrev gt : Name := .user 10
/-- `+` -/
abbrev plus : Name := .user 0
/-- No integer facts. -/
def noFacts : Facts := fun _ => false
/-- Index 0 holds an integer. -/
def intAt0 : Facts := fun k => k == 0

/-- `(if (> $x 0) $x)` → `(if (> $x 0) $x (empty))`. -/
example : N noFacts (.if2 (.call gt [.var 0, .lit (.int 0)]) (.var 0)) =
    .if3 (.call gt [.var 0, .lit (.int 0)]) (.var 0) .empty := rfl

/-- `(let* (($a (+ $x 1)) ($b (* $a 2))) $b)` → nested `let`s. -/
example : N noFacts (.letStar [.call plus [.var 0, .lit (.int 1)], .call plus [.var 0, .var 0]] (.var 0)) =
    .let_ (.call plus [.var 0, .lit (.int 1)]) (.let_ (.call plus [.var 0, .var 0]) (.var 0)) := rfl

/-- `(case (g) (($x (q $x))))` → `(let $x (g) (q $x))`. -/
example : N noFacts (.case_ (.call (.user 1) []) [(.bind, .call (.user 2) [.var 0])]) =
    .let_ (.call (.user 1) []) (.call (.user 2) [.var 0]) := rfl

/-- `(size-atom (id $x))` → `(size-atom $x)`, through `sizeVar`. -/
example : N noFacts (.call .size [.call .id [.var 3]]) = .call .size [.var 3] := rfl

/-- `(size-atom (g))` → `(let $v (g) (size-atom $v))`. -/
example : N noFacts (.call .size [.call (.user 1) []]) =
    .let_ (.call (.user 1) []) (.call .size [.var 0]) := rfl

/-- A bare `once` is wrapped; a `once` that is a `let` source stays. -/
example : N noFacts (.once (.var 0)) = .let_ (.once (.var 0)) (.var 0) := rfl
example : N noFacts (.let_ (.once (.var 0)) (.var 0)) = .let_ (.once (.var 0)) (.var 0) := rfl
example : N noFacts (.case_ (.once (.var 0)) [(.bind, .var 0)]) =
    .let_ (.once (.var 0)) (.var 0) := rfl

/-- `(min $a 3)` with `$a` an integer → `(if (< $a 3) $a 3)`; without the fact it stays. -/
example : N intAt0 (.call .min [.var 0, .lit (.int 3)]) =
    .if3 (.call .lt [.var 0, .lit (.int 3)]) (.var 0) (.lit (.int 3)) := rfl
example : N noFacts (.call .min [.var 0, .lit (.int 3)]) = .call .min [.var 0, .lit (.int 3)] := rfl

/-- `(foldl-atom $l 0 +)` → `(foldl-atom $l 0 $a $b (+ $a $b))`. -/
example : N noFacts (.iterC .foldl [.var 0, .lit (.int 0)] plus) =
    .iterB .foldl [.var 0, .lit (.int 0)] (.call plus [.var 1, .var 0]) := rfl

/-- `(map-atom $l id)` → `(map-atom $l $x $x)`. -/
example : N noFacts (.iterC .map [.var 0] .id) = .iterB .map [.var 0] (.var 0) := rfl

/-- A held position is left alone. -/
example : N noFacts (.quote (.if2 (.var 0) (.var 0))) = .quote (.if2 (.var 0) (.var 0)) := rfl

end Examples

end Mettapedia.Machines.AdmissionRewriting
