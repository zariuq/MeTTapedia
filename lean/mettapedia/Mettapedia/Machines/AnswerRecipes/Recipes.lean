import Mathlib.Tactic

/-!
# Answer recipes: a cached answer replayed with its identities anchored

A cached answer of a call is replayed for later calls of the same shape.  Its variables
are of three kinds, by where they come from:
* **caller** variables are the call's own; a replay for a new call restores the new
  call's;
* **retained** identities existed before the call and are held outside it (a stored
  state's variables, a sealed payload's); a replay keeps them exactly;
* **answer** variables were introduced by the computation; every replay gets fresh ones.

A *recipe* is an answer with each variable replaced by its slot: the solved input and the
output form one term, so the variables they share stay shared.  A *replay* instantiates
caller slots by the new call's variables, answer slots by a fresh supply, and leaves
retained slots as they are.

**Agreement.**  `LocalVariant K a b` says that `b` is `a` up to renaming the variables
outside `K`, by a renaming that is injective on `a`'s variables, fixes those in `K` and
sends the others outside `K`; it is an equivalence (`LocalVariant.refl`, `.symm`,
`.trans`).  An execution is `VariantInvariant` when renaming a call by a permutation that
fixes the retained identities renames its answers, in order, up to their own variables:
the property variant tabling rests on.

This file proves:
* `replay_recipe`: a replay for the call renamed by such a permutation is a local variant
  of the renamed answer, anchored at the new call's variables and the retained
  identities, provided the supply is injective on the answer's own variables and fresh
  for the anchors;
* `replay_agrees`: for every variant-invariant execution, replaying the recipes of a
  call's answers agrees with the uncached execution of the renamed call, answer by
  answer, in order;
* `runFresh_variantInvariant`: an execution that introduces an answer variable (the
  least index above the call and the retained identities) is variant invariant, so
  `replay_agrees` applies to it (`runFresh_replay_agrees`).

**Controls** (a call `f($0)`, the retained identity `5`, the new call `f($10)`, the
supply `v ↦ v + 100`):
* `(x, x)` stays aliased and `(x, y)` is not aliased (`replay_xx`, `replay_xy`);
* the caller's identity is restored (`replay_caller`), a retained identity survives
  (`replay_retained`), the solved input and the output keep their shared variable
  (`replay_linked`);
* two replays with disjoint supplies share no answer variable (`replays_independent`).

**Negative controls**, each the failure of one ingredient:
* a recipe without the retained kind (every variable not the call's is the answer's
  own) replays a retained identity as a fresh variable (`replayTwoKinds_loses_retained`);
* a recipe that keeps answer variables as identities hands the producer's variable to
  every replay (`replayKeep_shares`);
* instantiating the solved input and the output with separate supplies breaks the
  variable they share (`separate_breaks_link`);
* a supply that is not injective aliases `(x, y)` (`constant_supply_aliases`);
* a key that admits a renaming of a caller variable onto a retained identity replays an
  answer the uncached execution does not give (`plainKey_replays_wrong`): the
  `isRetained` execution is variant invariant, yet `f($0)` and `f(5)` are variants only
  by a renaming that moves the retained `5`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AnswerRecipes

/-! ## Terms -/

/-- Terms: variables, symbols, and binary application; an S-expression is a tree of
applications. -/
inductive Tm (V : Type) where
  | var (v : V)
  | sym (s : ℕ)
  | app (f a : Tm V)
  deriving DecidableEq

namespace Tm

variable {V W U : Type}

/-- Renaming variables. -/
def map (θ : V → W) : Tm V → Tm W
  | var v => var (θ v)
  | sym s => sym s
  | app f a => app (map θ f) (map θ a)

/-- The variable occurrences, left to right. -/
def vars : Tm V → List V
  | var v => [v]
  | sym _ => []
  | app f a => vars f ++ vars a

@[simp] theorem map_var (θ : V → W) (v : V) : (var v).map θ = var (θ v) := rfl
@[simp] theorem map_sym (θ : V → W) (s : ℕ) : (sym s : Tm V).map θ = sym s := rfl
@[simp] theorem map_app (θ : V → W) (f a : Tm V) :
    (app f a).map θ = app (f.map θ) (a.map θ) := rfl
@[simp] theorem vars_var (v : V) : (var v).vars = [v] := rfl
@[simp] theorem vars_sym (s : ℕ) : (sym s : Tm V).vars = [] := rfl
@[simp] theorem vars_app (f a : Tm V) : (app f a).vars = f.vars ++ a.vars := rfl

theorem map_id' (t : Tm V) : t.map (fun v => v) = t := by
  induction t with
  | var v => rfl
  | sym s => rfl
  | app f a ihf iha => simp [ihf, iha]

theorem map_map (θ : V → W) (η : W → U) (t : Tm V) :
    (t.map θ).map η = t.map (fun v => η (θ v)) := by
  induction t with
  | var v => rfl
  | sym s => rfl
  | app f a ihf iha => simp [ihf, iha]

theorem map_congr {θ η : V → W} (t : Tm V) (h : ∀ v ∈ t.vars, θ v = η v) :
    t.map θ = t.map η := by
  induction t with
  | var v => simp [h v (by simp)]
  | sym s => rfl
  | app f a ihf iha =>
    simp only [vars_app, List.mem_append] at h
    simp only [map_app, ihf (fun v hv => h v (Or.inl hv)), iha (fun v hv => h v (Or.inr hv))]

theorem vars_map (θ : V → W) (t : Tm V) : (t.map θ).vars = t.vars.map θ := by
  induction t with
  | var v => rfl
  | sym s => rfl
  | app f a ihf iha => simp [ihf, iha]

theorem mem_vars_map {θ : V → W} {t : Tm V} {w : W} :
    w ∈ (t.map θ).vars ↔ ∃ v ∈ t.vars, θ v = w := by
  rw [vars_map, List.mem_map]

theorem vars_eq_nil_of_isEmpty [IsEmpty V] (t : Tm V) : t.vars = [] := by
  induction t with
  | var v => exact (IsEmpty.false v).elim
  | sym s => rfl
  | app f a ihf iha => simp [ihf, iha]

end Tm

open Tm

variable {V : Type}

/-! ## Agreement up to the answer's own variables -/

/-- `b` is `a` up to renaming the variables outside `K`: by a renaming injective on `a`'s
variables that fixes those in `K` and sends the others outside `K`. -/
def LocalVariant (K : V → Prop) (a b : Tm V) : Prop :=
  ∃ θ : V → V, Set.InjOn θ {v | v ∈ a.vars} ∧ (∀ v ∈ a.vars, K v → θ v = v) ∧
    (∀ v ∈ a.vars, ¬ K v → ¬ K (θ v)) ∧ a.map θ = b

namespace LocalVariant

variable {K : V → Prop}

theorem refl (a : Tm V) : LocalVariant K a a :=
  ⟨fun v => v, fun _ _ _ _ h => h, fun _ _ _ => rfl, fun _ _ h => h, map_id' a⟩

theorem trans {a b c : Tm V} (h₁ : LocalVariant K a b) (h₂ : LocalVariant K b c) :
    LocalVariant K a c := by
  obtain ⟨θ, hinj, hfix, hout, rfl⟩ := h₁
  obtain ⟨η, hinj', hfix', hout', rfl⟩ := h₂
  have hmem : ∀ v ∈ a.vars, θ v ∈ (a.map θ).vars := fun v hv =>
    mem_vars_map.mpr ⟨v, hv, rfl⟩
  refine ⟨fun v => η (θ v), ?_, ?_, ?_, (map_map θ η a).symm⟩
  · exact hinj'.comp hinj (fun v hv => hmem v hv)
  · intro v hv hk
    have hθ := hfix v hv hk
    have hm : v ∈ (a.map θ).vars := by rw [← hθ]; exact hmem v hv
    simp only [hθ, hfix' v hm hk]
  · intro v hv hk
    exact hout' (θ v) (hmem v hv) (hout v hv hk)

theorem symm {a b : Tm V} (h : LocalVariant K a b) : LocalVariant K b a := by
  obtain ⟨θ, hinj, hfix, hout, rfl⟩ := h
  rcases isEmpty_or_nonempty V with hV | hV
  · have hm : a.map θ = a := by
      conv_rhs => rw [← map_id' a]
      exact map_congr a (by simp [vars_eq_nil_of_isEmpty a])
    rw [hm]; exact refl a
  · let η := Function.invFunOn θ {v | v ∈ a.vars}
    have hleft : ∀ v ∈ a.vars, η (θ v) = v := fun v hv => hinj.leftInvOn_invFunOn hv
    refine ⟨η, ?_, ?_, ?_, ?_⟩
    · have himg : {w | w ∈ (a.map θ).vars} = θ '' {v | v ∈ a.vars} := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_image, mem_vars_map]
      rw [himg]
      exact Function.invFunOn_injOn_image θ _
    · intro w hw hk
      obtain ⟨v, hv, rfl⟩ := mem_vars_map.mp hw
      by_cases hkv : K v
      · show η (θ v) = θ v
        rw [hleft v hv, hfix v hv hkv]
      · exact absurd hk (hout v hv hkv)
    · intro w hw hk
      obtain ⟨v, hv, rfl⟩ := mem_vars_map.mp hw
      rw [hleft v hv]
      intro hkv
      exact hk (by rw [hfix v hv hkv]; exact hkv)
    · rw [map_map]
      conv_rhs => rw [← map_id' a]
      exact map_congr a hleft

/-- A local variant keeps the equality pattern of variables: two variables of `a` are
equal exactly when their images are. -/
theorem map_eq_iff {a b : Tm V} (h : LocalVariant K a b) :
    ∃ θ : V → V, a.map θ = b ∧ ∀ v ∈ a.vars, ∀ w ∈ a.vars, (θ v = θ w ↔ v = w) := by
  obtain ⟨θ, hinj, -, -, rfl⟩ := h
  exact ⟨θ, rfl, fun v hv w hw => ⟨fun he => hinj hv hw he, fun he => he ▸ rfl⟩⟩

/-- Agreement depends on the anchors only at the variables of the two terms. -/
theorem congr_anchors {K' : V → Prop} {a b : Tm V} (h : LocalVariant K a b)
    (hK : ∀ v, v ∈ a.vars ∨ v ∈ b.vars → (K v ↔ K' v)) : LocalVariant K' a b := by
  obtain ⟨θ, hinj, hfix, hout, rfl⟩ := h
  have himg : ∀ v ∈ a.vars, θ v ∈ (a.map θ).vars := fun v hv => mem_vars_map.mpr ⟨v, hv, rfl⟩
  refine ⟨θ, hinj, fun v hv hk => hfix v hv ((hK v (Or.inl hv)).mpr hk), fun v hv hk => ?_, rfl⟩
  rw [← hK (θ v) (Or.inr (himg v hv))]
  exact hout v hv (fun h => hk ((hK v (Or.inl hv)).mp h))

end LocalVariant

/-! ## Recipes and replays -/

/-- The slot of an answer's variable. -/
inductive Slot (V : Type) where
  /-- A variable of the call: the caller's. -/
  | caller (v : V)
  /-- An identity from before the call, held outside it. -/
  | retained (v : V)
  /-- A variable the computation introduced: the answer's own. -/
  | own (v : V)
  deriving DecidableEq

variable [DecidableEq V]

/-- The slot of a variable of an answer to the call `q`, `R` marking the retained
identities: the call's variables first, then the retained ones, the rest the answer's
own. -/
def classify (q : Tm V) (R : V → Bool) (v : V) : Slot V :=
  if v ∈ q.vars then .caller v else if R v then .retained v else .own v

/-- The recipe of an answer: each variable replaced by its slot.  The answer is one term,
the solved input and the output together. -/
def recipe (q : Tm V) (R : V → Bool) (a : Tm V) : Tm (Slot V) :=
  a.map (classify q R)

/-- What a slot becomes in a replay: a caller slot the new call's variable, a retained
slot itself, an answer slot a variable of the supply. -/
def Slot.inst (π φ : V → V) : Slot V → V
  | .caller v => π v
  | .retained v => v
  | .own v => φ v

/-- A replay of a recipe. -/
def replay (π φ : V → V) (r : Tm (Slot V)) : Tm V := r.map (Slot.inst π φ)

/-- An answer's own variable: neither the call's nor retained. -/
def IsOwn (q : Tm V) (R : V → Bool) (v : V) : Prop := v ∉ q.vars ∧ R v = false

/-- The identities a replay for the call `q` renamed by `π` must fix: the new call's
variables and the retained identities. -/
def Anchors (q : Tm V) (R : V → Bool) (π : V → V) (w : V) : Prop :=
  w ∈ (q.map π).vars ∨ R w = true

/-- A permutation that fixes every retained identity. -/
def FixesRetained (R : V → Bool) (π : Equiv.Perm V) : Prop := ∀ v, R v = true → π v = v

omit [DecidableEq V] in
theorem FixesRetained.retained_iff {R : V → Bool} {π : Equiv.Perm V}
    (h : FixesRetained R π) (v : V) : R (π v) = R v := by
  cases hv : R v with
  | true => rw [h v hv, hv]
  | false =>
    cases hpv : R (π v) with
    | false => rfl
    | true =>
      have h1 : π (π v) = π v := h (π v) hpv
      have h2 : π v = v := π.injective h1
      rw [h2, hv] at hpv
      exact absurd hpv (by simp)

omit [DecidableEq V] in
theorem mem_vars_map_perm (π : Equiv.Perm V) (q : Tm V) (v : V) :
    π v ∈ (q.map π).vars ↔ v ∈ q.vars := by
  rw [mem_vars_map]
  constructor
  · rintro ⟨u, hu, he⟩
    rw [π.injective he] at hu
    exact hu
  · intro hv
    exact ⟨v, hv, rfl⟩

omit [DecidableEq V] in
theorem anchors_perm (q : Tm V) (R : V → Bool) (π : Equiv.Perm V) (hπ : FixesRetained R π)
    (v : V) : Anchors q R π (π v) ↔ v ∈ q.vars ∨ R v = true := by
  unfold Anchors
  rw [mem_vars_map_perm, hπ.retained_iff]

/-- A supply fresh for replaying the answer `a` of `q` for the call renamed by `π`:
injective on the answer's own variables, and sending them off the anchors. -/
structure Fresh (q : Tm V) (R : V → Bool) (π φ : V → V) (a : Tm V) : Prop where
  inj : Set.InjOn φ {v | v ∈ a.vars ∧ IsOwn q R v}
  off : ∀ v ∈ a.vars, IsOwn q R v → ¬ Anchors q R π (φ v)

theorem inst_classify_caller {q : Tm V} {R : V → Bool} {π φ : V → V} {v : V}
    (h : v ∈ q.vars) : Slot.inst π φ (classify q R v) = π v := by
  simp [classify, h, Slot.inst]

theorem inst_classify_retained {q : Tm V} {R : V → Bool} {π φ : V → V} {v : V}
    (h : v ∉ q.vars) (hr : R v = true) : Slot.inst π φ (classify q R v) = v := by
  simp [classify, h, hr, Slot.inst]

theorem inst_classify_own {q : Tm V} {R : V → Bool} {π φ : V → V} {v : V}
    (h : IsOwn q R v) : Slot.inst π φ (classify q R v) = φ v := by
  simp [classify, h.1, h.2, Slot.inst]

/-- The replay of a recipe is the answer renamed by its slots. -/
theorem replay_recipe_eq (q : Tm V) (R : V → Bool) (π φ : V → V) (a : Tm V) :
    replay π φ (recipe q R a) = a.map (fun v => Slot.inst π φ (classify q R v)) := by
  simp only [replay, recipe, map_map]

/-- **The round trip.**  A replay for the call renamed by a permutation that fixes the
retained identities, with a fresh supply, is a local variant of the renamed answer,
anchored at the new call's variables and the retained identities. -/
theorem replay_recipe (q : Tm V) (R : V → Bool) (π : Equiv.Perm V) (hπ : FixesRetained R π)
    (φ : V → V) (a : Tm V) (hφ : Fresh q R π φ a) :
    LocalVariant (Anchors q R π) (a.map π) (replay π φ (recipe q R a)) := by
  let θ : V → V := fun w => Slot.inst π φ (classify q R (π.symm w))
  have hθ : ∀ v, θ (π v) = Slot.inst π φ (classify q R v) := fun v => by simp [θ]
  -- the three cases of a variable of `a`
  have cases3 : ∀ v, v ∈ q.vars ∨ (v ∉ q.vars ∧ R v = true) ∨ IsOwn q R v := by
    intro v
    by_cases h : v ∈ q.vars
    · exact Or.inl h
    · by_cases hr : R v = true
      · exact Or.inr (Or.inl ⟨h, hr⟩)
      · exact Or.inr (Or.inr ⟨h, by simpa using hr⟩)
  have anchor_of_caller : ∀ v, v ∈ q.vars → Anchors q R π (π v) :=
    fun v h => (anchors_perm q R π hπ v).mpr (Or.inl h)
  have anchor_of_retained : ∀ v, R v = true → Anchors q R π v :=
    fun v h => Or.inr h
  refine ⟨θ, ?_, ?_, ?_, ?_⟩
  · -- injectivity on the renamed answer's variables
    intro w₁ hw₁ w₂ hw₂ he
    obtain ⟨v₁, hv₁, rfl⟩ := mem_vars_map.mp hw₁
    obtain ⟨v₂, hv₂, rfl⟩ := mem_vars_map.mp hw₂
    rw [hθ, hθ] at he
    rcases cases3 v₁ with c₁ | ⟨n₁, r₁⟩ | o₁ <;> rcases cases3 v₂ with c₂ | ⟨n₂, r₂⟩ | o₂
    · rw [inst_classify_caller c₁, inst_classify_caller c₂] at he; exact he
    · rw [inst_classify_caller c₁, inst_classify_retained n₂ r₂] at he
      have : π v₁ = v₁ := by
        have hr : R (π v₁) = true := by rw [he]; exact r₂
        rw [hπ.retained_iff] at hr
        exact hπ v₁ hr
      rw [this] at he
      exact absurd (he ▸ c₁) n₂
    · rw [inst_classify_caller c₁, inst_classify_own o₂] at he
      exact absurd (he ▸ anchor_of_caller v₁ c₁) (hφ.off v₂ hv₂ o₂)
    · rw [inst_classify_retained n₁ r₁, inst_classify_caller c₂] at he
      have : π v₂ = v₂ := by
        have hr : R (π v₂) = true := by rw [← he]; exact r₁
        rw [hπ.retained_iff] at hr
        exact hπ v₂ hr
      rw [this] at he
      exact absurd (he ▸ c₂) n₁
    · rw [inst_classify_retained n₁ r₁, inst_classify_retained n₂ r₂] at he
      rw [he]
    · rw [inst_classify_retained n₁ r₁, inst_classify_own o₂] at he
      exact absurd (he ▸ anchor_of_retained v₁ r₁) (hφ.off v₂ hv₂ o₂)
    · rw [inst_classify_own o₁, inst_classify_caller c₂] at he
      exact absurd (he.symm ▸ anchor_of_caller v₂ c₂) (hφ.off v₁ hv₁ o₁)
    · rw [inst_classify_own o₁, inst_classify_retained n₂ r₂] at he
      exact absurd (he.symm ▸ anchor_of_retained v₂ r₂) (hφ.off v₁ hv₁ o₁)
    · rw [inst_classify_own o₁, inst_classify_own o₂] at he
      rw [hφ.inj ⟨hv₁, o₁⟩ ⟨hv₂, o₂⟩ he]
  · -- anchors are fixed
    intro w hw hk
    obtain ⟨v, hv, rfl⟩ := mem_vars_map.mp hw
    rw [hθ]
    rcases cases3 v with c | ⟨n, r⟩ | o
    · exact inst_classify_caller c
    · rw [inst_classify_retained n r, hπ v r]
    · exact absurd ((anchors_perm q R π hπ v).mp hk)
        (by rintro (h | h); exact o.1 h; rw [o.2] at h; exact absurd h (by simp))
  · -- the answer's own variables leave the anchors
    intro w hw hk
    obtain ⟨v, hv, rfl⟩ := mem_vars_map.mp hw
    rw [hθ]
    rcases cases3 v with c | ⟨n, r⟩ | o
    · exact absurd (anchor_of_caller v c) hk
    · exact absurd ((anchors_perm q R π hπ v).mpr (Or.inr r)) hk
    · rw [inst_classify_own o]; exact hφ.off v hv o
  · rw [map_map, replay_recipe_eq]
    exact map_congr a (fun v _ => hθ v)

/-! ## Agreement with the uncached execution -/

/-- An execution is variant invariant when renaming a call by a permutation that fixes the
retained identities renames its answers, in order, up to the answers' own variables. -/
def VariantInvariant (R : V → Bool) (run : Tm V → List (Tm V)) : Prop :=
  ∀ π : Equiv.Perm V, FixesRetained R π → ∀ q : Tm V,
    List.Forall₂ (LocalVariant (Anchors q R π)) ((run q).map (Tm.map π)) (run (q.map π))

omit [DecidableEq V] in
theorem forall₂_of_pointwise {K : V → Prop} (f g : Tm V → Tm V) :
    ∀ (xs ys : List (Tm V)), List.Forall₂ (LocalVariant K) (xs.map f) ys →
      (∀ x ∈ xs, LocalVariant K (f x) (g x)) → List.Forall₂ (LocalVariant K) (xs.map g) ys
  | [], ys, h, _ => by cases h; exact .nil
  | x :: xs, ys, h, hfg => by
    simp only [List.map_cons] at h
    cases h with
    | cons hx hxs =>
      simp only [List.map_cons]
      exact .cons ((hfg x (by simp)).symm.trans hx)
        (forall₂_of_pointwise f g xs _ hxs (fun y hy => hfg y (by simp [hy])))

/-- **Replay agrees with the uncached execution.**  For a variant-invariant execution, the
replays of the recipes of a call's answers, for the call renamed by a permutation that
fixes the retained identities, agree with the uncached answers of the renamed call: the
same number, in order, each up to renaming its own variables, the new call's variables
and the retained identities fixed. -/
theorem replay_agrees (R : V → Bool) (run : Tm V → List (Tm V)) (hrun : VariantInvariant R run)
    (q : Tm V) (π : Equiv.Perm V) (hπ : FixesRetained R π) (φ : V → V)
    (hφ : ∀ a ∈ run q, Fresh q R π φ a) :
    List.Forall₂ (LocalVariant (Anchors q R π))
      ((run q).map fun a => replay π φ (recipe q R a)) (run (q.map π)) :=
  forall₂_of_pointwise (Tm.map π) _ (run q) _ (hrun π hπ q)
    (fun a ha => replay_recipe q R π hπ φ a (hφ a ha))

/-! ## An execution that introduces a variable -/

/-- The largest element of a list of indices, or `0`. -/
def bound : List ℕ → ℕ
  | [] => 0
  | x :: xs => max x (bound xs)

theorem le_bound {v : ℕ} : ∀ {l : List ℕ}, v ∈ l → v ≤ bound l
  | x :: xs, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_bound h) (le_max_right _ _)

/-- The retained identities of a finite world. -/
def inWorld (world : List ℕ) (v : ℕ) : Bool := decide (v ∈ world)

/-- The answer variable `runFresh` introduces: above the call's variables and the world. -/
def freshFor (world : List ℕ) (q : Tm ℕ) : ℕ := bound (q.vars ++ world) + 1

theorem freshFor_not_mem (world : List ℕ) (q : Tm ℕ) :
    freshFor world q ∉ q.vars ∧ inWorld world (freshFor world q) = false := by
  constructor
  · intro h
    have := le_bound (List.mem_append_left world h)
    simp only [freshFor] at this
    omega
  · simp only [inWorld, decide_eq_false_iff_not]
    intro h
    have := le_bound (List.mem_append_right q.vars h)
    simp only [freshFor] at this
    omega

/-- An execution with an answer variable: the call paired with a new variable. -/
def runFresh (world : List ℕ) (q : Tm ℕ) : List (Tm ℕ) :=
  [.app q (.var (freshFor world q))]

theorem runFresh_variantInvariant (world : List ℕ) :
    VariantInvariant (inWorld world) (runFresh world) := by
  intro π hπ q
  simp only [runFresh, List.map_cons, List.map_nil, map_app, map_var]
  refine .cons ?_ .nil
  set m := freshFor world q
  set m' := freshFor world (q.map π)
  obtain ⟨hmq, hmR⟩ := freshFor_not_mem world q
  obtain ⟨hmq', hmR'⟩ := freshFor_not_mem world (q.map π)
  have hπm : ¬ Anchors q (inWorld world) π (π m) := by
    rw [anchors_perm q _ π hπ m]
    rintro (h | h)
    · exact hmq h
    · rw [hmR] at h; exact absurd h (by simp)
  have hm' : ¬ Anchors q (inWorld world) π m' := by
    rintro (h | h)
    · exact hmq' h
    · rw [hmR'] at h; exact absurd h (by simp)
  have hanchor : ∀ w ∈ (q.map π).vars, Anchors q (inWorld world) π w := fun w hw => Or.inl hw
  refine ⟨Equiv.swap (π m) m', (Equiv.swap (π m) m').injective.injOn, ?_, ?_, ?_⟩
  · intro w hw hk
    have h1 : w ≠ π m := fun h => hπm (h ▸ hk)
    have h2 : w ≠ m' := fun h => hm' (h ▸ hk)
    exact Equiv.swap_apply_of_ne_of_ne h1 h2
  · intro w hw hk
    simp only [vars_app, vars_var, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact absurd (hanchor w hw) hk
    · rw [Equiv.swap_apply_left]; exact hm'
  · simp only [map_app, map_var, Equiv.swap_apply_left]
    congr 1
    conv_rhs => rw [← map_id' (q.map π)]
    refine map_congr _ (fun w hw => ?_)
    have h1 : w ≠ π m := fun h => hπm (h ▸ hanchor w hw)
    have h2 : w ≠ m' := fun h => hm' (h ▸ hanchor w hw)
    exact Equiv.swap_apply_of_ne_of_ne h1 h2

/-- `replay_agrees` for `runFresh`: a fresh supply avoiding the anchors makes every replay
agree with the uncached run of the renamed call. -/
theorem runFresh_replay_agrees (world : List ℕ) (q : Tm ℕ) (π : Equiv.Perm ℕ)
    (hπ : FixesRetained (inWorld world) π) (φ : ℕ → ℕ) (hinj : Function.Injective φ)
    (hoff : ∀ v, ¬ Anchors q (inWorld world) π (φ v)) :
    List.Forall₂ (LocalVariant (Anchors q (inWorld world) π))
      ((runFresh world q).map fun a => replay π φ (recipe q (inWorld world) a))
      (runFresh world (q.map π)) :=
  replay_agrees _ _ (runFresh_variantInvariant world) q π hπ φ
    (fun _ _ => ⟨hinj.injOn, fun v _ _ => hoff v⟩)

/-! ## Controls -/

namespace Controls

/-- The call `f($0)`. -/
def call : Tm ℕ := .app (.sym 0) (.var 0)
/-- The retained identity `5`. -/
def R : ℕ → Bool := fun v => v == 5
/-- The new call's variable `$10` in place of `$0`. -/
def π : Equiv.Perm ℕ := Equiv.swap 0 10
/-- A supply. -/
def φ : ℕ → ℕ := fun v => v + 100

theorem π_fixes : FixesRetained R π := by
  intro v hv
  have : v = 5 := by simpa [R] using hv
  subst this
  decide

/-- `(x, x)`. -/
def xx : Tm ℕ := .app (.var 1) (.var 1)
/-- `(x, y)`. -/
def xy : Tm ℕ := .app (.var 1) (.var 2)
/-- An answer holding the caller's variable. -/
def withCaller : Tm ℕ := .app (.var 0) (.var 1)
/-- An answer holding the retained identity. -/
def withRetained : Tm ℕ := .app (.var 5) (.var 1)
/-- A solved input `f($1)` and an output `$1` sharing the answer variable. -/
def linked : Tm ℕ := .app (.app (.sym 0) (.var 1)) (.var 1)

theorem replay_xx : replay π φ (recipe call R xx) = .app (.var 101) (.var 101) := by decide
theorem replay_xy : replay π φ (recipe call R xy) = .app (.var 101) (.var 102) := by decide
theorem replay_caller :
    replay π φ (recipe call R withCaller) = .app (.var 10) (.var 101) := by decide
theorem replay_retained :
    replay π φ (recipe call R withRetained) = .app (.var 5) (.var 101) := by decide
theorem replay_linked :
    replay π φ (recipe call R linked) = .app (.app (.sym 0) (.var 101)) (.var 101) := by decide

/-- Two replays with disjoint supplies share no answer variable. -/
theorem replays_independent :
    replay π (· + 100) (recipe call R xy) = .app (.var 101) (.var 102) ∧
      replay π (· + 200) (recipe call R xy) = .app (.var 201) (.var 202) := by decide

/-- The anchors of the new call: its variable `10` and the retained `5`. -/
theorem anchors_iff (w : ℕ) : Anchors call R π w ↔ w = 10 ∨ w = 5 := by
  have hcall : (call.map π).vars = [10] := by decide
  simp only [Anchors, hcall, List.mem_singleton, R, beq_iff_eq]

theorem φ_fresh (a : Tm ℕ) (ha : ∀ v ∈ a.vars, v < 3) : Fresh call R π φ a := by
  refine ⟨fun x _ y _ h => by simpa [φ] using h, fun v hv _ => ?_⟩
  rw [anchors_iff]
  have := ha v hv
  simp only [φ]
  omega

/-- The replays agree with the renamed answers (`replay_recipe`), on every control. -/
theorem controls_agree :
    LocalVariant (Anchors call R π) (xy.map π) (replay π φ (recipe call R xy)) ∧
      LocalVariant (Anchors call R π) (withRetained.map π)
        (replay π φ (recipe call R withRetained)) ∧
      LocalVariant (Anchors call R π) (linked.map π) (replay π φ (recipe call R linked)) := by
  refine ⟨replay_recipe _ _ _ π_fixes _ _ (φ_fresh _ ?_),
    replay_recipe _ _ _ π_fixes _ _ ⟨?_, ?_⟩,
    replay_recipe _ _ _ π_fixes _ _ (φ_fresh _ ?_)⟩
  · intro v hv; simp [xy] at hv; omega
  · exact fun x _ y _ h => by simpa [φ] using h
  · intro v hv ho
    simp only [withRetained, vars_app, vars_var, List.mem_append, List.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact absurd ho.2 (by decide)
    · rw [anchors_iff]; decide
  · intro v hv; simp [linked] at hv; omega

/-! ### Negative controls -/

/-- A recipe without the retained kind: every variable not the call's is the answer's
own. -/
def classifyTwo (q : Tm ℕ) (v : ℕ) : Slot ℕ := if v ∈ q.vars then .caller v else .own v

/-- It replays the retained identity `5` as the fresh `105`. -/
theorem replayTwoKinds_loses_retained :
    (withRetained.map (classifyTwo call)).map (Slot.inst π φ) = .app (.var 105) (.var 101) ∧
      ¬ LocalVariant (Anchors call R π) (withRetained.map π)
        ((withRetained.map (classifyTwo call)).map (Slot.inst π φ)) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨θ, -, hfix, -, he⟩
  have hw : withRetained.map π = .app (.var 5) (.var 1) := by decide
  have h5 : θ 5 = 5 := hfix 5 (by rw [hw]; simp) ((anchors_iff 5).mpr (Or.inr rfl))
  have hrep : (withRetained.map (classifyTwo call)).map (Slot.inst π φ) =
      .app (.var 105) (.var 101) := by decide
  rw [hw, hrep] at he
  simp only [map_app, map_var, Tm.app.injEq, Tm.var.injEq] at he
  omega

/-- A recipe that keeps the answer's own variables as identities. -/
def classifyKeep (q : Tm ℕ) (v : ℕ) : Slot ℕ := if v ∈ q.vars then .caller v else .retained v

/-- It hands the producer's variables to every replay, whatever the supply: two replays
with disjoint supplies share them. -/
theorem replayKeep_shares :
    (xy.map (classifyKeep call)).map (Slot.inst π (· + 100)) = .app (.var 1) (.var 2) ∧
      (xy.map (classifyKeep call)).map (Slot.inst π (· + 200)) = .app (.var 1) (.var 2) := by
  decide

/-- Instantiating the solved input and the output with separate supplies: the variable
they share becomes two. -/
theorem separate_breaks_link :
    Tm.app (replay π (· + 100) (recipe call R (.app (.sym 0) (.var 1))))
        (replay π (· + 200) (recipe call R (.var 1))) =
      .app (.app (.sym 0) (.var 101)) (.var 201) ∧
      ¬ LocalVariant (Anchors call R π) (linked.map π)
        (.app (.app (.sym 0) (.var 101)) (.var 201)) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨θ, -, -, -, he⟩
  have hl : linked.map π = .app (.app (.sym 0) (.var 1)) (.var 1) := by decide
  rw [hl] at he
  simp only [map_app, map_var, map_sym, Tm.app.injEq, Tm.var.injEq] at he
  omega

/-- A supply that is not injective aliases `(x, y)`. -/
theorem constant_supply_aliases :
    replay π (fun _ => 100) (recipe call R xy) = .app (.var 100) (.var 100) ∧
      ¬ LocalVariant (Anchors call R π) (xy.map π) (.app (.var 100) (.var 100)) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨θ, hinj, -, -, he⟩
  have hx : xy.map π = .app (.var 1) (.var 2) := by decide
  rw [hx] at he hinj
  simp only [map_app, map_var, Tm.app.injEq, Tm.var.injEq] at he
  have := hinj (by simp) (by simp) (he.1.trans he.2.symm)
  omega

/-- An execution that observes whether its argument is a retained identity: `f(v)`
answers `1` when `v` is retained, `0` otherwise. -/
def runIsRetained (R : ℕ → Bool) : Tm ℕ → List (Tm ℕ)
  | .app (.sym 0) (.var v) => [.sym (if R v then 1 else 0)]
  | _ => []

theorem runIsRetained_map (R : ℕ → Bool) (π : Equiv.Perm ℕ) (hπ : FixesRetained R π) :
    ∀ q : Tm ℕ, runIsRetained R (q.map π) = (runIsRetained R q).map (Tm.map π)
  | .var _ => rfl
  | .sym _ => rfl
  | .app (.var _) _ => rfl
  | .app (.app _ _) _ => rfl
  | .app (.sym 0) (.var v) => by simp [runIsRetained, hπ.retained_iff]
  | .app (.sym 0) (.sym _) => rfl
  | .app (.sym 0) (.app _ _) => rfl
  | .app (.sym (_ + 1)) _ => rfl

/-- It is variant invariant: identity with the world is what a permutation fixing the
world preserves. -/
theorem runIsRetained_variantInvariant : VariantInvariant R (runIsRetained R) := by
  intro π hπ q
  rw [runIsRetained_map R π hπ q]
  generalize (runIsRetained R q).map (Tm.map π) = l
  induction l with
  | nil => exact .nil
  | cons x xs ih => exact .cons (LocalVariant.refl x) ih

/-- A key that sees only the shape of the call: `f($0)` and `f(5)` are variants by the
renaming swapping `0` and `5`, which moves the retained `5`.  The answer recorded for
`f($0)`, replayed for `f(5)`, is not the uncached answer, and no renaming fixing the
retained identities relates the two calls. -/
theorem plainKey_replays_wrong :
    call.map (Equiv.swap 0 5) = .app (.sym 0) (.var 5) ∧
      (runIsRetained R call).map
          (fun a => replay (Equiv.swap 0 5) φ (recipe call R a)) = [.sym 0] ∧
      runIsRetained R (.app (.sym 0) (.var 5)) = [.sym 1] ∧
      ¬ ∃ σ : Equiv.Perm ℕ, FixesRetained R σ ∧ call.map σ = .app (.sym 0) (.var 5) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨σ, hσ, he⟩
  simp only [call, map_app, map_sym, map_var, Tm.app.injEq, Tm.var.injEq, true_and] at he
  have h5 : σ 5 = 5 := hσ 5 (by decide)
  have : (0 : ℕ) = 5 := σ.injective (he.trans h5.symm)
  omega

end Controls

end Mettapedia.Machines.AnswerRecipes
