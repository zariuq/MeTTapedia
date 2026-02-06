import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Valuation Algebra (Scopes + Combination + Marginalization)

This module provides a minimal **valuation-algebra** layer for factorized
world models.  A valuation is a function on full configurations, annotated
with the finite set of variables it actually depends on (its **scope**).

Key operations:
* **combine**: pointwise multiplication, with scope union
* **sumOut**: marginalization (sum out a variable)

We also prove a generic **VE correctness spine**:

```
combineAll (eliminateVars fs order) = sumOutAll (combineAll fs) order
```

under the usual commutative-semiring assumptions.

This is the algebraic core that underwrites variable elimination and
factor-graph semantics.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped Classical BigOperators

variable {V : Type*} {β : V → Type*} {K : Type*} [DecidableEq V]

/-! ## Full configurations -/

/-- A full configuration assigns a value to every variable. -/
abbrev FullConfig (V : Type*) (β : V → Type*) : Type _ := ∀ v : V, β v

/-- Update a single variable in a full configuration. -/
noncomputable def update (x : FullConfig V β) (v : V) (val : β v) : FullConfig V β :=
  fun u =>
    by
      classical
      by_cases h : u = v
      · subst h; exact val
      · exact x u

/-- Two configurations agree on a finite set of variables. -/
def agreeOn (x y : FullConfig V β) (S : Finset V) : Prop :=
  ∀ v ∈ S, x v = y v

lemma agreeOn_union_left {x y : FullConfig V β} {S T : Finset V} :
    agreeOn x y (S ∪ T) → agreeOn x y S := by
  intro h v hv
  exact h v (Finset.mem_union.mpr (Or.inl hv))

lemma agreeOn_union_right {x y : FullConfig V β} {S T : Finset V} :
    agreeOn x y (S ∪ T) → agreeOn x y T := by
  intro h v hv
  exact h v (Finset.mem_union.mpr (Or.inr hv))

lemma agreeOn_update_of_not_mem
    {x : FullConfig V β} {v : V} {val : β v} {S : Finset V} (hv : v ∉ S) :
    agreeOn (update x v val) x S := by
  intro u hu
  classical
  have huv : u ≠ v := by
    intro h
    exact hv (h ▸ hu)
  simp [update, huv]

lemma agreeOn_update
    {x y : FullConfig V β} {v : V} {val : β v} {S : Finset V}
    (h : agreeOn x y (S.erase v)) :
    agreeOn (update x v val) (update y v val) S := by
  intro u hu
  classical
  by_cases huv : u = v
  · subst huv
    simp [update]
  · have : u ∈ S.erase v := by
      exact Finset.mem_erase.mpr ⟨huv, hu⟩
    have hxy := h u this
    simp [update, huv, hxy]

/-! ## Valuations -/

/-- A valuation with an explicit finite scope. -/
structure Valuation (V : Type*) (β : V → Type*) (K : Type*) where
  scope : Finset V
  val : FullConfig V β → K

/-! ## Scope membership predicate -/

/-- Boolean test: does a valuation mention variable `v` in its scope? -/
def hasVar (v : V) (f : Valuation V β K) : Bool :=
  decide (v ∈ f.scope)

lemma hasVar_true_iff (v : V) (f : Valuation V β K) :
    hasVar (V := V) (β := β) (K := K) v f = true ↔ v ∈ f.scope := by
  simp [hasVar]

lemma hasVar_false_iff (v : V) (f : Valuation V β K) :
    hasVar (V := V) (β := β) (K := K) v f = false ↔ v ∉ f.scope := by
  simp [hasVar]

namespace Valuation

omit [DecidableEq V] in
@[ext]
theorem ext {φ ψ : Valuation V β K}
    (hscope : φ.scope = ψ.scope)
    (hval : ∀ x, φ.val x = ψ.val x) : φ = ψ := by
  cases φ with
  | mk scope₁ val₁ =>
    cases ψ with
    | mk scope₂ val₂ =>
      cases hscope
      have hfun : val₁ = val₂ := funext hval
      simp [hfun]

end Valuation

/-- A valuation respects its declared scope (depends only on those variables). -/
def RespectsScope {V : Type*} {β : V → Type*} {K : Type*}
    (φ : Valuation V β K) : Prop :=
  ∀ x y, agreeOn x y φ.scope → φ.val x = φ.val y

/-- The empty-scope valuation (constant 1). -/
noncomputable def oneValuation (V : Type*) (β : V → Type*) (K : Type*)
    [One K] : Valuation V β K :=
  ⟨∅, fun _ => 1⟩

/-- Combine two valuations (pointwise multiplication, scope union). -/
noncomputable def combine (φ ψ : Valuation V β K) [Mul K] : Valuation V β K :=
  ⟨φ.scope ∪ ψ.scope, fun x => φ.val x * ψ.val x⟩

lemma scope_combine (φ ψ : Valuation V β K) [Mul K] :
    (combine (φ := φ) (ψ := ψ)).scope = φ.scope ∪ ψ.scope := by
  rfl

lemma respectsScope_one (V : Type*) (β : V → Type*) (K : Type*) [One K] :
    RespectsScope (oneValuation V β K) := by
  intro _ _ _; rfl

lemma respectsScope_combine
    {φ ψ : Valuation V β K} [Mul K]
    (hφ : RespectsScope φ) (hψ : RespectsScope ψ) :
    RespectsScope (combine (φ := φ) (ψ := ψ)) := by
  intro x y hxy
  have hφ' : φ.val x = φ.val y := hφ x y (agreeOn_union_left hxy)
  have hψ' : ψ.val x = ψ.val y := hψ x y (agreeOn_union_right hxy)
  simp [combine, hφ', hψ']

/-- Sum out a variable from a valuation. -/
noncomputable def sumOut (φ : Valuation V β K) (v : V)
    [Fintype (β v)] [AddCommMonoid K] : Valuation V β K :=
  by
    classical
    by_cases hv : v ∈ φ.scope
    · refine ⟨φ.scope.erase v, ?_⟩
      intro x
      exact (Finset.univ : Finset (β v)).sum (fun val =>
        φ.val (update x v val))
    · exact φ

lemma sumOut_scope (φ : Valuation V β K) (v : V)
    [Fintype (β v)] [AddCommMonoid K] :
    (sumOut (φ := φ) v).scope = φ.scope.erase v := by
  classical
  by_cases hv : v ∈ φ.scope
  · simp [sumOut, hv]
  · simp [sumOut, hv, Finset.erase_eq_of_notMem]

lemma erase_union_left (s t : Finset V) (v : V) (hv : v ∉ t) :
    (s ∪ t).erase v = s.erase v ∪ t := by
  ext u
  by_cases h : u = v
  · subst h
    simp [hv]
  · simp [Finset.mem_union, Finset.mem_erase, h]

lemma sumOut_of_not_mem (φ : Valuation V β K) (v : V)
    [Fintype (β v)] [AddCommMonoid K] (hv : v ∉ φ.scope) :
    sumOut (φ := φ) v = φ := by
  classical
  simp [sumOut, hv]

lemma respectsScope_sumOut
    {φ : Valuation V β K} (hφ : RespectsScope φ) (v : V)
    [Fintype (β v)] [AddCommMonoid K] :
    RespectsScope (sumOut (φ := φ) v) := by
  classical
  by_cases hv : v ∈ φ.scope
  · intro x y hxy
    have hxy' : agreeOn x y (φ.scope.erase v) := by
      simpa [sumOut, hv] using hxy
    have hterm : ∀ val : β v,
        φ.val (update x v val) = φ.val (update y v val) := by
      intro val
      have hxy'' : agreeOn (update x v val) (update y v val) φ.scope :=
        agreeOn_update (v := v) (val := val) (S := φ.scope) hxy'
      exact hφ _ _ hxy''
    have hsum :
        (∑ val : β v, φ.val (update x v val)) =
          (∑ val : β v, φ.val (update y v val)) := by
      refine Finset.sum_congr rfl ?_
      intro val _
      exact hterm val
    simp [sumOut, hv, hsum]
  · simpa [sumOut, hv] using hφ

lemma sumOut_combine_of_not_mem
    {φ ψ : Valuation V β K} (v : V)
    [Fintype (β v)] [CommSemiring K]
    (hψ : RespectsScope ψ) (hv : v ∉ ψ.scope) :
    sumOut (φ := combine (φ := φ) (ψ := ψ)) v =
      combine (φ := sumOut (φ := φ) v) (ψ := ψ) := by
  classical
  by_cases hφ : v ∈ φ.scope
  · apply Valuation.ext
    · -- scope equality
      simp [sumOut, combine, hφ, erase_union_left (s := φ.scope) (t := ψ.scope) (v := v) hv]
    · intro x
      have hconst : ∀ val : β v, ψ.val (update x v val) = ψ.val x := by
        intro val
        have hxy : agreeOn (update x v val) x ψ.scope :=
          agreeOn_update_of_not_mem (x := x) (v := v) (val := val) hv
        exact hψ _ _ hxy
      calc
        (sumOut (φ := combine (φ := φ) (ψ := ψ)) v).val x
            = ∑ val : β v, φ.val (update x v val) * ψ.val (update x v val) := by
                simp [sumOut, hφ, combine]
        _ = ∑ val : β v, φ.val (update x v val) * ψ.val x := by
                refine Finset.sum_congr rfl ?_
                intro val _
                simp [hconst val]
        _ = (∑ val : β v, φ.val (update x v val)) * ψ.val x := by
                symm
                exact
                  Finset.sum_mul (s := (Finset.univ : Finset (β v)))
                    (f := fun val => φ.val (update x v val)) (a := ψ.val x)
        _ = (combine (φ := sumOut (φ := φ) v) (ψ := ψ)).val x := by
                simp [sumOut, hφ, combine]
  · apply Valuation.ext
    · ext u
      have hunion : v ∉ φ.scope ∪ ψ.scope := by
        intro hv'
        rcases Finset.mem_union.mp hv' with hv' | hv'
        · exact hφ hv'
        · exact hv hv'
      simp [sumOut, combine, hφ, hunion, Finset.mem_union]
    · intro x
      have hφ' : sumOut (φ := φ) v = φ := sumOut_of_not_mem (φ := φ) v hφ
      simp [sumOut, hφ, combine, hv]

/-! ## Combine-all and sum-out-all -/

noncomputable def combineAll (fs : List (Valuation V β K)) [One K] [Mul K] :
    Valuation V β K :=
  fs.foldr (fun f acc => combine (φ := f) (ψ := acc)) (oneValuation V β K)

noncomputable def sumOutAll (φ : Valuation V β K) (order : List V)
    [∀ v, Fintype (β v)] [AddCommMonoid K] : Valuation V β K :=
  order.foldl (fun acc v => sumOut (φ := acc) v) φ

lemma combine_comm (φ ψ : Valuation V β K) [CommMonoid K] :
    combine (φ := φ) (ψ := ψ) = combine (φ := ψ) (ψ := φ) := by
  apply Valuation.ext
  · ext v
    simp [combine, Finset.mem_union, or_comm]
  · intro x
    simp [combine, mul_comm]

lemma combine_assoc (φ ψ χ : Valuation V β K) [Semigroup K] :
    combine (φ := combine (φ := φ) (ψ := ψ)) (ψ := χ) =
      combine (φ := φ) (ψ := combine (φ := ψ) (ψ := χ)) := by
  apply Valuation.ext
  · ext v
    simp [combine, Finset.union_assoc]
  · intro x
    simp [combine, mul_assoc]

lemma combineAll_append (fs₁ fs₂ : List (Valuation V β K))
    [Monoid K] :
    combineAll (V := V) (β := β) (K := K) (fs₁ ++ fs₂) =
      combine (φ := combineAll (V := V) (β := β) (K := K) fs₁)
              (ψ := combineAll (V := V) (β := β) (K := K) fs₂) := by
  classical
  induction fs₁ with
  | nil =>
      simp [combineAll, combine, oneValuation]
  | cons f fs ih =>
      calc
        combineAll (V := V) (β := β) (K := K) (f :: fs ++ fs₂)
            = combine (φ := f)
                (ψ := combineAll (V := V) (β := β) (K := K) (fs ++ fs₂)) := by
                  simp [combineAll]
        _ = combine (φ := f)
              (ψ := combine (φ := combineAll (V := V) (β := β) (K := K) fs)
                        (ψ := combineAll (V := V) (β := β) (K := K) fs₂)) := by
                  simp [ih]
        _ = combine (φ := combine (φ := f)
                  (ψ := combineAll (V := V) (β := β) (K := K) fs))
                (ψ := combineAll (V := V) (β := β) (K := K) fs₂) := by
                  simp [combine_assoc]
        _ = combine (φ := combineAll (V := V) (β := β) (K := K) (f :: fs))
                (ψ := combineAll (V := V) (β := β) (K := K) fs₂) := by
                  simp [combineAll]

lemma combineAll_perm {fs fs' : List (Valuation V β K)} [CommMonoid K]
    (h : fs.Perm fs') :
    combineAll (V := V) (β := β) (K := K) fs =
      combineAll (V := V) (β := β) (K := K) fs' := by
  classical
  induction h with
  | nil =>
      rfl
  | cons a h ih =>
      have ih' := congrArg (fun t => combine (φ := a) (ψ := t)) ih
      simpa [combineAll] using ih'
  | swap a b l =>
      calc
        combineAll (V := V) (β := β) (K := K) (b :: a :: l)
            = combine (φ := b) (ψ := combine (φ := a) (ψ := combineAll (V := V) (β := β) (K := K) l)) := by
                simp [combineAll]
        _ = combine (φ := combine (φ := b) (ψ := a))
                (ψ := combineAll (V := V) (β := β) (K := K) l) := by
                simp [combine_assoc]
        _ = combine (φ := combine (φ := a) (ψ := b))
                (ψ := combineAll (V := V) (β := β) (K := K) l) := by
                simp [combine_comm]
        _ = combine (φ := a) (ψ := combine (φ := b) (ψ := combineAll (V := V) (β := β) (K := K) l)) := by
                simp [combine_assoc]
        _ = combineAll (V := V) (β := β) (K := K) (a :: b :: l) := by
                simp [combineAll]
  | trans h₁ h₂ ih₁ ih₂ =>
      simpa [ih₁] using ih₂

/-! ## RespectsScope: list utilities -/

def RespectsAll (fs : List (Valuation V β K)) : Prop :=
  ∀ f ∈ fs, RespectsScope f

lemma respectsScope_combineAll (fs : List (Valuation V β K))
    [One K] [Mul K] (h : RespectsAll (V := V) (β := β) (K := K) fs) :
    RespectsScope (combineAll (V := V) (β := β) (K := K) fs) := by
  classical
  induction fs with
  | nil =>
      simpa [combineAll] using
        (respectsScope_one (V := V) (β := β) (K := K))
  | cons f fs ih =>
      have hf : RespectsScope f := h f (by simp)
      have hfs : RespectsAll (V := V) (β := β) (K := K) fs := by
        intro g hg
        exact h g (by simp [hg])
      have ih' := ih hfs
      simpa [combineAll] using
        (respectsScope_combine (φ := f) (ψ := combineAll (V := V) (β := β) (K := K) fs) hf ih')

lemma not_mem_scope_combineAll (fs : List (Valuation V β K)) (v : V)
    [One K] [Mul K] (h : ∀ f ∈ fs, v ∉ f.scope) :
    v ∉ (combineAll (V := V) (β := β) (K := K) fs).scope := by
  classical
  induction fs with
  | nil =>
      simp [combineAll, oneValuation]
  | cons f fs ih =>
      have hf : v ∉ f.scope := h f (by simp)
      have hfs : ∀ g ∈ fs, v ∉ g.scope := by
        intro g hg
        exact h g (by simp [hg])
      have ih' := ih hfs
      intro hv
      have hv' : v ∈ f.scope ∪ (combineAll (V := V) (β := β) (K := K) fs).scope := by
        simpa [combineAll, combine] using hv
      rcases Finset.mem_union.mp hv' with hvf | hvr
      · exact hf hvf
      · exact ih' hvr

/-! ## Variable Elimination (valuation form) -/

noncomputable def eliminateVar (fs : List (Valuation V β K)) (v : V)
    [Fintype (β v)] [CommSemiring K] : List (Valuation V β K) :=
  let hit := fs.filter (hasVar (V := V) (β := β) (K := K) v)
  let rest := fs.filter (fun f => !(hasVar (V := V) (β := β) (K := K) v f))
  match hit with
  | [] => rest
  | _ =>
      let f := combineAll (V := V) (β := β) (K := K) hit
      sumOut (φ := f) v :: rest

noncomputable def eliminateVars (fs : List (Valuation V β K)) (order : List V)
    [∀ v, Fintype (β v)] [CommSemiring K] : List (Valuation V β K) :=
  order.foldl (fun acc v => eliminateVar (V := V) (β := β) (K := K) acc v) fs

omit [DecidableEq V] in
lemma perm_filter_partition (p : Valuation V β K → Bool) (fs : List (Valuation V β K)) :
    fs.Perm (fs.filter p ++ fs.filter (fun x => !p x)) := by
  classical
  -- helper: move a head element past a prefix
  have perm_cons_append :
      ∀ (a : Valuation V β K) (l₁ l₂ : List (Valuation V β K)),
        List.Perm (a :: l₁ ++ l₂) (l₁ ++ a :: l₂) := by
    intro a l₁ l₂
    have h : List.Perm ([a] ++ l₁) (l₁ ++ [a]) := by
      simpa using (List.perm_append_comm : List.Perm ([a] ++ l₁) (l₁ ++ [a]))
    -- append right with l₂
    simpa [List.append_assoc] using (h.append_right l₂)
  induction fs with
  | nil =>
      simp
  | cons a fs ih =>
      by_cases h : p a = true
      · simp [List.filter, h, ih, List.cons_append]
      · have h' : p a = false := by
          exact eq_false_of_ne_true h
        have ih' : fs.Perm (fs.filter p ++ fs.filter (fun x => !p x)) := ih
        have hcons : (a :: fs).Perm (a :: (fs.filter p ++ fs.filter (fun x => !p x))) := by
          exact ih'.cons a
        have hmid :
            List.Perm (a :: (fs.filter p ++ fs.filter (fun x => !p x)))
              (fs.filter p ++ a :: fs.filter (fun x => !p x)) :=
          perm_cons_append a (fs.filter p) (fs.filter (fun x => !p x))
        simpa [List.filter, h', List.cons_append, List.append_assoc] using hcons.trans hmid

/-! ## VE correctness spine -/

theorem combineAll_eliminateVar
    (fs : List (Valuation V β K)) (v : V)
    [Fintype (β v)] [CommSemiring K]
    (h : RespectsAll (V := V) (β := β) (K := K) fs) :
    combineAll (V := V) (β := β) (K := K) (eliminateVar (V := V) (β := β) (K := K) fs v) =
      sumOut (φ := combineAll (V := V) (β := β) (K := K) fs) v := by
  classical
  -- Split list into hit/rest by scope membership.
  let hit := fs.filter (hasVar (V := V) (β := β) (K := K) v)
  let rest := fs.filter (fun f => !(hasVar (V := V) (β := β) (K := K) v f))
  have hperm : fs.Perm (hit ++ rest) := by
    simpa [hit, rest] using perm_filter_partition (V := V) (β := β) (K := K)
      (p := hasVar (V := V) (β := β) (K := K) v) fs
  have hcombine_perm :
      combineAll (V := V) (β := β) (K := K) fs =
        combineAll (V := V) (β := β) (K := K) (hit ++ rest) := by
    exact combineAll_perm (V := V) (β := β) (K := K) hperm
  by_cases hhit : hit = []
  · -- no hit: elimination is just rest (and v not in any scope)
    have hrest_not_mem : ∀ f ∈ rest, v ∉ f.scope := by
      intro f hf
      have hpred :
          (fun f => !(hasVar (V := V) (β := β) (K := K) v f)) f := by
        exact List.of_mem_filter (p := fun f => !(hasVar (V := V) (β := β) (K := K) v f)) hf
      have hfalse : hasVar (V := V) (β := β) (K := K) v f = false := by
        simpa using hpred
      exact (hasVar_false_iff (V := V) (β := β) (K := K) v f).1 hfalse
    have hrest_scope :
        v ∉ (combineAll (V := V) (β := β) (K := K) rest).scope := by
      exact not_mem_scope_combineAll (V := V) (β := β) (K := K) rest v hrest_not_mem
    have hcombine_rest :
        combineAll (V := V) (β := β) (K := K) fs =
          combineAll (V := V) (β := β) (K := K) rest := by
      simpa [hhit] using hcombine_perm
    have hstep :
        combineAll (V := V) (β := β) (K := K)
          (eliminateVar (V := V) (β := β) (K := K) fs v) =
          combineAll (V := V) (β := β) (K := K) rest := by
      simp [eliminateVar, hit, rest, hhit, combineAll]
    have hsum :
        sumOut (φ := combineAll (V := V) (β := β) (K := K) fs) v =
          combineAll (V := V) (β := β) (K := K) rest := by
      calc
        sumOut (φ := combineAll (V := V) (β := β) (K := K) fs) v
            = sumOut (φ := combineAll (V := V) (β := β) (K := K) rest) v := by
                simp [hcombine_rest]
        _ = combineAll (V := V) (β := β) (K := K) rest := by
                exact sumOut_of_not_mem (φ := combineAll (V := V) (β := β) (K := K) rest) v hrest_scope
    exact hstep.trans hsum.symm
  · -- there is some hit: main VE step
    have hrest_not_mem : ∀ f ∈ rest, v ∉ f.scope := by
      intro f hf
      have hpred :
          (fun f => !(hasVar (V := V) (β := β) (K := K) v f)) f := by
        exact List.of_mem_filter (p := fun f => !(hasVar (V := V) (β := β) (K := K) v f)) hf
      have hfalse : hasVar (V := V) (β := β) (K := K) v f = false := by
        simpa using hpred
      exact (hasVar_false_iff (V := V) (β := β) (K := K) v f).1 hfalse
    have hrest_scope :
        v ∉ (combineAll (V := V) (β := β) (K := K) rest).scope := by
      exact not_mem_scope_combineAll (V := V) (β := β) (K := K) rest v hrest_not_mem
    have hrest_respects :
        RespectsScope (combineAll (V := V) (β := β) (K := K) rest) := by
      have : RespectsAll (V := V) (β := β) (K := K) rest := by
        intro f hf
        exact h f (by
          exact List.mem_of_mem_filter hf)
      exact respectsScope_combineAll (V := V) (β := β) (K := K) rest this
    -- combineAll fs = combine hit rest
    have hsplit :
        combineAll (V := V) (β := β) (K := K) fs =
          combine (φ := combineAll (V := V) (β := β) (K := K) hit)
                  (ψ := combineAll (V := V) (β := β) (K := K) rest) := by
      calc
        combineAll (V := V) (β := β) (K := K) fs
            = combineAll (V := V) (β := β) (K := K) (hit ++ rest) := hcombine_perm
        _ = combine (φ := combineAll (V := V) (β := β) (K := K) hit)
                    (ψ := combineAll (V := V) (β := β) (K := K) rest) := by
                      simpa using
                        (combineAll_append (V := V) (β := β) (K := K) hit rest)
    -- use commutation of sumOut with a factor that does not mention v
    have hcomm :
        sumOut (φ := combine (φ := combineAll (V := V) (β := β) (K := K) hit)
                      (ψ := combineAll (V := V) (β := β) (K := K) rest)) v =
          combine (φ := sumOut (φ := combineAll (V := V) (β := β) (K := K) hit) v)
                  (ψ := combineAll (V := V) (β := β) (K := K) rest) := by
      exact sumOut_combine_of_not_mem (v := v) (φ := combineAll (V := V) (β := β) (K := K) hit)
        (ψ := combineAll (V := V) (β := β) (K := K) rest) hrest_respects hrest_scope
    -- finish
    have hstep :
        combineAll (V := V) (β := β) (K := K)
          (eliminateVar (V := V) (β := β) (K := K) fs v) =
          combine (φ := sumOut (φ := combineAll (V := V) (β := β) (K := K) hit) v)
                  (ψ := combineAll (V := V) (β := β) (K := K) rest) := by
      simp [eliminateVar, hit, rest, combineAll]
    have hcomm' :
        combine (φ := sumOut (φ := combineAll (V := V) (β := β) (K := K) hit) v)
                (ψ := combineAll (V := V) (β := β) (K := K) rest) =
          sumOut (φ := combineAll (V := V) (β := β) (K := K) fs) v := by
      calc
        combine (φ := sumOut (φ := combineAll (V := V) (β := β) (K := K) hit) v)
                (ψ := combineAll (V := V) (β := β) (K := K) rest)
            = sumOut (φ := combine (φ := combineAll (V := V) (β := β) (K := K) hit)
                               (ψ := combineAll (V := V) (β := β) (K := K) rest)) v := by
                symm
                exact hcomm
        _ = sumOut (φ := combineAll (V := V) (β := β) (K := K) fs) v := by
                simp [hsplit]
    exact hstep.trans hcomm'

theorem combineAll_eliminateVars
    (fs : List (Valuation V β K)) (order : List V)
    [∀ v, Fintype (β v)] [CommSemiring K]
    (h : RespectsAll (V := V) (β := β) (K := K) fs) :
    combineAll (V := V) (β := β) (K := K) (eliminateVars (V := V) (β := β) (K := K) fs order) =
      sumOutAll (φ := combineAll (V := V) (β := β) (K := K) fs) order := by
  classical
  induction order generalizing fs with
  | nil =>
      simp [eliminateVars, sumOutAll]
  | cons v vs ih =>
      have h' : RespectsAll (V := V) (β := β) (K := K)
          (eliminateVar (V := V) (β := β) (K := K) fs v) := by
        -- elimination preserves RespectsScope
        have hhit : RespectsAll (V := V) (β := β) (K := K)
            (fs.filter (hasVar (V := V) (β := β) (K := K) v)) := by
          intro g hg
          exact h g (List.mem_of_mem_filter hg)
        have hrest : RespectsAll (V := V) (β := β) (K := K)
            (fs.filter (fun g => !(hasVar (V := V) (β := β) (K := K) v g))) := by
          intro g hg
          exact h g (List.mem_of_mem_filter hg)
        by_cases hhit_empty :
            (fs.filter (hasVar (V := V) (β := β) (K := K) v)) = []
        · simp [eliminateVar, hhit_empty] at *
          exact hrest
        · intro f hf
          simp [eliminateVar] at hf
          rcases hf with rfl | hf
          · have hhit' := respectsScope_combineAll (V := V) (β := β) (K := K)
              (fs.filter (hasVar (V := V) (β := β) (K := K) v)) hhit
            exact respectsScope_sumOut (φ := combineAll (V := V) (β := β) (K := K)
              (fs.filter (hasVar (V := V) (β := β) (K := K) v))) hhit' v
          · have hf' :
                f ∈ fs.filter (fun g => !(hasVar (V := V) (β := β) (K := K) v g)) := by
                exact List.mem_filter.mpr ⟨hf.1, by simp [hf.2]⟩
            exact hrest _ hf'
      have hstep :=
        combineAll_eliminateVar (V := V) (β := β) (K := K) (fs := fs) v h
      have ih' := ih (fs := eliminateVar (V := V) (β := β) (K := K) fs v) h'
      simpa [eliminateVars, sumOutAll, hstep] using ih'

end Mettapedia.ProbabilityTheory.BayesianNetworks
