import Mettapedia.TypeTheory.UniverseLevel.Bounded

/-!
# Conservative extension of level comparisons along an embedding

An embedding of level orders preserves and reflects the order, the least level
and the successor, and therefore the finite levels. Mapping the constants of a
level expression along an embedding leaves parameters, successor and maximum
in place. Evaluation, canonical forms and the canonical order test commute
with that map. A comparison of two level expressions therefore has the same
answer before and after the embedding. The comparison in the larger order
quantifies over every valuation, including those outside the image of the
embedding.

The finite levels embed into every level order, so a comparison of expressions
whose constants are natural numbers has the same answer over the natural
numbers and over any level order. Initiality of the embedding is not used.

With bounded variables the bounds are mapped too, and the embedding must be
initial: an initial embedding sends successor bounds to successor bounds and
limit bounds to limit bounds, so the comparison under bounds, and the supremum
over a bounded variable, are preserved. The embedding of the finite levels is
initial.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

open LevelOrder

variable {L L' : Type}

/-! ## Mapping constants -/

/-- Send each constant through `f`. Parameters, successor and maximum stay. -/
def LevelExpr.map (f : L → L') : LevelExpr L → LevelExpr L'
  | .const c => .const (f c)
  | .param i => .param i
  | .succ e => .succ (e.map f)
  | .max e₁ e₂ => .max (e₁.map f) (e₂.map f)

theorem LevelExpr.map_id : ∀ e : LevelExpr L, e.map (fun l => l) = e
  | .const _ => rfl
  | .param _ => rfl
  | .succ e => congrArg LevelExpr.succ (map_id e)
  | .max e₁ e₂ => congrArg₂ LevelExpr.max (map_id e₁) (map_id e₂)

theorem LevelExpr.map_map {L'' : Type} (g : L' → L'') (f : L → L') :
    ∀ e : LevelExpr L, (e.map f).map g = e.map (fun l => g (f l))
  | .const _ => rfl
  | .param _ => rfl
  | .succ e => congrArg LevelExpr.succ (map_map g f e)
  | .max e₁ e₂ => congrArg₂ LevelExpr.max (map_map g f e₁) (map_map g f e₂)

/-- Mapping commutes with simultaneous substitution. -/
theorem LevelExpr.map_subst (f : L → L') (σ : Nat → LevelExpr L) :
    ∀ e : LevelExpr L, (e.subst σ).map f = (e.map f).subst (fun i => (σ i).map f)
  | .const _ => rfl
  | .param _ => rfl
  | .succ e => congrArg LevelExpr.succ (map_subst f σ e)
  | .max e₁ e₂ => congrArg₂ LevelExpr.max (map_subst f σ e₁) (map_subst f σ e₂)

variable [LevelOrder L] [LevelOrder L']

/-- Evaluation of a mapped expression under a mapped valuation is the image of
the evaluation. -/
theorem LevelExpr.eval_map (f : Embedding L L') (v : Nat → L) :
    ∀ e : LevelExpr L,
      LevelExpr.eval (fun i => f (v i)) (e.map f) = f (LevelExpr.eval v e)
  | .const _ => rfl
  | .param _ => rfl
  | .succ e => by
    rw [LevelExpr.map, LevelExpr.eval, LevelExpr.eval, eval_map f v e, f.map_succ]
  | .max e₁ e₂ => by
    rw [LevelExpr.map, LevelExpr.eval, LevelExpr.eval, eval_map f v e₁, eval_map f v e₂,
      f.map_max]

/-! ## Canonical forms -/

namespace LevelNF

omit [LevelOrder L] [LevelOrder L'] in
/-- Map the constant of a canonical form and keep its parameter offsets. -/
def map (f : L → L') (nf : LevelNF L) : LevelNF L' :=
  ⟨f nf.constPart, nf.params⟩

omit [LevelOrder L'] in
private theorem mk_congr {c₁ c₂ : L'} {p₁ p₂ : List (Nat × Nat)}
    (constants : c₁ = c₂) (parameters : p₁ = p₂) :
    (⟨c₁, p₁⟩ : LevelNF L') = ⟨c₂, p₂⟩ := by
  cases constants
  cases parameters
  rfl

/-- An embedding preserves the absorption test: a constant lies under a finite
level exactly when its image does. -/
theorem map_absorb (f : Embedding L L') (c : L) (s : Nat) :
    f (if c ≤ ofNat s then bot else c) =
      if f c ≤ ofNat s then bot else f c := by
  have flip : f c ≤ ofNat s ↔ c ≤ ofNat s := by
    rw [← f.map_ofNat s, f.le_iff]
  cases decision : decide (c ≤ ofNat s) with
  | true =>
    have held := of_decide_eq_true decision
    rw [if_pos held, if_pos (flip.mpr held), f.map_bot]
  | false =>
    have missed := of_decide_eq_false decision
    rw [if_neg missed, if_neg (flip.not.mpr missed)]

theorem map_succNF (f : Embedding L L') :
    ∀ nf : LevelNF L, succNF (map f nf) = map f (succNF nf)
  | ⟨c, ps⟩ => by
    unfold map
    rw [succNF_eq, succNF_eq]
    apply mk_congr _ rfl
    rw [← f.map_succ]
    exact (map_absorb f (succ c) (supOffsets (ps.map fun (i, k) => (i, k + 1)))).symm

theorem map_mergeNF (f : Embedding L L') :
    ∀ nf₁ nf₂ : LevelNF L, mergeNF (map f nf₁) (map f nf₂) = map f (mergeNF nf₁ nf₂)
  | ⟨c₁, p₁⟩, ⟨c₂, p₂⟩ => by
    unfold map
    rw [mergeNF_eq, mergeNF_eq]
    apply mk_congr _ rfl
    rw [← f.map_max]
    exact (map_absorb f (max c₁ c₂)
      (supOffsets (p₁.foldl (fun acc (ik : Nat × Nat) => insertParam ik.1 ik.2 acc) p₂))).symm

/-- Normalization commutes with an embedding. -/
theorem map_normalize (f : Embedding L L') :
    ∀ e : LevelExpr L, normalize (e.map f) = map f (normalize e)
  | .const _ => rfl
  | .param _ => by
    rw [LevelExpr.map, normalize, normalize]
    unfold map
    rw [f.map_bot]
  | .succ e => by
    rw [LevelExpr.map, normalize, normalize, map_normalize f e, map_succNF]
  | .max e₁ e₂ => by
    rw [LevelExpr.map, normalize, normalize, map_normalize f e₁, map_normalize f e₂, map_mergeNF]

theorem map_injective (f : Embedding L L') {nf₁ nf₂ : LevelNF L}
    (h : map f nf₁ = map f nf₂) : nf₁ = nf₂ := by
  have constants : nf₁.constPart = nf₂.constPart :=
    f.injective (congrArg (fun nf : LevelNF L' => nf.constPart) h)
  have parameters : nf₁.params = nf₂.params :=
    congrArg (fun nf : LevelNF L' => nf.params) h
  cases nf₁
  cases nf₂
  cases constants
  cases parameters
  rfl

/-- The canonical order test is preserved and reflected by an embedding. -/
theorem canonicalLe_map (f : Embedding L L') (nf₁ nf₂ : LevelNF L) :
    CanonicalLe (map f nf₁) (map f nf₂) ↔ CanonicalLe nf₁ nf₂ := by
  unfold CanonicalLe
  have constants :
      f nf₁.constPart ≤ max (f nf₂.constPart) (ofNat (supOffsets nf₂.params)) ↔
        nf₁.constPart ≤ max nf₂.constPart (ofNat (supOffsets nf₂.params)) := by
    rw [← f.map_ofNat (supOffsets nf₂.params), ← f.map_max, f.le_iff]
  exact and_congr constants Iff.rfl

/-! ## Conservativity -/

/-- **Order is conservative along an embedding.** The left side quantifies over
every valuation into the larger order. -/
theorem level_le_conservative (f : Embedding L L') (e₁ e₂ : LevelExpr L) :
    (∀ v' : Nat → L',
        LevelExpr.eval v' (e₁.map f) ≤ LevelExpr.eval v' (e₂.map f)) ↔
      ∀ v : Nat → L, LevelExpr.eval v e₁ ≤ LevelExpr.eval v e₂ := by
  constructor
  · intro held
    have canonical := (normalize_le_iff (e₁.map f) (e₂.map f)).mpr held
    rw [map_normalize f e₁, map_normalize f e₂] at canonical
    exact (normalize_le_iff e₁ e₂).mp ((canonicalLe_map f _ _).mp canonical)
  · intro held
    have canonical := (normalize_le_iff e₁ e₂).mpr held
    have mapped := (canonicalLe_map f _ _).mpr canonical
    rw [← map_normalize f e₁, ← map_normalize f e₂] at mapped
    exact (normalize_le_iff (e₁.map f) (e₂.map f)).mp mapped

/-- **Equality is conservative along an embedding.** -/
theorem level_eq_conservative (f : Embedding L L') (e₁ e₂ : LevelExpr L) :
    (∀ v' : Nat → L',
        LevelExpr.eval v' (e₁.map f) = LevelExpr.eval v' (e₂.map f)) ↔
      ∀ v : Nat → L, LevelExpr.eval v e₁ = LevelExpr.eval v e₂ := by
  constructor
  · intro held
    have normal := (normalize_eq_iff (e₁.map f) (e₂.map f)).mpr held
    rw [map_normalize f e₁, map_normalize f e₂] at normal
    exact (normalize_eq_iff e₁ e₂).mp (map_injective f normal)
  · intro held
    have normal := (normalize_eq_iff e₁ e₂).mpr held
    have mapped : normalize (e₁.map f) = normalize (e₂.map f) := by
      rw [map_normalize f e₁, map_normalize f e₂, normal]
    exact (normalize_eq_iff (e₁.map f) (e₂.map f)).mp mapped

end LevelNF

/-! ## The finite levels -/

/-- A comparison of expressions with natural-number constants has the same
answer over the natural numbers and over `L`. -/
theorem nat_level_le_iff {M : Type} [LevelOrder M] (e₁ e₂ : LevelExpr Nat) :
    (∀ v : Nat → M,
        LevelExpr.eval v (e₁.map (Embedding.ofNat M)) ≤
          LevelExpr.eval v (e₂.map (Embedding.ofNat M))) ↔
      ∀ v : Nat → Nat, LevelExpr.eval v e₁ ≤ LevelExpr.eval v e₂ :=
  LevelNF.level_le_conservative (Embedding.ofNat M) e₁ e₂

/-- Equality of expressions with natural-number constants has the same answer
over the natural numbers and over `L`. -/
theorem nat_level_eq_iff {M : Type} [LevelOrder M] (e₁ e₂ : LevelExpr Nat) :
    (∀ v : Nat → M,
        LevelExpr.eval v (e₁.map (Embedding.ofNat M)) =
          LevelExpr.eval v (e₂.map (Embedding.ofNat M))) ↔
      ∀ v : Nat → Nat, LevelExpr.eval v e₁ = LevelExpr.eval v e₂ :=
  LevelNF.level_eq_conservative (Embedding.ofNat M) e₁ e₂

/-! ## Bounded variables -/

section Bounded

open PredLevelOrder LevelBounds

variable {K K' : Type} [PredLevelOrder K] [PredLevelOrder K']

/-- Map every bound through `f`. -/
def LevelBounds.map (f : K → K') (Δ : LevelBounds K) : LevelBounds K' :=
  fun i => (Δ i).map f

/-- An embedding preserves and reflects positivity of the bounds. -/
theorem LevelBounds.positive_map (f : Embedding K K') {Δ : LevelBounds K} :
    (LevelBounds.map f Δ).Positive ↔ Δ.Positive := by
  constructor
  · intro pos i c h
    have h' : LevelBounds.map f Δ i = some (f c) := by
      show (Δ i).map f = some (f c)
      rw [h]
      rfl
    have := pos i (f c) h'
    rwa [← f.map_bot, f.lt_iff] at this
  · intro pos i c' h
    have h' : (Δ i).map f = some c' := h
    cases hc : Δ i with
    | none => rw [hc] at h'; exact nomatch h'
    | some c =>
      rw [hc] at h'
      obtain rfl : f c = c' := Option.some.inj h'
      rw [← f.map_bot, f.lt_iff]
      exact pos i c hc

/-- What a canonical form exposes without a variable commutes with an embedding. -/
theorem LevelNF.floorWithout_map (f : Embedding K K') (nf : LevelNF K) (i : Nat) :
    LevelNF.floorWithout (LevelNF.map f nf) i = f (LevelNF.floorWithout nf i) := by
  unfold LevelNF.floorWithout LevelNF.map
  rw [f.map_max, f.map_ofNat]

/-- An initial embedding preserves and reflects the test that a bound fits. -/
theorem LevelBounds.boundFits_map {f : Embedding K K'} (initial : f.Initial) (β : K)
    (k : Nat) (D : K) : BoundFits (f β) k (f D) ↔ BoundFits β k D := by
  unfold BoundFits
  rw [pred?_map initial β]
  cases pred? β with
  | none => exact f.le_iff
  | some γ =>
    show addNat (f γ) k ≤ f D ↔ addNat γ k ≤ D
    rw [← f.map_addNat, f.le_iff]

/-- An initial embedding preserves and reflects the canonical order test under bounds. -/
theorem LevelBounds.canonicalLeUnder_map {f : Embedding K K'} (initial : f.Initial)
    (Δ : LevelBounds K) (nf₁ nf₂ : LevelNF K) :
    CanonicalLeUnder (LevelBounds.map f Δ) (LevelNF.map f nf₁) (LevelNF.map f nf₂) ↔
      CanonicalLeUnder Δ nf₁ nf₂ := by
  unfold CanonicalLeUnder
  have constants :
      f nf₁.constPart ≤ max (f nf₂.constPart) (ofNat (LevelNF.supOffsets nf₂.params)) ↔
        nf₁.constPart ≤ max nf₂.constPart (ofNat (LevelNF.supOffsets nf₂.params)) := by
    rw [← f.map_ofNat (LevelNF.supOffsets nf₂.params), ← f.map_max, f.le_iff]
  refine and_congr constants (forall_congr' fun ik => forall_congr' fun _ => ?_)
  unfold AtomLeUnder
  refine or_congr Iff.rfl ?_
  show (match (Δ ik.1).map f with
      | some β => BoundFits β ik.2 (LevelNF.floorWithout (LevelNF.map f nf₂) ik.1)
      | none => False) ↔ _
  cases Δ ik.1 with
  | none => exact Iff.rfl
  | some β =>
    show BoundFits (f β) ik.2 (LevelNF.floorWithout (LevelNF.map f nf₂) ik.1) ↔
      BoundFits β ik.2 (LevelNF.floorWithout nf₂ ik.1)
    rw [LevelNF.floorWithout_map]
    exact LevelBounds.boundFits_map initial β ik.2 _

/-- **Order under bounds is conservative along an initial embedding.** Under positive
bounds, a comparison of two level expressions has the same answer before and after the
constants and the bounds are mapped. -/
theorem LevelBounds.leUnder_conservative {f : Embedding K K'} (initial : f.Initial)
    {Δ : LevelBounds K} (pos : Δ.Positive) (e₁ e₂ : LevelExpr K) :
    LeUnder (LevelBounds.map f Δ) (e₁.map f) (e₂.map f) ↔ LeUnder Δ e₁ e₂ := by
  rw [← leUnder_iff_canonical pos e₁ e₂,
    ← leUnder_iff_canonical ((LevelBounds.positive_map f).mpr pos) (e₁.map f) (e₂.map f),
    LevelNF.map_normalize f e₁, LevelNF.map_normalize f e₂]
  exact LevelBounds.canonicalLeUnder_map initial Δ _ _

/-- **Equality under bounds is conservative along an initial embedding.** -/
theorem LevelBounds.eqUnder_conservative {f : Embedding K K'} (initial : f.Initial)
    {Δ : LevelBounds K} (pos : Δ.Positive) (e₁ e₂ : LevelExpr K) :
    EqUnder (LevelBounds.map f Δ) (e₁.map f) (e₂.map f) ↔ EqUnder Δ e₁ e₂ := by
  rw [eqUnder_iff, eqUnder_iff, LevelBounds.leUnder_conservative initial pos,
    LevelBounds.leUnder_conservative initial pos]

omit [PredLevelOrder K] [PredLevelOrder K'] in
/-- Occurrence of a variable is unchanged by mapping the constants. -/
theorem LevelExpr.occurs_map (f : K → K') (x : Nat) :
    ∀ e : LevelExpr K, LevelExpr.occurs x (e.map f) = LevelExpr.occurs x e
  | .const _ => rfl
  | .param _ => rfl
  | .succ e => LevelExpr.occurs_map f x e
  | .max e₁ e₂ => by
    show (LevelExpr.occurs x (e₁.map f) || LevelExpr.occurs x (e₂.map f)) = _
    rw [LevelExpr.occurs_map f x e₁, LevelExpr.occurs_map f x e₂]
    rfl

omit [PredLevelOrder K] [PredLevelOrder K'] in
/-- Instantiating a variable by a closed level commutes with mapping the constants. -/
theorem LevelExpr.map_subst_instantiate (f : K → K') (x : Nat) (c : K) (e : LevelExpr K) :
    (e.subst (LevelExpr.instantiate x (.const c))).map f =
      (e.map f).subst (LevelExpr.instantiate x (.const (f c))) := by
  rw [LevelExpr.map_subst]
  congr 1
  funext i
  unfold LevelExpr.instantiate
  by_cases h : i = x
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- **The supremum over a bounded variable commutes with an initial embedding.** -/
theorem LevelExpr.boundedSup_map {f : Embedding K K'} (initial : f.Initial) (x : Nat)
    (c : K) (e : LevelExpr K) :
    (LevelExpr.boundedSup x c e).map f = LevelExpr.boundedSup x (f c) (e.map f) := by
  unfold LevelExpr.boundedSup
  rw [pred?_map initial c]
  cases pred? c with
  | some p => exact LevelExpr.map_subst_instantiate f x p e
  | none =>
    show (if LevelExpr.occurs x e then
        LevelExpr.max (e.subst (LevelExpr.instantiate x (.const bot))) (.const c)
        else e.subst (LevelExpr.instantiate x (.const bot))).map f =
      if LevelExpr.occurs x (e.map f) then
        LevelExpr.max ((e.map f).subst (LevelExpr.instantiate x (.const bot))) (.const (f c))
        else (e.map f).subst (LevelExpr.instantiate x (.const bot))
    rw [LevelExpr.occurs_map]
    cases LevelExpr.occurs x e with
    | true =>
      rw [if_pos rfl, if_pos rfl]
      show LevelExpr.max ((e.subst (LevelExpr.instantiate x (.const bot))).map f)
        (.const (f c)) = _
      rw [LevelExpr.map_subst_instantiate, f.map_bot]
    | false =>
      rw [if_neg (by simp), if_neg (by simp), LevelExpr.map_subst_instantiate, f.map_bot]

/-- A comparison under bounds of expressions with natural-number constants and bounds has
the same answer over the natural numbers and over any level order with predecessors. -/
theorem nat_leUnder_iff {M : Type} [PredLevelOrder M] {Δ : LevelBounds Nat} (pos : Δ.Positive)
    (e₁ e₂ : LevelExpr Nat) :
    LeUnder (LevelBounds.map (Embedding.ofNat M) Δ) (e₁.map (Embedding.ofNat M))
        (e₂.map (Embedding.ofNat M)) ↔
      LeUnder Δ e₁ e₂ :=
  LevelBounds.leUnder_conservative (Embedding.ofNat_initial M) pos e₁ e₂

end Bounded

/-! ## Controls -/

/-- Over the natural numbers, the constant `0` lies under the constant `1`. -/
theorem nat_zero_le_one :
    ∀ v : Nat → Nat, LevelExpr.eval v (.const 0) ≤ LevelExpr.eval v (.const 1) := by
  decide

/-- The same comparison, transported along the embedding of the finite levels. -/
theorem nat_zero_le_one_embedded {M : Type} [LevelOrder M] :
    ∀ v : Nat → M,
      LevelExpr.eval v ((LevelExpr.const (0 : Nat)).map (Embedding.ofNat M)) ≤
        LevelExpr.eval v ((LevelExpr.const (1 : Nat)).map (Embedding.ofNat M)) :=
  (nat_level_le_iff (.const 0) (.const 1)).mpr nat_zero_le_one

/-- The constant map onto the least natural number. -/
def collapseToBot (_n : Nat) : Nat := 0

/-- That map does not commute with the successor, so it is not an embedding. -/
theorem collapseToBot_not_embedding :
    ¬ ∃ f : Embedding Nat Nat, ∀ n, f n = collapseToBot n := by
  intro ⟨f, agrees⟩
  have swap : (0 : Nat) = 1 := by
    calc
      (0 : Nat) = f 1 := (agrees 1).symm
      _ = f (succ 0) := by rw [nat_succ]
      _ = succ (f 0) := f.map_succ 0
      _ = succ 0 := congrArg succ (agrees 0)
      _ = 1 := nat_succ 0
  exact Nat.zero_ne_one swap

/-- Mapping constants to the least level makes `const 1 ≤ const 0` true, while
the original comparison is false. -/
theorem collapse_identifies_one_with_zero :
    (∀ v : Nat → Nat,
        LevelExpr.eval v ((LevelExpr.const (1 : Nat)).map collapseToBot) ≤
          LevelExpr.eval v ((LevelExpr.const (0 : Nat)).map collapseToBot)) ∧
      ¬ ∀ v : Nat → Nat,
        LevelExpr.eval v (.const (1 : Nat)) ≤ LevelExpr.eval v (.const (0 : Nat)) := by
  constructor
  · intro _
    show (0 : Nat) ≤ 0
    exact le_refl _
  · intro held
    have reversed : (1 : Nat) ≤ 0 := held (fun _ => 0)
    exact Nat.not_succ_le_zero 0 reversed

/-- `ω` is not a finite level. -/
theorem omega_ne_finite (n : Nat) : Level.omega ≠ (Embedding.ofNat Level) n := by
  intro agrees
  have image : (Embedding.ofNat Level).toFun n = Level.ofNat n :=
    Level.levelOrder_ofNat n
  rw [image] at agrees
  exact lt_irrefl _ (agrees ▸ Level.ofNat_lt_omega n)

/-- The constant valuation at `ω` is a valuation into the ordinal notations
that is not the image of a valuation of the natural numbers. The comparison of
the finite constants `0` and `1` still holds at that valuation. -/
theorem omega_valuation_outside_image :
    LevelExpr.eval (fun _ => Level.omega)
        ((LevelExpr.const (0 : Nat)).map (Embedding.ofNat Level)) ≤
      LevelExpr.eval (fun _ => Level.omega)
        ((LevelExpr.const (1 : Nat)).map (Embedding.ofNat Level)) ∧
      ¬ ∃ v : Nat → Nat, ∀ i, Level.omega = (Embedding.ofNat Level) (v i) := by
  refine ⟨?_, ?_⟩
  · show (Embedding.ofNat Level).toFun 0 ≤ (Embedding.ofNat Level).toFun 1
    exact (Embedding.ofNat Level).le_iff.mpr (Nat.zero_le 1)
  · intro ⟨v, agrees⟩
    exact omega_ne_finite (v 0) (agrees 0)

end Mettapedia.TypeTheory.UniverseLevel
