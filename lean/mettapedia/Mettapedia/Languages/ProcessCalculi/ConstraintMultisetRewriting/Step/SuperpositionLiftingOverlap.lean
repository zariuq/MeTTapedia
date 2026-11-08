import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionLifting

/-!
# The variable-overlap case is redundant, and every ground inference lifts or is redundant

## Superposition at or below a variable

A ground superposition of `l ≈ r ∨ D` into the main premise `Cθ` at a position at or below a variable
`x` of `C` (`AtVariable`: `L.lhs = c'[x]` and `xθ = d[l]`) is redundant (`overlap_redundant`): with
`θ'` the grounding that replaces `xθ = d[l]` by `d[r]`,

* `Cθ'` is a ground instance of the same clause and is smaller than `Cθ`: every literal of `Cθ'` is at
  most the corresponding literal of `Cθ` (`groundTerm_le_of_le`, `Lit.make_le_make`), and the literal
  containing `x` is strictly smaller (`groundTerm_lt_of_occurs`, `Lit.make_lt_make`); the multiset
  extension then descends (`clauseLT_map`);
* the side premise is smaller than the main premise;
* in any equality interpretation where both hold, either a literal of `D` holds, or `l ≈ r` holds, so
  `xθ' ≈ xθ` (`groundTerm_congr`), and the literals of `Cθ'` hold exactly when those of `Cθ` do
  (`NLit.holds_ground_iff`); the literal of `Cθ'` at `x` turns into the conclusion's rewritten literal.

So the conclusion follows from clauses of the set below the main premise.

## The dichotomy

* `lift_binary`: a ground superposition between instances of two variable-disjoint clauses is the
  instance of a lifted superposition (`SupLift`), or it is redundant with respect to any set holding
  its side premise and every instance of its main premise.
* `lift_unary`: a ground equality resolution or equality factoring of an instance lifts
  (`EqResLift`, `EqFactLift`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition

open Mettapedia.Logic.LP

variable {sig : LPSignature}

/-! ## Changing the arguments of an application one at a time -/

section Arguments

/-- The arguments below `k` from `a`, the others from `b`. -/
def mixArgs {n : ℕ} {α : Type*} (a b : Fin n → α) (k : ℕ) : Fin n → α :=
  fun i => if i.val < k then a i else b i

theorem mixArgs_zero {n : ℕ} {α : Type*} (a b : Fin n → α) : mixArgs a b 0 = b :=
  funext fun _ => if_neg (Nat.not_lt_zero _)

theorem mixArgs_full {n : ℕ} {α : Type*} (a b : Fin n → α) : mixArgs a b n = a :=
  funext fun i => if_pos i.isLt

theorem mixArgs_succ {n : ℕ} {α : Type*} (a b : Fin n → α) {k : ℕ} (hk : k < n) :
    mixArgs a b (k + 1) = Function.update (mixArgs a b k) ⟨k, hk⟩ (a ⟨k, hk⟩) := by
  funext i
  by_cases hi : i = ⟨k, hk⟩
  · rw [hi, Function.update_self]
    simp [mixArgs]
  · rw [Function.update_of_ne hi]
    have ne : i.val ≠ k := fun h => hi (Fin.ext h)
    by_cases lt : i.val < k
    · simp only [mixArgs, if_pos lt, if_pos (Nat.lt_succ_of_lt lt)]
    · have notSucc : ¬ i.val < k + 1 := by omega
      simp only [mixArgs, if_neg lt, if_neg notSucc]

theorem mixArgs_of_le {n : ℕ} {α : Type*} (a b : Fin n → α) {k : ℕ} (hk : n ≤ k) :
    mixArgs a b (k + 1) = mixArgs a b k := by
  funext i
  have one : i.val < k + 1 := by omega
  have two : i.val < k := by omega
  simp only [mixArgs, if_pos one, if_pos two]

theorem mixArgs_at {n : ℕ} {α : Type*} (a b : Fin n → α) {k : ℕ} (hk : k < n) :
    mixArgs a b k ⟨k, hk⟩ = b ⟨k, hk⟩ :=
  if_neg (lt_irrefl k)

/-- **A relation that survives changing one argument holds of arguments related pointwise.** -/
theorem app_of_pointwise (R : GroundTerm sig → GroundTerm sig → Prop) (refl : ∀ a, R a a)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (step : ∀ (f : sig.functionSymbols) (args : Fin (sig.functionArity f) → GroundTerm sig)
      (i : Fin (sig.functionArity f)) (a : GroundTerm sig), R a (args i) →
        R (GroundTerm.app f (Function.update args i a)) (GroundTerm.app f args))
    (f : sig.functionSymbols) {a b : Fin (sig.functionArity f) → GroundTerm sig}
    (each : ∀ i, R (a i) (b i)) : R (GroundTerm.app f a) (GroundTerm.app f b) := by
  have stage : ∀ k, R (GroundTerm.app f (mixArgs a b k)) (GroundTerm.app f b) := by
    intro k
    induction k with
    | zero => rw [mixArgs_zero]; exact refl _
    | succ k ih =>
        by_cases hk : k < sig.functionArity f
        · rw [mixArgs_succ a b hk]
          refine trans (step f (mixArgs a b k) ⟨k, hk⟩ (a ⟨k, hk⟩) ?_) ih
          rw [mixArgs_at a b hk]
          exact each _
        · rw [mixArgs_of_le a b (not_lt.mp hk)]
          exact ih
  have last := stage (sig.functionArity f)
  rwa [mixArgs_full] at last

/-- **Equal-up-to-an-interpretation substitutions give interpretation-equal instances.** -/
theorem groundTerm_congr (I : Congruence sig) {θ' θ : Grounding sig} (each : ∀ v, I.rel (θ' v) (θ v))
    (t : Term sig) : I.rel (θ'.groundTerm t) (θ.groundTerm t) := by
  induction t with
  | var v => exact each v
  | const _ => exact I.equivalence.refl _
  | app f ts ih =>
      refine app_of_pointwise I.rel I.equivalence.refl I.equivalence.trans
        (fun g args i a related => ?_) f ih
      have step := I.compatible (.app g args i .hole) related
      have back : (Ctx.app g args i .hole).fill (args i) = GroundTerm.app g args := by
        show GroundTerm.app g (Function.update args i (args i)) = _
        rw [Function.update_eq_self]
      rw [back] at step
      exact step

/-- **Variable occurrence.** -/
def Occurs (x : sig.vars) : Term sig → Prop
  | .var y => y = x
  | .const _ => False
  | .app _ ts => ∃ i, Occurs x (ts i)

theorem occurs_fill_var (x : sig.vars) : ∀ c : FirstOrderRewriting.Context sig, Occurs x (c.fill (.var x))
  | .hole => rfl
  | .app f args i inner => by
      show ∃ j, Occurs x (Function.update args i (inner.fill (.var x)) j)
      exact ⟨i, by rw [Function.update_self]; exact occurs_fill_var x inner⟩

end Arguments

/-! ## Monotonicity in the grounding -/

section Monotone

variable [LinearOrder (GroundTerm sig)] [GroundSimplification sig]

theorem app_le_app (f : sig.functionSymbols) {a b : Fin (sig.functionArity f) → GroundTerm sig}
    (each : ∀ i, a i ≤ b i) : GroundTerm.app f a ≤ GroundTerm.app f b :=
  app_of_pointwise (· ≤ ·) le_refl le_trans (fun g args i a le => by
    rcases le.lt_or_eq with lt | same
    · exact (GroundSimplification.monotone g args i a lt).le
    · rw [same, Function.update_eq_self]) f each

theorem app_lt_app (f : sig.functionSymbols) {a b : Fin (sig.functionArity f) → GroundTerm sig}
    (each : ∀ i, a i ≤ b i) (j : Fin (sig.functionArity f)) (strict : a j < b j) :
    GroundTerm.app f a < GroundTerm.app f b := by
  have mid : GroundTerm.app f a < GroundTerm.app f (Function.update a j (b j)) := by
    have step := GroundSimplification.monotone f (Function.update a j (b j)) j (a j)
      (by rw [Function.update_self]; exact strict)
    rwa [Function.update_idem, Function.update_eq_self] at step
  refine mid.trans_le (app_le_app f fun i => ?_)
  by_cases h : i = j
  · simp only [h, Function.update_self, le_refl]
  · rw [Function.update_of_ne h]
    exact each i

/-- **A pointwise smaller grounding gives smaller instances.** -/
theorem groundTerm_le_of_le {θ' θ : Grounding sig} (le : ∀ v, θ' v ≤ θ v) (t : Term sig) :
    θ'.groundTerm t ≤ θ.groundTerm t := by
  induction t with
  | var v => exact le v
  | const _ => exact le_rfl
  | app f ts ih => exact app_le_app f ih

/-- **Strictly smaller at an occurring variable gives a strictly smaller instance.** -/
theorem groundTerm_lt_of_occurs {θ' θ : Grounding sig} (le : ∀ v, θ' v ≤ θ v) {x : sig.vars}
    (lt : θ' x < θ x) : ∀ {t : Term sig}, Occurs x t → θ'.groundTerm t < θ.groundTerm t
  | .var y, occurs => by
      have same : y = x := occurs
      rw [same]
      exact lt
  | .const _, occurs => occurs.elim
  | .app f ts, occurs => by
      obtain ⟨i, inner⟩ := occurs
      exact app_lt_app f (fun j => groundTerm_le_of_le le (ts j)) i (groundTerm_lt_of_occurs le lt inner)

end Monotone

/-! ## Literals and clauses -/

section Literals

theorem Lit.make_le_make {T : Type*} [LinearOrder T] (negative : Bool) {a b a' b' : T} (ha : a ≤ a')
    (hb : b ≤ b') : Lit.make negative a b ≤ Lit.make negative a' b' := by
  rcases (max_le_max ha hb).lt_or_eq with lt | same
  · exact (Lit.lt_of_lhs_lt lt).le
  · rcases (min_le_min ha hb).lt_or_eq with lt' | same'
    · exact (show Lit.make negative a b < Lit.make negative a' b' from
        Lit.lt_iff.mpr (Or.inr ⟨same, Or.inr ⟨rfl, lt'⟩⟩)).le
    · exact le_of_eq (Lit.ext same rfl same')

theorem Lit.make_lt_make {T : Type*} [LinearOrder T] (negative : Bool) {a b a' b' : T} (ha : a < a')
    (hb : b ≤ b') : Lit.make negative a b < Lit.make negative a' b' := by
  refine lt_of_le_of_ne (Lit.make_le_make negative ha.le hb) fun same => ?_
  have h1 : max a b = max a' b' := congrArg Lit.lhs same
  have h2 : min a b = min a' b' := congrArg Lit.rhs same
  rcases le_total a b with hab | hab <;> rcases le_total a' b' with hab' | hab'
  · rw [min_eq_left hab, min_eq_left hab'] at h2
    exact ha.ne h2
  · rw [max_eq_right hab, max_eq_left hab'] at h1
    rw [min_eq_left hab, min_eq_right hab'] at h2
    have back : a' ≤ a := by rw [← h1, h2]; exact hb
    exact absurd ha (not_lt.mpr back)
  · rw [min_eq_right hab, min_eq_left hab'] at h2
    have back : a' ≤ a := by rw [← h2]; exact hab
    exact absurd ha (not_lt.mpr back)
  · rw [max_eq_left hab, max_eq_left hab'] at h1
    exact ha.ne h1

/-- **The multiset extension descends** when every element is replaced by one at most as large, and
one by a strictly smaller one. -/
theorem clauseLT_map {α : Type*} {T : Type*} [LinearOrder T] (m : Multiset α) (f g : α → Lit T)
    (le : ∀ x ∈ m, f x ≤ g x) {y : α} (member : y ∈ m) (lt : f y < g y) :
    ClauseLT (m.map f) (m.map g) := by
  have same : (m.filter fun x => f x = g x).map f = (m.filter fun x => f x = g x).map g :=
    Multiset.map_congr rfl fun x hx => (Multiset.mem_filter.mp hx).2
  have splitF : m.map f = (m.filter fun x => f x = g x).map f +
      (m.filter fun x => ¬ f x = g x).map f := by
    rw [← Multiset.map_add, Multiset.filter_add_not]
  have splitG : m.map g = (m.filter fun x => f x = g x).map f +
      (m.filter fun x => ¬ f x = g x).map g := by
    rw [same, ← Multiset.map_add, Multiset.filter_add_not]
  show Multiset.IsDershowitzMannaLT _ _
  rw [splitF, splitG]
  refine dm_intro _ _ _ (fun zero => ?_) fun z hz => ?_
  · have inside : g y ∈ (m.filter fun x => ¬ f x = g x).map g :=
      Multiset.mem_map_of_mem g (Multiset.mem_filter.mpr ⟨member, lt.ne⟩)
    rw [zero] at inside
    exact Multiset.notMem_zero _ inside
  · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
    obtain ⟨inM, ne⟩ := Multiset.mem_filter.mp hx
    exact ⟨g x, Multiset.mem_map_of_mem g hx, lt_of_le_of_ne (le x inM) ne⟩

variable [LinearOrder (GroundTerm sig)]

/-- A literal made on interpretation-equal terms holds exactly when the original does. -/
theorem Lit.holds_make_congr (I : Congruence sig) (negative : Bool) {a b a' b' : GroundTerm sig}
    (ha : I.rel a a') (hb : I.rel b b') :
    (Lit.make negative a b).Holds I.rel ↔ (Lit.make negative a' b').Holds I.rel := by
  have symm : ∀ x y, I.rel x y → I.rel y x := fun _ _ h => I.equivalence.symm h
  rw [Lit.holds_make symm, Lit.holds_make symm]
  have rel : I.rel a b ↔ I.rel a' b' :=
    ⟨fun h => I.equivalence.trans (I.equivalence.symm ha) (I.equivalence.trans h hb),
     fun h => I.equivalence.trans ha (I.equivalence.trans h (I.equivalence.symm hb))⟩
  cases negative <;> simp [rel]

theorem NLit.holds_ground_iff (I : Congruence sig) {θ' θ : Grounding sig}
    (each : ∀ v, I.rel (θ' v) (θ v)) (K : NLit sig) :
    (K.ground θ').Holds I.rel ↔ (K.ground θ).Holds I.rel :=
  Lit.holds_make_congr I K.negative (groundTerm_congr I each K.lhs) (groundTerm_congr I each K.rhs)

end Literals

/-! ## The variable-overlap case -/

section Overlap

variable [LinearOrder (GroundTerm sig)] [GroundSimplification sig]

/-- **A superposition at or below a variable of the main premise is redundant**: its conclusion follows
from the side premise and a smaller instance `Cθ'` of the main premise, both below `Cθ`. -/
theorem overlap_redundant {θ : Grounding sig} {Dc Cc : NClause sig} {E : Clause (GroundTerm sig)}
    (overlap : AtVariable θ Dc Cc E) {S : Set (Clause (GroundTerm sig))}
    (sideIn : NClause.ground θ Dc ∈ S) (instances : ∀ θ' : Grounding sig, NClause.ground θ' Cc ∈ S) :
    RedundantInference S (NClause.ground θ Cc) E := by
  classical
  obtain ⟨l, r, D, s, t, L, M, c', x, d, decreasing, sideEq, rfl, choice, sideBelow, atVar, atX, rfl⟩ :=
    overlap
  obtain ⟨θ', hθ'⟩ : ∃ θ' : Grounding sig, ∀ v, θ' v = if v = x then d.fill r else θ v :=
    ⟨fun v => if v = x then d.fill r else θ v, fun _ => rfl⟩
  have smaller : d.fill r < θ x := by rw [atX]; exact d.fill_lt_fill decreasing
  have atX' : θ' x = d.fill r := by rw [hθ', if_pos rfl]
  have offX : ∀ v, v ≠ x → θ' v = θ v := fun v h => by rw [hθ', if_neg h]
  have le : ∀ v, θ' v ≤ θ v := by
    intro v
    by_cases h : v = x
    · rw [h, atX']; exact smaller.le
    · rw [offX v h]
  have ltx : θ' x < θ x := by rw [atX']; exact smaller
  have groundMain : ∀ ρ : Grounding sig,
      NClause.ground ρ (s ++ M :: t) = L.ground ρ ::ₘ NClause.ground ρ (s ++ t) :=
    fun ρ => by rw [NClause.ground_middle, NLit.ground_of_choice choice]
  have Lmem : L.ground θ ∈ NClause.ground θ (s ++ M :: t) := by
    rw [groundMain]; exact Multiset.mem_cons_self _ _
  have sideLower : ClauseLT (NClause.ground θ Dc) (NClause.ground θ (s ++ M :: t)) :=
    dm_of_all_below _ _ (fun zero => by rw [zero] at Lmem; exact Multiset.notMem_zero _ Lmem)
      fun K member => ⟨L.ground θ, Lmem, sideBelow K member⟩
  have Llt : M.ground θ' < M.ground θ := by
    rw [← NLit.ground_of_choice choice, ← NLit.ground_of_choice choice]
    exact Lit.make_lt_make L.negative (groundTerm_lt_of_occurs le ltx (atVar ▸ occurs_fill_var x c'))
      (groundTerm_le_of_le le L.rhs)
  have mainLower : ClauseLT (NClause.ground θ' (s ++ M :: t)) (NClause.ground θ (s ++ M :: t)) :=
    clauseLT_map ((s ++ M :: t : List (NLit sig)) : Multiset (NLit sig)) (NLit.ground θ') (NLit.ground θ)
      (fun K _ => Lit.make_le_make K.negative (groundTerm_le_of_le le K.lhs) (groundTerm_le_of_le le K.rhs))
      (Multiset.mem_coe.mpr (List.mem_append_right _ List.mem_cons_self)) Llt
  intro I hyps
  have sideHolds := hyps _ ⟨sideIn, sideLower⟩
  have mainHolds := hyps _ ⟨instances θ', mainLower⟩
  have symm : ∀ a b, I.rel a b → I.rel b a := fun _ _ h => I.equivalence.symm h
  rw [← sideEq] at sideHolds
  rcases models_cons.mp sideHolds with rule | inD
  · have rel_lr : I.rel l r := by simpa using (Lit.holds_make symm false l r).mp rule
    have each : ∀ v, I.rel (θ' v) (θ v) := by
      intro v
      by_cases h : v = x
      · rw [h, atX', atX]
        exact symm _ _ (I.compatible d rel_lr)
      · rw [offX v h]
        exact I.equivalence.refl _
    rw [groundMain θ'] at mainHolds
    rcases models_cons.mp mainHolds with lit | rest
    · have lhsθ : θ.groundTerm L.lhs = (groundCtx θ c').fill (d.fill l) := by
        rw [atVar, groundTerm_fill]
        exact congrArg (groundCtx θ c').fill atX
      have ha : I.rel (θ'.groundTerm L.lhs) ((groundCtx θ c').fill (d.fill r)) := by
        refine I.equivalence.trans (groundTerm_congr I each L.lhs) ?_
        rw [lhsθ]
        exact I.compatible (groundCtx θ c') (I.compatible d rel_lr)
      exact models_cons.mpr (Or.inl ((Lit.holds_make_congr I L.negative ha
        (groundTerm_congr I each L.rhs)).mp lit))
    · obtain ⟨K, memK, holdsK⟩ := rest
      obtain ⟨K', memK', rfl⟩ := NClause.exists_of_mem_ground memK
      exact models_cons.mpr (Or.inr (models_add.mpr (Or.inr
        ⟨K'.ground θ, NClause.mem_ground memK', (NLit.holds_ground_iff I each K').mp holdsK⟩)))
  · exact models_cons.mpr (Or.inr (models_add.mpr (Or.inl inD)))

end Overlap

/-! ## Every ground inference lifts or is redundant -/

section Dichotomy

variable [LinearOrder (GroundTerm sig)] [DecidableEq sig.vars] [DecidableEq sig.constants]
  [DecidableEq sig.functionSymbols]

/-- **A ground equality resolution or equality factoring of an instance lifts.** -/
theorem lift_unary (ord : GroundedOrder sig) (θ : Grounding sig) {Cc : NClause sig}
    {side : Option (Clause (GroundTerm sig))} {main E : Clause (GroundTerm sig)}
    (inference : Inference side main E) (sideEq : side = none) (mainEq : main = NClause.ground θ Cc) :
    Nonempty (EqResLift ord.toStableOrder θ Cc E) ∨ Nonempty (EqFactLift ord.toStableOrder θ Cc E) := by
  cases inference with
  | posSup => cases sideEq
  | negSup => cases sideEq
  | eqRes C L negative trivial mainMax =>
      exact Or.inl (lift_eqRes ord θ _ L negative trivial mainMax mainEq)
  | eqFact C L L' positive positive' same strict mainMax =>
      exact Or.inr (lift_eqFact ord θ C L L' positive positive' same strict mainMax mainEq)

variable [GroundSimplification sig]

/-- **A ground superposition between instances lifts, or is redundant** with respect to any set holding
its side premise and every instance of its main premise. -/
theorem lift_binary (ord : GroundedOrder sig) (θ : Grounding sig) {Dc Cc : NClause sig}
    {side : Option (Clause (GroundTerm sig))} {main E : Clause (GroundTerm sig)}
    (inference : Inference side main E) (sideEq : side = some (NClause.ground θ Dc))
    (mainEq : main = NClause.ground θ Cc) :
    Nonempty (SupLift ord.toStableOrder θ Dc Cc E) ∨
      ∀ S : Set (Clause (GroundTerm sig)), NClause.ground θ Dc ∈ S →
        (∀ θ' : Grounding sig, NClause.ground θ' Cc ∈ S) → RedundantInference S (NClause.ground θ Cc) E := by
  cases inference with
  | @posSup l r D C L c decreasing sideMax positive larger strict mainMax smaller =>
      rcases lift_posSup ord θ D C L c decreasing sideMax positive larger strict mainMax smaller
        (Option.some.inj sideEq) mainEq with lifted | overlap
      · exact Or.inl lifted
      · exact Or.inr fun S sideIn instances => overlap_redundant overlap sideIn instances
  | @negSup l r D C L c decreasing sideMax negative larger strict mainMax =>
      rcases lift_negSup ord θ D C L c decreasing sideMax negative larger strict mainMax
        (Option.some.inj sideEq) mainEq with lifted | overlap
      · exact Or.inl lifted
      · exact Or.inr fun S sideIn instances => overlap_redundant overlap sideIn instances
  | eqRes => cases sideEq
  | eqFact => cases sideEq

end Dichotomy

#print axioms mixArgs_succ
#print axioms app_of_pointwise
#print axioms groundTerm_congr
#print axioms occurs_fill_var
#print axioms app_le_app
#print axioms app_lt_app
#print axioms groundTerm_le_of_le
#print axioms groundTerm_lt_of_occurs
#print axioms Lit.make_le_make
#print axioms Lit.make_lt_make
#print axioms clauseLT_map
#print axioms Lit.holds_make_congr
#print axioms NLit.holds_ground_iff
#print axioms overlap_redundant
#print axioms lift_unary
#print axioms lift_binary

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Superposition
