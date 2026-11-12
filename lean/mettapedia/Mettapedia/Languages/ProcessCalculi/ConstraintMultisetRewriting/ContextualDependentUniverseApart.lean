import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjective

/-!
# A type of a universe is never equal to a type that holds, at a rigid position, what the universe does not hold

The companion of `ContextualDependentUniverseInjective`: where an equation cannot be read at a smaller universe
because one side is not a term of it for a reason that no instantiation changes, the equation has no solution.

* **A normal type equal to a type of a universe is a type of that universe** (`normal_typed_of_equal`): the normal
  form of the type of the universe is the normal type up to heads, and a normal type is equal, at every universe at
  which it is typed, to a type that is the same up to heads.
* **A universe typed at a universe lies below it** (`head_typed_cumulative`), by generation and the inversion of
  subtyping at universes. Hence no type of `U` is equal to a universe that `U` does not hold (`sort_not_small`).
* **A variable declared at a universe is a type of the universes above it only** (`var_not_small`): no type of `U`
  is equal to a variable declared at a universe that does not lie below `U`.
* **Smallness goes through the formers** (`small_pi`, `small_sigma`, `small_id`): a Π, Σ or identity type equal to
  a type of `U` has its component types equal to types of `U`. The normal form of the type of `U` is a type of
  `U` of the same former, and its components are typed at universes whose join lies below `U`.
* **`Above U mark t`**: `t` holds, at a type position under formers, a universe that `U` does not hold, or a marked
  variable. In a context where every marked variable is declared at a universe that does not lie below `U`
  (`Marked`), no type of `U` is equal to such a `t` (`Above.not_small`). The relation is kept by every substitution
  that sends marked variables to marked variables (`Above.subst`).
* **Under a telescope** (`AboveUnder`, `AboveUnder.apart`): no term of `Π x̄. U` is equal, at `Π x̄. V`, to
  `λ x̄. t` with `Above U mark t`, where `mark` marks the variables of the telescope bound at a universe that does
  not lie below `U`. By β and the applications to a fresh variable. A substitution of the variables outside the
  telescope keeps the marks, so the statement holds under every instantiation of the unknowns.

**What is not covered.** A side that holds another unknown can be a term of the smaller universe under some
instantiations and not under others; that is not a refutation. A local declared at a universe below the one an
unknown declares for its argument is not marked; the statement for that case is `applied_local_apart` in
`ContextualDependentSweepWitnessesCumulative`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniverseInjective

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Marks -/

/-- The marking of the variables under one more binder; `new` marks the bound variable. -/
def liftMark {n : Nat} (mark : Fin n → Bool) (new : Bool) : Fin (n + 1) → Bool := Fin.cases new mark

/-- **Every marked variable is declared at a universe that does not lie below `u`.** -/
def Marked (R : Rules Head) (u : Head) {n : Nat} (Γ : Ctx Head n) (mark : Fin n → Bool) : Prop :=
  ∀ i, mark i = true → ∃ w, Ctx.lookup Γ i = .head w ∧ R.isUniverse w ∧ ¬ R.cumulative w u

theorem Marked.none (R : Rules Head) (u : Head) {n : Nat} (Γ : Ctx Head n) : Marked R u Γ fun _ => false :=
  fun _ marked => absurd marked Bool.false_ne_true

theorem Marked.snoc {R : Rules Head} {u : Head} {n : Nat} {Γ : Ctx Head n} {mark : Fin n → Bool}
    (marked : Marked R u Γ mark) (A : Tm Head n) : Marked R u (.snoc Γ A) (liftMark mark false) := by
  intro i
  refine Fin.cases (fun unmarked => absurd unmarked Bool.false_ne_true) (fun j held => ?_) i
  obtain ⟨w, declared, hw, apart⟩ := marked j held
  exact ⟨w, by rw [Ctx.lookup_snoc_succ, declared]; rfl, hw, apart⟩

theorem Marked.snocBound {R : Rules Head} {u w : Head} {n : Nat} {Γ : Ctx Head n} {mark : Fin n → Bool}
    (marked : Marked R u Γ mark) (hw : R.isUniverse w) (apart : ¬ R.cumulative w u) :
    Marked R u (.snoc Γ (.head w)) (liftMark mark true) := by
  intro i
  refine Fin.cases (fun _ => ⟨w, rfl, hw, apart⟩) (fun j held => ?_) i
  obtain ⟨w', declared, hw', apart'⟩ := marked j held
  exact ⟨w', by rw [Ctx.lookup_snoc_succ, declared]; rfl, hw', apart'⟩

/-- **A substitution that sends marked variables to marked variables.** -/
def MarkedSub {n m : Nat} (mark : Fin n → Bool) (target : Fin m → Bool) (τ : Sub Head n m) : Prop :=
  ∀ i, mark i = true → ∃ j, τ i = .var j ∧ target j = true

theorem MarkedSub.none {n m : Nat} (target : Fin m → Bool) (τ : Sub Head n m) :
    MarkedSub (fun _ => false) target τ := fun _ marked => absurd marked Bool.false_ne_true

theorem MarkedSub.lift {n m : Nat} {mark : Fin n → Bool} {target : Fin m → Bool} {τ : Sub Head n m}
    (kept : MarkedSub mark target τ) (new : Bool) :
    MarkedSub (liftMark mark new) (liftMark target new) (liftSub τ) := by
  intro i
  refine Fin.cases (fun held => ⟨0, rfl, held⟩) (fun k held => ?_) i
  obtain ⟨j, same, marked⟩ := kept k held
  refine ⟨j.succ, ?_, marked⟩
  change Presentation.rename wk (τ k) = .var j.succ
  rw [same]
  rfl

/-! ## The relations -/

/-- **`t` holds, at a type position under formers, a universe that `u` does not hold, or a marked variable.** -/
inductive Above (R : Rules Head) (u : Head) : {n : Nat} → (Fin n → Bool) → Tm Head n → Prop where
  | sort {n : Nat} {mark : Fin n → Bool} {k : Head} : (∀ above, R.headTyping k above → ¬ R.cumulative above u) →
      Above R u mark (.head k)
  | var {n : Nat} {mark : Fin n → Bool} {i : Fin n} : mark i = true → Above R u mark (.var i)
  | piDomain {n : Nat} {mark : Fin n → Bool} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Above R u mark A → Above R u mark (.pi A B)
  | piCodomain {n : Nat} {mark : Fin n → Bool} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Above R u (liftMark mark false) B → Above R u mark (.pi A B)
  | sigmaFirst {n : Nat} {mark : Fin n → Bool} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Above R u mark A → Above R u mark (.sigma A B)
  | sigmaSecond {n : Nat} {mark : Fin n → Bool} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Above R u (liftMark mark false) B → Above R u mark (.sigma A B)
  | id {n : Nat} {mark : Fin n → Bool} {A a b : Tm Head n} : Above R u mark A → Above R u mark (.id A a b)

/-- The relation is kept by a substitution that sends marked variables to marked variables. -/
theorem Above.subst {R : Rules Head} {u : Head} {n : Nat} {mark : Fin n → Bool} {t : Tm Head n}
    (above : Above R u mark t) :
    ∀ {m : Nat} {target : Fin m → Bool} (τ : Sub Head n m), MarkedSub mark target τ →
      Above R u target (Presentation.subst τ t) := by
  induction above with
  | sort apart => intro m target τ _; exact .sort apart
  | @var n mark i held =>
      intro m target τ kept
      obtain ⟨j, same, marked⟩ := kept i held
      change Above R u target (τ i)
      rw [same]
      exact .var marked
  | piDomain _ ih => intro m target τ kept; exact .piDomain (ih τ kept)
  | piCodomain _ ih => intro m target τ kept; exact .piCodomain (ih (liftSub τ) (kept.lift false))
  | sigmaFirst _ ih => intro m target τ kept; exact .sigmaFirst (ih τ kept)
  | sigmaSecond _ ih => intro m target τ kept; exact .sigmaSecond (ih (liftSub τ) (kept.lift false))
  | id _ ih => intro m target τ kept; exact .id (ih τ kept)

/-- **`t` is, under the abstractions of the telescope `large`, a type that holds what the universe `u` does not
hold**; `small` is `large` with `u` at its end. The variables of the telescope bound at a universe that does not lie
below `u` are marked. -/
inductive AboveUnder (R : Rules Head) (u : Head) : {n : Nat} → (Fin n → Bool) → Tm Head n → Tm Head n → Tm Head n →
    Prop where
  | base {n : Nat} {mark : Fin n → Bool} {v : Head} {t : Tm Head n} : R.isUniverse u → R.isUniverse v →
      Above R u mark t → AboveUnder R u mark (.head u) (.head v) t
  | pi {n : Nat} {mark : Fin n → Bool} {A : Tm Head n} {small large body : Tm Head (n + 1)} :
      AboveUnder R u (liftMark mark false) small large body →
      AboveUnder R u mark (.pi A small) (.pi A large) (.lam body)
  | bound {n : Nat} {mark : Fin n → Bool} {w : Head} {small large body : Tm Head (n + 1)} :
      R.isUniverse w → ¬ R.cumulative w u → AboveUnder R u (liftMark mark true) small large body →
      AboveUnder R u mark (.pi (.head w) small) (.pi (.head w) large) (.lam body)

/-- The relation is kept by a substitution that sends marked variables to marked variables. -/
theorem AboveUnder.subst {R : Rules Head} {u : Head} {n : Nat} {mark : Fin n → Bool} {small large t : Tm Head n}
    (under : AboveUnder R u mark small large t) :
    ∀ {m : Nat} {target : Fin m → Bool} (τ : Sub Head n m), MarkedSub mark target τ →
      AboveUnder R u target (Presentation.subst τ small) (Presentation.subst τ large) (Presentation.subst τ t) := by
  induction under with
  | base hu hv above => intro m target τ kept; exact .base hu hv (above.subst τ kept)
  | pi _ ih => intro m target τ kept; exact .pi (ih (liftSub τ) (kept.lift false))
  | bound hw apart _ ih => intro m target τ kept; exact .bound hw apart (ih (liftSub τ) (kept.lift true))

/-- **No term of the smaller type is equal to `t` at the larger type.** -/
def Apart (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (small large t : Tm Head n) : Prop :=
  CtxFormed R Γ → ∀ {s : Tm Head n}, Typed R Γ s small → ¬ Equal R Γ s t large

section Semantics

variable (facts : FormFacts S.R S.roles)

include facts in
/-- **Under a binder**: by β, from the applications to a fresh variable. -/
theorem Apart.pi {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {small large body : Tm Head (n + 1)}
    (inner : Apart S.R (.snoc Γ A) small large body) : Apart S.R Γ (.pi A small) (.pi A large) (.lam body) := by
  intro formed s ts equal
  obtain ⟨u, _, tSmall⟩ := Typed.isType ts formed
  have generation : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation tSmall
  obtain ⟨u₁, _, _, tA, hu₁, _, _, _, _⟩ := generation
  have typedLam : Typed S.R Γ (.lam body) (.pi A large) := (Equal.typed equal formed).2
  obtain ⟨w, hw, tLarge⟩ := Typed.isType typedLam formed
  have typedBody : Typed S.R (.snoc Γ A) body large := Typed.lam_inv facts typedLam formed
  have applied : Typed S.R (.snoc Γ A) (.app (Presentation.rename wk s) (.var 0)) small := by
    have step := Derivable.appElim (ts.rename (CtxRen.wk Γ A)) (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  have compared : Equal S.R (.snoc Γ A) (.app (Presentation.rename wk s) (.var 0))
      (.app (Presentation.rename wk (.lam body)) (.var 0)) large := by
    have step := Derivable.appCong (equal.rename (CtxRen.wk Γ A))
      (Derivable.refl (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0))
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  have beta : Equal S.R (.snoc Γ A) (.app (Presentation.rename wk (.lam body)) (.var 0)) body large := by
    have step := Derivable.betaPi (tLarge.rename (CtxRen.wk Γ A)) hw
      (typedBody.rename ((CtxRen.wk Γ A).snoc A)) (Derivable.var (R := S.R) (Γ := .snoc Γ A) 0)
    simpa only [Presentation.rename, Ctx.lookup, Products.fresh_instantiation] using step
  exact inner (formed.snoc ⟨u₁, hu₁, tA⟩) applied (.trans compared beta)

variable (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (rigid : ∀ name, S.roles name = .rigid) (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **A normal type equal to a type of a universe is a type of that universe.** -/
theorem normal_typed_of_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {s T : Tm Head n} {u : Head}
    (hu : S.R.isUniverse u) (ts : Typed S.R Γ s (.head u)) (equal : TypeEq S.R Γ s T)
    (normal : Long S.R S.roles (.type Γ T)) : Typed S.R Γ T (.head u) := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨u, hu, ts⟩
  obtain ⟨tZ, eZ⟩ := atZ hu ts
  have sZ : TypeEq S.R Γ s Z := ⟨u, hu, eZ⟩
  have same := long_type_unique facts roots heads algebra complete formed lZ normal
    (TypeEq.trans S.levels sZ.symm equal)
  exact (Equal.typed (Long.sameEqual facts heads lZ formed same hu tZ) formed).2

include facts algebra in
/-- A universe usable at a universe is cumulatively below it. -/
theorem typeLe_head_cumulative {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {w u : Head}
    (hw : S.R.isUniverse w) (hu : S.R.isUniverse u) (le : TypeLe S.R Γ (.head w) (.head u)) :
    S.R.cumulative w u := by
  obtain ⟨v, _, eU, c⟩ := Below.universe_cumulative facts algebra
    (TypeLe.toBelow le (IsType.head_of_universe hu)) formed hw (IsType.refl (IsType.head_of_universe hw))
  exact algebra.same_right c (TypeEq.head_injective facts eU.symm formed)

include facts algebra in
/-- **A universe typed at a universe lies below it**: its own universe is cumulatively below the other. -/
theorem head_typed_cumulative {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {k u : Head}
    (hu : S.R.isUniverse u) (typed : Typed S.R Γ (.head k) (.head u)) :
    ∃ above, S.R.headTyping k above ∧ S.R.cumulative above u := by
  have generation : GenerationAt S.R Γ (.head k) (.head u) := Typed.generation typed
  obtain ⟨above, typing, le⟩ := generation
  exact ⟨above, typing,
    typeLe_head_cumulative facts algebra formed (S.levels.ground_typing typing) hu le⟩

include facts roots heads algebra rigid complete in
/-- **No type of a universe is equal to a universe that the universe does not hold.** -/
theorem sort_not_small {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {s : Tm Head n} {u k : Head}
    (hu : S.R.isUniverse u) (apart : ∀ above, S.R.headTyping k above → ¬ S.R.cumulative above u)
    (ts : Typed S.R Γ s (.head u)) : ¬ TypeEq S.R Γ s (.head k) := by
  intro equal
  have typed := normal_typed_of_equal facts roots heads algebra rigid complete formed hu ts equal
    (.head (TypeEq.isType equal formed).2)
  obtain ⟨above, typing, c⟩ := head_typed_cumulative facts algebra formed hu typed
  exact apart above typing c

include facts roots heads algebra rigid complete in
/-- **No type of a universe is equal to a variable declared at a universe that does not lie below it.** -/
theorem var_not_small {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {i : Fin n} {w u : Head}
    (declared : Ctx.lookup Γ i = .head w) (hw : S.R.isUniverse w) (hu : S.R.isUniverse u)
    (apart : ¬ S.R.cumulative w u) {s : Tm Head n} (ts : Typed S.R Γ s (.head u)) :
    ¬ TypeEq S.R Γ s (.var i) := by
  intro equal
  have isW : IsType S.R Γ (.head w) := IsType.head_of_universe hw
  have spine : Long S.R S.roles (.spine Γ (.var i) (.head w)) := .var i (by rw [declared]; exact IsType.refl isW)
  have normal : Long S.R S.roles (.type Γ (.var i)) := .neutralType spine hw (IsType.refl isW).below
  have typed := normal_typed_of_equal facts roots heads algebra rigid complete formed hu ts equal normal
  have generation : TypeLe S.R Γ (Ctx.lookup Γ i) (.head u) := Typed.generation typed
  rw [declared] at generation
  exact apart (typeLe_head_cumulative facts algebra formed hw hu generation)

include facts roots heads algebra rigid complete in
/-- **A Π type equal to a type of a universe has its domain and codomain equal to types of that universe.** -/
theorem small_pi {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {s A : Tm Head n} {B : Tm Head (n + 1)}
    {u : Head} (hu : S.R.isUniverse u) (ts : Typed S.R Γ s (.head u)) (equal : TypeEq S.R Γ s (.pi A B)) :
    ∃ A' B', Typed S.R Γ A' (.head u) ∧ TypeEq S.R Γ A' A ∧ Typed S.R (.snoc Γ A') B' (.head u) ∧
      TypeEq S.R (.snoc Γ A') B' B := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨u, hu, ts⟩
  obtain ⟨tZ, eZ⟩ := atZ hu ts
  have sZ : TypeEq S.R Γ s Z := ⟨u, hu, eZ⟩
  have same : TypeEq S.R Γ Z (.pi A B) := TypeEq.trans S.levels sZ.symm equal
  cases lZ with
  | head _ => exact absurd same.symm (TypeEq.pi_ne_head facts formed)
  | pi _ _ _ =>
      obtain ⟨eA, eB⟩ := TypeEq.pi_injective facts same formed
      have generation : GenerationAt S.R _ (.pi _ _) (.head u) := Typed.generation tZ
      obtain ⟨u₁, u₂, w, tA, _, tB, _, join, le⟩ := generation
      obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
      have cw := typeLe_head_cumulative facts algebra formed (S.levels.join_level join).1 hu le
      exact ⟨_, _, Derivable.cumul tA (algebra.trans c₁ cw), eA, Derivable.cumul tB (algebra.trans c₂ cw), eB⟩
  | sigma _ _ _ => exact absurd same.symm (TypeEq.pi_ne_sigma facts formed)
  | id _ _ _ _ => exact absurd same.symm (TypeEq.pi_ne_id facts formed)
  | neutralType ls _ _ =>
      exact absurd rfl ((TypeEq.neutral_form facts same formed (Long.neutral_of_spine S.shape ls)
        (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _)

include facts roots heads algebra rigid complete in
/-- **A Σ type equal to a type of a universe has its components equal to types of that universe.** -/
theorem small_sigma {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {s A : Tm Head n} {B : Tm Head (n + 1)}
    {u : Head} (hu : S.R.isUniverse u) (ts : Typed S.R Γ s (.head u)) (equal : TypeEq S.R Γ s (.sigma A B)) :
    ∃ A' B', Typed S.R Γ A' (.head u) ∧ TypeEq S.R Γ A' A ∧ Typed S.R (.snoc Γ A') B' (.head u) ∧
      TypeEq S.R (.snoc Γ A') B' B := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨u, hu, ts⟩
  obtain ⟨tZ, eZ⟩ := atZ hu ts
  have sZ : TypeEq S.R Γ s Z := ⟨u, hu, eZ⟩
  have same : TypeEq S.R Γ Z (.sigma A B) := TypeEq.trans S.levels sZ.symm equal
  cases lZ with
  | head _ => exact absurd same.symm (TypeEq.sigma_ne_head facts formed)
  | pi _ _ _ => exact absurd same (TypeEq.pi_ne_sigma facts formed)
  | sigma _ _ _ =>
      obtain ⟨eA, eB⟩ := TypeEq.sigma_injective facts same formed
      have generation : GenerationAt S.R _ (.sigma _ _) (.head u) := Typed.generation tZ
      obtain ⟨u₁, u₂, w, tA, _, tB, _, join, le⟩ := generation
      obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
      have cw := typeLe_head_cumulative facts algebra formed (S.levels.join_level join).1 hu le
      exact ⟨_, _, Derivable.cumul tA (algebra.trans c₁ cw), eA, Derivable.cumul tB (algebra.trans c₂ cw), eB⟩
  | id _ _ _ _ => exact absurd same.symm (TypeEq.sigma_ne_id facts formed)
  | neutralType ls _ _ =>
      exact absurd rfl ((TypeEq.neutral_form facts same formed (Long.neutral_of_spine S.shape ls)
        (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 _ _)

include facts roots heads algebra rigid complete in
/-- **An identity type equal to a type of a universe has its type equal to a type of that universe.** -/
theorem small_id {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {s A a b : Tm Head n} {u : Head}
    (hu : S.R.isUniverse u) (ts : Typed S.R Γ s (.head u)) (equal : TypeEq S.R Γ s (.id A a b)) :
    ∃ A', Typed S.R Γ A' (.head u) ∧ TypeEq S.R Γ A' A := by
  obtain ⟨Z, lZ, atZ⟩ := long_type_exists facts roots heads algebra rigid complete formed ⟨u, hu, ts⟩
  obtain ⟨tZ, eZ⟩ := atZ hu ts
  have sZ : TypeEq S.R Γ s Z := ⟨u, hu, eZ⟩
  have same : TypeEq S.R Γ Z (.id A a b) := TypeEq.trans S.levels sZ.symm equal
  cases lZ with
  | head _ => exact absurd same.symm (TypeEq.id_ne_head facts formed)
  | pi _ _ _ => exact absurd same (TypeEq.pi_ne_id facts formed)
  | sigma _ _ _ => exact absurd same (TypeEq.sigma_ne_id facts formed)
  | id _ _ _ _ =>
      obtain ⟨eA, _, _⟩ := TypeEq.id_injective facts same formed
      have generation : GenerationAt S.R _ (.id _ _ _) (.head u) := Typed.generation tZ
      obtain ⟨u₁, tA, hu₁, _, _, le⟩ := generation
      exact ⟨_, Derivable.cumul tA (typeLe_head_cumulative facts algebra formed hu₁ hu le), eA⟩
  | neutralType ls _ _ =>
      exact absurd rfl ((TypeEq.neutral_form facts same formed (Long.neutral_of_spine S.shape ls)
        (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))).not_former.2.2.2 _ _ _)

include facts roots heads algebra rigid complete in
/-- **No type of a universe is equal to a type that holds, at a type position under formers, a universe the
universe does not hold or a variable declared at a universe that does not lie below it.** -/
theorem Above.not_small {u : Head} {n : Nat} {mark : Fin n → Bool} {t : Tm Head n} (above : Above S.R u mark t) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → Marked S.R u Γ mark → S.R.isUniverse u →
      ∀ {s : Tm Head n}, Typed S.R Γ s (.head u) → ¬ TypeEq S.R Γ s t := by
  induction above with
  | sort apart =>
      intro Γ formed _ hu s ts
      exact sort_not_small facts roots heads algebra rigid complete formed hu apart ts
  | @var n mark i held =>
      intro Γ formed marked hu s ts
      obtain ⟨w, declared, hw, apart⟩ := marked i held
      exact var_not_small facts roots heads algebra rigid complete formed declared hw hu apart ts
  | piDomain _ ih =>
      intro Γ formed marked hu s ts equal
      obtain ⟨_, _, tA, eA, _, _⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      exact ih formed marked hu tA eA
  | piCodomain _ ih =>
      intro Γ formed marked hu s ts equal
      obtain ⟨A', _, tA, _, tB, eB⟩ := small_pi facts roots heads algebra rigid complete formed hu ts equal
      exact ih (formed.snoc ⟨u, hu, tA⟩) (marked.snoc A') hu tB eB
  | sigmaFirst _ ih =>
      intro Γ formed marked hu s ts equal
      obtain ⟨_, _, tA, eA, _, _⟩ := small_sigma facts roots heads algebra rigid complete formed hu ts equal
      exact ih formed marked hu tA eA
  | sigmaSecond _ ih =>
      intro Γ formed marked hu s ts equal
      obtain ⟨A', _, tA, _, tB, eB⟩ := small_sigma facts roots heads algebra rigid complete formed hu ts equal
      exact ih (formed.snoc ⟨u, hu, tA⟩) (marked.snoc A') hu tB eB
  | id _ ih =>
      intro Γ formed marked hu s ts equal
      obtain ⟨_, tA, eA⟩ := small_id facts roots heads algebra rigid complete formed hu ts equal
      exact ih formed marked hu tA eA

include facts roots heads algebra rigid complete in
/-- **Under a telescope**: no term of the smaller telescope is equal, at the larger, to the type under the
abstractions. -/
theorem AboveUnder.apart {u : Head} {n : Nat} {mark : Fin n → Bool} {small large t : Tm Head n}
    (under : AboveUnder S.R u mark small large t) :
    ∀ {Γ : Ctx Head n}, Marked S.R u Γ mark → Apart S.R Γ small large t := by
  induction under with
  | base hu hv above =>
      intro Γ marked formed s ts equal
      exact above.not_small facts roots heads algebra rigid complete formed marked hu ts ⟨_, hv, equal⟩
  | pi _ ih => intro Γ marked; exact Apart.pi facts (ih (marked.snoc _))
  | bound hw apart _ ih => intro Γ marked; exact Apart.pi facts (ih (marked.snocBound hw apart))

end Semantics

end ContextualDependentUniverseInjective
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
