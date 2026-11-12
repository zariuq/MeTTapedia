import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidSolver

/-!
# Equations between arrow codes: rigid decomposition and clashes, as exact rules

An equation between two arrow codes at a universe `U_v` (`ArrowEq`) whose sides are both rigid is decided by its
formers and heads:

* **Decomposition** (`decomposeUpdate`, `decompose_exact`): `Π (_ : A). h ≐ Π (_ : A'). h'` with `h` and `h'` the same
  head up to the rule package's head equality has exactly the solutions of `A ≐ A'` at `U_v`. Every solution of the
  domain equation solves the whole by congruence; every solution of the whole solves the domains by injectivity of
  Π types, compared at `U_v` (`equal_at_universe`).
* **Equal heads** (`headEqUpdate`, `headEq_exact`): `h ≐ h'` with `h` and `h'` related by head equality is solved by
  every substitution.
* **Clashes** (`headClash_refutes`, `headPi_refutes`, `piHead_refutes`, `codomainClash_refutes`): two different
  heads, a head against a Π type, and Π types with different codomain heads have no solution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **An equation between two arrow codes at a universe.** -/
structure ArrowEq {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  v : Head
  annotation_left : e.1.1.code = .head v
  annotation_right : e.2.1.code = .head v
  universe_v : S.R.isUniverse v
  arrow_left : Arrow e.1.2.code
  arrow_right : Arrow e.2.2.code

/-- The view of the swapped equation. -/
def ArrowEq.swap {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) :
    ArrowEq ((e.2, e.1) : Equation (TotalTerm Θ)) :=
  ⟨w.v, w.annotation_right, w.annotation_left, w.universe_v, w.arrow_right, w.arrow_left⟩

/-- The equation a solution solves, read at the annotation's universe. -/
theorem ArrowEq.solved {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) :
    Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code) (Presentation.subst σ.substitution e.2.2.code)
      (.head w.v) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code)
    (Presentation.subst σ.substitution e.2.2.code) (Presentation.subst σ.substitution e.1.1.code) at equal
  rw [w.annotation_left] at equal
  exact equal

section Rules

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts algebra in
/-- A head typed at a universe is typed at it in every telescope. -/
theorem head_typed_everywhere {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {h u : Head}
    (hu : S.R.isUniverse u) (typed : Typed S.R Γ (.head h) (.head u)) :
    ∀ {m : Nat} (Δ : Ctx Head m), Typed S.R Δ (.head h) (.head u) := by
  obtain ⟨above, typing, c⟩ := head_typed_cumulative facts algebra formed hu typed
  intro m Δ
  exact Derivable.cumul (Derivable.headType typing) c

include facts algebra in
/-- The parts of a Π type of a universe: its domain is a type of that universe, and its codomain head too. -/
theorem pi_parts_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n} {h v : Head}
    (hv : S.R.isUniverse v) (typed : Typed S.R Γ (.pi A (.head h)) (.head v)) :
    Typed S.R Γ A (.head v) ∧ ∀ {m : Nat} (Δ : Ctx Head m), Typed S.R Δ (.head h) (.head v) := by
  have generation : GenerationAt S.R Γ (.pi A (.head h)) (.head v) := Typed.generation typed
  obtain ⟨u₁, u₂, w, tA, hu₁, tB, hu₂, join, le⟩ := generation
  have cw := typeLe_head_cumulative facts algebra formed (S.levels.join_level join).1 hv le
  obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
  have formedA : CtxFormed S.R (.snoc Γ A) := formed.snoc ⟨u₁, hu₁, tA⟩
  refine ⟨Derivable.cumul tA (algebra.trans c₁ cw), fun Δ => ?_⟩
  exact head_typed_everywhere facts algebra formedA hv (Derivable.cumul tB (algebra.trans c₂ cw)) Δ

/-- **The domain equation of a decomposition**, annotated where the equation is. -/
def domainEquation {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {A A' : Tm Head Θ.arity}
    {h h' : Head} (left : e.1.2.code = .pi A (.head h)) (right : e.2.2.code = .pi A' (.head h')) :
    Equation (TotalTerm Θ) :=
  (⟨e.1.1, ⟨A, by
      have typed := e.1.2.typed
      rw [left, w.annotation_left] at typed
      rw [w.annotation_left]
      exact (pi_parts_typed facts algebra Θ.formed w.universe_v typed).1⟩⟩,
    ⟨e.1.1, ⟨A', by
      have typed := e.2.2.typed
      rw [right, w.annotation_right] at typed
      rw [w.annotation_left]
      exact (pi_parts_typed facts algebra Θ.formed w.universe_v typed).1⟩⟩)

/-- **Decomposition**: `Π (_ : A). h ≐ Π (_ : A'). h'` with the same codomain head becomes `A ≐ A'`. -/
def decomposeUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {A A' : Tm Head Θ.arity}
    {h h' : Head} (left : e.1.2.code = .pi A (.head h)) (right : e.2.2.code = .pi A' (.head h'))
    (same : HeadSame S.R h h') (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := 𝟙 Θ
  remaining := domainEquation facts algebra w left right :: rest
  sound := by
    intro Δ g solved e' member
    rw [Category.comp_id]
    rcases List.mem_cons.mp member with rfl | member
    · have domains := ((equivalent_iff S.levels _ _).mp (solved _ List.mem_cons_self)).2
      change Equal S.R Δ.raw (Presentation.subst g.substitution A) (Presentation.subst g.substitution A')
        (Presentation.subst g.substitution e'.1.1.code) at domains
      rw [w.annotation_left] at domains
      have typedL := e'.1.2.typed
      rw [left, w.annotation_left] at typedL
      have typedR := e'.2.2.typed
      rw [right, w.annotation_right] at typedR
      have hT : ∀ {m : Nat} (Γ' : Ctx Head m), Typed S.R Γ' (.head h) (.head w.v) :=
        fun Γ' => (pi_parts_typed facts algebra Θ.formed w.universe_v typedL).2 Γ'
      have hT' : ∀ {m : Nat} (Γ' : Ctx Head m), Typed S.R Γ' (.head h') (.head w.v) :=
        fun Γ' => (pi_parts_typed facts algebra Θ.formed w.universe_v typedR).2 Γ'
      refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
      · change TypeEq S.R Δ.raw (Presentation.subst g.substitution e'.1.1.code)
          (Presentation.subst g.substitution e'.2.1.code)
        rw [w.annotation_left, w.annotation_right]
        exact IsType.refl (IsType.head_of_universe w.universe_v)
      · change Equal S.R Δ.raw (Presentation.subst g.substitution e'.1.2.code)
          (Presentation.subst g.substitution e'.2.2.code) (Presentation.subst g.substitution e'.1.1.code)
        rw [left, right, w.annotation_left]
        change Equal S.R Δ.raw (.pi (Presentation.subst g.substitution A) (.head h))
          (.pi (Presentation.subst g.substitution A') (.head h')) (.head w.v)
        have codomain : Equal S.R (.snoc Δ.raw (Presentation.subst g.substitution A)) (.head h) (.head h')
            (.head w.v) := by
          rcases same with rfl | equal
          · exact .refl (hT _)
          · exact .headEq equal (hT _) (hT' _)
        obtain ⟨w', join⟩ := S.levels.join_exists w.universe_v w.universe_v
        exact Derivable.cumulEq (Derivable.piCong domains w.universe_v codomain w.universe_v join)
          (algebra.join_least join (S.levels.cumulative_refl w.universe_v) (S.levels.cumulative_refl w.universe_v))
    · exact solved e' (List.mem_cons_of_mem _ member)
  complete := by
    intro Δ f solved
    refine ⟨f, ?_, fun term => ?_⟩
    · intro e' member
      rcases List.mem_cons.mp member with rfl | member
      · have whole := w.solved f (solved e List.mem_cons_self)
        rw [left, right] at whole
        change Equal S.R Δ.raw (.pi (Presentation.subst f.substitution A) (.head h))
          (.pi (Presentation.subst f.substitution A') (.head h')) (.head w.v) at whole
        have domains := (TypeEq.pi_injective facts ⟨w.v, w.universe_v, whole⟩ Δ.formed).1
        have typedL := e.1.2.typed
        rw [left, w.annotation_left] at typedL
        have typedR := e.2.2.typed
        rw [right, w.annotation_right] at typedR
        have tA := ((pi_parts_typed facts algebra Θ.formed w.universe_v typedL).1).substitute f.typed
        have tA' := ((pi_parts_typed facts algebra Θ.formed w.universe_v typedR).1).substitute f.typed
        refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
        · change TypeEq S.R Δ.raw (Presentation.subst f.substitution e.1.1.code)
            (Presentation.subst f.substitution e.1.1.code)
          rw [w.annotation_left]
          exact IsType.refl (IsType.head_of_universe w.universe_v)
        · change Equal S.R Δ.raw (Presentation.subst f.substitution A) (Presentation.subst f.substitution A')
            (Presentation.subst f.substitution e.1.1.code)
          rw [w.annotation_left]
          exact equal_at_universe facts roots heads algebra rigid complete Δ.formed w.universe_v tA tA' domains
      · exact solved e' (List.mem_cons_of_mem _ member)
    · rw [Category.comp_id]
      exact ((frames S.levels).equivalence Δ).refl _

include facts roots heads algebra rigid complete in
/-- **Decomposition is exact.** -/
theorem decompose_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {A A' : Tm Head Θ.arity}
    {h h' : Head} (left : e.1.2.code = .pi A (.head h)) (right : e.2.2.code = .pi A' (.head h'))
    (same : HeadSame S.R h h') (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (𝟙 Θ) (domainEquation facts algebra w left right :: rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨decomposeUpdate facts roots heads algebra rigid complete w left right same rest, rfl, rfl, rfl⟩

/-- **Equal heads**: `h ≐ h'` with `h` and `h'` related by head equality is removed. -/
def headEqUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {h h' : Head}
    (left : e.1.2.code = .head h) (right : e.2.2.code = .head h') (equal : S.R.headEq h h')
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) where
  target := Θ
  answer := 𝟙 Θ
  remaining := rest
  sound := by
    intro Δ g solved e' member
    rw [Category.comp_id]
    rcases List.mem_cons.mp member with rfl | member
    · have typedL := e'.1.2.typed
      rw [left, w.annotation_left] at typedL
      have typedR := e'.2.2.typed
      rw [right, w.annotation_right] at typedR
      refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
      · change TypeEq S.R Δ.raw (Presentation.subst g.substitution e'.1.1.code)
          (Presentation.subst g.substitution e'.2.1.code)
        rw [w.annotation_left, w.annotation_right]
        exact IsType.refl (IsType.head_of_universe w.universe_v)
      · change Equal S.R Δ.raw (Presentation.subst g.substitution e'.1.2.code)
          (Presentation.subst g.substitution e'.2.2.code) (Presentation.subst g.substitution e'.1.1.code)
        rw [left, right, w.annotation_left]
        exact .headEq equal (head_typed_everywhere facts algebra Θ.formed w.universe_v typedL _)
          (head_typed_everywhere facts algebra Θ.formed w.universe_v typedR _)
    · exact solved e' member
  complete := by
    intro Δ f solved
    refine ⟨f, fun e' member => solved e' (List.mem_cons_of_mem _ member), fun term => ?_⟩
    rw [Category.comp_id]
    exact ((frames S.levels).equivalence Δ).refl _

include facts algebra in
/-- **Removing an equation between equal heads is exact.** -/
theorem headEq_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {h h' : Head}
    (left : e.1.2.code = .head h) (right : e.2.2.code = .head h') (equal : S.R.headEq h h')
    (rest : EquationStore (TotalTerm Θ)) : Exact (frames S.levels) (e :: rest) (𝟙 Θ) rest :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨headEqUpdate facts algebra w left right equal rest, rfl, rfl, rfl⟩

include facts in
/-- **Two different heads clash.** -/
theorem headClash_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {h h' : Head}
    (left : e.1.2.code = .head h) (right : e.2.2.code = .head h') (apart : ¬ HeadSame S.R h h')
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := w.solved σ (models e List.mem_cons_self)
  rw [left, right] at equal
  exact apart (TypeEq.head_injective facts ⟨w.v, w.universe_v, equal⟩ Δ.formed)

include facts in
/-- **A head clashes with a Π type.** -/
theorem headPi_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {h : Head}
    {A : Tm Head Θ.arity} {B : Tm Head (Θ.arity + 1)} (left : e.1.2.code = .head h) (right : e.2.2.code = .pi A B)
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := w.solved σ (models e List.mem_cons_self)
  rw [left, right] at equal
  exact TypeEq.pi_ne_head facts Δ.formed ⟨w.v, w.universe_v, .symm equal⟩

include facts in
/-- **A Π type clashes with a head.** -/
theorem piHead_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) {h : Head}
    {A : Tm Head Θ.arity} {B : Tm Head (Θ.arity + 1)} (left : e.1.2.code = .pi A B) (right : e.2.2.code = .head h)
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := w.solved σ (models e List.mem_cons_self)
  rw [left, right] at equal
  exact TypeEq.pi_ne_head facts Δ.formed ⟨w.v, w.universe_v, equal⟩

include facts in
/-- **Π types with different codomain heads clash.** -/
theorem codomainClash_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e)
    {A A' : Tm Head Θ.arity} {h h' : Head} (left : e.1.2.code = .pi A (.head h))
    (right : e.2.2.code = .pi A' (.head h')) (apart : ¬ HeadSame S.R h h') (rest : EquationStore (TotalTerm Θ)) :
    ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := w.solved σ (models e List.mem_cons_self)
  rw [left, right] at equal
  change Equal S.R Δ.raw (.pi (Presentation.subst σ.substitution A) (.head h))
    (.pi (Presentation.subst σ.substitution A') (.head h')) (.head w.v) at equal
  obtain ⟨domains, codomains⟩ := TypeEq.pi_injective facts ⟨w.v, w.universe_v, equal⟩ Δ.formed
  have formedA : CtxFormed S.R (.snoc Δ.raw (Presentation.subst σ.substitution A)) :=
    Δ.formed.snoc (TypeEq.isType domains Δ.formed).1
  exact apart (TypeEq.head_injective facts codomains formedA)

end Rules

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
