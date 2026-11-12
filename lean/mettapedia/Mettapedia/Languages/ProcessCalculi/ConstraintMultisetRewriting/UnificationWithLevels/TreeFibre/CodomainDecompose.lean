import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIntersectionGeneralDeadBinder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentVariableFactorization

/-!
# Equations between arrow codes with codomains: decomposition, as an exact rule

An equation between two arrow codes with codomains at a universe `U_v` (`ArrowCodEq`) whose sides are both Π types is
decomposed into its domains and its codomains.

* **Decomposition** (`decomposeCodUpdate`, `decomposeCod_exact`): `Π (_ : A). B ≐ Π (_ : A'). B'` at `U_v`, the
  codomains not using the argument, has exactly the solutions of `A ≐ A'` and `B ≐ B'` at `U_v`. Every solution of the
  parts solves the whole by congruence, the codomains weakened. Every solution of the whole solves the domains by
  injectivity of Π types, and the codomains by injectivity and by strengthening typed equality past the unused
  argument (`EqualStrengthening`, a property of the rule package); the codomains are typed without the argument by
  `strengthen_normal`.
* **Clashes** (`headPiCod_refutes`, `piHeadCod_refutes`): a head against a Π type. Two heads are first-order arrow
  codes (`arrowEqOfHeads`), so equal heads and clashing heads are the rules of `ArrowRules`.
* **Rigid shapes** (`rigidCodOf`): a head, or a Π type whose codomain is read without the argument; every arrow code
  with codomains that is not an unknown has one (`rigidCodOf_code`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative ContextualDependentNormalChecking

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The view -/

/-- **An equation between two arrow codes with codomains at a universe.** -/
structure ArrowCodEq {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  v : Head
  annotation_left : e.1.1.code = .head v
  annotation_right : e.2.1.code = .head v
  universe_v : S.R.isUniverse v
  code_left : ArrowCod e.1.2.code
  code_right : ArrowCod e.2.2.code

/-- The view of the swapped equation. -/
def ArrowCodEq.swap {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) :
    ArrowCodEq ((e.2, e.1) : Equation (TotalTerm Θ)) :=
  ⟨w.v, w.annotation_right, w.annotation_left, w.universe_v, w.code_right, w.code_left⟩

/-- A first-order equation between arrow codes is one with codomains. -/
def ArrowEq.toCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowEq e) : ArrowCodEq e :=
  ⟨w.v, w.annotation_left, w.annotation_right, w.universe_v, arrowCod_of_arrow w.arrow_left,
    arrowCod_of_arrow w.arrow_right⟩

/-- Two heads are first-order arrow codes. -/
def arrowEqOfHeads {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) {h h' : Head}
    (left : e.1.2.code = .head h) (right : e.2.2.code = .head h') : ArrowEq e where
  v := w.v
  annotation_left := w.annotation_left
  annotation_right := w.annotation_right
  universe_v := w.universe_v
  arrow_left := by rw [left]; exact .head h
  arrow_right := by rw [right]; exact .head h'

/-- The equation a solution solves, read at the annotation's universe. -/
theorem ArrowCodEq.solved {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) :
    Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code) (Presentation.subst σ.substitution e.2.2.code)
      (.head w.v) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code)
    (Presentation.subst σ.substitution e.2.2.code) (Presentation.subst σ.substitution e.1.1.code) at equal
  rw [w.annotation_left] at equal
  exact equal

/-- **The parts of a Π code with codomains** are codes with codomains. -/
theorem arrowCod_pi_parts {n : Nat} {A B : Tm Head n} (code : ArrowCod (.pi A (Presentation.rename wk B))) :
    ArrowCod A ∧ ArrowCod B := by
  generalize hB : Presentation.rename wk B = B' at code
  cases code with
  | pi codeA codeB =>
      rename_i B₀
      have same : B = B₀ :=
        ContextualDependentVariableFactorization.rename_injective wk (Fin.succ_injective _) hB
      subst same
      exact ⟨codeA, codeB⟩

/-! ## Typing of the parts -/

section Parts

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- **The parts of a Π type of a universe, its codomain not using the argument**: the domain and the codomain read
without the argument are types of that universe. -/
theorem pi_cod_parts_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A B : Tm Head n} {v : Head}
    (hv : S.R.isUniverse v) (normalB : Normal (S := S) (Presentation.rename wk B))
    (typed : Typed S.R Γ (.pi A (Presentation.rename wk B)) (.head v)) :
    Typed S.R Γ A (.head v) ∧ Typed S.R Γ B (.head v) := by
  have generation : GenerationAt S.R Γ (.pi A (Presentation.rename wk B)) (.head v) := Typed.generation typed
  obtain ⟨u₁, u₂, w, tA, hu₁, tB, hu₂, join, le⟩ := generation
  have cw := typeLe_head_cumulative facts algebra formed (S.levels.join_level join).1 hv le
  obtain ⟨c₁, c₂⟩ := S.levels.join_upper join
  have formedA : CtxFormed S.R (.snoc Γ A) := formed.snoc ⟨u₁, hu₁, tA⟩
  refine ⟨Derivable.cumul tA (algebra.trans c₁ cw), ?_⟩
  exact strengthen_normal facts roots heads algebra rigid complete headTypingUnique declared formed formedA hv normalB
    (Derivable.cumul tB (algebra.trans c₂ cw))

end Parts

/-! ## Decomposition -/

section Decompose

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

include rigid in
/-- The codomain of a Π code with codomains is normal after weakening. -/
theorem normal_weak_codomain {n : Nat} {A B : Tm Head n} (code : ArrowCod (.pi A (Presentation.rename wk B))) :
    Normal (S := S) (Presentation.rename wk B) :=
  PiCode.normal rigid ((piCode_of_arrowCod (arrowCod_pi_parts code).2).rename wk)

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- The parts of the left side, typed at the annotation's universe. -/
theorem leftParts_typed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) {A B : Tm Head Θ.arity}
    (left : e.1.2.code = .pi A (Presentation.rename wk B)) :
    Typed S.R Θ.raw A (.head w.v) ∧ Typed S.R Θ.raw B (.head w.v) := by
  have typed := e.1.2.typed
  rw [left, w.annotation_left] at typed
  have code := w.code_left
  rw [left] at code
  exact pi_cod_parts_typed facts roots heads algebra rigid complete headTypingUnique declared Θ.formed w.universe_v
    (normal_weak_codomain rigid code) typed

include facts roots heads algebra rigid complete headTypingUnique declared in
/-- The parts of the right side, typed at the annotation's universe. -/
theorem rightParts_typed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) {A B : Tm Head Θ.arity}
    (right : e.2.2.code = .pi A (Presentation.rename wk B)) :
    Typed S.R Θ.raw A (.head w.v) ∧ Typed S.R Θ.raw B (.head w.v) := by
  have typed := e.2.2.typed
  rw [right, w.annotation_right] at typed
  have code := w.code_right
  rw [right] at code
  exact pi_cod_parts_typed facts roots heads algebra rigid complete headTypingUnique declared Θ.formed w.universe_v
    (normal_weak_codomain rigid code) typed

/-- **The domain equation of a decomposition**, annotated where the equation is. -/
def domainCodEquation {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e)
    {A A' B B' : Tm Head Θ.arity} (left : e.1.2.code = .pi A (Presentation.rename wk B))
    (right : e.2.2.code = .pi A' (Presentation.rename wk B')) : Equation (TotalTerm Θ) :=
  (⟨e.1.1, ⟨A, by
      rw [w.annotation_left]
      exact (leftParts_typed facts roots heads algebra rigid complete headTypingUnique declared w left).1⟩⟩,
    ⟨e.1.1, ⟨A', by
      rw [w.annotation_left]
      exact (rightParts_typed facts roots heads algebra rigid complete headTypingUnique declared w right).1⟩⟩)

/-- **The codomain equation of a decomposition**, read without the argument. -/
def codomainCodEquation {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e)
    {A A' B B' : Tm Head Θ.arity} (left : e.1.2.code = .pi A (Presentation.rename wk B))
    (right : e.2.2.code = .pi A' (Presentation.rename wk B')) : Equation (TotalTerm Θ) :=
  (⟨e.1.1, ⟨B, by
      rw [w.annotation_left]
      exact (leftParts_typed facts roots heads algebra rigid complete headTypingUnique declared w left).2⟩⟩,
    ⟨e.1.1, ⟨B', by
      rw [w.annotation_left]
      exact (rightParts_typed facts roots heads algebra rigid complete headTypingUnique declared w right).2⟩⟩)

variable (strengthening : ContextualDependentIntersectionGeneral.EqualStrengthening S.R)

/-- **Decomposition with codomains**: `Π (_ : A). B ≐ Π (_ : A'). B'` becomes `A ≐ A'` and `B ≐ B'`. -/
def decomposeCodUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e)
    {A A' B B' : Tm Head Θ.arity} (left : e.1.2.code = .pi A (Presentation.rename wk B))
    (right : e.2.2.code = .pi A' (Presentation.rename wk B')) (rest : EquationStore (TotalTerm Θ)) :
    Update S.levels (e :: rest) where
  target := Θ
  answer := 𝟙 Θ
  remaining := domainCodEquation facts roots heads algebra rigid complete headTypingUnique declared w left right ::
    codomainCodEquation facts roots heads algebra rigid complete headTypingUnique declared w left right :: rest
  sound := by
    intro Δ g solved e' member
    rw [Category.comp_id]
    rcases List.mem_cons.mp member with rfl | member
    · have domains := ((equivalent_iff S.levels _ _).mp (solved _ List.mem_cons_self)).2
      change Equal S.R Δ.raw (Presentation.subst g.substitution A) (Presentation.subst g.substitution A')
        (Presentation.subst g.substitution e'.1.1.code) at domains
      rw [w.annotation_left] at domains
      have codomains :=
        ((equivalent_iff S.levels _ _).mp (solved _ (List.mem_cons_of_mem _ List.mem_cons_self))).2
      change Equal S.R Δ.raw (Presentation.subst g.substitution B) (Presentation.subst g.substitution B')
        (Presentation.subst g.substitution e'.1.1.code) at codomains
      rw [w.annotation_left] at codomains
      refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
      · change TypeEq S.R Δ.raw (Presentation.subst g.substitution e'.1.1.code)
          (Presentation.subst g.substitution e'.2.1.code)
        rw [w.annotation_left, w.annotation_right]
        exact IsType.refl (IsType.head_of_universe w.universe_v)
      · change Equal S.R Δ.raw (Presentation.subst g.substitution e'.1.2.code)
          (Presentation.subst g.substitution e'.2.2.code) (Presentation.subst g.substitution e'.1.1.code)
        rw [left, right, w.annotation_left]
        change Equal S.R Δ.raw
          (.pi (Presentation.subst g.substitution A)
            (Presentation.subst (liftSub g.substitution) (Presentation.rename wk B)))
          (.pi (Presentation.subst g.substitution A')
            (Presentation.subst (liftSub g.substitution) (Presentation.rename wk B'))) (.head w.v)
        rw [subst_liftSub_wk, subst_liftSub_wk]
        have codomain : Equal S.R (.snoc Δ.raw (Presentation.subst g.substitution A))
            (Presentation.rename wk (Presentation.subst g.substitution B))
            (Presentation.rename wk (Presentation.subst g.substitution B')) (.head w.v) :=
          Equal.weaken codomains
        obtain ⟨w', join⟩ := S.levels.join_exists w.universe_v w.universe_v
        exact Derivable.cumulEq (Derivable.piCong domains w.universe_v codomain w.universe_v join)
          (algebra.join_least join (S.levels.cumulative_refl w.universe_v) (S.levels.cumulative_refl w.universe_v))
    · exact solved e' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  complete := by
    intro Δ f solved
    refine ⟨f, ?_, fun term => ?_⟩
    · have whole := w.solved f (solved e List.mem_cons_self)
      rw [left, right] at whole
      change Equal S.R Δ.raw
        (.pi (Presentation.subst f.substitution A)
          (Presentation.subst (liftSub f.substitution) (Presentation.rename wk B)))
        (.pi (Presentation.subst f.substitution A')
          (Presentation.subst (liftSub f.substitution) (Presentation.rename wk B'))) (.head w.v) at whole
      rw [subst_liftSub_wk, subst_liftSub_wk] at whole
      obtain ⟨domains, codomains⟩ := TypeEq.pi_injective facts ⟨w.v, w.universe_v, whole⟩ Δ.formed
      obtain ⟨tA, tB⟩ := leftParts_typed facts roots heads algebra rigid complete headTypingUnique declared w left
      obtain ⟨tA', tB'⟩ := rightParts_typed facts roots heads algebra rigid complete headTypingUnique declared w right
      have sA : Typed S.R Δ.raw (Presentation.subst f.substitution A) (.head w.v) := tA.substitute f.typed
      have sA' : Typed S.R Δ.raw (Presentation.subst f.substitution A') (.head w.v) := tA'.substitute f.typed
      have sB : Typed S.R Δ.raw (Presentation.subst f.substitution B) (.head w.v) := tB.substitute f.typed
      have sB' : Typed S.R Δ.raw (Presentation.subst f.substitution B') (.head w.v) := tB'.substitute f.typed
      intro e' member
      rcases List.mem_cons.mp member with rfl | member
      · refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
        · change TypeEq S.R Δ.raw (Presentation.subst f.substitution e.1.1.code)
            (Presentation.subst f.substitution e.1.1.code)
          rw [w.annotation_left]
          exact IsType.refl (IsType.head_of_universe w.universe_v)
        · change Equal S.R Δ.raw (Presentation.subst f.substitution A) (Presentation.subst f.substitution A')
            (Presentation.subst f.substitution e.1.1.code)
          rw [w.annotation_left]
          exact equal_at_universe facts roots heads algebra rigid complete Δ.formed w.universe_v sA sA' domains
      rcases List.mem_cons.mp member with rfl | member
      · refine (equivalent_iff S.levels _ _).mpr ⟨?_, ?_⟩
        · change TypeEq S.R Δ.raw (Presentation.subst f.substitution e.1.1.code)
            (Presentation.subst f.substitution e.1.1.code)
          rw [w.annotation_left]
          exact IsType.refl (IsType.head_of_universe w.universe_v)
        · change Equal S.R Δ.raw (Presentation.subst f.substitution B) (Presentation.subst f.substitution B')
            (Presentation.subst f.substitution e.1.1.code)
          rw [w.annotation_left]
          have formedA : CtxFormed S.R (.snoc Δ.raw (Presentation.subst f.substitution A)) :=
            Δ.formed.snoc (TypeEq.isType domains Δ.formed).1
          have wB : Typed S.R (.snoc Δ.raw (Presentation.subst f.substitution A))
              (Presentation.rename wk (Presentation.subst f.substitution B)) (.head w.v) := Typed.weaken sB
          have wB' : Typed S.R (.snoc Δ.raw (Presentation.subst f.substitution A))
              (Presentation.rename wk (Presentation.subst f.substitution B')) (.head w.v) := Typed.weaken sB'
          have weakEqual := equal_at_universe facts roots heads algebra rigid complete formedA w.universe_v wB wB'
            codomains
          exact strengthening formedA sB sB' weakEqual
      · exact solved e' (List.mem_cons_of_mem _ member)
    · rw [Category.comp_id]
      exact ((frames S.levels).equivalence Δ).refl _

include strengthening in
/-- **Decomposition with codomains is exact.** -/
theorem decomposeCod_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e)
    {A A' B B' : Tm Head Θ.arity} (left : e.1.2.code = .pi A (Presentation.rename wk B))
    (right : e.2.2.code = .pi A' (Presentation.rename wk B')) (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (𝟙 Θ)
      (domainCodEquation facts roots heads algebra rigid complete headTypingUnique declared w left right ::
        codomainCodEquation facts roots heads algebra rigid complete headTypingUnique declared w left right :: rest) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨decomposeCodUpdate facts roots heads algebra rigid complete headTypingUnique declared strengthening w left right
      rest, rfl, rfl, rfl⟩

end Decompose

/-! ## Clashes -/

section Clashes

variable (facts : FormFacts S.R S.roles)

include facts in
/-- **A head clashes with a Π type.** -/
theorem headPiCod_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) {h : Head}
    {A : Tm Head Θ.arity} {B : Tm Head (Θ.arity + 1)} (left : e.1.2.code = .head h) (right : e.2.2.code = .pi A B)
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := w.solved σ (models e List.mem_cons_self)
  rw [left, right] at equal
  exact TypeEq.pi_ne_head facts Δ.formed ⟨w.v, w.universe_v, .symm equal⟩

include facts in
/-- **A Π type clashes with a head.** -/
theorem piHeadCod_refutes {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (w : ArrowCodEq e) {h : Head}
    {A : Tm Head Θ.arity} {B : Tm Head (Θ.arity + 1)} (left : e.1.2.code = .pi A B) (right : e.2.2.code = .head h)
    (rest : EquationStore (TotalTerm Θ)) : ¬ (frames S.levels).Solvable (e :: rest) := by
  rintro ⟨Δ, σ, models⟩
  have equal := w.solved σ (models e List.mem_cons_self)
  rw [left, right] at equal
  exact TypeEq.pi_ne_head facts Δ.formed ⟨w.v, w.universe_v, equal⟩

end Clashes

/-! ## Rigid shapes -/

section RigidShapes

/-- The rigid shapes of an arrow code with codomains: a head, or a Π type with its codomain read without the
argument. -/
inductive RigidCod (Head : Type) (n : Nat) where
  | head (h : Head)
  | pi (A B : Tm Head n)

/-- Read the rigid shape of a code. -/
def rigidCodOf {n : Nat} : Tm Head n → Option (RigidCod Head n)
  | .head h => some (.head h)
  | .pi A B => (ContextualDependentInPlace.strengthenCode B).map fun B₀ => .pi A B₀.1
  | _ => none

theorem rigidCodOf_head {n : Nat} {t : Tm Head n} {h : Head} (found : rigidCodOf t = some (.head h)) :
    t = .head h := by
  cases t with
  | head h' =>
      simp only [rigidCodOf, Option.some.injEq, RigidCod.head.injEq] at found
      rw [found]
  | pi A B =>
      simp only [rigidCodOf, Option.map_eq_some_iff] at found
      obtain ⟨_, _, impossible⟩ := found
      cases impossible
  | _ => simp [rigidCodOf] at found

theorem rigidCodOf_pi {n : Nat} {t : Tm Head n} {A B : Tm Head n} (found : rigidCodOf t = some (.pi A B)) :
    t = .pi A (Presentation.rename wk B) := by
  cases t with
  | head h' => simp [rigidCodOf] at found
  | pi A' B' =>
      simp only [rigidCodOf, Option.map_eq_some_iff] at found
      obtain ⟨B₀, _, same⟩ := found
      simp only [RigidCod.pi.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rw [B₀.2]
  | _ => simp [rigidCodOf] at found

/-- **An arrow code with codomains that is not an unknown has a rigid shape.** -/
theorem rigidCodOf_code {n : Nat} {t : Tm Head n} (code : ArrowCod t) (notVar : varOf t = none) :
    (rigidCodOf t).isSome = true := by
  cases code with
  | var Y => cases notVar
  | head h => rfl
  | @pi A B _ _ =>
      have strong := ContextualDependentSpinesMany.strengthenCode_rename B
      show ((ContextualDependentInPlace.strengthenCode (Presentation.rename wk B)).map
        (fun B₀ => RigidCod.pi A B₀.1)).isSome = true
      cases found : ContextualDependentInPlace.strengthenCode (Presentation.rename wk B) with
      | none =>
          rw [found] at strong
          cases strong
      | some B₀ => rfl

end RigidShapes

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
