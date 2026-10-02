import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Package
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment

/-!
# Church–Rosser for the base of the accessibility package, and the separation

The root computation of a base package whose only rule is linear identity
elimination, `J A x M d y (refl z) ⟶ d`, extended by a package of proposition
codes, is a definition by constructor patterns:

* `J` applied to six patterns, the last `refl z`;
* the decoder `holds` applied to `imp p q`, to `a f` for each quantifier
  instance `a`, and to `e x y` for each equation instance `e`.

Each left side is linear, every variable of a right side occurs on its left,
and two left sides that unify are the same equation. With β, the pair
projections and a symmetric universe-head equality, the extended package is
therefore Church–Rosser (`Confluence.churchRosser`), by the complete
development of `ConstructorSystemDevelopment`. The accessibility package adds
no computation (`Signature.rules_computation`), so the same holds for it.

**Separation.** In a Church–Rosser package where a constant `c` heads no
equation, reduction keeps a spine headed by `c` headed by `c`
(`stepStar_spineHead`), and keeps a spine headed by a variable headed by that
variable (`stepStar_varHead`). So a `c`-headed spine and a variable-headed
spine are never convertible (`not_conv_spineHead_varHead`). For the recursor
with a variable step function `F`, the application `rec P R F a q` is headed by
the recursor and its unfolding `F a (λ y r. …)` by `F`: conversion does not
identify the recursor with its unfolding (`Signature.separation`), although
the propositional unfolding proves them equal. The same holds when the
unfolding computes to a spine headed by another constant that heads no equation
(`Signature.separation_of_reduct`), and under a variable predicate: the
decoder does not decode a code headed by a variable, so `holds (Q (rec …))` and
`holds (Q (F a …))` are not convertible either (`Signature.holds_separation`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization (DecoderStep appSpine)
open Presentation.AlgebraicSchema (SchemaFamily SchemaStep variableMultiplicity)
open Presentation.AlgebraicParallel
open Presentation.ConversionCoherence (ChurchRosser StepStar)
open Presentation.ConstructorSystem (Pattern LeftSide System ConstructorPresentation spineHead
  unifiable determined_of_disjoint)

variable {Head : Type}

namespace Confluence

/-! ## The equations -/

/-- One step of linear identity elimination: `J A x M d y (refl z) ⟶ d`. -/
def JStep (J : DeclName) {n : Nat} (l r : Tm Head n) : Prop :=
  ∃ a₀ a₁ a₂ a₃ a₄ a₅ : Tm Head n, l = appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl a₅] ∧ r = a₃

/-- `J A x M d y (refl z)`, over `A x M d y z`. -/
def elimLeft (J : DeclName) : Tm Head 6 :=
  .app (.app (.app (.app (.app (.app (.const J) (.var 0)) (.var 1)) (.var 2)) (.var 3)) (.var 4))
    (.refl (.var 5))

/-- `holds (imp p q)`, over `p q`. -/
def impLeft (K : Codes Head) : Tm Head 2 := K.holdsOf (K.impOf (.var 0) (.var 1))

/-- `Π (_ : holds p). holds q`, over `p q`. -/
def impRight (K : Codes Head) : Tm Head 2 := .pi (K.holdsOf (.var 0)) (K.holdsOf (.var 2))

/-- `holds (a f)`, over `f`. -/
def allLeft (K : Codes Head) (a : DeclName) : Tm Head 1 := K.holdsOf (.app (.const a) (.var 0))

/-- `Π (x : A). holds (f x)`, over `f`. -/
def allRight (K : Codes Head) (A : Tm Head 0) : Tm Head 1 :=
  .pi (liftClosed A) (K.holdsOf (.app (.var 1) (.var 0)))

/-- `holds (e x y)`, over `x y`. -/
def eqLeft (K : Codes Head) (e : DeclName) : Tm Head 2 :=
  K.holdsOf (.app (.app (.const e) (.var 0)) (.var 1))

/-- `Id A x y`, over `x y`. -/
def eqRight (A : Tm Head 0) : Tm Head 2 := .id (liftClosed A) (.var 0) (.var 1)

/-- The equations of the base: linear identity elimination and the decoders. -/
inductive Schema (J : DeclName) (K : Codes Head) : SchemaFamily Head
  | elim : Schema J K (elimLeft J) (.var 3)
  | imp : Schema J K (impLeft K) (impRight K)
  | all {a : DeclName} {A : Tm Head 0} : K.quantifiers a = some A →
      Schema J K (allLeft K a) (allRight K A)
  | eq {e : DeclName} {A : Tm Head 0} : K.equationCarrier e = some A →
      Schema J K (eqLeft K e) (eqRight A)

/-- The names are apart: `J` is not the decoder, and no code constructor is `J`
or the decoder; an equation instance is not implication. -/
structure Names (J : DeclName) (K : Codes Head) : Prop where
  j_ne_holds : J ≠ K.holds
  imp_ne_j : K.imp ≠ J
  imp_ne_holds : K.imp ≠ K.holds
  all_ne : ∀ {a : DeclName} {A : Tm Head 0}, K.quantifiers a = some A → a ≠ J ∧ a ≠ K.holds
  eq_ne : ∀ {e : DeclName} {A : Tm Head 0}, K.equationCarrier e = some A →
    e ≠ J ∧ e ≠ K.holds ∧ e ≠ K.imp

/-! ## The computation is the equations -/

theorem subst_elimLeft (J : DeclName) {n : Nat} (σ : Sub Head 6 n) :
    subst σ (elimLeft J) = appSpine (.const J) [σ 0, σ 1, σ 2, σ 3, σ 4, .refl (σ 5)] := rfl

theorem subst_allRight (K : Codes Head) (A : Tm Head 0) {n : Nat} (σ : Sub Head 1 n) :
    subst σ (allRight K A) =
      .pi (liftClosed A) (K.holdsOf (.app (rename wk (σ 0)) (.var 0))) := by
  simp only [allRight, Presentation.subst, subst_liftClosed, Codes.holdsOf]
  rfl

theorem subst_eqRight (A : Tm Head 0) {n : Nat} (σ : Sub Head 2 n) :
    subst σ (eqRight (Head := Head) A) = .id (liftClosed A) (σ 0) (σ 1) := by
  simp only [eqRight, Presentation.subst, subst_liftClosed]

/-- **The root computation of the extended base is exactly the instances of
the equations.** -/
theorem step_iff (J : DeclName) (K : Codes Head) {base : Rules Head}
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {l r : Tm Head n} :
    (K.extend base).computation.step l r ↔ SchemaStep (Schema J K) l r := by
  constructor
  · rintro (step | step)
    · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, hl, hr⟩ := computes.mp step
      rw [hl, hr]
      exact SchemaStep.instantiate Schema.elim
        (fun i => [a₀, a₁, a₂, a₃, a₄, a₅].get ⟨i.1, by simp⟩)
    · cases step with
      | imp p q =>
          exact SchemaStep.instantiate Schema.imp (fun i => [p, q].get ⟨i.1, by simp⟩)
      | all carrier f =>
          have h := SchemaStep.instantiate (Schema.all (J := J) (K := K) carrier)
            (fun _ : Fin 1 => f)
          rw [subst_allRight] at h
          exact h
      | eq carrier x y =>
          have h := SchemaStep.instantiate (Schema.eq (J := J) (K := K) carrier)
            (fun i => [x, y].get ⟨i.1, by simp⟩)
          rw [subst_eqRight] at h
          exact h
  · intro step
    cases step with
    | instantiate rule σ =>
        cases rule with
        | elim => exact .inl (computes.mpr ⟨σ 0, σ 1, σ 2, σ 3, σ 4, σ 5, rfl, rfl⟩)
        | imp => exact .inr (DecoderStep.imp (σ 0) (σ 1))
        | all carrier =>
            rw [subst_allRight]
            exact .inr (DecoderStep.all (D := K.decoders) carrier (σ 0))
        | eq carrier =>
            rw [subst_eqRight]
            exact .inr (DecoderStep.eq (D := K.decoders) carrier (σ 0) (σ 1))

/-! ## A constructor system -/

/-- The defined constants: `J` and the decoder. -/
def Defined (J : DeclName) (K : Codes Head) (c : DeclName) : Prop := c = J ∨ c = K.holds

/-- Their arities. -/
def arity (J : DeclName) (K : Codes Head) (c : DeclName) : Nat :=
  if c = J then 6 else if c = K.holds then 1 else 0

variable {J : DeclName} {K : Codes Head}

theorem arity_j : arity (Head := Head) J K J = 6 := if_pos rfl

theorem arity_holds (names : Names J K) : arity (Head := Head) J K K.holds = 1 := by
  simp only [arity, if_neg (Ne.symm names.j_ne_holds), if_true]

theorem not_defined_of_ne {c : DeclName} (hJ : c ≠ J) (hholds : c ≠ K.holds) : ¬ Defined J K c := by
  rintro (h | h)
  · exact hJ h
  · exact hholds h

theorem schema_left (names : Names J K) {m : Nat} {left right : Tm Head m}
    (rule : Schema J K left right) :
    ∃ name, Defined J K name ∧ 0 < arity J K name ∧ LeftSide (Defined J K) left name (arity J K name) := by
  cases rule with
  | elim =>
      refine ⟨J, .inl rfl, by rw [arity_j]; decide, ?_⟩
      rw [arity_j]
      exact .app (.app (.app (.app (.app (.app (.const J) (.var 0)) (.var 1)) (.var 2)) (.var 3))
        (.var 4)) (.refl (.var 5))
  | imp =>
      refine ⟨K.holds, .inr rfl, by rw [arity_holds names]; decide, ?_⟩
      rw [arity_holds names]
      exact .app (.const _) (.app (.app (.const (not_defined_of_ne names.imp_ne_j names.imp_ne_holds))
        (.var 0)) (.var 1))
  | all carrier =>
      refine ⟨K.holds, .inr rfl, by rw [arity_holds names]; decide, ?_⟩
      rw [arity_holds names]
      exact .app (.const _) (.app (.const (not_defined_of_ne (names.all_ne carrier).1
        (names.all_ne carrier).2)) (.var 0))
  | eq carrier =>
      refine ⟨K.holds, .inr rfl, by rw [arity_holds names]; decide, ?_⟩
      rw [arity_holds names]
      exact .app (.const _) (.app (.app (.const (not_defined_of_ne (names.eq_ne carrier).1
        (names.eq_ne carrier).2.1)) (.var 0)) (.var 1))

/-- Every variable of a left side occurs exactly once. -/
theorem schema_multiplicity {m : Nat} {left right : Tm Head m} (rule : Schema J K left right)
    (index : Fin m) : variableMultiplicity index left = 1 := by
  cases rule with
  | elim =>
      match index with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | 3 => rfl
      | 4 => rfl
      | 5 => rfl
  | imp =>
      match index with
      | 0 => rfl
      | 1 => rfl
  | all _ =>
      match index with
      | 0 => rfl
  | eq _ =>
      match index with
      | 0 => rfl
      | 1 => rfl

/-- Two equations whose left sides unify are the same equation. -/
theorem schema_disjoint (names : Names J K) {m m' : Nat} {left right : Tm Head m}
    {left' right' : Tm Head m'} (rule : Schema J K left right) (rule' : Schema J K left' right')
    (meet : unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tm Head arity × Tm Head arity) = ⟨m', (left', right')⟩ := by
  cases rule with
  | elim =>
      cases rule' with
      | elim => rfl
      | imp => simp [unifiable, elimLeft, impLeft] at meet
      | all _ => simp [unifiable, elimLeft, allLeft] at meet
      | eq _ => simp [unifiable, elimLeft, eqLeft] at meet
  | imp =>
      cases rule' with
      | elim => simp [unifiable, elimLeft, impLeft] at meet
      | imp => rfl
      | all _ => simp [unifiable, impLeft, allLeft] at meet
      | eq carrier =>
          simp only [unifiable, impLeft, eqLeft, Codes.holdsOf, Codes.impOf, decide_true,
            Bool.true_and, Bool.and_true, decide_eq_true_eq] at meet
          exact absurd meet.symm (names.eq_ne carrier).2.2
  | all carrier =>
      cases rule' with
      | elim => simp [unifiable, elimLeft, allLeft] at meet
      | imp => simp [unifiable, impLeft, allLeft] at meet
      | all carrier' =>
          simp only [unifiable, allLeft, Codes.holdsOf, decide_true, Bool.true_and, Bool.and_true,
            decide_eq_true_eq] at meet
          subst meet
          rw [carrier] at carrier'
          cases carrier'
          rfl
      | eq _ => simp [unifiable, allLeft, eqLeft] at meet
  | eq carrier =>
      cases rule' with
      | elim => simp [unifiable, elimLeft, eqLeft] at meet
      | imp =>
          simp only [unifiable, impLeft, eqLeft, Codes.holdsOf, Codes.impOf, decide_true,
            Bool.true_and, Bool.and_true, decide_eq_true_eq] at meet
          exact absurd meet (names.eq_ne carrier).2.2
      | all _ => simp [unifiable, allLeft, eqLeft] at meet
      | eq carrier' =>
          simp only [unifiable, eqLeft, Codes.holdsOf, decide_true, Bool.true_and, Bool.and_true,
            decide_eq_true_eq] at meet
          subst meet
          rw [carrier] at carrier'
          cases carrier'
          rfl

/-- **The equations of the base form a constructor system.** -/
def system (names : Names J K) : System Head where
  schema := Schema J K
  defined := Defined J K
  arity := arity J K
  left := schema_left names
  linear := fun rule index => by rw [schema_multiplicity rule index]
  covered := fun rule index _ => by rw [schema_multiplicity rule index]; decide
  determined := determined_of_disjoint
    (fun rule => by
      obtain ⟨name, -, -, side⟩ := schema_left names rule
      exact ⟨name, _, side⟩)
    (fun rule index _ => by rw [schema_multiplicity rule index]; decide)
    (schema_disjoint names)

/-- The extended base as a definition by constructor patterns. -/
def presentation {base : Rules Head}
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    (names : Names J K) (symmetric : Std.Symm base.headEq) :
    ConstructorPresentation (K.extend base) where
  presentation := SchemaFamily.presentation (Schema J K) (K.extend base)
    (fun {_ _ _} => step_iff J K computes)
  system := system names
  same := fun _ _ => Iff.rfl
  symmetric := symmetric

/-- **Church–Rosser for the base extended by codes.** -/
theorem churchRosser {base : Rules Head}
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    (names : Names J K) (symmetric : Std.Symm base.headEq) : ChurchRosser (K.extend base) :=
  (presentation computes names symmetric).churchRosser

/-! ## Root steps of the extended base -/

theorem schemaStep_inv {schema : SchemaFamily Head} {n : Nat} {l r : Tm Head n}
    (step : SchemaStep schema l r) :
    ∃ (m : Nat) (left right : Tm Head m) (σ : Sub Head m n),
      schema left right ∧ subst σ left = l ∧ subst σ right = r := by
  cases step with
  | instantiate rule σ => exact ⟨_, _, _, σ, rule, rfl, rfl⟩

variable {base : Rules Head}

/-- A root step of the extended base starts at an instance of a left side. -/
theorem root_source
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {l r : Tm Head n} (step : (K.extend base).computation.step l r) :
    ∃ (m : Nat) (left right : Tm Head m) (σ : Sub Head m n),
      Schema J K left right ∧ subst σ left = l :=
  let ⟨m, left, right, σ, rule, same, _⟩ := schemaStep_inv ((step_iff J K computes).mp step)
  ⟨m, left, right, σ, rule, same⟩

theorem no_root_var
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {i : Fin n} {u : Tm Head n} :
    ¬ (K.extend base).computation.step (.var i) u := by
  intro step
  obtain ⟨m, left, right, σ, rule, same⟩ := root_source computes step
  cases rule <;>
    simp [elimLeft, impLeft, allLeft, eqLeft, Codes.holdsOf, Codes.impOf, Presentation.subst] at same

theorem no_root_const
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {c : DeclName} {u : Tm Head n} :
    ¬ (K.extend base).computation.step (.const c) u := by
  intro step
  obtain ⟨m, left, right, σ, rule, same⟩ := root_source computes step
  cases rule <;>
    simp [elimLeft, impLeft, allLeft, eqLeft, Codes.holdsOf, Codes.impOf, Presentation.subst] at same

theorem no_root_var_app
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {i : Fin n} {t u : Tm Head n} :
    ¬ (K.extend base).computation.step (.app (.var i) t) u := by
  intro step
  obtain ⟨m, left, right, σ, rule, same⟩ := root_source computes step
  cases rule <;>
    simp [elimLeft, impLeft, allLeft, eqLeft, Codes.holdsOf, Codes.impOf, Presentation.subst] at same

/-- The decoder does not decode a code headed by a variable. -/
theorem no_root_holds_var_app
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {j : Fin n} {t u : Tm Head n} :
    ¬ (K.extend base).computation.step (K.holdsOf (.app (.var j) t)) u := by
  intro step
  obtain ⟨m, left, right, σ, rule, same⟩ := root_source computes step
  cases rule <;>
    simp [elimLeft, impLeft, allLeft, eqLeft, Codes.holdsOf, Codes.impOf, Presentation.subst] at same

/-- One step from the decoding of a variable-headed code steps inside the
argument. -/
theorem step_holds_var
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {j : Fin n} {t w : Tm Head n}
    (step : Step (K.extend base).headEq (K.holdsOf (.app (.var j) t)) w (K.extend base).computation) :
    ∃ t', w = K.holdsOf (.app (.var j) t') ∧
      Step (K.extend base).headEq t t' (K.extend base).computation := by
  cases step with
  | root rootStep => exact absurd rootStep (no_root_holds_var_app computes)
  | congAppFun inner =>
      cases inner with
      | root rootStep => exact absurd rootStep (no_root_const computes)
  | congAppArg inner =>
      cases inner with
      | root rootStep => exact absurd rootStep (no_root_var_app computes)
      | congAppFun inner' =>
          cases inner' with
          | root rootStep => exact absurd rootStep (no_root_var computes)
      | congAppArg inner' => exact ⟨_, rfl, inner'⟩

theorem stepStar_holds_var
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    {n : Nat} {j : Fin n} {t w : Tm Head n}
    (steps : StepStar (K.extend base) (K.holdsOf (.app (.var j) t)) w) :
    ∃ t', w = K.holdsOf (.app (.var j) t') ∧ StepStar (K.extend base) t t' := by
  induction steps with
  | refl => exact ⟨t, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨t', rfl, steps'⟩ := ih
      obtain ⟨t'', rfl, step'⟩ := step_holds_var computes step
      exact ⟨t'', rfl, .tail steps' step'⟩

/-- **Decodings of codes headed by the same variable are convertible only when
the variable's arguments are.** -/
theorem conv_of_conv_holds_var
    (computes : ∀ {n : Nat} {l r : Tm Head n}, base.computation.step l r ↔ JStep J l r)
    (names : Names J K) (symmetric : Std.Symm base.headEq) {n : Nat} {j : Fin n} {t u : Tm Head n}
    (conversion : Conv (K.extend base).headEq (K.holdsOf (.app (.var j) t))
      (K.holdsOf (.app (.var j) u)) (K.extend base).computation) :
    Conv (K.extend base).headEq t u (K.extend base).computation := by
  obtain ⟨w, first, second⟩ := (presentation computes names symmetric).churchRosser conversion
  obtain ⟨t', rfl, tSteps⟩ := stepStar_holds_var computes first
  obtain ⟨u', same, uSteps⟩ := stepStar_holds_var computes second
  simp only [Codes.holdsOf, Tm.app.injEq, true_and] at same
  subst same
  exact .trans _ _ _ (ConversionCoherence.stepStar_implies_conv tSteps)
    (.symm _ _ (ConversionCoherence.stepStar_implies_conv uSteps))

/-! ## Heads that reduction keeps -/

/-- The variable at the head of an application spine. -/
def varHead {n : Nat} : Tm Head n → Option (Fin n)
  | .var i => some i
  | .app f _ => varHead f
  | _ => none

theorem spineHead_of_varHead {n : Nat} {t : Tm Head n} {i : Fin n} (h : varHead t = some i) :
    spineHead t = none := by
  induction t with
  | var => rfl
  | app f a ihf =>
      simp only [varHead] at h
      simp only [spineHead, ihf h, Option.map_none]
  | _ => simp [varHead] at h

/-- A root step of a presented package starts at a spine headed by a defined
constant. -/
theorem root_defined {rules : Rules Head} (E : ConstructorPresentation rules) {n : Nat}
    {source target : Tm Head n} (step : rules.computation.step source target) :
    ∃ name, E.system.defined name ∧ spineHead source = some (name, E.system.arity name) := by
  obtain ⟨_, left, right, σ, rule, shape, _⟩ := E.presentation.cover step
  obtain ⟨name, defined, -, side⟩ := E.system.left ((E.same left right).mp rule)
  exact ⟨name, defined, shape ▸ ConstructorSystem.spineHead_subst_leftSide side σ⟩

/-- **One step keeps a spine headed by a constant that heads no equation.** -/
theorem step_spineHead {rules : Rules Head} (E : ConstructorPresentation rules) {c : DeclName}
    (hc : ¬ E.system.defined c) {n : Nat} {t u : Tm Head n}
    (step : Step rules.headEq t u rules.computation) :
    ∀ {k : Nat}, spineHead t = some (c, k) → spineHead u = some (c, k) := by
  induction step with
  | root rootStep =>
      intro k h
      obtain ⟨name, defined, shape⟩ := root_defined E rootStep
      rw [h] at shape
      cases shape
      exact absurd defined hc
  | @congAppFun _ g g' a _ ih =>
      intro k h
      simp only [spineHead] at h ⊢
      cases hg : spineHead g with
      | none => rw [hg] at h; cases h
      | some found =>
          rw [hg] at h
          obtain ⟨name, k'⟩ := found
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [ih hg]
          rfl
  | congAppArg _ _ =>
      intro k h
      simpa only [spineHead] using h
  | _ => intro k h; simp [spineHead] at h

theorem stepStar_spineHead {rules : Rules Head} (E : ConstructorPresentation rules)
    {c : DeclName} (hc : ¬ E.system.defined c) {n : Nat} {t u : Tm Head n}
    (steps : StepStar rules t u) {k : Nat} (h : spineHead t = some (c, k)) :
    spineHead u = some (c, k) := by
  induction steps with
  | refl => exact h
  | tail _ step ih => exact step_spineHead E hc step ih

/-- **One step keeps a spine headed by a variable.** -/
theorem step_varHead {rules : Rules Head} (E : ConstructorPresentation rules) {n : Nat}
    {t u : Tm Head n} (step : Step rules.headEq t u rules.computation) :
    ∀ {i : Fin n}, varHead t = some i → varHead u = some i := by
  induction step with
  | root rootStep =>
      intro i h
      obtain ⟨name, -, shape⟩ := root_defined E rootStep
      rw [spineHead_of_varHead h] at shape
      cases shape
  | congAppFun _ ih =>
      intro i h
      exact ih h
  | congAppArg _ _ =>
      intro i h
      exact h
  | _ => intro i h; simp [varHead] at h

theorem stepStar_varHead {rules : Rules Head} (E : ConstructorPresentation rules) {n : Nat}
    {t u : Tm Head n} (steps : StepStar rules t u) {i : Fin n} (h : varHead t = some i) :
    varHead u = some i := by
  induction steps with
  | refl => exact h
  | tail _ step ih => exact step_varHead E step ih

/-- **A spine headed by a constant that heads no equation is not convertible to
a spine headed by a variable.** -/
theorem not_conv_spineHead_varHead {rules : Rules Head} (E : ConstructorPresentation rules)
    {c : DeclName} (hc : ¬ E.system.defined c) {n : Nat} {t u : Tm Head n} {k : Nat}
    {i : Fin n} (h₁ : spineHead t = some (c, k)) (h₂ : varHead u = some i) :
    ¬ Conv rules.headEq t u rules.computation := by
  intro conversion
  obtain ⟨w, tw, uw⟩ := E.churchRosser conversion
  have e₁ := stepStar_spineHead E hc tw h₁
  rw [spineHead_of_varHead (stepStar_varHead E uw h₂)] at e₁
  cases e₁

/-- **Two spines headed by distinct constants that head no equation are not
convertible.** -/
theorem not_conv_spineHead_spineHead {rules : Rules Head} (E : ConstructorPresentation rules)
    {c c' : DeclName} (hc : ¬ E.system.defined c) (hc' : ¬ E.system.defined c') (ne : c ≠ c')
    {n : Nat} {t u : Tm Head n} {k k' : Nat} (h₁ : spineHead t = some (c, k))
    (h₂ : spineHead u = some (c', k')) : ¬ Conv rules.headEq t u rules.computation := by
  intro conversion
  obtain ⟨w, tw, uw⟩ := E.churchRosser conversion
  have e₁ := stepStar_spineHead E hc tw h₁
  rw [stepStar_spineHead E hc' uw h₂] at e₁
  cases e₁
  exact ne rfl

end Confluence

/-! ## The separation, for the accessibility package -/

namespace Signature

open Confluence

variable {S : Signature Head}

theorem spineHead_recSpine {n : Nat} (P R F a q : Tm Head n) :
    spineHead (S.recSpine P R F a q) = some (S.recursor, 5) := rfl

theorem varHead_unfolding {n : Nat} (P R a q : Tm Head n) (i : Fin n) :
    varHead (S.unfolding P R (.var i) a q) = some i := rfl

/-- **Conversion does not identify the recursor with its unfolding.** In a
presentation of the accessibility package by constructor patterns in which the
recursor heads no equation, `rec P R F a q` and `F a (λ y r. rec P R F y (inv R
a q y r))` are not convertible when the step function `F` is a variable. -/
theorem separation (E : ConstructorPresentation S.rules) (hrec : ¬ E.system.defined S.recursor)
    {n : Nat} (P R a q : Tm Head n) (i : Fin n) :
    ¬ Conv S.rules.headEq (S.recSpine P R (.var i) a q) (S.unfolding P R (.var i) a q)
      S.rules.computation :=
  not_conv_spineHead_varHead E hrec (spineHead_recSpine P R (.var i) a q) (varHead_unfolding P R a q i)

/-- **Separation at a step function whose unfolding computes to a constant.**
When the unfolding reduces to a spine headed by a constant other than the
recursor that heads no equation, the recursor is not convertible to its
unfolding. -/
theorem separation_of_reduct (E : ConstructorPresentation S.rules)
    (hrec : ¬ E.system.defined S.recursor) {d : DeclName} (hd : ¬ E.system.defined d)
    (ne : S.recursor ≠ d) {n : Nat} {P R F a q u : Tm Head n} {k : Nat}
    (steps : StepStar S.rules (S.unfolding P R F a q) u) (head : spineHead u = some (d, k)) :
    ¬ Conv S.rules.headEq (S.recSpine P R F a q) (S.unfolding P R F a q) S.rules.computation := by
  intro conversion
  exact not_conv_spineHead_spineHead E hrec hd ne (spineHead_recSpine P R F a q) head
    (.trans _ _ _ conversion (ConversionCoherence.stepStar_implies_conv steps))

/-- The accessibility package over a base computing by linear identity
elimination, presented by constructor patterns. -/
def presentation {J : DeclName}
    (computes : ∀ {n : Nat} {l r : Tm Head n}, S.base.computation.step l r ↔ JStep J l r)
    (names : Names J S.codes) (symmetric : Std.Symm S.base.headEq) :
    ConstructorPresentation S.rules :=
  Confluence.presentation (base := S.accBase) computes names symmetric

/-- **Church–Rosser for the accessibility package** over such a base. -/
theorem churchRosser {J : DeclName}
    (computes : ∀ {n : Nat} {l r : Tm Head n}, S.base.computation.step l r ↔ JStep J l r)
    (names : Names J S.codes) (symmetric : Std.Symm S.base.headEq) : ChurchRosser S.rules :=
  (S.presentation computes names symmetric).churchRosser

/-- **Conversion does not take a statement about the recursor to the same
statement about its unfolding.** For a variable predicate `Q`,
`holds (Q (rec P R F a q))` and `holds (Q (F a …))` are not convertible: the
conversion rule cannot replace the propositional unfolding in the transport
control. -/
theorem holds_separation {J : DeclName}
    (computes : ∀ {n : Nat} {l r : Tm Head n}, S.base.computation.step l r ↔ JStep J l r)
    (names : Names J S.codes) (symmetric : Std.Symm S.base.headEq)
    (hrec : S.recursor ≠ J ∧ S.recursor ≠ S.codes.holds)
    {n : Nat} (P R a q : Tm Head n) (i j : Fin n) :
    ¬ Conv S.rules.headEq (S.codes.holdsOf (.app (.var j) (S.recSpine P R (.var i) a q)))
      (S.codes.holdsOf (.app (.var j) (S.unfolding P R (.var i) a q))) S.rules.computation := by
  intro conversion
  exact S.separation (S.presentation computes names symmetric) (not_defined_of_ne hrec.1 hrec.2)
    P R a q i (conv_of_conv_holds_var (base := S.accBase) computes names symmetric conversion)

end Signature

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
