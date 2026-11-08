import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NeutralHeads

/-!
# Rigid-rigid equations: decomposition and certified refutation

A code has a **rigid shape** when its head cannot be changed by any substitution: a type
former (dependent function, dependent pair, identity), a universe or ground head, or an
elimination spine headed by a constant. In the rigid-constant profile such a code is a weak-head
form of a type (`isTypeForm_of_shape`), and substitution keeps its shape (`shape_subst`).

Two rigid shapes **clash** when they have different formers, different heads up to the
package's head equality, or different constants. Where the algorithmic equality is complete, a
clash of the endpoint types refutes their type equality, and a clash of the endpoint terms refutes
their equality at any type; for types compared as terms of a universe the former clashes count
as well. Every solution of an equation instantiates its endpoints, and instantiation keeps their
shapes, so a clash is a **certified refutation**: the equation has no solution at any later
context (`not_solves_of_clashes`), and neither has any store containing it
(`not_solvable_of_storeClashes`).

Equations between rigid type formers with the same head **decompose** into the equations of
their components, in both directions (`typeEq_pi_iff`, `typeEq_sigma_iff`, `typeEq_id_iff`).
The codomain equation of a function or pair type is stated over the left domain; it is
heterogeneous until the domain equation holds.

The checks are executable (`equationClashes`, `storeClashes`). They are conservative: a code
without a rigid shape, such as a metavariable application or an abstraction, never clashes.
Abstractions and pairs are not compared with neutral terms, since eta equates them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigid

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head : Type}

/-! ## Rigid shapes -/

/-- A head that no substitution can change. -/
inductive Shape (Head : Type) where
  | pi
  | sigma
  | id
  | head (h : Head)
  | const (name : DeclName)
  deriving DecidableEq

/-- The former of a type code, if it has one. -/
def former {n : Nat} : Tm Head n → Option (Shape Head)
  | .pi _ _ => some .pi
  | .sigma _ _ => some .sigma
  | .id _ _ _ => some .id
  | .head h => some (.head h)
  | _ => none

/-- The rigid shape of a code: its former, or the constant heading its elimination spine. -/
def shape {n : Nat} (t : Tm Head n) : Option (Shape Head) :=
  match former t with
  | some s => some s
  | none => (spineConst t).map .const

theorem former_eq_none_of_spineConst {n : Nat} {t : Tm Head n} {c : DeclName}
    (head : spineConst t = some c) : former t = none := by
  cases t <;> simp_all [spineConst, former]

theorem former_subst {n m : Nat} (σ : Sub Head n m) {t : Tm Head n} {s : Shape Head}
    (formed : former t = some s) : former (subst σ t) = some s := by
  cases t <;> first | exact formed | simp [former] at formed

theorem shape_subst {n m : Nat} (σ : Sub Head n m) {t : Tm Head n} {s : Shape Head}
    (shaped : shape t = some s) : shape (subst σ t) = some s := by
  unfold shape at shaped ⊢
  cases formed : former t with
  | some _ =>
      rw [formed] at shaped
      rw [former_subst σ formed]
      exact shaped
  | none =>
      rw [formed] at shaped
      cases headed : spineConst t with
      | none => rw [headed] at shaped; simp at shaped
      | some _ =>
          rw [headed] at shaped
          have moved := spineConst_subst σ headed
          rw [former_eq_none_of_spineConst moved, moved]
          exact shaped

/-- A neutral code has no former; its shape is the constant heading it, if any. -/
theorem former_eq_none_of_neutral {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) : former t = none := by
  cases t with
  | pi A B => exact absurd rfl (neutral.not_former.2.1 A B)
  | sigma A B => exact absurd rfl (neutral.not_former.2.2.1 A B)
  | id A a b => exact absurd rfl (neutral.not_former.2.2.2 A a b)
  | head h => exact absurd rfl (neutral.not_former.1 h)
  | _ => rfl

theorem shape_of_neutral {roles : Roles Head} {n : Nat} {t : Tm Head n}
    (neutral : Neutral roles t) : shape t = (spineConst t).map .const := by
  unfold shape
  rw [former_eq_none_of_neutral neutral]

/-! ## Clashes -/

/-- An index of the kind of a shape. -/
def Shape.kind : Shape Head → Nat
  | .pi => 0
  | .sigma => 1
  | .id => 2
  | .head _ => 3
  | .const _ => 4

/-- Two elimination spines headed by different constants. -/
def spineClashes {n : Nat} (t u : Tm Head n) : Bool :=
  match spineConst t, spineConst u with
  | some c, some d => !decide (c = d)
  | _, _ => false

theorem spineClashes_heads {n : Nat} {t u : Tm Head n} (clash : spineClashes t u = true) :
    ∃ c d, c ≠ d ∧ spineConst t = some c ∧ spineConst u = some d := by
  unfold spineClashes at clash
  cases headT : spineConst t with
  | none => rw [headT] at clash; cases clash
  | some c =>
      cases headU : spineConst u with
      | none => rw [headT, headU] at clash; cases clash
      | some d =>
          rw [headT, headU] at clash
          exact ⟨c, d, by simpa using clash, rfl, rfl⟩

theorem spineClashes_subst {n m : Nat} (σ : Sub Head n m) {t u : Tm Head n}
    (clash : spineClashes t u = true) : spineClashes (subst σ t) (subst σ u) = true := by
  obtain ⟨c, d, distinct, headT, headU⟩ := spineClashes_heads clash
  unfold spineClashes
  rw [spineConst_subst σ headT, spineConst_subst σ headU]
  simpa using distinct

/-- An annotation that is a universe head, at which terms are compared as types. -/
def universeAnnotation (R : Rules Head) [∀ head, Decidable (R.isUniverse head)] {n : Nat} :
    Tm Head n → Bool
  | .head u => decide (R.isUniverse u)
  | _ => false

theorem universeAnnotation_spec (R : Rules Head) [∀ head, Decidable (R.isUniverse head)]
    {n : Nat} {A : Tm Head n} (universe_ : universeAnnotation R A = true) :
    ∃ u, A = .head u ∧ R.isUniverse u := by
  cases A <;> simp_all [universeAnnotation]

theorem universeAnnotation_subst (R : Rules Head) [∀ head, Decidable (R.isUniverse head)]
    {n m : Nat} (σ : Sub Head n m) {A : Tm Head n} (universe_ : universeAnnotation R A = true) :
    universeAnnotation R (subst σ A) = true := by
  obtain ⟨u, rfl, _⟩ := universeAnnotation_spec R universe_
  exact universe_

/-! ## The rigid-constant profile -/

section Profile

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)
variable (facts : FormFacts S.R S.roles) (complete : AlgorithmicComplete S.R S.roles)

include rigid in
/-- A code with a rigid shape is a weak-head form of a type in the rigid-constant profile. -/
theorem isTypeForm_of_shape {n : Nat} {t : Tm Head n} {s : Shape Head}
    (shaped : shape t = some s) : IsTypeForm S.roles t := by
  unfold shape at shaped
  cases formed : former t with
  | some _ =>
      cases t with
      | pi A B => exact .inr (.inl ⟨A, B, rfl⟩)
      | sigma A B => exact .inr (.inr (.inl ⟨A, B, rfl⟩))
      | id A a b => exact .inr (.inr (.inr (.inl ⟨A, a, b, rfl⟩)))
      | head h => exact .inl ⟨h, rfl⟩
      | _ => simp [former] at formed
  | none =>
      rw [formed] at shaped
      cases headed : spineConst t with
      | none => rw [headed] at shaped; simp at shaped
      | some c =>
          exact .inr (.inr (.inr (.inr (.inl (Neutral.of_spineConst (rigid c) t headed)))))


include rigid complete in
/-- **Spines with different rigid heads are equal at no type.** -/
theorem not_equal_of_spineClashes {n : Nat} {Γ : Ctx Head n} {t u C : Tm Head n}
    (formed : CtxFormed S.R Γ) (clash : spineClashes t u = true) : ¬ Equal S.R Γ t u C := by
  obtain ⟨c, d, distinct, headT, headU⟩ := spineClashes_heads clash
  exact not_equal_of_rigid_heads complete formed distinct headT headU (rigid c) (rigid d)

/-! ### Decomposition of rigid type formers -/


include facts in
/-- **Dependent function types decompose**: their domains are equal, and their codomains are
equal over the left domain. -/
theorem typeEq_pi_iff {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (formed : CtxFormed S.R Γ) :
    TypeEq S.R Γ (.pi A B) (.pi A' B') ↔ TypeEq S.R Γ A A' ∧ TypeEq S.R (.snoc Γ A) B B' := by
  constructor
  · intro equal
    exact TypeEq.pi_injective facts equal formed
  · rintro ⟨⟨u, hu, domains⟩, ⟨v, hv, codomains⟩⟩
    obtain ⟨w, joined⟩ := S.levels.join_exists hu hv
    exact ⟨w, (S.levels.join_level joined).1, .piCong domains hu codomains hv joined⟩

include facts in
/-- **Dependent pair types decompose** in the same way. -/
theorem typeEq_sigma_iff {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (formed : CtxFormed S.R Γ) :
    TypeEq S.R Γ (.sigma A B) (.sigma A' B') ↔ TypeEq S.R Γ A A' ∧ TypeEq S.R (.snoc Γ A) B B' := by
  constructor
  · intro equal
    exact TypeEq.sigma_injective facts equal formed
  · rintro ⟨⟨u, hu, domains⟩, ⟨v, hv, codomains⟩⟩
    obtain ⟨w, joined⟩ := S.levels.join_exists hu hv
    exact ⟨w, (S.levels.join_level joined).1, .sigmaCong domains hu codomains hv joined⟩

include facts in
/-- **Identity types decompose** into their carrier and their two endpoints, the endpoints at
the left carrier. -/
theorem typeEq_id_iff {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n}
    (formed : CtxFormed S.R Γ) :
    TypeEq S.R Γ (.id A a b) (.id A' a' b') ↔
      TypeEq S.R Γ A A' ∧ Equal S.R Γ a a' A ∧ Equal S.R Γ b b' A := by
  constructor
  · intro equal
    exact TypeEq.id_injective facts equal formed
  · rintro ⟨⟨u, hu, carriers⟩, lefts, rights⟩
    exact ⟨u, hu, .idCong carriers hu lefts rights⟩

include facts in
/-- At every solution, the type component of an equation between dependent function types is
the domain equation together with the codomain equation over the left domain. -/
theorem solves_pi_iff {Γ Δ : Context S.R} (σ : Δ ⟶ Γ) {A A' : Tm Head Γ.arity}
    {B B' : Tm Head (Γ.arity + 1)} (equation : Equation (TotalTerm Γ))
    (left : equation.1.1.code = .pi A B) (right : equation.2.1.code = .pi A' B') :
    (frames S.levels).Solves σ equation ↔
      (TypeEq S.R Δ.raw (subst σ.substitution A) (subst σ.substitution A') ∧
        TypeEq S.R (.snoc Δ.raw (subst σ.substitution A)) (subst (liftSub σ.substitution) B)
          (subst (liftSub σ.substitution) B')) ∧
      Equal S.R Δ.raw (subst σ.substitution equation.1.2.code)
        (subst σ.substitution equation.2.2.code) (subst σ.substitution equation.1.1.code) := by
  refine (equivalent_iff S.levels _ _).trans (and_congr_left fun _ => ?_)
  change TypeEq S.R Δ.raw (subst σ.substitution equation.1.1.code)
    (subst σ.substitution equation.2.1.code) ↔ _
  rw [left, right]
  exact typeEq_pi_iff facts Δ.formed

end Profile

/-! ## Clashes -/

section Clashes

variable [DecidableEq Head]


/-- Two rigid shapes that no equality of types can relate. -/
def clashes (R : Rules Head) [DecidableRel R.headEq] : Shape Head → Shape Head → Bool
  | .head h, .head h' => !(decide (h = h') || decide (R.headEq h h'))
  | .const c, .const d => !decide (c = d)
  | s, s' => !decide (s.kind = s'.kind)

theorem clashes_self (R : Rules Head) [DecidableRel R.headEq] (s : Shape Head) :
    clashes R s s = false := by
  cases s with
  | head _ => simp [clashes]
  | const _ => simp [clashes]
  | _ => rfl

theorem clashes_heads (R : Rules Head) [DecidableRel R.headEq] {h h' : Head}
    (same : HeadSame R h h') : clashes R (.head h) (.head h') = false := by
  rcases same with same | same <;> simp [clashes, same]

/-- The shapes of two codes clash. Codes without rigid shapes never clash. -/
def shapeClashes (R : Rules Head) [DecidableRel R.headEq] {n : Nat} (A B : Tm Head n) : Bool :=
  match shape A, shape B with
  | some s, some s' => clashes R s s'
  | _, _ => false

theorem shapeClashes_subst (R : Rules Head) [DecidableRel R.headEq] {n m : Nat}
    (σ : Sub Head n m) {A B : Tm Head n} (clash : shapeClashes R A B = true) :
    shapeClashes R (subst σ A) (subst σ B) = true := by
  unfold shapeClashes at clash ⊢
  cases shapedA : shape A with
  | none => rw [shapedA] at clash; cases clash
  | some s =>
      cases shapedB : shape B with
      | none => rw [shapedA, shapedB] at clash; cases clash
      | some s' =>
          rw [shapedA, shapedB] at clash
          rw [shape_subst σ shapedA, shape_subst σ shapedB]
          exact clash

theorem shapeClashes_spec (R : Rules Head) [DecidableRel R.headEq] {n : Nat} {A B : Tm Head n}
    (clash : shapeClashes R A B = true) :
    ∃ s s', shape A = some s ∧ shape B = some s' ∧ clashes R s s' = true := by
  unfold shapeClashes at clash
  cases shapedA : shape A with
  | none => rw [shapedA] at clash; cases clash
  | some s =>
      cases shapedB : shape B with
      | none => rw [shapedA, shapedB] at clash; cases clash
      | some s' =>
          rw [shapedA, shapedB] at clash
          exact ⟨s, s', rfl, rfl, clash⟩

/-! ## Clashes refute -/

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (rigid : ∀ name, S.roles name = .rigid)
variable [DecidableRel S.R.headEq]
variable (facts : FormFacts S.R S.roles) (complete : AlgorithmicComplete S.R S.roles)

include rigid facts complete in
/-- **Equal types have compatible shapes.** -/
theorem typeEq_compatible {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (equal : TypeEq S.R Γ A B) {s s' : Shape Head}
    (shapedA : shape A = some s) (shapedB : shape B = some s') : clashes S.R s s' = false := by
  have forms := facts.forms equal formed (isTypeForm_of_shape rigid shapedA)
    (isTypeForm_of_shape rigid shapedB)
  rcases forms with ⟨_, _, rfl, rfl, same⟩ | ⟨_, _, _, _, rfl, rfl, _⟩ |
    ⟨_, _, _, _, rfl, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, rfl, _⟩ | ⟨T, _, role, rfl, rfl⟩ |
    ⟨neutralA, neutralB⟩
  · simp only [shape, former, Option.some.injEq] at shapedA shapedB
    subst shapedA shapedB
    exact clashes_heads S.R same
  · simp only [shape, former, Option.some.injEq] at shapedA shapedB
    subst shapedA shapedB
    rfl
  · simp only [shape, former, Option.some.injEq] at shapedA shapedB
    subst shapedA shapedB
    rfl
  · simp only [shape, former, Option.some.injEq] at shapedA shapedB
    subst shapedA shapedB
    rfl
  · rw [rigid T] at role
    cases role
  · rw [shape_of_neutral neutralA] at shapedA
    rw [shape_of_neutral neutralB] at shapedB
    cases headA : spineConst A with
    | none => rw [headA] at shapedA; simp at shapedA
    | some c =>
        cases headB : spineConst B with
        | none => rw [headB] at shapedB; simp at shapedB
        | some d =>
            rw [headA] at shapedA
            rw [headB] at shapedB
            simp at shapedA shapedB
            subst shapedA shapedB
            obtain ⟨_, _, e⟩ := equal
            have same := Algorithmic.rigidHeadsAgree (complete formed e) c d headA headB
              (rigid c) (rigid d)
            subst same
            exact clashes_self S.R _

include rigid facts complete in
/-- **Clashing types are equal in no context.** -/
theorem not_typeEq_of_shapeClashes {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (formed : CtxFormed S.R Γ) (clash : shapeClashes S.R A B = true) : ¬ TypeEq S.R Γ A B := by
  intro equal
  obtain ⟨_, _, shapedA, shapedB, clashing⟩ := shapeClashes_spec S.R clash
  rw [typeEq_compatible rigid facts complete formed equal shapedA shapedB] at clashing
  cases clashing

variable [∀ head, Decidable (S.R.isUniverse head)]

/-- **A certified clash of an equation**: its endpoint types clash, its endpoint terms are
spines of different constants, or its terms are types of a universe whose shapes clash. -/
def equationClashes {Γ : Context S.R} (equation : Equation (TotalTerm Γ)) : Bool :=
  shapeClashes S.R equation.1.1.code equation.2.1.code ||
    spineClashes equation.1.2.code equation.2.2.code ||
      (universeAnnotation S.R equation.1.1.code &&
        shapeClashes S.R equation.1.2.code equation.2.2.code)

include rigid facts complete in
/-- **A clash is a refutation**: the equation has no solution in any later context. -/
theorem not_solves_of_clashes {Γ Δ : Context S.R} {equation : Equation (TotalTerm Γ)}
    (clash : equationClashes equation = true) (σ : Δ ⟶ Γ) :
    ¬ (frames S.levels).Solves σ equation := by
  intro solved
  obtain ⟨types, terms⟩ := (equivalent_iff S.levels _ _).mp solved
  unfold equationClashes at clash
  simp only [Bool.or_eq_true, Bool.and_eq_true] at clash
  rcases clash with (typeClash | spineClash) | ⟨universe_, termClash⟩
  · exact not_typeEq_of_shapeClashes rigid facts complete Δ.formed
      (shapeClashes_subst S.R σ.substitution typeClash) types
  · exact not_equal_of_spineClashes rigid complete Δ.formed
      (spineClashes_subst σ.substitution spineClash) terms
  · obtain ⟨u, same, isUniverse⟩ := universeAnnotation_spec S.R
      (universeAnnotation_subst S.R σ.substitution universe_)
    have atUniverse : Equal S.R Δ.raw (subst σ.substitution equation.1.2.code)
        (subst σ.substitution equation.2.2.code) (.head u) := by
      have moved := terms
      change Equal S.R Δ.raw _ _ (subst σ.substitution equation.1.1.code) at moved
      rw [same] at moved
      exact moved
    exact not_typeEq_of_shapeClashes rigid facts complete Δ.formed
      (shapeClashes_subst S.R σ.substitution termClash) ⟨u, isUniverse, atUniverse⟩

/-- Some equation of the store clashes. -/
def storeClashes {Γ : Context S.R} (store : EquationStore (TotalTerm Γ)) : Bool :=
  store.any equationClashes

include rigid facts complete in
/-- **A store with a clashing equation has no solution in any later context.** -/
theorem not_solvable_of_storeClashes {Γ : Context S.R} {store : EquationStore (TotalTerm Γ)}
    (clash : storeClashes store = true) : ¬ (frames S.levels).Solvable store := by
  rintro ⟨Δ, σ, solved⟩
  obtain ⟨equation, member, clashing⟩ := List.any_eq_true.mp clash
  exact not_solves_of_clashes rigid facts complete clashing σ (solved equation member)


end Clashes

end ContextualDependentRigid
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
