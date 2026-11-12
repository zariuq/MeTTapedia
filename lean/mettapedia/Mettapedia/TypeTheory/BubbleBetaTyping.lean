import Mettapedia.TypeTheory.BubbleSubjectReduction

/-!
# The β step: when it keeps types, and why computation has to be conversion under dependency

The comparison core has abstraction and application and no built-in computation. This module
reads the β step as one more rule and asks what typing needs from it.

* `Beta` is the rule. It is stable under substitution and under shifting
  (`beta_substStable`, `beta_shiftStable`): the two facts are the commutation laws
  `KnowledgeSubstitution.substAt_substAt` and `KnowledgeSubstitution.shiftAt_substAt`.
* `beta_keeps_type`: in a bubble whose conversion is coherent and whose convertible products have
  convertible domains, the contractum of a β redex has every type of the redex. The proof is the
  substitution property of the typing judgment.
* `withBeta_preservesTypes`, `withBeta_subject_reduction`: a bubble that declares β together with
  rules that keep types has subject reduction. Coherence and convertible domains of the joint
  conversion remain hypotheses of these two statements.

So confluence of the rules enters typing at one place only: it gives the injectivity of products
(`BubbleTypingAlgorithmic.piCodomainInjective_of_confluent`), which uniqueness of types and the
β step need.

## Controls

* `Controls.arith_beta_keeps_type`: in the arithmetic bubble every hypothesis holds, and a β step
  at the root keeps the type.
* `Controls.computation_outside_conversion_breaks_types`: in the arithmetic bubble β is a
  computation and not a conversion. With `g : Π (n : nat). Vec n`, the term `g ((λ m. m) 0)` is
  typed at `Vec ((λ m. m) 0)`, it makes a β step inside the argument to `g 0`, and `g 0` is not
  typed at `Vec ((λ m. m) 0)`. A computation that types depend on has to be a conversion of the
  bubble, or the positions that types depend on have to hold terms that do not compute.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleBetaTyping

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.BubbleSubjectReduction
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The β rule: an applied abstraction is its body at the argument. -/
inductive Beta : Expr Base Const → Expr Base Const → Prop where
  | contract (A b a : Expr Base Const) : Beta (Expr.app (Expr.lam A b) a) (substAt 0 a b)

/-- β is stable under substitution: substitutions commute. -/
theorem beta_substStable :
    SubstitutionStable (Beta : Expr Base Const → Expr Base Const → Prop) := by
  intro left right rule depth replacement
  cases rule with
  | contract A b a =>
      have key : substAt depth replacement (substAt 0 a b) =
          substAt 0 (substAt depth replacement a) (substAt (depth + 1) replacement b) :=
        substAt_substAt replacement a b depth 0
      show Beta
        (Expr.app (Expr.lam (substAt depth replacement A) (substAt (depth + 1) replacement b))
          (substAt depth replacement a))
        (substAt depth replacement (substAt 0 a b))
      rw [key]
      exact Beta.contract _ _ _

/-- β is stable under shifting: a shift passes a substitution. -/
theorem beta_shiftStable : ShiftStable (Beta : Expr Base Const → Expr Base Const → Prop) := by
  intro left right rule cutoff
  cases rule with
  | contract A b a =>
      have key : shiftAt cutoff (substAt 0 a b) =
          substAt 0 (shiftAt cutoff a) (shiftAt (cutoff + 1) b) :=
        shiftAt_substAt a b cutoff 0
      show Beta
        (Expr.app (Expr.lam (shiftAt cutoff A) (shiftAt (cutoff + 1) b)) (shiftAt cutoff a))
        (shiftAt cutoff (substAt 0 a b))
      rw [key]
      exact Beta.contract _ _ _

/-- A typed abstraction has a typed domain and a typed body, and its product moves to the type. -/
theorem typed_lam_inv {moves : Expr Base Const → Expr Base Const → Prop}
    (coherent : Coherent moves) {Γ : List (Expr Base Const)} {A b T : Expr Base Const}
    (typed : Typed moves Γ (Expr.lam A b) T) :
    ∃ B, Typed moves Γ A univ ∧ Typed moves (A :: Γ) b B ∧ moves (Expr.pi A B) T := by
  obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed
  cases synth with
  | lam synthA atA synthb => exact ⟨_, .move synthA.typed atA, synthb.typed, moved⟩

/-- **The substitution property of typing in a bubble**, for the newest variable. -/
theorem hasTypeInside_subst {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    {Γ : List (Expr Base Const)} {s C e A : Expr Base Const}
    (typedS : HasTypeInside rules Γ s C) (typed : HasTypeInside rules (C :: Γ) e A) :
    HasTypeInside rules Γ (substAt 0 s e) (substAt 0 s A) :=
  typedKnowing_subst_solution substStable shiftStable typedS (typedKnowing_of_inside typed [])
    [] rfl (fun _ member => absurd member List.not_mem_nil)

/-- Convertible products have convertible domains. -/
def PiDomainInjective (rules : Expr Base Const → Expr Base Const → Prop) : Prop :=
  ∀ A B A' B' : Expr Base Const, Convertible rules (Expr.pi A B) (Expr.pi A' B') →
    Convertible rules A A'

/-- **The contractum of a β redex has every type of the redex**, in a bubble whose conversion is
coherent and whose convertible products have convertible domains. -/
theorem beta_keeps_type {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    (coherent : Coherent (Convertible rules)) (domains : PiDomainInjective rules)
    {Γ : List (Expr Base Const)} {A b a T : Expr Base Const}
    (typed : HasTypeInside rules Γ (Expr.app (Expr.lam A b) a) T) :
    HasTypeInside rules Γ (substAt 0 a b) T := by
  obtain ⟨A₁, B₁, typedF, typedA, atT⟩ := typed_app_inv coherent typed
  obtain ⟨B₀, _, typedB, atF⟩ := typed_lam_inv coherent typedF
  have domain : Convertible rules A₁ A := Relation.EqvGen.symm _ _ (domains _ _ _ _ atF)
  have codomain : Convertible rules B₀ B₁ := coherent.piCodomain _ _ _ _ atF
  have contracted :=
    hasTypeInside_subst substStable shiftStable (Typed.move typedA domain) typedB
  exact Typed.move contracted
    (Relation.EqvGen.trans _ _ _ (convertible_substAt substStable codomain 0 a) atT)

/-- Declared rules together with β. -/
def withBeta (user : Expr Base Const → Expr Base Const → Prop) :
    Expr Base Const → Expr Base Const → Prop :=
  fun left right => Beta left right ∨ user left right

theorem withBeta_substStable {user : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable user) : SubstitutionStable (withBeta user) := by
  intro left right rule depth replacement
  rcases rule with contracted | declared
  · exact Or.inl (beta_substStable _ _ contracted depth replacement)
  · exact Or.inr (stable _ _ declared depth replacement)

theorem withBeta_shiftStable {user : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable user) : ShiftStable (withBeta user) := by
  intro left right rule cutoff
  rcases rule with contracted | declared
  · exact Or.inl (beta_shiftStable _ _ contracted cutoff)
  · exact Or.inr (stable _ _ declared cutoff)

/-- **β together with rules that keep types keeps types.** Coherence of the joint conversion and
convertible domains of its convertible products are hypotheses. -/
theorem withBeta_preservesTypes {user : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable user) (shiftStable : ShiftStable user)
    (coherent : Coherent (Convertible (withBeta user)))
    (domains : PiDomainInjective (withBeta user))
    (declared : ∀ (Γ : List (Expr Base Const)) (left right A : Expr Base Const),
      user left right → HasTypeInside (withBeta user) Γ left A →
        HasTypeInside (withBeta user) Γ right A) :
    PreservesTypes (withBeta user) := by
  intro Γ left right T rule typed
  rcases rule with contracted | byUser
  · cases contracted with
    | contract A b a =>
        exact beta_keeps_type (withBeta_substStable substStable)
          (withBeta_shiftStable shiftStable) coherent domains typed
  · exact declared Γ left right T byUser typed

/-- **Subject reduction with β in the bubble**, under the hypotheses of
`withBeta_preservesTypes`. -/
theorem withBeta_subject_reduction {user : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable user) (shiftStable : ShiftStable user)
    (coherent : Coherent (Convertible (withBeta user)))
    (domains : PiDomainInjective (withBeta user))
    (declared : ∀ (Γ : List (Expr Base Const)) (left right A : Expr Base Const),
      user left right → HasTypeInside (withBeta user) Γ left A →
        HasTypeInside (withBeta user) Γ right A)
    {Γ : List (Expr Base Const)} {e e' A : Expr Base Const}
    (typed : HasTypeInside (withBeta user) Γ e A)
    (reduced : Relation.ReflTransGen (Rewrite (withBeta user)) e e') :
    HasTypeInside (withBeta user) Γ e' A :=
  subject_reduction_star (withBeta_shiftStable shiftStable)
    (withBeta_preservesTypes substStable shiftStable coherent domains declared) typed reduced

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic.Controls
open Mettapedia.TypeTheory.BubbleSubjectReduction.Controls
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls

/-- **In the arithmetic bubble a β step at the root keeps the type.** -/
theorem arith_beta_keeps_type {Γ : List AExpr} {A b a T : AExpr}
    (typed : HasTypeInside Rule Γ (Expr.app (Expr.lam A b) a) T) :
    HasTypeInside Rule Γ (substAt 0 a b) T :=
  beta_keeps_type rule_stable rule_shiftStable coherentRule
    (fun _ _ _ _ converted => arith_piDomain converted) typed

/-- The identity on numbers applied to zero: `(λ (m : nat). m) 0`. -/
def identityAtZero : AExpr := Expr.app (Expr.lam natType (bvar 0)) zeroE

/-- The context `g : Π (n : nat). Vec n`. -/
def familyContext : List AExpr := [Expr.pi natType (vec (bvar 0))]

theorem identityAtZero_typed : HasTypeInside Rule familyContext identityAtZero natType :=
  Typed.app (A := natType) (B := natType)
    (Typed.lam (Typed.base ()) (Typed.var (Γ := natType :: familyContext) (i := 0) rfl))
    (Typed.const _ ArithConst.zero)

/-- The redex contracts to zero and keeps the type of numbers. -/
theorem identityAtZero_contracts : HasTypeInside Rule familyContext zeroE natType :=
  arith_beta_keeps_type identityAtZero_typed

/-- `g ((λ m. m) 0)` is typed at `Vec ((λ m. m) 0)`. -/
theorem applied_before :
    HasTypeInside Rule familyContext (Expr.app (bvar 0) identityAtZero) (vec identityAtZero) :=
  Typed.app (A := natType) (B := vec (bvar 0)) (Typed.var (Γ := familyContext) (i := 0) rfl)
    identityAtZero_typed

/-- `g 0` is typed at `Vec 0`. -/
theorem applied_after :
    HasTypeInside Rule familyContext (Expr.app (bvar 0) zeroE) (vec zeroE) :=
  Typed.app (A := natType) (B := vec (bvar 0)) (Typed.var (Γ := familyContext) (i := 0) rfl)
    (Typed.const _ ArithConst.zero)

/-- **A computation that is not a conversion breaks types under dependency.** In the arithmetic
bubble, `g ((λ m. m) 0)` is typed at `Vec ((λ m. m) 0)` and makes a β step inside the argument to
`g 0`, which is not typed at `Vec ((λ m. m) 0)`. -/
theorem computation_outside_conversion_breaks_types :
    HasTypeInside Rule familyContext (Expr.app (bvar 0) identityAtZero) (vec identityAtZero) ∧
      Rewrite Beta (Expr.app (bvar 0) identityAtZero) (Expr.app (bvar 0) zeroE) ∧
      ¬ HasTypeInside Rule familyContext (Expr.app (bvar 0) zeroE) (vec identityAtZero) := by
  refine ⟨applied_before,
    Rewrite.appArgument (Rewrite.root (Beta.contract natType (bvar 0) zeroE)), ?_⟩
  intro typed
  have same : Expr.app (Expr.tyFam ()) zeroE = Expr.app (Expr.tyFam ()) identityAtZero :=
    arith_normal_type_unique false applied_after typed
  simp [identityAtZero, zeroE] at same

end Controls

/-! ## Axiom audit -/

#print axioms beta_substStable
#print axioms beta_shiftStable
#print axioms hasTypeInside_subst
#print axioms beta_keeps_type
#print axioms withBeta_preservesTypes
#print axioms withBeta_subject_reduction
#print axioms Controls.arith_beta_keeps_type
#print axioms Controls.identityAtZero_contracts
#print axioms Controls.computation_outside_conversion_breaks_types

end Mettapedia.TypeTheory.BubbleBetaTyping
