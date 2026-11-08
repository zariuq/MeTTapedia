import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRigidPairs

/-!
# Decomposing rigid type formers heterogeneously

R90 decomposed identity types with one carrier and Π/Σ types with one domain. Here the carriers
and the domains may differ, and the pieces are **heterogeneous equations** (R76's twins): two judged
terms whose types are not yet known to agree, each kept at its own type until the types are shown
equal.

* **Identity types.** At a universe `U`, `Id A a b ≐ Id A' a' b'` has exactly the solutions of
  `A ≐ A'` at `U` together with the heterogeneous `(a : A) ≐ (a' : A')` and `(b : A) ≐ (b' : A')`
  (`idParts`).
* **Π and Σ types.** At `U`, `Π A B ≐ Π A' B'` has exactly the solutions of `A ≐ A'` at `U`
  together with the heterogeneous **family twin** `(λ x. B : Π A U) ≐ (λ x. B' : Π A' U)`, whose type
  equation is the domain equation and whose terms compare the codomains under one binder once the
  domains agree (`binderParts`). The same holds for Σ.

Each decomposition keeps exactly the solutions at every later context, with no inhabitation premise.
Typing of every piece comes from generation; only the formation of the pieces' annotations reads
the budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRigidFormers

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentInPlace

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A decomposition of one equation**: a store with exactly its solutions at every later context. -/
abbrev Parts {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :=
  {parts : EquationStore (TotalTerm Θ) // ∀ {Δ : Context S.R} (σ : Δ ⟶ Θ),
    (frames S.levels).Solves σ equation ↔ (frames S.levels).Models σ parts}

theorem solves_raw {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (equation : Equation (TotalTerm Θ)) :
    (frames S.levels).Solves σ equation ↔
      TypeEq S.R Δ.raw (subst σ.substitution equation.1.1.code) (subst σ.substitution equation.2.1.code) ∧
        Equal S.R Δ.raw (subst σ.substitution equation.1.2.code) (subst σ.substitution equation.2.2.code)
          (subst σ.substitution equation.1.1.code) := Iff.rfl

theorem models_three {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (first second third : Equation (TotalTerm Θ)) :
    (frames S.levels).Models σ [first, second, third] ↔
      (frames S.levels).Solves σ first ∧ (frames S.levels).Solves σ second ∧ (frames S.levels).Solves σ third := by
  simp only [Frames.Models, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

theorem models_two {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) (first second : Equation (TotalTerm Θ)) :
    (frames S.levels).Models σ [first, second] ↔
      (frames S.levels).Solves σ first ∧ (frames S.levels).Solves σ second := by
  simp only [Frames.Models, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]

/-- A universe is a type. -/
theorem universe_isType {n : Nat} (Γ : Ctx Head n) {u : Head} (universal : S.R.isUniverse u) :
    IsType S.R Γ (.head u) := by
  obtain ⟨v, hv, typing, _⟩ := S.levels.successor universal
  exact ⟨v, hv, .headType typing⟩

/-! ## Identity types -/

/-- What generation says about an identity type at a universe. -/
theorem id_typed {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head} (typed : Typed S.R Γ (.id A a b) (.head u)) :
    Typed S.R Γ A (.head u) ∧ Typed S.R Γ a A ∧ Typed S.R Γ b A := by
  obtain ⟨_, carrier, _, first, second, below⟩ := typed.generation
  exact ⟨carrier.subsume below, first, second⟩

/-- **An equation between identity types at one universe**, read from its codes. -/
structure IdShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  u : Head
  carrier : Tm Head Θ.arity
  carrier' : Tm Head Θ.arity
  left : Tm Head Θ.arity
  left' : Tm Head Θ.arity
  right : Tm Head Θ.arity
  right' : Tm Head Θ.arity
  annotation : equation.1.1.code = .head u
  same : equation.2.1.code = .head u
  universal : S.R.isUniverse u
  leftCode : equation.1.2.code = .id carrier left right
  rightCode : equation.2.2.code = .id carrier' left' right'

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

/-- Read an equation between identity types at a universe; no budget. -/
def idShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (IdShape equation) :=
  match annotation : equation.1.1.code, leftCode : equation.1.2.code, rightCode : equation.2.2.code with
  | .head u, .id A a b, .id A' a' b' =>
      if same : equation.2.1.code = .head u then
        if universal : S.R.isUniverse u then
          some ⟨u, A, A', a, a', b, b', annotation, same, universal, leftCode, rightCode⟩
        else none
      else none
  | _, _, _ => none

variable [DecidableRel S.R.headEq] (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] in
theorem IdShape.leftTyped {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : IdShape equation) :
    Typed S.R Θ.raw shape.carrier (.head shape.u) ∧ Typed S.R Θ.raw shape.left shape.carrier ∧
      Typed S.R Θ.raw shape.right shape.carrier :=
  id_typed (by rw [← shape.leftCode, ← shape.annotation]; exact equation.1.2.typed)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] in
theorem IdShape.rightTyped {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : IdShape equation) :
    Typed S.R Θ.raw shape.carrier' (.head shape.u) ∧ Typed S.R Θ.raw shape.left' shape.carrier' ∧
      Typed S.R Θ.raw shape.right' shape.carrier' :=
  id_typed (by rw [← shape.rightCode, ← shape.same]; exact equation.2.2.typed)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] in
/-- **The pieces of an identity equation**: the carriers at the universe, and the two endpoint
pairs, each endpoint at its own carrier. -/
def IdShape.parts {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : IdShape equation)
    (carrier : {type : TypeOver Θ // type.code = shape.carrier})
    (carrier' : {type : TypeOver Θ // type.code = shape.carrier'}) : EquationStore (TotalTerm Θ) :=
  [(⟨equation.1.1, ⟨shape.carrier, by rw [shape.annotation]; exact shape.leftTyped.1⟩⟩,
      ⟨equation.1.1, ⟨shape.carrier', by rw [shape.annotation]; exact shape.rightTyped.1⟩⟩),
    (⟨carrier.val, ⟨shape.left, by rw [carrier.property]; exact shape.leftTyped.2.1⟩⟩,
      ⟨carrier'.val, ⟨shape.left', by rw [carrier'.property]; exact shape.rightTyped.2.1⟩⟩),
    (⟨carrier.val, ⟨shape.right, by rw [carrier.property]; exact shape.leftTyped.2.2⟩⟩,
      ⟨carrier'.val, ⟨shape.right', by rw [carrier'.property]; exact shape.rightTyped.2.2⟩⟩)]

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq] in
include facts roots heads algebra complete in
/-- **Identity types decompose heterogeneously**, with exactly the original solutions at every later
context. -/
theorem IdShape.exact {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : IdShape equation)
    (carrier : {type : TypeOver Θ // type.code = shape.carrier})
    (carrier' : {type : TypeOver Θ // type.code = shape.carrier'}) {Δ : Context S.R} (σ : Δ ⟶ Θ) :
    (frames S.levels).Solves σ equation ↔ (frames S.levels).Models σ (shape.parts carrier carrier') := by
  rw [solves_raw, IdShape.parts, models_three, solves_raw, solves_raw, solves_raw]
  simp only [carrier.property, carrier'.property,
    shape.annotation, shape.same, shape.leftCode, shape.rightCode]
  change TypeEq S.R Δ.raw (.head shape.u) (.head shape.u) ∧
      Equal S.R Δ.raw (.id (subst σ.substitution shape.carrier) (subst σ.substitution shape.left)
        (subst σ.substitution shape.right)) (.id (subst σ.substitution shape.carrier')
        (subst σ.substitution shape.left') (subst σ.substitution shape.right')) (.head shape.u) ↔
    (TypeEq S.R Δ.raw (.head shape.u) (.head shape.u) ∧
      Equal S.R Δ.raw (subst σ.substitution shape.carrier) (subst σ.substitution shape.carrier') (.head shape.u)) ∧
    (TypeEq S.R Δ.raw (subst σ.substitution shape.carrier) (subst σ.substitution shape.carrier') ∧
      Equal S.R Δ.raw (subst σ.substitution shape.left) (subst σ.substitution shape.left')
        (subst σ.substitution shape.carrier)) ∧
    (TypeEq S.R Δ.raw (subst σ.substitution shape.carrier) (subst σ.substitution shape.carrier') ∧
      Equal S.R Δ.raw (subst σ.substitution shape.right) (subst σ.substitution shape.right')
        (subst σ.substitution shape.carrier))
  have uType : TypeEq S.R Δ.raw (.head shape.u) (.head shape.u) := (universe_isType Δ.raw shape.universal).refl
  constructor
  · rintro ⟨_, held⟩
    obtain ⟨carriers, lefts, rights⟩ :=
      (ContextualDependentRigid.typeEq_id_iff facts Δ.formed).mp ⟨shape.u, shape.universal, held⟩
    exact ⟨⟨uType, equal_of_typeEq facts roots heads algebra complete Δ.formed shape.universal
        (shape.leftTyped.1.substitute σ.typed) (shape.rightTyped.1.substitute σ.typed) carriers⟩,
      ⟨carriers, lefts⟩, ⟨carriers, rights⟩⟩
  · rintro ⟨⟨_, carriers⟩, ⟨_, lefts⟩, ⟨_, rights⟩⟩
    exact ⟨uType, .idCong carriers shape.universal lefts rights⟩

variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R)
variable [DecidableRel S.R.cumulative]

/-- **The identity decomposition of one equation**: the carriers are formed at the budget. -/
def idParts (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (Parts equation) :=
  match idShape equation with
  | none => none
  | some shape =>
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ shape.carrier).bind
        fun carrier =>
          (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
            shape.carrier').map fun carrier' =>
            ⟨shape.parts carrier carrier', fun σ => shape.exact facts roots heads algebra complete carrier carrier' σ⟩

/-! ## Π and Σ types -/

/-- The binder formers: `Π` (`true`) and `Σ` (`false`). -/
def binder : Bool → {n : Nat} → Tm Head n → Tm Head (n + 1) → Tm Head n
  | true, _, A, B => .pi A B
  | false, _, A, B => .sigma A B

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
theorem subst_binder (isPi : Bool) {n m : Nat} (σ : Sub Head n m) (A : Tm Head n) (B : Tm Head (n + 1)) :
    subst σ (binder isPi A B) = binder isPi (subst σ A) (subst (liftSub σ) B) := by
  cases isPi <;> rfl

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts in
theorem typeEq_binder_iff (isPi : Bool) {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
    (formed : CtxFormed S.R Γ) :
    TypeEq S.R Γ (binder isPi A B) (binder isPi A' B') ↔ TypeEq S.R Γ A A' ∧ TypeEq S.R (.snoc Γ A) B B' := by
  cases isPi
  · exact ContextualDependentRigid.typeEq_sigma_iff facts formed
  · exact ContextualDependentRigid.typeEq_pi_iff facts formed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts algebra in
/-- What generation says about a binder at a universe: its domain and its family at that universe. -/
theorem binder_typed (isPi : Bool) {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {A : Tm Head n}
    {B : Tm Head (n + 1)} {u : Head} (typed : Typed S.R Γ (binder isPi A B) (.head u)) :
    Typed S.R Γ A (.head u) ∧ Typed S.R (.snoc Γ A) B (.head u) := by
  have key : ∀ {u₁ v w : Head}, Typed S.R Γ A (.head u₁) → Typed S.R (.snoc Γ A) B (.head v) → S.R.join u₁ v w →
      TypeLe S.R Γ (.head w) (.head u) → Typed S.R Γ A (.head u) ∧ Typed S.R (.snoc Γ A) B (.head u) := by
    intro u₁ v w tA tB join le
    have hw := (S.levels.join_level join).1
    have below : S.R.cumulative w u :=
      TypeLe.cumulative_of_heads facts algebra formed le hw (universe_isType Γ hw).refl rfl
    exact ⟨Typed.subsume (Derivable.cumul tA (S.levels.join_upper join).1) le,
      Derivable.cumul tB (algebra.trans (S.levels.join_upper join).2 below)⟩
  cases isPi
  · obtain ⟨_, _, _, tA, _, tB, _, join, le⟩ := (typed : Typed S.R Γ (.sigma A B) (.head u)).generation
    exact key tA tB join le
  · obtain ⟨_, _, _, tA, _, tB, _, join, le⟩ := (typed : Typed S.R Γ (.pi A B) (.head u)).generation
    exact key tA tB join le

/-- **An equation between Π types, or between Σ types, at one universe**, read from its codes. -/
structure BinderShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  isPi : Bool
  u : Head
  domain : Tm Head Θ.arity
  domain' : Tm Head Θ.arity
  family : Tm Head (Θ.arity + 1)
  family' : Tm Head (Θ.arity + 1)
  annotation : equation.1.1.code = .head u
  same : equation.2.1.code = .head u
  universal : S.R.isUniverse u
  leftCode : equation.1.2.code = binder isPi domain family
  rightCode : equation.2.2.code = binder isPi domain' family'

omit [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative] in
/-- Read an equation between Π types or Σ types at a universe; no budget. -/
def binderShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (BinderShape equation) :=
  match annotation : equation.1.1.code, leftCode : equation.1.2.code, rightCode : equation.2.2.code with
  | .head u, .pi A B, .pi A' B' =>
      if same : equation.2.1.code = .head u then
        if universal : S.R.isUniverse u then
          some ⟨true, u, A, A', B, B', annotation, same, universal, leftCode, rightCode⟩
        else none
      else none
  | .head u, .sigma A B, .sigma A' B' =>
      if same : equation.2.1.code = .head u then
        if universal : S.R.isUniverse u then
          some ⟨false, u, A, A', B, B', annotation, same, universal, leftCode, rightCode⟩
        else none
      else none
  | _, _, _ => none

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts algebra in
theorem BinderShape.leftTyped {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : BinderShape equation) :
    Typed S.R Θ.raw shape.domain (.head shape.u) ∧ Typed S.R (.snoc Θ.raw shape.domain) shape.family (.head shape.u) :=
  binder_typed facts algebra shape.isPi Θ.formed
    (by rw [← shape.leftCode, ← shape.annotation]; exact equation.1.2.typed)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts algebra in
theorem BinderShape.rightTyped {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : BinderShape equation) :
    Typed S.R Θ.raw shape.domain' (.head shape.u) ∧
      Typed S.R (.snoc Θ.raw shape.domain') shape.family' (.head shape.u) :=
  binder_typed facts algebra shape.isPi Θ.formed
    (by rw [← shape.rightCode, ← shape.same]; exact equation.2.2.typed)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **The pieces of a binder equation**: the domains at the universe, and the **family twin**
`(λ x. B : Π A U) ≐ (λ x. B' : Π A' U)`, each family at its own domain. -/
def BinderShape.parts {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : BinderShape equation)
    (family : {type : TypeOver Θ // type.code = .pi shape.domain (.head shape.u)})
    (family' : {type : TypeOver Θ // type.code = .pi shape.domain' (.head shape.u)}) : EquationStore (TotalTerm Θ) :=
  [(⟨equation.1.1, ⟨shape.domain, by rw [shape.annotation]; exact (shape.leftTyped facts algebra).1⟩⟩,
      ⟨equation.1.1, ⟨shape.domain', by rw [shape.annotation]; exact (shape.rightTyped facts algebra).1⟩⟩),
    (⟨family.val, ⟨.lam shape.family, by
        rw [family.property]
        exact .lamIntro (by have h := family.val.formed; rw [family.property] at h; exact h) family.val.universeWitness
          (shape.leftTyped facts algebra).2⟩⟩,
      ⟨family'.val, ⟨.lam shape.family', by
        rw [family'.property]
        exact .lamIntro (by have h := family'.val.formed; rw [family'.property] at h; exact h) family'.val.universeWitness
          (shape.rightTyped facts algebra).2⟩⟩)]

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts roots heads algebra complete in
/-- **Π and Σ types decompose heterogeneously**, through the family twin, with exactly the original
solutions at every later context. -/
theorem BinderShape.exact {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : BinderShape equation)
    (family : {type : TypeOver Θ // type.code = .pi shape.domain (.head shape.u)})
    (family' : {type : TypeOver Θ // type.code = .pi shape.domain' (.head shape.u)}) {Δ : Context S.R} (σ : Δ ⟶ Θ) :
    (frames S.levels).Solves σ equation ↔ (frames S.levels).Models σ (shape.parts facts algebra family family') := by
  rw [solves_raw, BinderShape.parts, models_two, solves_raw, solves_raw]
  simp only [family.property, family'.property, shape.annotation, shape.same, shape.leftCode, shape.rightCode]
  rw [subst_binder, subst_binder]
  change TypeEq S.R Δ.raw (.head shape.u) (.head shape.u) ∧
      Equal S.R Δ.raw (binder shape.isPi (subst σ.substitution shape.domain) (subst (liftSub σ.substitution) shape.family))
        (binder shape.isPi (subst σ.substitution shape.domain') (subst (liftSub σ.substitution) shape.family'))
        (.head shape.u) ↔
    (TypeEq S.R Δ.raw (.head shape.u) (.head shape.u) ∧
      Equal S.R Δ.raw (subst σ.substitution shape.domain) (subst σ.substitution shape.domain') (.head shape.u)) ∧
    (TypeEq S.R Δ.raw (.pi (subst σ.substitution shape.domain) (.head shape.u))
        (.pi (subst σ.substitution shape.domain') (.head shape.u)) ∧
      Equal S.R Δ.raw (.lam (subst (liftSub σ.substitution) shape.family))
        (.lam (subst (liftSub σ.substitution) shape.family'))
        (.pi (subst σ.substitution shape.domain) (.head shape.u)))
  have uType : TypeEq S.R Δ.raw (.head shape.u) (.head shape.u) := (universe_isType Δ.raw shape.universal).refl
  have tA := (shape.leftTyped facts algebra).1.substitute σ.typed
  have tA' := (shape.rightTyped facts algebra).1.substitute σ.typed
  have tB := (shape.leftTyped facts algebra).2.substitute (σ.typed.lift shape.domain)
  have tB' := (shape.rightTyped facts algebra).2.substitute (σ.typed.lift shape.domain')
  change Typed S.R Δ.raw (subst σ.substitution shape.domain) (.head shape.u) at tA
  change Typed S.R Δ.raw (subst σ.substitution shape.domain') (.head shape.u) at tA'
  change Typed S.R (.snoc Δ.raw (subst σ.substitution shape.domain)) (subst (liftSub σ.substitution) shape.family)
    (.head shape.u) at tB
  change Typed S.R (.snoc Δ.raw (subst σ.substitution shape.domain')) (subst (liftSub σ.substitution) shape.family')
    (.head shape.u) at tB'
  have formedA : CtxFormed S.R (.snoc Δ.raw (subst σ.substitution shape.domain)) :=
    .snoc Δ.formed ⟨shape.u, shape.universal, tA⟩
  have familyFormed := (family.val.reindex σ).formed
  change Typed S.R Δ.raw (subst σ.substitution family.val.code) (.head family.val.level) at familyFormed
  rw [family.property] at familyFormed
  have tLeft : Typed S.R Δ.raw (subst σ.substitution equation.1.2.code) (.head shape.u) := by
    have moved := equation.1.2.typed.substitute σ.typed
    rw [shape.annotation] at moved
    exact moved
  have tRight : Typed S.R Δ.raw (subst σ.substitution equation.2.2.code) (.head shape.u) := by
    have moved := equation.2.2.typed.substitute σ.typed
    rw [shape.same] at moved
    exact moved
  rw [shape.leftCode, subst_binder] at tLeft
  rw [shape.rightCode, subst_binder] at tRight
  constructor
  · rintro ⟨_, held⟩
    obtain ⟨domains, families⟩ := (typeEq_binder_iff facts shape.isPi Δ.formed).mp ⟨shape.u, shape.universal, held⟩
    have tB'' := Typed.stable tB' (CtxEq.snoc (CtxEq.refl Δ.raw Δ.formed) domains)
    refine ⟨⟨uType, equal_of_typeEq facts roots heads algebra complete Δ.formed shape.universal tA tA' domains⟩,
      (ContextualDependentRigid.typeEq_pi_iff facts Δ.formed).mpr
        ⟨domains, (universe_isType _ shape.universal).refl⟩, ?_⟩
    exact .lamCong familyFormed family.val.universeWitness
      (equal_of_typeEq facts roots heads algebra complete formedA shape.universal tB tB'' families)
  · rintro ⟨⟨_, domainsEqual⟩, ⟨_, lambdas⟩⟩
    have domains : TypeEq S.R Δ.raw (subst σ.substitution shape.domain) (subst σ.substitution shape.domain') :=
      ⟨shape.u, shape.universal, domainsEqual⟩
    have tB'' := Typed.stable tB' (CtxEq.snoc (CtxEq.refl Δ.raw Δ.formed) domains)
    obtain ⟨v, hv, typing, _⟩ := S.levels.successor shape.universal
    let domainType : TypeOver Δ := ⟨subst σ.substitution shape.domain, shape.u, shape.universal, tA⟩
    let codomainType : TypeOver (extend Δ domainType) := ⟨.head shape.u, v, hv, .headType typing⟩
    have bodies := (ContextualDependentScope.lambda_equal_iff S.levels
      (⟨_, tB⟩ : Term (extend Δ domainType) codomainType) (⟨_, tB''⟩ : Term (extend Δ domainType) codomainType)).mp
      lambdas
    have families : TypeEq S.R (.snoc Δ.raw (subst σ.substitution shape.domain))
        (subst (liftSub σ.substitution) shape.family) (subst (liftSub σ.substitution) shape.family') :=
      ⟨shape.u, shape.universal, bodies⟩
    exact ⟨uType, equal_of_typeEq facts roots heads algebra complete Δ.formed shape.universal tLeft tRight
      ((typeEq_binder_iff facts shape.isPi Δ.formed).mpr ⟨domains, families⟩)⟩

/-- **The binder decomposition of one equation**: the two family annotations are formed at the
budget. -/
def binderParts (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (Parts equation) :=
  match binderShape equation with
  | none => none
  | some shape =>
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
          (.pi shape.domain (.head shape.u))).bind fun family =>
        (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
            (.pi shape.domain' (.head shape.u))).map fun family' =>
          ⟨shape.parts facts algebra family family',
            fun σ => shape.exact facts roots heads algebra complete family family' σ⟩

/-! ## Pairs -/

/-- **An equation between pairs at a dependent pair type**, read from its codes. -/
structure PairShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  domain : Tm Head Θ.arity
  family : Tm Head (Θ.arity + 1)
  first : Tm Head Θ.arity
  second : Tm Head Θ.arity
  first' : Tm Head Θ.arity
  second' : Tm Head Θ.arity
  annotation : equation.1.1.code = .sigma domain family
  same : equation.2.1.code = .sigma domain family
  leftCode : equation.1.2.code = .pair first second
  rightCode : equation.2.2.code = .pair first' second'

omit [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative] [∀ head, Decidable (S.R.isUniverse head)] in
/-- Read an equation between pairs at a dependent pair type; no budget. -/
def pairShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (PairShape equation) :=
  match annotation : equation.1.1.code, leftCode : equation.1.2.code, rightCode : equation.2.2.code with
  | .sigma A B, .pair a b, .pair a' b' =>
      if same : equation.2.1.code = .sigma A B then
        some ⟨A, B, a, b, a', b', annotation, same, leftCode, rightCode⟩
      else none
  | _, _, _ => none

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts in
theorem PairShape.leftTyped {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : PairShape equation) :
    Typed S.R Θ.raw shape.first shape.domain ∧
      Typed S.R Θ.raw shape.second (inst0 shape.first shape.family) :=
  Typed.pair_inv facts (by rw [← shape.leftCode, ← shape.annotation]; exact equation.1.2.typed) Θ.formed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts in
theorem PairShape.rightTyped {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : PairShape equation) :
    Typed S.R Θ.raw shape.first' shape.domain ∧
      Typed S.R Θ.raw shape.second' (inst0 shape.first' shape.family) :=
  Typed.pair_inv facts (by rw [← shape.rightCode, ← shape.same]; exact equation.2.2.typed) Θ.formed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
/-- **The pieces of a pair equation**: the first components at the domain, and the heterogeneous
second components, each at the family instantiated at its own first component. -/
def PairShape.parts {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : PairShape equation)
    (domain : {type : TypeOver Θ // type.code = shape.domain})
    (fibre : {type : TypeOver Θ // type.code = inst0 shape.first shape.family})
    (fibre' : {type : TypeOver Θ // type.code = inst0 shape.first' shape.family}) : EquationStore (TotalTerm Θ) :=
  [(⟨domain.val, ⟨shape.first, by rw [domain.property]; exact (shape.leftTyped facts).1⟩⟩,
      ⟨domain.val, ⟨shape.first', by rw [domain.property]; exact (shape.rightTyped facts).1⟩⟩),
    (⟨fibre.val, ⟨shape.second, by rw [fibre.property]; exact (shape.leftTyped facts).2⟩⟩,
      ⟨fibre'.val, ⟨shape.second', by rw [fibre'.property]; exact (shape.rightTyped facts).2⟩⟩)]

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts in
/-- **Pairs decompose heterogeneously**, with exactly the original solutions at every later context. -/
theorem PairShape.exact {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : PairShape equation)
    (domain : {type : TypeOver Θ // type.code = shape.domain})
    (fibre : {type : TypeOver Θ // type.code = inst0 shape.first shape.family})
    (fibre' : {type : TypeOver Θ // type.code = inst0 shape.first' shape.family}) {Δ : Context S.R} (σ : Δ ⟶ Θ) :
    (frames S.levels).Solves σ equation ↔ (frames S.levels).Models σ (shape.parts facts domain fibre fibre') := by
  rw [solves_raw, PairShape.parts, models_two, solves_raw, solves_raw]
  simp only [domain.property, fibre.property, fibre'.property, shape.annotation, shape.same, shape.leftCode,
    shape.rightCode]
  rw [subst_inst0, subst_inst0]
  change TypeEq S.R Δ.raw (.sigma (subst σ.substitution shape.domain) (subst (liftSub σ.substitution) shape.family))
        (.sigma (subst σ.substitution shape.domain) (subst (liftSub σ.substitution) shape.family)) ∧
      Equal S.R Δ.raw (.pair (subst σ.substitution shape.first) (subst σ.substitution shape.second))
        (.pair (subst σ.substitution shape.first') (subst σ.substitution shape.second'))
        (.sigma (subst σ.substitution shape.domain) (subst (liftSub σ.substitution) shape.family)) ↔
    (TypeEq S.R Δ.raw (subst σ.substitution shape.domain) (subst σ.substitution shape.domain) ∧
      Equal S.R Δ.raw (subst σ.substitution shape.first) (subst σ.substitution shape.first')
        (subst σ.substitution shape.domain)) ∧
    (TypeEq S.R Δ.raw (inst0 (subst σ.substitution shape.first) (subst (liftSub σ.substitution) shape.family))
        (inst0 (subst σ.substitution shape.first') (subst (liftSub σ.substitution) shape.family)) ∧
      Equal S.R Δ.raw (subst σ.substitution shape.second) (subst σ.substitution shape.second')
        (inst0 (subst σ.substitution shape.first) (subst (liftSub σ.substitution) shape.family)))
  have annotationFormed := (equation.1.1.reindex σ).formed
  change Typed S.R Δ.raw (subst σ.substitution equation.1.1.code) (.head equation.1.1.level) at annotationFormed
  rw [shape.annotation] at annotationFormed
  change Typed S.R Δ.raw (.sigma (subst σ.substitution shape.domain) (subst (liftSub σ.substitution) shape.family))
    (.head equation.1.1.level) at annotationFormed
  obtain ⟨_, v, _, tA, _, tB, hv, _, _⟩ := annotationFormed.generation
  have ta := (shape.leftTyped facts).1.substitute σ.typed
  have tb := (shape.leftTyped facts).2.substitute σ.typed
  have ta' := (shape.rightTyped facts).1.substitute σ.typed
  have tb' := (shape.rightTyped facts).2.substitute σ.typed
  change Typed S.R Δ.raw (subst σ.substitution shape.first) (subst σ.substitution shape.domain) at ta
  change Typed S.R Δ.raw (subst σ.substitution shape.first') (subst σ.substitution shape.domain) at ta'
  change Typed S.R Δ.raw (subst σ.substitution shape.second)
    (subst σ.substitution (inst0 shape.first shape.family)) at tb
  change Typed S.R Δ.raw (subst σ.substitution shape.second')
    (subst σ.substitution (inst0 shape.first' shape.family)) at tb'
  rw [subst_inst0] at tb tb'
  have pairs := ContextualDependentRigid.equal_pair_iff annotationFormed equation.1.1.universeWitness tB hv ta tb ta' tb'
  have domainType : TypeEq S.R Δ.raw (subst σ.substitution shape.domain) (subst σ.substitution shape.domain) :=
    (Typed.isType ta Δ.formed).refl
  have sigmaType := (Typed.isType annotationFormed Δ.formed)
  constructor
  · rintro ⟨_, held⟩
    obtain ⟨firsts, seconds⟩ := pairs.mp held
    exact ⟨⟨domainType, firsts⟩,
      ⟨ContextualDependentRigid.second_types_of_first tB hv ta firsts, seconds⟩⟩
  · rintro ⟨⟨_, firsts⟩, ⟨_, seconds⟩⟩
    exact ⟨⟨equation.1.1.level, equation.1.1.universeWitness, .refl annotationFormed⟩, pairs.mpr ⟨firsts, seconds⟩⟩

/-- **The pair decomposition of one equation**: the domain and both fibres are formed at the budget. -/
def pairParts (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (Parts equation) :=
  match pairShape equation with
  | none => none
  | some shape =>
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
          shape.domain).bind fun domain =>
        (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
            (inst0 shape.first shape.family)).bind fun fibre =>
          (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
              (inst0 shape.first' shape.family)).map fun fibre' =>
            ⟨shape.parts facts domain fibre fibre', fun σ => shape.exact facts domain fibre fibre' σ⟩

/-! ## Reflexivity -/

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative] in
include facts in
/-- **An equation between reflexivity proofs holds at every solution**: both points are equal to the
identity type's left endpoint, so no decomposition is needed. The conversion scan, complete on typed
equal terms, discharges it. -/
theorem refl_solves {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {C x y a a' : Tm Head Θ.arity}
    (annotation : equation.1.1.code = .id C x y) (same : equation.2.1.code = .id C x y)
    (leftCode : equation.1.2.code = .refl a) (rightCode : equation.2.2.code = .refl a')
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : (frames S.levels).Solves σ equation := by
  have pointOf : ∀ {b : Tm Head Θ.arity}, Typed S.R Θ.raw (.refl b) (.id C x y) →
      Equal S.R Θ.raw b x C ∧ Equal S.R Θ.raw b y C := by
    intro b typed
    obtain ⟨_, _, le⟩ := typed.generation
    have equal := TypeLe.id_eq facts le (Typed.isType typed Θ.formed) Θ.formed
    obtain ⟨carriers, first, second⟩ := (ContextualDependentRigid.typeEq_id_iff facts Θ.formed).mp equal
    exact ⟨Equal.convType first carriers, Equal.convType second carriers⟩
  have leftTyped : Typed S.R Θ.raw (.refl a) (.id C x y) := by
    rw [← leftCode, ← annotation]; exact equation.1.2.typed
  have rightTyped : Typed S.R Θ.raw (.refl a') (.id C x y) := by
    rw [← rightCode, ← same]; exact equation.2.2.typed
  obtain ⟨leftX, leftY⟩ := pointOf leftTyped
  obtain ⟨rightX, _⟩ := pointOf rightTyped
  have points : Equal S.R Θ.raw a a' C := .trans leftX (.symm rightX)
  have idFormed : Typed S.R Θ.raw (.id C x y) (.head equation.1.1.level) := by
    have formed := equation.1.1.formed
    rw [annotation] at formed
    exact formed
  obtain ⟨u, tC, hu, _, _, _⟩ := idFormed.generation
  have identities : TypeEq S.R Θ.raw (.id C a a) (.id C x y) :=
    (ContextualDependentRigid.typeEq_id_iff facts Θ.formed).mpr ⟨⟨u, hu, .refl tC⟩, leftX, leftY⟩
  have refls : Equal S.R Θ.raw (.refl a) (.refl a') (.id C x y) := Equal.convType (.reflCong points) identities
  rw [solves_raw, annotation, same, leftCode, rightCode]
  exact ⟨⟨equation.1.1.level, equation.1.1.universeWitness, .refl (idFormed.substitute σ.typed)⟩,
    refls.substitute σ.typed⟩

/-- **The decomposition of one equation between rigid type formers**: identity types, then Π and
Σ types, then pairs. -/
def formerParts (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (Parts equation) :=
  (idParts facts roots heads algebra complete declared choices reducer fuel equation).or
    ((binderParts facts roots heads algebra complete declared choices reducer fuel equation).or
      (pairParts facts roots heads algebra declared choices reducer fuel equation))

end ContextualDependentRigidFormers
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
