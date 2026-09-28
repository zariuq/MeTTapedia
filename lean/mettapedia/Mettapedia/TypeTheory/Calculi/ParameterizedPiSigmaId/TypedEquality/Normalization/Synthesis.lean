import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Decidability

/-!
# Principal types of the kernel's synthesis, and its refutations

The kernel synthesizes a type for a variable, a constant, a head, a type former,
a reflexivity proof, an elimination of a synthesized term and an abstraction
applied to a synthesized argument. On these terms the synthesized type is
principal: every type of the term lies above it, up to conversion, raising
universes and cumulative subtyping.

Reflexivity is principal only when the synthesized type of its subject is
rigid, that is, usable only at types equal to it: identity types are invariant
in their carrier, so `refl X` for `X : 𝒰₀` has the incomparable types
`Id 𝒰₀ X X` and `Id 𝒰₁ X X`, and `refl F` for `F : A → 𝒰₀` has `Id (A → 𝒰₀) F F`
and `Id (A → 𝒰₁) F F`. Rigidity is decided by the shape of the type: a head
that is not a universe, a neutral type, an identity type, an inductive type, a
dependent function type with a rigid codomain, a dependent pair type with rigid
components.

Principal types make each refutation the kernel issues a theorem:

* an application whose function's type is not a dependent function type, and a
  projection whose argument's type is not a dependent pair type, has no type;
* a term checked against a type its synthesized type is not usable at does not
  have that type;
* two terms whose synthesized types have no common type above both are not
  equal at any type; distinct rigid types, dependent function types with
  distinct domains, and types of different formers have none. Distinct
  synthesized types alone do not suffice: `Π A 𝒰₀` and `Π A 𝒰₁` are both below
  `Π A 𝒰₁`;
* two terms of a principal type that the algorithm does not relate are not
  equal at any type, since a comparison at a larger type of terms of a smaller
  one is a comparison at the smaller one;
* a reflexivity proof whose subject is not equal to an endpoint is not typed at
  that identity type, and an abstraction, a pair or a reflexivity proof is not
  typed at a type of another former.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- A type usable only at types equal to it. -/
def Rigid (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (A : Tm Head n) : Prop :=
  ∀ {X : Tm Head n}, Below R Γ A X → TypeEq R Γ A X

/-- Types rigid by their shape: a head that is not a universe, a neutral type,
an identity type, an inductive type, a dependent function type with a rigid
codomain, a dependent pair type with rigid components, or a type reducing to
one of these. -/
inductive RigidShape (R : Rules Head) (roles : Roles Head) :
    {n : Nat} → Ctx Head n → Tm Head n → Prop where
  | head {n : Nat} {Γ : Ctx Head n} {h : Head} :
      ¬ R.isUniverse h → RigidShape R roles Γ (.head h)
  | neutral {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} :
      Neutral roles A → RigidShape R roles Γ A
  | id {n : Nat} {Γ : Ctx Head n} {C a b : Tm Head n} : RigidShape R roles Γ (.id C a b)
  | inductiveType {n : Nat} {Γ : Ctx Head n} {T : DeclName}
      {ctors : List (DeclName × List (Field Head))} :
      roles T = .inductive ctors → RigidShape R roles Γ (.const T)
  | pi {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)} :
      RigidShape R roles (.snoc Γ A) B → RigidShape R roles Γ (.pi A B)
  | sigma {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)} :
      RigidShape R roles Γ A → RigidShape R roles (.snoc Γ A) B →
      RigidShape R roles Γ (.sigma A B)
  | red {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n} :
      RedTy R roles Γ A A' → RigidShape R roles Γ A' → RigidShape R roles Γ A

/-- The two modes of the kernel's typing: synthesis computes a type of a term,
checking tests a term against an expected type. -/
inductive Mode where
  | synth
  | check

/-- The kernel's bidirectional typing. Synthesis computes a type for variables,
constants, heads, type formers over types, reflexivity proofs of rigid types,
eliminations of synthesized terms and abstractions applied to synthesized
arguments; the arguments of eliminations and the endpoints of identity types
are checked. Checking tests an abstraction, a pair or a reflexivity proof
against the weak-head normal form of the expected type, and any term by
synthesizing a type usable at the expected one. -/
inductive KernelTyping (R : Rules Head) (roles : Roles Head) :
    Mode → {n : Nat} → Ctx Head n → Tm Head n → Tm Head n → Prop where
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      KernelTyping R roles .synth Γ (.var i) (Ctx.lookup Γ i)
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} {u : Head} :
      R.constantType name = some type → Typed R .nil type (.head u) → R.isUniverse u →
      KernelTyping R roles .synth Γ (.const name) (liftClosed type)
  | head {n : Nat} {Γ : Ctx Head n} {h u : Head} :
      R.headTyping h u → KernelTyping R roles .synth Γ (.head h) (.head u)
  /-- A dependent function type over types: the synthesized types of its
  domain and codomain reduce to universes. -/
  | pi {n : Nat} {Γ : Ctx Head n} {A TA : Tm Head n} {B TB : Tm Head (n + 1)} {u v w : Head} :
      KernelTyping R roles .synth Γ A TA → RedTy R roles Γ TA (.head u) → R.isUniverse u →
      KernelTyping R roles .synth (.snoc Γ A) B TB → RedTy R roles (.snoc Γ A) TB (.head v) →
      R.isUniverse v → R.join u v w → KernelTyping R roles .synth Γ (.pi A B) (.head w)
  | sigma {n : Nat} {Γ : Ctx Head n} {A TA : Tm Head n} {B TB : Tm Head (n + 1)}
      {u v w : Head} :
      KernelTyping R roles .synth Γ A TA → RedTy R roles Γ TA (.head u) → R.isUniverse u →
      KernelTyping R roles .synth (.snoc Γ A) B TB → RedTy R roles (.snoc Γ A) TB (.head v) →
      R.isUniverse v → R.join u v w → KernelTyping R roles .synth Γ (.sigma A B) (.head w)
  | id {n : Nat} {Γ : Ctx Head n} {A TA a b : Tm Head n} {u : Head} :
      KernelTyping R roles .synth Γ A TA → RedTy R roles Γ TA (.head u) → R.isUniverse u →
      KernelTyping R roles .check Γ a A → KernelTyping R roles .check Γ b A →
      KernelTyping R roles .synth Γ (.id A a b) (.head u)
  /-- Reflexivity at a rigid type has a least type. -/
  | refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      KernelTyping R roles .synth Γ a A → RigidShape R roles Γ A →
      KernelTyping R roles .synth Γ (.refl a) (.id A a a)
  | app {n : Nat} {Γ : Ctx Head n} {f a F A : Tm Head n} {B : Tm Head (n + 1)} :
      KernelTyping R roles .synth Γ f F → RedTy R roles Γ F (.pi A B) →
      KernelTyping R roles .check Γ a A →
      KernelTyping R roles .synth Γ (.app f a) (inst0 a B)
  | fst {n : Nat} {Γ : Ctx Head n} {p P A : Tm Head n} {B : Tm Head (n + 1)} :
      KernelTyping R roles .synth Γ p P → RedTy R roles Γ P (.sigma A B) →
      KernelTyping R roles .synth Γ (.fst p) A
  | snd {n : Nat} {Γ : Ctx Head n} {p P A : Tm Head n} {B : Tm Head (n + 1)} :
      KernelTyping R roles .synth Γ p P → RedTy R roles Γ P (.sigma A B) →
      KernelTyping R roles .synth Γ (.snd p) (inst0 (.fst p) B)
  /-- An abstraction applied to a synthesized argument: the body is synthesized
  in the context the argument's type, or an equal annotation, extends. A larger
  domain types the body at a type above, since a variable of the argument's
  type is usable at the larger domain. -/
  | redex {n : Nat} {Γ : Ctx Head n} {a A D : Tm Head n} {b B : Tm Head (n + 1)} :
      KernelTyping R roles .synth Γ a A → TypeEq R Γ A D →
      KernelTyping R roles .synth (.snoc Γ D) b B →
      KernelTyping R roles .synth Γ (.app (.lam b) a) (inst0 a B)
  /-- An abstraction is checked against a dependent function type: its body
  against the codomain, over the domain. -/
  | lamCheck {n : Nat} {Γ : Ctx Head n} {body : Tm Head (n + 1)} {E A : Tm Head n}
      {B : Tm Head (n + 1)} :
      RedTy R roles Γ E (.pi A B) → KernelTyping R roles .check (.snoc Γ A) body B →
      KernelTyping R roles .check Γ (.lam body) E
  /-- A pair is checked against a dependent pair type: its first component
  against the domain, its second against the codomain at the first. -/
  | pairCheck {n : Nat} {Γ : Ctx Head n} {a b E A : Tm Head n} {B : Tm Head (n + 1)} :
      RedTy R roles Γ E (.sigma A B) → KernelTyping R roles .check Γ a A →
      KernelTyping R roles .check Γ b (inst0 a B) →
      KernelTyping R roles .check Γ (.pair a b) E
  /-- A reflexivity proof is checked against an identity type: its subject
  against the carrier, and equal to both endpoints there. -/
  | reflCheck {n : Nat} {Γ : Ctx Head n} {x E A a b : Tm Head n} :
      RedTy R roles Γ E (.id A a b) → KernelTyping R roles .check Γ x A →
      Equal R Γ x a A → Equal R Γ x b A → KernelTyping R roles .check Γ (.refl x) E
  /-- Any term is checked by synthesizing a type usable at the expected one. -/
  | switch {n : Nat} {Γ : Ctx Head n} {t T E : Tm Head n} :
      KernelTyping R roles .synth Γ t T → Below R Γ T E →
      KernelTyping R roles .check Γ t E

/-- `Γ ⊢ t ⇒ T`: the kernel synthesizes the type `T` for `t`. -/
abbrev Synth (R : Rules Head) (roles : Roles Head) {n : Nat} (Γ : Ctx Head n)
    (t T : Tm Head n) : Prop :=
  KernelTyping R roles .synth Γ t T

/-- `Γ ⊢ t ⇐ E`: the kernel checks `t` against the type `E`. -/
abbrev Check (R : Rules Head) (roles : Roles Head) {n : Nat} (Γ : Ctx Head n)
    (t E : Tm Head n) : Prop :=
  KernelTyping R roles .check Γ t E

/-- Instantiating the last context entry keeps a chain of conversions and
universe raises. -/
theorem TypeLe.instantiate {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {A a : Tm Head n}
    {X Y : Tm Head (n + 1)} (le : TypeLe R (.snoc Γ A) X Y) (typing : Typed R Γ a A) :
    TypeLe R Γ (inst0 a X) (inst0 a Y) := by
  induction le with
  | refl => exact .refl _
  | conv e hu _ ih => exact .conv (Equal.instantiate e typing) hu ih
  | cumul c _ ih => exact .cumul c ih
  | sub le _ ih => exact .sub (Derivable.substitutes le (SubstMor.single typing)) ih

variable {S : Setting Head L}

section Principal

variable (facts : FormFacts S.R S.roles)
  (algebra : CumulativeAlgebra S.R)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
include facts

omit facts in
/-- A universe is a type. -/
theorem universe_type {n : Nat} {Γ : Ctx Head n} {u : Head} (hu : S.R.isUniverse u) :
    IsType S.R Γ (.head u) := by
  obtain ⟨s, hs, typing, _⟩ := S.levels.successor hu
  exact ⟨s, hs, .headType typing⟩

/-- Types rigid by their shape are rigid. -/
theorem RigidShape.rigid {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
    (shape : RigidShape S.R S.roles Γ A) : CtxFormed S.R Γ → Rigid S.R Γ A := by
  induction shape with
  | head notUniverse =>
      intro formed X le
      exact Below.rigid le formed
        (fun u hu e => notUniverse ((HeadSame.level S.levels
          (TypeEq.head_injective facts e formed)).1.mpr hu))
        (fun A B e => TypeEq.pi_ne_head facts formed e.symm)
        (fun A B e => TypeEq.sigma_ne_head facts formed e.symm)
  | neutral nA =>
      intro formed X le
      exact Below.rigid le formed
        (fun u _ e => (TypeEq.neutral_form facts e formed nA (.inl ⟨u, rfl⟩)).not_former.1
          u rfl)
        (fun A B e => (TypeEq.neutral_form facts e formed nA
          (.inr (.inl ⟨A, B, rfl⟩))).not_former.2.1 A B rfl)
        (fun A B e => (TypeEq.neutral_form facts e formed nA
          (.inr (.inr (.inl ⟨A, B, rfl⟩)))).not_former.2.2.1 A B rfl)
  | id =>
      intro formed X le
      exact Below.rigid le formed (fun _ _ e => TypeEq.id_ne_head facts formed e)
        (fun _ _ e => TypeEq.pi_ne_id facts formed e.symm)
        (fun _ _ e => TypeEq.sigma_ne_id facts formed e.symm)
  | inductiveType role =>
      intro formed X le
      exact Below.rigid le formed (fun _ _ e => TypeEq.inductive_ne_head facts role formed e)
        (fun _ _ e => TypeEq.inductive_ne_pi facts role formed e)
        (fun _ _ e => TypeEq.inductive_ne_sigma facts role formed e)
  | @pi n Γ A B _ ih =>
      intro formed X le
      have typePi := (Below.isTypes le formed).1
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts typePi
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨A', B', eX, eA, leB⟩ :=
        Below.pi_source facts le formed (IsType.refl typePi)
      obtain ⟨v, hv, eB⟩ := ih formedA leB
      obtain ⟨w, hw, eA'⟩ := eA
      obtain ⟨j, join⟩ := S.levels.join_exists hw hv
      exact TypeEq.trans S.levels ⟨j, (S.levels.join_level join).1, .piCong eA' hw eB hv join⟩ eX.symm
  | @sigma n Γ A B _ _ ihA ihB =>
      intro formed X le
      have typeSigma := (Below.isTypes le formed).1
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.sigma_parts typeSigma
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨A', B', eX, leA, leB⟩ :=
        Below.sigma_source facts le formed (IsType.refl typeSigma)
      obtain ⟨w, hw, eA'⟩ := ihA formed leA
      obtain ⟨v, hv, eB⟩ := ihB formedA leB
      obtain ⟨j, join⟩ := S.levels.join_exists hw hv
      exact TypeEq.trans S.levels ⟨j, (S.levels.join_level join).1, .sigmaCong eA' hw eB hv join⟩
        eX.symm
  | red r _ ih =>
      intro formed X le
      have e := r.typeEq
      exact TypeEq.trans S.levels e (ih formed (.subTrans e.symm.below le))

/-- A type below a type of rigid shape equals it: rigid types have no proper
subtypes either. -/
theorem RigidShape.below_eq {n : Nat} {Γ : Ctx Head n} {R : Tm Head n}
    (shape : RigidShape S.R S.roles Γ R) :
    CtxFormed S.R Γ → ∀ {T : Tm Head n}, Below S.R Γ T R → TypeEq S.R Γ T R := by
  induction shape with
  | head notUniverse =>
      intro formed T le
      refine Below.rigid le formed (fun u hu e => ?_) (fun A B e => ?_) (fun A B e => ?_)
      · obtain ⟨v, hv, eR, _⟩ := Below.universe_source facts le formed hu e
        exact notUniverse ((HeadSame.level S.levels
          (TypeEq.head_injective facts eR formed)).1.mpr hv)
      · obtain ⟨_, _, eR, _, _⟩ := Below.pi_source facts le formed e
        exact TypeEq.pi_ne_head facts formed (TypeEq.symm eR)
      · obtain ⟨_, _, eR, _, _⟩ := Below.sigma_source facts le formed e
        exact TypeEq.sigma_ne_head facts formed (TypeEq.symm eR)
  | neutral nR =>
      intro formed T le
      refine Below.rigid le formed (fun u hu e => ?_) (fun A B e => ?_) (fun A B e => ?_)
      · obtain ⟨v, _, eR, _⟩ := Below.universe_source facts le formed hu e
        exact (TypeEq.neutral_form facts eR formed nR (.inl ⟨v, rfl⟩)).not_former.1 v rfl
      · obtain ⟨_, _, eR, _, _⟩ := Below.pi_source facts le formed e
        exact (TypeEq.neutral_form facts eR formed nR
          (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl
      · obtain ⟨_, _, eR, _, _⟩ := Below.sigma_source facts le formed e
        exact (TypeEq.neutral_form facts eR formed nR
          (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 _ _ rfl
  | id =>
      intro formed T le
      refine Below.rigid le formed (fun u hu e => ?_) (fun A B e => ?_) (fun A B e => ?_)
      · obtain ⟨_, _, eR, _⟩ := Below.universe_source facts le formed hu e
        exact TypeEq.id_ne_head facts formed eR
      · obtain ⟨_, _, eR, _, _⟩ := Below.pi_source facts le formed e
        exact TypeEq.pi_ne_id facts formed (TypeEq.symm eR)
      · obtain ⟨_, _, eR, _, _⟩ := Below.sigma_source facts le formed e
        exact TypeEq.sigma_ne_id facts formed (TypeEq.symm eR)
  | inductiveType role =>
      intro formed T le
      refine Below.rigid le formed (fun u hu e => ?_) (fun A B e => ?_) (fun A B e => ?_)
      · obtain ⟨_, _, eR, _⟩ := Below.universe_source facts le formed hu e
        exact TypeEq.inductive_ne_head facts role formed eR
      · obtain ⟨_, _, eR, _, _⟩ := Below.pi_source facts le formed e
        exact TypeEq.inductive_ne_pi facts role formed eR
      · obtain ⟨_, _, eR, _, _⟩ := Below.sigma_source facts le formed e
        exact TypeEq.inductive_ne_sigma facts role formed eR
  | @pi n Γ A B _ ih =>
      intro formed T le
      have typePi := (Below.isTypes le formed).2
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts typePi
      obtain ⟨A₁, B₁, eT, eA, leB⟩ := Below.pi_inv facts le formed (IsType.refl typePi)
      obtain ⟨v, hv, eB⟩ := ih (.snoc formed ⟨u, hu, tA⟩) (Below.ctxConv leB eA)
      obtain ⟨w, hw, eA'⟩ := TypeEq.symm eA
      obtain ⟨j, join⟩ := S.levels.join_exists hw hv
      exact TypeEq.trans S.levels eT (TypeEq.symm
        ⟨j, (S.levels.join_level join).1, .piCong eA' hw (.symm eB) hv join⟩)
  | @sigma n Γ A B _ _ ihA ihB =>
      intro formed T le
      have typeSigma := (Below.isTypes le formed).2
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.sigma_parts typeSigma
      obtain ⟨A₁, B₁, eT, leA, leB⟩ :=
        Below.sigma_inv facts le formed (IsType.refl typeSigma)
      have eA := ihA formed leA
      obtain ⟨v, hv, eB⟩ := ihB (.snoc formed ⟨u, hu, tA⟩) (Below.ctxConv leB eA)
      obtain ⟨w, hw, eA'⟩ := TypeEq.symm eA
      obtain ⟨j, join⟩ := S.levels.join_exists hw hv
      exact TypeEq.trans S.levels eT (TypeEq.symm
        ⟨j, (S.levels.join_level join).1, .sigmaCong eA' hw (.symm eB) hv join⟩)
  | red r _ ih =>
      intro formed T le
      exact TypeEq.trans S.levels (ih formed (.subTrans le (TypeEq.below r.typeEq)))
        (TypeEq.symm r.typeEq)

omit facts in
/-- What the kernel's typing establishes: a synthesized type is a type of the
term below all of its types, a checked type is a type of the term. -/
def KernelSound (S : Setting Head L) (mode : Mode) {n : Nat} (Γ : Ctx Head n)
    (t T : Tm Head n) : Prop :=
  match mode with
  | .synth => CtxFormed S.R Γ → Typed S.R Γ t T ∧ ∀ {X}, Typed S.R Γ t X → TypeLe S.R Γ T X
  | .check => CtxFormed S.R Γ → Typed S.R Γ t T

include algebra headsTyped in
/-- The kernel's typing is sound, and its synthesized types are principal. -/
theorem KernelTyping.sound {mode : Mode} {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
    (derivation : KernelTyping S.R S.roles mode Γ t T) : KernelSound S mode Γ t T := by
  induction derivation with
  | var i =>
      exact fun _ => ⟨.var i, fun typing => Typed.generation typing⟩
  | const declared typing hu =>
      refine fun _ => ⟨.const declared typing hu, fun typing' => ?_⟩
      obtain ⟨type', u', declared', _, _, le⟩ := Typed.generation typing'
      rw [declared] at declared'
      cases declared'
      exact le
  | head typing =>
      refine fun _ => ⟨.headType typing, fun typing' => ?_⟩
      obtain ⟨u', typing'', le⟩ := Typed.generation typing'
      obtain rfl := headsTyped typing typing''
      exact le
  | @pi n Γ A TA B TB u v w _ rA hu _ rB hv join ihA ihB =>
      intro formed
      obtain ⟨tA₀, principalA⟩ := ihA formed
      have tA := Typed.convType tA₀ rA.typeEq
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨tB₀, principalB⟩ := ihB formedA
      have tB := Typed.convType tB₀ rB.typeEq
      refine ⟨.piForm tA hu tB hv join, fun typing => ?_⟩
      obtain ⟨u', v', w', tA', _, tB', _, join', le⟩ := Typed.generation typing
      have cu := TypeLe.cumulative_of_heads facts algebra formed (principalA tA') hu
        rA.typeEq rfl
      have cv := TypeLe.cumulative_of_heads facts algebra formedA (principalB tB') hv
        rB.typeEq rfl
      obtain ⟨uw, vw⟩ := S.levels.join_upper join'
      exact .cumul (algebra.join_least join (algebra.trans cu uw) (algebra.trans cv vw)) le
  | @sigma n Γ A TA B TB u v w _ rA hu _ rB hv join ihA ihB =>
      intro formed
      obtain ⟨tA₀, principalA⟩ := ihA formed
      have tA := Typed.convType tA₀ rA.typeEq
      have formedA : CtxFormed S.R (.snoc Γ A) := .snoc formed ⟨u, hu, tA⟩
      obtain ⟨tB₀, principalB⟩ := ihB formedA
      have tB := Typed.convType tB₀ rB.typeEq
      refine ⟨.sigmaForm tA hu tB hv join, fun typing => ?_⟩
      obtain ⟨u', v', w', tA', _, tB', _, join', le⟩ := Typed.generation typing
      have cu := TypeLe.cumulative_of_heads facts algebra formed (principalA tA') hu
        rA.typeEq rfl
      have cv := TypeLe.cumulative_of_heads facts algebra formedA (principalB tB') hv
        rB.typeEq rfl
      obtain ⟨uw, vw⟩ := S.levels.join_upper join'
      exact .cumul (algebra.join_least join (algebra.trans cu uw) (algebra.trans cv vw)) le
  | @id n Γ A TA a b u _ rA hu _ _ ihA iha ihb =>
      intro formed
      have ta := iha formed
      have tb := ihb formed
      obtain ⟨tA₀, principalA⟩ := ihA formed
      refine ⟨.idForm (Typed.convType tA₀ rA.typeEq) hu ta tb, fun typing => ?_⟩
      obtain ⟨u', tA', _, _, _, le⟩ := Typed.generation typing
      exact .cumul (TypeLe.cumulative_of_heads facts algebra formed (principalA tA') hu
        rA.typeEq rfl) le
  | @refl n Γ a A _ rigidShape ih =>
      intro formed
      obtain ⟨ta, principal⟩ := ih formed
      refine ⟨.reflIntro ta, fun typing => ?_⟩
      obtain ⟨A', ta', le⟩ := Typed.generation typing
      obtain ⟨s, hs, e⟩ := RigidShape.rigid facts rigidShape formed
        (TypeLe.toBelow (principal ta') (Typed.isType ta' formed))
      exact TypeLe.trans (TypeEq.toLe ⟨s, hs, .idCong e hs (.refl ta) (.refl ta)⟩) le
  | @app n Γ f a F A B _ red _ ih iha =>
      intro formed
      have ta := iha formed
      obtain ⟨tf, principal⟩ := ih formed
      have eF := red.typeEq
      refine ⟨.appElim (Typed.convType tf eF) ta, fun typing => ?_⟩
      obtain ⟨A', B', tf', _, le⟩ := Typed.generation typing
      obtain ⟨_, leB⟩ := TypeLe.pi_parts facts
        (TypeLe.trans (TypeEq.toLe eF.symm) (principal tf')) (Typed.isType tf' formed)
        formed
      exact .sub (Derivable.substitutes leB (SubstMor.single ta)) le
  | @fst n Γ p P A B _ red ih =>
      intro formed
      obtain ⟨tp, principal⟩ := ih formed
      have eP := red.typeEq
      refine ⟨.fstElim (Typed.convType tp eP), fun typing => ?_⟩
      obtain ⟨A', B', tp', le⟩ := Typed.generation typing
      obtain ⟨leA, _⟩ := TypeLe.sigma_parts facts
        (TypeLe.trans (TypeEq.toLe eP.symm) (principal tp')) (Typed.isType tp' formed)
        formed
      exact .sub leA le
  | @snd n Γ p P A B _ red ih =>
      intro formed
      obtain ⟨tp, principal⟩ := ih formed
      have eP := red.typeEq
      have tp₁ := Typed.convType tp eP
      refine ⟨.sndElim tp₁, fun typing => ?_⟩
      obtain ⟨A', B', tp', le⟩ := Typed.generation typing
      obtain ⟨_, leB⟩ := TypeLe.sigma_parts facts
        (TypeLe.trans (TypeEq.toLe eP.symm) (principal tp')) (Typed.isType tp' formed)
        formed
      exact .sub (Derivable.substitutes leB (SubstMor.single (.fstElim tp₁))) le
  | @redex n Γ a A D b B _ eAD _ iha ihb =>
      intro formed
      obtain ⟨ta, principalA⟩ := iha formed
      have isD := (TypeEq.isType eAD formed).2
      have formedD : CtxFormed S.R (.snoc Γ D) := .snoc formed isD
      obtain ⟨tb, principalB⟩ := ihb formedD
      obtain ⟨u, hu, tD⟩ := isD
      obtain ⟨v, hv, tB⟩ := Typed.isType tb formedD
      obtain ⟨w, join⟩ := S.levels.join_exists hu hv
      have taD := Typed.convType ta eAD
      refine ⟨.appElim (.lamIntro (.piForm tD hu tB hv join) (S.levels.join_level join).1 tb)
        taD, fun typing => ?_⟩
      obtain ⟨A', B', tLam, ta', le⟩ := Typed.generation typing
      obtain ⟨A'', B'', s, tPi, hs, tb'', lePi⟩ := Typed.generation tLam
      -- The abstraction's own type is below `Π A' B'`: equal domains, codomains below.
      obtain ⟨e₁, leB''⟩ := TypeLe.pi_parts facts lePi
        (Typed.isType tLam formed) formed
      -- The argument's type is below `A'`, which equals `A''`.
      have leDA'' : Below S.R Γ D A'' :=
        .subTrans eAD.symm.below (.subTrans (TypeLe.toBelow (principalA ta')
          (Typed.isType ta' formed)) e₁.symm.below)
      have leB : TypeLe S.R (.snoc Γ D) B B'' := principalB (Typed.ctxBelow tb'' leDA'')
      have leB' : Below S.R (.snoc Γ D) B'' B' := Below.ctxBelow leB'' leDA''
      exact TypeLe.trans (TypeLe.instantiate (TypeLe.trans leB (TypeLe.of_below leB')) taD) le
  | @lamCheck n Γ body E A B red _ ih =>
      intro formed
      obtain ⟨u, hu, tPi⟩ := red.targetType
      obtain ⟨⟨v, hv, tA⟩, _⟩ := IsType.pi_parts ⟨u, hu, tPi⟩
      exact Typed.convType (.lamIntro tPi hu (ih (.snoc formed ⟨v, hv, tA⟩)))
        (TypeEq.symm red.typeEq)
  | @pairCheck n Γ a b E A B red _ _ iha ihb =>
      intro formed
      obtain ⟨u, hu, tSigma⟩ := red.targetType
      exact Typed.convType (.pairIntro tSigma hu (iha formed) (ihb formed))
        (TypeEq.symm red.typeEq)
  | @reflCheck n Γ x E A a b red _ ea eb ih =>
      intro formed
      have tx := ih formed
      obtain ⟨v, hv, tA⟩ := Typed.isType tx formed
      have eId : TypeEq S.R Γ (.id A x x) (.id A a b) := ⟨v, hv, .idCong (.refl tA) hv ea eb⟩
      exact Typed.convType (Typed.convType (.reflIntro tx) eId) (TypeEq.symm red.typeEq)
  | switch _ le ih =>
      intro formed
      exact .sub (ih formed).1 le

include algebra headsTyped in
/-- The synthesized type is a type of the term, and every type of the term lies
above it. -/
theorem Synth.principal {n : Nat} {Γ : Ctx Head n} {t T : Tm Head n}
    (synth : Synth S.R S.roles Γ t T) :
    CtxFormed S.R Γ → Typed S.R Γ t T ∧ ∀ {X}, Typed S.R Γ t X → TypeLe S.R Γ T X :=
  KernelTyping.sound facts algebra headsTyped synth

include algebra headsTyped in
/-- A term the kernel checks against a type has that type. -/
theorem Check.sound {n : Nat} {Γ : Ctx Head n} {t E : Tm Head n}
    (check : Check S.R S.roles Γ t E) : CtxFormed S.R Γ → Typed S.R Γ t E :=
  KernelTyping.sound facts algebra headsTyped check

end Principal

/-! ## Forms -/

section Forms

variable (facts : FormFacts S.R S.roles)
include facts

omit facts in
/-- A weak-head form of a type is a head or not. -/
theorem IsTypeForm.head_or {n : Nat} {X : Tm Head n} (form : IsTypeForm S.roles X) :
    (∃ h, X = .head h) ∨ ∀ h, X ≠ .head h := by
  rcases form with ⟨h, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | neutral | ⟨_, _, _, rfl⟩
  · exact .inl ⟨h, rfl⟩
  · exact .inr fun _ e => nomatch e
  · exact .inr fun _ e => nomatch e
  · exact .inr fun _ e => nomatch e
  · exact .inr fun h e => neutral.not_former.1 h e
  · exact .inr fun _ e => nomatch e

/-- A weak-head form of a type that is not a head is not equal to one. -/
theorem IsTypeForm.not_head {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {X : Tm Head n} (form : IsTypeForm S.roles X) (notHead : ∀ h, X ≠ .head h) :
    ∀ h, ¬ TypeEq S.R Γ X (.head h) := by
  rcases form with ⟨h, rfl⟩ | ⟨A, B, rfl⟩ | ⟨A, B, rfl⟩ | ⟨C, a, b, rfl⟩ | neutral |
    ⟨T, ctors, role, rfl⟩
  · exact absurd rfl (notHead h)
  · exact fun _ e => TypeEq.pi_ne_head facts formed e
  · exact fun _ e => TypeEq.sigma_ne_head facts formed e
  · exact fun _ e => TypeEq.id_ne_head facts formed e
  · exact fun h e => (TypeEq.neutral_form facts e formed neutral
      (.inl ⟨h, rfl⟩)).not_former.1 h rfl
  · exact fun _ e => TypeEq.inductive_ne_head facts role formed e

/-- A type is equal to a universe, or to no universe. -/
theorem IsType.universe_or {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {X : Tm Head n} (isX : IsType S.R Γ X) :
    (∃ w, S.R.isUniverse w ∧ TypeEq S.R Γ X (.head w)) ∨
      ∀ h, TypeEq S.R Γ X (.head h) → ¬ S.R.isUniverse h := by
  obtain ⟨X', red, form⟩ := facts.typeForm isX formed
  rcases form.head_or with ⟨h, rfl⟩ | notHead
  · rcases S.levels.universe_decided h with hu | notUniverse
    · exact .inl ⟨h, hu, red.typeEq⟩
    · refine .inr fun h' e hu' => notUniverse ?_
      have same := TypeEq.head_injective facts
        (TypeEq.trans S.levels red.typeEq.symm e) formed
      exact (HeadSame.level S.levels same).1.mpr hu'
  · exact .inr fun h e => absurd (TypeEq.trans S.levels red.typeEq.symm e)
      (IsTypeForm.not_head facts formed form notHead h)

/-- A type form above a dependent function type is one. -/
theorem TypeLe.pi_former {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {A : Tm Head n} {B : Tm Head (n + 1)} {Y : Tm Head n} (le : TypeLe S.R Γ (.pi A B) Y)
    (typeX : IsType S.R Γ (.pi A B)) (typeY : IsType S.R Γ Y) (formY : IsTypeForm S.roles Y) :
    ∃ A' B', Y = .pi A' B' := by
  obtain ⟨A₁, B₁, eY, _, _⟩ :=
    Below.pi_source facts (TypeLe.toBelow le typeY) formed (IsType.refl typeX)
  obtain ⟨A₂, B₂, same, _, _⟩ :=
    (facts.forms eY.symm formed (.inr (.inl ⟨_, _, rfl⟩)) formY).pi_left
  exact ⟨A₂, B₂, same⟩

/-- A type form above a dependent pair type is one. -/
theorem TypeLe.sigma_former {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {A : Tm Head n} {B : Tm Head (n + 1)} {Y : Tm Head n} (le : TypeLe S.R Γ (.sigma A B) Y)
    (typeX : IsType S.R Γ (.sigma A B)) (typeY : IsType S.R Γ Y) (formY : IsTypeForm S.roles Y) :
    ∃ A' B', Y = .sigma A' B' := by
  obtain ⟨A₁, B₁, eY, _, _⟩ :=
    Below.sigma_source facts (TypeLe.toBelow le typeY) formed (IsType.refl typeX)
  obtain ⟨A₂, B₂, same, _, _⟩ :=
    (facts.forms eY.symm formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) formY).sigma_left
  exact ⟨A₂, B₂, same⟩

/-- A type form above an identity type is one. -/
theorem TypeLe.id_former {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {C a b Y : Tm Head n} (le : TypeLe S.R Γ (.id C a b) Y) (typeY : IsType S.R Γ Y)
    (formY : IsTypeForm S.roles Y) : ∃ C' a' b', Y = .id C' a' b' := by
  obtain ⟨C₂, a₂, b₂, same, _⟩ := (facts.forms
    (TypeLe.id_eq facts le typeY formed) formed
    (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) formY).id_left
  exact ⟨C₂, a₂, b₂, same⟩

end Forms

/-! ## Common upper bounds -/

/-- Two types are bounded above when some type lies above both. Terms of types
without a common upper bound are never equal: an equality holds at a type
above both of their types. -/
def BoundedAbove (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (T U : Tm Head n) : Prop :=
  ∃ C, Below R Γ T C ∧ Below R Γ U C

theorem BoundedAbove.symm {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {T U : Tm Head n}
    (bounded : BoundedAbove R Γ T U) : BoundedAbove R Γ U T :=
  let ⟨C, leT, leU⟩ := bounded
  ⟨C, leU, leT⟩

/-- A rigid type and a type not below it have no common upper bound: every type
above the rigid one equals it. -/
theorem Rigid.not_boundedAbove {R : Rules Head} {n : Nat} {Γ : Ctx Head n} {T U : Tm Head n}
    (rigid : Rigid R Γ T) (notBelow : ¬ Below R Γ U T) : ¬ BoundedAbove R Γ T U :=
  fun ⟨_, leT, leU⟩ => notBelow (.subTrans leU (TypeEq.below (TypeEq.symm (rigid leT))))

section Bounds

variable (facts : FormFacts S.R S.roles)
include facts

omit facts in
/-- Two universes are bounded above, by their join. -/
theorem boundedAbove_universes {n : Nat} {Γ : Ctx Head n} {u v : Head}
    (hu : S.R.isUniverse u) (hv : S.R.isUniverse v) :
    BoundedAbove S.R Γ (.head u) (.head v) := by
  obtain ⟨w, join⟩ := S.levels.join_exists hu hv
  obtain ⟨uw, vw⟩ := S.levels.join_upper join
  exact ⟨.head w, .subUniv uw, .subUniv vw⟩

omit facts in
/-- Distinct rigid types have no common upper bound. -/
theorem not_boundedAbove_rigid {n : Nat} {Γ : Ctx Head n} {T U : Tm Head n}
    (rigidT : Rigid S.R Γ T) (rigidU : Rigid S.R Γ U) (unequal : ¬ TypeEq S.R Γ T U) :
    ¬ BoundedAbove S.R Γ T U :=
  fun ⟨_, leT, leU⟩ =>
    unequal (TypeEq.trans S.levels (rigidT leT) (TypeEq.symm (rigidU leU)))

/-- A dependent function type and a dependent pair type have no common upper
bound. -/
theorem not_boundedAbove_pi_sigma {n : Nat} {Γ : Ctx Head n} {T U A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (formed : CtxFormed S.R Γ) (eT : TypeEq S.R Γ T (.pi A B))
    (eU : TypeEq S.R Γ U (.sigma A' B')) : ¬ BoundedAbove S.R Γ T U := by
  rintro ⟨C, leT, leU⟩
  obtain ⟨_, _, eC, _, _⟩ := Below.pi_source facts leT formed eT
  obtain ⟨_, _, eC', _, _⟩ := Below.sigma_source facts leU formed eU
  exact TypeEq.pi_ne_sigma facts formed (TypeEq.trans S.levels (TypeEq.symm eC) eC')

/-- A universe and a dependent function type have no common upper bound. -/
theorem not_boundedAbove_universe_pi {n : Nat} {Γ : Ctx Head n} {T U A : Tm Head n}
    {B : Tm Head (n + 1)} {w : Head} (formed : CtxFormed S.R Γ) (hw : S.R.isUniverse w)
    (eT : TypeEq S.R Γ T (.head w)) (eU : TypeEq S.R Γ U (.pi A B)) :
    ¬ BoundedAbove S.R Γ T U := by
  rintro ⟨C, leT, leU⟩
  obtain ⟨_, _, eC, _⟩ := Below.universe_source facts leT formed hw eT
  obtain ⟨_, _, eC', _, _⟩ := Below.pi_source facts leU formed eU
  exact TypeEq.pi_ne_head facts formed (TypeEq.trans S.levels (TypeEq.symm eC') eC)

/-- A universe and a dependent pair type have no common upper bound. -/
theorem not_boundedAbove_universe_sigma {n : Nat} {Γ : Ctx Head n} {T U A : Tm Head n}
    {B : Tm Head (n + 1)} {w : Head} (formed : CtxFormed S.R Γ) (hw : S.R.isUniverse w)
    (eT : TypeEq S.R Γ T (.head w)) (eU : TypeEq S.R Γ U (.sigma A B)) :
    ¬ BoundedAbove S.R Γ T U := by
  rintro ⟨C, leT, leU⟩
  obtain ⟨_, _, eC, _⟩ := Below.universe_source facts leT formed hw eT
  obtain ⟨_, _, eC', _, _⟩ := Below.sigma_source facts leU formed eU
  exact TypeEq.sigma_ne_head facts formed (TypeEq.trans S.levels (TypeEq.symm eC') eC)

/-- Dependent function types with unequal domains have no common upper bound:
the types above one keep its domain. -/
theorem not_boundedAbove_pi_domains {n : Nat} {Γ : Ctx Head n} {T U A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (formed : CtxFormed S.R Γ) (eT : TypeEq S.R Γ T (.pi A B))
    (eU : TypeEq S.R Γ U (.pi A' B')) (unequal : ¬ TypeEq S.R Γ A A') :
    ¬ BoundedAbove S.R Γ T U := by
  rintro ⟨C, leT, leU⟩
  obtain ⟨A₁, B₁, eC, eA, _⟩ := Below.pi_source facts leT formed eT
  obtain ⟨A₂, B₂, eC', eA', _⟩ := Below.pi_source facts leU formed eU
  obtain ⟨e₁₂, _⟩ := TypeEq.pi_injective facts
    (TypeEq.trans S.levels (TypeEq.symm eC) eC') formed
  exact unequal (TypeEq.trans S.levels eA (TypeEq.trans S.levels e₁₂ (TypeEq.symm eA')))

/-- Dependent function types over one domain, with codomains without a common
upper bound, have none. -/
theorem not_boundedAbove_pi_codomains {n : Nat} {Γ : Ctx Head n} {T U A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (formed : CtxFormed S.R Γ) (eT : TypeEq S.R Γ T (.pi A B))
    (eU : TypeEq S.R Γ U (.pi A' B')) (eA : TypeEq S.R Γ A A')
    (apart : ¬ BoundedAbove S.R (.snoc Γ A) B B') : ¬ BoundedAbove S.R Γ T U := by
  rintro ⟨C, leT, leU⟩
  obtain ⟨A₁, B₁, eC, eA₁, leB⟩ := Below.pi_source facts leT formed eT
  obtain ⟨A₂, B₂, eC', _, leB'⟩ := Below.pi_source facts leU formed eU
  obtain ⟨_, eB₁₂⟩ := TypeEq.pi_injective facts
    (TypeEq.trans S.levels (TypeEq.symm eC) eC') formed
  -- The right codomain is below the left upper codomain, over the left domain.
  have leB₂₁ : Below S.R (.snoc Γ A) B₂ B₁ :=
    Below.ctxConv (TypeEq.below (TypeEq.symm eB₁₂)) (TypeEq.symm eA₁)
  exact apart ⟨B₁, leB, .subTrans (Below.ctxConv leB' (TypeEq.symm eA)) leB₂₁⟩

/-- Dependent pair types whose domains have no common upper bound have none. -/
theorem not_boundedAbove_sigma_domains {n : Nat} {Γ : Ctx Head n} {T U A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (formed : CtxFormed S.R Γ) (eT : TypeEq S.R Γ T (.sigma A B))
    (eU : TypeEq S.R Γ U (.sigma A' B')) (apart : ¬ BoundedAbove S.R Γ A A') :
    ¬ BoundedAbove S.R Γ T U := by
  rintro ⟨C, leT, leU⟩
  obtain ⟨A₁, B₁, eC, leA, _⟩ := Below.sigma_source facts leT formed eT
  obtain ⟨A₂, B₂, eC', leA', _⟩ := Below.sigma_source facts leU formed eU
  obtain ⟨e₁₂, _⟩ := TypeEq.sigma_injective facts
    (TypeEq.trans S.levels (TypeEq.symm eC) eC') formed
  exact apart ⟨A₁, leA, .subTrans leA' (TypeEq.below (TypeEq.symm e₁₂))⟩

/-- Dependent pair types over one domain, with codomains without a common upper
bound, have none. -/
theorem not_boundedAbove_sigma_codomains {n : Nat} {Γ : Ctx Head n} {T U A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (formed : CtxFormed S.R Γ) (eT : TypeEq S.R Γ T (.sigma A B))
    (eU : TypeEq S.R Γ U (.sigma A' B')) (eA : TypeEq S.R Γ A A')
    (apart : ¬ BoundedAbove S.R (.snoc Γ A) B B') : ¬ BoundedAbove S.R Γ T U := by
  rintro ⟨C, leT, leU⟩
  obtain ⟨A₁, B₁, eC, leA, leB⟩ := Below.sigma_source facts leT formed eT
  obtain ⟨A₂, B₂, eC', _, leB'⟩ := Below.sigma_source facts leU formed eU
  obtain ⟨_, eB₁₂⟩ := TypeEq.sigma_injective facts
    (TypeEq.trans S.levels (TypeEq.symm eC) eC') formed
  -- The upper codomains agree over the upper domain, hence over the smaller one.
  have leB₂₁ : Below S.R (.snoc Γ A) B₂ B₁ :=
    Below.ctxBelow (TypeEq.below (TypeEq.symm eB₁₂)) leA
  exact apart ⟨B₁, leB, .subTrans (Below.ctxConv leB' (TypeEq.symm eA)) leB₂₁⟩

end Bounds

/-! ## Refutations -/

section Refutation

variable (facts : FormFacts S.R S.roles)
  (algebra : CumulativeAlgebra S.R)
  (headsTyped : ∀ {h u u' : Head}, S.R.headTyping h u → S.R.headTyping h u' → u = u')
include facts algebra headsTyped

/-- A term whose synthesized type is not a dependent function type in weak-head
normal form is not applied: the application has no type. -/
theorem Synth.not_applicable {n : Nat} {Γ : Ctx Head n} {f F F' a X : Tm Head n}
    (synth : Synth S.R S.roles Γ f F) (formed : CtxFormed S.R Γ)
    (red : RedTy S.R S.roles Γ F F') (form : IsTypeForm S.roles F')
    (notPi : ∀ A B, F' ≠ .pi A B) : ¬ Typed S.R Γ (.app f a) X := by
  intro typing
  obtain ⟨A', B', tf', _, _⟩ := Typed.generation typing
  obtain ⟨_, principal⟩ := synth.principal facts algebra headsTyped formed
  have typePi := Typed.isType tf' formed
  have le : Below S.R Γ F' (.pi A' B') := TypeLe.toBelow
    (TypeLe.trans (TypeEq.toLe (TypeEq.symm red.typeEq)) (principal tf')) typePi
  obtain ⟨_, _, e, _, _⟩ := Below.pi_inv facts le formed (IsType.refl typePi)
  obtain ⟨_, _, same, _, _⟩ :=
    (facts.forms (TypeEq.symm e) formed (.inr (.inl ⟨_, _, rfl⟩)) form).pi_left
  exact notPi _ _ same

/-- A term whose synthesized type is not a dependent pair type in weak-head
normal form has no first projection. -/
theorem Synth.not_first {n : Nat} {Γ : Ctx Head n} {p P P' X : Tm Head n}
    (synth : Synth S.R S.roles Γ p P) (formed : CtxFormed S.R Γ)
    (red : RedTy S.R S.roles Γ P P') (form : IsTypeForm S.roles P')
    (notSigma : ∀ A B, P' ≠ .sigma A B) : ¬ Typed S.R Γ (.fst p) X := by
  intro typing
  obtain ⟨A', B', tp', _⟩ := Typed.generation typing
  obtain ⟨_, principal⟩ := synth.principal facts algebra headsTyped formed
  have typeSigma := Typed.isType tp' formed
  have le : Below S.R Γ P' (.sigma A' B') := TypeLe.toBelow
    (TypeLe.trans (TypeEq.toLe (TypeEq.symm red.typeEq)) (principal tp')) typeSigma
  obtain ⟨_, _, e, _, _⟩ := Below.sigma_inv facts le formed (IsType.refl typeSigma)
  obtain ⟨_, _, same, _, _⟩ := (facts.forms (TypeEq.symm e) formed
    (.inr (.inr (.inl ⟨_, _, rfl⟩))) form).sigma_left
  exact notSigma _ _ same

/-- A term whose synthesized type is not a dependent pair type in weak-head
normal form has no second projection. -/
theorem Synth.not_second {n : Nat} {Γ : Ctx Head n} {p P P' X : Tm Head n}
    (synth : Synth S.R S.roles Γ p P) (formed : CtxFormed S.R Γ)
    (red : RedTy S.R S.roles Γ P P') (form : IsTypeForm S.roles P')
    (notSigma : ∀ A B, P' ≠ .sigma A B) : ¬ Typed S.R Γ (.snd p) X := by
  intro typing
  obtain ⟨A', B', tp', _⟩ := Typed.generation typing
  exact Synth.not_first facts algebra headsTyped synth formed red form notSigma
    (X := A') (.fstElim tp')

/-- A term does not have a type its synthesized type is not below. -/
theorem Synth.not_typed {n : Nat} {Γ : Ctx Head n} {t T E : Tm Head n}
    (synth : Synth S.R S.roles Γ t T) (formed : CtxFormed S.R Γ)
    (notBelow : ¬ Below S.R Γ T E) : ¬ Typed S.R Γ t E := by
  intro typing
  obtain ⟨_, principal⟩ := synth.principal facts algebra headsTyped formed
  exact notBelow (TypeLe.toBelow (principal typing) (Typed.isType typing formed))

/-- Two terms whose synthesized types have no common upper bound are equal at no
type. -/
theorem Synth.not_equal_types {n : Nat} {Γ : Ctx Head n} {t u T U C : Tm Head n}
    (st : Synth S.R S.roles Γ t T) (su : Synth S.R S.roles Γ u U)
    (formed : CtxFormed S.R Γ) (apart : ¬ BoundedAbove S.R Γ T U) :
    ¬ Equal S.R Γ t u C := by
  intro equal
  obtain ⟨tC, uC⟩ := Equal.typed equal formed
  obtain ⟨_, principalT⟩ := st.principal facts algebra headsTyped formed
  obtain ⟨_, principalU⟩ := su.principal facts algebra headsTyped formed
  have isC := Typed.isType tC formed
  exact apart ⟨C, TypeLe.toBelow (principalT tC) isC, TypeLe.toBelow (principalU uC) isC⟩

end Refutation

/-! ## Refutations by the algorithm -/

section Algorithmic

variable (facts : FormFacts S.R S.roles)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra complete

/-- Two terms of a principal type that the algorithm does not relate there are
equal at no type: a comparison at a type above, of terms of the principal type,
is a comparison at the principal type. -/
theorem not_equal_of_unrelated {n : Nat} {Γ : Ctx Head n} {t u T C : Tm Head n}
    (formed : CtxFormed S.R Γ) (tT : Typed S.R Γ t T) (uT : Typed S.R Γ u T)
    (principal : ∀ {X}, Typed S.R Γ t X → TypeLe S.R Γ T X)
    (unrelated : ¬ Algorithmic S.R S.roles (.terms Γ t u T)) : ¬ Equal S.R Γ t u C := by
  intro equal
  obtain ⟨tC, _⟩ := Equal.typed equal formed
  have le := TypeLe.toBelow (principal tC) (Typed.isType tC formed)
  exact unrelated (Algorithmic.terms_down_here facts roots heads algebra le formed tT uT
    (complete formed equal))

omit roots heads algebra in
/-- Two types the algorithm does not relate as types are equal at no type, when
the first one's universe is below all its types. -/
theorem not_equal_of_types_unrelated {n : Nat} {Γ : Ctx Head n} {t u C : Tm Head n}
    {w : Head} (formed : CtxFormed S.R Γ) (hw : S.R.isUniverse w)
    (principal : ∀ {X}, Typed S.R Γ t X → TypeLe S.R Γ (.head w) X)
    (unrelated : ¬ Algorithmic S.R S.roles (.types Γ t u)) : ¬ Equal S.R Γ t u C := by
  intro equal
  obtain ⟨tC, _⟩ := Equal.typed equal formed
  obtain ⟨c, hc, eC, _⟩ := Below.universe_source facts
    (TypeLe.toBelow (principal tC) (Typed.isType tC formed)) formed hw
    (universe_type hw).refl
  exact unrelated (complete.types ⟨c, hc, Equal.convType equal eC⟩ formed)

omit roots heads algebra in
/-- A reflexivity proof whose subject the algorithm does not relate to the left
endpoint is not typed at that identity type. -/
theorem refl_not_typed_left {n : Nat} {Γ : Ctx Head n} {x C a b : Tm Head n}
    (formed : CtxFormed S.R Γ) (unrelated : ¬ Algorithmic S.R S.roles (.terms Γ x a C)) :
    ¬ Typed S.R Γ (.refl x) (.id C a b) := by
  intro typing
  obtain ⟨A, tx, le⟩ := Typed.generation typing
  have e := TypeLe.id_eq facts le (Typed.isType typing formed) formed
  obtain ⟨eA, ex, _⟩ := TypeEq.id_injective facts e formed
  exact unrelated (complete formed (Equal.convType ex eA))

omit roots heads algebra in
/-- A reflexivity proof whose subject the algorithm does not relate to the right
endpoint is not typed at that identity type. -/
theorem refl_not_typed_right {n : Nat} {Γ : Ctx Head n} {x C a b : Tm Head n}
    (formed : CtxFormed S.R Γ) (unrelated : ¬ Algorithmic S.R S.roles (.terms Γ x b C)) :
    ¬ Typed S.R Γ (.refl x) (.id C a b) := by
  intro typing
  obtain ⟨A, tx, le⟩ := Typed.generation typing
  have e := TypeLe.id_eq facts le (Typed.isType typing formed) formed
  obtain ⟨eA, _, ey⟩ := TypeEq.id_injective facts e formed
  exact unrelated (complete formed (Equal.convType ey eA))

end Algorithmic

/-! ## Introductions at a type of another former -/

section Formers

variable (facts : FormFacts S.R S.roles)
include facts

omit facts in
/-- A constant the rule package does not declare has no type. -/
theorem const_not_typed {n : Nat} {Γ : Ctx Head n} {name : DeclName} {X : Tm Head n}
    (undeclared : S.R.constantType name = none) : ¬ Typed S.R Γ (.const name) X := by
  intro typing
  obtain ⟨_, _, declared, _⟩ := Typed.generation typing
  rw [undeclared] at declared
  cases declared

/-- An abstraction is typed only at types whose weak-head form is a dependent
function type. -/
theorem lam_not_typed {n : Nat} {Γ : Ctx Head n} {body : Tm Head (n + 1)} {E E' : Tm Head n}
    (formed : CtxFormed S.R Γ) (red : RedTy S.R S.roles Γ E E')
    (form : IsTypeForm S.roles E') (notPi : ∀ A B, E' ≠ .pi A B) :
    ¬ Typed S.R Γ (.lam body) E := by
  intro typing
  obtain ⟨A, B, u, tPi, hu, _, le⟩ := Typed.generation typing
  obtain ⟨_, _, same⟩ := TypeLe.pi_former facts formed
    (TypeLe.trans le (TypeEq.toLe red.typeEq)) ⟨u, hu, tPi⟩ red.targetType form
  exact notPi _ _ same

/-- A pair is typed only at types whose weak-head form is a dependent pair
type. -/
theorem pair_not_typed {n : Nat} {Γ : Ctx Head n} {a b E E' : Tm Head n}
    (formed : CtxFormed S.R Γ) (red : RedTy S.R S.roles Γ E E')
    (form : IsTypeForm S.roles E') (notSigma : ∀ A B, E' ≠ .sigma A B) :
    ¬ Typed S.R Γ (.pair a b) E := by
  intro typing
  obtain ⟨A, B, u, tSigma, hu, _, _, le⟩ := Typed.generation typing
  obtain ⟨_, _, same⟩ := TypeLe.sigma_former facts formed
    (TypeLe.trans le (TypeEq.toLe red.typeEq)) ⟨u, hu, tSigma⟩ red.targetType form
  exact notSigma _ _ same

/-- A reflexivity proof is typed only at types whose weak-head form is an
identity type. -/
theorem refl_not_typed {n : Nat} {Γ : Ctx Head n} {x E E' : Tm Head n}
    (formed : CtxFormed S.R Γ) (red : RedTy S.R S.roles Γ E E')
    (form : IsTypeForm S.roles E') (notId : ∀ C a b, E' ≠ .id C a b) :
    ¬ Typed S.R Γ (.refl x) E := by
  intro typing
  obtain ⟨A, tx, le⟩ := Typed.generation typing
  obtain ⟨_, _, _, same⟩ := TypeLe.id_former facts formed
    (TypeLe.trans le (TypeEq.toLe red.typeEq)) red.targetType form
  exact notId _ _ _ same

end Formers

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
