import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Completeness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Transitivity

/-!
# η-long β-normal forms

The η-long β-normal forms of the typed βη equality, defined by the type, not by the shape of
the term alone:

* at a type equal to a dependent function type, a normal term is an abstraction whose body is
  normal at the codomain;
* at a type equal to a dependent pair type, a normal term is a pair of normal components, the
  second at the codomain instantiated at the first;
* at a type equal to an identity type, a normal term is reflexivity at a normal point, or neutral;
* at a type equal to a universe, a normal term is a normal type;
* at every other type, a normal term is neutral;
* a normal type is a head, a dependent function, pair or identity type with normal parts, or a
  neutral type;
* a neutral term is a variable or a rigid constant, applied to normal arguments and projected.

Every type index is read up to typed equality. The type of a neutral term is the type its head
assigns, up to typed equality; the type at which it is used is above it. So the predicate is
invariant under equal types and equal contexts (`Long.convType`, `Long.stable`) without
an appeal to uniqueness of types.

Normal forms are compared syntactically up to the rule package's head equality
(`SameUpToHeads`), which is the identity for packages with discrete heads.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaLong

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization

variable {Head : Type}

/-! ## Syntax up to head equality -/

/-- Equality of raw terms up to the head equality of the rule package at heads. -/
inductive SameUpToHeads (R : Rules Head) : {n : Nat} → Tm Head n → Tm Head n → Prop where
  | var {n : Nat} (i : Fin n) : SameUpToHeads R (.var i) (.var i)
  | const {n : Nat} (c : DeclName) : SameUpToHeads R (.const c : Tm Head n) (.const c)
  | head {n : Nat} {h h' : Head} : HeadSame R h h' →
      SameUpToHeads R (.head h : Tm Head n) (.head h')
  | pi {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} :
      SameUpToHeads R A A' → SameUpToHeads R B B' → SameUpToHeads R (.pi A B) (.pi A' B')
  | sigma {n : Nat} {A A' : Tm Head n} {B B' : Tm Head (n + 1)} :
      SameUpToHeads R A A' → SameUpToHeads R B B' → SameUpToHeads R (.sigma A B) (.sigma A' B')
  | id {n : Nat} {A A' x x' y y' : Tm Head n} :
      SameUpToHeads R A A' → SameUpToHeads R x x' → SameUpToHeads R y y' →
      SameUpToHeads R (.id A x y) (.id A' x' y')
  | lam {n : Nat} {b b' : Tm Head (n + 1)} :
      SameUpToHeads R b b' → SameUpToHeads R (.lam b) (.lam b')
  | app {n : Nat} {f f' a a' : Tm Head n} :
      SameUpToHeads R f f' → SameUpToHeads R a a' → SameUpToHeads R (.app f a) (.app f' a')
  | pair {n : Nat} {a a' b b' : Tm Head n} :
      SameUpToHeads R a a' → SameUpToHeads R b b' → SameUpToHeads R (.pair a b) (.pair a' b')
  | fst {n : Nat} {p p' : Tm Head n} : SameUpToHeads R p p' → SameUpToHeads R (.fst p) (.fst p')
  | snd {n : Nat} {p p' : Tm Head n} : SameUpToHeads R p p' → SameUpToHeads R (.snd p) (.snd p')
  | refl {n : Nat} {z z' : Tm Head n} :
      SameUpToHeads R z z' → SameUpToHeads R (.refl z) (.refl z')

theorem SameUpToHeads.rfl' {R : Rules Head} : ∀ {n : Nat} (t : Tm Head n), SameUpToHeads R t t
  | _, .var i => .var i
  | _, .const c => .const c
  | _, .head h => .head (HeadSame.refl h)
  | _, .pi A B => .pi (rfl' A) (rfl' B)
  | _, .sigma A B => .sigma (rfl' A) (rfl' B)
  | _, .id A x y => .id (rfl' A) (rfl' x) (rfl' y)
  | _, .lam b => .lam (rfl' b)
  | _, .app f a => .app (rfl' f) (rfl' a)
  | _, .pair a b => .pair (rfl' a) (rfl' b)
  | _, .fst p => .fst (rfl' p)
  | _, .snd p => .snd (rfl' p)
  | _, .refl z => .refl (rfl' z)

/-- With discrete heads, equality up to heads is syntactic equality. -/
theorem SameUpToHeads.eq_of_discrete {R : Rules Head}
    (discrete : ∀ {h h' : Head}, R.headEq h h' → h = h') {n : Nat} {s t : Tm Head n}
    (same : SameUpToHeads R s t) : s = t := by
  induction same with
  | var => rfl
  | const => rfl
  | head h =>
      rcases h with rfl | e
      · rfl
      · rw [discrete e]
  | pi _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | sigma _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | id _ _ _ ih₁ ih₂ ih₃ => rw [ih₁, ih₂, ih₃]
  | lam _ ih => rw [ih]
  | app _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | pair _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | fst _ ih => rw [ih]
  | snd _ ih => rw [ih]
  | refl _ ih => rw [ih]

/-- A term mentions no head when no universe or ground head occurs in it. Equality up to heads
of such a term with another is syntactic equality. -/
def HeadFree : {n : Nat} → Tm Head n → Prop
  | _, .var _ | _, .const _ => True
  | _, .head _ => False
  | _, .pi A B | _, .sigma A B => HeadFree A ∧ HeadFree B
  | _, .id A x y => HeadFree A ∧ HeadFree x ∧ HeadFree y
  | _, .lam b => HeadFree b
  | _, .app f a | _, .pair f a => HeadFree f ∧ HeadFree a
  | _, .fst p | _, .snd p | _, .refl p => HeadFree p

theorem SameUpToHeads.eq_of_headFree {R : Rules Head} {n : Nat} {s t : Tm Head n}
    (same : SameUpToHeads R s t) (free : HeadFree s) : s = t := by
  induction same with
  | var => rfl
  | const => rfl
  | head _ => exact free.elim
  | pi _ _ ih₁ ih₂ => rw [ih₁ free.1, ih₂ free.2]
  | sigma _ _ ih₁ ih₂ => rw [ih₁ free.1, ih₂ free.2]
  | id _ _ _ ih₁ ih₂ ih₃ => rw [ih₁ free.1, ih₂ free.2.1, ih₃ free.2.2]
  | lam _ ih => rw [ih free]
  | app _ _ ih₁ ih₂ => rw [ih₁ free.1, ih₂ free.2]
  | pair _ _ ih₁ ih₂ => rw [ih₁ free.1, ih₂ free.2]
  | fst _ ih => rw [ih free]
  | snd _ ih => rw [ih free]
  | refl _ ih => rw [ih free]

/-! ## The normal forms -/

/-- The judgments of normal forms: a normal type, a normal term at a type, and a neutral term
with the type its head assigns. -/
inductive LongStatement (Head : Type) : Type where
  | type {n : Nat} (context : Ctx Head n) (code : Tm Head n)
  | term {n : Nat} (context : Ctx Head n) (code type : Tm Head n)
  | spine {n : Nat} (context : Ctx Head n) (code type : Tm Head n)

/-- A type that is not equal to a dependent function or pair type: the types at which a normal
term may be neutral. -/
def Base (R : Rules Head) {n : Nat} (Γ : Ctx Head n) (T : Tm Head n) : Prop :=
  (∀ (A : Tm Head n) (B : Tm Head (n + 1)), ¬ TypeEq R Γ T (.pi A B)) ∧
    (∀ (A : Tm Head n) (B : Tm Head (n + 1)), ¬ TypeEq R Γ T (.sigma A B))

/-- **η-long β-normal forms.** -/
inductive Long (R : Rules Head) (roles : Roles Head) : LongStatement Head → Prop where
  -- Normal types
  | head {n : Nat} {Γ : Ctx Head n} {h : Head} :
      IsType R Γ (.head h) → Long R roles (.type Γ (.head h))
  | pi {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Long R roles (.type Γ A) → Long R roles (.type (.snoc Γ A) B) → IsType R Γ (.pi A B) →
      Long R roles (.type Γ (.pi A B))
  | sigma {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)} :
      Long R roles (.type Γ A) → Long R roles (.type (.snoc Γ A) B) → IsType R Γ (.sigma A B) →
      Long R roles (.type Γ (.sigma A B))
  | id {n : Nat} {Γ : Ctx Head n} {A x y : Tm Head n} :
      Long R roles (.type Γ A) → Long R roles (.term Γ x A) → Long R roles (.term Γ y A) →
      IsType R Γ (.id A x y) → Long R roles (.type Γ (.id A x y))
  | neutralType {n : Nat} {Γ : Ctx Head n} {V U : Tm Head n} {u : Head} :
      Long R roles (.spine Γ V U) → R.isUniverse u → Below R Γ U (.head u) →
      Long R roles (.type Γ V)
  -- Normal terms
  | univ {n : Nat} {Γ : Ctx Head n} {v T : Tm Head n} {u : Head} :
      R.isUniverse u → TypeEq R Γ T (.head u) → Typed R Γ v T → Long R roles (.type Γ v) →
      Long R roles (.term Γ v T)
  | lam {n : Nat} {Γ : Ctx Head n} {T A : Tm Head n} {b B : Tm Head (n + 1)} :
      TypeEq R Γ T (.pi A B) → IsType R Γ A → Typed R Γ (.lam b) T →
      Long R roles (.term (.snoc Γ A) b B) → Long R roles (.term Γ (.lam b) T)
  | pair {n : Nat} {Γ : Ctx Head n} {T A a b : Tm Head n} {B : Tm Head (n + 1)} :
      TypeEq R Γ T (.sigma A B) → Typed R Γ (.pair a b) T → Long R roles (.term Γ a A) →
      Long R roles (.term Γ b (inst0 a B)) → Long R roles (.term Γ (.pair a b) T)
  | refl {n : Nat} {Γ : Ctx Head n} {T A x y z : Tm Head n} :
      TypeEq R Γ T (.id A x y) → Typed R Γ (.refl z) T → Long R roles (.term Γ z A) →
      Long R roles (.term Γ (.refl z) T)
  | neutral {n : Nat} {Γ : Ctx Head n} {v T U : Tm Head n} :
      Long R roles (.spine Γ v U) → Below R Γ U T → Typed R Γ v T → Base R Γ T →
      Long R roles (.term Γ v T)
  -- Neutral terms
  | var {n : Nat} {Γ : Ctx Head n} {U : Tm Head n} (i : Fin n) :
      TypeEq R Γ U (Ctx.lookup Γ i) → Long R roles (.spine Γ (.var i) U)
  | const {n : Nat} {Γ : Ctx Head n} {U : Tm Head n} {c : DeclName} {type : Tm Head 0} :
      roles c = .rigid → R.constantType c = some type → Typed R Γ (.const c) (liftClosed type) →
      TypeEq R Γ U (liftClosed type) → Long R roles (.spine Γ (.const c) U)
  | app {n : Nat} {Γ : Ctx Head n} {f a U F A : Tm Head n} {B : Tm Head (n + 1)} :
      Long R roles (.spine Γ f F) → TypeEq R Γ F (.pi A B) → Long R roles (.term Γ a A) →
      TypeEq R Γ U (inst0 a B) → Long R roles (.spine Γ (.app f a) U)
  | fst {n : Nat} {Γ : Ctx Head n} {p U P A : Tm Head n} {B : Tm Head (n + 1)} :
      Long R roles (.spine Γ p P) → TypeEq R Γ P (.sigma A B) → TypeEq R Γ U A →
      Long R roles (.spine Γ (.fst p) U)
  | snd {n : Nat} {Γ : Ctx Head n} {p U P A : Tm Head n} {B : Tm Head (n + 1)} :
      Long R roles (.spine Γ p P) → TypeEq R Γ P (.sigma A B) →
      TypeEq R Γ U (inst0 (.fst p) B) → Long R roles (.spine Γ (.snd p) U)

/-- `v` is an η-long β-normal form of `t` at `A`. -/
def NormalForm (R : Rules Head) (roles : Roles Head) {n : Nat} (Γ : Ctx Head n)
    (t v A : Tm Head n) : Prop :=
  Long R roles (.term Γ v A) ∧ Equal R Γ t v A

/-! ## What a normal form is -/

/-- Normal types are types, normal terms have their type, neutral terms the type their head
assigns. -/
def Sound (R : Rules Head) : LongStatement Head → Prop
  | .type Γ V => IsType R Γ V
  | .term Γ v T => Typed R Γ v T
  | .spine Γ t U => Typed R Γ t U

theorem Long.sound {R : Rules Head} {roles : Roles Head} {st : LongStatement Head}
    (long : Long R roles st) : Sound R st := by
  induction long with
  | head isType => exact isType
  | pi _ _ isType _ _ => exact isType
  | sigma _ _ isType _ _ => exact isType
  | id _ _ _ isType _ _ _ => exact isType
  | neutralType _ hu e ih => exact ⟨_, hu, .sub ih e⟩
  | univ _ _ typed _ _ => exact typed
  | lam _ _ typed _ _ => exact typed
  | pair _ typed _ _ _ _ => exact typed
  | refl _ typed _ _ => exact typed
  | neutral _ _ typed _ _ => exact typed
  | var i e => exact Typed.convType (.var i) e.symm
  | const _ _ typed e => exact Typed.convType typed e.symm
  | app _ eF _ eU ihf iha =>
      exact Typed.convType (.appElim (Typed.convType ihf eF) iha) eU.symm
  | fst _ eP eU ih => exact Typed.convType (.fstElim (Typed.convType ih eP)) eU.symm
  | snd _ eP eU ih => exact Typed.convType (.sndElim (Typed.convType ih eP)) eU.symm

theorem Long.typed {R : Rules Head} {roles : Roles Head} {n : Nat} {Γ : Ctx Head n}
    {v T : Tm Head n} (long : Long R roles (.term Γ v T)) : Typed R Γ v T :=
  long.sound

theorem Long.spine_typed {R : Rules Head} {roles : Roles Head} {n : Nat} {Γ : Ctx Head n}
    {t U : Tm Head n} (long : Long R roles (.spine Γ t U)) : Typed R Γ t U :=
  long.sound

theorem Long.isType {R : Rules Head} {roles : Roles Head} {n : Nat} {Γ : Ctx Head n}
    {V : Tm Head n} (long : Long R roles (.type Γ V)) : IsType R Γ V :=
  long.sound

/-- Normal forms are weak-head normal, and neutral terms are neutral. -/
def Stuck (R : Rules Head) (roles : Roles Head) : LongStatement Head → Prop
  | .type _ V => Whnf R roles V
  | .term _ v _ => Whnf R roles v
  | .spine _ t _ => Neutral roles t

theorem Long.stuck {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {st : LongStatement Head} (long : Long R roles st) : Stuck R roles st := by
  induction long with
  | head => exact head_whnf shape _
  | pi => exact pi_whnf shape _ _
  | sigma => exact sigma_whnf shape _ _
  | id => exact id_whnf shape _ _ _
  | neutralType _ _ _ ih => exact Neutral.whnf shape ih
  | univ _ _ _ _ ih => exact ih
  | lam => exact lam_whnf shape _
  | pair => exact pair_whnf shape _ _
  | refl => exact refl_whnf shape _
  | neutral _ _ _ _ ih => exact Neutral.whnf shape ih
  | var i => exact .var i
  | const role _ _ _ => exact Neutral.rigid (c := _) [] role
  | app _ _ _ _ ih => exact .app ih
  | fst _ _ _ ih => exact .fst ih
  | snd _ _ _ ih => exact .snd ih

theorem Long.whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles) {n : Nat}
    {Γ : Ctx Head n} {v T : Tm Head n} (long : Long R roles (.term Γ v T)) : Whnf R roles v :=
  long.stuck shape

theorem Long.type_whnf {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {Γ : Ctx Head n} {V : Tm Head n} (long : Long R roles (.type Γ V)) :
    Whnf R roles V :=
  long.stuck shape

theorem Long.neutral_of_spine {R : Rules Head} {roles : Roles Head} (shape : RootShape R roles)
    {n : Nat} {Γ : Ctx Head n} {t U : Tm Head n} (long : Long R roles (.spine Γ t U)) :
    Neutral roles t :=
  long.stuck shape

/-! ## Invariance under equal types and equal contexts -/

section Invariance

variable {L : Type} [UniverseLevel.LevelOrder L] {R : Rules Head} {roles : Roles Head}

theorem Base.of_typeEq (levels : LevelModel R L) {n : Nat} {Γ : Ctx Head n} {T T' : Tm Head n} (base : Base R Γ T)
    (equal : TypeEq R Γ T T') : Base R Γ T' :=
  ⟨fun A B e => base.1 A B (TypeEq.trans levels equal e),
    fun A B e => base.2 A B (TypeEq.trans levels equal e)⟩

/-- A normal term is normal at every equal type. -/
theorem Long.convType (levels : LevelModel R L) {n : Nat} {Γ : Ctx Head n} {v T T' : Tm Head n}
    (long : Long R roles (.term Γ v T)) (equal : TypeEq R Γ T T') :
    Long R roles (.term Γ v T') := by
  cases long with
  | univ hu e typed long =>
      exact .univ hu (TypeEq.trans levels equal.symm e)
        (Typed.convType typed equal) long
  | lam e isA typed long =>
      exact .lam (TypeEq.trans levels equal.symm e) isA
        (Typed.convType typed equal) long
  | pair e typed la lb =>
      exact .pair (TypeEq.trans levels equal.symm e)
        (Typed.convType typed equal) la lb
  | refl e typed lz =>
      exact .refl (TypeEq.trans levels equal.symm e)
        (Typed.convType typed equal) lz
  | neutral ls le typed base =>
      exact .neutral ls (.subTrans le equal.below)
        (Typed.convType typed equal) (base.of_typeEq levels equal)

/-- A neutral term is neutral at every type equal to the one its head assigns. -/
theorem Long.spine_convType (levels : LevelModel R L) {n : Nat} {Γ : Ctx Head n} {t U U' : Tm Head n}
    (long : Long R roles (.spine Γ t U)) (equal : TypeEq R Γ U U') :
    Long R roles (.spine Γ t U') := by
  cases long with
  | var i e => exact .var i (TypeEq.trans levels equal.symm e)
  | const role declared typed e =>
      exact .const role declared typed (TypeEq.trans levels equal.symm e)
  | app lf eF la eU => exact .app lf eF la (TypeEq.trans levels equal.symm eU)
  | fst lp eP eU => exact .fst lp eP (TypeEq.trans levels equal.symm eU)
  | snd lp eP eU => exact .snd lp eP (TypeEq.trans levels equal.symm eU)

/-- What a normal form gives in a context of equal types, in both directions. -/
def StableAt (R : Rules Head) (roles : Roles Head) : LongStatement Head → Prop
  | .type Γ V => ∀ {Δ}, CtxEq R Γ Δ → CtxEq R Δ Γ → Long R roles (.type Δ V)
  | .term Γ v T => ∀ {Δ}, CtxEq R Γ Δ → CtxEq R Δ Γ → Long R roles (.term Δ v T)
  | .spine Γ t U => ∀ {Δ}, CtxEq R Γ Δ → CtxEq R Δ Γ → Long R roles (.spine Δ t U)

theorem Below.stable {n : Nat} {Γ Δ : Ctx Head n} {A B : Tm Head n} (le : Below R Γ A B)
    (equal : CtxEq R Γ Δ) : Below R Δ A B := by
  simpa only [subst_ids] using Derivable.substitutes le equal.substMor

theorem Base.stable {n : Nat} {Γ Δ : Ctx Head n} {T : Tm Head n} (base : Base R Γ T)
    (back : CtxEq R Δ Γ) : Base R Δ T :=
  ⟨fun A B e => base.1 A B (e.stable back), fun A B e => base.2 A B (e.stable back)⟩

theorem CtxEq.snocBoth {n : Nat} {Γ Δ : Ctx Head n} {A : Tm Head n} (equal : CtxEq R Γ Δ)
    (back : CtxEq R Δ Γ) (isType : IsType R Γ A) :
    CtxEq R (.snoc Γ A) (.snoc Δ A) ∧ CtxEq R (.snoc Δ A) (.snoc Γ A) :=
  ⟨equal.snocSame isType, back.snocSame (isType.stable equal)⟩

/-- **Normal forms survive equal contexts.** -/
theorem Long.stable (levels : LevelModel R L) {st : LongStatement Head} (long : Long R roles st) : StableAt R roles st := by
  induction long with
  | head isType => exact fun equal _ => .head (isType.stable equal)
  | pi lA _ isType ihA ihB =>
      intro Δ equal back
      obtain ⟨there, here⟩ := CtxEq.snocBoth equal back lA.isType
      exact .pi (ihA equal back) (ihB there here) (isType.stable equal)
  | sigma lA _ isType ihA ihB =>
      intro Δ equal back
      obtain ⟨there, here⟩ := CtxEq.snocBoth equal back lA.isType
      exact .sigma (ihA equal back) (ihB there here) (isType.stable equal)
  | id _ _ _ isType ihA ihx ihy =>
      intro Δ equal back
      exact .id (ihA equal back) (ihx equal back) (ihy equal back) (isType.stable equal)
  | neutralType _ hu e ih =>
      intro Δ equal back
      exact .neutralType (ih equal back) hu (Below.stable e equal)
  | univ hu e typed _ ih =>
      intro Δ equal back
      exact .univ hu (e.stable equal) (Typed.stable typed equal) (ih equal back)
  | lam e isA typed _ ih =>
      intro Δ equal back
      obtain ⟨there, here⟩ := CtxEq.snocBoth equal back isA
      exact .lam (e.stable equal) (isA.stable equal) (Typed.stable typed equal) (ih there here)
  | pair e typed _ _ iha ihb =>
      intro Δ equal back
      exact .pair (e.stable equal) (Typed.stable typed equal) (iha equal back) (ihb equal back)
  | refl e typed _ ih =>
      intro Δ equal back
      exact .refl (e.stable equal) (Typed.stable typed equal) (ih equal back)
  | neutral _ le typed base ih =>
      intro Δ equal back
      exact .neutral (ih equal back) (Below.stable le equal) (Typed.stable typed equal) (base.stable back)
  | var i e =>
      intro Δ equal back
      have here : TypeEq R Δ (Ctx.lookup Δ i) (Ctx.lookup _ i) := equal.lookup i
      exact .var i (TypeEq.trans levels (e.stable equal) here.symm)
  | const role declared typed e =>
      intro Δ equal back
      exact .const role declared (Typed.stable typed equal) (e.stable equal)
  | app _ eF _ eU ihf iha =>
      intro Δ equal back
      exact .app (ihf equal back) (eF.stable equal) (iha equal back) (eU.stable equal)
  | fst _ eP eU ih =>
      intro Δ equal back
      exact .fst (ih equal back) (eP.stable equal) (eU.stable equal)
  | snd _ eP eU ih =>
      intro Δ equal back
      exact .snd (ih equal back) (eP.stable equal) (eU.stable equal)

end Invariance

end ContextualDependentEtaLong
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
