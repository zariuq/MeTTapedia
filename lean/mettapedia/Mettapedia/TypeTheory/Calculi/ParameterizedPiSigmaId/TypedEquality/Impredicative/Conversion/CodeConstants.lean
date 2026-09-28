import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Telescopes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.CodeReading

/-!
# The code constants in the conversion model

A package of proposition codes is read by the conversion model when its value
side reads it as the consistency model does, and its realizer side declares
the code constants at their types, gives the decoder and the code constructors
their roles, keeps the type of codes rigid, and has two facts about the decoder
(`CodesReadN`):

* **the decoder is a congruence of the generic equality**: codes it relates at
  the type of codes have decodings it relates at the universe of proofs
  (`HoldsCongruence`). Typed equality has it by the congruence of application
  (`declarative_holdsCongruence`);
* **typed constructor spines at the type of codes decode**: such a spine is a code
  constructor applied to its arguments, and its decoding is a typed weak-head
  form of a type, reached by one root step.

Then each code constant is a valid term of its declared type (`valid_codeN`):

* the type of codes is a type constant of the universe of proofs, realized by
  the types: a rigid constant reaches itself;
* implication, the quantifiers and the equation codes are closed terms of their
  carriers (`ValidTmN.carrierConst`). Their values are the meanings of the value
  side (`ValueSide.read_imp`, `ValueSide.read_all`, `ValueSide.read_eq`). Their
  realizers are Girard's clauses over the meanings of the domains, which relate
  a code constructor to itself whatever the candidates of the domains are: its
  partial applications are weak-head normal functions, and its full
  applications to related arguments are constructor spines, related as head
  spines by the generic equality (`piOver_ctor₁`, `piOver_ctor₂`);
* the decoder sends codes with one meaning to proof types with one pack, of one
  shape as leaves; its realizers send constructed terms to types: the decodings
  of related codes are related by the congruence of the decoder, and the
  decoding of a code reaching a constructor spine reaches its typed decoding,
  of a code reaching a neutral term a neutral type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization hiding World
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier World Morph Truth Read CodesRead)
open TelescopeAbstraction (subst_empty closeType applyClosed liftClosed_zero)

variable {Head L : Type} [LevelOrder L]

/-! ## The decoder as a congruence -/

/-- **The decoder is a congruence of the generic equality**: codes it relates at
the type of codes have decodings it relates at the universe of proofs. -/
def HoldsCongruence (E : GenericEquality Head) (K : Codes Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {c c' : Tm Head n}, E.convTm Γ c c' (.const K.prop) →
    E.convTm Γ (.app (.const K.holds) c) (.app (.const K.holds) c') (.head K.proofs)

/-- **Typed equality has the congruence of the decoder**, in a package that
declares the decoder at its type. -/
theorem declarative_holdsCongruence {R : Rules Head} {K : Codes Head}
    (typed : ∀ {n : Nat} {Γ : Ctx Head n},
      Typed R Γ (.const K.holds) (.pi (.const K.prop) (.head K.proofs))) :
    HoldsCongruence (declarative R) K :=
  fun equal => Derivable.appCong (B := .head K.proofs) (.refl typed) equal

/-! ## The realizers of code constructors -/

namespace RealizerSide

variable {T : RealizerSide Head L} {n : Nat} {Δ : Ctx Head n}

/-- **A constructor applied to as many arguments as it declares**, typed at one
type on both sides and compared as head spines by the generic equality, is
related by the constructed terms. -/
theorem constructed_spine {A : Tm Head n} {c : DeclName} {args args' : List (Tm Head n)}
    (role : T.roles c = .constructor args.length) (length : args'.length = args.length)
    (typed : Typed T.R Δ (appSpine (.const c) args) A)
    (typed' : Typed T.R Δ (appSpine (.const c) args') A)
    (conv : T.E.convNe Δ (appSpine (.const c) args) (appSpine (.const c) args') A) :
    (ECand.constructed T).rel Δ A (appSpine (.const c) args) (appSpine (.const c) args') := by
  have role' : T.roles c = .constructor args'.length := length ▸ role
  exact ⟨⟨typed, typed', T.laws.convTm_of_convNe (.inr (.inl ⟨c, _, args, role, rfl⟩))
      (.inr (.inl ⟨c, _, args', role', rfl⟩)) conv⟩,
    ⟨_, .refl typed, .inl ⟨c, _, args, role, rfl, rfl⟩⟩,
    ⟨_, .refl typed', .inl ⟨c, _, args', role', rfl, rfl⟩⟩⟩

/-- **A constructor of one argument is related to itself by Girard's clause into
the constructed terms**, over any candidates of its domain, at its type
`Π D. B`, with `B` not depending on the argument. -/
theorem piOver_ctor₁ {c : DeclName} {D B : Tm Head n} (role : T.roles c = .constructor 1)
    (typeA : IsType T.R Δ (.pi D (Presentation.rename wk B)))
    (typed : Typed T.R Δ (.const c) (.pi D (Presentation.rename wk B)))
    {ι : Type} (d : ι → ECand T) :
    (ECand.piOver d fun _ => ECand.constructed T).rel Δ (.pi D (Presentation.rename wk B))
      (.const c) (.const c) := by
  have fn : FunNf T Δ (.pi D (Presentation.rename wk B)) (.const c) :=
    ⟨_, .refl typed, .inr (.inr ⟨c, [], 1, .inl role, Nat.zero_lt_one, rfl⟩)⟩
  refine (ECand.piOver_rel_pi (RedTy.refl typeA)).mpr ⟨fn, fn,
    T.laws.convTm_of_convNe (.inr (.inl ⟨c, _, [], role, rfl⟩))
      (.inr (.inl ⟨c, _, [], role, rfl⟩)) (T.laws.convNe_const c typed), fun i => ?_⟩
  intro k Θ ρ world s s' hs
  have hB : ∀ t : Tm Head k,
      inst0 t (Presentation.rename (liftRen ρ) (Presentation.rename wk B)) =
        Presentation.rename ρ B := fun t => by
    rw [rename_liftRen_wk, inst0_rename_wk]
  have typedρ : Typed T.R Θ (.const c) (.pi (Presentation.rename ρ D)
      (Presentation.rename (liftRen ρ) (Presentation.rename wk B))) := typed.rename world.1
  obtain ⟨ts, ts'⟩ := (d i).typed hs
  have tl := Derivable.appElim typedρ ts
  have tr := Derivable.appElim typedρ ts'
  have conv := T.laws.convNe_app (T.laws.convNe_const c typedρ) ((d i).escape hs)
  rw [hB] at tl tr conv ⊢
  exact constructed_spine (args := [s]) (args' := [s']) role rfl tl tr conv

/-- **A constructor of two arguments is related to itself by Girard's clause
into Girard's clause into the constructed terms**, over any candidates of its
domains, at its type `Π D. Π D'. B`, with `D'` and `B` not depending on the
arguments. -/
theorem piOver_ctor₂ {c : DeclName} {D D' B : Tm Head n} (role : T.roles c = .constructor 2)
    (typeA : IsType T.R Δ (.pi D (Presentation.rename wk (.pi D' (Presentation.rename wk B)))))
    (typed : Typed T.R Δ (.const c)
      (.pi D (Presentation.rename wk (.pi D' (Presentation.rename wk B)))))
    {ι κ : Type} (d : ι → ECand T) (d' : κ → ECand T) :
    (ECand.piOver d fun _ => ECand.piOver d' fun _ => ECand.constructed T).rel Δ
      (.pi D (Presentation.rename wk (.pi D' (Presentation.rename wk B)))) (.const c)
        (.const c) := by
  have fn : FunNf T Δ (.pi D (Presentation.rename wk (.pi D' (Presentation.rename wk B))))
      (.const c) :=
    ⟨_, .refl typed, .inr (.inr ⟨c, [], 2, .inl role, Nat.zero_lt_two, rfl⟩)⟩
  refine (ECand.piOver_rel_pi (RedTy.refl typeA)).mpr ⟨fn, fn,
    T.laws.convTm_of_convNe (.inr (.inl ⟨c, _, [], role, rfl⟩))
      (.inr (.inl ⟨c, _, [], role, rfl⟩)) (T.laws.convNe_const c typed), fun i => ?_⟩
  intro k Θ ρ world s s' hs
  have hB : ∀ t : Tm Head k,
      inst0 t (Presentation.rename (liftRen ρ)
        (Presentation.rename wk (.pi D' (Presentation.rename wk B)))) =
        Presentation.rename ρ (.pi D' (Presentation.rename wk B)) := fun t => by
    rw [rename_liftRen_wk, inst0_rename_wk]
  have typedρ : Typed T.R Θ (.const c) (.pi (Presentation.rename ρ D)
      (Presentation.rename (liftRen ρ)
        (Presentation.rename wk (.pi D' (Presentation.rename wk B))))) := typed.rename world.1
  obtain ⟨ts, ts'⟩ := (d i).typed hs
  have tl := Derivable.appElim typedρ ts
  have tr := Derivable.appElim typedρ ts'
  have conv := T.laws.convNe_app (T.laws.convNe_const c typedρ) ((d i).escape hs)
  rw [hB] at tl tr conv ⊢
  -- The partial application: again a weak-head normal function.
  have typeB : IsType T.R Θ (Presentation.rename ρ (.pi D' (Presentation.rename wk B))) := by
    obtain ⟨-, typeCod⟩ := IsType.pi_parts typeA
    obtain ⟨v, hv, tCod⟩ := typeCod
    have h := Typed.instantiate (tCod.rename (CtxRen.snoc world.1 D)) ts
    rw [hB] at h
    exact ⟨v, hv, h⟩
  have fn₁ : ∀ {t : Tm Head k}, Typed T.R Θ (.app (.const c) t)
      (Presentation.rename ρ (.pi D' (Presentation.rename wk B))) →
      FunNf T Θ (Presentation.rename ρ (.pi D' (Presentation.rename wk B))) (.app (.const c) t) :=
    fun {t} typing => ⟨_, .refl typing, .inr (.inr ⟨c, [t], 2, .inl role, Nat.one_lt_two, rfl⟩)⟩
  refine (ECand.piOver_rel_pi (RedTy.refl typeB)).mpr ⟨fn₁ tl, fn₁ tr,
    T.laws.convTm_of_convNe (.inr (.inl ⟨c, _, [s], role, rfl⟩))
      (.inr (.inl ⟨c, _, [s'], role, rfl⟩)) conv, fun j => ?_⟩
  intro k' Θ' ρ' world' u u' hu
  have hB' : ∀ t : Tm Head k',
      inst0 t (Presentation.rename (liftRen ρ') (Presentation.rename (liftRen ρ)
        (Presentation.rename wk B))) = Presentation.rename ρ' (Presentation.rename ρ B) :=
    fun t => by rw [rename_liftRen_wk, rename_liftRen_wk, inst0_rename_wk]
  have typedρ' : Typed T.R Θ' (Presentation.rename ρ' (.app (.const c) s))
      (.pi (Presentation.rename ρ' (Presentation.rename ρ D'))
        (Presentation.rename (liftRen ρ') (Presentation.rename (liftRen ρ)
          (Presentation.rename wk B)))) := Typed.rename tl world'.1
  have typedρ'' : Typed T.R Θ' (Presentation.rename ρ' (.app (.const c) s'))
      (.pi (Presentation.rename ρ' (Presentation.rename ρ D'))
        (Presentation.rename (liftRen ρ') (Presentation.rename (liftRen ρ)
          (Presentation.rename wk B)))) := Typed.rename tr world'.1
  obtain ⟨tu, tu'⟩ := (d' j).typed hu
  have tl' := Derivable.appElim typedρ' tu
  have tr' := Derivable.appElim typedρ'' tu'
  have conv' := T.laws.convNe_app (T.laws.convNe_rename world'.1 world'.2 conv)
    ((d' j).escape hu)
  rw [hB'] at tl' tr' conv' ⊢
  exact constructed_spine (args := [Presentation.rename ρ' s, u])
    (args' := [Presentation.rename ρ' s', u']) role rfl tl' tr' conv'

end RealizerSide

/-! ## Packages of codes read by the conversion model -/

variable {M : NModel Head L}

/-- **A package of proposition codes read by the conversion model**: the value side
reads it as the consistency model does; the realizer side declares the code
constants at their types, gives the decoder and the code constructors their
roles, keeps the type of codes rigid, has the universe of proofs, has the
decoder as a congruence of its generic equality, and decodes its typed
constructor spines at the type of codes, by one root step, to typed weak-head
forms of types. -/
structure CodesReadN (M : NModel Head L) (K : Codes Head) : Prop where
  read : CodesRead M.toModel K
  typed : ∀ {c : DeclName} {T : Tm Head 0}, K.codeType c = some T →
    Typed M.side.R .nil (.const c) T
  decoderRoles : DecoderRoles M.side.roles K.decoders
  propRigid : M.side.roles K.prop = .rigid
  proofs : M.side.R.isUniverse K.proofs
  holds : HoldsCongruence M.side.E K
  decodes : ∀ {n : Nat} {Δ : Ctx Head n} {k : DeclName} {args : List (Tm Head n)},
    CtxFormed M.side.R Δ → Typed M.side.R Δ (appSpine (.const k) args) (.const K.prop) →
      M.side.roles k = .constructor args.length →
      ∃ D, M.side.R.computation.step (.app (.const K.holds) (appSpine (.const k) args)) D ∧
        IsTypeForm M.side.roles D ∧ Typed M.side.R Δ D (.head K.proofs)

/-! ## Closed constants at carriers -/

/-- **A closed term with one meaning at an interpretable carrier, in every world,
is a valid term of the carrier's type** when that type is valid and the term's
realizer instances are related by the realizers of the meaning at every formed
context. -/
theorem ValidTmN.carrierConst (laws : M.Laws) {k : Kind} {C : Carrier k}
    (hC : C.Interpretable M.toModel) (validType : ValidTyN M .nil (C.term M.toModel))
    {c : Tm Head 0} {v : C.V M.reading}
    (read : ∀ {m : Nat} (ξ : World M.reading m), Read M.reading ξ (liftClosed c) C v)
    (real : ∀ {r : Nat} {Δ : Ctx Head r}, CtxFormed M.side.R Δ →
      IsType M.side.R Δ (liftClosed (C.term M.toModel)) →
      ((ecandAlgebra M.side).Real M.toSetting M.star M.num C v).rel Δ
        (liftClosed (C.term M.toModel)) (liftClosed c) (liftClosed c)) :
    ValidTmN M .nil c (C.term M.toModel) := by
  refine ⟨validType, fun {_ _ ξ _ _ _ _ _} e {P} d => ?_⟩
  obtain ⟨-, -, -, types⟩ := validType e
  rw [subst_empty] at d types
  obtain ⟨rel, hreal⟩ := ValueSide.carrier_closed laws.value hC read ξ d
  simp only [subst_empty]
  refine ⟨rel, ?_⟩
  rw [hreal]
  exact real e.formed types.left

/-! ## The code constants -/

section Codes

variable (laws : M.Laws) {K : Codes Head} (read : CodesReadN M K)
include laws read

/-- **The type of codes is a valid term of the universe of proofs**: a type
constant, of one shape with itself, realized by the types as a rigid constant
reaching itself. -/
theorem valid_propN : ValidTmN M .nil (.const K.prop) (.head K.proofs) := by
  have proofs := read.read.proofs
  refine ⟨ValidTyN.sort proofs read.proofs, fun {m r ξ σ σ' Δ ς ς'} _ {P} d => ?_⟩
  rw [subst_empty] at d
  change DenN M ξ (.head K.proofs) P at d
  rw [ValueSide.DenS.sort_inv laws.value proofs d]
  simp only [subst_empty]
  have typed : Typed M.side.R Δ (.const K.prop) (.head K.proofs) :=
    Typed.liftClosed (Δ := Δ) (read.typed K.codeType_prop)
  have neutral : Neutral M.side.roles (.const K.prop : Tm Head r) :=
    .rigid (args := []) read.propRigid
  have form : IsTypeForm M.side.roles (.const K.prop : Tm Head r) :=
    .inr (.inr (.inr (.inr (.inl neutral))))
  refine ⟨fun {_ ξ' _} _ => ?_, ⟨typed, typed, M.side.laws.convTm_of_convNe (.inl neutral)
    (.inl neutral) (M.side.laws.convNe_const K.prop typed)⟩, ⟨_, .refl typed, form⟩,
    ⟨_, .refl typed, form⟩⟩
  change ∃ Q, ValueSide.InterpAt M.value _ ξ' (.const K.prop) Q ∧
    ValueSide.InterpAt M.value _ ξ' (.const K.prop) Q ∧
      ValueSide.Shape M.value (ValueSide.InterpAt M.value _) .pair ξ' (.const K.prop)
        (.const K.prop)
  rw [read.read.prop]
  exact ⟨_, ValueSide.SInterp.prop .refl, ValueSide.SInterp.prop .refl,
    .const (.inl rfl) .refl .refl⟩

omit laws in
/-- **The decoding of a constructed code reaches a weak-head form of a type**:
a code reaching a constructor spine reaches its typed decoding, and a code
reaching a neutral term a neutral type. -/
theorem holds_reaches {r : Nat} {Δ : Ctx Head r} (formed : CtxFormed M.side.R Δ)
    (typedHolds : Typed M.side.R Δ (.const K.holds) (.pi (.const K.prop) (.head K.proofs)))
    {c w : Tm Head r} (red : RedTm M.side.R M.side.roles Δ c w (.const K.prop))
    (form : IsCtorForm M.side.roles w) :
    ReachesForm M.side (typeForms M.side.roles) Δ (.head K.proofs)
      (.app (.const K.holds) c) := by
  have holdsRole : M.side.roles K.holds = .computes 1 (.split 0 .constructor fun _ => .leaf) :=
    read.decoderRoles.holds
  have decoded : RedTm M.side.R M.side.roles Δ (.app (.const K.holds) c)
      (.app (.const K.holds) w) (.head K.proofs) :=
    ⟨WhRed.scrutinee (before := []) (after := []) holdsRole rfl red.red,
      .appElim typedHolds red.source, .appElim typedHolds red.target,
      Derivable.appCong (B := .head K.proofs) (.refl typedHolds) red.equal⟩
  rcases form with ⟨k, a, args, role, length, rfl⟩ | neutral
  · obtain ⟨D, step, formD, typedD⟩ :=
      read.decodes formed red.target (length ▸ role)
    exact ⟨D, decoded.trans (RedTm.root step decoded.target typedD), formD⟩
  · exact ⟨_, decoded, .inr (.inr (.inr (.inr (.inl
      (Neutral.stuck_single (before := []) (after := []) holdsRole rfl neutral)))))⟩

/-- **The decoder is a valid term of `prop → U`**, for the universe of proofs
`U`: codes with one meaning decode to proof types with one pack and one shape as
leaves, and constructed codes decode to types that its congruence relates. -/
theorem valid_holdsN (declared : K.codeType K.holds = some K.holdsType)
    (validType : ValidTyN M .nil K.holdsType) (partsType : StructuredN M .nil K.holdsType) :
    ValidTmN M .nil (.const K.holds) K.holdsType := by
  have proofs := read.read.proofs
  have holdsRole : M.side.roles K.holds = .computes 1 (.split 0 .constructor fun _ => .leaf) :=
    read.decoderRoles.holds
  refine ValidTmN.close laws (.snoc .nil (.const K.prop)) (C := .head K.proofs)
    (f := .const K.holds) validType partsType (read.typed declared)
    (fun args short => .inr (.inr ⟨K.holds, args, 1, .inr ⟨_, holdsRole⟩, short, rfl⟩))
    ⟨ValidTyN.sort proofs read.proofs, fun {m r ξ σ σ' Δ ς ς'} e {P} den => ?_⟩
  have formed := e.formed
  obtain ⟨-, RA, denA, hx, rx⟩ := e
  change DenN M ξ (.const K.prop) RA at denA
  change RA.rel (σ 0) (σ' 0) at hx
  change (RA.real (σ 0)).rel Δ (.const K.prop) (ς 0) (ς' 0) at rx
  change DenN M ξ (.head K.proofs) P at den
  rw [read.read.prop] at denA
  obtain rfl := ValueSide.DenS.prop_inv laws.value denA
  rw [ValueSide.DenS.sort_inv laws.value proofs den]
  show (ValueSide.universePack M.value (ValueSide.InterpAt M.value (M.levels.level K.proofs))
      ξ).rel (.app (.const K.holds) (σ 0)) (.app (.const K.holds) (σ' 0)) ∧
    (ECand.types M.side).rel Δ (.head K.proofs) (.app (.const K.holds) (ς 0))
      (.app (.const K.holds) (ς' 0))
  obtain ⟨X, ta, tb⟩ := hx
  have typedHolds : Typed M.side.R Δ (.const K.holds) (.pi (.const K.prop) (.head K.proofs)) :=
    Typed.liftClosed (Δ := Δ) (read.typed declared)
  obtain ⟨⟨t₀, t₀', conv⟩, ⟨w, red, form⟩, ⟨w', red', form'⟩⟩ := rx
  refine ⟨fun {_ ξ' ρ} w₁ => ?_, ⟨⟨.appElim typedHolds t₀, .appElim typedHolds t₀',
    read.holds conv⟩, holds_reaches read formed typedHolds red form,
    holds_reaches read formed typedHolds red' form'⟩⟩
  have holdsAt : ∀ {c : Tm Head _}, Truth M.reading ξ' c X →
      ValueSide.InterpAt M.value (M.levels.level K.proofs) ξ' (.app (.const K.holds) c)
          (ValueSide.holdsPack M.value _ X) ∧
        ValueSide.Shape M.value (ValueSide.InterpAt M.value (M.levels.level K.proofs)) .total ξ'
          (.app (.const K.holds) c) (.app (.const K.holds) c) := by
    intro c truth
    rw [read.read.holds]
    exact ⟨ValueSide.SInterp.holds .refl truth,
      ValueSide.Shape.holds laws.value (ValueSide.SInterp.holds .refl truth)⟩
  obtain ⟨ha, sa⟩ := holdsAt (ta.rename w₁)
  obtain ⟨hb, sb⟩ := holdsAt (tb.rename w₁)
  exact ⟨_, ha, hb, .total sa sb⟩

/-- **Implication is a valid term of `prop → prop → prop`**: it means the function
space of the meanings of its arguments, and it is realized by Girard's clauses
into the constructed terms. -/
theorem valid_impN (declared : K.codeType K.imp = some K.impType)
    (validType : ValidTyN M .nil K.impType) : ValidTmN M .nil (.const K.imp) K.impType := by
  have form : K.impType = (Carrier.arr .prop (.arr .prop .prop) : Carrier .gen).term M.toModel := by
    rw [show K.impType = .pi (.const K.prop) (.pi (.const K.prop) (.const K.prop)) from rfl,
      read.read.prop]
    rfl
  have typed := read.typed declared
  rw [form] at validType typed ⊢
  refine ValidTmN.carrierConst laws (.arr .prop (.arr .prop .prop)) validType
    (v := fun X Y => M.reading.impMeaning X Y) (fun ξ => ?_) (fun {r Δ} _ typeA => ?_)
  · exact ValueSide.read_imp (V := M.value) read.read ξ
  · exact RealizerSide.piOver_ctor₂ (D := .const M.prop) (D' := .const M.prop)
      (B := .const M.prop) (read.decoderRoles.imp) typeA (Typed.liftClosed (Δ := Δ) typed) _ _

/-- **A quantifier instance is a valid term of `(A → prop) → prop`**: it means
Girard's clause at its carrier over the meanings of its argument, and it is
realized by Girard's clause into the constructed terms. -/
theorem valid_allN {a : DeclName} {T : Tm Head 0} (carrier : K.quantifiers a = some T)
    (declared : K.codeType a = some (K.allType T)) (validType : ValidTyN M .nil (K.allType T)) :
    ValidTmN M .nil (.const a) (K.allType T) := by
  have role := read.decoderRoles.all carrier
  obtain ⟨k, A, carrierM, hA, rfl⟩ := read.read.all carrier
  have form : K.allType (A.term M.toModel) =
      (Carrier.arr (.arr A .prop) .prop : Carrier .gen).term M.toModel := by
    rw [show K.allType (A.term M.toModel) = .pi (.pi (A.term M.toModel) (.const K.prop))
      (.const K.prop) from rfl, read.read.prop]
    rfl
  have typed := read.typed declared
  rw [form] at validType typed ⊢
  refine ValidTmN.carrierConst laws (.arr (.arr hA .prop) .prop) validType
    (v := fun φ => M.reading.allMeaning A φ) (fun ξ => ValueSide.read_all (V := M.value) carrierM ξ)
    (fun {r Δ} _ typeA => ?_)
  exact RealizerSide.piOver_ctor₁ (D := liftClosed ((Carrier.arr A .prop).term M.toModel))
    (B := .const M.prop) role typeA (Typed.liftClosed (Δ := Δ) typed) _

/-- **An equation instance is a valid term of `A → A → prop`**: it means the
identity candidate of the equality of the meanings of its arguments, and it is
realized by Girard's clauses into the constructed terms. -/
theorem valid_eqN {e : DeclName} {T : Tm Head 0} (carrier : K.equationCarrier e = some T)
    (declared : K.codeType e = some (K.eqType T)) (validType : ValidTyN M .nil (K.eqType T)) :
    ValidTmN M .nil (.const e) (K.eqType T) := by
  have role := read.decoderRoles.eq carrier
  obtain ⟨k, A, carrierM, hA, rfl⟩ := read.read.eq carrier
  have form : K.eqType (A.term M.toModel) =
      (Carrier.arr A (.arr A .prop) : Carrier .gen).term M.toModel := by
    rw [show K.eqType (A.term M.toModel) = .pi (A.term M.toModel)
      (.pi (Presentation.rename wk (A.term M.toModel)) (.const K.prop)) from rfl, read.read.prop]
    rfl
  have typed := read.typed declared
  rw [form] at validType typed ⊢
  refine ValidTmN.carrierConst laws (.arr hA (.arr hA .prop)) validType
    (v := fun x y => M.reading.eqMeaning A x y) (fun ξ => ValueSide.read_eq (V := M.value) carrierM ξ)
    (fun {r Δ} _ typeA => ?_)
  have lifted : (liftClosed ((Carrier.arr A (.arr A .prop) : Carrier .gen).term M.toModel) :
      Tm Head r) = .pi (liftClosed (A.term M.toModel)) (Presentation.rename wk
        (.pi (liftClosed (A.term M.toModel)) (Presentation.rename wk (.const M.prop)))) := by
    change (liftClosed (.pi (A.term M.toModel) (Presentation.rename wk (.pi (A.term M.toModel)
      (Presentation.rename wk (.const M.prop))))) : Tm Head r) = _
    rw [Consistency.liftClosed_arrow, Consistency.liftClosed_arrow]
    rfl
  have typed' := Typed.liftClosed (Δ := Δ) typed
  rw [lifted] at typeA typed' ⊢
  exact RealizerSide.piOver_ctor₂ role typeA typed' _ _

/-- **Every code constant is a valid term of its declared type**, when the
declared types are valid with valid parts. -/
theorem valid_codeN
    (types : ∀ {c : DeclName} {T : Tm Head 0}, K.codeType c = some T →
      ValidTyN M .nil T ∧ StructuredN M .nil T)
    {c : DeclName} {T : Tm Head 0} (declared : K.codeType c = some T) :
    ValidTmN M .nil (.const c) T := by
  obtain ⟨validType, partsType⟩ := types declared
  have declared₀ := declared
  unfold Codes.codeType at declared
  by_cases hp : c = K.prop
  · rw [if_pos hp] at declared
    cases declared
    rw [hp]
    exact valid_propN laws read
  rw [if_neg hp] at declared
  by_cases hh : c = K.holds
  · rw [if_pos hh] at declared
    cases declared
    subst hh
    exact valid_holdsN laws read declared₀ validType partsType
  rw [if_neg hh] at declared
  by_cases hi : c = K.imp
  · rw [if_pos hi] at declared
    cases declared
    subst hi
    exact valid_impN laws read declared₀ validType
  rw [if_neg hi] at declared
  cases carrier : K.quantifiers c with
  | some A =>
      rw [carrier] at declared
      cases declared
      exact valid_allN laws read carrier declared₀ validType
  | none =>
      rw [carrier] at declared
      cases equation : K.equationCarrier c with
      | none => rw [equation] at declared; cases declared
      | some A =>
          rw [equation] at declared
          cases declared
          exact valid_eqN laws read equation declared₀ validType

end Codes


end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
