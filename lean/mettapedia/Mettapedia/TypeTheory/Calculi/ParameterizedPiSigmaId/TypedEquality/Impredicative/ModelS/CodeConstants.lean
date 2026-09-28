import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Formation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.CodeReading

/-!
# The code constants in model S

A package of proposition codes is read by model S when its value side reads it
as the consistency model does, its realizer side decodes it, the type of codes
does not compute on the realizer side, and the closed types of the
interpretable carriers are strongly normalizing there. Then each code constant
is a valid term of its declared type.

The declared types of implication, the quantifiers and the equation codes are
carriers, so validity comes down to two facts: the constant has a meaning at
the carrier, and it realizes that meaning. A meaning of a carrier is realized
by `Real` of the realizer algebra, whose function carriers are Girard's clause
over the meanings of the domain; over the Kripke candidates, and an inhabited
index, that is membership in every function space (`mem_piOver`).

* Implication means the Kripke function space of its arguments' meanings, and
  it sends realizers of codes to realizers of codes.
* `all@A` means Girard's clause at `A`, and it sends a family whose
  applications are realizers of codes to a realizer of codes.
* `eq@A` means the identity candidate of the equality of its arguments'
  meanings, and it sends strongly normalizing arguments to realizers of codes.

The type of codes is a type constant, of one shape with itself. The decoder
sends codes with one meaning to proof types with one pack, and of one shape as
leaves; its realizers send realizers of codes to strongly normalizing terms,
which is the definition of a realizer of codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier World Morph Truth Read CodesRead)
open StrongNormalization
open TelescopeAbstraction (subst_empty)
open ValueSide

variable {Head L : Type} [LevelOrder L] {M : SModel Head L}

/-- A package of proposition codes read by model S. -/
structure CodesReadS (M : SModel Head L) (K : Codes Head) : Prop where
  read : CodesRead M.toModel K
  decoders : M.realizers.decoders = K.decoders
  propStuck : ∀ arity scrutinee, M.realizers.roles K.prop ≠ .computes arity scrutinee
  carrierSN : ∀ {k : Kind} {C : Carrier k}, C.Interpretable M.toModel →
    SN M.realizers.rules (C.term M.toModel)

/-! ## Girard's clause over the Kripke candidates -/

/-- Girard's clause of the Kripke candidates over an inhabited index: the terms
that are in every function space from `d i` to `c i`. -/
theorem mem_piOver {ι : Type} (i₀ : ι) (d c : ι → M.Cand) {r : Nat} {t : Tm Head r} :
    ((kcandAlgebra M.realizers).piOver d c).mem t ↔
      ∀ (i : ι) {m : Nat} (ρ : Ren r m) (u : Tm Head m), (d i).mem u →
        (c i).mem (.app (Presentation.rename ρ t) u) := by
  rw [kcand_piOver_eq_pi M.realizers i₀ d c]
  exact Iff.rfl

/-! ## Closed constants at carriers -/

/-- A closed term with one meaning at an interpretable carrier, in every world,
that realizes this meaning is a valid term of the carrier's type. -/
theorem ValidTmS.carrierConst (laws : M.Laws) {k : Kind} {C : Carrier k}
    (hC : C.Interpretable M.toModel) (sn : SN M.realizers.rules (C.term M.toModel))
    {c : Tm Head 0} {v : C.V M.reading}
    (read : ∀ {m : Nat} (ξ : World M.reading m), Read M.reading ξ (liftClosed c) C v)
    (real : ∀ {r : Nat},
      (M.value.alg.Real M.value.toSetting M.value.star M.value.num C v).mem
        (liftClosed c : Tm Head r)) :
    ValidTmS M .nil c (C.term M.toModel) := by
  have den : ∀ {m : Nat} (ξ : World M.reading m),
      DenS M.value ξ (liftClosed (C.term M.toModel)) (carrierPack M.value C ξ) :=
    fun ξ => ⟨LevelOrder.bot, carrier_interp laws.value hC ξ⟩
  refine ⟨fun {_ _ ξ _ _ _} _ => ?_, fun {_ _ ξ _ _ _} _ {P} d => ?_⟩
  · rw [subst_empty, subst_empty, subst_empty]
    exact ⟨_, den ξ, den ξ, SN.rename M.realizers.reflects Fin.elim0 sn⟩
  · rw [subst_empty] at d
    obtain ⟨rel, hreal⟩ := carrier_closed laws.value hC read ξ d
    rw [subst_empty, subst_empty, subst_empty, hreal]
    exact ⟨rel, real⟩

/-- A closed term is a valid term of a closed type with a strongly normalizing
realizer instance, when the type has one pack at each world whose value
relation relates the term to itself and whose realizers of the term contain
it. -/
theorem ValidTmS.closed (laws : M.Laws) {c T : Tm Head 0} (sn : SN M.realizers.rules T)
    {D : ∀ {m : Nat}, World M.reading m → Pack M.value m}
    (den : ∀ {m : Nat} (ξ : World M.reading m), DenS M.value ξ (liftClosed T) (D ξ))
    (rel : ∀ {m : Nat} (ξ : World M.reading m), (D ξ).rel (liftClosed c) (liftClosed c))
    (real : ∀ {m : Nat} (ξ : World M.reading m) {r : Nat},
      ((D ξ).real (liftClosed c)).mem (liftClosed c : Tm Head r)) :
    ValidTmS M .nil c T := by
  refine ⟨fun {_ _ ξ _ _ _} _ => ?_, fun {_ _ ξ _ _ _} _ {P} d => ?_⟩
  · rw [subst_empty, subst_empty, subst_empty]
    exact ⟨_, den ξ, den ξ, SN.rename M.realizers.reflects Fin.elim0 sn⟩
  · rw [subst_empty] at d
    obtain rfl := DenS.deterministic laws.value d (den ξ)
    rw [subst_empty, subst_empty, subst_empty]
    exact ⟨rel ξ, real ξ⟩

section Read

variable {K : Codes Head} (read : CodesReadS M K)
include read

theorem CodesReadS.holds_eq : M.realizers.decoders.holds = K.holds := by
  rw [read.decoders]
  rfl

theorem CodesReadS.imp_eq : M.realizers.decoders.imp = K.imp := by
  rw [read.decoders]
  rfl

theorem CodesReadS.all_eq {a : DeclName} {T : Tm Head 0} (carrier : K.quantifiers a = some T) :
    M.realizers.decoders.allCarrier a = some T := by
  rw [read.decoders]
  exact carrier

theorem CodesReadS.eq_eq {e : DeclName} {T : Tm Head 0}
    (carrier : K.equationCarrier e = some T) : M.realizers.decoders.eqCarrier e = some T := by
  rw [read.decoders]
  exact carrier

/-- The type of codes does not compute on the realizer side, so it is strongly
normalizing in every scope. -/
theorem CodesReadS.prop_sn {n : Nat} : SN M.realizers.rules (.const K.prop : Tm Head n) :=
  SN.constSpine M.realizers.shape (args := [])
    (fun arity scrutinee role => absurd role (read.propStuck arity scrutinee)) (by simp)

end Read

section Laws

variable (laws : M.Laws) {K : Codes Head} (read : CodesReadS M K)
include laws read

/-! ## Implication -/

/-- Implication is a valid term of `prop → prop → prop`. -/
theorem valid_impS : ValidTmS M .nil (.const K.imp) K.impType := by
  have form : K.impType =
      (Carrier.arr .prop (.arr .prop .prop) : Carrier .gen).term M.toModel := by
    rw [show K.impType = .pi (.const K.prop) (.pi (.const K.prop) (.const K.prop)) from rfl,
      read.read.prop]
    rfl
  rw [form]
  have hC : (Carrier.arr .prop (.arr .prop .prop) : Carrier .gen).Interpretable M.toModel :=
    .arr .prop (.arr .prop .prop)
  refine ValidTmS.carrierConst laws hC (read.carrierSN hC)
    (v := fun X Y => M.reading.impMeaning X Y) (fun ξ => ?_) (fun {r} => ?_)
  · exact read_imp (V := M.value) read.read ξ
  · show ((kcandAlgebra M.realizers).piOver _ _).mem _
    refine (mem_piOver M.realizers.sn _ _).mpr fun X m ρ u hu => ?_
    show ((kcandAlgebra M.realizers).piOver _ _).mem _
    refine (mem_piOver M.realizers.sn _ _).mpr fun Y m' ρ' u' hu' => ?_
    change (M.realizers.codes).mem (.app (.app (.const K.imp) (Presentation.rename ρ' u)) u')
    rw [← read.imp_eq]
    exact CodeReal.imp_mem M.realizers.shape M.realizers.reflects M.realizers.decoderRoles
      M.realizers.decodes ((M.realizers.codes).rename ρ' hu) hu'

/-! ## Quantifiers -/

/-- A quantifier instance is a valid term of `(A → prop) → prop`. -/
theorem valid_allS {a : DeclName} {T : Tm Head 0} (carrier : K.quantifiers a = some T) :
    ValidTmS M .nil (.const a) (K.allType T) := by
  obtain ⟨k, A, carrierM, hA, rfl⟩ := read.read.all carrier
  have form : K.allType (A.term M.toModel) =
      (Carrier.arr (.arr A .prop) .prop : Carrier .gen).term M.toModel := by
    rw [show K.allType (A.term M.toModel) = .pi (.pi (A.term M.toModel) (.const K.prop))
      (.const K.prop) from rfl, read.read.prop]
    rfl
  rw [form]
  have hC : (Carrier.arr (.arr A .prop) .prop : Carrier .gen).Interpretable M.toModel :=
    .arr (.arr hA .prop) .prop
  refine ValidTmS.carrierConst laws hC (read.carrierSN hC)
    (v := fun φ => M.reading.allMeaning A φ) (fun ξ => ?_) (fun {r} => ?_)
  · exact read_all (V := M.value) carrierM ξ
  · have point := Realizability.point M.toSetting M.star M.realizers.sn A
    show ((kcandAlgebra M.realizers).piOver _ _).mem _
    refine (mem_piOver (fun _ => M.realizers.sn) _ _).mpr fun φ m ρ u hu => ?_
    have family := (mem_piOver point _ _).mp hu
    exact CodeReal.all_mem M.realizers.shape M.realizers.reflects M.realizers.decoderRoles
      M.realizers.decodes (read.all_eq carrier) (read.carrierSN hA)
      (family point wk (.var 0) (KCand.var_mem (RootShape.spineHeaded M.realizers.shape) _ 0))

/-! ## Equations -/

/-- An equation instance is a valid term of `A → A → prop`. -/
theorem valid_eqS {e : DeclName} {T : Tm Head 0} (carrier : K.equationCarrier e = some T) :
    ValidTmS M .nil (.const e) (K.eqType T) := by
  obtain ⟨k, A, carrierM, hA, rfl⟩ := read.read.eq carrier
  have form : K.eqType (A.term M.toModel) =
      (Carrier.arr A (.arr A .prop) : Carrier .gen).term M.toModel := by
    rw [show K.eqType (A.term M.toModel) = .pi (A.term M.toModel)
      (.pi (Presentation.rename wk (A.term M.toModel)) (.const K.prop)) from rfl,
      read.read.prop]
    rfl
  rw [form]
  have hC : (Carrier.arr A (.arr A .prop) : Carrier .gen).Interpretable M.toModel :=
    .arr hA (.arr hA .prop)
  refine ValidTmS.carrierConst laws hC (read.carrierSN hC)
    (v := fun x y => M.reading.eqMeaning A x y) (fun ξ => ?_) (fun {r} => ?_)
  · exact read_eq (V := M.value) carrierM ξ
  · have point := Realizability.point M.toSetting M.star M.realizers.sn A
    show ((kcandAlgebra M.realizers).piOver _ _).mem _
    refine (mem_piOver point _ _).mpr fun x m ρ u hu => ?_
    show ((kcandAlgebra M.realizers).piOver _ _).mem _
    refine (mem_piOver point _ _).mpr fun y m' ρ' u' hu' => ?_
    exact CodeReal.eq_mem M.realizers.shape M.realizers.reflects M.realizers.decoderRoles
      M.realizers.decodes (read.eq_eq carrier) (read.carrierSN hA)
      (SN.rename M.realizers.reflects ρ' (KCand.sn _ hu)) (KCand.sn _ hu')

/-! ## The type of codes and the decoder -/

/-- The type of codes is a valid term of the universe of proofs: a type
constant, of one shape with itself. -/
theorem valid_propS : ValidTmS M .nil (.const K.prop) (.head K.proofs) := by
  have proofs := read.read.proofs
  refine ⟨ValidTyS.sort proofs, fun {_ _ ξ _ _ _} _ {P} d => ?_⟩
  rw [subst_empty] at d
  change DenS M.value ξ (.head K.proofs) P at d
  rw [DenS.sort_inv laws proofs d]
  rw [subst_empty, subst_empty, subst_empty]
  refine ⟨fun {_ ξ' _} _ => ?_, SN.rename M.realizers.reflects Fin.elim0 read.prop_sn⟩
  change ∃ Q, InterpAt M.value _ ξ' (.const K.prop) Q ∧ InterpAt M.value _ ξ' (.const K.prop) Q ∧
    Shape M.value (InterpAt M.value _) .pair ξ' (.const K.prop) (.const K.prop)
  rw [read.read.prop]
  exact ⟨_, SInterp.prop .refl, SInterp.prop .refl, .const (.inl rfl) .refl .refl⟩

/-- The decoder is a valid term of `prop → U`, for the universe of proofs `U`:
codes with one meaning decode to proof types with one pack and one shape, and a
realizer of codes decodes to a strongly normalizing type. -/
theorem valid_holdsS : ValidTmS M .nil (.const K.holds) K.holdsType := by
  have proofs := read.read.proofs
  let k := M.levels.level K.proofs
  let P : ∀ {m : Nat} (ξ : World M.reading m), ValueSide.PiPack M.value ξ := fun ξ =>
    PiPack.arrow ξ (fun ξ' => carrierPack M.value .prop ξ')
      (fun ξ' => universePack M.value (InterpAt M.value k) ξ')
  have form : ∀ {m : Nat}, (liftClosed K.holdsType : Tm Head m) =
      .pi (.const M.prop) (.head K.proofs) := by
    intro m
    rw [← read.read.prop]
    rfl
  have interp : ∀ {m : Nat} (ξ : World M.reading m),
      InterpAt M.value (LevelOrder.succ k) ξ (liftClosed K.holdsType) (P ξ).piPack := by
    intro m ξ
    rw [form]
    exact SInterp.pi .refl (P ξ) (fun {_ _ _} _ => SInterp.prop .refl)
      (fun {_ ξ' _} _ {_} _ => InterpAt.sort proofs (LevelOrder.lt_succ k) ξ')
      (fun {_ _ _} _ {_ _} _ _ _ => rfl)
  have den : ∀ {m : Nat} (ξ : World M.reading m),
      DenS M.value ξ (liftClosed K.holdsType) (P ξ).piPack := fun ξ => ⟨_, interp ξ⟩
  -- A decoding of a code with a meaning is a leaf at the level of the universe of proofs.
  have holdsAt : ∀ {m : Nat} (ξ : World M.reading m) {c : Tm Head m} {X : M.value.alg.Cand},
      Truth M.reading ξ c X →
        InterpAt M.value k ξ (.app (.const K.holds) c) (holdsPack M.value m X) ∧
          Shape M.value (InterpAt M.value k) .total ξ (.app (.const K.holds) c)
            (.app (.const K.holds) c) := by
    intro m ξ c X truth
    rw [read.read.holds]
    exact ⟨SInterp.holds .refl truth, Shape.holds laws.value (SInterp.holds .refl truth)⟩
  have holdsSN : ∀ {r : Nat}, SN M.realizers.rules (.const K.holds : Tm Head r) := by
    intro r
    rw [← read.holds_eq]
    exact SN.intro fun v step =>
      absurd step (holds_normal M.realizers.shape M.realizers.decoderRoles v)
  refine ⟨fun {_ _ ξ _ _ _} _ => ?_, fun {_ _ ξ _ _ _} _ {Q} d => ?_⟩
  · rw [subst_empty, subst_empty, subst_empty]
    refine ⟨_, den ξ, den ξ, ?_⟩
    rw [form, ← read.read.prop]
    exact SN.pi (RootShape.spineHeaded M.realizers.shape) read.prop_sn
      (SN.head (RootShape.spineHeaded M.realizers.shape) _)
  · rw [subst_empty] at d
    obtain rfl := DenS.deterministic laws.value d (den ξ)
    rw [subst_empty, subst_empty, subst_empty]
    refine ⟨fun {_ ξ' ρ} w {a b} _ hab => ?_, (PiPack.mem_real _).mpr ⟨holdsSN, ?_⟩⟩
    · obtain ⟨X, ta, tb⟩ := hab
      intro _ ξ'' ρ' w'
      obtain ⟨ha, sa⟩ := holdsAt ξ'' (ta.rename w')
      obtain ⟨hb, sb⟩ := holdsAt ξ'' (tb.rename w')
      exact ⟨holdsPack M.value _ X, ha, hb, .total sa sb⟩
    · intro _ ξ' ρ w a _ _ ρr u hu
      change SN M.realizers.rules (.app (.const K.holds) u)
      rw [← read.holds_eq]
      exact hu

/-- Every code constant is a valid term of its declared type. -/
theorem valid_codeS {c : DeclName} {T : Tm Head 0} (declared : K.codeType c = some T) :
    ValidTmS M .nil (.const c) T := by
  unfold Codes.codeType at declared
  by_cases hp : c = K.prop
  · rw [if_pos hp] at declared
    cases declared
    rw [hp]
    exact valid_propS laws read
  rw [if_neg hp] at declared
  by_cases hh : c = K.holds
  · rw [if_pos hh] at declared
    cases declared
    rw [hh]
    exact valid_holdsS laws read
  rw [if_neg hh] at declared
  by_cases hi : c = K.imp
  · rw [if_pos hi] at declared
    cases declared
    rw [hi]
    exact valid_impS laws read
  rw [if_neg hi] at declared
  cases carrier : K.quantifiers c with
  | some A =>
      rw [carrier] at declared
      cases declared
      exact valid_allS laws read carrier
  | none =>
      rw [carrier] at declared
      cases equation : K.equationCarrier c with
      | none => rw [equation] at declared; cases declared
      | some A =>
          rw [equation] at declared
          cases declared
          exact valid_eqS laws read equation

end Laws

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
