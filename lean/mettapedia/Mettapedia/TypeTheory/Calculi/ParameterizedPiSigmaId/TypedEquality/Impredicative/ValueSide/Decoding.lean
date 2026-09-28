import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Carriers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Root

/-!
# Decodings in the value model

On the value side `holds` is rigid: `holds c`, for a code `c` meaning a
candidate `X`, relates every pair of values and is realized by `X`
(`holdsPack`). The decoding of a code is interpreted by the same pack, at every
level and over every table of the levels below:

* `Π (holds p) (holds q)`, for `p` meaning `X` and `q` meaning `Y`: every
  argument is valid and the daimon is one, so by C1 the realizers are the
  function space from `X` to `Y`, the meaning of `imp p q`
  (`interp_holds_imp`);
* `Π (x : A). holds (f x)`, for a carrier `A` and `f` reading at `A → prop` as
  `φ`: an argument with meaning `v` makes `f x` mean `φ v`, and every meaning is
  the meaning of an argument, so by C2 the realizers are Girard's clause over
  the meanings of `A`, the meaning of `all@A f` (`interp_holds_all`);
* `Id A x y`, for `x` and `y` reading at `A` as `v` and `w`: the endpoints are
  related exactly when `v = w`, so by C3 the realizers are the identity
  candidate of `v = w`, the meaning of `eq@A x y` (`interp_id_carrier`).

Every pack involved relates all values, as proof types do. So the decoding of
an interpreted code is interpreted by the code's pack (`decoder_interp`), and,
a type having at most one pack at a level, a code and its decoding have one
pack wherever both are interpreted (`decoder_coherent`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier World Morph Truth Read)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-- The meaning of a code, written as the meet of its meanings: no choice is
involved, and a code with a meaning has it as its meet. -/
def codeMeaning {n : Nat} (ξ : World V.reading n) (c : Tm Head n) : V.alg.Cand :=
  V.alg.meet fun X : {X : V.alg.Cand // Truth V.reading ξ c X} => X.1

theorem codeMeaning_eq (laws : V.Laws) {n : Nat} {ξ : World V.reading n} {c : Tm Head n}
    {X : V.alg.Cand} (truth : Truth V.reading ξ c X) : codeMeaning ξ c = X :=
  laws.alg.meet_const _ X (fun Y => Consistency.Truth.deterministic laws.reading Y.2 truth)
    ⟨⟨X, truth⟩⟩

section Decodings

variable (laws : V.Laws) {l : L} {below : L → IPack V}
include laws

/-! ## Implication -/

/-- **The decoding of an implication is interpreted by the proof pack of the
function space of the two meanings.** -/
theorem interp_holds_imp {n : Nat} {ξ : World V.reading n} {p q : Tm Head n}
    {X Y : V.alg.Cand} (hp : Truth V.reading ξ p X) (hq : Truth V.reading ξ q Y) :
    SInterp V l below ξ (.pi (.app (.const V.holds) p)
        (.app (.const V.holds) (Presentation.rename wk q)))
      (holdsPack V n (V.alg.arrow X Y)) := by
  let P : PiPack V ξ :=
    PiPack.arrow ξ (fun {m} _ => holdsPack V m X) (fun {m} _ => holdsPack V m Y)
  have interp : SInterp V l below ξ (.pi (.app (.const V.holds) p)
      (.app (.const V.holds) (Presentation.rename wk q))) P.piPack :=
    SInterp.pi .refl P (fun {_ _ _} w => SInterp.holds .refl (hp.rename w))
      (fun {_ _ ρ} w {a} _ => by
        change SInterp V l below _ (.app (.const V.holds)
          (inst0 a (Presentation.rename (liftRen ρ) (Presentation.rename wk q)))) _
        rw [rename_liftRen_wk, inst0_rename_wk]
        exact SInterp.holds .refl (hq.rename w))
      (fun {_ _ _} _ {_ _} _ _ _ => rfl)
  have same : P.piPack = holdsPack V n (V.alg.arrow X Y) := by
    have rel : P.rel = fun _ _ => True :=
      funext fun _ => funext fun _ =>
        propext ⟨fun _ => trivial, fun _ {_ _ _} _ {_ _} _ _ => trivial⟩
    have real : P.real = fun _ => V.alg.arrow X Y := by
      funext f
      exact laws.alg.piOver_const ⟨⟨n, ξ, idRen, Morph.id ξ, .const V.star, trivial⟩⟩ X Y
    change (⟨P.rel, P.real⟩ : Pack V n) = _
    rw [rel, real]
    rfl
  rw [← same]
  exact interp

/-! ## Quantifiers -/

/-- **The decoding of a quantifier over an interpretable carrier is interpreted
by the proof pack of Girard's clause over the meanings of the carrier.** -/
theorem interp_holds_all {k : Kind} {K : Carrier k} (hK : K.Interpretable V.toModel) {n : Nat}
    {ξ : World V.reading n} {f : Tm Head n} {φ : K.V V.reading → V.alg.Cand}
    (read : Read V.reading ξ f (.arr K .prop) φ) :
    SInterp V l below ξ (.pi (liftClosed (K.term V.toModel))
        (.app (.const V.holds) (.app (Presentation.rename wk f) (.var 0))))
      (holdsPack V n (V.alg.piOver (V.alg.Real V.toSetting V.star V.num K) φ)) := by
  let P : PiPack V ξ :=
    { dom := fun {_ ξ' _} _ => carrierPack V K ξ'
      cod := fun {m ξ' ρ} _ {a} _ =>
        holdsPack V m (codeMeaning ξ' (.app (Presentation.rename ρ f) a)) }
  have truthAt : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} {v : K.V V.reading}, Read V.reading ξ' a K v →
        Truth V.reading ξ' (.app (Presentation.rename ρ f) a) (φ v) :=
    fun w _ _ ra => (Read.app (read.rename w) ra).prop_inv
  have interp : SInterp V l below ξ (.pi (liftClosed (K.term V.toModel))
      (.app (.const V.holds) (.app (Presentation.rename wk f) (.var 0)))) P.piPack := by
    refine SInterp.pi .refl P (fun {_ _ _} _ => ?_) (fun {_ _ ρ} w {a} ha => ?_) ?_
    · rw [rename_liftClosed]
      exact carrier_interp laws hK _
    · change SInterp V l below _ (inst0 a (.app (.const V.holds)
        (.app (Presentation.rename (liftRen ρ) (Presentation.rename wk f)) (.var 0)))) _
      rw [rename_liftRen_wk]
      change SInterp V l below _ (.app (.const V.holds)
        (.app (inst0 a (Presentation.rename wk (Presentation.rename ρ f))) a)) _
      rw [inst0_rename_wk]
      obtain ⟨v, ra⟩ := (carrierPack_val laws K).mp ha
      change SInterp V l below _ _
        (holdsPack V _ (codeMeaning _ (.app (Presentation.rename ρ f) a)))
      rw [codeMeaning_eq laws (truthAt w ra)]
      exact SInterp.holds .refl (truthAt w ra)
    · intro m ξ' ρ w a b _ _ hab
      obtain ⟨v, ra, rb⟩ := (carrierPack_rel laws K ξ' a b).mp hab
      change holdsPack V m _ = holdsPack V m _
      rw [codeMeaning_eq laws (truthAt w ra), codeMeaning_eq laws (truthAt w rb)]
  have same :
      P.piPack = holdsPack V n (V.alg.piOver (V.alg.Real V.toSetting V.star V.num K) φ) := by
    have rel : P.rel = fun _ _ => True :=
      funext fun _ => funext fun _ =>
        propext ⟨fun _ => trivial, fun _ {_ _ _} _ {_ _} _ _ => trivial⟩
    have real : P.real = fun _ => V.alg.piOver (V.alg.Real V.toSetting V.star V.num K) φ := by
      funext g
      exact carrierPi_real laws K P (fun _ => rfl) (fun rx => carrierPack_real laws K rx) g φ
        fun {_ _ ρ} w {x} _ {v} rx => by
          change codeMeaning _ (.app (Presentation.rename ρ f) x) = φ v
          exact codeMeaning_eq laws (truthAt w rx)
    change (⟨P.rel, P.real⟩ : Pack V n) = _
    rw [rel, real]
    rfl
  rw [← same]
  exact interp

/-! ## Equations -/

/-- **The decoding of an equation over an interpretable carrier is interpreted
by the proof pack of the identity candidate of the equality of the endpoints'
meanings.** -/
theorem interp_id_carrier {k : Kind} {K : Carrier k} (hK : K.Interpretable V.toModel) {n : Nat}
    {ξ : World V.reading n} {x y : Tm Head n} {v w : K.V V.reading}
    (rx : Read V.reading ξ x K v) (ry : Read V.reading ξ y K w) :
    SInterp V l below ξ (.id (liftClosed (K.term V.toModel)) x y)
      (holdsPack V n (V.alg.ident (v = w))) := by
  have interp : SInterp V l below ξ (.id (liftClosed (K.term V.toModel)) x y)
      (identPack (carrierPack V K ξ) x y) :=
    SInterp.ident .refl (carrierPack V K ξ) (carrier_interp laws hK ξ)
      ((carrierPack_val laws K).mpr ⟨v, rx⟩) ((carrierPack_val laws K).mpr ⟨w, ry⟩)
  have same : (carrierPack V K ξ).rel x y ↔ v = w := by
    rw [carrierPack_rel laws K ξ x y]
    constructor
    · rintro ⟨u, rx', ry'⟩
      rw [Consistency.Read.deterministic laws.reading rx rx',
        Consistency.Read.deterministic laws.reading ry ry']
    · rintro rfl
      exact ⟨v, rx, ry⟩
  rw [← V.alg.ident_congr same]
  exact interp

/-! ## Coherence -/

/-- **The decoding of an interpreted code is interpreted by the pack of the
code**, for every decoder rule. -/
theorem decoder_interp {D : Decoders Head} (decodes : Consistency.Decodes V.toModel D) {n : Nat}
    {ξ : World V.reading n} {x y : Tm Head n} (step : DecoderStep D x y) {P : Pack V n}
    (hx : SInterp V l below ξ x P) : SInterp V l below ξ y P := by
  cases step with
  | imp p q =>
      rw [decodes.holds, decodes.imp] at hx
      rw [decodes.holds]
      obtain ⟨X, truth, rfl⟩ := hx.holds_inv laws .refl
      obtain ⟨_, _, hp, hq, rfl⟩ := Consistency.Truth.imp_inv laws.reading truth
      exact interp_holds_imp laws hp hq
  | all carrier f =>
      obtain ⟨_, C, carrierM, hC, rfl⟩ := decodes.all carrier
      rw [decodes.holds] at hx ⊢
      obtain ⟨X, truth, rfl⟩ := hx.holds_inv laws .refl
      obtain ⟨_, read, rfl⟩ := Consistency.Truth.all_inv laws.reading carrierM truth
      exact interp_holds_all laws hC read
  | eq carrier a b =>
      obtain ⟨_, C, carrierM, hC, rfl⟩ := decodes.eq carrier
      rw [decodes.holds] at hx
      obtain ⟨X, truth, rfl⟩ := hx.holds_inv laws .refl
      obtain ⟨_, _, readX, readY, rfl⟩ := Consistency.Truth.eq_inv laws.reading carrierM truth
      exact interp_id_carrier laws hC readX readY

/-- **A code and its decoding have one pack wherever both are interpreted at a
level**, for every decoder rule. -/
theorem decoder_coherent {D : Decoders Head} (decodes : Consistency.Decodes V.toModel D)
    {n : Nat} {ξ : World V.reading n} {x y : Tm Head n} (step : DecoderStep D x y)
    {P₁ P₂ : Pack V n} (hx : SInterp V l below ξ x P₁) (hy : SInterp V l below ξ y P₂) :
    P₁ = P₂ :=
  (decoder_interp laws decodes step hx).deterministic laws hy

end Decodings

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
