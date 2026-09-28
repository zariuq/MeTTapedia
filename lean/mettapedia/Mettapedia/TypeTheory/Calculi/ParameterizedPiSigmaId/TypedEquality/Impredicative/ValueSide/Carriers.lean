import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Reading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Denotation

/-!
# Carriers in the value model

A carrier of the quantifier and equation codes is also a closed type. In the
value model it is interpreted, at every level and world, by its *carrier
pack* (`carrier_interp`): the codes at `prop`, the inductive pack of the
numbers at `num`, the total pack at a rigid base type, and at a function
carrier the pack of a non-dependent function type.

* The value relation of a carrier pack relates terms with a common meaning
  (`carrierPack_rel`).
* A value with meaning `v` is realized by `Real` of `v` (`carrierPack_real`).
  At the numbers, the realizers of a term are those of its shape, which are
  those of its value (`numIndPack_real_value`). At a function carrier they are
  Girard's clause over the valid arguments at every world reached by a
  morphism; every meaning of the domain is the meaning of such an argument, so
  by the law of Girard's clause they are Girard's clause over the meanings,
  the realizers of the function's meaning (`carrierPi_real`, C2). No
  membership is read.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Kind Carrier World Morph Read DataEq dataValue)
open Realizability (HasShape)
open StrongNormalization (NumShape)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-! ## The numbers -/

/-- The numbers are interpreted by their inductive pack, at every level and
over every table of the levels below. -/
theorem SInterp.num (laws : V.Laws) {l : L} {below : L → IPack V} {n : Nat}
    {ξ : World V.reading n} {A : Tm Head n} (red : WhRed V.rules V.roles A (.const V.num)) :
    SInterp V l below ξ A (numIndPack V n) :=
  SInterp.ind red laws.num_role _ fun mem => by
    rw [closedFields_numConstructors] at mem
    cases mem

variable (V) in
/-- A term of each shape of numbers: a numeral, or successors of the daimon. -/
def shapeTerm {n : Nat} : NumShape → Tm Head n
  | .zero => .const V.zero
  | .suc s => .app (.const V.suc) (shapeTerm s)
  | .star => .const V.star

/-- The term of a shape has that shape. -/
theorem hasShape_shapeTerm {n : Nat} (s : NumShape) :
    HasShape V.toSetting V.star (shapeTerm V s : Tm Head n) s := by
  induction s with
  | zero => exact .zero .refl
  | suc s ih => exact .suc .refl ih
  | star => exact .star .refl .star

/-- A term of the numbers with a shape is realized by the realizers of the
shape. -/
theorem numIndPack_real_of_shape (laws : V.Laws) {n : Nat} {a : Tm Head n} {s : NumShape}
    (shape : HasShape V.toSetting V.star a s) :
    (numIndPack V n).real a = V.alg.numReal V.num V.zero V.suc s := by
  rw [numIndPack_real laws]
  exact laws.alg.meet_const _ _
    (fun s' => congrArg (V.alg.numReal V.num V.zero V.suc)
      (HasShape.deterministic laws.values.truth laws.star s'.2 shape))
    ⟨⟨s, shape⟩⟩

/-- **The realizers of the numbers are the realizers of their meanings**: a
term of the numbers related to itself is realized by `Real` at `num` of its
value. -/
theorem numIndPack_real_value (laws : V.Laws) {n : Nat} {a : Tm Head n}
    (rel : DataEq V.reading .num a a) :
    (numIndPack V n).real a =
      V.alg.Real V.toSetting V.star V.num .num
        (dataValue (P := V.alg.Cand) V.reading .num a rel) := by
  obtain ⟨s, shape, -⟩ := id rel
  rw [numIndPack_real_of_shape laws shape]
  exact (laws.alg.numValReal_dataValue laws.values.truth laws.star V.num rel shape).symm

/-! ## Carrier packs -/

/-- The family of a non-dependent function type whose domain and codomain packs
are the same at every world reached by a morphism. -/
def PiPack.arrow {n : Nat} (ξ : World V.reading n)
    (D C : ∀ {m : Nat}, World V.reading m → Pack V m) : PiPack V ξ where
  dom := fun {_ ξ' _} _ => D ξ'
  cod := fun {_ ξ' _} _ {_} _ => C ξ'

variable (V) in
/-- The pack of a carrier: the codes at `prop`, the numbers at `num`, the total
pack at a rigid base type, and the pack of a non-dependent function type at a
function carrier. -/
def carrierPack : {k : Kind} → Carrier k → {n : Nat} → World V.reading n → Pack V n
  | _, .prop, _, ξ => propPack V ξ
  | _, .num, n, _ => numIndPack V n
  | _, .rigid _, n, _ => Pack.total V n
  | _, .arr K K', _, ξ =>
      (PiPack.arrow ξ (fun ξ' => carrierPack K ξ') (fun ξ' => carrierPack K' ξ')).piPack

/-- **An interpretable carrier, read as a type, is interpreted by its pack** at
every level and world. -/
theorem carrier_interp (laws : V.Laws) {l : L} {below : L → IPack V} :
    ∀ {k : Kind} {K : Carrier k}, K.Interpretable V.toModel → ∀ {n : Nat}
      (ξ : World V.reading n),
      SInterp V l below ξ (liftClosed (K.term V.toModel)) (carrierPack V K ξ)
  | _, _, .prop, _, _ => SInterp.prop .refl
  | _, _, .num, _, _ => SInterp.num laws .refl
  | _, _, .rigid role notProp notHolds, _, _ =>
      SInterp.rigid (args := []) .refl role notProp notHolds
  | _, _, @Consistency.Carrier.Interpretable.arr _ _ _ _ _ _ K K' dom cod, _, ξ => by
      change SInterp V l below ξ (liftClosed (.pi (K.term V.toModel)
        (Presentation.rename wk (K'.term V.toModel)))) _
      rw [Consistency.liftClosed_arrow]
      exact SInterp.pi .refl
        (PiPack.arrow ξ (fun ξ' => carrierPack V K ξ') (fun ξ' => carrierPack V K' ξ'))
        (fun {_ _ _} _ => by
          rw [rename_liftClosed]
          exact carrier_interp laws dom _)
        (fun {_ _ _} _ {_} _ => by
          rw [rename_liftRen_wk, inst0_rename_wk, rename_liftClosed]
          exact carrier_interp laws cod _)
        (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- **The value relation of a carrier pack relates terms with a common
meaning.** -/
theorem carrierPack_rel (laws : V.Laws) : ∀ {k : Kind} (K : Carrier k) {n : Nat}
    (ξ : World V.reading n) (a b : Tm Head n),
      (carrierPack V K ξ).rel a b ↔ K.rel V.reading ξ a b
  | _, .prop, _, ξ, a, b => by
      rw [Consistency.Carrier.rel_prop]
      rfl
  | _, .num, _, ξ, a, b => by
      rw [Consistency.Carrier.rel_data laws.reading]
      exact numIndPack_rel
  | _, .rigid T, _, ξ, a, b => by
      rw [Consistency.Carrier.rel_rigid]
      rfl
  | _, @Carrier.arr k .gen K K', _, ξ, f, g => by
      rw [← Consistency.Carrier.arrow_iff laws.reading]
      constructor
      · intro related m ξ' ρ w a b ha hab
        exact (carrierPack_rel laws K' ξ' _ _).mp
          (related w ((carrierPack_rel laws K ξ' a a).mpr ha)
            ((carrierPack_rel laws K ξ' a b).mpr hab))
      · intro related m ξ' ρ w a b ha hab
        exact (carrierPack_rel laws K' ξ' _ _).mpr
          (related w ((carrierPack_rel laws K ξ' a a).mp ha)
            ((carrierPack_rel laws K ξ' a b).mp hab))
  | _, @Carrier.arr k .data K K', _, ξ, f, g => by
      rw [Consistency.Carrier.rel_data laws.reading (.arr K K'),
        ← Consistency.Carrier.arrow_data_iff laws.reading]
      constructor
      · intro related m ξ' ρ w a b ha hab
        exact (carrierPack_rel laws K' ξ' _ _).mp
          (related w ((carrierPack_rel laws K ξ' a a).mpr ha)
            ((carrierPack_rel laws K ξ' a b).mpr hab))
      · intro related m ξ' ρ w a b ha hab
        exact (carrierPack_rel laws K' ξ' _ _).mpr
          (related w ((carrierPack_rel laws K ξ' a a).mp ha)
            ((carrierPack_rel laws K ξ' a b).mp hab))

/-- A valid value of a carrier pack is a term with a meaning. -/
theorem carrierPack_val (laws : V.Laws) {k : Kind} (K : Carrier k) {n : Nat}
    {ξ : World V.reading n} {a : Tm Head n} :
    (carrierPack V K ξ).Val a ↔ ∃ v, Read V.reading ξ a K v :=
  (carrierPack_rel laws K ξ a a).trans
    ⟨fun ⟨v, ra, _⟩ => ⟨v, ra⟩, fun ⟨v, ra⟩ => ⟨v, ra, ra⟩⟩

/-! ## Realizers of carrier packs -/

/-- **C2: a dependent function type over a carrier is realized by Girard's
clause over the meanings of the carrier.** When the domain's pack is the
carrier's pack at every world reached by a morphism, its values are realized
by the realizers of their meanings, and the applications of `f` to valid
arguments with a meaning are realized by a family of candidates of the
meaning, the realizers of `f` are Girard's clause of the family: every valid
argument has a meaning, and every meaning is that of a valid argument. -/
theorem carrierPi_real (laws : V.Laws) {k : Kind} (K : Carrier k) {n : Nat}
    {ξ : World V.reading n} (P : PiPack V ξ)
    (hdom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
      P.dom w = carrierPack V K ξ')
    (domReal : ∀ {m : Nat} {ξ' : World V.reading m} {x : Tm Head m} {v : K.V V.reading},
      Read V.reading ξ' x K v →
        (carrierPack V K ξ').real x = V.alg.Real V.toSetting V.star V.num K v)
    (f : Tm Head n) (cod : K.V V.reading → V.alg.Cand)
    (codAt : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {x : Tm Head m} (hx : (P.dom w).Val x) {v : K.V V.reading}, Read V.reading ξ' x K v →
        (P.cod w hx).real (.app (Presentation.rename ρ f) x) = cod v) :
    P.real f = V.alg.piOver (V.alg.Real V.toSetting V.star V.num K) cod := by
  refine laws.alg.piOver_congr _ _ _ _ (fun i => ?_) (fun v => ?_)
  · have hx : (carrierPack V K i.world).Val i.arg := by
      rw [← hdom i.morph]
      exact i.valid
    obtain ⟨v, rx⟩ := (carrierPack_val laws K).mp hx
    refine ⟨v, ?_, codAt i.morph i.valid rx⟩
    show (P.dom i.morph).real i.arg = _
    rw [hdom i.morph]
    exact domReal rx
  · obtain ⟨m, ξ', ρ, x, w, rx⟩ := Carrier.realizedAt K v ξ
    have hx : (P.dom w).Val x := by
      rw [hdom w]
      exact (carrierPack_val laws K).mpr ⟨v, rx⟩
    refine ⟨⟨m, ξ', ρ, w, x, hx⟩, ?_, codAt w hx rx⟩
    show (P.dom w).real x = _
    rw [hdom w]
    exact domReal rx

/-- The realizers of the pack of a function carrier: when the function's
applications to arguments with a meaning are realized by a family of
candidates of the meaning, they are Girard's clause of the family. -/
theorem arrowPack_real (laws : V.Laws) {k k' : Kind} (K : Carrier k) (K' : Carrier k')
    {n : Nat} {ξ : World V.reading n} (f : Tm Head n)
    (domReal : ∀ {m : Nat} {ξ' : World V.reading m} {x : Tm Head m} {v : K.V V.reading},
      Read V.reading ξ' x K v →
        (carrierPack V K ξ').real x = V.alg.Real V.toSetting V.star V.num K v)
    (cod : K.V V.reading → V.alg.Cand)
    (codAt : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∀ {x : Tm Head m} {v : K.V V.reading}, Read V.reading ξ' x K v →
        (carrierPack V K' ξ').real (.app (Presentation.rename ρ f) x) = cod v) :
    (PiPack.arrow ξ (fun ξ' => carrierPack V K ξ') (fun ξ' => carrierPack V K' ξ')).real f =
      V.alg.piOver (V.alg.Real V.toSetting V.star V.num K) cod :=
  carrierPi_real laws K _ (fun _ => rfl) domReal f cod fun w _ _ _ rx => codAt w rx

/-- **A value of a carrier pack with a meaning is realized by the realizers of
the meaning.** -/
theorem carrierPack_real (laws : V.Laws) : ∀ {k : Kind} (K : Carrier k) {n : Nat}
    {ξ : World V.reading n} {a : Tm Head n} {v : K.V V.reading}, Read V.reading ξ a K v →
      (carrierPack V K ξ).real a = V.alg.Real V.toSetting V.star V.num K v
  | _, .prop, _, _, _, _, _ => rfl
  | _, .rigid _, _, _, _, _, _ => rfl
  | _, .num, _, _, _, _, read => by
      obtain ⟨rel, rfl⟩ := read.data_inv
      exact numIndPack_real_value laws rel
  | _, @Carrier.arr _ .gen K K', _, ξ, f, φ, read =>
      arrowPack_real laws K K' f (fun rx => carrierPack_real laws K rx)
        (fun v => V.alg.Real V.toSetting V.star V.num K' (φ v))
        (fun w _ _ rx => carrierPack_real laws K' (Read.app (read.rename w) rx))
  | _, @Carrier.arr .gen .data K K', _, ξ, f, F, read => by
      obtain ⟨rel, rfl⟩ := read.data_inv
      refine arrowPack_real laws K K' f (fun rx => carrierPack_real laws K rx) _ ?_
      intro m ξ' ρ w x v rx
      have relApp : DataEq V.reading K' (.app (Presentation.rename ρ f) x)
          (.app (Presentation.rename ρ f) x) := by
        have h := Consistency.DataEq.subst₂ K' (rel : DataEq V.reading K'
          (.app (Presentation.rename wk f) (.var 0)) (.app (Presentation.rename wk f) (.var 0)))
          (consSub x (renSub ρ)) (consSub x (renSub ρ))
        simp only [Presentation.subst, subst_consSub_rename_wk, consSub_zero, subst_renSub] at h
        exact h
      rw [carrierPack_real laws K' (.data relApp)]
      exact congrArg (V.alg.Real V.toSetting V.star V.num K')
        (appGen_dataValue (P := V.alg.Cand) (K := K) (B := K') (f := f) rel ρ x relApp)
  | _, @Carrier.arr .data .data K K', _, ξ, f, F, read => by
      obtain ⟨rel, rfl⟩ := read.data_inv
      refine arrowPack_real laws K K' f (fun rx => carrierPack_real laws K rx) _ ?_
      intro m ξ' ρ w x v rx
      obtain ⟨relX, rfl⟩ := rx.data_inv
      have relApp : DataEq V.reading K' (.app (Presentation.rename ρ f) x)
          (.app (Presentation.rename ρ f) x) := rel ρ relX
      rw [carrierPack_real laws K' (.data relApp)]
      exact congrArg (V.alg.Real V.toSetting V.star V.num K')
        (appData_dataValue (P := V.alg.Cand) (K := K) (B := K') (f := f) rel ρ relX relApp)

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
