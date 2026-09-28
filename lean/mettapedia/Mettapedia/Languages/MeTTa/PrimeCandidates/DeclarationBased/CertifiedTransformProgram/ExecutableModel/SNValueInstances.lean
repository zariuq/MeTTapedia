import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueNumbers
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueRecursor
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueIterator

/-!
# The transport value model on the skeleton-free value side: instances

The instances of the transport value model on the skeleton-free value side
(`vmodel`):

* the transport's laws, with no hypothesis on its reductions
  (`vmodel_coe_val`, …), since the table holds (`vmodel_coeRules`);
* the program's codes: `holds (imp p q)` and `Π (holds p) (holds q)`, and
  `holds (all@num f)` and `Π (x : num). holds (f x)`, are pairs of one shape with
  one pack at every level (`ValueModel.holdsImp_shapePair`,
  `ValueModel.holdsAll_shapePair`), their decodings are hereditarily total, and
  the transports out of them into `num → num` are related to the daimon and to
  each other; the transport out of `Σ (holds p) (holds q)` into `Σ num num` is
  related to the daimon. The reading of the model is the candidate reading
  (`vmodel_reading_eq`): implication means the function space of Kripke
  candidates and the quantifier Girard's clause (`vmodel_impMeaning`,
  `vmodel_allMeaning`);
* identity elimination: at reflexivity it is the transport of its method along
  one type, related to the method (`vmodel_j_refl`); at a path stuck on the
  daimon with a constant motive it returns its method (`vmodel_j_star_num`); the
  transport of a valid method between covered instances of the motive is valid
  (`vmodel_j_val`), and transports of related methods are related
  (`vmodel_j_congr`); with the large motive, identity elimination from `0` to `1`
  gives the daimon, a valid value of every pack of the result type
  (`vmodel_largeJ_valid`), while the method `0`, which a cast would return, is
  no value of `num → num` (`vnumArrow_not_rel_zero`).

## The constants

Every declared constant of the executable package other than identity
elimination and the two definitions that use it, `sucMove` and `sucStep`, is a
valid term of its declared type in the model: the numbers, the sets and their
constants, the recursor and the iterator by their own proofs, and each
definition by one equation from the fundamental lemma of the stage that types
its right-hand side. Identity elimination, `sucMove` and `sucStep` are valid
through the typed step of identity elimination, and the whole object package is
sound (`vmodel_soundS_objectRules`, in `SNValueSound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World Morph Truth Carrier)
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic)
open Mettapedia.Logic
open Package (U0 numT jName numRecName)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## The transport's laws, without hypotheses -/

section Laws

variable {v} {l n : Nat} {ξ : World (vmodel v).reading n}

/-- Between interpreted types, the transport reduces to a reduct one row of the
table gives. -/
theorem vmodel_coe_reduct {X Y : Tower.Tm n} {PX PY : ValueSide.Pack (vmodel v).value n}
    (hX : ValueSide.InterpAt (vmodel v).value l ξ X PX)
    (hY : ValueSide.InterpAt (vmodel v).value l ξ Y PY) (d : Tower.Tm n) :
    ∃ r, WhRed (vmodel v).rules (vmodel v).roles (ValueSide.coeApp coeN X Y d) r ∧
      ValueSide.CoeReduct (vmodel v).value coeN X Y d r :=
  ValueSide.CoeRules.reduct (vmodel_valueLaws v)
    (ValueSide.InterpAt.facts (vmodel_valueLaws v) l) (vmodel_coeRules v) hX hY d

/-- **Validity.** -/
theorem vmodel_coe_val {X Y : Tower.Tm n} {PX PY : ValueSide.Pack (vmodel v).value n}
    (hX : ValueSide.InterpAt (vmodel v).value l ξ X PX)
    (hY : ValueSide.InterpAt (vmodel v).value l ξ Y PY)
    (coverX : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ X X)
    (coverY : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ Y Y)
    {d : Tower.Tm n} (hd : PX.Val d) : PY.Val (ValueSide.coeApp coeN X Y d) :=
  ValueSide.coe_val (vmodel_valueLaws v) (ValueSide.InterpAt.facts (vmodel_valueLaws v) l)
    (vmodel_coeRules v) hX hY coverX coverY hd

/-- **Congruence.** -/
theorem vmodel_coe_congr {X X' Y Y' : Tower.Tm n}
    {PX PX' PY PY' : ValueSide.Pack (vmodel v).value n}
    (sources : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ X X'
      PX PX')
    (targets : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ Y Y'
      PY PY')
    {d d' : Tower.Tm n} (hdd' : PX.rel d d') :
    PY.rel (ValueSide.coeApp coeN X Y d) (ValueSide.coeApp coeN X' Y' d') :=
  ValueSide.coe_congr (vmodel_valueLaws v) (ValueSide.InterpAt.facts (vmodel_valueLaws v) l)
    (vmodel_coeRules v) sources targets hdd'

/-- **Coherence.** -/
theorem vmodel_coe_coherent {X Y : Tower.Tm n} {PX PY : ValueSide.Pack (vmodel v).value n}
    (same : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ X Y
      PX PY)
    {d : Tower.Tm n} (hd : PX.Val d) : PY.rel (ValueSide.coeApp coeN X Y d) d :=
  ValueSide.coe_coherent (vmodel_valueLaws v) (ValueSide.InterpAt.facts (vmodel_valueLaws v) l)
    (vmodel_coeRules v) same hd

/-- Between two types of one shape with one pack, the transport has the
realizers of its method. -/
theorem vmodel_coe_real {X Y : Tower.Tm n} {PX PY : ValueSide.Pack (vmodel v).value n}
    (same : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ X Y
      PX PY)
    {d : Tower.Tm n} (hd : PX.Val d) : PY.real (ValueSide.coeApp coeN X Y d) = PY.real d :=
  ValueSide.coe_real (vmodel_valueLaws v) (ValueSide.InterpAt.facts (vmodel_valueLaws v) l)
    (vmodel_coeRules v) same hd

/-- A transport out of a hereditarily total type is related to the daimon. -/
theorem vmodel_coe_total_star {S Z : Tower.Tm n} {PZ : ValueSide.Pack (vmodel v).value n}
    (total : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .total ξ S S)
    (hZ : ValueSide.InterpAt (vmodel v).value l ξ Z PZ)
    (cover : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ Z Z)
    (e : Tower.Tm n) : PZ.rel (ValueSide.coeApp coeN S Z e) (.const starN) :=
  ValueSide.coe_total_star (vmodel_valueLaws v) (ValueSide.InterpAt.facts (vmodel_valueLaws v) l)
    (vmodel_coeRules v) total hZ cover e

/-- Transports out of two hereditarily total types into the two types of a pair
are related. -/
theorem vmodel_coe_total_congr {S S' Z Z' : Tower.Tm n}
    {PZ PZ' : ValueSide.Pack (vmodel v).value n}
    (total : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .total ξ S S)
    (total' : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .total ξ
      S' S')
    (targets : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ Z Z'
      PZ PZ')
    (e e' : Tower.Tm n) :
    PZ.rel (ValueSide.coeApp coeN S Z e) (ValueSide.coeApp coeN S' Z' e') :=
  ValueSide.coe_total_congr (vmodel_valueLaws v) (ValueSide.InterpAt.facts (vmodel_valueLaws v) l)
    (vmodel_coeRules v) total total' targets e e'

end Laws

/-! ## The meanings of codes -/

/-- Implication means the function space of Kripke candidates, as in the
candidate reading. -/
theorem vmodel_impMeaning (X Y : (vmodel v).reading.P) :
    (vmodel v).reading.impMeaning X Y =
      (Realizability.candidateReading (tmodelC v).toSetting starN objectRealizers).impMeaning
        X Y :=
  ModelS.kcand_arrow objectRealizers X Y

/-- A quantifier means Girard's clause over the meanings of its carrier, as in
the candidate reading. -/
theorem vmodel_allMeaning {k : Consistency.Kind} (K : Carrier k)
    (φ : K.V (vmodel v).reading → (vmodel v).reading.P) :
    (vmodel v).reading.allMeaning K φ =
      (Realizability.candidateReading (tmodelC v).toSetting starN objectRealizers).allMeaning
        K φ :=
  ModelS.kcand_allMeaning objectRealizers (tmodelC v).toSetting starN numN rfl rfl
    objectRoles_num_ctors K φ

/-! ## The pack of `num → num` -/

/-- The pack of `num → num`: functions sending numbers of one shape to numbers
of one shape (`vinterp_numArrow`). -/
abbrev vnumArrow {n : Nat} (ξ : World (vmodel v).reading n) : ValueSide.Pack (vmodel v).value n :=
  varrowD v (vnumD v) (vnumD v) ξ

/-- `num → num` is of one shape with itself at every level. -/
theorem vshape_numArrow (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ
      (.pi numT numT) (.pi numT numT) :=
  (ValueSide.numArrow_shape (vmodel_valueLaws v) ξ).1

/-- **The numeral `0` is no value of `num → num`**: applied to the daimon, a
number of the daimonic shape, it gives `0 ⋆`, which is weak-head normal and
neither `0`, a successor, nor stuck on the daimon, so it has no shape of
numbers. -/
theorem vnumArrow_not_rel_zero {n : Nat} (ξ : World (vmodel v).reading n) :
    ¬ (vnumArrow v ξ).rel (.const zeroN) (.const zeroN) := by
  intro rel
  have star : (ValueSide.numIndPack (vmodel v).value n).rel (.const starN) (.const starN) :=
    ValueSide.numIndPack_rel.mpr ⟨.star, .star .refl .star, .star .refl .star⟩
  obtain ⟨s, shape, -⟩ := ValueSide.numIndPack_rel.mp (rel (Morph.id ξ) star star)
  have stuck : ∀ {c : DeclName}, (c = zeroN ∨ c = sucN) →
      ∀ arity scrutinee, tmodelRoles c ≠ .computes arity scrutinee := by
    rintro c (rfl | rfl) _ _ role
    · rw [tmodelRoles_zero] at role
      cases role
    · rw [tmodelRoles_suc] at role
      cases role
  have normal : Whnf (tmodelC v).rules (tmodelC v).roles
      (appSpine (.const zeroN) [.const starN] : Tower.Tm n) :=
    constSpine_whnf (tmodelShape v) (stuck (.inl rfl)) _
  cases shape with
  | zero red =>
      cases WhRed.whnf_unique (tmodelShape v) red .refl
        (constSpine_whnf (tmodelShape v) (stuck (.inl rfl)) (args := [])) normal
  | suc red _ =>
      have e := WhRed.whnf_unique (tmodelShape v) red .refl
        (constSpine_whnf (tmodelShape v) (stuck (.inr rfl)) (args := [_])) normal
      exact absurd (Tm.const.inj (Tm.app.inj e).1) (by change ¬ sucN = zeroN; decide)
  | star red daimonic =>
      have e := WhRed.whnf_unique (tmodelShape v) red .refl
        ((daimonic.neutral tmodelRoles_star).whnf (tmodelShape v)) normal
      subst e
      rcases daimonic.constSpine (c := zeroN) (args := [.const starN]) rfl with e | ⟨_, _, role⟩
      · exact absurd e (by change ¬ zeroN = starN; decide)
      · exact stuck (.inl rfl) _ _ role

/-- The pack of `Σ num num`. -/
def vnumPair {n : Nat} (ξ : World (vmodel v).reading n) : ValueSide.Pack (vmodel v).value n :=
  (ValueSide.PiPack.arrow ξ (fun {m} _ => ValueSide.numIndPack (vmodel v).value m)
    (fun {m} _ => ValueSide.numIndPack (vmodel v).value m)).sigmaPack

/-! ## The program's codes -/

/-- The decoding `holds (imp p q)` of the implication of two generic
propositions `p` and `q`. -/
def holdsImp : Tower.Tm 2 :=
  .app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0))

/-- Its unfolding, `Π (holds p) (holds q)`. -/
def impDecoding : Tower.Tm 2 :=
  .pi (.app (.const holdsN) (.var 1)) (.app (.const holdsN) (Presentation.rename wk (.var 0)))

theorem holdsImp_step : DecoderStep programCodes.decoders holdsImp impDecoding :=
  DecoderStep.imp (.var 1) (.var 0)

/-- The carrier of `all@num` among the program's decoders. -/
theorem decoders_allNum :
    programCodes.decoders.allCarrier allNumN = some (typeTerm SetProfile.numTy) := by
  change (SetProfile.allInstance? allNumN).map typeTerm = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- The decoding `holds (all@num f)` of the quantifier over the numbers of a
generic family `f`. -/
def holdsAll : Tower.Tm 1 :=
  .app (.const holdsN) (.app (.const allNumN) (.var 0))

/-- Its unfolding, `Π (x : num). holds (f x)`. -/
def allDecoding : Tower.Tm 1 :=
  .pi (liftClosed (typeTerm SetProfile.numTy))
    (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))

theorem holdsAll_step : DecoderStep programCodes.decoders holdsAll allDecoding :=
  DecoderStep.all (decoders_allNum) (.var 0)

/-- The pair type `Σ (holds p) (holds q)` of two generic propositions. -/
def holdsPairType : Tower.Tm 2 :=
  .sigma (.app (.const holdsN) (.var 1)) (.app (.const holdsN) (Presentation.rename wk (.var 0)))

namespace ValueModel

/-- The carrier of `all@num` in the model. -/
theorem allCarrier_allNum : (tmodelC v).allCarrier allNumN = some ⟨.data, .num⟩ := by
  change (SetProfile.allInstance? allNumN).map carrierOf = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- A world with two generic propositions: `p`, meaning `X`, and `q`, meaning
`Y`. -/
def propWorld (X Y : (vmodel v).reading.P) : World (vmodel v).reading 2 :=
  (Consistency.World.closed.snoc ⟨.prop, X⟩).snoc ⟨.prop, Y⟩

theorem propWorld_truth₁ (X Y : (vmodel v).reading.P) :
    Truth (vmodel v).reading (propWorld v X Y) (.var 1) X :=
  (Consistency.Read.generic_prop (S := (vmodel v).reading) (propWorld v X Y) (i := 1)
    rfl).prop_inv

theorem propWorld_truth₀ (X Y : (vmodel v).reading.P) :
    Truth (vmodel v).reading (propWorld v X Y) (.var 0) Y :=
  (Consistency.Read.generic_prop (S := (vmodel v).reading) (propWorld v X Y) (i := 0)
    rfl).prop_inv

/-- `holds (imp p q)` is interpreted at every level by the proof pack of the
implication of the two meanings. -/
theorem holdsImp_interp (l : Nat) (X Y : (vmodel v).reading.P) :
    ValueSide.InterpAt (vmodel v).value l (propWorld v X Y) holdsImp
      (ValueSide.holdsPack (vmodel v).value 2 ((vmodel v).reading.impMeaning X Y)) :=
  ValueSide.SInterp.holds .refl (.imp .refl (propWorld_truth₁ v X Y) (propWorld_truth₀ v X Y))

/-- **`holds (imp p q)` and `Π (holds p) (holds q)` form a pair of one shape with
one pack**, at every level and for all meanings of `p` and `q`. -/
theorem holdsImp_shapePair (l : Nat) (X Y : (vmodel v).reading.P) :
    ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) (propWorld v X Y)
      holdsImp impDecoding
      (ValueSide.holdsPack (vmodel v).value 2 ((vmodel v).reading.impMeaning X Y))
      (ValueSide.holdsPack (vmodel v).value 2 ((vmodel v).reading.impMeaning X Y)) := by
  have left := holdsImp_interp v l X Y
  have right := ValueSide.decoder_interp (vmodel_valueLaws v) (vprogramDecodes v) holdsImp_step left
  exact ⟨left, right, rfl,
    ValueSide.decoder_shape (vmodel_valueLaws v) (vprogramDecodes v) holdsImp_step left right⟩

/-- `Π (holds p) (holds q)` is a hereditarily total dependent function type. -/
theorem impDecoding_total (l : Nat) (X Y : (vmodel v).reading.P) :
    ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .total
      (propWorld v X Y) impDecoding impDecoding :=
  ValueSide.Shape.total_of_holds_left (vmodel_valueLaws v) (holdsImp_shapePair v l X Y).shape

/-- A world with a generic family over the numbers, of meaning `φ`. -/
def predWorld (φ : (Carrier.arr .num .prop).V (vmodel v).reading) :
    World (vmodel v).reading 1 :=
  Consistency.World.closed.snoc ⟨.arr .num .prop, φ⟩

/-- `holds (all@num f)` is interpreted at every level by the proof pack of
Girard's clause for the meaning of `f`. -/
theorem holdsAll_interp (l : Nat) (φ : (Carrier.arr .num .prop).V (vmodel v).reading) :
    ValueSide.InterpAt (vmodel v).value l (predWorld v φ) holdsAll
      (ValueSide.holdsPack (vmodel v).value 1 ((vmodel v).reading.allMeaning .num φ)) := by
  have read : Consistency.Read (vmodel v).reading (predWorld v φ) (.var 0)
      (.arr .num .prop) φ :=
    Consistency.Read.generic' (S := (vmodel v).reading) (predWorld v φ) (i := 0) rfl
  exact ValueSide.SInterp.holds .refl (.all (allCarrier_allNum v) .refl read)

/-- **`holds (all@num f)` and `Π (x : num). holds (f x)` form a pair of one shape
with one pack**, at every level and for every meaning of `f`. -/
theorem holdsAll_shapePair (l : Nat) (φ : (Carrier.arr .num .prop).V (vmodel v).reading) :
    ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) (predWorld v φ)
      holdsAll allDecoding
      (ValueSide.holdsPack (vmodel v).value 1 ((vmodel v).reading.allMeaning .num φ))
      (ValueSide.holdsPack (vmodel v).value 1 ((vmodel v).reading.allMeaning .num φ)) := by
  have left := holdsAll_interp v l φ
  have right := ValueSide.decoder_interp (vmodel_valueLaws v) (vprogramDecodes v) holdsAll_step left
  exact ⟨left, right, rfl,
    ValueSide.decoder_shape (vmodel_valueLaws v) (vprogramDecodes v) holdsAll_step left right⟩

/-- `Π (x : num). holds (f x)` is a hereditarily total dependent function type. -/
theorem allDecoding_total (l : Nat) (φ : (Carrier.arr .num .prop).V (vmodel v).reading) :
    ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .total
      (predWorld v φ) allDecoding allDecoding :=
  ValueSide.Shape.total_of_holds_left (vmodel_valueLaws v) (holdsAll_shapePair v l φ).shape

/-- **`Σ (holds p) (holds q)` is a hereditarily total dependent pair type.** -/
theorem holdsPairType_total (l : Nat) (X Y : (vmodel v).reading.P) :
    ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .total
      (propWorld v X Y) holdsPairType holdsPairType :=
  ValueSide.shape_holdsPair (vmodel_valueLaws v) (propWorld_truth₁ v X Y) (propWorld_truth₀ v X Y)

/-! ### Transports out of the decodings -/

/-- **The transport out of `Π (holds p) (holds q)` into `num → num` is related to
the daimon.** -/
theorem impDecoding_numArrow (X Y : (vmodel v).reading.P) (f : Tower.Tm 2) :
    (vnumArrow v (propWorld v X Y)).rel (ValueSide.coeApp coeN impDecoding (.pi numT numT) f)
      (.const starN) :=
  vmodel_coe_total_star (impDecoding_total v 0 X Y) (vinterp_numArrow v 0 (propWorld v X Y))
    (vshape_numArrow v 0 (propWorld v X Y)) f

/-- **The transports out of `holds (imp p q)` and out of `Π (holds p) (holds q)`
into `num → num` are related.** -/
theorem holdsImp_numArrow_congr (X Y : (vmodel v).reading.P) (d d' : Tower.Tm 2) :
    (vnumArrow v (propWorld v X Y)).rel (ValueSide.coeApp coeN holdsImp (.pi numT numT) d)
      (ValueSide.coeApp coeN impDecoding (.pi numT numT) d') :=
  vmodel_coe_congr (holdsImp_shapePair v 0 X Y)
    ⟨vinterp_numArrow v 0 (propWorld v X Y), vinterp_numArrow v 0 (propWorld v X Y), rfl,
      vshape_numArrow v 0 (propWorld v X Y)⟩ trivial

/-- **The transport out of `Π (x : num). holds (f x)` into `num → num` is related
to the daimon.** Its domain is the numbers, so the argument transported back
into it is a genuine transport. -/
theorem allDecoding_numArrow (φ : (Carrier.arr .num .prop).V (vmodel v).reading)
    (f : Tower.Tm 1) :
    (vnumArrow v (predWorld v φ)).rel (ValueSide.coeApp coeN allDecoding (.pi numT numT) f)
      (.const starN) :=
  vmodel_coe_total_star (allDecoding_total v 0 φ) (vinterp_numArrow v 0 (predWorld v φ))
    (vshape_numArrow v 0 (predWorld v φ)) f

/-- The transports out of `holds (all@num f)` and out of
`Π (x : num). holds (f x)` into `num → num` are related. -/
theorem holdsAll_numArrow_congr (φ : (Carrier.arr .num .prop).V (vmodel v).reading)
    (d d' : Tower.Tm 1) :
    (vnumArrow v (predWorld v φ)).rel (ValueSide.coeApp coeN holdsAll (.pi numT numT) d)
      (ValueSide.coeApp coeN allDecoding (.pi numT numT) d') :=
  vmodel_coe_congr (holdsAll_shapePair v 0 φ)
    ⟨vinterp_numArrow v 0 (predWorld v φ), vinterp_numArrow v 0 (predWorld v φ), rfl,
      vshape_numArrow v 0 (predWorld v φ)⟩ trivial

/-- **The transport out of `Σ (holds p) (holds q)` into `Σ num num` is related to
the daimon**, in the pack of `Σ num num`, whose pairs need projections of
common shapes. -/
theorem holdsPairType_numPair (X Y : (vmodel v).reading.P) (e : Tower.Tm 2) :
    (vnumPair v (propWorld v X Y)).rel (ValueSide.coeApp coeN holdsPairType (.sigma numT numT) e)
      (.const starN) :=
  vmodel_coe_total_star (holdsPairType_total v 0 X Y)
    (ValueSide.interp_numPair (vmodel_valueLaws v) (propWorld v X Y))
    (ValueSide.shape_numPair (vmodel_valueLaws v) (propWorld v X Y)) e

end ValueModel

/-! ## Controls on identity elimination -/

/-- The numeral one. -/
abbrev oneT {n : Nat} : Tower.Tm n := .app (.const sucN) (.const zeroN)

/-- The step function `λ_ _. num → num` of the large motive. -/
abbrev arrowStep {n : Nat} : Tower.Tm n := .lam (.lam (.pi numT numT))

/-- The motive `λ y _. num-rec (λ_. U0) num (λ_ _. num → num) y`. It needs the
recursor with a motive into the second universe. -/
def largeMotive : Tower.Tm 0 :=
  .lam (.lam (appSpine (.const numRecName) [.lam U0, numT, arrowStep, .var 1]))

/-- Identity elimination with the large motive, from `0` to `1` along `e`, with
the method `0`. -/
def largeJ (e : Tower.Tm 0) : Tower.Tm 0 :=
  appSpine (.const jName) [numT, .const zeroN, largeMotive, .const zeroN, oneT, e]

/-- The constant motive `λ_ _. num`. -/
def constMotive : Tower.Tm 0 := .lam (.lam numT)

/-- Identity elimination with the constant motive at the path `refl 0`, from `0`
to `0`, with the method `0`. -/
def reflJ : Tower.Tm 0 :=
  appSpine (.const jName)
    [numT, .const zeroN, constMotive, .const zeroN, .const zeroN, .refl (.const zeroN)]

/-- `(λ_ _. num) 0 e` computes the numbers, for every path `e`. -/
theorem constMotive_red {e : Tower.Tm 0} :
    WhRed (vmodel v).rules (vmodel v).roles (.app (.app constMotive (.const zeroN)) e) numT :=
  .head (.appFun (.beta _ _)) (.single (.beta _ _))

/-- At `1` the large motive computes `num → num` on the value side. -/
theorem largeMotive_one_red (e : Tower.Tm 0) :
    WhRed (vmodel v).rules (vmodel v).roles (.app (.app largeMotive oneT) e)
      (.pi numT numT) := by
  have iota : (vmodel v).rules.computation.step
      (appSpine (.const numRecName) [.lam U0, numT, arrowStep, oneT] : Tower.Tm 0)
      (.app (.app arrowStep (.const zeroN))
        (appSpine (.const numRecName) [.lam U0, numT, arrowStep, .const zeroN])) :=
    tmodel_step v (tmodelListed v 0 (by decide))
      ⟨.lam U0, [numT, arrowStep], 1, sucN, [.recursive], [.const zeroN], arrowStep,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact .head (.appFun (.beta _ _)) (.head (.beta _ _) (.head (.root iota)
    (.head (.appFun (.beta _ _)) (.single (.beta _ _)))))

/-- At `0` and reflexivity the large motive computes the numbers on the value
side. -/
theorem largeMotive_zero_red :
    WhRed (vmodel v).rules (vmodel v).roles
      (.app (.app largeMotive (.const zeroN)) (.refl (.const zeroN))) numT := by
  have iota : (vmodel v).rules.computation.step
      (appSpine (.const numRecName) [.lam U0, numT, arrowStep, .const zeroN] : Tower.Tm 0)
      numT :=
    tmodel_step v (tmodelListed v 0 (by decide))
      ⟨.lam U0, [numT, arrowStep], 0, zeroN, [], [], numT, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact .head (.appFun (.beta _ _)) (.head (.beta _ _) (.single (.root iota)))

/-- With the large motive, identity elimination from `0` to `1` reduces to the
daimon: it transports its method from the numbers into `num → num`, and the
transport into a dependent function type from the numbers gives the daimon. -/
theorem vmodel_largeJ_red (e : Tower.Tm 0) :
    WhRed (vmodel v).rules (vmodel v).roles (largeJ e) (.const starN) := by
  have table := tmodel_coeTable v
  exact .head (tmodel_j_step v _ _ _ _ _ _) ((table.red_target (largeMotive_one_red v e)).trans
    (.head (table.step_coe .pi) ((table.red_pi (largeMotive_zero_red v)).tail
      (table.step_pi (.star ⟨_, .spine [] tmodelRoles_num_stuck⟩ fun _ _ => nofun)))))

/-- **At reflexivity, identity elimination is the transport of its method along
one type, and is related to the method**, at every type of one shape with
itself. -/
theorem vmodel_j_refl {l n : Nat} {ξ : World (vmodel v).reading n} {A x P d : Tower.Tm n}
    {Q : ValueSide.Pack (vmodel v).value n}
    (same : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ
      (.app (.app P x) (.refl x)) (.app (.app P x) (.refl x)) Q Q)
    (hd : Q.Val d) :
    WhRed (vmodel v).rules (vmodel v).roles (appSpine (.const jName) [A, x, P, d, x, .refl x])
        (ValueSide.coeApp coeN (.app (.app P x) (.refl x)) (.app (.app P x) (.refl x)) d) ∧
      Q.rel (appSpine (.const jName) [A, x, P, d, x, .refl x]) d := by
  have facts := ValueSide.InterpAt.facts (vmodel_valueLaws v) l
  have step := tmodel_j_step v A x P d x (.refl x)
  exact ⟨.single step, facts.expandLeft same.right (.single step) (vmodel_coe_coherent same hd)⟩

/-- With the constant motive `λ_ _. num`, identity elimination at `refl 0` is
related to its method `0` at the numbers. -/
theorem vmodel_j_refl_num (ξ : World (vmodel v).reading 0) :
    (ValueSide.numIndPack (vmodel v).value 0).rel
      (appSpine (.const jName)
        [numT, .const zeroN, constMotive, .const zeroN, .const zeroN, .refl (.const zeroN)])
      (.const zeroN) := by
  have laws := vmodel_valueLaws v
  have interp : ValueSide.InterpAt (vmodel v).value 0 ξ
      (.app (.app constMotive (.const zeroN)) (.refl (.const zeroN)))
      (ValueSide.numIndPack (vmodel v).value 0) :=
    ValueSide.InterpAt.num laws 0 (constMotive_red v)
  exact (vmodel_j_refl v ⟨interp, interp, rfl,
    .const (.inr ⟨_, laws.num_role⟩) (constMotive_red v) (constMotive_red v)⟩
      (ValueSide.numIndPack_rel.mpr ⟨.zero, .zero .refl, .zero .refl⟩)).2

/-- **At a path stuck on the daimon, identity elimination returns its method.**
With the constant motive `λ_ _. num`, identity elimination from `0` to `0` along
the daimon reduces to `0`: its transport between two types that compute the
numbers returns the method, by the constant row of the table. -/
theorem vmodel_j_star_num :
    WhRed (vmodel v).rules (vmodel v).roles
      (appSpine (.const jName)
        [numT, .const zeroN, constMotive, .const zeroN, .const zeroN, .const starN])
      (.const zeroN) :=
  .head (tmodel_j_step v _ _ _ _ _ _)
    ((vmodel_coeRules v).const (c := numN) (.inr ⟨_, tmodelRoles_num⟩) (constMotive_red v)
      (constMotive_red v))

/-- **The transport of a valid method is valid**: identity elimination, whose
motive's instances at the point with reflexivity and at the endpoint with the
path are interpreted and each of one shape with itself, applied to a valid
value of the first, is a valid value of the second. -/
theorem vmodel_j_val {l n : Nat} {ξ : World (vmodel v).reading n} {A x P d y e : Tower.Tm n}
    {PX PY : ValueSide.Pack (vmodel v).value n}
    (hX : ValueSide.InterpAt (vmodel v).value l ξ (.app (.app P x) (.refl x)) PX)
    (hY : ValueSide.InterpAt (vmodel v).value l ξ (.app (.app P y) e) PY)
    (coverX : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ
      (.app (.app P x) (.refl x)) (.app (.app P x) (.refl x)))
    (coverY : ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ
      (.app (.app P y) e) (.app (.app P y) e))
    (hd : PX.Val d) : PY.Val (appSpine (.const jName) [A, x, P, d, y, e]) := by
  have facts := ValueSide.InterpAt.facts (vmodel_valueLaws v) l
  have step := tmodel_j_step v A x P d y e
  exact facts.expandRel hY (.single step) (.single step)
    (vmodel_coe_val hX hY coverX coverY hd)

/-- **Identity eliminations of related methods between pairs of instances of the
motives are related**: the transports are, and identity elimination computes
to them. -/
theorem vmodel_j_congr {l n : Nat} {ξ : World (vmodel v).reading n}
    {A x P d y e A' x' P' d' y' e' : Tower.Tm n} {PX PX' PY PY' : ValueSide.Pack (vmodel v).value n}
    (sources : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ
      (.app (.app P x) (.refl x)) (.app (.app P' x') (.refl x')) PX PX')
    (targets : ValueSide.ShapePair (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) ξ
      (.app (.app P y) e) (.app (.app P' y') e') PY PY')
    (hdd' : PX.rel d d') :
    PY.rel (appSpine (.const jName) [A, x, P, d, y, e])
      (appSpine (.const jName) [A', x', P', d', y', e']) := by
  have facts := ValueSide.InterpAt.facts (vmodel_valueLaws v) l
  exact facts.expandRel targets.left (.single (tmodel_j_step v A x P d y e))
    (.single (tmodel_j_step v A' x' P' d' y' e')) (vmodel_coe_congr sources targets hdd')

/-- **The large motive does not break the transport.** With the motive
`λ y _. num-rec (λ_. U0) num (λ_ _. num → num) y`, from `0` to `1` along any
path `e`, identity elimination transports the method `0` from the numbers into
`num → num`: the source is no dependent function type, so the transport gives
the daimon, and the value is valid at every pack of the result type `P 1 e`.
The method itself is no value there (`vnumArrow_not_rel_zero`). -/
theorem vmodel_largeJ_valid (ξ : World (vmodel v).reading 0) (e : Tower.Tm 0) :
    WhRed (vmodel v).rules (vmodel v).roles (largeJ e) (.const starN) ∧
      ∀ {P : ValueSide.Pack (vmodel v).value 0},
        ValueSide.DenS (vmodel v).value ξ (.app (.app largeMotive oneT) e) P →
          P.Val (largeJ e) := by
  have laws := vmodel_valueLaws v
  have facts := ValueSide.InterpAt.facts laws 0
  have rX := largeMotive_zero_red v
  have rY := largeMotive_one_red v e
  have jStep := tmodel_j_step v numT (.const zeroN) largeMotive (.const zeroN) oneT e
  have hX : ValueSide.InterpAt (vmodel v).value 0 ξ
      (.app (.app largeMotive (.const zeroN)) (.refl (.const zeroN)))
      (ValueSide.numIndPack (vmodel v).value 0) :=
    ValueSide.InterpAt.num laws 0 rX
  have hY : ValueSide.InterpAt (vmodel v).value 0 ξ (.app (.app largeMotive oneT) e)
      (vnumArrow v ξ) :=
    ValueSide.InterpAt.expand rY (vinterp_numArrow v 0 ξ)
  obtain ⟨-, val⟩ := ValueSide.coe_num_numArrow laws facts (vmodel_coeRules v) hX hY rX rY
    (d := .const zeroN) (ValueSide.numIndPack_rel.mpr ⟨.zero, .zero .refl, .zero .refl⟩)
  refine ⟨vmodel_largeJ_red v e, fun {P} den => ?_⟩
  obtain rfl := ValueSide.DenS.deterministic laws den ⟨0, hY⟩
  exact facts.expandRel hY (.single jStep) (.single jStep) val

/-! ## The constants with dependent types -/

open Package (iterName eqAtName keepName transportName composeName returnIterName
  sucMoveName sucStepName numRecType iterType eqAtType keepType transportType composeType
  returnIterType returnIterResult transportTelescope composeTelescope)

/-- The recursor is valid: its declared type is typed in the stage of the
numbers and their constructors, whose fundamental lemma gives the validity of
the type and of its parts. -/
theorem vmodel_valid_numRec' : ModelS.ValidTmS (vmodel v) .nil (.const numRecName) numRecType := by
  have sound₀ := vstage_soundS_of v (names := [numN, zeroN, sucN]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact vmodel_valid_num v
      · exact vmodel_valid_zero v
      · exact vmodel_valid_suc v
  obtain ⟨validT, partsT, _⟩ := ModelS.Derivable.validS sound₀ numRecType_typed trivial
  exact vmodel_valid_numRec v (validT.validTy (.sort _)) partsT

/-- The iterator is valid: its declared type is typed in the stage of the
numbers. -/
theorem vmodel_valid_iter' : ModelS.ValidTmS (vmodel v) .nil (.const iterName) iterType := by
  have sound₀ := vstage_soundS_of v (names := [numN]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      subst mem
      obtain rfl := Option.some.inj declared
      exact vmodel_valid_num v
  obtain ⟨validT, partsT, _⟩ := ModelS.Derivable.validS sound₀ (iterType_typed (by simp)) trivial
  exact vmodel_valid_iter v (validT.validTy (.sort _)) partsT

/-! ## Definitions by one equation -/

theorem vmodel_valid_eqAt : ModelS.ValidTmS (vmodel v) .nil (.const eqAtName) eqAtType := by
  have sound₀ := vstage_soundS_of v (names := [numN, zeroN, sucN, addN]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact vmodel_valid_num v
      · exact vmodel_valid_zero v
      · exact vmodel_valid_suc v
      · exact vmodel_valid_add v
  exact ModelS.ValidTmS.definition (Θ := eqAtTele) (C := U0) (rhs := eqAtRhs) sound₀
    ⟨_, .sort _, eqAtType_typed⟩ eqAtBody_typed
    (fun σ => vmodel_rule v (listed 4 (by decide)) (by decide) ⟨σ, rfl, rfl⟩)
    (fun _ sns X h => KCand.definition_mem objectShape X objectRoles_eqAt
      (objectStep_definition (listed 4 (by decide)) (by decide)) sns h)

theorem vmodel_valid_keep : ModelS.ValidTmS (vmodel v) .nil (.const keepName) keepType :=
  ModelS.ValidTmS.definition (Θ := keepTele) (C := .sigma (.var 3) (.app (.var 3) (.var 0)))
    (rhs := keepRhs)
    (vstage_soundS_of v (names := []) (by decide) fun _ mem => absurd mem List.not_mem_nil)
    ⟨_, .sort _, keepType_typed⟩ keepBody_typed
    (fun σ => vmodel_rule v (listed 6 (by decide)) (by decide) ⟨σ, rfl, rfl⟩)
    (fun _ sns X h => KCand.definition_mem objectShape X objectRoles_keep
      (objectStep_definition (listed 6 (by decide)) (by decide)) sns h)

theorem vmodel_valid_transport :
    ModelS.ValidTmS (vmodel v) .nil (.const transportName) transportType :=
  ModelS.ValidTmS.definition (Θ := transportTelescope)
    (C := .sigma (.var 5) (.app (.var 5) (.var 0))) (rhs := transportRhs)
    (vstage_soundS_of v (names := []) (by decide) fun _ mem => absurd mem List.not_mem_nil)
    ⟨_, .sort _, transportType_typed⟩ transportBody_typed
    (fun σ => vmodel_rule v (listed 7 (by decide)) (by decide) ⟨σ, rfl, rfl⟩)
    (fun _ sns X h => KCand.definition_mem objectShape X objectRoles_transport
      (objectStep_definition (listed 7 (by decide)) (by decide)) sns h)

theorem vmodel_valid_compose :
    ModelS.ValidTmS (vmodel v) .nil (.const composeName) composeType :=
  ModelS.ValidTmS.definition (Θ := composeTelescope)
    (C := .sigma (.var 5) (.app (.var 5) (.var 0))) (rhs := composeRhs)
    (vstage_soundS_of v (names := []) (by decide) fun _ mem => absurd mem List.not_mem_nil)
    ⟨_, .sort _, composeType_typed⟩ composeBody_typed
    (fun σ => vmodel_rule v (listed 8 (by decide)) (by decide) ⟨σ, rfl, rfl⟩)
    (fun _ sns X h => KCand.definition_mem objectShape X objectRoles_compose
      (objectStep_definition (listed 8 (by decide)) (by decide)) sns h)

theorem vmodel_valid_returnIter :
    ModelS.ValidTmS (vmodel v) .nil (.const returnIterName) returnIterType := by
  have sound₀ := vstage_soundS_of v (names := [numN, zeroN, sucN, iterName]) (by decide)
    fun name mem type declared => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact vmodel_valid_num v
      · exact vmodel_valid_zero v
      · exact vmodel_valid_suc v
      · exact vmodel_valid_iter' v
  exact ModelS.ValidTmS.definition (Θ := returnIterTele) (C := returnIterResult)
    (rhs := returnIterRhs) sound₀ ⟨_, .sort _, returnIterType_typed (by simp)⟩
    (returnIterBody_typed (by simp) (by simp))
    (fun σ => vmodel_rule v (listed 10 (by decide)) (by decide) ⟨σ, rfl, rfl⟩)
    (fun _ sns X h => KCand.definition_mem objectShape X objectRoles_returnIter
      (objectStep_definition (listed 10 (by decide)) (by decide)) sns h)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
