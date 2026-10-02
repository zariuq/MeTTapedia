import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Definable

/-!
# The square at data carriers: model SN's truth reading and the set tower

Model SN reads the object package's proposition codes through the truth reading of its
consistency model (`Consistency.Setting.truthReading`): a code means a Lean proposition,
implication is `→`, the quantifier `all@A` is `∀` over the meanings at the carrier `A`, and the
equation `eq@A` is `=`. A meaning at the numbers is a class of closed terms computing one
numeral. The set tower reads the same codes by truth values `Ω = 𝒫 {∅}`, the numbers by `ω`,
and the quantifier by a trace product over the set of a simple type (`objectSetConsts`).

**The carriers** (`NumCarrier`): `prop`, the numbers, and functions into generic carriers, that
is, the simple types over `prop` and `num` whose function types end in `prop`. They extend the
carriers without data of the reading square (`Square.PureCarrier`) by the numbers; the rigid base
types are left out, since the only one of the object package, the sets, is read by `V_ω` in the
tower (see `ObjectSetSquareControls`).

**The correspondence** (`valEquiv`). At every such carrier the meanings of model SN's truth
reading are in bijection with the elements of the carrier's set in the tower:

* a proposition is a truth value (`Square.propEquiv`);
* a value of the numbers, the class of the numeral `k`, is the set `numeral k ∈ ω`
  (`numEquiv`, `valEquiv_numClass`);
* a function of meanings is a trace function (`tracePiEquiv`).

**The square** (`square_all`, `square_eq`, with `square_all_num`, `square_eq_num` and the
impredicative `square_all_prop`): `truthCode` carries the meaning of the quantifier at every such
carrier, the numbers included, and of the equation to the tower's trace product and identity
truth value. Implication is carrier free (`Square.square_imp`).

**The code constants** (`impConst_square`, `allConst_square`, `eqConst_square`): the values the
tower gives the constants `imp`, `all@A` and `eq@A` at these carriers are, through the
correspondence, model SN's meanings of implication, of the quantifier and of the equation. These
are the cases of the constants in the square on code terms (`ObjectSetSquareTerms`).

`Classical.choice` enters only through the set layer: the trace products and graphs of `ZFSet`,
and the natural of a number (`natOf`) in the inverse of `numEquiv`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (pisCtx)
open Presentation.TypedEquality.Impredicative.Consistency (Carrier Kind Setting Q numClass sucClass
  numClass_injective sucClass_numClass)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (Elements)
open ZFSetTraceProducts (traceApp tracePiSet tracePiEquiv)
open ZFSetTraceProofDecoding (truthCode)
open Mettapedia.Logic

universe u

namespace CodeModel
namespace SetSquare

/-! ## The carriers -/

/-- **The carriers built from `prop`, the numbers and functions into generic carriers**, with
their kinds: `prop` and every function type are generic, the numbers are data. -/
inductive NumCarrier : Kind → Type where
  | prop : NumCarrier .gen
  | num : NumCarrier .data
  | arr {k : Kind} (A : NumCarrier k) (B : NumCarrier .gen) : NumCarrier .gen

namespace NumCarrier

/-- The consistency model's carrier. -/
@[reducible] def toCarrier : {k : Kind} → NumCarrier k → Carrier k
  | _, .prop => .prop
  | _, .num => .num
  | _, .arr A B => .arr A.toCarrier B.toCarrier

/-- The simple type of the profile. -/
@[reducible] def toTy : {k : Kind} → NumCarrier k → HOL.Ty SetProfile.SetBase
  | _, .prop => .prop
  | _, .num => SetProfile.numTy
  | _, .arr A B => .arr A.toTy B.toTy

/-- The object package's carrier of the simple type is the carrier. -/
theorem carrierOf_toTy : ∀ {k : Kind} (A : NumCarrier k), carrierOf A.toTy = ⟨k, A.toCarrier⟩
  | _, .prop => rfl
  | _, .num => rfl
  | _, .arr A B => by
      show (⟨(carrierOf B.toTy).1, .arr (carrierOf A.toTy).2 (carrierOf B.toTy).2⟩ :
        Σ k, Carrier k) = _
      rw [carrierOf_toTy A, carrierOf_toTy B]

end NumCarrier

/-- The meanings of a carrier in the truth reading of a setting. -/
abbrev Val {Head : Type} (S : Setting Head) {k : Kind} (A : NumCarrier k) : Type :=
  Carrier.Val S.numerals Prop A.toCarrier

/-! ## The numbers -/

section Numbers

variable {Head : Type} {S : Setting Head}

/-- The set of a value of the numbers: the numeral it computes, read off by separation in `ω`. -/
noncomputable def numSet (q : Q S.numerals .num) : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.sep (fun x => ∃ k, x = numeral k ∧ q = numClass S.numerals k) ZFSet.omega)

/-- The set of the class of a numeral is the numeral. -/
theorem numSet_numClass (laws : S.Laws) (k : ℕ) :
    numSet.{u} (numClass S.numerals k) = numeral k := by
  have single : ZFSet.sep (fun x => ∃ j, x = numeral.{u} j ∧
      numClass S.numerals k = numClass S.numerals j) ZFSet.omega = {numeral k} := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, ZFSet.mem_singleton]
    constructor
    · rintro ⟨-, j, rfl, same⟩
      rw [numClass_injective laws.numerals same]
    · rintro rfl
      exact ⟨numeral_mem_omega k, k, rfl, rfl⟩
  rw [numSet, single, ZFSet.sUnion_singleton]

theorem numSet_mem (laws : S.Laws) (q : Q S.numerals .num) : numSet.{u} q ∈ ZFSet.omega := by
  obtain ⟨k, rfl⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass q
  rw [numSet_numClass laws]
  exact numeral_mem_omega k

/-- **The values of the numbers are the natural numbers**: the class of the numeral `k`
corresponds to `numeral k ∈ ω`. -/
noncomputable def numEquiv (laws : S.Laws) : Q S.numerals .num ≃ Elements (ZFSet.omega.{u}) where
  toFun q := ⟨numSet q, numSet_mem laws q⟩
  invFun x := numClass S.numerals (natOf x.1)
  left_inv q := by
    obtain ⟨k, rfl⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass q
    simp only [numSet_numClass laws, natOf_numeral]
  right_inv x := Subtype.ext (by simp only [numSet_numClass laws, numeral_natOf x.2])

end Numbers

/-! ## The correspondence of carriers -/

section Correspondence

variable {Head : Type} {S : Setting Head} (laws : S.Laws)

/-- **The carriers correspond**: a meaning of a carrier in the truth reading is an element of
the carrier's set in the tower. -/
noncomputable def valEquiv : {k : Kind} → (A : NumCarrier k) →
    Val S A ≃ Elements (simpleSet.{u} A.toTy)
  | _, .prop => Square.propEquiv
  | _, .num => numEquiv laws
  | _, .arr A B => (Equiv.arrowCongr (valEquiv A) (valEquiv B)).trans
      (tracePiEquiv (simpleSet A.toTy) fun _ => simpleSet B.toTy).symm

@[simp] theorem valEquiv_prop (P : Prop) : (valEquiv.{u} laws .prop P).1 = truthCode P := rfl

/-- The class of the numeral `k` is the set `numeral k`. -/
@[simp] theorem valEquiv_numClass (k : ℕ) :
    (valEquiv.{u} laws .num (numClass S.numerals k)).1 = numeral k :=
  numSet_numClass laws k

/-- The successor of a value of the numbers is the successor of its set. -/
theorem valEquiv_sucClass (q : Q S.numerals .num) :
    (valEquiv.{u} laws .num (sucClass S.numerals q)).1 =
      insert (valEquiv.{u} laws .num q).1 (valEquiv.{u} laws .num q).1 := by
  obtain ⟨k, rfl⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass q
  rw [sucClass_numClass, valEquiv_numClass, valEquiv_numClass]
  rfl

/-- Every element of a carrier's set is the set of a meaning. -/
theorem exists_valEquiv {k : Kind} (A : NumCarrier k) {x : ZFSet.{u}}
    (hx : x ∈ simpleSet.{u} A.toTy) : ∃ v : Val S A, (valEquiv laws A v).1 = x :=
  ⟨(valEquiv laws A).symm ⟨x, hx⟩, by rw [Equiv.apply_symm_apply]⟩

/-- **Application**: the trace function of a function of meanings, applied to the set of a
meaning, is the set of the function's value there. -/
theorem valEquiv_arr_apply {k : Kind} (A : NumCarrier k) (B : NumCarrier .gen)
    (φ : Val S (.arr A B)) (v : Val S A) :
    traceApp (valEquiv.{u} laws (.arr A B) φ).1 (valEquiv laws A v).1 =
      (valEquiv laws B (φ v)).1 := by
  have beta := congrArg Subtype.val (congrFun (ZFSetTraceProducts.trace_beta
    (a := simpleSet.{u} A.toTy) (b := fun _ => simpleSet.{u} B.toTy)
    (fun x => valEquiv laws B (φ ((valEquiv laws A).symm x)))) (valEquiv laws A v))
  simp only [Equiv.symm_apply_apply] at beta
  exact beta

/-- **Extensionality**: a trace function of the set of `A → B` is the set of a function of
meanings when it agrees with it at the set of every meaning. -/
theorem eq_valEquiv_arr {k : Kind} (A : NumCarrier k) (B : NumCarrier .gen) {t : ZFSet.{u}}
    (ht : t ∈ simpleSet.{u} (NumCarrier.arr A B).toTy) {φ : Val S (.arr A B)}
    (pointwise : ∀ v, traceApp t (valEquiv laws A v).1 = (valEquiv laws B (φ v)).1) :
    t = (valEquiv laws (.arr A B) φ).1 := by
  refine tracePiSet_ext ht (valEquiv laws (.arr A B) φ).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := exists_valEquiv laws A hx
  rw [pointwise v, valEquiv_arr_apply]

end Correspondence

/-! ## The square at every carrier -/

section Square

variable {Head : Type} {S : Setting Head} (laws : S.Laws)

/-- The family on the tower's set of a carrier induced by a predicate on its meanings. -/
noncomputable def lift {k : Kind} (A : NumCarrier k) (φ : Val S A → Prop) :
    ZFSet.{u} → ZFSet.{u} :=
  fun x => truthCode (∃ hx : x ∈ simpleSet.{u} A.toTy, φ ((valEquiv laws A).symm ⟨x, hx⟩))

/-- **The quantifier at every carrier**, the numbers and `prop` included: the tower reads
`∀ v, φ v` as the trace product of the induced family over the carrier's set. -/
theorem square_all {k : Kind} (A : NumCarrier k) (φ : Val S A → Prop) :
    truthCode.{u} (S.truthReading.allMeaning A.toCarrier φ) =
      tracePiSet (simpleSet A.toTy) (lift laws A φ) := by
  change _ = tracePiSet (simpleSet A.toTy)
    (fun x => truthCode (∃ hx : x ∈ simpleSet A.toTy, φ ((valEquiv laws A).symm ⟨x, hx⟩)))
  rw [Controls.tracePiSet_truthCode]
  congr 1
  apply propext
  change (∀ v, φ v) ↔ ∀ x ∈ simpleSet A.toTy, ∃ hx : x ∈ simpleSet A.toTy,
    φ ((valEquiv laws A).symm ⟨x, hx⟩)
  constructor
  · intro all x hx
    exact ⟨hx, all _⟩
  · intro all v
    obtain ⟨_, holds⟩ := all _ (valEquiv laws A v).2
    simpa using holds

/-- **The equation at every carrier**: the tower reads `v = w` as the truth value of the
equality of the corresponding sets. -/
theorem square_eq {k : Kind} (A : NumCarrier k) (v w : Val S A) :
    truthCode.{u} (S.truthReading.eqMeaning A.toCarrier v w) =
      truthCode ((valEquiv laws A v).1 = (valEquiv laws A w).1) := by
  congr 1
  apply propext
  change v = w ↔ _
  constructor
  · rintro rfl
    rfl
  · intro same
    exact (valEquiv laws A).injective (Subtype.ext same)

/-- **The quantifier over the numbers**, `all@num`: the trace product over `ω`. -/
theorem square_all_num (φ : Q S.numerals .num → Prop) :
    truthCode.{u} (S.truthReading.allMeaning Carrier.num φ) =
      tracePiSet ZFSet.omega (lift laws .num φ) :=
  square_all laws .num φ

include laws in
/-- **The equation at the numbers**, `eq@num`, between the values of two numerals: the truth
value of the equality of the numerals in `ω`. -/
theorem square_eq_num (k j : ℕ) :
    truthCode.{u} (S.truthReading.eqMeaning Carrier.num (numClass S.numerals k)
      (numClass S.numerals j)) = truthCode (numeral.{u} k = numeral j) :=
  (square_eq laws .num (numClass S.numerals k) (numClass S.numerals j)).trans (by
    rw [valEquiv_numClass, valEquiv_numClass])

/-- **The impredicative quantifier**, `all@prop`: the trace product over `Ω`. -/
theorem square_all_prop (φ : Prop → Prop) :
    truthCode.{u} (S.truthReading.allMeaning Carrier.prop φ) =
      tracePiSet Square.omega (lift laws .prop φ) :=
  square_all laws .prop φ

/-- Reading truth back: a meaning at `prop` holds exactly when its set contains the empty
proof. -/
theorem empty_mem_valEquiv_prop (P : Prop) : (∅ : ZFSet.{u}) ∈ (valEquiv laws .prop P).1 ↔ P :=
  Square.square_truth_iff P

end Square

/-! ## The values of the code constants -/

section Constants

variable (h : CofinalInaccessibles.{u})

/-- The tower's value of `imp` is a trace function between truth values. -/
theorem impConst_mem :
    objectSetConsts h impN ∈ simpleSet.{u} (.arr .prop (.arr .prop .prop)) := by
  have typed := setRaw_typed h .imp
  rw [← objectSetConsts_of h (show objConst impN = .imp by decide), declType_imp,
    ev_pisCtx] at typed
  change objectSetConsts h impN ∈ tracePiSet (objectSetConsts h propN)
    (fun _ => tracePiSet (objectSetConsts h propN) fun _ => objectSetConsts h propN) at typed
  rw [setConst_prop h] at typed
  exact typed

/-- The tower's value of `all@A` is a trace function from the predicates on `A`. -/
theorem allConst_mem (type : HOL.Ty SetProfile.SetBase) :
    objectSetConsts h (SetProfile.allName type) ∈ simpleSet.{u} (.arr (.arr type .prop) .prop) := by
  have typed := setRaw_typed h (.all type)
  rw [← objectSetConsts_of h (objConst_allName type), declType_all, ev_pisCtx] at typed
  change objectSetConsts h (SetProfile.allName type) ∈ tracePiSet
    (ev (objHeads h) (objectSetConsts h)
      (liftTm (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 (.arr type .prop)))
      Fin.elim0) (fun _ => objectSetConsts h propN) at typed
  rw [ev_objTypeAt h, setConst_prop h] at typed
  exact typed

/-- The tower's value of `eq@A` is a curried trace function on `A`. -/
theorem eqConst_mem (type : HOL.Ty SetProfile.SetBase) :
    objectSetConsts h (SetProfile.eqName type) ∈ simpleSet.{u} (.arr type (.arr type .prop)) := by
  have typed := setRaw_typed h (.eq type)
  rw [← objectSetConsts_of h (objConst_eqName type), declType_eq, ev_pisCtx] at typed
  change objectSetConsts h (SetProfile.eqName type) ∈ tracePiSet
    (ev (objHeads h) (objectSetConsts h)
      (liftTm (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type)) Fin.elim0)
    (fun x => tracePiSet (ev (objHeads h) (objectSetConsts h)
      (liftTm (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
      (extend Fin.elim0 x)) fun _ => objectSetConsts h propN) at typed
  simp only [ev_objTypeAt h, setConst_prop h] at typed
  exact typed

variable {Head : Type} {S : Setting Head} (laws : S.Laws)

/-- **Implication.** The tower's value of `imp` is, through the correspondence, model SN's
implication `P → Q`. -/
theorem impConst_square :
    objectSetConsts h impN = (valEquiv.{u} laws (.arr .prop (.arr .prop .prop))
      (fun P Q => S.truthReading.impMeaning P Q)).1 := by
  have member : objectSetConsts h impN ∈ tracePiSet (simpleSet.{u} NumCarrier.prop.toTy)
      (fun _ => simpleSet.{u} (NumCarrier.arr .prop .prop).toTy) := impConst_mem h
  refine eq_valEquiv_arr laws .prop (.arr .prop .prop) member fun P => ?_
  have fibre : traceApp (objectSetConsts h impN) (valEquiv laws .prop P).1 ∈
      simpleSet.{u} (NumCarrier.arr .prop .prop).toTy :=
    traceApp_mem_fibre (b := fun _ => simpleSet.{u} (NumCarrier.arr .prop .prop).toTy) member
      (valEquiv laws .prop P).2
  refine eq_valEquiv_arr laws .prop .prop fibre fun Q => ?_
  rw [imp_apply h (valEquiv laws .prop P).2 (valEquiv laws .prop Q).2]
  change truthCode ((∅ : ZFSet.{u}) ∈ truthCode P → (∅ : ZFSet.{u}) ∈ truthCode Q) =
    truthCode (P → Q)
  rw [Square.square_truth_iff, Square.square_truth_iff]

/-- **The quantifier at every carrier.** The tower's value of `all@A` is, through the
correspondence, model SN's quantifier `∀ v, φ v` over the meanings at `A`. -/
theorem allConst_square {k : Kind} (A : NumCarrier k) :
    objectSetConsts h (SetProfile.allName A.toTy) = (valEquiv.{u} laws (.arr (.arr A .prop) .prop)
      (fun φ => S.truthReading.allMeaning A.toCarrier φ)).1 := by
  refine eq_valEquiv_arr laws (.arr A .prop) .prop (allConst_mem h A.toTy) fun φ => ?_
  rw [all_apply h A.toTy (valEquiv laws (.arr A .prop) φ).2]
  change _ = truthCode (∀ v, φ v)
  congr 1
  apply propext
  constructor
  · intro all v
    have holds := all _ (valEquiv laws A v).2
    rw [valEquiv_arr_apply] at holds
    exact (Square.square_truth_iff _).mp holds
  · intro all x hx
    obtain ⟨v, rfl⟩ := exists_valEquiv laws A hx
    rw [valEquiv_arr_apply]
    exact (Square.square_truth_iff _).mpr (all v)

/-- **The equation at every carrier.** The tower's value of `eq@A` is, through the
correspondence, model SN's equation `v = w` between meanings at `A`. -/
theorem eqConst_square {k : Kind} (A : NumCarrier k) :
    objectSetConsts h (SetProfile.eqName A.toTy) = (valEquiv.{u} laws (.arr A (.arr A .prop))
      (fun v w => S.truthReading.eqMeaning A.toCarrier v w)).1 := by
  have member : objectSetConsts h (SetProfile.eqName A.toTy) ∈ tracePiSet (simpleSet.{u} A.toTy)
      (fun _ => simpleSet.{u} (NumCarrier.arr A .prop).toTy) := eqConst_mem h A.toTy
  refine eq_valEquiv_arr laws A (.arr A .prop) member fun v => ?_
  have fibre : traceApp (objectSetConsts h (SetProfile.eqName A.toTy)) (valEquiv laws A v).1 ∈
      simpleSet.{u} (NumCarrier.arr A .prop).toTy :=
    traceApp_mem_fibre (b := fun _ => simpleSet.{u} (NumCarrier.arr A .prop).toTy) member
      (valEquiv laws A v).2
  refine eq_valEquiv_arr laws A .prop fibre fun w => ?_
  rw [eq_apply h A.toTy (valEquiv laws A v).2 (valEquiv laws A w).2]
  change truthCode ((valEquiv laws A v).1 = (valEquiv laws A w).1) = truthCode (v = w)
  congr 1
  apply propext
  exact ⟨fun same => (valEquiv laws A).injective (Subtype.ext same), fun same => same ▸ rfl⟩

end Constants

end SetSquare
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
