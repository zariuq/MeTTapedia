import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSquareTerms
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetValuesControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSteps

/-!
# Controls for the square at data carriers and on code terms

**Positive controls.** Closed code terms of the syntax (`CodeTerm`), each true in both readings
or false in both, for model SN of the object package and the set tower:

* `zero = zero` at the numbers holds in both (`zeroEqZero_both`);
* `∀ n. zero = suc n` holds in neither (`zeroEqSuc_neither`);
* the impredicative codes agree: `∀ p : prop. p ⇒ p` holds in both (`propImpSelf_both`), and
  `∀ p : prop. p` in neither (`propAll_neither`);
* induction on the numbers, quantified over every predicate `num → prop`, holds in both
  (`numInduction_both`);
* arithmetic through the computation of `add`: `add (suc zero) (suc zero) = suc (suc zero)` and
  commutativity of addition hold in both (`onePlusOne_both`, `addComm_both`), and
  `∀ n. add n zero = suc n` in neither (`addZeroSuc_neither`).

**Negative controls.** Each shows that a restriction of the square is needed.

* **The sets, at the carrier.** The consistency model reads the rigid type `set` by one point,
  so any two sets are equal in it, while the tower reads `set` as `V_ω`, which has the two
  distinct points `∅` and `𝒫 ∅`. No correspondence of carriers exists (`no_setEquiv`), and the
  trace-product reading of `∀ x y : set. x = y` differs from model SN's (`square_fails_set`).
* **The sets, at a code term.** The code `∀ x y : set. x = y` holds in model SN's truth reading
  (`setEqCode_modelSN`) and its value in the tower is the false truth value
  (`setEqCode_tower`).
* **A function carrier into the numbers.** Model SN reads the data carrier `prop → num` by
  classes of terms, which cannot inspect their argument, so the code
  `∀ f : prop → num. ∀ p q : prop. f p = f q` holds in it (`parametricCode_modelSN`). The tower
  has every function from `Ω` into `ω`, among them the inclusion, and the code is false there
  (`parametricCode_tower`).
* **A computing data term at an ill-typed instance.** The data of the syntax are built from
  numerals and `add`. A term of the package that model SN's reduction computes to a numeral can
  have another value in the tower when its instance is not typed: the recursor at the motive
  `λn. prop` with the value at zero `two`, a number and not a code, computes `two` in model SN,
  while the tower's traced graph gives `∅` outside the motive's value `Ω` at zero. So
  `eq@num (num-rec (λn. prop) two (λn p. p) zero) two` holds in model SN's truth reading
  (`recCode_modelSN`) and is false in the tower (`recCode_tower`).

The functions on the numbers, `num → num`, are the subject of `ObjectSetSquareChoice`.

The tower's side of the control at `prop → num` uses that `Ω = 𝒫 {∅}` has exactly the two
elements `∅` and `{∅}` (`truthValue_mem_omega`), a case split of the classical set layer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Consistency (Carrier Kind Setting DataSetting Q
  numClass sucClass Truth Read World DataEq dataValue dataValue_sound numClass_injective NumVal
  numVal_numeral)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (Elements graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta traceApp_empty)
open ZFSetTraceProofDecoding (truthCode)
open FormationSensitiveHOLInterface (typeAt)
open Mettapedia.Logic

universe u

namespace CodeModel
namespace SetSquare

/-! ## Positive controls -/

section Codes

/-- `zero = zero` at the numbers. -/
def zeroEqZero : CodeTerm [] .prop := .eqOf .zero .zero

/-- `∀ n : num. zero = suc n`. -/
def zeroEqSuc : CodeTerm [] .prop := .allOf .num (.eqOf .zero (.suc (.var .zero)))

/-- `∀ p : prop. p ⇒ p`, an impredicative code. -/
def propImpSelf : CodeTerm [] .prop := .allOf .prop (.impOf (.var .zero) (.var .zero))

/-- `∀ p : prop. p`, the false impredicative code. -/
def propAll : CodeTerm [] .prop := .allOf .prop (.var .zero)

/-- Induction on the numbers over every predicate:
`∀ P : num → prop. P zero ⇒ (∀ n. P n ⇒ P (suc n)) ⇒ ∀ n. P n`. -/
def numInduction : CodeTerm [] .prop :=
  .allOf (.arr .num .prop) (.impOf (.app (.var .zero) .zero)
    (.impOf (.allOf .num (.impOf (.app (.var (.succ .zero)) (.var .zero))
        (.app (.var (.succ .zero)) (.suc (.var .zero)))))
      (.allOf .num (.app (.var (.succ .zero)) (.var .zero)))))

/-- `add (suc zero) (suc zero) = suc (suc zero)`. -/
def onePlusOne : CodeTerm [] .prop :=
  .eqOf (.add (.suc .zero) (.suc .zero)) (.suc (.suc .zero))

/-- Commutativity of addition: `∀ n m : num. add n m = add m n`. -/
def addComm : CodeTerm [] .prop :=
  .allOf .num (.allOf .num (.eqOf (.add (.var (.succ .zero)) (.var .zero))
    (.add (.var .zero) (.var (.succ .zero)))))

/-- `∀ n : num. add n zero = suc n`, false. -/
def addZeroSuc : CodeTerm [] .prop :=
  .allOf .num (.eqOf (.add (.var .zero) .zero) (.suc (.var .zero)))

end Codes

section Meanings

variable {Head : Type} (S : Setting Head)
  (plus : Q S.numerals .num → Q S.numerals .num → Q S.numerals .num)

theorem zeroEqZero_meaning : zeroEqZero.meaning S plus MEnv.nil := rfl

theorem zeroEqSuc_meaning (laws : S.Laws) : ¬ zeroEqSuc.meaning S plus MEnv.nil := fun all => by
  have same : numClass S.numerals 0 = numClass S.numerals 1 := all (numClass S.numerals 0)
  exact absurd (numClass_injective laws.numerals same) (by decide)

theorem propImpSelf_meaning : propImpSelf.meaning S plus MEnv.nil := fun _ holds => holds

theorem propAll_meaning : ¬ propAll.meaning S plus MEnv.nil := fun all => all False

/-- Induction over the values of the numbers: every value is the class of a numeral. -/
theorem induction_numClass (R : Q S.numerals .num → Prop) (atZero : R (numClass S.numerals 0))
    (step : ∀ q, R q → R (sucClass S.numerals q)) : ∀ q, R q := by
  intro q
  obtain ⟨k, rfl⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass q
  induction k with
  | zero => exact atZero
  | succ k ih => exact step _ ih

theorem numInduction_meaning : numInduction.meaning S plus MEnv.nil :=
  fun R atZero step => induction_numClass S R atZero step

variable {S plus} (plusNumerals : ∀ i j, plus (numClass S.numerals i) (numClass S.numerals j) =
  numClass S.numerals (i + j))
include plusNumerals

theorem onePlusOne_meaning : onePlusOne.meaning S plus MEnv.nil :=
  plusNumerals 1 1

/-- An addition that adds numerals is commutative on the values of the numbers. -/
theorem plus_comm (q r : Q S.numerals .num) : plus q r = plus r q := by
  obtain ⟨i, rfl⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass q
  obtain ⟨j, rfl⟩ := Presentation.TypedEquality.Impredicative.Consistency.Q.eq_numClass r
  rw [plusNumerals, plusNumerals, Nat.add_comm]

theorem addComm_meaning : addComm.meaning S plus MEnv.nil :=
  fun q r => plus_comm plusNumerals q r

theorem addZeroSuc_meaning (laws : S.Laws) : ¬ addZeroSuc.meaning S plus MEnv.nil := fun all => by
  have same : numClass S.numerals 0 = numClass S.numerals 1 := by
    have atZero : plus (numClass S.numerals 0) (numClass S.numerals 0) =
        sucClass S.numerals (numClass S.numerals 0) := all (numClass S.numerals 0)
    rwa [plusNumerals] at atZero
  exact absurd (numClass_injective laws.numerals same) (by decide)

end Meanings

section Positive

variable (h : CofinalInaccessibles.{u}) (v : Nat → Nat)

/-- Model SN's truth reading of a closed code holds exactly when its meaning does. -/
theorem modelSN_holds_iff (φ : CodeTerm [] .prop) :
    (∃ P, Truth (vmodel v).toModel.reading World.closed φ.toC.erase P ∧ P) ↔
      φ.meaning (tmodelC v).toSetting (addClass _ (modelSN_computesAdd v)) MEnv.nil :=
  truth_holds_iff (rules := tmodelRules v) (roles := tmodelRoles) (tmodelC_laws v).truth
    (modelSN_computesAdd v) φ

/-- The tower holds of a closed code exactly when its meaning does. -/
theorem tower_holds_iff_modelSN (φ : CodeTerm [] .prop) :
    (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) φ.toC) Fin.elim0 ↔
      φ.meaning (tmodelC v).toSetting (addClass _ (modelSN_computesAdd v)) MEnv.nil :=
  tower_holds_iff h (tmodelC_laws v).truth (addClass_numClass _ (modelSN_computesAdd v)) φ

/-- **Positive: `zero = zero` holds in model SN and in the tower.** -/
theorem zeroEqZero_both :
    (∃ P, Truth (vmodel v).toModel.reading World.closed zeroEqZero.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) zeroEqZero.toC) Fin.elim0 :=
  ⟨(modelSN_holds_iff v _).mpr (zeroEqZero_meaning _ _),
    (tower_holds_iff_modelSN h v _).mpr (zeroEqZero_meaning _ _)⟩

/-- **Positive: `∀ n. zero = suc n` holds in neither.** -/
theorem zeroEqSuc_neither :
    ¬ (∃ P, Truth (vmodel v).toModel.reading World.closed zeroEqSuc.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∉ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) zeroEqSuc.toC) Fin.elim0 :=
  ⟨fun holds => zeroEqSuc_meaning _ _ (tmodelC_laws v).truth ((modelSN_holds_iff v _).mp holds),
    fun holds => zeroEqSuc_meaning _ _ (tmodelC_laws v).truth
      ((tower_holds_iff_modelSN h v _).mp holds)⟩

/-- **Positive: the impredicative code `∀ p : prop. p ⇒ p` holds in both.** -/
theorem propImpSelf_both :
    (∃ P, Truth (vmodel v).toModel.reading World.closed propImpSelf.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) propImpSelf.toC) Fin.elim0 :=
  ⟨(modelSN_holds_iff v _).mpr (propImpSelf_meaning _ _),
    (tower_holds_iff_modelSN h v _).mpr (propImpSelf_meaning _ _)⟩

/-- **Positive: the impredicative code `∀ p : prop. p` holds in neither.** -/
theorem propAll_neither :
    ¬ (∃ P, Truth (vmodel v).toModel.reading World.closed propAll.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∉ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) propAll.toC) Fin.elim0 :=
  ⟨fun holds => propAll_meaning _ _ ((modelSN_holds_iff v _).mp holds),
    fun holds => propAll_meaning _ _ ((tower_holds_iff_modelSN h v _).mp holds)⟩

/-- **Positive: induction on the numbers over every predicate holds in both.** -/
theorem numInduction_both :
    (∃ P, Truth (vmodel v).toModel.reading World.closed numInduction.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) numInduction.toC) Fin.elim0 :=
  ⟨(modelSN_holds_iff v _).mpr (numInduction_meaning _ _),
    (tower_holds_iff_modelSN h v _).mpr (numInduction_meaning _ _)⟩

/-- **Positive: `add (suc zero) (suc zero) = suc (suc zero)` holds in both**: model SN computes
the sum by the recursion of `add`, the tower by its traced graph. -/
theorem onePlusOne_both :
    (∃ P, Truth (vmodel v).toModel.reading World.closed onePlusOne.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) onePlusOne.toC) Fin.elim0 :=
  ⟨(modelSN_holds_iff v _).mpr (onePlusOne_meaning (addClass_numClass _ (modelSN_computesAdd v))),
    (tower_holds_iff_modelSN h v _).mpr
      (onePlusOne_meaning (addClass_numClass _ (modelSN_computesAdd v)))⟩

/-- **Positive: commutativity of addition holds in both.** -/
theorem addComm_both :
    (∃ P, Truth (vmodel v).toModel.reading World.closed addComm.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) addComm.toC) Fin.elim0 :=
  ⟨(modelSN_holds_iff v _).mpr (addComm_meaning (addClass_numClass _ (modelSN_computesAdd v))),
    (tower_holds_iff_modelSN h v _).mpr
      (addComm_meaning (addClass_numClass _ (modelSN_computesAdd v)))⟩

/-- **Positive: `∀ n. add n zero = suc n` holds in neither.** -/
theorem addZeroSuc_neither :
    ¬ (∃ P, Truth (vmodel v).toModel.reading World.closed addZeroSuc.toC.erase P ∧ P) ∧
      (∅ : ZFSet.{u}) ∉ ev (objHeads h) (objectSetConsts h)
        (CTm.app (.const holdsN) addZeroSuc.toC) Fin.elim0 :=
  ⟨fun holds => addZeroSuc_meaning (addClass_numClass _ (modelSN_computesAdd v))
      (tmodelC_laws v).truth ((modelSN_holds_iff v _).mp holds),
    fun holds => addZeroSuc_meaning (addClass_numClass _ (modelSN_computesAdd v))
      (tmodelC_laws v).truth ((tower_holds_iff_modelSN h v _).mp holds)⟩

end Positive

/-! ## The tower's quantifier over a traced graph -/

section Graphs

variable (h : CofinalInaccessibles.{u})

/-- The tower's quantifier at a simple type, applied to the traced graph of a family of truth
values, is the truth value of the quantification of the family's truth. -/
theorem all_graph (type : HOL.Ty SetProfile.SetBase) {F : ZFSet.{u} → ZFSet.{u}}
    (truthValues : ∀ x ∈ simpleSet.{u} type, F x ∈ Square.omega) :
    traceApp (objectSetConsts h (SetProfile.allName type)) (traceLam (graph (simpleSet type) F)) =
      truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ F x) := by
  rw [all_apply h type (traceLam_graph_mem truthValues)]
  congr 1
  apply propext
  exact forall₂_congr fun x hx => by rw [traceApp_graph_beta _ hx]

end Graphs

/-! ## Negative controls: the sets -/

section Sets

/-- `∅` and `𝒫 ∅` are distinct. -/
theorem empty_ne_powerset_empty : (∅ : ZFSet.{u}) ≠ ZFSet.powerset ∅ := fun same => by
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← same] at member
  exact ZFSet.notMem_empty _ member

theorem powerset_empty_mem_finiteSets : ZFSet.powerset (∅ : ZFSet.{u}) ∈ finiteSets :=
  powerset_mem_finiteSets empty_mem_finiteSets

/-- **No correspondence at the sets.** The consistency model's meanings of the rigid type
`set`, one point, are not in bijection with `V_ω`, the tower's value of `set`. -/
theorem no_setEquiv {Head : Type} (S : Setting Head) :
    IsEmpty (Carrier.Val S.numerals Prop (Carrier.rigid setN) ≃ Elements (finiteSets.{u})) := by
  refine ⟨fun e => empty_ne_powerset_empty ?_⟩
  have same : e.symm ⟨∅, empty_mem_finiteSets⟩ =
      e.symm ⟨ZFSet.powerset ∅, powerset_empty_mem_finiteSets⟩ := rfl
  exact congrArg Subtype.val (e.symm.injective same)

/-- **The square fails at the sets.** The consistency model makes any two sets equal; the
trace-product reading over `V_ω` makes the same statement false. -/
theorem square_fails_set {Head : Type} (S : Setting Head) :
    truthCode.{u} (S.truthReading.allMeaning (Carrier.rigid setN) fun x =>
        S.truthReading.allMeaning (Carrier.rigid setN) fun y =>
          S.truthReading.eqMeaning (Carrier.rigid setN) x y) ≠
      tracePiSet finiteSets (fun x => tracePiSet finiteSets (fun y => truthCode (x = y))) := by
  intro same
  have lhs : (∅ : ZFSet.{u}) ∈ truthCode (S.truthReading.allMeaning (Carrier.rigid setN) fun x =>
      S.truthReading.allMeaning (Carrier.rigid setN) fun y =>
        S.truthReading.eqMeaning (Carrier.rigid setN) x y) :=
    (Square.square_truth_iff _).mpr fun _ _ => rfl
  rw [same] at lhs
  have inner : ∀ x, tracePiSet finiteSets (fun y => truthCode (x = y)) =
      truthCode (∀ y ∈ finiteSets.{u}, x = y) := fun x => Controls.tracePiSet_truthCode _ _
  simp only [inner, Controls.tracePiSet_truthCode] at lhs
  exact empty_ne_powerset_empty ((Square.square_truth_iff _).mp lhs ∅ empty_mem_finiteSets _
    powerset_empty_mem_finiteSets)

/-- `∀ x y : set. x = y`, annotated. -/
def setEqCode : CTm Tower.Head 0 :=
  .app (.const (SetProfile.allName SetProfile.setTy))
    (.lam (liftTm (typeAt SetProfile.types 0 SetProfile.setTy))
      (.app (.const (SetProfile.allName SetProfile.setTy))
        (.lam (liftTm (typeAt SetProfile.types 1 SetProfile.setTy))
          (.app (.app (.const (SetProfile.eqName SetProfile.setTy)) (.var 1)) (.var 0)))))

variable {rules : Rules Tower.Head} {roles : Roles Tower.Head}

theorem allCarrier_set :
    (objSetting rules roles).truthReading.allCarrier (SetProfile.allName SetProfile.setTy) =
      some ⟨.gen, .rigid setN⟩ := by
  change (SetProfile.allInstance? (SetProfile.allName SetProfile.setTy)).map carrierOf = _
  rw [SetProfile.allInstance?_allName]
  rfl

theorem eqCarrier_set :
    (objSetting rules roles).truthReading.eqCarrier (SetProfile.eqName SetProfile.setTy) =
      some ⟨.gen, .rigid setN⟩ := by
  change (SetProfile.eqInstance? (SetProfile.eqName SetProfile.setTy)).map carrierOf = _
  rw [SetProfile.eqInstance?_eqName]
  rfl

/-- Model SN's truth reading of `∀ x y : set. x = y`: any two points of the one-point carrier
are equal. -/
theorem setEqCode_truth :
    Truth (objSetting rules roles).truthReading World.closed setEqCode.erase
      ((objSetting rules roles).truthReading.allMeaning (Carrier.rigid setN) fun x =>
        (objSetting rules roles).truthReading.allMeaning (Carrier.rigid setN) fun y =>
          (objSetting rules roles).truthReading.eqMeaning (Carrier.rigid setN) x y) := by
  refine .all allCarrier_set .refl
    (.genericArg fun _ => Read.expand (.single (WhStep.beta _ _)) ?_)
  rw [inst0_var_zero_rename_liftRen_wk]
  refine .prop (.all allCarrier_set .refl
    (.genericArg fun _ => Read.expand (.single (WhStep.beta _ _)) ?_))
  rw [inst0_var_zero_rename_liftRen_wk]
  exact .prop (.eq eqCarrier_set .refl .rigid .rigid)

/-- **Negative, model SN's side: `∀ x y : set. x = y` holds in model SN's truth reading.** -/
theorem setEqCode_modelSN (v : Nat → Nat) :
    ∃ P, Truth (vmodel v).toModel.reading World.closed setEqCode.erase P ∧ P :=
  ⟨_, setEqCode_truth (rules := tmodelRules v) (roles := tmodelRoles), fun _ _ => rfl⟩

/-- **Negative, the tower's side: the value of `holds (∀ x y : set. x = y)` is the false truth
value**, since `V_ω` has the two points `∅` and `𝒫 ∅`. -/
theorem setEqCode_tower (h : CofinalInaccessibles.{u}) :
    (∅ : ZFSet.{u}) ∉ ev (objHeads h) (objectSetConsts h)
      (CTm.app (.const holdsN) setEqCode) Fin.elim0 := by
  intro holds
  change (∅ : ZFSet.{u}) ∈ traceApp (objectSetConsts h holdsN)
    (traceApp (objectSetConsts h (SetProfile.allName SetProfile.setTy))
      (traceLam (graph (ev (objHeads h) (objectSetConsts h)
        (liftTm (typeAt SetProfile.types 0 SetProfile.setTy)) Fin.elim0) fun x =>
          traceApp (objectSetConsts h (SetProfile.allName SetProfile.setTy))
            (traceLam (graph (ev (objHeads h) (objectSetConsts h)
              (liftTm (typeAt SetProfile.types 1 SetProfile.setTy)) (extend Fin.elim0 x))
              fun y => traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.setTy))
                x) y))))) at holds
  simp only [ev_objTypeAt h] at holds
  have inner : ∀ x ∈ simpleSet.{u} SetProfile.setTy,
      traceApp (objectSetConsts h (SetProfile.allName SetProfile.setTy))
        (traceLam (graph (simpleSet SetProfile.setTy) fun y =>
          traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.setTy)) x) y)) =
        truthCode (∀ y ∈ simpleSet.{u} SetProfile.setTy, x = y) := by
    intro x hx
    rw [all_graph h SetProfile.setTy fun y hy => by
      rw [eq_apply h SetProfile.setTy hx hy]
      exact Square.truthCode_mem_omega _]
    congr 1
    apply propext
    exact forall₂_congr fun y hy => by
      rw [eq_apply h SetProfile.setTy hx hy, Square.square_truth_iff]
  have outer := all_graph h SetProfile.setTy (F := fun x =>
      traceApp (objectSetConsts h (SetProfile.allName SetProfile.setTy))
        (traceLam (graph (simpleSet SetProfile.setTy) fun y =>
          traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.setTy)) x) y)))
    fun x hx => by
      rw [inner x hx]
      exact Square.truthCode_mem_omega _
  rw [outer, holds_apply h (Square.truthCode_mem_omega _), Square.square_truth_iff] at holds
  have atEmpty := holds ∅ empty_mem_finiteSets
  rw [inner ∅ empty_mem_finiteSets, Square.square_truth_iff] at atEmpty
  exact empty_ne_powerset_empty (atEmpty _ powerset_empty_mem_finiteSets)

end Sets

/-! ## Negative controls: a function carrier into the numbers -/

section Parametric

/-- The simple type `prop → num`. -/
abbrev propNumTy : HOL.Ty SetProfile.SetBase := .arr .prop SetProfile.numTy

/-- `∀ f : prop → num. ∀ p q : prop. f p = f q`, annotated. -/
def parametricCode : CTm Tower.Head 0 :=
  .app (.const (SetProfile.allName propNumTy)) (.lam (liftTm (typeAt SetProfile.types 0 propNumTy))
    (.app (.const (SetProfile.allName .prop)) (.lam (liftTm (typeAt SetProfile.types 1 .prop))
      (.app (.const (SetProfile.allName .prop)) (.lam (liftTm (typeAt SetProfile.types 2 .prop))
        (.app (.app (.const (SetProfile.eqName SetProfile.numTy)) (.app (.var 2) (.var 1)))
          (.app (.var 2) (.var 0))))))))

/-- A term related to itself at `prop → num` computes one numeral at any two arguments: it
cannot inspect its argument. -/
theorem related_propNum {S : DataSetting Tower.Head} {n : Nat} {f : Tm Tower.Head n}
    (related : DataEq S (.arr .prop .num) f f) (a b : Tm Tower.Head n) :
    DataEq S .num (.app f a) (.app f b) := by
  have opened := DataEq.subst₂ (S := S) Carrier.num
    (related : DataEq S .num (.app (Presentation.rename wk f) (.var 0))
      (.app (Presentation.rename wk f) (.var 0))) (subst0 a) (subst0 b)
  change DataEq S .num (.app (inst0 a (Presentation.rename wk f)) a)
    (.app (inst0 b (Presentation.rename wk f)) b) at opened
  rwa [inst0_rename_wk, inst0_rename_wk] at opened

variable {rules : Rules Tower.Head} {roles : Roles Tower.Head}

theorem allCarrier_propNum :
    (objSetting rules roles).truthReading.allCarrier (SetProfile.allName propNumTy) =
      some ⟨.data, .arr .prop .num⟩ := by
  change (SetProfile.allInstance? (SetProfile.allName propNumTy)).map carrierOf = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- Model SN's truth reading of `∀ f : prop → num. ∀ p q : prop. f p = f q`: at every term
related to itself at `prop → num`, and at all meanings `p` and `q`, the two applications compute
one numeral. -/
theorem parametricCode_truth :
    Truth (objSetting rules roles).truthReading World.closed parametricCode.erase
      ((objSetting rules roles).truthReading.allMeaning (Carrier.arr .prop .num) fun _ =>
        (objSetting rules roles).truthReading.allMeaning Carrier.prop fun _ =>
          (objSetting rules roles).truthReading.allMeaning Carrier.prop fun _ => True) := by
  have read : Read (objSetting rules roles).truthReading World.closed
      (Presentation.subst Presentation.ids (.lam
        (.app (.const (SetProfile.allName .prop)) (.lam
          (.app (.const (SetProfile.allName .prop)) (.lam
            (.app (.app (.const (SetProfile.eqName SetProfile.numTy)) (.app (.var 2) (.var 1)))
              (.app (.var 2) (.var 0)))))))))
      (.arr (.arr .prop .num) .prop)
      (fun _ => (objSetting rules roles).truthReading.allMeaning Carrier.prop fun _ =>
        (objSetting rules roles).truthReading.allMeaning Carrier.prop fun _ => True) := by
    refine Read.lam_data fun {_ ξ _} _ {s} related => .prop ?_
    refine .all (allCarrier_toTy .prop) .refl (Read.lam_gen fun p => .prop ?_)
    refine .all (allCarrier_toTy .prop) .refl (Read.lam_gen fun q => .prop ?_)
    have shifted : DataEq (objSetting rules roles).numerals (.arr .prop .num)
        (Presentation.rename wk (Presentation.rename wk s))
        (Presentation.rename wk (Presentation.rename wk s)) :=
      (related.rename₂ wk).rename₂ wk
    have first := related_propNum shifted (.var 1) (.var 1)
    have second := related_propNum shifted (.var 0) (.var 0)
    have truth : Truth (objSetting rules roles).truthReading
        ((ξ.snoc ⟨Carrier.prop, p⟩).snoc ⟨Carrier.prop, q⟩)
        (.app (.app (.const (SetProfile.eqName SetProfile.numTy))
          (.app (Presentation.rename wk (Presentation.rename wk s)) (.var 1)))
          (.app (Presentation.rename wk (Presentation.rename wk s)) (.var 0)))
        (dataValue (P := Prop) (objSetting rules roles).numerals .num _ first =
          dataValue (P := Prop) (objSetting rules roles).numerals .num _ second) :=
      .eq (eqCarrier_toTy .num) .refl (.data first) (.data second)
    rw [eq_true (dataValue_sound first second (related_propNum shifted _ _))] at truth
    exact truth
  rw [Presentation.subst_ids] at read
  exact .all allCarrier_propNum .refl read

/-- **Negative, model SN's side: `∀ f : prop → num. ∀ p q : prop. f p = f q` holds in model SN's
truth reading.** -/
theorem parametricCode_modelSN (v : Nat → Nat) :
    ∃ P, Truth (vmodel v).toModel.reading World.closed parametricCode.erase P ∧ P :=
  ⟨_, parametricCode_truth (rules := tmodelRules v) (roles := tmodelRoles),
    fun _ _ _ => trivial⟩

/-- A truth value is a natural number: `Ω = {0, 1}`. -/
theorem truthValue_mem_omega {p : ZFSet.{u}} (hp : p ∈ Square.omega) : p ∈ ZFSet.omega := by
  have below : p ⊆ {∅} := ZFSet.mem_powerset.mp hp
  by_cases hEmpty : (∅ : ZFSet.{u}) ∈ p
  · have one : p = numeral 1 := by
      apply ZFSet.ext
      intro z
      constructor
      · intro hz
        rw [ZFSet.mem_singleton.mp (below hz)]
        exact ZFSet.mem_insert _ _
      · intro hz
        rcases ZFSet.mem_insert_iff.mp hz with rfl | hz
        · exact hEmpty
        · exact absurd hz (ZFSet.notMem_empty _)
    rw [one]
    exact numeral_mem_omega 1
  · have zero : p = numeral 0 := by
      apply ZFSet.ext
      intro z
      constructor
      · intro hz
        rw [ZFSet.mem_singleton.mp (below hz)] at hz
        exact absurd hz hEmpty
      · intro hz
        exact absurd hz (ZFSet.notMem_empty _)
    rw [zero]
    exact numeral_mem_omega 0

/-- **Negative, the tower's side: the value of `holds (∀ f : prop → num. ∀ p q : prop. f p = f q)`
is the false truth value**: the inclusion of `Ω` into `ω` separates the two truth values. -/
theorem parametricCode_tower (h : CofinalInaccessibles.{u}) :
    (∅ : ZFSet.{u}) ∉ ev (objHeads h) (objectSetConsts h)
      (CTm.app (.const holdsN) parametricCode) Fin.elim0 := by
  intro holds
  change (∅ : ZFSet.{u}) ∈ traceApp (objectSetConsts h holdsN)
    (traceApp (objectSetConsts h (SetProfile.allName propNumTy))
      (traceLam (graph (ev (objHeads h) (objectSetConsts h)
        (liftTm (typeAt SetProfile.types 0 propNumTy)) Fin.elim0) fun f =>
          traceApp (objectSetConsts h (SetProfile.allName .prop))
            (traceLam (graph (ev (objHeads h) (objectSetConsts h)
              (liftTm (typeAt SetProfile.types 1 .prop)) (extend Fin.elim0 f)) fun p =>
                traceApp (objectSetConsts h (SetProfile.allName .prop))
                  (traceLam (graph (ev (objHeads h) (objectSetConsts h)
                    (liftTm (typeAt SetProfile.types 2 .prop))
                      (extend (extend Fin.elim0 f) p)) fun q =>
                    traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.numTy))
                      (traceApp f p)) (traceApp f q)))))))) at holds
  simp only [ev_objTypeAt h] at holds
  -- the equation of two values of a function of `prop → num`
  have equation : ∀ f ∈ simpleSet.{u} propNumTy, ∀ p ∈ simpleSet.{u} .prop,
      ∀ q ∈ simpleSet.{u} .prop,
      traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.numTy))
        (traceApp f p)) (traceApp f q) = truthCode (traceApp f p = traceApp f q) :=
    fun f hf p hp q hq => eq_apply h SetProfile.numTy (traceApp_mem_fibre hf hp)
      (traceApp_mem_fibre hf hq)
  -- the quantifier over `q`
  have overQ : ∀ f ∈ simpleSet.{u} propNumTy, ∀ p ∈ simpleSet.{u} .prop,
      traceApp (objectSetConsts h (SetProfile.allName .prop))
        (traceLam (graph (simpleSet .prop) fun q =>
          traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.numTy))
            (traceApp f p)) (traceApp f q))) =
        truthCode (∀ q ∈ simpleSet.{u} .prop, traceApp f p = traceApp f q) := by
    intro f hf p hp
    rw [all_graph h .prop fun q hq => by
      rw [equation f hf p hp q hq]
      exact Square.truthCode_mem_omega _]
    congr 1
    apply propext
    exact forall₂_congr fun q hq => by rw [equation f hf p hp q hq, Square.square_truth_iff]
  -- the quantifier over `p`
  have overP : ∀ f ∈ simpleSet.{u} propNumTy,
      traceApp (objectSetConsts h (SetProfile.allName .prop))
        (traceLam (graph (simpleSet .prop) fun p =>
          traceApp (objectSetConsts h (SetProfile.allName .prop))
            (traceLam (graph (simpleSet .prop) fun q =>
              traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.numTy))
                (traceApp f p)) (traceApp f q))))) =
        truthCode (∀ p ∈ simpleSet.{u} .prop, ∀ q ∈ simpleSet.{u} .prop,
          traceApp f p = traceApp f q) := by
    intro f hf
    rw [all_graph h .prop fun p hp => by
      rw [overQ f hf p hp]
      exact Square.truthCode_mem_omega _]
    congr 1
    apply propext
    exact forall₂_congr fun p hp => by rw [overQ f hf p hp, Square.square_truth_iff]
  have overF := all_graph h propNumTy (F := fun f =>
      traceApp (objectSetConsts h (SetProfile.allName .prop))
        (traceLam (graph (simpleSet .prop) fun p =>
          traceApp (objectSetConsts h (SetProfile.allName .prop))
            (traceLam (graph (simpleSet .prop) fun q =>
              traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.numTy))
                (traceApp f p)) (traceApp f q))))))
    fun f hf => by
      rw [overP f hf]
      exact Square.truthCode_mem_omega _
  rw [overF, holds_apply h (Square.truthCode_mem_omega _), Square.square_truth_iff] at holds
  -- the inclusion of the truth values into the numbers
  have inclusion : truthIdentity.{u} ∈ simpleSet.{u} propNumTy :=
    traceLam_graph_mem fun _ hp => truthValue_mem_omega hp
  have atInclusion := holds _ inclusion
  rw [overP _ inclusion, Square.square_truth_iff] at atInclusion
  have separated := atInclusion ∅ empty_mem_truthValues {∅} true_mem_truthValues
  rw [truthIdentity, traceApp_graph_beta _ empty_mem_truthValues,
    traceApp_graph_beta _ true_mem_truthValues] at separated
  exact empty_ne_true separated

end Parametric

/-! ## Negative controls: a computing data term at an ill-typed instance -/

section Recursor

/-- The numeral `two`, annotated. -/
abbrev twoC {n : Nat} : CTm Tower.Head n := .app (.const sucN) (.app (.const sucN) (.const zeroN))

/-- The recursor at the motive `λn. prop`, the value at zero `two`, a number and not a code,
and the step `λn p. p`, applied to `zero`, annotated. -/
def recTermC : CTm Tower.Head 0 :=
  .app (.app (.app (.app (.const Package.numRecName)
    (.lam (liftTm (typeAt SetProfile.types 0 SetProfile.numTy)) (.const propN))) twoC)
    (.lam (liftTm (typeAt SetProfile.types 0 SetProfile.numTy))
      (.lam (liftTm (typeAt SetProfile.types 1 .prop)) (.var 0))))
    (.const zeroN)

/-- `eq@num (num-rec (λn. prop) two (λn p. p) zero) two`, annotated. -/
def recCode : CTm Tower.Head 0 :=
  .app (.app (.const (SetProfile.eqName SetProfile.numTy)) recTermC) twoC

/-- Model SN's reduction computes the recursor at zero to its value at zero, whatever the
motive. -/
theorem recTerm_numVal (v : Nat → Nat) : NumVal (tmodelC v).toSetting recTermC.erase 2 :=
  (numVal_numeral (S := (tmodelC v).toSetting) 2).expand
    (.single (objectTExt.numRec_zero_step v (.lam (.const propN))
      (Presentation.TypedEquality.Impredicative.Consistency.numeral (tmodelC v).toSetting 2)
      (.lam (.lam (.var 0)))))

/-- **Negative, model SN's side: the code holds in model SN's truth reading**: both sides of the
equation compute the numeral `two`. -/
theorem recCode_modelSN (v : Nat → Nat) :
    ∃ P, Truth (vmodel v).toModel.reading World.closed recCode.erase P ∧ P := by
  have computed : DataEq (tmodelC v).toSetting.numerals .num recTermC.erase recTermC.erase :=
    ⟨2, recTerm_numVal v, recTerm_numVal v⟩
  have two : DataEq (tmodelC v).toSetting.numerals .num (twoC : CTm Tower.Head 0).erase
      (twoC : CTm Tower.Head 0).erase :=
    DataEq.numeral (S := (tmodelC v).toSetting.numerals) 2
  exact ⟨_, .eq (eqCarrier_toTy (rules := tmodelRules v) (roles := tmodelRoles) .num) .refl
      (.data computed) (.data two),
    dataValue_sound computed two ⟨2, recTerm_numVal v, numVal_numeral 2⟩⟩

/-- `two` is no truth value. -/
theorem two_not_mem_truthValues : (numeral 2 : ZFSet.{u}) ∉ Square.omega := fun member => by
  have one : (numeral 1 : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) :=
    ZFSet.mem_powerset.mp member (ZFSet.mem_insert _ _)
  have empty : (∅ : ZFSet.{u}) ∈ (numeral 1 : ZFSet.{u}) := ZFSet.mem_insert _ _
  rw [ZFSet.mem_singleton.mp one] at empty
  exact ZFSet.notMem_empty _ empty

/-- **Negative, the tower's side: the value of `holds` of the code is the false truth value**:
the recursor's traced graph, at the motive `λn. prop`, has no value at `two`, which lies outside
`Ω`, so the left side's value is `∅`, not `two`. -/
theorem recCode_tower (h : CofinalInaccessibles.{u}) :
    (∅ : ZFSet.{u}) ∉ ev (objHeads h) (objectSetConsts h)
      (CTm.app (.const holdsN) recCode) Fin.elim0 := by
  have twoValue : ev (objHeads h) (objectSetConsts h) (twoC : CTm Tower.Head 0) Fin.elim0 =
      numeral 2 := by
    show traceApp (objectSetConsts h sucN) (traceApp (objectSetConsts h sucN)
      (objectSetConsts h zeroN)) = _
    rw [setConst_zero h, suc_apply h (numeral_mem_omega 0)]
    show traceApp (objectSetConsts h sucN) (numeral 1) = _
    rw [suc_apply h (numeral_mem_omega 1)]
    rfl
  have motiveValue : ev (objHeads h) (objectSetConsts h)
      (.lam (liftTm (typeAt SetProfile.types 0 SetProfile.numTy)) (.const propN) :
        CTm Tower.Head 0) Fin.elim0 =
      traceLam (graph ZFSet.omega fun _ => Square.omega) := by
    show traceLam (graph (ev (objHeads h) (objectSetConsts h)
      (liftTm (typeAt SetProfile.types 0 SetProfile.numTy)) Fin.elim0)
        fun _ => objectSetConsts h propN) = _
    rw [ev_objTypeAt h, setConst_prop h]
    rfl
  have typed : objectSetConsts h Package.numRecName ∈
      ev (objHeads h) (objectSetConsts h)
        (Presentation.TypedEquality.Impredicative.Domain.nrTypeC numNames) Fin.elim0 := by
    rw [numRec_value h]
    exact numRecValue_mem (numberReading h)
  change objectSetConsts h Package.numRecName ∈ tracePiSet
    (ev (objHeads h) (objectSetConsts h) (.pi (.const numN) (.head (.sort Tower.zero)) :
      CTm Tower.Head 0) Fin.elim0)
    (fun P => tracePiSet (traceApp P (objectSetConsts h zeroN)) _) at typed
  have motiveTyped : traceLam (graph ZFSet.omega fun _ => Square.omega.{u}) ∈
      ev (objHeads h) (objectSetConsts h) (.pi (.const numN) (.head (.sort Tower.zero)) :
        CTm Tower.Head 0) Fin.elim0 := by
    show _ ∈ tracePiSet (objectSetConsts h numN) fun _ => lowest h
    rw [setConst_num h]
    exact traceLam_graph_mem fun _ _ => truthValues_mem_level h 0
  have atMotive := traceApp_mem_fibre typed motiveTyped
  have outside : (numeral 2 : ZFSet.{u}) ∉
      traceApp (traceLam (graph ZFSet.omega fun _ => Square.omega.{u}))
        (objectSetConsts h zeroN) := by
    rw [setConst_zero h, traceApp_graph_beta _ (numeral_mem_omega 0)]
    exact two_not_mem_truthValues
  have recValue : ev (objHeads h) (objectSetConsts h) recTermC Fin.elim0 = ∅ := by
    change traceApp (traceApp (traceApp (traceApp (objectSetConsts h Package.numRecName)
      (ev (objHeads h) (objectSetConsts h)
        (.lam (liftTm (typeAt SetProfile.types 0 SetProfile.numTy)) (.const propN) :
          CTm Tower.Head 0) Fin.elim0))
      (ev (objHeads h) (objectSetConsts h) (twoC : CTm Tower.Head 0) Fin.elim0)) _)
        (objectSetConsts h zeroN) = ∅
    rw [motiveValue, twoValue, traceApp_eq_empty_of_not_mem atMotive outside, traceApp_empty,
      traceApp_empty]
  intro holds
  change (∅ : ZFSet.{u}) ∈ traceApp (objectSetConsts h holdsN)
    (traceApp (traceApp (objectSetConsts h (SetProfile.eqName SetProfile.numTy))
      (ev (objHeads h) (objectSetConsts h) recTermC Fin.elim0))
      (ev (objHeads h) (objectSetConsts h) (twoC : CTm Tower.Head 0) Fin.elim0)) at holds
  rw [recValue, twoValue, eq_apply h SetProfile.numTy
      (show (∅ : ZFSet.{u}) ∈ ZFSet.omega from numeral_mem_omega 0) (numeral_mem_omega 2),
    holds_apply h (Square.truthCode_mem_omega _), Square.square_truth_iff] at holds
  exact absurd (numeral_injective (show (numeral 0 : ZFSet.{u}) = numeral 2 from holds))
    (by decide)

end Recursor

end SetSquare
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
