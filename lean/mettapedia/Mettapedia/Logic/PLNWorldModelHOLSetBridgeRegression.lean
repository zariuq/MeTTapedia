import Mettapedia.Logic.PLNWorldModelHOLSetBridge
import Mettapedia.Logic.PLNHigherOrderHOLSoundness

/-!
# Direct Set/HOL/WM Regression Fixtures

Concrete theorem fixtures consuming the direct `Set -> HOL -> WM` bridge.

The emphasis here is on genuinely HOL-native set queries:

- positive higher-order universal validity,
- HO-PLN rule transport through the direct set/HOL/WM route,
- and a concrete negative counterexample on a small pointed set structure.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLSetBridgeRegression

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.Logic.HOL
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelHOLSetBridge
open scoped ENNReal

/-- The distinguished individual type for the direct set-based HOL grounding. -/
abbrev SetObjTy : Ty SetBaseTy :=
  .base Mettapedia.Logic.HOL.Embedding.FirstOrder.BaseTy.ind

/-- Endofunction type on the directly grounded set carrier. -/
abbrev SetEndTy : Ty SetBaseTy := SetObjTy ⇒ SetObjTy

/-- Unary predicate type on the directly grounded set carrier. -/
abbrev SetPredTy : Ty SetBaseTy := SetObjTy ⇒ .prop

/-- Endofunction type on unary predicates over the directly grounded set carrier. -/
abbrev SetPredEndTy : Ty SetBaseTy := SetPredTy ⇒ SetPredTy

/-- HOL-native positive query: every endofunction is self-equal. -/
def holNativeHigherOrderRefl : SetHOLQuery :=
  .all (σ := SetEndTy) (.eq (.var .vz) (.var .vz))

/-- Closed identity endofunction on the directly grounded set carrier. -/
def holNativeId : Term SetConst [] SetEndTy :=
  .lam (.var .vz)

/-- HOL-native eta-equality query for the identity endofunction. -/
def holNativeEtaIdEq : SetHOLQuery :=
  .eq (.lam (.app (weaken (Base := SetBaseTy) (σ := SetObjTy) holNativeId) (.var .vz)))
    holNativeId

/-- HOL-native negative query: every endofunction fixes every point. -/
def holNativeEveryEndoFixesEveryPoint : SetHOLQuery :=
  .all (σ := SetEndTy)
    (.all (σ := SetObjTy)
      (.eq (.app (.var (.vs .vz)) (.var .vz)) (.var .vz)))

/-- Closed identity endofunction on unary predicates over the directly grounded
set carrier. -/
def holNativePredId : Term SetConst [] SetPredEndTy :=
  .lam (.var .vz)

/-- HOL-native positive query:
every unary predicate implies itself at every point. -/
def holNativePredSelfImp : SetHOLQuery :=
  .all (σ := SetPredTy)
    (.all (σ := SetObjTy)
      (.imp (.app (.var (.vs .vz)) (.var .vz))
            (.app (.var (.vs .vz)) (.var .vz))))

/-- HOL-native negative query:
every unary predicate holds at every point. -/
def holNativeEveryPredHoldsEverywhere : SetHOLQuery :=
  .all (σ := SetPredTy)
    (.all (σ := SetObjTy)
      (.app (.var (.vs .vz)) (.var .vz)))

/-- HOL-native eta-equality query for the identity endofunction on predicates. -/
def holNativePredEtaIdEq : SetHOLQuery :=
  .eq
    (.lam (.app (weaken (Base := SetBaseTy) (σ := SetPredTy) holNativePredId) (.var .vz)))
    holNativePredId

theorem holNativeHigherOrderRefl_provable :
    Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
      (Const := SetConst) holNativeHigherOrderRefl :=
  .allI (.eqRefl (.var .vz))

theorem holNativeEtaIdEq_provable :
    Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
      (Const := SetConst) holNativeEtaIdEq :=
  Mettapedia.Logic.PLNHigherOrderHOLRules.holProvEq_eta
    (Base := SetBaseTy) (Const := SetConst) holNativeId

theorem holNativePredSelfImp_provable :
    Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
      (Const := SetConst) holNativePredSelfImp :=
  .allI (.allI (.impI (.hyp (by simp))))

theorem holNativePredEtaIdEq_provable :
    Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
      (Const := SetConst) holNativePredEtaIdEq :=
  Mettapedia.Logic.PLNHigherOrderHOLRules.holProvEq_eta
    (Base := SetBaseTy) (Const := SetConst) holNativePredId

/-- Positive fixture:
the direct set/HOL bridge sends the HOL-native higher-order reflexivity theorem
to singleton strength `1` on every pointed set structure. -/
theorem hol_native_higherOrderRefl_singleton_fixture
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) holNativeHigherOrderRefl = 1 := by
  have hsatisfies : setHolSatisfies S holNativeHigherOrderRefl := by
    simpa [setHolSatisfies] using
      (Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models
        (Base := SetBaseTy) (Const := SetConst)
        (φ := holNativeHigherOrderRefl) holNativeHigherOrderRefl_provable
        (M := Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S))
  exact
    queryStrength_singleton_of_satisfies
      (S := S) (φ := holNativeHigherOrderRefl) hsatisfies

/-- Positive fixture:
the HOL-native eta-equality query for the identity endofunction is valid on
every directly grounded pointed set structure. -/
theorem hol_native_eta_id_singleton_fixture
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) holNativeEtaIdEq = 1 := by
  have hsatisfies : setHolSatisfies S holNativeEtaIdEq := by
    simpa [setHolSatisfies] using
      (Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models
        (Base := SetBaseTy) (Const := SetConst)
        (φ := holNativeEtaIdEq) holNativeEtaIdEq_provable
        (M := Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S))
  exact
    queryStrength_singleton_of_satisfies
      (S := S) (φ := holNativeEtaIdEq) hsatisfies

/-- Positive fixture:
quantified predicate self-implication is valid on every directly grounded
pointed set structure. -/
theorem hol_native_pred_self_imp_singleton_fixture
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) holNativePredSelfImp = 1 := by
  have hsatisfies : setHolSatisfies S holNativePredSelfImp := by
    simpa [setHolSatisfies] using
      (Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models
        (Base := SetBaseTy) (Const := SetConst)
        (φ := holNativePredSelfImp) holNativePredSelfImp_provable
        (M := Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S))
  exact
    queryStrength_singleton_of_satisfies
      (S := S) (φ := holNativePredSelfImp) hsatisfies

/-- Positive fixture:
eta-equality for the predicate identity endofunction is valid on every directly
grounded pointed set structure. -/
theorem hol_native_pred_eta_id_singleton_fixture
    (S : SetPointed) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({S} : SetState) holNativePredEtaIdEq = 1 := by
  have hsatisfies : setHolSatisfies S holNativePredEtaIdEq := by
    simpa [setHolSatisfies] using
      (Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models
        (Base := SetBaseTy) (Const := SetConst)
        (φ := holNativePredEtaIdEq) holNativePredEtaIdEq_provable
        (M := Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S))
  exact
    queryStrength_singleton_of_satisfies
      (S := S) (φ := holNativePredEtaIdEq) hsatisfies

/-- Positive fixture:
the higher-order commutativity rule for conjunction transports directly through
`Set -> HOL -> WM`, even when one conjunct is genuinely higher-order. -/
theorem hol_native_and_comm_queryEq_fixture :
    WMQueryEq (State := SetState) (Query := SetHOLQuery)
      (.and holNativeHigherOrderRefl (.top : SetHOLQuery))
      (.and (.top : SetHOLQuery) holNativeHigherOrderRefl) := by
  apply queryEq_of_pointwiseIff
  intro S
  have hpoint :=
    Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_pointwise
      (Base := SetBaseTy) (Const := SetConst)
      (φ := .and holNativeHigherOrderRefl (.top : SetHOLQuery))
      (ψ := .and (.top : SetHOLQuery) holNativeHigherOrderRefl)
      (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_and_comm
        (Base := SetBaseTy) (Const := SetConst)
        holNativeHigherOrderRefl (.top : SetHOLQuery))
      (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
  change
    HenkinModel.models
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
        (.and holNativeHigherOrderRefl (.top : SetHOLQuery)) ↔
      HenkinModel.models
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
        (.and (.top : SetHOLQuery) holNativeHigherOrderRefl)
  exact hpoint

/-- Positive fixture:
the higher-order commutativity rule for disjunction transports directly through
`Set -> HOL -> WM`, even when one disjunct is genuinely higher-order. -/
theorem hol_native_or_comm_queryEq_fixture :
    WMQueryEq (State := SetState) (Query := SetHOLQuery)
      (.or holNativeHigherOrderRefl (.top : SetHOLQuery))
      (.or (.top : SetHOLQuery) holNativeHigherOrderRefl) := by
  apply queryEq_of_pointwiseIff
  intro S
  have hpoint :=
    Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_pointwise
      (Base := SetBaseTy) (Const := SetConst)
      (φ := .or holNativeHigherOrderRefl (.top : SetHOLQuery))
      (ψ := .or (.top : SetHOLQuery) holNativeHigherOrderRefl)
      (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_or_comm
        (Base := SetBaseTy) (Const := SetConst)
        holNativeHigherOrderRefl (.top : SetHOLQuery))
      (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
  change
    HenkinModel.models
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
        (.or holNativeHigherOrderRefl (.top : SetHOLQuery)) ↔
      HenkinModel.models
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
        (.or (.top : SetHOLQuery) holNativeHigherOrderRefl)
  exact hpoint

/-- Positive fixture:
the higher-order `not` congruence rule transports directly through the set/HOL
bridge when applied to a genuinely higher-order conjunction. -/
theorem hol_native_not_and_comm_queryEq_fixture :
    WMQueryEq (State := SetState) (Query := SetHOLQuery)
      (.not (.and holNativeHigherOrderRefl (.top : SetHOLQuery)))
      (.not (.and (.top : SetHOLQuery) holNativeHigherOrderRefl)) := by
  apply queryEq_of_pointwiseIff
  intro S
  have hpoint :=
    Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_pointwise
      (Base := SetBaseTy) (Const := SetConst)
      (φ := .not (.and holNativeHigherOrderRefl (.top : SetHOLQuery)))
      (ψ := .not (.and (.top : SetHOLQuery) holNativeHigherOrderRefl))
      (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_not
        (Base := SetBaseTy) (Const := SetConst)
        (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_and_comm
          (Base := SetBaseTy) (Const := SetConst)
          holNativeHigherOrderRefl (.top : SetHOLQuery)))
      (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
  change
    HenkinModel.models
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
        (.not (.and holNativeHigherOrderRefl (.top : SetHOLQuery))) ↔
      HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          (.not (.and (.top : SetHOLQuery) holNativeHigherOrderRefl))
  exact hpoint

/-- Positive fixture:
conjunction commutativity transports directly through the set/HOL bridge even
when the query itself quantifies over predicates. -/
theorem hol_native_pred_and_comm_queryEq_fixture :
    WMQueryEq (State := SetState) (Query := SetHOLQuery)
      (.and holNativePredSelfImp (.top : SetHOLQuery))
      (.and (.top : SetHOLQuery) holNativePredSelfImp) := by
  apply queryEq_of_pointwiseIff
  intro S
  have hpoint :=
    Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvIff_implies_pointwise
      (Base := SetBaseTy) (Const := SetConst)
      (φ := .and holNativePredSelfImp (.top : SetHOLQuery))
      (ψ := .and (.top : SetHOLQuery) holNativePredSelfImp)
      (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvIff_and_comm
        (Base := SetBaseTy) (Const := SetConst)
        holNativePredSelfImp (.top : SetHOLQuery))
      (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
  change
    HenkinModel.models
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
        (.and holNativePredSelfImp (.top : SetHOLQuery)) ↔
      HenkinModel.models
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
        (.and (.top : SetHOLQuery) holNativePredSelfImp)
  exact hpoint

/-- Positive fixture:
the higher-order left-conjunct rule induces multiset WM consequence directly on
set-pointed states. -/
theorem hol_native_and_left_multiset_fixture
    (W : SetState) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (.and holNativeHigherOrderRefl (.top : SetHOLQuery)) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        holNativeHigherOrderRefl := by
  have himp :
      ∀ S : SetPointed,
        setHolSatisfies S (.and holNativeHigherOrderRefl (.top : SetHOLQuery)) →
          setHolSatisfies S holNativeHigherOrderRefl := by
    intro S
    have hpoint :=
      Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_pointwise
        (Base := SetBaseTy) (Const := SetConst)
        (φ := .and holNativeHigherOrderRefl (.top : SetHOLQuery))
        (ψ := holNativeHigherOrderRefl)
        (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_and_left
          (Base := SetBaseTy) (Const := SetConst)
          (φ := holNativeHigherOrderRefl) (ψ := (.top : SetHOLQuery)))
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
    change
      HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          (.and holNativeHigherOrderRefl (.top : SetHOLQuery)) →
        HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          holNativeHigherOrderRefl
    exact hpoint
  exact
    queryStrength_le_of_pointwise
      (W := W)
      (φ := .and holNativeHigherOrderRefl (.top : SetHOLQuery))
      (ψ := holNativeHigherOrderRefl)
      himp

/-- Positive fixture:
the higher-order left-conjunct rule also induces multiset WM consequence for a
predicate-quantified higher-order query. -/
theorem hol_native_pred_and_left_multiset_fixture
    (W : SetState) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (.and holNativePredSelfImp (.top : SetHOLQuery)) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        holNativePredSelfImp := by
  have himp :
      ∀ S : SetPointed,
        setHolSatisfies S (.and holNativePredSelfImp (.top : SetHOLQuery)) →
          setHolSatisfies S holNativePredSelfImp := by
    intro S
    have hpoint :=
      Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_pointwise
        (Base := SetBaseTy) (Const := SetConst)
        (φ := .and holNativePredSelfImp (.top : SetHOLQuery))
        (ψ := holNativePredSelfImp)
        (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_and_left
          (Base := SetBaseTy) (Const := SetConst)
          (φ := holNativePredSelfImp) (ψ := (.top : SetHOLQuery)))
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
    change
      HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          (.and holNativePredSelfImp (.top : SetHOLQuery)) →
        HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          holNativePredSelfImp
    exact hpoint
  exact
    queryStrength_le_of_pointwise
      (W := W)
      (φ := .and holNativePredSelfImp (.top : SetHOLQuery))
      (ψ := holNativePredSelfImp)
      himp

/-- Positive fixture:
the higher-order left disjunction-introduction rule induces multiset WM
consequence directly on set-pointed states. -/
theorem hol_native_or_intro_left_multiset_fixture
    (W : SetState) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        holNativeHigherOrderRefl ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (.or holNativeHigherOrderRefl (.top : SetHOLQuery)) := by
  have himp :
      ∀ S : SetPointed,
        setHolSatisfies S holNativeHigherOrderRefl →
          setHolSatisfies S (.or holNativeHigherOrderRefl (.top : SetHOLQuery)) := by
    intro S
    have hpoint :=
      Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_pointwise
        (Base := SetBaseTy) (Const := SetConst)
        (φ := holNativeHigherOrderRefl)
        (ψ := .or holNativeHigherOrderRefl (.top : SetHOLQuery))
        (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_or_intro_left
          (Base := SetBaseTy) (Const := SetConst)
          holNativeHigherOrderRefl (.top : SetHOLQuery))
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
    change
      HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          holNativeHigherOrderRefl →
        HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          (.or holNativeHigherOrderRefl (.top : SetHOLQuery))
    exact hpoint
  exact
    queryStrength_le_of_pointwise
      (W := W)
      (φ := holNativeHigherOrderRefl)
      (ψ := .or holNativeHigherOrderRefl (.top : SetHOLQuery))
      himp

/-- Positive fixture:
the direct set/HOL/WM route also transports disjunction introduction for a
genuinely predicate-quantified higher-order query. -/
theorem hol_native_pred_or_intro_left_multiset_fixture
    (W : SetState) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        holNativePredSelfImp ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery) W
        (.or holNativePredSelfImp (.top : SetHOLQuery)) := by
  have himp :
      ∀ S : SetPointed,
        setHolSatisfies S holNativePredSelfImp →
          setHolSatisfies S (.or holNativePredSelfImp (.top : SetHOLQuery)) := by
    intro S
    have hpoint :=
      Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvImp_implies_pointwise
        (Base := SetBaseTy) (Const := SetConst)
        (φ := holNativePredSelfImp)
        (ψ := .or holNativePredSelfImp (.top : SetHOLQuery))
        (Mettapedia.Logic.PLNHigherOrderHOLRules.holProvImp_or_intro_left
          (Base := SetBaseTy) (Const := SetConst)
          holNativePredSelfImp (.top : SetHOLQuery))
        (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
    change
      HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          holNativePredSelfImp →
        HenkinModel.models
          (Mettapedia.Logic.HOL.Semantics.SetBased.ofPointed S)
          (.or holNativePredSelfImp (.top : SetHOLQuery))
    exact hpoint
  exact
    queryStrength_le_of_pointwise
      (W := W)
      (φ := holNativePredSelfImp)
      (ψ := .or holNativePredSelfImp (.top : SetHOLQuery))
      himp

local instance : LO.SetStructure Bool := ⟨fun _ _ => False⟩

/-- A tiny concrete pointed set structure used as a direct HOL countermodel. -/
def boolFlatPointed : SetPointed :=
  LO.FirstOrder.Struc.mk Bool (by infer_instance) (standardStructure Bool)

/-- Negative fixture:
on a two-point carrier, not every endofunction fixes every point. This is a
genuinely HOL-native counterexample, not an embedded FOL sentence. -/
theorem bool_flat_not_every_endo_fixes_every_point :
    ¬ setHolSatisfies boolFlatPointed holNativeEveryEndoFixesEveryPoint := by
  change ¬ ∀ f : ULift Bool → ULift Bool, True → ∀ x : ULift Bool, True → f x = x
  intro h
  have hbad := h (fun _ => ULift.up false) trivial (ULift.up true) trivial
  exact Bool.false_ne_true (congrArg ULift.down hbad)

/-- Negative fixture:
the concrete Bool countermodel yields singleton strength `0` for the failing
HOL-native higher-order query. -/
theorem bool_flat_every_endo_fixes_every_point_singleton_zero :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({boolFlatPointed} : SetState) holNativeEveryEndoFixesEveryPoint = 0 := by
  exact
    queryStrength_singleton_of_not_satisfies
      (S := boolFlatPointed)
      (φ := holNativeEveryEndoFixesEveryPoint)
      bool_flat_not_every_endo_fixes_every_point

/-- Negative fixture:
on a two-point carrier, not every unary predicate holds everywhere. -/
theorem bool_flat_not_every_pred_holds_everywhere :
    ¬ setHolSatisfies boolFlatPointed holNativeEveryPredHoldsEverywhere := by
  change
    ¬ ∀ P : ULift Bool → ULift Prop, True →
      ∀ x : ULift Bool, True → (P x).down
  intro h
  have hbad := h (fun _ => ULift.up False) trivial (ULift.up false) trivial
  exact hbad

/-- Negative fixture:
the concrete Bool countermodel yields singleton strength `0` for the failing
predicate-quantified HOL-native query. -/
theorem bool_flat_every_pred_holds_everywhere_singleton_zero :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetHOLQuery)
        ({boolFlatPointed} : SetState) holNativeEveryPredHoldsEverywhere = 0 := by
  exact
    queryStrength_singleton_of_not_satisfies
      (S := boolFlatPointed)
      (φ := holNativeEveryPredHoldsEverywhere)
      bool_flat_not_every_pred_holds_everywhere

end Mettapedia.Logic.PLNWorldModelHOLSetBridgeRegression
