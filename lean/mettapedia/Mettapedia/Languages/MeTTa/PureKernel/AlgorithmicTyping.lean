import Mettapedia.Languages.MeTTa.PureKernel.DefEq

namespace Mettapedia.Languages.MeTTa.PureKernel

open Syntax
open Context
open Renaming
open Substitution
open Reduction
open Confluence
open Typing

structure InferredTyping (Γ : Ctx n) (t : PureTm n) where
  type : PureTm n
  typing : HasType Γ t type

structure CheckedTyping (Γ : Ctx n) (t A : PureTm n) : Type where
  typing : HasType Γ t A

mutual

def inferPureType : (Γ : Ctx n) -> (t : PureTm n) -> Except String (InferredTyping Γ t)
  | Γ, .var i =>
      pure { type := lookup Γ i, typing := HasType.var (Γ := Γ) i }
  | _, .const c =>
      throw s!"unknown declaration constant in current kernel fragment: {reprStr c}"
  | Γ, .u0 =>
      pure { type := .u1, typing := HasType.u0_type Γ }
  | _, .u1 =>
      throw "Type1 has no type in the current Pure kernel"
  | Γ, .pi A B => do
      let hA <- checkPureType Γ A .u1
      let hB <- checkPureType (.snoc Γ A) B .u1
      pure { type := .u1, typing := HasType.pi_form hA.typing hB.typing }
  | Γ, .sigma A B => do
      let hA <- checkPureType Γ A .u1
      let hB <- checkPureType (.snoc Γ A) B .u1
      pure { type := .u1, typing := HasType.sigma_form hA.typing hB.typing }
  | Γ, .id A a b => do
      let hA <- checkPureType Γ A .u1
      let ha <- checkPureType Γ a A
      let hb <- checkPureType Γ b A
      pure { type := .u1, typing := HasType.id_form hA.typing ha.typing hb.typing }
  | _, .lam _ =>
      throw "cannot infer a lambda without an expected Pi type; use `(: term type)`"
  | Γ, .app (.lam body) a => do
      let arg <- inferPureType Γ a
      let bodyTy <- inferPureType (.snoc Γ arg.type) body
      pure
        { type := inst0 a bodyTy.type
          typing := HasType.app_elim (HasType.lam_intro bodyTy.typing) arg.typing }
  | Γ, .app f a => do
      let funInfo <- inferPureType Γ f
      match asPi? funInfo.type with
      | some piInfo =>
          let hfPi : HasType Γ f (.pi piInfo.dom piInfo.cod) :=
            HasType.conv funInfo.typing piInfo.conv
          let ha <- checkPureType Γ a piInfo.dom
          pure
            { type := inst0 a piInfo.cod
              typing := HasType.app_elim hfPi ha.typing }
      | none =>
          throw "application expects a function whose type normalizes to Pi"
  | Γ, .pair a b => do
      let leftTy <- inferPureType Γ a
      let rightTy <- inferPureType Γ b
      have hb' : HasType Γ b (inst0 a (rename wk rightTy.type)) := by
        simpa [inst0_rename_wk_cancel a rightTy.type] using rightTy.typing
      pure
        { type := .sigma leftTy.type (rename wk rightTy.type)
          typing := HasType.pair_intro leftTy.typing hb' }
  | Γ, .fst p => do
      let pairInfo <- inferPureType Γ p
      match asSigma? pairInfo.type with
      | some sigmaInfo =>
          let hpSigma : HasType Γ p (.sigma sigmaInfo.dom sigmaInfo.cod) :=
            HasType.conv pairInfo.typing sigmaInfo.conv
          pure { type := sigmaInfo.dom, typing := HasType.fst_elim hpSigma }
      | none =>
          throw "fst expects a term whose type normalizes to Sigma"
  | Γ, .snd p => do
      let pairInfo <- inferPureType Γ p
      match asSigma? pairInfo.type with
      | some sigmaInfo =>
          let hpSigma : HasType Γ p (.sigma sigmaInfo.dom sigmaInfo.cod) :=
            HasType.conv pairInfo.typing sigmaInfo.conv
          pure
            { type := inst0 (.fst p) sigmaInfo.cod
              typing := HasType.snd_elim hpSigma }
      | none =>
          throw "snd expects a term whose type normalizes to Sigma"
  | Γ, .refl a => do
      let info <- inferPureType Γ a
      pure
        { type := .id info.type a a
          typing := HasType.refl_intro info.typing }
termination_by _ t => 2 * sizeOf t
decreasing_by
  all_goals
    simp_wf <;> try omega

def checkPureType : (Γ : Ctx n) -> (t A : PureTm n) -> Except String (CheckedTyping Γ t A)
  | Γ, .lam body, expected =>
      match asPi? expected with
      | some piInfo => do
          let hBody <- checkPureType (.snoc Γ piInfo.dom) body piInfo.cod
          have hconv : Conv (.pi piInfo.dom piInfo.cod) expected :=
            Relation.EqvGen.symm _ _ piInfo.conv
          pure { typing := HasType.conv (HasType.lam_intro hBody.typing) hconv }
      | none =>
          throw "lambda requires an expected Pi type"
  | Γ, .pair a b, expected =>
      match asSigma? expected with
      | some sigmaInfo => do
          let ha <- checkPureType Γ a sigmaInfo.dom
          let hb <- checkPureType Γ b (inst0 a sigmaInfo.cod)
          have hconv : Conv (.sigma sigmaInfo.dom sigmaInfo.cod) expected :=
            Relation.EqvGen.symm _ _ sigmaInfo.conv
          pure { typing := HasType.conv (HasType.pair_intro ha.typing hb.typing) hconv }
      | none => do
          let inferred <- inferPureType Γ (.pair a b)
          match defEqByNormalization? inferred.type expected with
          | some hconv => pure { typing := HasType.conv inferred.typing hconv.conv }
          | none =>
              throw s!"type mismatch: inferred {reprStr (cdev inferred.type)} but expected {reprStr (cdev expected)}"
  | Γ, t, expected => do
      let inferred <- inferPureType Γ t
      match defEqByNormalization? inferred.type expected with
      | some hconv => pure { typing := HasType.conv inferred.typing hconv.conv }
      | none =>
          throw s!"type mismatch: inferred {reprStr (cdev inferred.type)} but expected {reprStr (cdev expected)}"
termination_by _ t _ => 2 * sizeOf t + 1
decreasing_by
  all_goals
    simp_wf <;> try omega

end

def checkIsPureType (Γ : Ctx n) (A : PureTm n) : Except String Unit := do
  match A with
  | .u1 => pure ()
  | _ =>
      let _ <- checkPureType Γ A .u1
      pure ()

def inferClosedPureType (t : PureTm 0) : Except String (InferredTyping .nil t) :=
  inferPureType .nil t

def checkClosedPureType (t A : PureTm 0) : Except String (CheckedTyping .nil t A) :=
  checkPureType .nil t A

/-- A small open-term counterexample showing that `checkPureType` is not
complete for expected types merely convertible to `Pi`: the expected type below
is convertible to a `Pi`, but `asPi?` only inspects `cdev`, so lambda checking
fails before conversion can help. -/
private def lambdaCheckCounterCtx : Ctx 1 :=
  .snoc .nil .u0

private def lambdaCheckCounterExpectedRight : PureTm 1 :=
  .pi (.u0 : PureTm 1) (.u0 : PureTm 2)

private def lambdaCheckCounterExpectedBody : PureTm 2 :=
  rename wk lambdaCheckCounterExpectedRight

private def lambdaCheckCounterExpected : PureTm 1 :=
  .app (.fst (.pair (.lam lambdaCheckCounterExpectedBody) (.var 0))) (.var 0)

private def lambdaCheckCounterTerm : PureTm 1 :=
  .lam (.var 0)

private theorem lambdaCheckCounterTerm_typed_right :
    HasType lambdaCheckCounterCtx lambdaCheckCounterTerm lambdaCheckCounterExpectedRight := by
  apply HasType.lam_intro
  simpa [lambdaCheckCounterCtx, lambdaCheckCounterTerm, lambdaCheckCounterExpectedRight,
    Context.lookup_snoc_zero, Renaming.rename] using
    (HasType.var (Γ := .snoc lambdaCheckCounterCtx (.u0 : PureTm 1)) (i := (0 : Fin 2)))

private theorem lambdaCheckCounterExpected_conv :
    Conv lambdaCheckCounterExpected lambdaCheckCounterExpectedRight := by
  refine Relation.EqvGen.trans _ _ _
    (red_implies_conv
      (.congAppFun
        (.betaSigmaFst (.lam lambdaCheckCounterExpectedBody) (.var 0))))
    ?_
  exact red_implies_conv (.betaPi lambdaCheckCounterExpectedBody (.var 0))

private theorem lambdaCheckCounterTerm_typed_expected :
    HasType lambdaCheckCounterCtx lambdaCheckCounterTerm lambdaCheckCounterExpected := by
  exact HasType.conv lambdaCheckCounterTerm_typed_right
    (Relation.EqvGen.symm _ _ lambdaCheckCounterExpected_conv)

private theorem lambdaCheckCounterExpected_asPi_none :
    asPi? lambdaCheckCounterExpected = none := by
  simp [asPi?, lambdaCheckCounterExpected, cdev]

theorem checkPureType_not_complete_for_convertible_pi :
    ∃ (Γ : Ctx 1) (t A : PureTm 1),
      HasType Γ t A ∧
      checkPureType Γ t A = Except.error "lambda requires an expected Pi type" := by
  refine ⟨lambdaCheckCounterCtx, lambdaCheckCounterTerm, lambdaCheckCounterExpected,
    lambdaCheckCounterTerm_typed_expected, ?_⟩
  unfold checkPureType
  simp [lambdaCheckCounterTerm, lambdaCheckCounterExpected_asPi_none]
  rfl

end Mettapedia.Languages.MeTTa.PureKernel
