import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRealizers

/-!
# Strongly normalizing codes need not decode to strongly normalizing types

A quantifier code is decoded by applying its family to a fresh variable. When
the family is a partial application of a defined constant, the variable can
complete the arguments, and the definition then unfolds. So a code in normal
form can decode to a type without a normal form.

* **Negative control.** `all@num (transportCert zero zero ω zero ω)`, with
  `ω = λx. x x`, is normal: `transportCert` takes six arguments and has five.
  Its decoding unfolds `transportCert` at the fresh variable and exposes
  `ω ω`, which reduces to itself. The code is therefore no realizer of codes.
* **Positive control.** `all@num (λx. eq@num x x)` is a realizer of codes: its
  decoding is strongly normalizing.

The realizers of codes are therefore the codes whose decoding is strongly
normalizing, not all strongly normalizing codes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Package (transportName transportTelescope)

namespace CodeModel

namespace DecodingControl

theorem spine : SpineHeaded objectRules := RootShape.spineHeaded objectShape

/-- Self-application `λx. x x`. -/
def selfApp {n : Nat} : Tower.Tm n := .lam (.app (.var 0) (.var 0))

/-- `transportCert zero zero ω zero ω`: five of its six arguments. -/
def partialTransport {n : Nat} : Tower.Tm n :=
  appSpine (.const transportName) [.const zeroN, .const zeroN, selfApp, .const zeroN, selfApp]

/-- The code `all@num (transportCert zero zero ω zero ω)`. -/
def loopingCode : Tower.Tm 0 := .app (.const allNumN) partialTransport

theorem zero_sn {n : Nat} : SN objectRules (.const zeroN : Tower.Tm n) :=
  SN.constSpine objectShape (args := [])
    (fun arity scrutinee role => by rw [objectRoles_zero] at role; cases role) (by simp)

theorem selfApp_sn {n : Nat} : SN objectRules (selfApp : Tower.Tm n) := by
  refine SN.lam spine (SN.intro fun v step => ?_)
  rcases Inert.app_reduct objectShape (Inert.var 0) step with ⟨f', s, -⟩ | ⟨a', s, -⟩
  · exact absurd s (var_normal spine 0 f')
  · exact absurd s (var_normal spine 0 a')

theorem partialTransport_sn {n : Nat} : SN objectRules (partialTransport : Tower.Tm n) := by
  refine SN.constSpine objectShape (fun arity scrutinee role => ?_) ?_
  · rw [objectRoles_of_roles roles_transport nofun] at role
    injection role with same
    rw [← same]
    exact Nat.lt_succ_self _
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    · exact zero_sn
    · exact zero_sn
    · exact selfApp_sn
    · exact zero_sn
    · exact selfApp_sn

/-- The looping code is strongly normalizing: it is in fact normal. -/
theorem loopingCode_sn : SN objectRules loopingCode :=
  SN.constSpine objectShape (args := [partialTransport])
    (fun arity scrutinee role => by
      rw [objectRoles_all (SetProfile.allInstance?_allName SetProfile.numTy)] at role
      cases role)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact partialTransport_sn)

/-- The carrier of `all@num`. -/
theorem carrier_allNum :
    programCodes.decoders.allCarrier allNumN = some (typeTerm SetProfile.numTy) := by
  change (SetProfile.allInstance? allNumN).map typeTerm = _
  rw [SetProfile.allInstance?_allName]
  rfl

/-- The telescope substitution of the completed application. -/
def completion : Sub Tower.Head 6 1 :=
  consSub (.var 0) (consSub selfApp (consSub (.const zeroN) (consSub selfApp
    (consSub (.const zeroN) (consSub (.const zeroN) Fin.elim0)))))

theorem transport_mem :
    (transportName, definitionComputation transportName transportTelescope transportRhs) ∈
      computations.filter (fun entry => (fun _ => true) entry.1) := by
  refine List.mem_filter.mpr ⟨?_, rfl⟩
  simp only [computations]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))

/-- The unfolded body of the decoded quantifier. -/
def pairBody : Tower.Tm 1 :=
  .pair (.app selfApp selfApp) (.app (.app (.const zeroN) selfApp) (.var 0))

/-- The decoding after the definition unfolds. -/
def loop : Tower.Tm 0 :=
  .pi (liftClosed (typeTerm SetProfile.numTy)) (.app (.const holdsN) pairBody)

theorem decode_step :
    StrongNormalization.Reduces objectRules (.app (.const holdsN) loopingCode)
      (.pi (liftClosed (typeTerm SetProfile.numTy))
        (.app (.const holdsN) (.app (Presentation.rename wk partialTransport) (.var 0)))) :=
  .root (.inr (DecoderStep.all carrier_allNum partialTransport))

theorem unfold_step :
    StrongNormalization.Reduces objectRules
      (.pi (liftClosed (typeTerm SetProfile.numTy))
        (.app (.const holdsN) (.app (Presentation.rename wk partialTransport) (.var 0)))) loop := by
  refine .congPiCod (.congAppArg (.root (.inl ?_)))
  exact RootComputation.step_unionAll transport_mem ⟨completion, rfl, rfl⟩

theorem loop_step : StrongNormalization.Reduces objectRules loop loop :=
  .congPiCod (.congAppArg (.congPairFst (.betaPi _ _)))

theorem not_sn_of_loop {R : Rules Tower.Head} {n : Nat} {t : Tower.Tm n}
    (step : StrongNormalization.Reduces R t t) : ¬ SN R t := by
  have key : ∀ x, SN R x → x ≠ t := by
    intro x sn
    induction sn with
    | intro x _ ih =>
        intro e
        subst e
        exact ih x step rfl
  exact fun sn => key t sn rfl

/-- The decoding of the looping code is not strongly normalizing. -/
theorem holds_loopingCode_not_sn : ¬ SN objectRules (.app (.const holdsN) loopingCode) := by
  intro sn
  exact not_sn_of_loop loop_step ((sn.reduct decode_step).reduct unfold_step)

/-- A strongly normalizing code whose decoding is not strongly normalizing. -/
theorem sn_code_not_sn_decoding :
    SN objectRules loopingCode ∧ ¬ SN objectRules (.app (.const holdsN) loopingCode) :=
  ⟨loopingCode_sn, holds_loopingCode_not_sn⟩

/-- The looping code is no realizer of codes. -/
theorem loopingCode_not_codeReal :
    ¬ (CodeReal objectShape objectReflects objectDecoderRoles).mem loopingCode :=
  holds_loopingCode_not_sn

/-! ## The positive control -/

/-- The family `λx. eq@num x x`. -/
def reflexivity {n : Nat} : Tower.Tm n :=
  .lam (.app (.app (.const eqNumN) (.var 0)) (.var 0))

/-- The code `all@num (λx. eq@num x x)`. -/
def reflexivityCode : Tower.Tm 0 := .app (.const allNumN) reflexivity

theorem carrier_eqNum :
    programCodes.decoders.eqCarrier eqNumN = some (typeTerm SetProfile.numTy) := by
  change (if true = true then (SetProfile.eqInstance? eqNumN).map typeTerm else none) = _
  rw [if_pos rfl, SetProfile.eqInstance?_eqName]
  rfl

theorem num_sn : SN objectRules (typeTerm SetProfile.numTy) :=
  SN.constSpine objectShape (args := [])
    (fun arity scrutinee role => by rw [objectRoles_num] at role; cases role) (by simp)

/-- The reflexivity code is a realizer of codes. -/
theorem reflexivityCode_codeReal :
    (CodeReal objectShape objectReflects objectDecoderRoles).mem reflexivityCode := by
  refine CodeReal.all_mem objectShape objectReflects objectDecoderRoles objectDecodes
    carrier_allNum num_sn ?_
  have equation : ∀ {n : Nat} (i : Fin n), (CodeReal objectShape objectReflects
      objectDecoderRoles).mem (.app (.app (.const eqNumN) (.var i)) (.var i) : Tower.Tm n) :=
    fun i => CodeReal.eq_mem objectShape objectReflects objectDecoderRoles objectDecodes
      carrier_eqNum num_sn (SN.var spine i) (SN.var spine i)
  have redex := KCand.beta objectShape (CodeReal objectShape objectReflects objectDecoderRoles)
    (body := (.app (.app (.const eqNumN) (.var 0)) (.var 0) : Tower.Tm 2))
    (a := (.var 0 : Tower.Tm 1))
    ((CodeReal objectShape objectReflects objectDecoderRoles).sn (equation 0)) (SN.var spine 0)
    (equation 0)
  exact redex

end DecodingControl

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
