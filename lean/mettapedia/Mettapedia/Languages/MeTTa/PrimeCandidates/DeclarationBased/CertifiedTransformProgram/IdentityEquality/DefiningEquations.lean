import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.HostedTransport

/-!
# Defining equations are realized by reflexivity

Under the identity reading, an assumed equation `∀ n. l = r` is realized by
`λ n. refl l` when its two sides are convertible.  A defining equation of `add`
is: `add n zero` computes to `n`, so `λ n. refl (add n zero)` proves
`∀ n. add n zero = n`.

Zero on the left is not: `∀ n. add zero n = n` holds, but only by induction.  At
an open index `add zero n` and `n` are different terms without computation steps,
so no reflexivity proof has the type `Id num (add zero n) n`
(`HostedTransport.refl_not_hosted_open`).  An assumption of that form stays an
assumption unless its source proof is linked.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.DefiningEquations

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open SetProfile (numTy holdsName zeroNative addNative)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Execution
open CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Realizations
open FormationSensitiveHOLIdentityEquality (decode decodes)
open Mettapedia.Logic

/-- `add-zero-right : ∀ n. add n zero = n`. -/
def addZeroRight : HOL.Formula SetProfile.SetConst [] :=
  .all (σ := numTy) (.eq (SetProfile.addT (.var .vz) SetProfile.zeroT) (.var .vz))

theorem addZeroRight_represented :
    ∃ code, FormationSensitiveHOLInterface.represent SetProfile.signature addZeroRight =
      some code :=
  ⟨_, rfl⟩

/-- `Π n : num. Id num (add n zero) n`. -/
def addZeroRightDecoded : Tower.Tm 0 :=
  .pi numT (.id numT (addNative (.var 0) zeroNative) (.var 0))

theorem addZeroRight_decoded :
    decode SetProfile.signature holdsName addZeroRight = some addZeroRightDecoded :=
  rfl

/-- `λ n. refl (add n zero)`. -/
def addZeroRightRealization : Tower.Tm 0 := .lam (.refl (addNative (.var 0) zeroNative))

theorem addZeroRightRealization_decoded :
    Typing identityRules .nil addZeroRightRealization addZeroRightDecoded := by
  have index : Typing R (.snoc .nil numT) (.var 0) numT := Typing.var 0
  have point : Typing R (.snoc .nil numT) (addNative (.var 0) zeroNative) numT :=
    addNative_typed index zeroNative_typed
  have formed : Typing R .nil addZeroRightDecoded U0 :=
    pi_at numT_typed (id_at numT_typed point index)
  -- `add n zero` computes to `n` by the first equation of `add`
  have reflexive : Typing R (.snoc .nil numT) (.refl (addNative (.var 0) zeroNative))
      (.id numT (addNative (.var 0) zeroNative) (.var 0)) :=
    Typing.conv (Typing.reflIntro point) (id_at numT_typed point index)
      (isUniverseAt Tower.zero)
      (Runs.conv (Runs.identity .refl .refl (add_zero_run (.var 0))))
  exact toIdentity (Typing.lamIntro formed (isUniverseAt Tower.zero) reflexive)

/-- Reflexivity realizes the defining equation, as a proof of its represented
proposition under the identity reading. -/
theorem addZeroRightRealization_typed {code : Tower.Tm 0}
    (represented : FormationSensitiveHOLInterface.represent SetProfile.signature addZeroRight =
      some code) :
    Typing identityRules .nil addZeroRightRealization (Holds code) :=
  Typing.conv addZeroRightRealization_decoded (toIdentity (holds_formed represented))
    (isUniverseAt Tower.zero)
    (.symm _ _ (toIdentity_runs (decodes SetProfile.signature holdsName proofToIdentity
      identity_decodes addZeroRight represented addZeroRight_decoded)))

#print axioms addZeroRightRealization_decoded
#print axioms addZeroRightRealization_typed

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.DefiningEquations
