import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Realizations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion

/-!
# The retained source proof as identity evidence

The runtime's proof term for `zero-add` applies three assumption constants.
Linking replaces each constant by its realization.  The linked term is
exactly what the compiler produces from the source proof with the
realizations as its hypotheses, and it proves `∀ k. add zero k = k` in the
identity profile.

Read as a dependent type, that statement is `Π k : num. Id num (add zero k) k`.
At an open index `k : num` the linked proof is therefore evidence for `eqAt k`,
and it feeds the program's native identity-typed steps there.  This evidence is
the translated source proof, not reflexivity: reflexivity is not evidence for
`eqAt k` at an open index.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Translation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open SetProfile (numTy holdsName zeroNative sucNative addNative)
open CertifiedTransformProgram.Package CertifiedTransformProgram.IdentityEquality
open CertifiedTransformProgram.IdentityEquality.Realizations
open FormationSensitiveHOLIdentityEquality (decode decodes)
open Mettapedia.Logic

/-- The realizations of the three assumptions, in the checker's order. -/
def realizations : Fin SetProfile.zeroAddAssumptions.length → Tower.Tm 0 :=
  ![inductionRealization, reflRealization, substRealization]

/-- Linking: each assumption constant is replaced by its realization. -/
def linking : ConstantExpansion.Bodies Tower.Head := fun name =>
  if name = SetProfile.inductionName then inductionRealization
  else if name = SetProfile.reflName then reflRealization
  else if name = SetProfile.substName then substRealization
  else .const name

/-- The runtime's proof term for `zero-add`, linked against the realizations. -/
def linkedZeroAdd : Tower.Tm 0 := ConstantExpansion.expand linking SetProfile.zeroAddTerm

/-- Compiling the source proof with the realizations as hypotheses gives the
linked runtime term. -/
theorem linkedZeroAdd_compiles :
    HOLNativeGenericProofCompiler.Modulo.compileModulo SetProfile.signature SetProfile.zeroAddProof
      Fin.elim0 realizations = some linkedZeroAdd :=
  rfl

/-- The logical proof operations, checked in the identity profile. -/
noncomputable def identityOperations :
    HOLNativeGenericProofCompiler.Operations SetProfile.signature holdsName :=
  HOLNativeGenericProofCompiler.Operations.logicalOnlyAt SetProfile.signature holdsName
    SetProfile.holdsName_fresh identityRules proofToIdentity

theorem realizations_typed :
    HOLNativeGenericProofCompiler.GenericTyping.Hypotheses SetProfile.signature identityOperations
      (.nil : Tower.Ctx 0) Fin.elim0 realizations := by
  intro index
  refine ⟨SetProfile.assumptionCodes index, SetProfile.assumption_represented index, ?_⟩
  rw [SetProfile.subst_elim0]
  fin_cases index
  · exact inductionRealization_typed
  · exact reflRealization_typed
  · exact substRealization_typed

/-- The linked proof proves `∀ k. add zero k = k` in the identity profile. -/
theorem linkedZeroAdd_typed :
    Typing identityRules .nil linkedZeroAdd (Holds SetProfile.zeroAddCode) := by
  obtain ⟨code, represented, typed⟩ :=
    HOLNativeGenericProofCompiler.Modulo.compileModulo_typed SetProfile.signature holdsName
      identityOperations SetProfile.realization SetProfile.zeroAddProof (objects := Fin.elim0)
      (fun index => index.elim0) realizations_typed linkedZeroAdd_compiles
  rw [SetProfile.zeroAdd_represented] at represented
  cases represented
  rw [SetProfile.subst_elim0] at typed
  exact typed

/-- `Π k : num. Id num (add zero k) k`. -/
def zeroAddDecoded : Tower.Tm 0 := .pi numT (.id numT (addNative zeroNative (.var 0)) (.var 0))

theorem zeroAddStatement_decoded :
    decode SetProfile.signature holdsName SetProfile.zeroAddStatement = some zeroAddDecoded :=
  rfl

/-- The linked proof has the dependent reading of `zero-add` as its type. -/
theorem linkedZeroAdd_decoded : Typing identityRules .nil linkedZeroAdd zeroAddDecoded :=
  Typing.conv linkedZeroAdd_typed
    (toIdentity (pi_at numT_typed
      (id_at numT_typed (addNative_typed zeroNative_typed (Typing.var 0)) (Typing.var 0))))
    (isUniverseAt Tower.zero)
    (toIdentity_runs (decodes SetProfile.signature holdsName proofToIdentity identity_decodes
      SetProfile.zeroAddStatement SetProfile.zeroAdd_represented zeroAddStatement_decoded))

/-- At an open index `k : num`, the translated source proof is evidence for
`eqAt k`. -/
theorem linkedZeroAdd_open :
    Typing identityRules (.snoc .nil numT) (.app (liftClosed linkedZeroAdd) (.var 0))
      (eqAtApp (.var 0)) := by
  have closed := FormationSensitiveHOLInterface.closed_typed linkedZeroAdd_decoded (.snoc .nil numT)
  have applied := Typing.appElim closed (toIdentity (Typing.var (R := R) (Γ := .snoc .nil numT) 0))
  exact Typing.conv applied (toIdentity (eqAt_typed (Typing.var 0))) (isUniverseAt Tower.zero)
    (.symm _ _ (toIdentity_conversion (package_step listed_eqAt (at1 (.var 0)))))

/-- The translated evidence feeds the program's successor step at the open
index: `sucStep k (zero-add k) : Σ y : num. eqAt y`. -/
theorem linkedZeroAdd_feeds_sucStep :
    Typing identityRules (.snoc .nil numT)
      (app2 (.const sucStepName) (.var 0) (.app (liftClosed linkedZeroAdd) (.var 0)))
      (.sigma numT (eqAtApp (.var 0))) :=
  Typing.appElim
    (Typing.appElim (toIdentity (sucStep_typed _))
      (toIdentity (Typing.var (R := R) (Γ := .snoc .nil numT) 0)))
    linkedZeroAdd_open

#print axioms linkedZeroAdd_compiles
#print axioms realizations_typed
#print axioms linkedZeroAdd_typed
#print axioms linkedZeroAdd_decoded
#print axioms linkedZeroAdd_open
#print axioms linkedZeroAdd_feeds_sucStep

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality.Translation
