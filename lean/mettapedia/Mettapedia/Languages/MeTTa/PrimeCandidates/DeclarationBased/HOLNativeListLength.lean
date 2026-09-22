import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.HOLNativeListConstantBodies
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveMixedListElimination

/-!
# The retained HOL length symbol as a native List fold

Length uses the already declared small count carrier with its zero and
successor. No induction or equation is assumed for those constants. The
actual List eliminator defines the fold and supplies its two equations.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace HOLNativeListLength

open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.SchemaElaboration NativeIndexedFamilies IntrinsicMaps RussellTarski
open HOLNativeListConstantBodies
open FormationSensitiveHOLInterface

abbrev ConsType := @FormationSensitiveMixedListElimination.consCaseType

theorem universes : UniverseRegularity rules :=
  (towerUniverseRegularity.includeSignature
    FormationSensitiveNativeHOLMapExecution.nativeInstance.signature).includeSignature
    FormationSensitiveHOLProofFamily.declarations

theorem consType_formed {n : Nat} {Γ : Tower.Ctx n}
    {element motive nilCase : Tower.Tm n}
    (contextFormed : ContextFormation rules Γ)
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (motiveTyped : Typing Γ motive (.pi (Intrinsic.listApp element) (sortTm Tower.zero)))
    (nilTyped : Typing Γ nilCase (.app motive (Intrinsic.nilApp element))) :
    ∃ u, rules.isUniverse u ∧ Typing Γ (ConsType element motive) (.head u) := by
  have constant := FormationSensitiveHOLProofListIntegration.execution_typed
    (FormationSensitiveNativeHOLMapExecution.eliminateConstant_typed Γ)
  have afterElement := FormationSensitive.Typing.appElim constant elementTyped
  have afterMotive := FormationSensitive.Typing.appElim afterElement motiveTyped
  have nilExpected : Typing Γ nilCase
      (instantiateTwoAt Tower.zero element motive Intrinsic.nilCaseType) := by
    rw [instantiateTwoAt_eq_subst, mapHead_nilCaseType,
      Intrinsic.subst_nilCaseType_motiveSchema]
    exact nilTyped
  have afterNil := FormationSensitive.Typing.appElim afterMotive nilExpected
  obtain ⟨_, _, typeFormed⟩ := afterNil.regularity universes contextFormed
  obtain ⟨u, _, _, domainFormed, domainUniverse, _, _, _⟩ := typeFormed.piFormation
  refine ⟨u, domainUniverse, ?_⟩
  change Typing Γ (instantiateThreeAt Tower.zero element motive nilCase Intrinsic.consCaseType)
    (.head u) at domainFormed
  rw [instantiateThreeAt_eq_subst, mapHead_consCaseType] at domainFormed
  exact domainFormed

theorem count_beta {n : Nat} (argument : Tower.Tm n) :
    Conv rules.headEq (.app (.lam countType) argument) countType rules.computation :=
  .rel _ _ (.betaPi _ _)

theorem consType_converts {n : Nat} (element : Tower.Tm n) :
    Conv rules.headEq (ConsType element (.lam countType)) (lengthStepType element)
      rules.computation := by
  apply Conv.congPi (.refl _)
  apply Conv.congPi (.refl _)
  exact Conv.congPi (count_beta (.var 0)) (count_beta _)

theorem fold_typed {n : Nat} {Γ : Tower.Ctx n} {element list : Tower.Tm n}
    (contextFormed : ContextFormation rules Γ)
    (elementTyped : Typing Γ element (sortTm Tower.zero))
    (listTyped : Typing Γ list (Intrinsic.listApp element)) :
    Typing Γ (Intrinsic.eliminateApp element (.lam countType) zeroTerm lengthStep list)
      countType := by
  have motiveTyped := constantFamily_typed (list_typed elementTyped) (count_typed Γ)
  have nilAtMotive : Typing Γ zeroTerm (.app (.lam countType) (Intrinsic.nilApp element)) :=
    .conv (zero_typed Γ)
      (FormationSensitiveMixedListElimination.result_formed motiveTyped (nil_typed elementTyped))
      (.sort Tower.zero) (count_beta _).symm
  obtain ⟨u, universeWitness, consFormed⟩ :=
    consType_formed contextFormed elementTyped motiveTyped nilAtMotive
  have consAtMotive : Typing Γ lengthStep (ConsType element (.lam countType)) :=
    .conv (lengthStep_typed elementTyped) consFormed universeWitness (consType_converts element).symm
  have eliminated := FormationSensitiveMixedListElimination.eliminateApp_typed
    elementTyped motiveTyped nilAtMotive consAtMotive listTyped
  exact .conv eliminated (count_typed Γ) (.sort Tower.zero) (count_beta list)

theorem length_typed {element : Tower.Tm 0}
    (formed : Typing .nil element (sortTm Tower.zero)) :
    Typing .nil (lengthBody element) (arrow (Intrinsic.listApp element) countType) := by
  have listFormed := list_typed formed
  have contextFormed : ContextFormation rules (.snoc .nil (Intrinsic.listApp element)) :=
    .snoc .nil listFormed (.sort Tower.zero)
  apply FormationSensitive.Typing.lamIntro
    (pi_zero listFormed (count_typed _)) (.sort Tower.zero)
  have weakened : Typing (.snoc .nil (Intrinsic.listApp element))
      (liftClosed element) (sortTm Tower.zero) := closed_typed formed _
  have argument := FormationSensitive.Typing.var (R := rules)
    (Γ := .snoc .nil (Intrinsic.listApp element)) (0 : Fin 1)
  have same : (wk : Ren 0 1) = Fin.elim0 := by
    funext index
    exact Fin.elim0 index
  have argumentTyped : Typing (.snoc .nil (Intrinsic.listApp element))
      (.var 0) (Intrinsic.listApp (liftClosed element)) := by
    simpa only [Ctx.lookup_snoc_zero, Intrinsic.rename_listApp, same, liftClosed] using argument
  exact fold_typed contextFormed weakened argumentTyped

#print axioms consType_formed
#print axioms consType_converts
#print axioms fold_typed
#print axioms length_typed

end HOLNativeListLength
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
