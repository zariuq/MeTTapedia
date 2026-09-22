import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.NativeCheckedJudgmentPresheaf
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayContextConversion

/-!
# Checked binder conversion in the native context category

Independently checked formation extends an existing checked context.
Conversion between two such binder types gives an actual certificate-retaining
identity substitution between the extensions. Its action is the executable
body-certificate transformer, and observation commutes with that action.
Conversion there and back retains casts even when the erased substitution
is the identity. No strict isomorphism of retained evidence is asserted.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedSubstitution

open Presentation NativeIndexedFamilies NativeJudgmentReplay
open _root_.CategoryTheory

def Context.extend (context : Context) (type : Tower.Tm context.arity) (level : Tower.Head)
    (formation : Code context.arity) (isUniverse : IntrinsicRelator.rules.isUniverse level)
    (formed : check context.raw type (.head level) context.code formation = true) : Context where
  arity := context.arity + 1
  raw := .snoc context.raw type
  code := .snoc context.code level formation
  accepted := by
    simp only [check, StructuralTypingReplay.checkJudgment, Bool.and_eq_true] at formed
    simp only [StructuralTypingReplay.checkContext, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨context.accepted, isUniverse⟩, formed.2⟩

def changeNewest (context : Context) (old new : Tower.Tm context.arity)
    (u v : Tower.Head) (oldFormation newFormation : Code context.arity)
    (oldUniverse : IntrinsicRelator.rules.isUniverse u) (newUniverse : IntrinsicRelator.rules.isUniverse v)
    (oldFormed : check context.raw old (.head u) context.code oldFormation = true)
    (newFormed : check context.raw new (.head v) context.code newFormation = true)
    (forward : NativeRelatorConversionChecking.Code context.arity)
    (converted : NativeRelatorConversionChecking.check forward old new = true) :
    context.extend new v newFormation newUniverse newFormed ⟶
      context.extend old u oldFormation oldUniverse oldFormed where
  substitution := ids
  codes := StructuralTypingReplay.newestImageCodes NativeRelatorConversionChecking.rename
    new u oldFormation (.symm forward)
  accepted := by
    apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
    intro index
    have inputs := oldFormed
    simp only [check, StructuralTypingReplay.checkJudgment, Bool.and_eq_true] at inputs
    exact StructuralTypingReplay.newestImageCodes_checked NativeRelatorConversionChecking.rename
      IntrinsicRelator.rules NativeRelatorConversionChecking.check NativeRelatorConversionChecking.check_rename
      inputs.2 oldUniverse
      (StructuralConversionCode.Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode converted) index

/-- The categorical action is the exact computed body-certificate action,
not just an equality after discarding proofs. -/
theorem reindex_changeNewest (context : Context) (old new : Tower.Tm context.arity)
    (u v : Tower.Head) (oldFormation newFormation : Code context.arity)
    (oldUniverse : IntrinsicRelator.rules.isUniverse u) (newUniverse : IntrinsicRelator.rules.isUniverse v)
    (oldFormed : check context.raw old (.head u) context.code oldFormation = true)
    (newFormed : check context.raw new (.head v) context.code newFormation = true)
    (forward : NativeRelatorConversionChecking.Code context.arity)
    (converted : NativeRelatorConversionChecking.check forward old new = true)
    (receipt : JudgmentReceipt (context.extend old u oldFormation oldUniverse oldFormed)) :
    let arrow := changeNewest context old new u v oldFormation newFormation oldUniverse newUniverse
      oldFormed newFormed forward converted
    (receipt.reindex arrow).subject = receipt.subject ∧
      (receipt.reindex arrow).type = receipt.type ∧
      (receipt.reindex arrow).code = convertNewest new u oldFormation forward receipt.subject receipt.type receipt.code ∧
      (receipt.reindex arrow).observe = receipt.observe.reindex (forget.map arrow) := by
  exact ⟨subst_ids _, subst_ids _, rfl, receipt.observe_reindex _⟩

namespace ConversionControls

open NativeJudgmentReplay.ContextConversionControls
open NativeRelatorConversionChecking.Examples (identityExpansionCode)

def source : Context :=
  Controls.groundContext.extend oldType (.sort Tower.zero) oldFormation (.sort _) (by decide +kernel)
def target : Context :=
  Controls.groundContext.extend newType (.sort Tower.zero) newFormation (.sort _) (by decide +kernel)

def forward : target ⟶ source :=
  changeNewest Controls.groundContext oldType newType (.sort Tower.zero) (.sort Tower.zero)
    oldFormation newFormation (.sort _) (.sort _) (by decide +kernel) (by decide +kernel)
    (identityExpansionCode (.var (0 : Fin 1))) (by decide +kernel)

def backward : source ⟶ target :=
  changeNewest Controls.groundContext newType oldType (.sort Tower.zero) (.sort Tower.zero)
    newFormation oldFormation (.sort _) (.sort _) (by decide +kernel) (by decide +kernel)
    (.symm (identityExpansionCode (.var (0 : Fin 1)))) (by decide +kernel)

theorem round_trip_erases_to_identity :
    forget.map (backward ≫ forward) = 𝟙 source.toFormed := by
  apply FormationSensitiveContextual.Hom.ext
  funext index
  rfl

theorem round_trip_retains_casts : backward ≫ forward ≠ 𝟙 source := by
  intro equal
  have codes := congrArg (fun arrow : source ⟶ source => arrow.codes (0 : Fin 2)) equal
  cases codes

def receipt : JudgmentReceipt source := ⟨.var (0 : Fin 2), oldLookup, .var, by decide +kernel⟩

theorem converted_receipt_uses_computed_certificate :
    (receipt.reindex forward).code = convertedVariable := rfl

theorem round_trip_preserves_observation :
    (receipt.reindex (backward ≫ forward)).observe = receipt.observe := by
  rw [JudgmentReceipt.observe_reindex, round_trip_erases_to_identity]
  exact FormationSensitiveContextual.QTerm.reindex_id _

end ConversionControls

#print axioms reindex_changeNewest
#print axioms ConversionControls.round_trip_erases_to_identity
#print axioms ConversionControls.round_trip_retains_casts
#print axioms ConversionControls.converted_receipt_uses_computed_certificate
#print axioms ConversionControls.round_trip_preserves_observation

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeCheckedSubstitution
