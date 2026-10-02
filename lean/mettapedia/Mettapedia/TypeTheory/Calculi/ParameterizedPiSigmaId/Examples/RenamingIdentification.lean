import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayRenaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay

/-! # Concrete instances and controls for StructuralTypingReplayRenaming -/

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace StructuralTypingReplay

namespace IdentifyingAssumptions

private def zero : LevelExpr Nat := .const 0

def source : Tower.Ctx 3 := .snoc (.snoc (.snoc .nil (sortTm zero)) (sortTm zero)) (.var 1)

def target : Tower.Ctx 2 := .snoc (.snoc .nil (sortTm zero)) (.var 0)

def identification : Ren 3 2 := Fin.cases 0 (fun _ => 1)

abbrev rules := DependentPack.rules

theorem source_formed : FormationSensitive.ContextFormation rules source := by
  apply FormationSensitive.ContextFormation.snoc
    (u := .sort zero)
  · exact .snoc (.snoc .nil (.headType (.sort zero)) (.sort (.succ zero)))
      (.headType (.sort zero)) (.sort (.succ zero))
  · exact .var 1
  · exact .sort zero

theorem target_formed : FormationSensitive.ContextFormation rules target := by
  apply FormationSensitive.ContextFormation.snoc
    (u := .sort zero)
  · exact .snoc .nil (.headType (.sort zero)) (.sort (.succ zero))
  · exact .var 0
  · exact .sort zero

theorem compatible : CtxRen source target identification := by
  unfold CtxRen
  decide +kernel

/-- A certificate whose type names the other assumption fails before their
identification but succeeds afterwards. Both contexts are positively formed. -/
theorem rejection_not_invariant :
    check rules noConversionCheck source (.var 0) (.var 1) .var = false ∧
      check rules noConversionCheck target (rename identification (.var 0))
        (rename identification (.var 1)) (Code.rename noConversionRename identification .var) = true := by
  decide +kernel

end IdentifyingAssumptions


#print axioms IdentifyingAssumptions.source_formed
#print axioms IdentifyingAssumptions.rejection_not_invariant

end StructuralTypingReplay
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
