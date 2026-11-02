import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllCanonicalProduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveAlignmentReplay

/-!
# Final alignment of the original closed two-position Vector All control

The guard retains actual formation and replay of the original result type,
its universe and cumulative policies, and validation of the original complete
conversion recipe. The source is the actual final synthesized type.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.FinalAlignment
open Presentation RussellTarski
open NativeNaturalVectorFamilies
open ReplayComponents

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

private def applicationSearchRoot {n : Nat} (term : Tower.Tm n) : Option (decoder.Code n) :=
  match term with
  | .app _ _ => searchRoot term
  | _ => none

private theorem actual_search_root : @searchRoot = @applicationSearchRoot := by
  funext n term
  cases term <;> rfl

private def choicesAt (search : {n : Nat} → Tower.Tm n → Option (decoder.Code n)) :
    FormationSensitiveElaboration.Choices Tower.Head decoder.Code :=
  { NativeVectorAll.choices with
    normalize := fun fuel term => StructuralConversionSearch.termProjection decoder.decode search fuel term
    conversion := fun fuel left right => do
      let first := StructuralConversionSearch.termProjection decoder.decode search fuel left
      let second := StructuralConversionSearch.termProjection decoder.decode search fuel right
      let middle ← StructuralConversionSearch.compareShape first second
      let recipe := StructuralConversionCode.Code.trans
        (StructuralConversionSearch.produce decoder.decode search fuel left).recipe
        (.trans middle (.symm (StructuralConversionSearch.produce decoder.decode search fuel right).recipe))
      if middle.check NativeVectorAll.rules.headEq decoder.decode first second then some recipe else none }

private theorem filteredChoices_exact : NativeVectorAll.choices = choicesAt applicationSearchRoot := by
  have original : evaluationChoices = choicesAt searchRoot := rfl
  exact choices_for_proof_evaluation.trans (original.trans (congrArg choicesAt actual_search_root))

private theorem conversion_observation (fuel : Nat) {n : Nat} (source target : Tower.Tm n) :
    FormationSensitiveElaboration.conversionReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
      NativeVectorAll.choices fuel source target =
      (NativeVectorAll.choices.conversion fuel source target).isSome := by
  have checked (recipe : StructuralConversionCode.Code Tower.Head NativeVectorAll.decoder.Code n)
      (produced : NativeVectorAll.choices.conversion fuel source target = some recipe) :
      recipe.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode source target = true := by
    change StructuralConversionSearch.compare NativeVectorAll.decoder NativeVectorAll.searchRoot
      (headEq := NativeVectorAll.rules.headEq) fuel source target = some recipe at produced
    dsimp only [StructuralConversionSearch.compare] at produced
    cases matched : StructuralConversionSearch.compareShape (RootCode := NativeVectorAll.decoder.Code)
        (StructuralConversionSearch.produce NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel source).term
        (StructuralConversionSearch.produce NativeVectorAll.decoder.decode NativeVectorAll.searchRoot fuel target).term with
    | none => simp [matched] at produced
    | some middle =>
      simp only [matched,Option.bind_eq_bind,Option.bind_some] at produced
      split at produced
      · rename_i accepted
        cases Option.some.inj produced
        exact accepted
      · cases produced
  unfold FormationSensitiveElaboration.conversionReplayAccepted
  cases produced : NativeVectorAll.choices.conversion fuel source target with
  | none => rfl
  | some recipe => exact checked recipe produced

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem final_alignmentGuard :
    FormationSensitiveElaboration.alignReplayGuard NativeVectorAll.rules NativeVectorAll.decoder
      NativeVectorAll.choices 127 .nil (prefixType 6) CanonicalChecking.type = true := by
  unfold FormationSensitiveElaboration.alignReplayGuard
  dsimp only
  rw [conversion_observation]
  rw [filteredChoices_exact]
  decide +kernel

#print axioms final_alignmentGuard
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.CanonicalChecking.FinalAlignment
