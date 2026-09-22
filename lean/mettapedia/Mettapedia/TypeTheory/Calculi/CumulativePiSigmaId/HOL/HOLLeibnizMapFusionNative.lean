import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizNativeProofTranslation
import Mettapedia.Logic.HOL.UniformListMapFusion

/-!
# The retained uniform map-fusion proof becomes a native proof

The original HOL proof tree is passed to the constructive equality compiler.
Its original five ordered theory assumptions are abstracted as proof inputs;
none is introduced as a native declaration. The result proves the uniformly
quantified statement, including the source proof's induction application.

This is a conditional theorem over the existing opaque list signature. It
does not claim native list computation or construct the induction principle.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizMapFusionNative

open Presentation Mettapedia.Logic HOL.UniformListInduction
open HOLLeibnizNativeProofTranslation

def closedClaim : Formula [] :=
  .imp lengthCons (.imp lengthNil (.imp mapCons (.imp mapNil
    (.imp inductionPrinciple HOL.UniformListMapFusion.mapFusion))))

/-- Only assumption abstraction is added; the proof body is the original
retained map-fusion proof, not an independently authored replacement. -/
def closedProof : HOL.ProofSyntax Symbol [] closedClaim :=
  .impI (.impI (.impI (.impI (.impI HOL.UniformListMapFusion.mapFusionProof))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem original_compiles :
    (compile (HOL.UniformListMapFusion.mapFusionProof (Γ := []))
      (n := 5) Fin.elim0 (fun i => .var i)).isSome = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem closed_compiles : (compile closedProof (n := 0) Fin.elim0 Fin.elim0).isSome = true := by
  decide

def nativeProof : Tower.Tm 0 :=
  (compile closedProof (n := 0) Fin.elim0 Fin.elim0).get closed_compiles

theorem compiler_emits_nativeProof :
    compile closedProof Fin.elim0 Fin.elim0 = some nativeProof :=
  (Option.some_get closed_compiles).symm

theorem native_judgment : ∃ proposition : Tower.Tm 0,
    represent closedClaim = some proposition ∧
      FormationSensitive.Judgment FormationSensitiveHOLProofFamily.rules .nil nativeProof
        (FormationSensitiveHOLProofFamily.proof proposition) :=
  NativeTyping.compile_closed closedProof compiler_emits_nativeProof

#print axioms original_compiles
#print axioms HOL.UniformListMapFusion.mapFusionProof
#print axioms closed_compiles
#print axioms compiler_emits_nativeProof
#print axioms native_judgment

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizMapFusionNative
