import Mettapedia.GSLT.Scope.SimpleFragmentBeckChevalley
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectFormFacts

/-!
# Typed equality of the object package on the simple fragment is βη-conversion

The object package, the executable equations together with the proposition codes, has the
facts about the weak-head forms of its types (`CodeModel.objectRules_formFacts`). So the
completeness of its typed equality on erasures of simple terms no longer needs them as a
hypothesis (`betaEtaConv_of_equal_object'`). With soundness of βη-conversion, which holds for
every package with the formation rules of the simple fragment, the typed equality of the
object package on the erasures of simple terms of one type is exactly βη-conversion
(`objectEqual_iff_betaEtaConv`).

Control: `s z` and `z` in the context `s : atom → atom, z : atom` are not equal in the object
package (`successorOfZero_not_equal_object`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Scope.SimpleFragmentBeckChevalley

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.TowerDTT
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open ExecutableModel

/-- **Completeness on the simple fragment for the object package, without hypotheses.** -/
theorem betaEtaConv_of_equal_object' {Γ : List Ty} {A : Ty} {l r : Term Γ A}
    (equal : Equal CodeModel.objectRules (eraseContext Γ) (eraseTerm l) (eraseTerm r)
      (eraseTypeAt Γ.length A)) :
    BetaEtaConv l r :=
  betaEtaConv_of_equal_object CodeModel.objectRules_formFacts equal

/-- **The typed equality of the object package on erasures of simple terms of one type is
exactly βη-conversion.** -/
theorem objectEqual_iff_betaEtaConv {Γ : List Ty} {A : Ty} (l r : Term Γ A) :
    Equal CodeModel.objectRules (eraseContext Γ) (eraseTerm l) (eraseTerm r)
        (eraseTypeAt Γ.length A) ↔
      BetaEtaConv l r :=
  ⟨betaEtaConv_of_equal_object', equal_of_betaEtaConv simpleHeadRules⟩

/-- **Control: the object package does not equate `s z` with `z`.** -/
theorem successorOfZero_not_equal_object :
    ¬ Equal CodeModel.objectRules (eraseContext [.arr .atom .atom, .atom])
      (eraseTerm successorOfZero) (eraseTerm zeroVariable) (eraseTypeAt 2 .atom) :=
  fun equal => successorOfZero_not_betaEtaConv (betaEtaConv_of_equal_object' equal)

end Mettapedia.GSLT.Scope.SimpleFragmentBeckChevalley
