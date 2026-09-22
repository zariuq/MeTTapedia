import Mettapedia.GSLT.GraphTheory.InterpretationTransport
import Mettapedia.GSLT.Core.WebSemanticsControls

/-! Nonidentity representation controls on the infinite natural-number web. -/

namespace Mettapedia.GSLT.GraphTheory.InterpretationTransportControls

open Mettapedia.GSLT.Core

def swapTokens : Nat ≃ Nat := Equiv.swap 0 1

def recodedModel : GraphModel :=
  recode GraphModel.naturalModel GraphModel.naturalModel.web swapTokens

def recoding : CodingEquiv GraphModel.naturalModel recodedModel :=
  recodeEquiv GraphModel.naturalModel GraphModel.naturalModel.web swapTokens

theorem changes_token : recoding.carrier (0 : Nat) = (1 : Nat) := by
  change swapTokens 0 = 1
  decide

theorem changes_set : recoding.sets ({0} : Set Nat) = ({1} : Set Nat) := by
  change swapTokens '' ({0} : Set Nat) = {1}
  rw [Set.image_singleton]
  rfl

/-- Swapping carrier tokens while retaining the old coding is not a lawful
graph-model equivalence. -/
theorem untransported_coding_not_lawful :
    ¬ ∀ (a : Finset Nat) (x : Nat),
      swapTokens (GraphModel.naturalModel.code a x) =
        GraphModel.naturalModel.code (swapTokens.finsetCongr a) (swapTokens x) := by
  intro h
  have bad := h {0} 0
  have ne : swapTokens (GraphModel.naturalModel.code ({0} : Finset Nat) (0 : Nat)) ≠
      GraphModel.naturalModel.code (swapTokens.finsetCongr ({0} : Finset Nat)) (swapTokens 0) := by
    change swapTokens (Encodable.encode (({0} : Finset Nat), (0 : Nat))) ≠
      Encodable.encode (swapTokens.finsetCongr ({0} : Finset Nat), swapTokens 0)
    have singleton_code (n : Nat) : Encodable.encode ({n} : Finset Nat) =
        Encodable.encode [n] := by
      change Encodable.encode (({n} : Multiset Nat).sort (· ≤ ·)) = _
      rw [Multiset.sort_singleton]
    simp only [Equiv.finsetCongr_apply, Finset.map_singleton, Encodable.encode_prod_val,
      singleton_code, Encodable.encode_nat]
    decide +kernel
  exact ne bad

def inputEnv : Env GraphModel.naturalModel := fun n => {n}

/-- This term exercises both abstraction and application, retaining a free
input through beta evaluation. -/
def identityConsumer : LambdaTerm := .app (.lam (.var 0)) (.var 0)

theorem source_result :
    interpret GraphModel.naturalModel inputEnv identityConsumer = ({0} : Set Nat) := by
  rw [identityConsumer, interpret_beta]
  rfl

theorem transported_result :
    interpret recodedModel (recoding.env inputEnv) identityConsumer = ({1} : Set Nat) := by
  rw [← recoding.interpretation, source_result, changes_set]

/-- Using the unchanged environment instead of the transported input does not
compute the corresponding represented answer. -/
theorem unchanged_environment_wrong_result :
    interpret recodedModel (fun n => ({n} : Set Nat)) identityConsumer ≠ ({1} : Set Nat) := by
  have h := interpret_beta recodedModel (.var 0) (.var 0) (fun n => ({n} : Set Nat))
  change interpret recodedModel _ (.app (.lam (.var 0)) (.var 0)) ≠ _
  rw [h]
  change ({0} : Set Nat) ≠ {1}
  intro h
  have : (0 : Nat) = 1 := Set.singleton_injective h
  omega

theorem all_terms_commute (term : LambdaTerm) (ρ : Env GraphModel.naturalModel) :
    recoding.sets (interpret GraphModel.naturalModel ρ term) =
      interpret recodedModel (recoding.env ρ) term :=
  recoding.interpretation term ρ

theorem actual_theories_equal :
    lambdaTheoryOf GraphModel.naturalModel = lambdaTheoryOf recodedModel :=
  recoding.lambdaTheoryOf_eq

theorem roundtrip (term : LambdaTerm) (ρ : Env GraphModel.naturalModel) :
    recoding.symm.sets (interpret recodedModel (recoding.env ρ) term) =
      interpret GraphModel.naturalModel ρ term := by
  rw [← recoding.interpretation]
  exact recoding.sets.symm_apply_apply _

end Mettapedia.GSLT.GraphTheory.InterpretationTransportControls
