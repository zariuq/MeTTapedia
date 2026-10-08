import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.ExecutableCheckingControls

/-!
# Discriminating source-annotation controls

Checking after domain erasure is insufficient. The source tests distinguish
terms with identical erasures but different written contracts. They also check
annotations inside expected types and context entries, where early reduction
could otherwise conceal an invalid source term.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ExecutableWrittenCheckingControls

open TypedEquality.Normalization
open ExecutableCheckingControls (level num zero sort rules)

def test {n : Nat} (context : ExecutableWrittenChecking.SourceContext Tower.Head n)
    (term type : ATm Tower.Head n) : Bool :=
  ExecutableTowerNumbers.acceptsSource level 80 context term type

def numA {n : Nat} : ATm Tower.Head n := ATm.ofTm num

def zeroA {n : Nat} : ATm Tower.Head n := ATm.ofTm zero

def sortA {n : Nat} (index : Nat) : ATm Tower.Head n := ATm.ofTm (sort index)

def idType : ATm Tower.Head 0 := .pi numA numA

def writtenId : ATm Tower.Head 0 := .lamTyped numA (.var 0)

def wrongDomainId : ATm Tower.Head 0 := .lamTyped (sortA 0) (.var 0)

def missingDomain : ATm Tower.Head 0 := .lamTyped (.const `missing) zeroA

/-- A context entry computes to a universe after erasure, but its original
written function domain is undeclared. -/
def invalidContextDomain : ATm Tower.Head 0 :=
  .app (.lamTyped (.const `missing) (sortA 0)) zeroA

def invalidContext : ExecutableWrittenChecking.SourceContext Tower.Head 1 :=
  .snoc .nil invalidContextDomain

/-- The proposed identity type contains two annotated function endpoints. -/
def invalidExpected : ATm Tower.Head 0 :=
  .id idType missingDomain missingDomain

theorem written_identity_accepted : test .nil writtenId idType = true := by decide +kernel

theorem written_identity_synthesized :
    (ExecutableWrittenChecking.synth (TowerNumbersModel.setting level (fun _ => 0))
      (TowerNumbersModel.facts level) (TowerNumbersModel.roots level)
      (TowerNumbersModel.heads level) (TowerNumbersModel.algebra level)
      (ExecutableTowerNumbers.declaredTypesFormed level)
      (ExecutableTowerNumbers.choices level) (ExecutableTowerNumbers.fullReducer level)
      80 .nil .nil writtenId).map Sigma.fst = some idType.erase := by
  decide +kernel

theorem erased_identities_agree : writtenId.erase = wrongDomainId.erase := rfl

theorem wrong_written_domain_rejected : test .nil wrongDomainId idType = false := by decide +kernel

theorem missing_written_domain_rejected : test .nil missingDomain idType = false := by decide +kernel

theorem erased_missing_domain_is_typed :
    ExecutableCheckingControls.test .nil missingDomain.erase idType.erase = true := by
  decide +kernel

theorem written_expected_type_rejected :
    test .nil (.refl missingDomain) invalidExpected = false := by decide +kernel

theorem invalid_written_context_rejected :
    test invalidContext (.var 0) (sortA 0) = false := by decide +kernel

theorem erased_context_would_accept :
    ExecutableCheckingControls.test invalidContext.erase (.var 0) (sort 0) = true := by
  decide +kernel

theorem dependent_source_pack_accepted :
    test .nil (ATm.ofTm ExecutableCheckingControls.pack)
      (ATm.ofTm ExecutableCheckingControls.packType) = true := by decide +kernel

theorem well_scoped_written_body :
    NativeSyntax.checkScope 0 (NativeSyntax.encode writtenId) = true := by decide +kernel

theorem written_domain_is_outside_binder :
    NativeSyntax.checkScope 0 (.lamTyped (.var 0) (.var 0) : NativeSyntax.Raw Tower.Head) =
      false := by decide +kernel

theorem raw_scope_refusal :
    ExecutableTowerNumbers.acceptsRaw level 80 .nil
      (.lamTyped (.var 0) (.var 0)) (NativeSyntax.encode idType) = false := by decide +kernel

theorem raw_written_identity_accepted :
    ExecutableTowerNumbers.acceptsRaw level 80 .nil
      (NativeSyntax.encode writtenId) (NativeSyntax.encode idType) = true := by decide +kernel

theorem substitution_checks_domain_and_lifts_body :
    NativeSyntax.substituteZero (.const `A : NativeSyntax.Raw Tower.Head) 0
      (.lamTyped (.var 0) (.pair (.var 0) (.var 1))) =
      .lamTyped (.const `A) (.pair (.var 0) (.const `A)) := by decide +kernel

/-- The accepted source has its annotated typing, rather than only an erased
term's typing. -/
theorem written_identity_typed : TypedEquality.ATyped rules .nil writtenId idType.erase :=
  ExecutableTowerNumbers.acceptsSource_sound level written_identity_accepted

end ExecutableWrittenCheckingControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
