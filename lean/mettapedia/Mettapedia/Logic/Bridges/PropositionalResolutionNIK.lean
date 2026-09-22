import Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority
import Mettapedia.GSLT.Logic.PropositionalResolutionNIK

/-!
# NIK contract for the propositional resolution kernel

The native kernel lives in `PropositionalResolutionNIK` (rules, replay,
`empty_iff_unsat`). This module only hosts that kernel as a qualified
NIK rule system: least closure is scope, Boolean consequence is meaning,
derivation trees are certificates. Foundation is not used.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.PropositionalResolutionNIK

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef.NIKInitialRuleClosureAuthority
open Mettapedia.GSLT.Logic.PropositionalFormula
open Mettapedia.GSLT.Logic.PropositionalResolution

def resolutionKernel (Γ : CNF) : QualifiedRuleSystem Clause where
  rules := ResRule Γ
  witness := resWitness Γ
  Meaning := Consequence Γ
  rules_sound := fun _ _ rule hyp => resRule_sound rule hyp

theorem accepted_means_consequence (Γ : CNF) (c : Clause)
    (certificate : Derivation Clause (resWitness Γ).W)
    (accepted :
      ((resolutionKernel Γ).contract.checker ()).check c certificate = true) :
    Consequence Γ c :=
  QualifiedRuleSystem.accepted_meaning (resolutionKernel Γ) c certificate accepted

theorem empty_accepted_unsat (Γ : CNF)
    (certificate : Derivation Clause (resWitness Γ).W)
    (accepted :
      ((resolutionKernel Γ).contract.checker ()).check [] certificate = true) :
    Unsat Γ :=
  (empty_iff_unsat Γ).mp
    (((resolutionKernel Γ).contract.scopeAuthority ()).sound [] certificate accepted)

theorem unsat_has_accepted_empty (Γ : CNF) (h : Unsat Γ) :
    ∃ certificate : Derivation Clause (resWitness Γ).W,
      ((resolutionKernel Γ).contract.checker ()).check [] certificate = true := by
  obtain ⟨certificate, valid, concludes⟩ := replay_empty_of_unsat Γ h
  refine ⟨certificate, ?_⟩
  unfold QualifiedRuleSystem.contract QualifiedRuleSystem.checker
  simp [Mettapedia.OSLF.Framework.InitialModalSchema.replayChecker]
  exact ⟨valid, concludes⟩

#print axioms accepted_means_consequence
#print axioms empty_accepted_unsat
#print axioms unsat_has_accepted_empty

end Mettapedia.Logic.Bridges.PropositionalResolutionNIK
