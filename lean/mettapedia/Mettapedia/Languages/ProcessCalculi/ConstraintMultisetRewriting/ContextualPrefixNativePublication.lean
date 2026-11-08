import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixIsolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFrameAsks

/-!
# Actual solver-backed publication preserves an isolated prefix

The bounded worklist processes the disjoint prefix and ambient problems.
Its reusable output keeps the actual residual equations, while its value
uses only the copied prefix declarations. Prefix instances and original-cut
guard asks are preserved without a solver-completion assumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixNativePublication

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows

variable {S : Signature} {Prefix Ambient Local Next : Type}
    (savedDecl : Prefix → MetaArity S) (ambient : Ambient → MetaArity S)
    [DecidableEq Prefix] [DecidableEq Ambient] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]
    (saved : ContextualResidual.Problem savedDecl) (current : ContextualResidual.Problem ambient)

structure Computed (fuel : Nat) where
  update : ContextualFrameUpdate.Update (ContextualPrefixIsolation.problem savedDecl ambient saved current)
  computed : ContextualFrameWorklist.run fuel (ContextualPrefixIsolation.combined savedDecl ambient)
    (ContextualPrefixIsolation.problem savedDecl ambient saved current) = .residual update

theorem realize (fuel : Nat) (savedConsistent : ContextualConditionalExecution.Solvable saved)
    (currentConsistent : ContextualConditionalExecution.Solvable current) :
    Nonempty (Computed savedDecl ambient saved current fuel) := by
  obtain ⟨Future, future, candidate, model⟩ := savedConsistent
  obtain ⟨Extra, extra, both, jointModel, _⟩ :=
    ContextualPrefixIsolation.extend_model savedDecl ambient saved current currentConsistent candidate model
  obtain ⟨update, computed, _⟩ := ContextualFrameWorklist.preserves_every_solution fuel
    (ContextualPrefixIsolation.problem savedDecl ambient saved current) _ both jointModel
  exact ⟨⟨update, computed⟩⟩

variable {savedDecl ambient saved current} {fuel : Nat}
    (result : Computed savedDecl ambient saved current fuel)

abbrev Computed.targetFamily := ContextualComputedFreshFrame.active
  (ContextualPrefixIsolation.combined savedDecl ambient) result.update.declaration

def Computed.information : ContextualResidual.Problem result.targetFamily :=
  ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource result.update)
    (ContextualPrefixIsolation.problem savedDecl ambient saved current)

def Computed.row (locals : Local → MetaArity S) {Γ : Ctx S} {sort : S.Srt}
    (value : Term (signature S savedDecl) Γ sort) :
    Row (ContextualPublication.privateFamily locals result.update.declaration) result.targetFamily Γ sort :=
  ContextualConditionalPublication.ordinary locals result.update.declaration result.targetFamily
    (ContextualConditionalAnswers.ofUpdate result.update
      (instantiate (ContextualStoredRows.privateSource savedDecl ambient) value))

theorem Computed.row_instances (locals : Local → MetaArity S) (currentConsistent : ContextualConditionalExecution.Solvable current)
    {Γ : Ctx S} {sort : S.Srt} {next : Next → MetaArity S}
    (candidate : Assignment result.targetFamily next) (value : Term (signature S savedDecl) Γ sort)
    (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals result.update.declaration) result.targetFamily candidate pattern
        (result.row locals value) ↔ ContextualPublication.SourceInstances saved value next pattern :=
  (ContextualConditionalPublication.update_matches_source locals result.targetFamily result.update candidate _ pattern).trans
    (ContextualPrefixIsolation.instances_iff savedDecl ambient saved current currentConsistent value pattern)

theorem Computed.original_guard_asks {O : Type} (locals : Local → MetaArity S)
    (currentConsistent : ContextualConditionalExecution.Solvable current)
    {Γ : Ctx S} {sort : S.Srt} (rows : O → Row locals savedDecl Γ sort) (world : Finset O)
    (check : Check (Term (signature S savedDecl) Γ sort)) :
    ContextualConditionalGuards.Ask locals result.information
        (fun occurrence => ((rows occurrence).map locals savedDecl
          (ContextualStoredRows.privateSource savedDecl ambient)).map locals _
          (ContextualComputedFreshFrame.includeSource result.update)) world
        ((check.map (instantiate (ContextualStoredRows.privateSource savedDecl ambient))).map
          (instantiate (ContextualComputedFreshFrame.includeSource result.update))) ↔
      ContextualConditionalGuards.Ask locals saved rows world check := by
  have moved := ContextualConditionalNaturality.ask_extension_iff locals
    (ContextualComputedFreshFrame.declarationExtension result.update)
    (ContextualPrefixIsolation.problem savedDecl ambient saved current)
    (fun occurrence => (rows occurrence).map locals savedDecl (ContextualStoredRows.privateSource savedDecl ambient)) world
    (check.map (instantiate (ContextualStoredRows.privateSource savedDecl ambient)))
  rw [ContextualComputedFreshFrame.declarationExtension_assignment] at moved
  exact moved.trans (ContextualPrefixIsolation.asks_iff savedDecl ambient locals saved current currentConsistent rows world check)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixNativePublication
