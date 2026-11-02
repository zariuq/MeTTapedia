import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCompleteness

/-!
# Proof observation of physical execution and its exact converse

Raw physical histories retain request traffic, allocation identities and
unselected work. The equivalence here quotients by the specified ordered
proof-vector observation only. Surjectivity is supplied by the actual source
compiler, not postulated as a field of execution. Cut is realized by continuing
at the first execution's physical endpoint and selecting its actual outputs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value locatedAction)
open InferenceRequestExecution (Occurrence payload system)
open InferenceJudgmentBoards
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef} {before : Configuration Value Occurrence}
  {prior : Board before} {goals : List Pattern}

noncomputable def compile (background : locatedAction.Consistent before.equations)
    (proofs : OpenDerivationList definition prior.judgments goals) :
    Execution (definition := definition) before prior goals :=
  Classical.choose (every_vector_is_observed background prior proofs)

theorem compile_observe (background : locatedAction.Consistent before.equations)
    (proofs : OpenDerivationList definition prior.judgments goals) :
    (compile background proofs).observe = proofs :=
  Classical.choose_spec (every_vector_is_observed background prior proofs)

def proofObservation (definition : ValidatedCalculusLanguageDef)
    (before : Configuration Value Occurrence) (prior : Board before) (goals : List Pattern) :
    Setoid (Execution (definition := definition) before prior goals) where
  r first second := first.observe = second.observe
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev ObservedExecution (definition : ValidatedCalculusLanguageDef)
    (before : Configuration Value Occurrence) (prior : Board before) (goals : List Pattern) :=
  Quotient (proofObservation definition before prior goals)

noncomputable def observeQuotient : ObservedExecution definition before prior goals →
    OpenDerivationList definition prior.judgments goals :=
  Quotient.lift Execution.observe (fun _ _ same => same)

/-- The declared proof observation of actual executions is exactly the
source derivation vector. Equal judgments at different premise positions
remain different proof vectors under this equivalence. -/
noncomputable def proofObservationEquiv (background : locatedAction.Consistent before.equations) :
    ObservedExecution definition before prior goals ≃
      OpenDerivationList definition prior.judgments goals where
  toFun := observeQuotient
  invFun proofs := Quotient.mk _ (compile background proofs)
  left_inv observed := by
    induction observed using Quotient.inductionOn with
    | _ execution =>
        apply Quotient.sound
        exact compile_observe background execution.observe
  right_inv proofs := compile_observe background proofs

/-- Compilation after observation reproduces precisely the observation;
it makes no claim to reproduce hidden request traffic or physical IDs. -/
theorem compile_observed_equivalent (background : locatedAction.Consistent before.equations)
    (execution : Execution (definition := definition) before prior goals) :
    (proofObservation definition before prior goals).r (compile background execution.observe) execution :=
  compile_observe background execution.observe

/-- A source cut is physically realized after the first execution, using
the first execution's selected output occurrences as the second input map. -/
theorem realizes_cut (background : locatedAction.Consistent before.equations)
    (first : Execution (definition := definition) before prior goals) {conclusions : List Pattern}
    (secondProofs : OpenDerivationList definition goals conclusions) :
    ∃ second : Execution (definition := definition) first.after first.board conclusions,
      (first.follow second).observe = secondProofs.bind first.observe := by
  obtain ⟨second, replay⟩ := realizes_derivations secondProofs first.after
    (first.ordinary.consistent background) first.board first.outputs
  refine ⟨second, ?_⟩
  rw [Execution.follow_observe]
  change second.observe.bind first.arrow = _
  rw [replay]
  exact OpenDerivationList.bind_assoc secondProofs (first.outputs.interpret definition) first.arrow

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
