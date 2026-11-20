import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSaturationFixed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationControls

/-!
# Controls for one coherent schematic saturation

One actual output occurrence at one result interpretation supports all type
instances. One coherent run chain contains infinitely many distinct proof
terms. Empty pair agendas miss a real consequence. A genuinely shared open
variable is retained by a full round, while contradictory knowledge admits
no protected execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine.Controls

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig args2 head)
open ApplicationSyntax
open ApplicationSemantics (Derives)

theorem sourceKnown : X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id rowSig) source.knowledge :=
  Interface.Frames.models_nil _

theorem one_output_all_type_instances :
    ∃ f : Attempt 0 1 Nat source, (machine 0 1 Nat).Admits f ∧
      ∃ point : Subst rowSig, 1 ∈ f.result.present ∧ ∀ chosen : Tm,
        (f.result.label 1).ReadsAt X (b := PUnit.unit) point
          (judgment 0 (app identityProof identityProof) (arrow 1 chosen chosen)) := by
  obtain ⟨f, admitted, same, point, _, agrees, present, _⟩ :=
    application_realized 0 1 source (Subst.id rowSig) sourceKnown 0 0 1
      (by decide) (by decide) (by decide) identityProof identityProof
      (arrow 1 proposition proposition) (arrow 1 proposition proposition)
      (identity_reading (arrow 1 proposition proposition)) (identity_reading proposition)
  refine ⟨f, admitted, point, present, fun chosen => ?_⟩
  exact candidate_family_complete f (Subst.id rowSig) point sourceKnown agrees 0 0 1
    (by decide) (by decide) (by decide) same identityProof identityProof
    (arrow 1 chosen chosen) (arrow 1 chosen chosen)
    (identity_reading (arrow 1 chosen chosen)) (identity_reading chosen)

def leftArgument : Tm → Tm
  | .app .app children => children head
  | other => other

def proofPart (value : Tm) : Tm := rightArgument (leftArgument value)

theorem proofPart_judgment (tag : Nat) (proof proposition : Tm) :
    proofPart (judgment tag proof proposition) = proof := rfl

theorem initial_misses_application (chosen : Tm) :
    judgment 0 (app identityProof identityProof) (arrow 1 chosen chosen) ∉
      storeReadings source (Subst.id rowSig) := by
  rintro ⟨o, present, locals, _, _, output⟩
  have only : o = 0 := Finset.mem_singleton.mp present
  subst o
  change locals.applyTerm identityValue = _ at output
  simp only [identityValue, apply_judgment, apply_arrow, identityProof, apply_symbol, Subst.applyTerm] at output
  have impossible := congrArg proofPart output
  rw [proofPart_judgment, proofPart_judgment] at impossible
  cases impossible

theorem first_round_contains_application (chosen : Tm) :
    judgment 0 (app identityProof identityProof) (arrow 1 chosen chosen) ∈
      storeReadings (saturationPrefix 0 1 source (Subst.id rowSig) sourceKnown 1).run.last
        (saturationPrefix 0 1 source (Subst.id rowSig) sourceKnown 1).source := by
  rw [saturationPrefix_exact]
  apply Or.inr
  refine ⟨⟨identityProof, identityProof, arrow 1 chosen chosen, arrow 1 chosen chosen⟩, ?_, ?_⟩
  · intro premise member
    simp only [ApplicationSemantics.consequence, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact ⟨0, by decide, identity_reading (arrow 1 chosen chosen)⟩
    · exact ⟨0, by decide, identity_reading chosen⟩
  · exact Finset.mem_singleton_self _

def iteratedIdentity : Nat → Tm
  | 0 => identityProof
  | n + 1 => app identityProof (iteratedIdentity n)

theorem iterated_derives (n : Nat) (chosen : Tm) :
    Derives 0 1 (source.dataAt X (b := PUnit.unit) (Subst.id rowSig)) (Subst.id rowSig)
      (judgment 0 (iteratedIdentity n) (arrow 1 chosen chosen)) := by
  induction n with
  | zero =>
    apply Derives.hypothesis
    exact (hypothesis_occurrence source (Subst.id rowSig) _).mpr
      ⟨0, by decide, identity_reading chosen⟩
  | succ n ih =>
    exact Derives.apply (domain := arrow 1 chosen chosen)
      (Derives.hypothesis ((hypothesis_occurrence source (Subst.id rowSig) _).mpr
        ⟨0, by decide, identity_reading (arrow 1 chosen chosen)⟩)) ih

theorem one_chain_contains_all_instances (n : Nat) (chosen : Tm) :
    judgment 0 (iteratedIdentity n) (arrow 1 chosen chosen) ∈
      saturationReadings 0 1 source (Subst.id rowSig) sourceKnown :=
  (saturationReadings_iff_derives source (Subst.id rowSig) sourceKnown _).mpr (iterated_derives n chosen)

theorem application_size (function argument : Tm) :
    (app function argument).size = 1 + function.size + argument.size := by
  change 1 + (∑ i : Fin 2, (args2 function argument i).size) = 1 + function.size + argument.size
  rw [Fin.sum_univ_two]
  change 1 + (function.size + argument.size) = 1 + function.size + argument.size
  omega

theorem iterated_size (n : Nat) : (iteratedIdentity n).size = 2 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedIdentity, application_size, ih]
    change 1 + 1 + (2 * n + 1) = 2 * (n + 1) + 1
    omega

theorem iterated_injective : Function.Injective iteratedIdentity := by
  intro n m same
  have sizes := congrArg Term.size same
  rw [iterated_size, iterated_size] at sizes
  omega

theorem infinite_proof_family :
    (saturationReadings 0 1 source (Subst.id rowSig) sourceKnown).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : Nat => judgment 0 (iteratedIdentity n) (arrow 1 proposition proposition)) ?_ ?_
  · intro n m same
    apply iterated_injective
    have proofs := congrArg proofPart same
    simpa only [proofPart_judgment] using proofs
  · intro n
    exact one_chain_contains_all_instances n proposition

def openSource : Store Nat :=
  ⟨PUnit.unit, [], {0, 1}, fun o => if o = 0 then .schematic identitySchema else .shared (.var 7)⟩

theorem full_round_preserves_unresolved_source :
    ∃ execution : ProtectedRun 0 1 openSource (Subst.id rowSig),
      storeReadings execution.run.last execution.source =
        StepWeb.KernelRounds.immediate (ApplicationSemantics.consequence 0 1)
          (storeReadings openSource (Subst.id rowSig)) ∧
      execution.source.applyTerm (execution.run.toLast.applyTerm (.var 7)) = .var 7 := by
  obtain ⟨execution, exactResult⟩ := application_round_exists (judgmentTag := 0) (arrowTag := 1)
    openSource (Subst.id rowSig) (Interface.Frames.models_nil _)
  refine ⟨execution, exactResult, execution.agrees (.var 7) ?_⟩
  exact ambient_in_context openSource 1 (by decide) (.var 7)
    (show (.var 7 : Tm) ∈ (openSource.label 1).ambientTerms by simp [openSource, Row.ambientTerms])

def inconsistentSource : Store Nat :=
  ⟨PUnit.unit, [(symbol 20, symbol 21)], {0}, fun _ => .schematic identitySchema⟩

theorem inconsistent_source_has_no_protected_execution (caller : Subst rowSig) :
    ¬ Nonempty (ProtectedRun 0 1 inconsistentSource caller) := by
  rintro ⟨execution⟩
  have solved := execution.run.models_start execution.source execution.known
  have impossible := solved (symbol 20, symbol 21) (List.mem_singleton_self _)
  change symbol 20 = symbol 21 at impossible
  cases impossible

#print axioms one_output_all_type_instances
#print axioms initial_misses_application
#print axioms first_round_contains_application
#print axioms one_chain_contains_all_instances
#print axioms iterated_injective
#print axioms infinite_proof_family
#print axioms full_round_preserves_unresolved_source
#print axioms inconsistent_source_has_no_protected_execution

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine.Controls
