import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConventionSteps

/-!
# The manuscript's calculus by a finite program, without the variable convention as a hypothesis

The step is the single-firing step `RuleSyntax.step` of the fixed three-rule `program` of `FiniteComm`, at the
one frame of structural substitution on patterns, with the five choices stated there: a bag store, one match,
guards asked after the firing's own tells (the rules have none), a fixed set of rules beside the store, one
store of knowledge.

`manuscript_calculus_by_a_finite_program` assumes the variable convention across parallel parts: its first
clause is for hosted processes (`HostedProcess`: hosted parts that share no variable), and its source's COMM
(`BagComm`) asks the convention of its redex. Here the convention is not assumed. The process is any tame process
whose parts are hosted; alpha-equivalence, in the manuscript's sense (`Corrected.Alpha`) or as equal closed
forms, enters where the renaming does.

## The clauses (`manuscript_calculus_without_the_convention`)

1. every tame process with hosted parts is alpha-equivalent, part by part, to a hosted process, which is
   represented (the renaming of `FiniteConvention`);
2. every transition of the step is a communication or housekeeping;
3. housekeeping keeps the represented bag;
4. at a ground-unifiable bag, a communication is a source step (`BagComm`);
5. every source step up to alpha-equivalence (`CommUpToAlpha`: a COMM step of a tame alpha-variant of the
   parts), from a represented bag of tame parts, is matched by housekeeping firings and one communication, to
   a state that represents an alpha-variant of the source step's target;
6. a run of `k` housekeeping firings has `k` at most the spine weight of the parts.

The other conditions stay named: ground principal unifiers with first-order values (`BagComm`,
`GroundUnifiable`), first-order closed continuations without inner binders (`Hosted`), binary parallel
composition (`parts`), and tameness (`Corrected.tame`).

Along whole runs (`hosted_runs_up_to_alpha` in `FiniteConventionSteps`): every run of the source up to
alpha-equivalence from the parts of a tame process with hosted parts is matched by a run of the step from the
initial state of the renamed process.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open MeTTaCalculus.Corrected (tame Alpha close)
open FiniteProgram (parts Hosted HostedProcess BagComm Represents RepresentsBy GroundUnifiable program Communicates
  Administers AdministrativeRun weightOf communication_complete manuscript_calculus_by_a_finite_program
  every_hosted_process_represented)
open Comm (Tm X E)
open LogicOverTheStep.StepSpan (Succ)

/-- **The source up to alpha-equivalence contains the source**: a COMM step of a tame bag is one. -/
theorem commUpToAlpha_of_bagComm {M M' : Multiset Pattern} (tameM : ∀ c ∈ M, tame c = true) (step : BagComm M M') :
    CommUpToAlpha M M' :=
  ⟨M, M', tameM, rfl, step, rfl⟩

/-- **At a bag under the convention, the source up to alpha-equivalence is the source, up to alpha-equivalence of
the target.** -/
theorem bagComm_of_commUpToAlpha {M M' : Multiset Pattern} (tameM : ∀ c ∈ M, tame c = true)
    (hostedM : ∀ c ∈ M, Hosted c) (conventionM : Convention M) (step : CommUpToAlpha M M') :
    ∃ M'', BagComm M M'' ∧ M''.map close = M'.map close := by
  obtain ⟨N, N', tameN, sameN, comm, sameN'⟩ := step
  obtain ⟨M'', commM, closeM'', -⟩ := bagComm_respects_alpha tameM hostedM conventionM tameN sameN comm
  exact ⟨M'', commM, closeM''.trans sameN'⟩

/-- **Every tame process with hosted parts is represented, up to alpha-equivalence**: its renaming apart is a
hosted process, related to it by the manuscript's renaming rule, part by part, and represented. -/
theorem every_tame_hosted_process_represented (P : Pattern) (tameP : tame P = true)
    (hostedParts : ∀ c ∈ parts P, Hosted c) :
    ∃ P', Alpha P P' ∧ HostedProcess P' ∧ List.Forall₂ Alpha (parts P) (parts P') ∧
      ∃ s : State Tm ℕ, Represents s (parts P') := by
  obtain ⟨alpha, hostedP', each⟩ := renaming_into_the_convention P tameP hostedParts
  exact ⟨renameApart P, alpha, hostedP', each, every_hosted_process_represented _ hostedP'⟩

/-- **Every source step up to alpha-equivalence is matched.** From a state that represents a bag of tame parts, a
COMM step between alpha-variants of the parts is matched by housekeeping firings and one communication, to a state
that represents an alpha-variant of the step's target. The represented bag satisfies the convention and its parts
are hosted (`representsBy_convention`, `representsBy_hosted`); the source's bag need not satisfy the convention. -/
theorem communication_complete_up_to_alpha {s : State Tm ℕ} {M M' : Multiset Pattern} (represented : Represents s M)
    (tameM : ∀ c ∈ M, tame c = true) (step : CommUpToAlpha M M') :
    ∃ (s₁ s₂ : State Tm ℕ) (M'' : Multiset Pattern), Relation.ReflTransGen Administers s s₁ ∧
      Communicates s₁ s₂ ∧ Represents s₂ M'' ∧ M''.map close = M'.map close := by
  obtain ⟨comp, representedBy⟩ := represented
  obtain ⟨N, N', tameN, sameN, comm, sameN'⟩ := step
  obtain ⟨M'', commM, closeM'', -⟩ := bagComm_respects_alpha tameM (representsBy_hosted representedBy)
    (representsBy_convention representedBy) tameN sameN comm
  obtain ⟨s₁, s₂, run, fires, represented₂⟩ := communication_complete representedBy commM
  exact ⟨s₁, s₂, M'', run, fires, represented₂, closeM''.trans sameN'⟩

/-- **The F1R3FLY manuscript's calculus on the single-firing step by a finite program, without the variable
convention as a hypothesis.**

The step is `RuleSyntax.step` of the fixed three-rule `program` at the one frame of structural substitution on
patterns. Through `Represents`, with the bag of parallel parts as the source:

1. every tame process whose parts are hosted is alpha-equivalent, part by part and by the manuscript's renaming
   rule, to a hosted process that is represented;
2. every transition of the step is a communication or housekeeping;
3. housekeeping keeps the represented bag;
4. at a bag whose unifiable pairs of inputs have ground principal unifiers with first-order values, a
   communication is a source step;
5. every source step up to alpha-equivalence from a represented bag of tame parts is matched by housekeeping
   firings and one communication, up to alpha-equivalence of the target;
6. a run of `k` housekeeping firings from a state represented through `comp` has `k` at most the spine weight of
   its parts. -/
theorem manuscript_calculus_without_the_convention :
    program.Finite ∧
    (∀ P : Pattern, tame P = true → (∀ c ∈ parts P, Hosted c) →
      ∃ P', Alpha P P' ∧ HostedProcess P' ∧ List.Forall₂ Alpha (parts P) (parts P') ∧
        ∃ s : State Tm ℕ, Represents s (parts P')) ∧
    (∀ s s' : State Tm ℕ,
      Succ (RuleSyntax.step X ℕ E program).toStep s s' ↔ Communicates s s' ∨ Administers s s') ∧
    (∀ {s s' : State Tm ℕ} {M : Multiset Pattern}, Represents s M → Administers s s' → Represents s' M) ∧
    (∀ {s s' : State Tm ℕ} {M : Multiset Pattern}, Represents s M → GroundUnifiable M →
      Communicates s s' → ∃ M', BagComm M M' ∧ Represents s' M') ∧
    (∀ {s : State Tm ℕ} {M M' : Multiset Pattern}, Represents s M → (∀ c ∈ M, tame c = true) →
      CommUpToAlpha M M' → ∃ (s₁ s₂ : State Tm ℕ) (M'' : Multiset Pattern),
        Relation.ReflTransGen Administers s s₁ ∧ Communicates s₁ s₂ ∧ Represents s₂ M'' ∧
          M''.map close = M'.map close) ∧
    (∀ {s e : State Tm ℕ} {M : Multiset Pattern} {comp : ℕ → Pattern} {k : ℕ},
      RepresentsBy s M comp → AdministrativeRun k s e → k ≤ weightOf s.present comp) := by
  obtain ⟨finite, -, succ, housekeeping, sound, -, bounded⟩ := manuscript_calculus_by_a_finite_program
  exact ⟨finite, every_tame_hosted_process_represented, succ, housekeeping, sound,
    fun represented tameM step => communication_complete_up_to_alpha represented tameM step, bounded⟩

#print axioms commUpToAlpha_of_bagComm
#print axioms bagComm_of_commUpToAlpha
#print axioms every_tame_hosted_process_represented
#print axioms communication_complete_up_to_alpha
#print axioms manuscript_calculus_without_the_convention

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteConvention
