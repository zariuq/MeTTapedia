import Mettapedia.TypeTheory.TH0NamedElaborationBridge
import Mettapedia.Logic.HOL.HigherOrderAlgorithmProfiles
import Mettapedia.Logic.OpenEndedReasoningEnvelope
import Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition

/-!
# The computational trinity for the portable TH0 boundary

This module connects four layers that must remain distinct in a TPTP and
MeTTa implementation:

* a named TH0 formula elaborates to one intrinsically typed formula;
* representation-specific dialect adapters observe that same formula;
* proof-relevant substitutions induce operational GSLT events whose
  proposition-valued readout is syntactic unifiability;
* an exact two-stage native checker transports final physical acceptance back
  to an intrinsic unifier and its operational cospan.

The connection is deliberately independent of a search calculus.  Staged
unifier enumeration, proof planning, lambda-superposition, higher-order ILP,
finite-model search, and infinitary search may all propose artifacts, but the
semantic checker and the typed operational realization do not depend on the
producer's role.

The final section is a realization contract, not a claim that a particular C
file has been generated.  The external build must establish that its
StructuredC and C carriers inhabit the two exact refinements.  In particular,
agreement only on canonical compiler output is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.TH0ComputationalTrinity

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ExactCheckerWireRefinement
open Mettapedia.GSLT.LanguageDef.ExactCheckerRefinementComposition
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.TH0SyntacticUnifierService
open Mettapedia.Logic.HOL.TH0SubstitutionOperationalGSLT
open Mettapedia.Logic.HOL.HigherOrderAlgorithmProfiles
open Mettapedia.Logic.ProofProducingSearch
open Mettapedia.TypeTheory.TH0InterchangeAlgorithmBoundary
open Mettapedia.TypeTheory.TH0NamedElaborationBridge
open Mettapedia.TypeTheory.TH0SimultaneousSubstitutionService

/-! ## Intensional evidence and its operational and extensional views -/

/-- An intrinsic unifier together with the two proof-relevant operational
events that it determines.  The event data remains available even though the
ordinary GSLT observer sees only existence of a step. -/
structure OperationalRealization (problem : Problem) where
  unifier : Unifier problem
  leftEvent : Event
    (UnifierOps.leftState unifier) (UnifierOps.apex unifier)
  rightEvent : Event
    (UnifierOps.rightState unifier) (UnifierOps.apex unifier)

namespace OperationalRealization

/-- Every intrinsic unifier has a canonical operational realization. -/
def ofUnifier {problem : Problem} (unifier : Unifier problem) :
    OperationalRealization problem where
  unifier := unifier
  leftEvent := UnifierOps.leftEvent unifier
  rightEvent := UnifierOps.rightEvent unifier

/-- Forget exact event occurrences to proposition-valued GSLT steps. -/
theorem semanticCospan {problem : Problem}
    (realization : OperationalRealization problem) :
    (theory problem.type.decode).Step
        (UnifierOps.leftState realization.unifier)
        (UnifierOps.apex realization.unifier) ∧
      (theory problem.type.decode).Step
        (UnifierOps.rightState realization.unifier)
        (UnifierOps.apex realization.unifier) :=
  ⟨⟨realization.leftEvent⟩, ⟨realization.rightEvent⟩⟩

/-- Extensional unifiability and existence of a proof-relevant operational
realization coincide.  This does not identify two realizations. -/
theorem meaning_iff_nonempty (problem : Problem) :
    problem.Meaning ↔ Nonempty (OperationalRealization problem) := by
  constructor
  · rintro ⟨unifier⟩
    exact ⟨ofUnifier unifier⟩
  · rintro ⟨realization⟩
    exact ⟨realization.unifier⟩

theorem ofMeaning {problem : Problem} (meaning : problem.Meaning) :
    Nonempty (OperationalRealization problem) :=
  (meaning_iff_nonempty problem).mp meaning

end OperationalRealization

/-! ## Named source, portable packet, and dialect observations -/

/-- A decoded formula gives a well-typed reflexive unification problem.  This
is a small but genuine consumer of the portable packet: malformed packets do
not pass merely because their two raw trees are equal. -/
def reflexiveProblemOf (packet : FormulaPacket) : Problem where
  source := []
  target := []
  type := .prop
  left := packet.term
  right := packet.term

/-- The empty-context identity substitution used for a closed formula. -/
def closedIdentityCertificate : SubstitutionPacket :=
  encodeSubstitution
    (Subst.id (Base := String) (Const := Constant) (Γ := []))

/-- Independent TH0 admission, rather than raw packet equality, is sufficient
for the reflexive problem to replay. -/
theorem admitted_formula_reflexive_check
    {packet : FormulaPacket} {formula : ClosedFormula Constant}
    (admitted : decodeFormula? packet = some formula) :
    check (reflexiveProblemOf packet) closedIdentityCertificate = true := by
  unfold decodeFormula? at admitted
  split at admitted
  next valid =>
    have termDecoded :
        decodeTerm? [] packet.term (.prop : Ty String) = some formula :=
      admitted
    have executes :
        ∃ result,
          substitutePacket? closedIdentityCertificate TypePacket.prop
              packet.term = some result := by
      refine ⟨encodeTerm
        (subst
          (TypedSubstitution.ofSubst
            (Subst.id (Base := String) (Const := Constant) (Γ := []))).toSubst
          formula), ?_⟩
      simp [closedIdentityCertificate, substitutePacket?, TypePacket.prop,
        termDecoded]
    obtain ⟨result, executed⟩ := executes
    unfold TH0SyntacticUnifierService.check reflexiveProblemOf
    rw [if_pos (by rfl), if_pos (by rfl), executed]
    simp
  next invalid =>
    simp at admitted

/-- A successful named compilation simultaneously has one intrinsic meaning
for any two conforming dialect adapters and one proof-relevant operational
realization.  Thus named syntax, portable data, dialect storage, and execution
meet without making any dialect the HOL authority. -/
theorem compiled_formula_has_dialect_and_operational_views
    (first second : FormulaAdapter)
    {signature : SignaturePacket} {source : NamedTH0Term}
    {packet : FormulaPacket}
    (compiled : compileFormula signature source = .ok packet) :
    ∃ formula : ClosedFormula Constant,
      first.decode packet = some formula ∧
      second.decode packet = some formula ∧
      Nonempty (OperationalRealization (reflexiveProblemOf packet)) := by
  obtain ⟨formula, firstReplay, secondReplay⟩ :=
    compileFormula_adapter_agreement first second compiled
  have admitted : decodeFormula? packet = some formula := by
    rw [← first.agrees]
    exact firstReplay
  have accepted := admitted_formula_reflexive_check admitted
  exact ⟨formula, firstReplay, secondReplay,
    OperationalRealization.ofMeaning (check_sound accepted)⟩

/-! ## Search is an accelerator over the same meaning -/

universe uOrigin

/-- Whichever algorithm produced an accepted syntactic-unification
certificate, independent replay yields the same intrinsic and operational
meaning.  The role tag has no authority in this proof. -/
theorem accepted_search_has_operational_realization
    {Origin : Type uOrigin}
    (source : CheckedCandidateSource authority Origin)
    {stage : Nat} (accepted : source.producer.AcceptedAt stage) :
    Nonempty
      (OperationalRealization accepted.proposal.claim) :=
  OperationalRealization.ofMeaning
    (CheckedCandidateSource.accepted_sound source accepted)

/-- Eventual positive success has the same operational meaning; no claim is
made from absence at a finite stage. -/
theorem eventual_search_has_operational_realization
    {Origin : Type uOrigin}
    (source : CheckedCandidateSource authority Origin)
    {problem : Problem} (accepted : source.producer.EventuallyAccepts problem) :
    Nonempty (OperationalRealization problem) :=
  OperationalRealization.ofMeaning
    (CheckedCandidateSource.eventual_acceptance_sound source accepted)

/-! ## Exact StructuredC-to-C-shaped refinement -/

/-- The intrinsic syntactic-unification checker in the representation-
independent checker interface. -/
def syntacticChecker : Checker Problem SubstitutionPacket where
  check := TH0SyntacticUnifierService.check

theorem syntacticChecker_sound :
    syntacticChecker.Sound Problem.Meaning := by
  intro problem certificate accepted
  exact check_sound accepted

universe uStructuredProblem uStructuredCertificate
universe uCProblem uCCertificate

variable
    {StructuredProblem : Type uStructuredProblem}
    {StructuredCertificate : Type uStructuredCertificate}
    {CProblem : Type uCProblem} {CCertificate : Type uCCertificate}
    {sourceProblemCodec : Checker.PartialCodec Problem StructuredProblem}
    {sourceCertificateCodec :
      Checker.PartialCodec SubstitutionPacket StructuredCertificate}
    {structuredChecker : Checker StructuredProblem StructuredCertificate}
    {structuredProblemCodec : Checker.PartialCodec StructuredProblem CProblem}
    {structuredCertificateCodec :
      Checker.PartialCodec StructuredCertificate CCertificate}
    {cChecker : Checker CProblem CCertificate}

/-- Canonical source packets commute through both exact native boundaries. -/
theorem canonical_native_check_commutes
    (pipeline : DirectNativeCheckerPipeline syntacticChecker
      sourceProblemCodec sourceCertificateCodec structuredChecker
      structuredProblemCodec structuredCertificateCodec cChecker)
    (problem : Problem) (certificate : SubstitutionPacket) :
    cChecker.check
        ((composeCodec sourceProblemCodec structuredProblemCodec).encode
          problem)
        ((composeCodec sourceCertificateCodec structuredCertificateCodec).encode
          certificate) =
      TH0SyntacticUnifierService.check problem certificate :=
  pipeline.exactToC.canonical_check_commutes problem certificate

/-- Acceptance of an arbitrary final C-shaped input decodes to an intrinsic
unifier and therefore to its proof-relevant operational realization.  The
input need not have been emitted by the canonical encoder. -/
theorem accepted_native_has_operational_realization
    (pipeline : DirectNativeCheckerPipeline syntacticChecker
      sourceProblemCodec sourceCertificateCodec structuredChecker
      structuredProblemCodec structuredCertificateCodec cChecker)
    {cProblem : CProblem} {cCertificate : CCertificate}
    (accepted : cChecker.check cProblem cCertificate = true) :
    ∃ problem : Problem,
      (composeCodec sourceProblemCodec structuredProblemCodec).decode
          cProblem = some problem ∧
      Nonempty (OperationalRealization problem) := by
  have meaningful :=
    (pipeline.cSound syntacticChecker_sound) cProblem cCertificate accepted
  unfold DecodedMeaning at meaningful
  cases structuredDecoded : structuredProblemCodec.decode cProblem with
  | none =>
      simp [composeCodec, structuredDecoded] at meaningful
  | some structuredProblem =>
      cases sourceDecoded : sourceProblemCodec.decode structuredProblem with
      | none =>
          simp [composeCodec, structuredDecoded, sourceDecoded] at meaningful
      | some problem =>
          have decoded :
              (composeCodec sourceProblemCodec structuredProblemCodec).decode
                  cProblem = some problem := by
            simp [composeCodec, structuredDecoded, sourceDecoded]
          have problemMeaning : problem.Meaning := by
            simpa [composeCodec, structuredDecoded, sourceDecoded] using
              meaningful
          exact ⟨problem, decoded,
            OperationalRealization.ofMeaning problemMeaning⟩

/-! ## Discriminating controls and integrated crown -/

namespace Canary

open Mettapedia.TypeTheory.TH0NamedElaborationBridge.Canary

/-- The concrete named identity formula traverses elaboration, two dialect
observations, syntactic replay, and the operational GSLT. -/
theorem named_identity_traverses_the_trinity :
    ∃ formula : ClosedFormula Constant,
      (uniformDialectAdapters .he).decode identityPacket = some formula ∧
      (uniformDialectAdapters .petta).decode identityPacket = some formula ∧
      Nonempty (OperationalRealization (reflexiveProblemOf identityPacket)) :=
  compiled_formula_has_dialect_and_operational_views
    (uniformDialectAdapters .he) (uniformDialectAdapters .petta)
    named_identity_compiles

/-- Finite search can miss an already meaningful TH0 problem and find it at a
later stage; the operational realization depends on replay, not on the stage. -/
theorem finite_miss_then_operational_success :
    ¬ Nonempty
        (TH0SyntacticUnifierService.Canary.producer.EvidenceFor
          TH0SyntacticUnifierService.Canary.baseProblem 0) ∧
      Nonempty
        (OperationalRealization
          TH0SyntacticUnifierService.Canary.baseProblem) := by
  exact ⟨TH0SyntacticUnifierService.Canary.stage_zero_has_no_accepted_unifier,
    eventual_search_has_operational_realization
      HigherOrderAlgorithmProfiles.Canary.syntacticSource
      TH0SyntacticUnifierService.Canary.baseProblem_eventuallyAccepted⟩

/-- Proof relevance is retained below the extensional GSLT observer, while
syntactic substitution remains strictly below beta-eta-aware unification. -/
theorem richness_and_algorithm_boundary :
    ¬ Subsingleton
        (Event TH0SubstitutionOperationalGSLT.Canary.constantSource
          TH0SubstitutionOperationalGSLT.Canary.constantTarget) ∧
      requirements .syntacticSubstitution ⊂
        requirements .betaEtaUnification :=
  ⟨TH0SubstitutionOperationalGSLT.Canary.proof_relevant_fibre_over_thin_step.2,
    syntactic_substitution_strictly_below_betaEta_unification⟩

end Canary

/-! ## Audited theorem crowns -/

#print axioms OperationalRealization.meaning_iff_nonempty
#print axioms admitted_formula_reflexive_check
#print axioms compiled_formula_has_dialect_and_operational_views
#print axioms accepted_search_has_operational_realization
#print axioms eventual_search_has_operational_realization
#print axioms syntacticChecker_sound
#print axioms canonical_native_check_commutes
#print axioms accepted_native_has_operational_realization
#print axioms Canary.named_identity_traverses_the_trinity
#print axioms Canary.finite_miss_then_operational_success
#print axioms Canary.richness_and_algorithm_boundary

end Mettapedia.Logic.HOL.TH0ComputationalTrinity
