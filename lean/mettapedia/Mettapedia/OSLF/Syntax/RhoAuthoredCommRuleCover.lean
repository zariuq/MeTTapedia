import Mettapedia.OSLF.Syntax.RhoEquationRuleModels
import Mettapedia.OSLF.Syntax.RhoCommunicationEncoding
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

/-!
# The intrinsic communication generator and authored rho COMM rule

Every closed-context channel, payload, and one-name continuation determines
an intrinsic binary COMM constructor and an actual authored COMM firing. The
encoded source and canonical input-first hash bag are structurally congruent.
Under the exact quote-safety hypotheses, the authored source and result inhabit
the closed rho carrier. The intrinsic constructor survives the source equation
quotient. Immediate reduct equality is not asserted: authored semantic
substitution can contract quoted Drops that intrinsic substitution retains.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
open Mettapedia.OSLF.Binding.RhoRulePolynomialMorphism
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem

private abbrev raw := BindingCloneAlgebra.terms sig

def intrinsicSource (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) : Term sig [] Srt.pr :=
  commSource raw channel payload body

def authoredInputFirst (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) : Pattern :=
  .collection .hashBag
    [.apply "PInput" [encodeTerm channel, .lambda none (encodeTerm body)],
     .apply "POutput" [encodeTerm channel, encodeTerm payload]] none

def authoredResult (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) : Pattern :=
  .collection .hashBag
    [semanticCommSubst (encodeTerm body) (encodeTerm payload)] none

theorem source_encoded (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    encodeTerm (intrinsicSource channel payload body) =
      .collection .hashBag
        [.apply "POutput" [encodeTerm channel, encodeTerm payload],
         .apply "PInput" [encodeTerm channel, .lambda none (encodeTerm body)]] none :=
  rfl

theorem source_structurally_congruent (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    StructuralCongruence
      (encodeTerm (intrinsicSource channel payload body))
      (authoredInputFirst channel payload body) := by
  rw [source_encoded]
  exact StructuralCongruence.par_comm _ _

theorem authored_comm_all (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    RhoStep (authoredInputFirst channel payload body)
      (authoredResult payload body) := by
  change RhoStep
    (.collection .hashBag
      ([.apply "PInput" [encodeTerm channel, .lambda none (encodeTerm body)],
        .apply "POutput" [encodeTerm channel, encodeTerm payload]] ++ []) none)
    (.collection .hashBag
      (semanticCommSubst (encodeTerm body) (encodeTerm payload) :: []) none)
  apply RhoStep.comm (free := FreeSortContext.empty) (bound := [])
  · simpa [EncodedTermTyped, contextLabels, sortLabel,
      rhoReflectivePresentation] using encodedTerm_typed body
  · simpa [EncodedTermTyped, contextLabels] using encodedTerm_typed payload

/-- The intrinsic schema has one occurrence for every closed channel,
payload and one-name continuation; the input binder is retained in the
judgment index of that occurrence. -/
def intrinsicCommTree (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    (rules raw).Fix ()
      (judgment raw (intrinsicSource channel payload body)
        (commTarget raw payload body)) :=
  .roll (RuleShape.comm (A := raw) (Γ := []) channel payload body)
    (fun impossible => impossible.elim)

private noncomputable abbrev sourceAlgebra :=
  (FreeBindingEquationModel.presented rhoSourceE).algebra

/-- The same constructor survives the full intrinsic source equation model,
including its rule occurrence rather than merely its endpoint relation. -/
noncomputable def sourceEquationCommTree (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    (rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw (intrinsicSource channel payload body)
          (commTarget raw payload body))) :=
  interpretTree (FreeBindingClone.interpretHom sourceAlgebra) _
    (intrinsicCommTree channel payload body)

/-- Every closed intrinsic COMM generator has a source-congruent authored
COMM step and a retained generator in the source equation model. The
immediate targets are intentionally not identified here: authored semantic
substitution may contract a quoted Drop that intrinsic substitution retains. -/
theorem comm_source_and_rule_cover (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    StructuralCongruence
      (encodeTerm (intrinsicSource channel payload body))
      (authoredInputFirst channel payload body) ∧
    RhoStep (authoredInputFirst channel payload body)
      (authoredResult payload body) ∧
    Nonempty ((rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw (intrinsicSource channel payload body)
          (commTarget raw payload body)))) :=
  ⟨source_structurally_congruent channel payload body,
   authored_comm_all channel payload body,
   ⟨sourceEquationCommTree channel payload body⟩⟩

theorem encoded_comm_source_admitted_of_safe
    (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (intrinsicSource channel payload body)) := by
  rw [encoded_process_admitted_iff_quoteSafe]
  have expanded : intrinsicSource channel payload body =
      Term.op Op.par
        (.cons (Term.op Op.out (.cons channel (.cons payload .nil)))
          (.cons (Term.op Op.inp (.cons channel (.cons body .nil))) .nil)) := rfl
  rw [expanded]
  simp [intrinsicQuoteSafe, intrinsicQuoteSafeArgs,
    channelSafe, payloadSafe, bodySafe]

theorem authored_comm_source_admitted_of_safe
    (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (authoredInputFirst channel payload body) := by
  apply (rhoClosedTermWellSorted_process_iff _).mpr
  constructor
  · exact .parallel
      (.cons
        (.input
          (show NameWellSorted rhoReflectivePresentation
            FreeSortContext.empty [] (encodeTerm channel) from
              encodedTerm_typed channel)
          (show ProcWellSorted rhoReflectivePresentation
            FreeSortContext.empty [rhoReflectivePresentation.nameSort]
            (encodeTerm body) from by
              simpa [EncodedTermTyped, contextLabels, sortLabel,
                rhoReflectivePresentation] using encodedTerm_typed body))
        (.cons
          (.output (encodedTerm_typed channel) (encodedTerm_typed payload))
          .nil))
  · simp [authoredInputFirst, binderSafeAt, binderSafeListAt,
      encodeTerm_quoteSafe, channelSafe, payloadSafe, bodySafe]

theorem authored_comm_result_admitted_of_safe
    (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (authoredResult payload body) := by
  have sourceAdmitted := authored_comm_source_admitted_of_safe
    channel payload body channelSafe payloadSafe bodySafe
  have sourceParts := (rhoClosedTermWellSorted_process_iff _).mp sourceAdmitted
  exact (rhoClosedTermWellSorted_process_iff _).mpr
    (rhoStep_preserves_closed sourceParts.1 sourceParts.2
      (authored_comm_all channel payload body))

theorem comm_closed_source_and_rule_cover
    (channel : Term sig [] Srt.nm)
    (payload : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (encodeTerm (intrinsicSource channel payload body)) ∧
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (authoredInputFirst channel payload body) ∧
    RhoClosedTermWellSorted
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      (authoredResult payload body) ∧
    StructuralCongruence
      (encodeTerm (intrinsicSource channel payload body))
      (authoredInputFirst channel payload body) ∧
    RhoStep (authoredInputFirst channel payload body)
      (authoredResult payload body) ∧
    Nonempty ((rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw (intrinsicSource channel payload body)
          (commTarget raw payload body)))) := by
  have cover := comm_source_and_rule_cover channel payload body
  exact ⟨encoded_comm_source_admitted_of_safe channel payload body
      channelSafe payloadSafe bodySafe,
    authored_comm_source_admitted_of_safe channel payload body
      channelSafe payloadSafe bodySafe,
    authored_comm_result_admitted_of_safe channel payload body
      channelSafe payloadSafe bodySafe,
    cover.1, cover.2.1, cover.2.2⟩

/-- The open-name continuation rules out an unqualified structural
identification of all immediate authored and intrinsic COMM reducts. The
existing residual-equivalence theorem is the justified weaker comparison. -/
theorem no_unqualified_comm_target_structural_comparison :
    ¬ ∀ (payload : Term sig [] Srt.pr)
        (body : Term sig [Srt.nm] Srt.pr),
      StructuralCongruence
        (authoredResult payload body)
        (encodeTerm (commTarget raw payload body)) := by
  intro all
  let body : Term sig [Srt.nm] Srt.pr :=
    Term.op Op.drp (.cons (.var .zero) .nil)
  have bad := all nilP body
  have targetEq : commTarget raw nilP body = RhoSchema.commTarget := by
    rfl
  have sourceEq : authoredResult nilP body = authoredCommReduct := by
    rfl
  have h : StructuralCongruence authoredCommReduct
      (encodeTerm commTarget) := by
    rw [targetEq, sourceEq] at bad
    exact bad
  exact notStructurallyCongruent (StructuralCongruence.symm _ _ h)

/-- The obstruction persists inside the quote-safe input domain. It is not
caused by admitting an intrinsically ill-scoped communication source. -/
theorem no_quoteSafe_comm_target_structural_comparison :
    ¬ ∀ (payload : Term sig [] Srt.pr)
        (body : Term sig [Srt.nm] Srt.pr),
      intrinsicQuoteSafe 0 payload = true →
      intrinsicQuoteSafe 1 body = true →
      StructuralCongruence
        (authoredResult payload body)
        (encodeTerm (commTarget raw payload body)) := by
  intro all
  let body : Term sig [Srt.nm] Srt.pr :=
    Term.op Op.drp (.cons (.var .zero) .nil)
  have bad := all nilP body (by decide +kernel) (by decide +kernel)
  have targetEq : commTarget raw nilP body = RhoSchema.commTarget := by
    rfl
  have sourceEq : authoredResult nilP body = authoredCommReduct := by
    rfl
  have h : StructuralCongruence authoredCommReduct
      (encodeTerm commTarget) := by
    rw [targetEq, sourceEq] at bad
    exact bad
  exact notStructurallyCongruent (StructuralCongruence.symm _ _ h)

#print axioms source_structurally_congruent
#print axioms authored_comm_all
#print axioms sourceEquationCommTree
#print axioms comm_source_and_rule_cover
#print axioms encoded_comm_source_admitted_of_safe
#print axioms authored_comm_source_admitted_of_safe
#print axioms authored_comm_result_admitted_of_safe
#print axioms comm_closed_source_and_rule_cover
#print axioms no_unqualified_comm_target_structural_comparison
#print axioms no_quoteSafe_comm_target_structural_comparison

end Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover
