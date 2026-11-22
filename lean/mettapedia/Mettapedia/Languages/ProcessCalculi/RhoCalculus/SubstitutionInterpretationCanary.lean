import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopedSemanticSubstitution

/-!
# The substitution interpretation is not an equation

The rho presentation authors the `Comm` contractum as an explicit substitution
node.  Two interpretations of that node are in play:

* the syntactic interpretation, used by the language-generated GSLT of the
  five-field core, instantiates the binder structurally, so a receiver that
  drops the received name is left with the drop of a quotation; and
* the declared reflective interpretation, selected by rho's reflection
  profile, exposes the payload at a matched drop, which is the paper's
  semantic substitution.

Both interpretations match the same redex with the same bindings.  Their
contracta differ, and the difference is not an equation: the two contracta
have distinct canonical forms, so no presentation-derived or authored law
identifies them.  This module records that fact on one closed source, at the
primitive step level of each interpretation.  Consequently the step relation of
a language-generated GSLT is fixed only once the substitution interpretation is
declared; for rho the declared one is the reflective profile, and the generic
construction at that interpretation is the one the agreement module compares
with the established semantics.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionInterpretationCanary

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness

set_option autoImplicit false

/-! ## The closed source and its two contracta -/

/-- A receiver on the quoted nil channel that drops the name it receives. -/
def receiver : Pattern :=
  .apply "PInput"
    [.apply "NQuote" [.apply "PZero" []], .lambda none (.apply "PDrop" [.bvar 0])]

/-- A sender of nil on the quoted nil channel. -/
def sender : Pattern :=
  .apply "POutput" [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]

/-- The closed synchronization source. -/
def dropReceiverSource : Pattern := .collection .hashBag [receiver, sender] none

/-- The contractum under structural instantiation: the drop of the received
quotation remains. -/
def syntacticContractum : Pattern :=
  .collection .hashBag [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]] none

/-- The contractum under the declared reflective substitution: the payload. -/
def declaredContractum : Pattern := .collection .hashBag [.apply "PZero" []] none

theorem dropReceiverSource_closed :
    RhoClosedTermWellSorted rhoProc dropReceiverSource :=
  (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.parallel (.cons (.input (.quote .unit) (.drop (.bvar rfl)))
      (.cons (.output (.quote .unit) .unit) .nil)), by decide⟩

theorem syntacticContractum_closed :
    RhoClosedTermWellSorted rhoProc syntacticContractum :=
  (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.parallel (.cons (.drop (.quote .unit)) .nil), by decide⟩

theorem declaredContractum_closed :
    RhoClosedTermWellSorted rhoProc declaredContractum :=
  (rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.parallel (.cons .unit .nil), by decide⟩

/-! ## Matcher facts, decided by the kernel -/

private theorem rhoCalc_rewrites :
    rhoCalc.rewrites = [rhoCommRewrite, rhoParCongRewrite] := rfl

/-- The one binding produced for `Comm` on the source by both interpretations. -/
def commBindings : Bindings :=
  [("q", .apply "PZero" []), ("rest", .collection .hashBag [] none),
   ("p", .apply "PDrop" [.bvar 0]), ("n", .apply "NQuote" [.apply "PZero" []])]

/-- The `ParCong` binding selecting the receiver. -/
def parCongReceiverBindings : Bindings :=
  [("rest", .collection .hashBag [sender] none), ("S", receiver)]

/-- The `ParCong` binding selecting the sender. -/
def parCongSenderBindings : Bindings :=
  [("rest", .collection .hashBag [receiver] none), ("S", sender)]

theorem declared_comm_match :
    matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite dropReceiverSource =
      [commBindings] := by
  decide +kernel

theorem declared_comm_instantiate :
    applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite commBindings =
      declaredContractum := by
  decide +kernel

theorem declared_parCong_match :
    matchPatternForRuleUsing rhoReflectionProfile rhoParCongRewrite dropReceiverSource =
      [parCongReceiverBindings, parCongSenderBindings] := by
  decide +kernel

theorem declared_comm_no_match_receiver :
    matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite receiver = [] := by
  decide +kernel

theorem declared_parCong_no_match_receiver :
    matchPatternForRuleUsing rhoReflectionProfile rhoParCongRewrite receiver = [] := by
  decide +kernel

theorem declared_comm_no_match_sender :
    matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite sender = [] := by
  decide +kernel

theorem declared_parCong_no_match_sender :
    matchPatternForRuleUsing rhoReflectionProfile rhoParCongRewrite sender = [] := by
  decide +kernel

theorem syntactic_comm_match :
    matchPattern rhoCommRewrite.left dropReceiverSource = [commBindings] := by
  decide +kernel

theorem syntactic_comm_instantiate :
    applyBindings commBindings rhoCommRewrite.right = syntacticContractum := by
  decide +kernel

theorem syntactic_parCong_match :
    matchPattern rhoParCongRewrite.left dropReceiverSource =
      [parCongReceiverBindings, parCongSenderBindings] := by
  decide +kernel

theorem syntactic_comm_no_match_receiver :
    matchPattern rhoCommRewrite.left receiver = [] := by
  decide +kernel

theorem syntactic_parCong_no_match_receiver :
    matchPattern rhoParCongRewrite.left receiver = [] := by
  decide +kernel

theorem syntactic_comm_no_match_sender :
    matchPattern rhoCommRewrite.left sender = [] := by
  decide +kernel

theorem syntactic_parCong_no_match_sender :
    matchPattern rhoParCongRewrite.left sender = [] := by
  decide +kernel

/-! ## The components are inert under both interpretations -/

theorem receiver_declared_rewriteAt_nil (fuel : Nat) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt rhoRuleInterpretation
      rhoBasePremises rhoCalc fuel receiver = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt, rhoCalc_rewrites]
      simp [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
        rhoRuleInterpretation, declared_comm_no_match_receiver,
        declared_parCong_no_match_receiver]

theorem sender_declared_rewriteAt_nil (fuel : Nat) :
    Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt rhoRuleInterpretation
      rhoBasePremises rhoCalc fuel sender = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.rewriteAt, rhoCalc_rewrites]
      simp [Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
        rhoRuleInterpretation, declared_comm_no_match_sender,
        declared_parCong_no_match_sender]

theorem receiver_syntactic_rewriteAt_nil (fuel : Nat) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt defaultBasePremises rhoCalc fuel
      receiver = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt, rhoCalc_rewrites]
      simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.applyRuleUsing,
        syntactic_comm_no_match_receiver, syntactic_parCong_no_match_receiver]

theorem sender_syntactic_rewriteAt_nil (fuel : Nat) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt defaultBasePremises rhoCalc fuel
      sender = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rw [Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt, rhoCalc_rewrites]
      simp [Mettapedia.OSLF.MeTTaIL.ContextualStep.applyRuleUsing,
        syntactic_comm_no_match_sender, syntactic_parCong_no_match_sender]

/-! ## Positive controls: each interpretation fires on the source -/

/-- The syntactic primitive step reaches the inert drop. -/
theorem syntactic_step :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step defaultBasePremises rhoCalc
      dropReceiverSource syntacticContractum :=
  ⟨1, .rule (initialBindings := commBindings) (finalBindings := commBindings)
    (List.Mem.head _)
    (by
      show commBindings ∈ matchPattern rhoCommRewrite.left dropReceiverSource
      rw [syntactic_comm_match]
      exact List.Mem.head _)
    (.nil commBindings)
    (by
      rw [applyBindingsForRule_eq_syntactic,
        applyRuleBindings_eq_applyBindings rhoCommRewrite _ (by decide)]
      exact syntactic_comm_instantiate)⟩

/-- The declared primitive step reaches the payload. -/
theorem declared_step : RhoStep dropReceiverSource declaredContractum := by
  have step := RhoStep.comm (free := FreeSortContext.empty) (bound := [])
    (.apply "NQuote" [.apply "PZero" []]) (.apply "PDrop" [.bvar 0]) (.apply "PZero" []) []
    (.drop (.bvar rfl)) .unit
  have normalized : semanticNormalizeProc (.apply "PZero" []) = .apply "PZero" [] := by
    simp [semanticNormalizeProc]
  rw [semanticCommSubst_collapses_bound_drop, normalized] at step
  exact step

/-! ## Negative controls: neither interpretation reaches the other's contractum -/

/-- The declared step never produces the inert drop. -/
theorem declared_step_not_syntacticContractum :
    ¬ RhoStep dropReceiverSource syntacticContractum := by
  rintro ⟨fuel, step⟩
  cases step with
  | rule membership matched premises applied =>
      rw [rhoCalc_rewrites] at membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · change _ ∈ matchPatternForRuleUsing rhoReflectionProfile rhoCommRewrite
          dropReceiverSource at matched
        rw [declared_comm_match, List.mem_singleton] at matched
        subst matched
        change Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.PremisesAt _ _ _ _ _ [] _
          at premises
        cases premises
        change applyBindingsForRuleUsing rhoReflectionProfile rhoCommRewrite commBindings =
          syntacticContractum at applied
        rw [declared_comm_instantiate] at applied
        exact absurd applied (by decide)
      · change _ ∈ matchPatternForRuleUsing rhoReflectionProfile rhoParCongRewrite
          dropReceiverSource at matched
        rw [declared_parCong_match] at matched
        change Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.PremisesAt _ _ _ _ _
          [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons first _ =>
            cases first with
            | congruence componentStep _ _ =>
                have member :=
                  Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.mem_rewriteAt_iff_stepAt.mpr
                    componentStep
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                  at matched
                rcases matched with rfl | rfl
                · rw [show applyBindings parCongReceiverBindings (.fvar "S") = receiver by
                      decide +kernel, receiver_declared_rewriteAt_nil] at member
                  exact List.not_mem_nil member
                · rw [show applyBindings parCongSenderBindings (.fvar "S") = sender by
                      decide +kernel, sender_declared_rewriteAt_nil] at member
                  exact List.not_mem_nil member

/-- The syntactic step never produces the payload. -/
theorem syntactic_step_not_declaredContractum :
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step defaultBasePremises rhoCalc
      dropReceiverSource declaredContractum := by
  rintro ⟨fuel, step⟩
  cases step with
  | rule membership matched premises applied =>
      rw [rhoCalc_rewrites] at membership
      simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl
      · change _ ∈ matchPattern rhoCommRewrite.left dropReceiverSource at matched
        rw [syntactic_comm_match, List.mem_singleton] at matched
        subst matched
        change Mettapedia.OSLF.MeTTaIL.ContextualStep.PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [applyBindingsForRule_eq_syntactic,
          applyRuleBindings_eq_applyBindings rhoCommRewrite _ (by decide),
          syntactic_comm_instantiate] at applied
        exact absurd applied (by decide)
      · change _ ∈ matchPattern rhoParCongRewrite.left dropReceiverSource at matched
        rw [syntactic_parCong_match] at matched
        change Mettapedia.OSLF.MeTTaIL.ContextualStep.PremisesAt _ _ _ _
          [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons first _ =>
            cases first with
            | congruence componentStep _ _ =>
                have member :=
                  Mettapedia.OSLF.MeTTaIL.ContextualStep.mem_rewriteAt_iff_stepAt.mpr
                    componentStep
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                  at matched
                rcases matched with rfl | rfl
                · rw [show applyBindings parCongReceiverBindings (.fvar "S") = receiver by
                      decide +kernel, receiver_syntactic_rewriteAt_nil] at member
                  exact List.not_mem_nil member
                · rw [show applyBindings parCongSenderBindings (.fvar "S") = sender by
                      decide +kernel, sender_syntactic_rewriteAt_nil] at member
                  exact List.not_mem_nil member

/-! ## The two contracta are not equated by any law -/

/-- No authored or presentation-derived equation identifies the inert drop
with the payload: their canonical forms differ. -/
theorem contracta_inequivalent :
    ¬ CoreEquiv defaultBasePremises syntacticContractum declaredContractum := by
  rw [coreEquiv_iff_canonicalize_eq syntacticContractum_closed declaredContractum_closed]
  decide +kernel

/-! ## Transport to the two GSLTs -/

/-- The syntactic language-generated GSLT steps to the inert drop. -/
theorem langGSLT_step_syntacticContractum :
    (langGSLT rhoCalc).Step dropReceiverSource syntacticContractum :=
  ⟨dropReceiverSource, syntacticContractum, Relation.EqvGen.refl _, syntactic_step,
    Relation.EqvGen.refl _⟩

/-- The established rho GSLT steps to the payload. -/
theorem rhoLanguageDefGSLT_step_declaredContractum :
    rhoLanguageDefGSLT.Step ⟨dropReceiverSource, dropReceiverSource_closed⟩
      ⟨declaredContractum, declaredContractum_closed⟩ :=
  ⟨⟨dropReceiverSource, dropReceiverSource_closed⟩,
    ⟨declaredContractum, declaredContractum_closed⟩, rfl, declared_step, rfl⟩

/-- Summary: on one closed source the two primitive step relations disagree,
each reaching a contractum the other cannot, and the contracta are
inequivalent under every generated equation. -/
theorem primitive_steps_differ :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step defaultBasePremises rhoCalc
        dropReceiverSource syntacticContractum ∧
      ¬ RhoStep dropReceiverSource syntacticContractum ∧
      RhoStep dropReceiverSource declaredContractum ∧
      ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step defaultBasePremises rhoCalc
        dropReceiverSource declaredContractum ∧
      ¬ CoreEquiv defaultBasePremises syntacticContractum declaredContractum :=
  ⟨syntactic_step, declared_step_not_syntacticContractum, declared_step,
    syntactic_step_not_declaredContractum, contracta_inequivalent⟩

/-! ## Opening must retain the authored drop position -/

namespace Opening
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern rhoReflectivePresentation)
open Mettapedia.OSLF.MeTTaIL.Substitution (openBVar)
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.Languages.ProcessCalculi.RhoCalculus

def zero : Pattern := .apply "PZero" []
def quote (process : Pattern) : Pattern := .apply "NQuote" [process]
def drop (name : Pattern) : Pattern := .apply "PDrop" [name]
def receivedDrop : Pattern := drop (.bvar 0)
def literalDrop : Pattern := drop (quote zero)

theorem received_body_well_sorted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"] receivedDrop :=
  .drop (.bvar rfl)

theorem literal_body_well_sorted :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"] literalDrop :=
  .drop (.quote .unit)

theorem bodies_quote_safe : binderSafeAt "NQuote" 1 receivedDrop = true ∧
    binderSafeAt "NQuote" 1 literalDrop = true := by decide

theorem ordinary_opening_forgets_drop_origin :
    openBVar 0 (quote zero) receivedDrop = openBVar 0 (quote zero) literalDrop := by
  simp [openBVar, receivedDrop, literalDrop, drop, quote, zero]

theorem semantic_opening_retains_drop_origin :
    semanticCommSubst receivedDrop zero = zero ∧
      semanticCommSubst literalDrop zero = literalDrop := by
  constructor <;> rfl

theorem literal_drop_is_not_a_process_equation : ¬ StructuralCongruence zero literalDrop := by
  intro equivalent
  have same := Canonical.canonicalize_eq_of_structuralCongruence equivalent
    (by simp [Canonical.HashSetFree, Canonical.HashSetFreeList, zero])
    (by simp [Canonical.HashSetFree, Canonical.HashSetFreeList, literalDrop, drop, quote, zero])
  exact (show Canonical.canonicalize zero ≠ Canonical.canonicalize literalDrop from by decide) same

/-- No function of the ordinary opened term alone reconstructs semantic COMM,
even with nil payload and well-sorted quotation-safe receiver bodies. -/
theorem no_postprocessing_of_ordinary_opening :
    ¬ ∃ finish : Pattern → Pattern, ∀ body : Pattern,
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"] body →
      binderSafeAt "NQuote" 1 body = true →
      finish (openBVar 0 (quote zero) body) = semanticCommSubst body zero := by
  rintro ⟨finish, implements⟩
  have first := implements receivedDrop received_body_well_sorted bodies_quote_safe.1
  have second := implements literalDrop literal_body_well_sorted bodies_quote_safe.2
  rw [ordinary_opening_forgets_drop_origin] at first
  have impossible : zero = literalDrop :=
    semantic_opening_retains_drop_origin.1.symm.trans
      (first.symm.trans (second.trans semantic_opening_retains_drop_origin.2))
  exact (show zero ≠ literalDrop from by decide) impossible

/-- The same obstruction remains when the proposed reconstruction is allowed
to return any structurally congruent representative. -/
theorem no_postprocessing_modulo_process_equations :
    ¬ ∃ finish : Pattern → Pattern, ∀ body : Pattern,
      ProcWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"] body →
      binderSafeAt "NQuote" 1 body = true →
      StructuralCongruence (finish (openBVar 0 (quote zero) body)) (semanticCommSubst body zero) := by
  rintro ⟨finish, implements⟩
  have first := implements receivedDrop received_body_well_sorted bodies_quote_safe.1
  have second := implements literalDrop literal_body_well_sorted bodies_quote_safe.2
  rw [ordinary_opening_forgets_drop_origin, semantic_opening_retains_drop_origin.1] at first
  rw [semantic_opening_retains_drop_origin.2] at second
  exact literal_drop_is_not_a_process_equation (StructuralCongruence.trans _ _ _
    (StructuralCongruence.symm _ _ first) second)

def redundantChannel : Pattern := .apply "POutput" [quote (drop (quote zero)), zero]
def normalizedChannel : Pattern := .apply "POutput" [quote zero, zero]

theorem redundant_channel_is_closed_process :
    ProcWellSorted rhoReflectivePresentation FreeSortContext.empty [] redundantChannel ∧
      binderSafeAt "NQuote" 0 redundantChannel = true :=
  ⟨.output (.quote (.drop (.quote .unit))) .unit, by decide⟩

theorem every_raw_single_substitution_changes_this_process (index : Nat) (replacement : Pattern) :
    semanticSubstProc index replacement redundantChannel = normalizedChannel := rfl

theorem raw_single_substitutions_have_no_identity :
    ¬ ∃ index replacement, ∀ process,
      semanticSubstProc index replacement process = process := by
  rintro ⟨index, replacement, identity⟩
  have impossible := (every_raw_single_substitution_changes_this_process index replacement).symm.trans
    (identity redundantChannel)
  exact (show normalizedChannel ≠ redundantChannel from by decide) impossible


theorem this_identity_obstruction_is_only_representational :
    StructuralCongruence redundantChannel normalizedChannel := by
  apply Canonical.structuralCongruence_of_canonicalize_eq
  decide

def quotedBoundDrop : Pattern := quote (drop (.bvar 0))

theorem name_equation_has_two_well_sorted_names :
    NameWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"] quotedBoundDrop ∧
      NameWellSorted rhoReflectivePresentation FreeSortContext.empty ["Name"] (.bvar 0) ∧
      NameEquiv quotedBoundDrop (.bvar 0) :=
  ⟨.quote (.drop (.bvar rfl)), .bvar rfl, .quote_drop _⟩

theorem name_substitution_respects_this_name_equation :
    semanticSubstName 0 (quote zero) quotedBoundDrop = semanticSubstName 0 (quote zero) (.bvar 0) := rfl

/-- Applying the process operation to a name is not a sort-independent action. -/
theorem process_substitution_does_not_preserve_this_name_equation :
    ¬ StructuralCongruence (semanticSubstProc 0 (quote zero) quotedBoundDrop)
      (semanticSubstProc 0 (quote zero) (.bvar 0)) := by
  intro related
  have same := Canonical.canonicalize_eq_of_structuralCongruence related
    (by simp [semanticSubstProc, quotedBoundDrop, quote, drop,
      Canonical.HashSetFree, Canonical.HashSetFreeList])
    (by simp [semanticSubstProc, zero, quote, Canonical.HashSetFree, Canonical.HashSetFreeList])
  exact (show Canonical.canonicalize (semanticSubstProc 0 (quote zero) quotedBoundDrop) ≠
    Canonical.canonicalize (semanticSubstProc 0 (quote zero) (.bvar 0)) from by decide) same

theorem this_name_equation_crosses_the_quote_scope_boundary :
    binderSafeAt "NQuote" 1 quotedBoundDrop = false ∧
      binderSafeAt "NQuote" 1 (.bvar 0) = true := by decide


theorem residual_equivalence_is_not_structural_congruence :
    ProcResidualEquiv literalDrop zero ∧ ¬ StructuralCongruence literalDrop zero := by
  refine ⟨.unquote zero, fun related => ?_⟩
  exact literal_drop_is_not_a_process_equation (StructuralCongruence.symm _ _ related)

#print axioms received_body_well_sorted
#print axioms bodies_quote_safe
#print axioms no_postprocessing_of_ordinary_opening
#print axioms no_postprocessing_modulo_process_equations
#print axioms this_identity_obstruction_is_only_representational
#print axioms name_substitution_respects_this_name_equation
#print axioms residual_equivalence_is_not_structural_congruence

theorem literal_drop_has_no_reduction (target : Pattern) :
    ¬ Nonempty (Reduction.Reduces literalDrop target) :=
  Reduction.no_reduction_of_ioCount_zero
    (by simp [Reduction.ioCount, literalDrop, drop, quote, zero])

/-- The body is inspected before opening; the received drop activates but a
literal suspended drop does not. -/
def actual_communication_activates_the_received_drop :
    Reduction.Reduces
      (.collection .hashBag
        [.apply "POutput" [quote zero, zero],
         .apply "PInput" [quote zero, .lambda none receivedDrop]] none)
      (.collection .hashBag [zero] none) := .comm

#print axioms literal_drop_has_no_reduction
#print axioms actual_communication_activates_the_received_drop

end Opening

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionInterpretationCanary
