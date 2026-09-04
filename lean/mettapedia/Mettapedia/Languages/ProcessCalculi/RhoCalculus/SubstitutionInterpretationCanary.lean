import Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedEquationCompleteness

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
      show applyBindings commBindings rhoCommRewrite.right = syntacticContractum
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
        change applyBindings commBindings rhoCommRewrite.right = declaredContractum at applied
        rw [syntactic_comm_instantiate] at applied
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

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.SubstitutionInterpretationCanary
