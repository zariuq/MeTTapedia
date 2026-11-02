import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategory
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceControls

/-! # Concrete seed multiplicity and physical categorical composition -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategoryControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.OpenApplicationControls (a b c definition)
open PersistentInference PersistentInferenceControls
open _root_.CategoryTheory

def firstContext : PersistentContext definition :=
  ⟨[a], by intro pattern member; obtain rfl := List.mem_singleton.mp member; rfl⟩

def middleContext : PersistentContext definition :=
  ⟨[b], by intro pattern member; obtain rfl := List.mem_singleton.mp member; rfl⟩

def lastContext : PersistentContext definition :=
  ⟨[c], by intro pattern member; obtain rfl := List.mem_singleton.mp member; rfl⟩

def doubledContext : PersistentContext definition :=
  ⟨[a, a], by intro pattern member; simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
              subst pattern; rfl⟩

theorem seed_cardinality {language : ValidatedCalculusLanguageDef} (context : PersistentContext language) :
    context.state.present.card = context.judgments.length := by
  classical
  change (List.ofFn context.row).toFinset.card = _
  rw [List.toFinset_card_of_nodup (List.nodup_ofFn.mpr context.row_injective), List.length_ofFn]

theorem equal_judgments_seed_two_occurrences : doubledContext.state.present.card = 2 :=
  seed_cardinality doubledContext

theorem canonical_equal_rows_have_different_identities :
    doubledContext.row ⟨0, by decide⟩ ≠ doubledContext.row ⟨1, by decide⟩ :=
  doubledContext.occurrence_positions_are_distinct _ _ (by decide)

theorem concrete_identity_has_no_rule_or_request_steps :
    firstContext.identityRepresentative.actors = [] := rfl

noncomputable def firstRun : PersistentContext.Representative firstContext middleContext :=
  compile firstContext.consistent (.cons abProof .nil)

noncomputable def secondRun : PersistentContext.Representative middleContext lastContext :=
  compile middleContext.consistent (.cons bcProof .nil)

noncomputable def firstArrow : firstContext ⟶ middleContext := Quotient.mk _ firstRun
noncomputable def secondArrow : middleContext ⟶ lastContext := Quotient.mk _ secondRun

theorem physical_composite_keeps_the_first_run :
    (PersistentContext.composeRepresentative firstRun secondRun).trace =
      firstRun.trace.append (PersistentContext.continuation firstRun secondRun).trace :=
  PersistentContext.composition_keeps_first_physical_trace firstRun secondRun

theorem categorical_composition_replays_both_original_rules :
    PersistentContext.readout (firstArrow ≫ secondArrow) = cutProof := by
  change PersistentContext.readout (PersistentContext.compose firstArrow secondArrow) = _
  rw [PersistentContext.readout_compose]
  change secondRun.observe.bind firstRun.observe = _
  rw [show firstRun.observe = .cons abProof .nil from compile_observe firstContext.consistent _,
    show secondRun.observe = .cons bcProof .nil from compile_observe middleContext.consistent _]
  rfl

theorem categorical_proof_observation_keeps_two_rule_nodes :
    (PersistentContext.readout (firstArrow ≫ secondArrow)).ruleCount = 2 := by
  rw [categorical_composition_replays_both_original_rules]
  exact cut_keeps_both_primitive_nodes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategoryControls
