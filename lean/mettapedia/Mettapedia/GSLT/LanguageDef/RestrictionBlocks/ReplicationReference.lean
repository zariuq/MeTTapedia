import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationLawShapes
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Coherence
import Mettapedia.OSLF.MeTTaIL.ReferenceStepAgreement

/-!
# The reference relation and the static theory with replication

When no law has premises and every raw law instantiates its other side plainly (`PlainLaws`), the reference
relation's equation steps are the static theory's (`equationStep_iff_of_plain`): a law with binders is read through its
declaration in both relations, and a raw law's other side is instantiated alike.

For a calculus with restriction and replication this holds (`equationStep_iff_replication`): every law has no premise,
and a raw law (ν of inaction and the five laws of replication) binds no name (`raw_notDeeper`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (AuthoredEquation PremisesValid captureSitesOf notDeeper notDeeperList
  applyBindingsScoped_eq_applyBindings_of_notDeeper)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationInstance EquationContextStep readsRaw
  declaredInstanceAt_iff_applyEquationAt)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings applyBindingsScoped captureDepth captureDepthList)

/-! ## Plain laws -/

/-- **Plain laws**: no law has premises, and a raw law instantiates its other side plainly, no metavariable deeper than
where the first side captured it. -/
structure PlainLaws (language : LanguageDef) : Prop where
  premises : ∀ equation ∈ language.equations, equation.premises = []
  aligned : ∀ equation ∈ language.equations, readsRaw equation = true →
    notDeeper (captureSitesOf equation.left equation.premises) 0 equation.right = true ∧
      notDeeper (captureSitesOf equation.right equation.premises) 0 equation.left = true

/-- **An authored instance of the reference relation is an instance of the static theory**, for plain laws. -/
theorem authored_iff_instance_of_plain {language : LanguageDef} (plain : PlainLaws language) (relEnv : RelationEnv)
    (base : BasePremiseEvaluator) {source target : Pattern} :
    AuthoredEquation relEnv language source target ↔ EquationInstance base language source target := by
  constructor
  · intro authored
    cases authored with
    | forward member raw matched premises =>
        have aligned := (plain.aligned _ member raw).1
        rw [plain.premises _ member] at premises
        cases premises
        rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ 0 _ aligned]
        exact ⟨0, .forward member raw matched (by rw [plain.premises _ member]; exact .nil _) rfl⟩
    | reverse member raw matched premises =>
        have aligned := (plain.aligned _ member raw).2
        rw [plain.premises _ member] at premises
        cases premises
        rw [applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ 0 _ aligned]
        exact ⟨0, .reverse member raw matched (by rw [plain.premises _ member]; exact .nil _) rfl⟩
    | declared member notRaw applied =>
        exact ⟨0, .declared member notRaw
          ((declaredInstanceAt_iff_applyEquationAt (plain.premises _ member)).mpr applied)⟩
    | premised member _ premised _ => exact absurd (plain.premises _ member) premised
  · rintro ⟨_, equationInstance⟩
    cases equationInstance with
    | forward member raw matched premises applied =>
        have aligned := (plain.aligned _ member raw).1
        rw [plain.premises _ member] at premises
        cases premises
        rw [← applied, ← applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ 0 _ aligned]
        exact .forward (witnesses := []) member raw matched (by rw [plain.premises _ member]; exact .nil _)
    | reverse member raw matched premises applied =>
        have aligned := (plain.aligned _ member raw).2
        rw [plain.premises _ member] at premises
        cases premises
        rw [← applied, ← applyBindingsScoped_eq_applyBindings_of_notDeeper _ _ 0 _ aligned]
        exact .reverse (witnesses := []) member raw matched (by rw [plain.premises _ member]; exact .nil _)
    | declared member notRaw declared =>
        exact .declared member notRaw ((declaredInstanceAt_iff_applyEquationAt (plain.premises _ member)).mp declared)

/-- **The reference equation steps are the static theory's**, for plain laws. -/
theorem equationStep_iff_of_plain {language : LanguageDef} (plain : PlainLaws language) (relEnv : RelationEnv)
    (base : BasePremiseEvaluator) {first second : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.EquationStep relEnv language first second ↔
      EquationContextStep base language first second := by
  constructor
  · rintro ⟨context, generator⟩
    rcases generator with authored | derived
    · exact .inContext context (.inl ((authored_iff_instance_of_plain plain relEnv base).mp authored))
    · exact .inContext context (.inr derived)
  · rintro ⟨context, generator⟩
    rcases generator with equationInstance | derived
    · exact .inContext context (.inl ((authored_iff_instance_of_plain plain relEnv base).mpr equationInstance))
    · exact .inContext context (.inr derived)

variable {language : LanguageDef} {block : ReplicationBlock} [laws : ReplicationLanguage language block]

include laws in
/-- Every law of a calculus with restriction and replication has no premise. -/
theorem replication_premises_nil {equation : Equation} (member : equation ∈ language.equations) :
    equation.premises = [] := by
  rcases replicationLaws_cases (block := block) member with
    rfl | rfl | rfl | ⟨label, listed, rfl⟩ | rfl | rfl | rfl | rfl | rfl <;> rfl

include laws in
/-- **A raw law instantiates its other side plainly**: no metavariable sits under a binder. -/
theorem raw_notDeeper {equation : Equation} (member : equation ∈ language.equations) (raw : readsRaw equation = true) :
    notDeeper (captureSitesOf equation.left equation.premises) 0 equation.right = true ∧
      notDeeper (captureSitesOf equation.right equation.premises) 0 equation.left = true := by
  rcases replicationLaws_cases (block := block) member with
    rfl | rfl | rfl | ⟨label, listed, rfl⟩ | rfl | rfl | rfl | rfl | rfl
  · constructor <;> simp [restrictionNilOf, notDeeper, notDeeperList]
  · exact absurd raw (by rw [exchange_raw]; decide)
  · exact absurd raw (by rw [extrusion_raw]; decide)
  · exact absurd raw (by rw [emptyUnit_raw]; decide)
  all_goals
    constructor <;>
      simp [replicationUnfoldOf, replicationNilOf, replicationTwiceOf, replicationParOf, replicationIdempotentOf,
        notDeeper, notDeeperList, captureSitesOf, captureDepth, captureDepthList]

include laws in
/-- **The laws of a calculus with restriction and replication are plain.** -/
theorem replication_plain : PlainLaws language :=
  ⟨fun _ member => replication_premises_nil (block := block) member,
    fun _ member raw => raw_notDeeper (block := block) member raw⟩

include laws in
/-- **The reference equation steps are the static theory's**, in a calculus with restriction and replication. -/
theorem equationStep_iff_replication (relEnv : RelationEnv) (base : BasePremiseEvaluator) {first second : Pattern} :
    Mettapedia.OSLF.MeTTaIL.ReferenceStep.EquationStep relEnv language first second ↔
      EquationContextStep base language first second :=
  equationStep_iff_of_plain (replication_plain (block := block)) relEnv base

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
