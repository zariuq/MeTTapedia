import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationExecution
import Mettapedia.GSLT.Parsing.LanguageDefScalarSyntax
import Mettapedia.GSLT.Parsing.ClassAwarePackedForestSaturation

/-! # The authored transform boundary through the scalar parser and packed forest

The structural rows are compiled from `tcalc.module`. A named lexical profile
supplies the scalar interpretation of its parameter sorts. The original-row
source judgment, compiled parser entry and independently replayed packed
forest agree on whole-input CST observations. Global saturation is one sufficient
completeness certificate; replay alone supplies soundness. This strong global
criterion is not asserted of root-pruned native GLL/GLR forests.

No ambiguity policy acts during compilation or replay. A policy is a separate
predicate on complete CSTs. These results concern the authored event boundary;
internal payload syntax and binding-aware interpretation are further layers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Parser

open Mettapedia.GSLT.Parsing
open LanguageDefSyntaxCompiler ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwarePackedForest ClassAwareParserPackCertificate

def binding : Binding where
  literalRef token := some token
  lexicalSortRef _ := none
  categoryRef := id
  ruleRef := id

def rules : List CompiledRule :=
  (compileRules? binding language).get (by decide +kernel)

theorem rules_compiled : compileRules? binding language = some rules := by decide +kernel

def literalScalars (token : String) : Option (List Nat) := some (token.toList.map Char.toNat)

def plan (profile : ParserProfileLayer) : CompiledParserPackPlan :=
  { lexical := compileLexicalPack profile
    structural := (compileStructuralProductions? literalScalars profile.startSort rules).get
      (by rfl) }

theorem plan_compiled (profile : ParserProfileLayer) :
    compileParserPackPlan? literalScalars profile rules = some (plan profile) := rfl

theorem plan_agreement (profile : ParserProfileLayer) :
    ParserPackPlanAgreement literalScalars profile rules (plan profile) :=
  ParserPackPlanAgreement.of_compilation (plan_compiled profile)

/-- Direct codepoint parsing of the original authored rows and lexical profile. -/
abbrev Source (profile : ParserProfileLayer) (input : List Nat) (tree : CST) :=
  LanguageDefScalarSyntax.DerivesAt literalScalars profile language input
    profile.startSort 0 input.length tree

/-- The target's distinct administrative entry enforces whole-input consumption. -/
abbrev Entry (profile : ParserProfileLayer) (input : List Nat) (tree : CST) :=
  ParserPackEntryDerivesAt profile (plan profile) input
    (plan profile).entryProduction.resultState input.length tree

theorem source_iff_entry (profile : ParserProfileLayer) (input : List Nat) (tree : CST) :
    Nonempty (Source profile input tree) ↔ Nonempty (Entry profile input tree) := by
  exact (LanguageDefScalarSyntax.source_plan_iff rules_compiled).trans
    (sourcePlanEntryDerivationEquiv (plan_agreement profile) tree).nonempty_congr

theorem source_iff_parser (profile : ParserProfileLayer) (input : List Nat) (tree : CST) :
    Nonempty (Source profile input tree) ↔
      Nonempty (ParserPackRootDerives profile (plan profile) input tree) := by
  exact (LanguageDefScalarSyntax.source_plan_iff rules_compiled).trans
    (sourcePlanRootDerivationEquiv (plan_agreement profile) tree).nonempty_congr

/-- An arbitrary backend may propose a forest. Every accepted tree still
replays against the generated plan, including lexical and structural evidence. -/
abbrev Packed (forest : Forest) (profile : ParserProfileLayer) (input : List Nat) (tree : CST) :=
  PackedFibre forest profile (plan profile) input profile.startSort 0 input.length tree

theorem packed_reflects (forest : Forest) (profile : ParserProfileLayer)
    (input : List Nat) (tree : CST) :
    Nonempty (Packed forest profile input tree) → Nonempty (Source profile input tree) := by
  rintro ⟨certificate, replay⟩
  exact (source_iff_parser profile input tree).mpr ⟨replay.derivation⟩

theorem checked_forest_iff_source (forest : Forest) (profile : ParserProfileLayer)
    (input : List Nat)
    (checked : ClassAwarePackedForestSaturation.validateRuleSaturation
      forest profile (plan profile) input = true) (tree : CST) :
    Nonempty (Packed forest profile input tree) ↔ Nonempty (Source profile input tree) := by
  refine ⟨packed_reflects forest profile input tree, ?_⟩
  intro source
  obtain ⟨derived⟩ := (source_iff_parser profile input tree).mp source
  have complete := ClassAwarePackedForestSaturation.validateRuleSaturation_root_complete checked tree
  exact ⟨Certificate.ofDerivation derived, ⟨complete derived⟩,
    ClassAwareParserPackCertificate.Replays.ofDerivation derived⟩

/-- A checked complete forest keeps both parses, before any policy acts. -/
theorem ambiguity_retained (forest : Forest) (profile : ParserProfileLayer) (input : List Nat)
    (checked : ClassAwarePackedForestSaturation.validateRuleSaturation
      forest profile (plan profile) input = true)
    (first second : CST) (different : first ≠ second)
    (one : Source profile input first) (two : Source profile input second) :
    Nonempty (Packed forest profile input first) ∧
      Nonempty (Packed forest profile input second) ∧ first ≠ second :=
  ⟨(checked_forest_iff_source forest profile input checked first).mpr ⟨one⟩,
    (checked_forest_iff_source forest profile input checked second).mpr ⟨two⟩, different⟩

theorem spurious_parse_rejected (forest : Forest) (profile : ParserProfileLayer)
    (input : List Nat) (tree : CST) (absent : ¬ Nonempty (Source profile input tree)) :
    ¬ Nonempty (Packed forest profile input tree) :=
  fun replay => absent (packed_reflects forest profile input tree replay)

theorem missing_parse_rejects_completeness (forest : Forest) (profile : ParserProfileLayer)
    (input : List Nat) (tree : CST) (source : Source profile input tree)
    (missing : ¬ Nonempty (Packed forest profile input tree)) :
    ClassAwarePackedForestSaturation.validateRuleSaturation
      forest profile (plan profile) input ≠ true := by
  intro checked
  exact missing ((checked_forest_iff_source forest profile input checked tree).mpr ⟨source⟩)

def Selected (keep : CST → Bool) (forest : Forest) (profile : ParserProfileLayer)
    (input : List Nat) (tree : CST) : Prop :=
  Nonempty (Packed forest profile input tree) ∧ keep tree = true

theorem selected_iff (keep : CST → Bool) (forest : Forest) (profile : ParserProfileLayer)
    (input : List Nat)
    (checked : ClassAwarePackedForestSaturation.validateRuleSaturation
      forest profile (plan profile) input = true) (tree : CST) :
    Selected keep forest profile input tree ↔ Nonempty (Source profile input tree) ∧ keep tree = true :=
  and_congr (checked_forest_iff_source forest profile input checked tree) Iff.rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Parser
