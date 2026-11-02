import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClauseSoundness
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceSemantics
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator

/-! Prepared Datalog plans retain actual source declaration positions.
Their equation-free, root-only receipts have no administrative predecessor
or hidden inner firing that could change the source request. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PlanReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

theorem prepared_payload (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) :
    ∃ core : Join.Program.Prepared, ∃ encoded : List Pattern,
      Join.Program.prepare? program seeds = some core ∧
      seeds.mapM (Executable.fact? core.vocabulary) = some encoded ∧
      prepared = ⟨program,core.vocabulary,Query.language (core.rules.map (Query.lowerRule core.vocabulary)),
        encoded.eraseDups,Executable.comparisonRows program core.vocabulary⟩ := by
  cases base : Join.Program.prepare? program seeds with
  | none => simp [Executable.prepare,base] at accepted
  | some core =>
    cases diagnostic : Executable.scalarDiagnostic? program core.vocabulary with
    | some _ => simp [Executable.prepare,base,diagnostic] at accepted
    | none =>
      cases encoded : seeds.mapM (Executable.fact? core.vocabulary) with
      | none => simp [Executable.prepare,base,diagnostic,encoded] at accepted
      | some values =>
        simp only [Executable.prepare,base,diagnostic,encoded] at accepted
        change Except.ok (ε := String)
          (Executable.Prepared.mk program core.vocabulary
            (Query.language (core.rules.map (Query.lowerRule core.vocabulary)))
            values.eraseDups (Executable.comparisonRows program core.vocabulary)) = .ok prepared at accepted
        exact ⟨core,values,rfl,encoded,(Except.ok.inj accepted).symm⟩

private theorem prepared_language (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) :
    ∃ rules, prepared.compiled = Query.language rules := by
  obtain ⟨core,encoded,_,_,same⟩ := prepared_payload program seeds prepared accepted
  subst prepared
  exact ⟨_,rfl⟩

theorem equations_empty (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) :
    (Executable.plan prepared known).equations = [] := by
  obtain ⟨rules,language⟩ := prepared_language program seeds prepared accepted
  have none : prepared.compiled.equations = [] := by rw [language]; rfl
  simp [Executable.plan,GeneralExecutionAdmission.compile,GeneralExecutionAdmission.equations,
    GeneralExecutionAdmission.selectedEquations,Executable.snapshot,none]

theorem conversion_trivial (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    {before after : Pattern} {history : List GeneralOccurrenceSemantics.Conversion}
    (converted : GeneralOccurrenceSemantics.ConversionPath (Executable.plan prepared known) [] (.base "DlStatement")
      before after history) : before = after ∧ history = [] := by
  cases converted with
  | nil => exact ⟨rfl,rfl⟩
  | cons complete _ _ =>
    have member := List.fst_mem_of_mem_zipIdx complete.job.1
    rw [equations_empty program seeds prepared accepted known] at member
    cases member
  | back complete _ _ =>
    have member := List.fst_mem_of_mem_zipIdx complete.job.1
    rw [equations_empty program seeds prepared accepted known] at member
    cases member

theorem root_site (prepared : Executable.Prepared) (known : List Pattern) (source : Pattern) (site : SiteData)
    (licensed : Licensed (GeneralPlanEnvironment.environment (Executable.plan prepared known)).language
      (Executable.plan prepared known).snapshot.free (Executable.plan prepared known).permissions.sites
      [] (.base "DlStatement") source site) : site = SiteData.here [] (.base "DlStatement") source := by
  have generated := generate_complete licensed
  change site ∈ generate _ _ .rootOnly [] (.base "DlStatement") source at generated
  rw [generate_rootOnly] at generated
  split at generated
  · exact List.mem_singleton.mp generated
  · cases generated

theorem declaration_source (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (source : Pattern) (receipt : GeneralRuleJobs.Receipt)
    (valid : receipt.Valid (Executable.plan prepared known) [] (.base "DlStatement") source) :
    ∃ ordinal clause rule,
      ProgramGrounding.ClauseAt program ordinal clause ∧
      Query.compileClause? prepared.vocabulary ordinal clause = some rule ∧
      receipt.job.declaration.authored = rule ∧
      receipt.job.declaration.declarationIndex < prepared.compiled.rewrites.length := by
  obtain ⟨rule,index,member,_,planned⟩ := GeneralExecutionAdmission.compiled_rule_origin
    (List.fst_mem_of_mem_zipIdx valid.1.1)
  have read := GeneralExecutionAdmission.rulePlan_readout planned
  have atRule := List.mk_mem_zipIdx_iff_getElem?.mp member
  have inside : index < prepared.compiled.rewrites.length := (List.getElem?_eq_some_iff.mp atRule).1
  obtain ⟨ordinal,clause,atSource,compiled,_⟩ := Executable.compiled_origin_at program seeds prepared accepted index inside
  have actual : prepared.compiled.rewrites[index] = rule := (List.getElem?_eq_some_iff.mp atRule).2
  rw [actual] at compiled
  exact ⟨ordinal,clause,rule,atSource,compiled,read.2.1,read.1 ▸ inside⟩

#print axioms prepared_payload
#print axioms equations_empty
#print axioms conversion_trivial
#print axioms root_site
#print axioms declaration_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PlanReading
