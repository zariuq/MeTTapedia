import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRRewriteValidation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotAdmission

/-! Generated rule names retain distinct source statement positions. The
fixed authored signature and every compiled rewrite row therefore pass the
actual language validator, completing admission of canonical snapshots. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.LanguageValidation

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private theorem numbered_indices_unique (program : Program) :
    ((LPBridge.numberedClauses program).map Prod.fst).Nodup := by
  have indexed := List.pairwise_map.mp (List.nodup_zipIdx_map_snd program.statements)
  simp only [LPBridge.numberedClauses,List.map_filterMap]
  apply List.Pairwise.filterMap _ ?_ indexed
  intro first second different left leftFormed right rightFormed same
  rcases first with ⟨first,index⟩
  rcases second with ⟨second,other⟩
  cases first <;> cases second <;> simp_all

private theorem compiled_name (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) : rule.name = "datalog-clause:" ++ toString ordinal := by
  obtain ⟨original,formed,rfl⟩ := Option.map_eq_some_iff.mp compiled
  unfold Join.compileClause? at formed
  split at formed
  · cases formed
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at formed
    obtain ⟨_,_,_,_,same⟩ := formed
    cases Option.some.inj same
    rfl

private theorem names_of_rows (pools : Join.Pools) (clauses : List (Nat × Clause)) (rules : List RewriteRule)
    (related : List.Forall₂ (fun entry rule => Query.compileClause? pools entry.1 entry.2 = some rule) clauses rules) :
    rules.map RewriteRule.name = clauses.map (fun entry => "datalog-clause:" ++ toString entry.1) := by
  induction related with
  | nil => rfl
  | @cons entry rule entries rules first rest ih =>
    simp only [List.map_cons,compiled_name pools entry.1 entry.2 rule first,ih]

theorem rule_names_unique (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) : (prepared.compiled.rewrites.map RewriteRule.name).Nodup := by
  obtain ⟨core,values,formed,_,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
  have original := (Join.Program.prepare?_sound program seeds core formed).2.2.2
  have related : List.Forall₂ (fun entry rule => Query.compileClause? core.vocabulary entry.1 entry.2 = some rule)
      (LPBridge.numberedClauses program) (core.rules.map (Query.lowerRule core.vocabulary)) := by
    apply List.forall₂_map_right_iff.mpr
    exact original.imp (fun entry rule compiled => congrArg (Option.map (Query.lowerRule core.vocabulary)) compiled)
  change ((core.rules.map (Query.lowerRule core.vocabulary)).map RewriteRule.name).Nodup
  rw [names_of_rows core.vocabulary _ _ related]
  have encoded := (numbered_indices_unique program).map (f := fun index : Nat => "datalog-clause:" ++ toString index)
    (fun first second same => Nat.repr_injective ((String.append_right_inj "datalog-clause:").mp same))
  simpa only [List.map_map,Function.comp_def] using encoded

theorem language_valid (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) : prepared.compiled.validate = [] := by
  have types : prepared.compiled.typeNames = Query.baseLanguage.typeNames := by
    obtain ⟨core,values,_,_,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
    rfl
  have terms : prepared.compiled.terms = Query.baseLanguage.terms := SourcePlan.plan_grammar program seeds prepared accepted []
  have equations : prepared.compiled.equations = [] := by
    obtain ⟨core,values,_,_,rfl⟩ := PlanReading.prepared_payload program seeds prepared accepted
    rfl
  have baseValid : Query.baseLanguage.validate = [] := by decide +kernel
  apply LanguageDef.validate_eq_nil_of_rows
  · rw [types]
    decide +kernel
  · rw [terms]
    decide +kernel
  · simp only [equations,List.map_nil,List.nodup_nil]
  · exact rule_names_unique program seeds prepared accepted
  · intro term member
    rw [terms] at member
    simpa only [LanguageDef.validateTerm,types] using
      LanguageDef.validateTerm_eq_nil_of_validate_eq_nil Query.baseLanguage baseValid term member
  · intro equation member
    rw [equations] at member
    cases member
  · intro rule member
    obtain ⟨index,selected⟩ := List.mem_iff_getElem?.mp member
    have inside := (List.getElem?_eq_some_iff.mp selected).1
    obtain ⟨ordinal,clause,source,compiled,_⟩ := Executable.compiled_origin_at program seeds prepared accepted index inside
    rw [(List.getElem?_eq_some_iff.mp selected).2] at compiled
    exact RewriteValidation.rewrite_valid program seeds prepared accepted ordinal clause source rule compiled

theorem canonical_snapshot_admitted (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern)
    (canonical : ClosureMachine.CanonicalFacts prepared known) : (Executable.plan prepared known).complete = true :=
  SnapshotAdmission.complete_of_language_valid program seeds prepared accepted known canonical (language_valid program seeds prepared accepted)

theorem initial_admitted (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) :
    (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true :=
  canonical_snapshot_admitted program seeds prepared accepted prepared.seedFacts.eraseDups
    (ClosureMachine.begin_canonical program seeds prepared accepted)

#print axioms language_valid
#print axioms canonical_snapshot_admitted
#print axioms initial_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.LanguageValidation
