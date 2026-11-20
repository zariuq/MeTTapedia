import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgram
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ProgramScope

/-!
# Formation of the assembled general normal-form source program

The original equations, root probes, structural scanner and evaluator driver
retain their actual compiled key family. Every equation satisfies the source
hosting scope, distinct-site and arrow-fragment conditions. The public query
uses the existing done-payload bind. These formation laws supply no reduction
oracle or execution correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramFormation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open NativeTypesOnTheStep.Computing

@[simp] theorem support_wrap {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) :
    support (NormalProbe.wrap term) = support term := by
  change support (NormalScanner.nodeAt NormalProbe.probeTag [term]) = support term
  simp only [NormalScanner.support_nodeAt, List.flatMap_cons, List.flatMap_nil, List.append_nil]

@[simp] theorem support_evaluateAt {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) :
    support (NormalProgram.evaluateAt term) = support term := by
  simp only [NormalProgram.evaluateAt, NormalScanner.support_nodeAt, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

@[simp] theorem support_nextAt {X : Type} (target : X → MetaArity MSig) :
    support (NormalProgram.nextAt target) = [] := rfl

@[simp] theorem support_seekAt {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) : support (NormalProgram.seekAt term) = support term := by
  simp only [NormalProgram.seekAt, NormalScanner.support_nodeAt, support_nextAt,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

@[simp] theorem support_resumeAt {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) : support (NormalProgram.resumeAt term) = support term := by
  simp only [NormalProgram.resumeAt, NormalScanner.support_nodeAt, support_nextAt,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

@[simp] theorem support_doneAt {X : Type} {target : X → MetaArity MSig}
    (term : Term (signature MSig target) [] ()) : support (NormalProgram.doneAt term) = support term := by
  simp only [NormalProgram.doneAt, NormalScanner.support_nodeAt, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

@[simp] theorem names_wrap {κ : Keys MSig} (allowed : List κ.Site) (term : Data κ [] ()) :
    NamesIn allowed (NormalProbe.wrap term) ↔ NamesIn allowed term := by
  simp only [NamesIn, support_wrap]

@[simp] theorem names_evaluateAt {κ : Keys MSig} (allowed : List κ.Site) (term : Data κ [] ()) :
    NamesIn allowed (NormalProgram.evaluateAt term) ↔ NamesIn allowed term := by
  simp only [NamesIn, support_evaluateAt]

@[simp] theorem names_seekAt {κ : Keys MSig} (allowed : List κ.Site) (term : Data κ [] ()) :
    NamesIn allowed (NormalProgram.seekAt term) ↔ NamesIn allowed term := by
  simp only [NamesIn, support_seekAt]

@[simp] theorem names_resumeAt {κ : Keys MSig} (allowed : List κ.Site) (term : Data κ [] ()) :
    NamesIn allowed (NormalProgram.resumeAt term) ↔ NamesIn allowed term := by
  simp only [NamesIn, support_resumeAt]

@[simp] theorem names_doneAt {κ : Keys MSig} (allowed : List κ.Site) (term : Data κ [] ()) :
    NamesIn allowed (NormalProgram.doneAt term) ↔ NamesIn allowed term := by
  simp only [NamesIn, support_doneAt]

theorem names_redex_marker {κ : Keys MSig} (allowed : List κ.Site) :
    NamesIn allowed (NormalProbe.marker (fam κ)) := by
  intro name member
  change name ∈ [] at member
  cases member

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

theorem probes_formed :
    ∀ clause ∈ NormalProgram.probes built D,
      clause.Scoped ∧ (clause.site :: clause.rhs.sites).Nodup ∧ Hosting.ArrowComp clause.rhs := by
  intro clause member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  refine ⟨⟨?_, names_redex_marker _⟩, List.nodup_singleton _, ?_⟩
  · exact (names_wrap _ _).mpr (ProgramScope.embedded_names built.rules index _)
  · trivial

theorem driver_formed :
    ∀ clause ∈ NormalProgram.driver built D,
      clause.Scoped ∧ (clause.site :: clause.rhs.sites).Nodup ∧ Hosting.ArrowComp clause.rhs := by
  intro clause member
  simp only [NormalProgram.driver, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (names_evaluateAt _ _).mpr (NormalScanner.names_datum built _ List.mem_cons_self 0)
    · refine ⟨⟨?_, NormalScanner.names_marker _, ?_⟩, ?_⟩
      · exact (NormalScanner.names_scanAt _ _).mpr
          (NormalScanner.names_datum built _ List.mem_cons_self 0)
      · exact (names_doneAt _ _).mpr (NormalScanner.names_datum built _ (by simp) 0)
      · exact (names_seekAt _ _).mpr (NormalScanner.names_datum built _ List.mem_cons_self 0)
    · have distinct : ([0, 1] : List (Fin 5)).Nodup := by decide +kernel
      exact distinct.map (NormalScanner.site_injective built)
    · exact ⟨⟨trivial, trivial⟩, trivial⟩
  · refine ⟨⟨?_, ?_⟩, List.nodup_singleton _, ?_⟩
    · exact (names_resumeAt _ _).mpr (NormalScanner.names_datum built _ List.mem_cons_self 0)
    · exact (names_evaluateAt _ _).mpr (NormalScanner.names_datum built _ List.mem_cons_self 0)
    · trivial

theorem equation_mem_iff (clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty) :
    clause ∈ (NormalProgram.program built D).equations ↔
      clause ∈ (BinderCore.program built.rules).equations ∨
      clause ∈ NormalProgram.probes built D ∨
      clause ∈ NormalScanner.equations built D ∨ clause ∈ NormalProgram.driver built D := by
  simp only [NormalProgram.program, List.mem_append, or_assoc]

theorem original_mem {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (BinderCore.program built.rules).equations) :
    clause ∈ (NormalProgram.program built D).equations :=
  (equation_mem_iff built D clause).mpr (.inl member)

theorem probe_mem (index : Fin built.rules.length) (member : index ∈ NormalProgram.rootIndices built) :
    NormalProbe.equation (BinderCore.embedEquation built.rules (Ty := D.Ty) index) ∈
      (NormalProgram.program built D).equations :=
  (equation_mem_iff built D _).mpr (.inr (.inl (List.mem_map.mpr ⟨index, member, rfl⟩)))

theorem scanner_mem (kind : NormalScanner.Constructor) :
    NormalScanner.equation built D kind ∈ (NormalProgram.program built D).equations :=
  (equation_mem_iff built D _).mpr (.inr (.inr (.inl
    (List.mem_map.mpr ⟨kind, NormalScanner.constructor_list_complete kind, rfl⟩))))

theorem driver_mem {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ NormalProgram.driver built D) : clause ∈ (NormalProgram.program built D).equations :=
  (equation_mem_iff built D clause).mpr (.inr (.inr (.inr member)))

theorem equations_formed :
    ∀ clause ∈ (NormalProgram.program built D).equations,
      clause.Scoped ∧ (clause.site :: clause.rhs.sites).Nodup ∧ Hosting.ArrowComp clause.rhs := by
  intro clause member
  rcases (equation_mem_iff built D clause).mp member with original | probe | scanner | driver
  · exact ProgramScope.equations built.rules D clause original
  · exact probes_formed built D clause probe
  · exact NormalScanner.equations_formed built D clause scanner
  · exact driver_formed built D clause driver

theorem program_arrows : Hosting.ArrowProgram (NormalProgram.program built D) :=
  fun clause member => (equations_formed built D clause member).2.2

theorem query_scoped (term : Tower.Tm 0) {Ty : Type} :
    (NormalProgram.query built (Ty := Ty) term).Scoped
      [ProgramLayout.querySite RuntimeSubstitution.rules built.authored] :=
  PublicQuery.query_scoped RuntimeSubstitution.rules built.authored (NormalProgram.code term)

theorem query_distinct (term : Tower.Tm 0) {Ty : Type} :
    (ProgramLayout.querySite RuntimeSubstitution.rules built.authored ::
      (NormalProgram.query built (Ty := Ty) term).sites).Nodup :=
  PublicQuery.query_distinct RuntimeSubstitution.rules built.authored (NormalProgram.code term)

theorem query_arrows (term : Tower.Tm 0) {Ty : Type} :
    Hosting.ArrowComp (NormalProgram.query built (Ty := Ty) term) :=
  PublicQuery.query_arrows RuntimeSubstitution.rules built.authored (NormalProgram.code term)

theorem query_site : ProgramLayout.querySite RuntimeSubstitution.rules built.authored =
    NormalScanner.site built 0 := rfl

theorem result_site : ProgramLayout.resultSite RuntimeSubstitution.rules built.authored =
    NormalScanner.site built 1 := rfl

theorem original_lhs_head
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (BinderCore.program built.rules).equations) :
    literalHead clause.lhs = some activeTag := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact literalHead_instantiate (BinderCore.embedAt built.rules index) (built.separated.lhs index)

theorem probe_lhs_head
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ NormalProgram.probes built D) :
    literalHead clause.lhs = some NormalProbe.probeTag := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem scanner_lhs_head
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ NormalScanner.equations built D) :
    literalHead clause.lhs = some NormalScanner.scanTag := by
  obtain ⟨kind, _, rfl⟩ := List.mem_map.mp member
  exact NormalScanner.equation_head built D kind

theorem driver_lhs_heads
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ NormalProgram.driver built D) :
    literalHead clause.lhs = some NormalProgram.evaluateTag ∨ literalHead clause.lhs = some activeTag := by
  simp only [NormalProgram.driver, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inl rfl
  · exact .inr rfl

theorem lhs_heads
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations) :
    literalHead clause.lhs = some activeTag ∨
      literalHead clause.lhs = some NormalProbe.probeTag ∨
      literalHead clause.lhs = some NormalScanner.scanTag ∨
      literalHead clause.lhs = some NormalProgram.evaluateTag := by
  rcases (equation_mem_iff built D clause).mp member with original | probe | scanner | driver
  · exact .inl (original_lhs_head built D original)
  · exact .inr (.inl (probe_lhs_head built D probe))
  · exact .inr (.inr (.inl (scanner_lhs_head built D scanner)))
  · rcases driver_lhs_heads built D driver with evaluate | active
    · exact .inr (.inr (.inr evaluate))
    · exact .inl active

theorem done_lhs_head_excluded
    {clause : SourceLanguage.Equation (BinderCore.keys built.rules) [] () D.Ty}
    (member : clause ∈ (NormalProgram.program built D).equations) :
    literalHead clause.lhs ≠ some doneTag := by
  intro headed
  rcases lhs_heads built D member with active | probe | scanner | evaluate
  · exact active_done_distinct (Option.some.inj (active.symm.trans headed))
  · exact (by decide +kernel : NormalProbe.probeTag ≠ doneTag)
      (Option.some.inj (probe.symm.trans headed))
  · exact (by decide +kernel : NormalScanner.scanTag ≠ doneTag)
      (Option.some.inj (scanner.symm.trans headed))
  · exact (by decide +kernel : NormalProgram.evaluateTag ≠ doneTag)
      (Option.some.inj (evaluate.symm.trans headed))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramFormation

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramFormation.equations_formed
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalProgramFormation.done_lhs_head_excluded
