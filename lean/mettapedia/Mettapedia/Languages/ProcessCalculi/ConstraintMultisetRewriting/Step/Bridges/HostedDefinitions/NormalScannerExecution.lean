import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerGrounding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalFrameTransport

/-!
# Actual execution of the recursive native scanner

Execution is composed in the existing source program. Each selected branch
retains its incoming store as a prefix, so later native fields remain
determined after earlier child scans. The induction works beneath the actual
pending frames and retains every sibling of the surrounding configuration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing
open NormalScannerGrounding (kind values childJobs checkChain matchStore)

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

private abbrev Completes (code : MClosed) : Prop :=
  ∀ (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
    (q : Comp (BinderCore.keys built.rules) [] () D.Ty)
    {qsite : (BinderCore.keys built.rules).Site},
    q.Scoped [qsite] → (qsite :: q.sites).Nodup → Hosting.ArrowComp q →
    ∀ (current : Config (BinderCore.keys built.rules) [] () D.Ty),
    Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current →
    ∀ (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (datum : Data (BinderCore.keys built.rules) [] ())
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)),
    (⟨K, .eval (.apply (NormalScanner.scanAt datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches →
    Determines K datum code →
    ∃ next extra, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧ Solvable (K ++ extra)

theorem call_below
    (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
    (q : Comp (BinderCore.keys built.rules) [] () D.Ty) {qsite : (BinderCore.keys built.rules).Site}
    (qScoped : q.Scoped [qsite]) (distinct : (qsite :: q.sites).Nodup) (arrow : Hosting.ArrowComp q)
    {current : Config (BinderCore.keys built.rules) [] () D.Ty}
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (member : (⟨K, .eval (.apply datum), frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ∈
      current.branches) : Hosting.StoreBelow current.world.scope K ∧ Hosting.DependsBelow current.world.scope datum := by
  exact NormalProbeFreshness.scoped_call_below built
    (Hosting.scoping_reachable spaces q (NormalProgramFormation.equations_formed built D)
      qScoped distinct arrow current reached _ member)

private theorem complete_chain
    (environment : Fin 3 → MClosed) (fields : List (Fin 3)) (copyScope : Nat)
    (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
    (q : Comp (BinderCore.keys built.rules) [] () D.Ty) {qsite : (BinderCore.keys built.rules).Site}
    (qScoped : q.Scoped [qsite]) (distinct : (qsite :: q.sites).Nodup) (arrow : Hosting.ArrowComp q) :
    ∀ (jobs : List (Fin 5 × Fin 3)),
    (∀ job ∈ jobs, job.1 ≠ 0 ∧ job.2 ∈ fields) →
    (∀ job ∈ jobs, Completes built D supply (environment job.2)) →
    ∀ (current : Config (BinderCore.keys built.rules) [] () D.Ty),
    Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current →
    ∀ (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)),
    (⟨K, .eval ((checkChain built jobs).inst (copyAt (BinderCore.keys built.rules) copyScope)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches →
    Solvable K →
    (∀ index ∈ fields, Determines K
      (instantiate (copyAt (BinderCore.keys built.rules) copyScope) (NormalScanner.datum built index))
      (environment index)) →
    ∃ next extra, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧ Solvable (K ++ extra) := by
  intro jobs
  induction jobs with
  | nil =>
      intro valid ready current reached K frames pending member live available
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      let returned : Branch (BinderCore.keys built.rules) [] () D.Ty :=
        ⟨K, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), frames, pending⟩
      have step : SourceLanguage.Step D (NormalProgram.program built D) supply current
          ⟨current.world, returned ::ₘ rest⟩ :=
        SourceLanguage.Step.of_eq split rfl live (.ret current.world K _ frames pending)
      refine ⟨⟨current.world, returned ::ₘ rest⟩, [], Relation.ReflTransGen.single step, ?_, ?_⟩
      · simpa only [List.append_nil] using (Multiset.mem_cons_self returned rest)
      · simpa only [List.append_nil] using live
  | cons job jobs ih =>
      intro valid ready current reached K frames pending member live available
      let copied := copyAt (BinderCore.keys built.rules) copyScope
      let field := instantiate copied (NormalScanner.datum built job.2)
      let body : Comp (BinderCore.keys built.rules) [] () D.Ty := (checkChain built jobs).inst copied
      let marker := NormalScanner.marker (fam (BinderCore.keys built.rules))
      let frame : Frame (BinderCore.keys built.rules) [] () D.Ty :=
        .bindTo (NormalScanner.site built job.1) marker body
      have codeShape : (checkChain built (job :: jobs)).inst copied =
          .let_ (NormalScanner.site built job.1) marker (.apply (NormalScanner.scanAt field)) body := by
        simp only [checkChain, List.foldr_cons, NormalScanner.childTest, Comp.inst, Comp.mapData,
          NormalScanner.instantiate_marker, NormalScanner.instantiate_scanAt]
        rfl
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      rw [codeShape] at split
      let entered : Branch (BinderCore.keys built.rules) [] () D.Ty :=
        ⟨K, .eval (.apply (NormalScanner.scanAt field)), frame :: frames, pending⟩
      let started : Config (BinderCore.keys built.rules) [] () D.Ty :=
        ⟨current.world, entered ::ₘ rest⟩
      have start : SourceLanguage.Step D (NormalProgram.program built D) supply current started :=
        SourceLanguage.Step.of_eq split rfl live (.letStart current.world K (NormalScanner.site built job.1)
          marker (.apply (NormalScanner.scanAt field)) body frames pending)
      have selected := valid job List.mem_cons_self
      obtain ⟨childDone, childExtra, childRun, childMember, childLive⟩ :=
        ready job List.mem_cons_self spaces q qScoped distinct arrow started (reached.tail start)
          K field (frame :: frames) pending (Multiset.mem_cons_self _ _) (available job.2 selected.2)
      have fixesBody := NormalScannerGrounding.open_copied_chain built (Ty := D.Ty) jobs
        copyScope childDone.world.scope job.1 selected.1
      obtain ⟨other, childSplit⟩ := Multiset.exists_cons_of_mem childMember
      let nextStore := (K ++ childExtra) ++ [(marker, marker)]
      let continued : Branch (BinderCore.keys built.rules) [] () D.Ty :=
        ⟨nextStore, .eval body, frames, pending⟩
      let bound : Config (BinderCore.keys built.rules) [] () D.Ty :=
        ⟨childDone.world.fresh, continued ::ₘ other⟩
      have nextLive : Solvable nextStore := by
        obtain ⟨X, target, assignment, solved⟩ := childLive
        exact ⟨X, target, assignment, (models_append assignment _ _).mpr
          ⟨solved, (models_singleton assignment _).mpr rfl⟩⟩
      have bind : SourceLanguage.Step D (NormalProgram.program built D) supply childDone bound := by
        have step := SourceLanguage.Step.of_eq childSplit rfl childLive
          (Move.letBind (D := D) (P := NormalProgram.program built D) (supply := supply)
            childDone.world (K ++ childExtra) marker (NormalScanner.site built job.1) marker body frames pending)
        have markerFixed : instantiate
            (openAt (BinderCore.keys built.rules) (NormalScanner.site built job.1) childDone.world.scope) marker = marker := rfl
        have bodyFixed : body.inst
            (openAt (BinderCore.keys built.rules) (NormalScanner.site built job.1) childDone.world.scope) = body := fixesBody
        rw [markerFixed, bodyFixed] at step
        exact step
      have preserved : ∀ index ∈ fields, Determines nextStore
          (instantiate copied (NormalScanner.datum built index)) (environment index) := by
        intro index used
        exact NormalScannerGrounding.determines_append built
          (NormalScannerGrounding.determines_append built (available index used) childLive) nextLive
      have tailValid : ∀ next ∈ jobs, next.1 ≠ 0 ∧ next.2 ∈ fields :=
        fun next inside => valid next (List.mem_cons_of_mem _ inside)
      have tailReady : ∀ next ∈ jobs, Completes built D supply (environment next.2) :=
        fun next inside => ready next (List.mem_cons_of_mem _ inside)
      have beforeTail := ((Relation.ReflTransGen.single start).trans childRun).tail bind
      obtain ⟨after, extra, finished, included, alive⟩ :=
        ih tailValid tailReady bound (reached.trans beforeTail) nextStore frames pending
          (Multiset.mem_cons_self _ _) nextLive preserved
      refine ⟨after, childExtra ++ [(marker, marker)] ++ extra, beforeTail.trans finished, ?_, ?_⟩
      · simpa only [nextStore, List.append_assoc] using included
      · simpa only [nextStore, List.append_assoc] using alive

private theorem complete_case {n : Nat} (term : Tower.Tm n) (normal : NormalStructure.Normal built term)
    (children : ∀ job ∈ childJobs (kind term), Completes built D supply (values term job.2)) :
    Completes built D supply (encodeTm term) := by
  intro spaces q qsite qScoped distinct arrow current reached K datum frames pending member determined
  obtain ⟨storeBelow, callBelow⟩ := call_below built D supply spaces q qScoped distinct arrow reached member
  let copyScope := current.world.scope
  let ctor := kind term
  let environment := values term
  let copied := copyAt (BinderCore.keys built.rules) copyScope
  let fieldPattern := instantiate copied (NormalScanner.pattern built ctor)
  let body : Comp (BinderCore.keys built.rules) [] () D.Ty :=
    (checkChain built (childJobs ctor)).inst copied
  let nextStore := matchStore built copyScope K datum ctor
  have live : Solvable nextStore := NormalScannerGrounding.match_live built copyScope K datum ctor
    environment (encodeTm term) (NormalScannerGrounding.encode_instance term) storeBelow callBelow determined
  let clause := NormalScanner.equation built D ctor
  let branches := (NormalProgram.program built D).equations.map
    (callBranch D copyScope K (NormalScanner.scanAt datum) frames pending)
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  let selected : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨current.world.fresh, (branches : Multiset _) + rest⟩
  have step : SourceLanguage.Step D (NormalProgram.program built D) supply current selected :=
    SourceLanguage.Step.of_eq split rfl determined.1 (.apply current.world K (NormalScanner.scanAt datum)
      frames pending ⟨clause, NormalProgramFormation.scanner_mem built D ctor, live⟩)
  have chosen : callBranch D copyScope K (NormalScanner.scanAt datum) frames pending clause ∈ selected.branches :=
    Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map.mpr
      ⟨clause, NormalProgramFormation.scanner_mem built D ctor, rfl⟩)))
  have rootMember : (⟨nextStore, .eval (NormalScanner.rootTest built fieldPattern body), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ selected.branches := by
    simpa only [clause, NormalScannerGrounding.callBranch_shape, NormalScannerGrounding.childTests_eq_chain] using chosen
  have patternDetermined := NormalScannerGrounding.copied_pattern_determines built copyScope K datum ctor
    (encodeTm term) determined live
  have rootDetermined := NormalScannerGrounding.determines_root built patternDetermined
  have disabled : ¬ NormalRootMatching.Enabled built D selected.world.scope nextStore
      (NormalScanner.rootAt fieldPattern) :=
    NormalRootMatching.normal_disables_probes built D selected.world.scope nextStore
      (NormalScanner.rootAt fieldPattern) term (csym NormalScanner.stopTag) rootDetermined normal
  have fixesTerm : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1)
      selected.world.scope) fieldPattern = fieldPattern :=
    NormalScannerGrounding.open_copied_pattern built ctor copyScope selected.world.scope 1 (by decide +kernel)
  have fixesBody : body.inst (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1)
      selected.world.scope) = body :=
    NormalScannerGrounding.open_copied_chain built _ copyScope selected.world.scope 1 (by decide +kernel)
  obtain ⟨other, rootSplit⟩ := Multiset.exists_cons_of_mem rootMember
  let probe := NormalScanner.probeAt fieldPattern
  let rootStore := nextStore ++ [(probe, probe)]
  let continued : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨selected.world.fresh, (⟨rootStore, .eval body, frames, pending⟩ ::ₘ other)⟩
  obtain ⟨gate, rootLive⟩ := NormalProbeExecution.unmatched_fixed_runs built D supply selected.world
    nextStore fieldPattern body frames pending other live disabled fixesTerm fixesBody
  have rootRun : Runs D (NormalProgram.program built D) supply selected continued := by
    simpa only [← rootSplit] using gate
  have rootFields : ∀ index ∈ ctor.fields, Determines rootStore
      (instantiate copied (NormalScanner.datum built index)) (environment index) := by
    intro index used
    exact NormalScannerGrounding.determines_append built
      (NormalScannerGrounding.copied_field_determines built copyScope K datum ctor environment
        (encodeTm term) (NormalScannerGrounding.encode_instance term) determined live index used) rootLive
  have beforeChain := (Relation.ReflTransGen.single step).trans rootRun
  obtain ⟨after, extra, scanned, included, alive⟩ :=
    complete_chain built D supply environment ctor.fields copyScope spaces q qScoped distinct arrow
      (childJobs ctor) (NormalScannerGrounding.childJobs_sites ctor) children
      continued (reached.trans beforeChain) rootStore frames pending
      (Multiset.mem_cons_self _ _) rootLive rootFields
  let matching : Constraint (BinderCore.keys built.rules) [] () :=
    (instantiate copied (NormalScanner.scanAt (NormalScanner.pattern built ctor)), NormalScanner.scanAt datum)
  refine ⟨after, [matching] ++ [(probe, probe)] ++ extra, beforeChain.trans scanned, ?_, ?_⟩
  · simpa only [rootStore, nextStore, matchStore, List.append_assoc] using included
  · simpa only [rootStore, nextStore, matchStore, List.append_assoc] using alive

private theorem normal_complete {n : Nat} (term : Tower.Tm n) (normal : NormalStructure.Normal built term) :
    Completes built D supply (encodeTm term) := by
  revert normal
  induction term with
  | var index =>
      intro normal
      apply complete_case built D supply (.var index) normal
      intro job inside
      cases inside
  | const name =>
      intro normal
      apply complete_case built D supply (.const name) normal
      intro job inside
      cases inside
  | head head =>
      intro normal
      apply complete_case built D supply (.head head) normal
      intro job inside
      cases inside
  | pi domain body ihDomain ihBody =>
      intro normal
      have parts := NormalStructure.normal_children built (.pi domain body) normal
      apply complete_case built D supply (.pi domain body) normal
      intro job inside
      simp only [kind, childJobs, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact ihDomain parts.1
      · exact ihBody parts.2
  | sigma domain body ihDomain ihBody =>
      intro normal
      have parts := NormalStructure.normal_children built (.sigma domain body) normal
      apply complete_case built D supply (.sigma domain body) normal
      intro job inside
      simp only [kind, childJobs, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact ihDomain parts.1
      · exact ihBody parts.2
  | id carrier left right ihCarrier ihLeft ihRight =>
      intro normal
      have parts := NormalStructure.normal_children built (.id carrier left right) normal
      apply complete_case built D supply (.id carrier left right) normal
      intro job inside
      simp only [kind, childJobs, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact ihCarrier parts.1
      · exact ihLeft parts.2.1
      · exact ihRight parts.2.2
  | lam body ih =>
      intro normal
      have part := NormalStructure.normal_children built (.lam body) normal
      apply complete_case built D supply (.lam body) normal
      intro job inside
      have same : job = (2, 0) := List.mem_singleton.mp inside
      subst job
      exact ih part
  | app function argument ihFunction ihArgument =>
      intro normal
      have parts := NormalStructure.normal_children built (.app function argument) normal
      apply complete_case built D supply (.app function argument) normal
      intro job inside
      simp only [kind, childJobs, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact ihFunction parts.1
      · exact ihArgument parts.2
  | pair first second ihFirst ihSecond =>
      intro normal
      have parts := NormalStructure.normal_children built (.pair first second) normal
      apply complete_case built D supply (.pair first second) normal
      intro job inside
      simp only [kind, childJobs, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact ihFirst parts.1
      · exact ihSecond parts.2
  | fst subject ih =>
      intro normal
      have part := NormalStructure.normal_children built (.fst subject) normal
      apply complete_case built D supply (.fst subject) normal
      intro job inside
      have same : job = (2, 0) := List.mem_singleton.mp inside
      subst job
      exact ih part
  | snd subject ih =>
      intro normal
      have part := NormalStructure.normal_children built (.snd subject) normal
      apply complete_case built D supply (.snd subject) normal
      intro job inside
      have same : job = (2, 0) := List.mem_singleton.mp inside
      subst job
      exact ih part
  | refl subject ih =>
      intro normal
      have part := NormalStructure.normal_children built (.refl subject) normal
      apply complete_case built D supply (.refl subject) normal
      intro job inside
      have same : job = (2, 0) := List.mem_singleton.mp inside
      subst job
      exact ih part

theorem completes_branch {n : Nat} (term : Tower.Tm n) (normal : NormalStructure.Normal built term)
    (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
    (q : Comp (BinderCore.keys built.rules) [] () D.Ty) {qsite : (BinderCore.keys built.rules).Site}
    (qScoped : q.Scoped [qsite]) (distinct : (qsite :: q.sites).Nodup) (arrow : Hosting.ArrowComp q)
    (current : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (member : (⟨K, .eval (.apply (NormalScanner.scanAt datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches)
    (determined : Determines K datum (encodeTm term)) :
    ∃ next extra, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧ Solvable (K ++ extra) :=
  normal_complete built D supply term normal spaces q qScoped distinct arrow current reached K datum frames pending
    member determined

theorem normal_executes {n : Nat} (term : Tower.Tm n) (normal : NormalStructure.Normal built term) :
    ∃ next branch,
      Runs D (NormalProgram.program built D) supply
        (Config.initial (fun _ => 0) (NormalScanner.query built (encodeTm term))) next ∧
      branch ∈ next.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      (csym NormalScanner.markerTag) ∈ branch.answer (D := D) := by
  let q := NormalScanner.query built (Ty := D.Ty) (encodeTm term)
  let current := Config.initial (fun _ => 0) q
  have live : Solvable ([] : List (Constraint (BinderCore.keys built.rules) [] ())) :=
    ⟨Empty, ProgramBinders.ground MSig, ProgramBinders.close (fam (BinderCore.keys built.rules)),
      fun _ inside => False.elim (List.not_mem_nil inside)⟩
  have determined := NormalProbeFreshness.determines_include built [] live (encodeTm term)
  obtain ⟨next, extra, run, member, alive⟩ := completes_branch built D supply term normal
    (fun _ => 0) q (NormalScanner.query_scoped built (encodeTm term))
    (NormalScanner.query_distinct built (encodeTm term)) (NormalScanner.query_arrows built (encodeTm term))
    current Relation.ReflTransGen.refl [] (Rigid.includeTerm (fam (BinderCore.keys built.rules)) (encodeTm term))
    [] [] (Multiset.mem_singleton_self _) determined
  let branch : Branch (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨extra, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), [], []⟩
  refine ⟨next, branch, run, member, ⟨rfl, _, rfl⟩, alive, ?_⟩
  obtain ⟨X, target, assignment, solved⟩ := alive
  exact ⟨NormalScanner.marker (fam (BinderCore.keys built.rules)), rfl, X, target, assignment, solved, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecution.completes_branch
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerExecution.normal_executes
