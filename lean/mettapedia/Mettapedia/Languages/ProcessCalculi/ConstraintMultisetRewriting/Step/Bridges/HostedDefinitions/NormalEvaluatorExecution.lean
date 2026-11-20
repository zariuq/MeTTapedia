import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorGrounding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.StepRewrites

/-!
# Actual source executions of the normal evaluator

Original compiler rows execute inside the enlarged source program. Every
selected step keeps the full incoming store as a prefix and retains all
siblings, source worlds, pending frames and obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorExecution

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing
open NormalEvaluatorGrounding (DriverEntry callAt callCode bodyAt clause matchStore)

local instance closedTerms : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)
  (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
  (q : Comp (BinderCore.keys built.rules) [] () D.Ty) {qsite : (BinderCore.keys built.rules).Site}
  (qScoped : q.Scoped [qsite]) (distinct : (qsite :: q.sites).Nodup) (arrow : Hosting.ArrowComp q)

include qScoped distinct arrow

theorem original_step {before after : MClosed}
    (rewriting : ProgramBinders.Rewrites built.rules.get before after)
    (current : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (member : (⟨K, .eval (.apply datum), frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ∈
      current.branches) (determined : Determines K datum before) :
    ∃ next extra output, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .eval (.apply output), frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ∈
        next.branches ∧ Determines (K ++ extra) output after := by
  obtain ⟨storeBelow, callBelow⟩ :=
    NormalScannerExecution.call_below built D supply spaces q qScoped distinct arrow reached member
  obtain ⟨index, answered⟩ := rewriting
  let scope := current.world.scope
  let selectedClause := BinderCore.embedEquation built.rules (Ty := D.Ty) index
  let constraint : Constraint (BinderCore.keys built.rules) [] () :=
    (instantiate (BinderCore.stamp built.rules scope index) (built.rules.get index).lhs, datum)
  let output := instantiate (BinderCore.stamp built.rules scope index) (built.rules.get index).rhs
  have live : Solvable (K ++ [constraint]) := NormalEvaluatorGrounding.original_match_live built index scope
    K datum before after storeBelow callBelow determined answered
  have outputDetermined : Determines (K ++ [constraint]) output after :=
    NormalEvaluatorGrounding.original_output_determines built index scope K datum before after determined answered live
  have selectedMember : selectedClause ∈ (NormalProgram.program built D).equations :=
    NormalProgramFormation.original_mem built D (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)
  let children := (NormalProgram.program built D).equations.map (callBranch D scope K datum frames pending)
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  let next : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨current.world.fresh, (children : Multiset _) + rest⟩
  have admitted : Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope) selectedClause.lhs, datum)]) := by
    simpa only [selectedClause, BinderCore.embedEquation, BinderCore.copy_embed] using live
  have step : SourceLanguage.Step D (NormalProgram.program built D) supply current next :=
    SourceLanguage.Step.of_eq split rfl determined.1
      (.apply current.world K datum frames pending ⟨selectedClause, selectedMember, admitted⟩)
  have chosen : callBranch D scope K datum frames pending selectedClause ∈ next.branches :=
    Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map.mpr
      ⟨selectedClause, selectedMember, rfl⟩)))
  refine ⟨next, [constraint], output, Relation.ReflTransGen.single step, ?_, outputDetermined⟩
  simpa only [selectedClause, BinderCore.callBranch_embed] using chosen

theorem original_runs {before after : MClosed} (rewritten : RuleInstances.Steps built.rules before after) :
    ∀ (current : Config (BinderCore.keys built.rules) [] () D.Ty),
    Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current →
    ∀ (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (datum : Data (BinderCore.keys built.rules) [] ())
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)),
    (⟨K, .eval (.apply datum), frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches →
    Determines K datum before →
    ∃ next extra output, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .eval (.apply output), frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ∈
        next.branches ∧ Determines (K ++ extra) output after := by
  induction rewritten with
  | refl =>
      intro current reached K datum frames pending member determined
      exact ⟨current, [], datum, .refl, by simpa only [List.append_nil] using member,
        by simpa only [List.append_nil] using determined⟩
  | tail earlier rewriting ih =>
      intro current reached K datum frames pending member determined
      obtain ⟨middle, extra, output, run, included, available⟩ :=
        ih current reached K datum frames pending member determined
      obtain ⟨next, more, result, advanced, present, final⟩ :=
        original_step built D supply spaces q qScoped distinct arrow rewriting middle (reached.trans run)
          (K ++ extra) output frames pending included available
      exact ⟨next, extra ++ more, result, run.trans advanced,
        by simpa only [List.append_assoc] using present, by simpa only [List.append_assoc] using final⟩

theorem driver_enters (entry : DriverEntry) (code : MClosed)
    (current : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (call : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (member : (⟨K, .eval (.apply call), frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ∈
      current.branches) (determined : Determines K call (callCode entry code)) :
    ∃ next, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨matchStore built entry current.world.scope K call,
        .eval (bodyAt built entry
          (instantiate (copyAt (BinderCore.keys built.rules) current.world.scope) (NormalScanner.datum built 0))),
        frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧
      Determines (matchStore built entry current.world.scope K call)
        (instantiate (copyAt (BinderCore.keys built.rules) current.world.scope) (NormalScanner.datum built 0)) code := by
  obtain ⟨storeBelow, callBelow⟩ :=
    NormalScannerExecution.call_below built D supply spaces q qScoped distinct arrow reached member
  let scope := current.world.scope
  have live := NormalEvaluatorGrounding.match_live built entry scope K call code storeBelow callBelow determined
  have field := NormalEvaluatorGrounding.copied_field_determines built entry scope K call code determined live
  let children := (NormalProgram.program built D).equations.map (callBranch D scope K call frames pending)
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  let next : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨current.world.fresh, (children : Multiset _) + rest⟩
  have admitted : Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) scope)
      (clause built D entry).lhs, call)]) := live
  have step : SourceLanguage.Step D (NormalProgram.program built D) supply current next :=
    SourceLanguage.Step.of_eq split rfl determined.1 (.apply current.world K call frames pending
      ⟨clause built D entry, NormalEvaluatorGrounding.clause_mem built D entry, admitted⟩)
  have chosen : callBranch D scope K call frames pending (clause built D entry) ∈ next.branches :=
    Multiset.mem_add.mpr (.inl (Multiset.mem_coe.mpr (List.mem_map.mpr
      ⟨clause built D entry, NormalEvaluatorGrounding.clause_mem built D entry, rfl⟩)))
  refine ⟨next, .single step, ?_, field⟩
  simpa only [NormalEvaluatorGrounding.callBranch_shape] using chosen

theorem normal_reply {n : Nat} (term : Tower.Tm n) (normal : NormalStructure.Normal built term)
    (current : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (member : (⟨K, .eval (.apply (NormalProgram.evaluateAt datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches)
    (determined : Determines K datum (encodeTm term)) :
    ∃ next extra output, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .value (NormalProgram.doneAt output), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧
      Determines (K ++ extra) output (encodeTm term) := by
  let scope := current.world.scope
  let call := NormalProgram.evaluateAt datum
  let field := instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built 0)
  let selectedStore := matchStore built .evaluate scope K call
  let marker := NormalScanner.marker (fam (BinderCore.keys built.rules))
  let body : Comp (BinderCore.keys built.rules) [] () D.Ty := .ret (NormalProgram.doneAt field)
  let scanBody : Comp (BinderCore.keys built.rules) [] () D.Ty :=
    .let_ (NormalScanner.site built 1) marker (.apply (NormalScanner.scanAt field)) body
  let seekBody : Comp (BinderCore.keys built.rules) [] () D.Ty := .apply (NormalProgram.seekAt field)
  let frame : Frame (BinderCore.keys built.rules) [] () D.Ty :=
    .bindTo (NormalScanner.site built 1) marker body
  obtain ⟨entered, enter, chosen, fieldDetermined⟩ :=
    driver_enters built D supply spaces q qScoped distinct arrow .evaluate (encodeTm term) current reached
      K call frames pending member (NormalEvaluatorGrounding.determines_callAt built .evaluate determined)
  change (⟨selectedStore, .eval (.choice scanBody seekBody), frames, pending⟩ :
    Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ entered.branches at chosen
  change Determines selectedStore field (encodeTm term) at fieldDetermined
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem chosen
  let other : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty) :=
    (⟨selectedStore, .eval seekBody, frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ::ₘ rest
  let choosing : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨entered.world, (⟨selectedStore, .eval scanBody, frames, pending⟩ ::ₘ other)⟩
  have choose : SourceLanguage.Step D (NormalProgram.program built D) supply entered choosing :=
    SourceLanguage.Step.of_eq split (by simp [other, Multiset.cons_add]) fieldDetermined.1
      (.choice entered.world selectedStore scanBody seekBody frames pending)
  let started : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨entered.world, (⟨selectedStore, .eval (.apply (NormalScanner.scanAt field)), frame :: frames, pending⟩ ::ₘ other)⟩
  have start : SourceLanguage.Step D (NormalProgram.program built D) supply choosing started :=
    SourceLanguage.Step.of_eq rfl rfl fieldDetermined.1
      (.letStart entered.world selectedStore (NormalScanner.site built 1) marker
        (.apply (NormalScanner.scanAt field)) body frames pending)
  have beforeScan : Runs D (NormalProgram.program built D) supply current started := (enter.tail choose).tail start
  obtain ⟨scanned, scanExtra, scan, scanMember, scanLive⟩ :=
    NormalScannerExecution.completes_branch built D supply term normal spaces q qScoped distinct arrow
      started (reached.trans beforeScan) selectedStore field (frame :: frames) pending
      (Multiset.mem_cons_self _ _) fieldDetermined
  let scanStore := selectedStore ++ scanExtra
  let finalStore := scanStore ++ [(marker, marker)]
  have finalLive : Solvable finalStore := by
    obtain ⟨X, target, assignment, solved⟩ := scanLive
    exact ⟨X, target, assignment, (models_append assignment _ _).mpr
      ⟨solved, (models_singleton assignment _).mpr rfl⟩⟩
  have fixesField : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1)
      scanned.world.scope) field = field :=
    NormalScannerGrounding.open_copied_datum built scope scanned.world.scope 1 (by decide +kernel) 0
  have fixesBody : body.inst (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1)
      scanned.world.scope) = body := by
    simp only [body, Comp.inst, Comp.mapData, NormalProgram.doneAt, NormalScanner.instantiate_nodeAt,
      List.map_cons, List.map_nil]
    rw [fixesField]
  obtain ⟨siblings, scanSplit⟩ := Multiset.exists_cons_of_mem scanMember
  let returning : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨scanned.world.fresh, (⟨finalStore, .eval body, frames, pending⟩ ::ₘ siblings)⟩
  have bind : SourceLanguage.Step D (NormalProgram.program built D) supply scanned returning := by
    have step := SourceLanguage.Step.of_eq scanSplit rfl scanLive
      (Move.letBind (D := D) (P := NormalProgram.program built D) (supply := supply)
        scanned.world scanStore marker (NormalScanner.site built 1) marker body frames pending)
    have fixesMarker : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1)
        scanned.world.scope) marker = marker := rfl
    rw [fixesMarker, fixesBody] at step
    exact step
  let next : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨scanned.world.fresh, (⟨finalStore, .value (NormalProgram.doneAt field), frames, pending⟩ ::ₘ siblings)⟩
  have reply : SourceLanguage.Step D (NormalProgram.program built D) supply returning next :=
    SourceLanguage.Step.of_eq rfl rfl finalLive
      (.ret scanned.world.fresh finalStore (NormalProgram.doneAt field) frames pending)
  have outputDetermined : Determines finalStore field (encodeTm term) :=
    NormalScannerGrounding.determines_append built
      (NormalScannerGrounding.determines_append built fieldDetermined scanLive) finalLive
  let matching : Constraint (BinderCore.keys built.rules) [] () :=
    (instantiate (copyAt (BinderCore.keys built.rules) scope)
      (callAt .evaluate (NormalScanner.datum built 0)), call)
  refine ⟨next, [matching] ++ scanExtra ++ [(marker, marker)], field,
    ((beforeScan.trans scan).tail bind).tail reply, ?_, ?_⟩
  · simpa only [next, matching, finalStore, scanStore, selectedStore, matchStore, List.append_assoc] using
      (Multiset.mem_cons_self (⟨finalStore, .value (NormalProgram.doneAt field), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) siblings)
  · simpa only [matching, finalStore, scanStore, selectedStore, matchStore, List.append_assoc] using outputDetermined

theorem evaluate_step {n : Nat} {before after : Tower.Tm n}
    (reduction : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after)
    (current : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (member : (⟨K, .eval (.apply (NormalProgram.evaluateAt datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches)
    (determined : Determines K datum (encodeTm before)) :
    ∃ next extra output, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .eval (.apply (NormalProgram.evaluateAt output)), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧
      Determines (K ++ extra) output (encodeTm after) := by
  let scope := current.world.scope
  let call := NormalProgram.evaluateAt datum
  let field := instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built 0)
  let selectedStore := matchStore built .evaluate scope K call
  let scanBody : Comp (BinderCore.keys built.rules) [] () D.Ty :=
    .let_ (NormalScanner.site built 1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
      (.apply (NormalScanner.scanAt field)) (.ret (NormalProgram.doneAt field))
  let seekBody : Comp (BinderCore.keys built.rules) [] () D.Ty := .apply (NormalProgram.seekAt field)
  obtain ⟨entered, enter, chosen, fieldDetermined⟩ :=
    driver_enters built D supply spaces q qScoped distinct arrow .evaluate (encodeTm before) current reached
      K call frames pending member (NormalEvaluatorGrounding.determines_callAt built .evaluate determined)
  change (⟨selectedStore, .eval (.choice scanBody seekBody), frames, pending⟩ :
    Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ entered.branches at chosen
  change Determines selectedStore field (encodeTm before) at fieldDetermined
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem chosen
  let choosing : Config (BinderCore.keys built.rules) [] () D.Ty :=
    ⟨entered.world,
      (⟨selectedStore, .eval scanBody, frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ::ₘ
      (⟨selectedStore, .eval seekBody, frames, pending⟩ : Branch (BinderCore.keys built.rules) [] () D.Ty) ::ₘ rest⟩
  have choose : SourceLanguage.Step D (NormalProgram.program built D) supply entered choosing :=
    SourceLanguage.Step.of_eq split (by simp [Multiset.cons_add]) fieldDetermined.1
      (.choice entered.world selectedStore scanBody seekBody frames pending)
  have seeker : (⟨selectedStore, .eval (.apply (NormalProgram.seekAt field)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ choosing.branches :=
    Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  have beforeSeek := enter.tail choose
  obtain ⟨advanced, rewriteExtra, reply, rewritten, replyMember, replyDetermined⟩ :=
    original_runs built D supply spaces q qScoped distinct arrow
      (StepRewrites.directed_step built reduction (nodeC NormalProgram.nextTag [])) choosing
      (reached.trans beforeSeek) selectedStore (NormalProgram.seekAt field) frames pending seeker
      (NormalEvaluatorGrounding.determines_seekAt built fieldDetermined)
  obtain ⟨next, resume, finalMember, resultDetermined⟩ :=
    driver_enters built D supply spaces q qScoped distinct arrow .resume (encodeTm after) advanced
      ((reached.trans beforeSeek).trans rewritten) (selectedStore ++ rewriteExtra) reply frames pending
      replyMember replyDetermined
  let result := instantiate (copyAt (BinderCore.keys built.rules) advanced.world.scope) (NormalScanner.datum built 0)
  let matching : Constraint (BinderCore.keys built.rules) [] () :=
    (instantiate (copyAt (BinderCore.keys built.rules) scope)
      (callAt .evaluate (NormalScanner.datum built 0)), call)
  let resumeMatching : Constraint (BinderCore.keys built.rules) [] () :=
    (instantiate (copyAt (BinderCore.keys built.rules) advanced.world.scope)
      (callAt .resume (NormalScanner.datum built 0)), reply)
  refine ⟨next, [matching] ++ rewriteExtra ++ [resumeMatching], result,
    (beforeSeek.trans rewritten).trans resume, ?_, ?_⟩
  · simpa only [bodyAt, matchStore, selectedStore, List.append_assoc] using finalMember
  · simpa only [matchStore, selectedStore, List.append_assoc] using resultDetermined

theorem evaluate_steps {n : Nat} {before after : Tower.Tm n}
    (reductions : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) before after) :
    ∀ (current : Config (BinderCore.keys built.rules) [] () D.Ty),
    Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current →
    ∀ (K : List (Constraint (BinderCore.keys built.rules) [] ()))
      (datum : Data (BinderCore.keys built.rules) [] ())
      (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
      (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)),
    (⟨K, .eval (.apply (NormalProgram.evaluateAt datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches →
    Determines K datum (encodeTm before) →
    ∃ next extra output, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .eval (.apply (NormalProgram.evaluateAt output)), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧
      Determines (K ++ extra) output (encodeTm after) := by
  induction reductions with
  | refl =>
      intro current reached K datum frames pending member determined
      exact ⟨current, [], datum, .refl, by simpa only [List.append_nil] using member,
        by simpa only [List.append_nil] using determined⟩
  | tail earlier reduction ih =>
      intro current reached K datum frames pending member determined
      obtain ⟨middle, extra, output, run, included, available⟩ :=
        ih current reached K datum frames pending member determined
      obtain ⟨next, more, result, advanced, present, final⟩ :=
        evaluate_step built D supply spaces q qScoped distinct arrow reduction middle (reached.trans run)
          (K ++ extra) output frames pending included available
      exact ⟨next, extra ++ more, result, run.trans advanced,
        by simpa only [List.append_assoc] using present, by simpa only [List.append_assoc] using final⟩

theorem completes_branch {n : Nat} {before normalForm : Tower.Tm n}
    (reductions : StrongNormalization.ReducesStar (Definitions.devPackage dev built.nativeRows) before normalForm)
    (normal : NormalStructure.Normal built normalForm)
    (current : Config (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces q) current)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty))
    (pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty))
    (member : (⟨K, .eval (.apply (NormalProgram.evaluateAt datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ current.branches)
    (determined : Determines K datum (encodeTm before)) :
    ∃ next extra output, Runs D (NormalProgram.program built D) supply current next ∧
      (⟨K ++ extra, .value (NormalProgram.doneAt output), frames, pending⟩ :
        Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ next.branches ∧
      Determines (K ++ extra) output (encodeTm normalForm) := by
  obtain ⟨middle, extra, output, run, included, available⟩ :=
    evaluate_steps built D supply spaces q qScoped distinct arrow reductions current reached
      K datum frames pending member determined
  obtain ⟨next, more, result, replied, present, final⟩ :=
    normal_reply built D supply spaces q qScoped distinct arrow normalForm normal middle (reached.trans run)
      (K ++ extra) output frames pending included available
  exact ⟨next, extra ++ more, result, run.trans replied,
    by simpa only [List.append_assoc] using present, by simpa only [List.append_assoc] using final⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorExecution

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorExecution.original_runs
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorExecution.completes_branch
