import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorProgressEpisodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalPublicTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalEvaluatorCertificates
import Mathlib.Data.Prod.Lex

/-!
# Lexicographic progress evidence for the actual normal evaluator

The components distinguish native directed progress, original-row episode
accessibility, and finite source/scanner administration. An episode keeps its
native source fixed; only its real return to evaluation can reset episode
work under a smaller native accessibility rank.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgress

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NormalEvaluatorCertificates (Certificate Reaches publicFrame payload markerFrame scanBody envelop CorrectOutput)

abbrev Weight := Ordinal.{0} ×ₗ (Ordinal.{0} ×ₗ Nat)

def weight (native episode : Ordinal.{0}) (phase : Nat) : Weight :=
  toLex (native, toLex (episode, phase))

theorem weight_native_lt {first second : Ordinal.{0}} (less : first < second)
    (firstEpisode secondEpisode : Ordinal.{0}) (firstPhase secondPhase : Nat) :
    weight first firstEpisode firstPhase < weight second secondEpisode secondPhase :=
  Prod.Lex.toLex_lt_toLex.mpr (.inl less)

theorem weight_episode_lt (native : Ordinal.{0}) {first second : Ordinal.{0}} (less : first < second)
    (firstPhase secondPhase : Nat) :
    weight native first firstPhase < weight native second secondPhase :=
  Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (.inl less)⟩)

theorem weight_phase_lt (native episode : Ordinal.{0}) {first second : Nat} (less : first < second) :
    weight native episode first < weight native episode second :=
  Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (.inr ⟨rfl, less⟩)⟩)

theorem weight_le {firstNative secondNative firstEpisode secondEpisode : Ordinal.{0}}
    {firstPhase secondPhase : Nat} (native : firstNative ≤ secondNative)
    (episode : firstEpisode ≤ secondEpisode) (phase : firstPhase ≤ secondPhase) :
    weight firstNative firstEpisode firstPhase ≤ weight secondNative secondEpisode secondPhase := by
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases lt_or_eq_of_le native with less | same
  · exact .inl less
  · refine .inr ⟨same, Prod.Lex.toLex_le_toLex.mpr ?_⟩
    rcases lt_or_eq_of_le episode with less | equal
    · exact .inl less
    · exact .inr ⟨equal, phase⟩

theorem weight_zero_phase_lt (native episode : Ordinal.{0}) {first second : Nat} (less : first < second) :
    weight 0 0 first < weight native episode second :=
  (weight_phase_lt 0 0 less).trans_le (weight_le bot_le bot_le le_rfl)

variable {dev : Definitions.Development} (built : Compiled dev)

def evaluationBudget (before : Tower.Tm 0) : Ordinal.{0} :=
  Order.succ (NormalEvaluatorProgressEpisodes.episode_normalizes built
    (NormalEvaluatorMachineView.initial built before)).rank

theorem episode_lt_evaluationBudget (before : Tower.Tm 0) :
    (NormalEvaluatorProgressEpisodes.episode_normalizes built
      (NormalEvaluatorMachineView.initial built before)).rank < evaluationBudget built before :=
  Order.lt_succ _

theorem evaluationBudget_positive (before : Tower.Tm 0) : 0 < evaluationBudget built before :=
  lt_of_le_of_lt bot_le (episode_lt_evaluationBudget built before)

abbrev NativeAcc (term : Tower.Tm 0) : Prop :=
  Acc (fun after before => StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after) term

theorem native_acc_reaches {initial current : Tower.Tm 0} (source : NativeAcc built initial)
    (reached : Reaches built initial current) : NativeAcc built current := by
  induction reached with
  | refl => exact source
  | tail _ step ih => exact ih.inv step

def nativeRank {initial current : Tower.Tm 0} (source : NativeAcc built initial)
    (reached : Reaches built initial current) : Ordinal.{0} :=
  (native_acc_reaches built source reached).rank

theorem nativeRank_step_lt {initial before after : Tower.Tm 0} (source : NativeAcc built initial)
    (reached : Reaches built initial before)
    (reduction : StrongNormalization.Reduces (Definitions.devPackage dev built.nativeRows) before after) :
    nativeRank built source (reached.tail reduction) < nativeRank built source reached :=
  Acc.rank_lt_of_rel (native_acc_reaches built source reached) reduction

variable (D : Discipline MSig [] ())

inductive Score {initial : Tower.Tm 0} (source : NativeAcc built initial) :
    {before : Branch (BinderCore.keys built.rules) [] () D.Ty} → Certificate built D initial before → Weight → Prop
  | initial : Score source .initial (weight source.rank (evaluationBudget built initial) 3)
  | evaluating {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ())
      (reached : Reaches built initial current)
      (input : Determines K call (NormalEvaluatorGrounding.callCode .evaluate (encodeTm current))) :
      Score source (.evaluating current call reached input)
        (weight (nativeRank built source reached) (evaluationBudget built current) 2)
  | choosing {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (scope : Nat) (reached : Reaches built initial current)
      (input : Determines K (payload built scope) (encodeTm current)) :
      Score source (.choosing current scope reached input)
        (weight (nativeRank built source reached) (evaluationBudget built current) 1)
  | startingScan {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (scope : Nat) (reached : Reaches built initial current)
      (input : Determines K (payload built scope) (encodeTm current)) :
      Score source (.startingScan current scope reached input)
        (weight (nativeRank built source reached) 0 (NormalScannerProgressRank.scanCost current + 5))
  | machine {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (before : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
      (reached : Reaches built initial before) (episode : NormalEvaluatorMachineView.Episode built before code)
      (input : Determines K call code) :
      Score source (.machine before call code reached episode input)
        (weight (nativeRank built source reached) (NormalEvaluatorProgressEpisodes.episode_normalizes built episode).rank 2)
  | machineValue {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
      (head : closedHead code = some activeTag) (input : Determines K call code) :
      Score source (.machineValue call code head input) (weight 0 0 1)
  | scanning (current : Tower.Tm 0) (scope : Nat)
      (inside : Branch (BinderCore.keys built.rules) [] () D.Ty)
      (reached : Reaches built initial current)
      (input : Determines inside.store (payload built scope) (encodeTm current))
      (scanner : NormalScannerCertificates.Certificate built D ⟨0, current⟩ inside)
      {work : Nat} (scored : NormalScannerProgressRank.Score built D scanner work) :
      Score source (.scanning current scope inside reached input scanner)
        (weight (nativeRank built source reached) 0 (work + 4))
  | returningDone {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
      (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
      (input : Determines K datum (encodeTm current)) :
      Score source (.returningDone current datum reached normal input)
        (weight (nativeRank built source reached) 0 3)
  | repliedDone {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
      (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
      (input : Determines K datum (encodeTm current)) :
      Score source (.repliedDone current datum reached normal input)
        (weight (nativeRank built source reached) 0 2)
  | returning {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (datum : Data (BinderCore.keys built.rules) [] ()) (correct : CorrectOutput built initial K datum) :
      Score source (.returning datum correct) (weight 0 0 1)
  | finished {K : List (Constraint (BinderCore.keys built.rules) [] ())}
      (datum : Data (BinderCore.keys built.rules) [] ()) (correct : CorrectOutput built initial K datum) :
      Score source (.finished datum correct) (weight 0 0 0)

theorem certificate_has_score {initial : Tower.Tm 0} (source : NativeAcc built initial)
    {before : Branch (BinderCore.keys built.rules) [] () D.Ty} (known : Certificate built D initial before) :
    ∃ work, Score built D source known work := by
  cases known with
  | initial => exact ⟨_, .initial⟩
  | evaluating current call reached input => exact ⟨_, .evaluating current call reached input⟩
  | choosing current scope reached input => exact ⟨_, .choosing current scope reached input⟩
  | startingScan current scope reached input => exact ⟨_, .startingScan current scope reached input⟩
  | machine before call code reached episode input => exact ⟨_, .machine before call code reached episode input⟩
  | machineValue call code head input => exact ⟨_, .machineValue call code head input⟩
  | scanning current scope inside reached input scanner =>
      obtain ⟨work, scored⟩ := NormalScannerProgressRank.certificate_has_score built D scanner
      exact ⟨_, .scanning current scope inside reached input scanner scored⟩
  | returningDone current datum reached normal input => exact ⟨_, .returningDone current datum reached normal input⟩
  | repliedDone current datum reached normal input => exact ⟨_, .repliedDone current datum reached normal input⟩
  | returning datum correct => exact ⟨_, .returning datum correct⟩
  | finished datum correct => exact ⟨_, .finished datum correct⟩

abbrev Ranked {initial : Tower.Tm 0} (source : NativeAcc built initial)
    (branch : Branch (BinderCore.keys built.rules) [] () D.Ty) (work : Weight) : Prop :=
  ∃ known : Certificate built D initial branch, Score built D source known work

variable (supply : Nat → MClosed) {initial : Tower.Tm 0} (source : NativeAcc built initial)
  {world nextWorld : World (BinderCore.keys built.rules) [] ()}
  {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}

theorem initial_move
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨[], .eval (NormalProgram.query built initial), [], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight source.rank (evaluationBudget built initial) 3 := by
  cases moved with
  | letStart =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      have input := NormalProbeFreshness.determines_include built [] Hosting.initial_live (NormalProgram.code initial)
      refine ⟨_, ⟨.evaluating initial _ .refl input, .evaluating initial _ .refl input⟩, ?_⟩
      exact weight_phase_lt _ _ (by decide : 2 < 3)

theorem choosing_move {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    (current : Tower.Tm 0) (scope : Nat) (reached : Reaches built initial current)
    (input : Determines K (payload built scope) (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (NormalEvaluatorGrounding.bodyAt built .evaluate (payload built scope)),
        [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight (nativeRank built source reached) (evaluationBudget built current) 1 := by
  cases moved with
  | choice =>
      intro child member _
      rcases Multiset.mem_cons.mp member with rfl | later
      · exact ⟨_, ⟨.startingScan current scope reached input, .startingScan current scope reached input⟩,
          weight_episode_lt _ (evaluationBudget_positive built current) _ _⟩
      · rw [Multiset.mem_singleton.mp later]
        have determined := NormalEvaluatorGrounding.determines_seekAt built input
        have episode := NormalEvaluatorMachineView.initial built current
        exact ⟨_, ⟨.machine current _ _ reached episode determined, .machine current _ _ reached episode determined⟩,
          weight_episode_lt _ (episode_lt_evaluationBudget built current) _ _⟩

theorem startingScan_move {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    (current : Tower.Tm 0) (scope : Nat) (reached : Reaches built initial current)
    (input : Determines K (payload built scope) (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (scanBody built D scope), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight (nativeRank built source reached) 0 (NormalScannerProgressRank.scanCost current + 5) := by
  cases moved with
  | letStart =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      let inside : Branch (BinderCore.keys built.rules) [] () D.Ty :=
        ⟨K, .eval (.apply (NormalScanner.scanAt (payload built scope))), [], []⟩
      have scanner : NormalScannerCertificates.Certificate built D ⟨0, current⟩ inside :=
        .scan (payload built scope) ⟨0, current⟩ [] input .done
      have scored : NormalScannerProgressRank.Score built D scanner (NormalScannerProgressRank.scanCost current) :=
        .scan (payload built scope) ⟨0, current⟩ [] input .done .done
      refine ⟨_, ⟨.scanning current scope inside reached input scanner,
        .scanning current scope inside reached input scanner scored⟩, ?_⟩
      exact weight_phase_lt _ _ (by omega)

theorem evaluating_move (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (current : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ())
    (reached : Reaches built initial current)
    (input : Determines K call (NormalEvaluatorGrounding.callCode .evaluate (encodeTm current)))
    (storeBelow : Hosting.StoreBelow world.scope K) (callBelow : Hosting.DependsBelow world.scope call)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.apply call), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight (nativeRank built source reached) (evaluationBudget built current) 2 := by
  intro child member live
  cases moved with
  | apply =>
      obtain ⟨equation, included, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      have same := NormalEvaluatorDriverReadback.evaluate_clause built D world.scope K call (encodeTm current)
        input included live
      subst equation
      have field := NormalEvaluatorGrounding.copied_field_determines built .evaluate world.scope K call
        (encodeTm current) input live
      rw [NormalEvaluatorGrounding.callBranch_shape]
      exact ⟨_, ⟨.choosing current world.scope reached field, .choosing current world.scope reached field⟩,
        weight_phase_lt _ _ (by decide : 1 < 2)⟩
  | unmatched =>
      have noMatch : ∀ equation ∈ (NormalProgram.program built D).equations,
          ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) world.scope) equation.lhs, call)]) :=
        by assumption
      have matched := NormalEvaluatorGrounding.match_live built .evaluate world.scope K call (encodeTm current)
        storeBelow callBelow input
      exact False.elim (noMatch _ (NormalEvaluatorGrounding.clause_mem built D .evaluate) matched)

theorem machine_move (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (before : Tower.Tm 0) (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (reached : Reaches built initial before) (episode : NormalEvaluatorMachineView.Episode built before code)
    (input : Determines K call code)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.apply call), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight (nativeRank built source reached)
        (NormalEvaluatorProgressEpisodes.episode_normalizes built episode).rank 2 := by
  intro child member live
  cases moved with
  | apply =>
      obtain ⟨equation, included, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp member)
      rcases NormalEvaluatorDriverReadback.active_clause built D world.scope K call code input
        (NormalEvaluatorMachineView.head built episode) included live with original | driver
      · obtain ⟨index, _, rfl⟩ := List.mem_map.mp original
        obtain ⟨after, datum, focus, answered, output⟩ := GroundCall.live_callBranch_determines built.rules D
          index world.scope K call code [publicFrame built D] [] input
          (NormalGroundingCompiled.grounded built _ (List.get_mem built.rules index)) live
        have nextEpisode := NormalEvaluatorMachineView.step built episode ⟨index, answered⟩
        change ∃ childWork, Ranked built D source ⟨_,
          (callBranch D world.scope K call [publicFrame built D] [] (BinderCore.embedEquation built.rules index)).focus,
          [publicFrame built D], []⟩ childWork ∧ _
        rw [focus]
        exact ⟨_, ⟨.machine before datum after reached nextEpisode output,
          .machine before datum after reached nextEpisode output⟩,
          weight_episode_lt _ (NormalEvaluatorProgressEpisodes.episode_rank_lt built episode ⟨index, answered⟩) _ _⟩
      · subst equation
        obtain ⟨encoded, shape⟩ := NormalEvaluatorDriverReadback.matching_driver_payload built .resume
          world.scope K call code input live
        obtain ⟨after, reduced, native⟩ := NormalEvaluatorMachineView.resume_view built episode shape.symm
        have resumeInput : Determines K call (NormalEvaluatorGrounding.callCode .resume (encodeTm after)) := by
          rw [← shape, native] at input
          exact input
        have field := NormalEvaluatorGrounding.copied_field_determines built .resume world.scope K call
          (encodeTm after) resumeInput live
        rw [NormalEvaluatorGrounding.callBranch_shape]
        have evaluated := NormalEvaluatorGrounding.determines_callAt built .evaluate field
        exact ⟨_, ⟨.evaluating after (NormalProgram.evaluateAt (payload built world.scope)) (reached.tail reduced) evaluated,
          .evaluating after (NormalProgram.evaluateAt (payload built world.scope)) (reached.tail reduced) evaluated⟩,
          weight_native_lt (nativeRank_step_lt built source reached reduced) _ _ _ _⟩
  | unmatched =>
      rw [Multiset.mem_singleton.mp member]
      exact ⟨_, ⟨.machineValue call code (NormalEvaluatorMachineView.head built episode) input,
        .machineValue call code (NormalEvaluatorMachineView.head built episode) input⟩,
        weight_zero_phase_lt _ _ (by decide : 1 < 2)⟩

theorem machineValue_move {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    (call : Data (BinderCore.keys built.rules) [] ()) (code : MClosed)
    (head : closedHead code = some activeTag) (input : Determines K call code)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value call, [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight 0 0 1 := by
  let result := PublicQuery.result RuntimeSubstitution.rules built.authored
  let site := PublicQuery.site RuntimeSubstitution.rules built.authored
  change Move D (NormalProgram.program built D) supply world
    ⟨K, .value call, [.bindTo site (PublicReadout.pattern result) (.ret result)], []⟩ nextWorld children at moved
  cases moved with
  | letBind =>
      intro child member live
      rw [Multiset.mem_singleton.mp member] at live
      obtain ⟨X, target, assignment, solved⟩ := live
      obtain ⟨old, added⟩ := (models_append assignment _ _).mp solved
      have bound := (models_singleton assignment _).mp added
      dsimp only at bound
      have left := literalHead_instantiate assignment
        (literalHead_instantiate (openAt (BinderCore.keys built.rules) site world.scope)
          (show literalHead (PublicReadout.pattern result) = some doneTag from rfl))
      have original := input.2 target assignment old
      have heads := congrArg literalHead bound
      rw [left, original, literalHead_include, head] at heads
      exact False.elim (active_done_distinct (Option.some.inj heads.symm))

theorem returningDone_move {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
    (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
    (input : Determines K datum (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.ret (NormalProgram.doneAt datum)), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight (nativeRank built source reached) 0 3 := by
  cases moved with
  | ret =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      exact ⟨_, ⟨.repliedDone current datum reached normal input, .repliedDone current datum reached normal input⟩,
        weight_phase_lt _ _ (by decide : 2 < 3)⟩

theorem repliedDone_move {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    (current : Tower.Tm 0) (datum : Data (BinderCore.keys built.rules) [] ())
    (reached : Reaches built initial current) (normal : NormalStructure.Normal built current)
    (input : Determines K datum (encodeTm current))
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .value (NormalProgram.doneAt datum), [publicFrame built D], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight (nativeRank built source reached) 0 2 := by
  let result := PublicQuery.result RuntimeSubstitution.rules built.authored
  let site := PublicQuery.site RuntimeSubstitution.rules built.authored
  change Move D (NormalProgram.program built D) supply world
    ⟨K, .value (NormalProgram.doneAt datum), [.bindTo site (PublicReadout.pattern result) (.ret result)], []⟩
    nextWorld children at moved
  cases moved with
  | letBind =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      have correct : CorrectOutput built initial
          (K ++ [(instantiate (openAt (BinderCore.keys built.rules) site world.scope)
            (PublicReadout.pattern result), NormalProgram.doneAt datum)])
          (instantiate (openAt (BinderCore.keys built.rules) site world.scope) result) := by
        intro value read
        have original := PublicReadout.bind_reads_original K result (NormalProgram.doneAt datum) site world.scope value read
        have reply := ((NormalEvaluatorCertificates.determines_done built input).reads_iff (doneC value)).mp original
        have same : value = encodeTm current := (List.cons.inj (DataEmbedding.nodeC_eq_iff.mp reply).2).1
        exact ⟨current, same, reached, normal⟩
      exact ⟨_, ⟨.returning _ correct, .returning _ correct⟩,
        weight_zero_phase_lt _ _ (by decide : 1 < 2)⟩

theorem returning_move {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    (datum : Data (BinderCore.keys built.rules) [] ()) (correct : CorrectOutput built initial K datum)
    (moved : Move D (NormalProgram.program built D) supply world
      ⟨K, .eval (.ret datum), [], []⟩ nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight 0 0 1 := by
  cases moved with
  | ret =>
      intro child member _
      rw [Multiset.mem_singleton.mp member]
      exact ⟨_, ⟨.finished datum correct, .finished datum correct⟩,
        weight_phase_lt _ _ (by decide : 0 < 1)⟩

theorem scanner_finished_score {outer : NormalChildViews.Child}
    {inside : Branch (BinderCore.keys built.rules) [] () D.Ty}
    {scanner : NormalScannerCertificates.Certificate built D outer inside} {work : Nat}
    (scored : NormalScannerProgressRank.Score built D scanner work) (finished : inside.Finished (D := D)) :
    inside = ⟨inside.store, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))), [], []⟩ ∧ work = 0 := by
  cases scored with
  | scan | start | probing | chain =>
      obtain ⟨_, value, focus⟩ := finished
      cases focus
  | probed | redexReturning | redexValue => cases finished.1
  | normalValue current frames normal outside scored =>
      have empty : frames = [] := finished.1
      subst frames
      refine ⟨rfl, ?_⟩
      cases scored
      rfl

theorem scanning_move (current : Tower.Tm 0) (scope : Nat)
    (inside : Branch (BinderCore.keys built.rules) [] () D.Ty)
    (reached : Reaches built initial current)
    (input : Determines inside.store (payload built scope) (encodeTm current))
    (scanner : NormalScannerCertificates.Certificate built D ⟨0, current⟩ inside)
    {work : Nat} (scored : NormalScannerProgressRank.Score built D scanner work)
    (arrow : Hosting.ArrowBranch (envelop built D scope inside))
    (fresh : NormalScannerReflection.FreshCalls built D world.scope (envelop built D scope inside))
    (moved : Move D (NormalProgram.program built D) supply world (envelop built D scope inside) nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧
      childWork < weight (nativeRank built source reached) 0 (work + 4) := by
  by_cases finished : inside.Finished (D := D)
  · obtain ⟨shape, zero⟩ := scanner_finished_score built D scored finished
    subst work
    have normal := NormalScannerCertificates.finished_normal built D scanner finished
    have actual : Move D (NormalProgram.program built D) supply world
        ⟨inside.store, .value (NormalScanner.marker (fam (BinderCore.keys built.rules))),
          [markerFrame built D scope, publicFrame built D], []⟩ nextWorld children := by
      have changed := moved
      rw [shape] at changed
      simpa only [envelop, ContinuationLift.branch, List.nil_append, List.singleton_append] using changed
    cases actual with
    | letBind =>
        intro child member live
        have output := NormalEvaluatorStore.determines_child D (NormalProgram.program built D) supply moved input member live
        rw [Multiset.mem_singleton.mp member] at output ⊢
        have fixed : instantiate (openAt (BinderCore.keys built.rules) (NormalScanner.site built 1) world.scope)
            (payload built scope) = payload built scope :=
          NormalScannerGrounding.open_copied_datum built scope world.scope 1 (by decide) 0
        simp only [Comp.inst, Comp.mapData, NormalProgram.doneAt,
          NormalScanner.instantiate_nodeAt, List.map_cons, List.map_nil, fixed]
        exact ⟨_, ⟨.returningDone current (payload built scope) reached normal output,
          .returningDone current (payload built scope) reached normal output⟩,
          weight_phase_lt _ _ (by decide : 3 < 0 + 4)⟩
  · let middle := ContinuationLift.branch (markerFrame built D scope) inside
    have middleArrow : Hosting.ArrowBranch middle :=
      NormalScannerEmbedded.arrow_inner built D (publicFrame built D) middle arrow
    have running : ¬ middle.Finished (D := D) := by
      intro done
      have empty := done.1
      simp [middle, ContinuationLift.branch] at empty
    obtain ⟨middleChildren, middleMove, same⟩ := NormalFrameReflection.move D (NormalProgram.program built D)
      supply (publicFrame built D) middleArrow running moved
    have insideArrow := NormalScannerEmbedded.arrow_inner built D (markerFrame built D scope) inside middleArrow
    obtain ⟨innerChildren, innerMove, sameMiddle⟩ := NormalFrameReflection.move D (NormalProgram.program built D)
      supply (markerFrame built D scope) insideArrow finished middleMove
    have innerFresh : NormalScannerReflection.FreshCalls built D world.scope inside := fresh
    intro child member live
    have output := NormalEvaluatorStore.determines_child D (NormalProgram.program built D) supply moved input member live
    rw [same] at member
    obtain ⟨mid, included, rfl⟩ := Multiset.mem_map.mp member
    rw [sameMiddle] at included
    obtain ⟨newInside, made, rfl⟩ := Multiset.mem_map.mp included
    obtain ⟨newWork, ⟨known, newScore⟩, less⟩ :=
      NormalScannerProgressMoves.move built D supply scored innerFresh innerMove newInside made live
    exact ⟨_, ⟨.scanning current scope newInside reached output known,
      .scanning current scope newInside reached output known newScore⟩,
      weight_phase_lt _ _ (by omega)⟩

theorem move_score {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    {known : Certificate built D initial before} {work : Weight}
    (scored : Score built D source known work) (arrow : Hosting.ArrowBranch before)
    (fresh : NormalScannerReflection.FreshCalls built D world.scope before)
    (moved : Move D (NormalProgram.program built D) supply world before nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ranked built D source child childWork ∧ childWork < work := by
  cases scored with
  | initial => exact initial_move built D supply source moved
  | evaluating current call reached input =>
      obtain ⟨storeBelow, callBelow⟩ := fresh _ rfl
      exact evaluating_move built D supply source _ current call reached input storeBelow callBelow moved
  | choosing current scope reached input => exact choosing_move built D supply source current scope reached input moved
  | startingScan current scope reached input => exact startingScan_move built D supply source current scope reached input moved
  | machine before call code reached episode input => exact machine_move built D supply source _ before call code reached episode input moved
  | machineValue call code head input => exact machineValue_move built D supply source call code head input moved
  | scanning current scope inside reached input scanner scored =>
      exact scanning_move built D supply source current scope inside reached input scanner scored arrow fresh moved
  | returningDone current datum reached normal input => exact returningDone_move built D supply source current datum reached normal input moved
  | repliedDone current datum reached normal input => exact repliedDone_move built D supply source current datum reached normal input moved
  | returning datum correct => exact returning_move built D supply source datum correct moved
  | finished => exact False.elim (Move.value_still moved)

def Ready (before : Branch (BinderCore.keys built.rules) [] () D.Ty) (work : Weight) : Prop :=
  Ranked built D source before work ∧ Hosting.ArrowBranch before

theorem ready_decreases (world nextWorld : World (BinderCore.keys built.rules) [] ())
    (before : Branch (BinderCore.keys built.rules) [] () D.Ty)
    (children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)) (work : Weight)
    (ready : Ready built D source before work) (fresh : NormalScannerReflection.FreshCalls built D world.scope before)
    (moved : Move D (NormalProgram.program built D) supply world before nextWorld children) :
    ∀ child ∈ children, Solvable child.store → ∃ childWork, Ready built D source child childWork ∧ childWork < work := by
  obtain ⟨⟨known, scored⟩, arrow⟩ := ready
  intro child member live
  obtain ⟨newWork, ranked, less⟩ := move_score built D supply source scored arrow fresh moved child member live
  exact ⟨newWork, ⟨ranked, NormalFrameTransport.children_arrows D (NormalProgram.program built D) supply
    (NormalProgramFormation.program_arrows built D) arrow moved child member⟩, less⟩

theorem source_normalizes (term : Tower.Tm 0) (normalizing : NativeAcc built term) :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program built D) supply before after)
      (Config.initial (fun _ => 0) (NormalProgram.query built term)) := by
  classical
  let q := NormalProgram.query built (Ty := D.Ty) term
  let current := Config.initial (fun _ => 0) q
  let branch : Branch (BinderCore.keys built.rules) [] () D.Ty := ⟨[], .eval q, [], []⟩
  let initialWork := weight normalizing.rank (evaluationBudget built term) 3
  have prepared : NormalScannerProgress.Labelled built D (Ready built D normalizing) current {initialWork} := by
    refine ⟨{(branch, initialWork)}, ?_, ?_, ?_⟩
    · rw [Multiset.map_singleton]
      change {branch} = Multiset.filter (fun b => Solvable b.store) {branch}
      have live : Solvable branch.store := Hosting.initial_live
      rw [Multiset.filter_singleton, if_pos live]
    · simp
    · intro pair member
      rw [Multiset.mem_singleton] at member
      subst pair
      exact ⟨⟨.initial, .initial⟩, trivial, .inl ⟨q, rfl, NormalProgramFormation.query_arrows built term⟩⟩
  exact NormalScannerProgress.labelled_normalizes built D supply (Ready built D normalizing)
    (ready_decreases built D supply normalizing) (fun _ => 0) q
    (NormalProgramFormation.query_scoped built term) (NormalProgramFormation.query_distinct built term)
    (NormalProgramFormation.query_arrows built term) current .refl {initialWork} prepared

include supply in
theorem native_normalizes (N : Hosting.Nodes MSig [] ()) (term : Tower.Tm 0) (normalizing : NativeAcc built term) :
    Acc (fun after before => (FrontierArrow.target (D := D) N (NormalProgram.program built D)).Step before after)
      (FrontierArrow.initialState (D := D) N (NormalProgram.program built D) (NormalProgram.query built term)) :=
  (NormalPublicTransport.normalization_iff built D supply N term).mp (source_normalizes built D supply term normalizing)

theorem identity_nativeAcc : NativeAcc ExecutionControls.built NormalScanner.lambdaExample := by
  refine .intro _ ?_
  intro output reduced
  exact False.elim (NormalScannerExecutionControls.lambda_normal output reduced)

private theorem lambda_zero_normal {n : Nat} (output : Tower.Tm n) :
    ¬ StrongNormalization.Reduces (Definitions.devPackage [] ExecutionControls.built.nativeRows)
      (.lam (.var 0)) output := by
  intro reduced
  cases reduced with
  | root edge =>
      obtain ⟨_, spine, _, _⟩ :=
        Definitions.dev_root_spine ExecutionControls.empty_checked ExecutionControls.built.native edge
      simp [ConstructorSystem.spineHead] at spine
  | congLam edge => exact ExecutionControls.variable_normal _ _ edge

private theorem beta_body_only (output : Tower.Tm 1)
    (reduced : StrongNormalization.Reduces (Definitions.devPackage [] ExecutionControls.built.nativeRows)
      NormalScannerExecutionControls.betaBody output) : output = .var 0 := by
  cases reduced with
  | betaPi => rfl
  | root edge =>
      obtain ⟨_, spine, _, _⟩ :=
        Definitions.dev_root_spine ExecutionControls.empty_checked ExecutionControls.built.native edge
      simp [NormalScannerExecutionControls.betaBody, ConstructorSystem.spineHead] at spine
  | congAppFun edge => exact False.elim (lambda_zero_normal _ edge)
  | congAppArg edge => exact False.elim (ExecutionControls.variable_normal _ _ edge)

theorem beta_below_binder_only (output : Tower.Tm 0)
    (reduced : StrongNormalization.Reduces (Definitions.devPackage [] ExecutionControls.built.nativeRows)
      NormalScannerExecutionControls.betaBelowBinder output) : output = NormalScanner.lambdaExample := by
  cases reduced with
  | root edge =>
      obtain ⟨_, spine, _, _⟩ :=
        Definitions.dev_root_spine ExecutionControls.empty_checked ExecutionControls.built.native edge
      simp [NormalScannerExecutionControls.betaBelowBinder, ConstructorSystem.spineHead] at spine
  | congLam edge => exact congrArg (fun body : Tower.Tm 1 => (.lam body : Tower.Tm 0)) (beta_body_only _ edge)

theorem beta_below_binder_nativeAcc : NativeAcc ExecutionControls.built NormalScannerExecutionControls.betaBelowBinder := by
  refine .intro _ ?_
  intro output reduced
  rw [beta_below_binder_only output reduced]
  exact identity_nativeAcc

theorem identity_source_normalizes :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program ExecutionControls.built D)
      supply before after)
      (Config.initial (fun _ => 0) (NormalProgram.query ExecutionControls.built NormalScanner.lambdaExample)) :=
  source_normalizes ExecutionControls.built D supply NormalScanner.lambdaExample identity_nativeAcc

theorem beta_below_binder_source_normalizes :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program ExecutionControls.built D)
      supply before after)
      (Config.initial (fun _ => 0)
        (NormalProgram.query ExecutionControls.built NormalScannerExecutionControls.betaBelowBinder)) :=
  source_normalizes ExecutionControls.built D supply NormalScannerExecutionControls.betaBelowBinder beta_below_binder_nativeAcc

theorem beta_below_binder_controller_normalizes (sourceSupply : Nat → MClosed) :
    Acc (fun after before => (FrontierArrow.target (D := untyped.discipline) Hosting.mettaNodes
      (NormalProgram.program ExecutionControls.built untyped.discipline)).Step before after)
      (FrontierArrow.initialState (D := untyped.discipline) Hosting.mettaNodes
        (NormalProgram.program ExecutionControls.built untyped.discipline)
        (NormalProgram.query ExecutionControls.built NormalScannerExecutionControls.betaBelowBinder)) :=
  native_normalizes ExecutionControls.built untyped.discipline sourceSupply Hosting.mettaNodes
    NormalScannerExecutionControls.betaBelowBinder beta_below_binder_nativeAcc

def diagonal : Tower.Tm 0 := .lam (.app (.var 0) (.var 0))
def omega : Tower.Tm 0 := .app diagonal diagonal

theorem omega_reduces_self :
    StrongNormalization.Reduces (Definitions.devPackage [] ExecutionControls.built.nativeRows) omega omega :=
  .betaPi _ _

theorem omega_not_nativeAcc : ¬ NativeAcc ExecutionControls.built omega := by
  intro accessible
  exact (lt_irrefl accessible.rank) (Acc.rank_lt_of_rel accessible omega_reduces_self)

theorem omega_scanner_normalizes :
    Acc (fun after before => SourceLanguage.Step D (NormalProgram.program ExecutionControls.built D)
      supply before after)
      (Config.initial (fun _ => 0) (NormalScanner.query ExecutionControls.built (encodeTm omega))) :=
  NormalScannerProgress.scanner_normalizes ExecutionControls.built D supply omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgress

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgress.source_normalizes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalEvaluatorProgress.native_normalizes
