import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.History
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedClasses

/-!
# Hosted answer classes on origin-fibred world histories

The answer observer is `Hosting.Alternatives.classAnswer`. Its actual held
executions project to singleton-world paths while retaining the rigid origin
word separately. Endpoint reads use the unique alternative occurrence of a
shaped hosted state. Fresh openings and occurrence aliases may change the
path; they preserve the answer of a fixed origin word.

These laws do not identify distinct equation indices or erase the order of
events inside a history. Delivered prefixes and complete source runs are
treated separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.HostedAnswers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.GSLT.IndexedOperational
open SourceLanguage Hosting Hosting.Alternatives
open RuleSyntax RuleSyntax.Worlds RuleSyntax.RuleOccurrences
open RuleSyntax.StepWeb LiveRules
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
  {κ : Keys S} {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-- The actual singleton world with ambient control rules and shared equation
support. Indexed equation origins remain in the held execution. -/
abbrev world (P : SourceLanguage.Program κ Γ star D.Ty) (state : HostState S) :=
  singleton (controlRules N) (Counted.equationRules N P) state

/-- Actual counted executions of the existing held-rule step. -/
abbrev Run (P : SourceLanguage.Program κ Γ star D.Ty) (q : Comp κ Γ star D.Ty) (count : Nat) :=
  Origins.HeldRuns (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
    (P := controlRules N) (ids := Counted.heldIds P) (code := Counted.heldRule N P)
    (fun _ => ()) (Hosting.start N P q) count

noncomputable def projected (q : Comp κ Γ star D.Ty) {count : Nat} (run : Run N P q count) :=
  Origins.projectRun (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
    (fun _ => ()) (Counted.offers N P) (Hosting.start N P q) count run

noncomputable def history (q : Comp κ Γ star D.Ty) {count : Nat} (run : Run N P q count) :
    ExecutionPath (firings (O := ℕ) (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S))
      (world N P (Hosting.start N P q)) (world N P (projected N q run).val.last) :=
  OriginSupport.worldPath (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
    (fun _ => ()) (Counted.offers N P) run

theorem history_length (q : Comp κ Γ star D.Ty) {count : Nat} (run : Run N P q count) :
    (history N q run).length = count :=
  OriginSupport.worldPath_length (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
    (fun _ => ()) (Counted.offers N P) run

theorem projected_last (q : Comp κ Γ star D.Ty) {count : Nat} (run : Run N P q count)
    {state : HostState S} (last : run.val.last = Counted.heldState N P state) :
    (projected N q run).val.last = state := by
  have rows := OriginSupport.worldPath_rows (Interface.Frames.contextual S)
    (RuleSyntax.Contextual.declarations S) (fun _ => ()) (Counted.offers N P) run
  exact holding_injective (rows.symm.trans last)

/-- The equation rows leave exactly one possible alternative index. -/
theorem shaped_index_unique {state : HostState S} {first second : Nat}
    (left : StepAlone.Shaped N P state first) (right : StepAlone.Shaped N P state second) :
    first = second := by
  have inside : first ∈ state.present := by
    rw [left.present]
    exact Finset.mem_insert_self _ _
  rw [right.present,Finset.mem_insert,Finset.mem_range] at inside
  rcases inside with same | small
  · exact same
  · exact False.elim ((not_lt.mpr left.notRow) small)

/-- The actual final occurrence is recovered from the run and its structural
shape, rather than supplied as an arbitrary answer-reading index. -/
theorem heldFrom_of_pointed_run (q : Comp κ Γ star D.Ty)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {count : Nat} (run : Run N P q count) {state : HostState S} {index : Nat}
    (last : run.val.last = Counted.heldState N P state) (shaped : StepAlone.Shaped N P state index) :
    Counted.HeldFrom N P q (Counted.originsOf N run.val) state index := by
  obtain ⟨actual,port,endpoint,held⟩ := Counted.heldFrom_of_run N q unopened run.val
  have sameState : actual = state := holding_injective (endpoint.symm.trans last)
  subst actual
  have samePort := shaped_index_unique N (Counted.shaped_of_heldFrom N q unopened held) shaped
  subst port
  exact held

/-- A named hosted history gives its actual origin-retaining execution and
its actual world endpoint, with the same number of firings. -/
theorem named_history_world (q : Comp κ Γ star D.Ty) {word : List RuleName}
    {state : HostState S} {index : Nat} (named : NamedFrom N P q word state index) :
    ∃ run : Run N P q word.length,
      Counted.originsOf N run.val = word.map (Counted.origin N) ∧
      run.val.last = Counted.heldState N P state ∧
      world N P (projected N q run).val.last = world N P state ∧
      (history N q run).length = word.length := by
  obtain ⟨actual,last,origins⟩ := Counted.run_of_heldFrom N q (Counted.heldFrom_of_namedFrom N q named)
  have length : actual.word.length = word.length := by
    have lengths := congrArg List.length origins
    simpa only [Counted.originsOf,List.length_map] using lengths
  let run : Run N P q word.length := ⟨actual,length⟩
  exact ⟨run,origins,last,congrArg (world N P) (projected_last N q run last),history_length N q run⟩

/-- The existing class observer is exactly the actual endpoint's reading,
independently of which fresh aliases that named history chose. -/
theorem named_endpoint_answer (q : Comp κ Γ star D.Ty) {word : List RuleName}
    {state : HostState S} {index : Nat} (named : NamedFrom N P q word state index) :
    classAnswer N P q word = stateAnswer N state index := by
  ext value
  constructor
  · rintro ⟨other,port,reached,shown⟩
    rwa [(answer_of_rule_word N q rfl reached named).1] at shown
  · intro shown
    exact ⟨state,index,named,shown⟩

/-- Every supplied singleton-world path from the hosted query is the complete
projected path of an actual named history. Origins are retained separately. -/
theorem world_path_named (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {last : Bag (RuleSyntax.Contextual.Terms S) ℕ}
    (path : ExecutionPath (firings (O := ℕ) (Interface.Frames.contextual S)
      (RuleSyntax.Contextual.declarations S)) (world N P (Hosting.start N P q)) last) :
    ∃ run : Run N P q path.length, HEq (history N q run) path ∧
      ∃ (word : List RuleName) (state : HostState S) (index : Nat),
        Counted.originsOf N run.val = word.map (Counted.origin N) ∧
        run.val.last = Counted.heldState N P state ∧
        NamedFrom N P q word state index ∧ world N P state = last := by
  obtain ⟨run,endpoint,exactPath⟩ := History.worldPath_lifts_exact
    (Interface.Frames.contextual S) (RuleSyntax.Contextual.declarations S)
    (fun _ => ()) (Counted.offers N P) path
  obtain ⟨state,index,lastState,held⟩ := Counted.heldFrom_of_run N q unopened run.val
  obtain ⟨word,origins,named,_⟩ := Counted.named_of_heldFrom N q plainP plainQ unopened held
  refine ⟨run,exactPath,word,state,index,origins.symm,lastState,named,?_⟩
  rw [← projected_last N q run lastState]
  exact endpoint

/-- The existing answer observer is read at the actual projected world and
the unique alternative occurrence of its held execution. -/
theorem classAnswer_world (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (word : List RuleName) (value : Term S Γ star) :
    value ∈ classAnswer N P q word ↔
      ∃ run : Run N P q word.length,
        Counted.originsOf N run.val = word.map (Counted.origin N) ∧
          ∃ (state : HostState S) (index : Nat),
            run.val.last = Counted.heldState N P state ∧ StepAlone.Shaped N P state index ∧
              Shows (fun actual => value ∈ stateAnswer N actual index)
                (world N P (projected N q run).val.last) := by
  rw [Counted.classAnswer_held N q plainP plainQ unopened]
  constructor
  · rintro ⟨state,index,held,shown⟩
    obtain ⟨actual,last,origins⟩ := Counted.run_of_heldFrom N q held
    have length : actual.word.length = word.length := by
      have lengths := congrArg List.length origins
      simpa only [Counted.originsOf,List.length_map] using lengths
    let run : Run N P q word.length := ⟨actual,length⟩
    refine ⟨run,origins,state,index,last,Counted.shaped_of_heldFrom N q unopened held,?_⟩
    rw [projected_last N q run last]
    exact (singleton_shows _ _ state _).mpr shown
  · rintro ⟨run,origins,state,index,last,shaped,shown⟩
    have held := heldFrom_of_pointed_run N q unopened run last shaped
    rw [origins] at held
    refine ⟨state,index,held,?_⟩
    rw [projected_last N q run last] at shown
    exact (singleton_shows _ _ state _).mp shown

/-- Fresh openings, frames and occurrence aliases do not change the answer
of a fixed rigid-origin word. Equation indices are not identified. -/
theorem fresh_alias_readout (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {word : List (Use (CRule S) ℕ)} {first second : HostState S} {firstIndex secondIndex : Nat}
    (left : Counted.HeldFrom N P q word first firstIndex)
    (right : Counted.HeldFrom N P q word second secondIndex) :
    stateAnswer N first firstIndex = stateAnswer N second secondIndex ∧
      (StateFinished N first firstIndex ↔ StateFinished N second secondIndex) := by
  obtain ⟨leftWord,leftOrigins,leftNamed,_⟩ := Counted.named_of_heldFrom N q plainP plainQ unopened left
  obtain ⟨rightWord,rightOrigins,rightNamed,_⟩ := Counted.named_of_heldFrom N q plainP plainQ unopened right
  have same : leftWord = rightWord := List.map_injective_iff.mpr (Counted.origin_injective N)
    (leftOrigins.trans rightOrigins.symm)
  subst rightWord
  exact answer_of_rule_word N q rfl leftNamed rightNamed

/-- One actual named move extends its actual causal history and gives a
one-firing world edge. The prior events are not permuted. -/
theorem named_move_world (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P)
    {before after : World κ Γ star} {branch child : Branch κ Γ star D.Ty} {name : RuleName}
    (move : NamedMove P before branch name after child)
    {word : List RuleName} {state : HostState S} {index fresh : Nat}
    (named : NamedFrom N P q word state index) (represented : Represents N P before.scope branch state index)
    (plain : PlainBranch branch) (live : Solvable child.store) (unused : fresh ∉ state.present) :
    ∃ next : HostState S,
      Counted.HeldFires N P (Counted.origin N name) state index next fresh ∧
        RuleSyntax.Worlds.Fires
          (events (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S))
            (world N P state) (world N P next) ∧
          NamedFrom N P q (word ++ [name]) next fresh ∧ Represents N P after.scope child next fresh := by
  obtain ⟨next,held,rep,_⟩ := Counted.held_of_namedMove N plainP move represented plain live unused
  have fired := Counted.firesNamed_of_heldFires held
  have ordinary := (Hosting.fires_iff_step N P state next).mp (firesNamed_fires N fired)
  exact ⟨next,held,
    (one_world_bisimulation (X := Interface.Frames.contextual S)
      (E := RuleSyntax.Contextual.declarations S) (O := ℕ) (controlRules N) (Counted.equationRules N P)).zig ordinary,
    .snoc named fired,rep⟩

/-- A real source step replaces precisely the witnessed frontier entry.
Every live named child extends every actual history of that entry by its
rigid origin and an actual world firing; the other entries remain in place. -/
theorem tracing_step_world (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P)
    {C C' : Config κ Γ star D.Ty} {L : Multiset (Branch κ Γ star D.Ty × List RuleName)}
    {G : Multiset (List RuleName)} (tracing : Tracing N P q C L G)
    (step : SourceLanguage.Step D P supply C C') :
    ∃ (branch : Branch κ Γ star D.Ty) (word : List RuleName)
      (rest : Multiset (Branch κ Γ star D.Ty × List RuleName))
      (names : List RuleName) (child : RuleName → Branch κ Γ star D.Ty),
      L = (branch,word) ::ₘ rest ∧ names.Nodup ∧
        (∀ name ∈ names, NamedMove P C.world branch name C'.world (child name)) ∧
        (∀ name ∈ names, Solvable (child name).store → ∀ (state : HostState S) (index fresh : Nat),
          NamedFrom N P q word state index → fresh ∉ state.present →
            ∃ next : HostState S,
              Counted.HeldFires N P (Counted.origin N name) state index next fresh ∧
                RuleSyntax.Worlds.Fires
                  (events (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S))
                    (world N P state) (world N P next) ∧
                  NamedFrom N P q (word ++ [name]) next fresh ∧ Represents N P C'.world.scope (child name) next fresh ∧
                  ∃ run : Run N P q (word ++ [name]).length,
                    Counted.originsOf N run.val = (word ++ [name]).map (Counted.origin N) ∧
                    run.val.last = Counted.heldState N P next ∧
                    world N P (projected N q run).val.last = world N P next) ∧
        ((names = [] ∧ Tracing N P q C' rest (word ::ₘ G)) ∨
          (names ≠ [] ∧ Tracing N P q C'
            ((((names : Multiset RuleName).filter fun name => Solvable (child name).store).map
              fun name => (child name,word ++ [name])) + rest) G)) := by
  obtain ⟨branch,word,rest,names,child,split,distinct,moves,nextTracing⟩ :=
    tracing_step_witness N plainP q tracing step
  have member : (branch,word) ∈ L := by
    rw [split]
    exact Multiset.mem_cons_self _ _
  refine ⟨branch,word,rest,names,child,split,distinct,moves,?_,nextTracing⟩
  intro name inside live state index fresh named unused
  obtain ⟨next,held,edge,extended,represented⟩ := named_move_world N q plainP (moves name inside) named
    (tracing.uniform (branch,word) member state index named) (tracing.plain (branch,word) member) live unused
  obtain ⟨run,origins,last,endpoint,_⟩ := named_history_world N q extended
  exact ⟨next,held,edge,extended,represented,run,origins,last,endpoint⟩

/-- At a traced finite cut, every actual live frontier entry has its own
origin-retaining world history. The bag is the existing class observer. -/
theorem delivered_world_bag (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    {L : Multiset (Branch κ Γ star D.Ty × List RuleName)} {G : Multiset (List RuleName)}
    (tracing : Tracing N P q C L G) :
    (∀ x ∈ L, ∃ run : Run N P q x.2.length,
      Counted.originsOf N run.val = x.2.map (Counted.origin N) ∧
        ∃ (state : HostState S) (index : Nat),
          run.val.last = Counted.heldState N P state ∧ Represents N P C.world.scope x.1 state index ∧
            StepAlone.Shaped N P state index ∧
            world N P (projected N q run).val.last = world N P state ∧
            (history N q run).length = x.2.length) ∧
      C.answers (D := D) =
        ((L.map Prod.snd).filter fun word => Counted.FinishedHeldClass N P q (word.map (Counted.origin N))).map
          (classAnswer N P q) := by
  obtain ⟨_,answers⟩ := Counted.delivered_of_tracing N q plainP plainQ unopened tracing
  refine ⟨?_,answers⟩
  intro entry member
  obtain ⟨state,index,named⟩ := tracing.reached entry member
  obtain ⟨run,origins,last,endpoint,length⟩ := named_history_world N q named
  have represented := tracing.uniform entry member state index named
  exact ⟨run,origins,state,index,last,represented,
    ⟨represented.notRow,represented.present,represented.rows⟩,endpoint,length⟩

/-- Every actual finite source run carries the same world-history evidence,
including runs whose frontier is not yet quiescent. -/
theorem delivered_world_prefix (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ (L : Multiset (Branch κ Γ star D.Ty × List RuleName)) (G : Multiset (List RuleName)),
      Tracing N P q C L G ∧
        (∀ x ∈ L, ∃ run : Run N P q x.2.length,
          Counted.originsOf N run.val = x.2.map (Counted.origin N) ∧
            ∃ (state : HostState S) (index : Nat),
              run.val.last = Counted.heldState N P state ∧ Represents N P C.world.scope x.1 state index ∧
                StepAlone.Shaped N P state index ∧
                world N P (projected N q run).val.last = world N P state ∧
                (history N q run).length = x.2.length) ∧
          C.answers (D := D) =
            ((L.map Prod.snd).filter fun word => Counted.FinishedHeldClass N P q (word.map (Counted.origin N))).map
              (classAnswer N P q) := by
  obtain ⟨L,G,tracing⟩ := tracing_runs N spaces q plainP plainQ unopened runs
  exact ⟨L,G,tracing,delivered_world_bag N q plainP plainQ unopened tracing⟩

/-- Terminality concerns the actual singleton firing relation, separately
from support erasure and from management moves between worlds. -/
theorem world_terminal_iff (state : HostState S) :
    (∀ next, ¬ RuleSyntax.Worlds.Fires
      (events (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S)) (world N P state) next) ↔
      Terminal N P state := by
  let comparison := one_world_bisimulation (X := Interface.Frames.contextual S)
    (E := RuleSyntax.Contextual.declarations S) (O := ℕ) (controlRules N) (Counted.equationRules N P)
  constructor
  · intro stopped after moved
    exact stopped _ (comparison.zig ((Hosting.fires_iff_step N P state after).mp moved))
  · intro stopped next moved
    obtain ⟨after,source,_⟩ := comparison.zag moved
    exact stopped after ((Hosting.fires_iff_step N P state after).mpr source)

/-- A complete rigid-origin class reaches an actual terminal world. -/
theorem complete_word_world (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {word : List RuleName}
    (complete : Counted.CompleteHeldRun N P q (word.map (Counted.origin N))) :
    ∃ run : Run N P q word.length,
      Counted.originsOf N run.val = word.map (Counted.origin N) ∧
        ∃ (state : HostState S) (index : Nat),
          run.val.last = Counted.heldState N P state ∧ StepAlone.Shaped N P state index ∧
            NamedFrom N P q word state index ∧
            world N P (projected N q run).val.last = world N P state ∧
            (∀ next, ¬ RuleSyntax.Worlds.Fires
              (events (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S))
                (world N P state) next) := by
  obtain ⟨state,index,named,terminal⟩ :=
    (Counted.completeHeldRun_map_iff N q plainP plainQ unopened word).mp complete
  obtain ⟨run,origins,last,endpoint,_⟩ := named_history_world N q named
  exact ⟨run,origins,state,index,last,
    Counted.shaped_of_heldFrom N q unopened (Counted.heldFrom_of_namedFrom N q named),
    named,endpoint,(world_terminal_iff N state).mpr terminal⟩

/-- Complete-source bags count rigid origin words once. Each counted member
has an actual terminal world history; equal equation schemas stay distinct. -/
theorem complete_world_bag (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ word, M.count word = if Counted.CompleteHeldRun N P q (word.map (Counted.origin N)) then 1 else 0) ∧
        (∀ word ∈ M, ∃ run : Run N P q word.length,
          Counted.originsOf N run.val = word.map (Counted.origin N) ∧
            ∃ (state : HostState S) (index : Nat),
              run.val.last = Counted.heldState N P state ∧ StepAlone.Shaped N P state index ∧
                NamedFrom N P q word state index ∧
                world N P (projected N q run).val.last = world N P state ∧
                (∀ next, ¬ RuleSyntax.Worlds.Fires
                  (events (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S))
                    (world N P state) next)) ∧
          C.answers (D := D) =
            (M.filter fun word => Counted.FinishedHeldClass N P q (word.map (Counted.origin N))).map
              (classAnswer N P q) := by
  obtain ⟨M,counts,_,answers⟩ := Counted.bag_of_held_classes N spaces q plainP plainQ unopened runs quiet
  refine ⟨M,counts,?_,answers⟩
  intro word member
  have positive : 0 < M.count word := Multiset.count_pos.mpr member
  have complete : Counted.CompleteHeldRun N P q (word.map (Counted.origin N)) := by
    by_contra missing
    rw [counts,if_neg missing] at positive
    exact Nat.not_lt_zero _ positive
  exact complete_word_world N q plainP plainQ unopened complete

/-- Two actual completed source executions have the same rigid-origin bag
and the same existing answer observer. Each counted class still has its own
terminal world history. This does not equate their ordered histories. -/
theorem complete_world_bag_determined (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {first second : Config κ Γ star D.Ty}
    (firstRuns : Runs D P supply (Config.initial spaces q) first) (firstQuiet : first.Quiescent P supply)
    (secondRuns : Runs D P supply (Config.initial spaces q) second) (secondQuiet : second.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ word, M.count word = if Counted.CompleteHeldRun N P q (word.map (Counted.origin N)) then 1 else 0) ∧
        (∀ word ∈ M, ∃ run : Run N P q word.length,
          Counted.originsOf N run.val = word.map (Counted.origin N) ∧
            ∃ (state : HostState S) (index : Nat),
              run.val.last = Counted.heldState N P state ∧ StepAlone.Shaped N P state index ∧
                NamedFrom N P q word state index ∧
                world N P (projected N q run).val.last = world N P state ∧
                (∀ next, ¬ RuleSyntax.Worlds.Fires
                  (events (Interface.Frames.contextual S) ℕ (RuleSyntax.Contextual.declarations S))
                    (world N P state) next)) ∧
          first.answers (D := D) =
            (M.filter fun word => Counted.FinishedHeldClass N P q (word.map (Counted.origin N))).map
              (classAnswer N P q) ∧
          second.answers (D := D) =
            (M.filter fun word => Counted.FinishedHeldClass N P q (word.map (Counted.origin N))).map
              (classAnswer N P q) := by
  obtain ⟨M,counts,worlds,firstAnswers⟩ := complete_world_bag N spaces q plainP plainQ unopened firstRuns firstQuiet
  have same := answers_determined N spaces q plainP plainQ unopened firstRuns firstQuiet secondRuns secondQuiet
  exact ⟨M,counts,worlds,firstAnswers,same.symm.trans firstAnswers⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.HostedAnswers
