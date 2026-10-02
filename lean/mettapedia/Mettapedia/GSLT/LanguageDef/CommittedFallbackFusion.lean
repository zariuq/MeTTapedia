import Mettapedia.GSLT.LanguageDef.CommittedFallbackNative
import Mettapedia.Machines.IntegerGuardPartition

/-!
# Admitting a choice-free guard prefix

An exhausted pure guard can enter fallback directly. A pure guard producing
one answer can return that answer directly only when its residual terminates
normally and silently, even after an answer consumer changes the world.
`Admitted` records those local provider facts.
Uniqueness of successful answers alone says nothing about a later fault,
performed effect, suspension or divergence.

`direct` is an independent choice-free control decision. Its equality
with the native cursor prefix is proved, not used to define it. The fallback
cursor remains the existing runtime service; arbitrary relational queries are
not replaced with cached Booleans. Answer payloads can include refined stores.
`boolean_erasure_iff` isolates the additional condition for retaining only a
Boolean: a successful answer must leave the caller's payload unchanged.

These are semantic admission laws, not a claim that C code, source parsing,
or a compiler's analysis has already been verified. An implementation must
establish the local admission facts for each fast path. Inspection counts can
change under fusion; the declared observation retains outcomes, answer order,
world and any remaining live cursor, rather than internal polling ticks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CommittedFallbackFusion

open HostCalls (Pull)
open CommittedFallback
open CommittedFallbackNative
open CommittedFallbackNative.Controls (tick run)

variable {Cursor Answer World Fault : Type}

/-- No answers, or one answer with a normally exhausted, effect-free residual.
The residual law quantifies over the world supplied on resumption: consumer
effects or space mutation cannot make the erased suffix productive again.
These are primitive provider equations, not the desired compiler law. -/
def Admitted (queries : Queries Cursor Answer World Fault)
    (cursor : Cursor) (world : World) : Option Answer → Prop
  | none => queries.exact cursor world = (world, .ok .done)
  | some answer => ∃ rest,
      queries.exact cursor world = (world, .ok (.yield answer rest)) ∧
      ∀ laterWorld, queries.exact rest laterWorld = (laterWorld, .ok .done)

/-- Direct control for a qualified guard. It neither polls a provider nor
allocates a query choice. The fallback entry keeps its ordinary live cursor. -/
def direct (queries : Queries Cursor Answer World Fault) (decision : Option Answer)
    (world : World) (answers : List Answer) : Native Cursor Answer World Fault :=
  match decision with
  | none => ⟨some (queries.startFallback world), true, false, none, world, answers⟩
  | some answer => ⟨none, false, false, none, world, answers ++ [answer]⟩

def pollCount (decision : Option Answer) : Nat :=
  match decision with | none => 1 | some _ => 2

/-- The skipped native path exists independently in the source SOS. This
also gives the no-invention direction for each admitted fused transition. -/
theorem direct_reflects_path (queries : Queries Cursor Answer World Fault)
    (cursor : Cursor) (world : World) (answers : List Answer) (decision : Option Answer)
    (admitted : Admitted queries cursor world decision) :
    ∃ finish : State Cursor Answer World Fault,
      Reaches queries ⟨.probing cursor, world, answers⟩ finish ∧
      encode finish = direct queries decision world answers := by
  cases decision with
  | none =>
      exact ⟨⟨.fallback (queries.startFallback world), world, answers⟩,
        Relation.ReflTransGen.single (.probingDone admitted), rfl⟩
  | some answer =>
      obtain ⟨rest, first, exhausted⟩ := admitted
      exact ⟨⟨.done, world, answers ++ [answer]⟩,
        (Relation.ReflTransGen.single (.probingYield first)).tail
          (.committedDone (exhausted world)), rfl⟩

/-- Exact native-prefix equality retains binding payloads, diagnostics,
performed world and fallback residuals, not merely Boolean acceptance. -/
theorem native_prefix_exact (queries : Queries Cursor Answer World Fault)
    (cursor : Cursor) (world : World) (answers : List Answer) (decision : Option Answer)
    (admitted : Admitted queries cursor world decision) :
    run queries (pollCount decision) (encode ⟨.probing cursor, world, answers⟩) =
      direct queries decision world answers := by
  cases decision with
  | none =>
      simp [run, tick, next, encode, pollCount, direct, Admitted] at admitted ⊢
      rw [admitted]
      rfl
  | some answer =>
      obtain ⟨rest, first, exhausted⟩ := admitted
      simp [run, tick, next, encode, pollCount, direct, first, exhausted world]

/-- The success marker is installed before consuming the answer. Even a
consumer that changes the world or returns no observations cannot re-open
fallback or make this admitted residual produce another answer. -/
theorem suffix_inert_after_consumer {Result : Type}
    (queries : Queries Cursor Answer World Fault) (cursor : Cursor)
    (world : World) (answer : Answer) (answers : List Answer)
    (admitted : Admitted queries cursor world (some answer)) :
    ∃ rest, queries.exact cursor world = (world, .ok (.yield answer rest)) ∧
      ∀ consume : Answer → World → World × Result,
        next queries (encode ⟨.committed rest, (consume answer world).1,
          answers ++ [answer]⟩) =
        some (encode ⟨.done, (consume answer world).1, answers ++ [answer]⟩) := by
  obtain ⟨rest, first, exhausted⟩ := admitted
  refine ⟨rest, first, ?_⟩
  intro consume
  simp [next, encode, exhausted (consume answer world).1]

theorem run_add (queries : Queries Cursor Answer World Fault) (first later : Nat)
    (state : Native Cursor Answer World Fault) :
    run queries (first + later) state = run queries later (run queries first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add, run]
  | succ first ih =>
      rw [Nat.succ_add, run, run, ih]

/-- All later native query behavior is retained. In particular, fusion does
not run, suppress or cache the authored fallback's effects or answers. -/
theorem fusion_preserves_resumption (queries : Queries Cursor Answer World Fault)
    (cursor : Cursor) (world : World) (answers : List Answer) (decision : Option Answer)
    (admitted : Admitted queries cursor world decision) (later : Nat) :
    run queries (pollCount decision + later) (encode ⟨.probing cursor, world, answers⟩) =
      run queries later (direct queries decision world answers) := by
  rw [run_add, native_prefix_exact queries cursor world answers decision admitted]

/-- Any observer of the retained endpoint can be substituted, including
effectful/faulting consumers parameterized by its world and binding payloads. -/
theorem fusion_preserves_observation {Observation : Type}
    (observe : Native Cursor Answer World Fault → Observation)
    (queries : Queries Cursor Answer World Fault) (cursor : Cursor) (world : World)
    (answers : List Answer) (decision : Option Answer)
    (admitted : Admitted queries cursor world decision) (later : Nat) :
    observe (run queries (pollCount decision + later)
      (encode ⟨.probing cursor, world, answers⟩)) =
    observe (run queries later (direct queries decision world answers)) :=
  congrArg observe (fusion_preserves_resumption queries cursor world answers decision admitted later)

/-- A Boolean can replace a relational answer precisely when its retained
payload is the caller's original one. One-answer refinements need that payload. -/
theorem boolean_erasure_iff (decision : Option Answer) (caller : Answer) :
    (if decision.isSome then some caller else none) = decision ↔
      ∀ answer, decision = some answer → answer = caller := by
  cases decision <;> simp [eq_comm]

/-- For a pure, binding-preserving guard the existing ordered-branch law
then eliminates the singleton alternative as an ordinary conditional. -/
theorem pure_branch_fusion {Result : Type} (accepts : Bool) (caller : Answer)
    (yes no : Answer → List (Result × Answer)) :
    (Mettapedia.Machines.IntegerGuardPartition.guard accepts caller).flatMap yes ++
      (Mettapedia.Machines.IntegerGuardPartition.guard (!accepts) caller).flatMap no =
    if accepts then yes caller else no caller :=
  Mettapedia.Machines.IntegerGuardPartition.complementary_guard_fusion accepts caller yes no

namespace Controls

def pureQueries : Queries (List (Nat × Nat)) (Nat × Nat) Nat String where
  exact cursor world := (world, .ok (match cursor with
    | [] => .done | answer :: rest => .yield answer rest))
  fallback cursor world := (world, .ok (match cursor with
    | [] => .done | answer :: rest => .yield answer rest))
  startFallback _ := [(99, 0)]

theorem empty_probe_is_admitted : Admitted pureQueries [] 0 none := rfl

theorem one_refinement_is_admitted : Admitted pureQueries [(7, 1)] 0 (some (7, 1)) :=
  ⟨[], rfl, fun _ => rfl⟩

theorem pure_refinement_can_drop_its_cursor :
    run pureQueries 2 (encode ⟨.probing [(7, 1)], 0, []⟩) =
      direct pureQueries (some (7, 1)) 0 [] :=
  native_prefix_exact pureQueries [(7, 1)] 0 [] (some (7, 1)) one_refinement_is_admitted

theorem but_cannot_drop_its_binding :
    (if (some (7, 1) : Option (Nat × Nat)).isSome then some (7, 0) else none) ≠
      some (7, 1) := by decide

theorem repeated_answers_are_not_a_direct_decision :
    ¬ Admitted pureQueries [(7, 1), (7, 1)] 0 (some (7, 1)) := by
  simp [Admitted, pureQueries, Pull.yield.injEq]

def tailFault : Queries Nat (Nat × Nat) Nat String where
  exact cursor world := (world, match cursor with
    | 0 => .ok (.yield (7, 1) 1)
    | _ => .error "fault after the only answer")
  fallback _ world := (world, .ok .done)
  startFallback _ := 2

theorem one_answer_followed_by_fault_is_not_admitted :
    ¬ Admitted tailFault 0 0 (some (7, 1)) := by simp [Admitted, tailFault]

theorem erasing_a_tail_fault_changes_the_observation :
    (run tailFault 2 (encode ⟨.probing 0, 0, []⟩)).error =
      some "fault after the only answer" ∧
    (direct tailFault (some (7, 1)) 0 []).error = none := by decide

def tailEffect : Queries Nat (Nat × Nat) Nat String where
  exact cursor world := match cursor with
    | 0 => (world, .ok (.yield (7, 1) 1))
    | _ => (world + 1, .ok .done)
  fallback _ world := (world, .ok .done)
  startFallback _ := 2

theorem one_answer_followed_by_effect_is_not_admitted :
    ¬ Admitted tailEffect 0 0 (some (7, 1)) := by simp [Admitted, tailEffect]

theorem erasing_a_tail_effect_changes_the_world :
    (run tailEffect 2 (encode ⟨.probing 0, 0, []⟩)).world = 1 ∧
    (direct tailEffect (some (7, 1)) 0 []).world = 0 := by decide

def waiting : Queries Nat (Nat × Nat) Nat String where
  exact cursor world := (world, .ok (match cursor with
    | 0 => .suspend 1
    | 1 => .yield (7, 1) 2
    | _ => .done))
  fallback _ world := (world, .ok .done)
  startFallback _ := 3

theorem suspension_is_neither_rejection_nor_immediate_success :
    ¬ Admitted waiting 0 0 none ∧ ¬ Admitted waiting 0 0 (some (7, 1)) := by
  simp [Admitted, waiting]

theorem retained_suspension_eventually_delivers_the_answer :
    (run waiting 1 (encode ⟨.probing 0, 0, []⟩)) = encode ⟨.probing 1, 0, []⟩ ∧
    (run waiting 3 (encode ⟨.probing 0, 0, []⟩)).answers = [(7, 1)] := by decide

def worldSensitive : Queries Nat (Nat × Nat) Nat String where
  exact cursor world := (world, match cursor with
    | 0 => .ok (.yield (7, 1) 1)
    | _ => if world = 0 then .ok .done else .error "consumer changed the space")
  fallback _ world := (world, .ok .done)
  startFallback _ := 2

/-- The initial two polls appear pure and complete. That is not an admission
certificate when a consumer can intervene between the yield and the last poll. -/
theorem entry_world_only_is_insufficient :
    worldSensitive.exact 0 0 = (0, .ok (.yield (7, 1) 1)) ∧
    worldSensitive.exact 1 0 = (0, .ok .done) ∧
    worldSensitive.exact 1 1 = (1, .error "consumer changed the space") := ⟨rfl, rfl, rfl⟩

theorem world_sensitive_residual_is_not_admitted :
    ¬ Admitted worldSensitive 0 0 (some (7, 1)) := by
  rintro ⟨rest, first, exhausted⟩
  have rest_eq : rest = 1 := by simpa [worldSensitive, eq_comm] using first
  subst rest
  have impossible := exhausted 1
  simp [worldSensitive] at impossible

end Controls

end Mettapedia.GSLT.LanguageDef.CommittedFallbackFusion
