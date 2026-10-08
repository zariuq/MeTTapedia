import Mettapedia.Machines.OrderedDependencyBatch

/-!
# Module export, completed effects and profile-specific publication

Registration execution is represented by an ordered event stream. A refusal
terminates that stream; later events have not happened. Default exports keep
tokens private until dependency publication succeeds, but retain completed
effects and a lifetime-qualified refusal. Compatibility exports link first and
publish each completed token, matching the separately observed reference.
Default naming is recorded per importer, independently of transitive links.

These are executable transition-model laws, not a refinement proof for C,
Python, allocation, exception transport or the ownership services.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HEModuleExport

open OrderedDependencyStore OrderedDependencyBatch

universe u v w x

inductive Event (Token : Type u) (Effect : Type v) (Fault : Type w) where
  | token : Token → Event Token Effect Fault
  | effect : Effect → Event Token Effect Fault
  | refuse : Fault → Event Token Effect Fault
  deriving DecidableEq

structure Execution (Token : Type u) (Effect : Type v) (Fault : Type w) where
  tokens : List Token
  effects : List Effect
  fault : Option Fault
  deriving DecidableEq

variable {Token : Type u} {Effect : Type v} {Fault : Type w}

def execute : List (Event Token Effect Fault) → Execution Token Effect Fault
  | [] => ⟨[], [], none⟩
  | .token token :: rest =>
      let tail := execute rest
      { tail with tokens := token :: tail.tokens }
  | .effect effect :: rest =>
      let tail := execute rest
      { tail with effects := effect :: tail.effects }
  | .refuse fault :: _ => ⟨[], [], some fault⟩

/-- A completed prefix composes with the next event stream, but a refused
prefix stops execution rather than executing or replaying its suffix. -/
theorem execute_append (earlier suffix : List (Event Token Effect Fault)) :
    execute (earlier ++ suffix) =
      match (execute earlier).fault with
      | some _ => execute earlier
      | none => ⟨(execute earlier).tokens ++ (execute suffix).tokens,
          (execute earlier).effects ++ (execute suffix).effects, (execute suffix).fault⟩ := by
  induction earlier with
  | nil => simp [execute]
  | cons event rest ih =>
      cases event <;> simp only [List.cons_append, execute] at *
      · rw [ih]
        cases h : (execute rest).fault <;> simp [h]
      · rw [ih]
        cases h : (execute rest).fault <;> simp [h]

theorem refusal_keeps_completed_prefix (earlier suffix : List (Event Token Effect Fault))
    (fault : Fault) (completed : (execute earlier).fault = none) :
    execute (earlier ++ .refuse fault :: suffix) =
      ⟨(execute earlier).tokens, (execute earlier).effects, some fault⟩ := by
  simp [execute_append, completed, execute]

structure Key (size : Nat) where
  reader : Fin size
  source : Fin size
  readerLifetime : Nat
  sourceLifetime : Nat
  deriving DecidableEq

inductive Reason (Fault : Type w) where
  | recordAllocation
  | dependencyAllocation
  | hook : Fault → Reason Fault
  deriving DecidableEq

structure State (Entry : Type x) (Token : Type u) (Effect : Type v)
    (Fault : Type w) (size : Nat) where
  store : Store Entry size
  tokens : Fin size → List Token
  lifetime : Fin size → Nat
  refusals : List (Key size × Reason Fault)
  pending : List (Key size)
  effects : List Effect
  named : List (Key size)

variable {Entry : Type x} {size : Nat}

def key (s : State Entry Token Effect Fault size) (reader source : Fin size) : Key size :=
  ⟨reader, source, s.lifetime reader, s.lifetime source⟩

def lookup (target : Key size) : List (Key size × Reason Fault) → Option (Reason Fault)
  | [] => none
  | (found, reason) :: rest => if found = target then some reason else lookup target rest

def bypass (s : State Entry Token Effect Fault size) (reader source : Fin size) : Prop :=
  reader = source ∨ key s reader source ∈ s.pending ∨ source ∈ (s.store.members reader).deps

instance (s : State Entry Token Effect Fault size) (reader source : Fin size) :
    Decidable (bypass s reader source) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def atomicBypass (s : State Entry Token Effect Fault size) (reader source : Fin size) : Prop :=
  reader = source ∨ key s reader source ∈ s.pending ∨ key s reader source ∈ s.named

instance (s : State Entry Token Effect Fault size) (reader source : Fin size) :
    Decidable (atomicBypass s reader source) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def linkCandidates (s : State Entry Token Effect Fault size) (reader source : Fin size)
    (dependencies : List (Fin size)) : List (Fin size) :=
  if source ∈ (s.store.members reader).deps then [] else source :: dependencies

structure Attempt (Entry : Type x) (Token : Type u) (Effect : Type v)
    (Fault : Type w) (size : Nat) where
  state : State Entry Token Effect Fault size
  fault : Option (Reason Fault)

def rejected (s : State Entry Token Effect Fault size) (reader source : Fin size)
    (execution : Execution Token Effect Fault) (reason : Reason Fault) :
    Attempt Entry Token Effect Fault size :=
  ⟨{ s with
      refusals := (key s reader source, reason) :: s.refusals
      effects := s.effects ++ execution.effects }, some reason⟩

def accepted (s : State Entry Token Effect Fault size) (reader : Fin size)
    (published : Store Entry size) (execution : Execution Token Effect Fault) :
    State Entry Token Effect Fault size :=
  { s with
    store := published
    tokens := Function.update s.tokens reader (s.tokens reader ++ execution.tokens),
    effects := s.effects ++ execution.effects }

def atomic (s : State Entry Token Effect Fault size) (reader source : Fin size)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (recordReserved linksReserved : Bool) : Attempt Entry Token Effect Fault size :=
  if atomicBypass s reader source then ⟨s, none⟩ else
  match lookup (key s reader source) s.refusals with
  | some reason => ⟨s, some reason⟩
  | none =>
    if !recordReserved then ⟨s, some .recordAllocation⟩ else
    let execution := execute events
    match execution.fault with
    | some fault => rejected s reader source execution (.hook fault)
    | none =>
      match tryPublish s.store reader (linkCandidates s reader source dependencies) linksReserved with
      | none => rejected s reader source execution .dependencyAllocation
      | some published => ⟨{ accepted s reader published execution with
          named := key s reader source :: s.named }, none⟩

def compatibility (s : State Entry Token Effect Fault size) (reader source : Fin size)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (linksReserved : Bool) : Attempt Entry Token Effect Fault size :=
  if bypass s reader source then ⟨s, none⟩ else
  match tryPublish s.store reader (source :: dependencies) linksReserved with
  | none => ⟨s, some .dependencyAllocation⟩
  | some published =>
    let execution := execute events
    ⟨accepted s reader published execution, execution.fault.map Reason.hook⟩

theorem atomic_failure_preserves_publication (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (dependencies : List (Fin size))
    (events : List (Event Token Effect Fault)) (recordReserved linksReserved : Bool)
    (failed : (atomic s reader source dependencies events recordReserved linksReserved).fault ≠ none) :
    (atomic s reader source dependencies events recordReserved linksReserved).state.store = s.store ∧
    (atomic s reader source dependencies events recordReserved linksReserved).state.tokens = s.tokens := by
  unfold atomic at failed ⊢
  dsimp only at failed ⊢
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · split
          · exact ⟨rfl, rfl⟩
          · simp_all

theorem retained_refusal_does_not_replay (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (dependencies : List (Fin size))
    (events : List (Event Token Effect Fault)) (reason : Reason Fault)
    (known : lookup (key s reader source) s.refusals = some reason)
    (recordReserved linksReserved : Bool) :
    (atomic s reader source dependencies events recordReserved linksReserved).state = s := by
  by_cases skip : atomicBypass s reader source <;> simp [atomic, skip, known]

theorem hook_failure_retains_effects_and_reason (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (dependencies : List (Fin size))
    (events : List (Event Token Effect Fault)) (fault : Fault)
    (fresh : ¬ atomicBypass s reader source)
    (unknown : lookup (key s reader source) s.refusals = none)
    (failed : (execute events).fault = some fault) (linksReserved : Bool) :
    (atomic s reader source dependencies events true linksReserved).state.effects =
        s.effects ++ (execute events).effects ∧
      lookup (key (atomic s reader source dependencies events true linksReserved).state reader source)
        (atomic s reader source dependencies events true linksReserved).state.refusals =
          some (.hook fault) := by
  simp only [atomic, if_neg fresh, unknown]
  simp [failed, rejected, key, lookup]

def retries (s : State Entry Token Effect Fault size) (reader source : Fin size)
    (dependencies : List (Fin size)) : List (List (Event Token Effect Fault)) →
    State Entry Token Effect Fault size
  | [] => s
  | events :: rest => retries (atomic s reader source dependencies events true true).state
      reader source dependencies rest

theorem retained_refusal_ignores_all_retry_streams (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (dependencies : List (Fin size)) (reason : Reason Fault)
    (known : lookup (key s reader source) s.refusals = some reason)
    (streams : List (List (Event Token Effect Fault))) :
    retries s reader source dependencies streams = s := by
  induction streams with
  | nil => rfl
  | cons events rest ih =>
      rw [retries, retained_refusal_does_not_replay s reader source dependencies events reason known]
      exact ih

theorem record_failure_precedes_effects (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (dependencies : List (Fin size))
    (events : List (Event Token Effect Fault)) (linksReserved : Bool) :
    (atomic s reader source dependencies events false linksReserved).state = s := by
  unfold atomic
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem atomic_preserves_reverse_index (s : State Entry Token Effect Fault size)
    (valid : ObserverInvariant s.store) (reader source : Fin size)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (recordReserved linksReserved : Bool) :
    ObserverInvariant (atomic s reader source dependencies events recordReserved linksReserved).state.store := by
  unfold atomic
  dsimp only
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · split
        · exact valid
        · have preserved := tryPublish_observers s.store valid reader
            (linkCandidates s reader source dependencies) linksReserved
          split
          · exact valid
          · rename_i published equality
            simpa [afterAttempt, equality, accepted] using preserved

theorem atomic_preserves_identity_deduplication (s : State Entry Token Effect Fault size)
    (valid : DistinctDependencies s.store) (reader source : Fin size)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (recordReserved linksReserved : Bool) :
    DistinctDependencies (atomic s reader source dependencies events recordReserved linksReserved).state.store := by
  unfold atomic
  dsimp only
  split
  · exact valid
  · split
    · exact valid
    · split
      · exact valid
      · split
        · exact valid
        · have preserved := tryPublish_distinct s.store valid reader
            (linkCandidates s reader source dependencies) linksReserved
          split
          · exact valid
          · rename_i published equality
            simpa [afterAttempt, equality, accepted] using preserved

theorem compatibility_reservation_failure_precedes_hooks
    (s : State Entry Token Effect Fault size) (reader source : Fin size)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (linksReserved : Bool)
    (refused : tryPublish s.store reader (source :: dependencies) linksReserved = none) :
    (compatibility s reader source dependencies events linksReserved).state = s := by
  by_cases skip : bypass s reader source <;> simp [compatibility, skip, refused]

theorem compatibility_failure_retains_completed_publication
    (s : State Entry Token Effect Fault size) (reader source : Fin size)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (linksReserved : Bool) (published : Store Entry size) (fault : Fault)
    (fresh : ¬ bypass s reader source)
    (linked : tryPublish s.store reader (source :: dependencies) linksReserved = some published)
    (refused : (execute events).fault = some fault) :
    let result := compatibility s reader source dependencies events linksReserved
    result.state.store = published ∧ result.state.tokens reader =
        s.tokens reader ++ (execute events).tokens ∧
      result.state.effects = s.effects ++ (execute events).effects ∧
      result.fault = some (.hook fault) := by
  simp [compatibility, fresh, linked, accepted, refused]

theorem compatibility_preserves_reverse_index (s : State Entry Token Effect Fault size)
    (valid : ObserverInvariant s.store) (reader source : Fin size)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (linksReserved : Bool) :
    ObserverInvariant (compatibility s reader source dependencies events linksReserved).state.store := by
  unfold compatibility
  split
  · exact valid
  · have preserved := tryPublish_observers s.store valid reader (source :: dependencies) linksReserved
    split
    · exact valid
    · rename_i published equality
      simpa [afterAttempt, equality, accepted] using preserved

theorem linked_import_is_noop_in_compatibility (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (linked : source ∈ (s.store.members reader).deps)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (linksReserved : Bool) :
    compatibility s reader source dependencies events linksReserved = ⟨s, none⟩ := by
  have skip : bypass s reader source := .inr (.inr linked)
  simp [compatibility, skip]

theorem completed_naming_does_not_replay (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (named : key s reader source ∈ s.named)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (recordReserved linksReserved : Bool) :
    atomic s reader source dependencies events recordReserved linksReserved = ⟨s, none⟩ := by
  have skip : atomicBypass s reader source := .inr (.inr named)
  simp [atomic, skip]

theorem reentrant_import_is_noop_in_both_profiles (s : State Entry Token Effect Fault size)
    (reader source : Fin size) (pending : key s reader source ∈ s.pending)
    (dependencies : List (Fin size)) (events : List (Event Token Effect Fault))
    (recordReserved linksReserved : Bool) :
    atomic s reader source dependencies events recordReserved linksReserved = ⟨s, none⟩ ∧
      compatibility s reader source dependencies events linksReserved = ⟨s, none⟩ := by
  have skip : bypass s reader source := .inr (.inl pending)
  have atomicSkip : atomicBypass s reader source := .inr (.inl pending)
  simp [atomic, compatibility, skip, atomicSkip]

theorem changed_lifetime_changes_key (s t : State Entry Token Effect Fault size)
    (reader source : Fin size) (changed : s.lifetime reader ≠ t.lifetime reader) :
    key s reader source ≠ key t reader source := by
  intro same
  exact changed (congrArg Key.readerLifetime same)

theorem changed_importer_changes_key (s : State Entry Token Effect Fault size)
    (first second source : Fin size) (different : first ≠ second) :
    key s first source ≠ key s second source := by
  intro same
  exact different (congrArg Key.reader same)

theorem changed_source_lifetime_changes_key (s t : State Entry Token Effect Fault size)
    (reader source : Fin size) (changed : s.lifetime source ≠ t.lifetime source) :
    key s reader source ≠ key t reader source := by
  intro same
  exact changed (congrArg Key.sourceLifetime same)

namespace Controls

def base : State Nat Nat String String 4 :=
  ⟨initial 17 (fun member => if member = 0 then [10] else if member = 1 then [20, 20] else [30]),
    fun _ => [], fun _ => 1, [], [], [], []⟩

def events : List (Event Nat String String) :=
  [.effect "hook", .token 91, .refuse "late refusal", .effect "unexecuted", .token 92]

def failed : State Nat Nat String String 4 := (atomic base 0 1 [2, 1] events true true).state
def compatState : State Nat Nat String String 4 := (compatibility base 0 1 [2, 1] events true).state

theorem failure_preserves_values_but_not_erases_effects :
    query failed.store 0 = [10] ∧ failed.tokens 0 = [] ∧ failed.effects = ["hook"] := by decide

theorem retained_failure_does_not_execute_new_events :
    retries failed 0 1 [2, 1] [[.effect "replay"], [.token 99]] = failed := by
  exact retained_refusal_ignores_all_retry_streams failed 0 1 [2, 1] (.hook "late refusal")
    (by decide) _

theorem compatibility_retains_ordered_partial_publication :
    query compatState.store 0 = [10, 20, 20, 30] ∧ compatState.tokens 0 = [91] ∧
      compatState.effects = ["hook"] ∧ 0 ∈ compatState.store.observers 1 ∧
      (compatState.store.members 0).deps = [1, 2] := by decide

theorem compatibility_repeat_cannot_replay :
    compatibility compatState 0 1 [2, 1] [.effect "replay", .token 99] false = ⟨compatState, none⟩ := by
  exact linked_import_is_noop_in_compatibility compatState 0 1 (by decide) [2, 1] _ false

theorem reservation_failure_has_profile_specific_effects :
    (atomic base 0 1 [] [.effect "hook", .token 91] true false).state.effects = ["hook"] ∧
      (compatibility base 0 1 [] [.effect "hook", .token 91] false).state.effects = [] := by decide

theorem successful_export_preserves_order_and_duplicates :
    let next := (atomic base 0 1 [2, 1] [.token 91, .token 91, .token 92] true true).state
    query next.store 0 = [10, 20, 20, 30] ∧ next.tokens 0 = [91, 91, 92] := by decide

theorem different_importer_can_export :
    (atomic failed 3 1 [] [.effect "new importer", .token 93] true true).state.tokens 3 = [93] ∧
      (atomic failed 3 1 [] [.effect "new importer", .token 93] true true).state.effects =
        ["hook", "new importer"] := by decide

def newLifetime : State Nat Nat String String 4 :=
  { failed with lifetime := Function.update failed.lifetime 0 2 }

theorem new_lifetime_does_not_inherit_refusal :
    (atomic newLifetime 0 1 [] [.effect "new lifetime", .token 94] true true).state.tokens 0 = [94] := by decide

def laterLinked : State Nat Nat String String 4 :=
  { failed with store := publish failed.store 0 [3, 1] }

theorem later_transitive_link_does_not_erase_refusal :
    (atomic laterLinked 0 1 [] [.effect "replay", .token 91] true true).fault =
        some (.hook "late refusal") ∧
      (atomic laterLinked 0 1 [] [.effect "replay", .token 91] true true).state.tokens 0 = [] ∧
      (atomic laterLinked 0 1 [] [.effect "replay", .token 91] true true).state.effects = ["hook"] := by decide

def linkedButUnnamed : State Nat Nat String String 4 :=
  { base with store := publish base.store 0 [3, 1] }

def newlyNamed : State Nat Nat String String 4 :=
  (atomic linkedButUnnamed 0 1 [2] [.effect "first naming", .token 91] true false).state

theorem transitive_link_does_not_replace_lexical_naming :
    newlyNamed.store = linkedButUnnamed.store ∧ newlyNamed.tokens 0 = [91] ∧
      newlyNamed.effects = ["first naming"] ∧
      key newlyNamed 0 1 ∈ newlyNamed.named ∧ newlyNamed.tokens 3 = [] := by
  constructor
  · rfl
  · decide

theorem completed_naming_survives_repeated_imports :
    atomic newlyNamed 0 1 [2] [.effect "replay", .token 99] false false =
        ⟨newlyNamed, none⟩ := by
  exact completed_naming_does_not_replay newlyNamed 0 1 (by decide) [2] _ false false

theorem compatibility_keeps_transitive_link_noop :
    compatibility linkedButUnnamed 0 1 [2] [.effect "first naming", .token 91] false =
        ⟨linkedButUnnamed, none⟩ := by
  exact linked_import_is_noop_in_compatibility linkedButUnnamed 0 1 (by decide) [2] _ false

def addressOnlyLookup (s : State Nat Nat String String 4) (reader source : Fin 4) :
    Option (Reason String) :=
  (s.refusals.find? fun record => record.1.reader == reader && record.1.source == source).map Prod.snd

theorem address_only_lookup_inherits_expired_refusal :
    addressOnlyLookup newLifetime 0 1 = some (.hook "late refusal") ∧
      lookup (key newLifetime 0 1) newLifetime.refusals = none := by decide

theorem rolling_back_effects_changes_observation : failed.effects ≠ base.effects := by decide

end Controls

#print axioms execute_append
#print axioms refusal_keeps_completed_prefix
#print axioms atomic_failure_preserves_publication
#print axioms retained_refusal_does_not_replay
#print axioms hook_failure_retains_effects_and_reason
#print axioms retained_refusal_ignores_all_retry_streams
#print axioms record_failure_precedes_effects
#print axioms atomic_preserves_reverse_index
#print axioms atomic_preserves_identity_deduplication
#print axioms compatibility_reservation_failure_precedes_hooks
#print axioms compatibility_failure_retains_completed_publication
#print axioms compatibility_preserves_reverse_index
#print axioms linked_import_is_noop_in_compatibility
#print axioms completed_naming_does_not_replay
#print axioms reentrant_import_is_noop_in_both_profiles
#print axioms changed_lifetime_changes_key
#print axioms changed_importer_changes_key
#print axioms changed_source_lifetime_changes_key
#print axioms Controls.failure_preserves_values_but_not_erases_effects
#print axioms Controls.retained_failure_does_not_execute_new_events
#print axioms Controls.compatibility_retains_ordered_partial_publication
#print axioms Controls.compatibility_repeat_cannot_replay
#print axioms Controls.reservation_failure_has_profile_specific_effects
#print axioms Controls.successful_export_preserves_order_and_duplicates
#print axioms Controls.different_importer_can_export
#print axioms Controls.new_lifetime_does_not_inherit_refusal
#print axioms Controls.later_transitive_link_does_not_erase_refusal
#print axioms Controls.transitive_link_does_not_replace_lexical_naming
#print axioms Controls.completed_naming_survives_repeated_imports
#print axioms Controls.compatibility_keeps_transitive_link_noop
#print axioms Controls.address_only_lookup_inherits_expired_refusal
#print axioms Controls.rolling_back_effects_changes_observation
end Mettapedia.Machines.HEModuleExport
