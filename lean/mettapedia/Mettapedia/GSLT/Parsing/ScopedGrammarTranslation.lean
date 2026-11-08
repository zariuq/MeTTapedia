import Mettapedia.GSLT.Parsing.ScopedGrammarState

/-!
# Transporting scoped grammar effects through a compiler

These laws lift a proved equation for the actual single-entry compiler to
scope stacks, registrations and activation. They do not postulate parser
correctness: the entry equation and the parsing interpretation are separate
obligations of each concrete compiler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ScopedGrammarTranslation

open ScopedGrammarState

variable {Namespace A B R S : Type} [DecidableEq Namespace]

def frame (translate : A → B) (source : Frame (List Namespace) A) : Frame (List Namespace) B :=
  ⟨translate source.value, source.context, source.delimitsLocal⟩

def entry (translate : R → S) : Entry Namespace R → Entry Namespace S
  | .global rule => .global (translate rule)
  | .scoped scopeName rule => .scoped scopeName (translate rule)

def state (values : A → B) (rules : R → S) (source : State Namespace R A) : State Namespace S B where
  frames := source.frames.map (frame values)
  registry := fun scopeName => (source.registry scopeName).map (List.map rules)
  published := source.published.map (entry rules)

variable (values : A → B) (rules : R → S) (sourceAdd : A → R → A) (targetAdd : B → S → B)
  (commutes : ∀ value rule, values (sourceAdd value rule) = targetAdd (values value) (rules rule))

include commutes

theorem foldl_entries (source : List R) (value : A) :
    values (source.foldl sourceAdd value) = (source.map rules).foldl targetAdd (values value) := by
  induction source generalizing value with
  | nil => rfl
  | cons rule rest ih => simp [List.foldl, ih, commutes]

omit [DecidableEq Namespace] in
theorem frames_local (source : List (Frame (List Namespace) A)) (rule : R) :
    (Frames.localUpdate sourceAdd rule source).map (frame values) =
      Frames.localUpdate targetAdd (rules rule) (source.map (frame values)) := by
  induction source with
  | nil => rfl
  | cons top rest ih =>
      cases boundary : top.delimitsLocal <;>
        simp [Frames.localUpdate, boundary, frame, ih, commutes]

omit [DecidableEq Namespace] in
theorem frames_global (source : List (Frame (List Namespace) A)) (rule : R) :
    (Frames.globalUpdate sourceAdd rule source).map (frame values) =
      Frames.globalUpdate targetAdd (rules rule) (source.map (frame values)) := by
  simp [Frames.globalUpdate, List.map_map, frame, commutes]

omit [DecidableEq Namespace] in
theorem localEntry (source : State Namespace R A) (rule : R) :
    state values rules (ScopedGrammarState.localEntry sourceAdd rule source) =
      ScopedGrammarState.localEntry targetAdd (rules rule) (state values rules source) := by
  simp [state, ScopedGrammarState.localEntry, frames_local values rules sourceAdd targetAdd commutes]

theorem register (source : State Namespace R A) (update : Entry Namespace R) :
    state values rules (ScopedGrammarState.register sourceAdd update source) =
      ScopedGrammarState.register targetAdd (entry rules update) (state values rules source) := by
  cases update with
  | global rule =>
      simp [state, entry, ScopedGrammarState.register,
        frames_global values rules sourceAdd targetAdd commutes]
  | «scoped» scopeName rule =>
      simp only [state, entry, ScopedGrammarState.register, List.map_map, List.map_append, List.map_cons, List.map_nil]
      congr 1
      · apply List.map_congr_left
        intro top
        rcases top with ⟨value, context, boundary⟩
        by_cases enabled : scopeName ∈ context
        · simp [frame, active, enabled, commutes]
        · simp [frame, active, enabled]
      · funext name
        split
        · next equality =>
            subst name
            cases source.registry scopeName <;> simp
        · simp_all

omit commutes [DecidableEq Namespace] in
theorem push (source : State Namespace R A) :
    state values rules (ScopedGrammarState.push source) =
      ScopedGrammarState.push (state values rules source) := by
  cases frames : source.frames <;> simp [state, ScopedGrammarState.push, Frames.push, frames, frame]

omit commutes [DecidableEq Namespace] in
theorem pop (source : State Namespace R A) :
    state values rules (ScopedGrammarState.pop source) =
      ScopedGrammarState.pop (state values rules source) := by
  cases frames : source.frames with
  | nil => simp [state, ScopedGrammarState.pop, Frames.pop, frames]
  | cons top rest =>
      cases rest <;> simp [state, ScopedGrammarState.pop, Frames.pop, frames]

theorem activate (resetBoundary : Bool) (scopeName : Namespace) (source : State Namespace R A) :
    state values rules (ScopedGrammarState.activate resetBoundary sourceAdd scopeName source) =
      ScopedGrammarState.activate resetBoundary targetAdd scopeName (state values rules source) := by
  cases frames : source.frames with
  | nil => simp [state, ScopedGrammarState.activate, frames]
  | cons top rest =>
      rcases top with ⟨value, context, boundary⟩
      by_cases enabled : scopeName ∈ context
      · simp [state, ScopedGrammarState.activate, frames, frame, active, enabled]
      · cases registered : source.registry scopeName with
        | none => simp [state, ScopedGrammarState.activate, frames, registered, frame, active, enabled]
        | some entries =>
            simp [state, ScopedGrammarState.activate, frames, registered, frame, active, enabled,
              foldl_entries values rules sourceAdd targetAdd commutes]

omit commutes [DecidableEq Namespace] in
theorem delimit (count : Nat) (source : State Namespace R A) :
    state values rules (ScopedGrammarState.delimit count source) =
      ScopedGrammarState.delimit count (state values rules source) := by
  have frames : ∀ (count : Nat) (stack : List (Frame (List Namespace) A)),
      (Frames.setDelimits count stack).map (frame values) =
        Frames.setDelimits count (stack.map (frame values)) := by
    intro count
    induction count with
    | zero => intro stack; rfl
    | succ count ih =>
        intro stack
        cases stack <;> simp [Frames.setDelimits, frame, ih]
  simp [state, ScopedGrammarState.delimit, frames]

omit commutes [DecidableEq Namespace] in
theorem initial (base : A) :
    state values rules (ScopedGrammarState.initial base : State Namespace R A) =
      ScopedGrammarState.initial (values base) := rfl

theorem registrations (source : State Namespace R A) (updates : List (Entry Namespace R)) :
    state values rules (updates.foldl (fun s e => ScopedGrammarState.register sourceAdd e s) source) =
      (updates.map (entry rules)).foldl (fun s e => ScopedGrammarState.register targetAdd e s)
        (state values rules source) := by
  induction updates generalizing source with
  | nil => rfl
  | cons update rest ih =>
      simp [List.foldl, ih, register values rules sourceAdd targetAdd commutes]

theorem imports (base : A) (updates : List (Entry Namespace R)) :
    state values rules (ScopedGrammarState.imports id sourceAdd base updates) =
      ScopedGrammarState.imports id targetAdd (values base) (updates.map (entry rules)) := by
  have sourceFinish : (fun f : Frame (List Namespace) A => { f with value := id f.value }) = id := rfl
  have targetFinish : (fun f : Frame (List Namespace) B => { f with value := id f.value }) = id := rfl
  simp only [ScopedGrammarState.imports, sourceFinish, targetFinish, List.map_id]
  have mapped := registrations values rules sourceAdd targetAdd commutes (ScopedGrammarState.initial base) updates
  rw [initial] at mapped
  have forget := congrArg (fun s : State Namespace S B => { s with published := [] }) mapped
  exact forget

end Mettapedia.GSLT.Parsing.ScopedGrammarTranslation
