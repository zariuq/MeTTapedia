import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaActivation

/-!
# Cold/warm neutrality of written-call classification

This cache stores a concrete source decision: whether a written head is callable
in a registry. Soundness refers to that decision, not to an assumed evaluator
equivalence. Lookup, warming and dependency-sensitive transfer preserve it.
The resulting decision feeds the actual source call/data rules in context.

This is not a cache for bodies, typing, argument-demand policies or answers.
Changing one of those may change execution while leaving this classification
unchanged. The controls make that boundary explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallCache

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open PeTTaActivation PeTTaContexts Unifying

abbrev Cache := String → Option Bool

def empty : Cache := fun _ => none

def Sound (registry : SpaceSemantics.Program) (cache : Cache) : Prop :=
  ∀ head value, cache head = some value → value = callable registry head

def lookup (registry : SpaceSemantics.Program) (cache : Cache) (head : String) : Bool :=
  match cache head with
  | some value => value
  | none => callable registry head

def warm (registry : SpaceSemantics.Program) (cache : Cache) (head : String) : Cache :=
  Function.update cache head (some (callable registry head))

theorem empty_sound (registry : SpaceSemantics.Program) : Sound registry empty := by
  intro head value found
  cases found

theorem lookup_exact {registry : SpaceSemantics.Program} {cache : Cache}
    (sound : Sound registry cache) (head : String) :
    lookup registry cache head = callable registry head := by
  cases found : cache head with
  | none => simp [lookup, found]
  | some value => simpa [lookup, found] using sound head value found

theorem warm_sound {registry : SpaceSemantics.Program} {cache : Cache}
    (sound : Sound registry cache) (warmed : String) : Sound registry (warm registry cache warmed) := by
  intro head value found
  by_cases same : head = warmed
  · subst head
    simpa [warm, eq_comm] using found
  · simp [warm, same] at found
    exact sound head value found

theorem warm_is_neutral {registry : SpaceSemantics.Program} {cache : Cache}
    (sound : Sound registry cache) (warmed queried : String) :
    lookup registry (warm registry cache warmed) queried = lookup registry cache queried := by
  rw [lookup_exact (warm_sound sound warmed), lookup_exact sound]

/-- A semantic reference invalidator. An implementation may maintain these dependencies incrementally. -/
def transfer (oldRegistry newRegistry : SpaceSemantics.Program) (cache : Cache) : Cache := fun head =>
  if callable oldRegistry head = callable newRegistry head then cache head else none

theorem transfer_sound {oldRegistry newRegistry : SpaceSemantics.Program} {cache : Cache}
    (sound : Sound oldRegistry cache) : Sound newRegistry (transfer oldRegistry newRegistry cache) := by
  intro head value found
  unfold transfer at found
  split at found
  · rename_i unchanged
    exact (sound head value found).trans unchanged
  · cases found

theorem transfer_keeps_unaffected (oldRegistry newRegistry : SpaceSemantics.Program) (cache : Cache)
    (head : String) (unchanged : callable oldRegistry head = callable newRegistry head) :
    transfer oldRegistry newRegistry cache head = cache head := by simp [transfer, unchanged]

theorem transfer_drops_changed (oldRegistry newRegistry : SpaceSemantics.Program) (cache : Cache)
    (head : String) (changed : callable oldRegistry head ≠ callable newRegistry head) :
    transfer oldRegistry newRegistry cache head = none := by simp [transfer, changed]

theorem transferred_lookup_exact {oldRegistry newRegistry : SpaceSemantics.Program} {cache : Cache}
    (sound : Sound oldRegistry cache) (head : String) :
    lookup newRegistry (transfer oldRegistry newRegistry cache) head = callable newRegistry head :=
  lookup_exact (transfer_sound sound) head

/-- A cached positive decision admits the same source call in every supported context. -/
theorem cached_call_in_context (registry : SpaceSemantics.Program) (cache : Cache)
    (sound : Sound registry cache) (context : Context) (base : Configuration) (bindings : Subst)
    (head : String) (arguments : List Atom) (frames : List Frame)
    (ready : frames? bindings context = some frames)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : lookup registry cache head = true) :
    Relation.ReflTransGen (Transition registry)
      (atExpression base bindings (plug context (.expression (.symbol head :: arguments))))
      { base with
        control := .arguments bindings (.function head) arguments [] 0
        frames := frames ++ base.frames } := by
  apply written_call_in_context registry context base bindings head arguments frames ready ordinary
  simpa [lookup_exact sound head] using recognized

/-- The same cache laws apply to installed code when its inventory is part
of the actual registry key. A public-only negative entry cannot stand in for it. -/
theorem cached_current_call_in_context (registry : SpaceSemantics.Program) (cache : Cache)
    (context : Context) (base : Configuration) (bindings : Subst)
    (sound : Sound (codeRegistry registry base.privateCode) cache)
    (head : String) (arguments : List Atom) (frames : List Frame)
    (ready : frames? bindings context = some frames)
    (ordinary : sourceControlForm (.expression (.symbol head :: arguments)) = false)
    (recognized : lookup (codeRegistry registry base.privateCode) cache head = true) :
    Relation.ReflTransGen (Transition registry)
      (atExpression base bindings (plug context (.expression (.symbol head :: arguments))))
      {base with
        control := .arguments bindings (.function head) arguments [] 0
        frames := frames ++ base.frames} := by
  apply current_written_call_in_context registry context base bindings head arguments frames ready ordinary
  simpa [lookup_exact sound head] using recognized

namespace Controls

def registry (body : Atom) : SpaceSemantics.Program :=
  { equations := [⟨"worker", [], body⟩], declarations := [], layout := [.equation] }

def coldRegistry : SpaceSemantics.Program := { equations := [], declarations := [] }
def oldCache : Cache := warm coldRegistry empty "worker"
def changedRegistry : SpaceSemantics.Program := registry (.symbol "new")

theorem stale_negative_changes_classification :
    lookup changedRegistry oldCache "worker" = false ∧
    callable changedRegistry "worker" = true := by decide +kernel

theorem transfer_repairs_stale_negative :
    lookup changedRegistry (transfer coldRegistry changedRegistry oldCache) "worker" = true := by
  decide +kernel

theorem negative_cache_is_not_sound_after_new_definition : ¬ Sound changedRegistry oldCache := by
  intro sound
  have same := lookup_exact sound "worker"
  have observations := stale_negative_changes_classification
  rw [observations.1, observations.2] at same
  cases same

def beforeBodyChange : SpaceSemantics.Program := registry (.symbol "before")
def afterBodyChange : SpaceSemantics.Program := registry (.symbol "after")
def worker : Atom := .expression [.symbol "worker"]

/-- Body changes can preserve callability while changing the program's answer. -/
theorem classification_is_not_an_answer_cache :
    callable beforeBodyChange "worker" = callable afterBodyChange "worker" ∧
    observed (run beforeBodyChange 40 (start (Effects.loaded beforeBodyChange) worker)) =
      .answers [.symbol "before"] ∧
    observed (run afterBodyChange 40 (start (Effects.loaded afterBodyChange) worker)) =
      .answers [.symbol "after"] := by decide +kernel

end Controls
end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCallCache
