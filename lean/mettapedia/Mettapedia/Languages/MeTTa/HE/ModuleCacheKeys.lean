import Mettapedia.Languages.MeTTa.HE.ModuleInvalidation
import Mettapedia.Machines.OrderedDependencyCacheKeys

/-!
# Read stamps as cache keys for HE module observations

The finite store's read stamp is a sound key for the ordered HE module
observation and for subject-specific annotation lookups, on the points of one
run of the store's update algorithm. Soundness is derived from the store's
notifications, through the adapter that realizes the HE module view by the
finite query. A revision without the module identity is not a key.

This is an adapter theorem for the model, not a refinement proof for C
execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ModuleCacheKeys

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines
open Mettapedia.Machines.OrderedDependencyStore
open Mettapedia.Languages.MeTTa.HE.ModuleInvalidation
open Mettapedia.GSLT.Dynamics.MemoizationObserver (SoundKey)
open Mettapedia.GSLT.Dynamics.CacheCoherence (runAt)
open Mettapedia.GSLT.Core.NonFactorization

variable {size : Nat}

/-- **The read stamp is a sound key for the HE module observation.** -/
theorem readStamp_soundKey_module (origin : Store Atom size) (holds : ObserverInvariant origin)
    (actions : List (Action Atom size)) :
    SoundKey
      (fun point : Nat × Fin size => readStamp (runAt step origin actions point.1) point.2)
      (fun point => (moduleNode (runAt step origin actions point.1) point.2).view
        (ownStore (runAt step origin actions point.1))) := by
  intro first second same
  dsimp only
  rw [← finite_query_realizes_module_observation, ← finite_query_realizes_module_observation]
  exact OrderedDependencyCacheKeys.readStamp_soundKey_run origin holds actions first second same

/-- **The read stamp is a sound key for annotation lookups.** -/
theorem readStamp_soundKey_annotations (origin : Store Atom size)
    (holds : ObserverInvariant origin) (actions : List (Action Atom size)) (subject : Atom) :
    SoundKey
      (fun point : Nat × Fin size => readStamp (runAt step origin actions point.1) point.2)
      (fun point => getAnnotatedTypes ((moduleNode (runAt step origin actions point.1)
        point.2).toSpace (ownStore (runAt step origin actions point.1))) subject) := by
  intro first second same
  have equal := readStamp_soundKey_module origin holds actions first second same
  exact congrArg (fun atoms => getAnnotatedTypes ⟨atoms⟩ subject) equal

namespace Controls

/-- Two modules: the first is empty, the second holds one symbol. -/
def twoModules : Store Atom 2 :=
  initial 11 fun source => if source = 0 then [] else [.symbol "a"]

def moduleView (point : Fin 2) : List Atom :=
  (moduleNode twoModules point).view (ownStore twoModules)

/-- Positive: the stamp is sound along a concrete run. -/
theorem twoModules_sound :
    SoundKey
      (fun point : Nat × Fin 2 =>
        readStamp (runAt step twoModules [.link 0 1, .append 1 [.symbol "b"]] point.1) point.2)
      (fun point => (moduleNode (runAt step twoModules [.link 0 1, .append 1 [.symbol "b"]]
        point.1) point.2).view
          (ownStore (runAt step twoModules [.link 0 1, .append 1 [.symbol "b"]] point.1))) :=
  readStamp_soundKey_module twoModules (initial_observers _ _) _

/-- **A revision without the module is not a key**: both modules are at
revision zero with different observations. -/
def revisionOnlyFiber :
    NonTrivialFiber (fun point : Fin 2 => (twoModules.members point).revision) moduleView where
  left := 0
  right := 1
  sameShadow := rfl
  differentValue := by
    simp only [moduleView, module_observation_eq, view, twoModules, initial]
    simp

theorem revision_without_module_not_key :
    ¬ SoundKey (fun point : Fin 2 => (twoModules.members point).revision) moduleView :=
  fun sound => revisionOnlyFiber.differentValue (sound _ _ revisionOnlyFiber.sameShadow)

end Controls

#print axioms readStamp_soundKey_module
#print axioms readStamp_soundKey_annotations
#print axioms Controls.twoModules_sound
#print axioms Controls.revision_without_module_not_key

end Mettapedia.Languages.MeTTa.HE.ModuleCacheKeys
