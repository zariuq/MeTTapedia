import Mathlib.Data.List.Basic

/-!
# Authority-indexed branch restoration

Scheduling and branch-state restoration are independent axes.  This module
defines the weakest owned-image interface needed by either a full-state oracle
or a path-replay realization: capture under an authority key, restore only
under that same key, and refuse foreign or stale images.

`FullImage` is the simple correctness representation.  `ReplayPath` stores a
root state and a forward trail; extending two images from one prefix retains
the same root and gives independent paths.  A native backend may represent the
root by a shared pointer or persistent node, but no physical-sharing or cost
claim is made by these semantic definitions.

This replay trail is not PathMap.  PathMap may accelerate the forward
branching system and its indices; restoration returns to an authorized branch
state.  The two mechanisms may share occurrence-path identities without
sharing an implementation contract.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AuthorizedRestoration

universe uKey uState uImage uStep

/-- Representation-neutral restoration of owned branch images.  The key may
contain owner, machine identity, source revision, or any other authority which
must remain current at restoration time. -/
structure System (Key : Type uKey) (State : Type uState) where
  Image : Type uImage
  capture : Key -> State -> Image
  keyOf : Image -> Key
  restore? : Key -> Image -> Option State
  key_capture : forall key state, keyOf (capture key state) = key
  restore_capture : forall key state,
    restore? key (capture key state) = some state
  restore_foreign : forall expected image,
    expected ≠ keyOf image -> restore? expected image = none

namespace System

variable {Key : Type uKey} {State : Type uState}

/-- A successful restoration certifies that the supplied authority key is the
one carried by the image. -/
theorem key_eq_of_restore?_eq_some
    (system : System.{uKey, uState, uImage} Key State)
    {expected : Key} {image : system.Image} {state : State}
    (restored : system.restore? expected image = some state) :
    expected = system.keyOf image := by
  by_contra foreign
  rw [system.restore_foreign expected image foreign] at restored
  contradiction

end System

/-! ## Full-image reference realization -/

namespace FullImage

variable {Key : Type uKey} {State : Type uState}

def system [DecidableEq Key] : System Key State where
  Image := Key × State
  capture key state := (key, state)
  keyOf image := image.1
  restore? expected image :=
    if expected = image.1 then some image.2 else none
  key_capture _ _ := rfl
  restore_capture key state := by simp
  restore_foreign expected image foreign := by simp [foreign]

end FullImage

/-! ## Forward replay-path realization -/

/-- One authorized root plus a forward replay trail. -/
structure ReplayPath (Key : Type uKey) (State : Type uState)
    (Step : Type uStep) where
  key : Key
  root : State
  trail : List Step
deriving Repr

namespace ReplayPath

variable {Key : Type uKey} {State : Type uState} {Step : Type uStep}

/-- Apply a forward trail from a root state.  Invertibility is deliberately
not required: restoration replays from the root. -/
def replay (applyStep : State -> Step -> State) :
    State -> List Step -> State :=
  List.foldl applyStep

@[simp] theorem replay_nil (applyStep : State -> Step -> State)
    (root : State) :
    replay applyStep root [] = root :=
  rfl

theorem replay_append (applyStep : State -> Step -> State)
    (root : State) (initialTrail suffix : List Step) :
    replay applyStep root (initialTrail ++ suffix) =
      replay applyStep (replay applyStep root initialTrail) suffix := by
  simp [replay]

/-- The authority-indexed replay-path restoration system. -/
def system [DecidableEq Key] (applyStep : State -> Step -> State) :
    System Key State where
  Image := ReplayPath Key State Step
  capture key state := ⟨key, state, []⟩
  keyOf image := image.key
  restore? expected image :=
    if expected = image.key then
      some (replay applyStep image.root image.trail)
    else
      none
  key_capture _ _ := rfl
  restore_capture key state := by simp [replay]
  restore_foreign expected image foreign := by simp [foreign]

/-- Extend an image by a forward suffix while retaining its authority and
root identity. -/
def extend (image : ReplayPath Key State Step) (suffix : List Step) :
    ReplayPath Key State Step :=
  { image with trail := image.trail ++ suffix }

@[simp] theorem extend_key (image : ReplayPath Key State Step)
    (suffix : List Step) :
    (image.extend suffix).key = image.key :=
  rfl

@[simp] theorem extend_root (image : ReplayPath Key State Step)
    (suffix : List Step) :
    (image.extend suffix).root = image.root :=
  rfl

@[simp] theorem extend_trail (image : ReplayPath Key State Step)
    (suffix : List Step) :
    (image.extend suffix).trail = image.trail ++ suffix :=
  rfl

/-- Restoration after path extension is replay of the suffix after the
prefix state. -/
theorem restore?_extend [DecidableEq Key]
    (applyStep : State -> Step -> State)
    (image : ReplayPath Key State Step) (suffix : List Step) :
    (system applyStep).restore? image.key (image.extend suffix) =
      some
        (replay applyStep
          (replay applyStep image.root image.trail) suffix) := by
  simp [system, extend, replay_append]

/-- Two alternative suffixes retain one semantic root while producing
independent branch images. -/
def fork (image : ReplayPath Key State Step)
    (left right : List Step) :
    ReplayPath Key State Step × ReplayPath Key State Step :=
  (image.extend left, image.extend right)

theorem fork_retains_root (image : ReplayPath Key State Step)
    (left right : List Step) :
    (image.fork left right).1.root = image.root /\
      (image.fork left right).2.root = image.root :=
  ⟨rfl, rfl⟩

end ReplayPath

/-! ## Positive and negative controls -/

namespace Canary

abbrev AuthorityKey := Nat × Nat

def addStep : Nat -> Nat -> Nat :=
  Nat.add

def baseImage : ReplayPath AuthorityKey Nat Nat :=
  (ReplayPath.system addStep).capture (3, 11) 10

def branches :
    ReplayPath AuthorityKey Nat Nat × ReplayPath AuthorityKey Nat Nat :=
  baseImage.fork [2, 3] [7]

theorem capture_restores :
    (ReplayPath.system addStep).restore? (3, 11) baseImage = some 10 := by
  rfl

theorem branches_retain_root_and_diverge :
    branches.1.root = 10 /\ branches.2.root = 10 /\
      branches.1.trail = [2, 3] /\ branches.2.trail = [7] := by
  decide

theorem left_branch_restores :
    (ReplayPath.system addStep).restore? (3, 11) branches.1 = some 15 := by
  decide

theorem right_branch_restores :
    (ReplayPath.system addStep).restore? (3, 11) branches.2 = some 17 := by
  decide

/-- A stale revision cannot restore an otherwise well-formed image. -/
theorem stale_revision_is_refused :
    (ReplayPath.system addStep).restore? (3, 12) branches.1 = none := by
  decide

/-- A foreign owner cannot restore the same image either. -/
theorem foreign_owner_is_refused :
    (ReplayPath.system addStep).restore? (4, 11) branches.1 = none := by
  decide

/-- The full-image oracle obeys the same authority boundary. -/
theorem fullImage_foreign_key_is_refused :
    (FullImage.system : System AuthorityKey Nat).restore? (4, 11)
        ((FullImage.system : System AuthorityKey Nat).capture (3, 11) 10) =
      none := by
  decide

end Canary

#print axioms System.key_eq_of_restore?_eq_some
#print axioms ReplayPath.replay_append
#print axioms ReplayPath.restore?_extend
#print axioms ReplayPath.fork_retains_root
#print axioms Canary.capture_restores
#print axioms Canary.branches_retain_root_and_diverge
#print axioms Canary.left_branch_restores
#print axioms Canary.right_branch_restores
#print axioms Canary.stale_revision_is_refused
#print axioms Canary.foreign_owner_is_refused
#print axioms Canary.fullImage_foreign_key_is_refused

end Mettapedia.GSLT.Core.AuthorizedRestoration
