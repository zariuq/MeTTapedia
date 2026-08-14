import Mettapedia.GSLT.Core.Composition

/-!
# Sparse optional-effect trails

A transactional machine commonly records one logical checkpoint for every
write while carrying an additional effect snapshot only on some writes.  A
dense trail embeds the optional payload in every hot checkpoint.  This module
gives the representation-independent optimization used by compiled GSLT
machines: retain logical checkpoints in one stack and present effect payloads
in a second, cold stack.

The source and sparse machines are defined independently.  Packing is exact,
one-step and multi-step rollback recover the same checkpoints, malformed
sparse states fail closed, and an effect-free trace allocates no cold entries.
The last theorem is the decidable local cost certificate: the optimization is
useful precisely when the presented machine's effect trace is sparse.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanSparseEffectTrail

universe uLogical uEffect

/-- The semantic checkpoint before representation specialization. -/
structure Checkpoint (Logical : Type uLogical) (Effect : Type uEffect) where
  logical : Logical
  effect : Option Effect
  deriving DecidableEq, Repr

/-- The hot checkpoint contains only logical state and one presence bit. -/
structure HotCheckpoint (Logical : Type uLogical) where
  logical : Logical
  effectPresent : Bool
  deriving DecidableEq, Repr

/-- Physical split representation.  Both lists are newest-first stacks. -/
structure SparseTrail (Logical : Type uLogical) (Effect : Type uEffect) where
  hot : List (HotCheckpoint Logical)
  cold : List Effect
  deriving DecidableEq, Repr

def empty : SparseTrail Logical Effect := ⟨[], []⟩

/-- Store every logical checkpoint in the hot trail, but add a cold entry only
when the source checkpoint actually carries an effect. -/
def push (checkpoint : Checkpoint Logical Effect)
    (trail : SparseTrail Logical Effect) : SparseTrail Logical Effect :=
  match checkpoint.effect with
  | none =>
      { hot := ⟨checkpoint.logical, false⟩ :: trail.hot
        cold := trail.cold }
  | some effect =>
      { hot := ⟨checkpoint.logical, true⟩ :: trail.hot
        cold := effect :: trail.cold }

/-- Decode and remove the newest checkpoint.  A presence bit without a cold
payload is rejected rather than interpreted as an absent effect. -/
def pop? (trail : SparseTrail Logical Effect) :
    Option (Checkpoint Logical Effect × SparseTrail Logical Effect) :=
  match trail.hot with
  | [] => none
  | checkpoint :: rest =>
      if checkpoint.effectPresent then
        match trail.cold with
        | [] => none
        | effect :: cold =>
            some (⟨checkpoint.logical, some effect⟩, ⟨rest, cold⟩)
      else
        some (⟨checkpoint.logical, none⟩, ⟨rest, trail.cold⟩)

/-- A freshly pushed checkpoint is recovered exactly, including effect
absence. -/
theorem pop?_push (checkpoint : Checkpoint Logical Effect)
    (trail : SparseTrail Logical Effect) :
    pop? (push checkpoint trail) = some (checkpoint, trail) := by
  cases checkpoint with
  | mk logical effect =>
      cases effect <;> rfl

/-- Compile a semantic checkpoint stack into the sparse physical carrier. -/
def pack : List (Checkpoint Logical Effect) → SparseTrail Logical Effect
  | [] => empty
  | checkpoint :: rest => push checkpoint (pack rest)

/-- Decode both physical stacks, rejecting missing or unconsumed cold
payloads. -/
def unpackAux : List (HotCheckpoint Logical) → List Effect →
    Option (List (Checkpoint Logical Effect))
  | [], [] => some []
  | [], _ :: _ => none
  | checkpoint :: rest, cold =>
      if checkpoint.effectPresent then
        match cold with
        | [] => none
        | effect :: coldRest => do
            let decodedRest ← unpackAux rest coldRest
            some (⟨checkpoint.logical, some effect⟩ :: decodedRest)
      else do
        let decodedRest ← unpackAux rest cold
        some (⟨checkpoint.logical, none⟩ :: decodedRest)

def unpack (trail : SparseTrail Logical Effect) :
    Option (List (Checkpoint Logical Effect)) :=
  unpackAux trail.hot trail.cold

/-- Sparse compilation preserves the complete semantic checkpoint stack. -/
theorem unpack_pack (checkpoints : List (Checkpoint Logical Effect)) :
    unpack (pack checkpoints) = some checkpoints := by
  induction checkpoints with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      unfold unpack at inductionHypothesis
      cases checkpoint with
      | mk logical effect =>
          cases effect <;>
            simp [pack, push, unpack, unpackAux, inductionHypothesis]

/-- A certified realization packages the sparse carrier without making its
physical layout part of the semantic observation. -/
def sparseTrailRealization :
    Mettapedia.GSLT.SimpleRealization
      (List (Checkpoint Logical Effect))
      (SparseTrail Logical Effect)
      (Option (List (Checkpoint Logical Effect))) where
  compile := fun _ checkpoints => pack checkpoints
  observeSource := fun _ checkpoints => some checkpoints
  observeArtifact := fun _ trail => unpack trail
  adequate := fun _ checkpoints => unpack_pack checkpoints

/-- Repeated physical rollback. -/
def rollback? : Nat → SparseTrail Logical Effect →
    Option (SparseTrail Logical Effect)
  | 0, trail => some trail
  | steps + 1, trail => do
      let (_, rest) ← pop? trail
      rollback? steps rest

theorem pack_append (first second : List (Checkpoint Logical Effect)) :
    pack (first ++ second) = first.foldr push (pack second) := by
  induction first with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      simp [pack, inductionHypothesis]

/-- Rolling back a packed prefix restores exactly the packed suffix. -/
theorem rollback?_pack_append
    (leading trailing : List (Checkpoint Logical Effect)) :
    rollback? leading.length (pack (leading ++ trailing)) =
      some (pack trailing) := by
  induction leading with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      simp [pack, rollback?, pop?_push, inductionHypothesis]

/-- A decidable recognizer for the local no-effect fragment. -/
def effectFree : List (Checkpoint Logical Effect) → Bool
  | [] => true
  | checkpoint :: rest => checkpoint.effect.isNone && effectFree rest

/-- Exact number of cold payloads required by a semantic trace. -/
def effectCount : List (Checkpoint Logical Effect) → Nat
  | [] => 0
  | checkpoint :: rest =>
      match checkpoint.effect with
      | none => effectCount rest
      | some _ => effectCount rest + 1

/-- The physical cold-trail length is exactly the semantic effect count. -/
theorem pack_cold_length (checkpoints : List (Checkpoint Logical Effect)) :
    (pack checkpoints).cold.length = effectCount checkpoints := by
  induction checkpoints with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      cases checkpoint with
      | mk logical effect =>
          cases effect <;> simp [pack, push, effectCount, inductionHypothesis]

/-- The recognizer is a complete certificate for zero cold allocation. -/
theorem pack_cold_empty_iff_effectFree
    (checkpoints : List (Checkpoint Logical Effect)) :
    (pack checkpoints).cold = [] ↔ effectFree checkpoints = true := by
  induction checkpoints with
  | nil => simp [pack, empty, effectFree]
  | cons checkpoint rest inductionHypothesis =>
      cases checkpoint with
      | mk logical effect =>
          cases effect <;>
            simp [pack, push, effectFree, inductionHypothesis]

/-! ## Forward arrays with explicit cold-trail watermarks

The executable C carrier stores both arrays oldest-first.  Each hot row keeps
the length of the cold array immediately before its optional payload was
appended.  The following independent carrier makes that representation choice
explicit.  Its decoder checks the watermark rather than trusting it, so a
malformed row fails closed.
-/

/-- C-shaped hot checkpoint: logical state, the preceding cold length, and a
presence bit. -/
structure MarkedHotCheckpoint (Logical : Type uLogical) where
  logical : Logical
  effectMark : Nat
  effectPresent : Bool
  deriving DecidableEq, Repr

/-- Physical forward arrays.  Their last rows are the newest checkpoint and
optional effect, respectively. -/
structure MarkedTrail (Logical : Type uLogical) (Effect : Type uEffect) where
  hot : List (MarkedHotCheckpoint Logical)
  cold : List Effect
  deriving DecidableEq, Repr

def markedEmpty : MarkedTrail Logical Effect := ⟨[], []⟩

/-- Append one semantic checkpoint exactly as the executable carrier does. -/
def appendMarked (checkpoint : Checkpoint Logical Effect)
    (trail : MarkedTrail Logical Effect) : MarkedTrail Logical Effect :=
  let effectMark := trail.cold.length
  match checkpoint.effect with
  | none =>
      { hot := trail.hot ++ [⟨checkpoint.logical, effectMark, false⟩]
        cold := trail.cold }
  | some effect =>
      { hot := trail.hot ++ [⟨checkpoint.logical, effectMark, true⟩]
        cold := trail.cold ++ [effect] }

/-- Decode and remove the newest C-shaped checkpoint.  Both absent and
present rows must point at the exact preceding cold length. -/
def popMarked? (trail : MarkedTrail Logical Effect) :
    Option (Checkpoint Logical Effect × MarkedTrail Logical Effect) :=
  match trail.hot.getLast? with
  | none => none
  | some checkpoint =>
      if checkpoint.effectPresent then
        match trail.cold.getLast? with
        | none => none
        | some effect =>
            if checkpoint.effectMark = trail.cold.dropLast.length then
              some
                (⟨checkpoint.logical, some effect⟩,
                  ⟨trail.hot.dropLast, trail.cold.dropLast⟩)
            else
              none
      else if checkpoint.effectMark = trail.cold.length then
        some
          (⟨checkpoint.logical, none⟩,
            ⟨trail.hot.dropLast, trail.cold⟩)
      else
        none

/-- The explicit watermark created by `appendMarked` is sufficient to recover
the exact semantic checkpoint and the complete preceding carrier. -/
theorem popMarked?_appendMarked
    (checkpoint : Checkpoint Logical Effect)
    (trail : MarkedTrail Logical Effect) :
    popMarked? (appendMarked checkpoint trail) = some (checkpoint, trail) := by
  cases checkpoint with
  | mk logical effect =>
      cases effect <;> simp [appendMarked, popMarked?]

/-- Compile a newest-first semantic stack into the executable oldest-first
arrays. -/
def packMarked : List (Checkpoint Logical Effect) → MarkedTrail Logical Effect
  | [] => markedEmpty
  | checkpoint :: rest => appendMarked checkpoint (packMarked rest)

theorem packMarked_hot_length
    (checkpoints : List (Checkpoint Logical Effect)) :
    (packMarked checkpoints).hot.length = checkpoints.length := by
  induction checkpoints with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      cases checkpoint with
      | mk logical effect =>
          cases effect <;>
            simp [packMarked, appendMarked, inductionHypothesis]

/-- Fuelled total decoder for a physical trail.  At zero rows both arrays must
be empty; surplus cold payloads are rejected. -/
def unpackMarkedN : Nat → MarkedTrail Logical Effect →
    Option (List (Checkpoint Logical Effect))
  | 0, trail =>
      if trail.hot = [] ∧ trail.cold = [] then some [] else none
  | steps + 1, trail => do
      let (checkpoint, rest) ← popMarked? trail
      let checkpoints ← unpackMarkedN steps rest
      some (checkpoint :: checkpoints)

def unpackMarked (trail : MarkedTrail Logical Effect) :
    Option (List (Checkpoint Logical Effect)) :=
  unpackMarkedN trail.hot.length trail

/-- The C-shaped carrier decodes to the same complete ordered semantic stack. -/
theorem unpackMarked_packMarked
    (checkpoints : List (Checkpoint Logical Effect)) :
    unpackMarked (packMarked checkpoints) = some checkpoints := by
  unfold unpackMarked
  rw [packMarked_hot_length]
  induction checkpoints with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      simp [packMarked, unpackMarkedN, popMarked?_appendMarked,
        inductionHypothesis]

/-- Repeated physical rollback for the C-shaped carrier. -/
def rollbackMarked? : Nat → MarkedTrail Logical Effect →
    Option (MarkedTrail Logical Effect)
  | 0, trail => some trail
  | steps + 1, trail => do
      let (_, rest) ← popMarked? trail
      rollbackMarked? steps rest

/-- Rolling back a newest prefix restores the exact older suffix, including
every cold watermark. -/
theorem rollbackMarked?_packMarked_append
    (leading trailing : List (Checkpoint Logical Effect)) :
    rollbackMarked? leading.length (packMarked (leading ++ trailing)) =
      some (packMarked trailing) := by
  induction leading with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      simp [packMarked, rollbackMarked?, popMarked?_appendMarked,
        inductionHypothesis]

/-- The executable cold-array length is still exactly the semantic effect
count. -/
theorem packMarked_cold_length
    (checkpoints : List (Checkpoint Logical Effect)) :
    (packMarked checkpoints).cold.length = effectCount checkpoints := by
  induction checkpoints with
  | nil => rfl
  | cons checkpoint rest inductionHypothesis =>
      cases checkpoint with
      | mk logical effect =>
          cases effect <;>
            simp [packMarked, appendMarked, effectCount,
              inductionHypothesis]

/-- The C-shaped representation and the abstract sparse representation have
the same exact cold-allocation certificate. -/
theorem packMarked_cold_empty_iff_effectFree
    (checkpoints : List (Checkpoint Logical Effect)) :
    (packMarked checkpoints).cold = [] ↔ effectFree checkpoints = true := by
  induction checkpoints with
  | nil => simp [packMarked, markedEmpty, effectFree]
  | cons checkpoint rest inductionHypothesis =>
      cases checkpoint with
      | mk logical effect =>
          cases effect <;>
            simp [packMarked, appendMarked, effectFree,
              inductionHypothesis]

/-! Malformed-watermark controls. -/

/-- An absent row may not point before the current cold suffix. -/
example (logical : Logical) (effect : Effect) :
    popMarked?
        ({ hot := [⟨logical, 0, false⟩], cold := [effect] } :
          MarkedTrail Logical Effect) = none := by
  rfl

/-- A present row may not skip the preceding cold suffix. -/
example (logical : Logical) (first second : Effect) :
    popMarked?
        ({ hot := [⟨logical, 0, true⟩], cold := [first, second] } :
          MarkedTrail Logical Effect) = none := by
  rfl

/-- Surplus cold state is rejected even when there are no hot rows. -/
example (effect : Effect) :
    unpackMarked
        ({ hot := [], cold := [effect] } : MarkedTrail Logical Effect) =
      none := by
  rfl

/-! ## Rejecting controls and independent witnesses -/

/-- Extra cold state is not silently discarded. -/
example (effect : Effect) :
    unpack ({ hot := [], cold := [effect] } : SparseTrail Logical Effect) =
      none := by
  rfl

/-- A claimed effect without its payload fails closed. -/
example (logical : Logical) :
    unpack
        ({ hot := [⟨logical, true⟩], cold := [] } :
          SparseTrail Logical Effect) = none := by
  rfl

private def parserTrace : List (Checkpoint Nat String) :=
  [⟨0, none⟩, ⟨1, none⟩, ⟨2, none⟩]

/-- A parser/action transaction is admitted by the zero-cold recognizer. -/
example : effectFree parserTrace = true ∧ (pack parserTrace).cold = [] := by
  decide

private def ruleMachineTrace : List (Checkpoint String Nat) :=
  [⟨"enter", none⟩, ⟨"emit", some 7⟩, ⟨"leave", none⟩]

/-- A distinct rule-machine transaction uses exactly one optional effect
snapshot and is consequently rejected by the zero-cold recognizer. -/
example : effectFree ruleMachineTrace = false ∧
    (pack ruleMachineTrace).cold.length = 1 := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanSparseEffectTrail
