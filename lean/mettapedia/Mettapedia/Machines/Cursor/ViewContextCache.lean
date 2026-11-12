import Mettapedia.Machines.Cursor.PartialViewIndex

/-!
# An observation cache is indexed by its interpretation

Logical list reading and inspection of a tagged encoding are distinct
observations of the same stored carrier. Sharing a node identity does not
license sharing facts across those modes. This supplies a concrete negative
control for cache keys that omit their semantic descriptor.

The encoded interpretation below is an explicit finite test profile, not a
claim that it is CeTTa's complete quote/closure semantics. Actual boundaries
may choose different views for different children. Their descriptor and
source dependencies belong to the observation key or its enclosing scope.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ViewContextCache

open SemanticTermView

def encoded (value : Stored) : Term :=
  match value with
  | .rigid label => .rigid label
  | .var name => .var name
  | .cell first rest =>
      .pair (.rigid (.opaque 0 0))
        (.pair (encoded first) (.pair (encoded rest) (.rigid (.ending .expression))))
  | .block items rest =>
      (items.attach.map fun item => encoded item.val).foldr Term.pair (encoded rest)
termination_by sizeOf value
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    have smaller := List.sizeOf_lt_of_mem item.property
    omega

inductive Mode where
  | logical
  | encoded
  deriving DecidableEq, Repr

def meaning : Mode → Stored → Term
  | .logical, value => value.denote
  | .encoded, value => encoded value

def observation (mode : Mode) (value : Stored) (path : Path) : Observation :=
  project (meaning mode value) path

structure Entry where
  mode : Mode
  fact : Observation

/-- A table may partition entries by descriptor instead of performing this
comparison for every row; the law is about permitted reuse, not a mandated
per-candidate check. -/
def lookup (mode : Mode) (entry : Entry) : Option Observation :=
  if entry.mode = mode then some entry.fact else none

theorem lookup_sound (mode : Mode) (value : Stored) (path : Path) (entry : Entry)
    (valid : entry.fact = observation entry.mode value path) (fact : Observation)
    (found : lookup mode entry = some fact) : fact = observation mode value path := by
  by_cases same : entry.mode = mode
  · simpa [lookup, same, valid] using found.symm
  · simp [lookup, same] at found

theorem mode_miss_does_not_refute (requested : Mode) (entry : Entry)
    (different : entry.mode ≠ requested) (query : Observation) :
    PartialViewIndex.permits query (lookup requested entry) = true := by
  simp [lookup, different, PartialViewIndex.permits]

namespace Controls

open SemanticTermView.Controls

def encodedHead : Entry := ⟨.encoded, observation .encoded cellForm [.first]⟩

theorem same_carrier_different_observation :
    observation .logical cellForm [.first] = .rigid (.symbol 3) ∧
      observation .encoded cellForm [.first] = .rigid (.opaque 0 0) := by
  simp [observation, meaning, encoded, cellForm, value, Stored.denote, project]

/-- Reusing the encoded fact as a logical fact would reject a genuine
match between a flat sequence and its cell representation. -/
theorem missing_mode_can_drop_a_match :
    Unifies arrayForm.denote cellForm.denote ∧
      PartialViewIndex.permits (observation .logical arrayForm [.first])
        (some encodedHead.fact) = false ∧
      PartialViewIndex.permits (observation .logical arrayForm [.first])
        (lookup .logical encodedHead) = true := by
  refine ⟨⟨Term.var, Term.var, congrArg (substitute Term.var) same_value_different_storage⟩, ?_, ?_⟩
  · simp [PartialViewIndex.permits, encodedHead, observation, meaning, encoded, arrayForm,
      flat, cellForm, value, denote_block, Stored.denote, project, compatible]
  · exact mode_miss_does_not_refute _ _ (by decide) _

theorem residual_position_also_matters :
    observe (.segment [.rigid (.symbol 3), .rigid (.symbol 4)] exprEnd) [.first] =
      .rigid (.symbol 3) ∧
    observe (.segment [.rigid (.symbol 4)] exprEnd) [.first] = .rigid (.symbol 4) := by
  rw [observe_correct, observe_correct]
  simp [Focus.denote, Stored.denote, project]

end Controls

end Mettapedia.Machines.Cursor.ViewContextCache
