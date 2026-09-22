import Mettapedia.Languages.MeTTa.TermView
import Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-!
# Demanded paths through borrowed term representations

The path reader distinguishes an unknown variable from a proven absent child.
It observes one constructor at a time, without forcing siblings. Its naturality
law specializes to the existing source/environment cursors. This is a semantic
model; the C binding resolver and its lifetime discipline need separate tests.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.CursorPathObservation

open Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
open Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
open Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation
open TermViewCompilation

universe u v

inductive Observation (Value : Type u) where
  | unknown
  | absent
  | found (value : Value)
  deriving DecidableEq

def Observation.map {A : Type u} {B : Type v} (f : A → B) :
    Observation A → Observation B
  | .unknown => .unknown
  | .absent => .absent
  | .found value => .found (f value)

/-- A path reaching a variable is unknown, even when further children were
requested. An absent child is evidence obtained from a known constructor. -/
def readPath {A : Type u} (out : A → TermLayer A) :
    List Nat → A → Observation A
  | [], value => match out value with
      | .variable _ => .unknown
      | _ => .found value
  | index :: rest, value => match out value with
      | .variable _ => .unknown
      | .application _ children => match children[index]? with
          | none => .absent
          | some child => readPath out rest child
      | _ => .absent

/-- A layer-preserving representation map preserves every finite path
observation, including the distinction between unavailable and absent. -/
theorem readPath_natural {A : Type u} {B : Type v}
    (outA : A → TermLayer A) (outB : B → TermLayer B) (denote : A → B)
    (layer_exact : ∀ value, (outA value).map denote = outB (denote value))
    (path : List Nat) (value : A) :
    (readPath outA path value).map denote = readPath outB path (denote value) := by
  induction path generalizing value with
  | nil =>
      have exact := layer_exact value
      cases observed : outA value <;>
        simp only [observed, TermLayer.map] at exact <;>
        simp [readPath, observed, ← exact, Observation.map]
  | cons index rest ih =>
      have exact := layer_exact value
      cases observed : outA value <;>
        simp only [observed, TermLayer.map] at exact <;>
        simp only [readPath, observed, ← exact, Observation.map]
      case application head children =>
        simp only [List.getElem?_map]
        cases selected : children[index]? with
        | none => rfl
        | some child => simpa [Observation.map] using ih child

/-- Borrowed source/environment traversal commutes with complete forcing. -/
theorem cursor_readPath_exact {Owner Revision Occurrence Plan : Type}
    (cursor : Cursor Owner Revision Occurrence Plan) (path : List Nat) :
    (readPath Cursor.out path cursor).map Cursor.denote =
      readPath outOpen path cursor.denote :=
  readPath_natural Cursor.out outOpen Cursor.denote Cursor.out_exact path cursor

/-- An observer of a finite collection of demanded paths can use either
representation. The list retains repeated observations and their order. -/
theorem cursor_observe_paths {Owner Revision Occurrence Plan Result : Type}
    (cursor : Cursor Owner Revision Occurrence Plan) (paths : List (List Nat))
    (observe : List (Observation OpenTerm) → Result) :
    observe (paths.map (fun path =>
      (readPath Cursor.out path cursor).map Cursor.denote)) =
    observe (paths.map (fun path => readPath outOpen path cursor.denote)) := by
  congr 1
  apply List.map_congr_left
  intro path _
  exact cursor_readPath_exact cursor path

/-! A nonlinear constraint compares observations of two subtrees. Its
refutation is a conflict on a demanded path, never the identity of the
borrowed source pointer or the printed name of an unresolved variable. -/

private abbrev Shaped := Mettapedia.GSLT.LanguageDef.MatchDecisionContract.Shaped.Obs

/-- A rigid layer key retains literal values, constructor identity and arity.
Variable layers supply no key; descendants are observed on their own paths. -/
def rigidLayer {A : Type u} (layer : TermLayer A) : Option (TermLayer Unit) :=
  match layer with
  | .variable _ => none
  | other => some (other.map (fun _ => ()))

theorem rigidLayer_map {A : Type u} {B : Type v}
    (f : A → B) (layer : TermLayer A) :
    rigidLayer (layer.map f) = rigidLayer layer := by
  cases layer <;> simp [rigidLayer, TermLayer.map, List.map_map, Function.comp_def]

def rigidObservation {A : Type u} (out : A → TermLayer A) :
    Observation A → Shaped (TermLayer Unit)
  | .unknown => .unknown
  | .absent => .absent
  | .found value => match rigidLayer (out value) with
      | none => .unknown
      | some key => .present key

theorem rigidObservation_map {A : Type u} {B : Type v}
    (outA : A → TermLayer A) (outB : B → TermLayer B) (denote : A → B)
    (exact : ∀ value, (outA value).map denote = outB (denote value))
    (observation : Observation A) :
    rigidObservation outB (observation.map denote) =
      rigidObservation outA observation := by
  cases observation with
  | unknown => rfl
  | absent => rfl
  | found value => simp [Observation.map, rigidObservation, ← exact value, rigidLayer_map]

def rigidAt {A : Type u} (out : A → TermLayer A) (path : List Nat) (value : A) :
    Shaped (TermLayer Unit) := rigidObservation out (readPath out path value)

theorem rigidAt_natural {A : Type u} {B : Type v}
    (outA : A → TermLayer A) (outB : B → TermLayer B) (denote : A → B)
    (exact : ∀ value, (outA value).map denote = outB (denote value))
    (path : List Nat) (value : A) :
    rigidAt outA path value = rigidAt outB path (denote value) := by
  unfold rigidAt
  rw [← readPath_natural outA outB denote exact path value]
  exact (rigidObservation_map outA outB denote exact _).symm

def refutesPaths {A : Type u} (out : A → TermLayer A)
    (paths : List (List Nat)) (left right : A) : Bool :=
  paths.any fun path =>
    Mettapedia.GSLT.LanguageDef.MatchDecisionContract.Shaped.Obs.conflictB
      (rigidAt out path left) (rigidAt out path right)

/-- The actual source/environment cursor and full forcing give identical
finite-path refutations, including unknown variables and absent children. -/
theorem cursor_refutesPaths_exact {Owner Revision Occurrence Plan : Type}
    (paths : List (List Nat)) (left right : Cursor Owner Revision Occurrence Plan) :
    refutesPaths Cursor.out paths left right =
      refutesPaths outOpen paths left.denote right.denote := by
  unfold refutesPaths
  congr 1
  funext path
  rw [rigidAt_natural Cursor.out outOpen Cursor.denote Cursor.out_exact,
      rigidAt_natural Cursor.out outOpen Cursor.denote Cursor.out_exact]

/-- A reported conflict excludes every common realization of the observed
subtrees, rather than merely asserting their current syntactic inequality. -/
theorem refutesPaths_no_common_realization {A : Type u}
    (out : A → TermLayer A) (paths : List (List Nat)) (left right : A)
    (refuted : refutesPaths out paths left right = true) :
    ¬ ∃ term,
      Mettapedia.GSLT.LanguageDef.MatchDecisionContract.Shaped.Realizes term
        (fun path => rigidAt out path left) ∧
      Mettapedia.GSLT.LanguageDef.MatchDecisionContract.Shaped.Realizes term
        (fun path => rigidAt out path right) := by
  obtain ⟨path, _, conflict⟩ := List.any_eq_true.mp refuted
  rintro ⟨term, realizesLeft, realizesRight⟩
  exact Mettapedia.GSLT.LanguageDef.MatchDecisionContract.Shaped.Obs.conflictB_sound
    conflict (realizesLeft path) (realizesRight path)

example : refutesPaths outOpen [[0]]
    (.application [102] (.cons (.integer 1) .nil))
    (.application [102] (.cons (.integer 2) .nil)) = true := rfl

example : refutesPaths outOpen [[0]]
    (.application [102] (.cons (.variable ⟨7, 1⟩) .nil))
    (.application [102] (.cons (.integer 2) .nil)) = false := rfl

example : readPath outOpen [3] (.variable ⟨7, 1⟩) = .unknown := rfl
example : readPath outOpen [3] (.integer 42) = .absent := rfl
example : readPath outOpen [] (.integer 42) = .found (.integer 42) := rfl

end Mettapedia.Languages.MeTTa.CursorPathObservation
