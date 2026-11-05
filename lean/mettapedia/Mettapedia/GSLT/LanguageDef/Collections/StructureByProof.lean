import Mettapedia.GSLT.LanguageDef.Collections.Presentations
import Mettapedia.Algebra.Collections.FoldRespect
import Mathlib.Tactic.Ring

/-!
# Structure found by proof: recognized recursions, open tails, and the limit of shape

A MeTTa program declares no datatypes. Its terms are atoms, and a chain of
cells of one constructor family is a spine whatever program built it
(`Presentations.Family.equivCanonical`), so storing it as one is sound with
no evidence at all. What needs evidence is replacing the program's own
evaluation by a native one, and storing a quotient.

* **A recognized structural recursion** is a function whose answers on a cell
  are its answers on the rest with one step applied, the step reading the
  cell's field and the answer's bindings (`Recognized`). Its answers on any
  term are the answers on the end of the maximal spine, each mapped by the
  right fold of the steps (`Recognized.answers_spine`). The end is evaluated
  by the program, so the law holds for open and improper ends as well, and for
  every bag of answers there: a native walk over the spine, with one call of
  the interpreter at the end, has exactly the program's answers.
* **Open tails.** The answers of a spine with any end are the answers of the
  end mapped by the fold of the known prefix (`Recognized.answers_build`).
  When unification binds the end to a further spine, the prefix's fold
  composes with the new one (`Recognized.answers_extend`). For affine steps
  `b ↦ e f + B · b`, which cover lengths, sums and polynomial fingerprints,
  the fold of a prefix is two numbers (`Affine`), extended in one step per
  element and composed in one step per join (`foldr_eq_summary`,
  `summary_append`).
* **Revision.** Recognition is a fact about the program at one revision.
  Adding an overlapping equation, such as a catch-all `(= (len $x) 0)`,
  changes the answers on cells so that no step recognizes them
  (`Controls.catch_all_unrecognizable`): a native fold kept past that
  revision would lose answers, so the fast path is keyed by the revision.
* **Shape cannot decide a quotient.** Two programs with the same constructors
  and the same operations differ in whether storing their sequences as bags
  is sound: one only counts, one also reads the head. No rule that sees only
  the constructors and operations is both sound and complete
  (`no_shape_only_admission`). The evidence has to come from the observers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.StructureByProof

open Presentations (Family Spine)
open Mettapedia.Algebra.Collections.ObservationalQuotient (Machine)
open Mettapedia.Algebra.Collections.FoldRespect

universe u v w x

/-! ## Recognized structural recursion -/

section Recognized

variable {T : Type u} {F : Type v} (P : Family T F) {β : Type w} {ε : Type x}

/-- A structural recursion over the family `P`, recognized from a program:
the bag of answers, each a value with its bindings, of every cell is the bag
of answers of its rest, each stepped by the cell's field. -/
structure Recognized (answers : T → Multiset (β × ε)) where
  step : F → ε → β → β
  cell_answers : ∀ f r, answers (P.cell f r) = (answers r).map fun p => (step f p.2 p.1, p.2)

namespace Recognized

variable {P} {answers : T → Multiset (β × ε)} (R : Recognized P answers)

/-- The fold of a list of fields, for one answer's bindings. -/
def foldFields (fs : List F) (p : β × ε) : β × ε := (fs.foldr (fun f b => R.step f p.2 b) p.1, p.2)

theorem foldFields_cons (f : F) (fs : List F) (p : β × ε) :
    R.foldFields (f :: fs) p = (R.step f p.2 (R.foldFields fs p).1, p.2) := rfl

/-- **The answers of a spine with any end.** -/
theorem answers_build (fs : List F) (e : T) :
    answers (P.build ⟨fs, e⟩) = (answers e).map (R.foldFields fs) := by
  induction fs with
  | nil =>
      simp only [Family.build_nil]
      conv_lhs => rw [← Multiset.map_id (answers e)]
      rfl
  | cons f fs ih =>
      rw [Family.build_cons, R.cell_answers, ih, Multiset.map_map]
      rfl

/-- **A recognized recursion is a native fold over the maximal spine**, with
one evaluation of its end. -/
theorem answers_spine (t : T) :
    answers t = (answers (P.spine t).stop).map (R.foldFields (P.spine t).elems) := by
  conv_lhs => rw [← P.build_spine t]
  exact R.answers_build _ _

/-- **Binding an open end extends the fold**: the prefix's fold composes with
the fold of the spine bound to the end. -/
theorem answers_extend (fs gs : List F) (e : T) :
    answers (P.build ⟨fs, P.build ⟨gs, e⟩⟩) =
      (answers e).map (R.foldFields fs ∘ R.foldFields gs) := by
  rw [R.answers_build, R.answers_build, Multiset.map_map]

theorem foldFields_append (fs gs : List F) (p : β × ε) :
    R.foldFields (fs ++ gs) p = R.foldFields fs (R.foldFields gs p) := by
  simp [foldFields, List.foldr_append]

/-- A deterministic end gives one answer, the fold of the prefix. -/
theorem answers_of_single (t : T) {p : β × ε} (single : answers (P.spine t).stop = {p}) :
    answers t = {R.foldFields (P.spine t).elems p} := by
  rw [R.answers_spine, single, Multiset.map_singleton]

end Recognized

end Recognized

/-! ## Affine prefix summaries -/

section Affine

variable {R : Type u} [CommRing R]

/-- The affine map `x ↦ offset + scale · x`. -/
@[ext]
structure Affine (R : Type u) where
  scale : R
  offset : R

namespace Affine

def apply (a : Affine R) (x : R) : R := a.offset + a.scale * x

/-- Composition: `a` after `b`. -/
def comp (a b : Affine R) : Affine R := ⟨a.scale * b.scale, a.offset + a.scale * b.offset⟩

theorem apply_comp (a b : Affine R) (x : R) : (a.comp b).apply x = a.apply (b.apply x) := by
  simp only [apply, comp]
  ring

def one : Affine R := ⟨1, 0⟩

theorem comp_assoc (a b c : Affine R) : (a.comp b).comp c = a.comp (b.comp c) := by
  ext <;> simp only [comp] <;> ring

theorem one_comp (a : Affine R) : one.comp a = a := by
  ext <;> simp [one, comp]

end Affine

variable {F : Type v}

/-- The summary of a prefix for the step `b ↦ e f + B · b`. -/
def summary (e : F → R) (B : R) : List F → Affine R
  | [] => Affine.one
  | f :: fs => (⟨B, e f⟩ : Affine R).comp (summary e B fs)

/-- **A prefix's fold is its summary.** -/
theorem foldr_eq_summary (e : F → R) (B : R) (fs : List F) (z : R) :
    fs.foldr (fun f b => e f + B * b) z = (summary e B fs).apply z := by
  induction fs with
  | nil => simp [summary, Affine.one, Affine.apply]
  | cons f fs ih =>
      rw [List.foldr_cons, ih, summary, Affine.apply_comp]
      rfl

/-- **Summaries compose** when prefixes are joined. -/
theorem summary_append (e : F → R) (B : R) (fs gs : List F) :
    summary e B (fs ++ gs) = (summary e B fs).comp (summary e B gs) := by
  induction fs with
  | nil => simp [summary, Affine.one_comp]
  | cons f fs ih => rw [List.cons_append, summary, summary, ih, Affine.comp_assoc]

/-- The length's summary: scale one, offset the count. -/
theorem summary_length (fs : List F) : summary (fun _ => (1 : ℤ)) 1 fs = ⟨1, fs.length⟩ := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      rw [summary, ih]
      ext
      · simp [Affine.comp]
      · simp only [Affine.comp, List.length_cons, Nat.cast_succ]
        ring

end Affine

/-! ## Shape cannot decide a quotient -/

/-- A rule that admits bag storage by looking only at the operations of a
program, here prepending. -/
def ShapeOnlyAdmission := (ℕ → List ℕ → Multiset (List ℕ)) → Prop

/-- Sound: every program whose operations it admits is one under which
reordered sequences are contextually equivalent. -/
def ShapeOnlyAdmission.Sound (rule : ShapeOnlyAdmission) : Prop :=
  ∀ (ω : Type) (M : Machine ℕ ω (List ℕ) ℕ), rule M.step → ∀ a b : List ℕ, a.Perm b → M.Equiv a b

/-- Complete: it admits the operations of every program under which bag
storage is sound. -/
def ShapeOnlyAdmission.Complete (rule : ShapeOnlyAdmission) : Prop :=
  ∀ (ω : Type) (M : Machine ℕ ω (List ℕ) ℕ), (∀ a b : List ℕ, a.Perm b → M.Equiv a b) → rule M.step

/-- **No shape-only rule is sound and complete.** A program that only counts
and a program that also reads the head have the same operations; bag
storage is sound for the first and not for the second. -/
theorem no_shape_only_admission (rule : ShapeOnlyAdmission) :
    ¬ (rule.Sound ∧ rule.Complete) := by
  rintro ⟨sound, complete⟩
  let counting : Machine ℕ Unit (List ℕ) ℕ :=
    foldMachine (fun (_ : Unit) (_ : ℕ) (n : ℕ) => n + 1) (fun _ => 0)
  have countingSound : ∀ a b : List ℕ, a.Perm b → counting.Equiv a b := fun a b h =>
    bag_storage_sound _ _ (fun _ => leftCommutes_blind _) h
  have admitted : rule counting.step := complete Unit counting countingSound
  have headSound := sound Bool Controls.sumAndHead admitted [2, 1] [1, 2] (List.Perm.swap 1 2 [])
  have := Controls.sumAndHead.equiv_refines false _ _ headSound
  revert this
  decide

/-! ## Controls -/

namespace Controls

open Presentations (binary)
open Mettapedia.Languages.MeTTa.OSLFCore

/-- `len` with a catch-all equation `(= (len $x) 0)` added: every call also
answers `0`. -/
def lenWithCatchAll : List ℕ → Multiset ℕ
  | [] => {0, 0}
  | _ :: xs => (lenWithCatchAll xs).map (· + 1) + {0}

/-- **An overlapping equation defeats recognition**: no step maps the answers
of the rest to the answers of the cell, since the cell has one answer more. -/
theorem catch_all_unrecognizable :
    ¬ ∃ step : ℕ → ℕ → ℕ, ∀ x xs,
      lenWithCatchAll (x :: xs) = (lenWithCatchAll xs).map (step x) := by
  rintro ⟨step, h⟩
  have := congrArg Multiset.card (h 0 [])
  simp [lenWithCatchAll] at this

/-- The authored `len`, recognized: its fold over `(Cons a (Cons b $t))`
answers two more than each answer of `(len $t)`. -/
theorem len_open_tail (answers : Atom → Multiset (ℕ × Unit))
    (R : Recognized (binary "Cons") answers) (lenStep : ∀ x θ b, R.step x θ b = b + 1)
    (a b t : Atom) :
    answers ((binary "Cons").build ⟨[a, b], t⟩) = (answers t).map fun p => (p.1 + 2, p.2) := by
  rw [R.answers_build]
  refine Multiset.map_congr rfl fun p _ => ?_
  simp only [Recognized.foldFields, List.foldr_cons, List.foldr_nil, lenStep]

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.StructureByProof
