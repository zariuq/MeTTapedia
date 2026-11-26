import Mettapedia.GSLT.Contracts.LiveTheoryProjections
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTa
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveCountRegion

/-! Two PeTTa instances. Named directional-rule reads are the ordered frontier
of the generated space language. Exact occurrence counts can be added over a
resolved path, but a completed scan is not in general a single source firing. -/
set_option autoImplicit false
namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveTheoryReadings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Contracts.LiveTheoryProjections
open SpaceSemantics (Equation Indexes Program)
open SpaceTheory.PeTTaPresentation (readEquation readEquation_shape)

variable {S : Type*}

/-- Only directional rule syntax is fixed by this instance. Selecting type
or scoped-equality declarations belongs to the corresponding profile. -/
def classify (types equations : Atom → Option (Option String)) : Classifier String Atom
  | .rewrite, a => (readEquation a).map (fun e => some e.head)
  | .typing, a => types a
  | .equation, a => equations a

private def decodeRules : Reply S Atom → List Equation
  | .rows rs => rs.filterMap readEquation
  | .path _ => []

private theorem parsed {rs : List Atom} {p : Program} (idx : Indexes rs p) :
    rs.filterMap readEquation = p.equations := by
  induction idx with
  | nil => rfl
  | equation h args body tail ih => simp [ih]
  | declaration subject type tail ih => simpa [List.filterMap_cons] using ih
  | fact row notEquation _ tail ih =>
    have no : readEquation row = none := by
      rw [readEquation_shape]; split
      · exact (notEquation _ _ _ rfl).elim
      · rfl
    simpa [no] using ih

private theorem filter_parsed (types eqs : Atom → Option (Option String)) (rs : List Atom) (h : String) :
    (((catalog (classify types eqs) .rewrite rs).filter (selects (classify types eqs) .rewrite h)).filterMap
      readEquation) = (rs.filterMap readEquation).filter (fun e => e.head == h) := by
  induction rs with
  | nil => rfl
  | cons row rest ih =>
    cases parse : readEquation row with
    | none => simpa [catalog, classify, selects, parse] using ih
    | some e =>
      by_cases head : e.head = h <;> simp [catalog, classify, selects, parse, head] at ih ⊢ <;> exact ih

theorem named_candidates (types eqs : Atom → Option (Option String)) (w : World S Atom)
    (s : S) (langName head : String) :
    decodeRules (read (classify types eqs) w (.named s .rewrite head)) =
      SpaceTheory.PeTTaPresentation.candidates (SpaceTheory.PeTTaPresentation.language langName (w.occurrences s))
        (w.occurrences s) head := by
  rw [SpaceTheory.PeTTaPresentation.candidates_exact, ← parsed (SpaceSemantics.index_exact (w.occurrences s))]
  exact filter_parsed types eqs _ head

/-- One fixed query and binding environment at the cut. Disjoint *slices of
occurrences* suffice: equal atom values need not live on the same worker.
A path containing a space twice visits it twice. -/
theorem count_on_path (q : LiveCountRegion.Query) (b : Subst) (w : World S Atom)
    (path : List S) (initial : Nat) :
    LiveCountRegion.run q b ⟨path.flatMap w.occurrences, initial⟩ = initial +
      (path.map (fun s => LiveCountRegion.run q b ⟨w.occurrences s, 0⟩)).sum := by
  induction path generalizing initial with
  | nil => rfl
  | cons s rest ih =>
    rw [List.flatMap_cons, LiveCountRegion.run_append, ih 0]
    have offset := LiveCountRegion.run_append q b [] (w.occurrences s) initial
    change LiveCountRegion.run q b ⟨w.occurrences s, initial⟩ =
      initial + LiveCountRegion.run q b ⟨w.occurrences s, 0⟩ at offset
    simp [offset, Nat.add_assoc]

theorem macro_not_one_scan (q : LiveCountRegion.Query) (b : Subst)
    (a₁ a₂ : Atom) (rest : List Atom) (initial : Nat) :
    let c : LiveCountRegion.Cursor := ⟨a₁ :: a₂ :: rest, initial⟩
    let done_ : LiveCountRegion.Cursor := ⟨[], LiveCountRegion.run q b c⟩
    (LiveCountRegion.theory q b).MultiStep c done_ ∧ ¬ LiveCountRegion.Scan q b c done_ := by
  refine ⟨LiveCountRegion.run_reaches q b _ initial, ?_⟩
  intro step
  cases step

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.LiveTheoryReadings
