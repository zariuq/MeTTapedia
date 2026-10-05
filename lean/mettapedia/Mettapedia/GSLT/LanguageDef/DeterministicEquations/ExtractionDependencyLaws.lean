import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ExtractionLaws
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension

/-! # Checked linking of extracted computations

The guard excludes every call head of the retained program, including data
constructors and primitive calls. It preserves the real evaluator's outcomes
at every fuel, rather than only preserving successful observations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

def avoidsCalls (source extra : Program) : Bool :=
  extra.all fun row => !source.calledHeads.contains row.head

theorem avoidsCalls_iff (source extra : Program) :
    avoidsCalls source extra = true ↔
      ∀ row ∈ extra, row.head ∉ source.calledHeads := by
  simp [avoidsCalls, List.all_eq_true]

theorem calledHead_of_contains (source : Program) (head : String)
    (known : source.calledHeads.contains head = true) : head ∈ source.calledHeads := by
  simpa using known

theorem linked_apply_exact (source leading trailing : Program) (host : Host)
    (before : avoidsCalls source leading = true)
    (after : avoidsCalls source trailing = true)
    (fuel : Nat) (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) :
    apply (leading ++ source ++ trailing) host fuel head arguments =
      apply source host fuel head arguments :=
  apply_frame_eq source leading trailing host (avoidsCalls_iff _ _ |>.mp before)
    (avoidsCalls_iff _ _ |>.mp after) fuel head used arguments

theorem linked_result_exact (source leading trailing : Program) (host : Host)
    (before : avoidsCalls source leading = true)
    (after : avoidsCalls source trailing = true)
    (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) (result : Term) :
    Applies (leading ++ source ++ trailing) host head arguments result ↔
      Applies source host head arguments result :=
  Applies.frame_iff source leading trailing host (avoidsCalls_iff _ _ |>.mp before)
    (avoidsCalls_iff _ _ |>.mp after) head used arguments result

theorem linked_computes (source leading trailing : Program) (host : Host)
    (before : avoidsCalls source leading = true)
    (after : avoidsCalls source trailing = true)
    (head : String) (used : head ∈ source.calledHeads) (arguments : List Term) (result : Term)
    (computed : Applies source host head arguments result) :
    Applies (leading ++ source ++ trailing) host head arguments result :=
  (linked_result_exact source leading trailing host before after head used arguments result).mpr computed

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
