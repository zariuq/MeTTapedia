import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Terms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Language
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Reference
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Specializer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.MatchBuild
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Phases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Correctness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Bridge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecializedAdmission.Printer

/-!
# Specialized admission: the specializer, verified once

A rule (a firing schema) is compiled into a straight-line decision program (`Language`) by a
specializer written as a Lean function (`Specializer.specialize`). For every rule of the
specialized class, every state, parameters and selected occurrences:

* `specialized_admission`, `specialized_firing`: the program gives the step's verdict (admitted,
  or the first conjunct of admission that fails: shapes, fits, unsolvable, or which guard), a
  refusal and an admission without commit change nothing, and a firing leaves the step's result
  with the next identities made;
* `firstOrder_admits_iff`, `specialized_admits_iff_firstOrder`: the reference these theorems use
  is the first-order step's admission (`AnnotatedRuns.firstOrder`), with the frame conjuncts the
  one-frame step leaves to its frame;
* `specialize_isSome_iff`, `dispatch_generic_iff`: a decision goes to the generic route exactly
  outside the specialized fragment;
* `Controls`: Micromath's `substitute1` and guarded rules, two planted faults the theorems
  forbid, and rules just outside the class;
* `Printer`: the C printer, the unverified step from a verified program to C.

## The decision language and t-ISA

Every instruction reads and writes a bounded set of registers, and the state only through five
accessors (identity lookup, head-bucket iteration, take, make, interning a term), so each has a
fixed lowering: a match instruction is a tag compare and loads, a test a compare and a conditional
exit, a scan a capped loop over a bucket, a refusal a return of its reason. With terms and the
state laid out as word regions, templates proved once per instruction, and the accessors as
proved routines, the lowering would replace the C compiler in the trusted base.
-/
