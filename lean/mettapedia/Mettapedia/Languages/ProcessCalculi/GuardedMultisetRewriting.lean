import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Shifts
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Store
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Build
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Operations
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Names
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Matching
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Examples
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedSteps
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Reflection
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.ValuesAndSpaces
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Calculus

/-!
# Guarded multiset rewriting with contextual matching

This theory uses one-sided matching. Its mathematical results do not assert
conformance to a programming language. Two-sided equation-store refinements
and their resolved-instance comparison are developed in
`ConstraintMultisetRewriting`.

Terms are binding trees, stored as shared DAGs with shifts on edges; configurations are bags of
terms living in spaces reached through handles with rights; one rule, the step, gathers, checks and
produces; data stays data, and only `eval` runs stored code.

* `GuardedMultisetRewriting.Step`: **the step** (the two-line law), `whenever`, and the theorem that it is
  exactly the compiled transform's step of the interaction semantics (`step_of_fires`,
  `fires_of_step`); read patterns may share one value, a take never shares with a read; `Examples`
  has small programs, including both of these.
* `GuardedMultisetRewriting.SharedTerms`: **the term layer**. Shifts on binding trees (`Shifts`); a store of
  nodes with shifts on edges, where canonical references stand for equal trees exactly when they are
  equal (`Store.unfold_eq_iff`); building, lowering and tightening (`Build`); shifting without
  allocation and opening a binder with shifting (`Operations`); named terms, alpha-equivalent
  exactly when they are one reference (`Names`); matching on references equal to matching on trees
  (`Matching`).
* `GuardedMultisetRewriting.SharedSteps`: **running on shared DAGs is running on trees** (`sharedStep_sound`,
  `sharedStep_complete`).
* `GuardedMultisetRewriting.Reflection`: data stays data, `eval`, the declaration contract; **sealed spaces keep
  their equations** (`sealed_bisimulation`) and unrestricted syntax readers collapse them
  (`data_reader_collapses`).
* `GuardedMultisetRewriting.ValuesAndSpaces`: terms are values, spaces are locations, snapshots are the bridge;
  a step is a write at each space it writes.
* `GuardedMultisetRewriting.Calculus`: the calculus assembled, processes with rights, formation, and the derived
  forms with their owners.
-/
