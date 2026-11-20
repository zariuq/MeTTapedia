import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Basic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Heads
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Inductive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Data
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Calls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Normalization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Packages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Rows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.ReadingCorrespondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Unsaturated

/-!
# The answer of a call, on the directed reduction

* `Basic`: the answer of a call is a directed normal form reached by the directed reduction (β, both
  projections and the declared rows, with no head steps); it is unique on the nose in every constructor
  presentation, typed in every qualified package, and an answer of the full reduction when it has no head;
  strong normalization gives existence.
* `Heads`: equality up to universe heads; the rows of a constructor system do not look at heads, so every
  answer of the full reduction without heads is an answer, and the directed normal forms convertible with a
  call are head-congruent to its answer. The two notions of answer coincide off the heads under two
  hypotheses, a constructor presentation and heads related to themselves, each with its control.
* `Inductive`: at an inductive type with recursive fields, by the logical relation of the package's
  normalization model and without assuming strong normalization, every closed term reaches a constructor
  tree, its only answer, when no closed neutral term is typed at that type.
* `Data`: the data types of the vectors package (numbers, unit, empty type, nondependent pairs, vectors over
  data types) and their values; every closed term of a data type has exactly one answer, a value.
* `Calls`: the compiled interpretation of a definition by rows. A ground call of a closed checked function
  whose declared result type at the arguments is a data type has exactly one answer, a value of that type;
  addition by rows, append on it, map, a definition into pairs; the control at a full call whose declared
  type is a universe.
* `Normalization`: under strong normalization every typed term of a qualified package has exactly one
  answer, with the executable package as an instance; in a qualified package that is not strongly
  normalizing, the closed numbers have their answers all the same.
* `Packages`: which qualified packages of the tree meet which hypothesis; the control showing that the
  hypothesis on closed neutral terms at the type cannot be dropped.
* `Rows`: the definition as a declared constant with its rows as rules. Every ground call of a checked
  definition in the class (recursion on a call index with saturated recursive calls, or one row without a
  call index), whose declared result type at the arguments is a data type, has exactly one answer in the
  extended package, the answer of the compiled call; and the rows reach no value that the compiled reading
  does not answer.
* `ReadingCorrespondence`: the rows' system and the package's, related by the reading, as an operational
  correspondence of the general theory.
* `Unsaturated`: where the class of `Rows` stops inside the checked functions. A definition whose row
  passes its recursive call on without the later arguments is a closed checked function, the reading is
  sound for it, agreement by conversion fails for it at a full call, and the ground calls that were run
  agree; that every ground call of it has an answer by its rows is not proved. A recursive call that
  changes a later argument and keeps all of them is in the class.
-/
