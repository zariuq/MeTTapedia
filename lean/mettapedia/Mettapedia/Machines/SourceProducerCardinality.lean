import Mettapedia.Machines.SourceProducerCardinality.Core
import Mettapedia.Machines.SourceProducerCardinality.Shared

/-!
# Cardinality derived from the existing recursive equation IR

Executable admission follows finite authored syntax and the current Shape,
with conservative unknown bounds at recursive calls. It neither follows future
invocations nor runs constructors to discover an answer count. The recursive
`sourceGrade` remains a semantic reference. Grades bound outer occurrences:
a returned empty collection is one answer, and equal collections from distinct
equations remain distinct answers.

This is the finite pure, scope-resolved IR of `SourceProducerAdmission`.
`unsupported` keeps an unknown grade and cannot supply execution permission.
Syntax elaboration, native correspondence, effects and open producers have
their own obligations. The no-rule observer retains only a separately supplied
fallback, never a fallback for a matching body that fails.

The declarations live in the modules imported above, split along their
dependencies; the concrete controls are in
`Mettapedia.Machines.SourceProducerCardinality.Controls`.
-/
