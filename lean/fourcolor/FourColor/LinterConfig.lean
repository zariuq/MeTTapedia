/-
Global linter configuration for FourColor project

These linters are temporarily disabled to reduce noise while we focus on
eliminating sorries and completing proofs. Once the mathematical content is
solid, we'll re-enable these and clean up systematically.

See CLAUDE.md for the cleanup roadmap.
-/

-- Silence noisy but non-critical warnings
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
