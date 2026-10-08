import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSourceTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableRawChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableWeakHead
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.InductiveHeadMapping

/-!
# Executable checking for the parameterized Pi/Sigma/identity calculus

This is an import entry point for the general theorem layer. Its declarations
live in the imported subject modules; no second checking authority is defined
here.

`ExecutableChecking` reconstructs synthesis, checking, subsumption and
type-directed conversion. Its soundness theorems require the rule package's
formation, computation-preservation, cumulativity and declaration-formation
proofs. `ExecutableWrittenChecking` retains context formation, written
expected-type formation and annotated term typing in its certificates.

`ExecutableSourceTransport` carries those certificates along actual rule
morphisms. This preserves accepted evidence, without equating the finite-budget
decisions of two different procedures. Raw scope recovery and beta substitution
are supplied by `ExecutableRawChecking`; full and weak-head reduction procedures
retain their reduction paths. Inductive head maps transport actual recursor
equations under their stated hypotheses.

The syntax is one specified dependent grammar. A concrete rule package must
discharge the interpretation obligations before using the soundness theorems.
Finite-budget failure alone gives no non-derivability or inconsistency result.
-/
