import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateApplication
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateCheckedRealizability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateBetaRealizability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateStructuralProofs

/-!
# The guarded predicate interface to HOL

The shared lexical reader connects four distinct obligations:

* `GuardedTypeFormation` retains source formation and the selected predicate.
* `GuardedRealizer` retains source typing and an actual HOL membership proof.
* `GuardedSubstitution` transports source typings and target guard evidence.
* `Interpreter.checkRealizer?` admits endpoint transport only after checking
  both the source context and the supplied equality certificate.

`GuardedBeta` additionally connects represented source function contraction to
one independently defined HOL beta step. Its guard is the dependent codomain
at the actual argument. Structural pair and identity codes use their selected
profile; their reading alone does not establish their computation laws.

These components share exact source syntax, contexts and target readings.
First-class universes, arbitrary root interpretations, intensional identity
reflection, total interpretation of source derivations and full Lean import
remain separate obligations. This entry point introduces no additional rules.
-/
