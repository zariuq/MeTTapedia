import Mettapedia.Languages.Micromath.Kernel
import Mettapedia.Languages.Micromath.ModelExtension
import Mettapedia.Languages.Micromath.Checking
import Mettapedia.Languages.Micromath.SharedChecking

/-!
# Micromath's equational kernel as a represented checking candidate

The static binary-superposition rules have an independent semantic soundness
theorem and an exact connection to the common finitary certificate checker.
Fresh interpretation extension is conservative on the allocated vocabulary;
future symbol occurrences require uniform validity beyond that vocabulary.

The source reference is revision `41ea90e86d04762b411bac67af43d75986297ecb`:
https://git.olsak.net/mirek/Micromath/src/commit/41ea90e86d04762b411bac67af43d75986297ecb/README.md

The set-theoretic axiom profiles, trusted snapshot/challenge interpretation,
mutable-slot execution, UInt64 bounds, binary readers and C refinement retain
separate obligations. This entry point does not select a Prime foundation or
establish comparative minimality against other checking kernels.
-/
