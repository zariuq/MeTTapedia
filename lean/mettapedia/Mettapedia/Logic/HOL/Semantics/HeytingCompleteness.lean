import Mettapedia.Logic.HOL.Semantics.HeytingGeneral
import Mettapedia.Logic.HOL.Semantics.KripkeHenkinCountermodel

/-!
# Heyting Completeness Package

Public citation handle for the intuitionistic HOL core theorem package.

This module re-exports the Heyting-valued substitutional semantics and the
Lindenbaum model interface:

- `HeytingSem.HeytingGeneralModel`;
- `HeytingSem.sound`;
- `HeytingSem.Lindenbaum.lindenbaumModel`;
- `HeytingSem.provable_iff_heytingConsequence_param_free`;
- `HeytingSem.lindenbaumModel_refutes_nontheorem`;
- `KripkeHenkin.em_not_derivable`.

Scope: parameter-free closed theories over `WithParams`; EM-free extensional
HOL calculus.  The Heyting theorem is the main citable completeness interface.
The excluded-middle canary is the concrete negative example showing that the
same EM-free calculus does not derive `p ∨ ¬p`.

Axiom audit: the soundness and canary interfaces are Choice-free, while the
Lindenbaum completeness direction uses `Classical.choice` along with the usual
quotient/propositional extensionality footprint.
-/

