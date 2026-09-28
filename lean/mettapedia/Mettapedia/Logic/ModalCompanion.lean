import Mettapedia.Logic.ModalCompanion.Derivations
import Mettapedia.Logic.ModalCompanion.GeometricBarr
import Mettapedia.Logic.ModalCompanion.GoedelReverseTranslation
import Mettapedia.Logic.ModalCompanion.GoedelFaithfulness

/-!
# Gödel's syntactic proof that the modal translation of intuitionistic logic is faithful

Gödel's 1941 proof, as proof transformations on derivation trees with assumptions:

* `ModalCompanion.Derivations`: derivation trees for the intuitionistic, classical and S4
  Hilbert calculi, as Foundation entailment systems, and their agreement with Foundation's
  `Propositional.Int`, `Propositional.Cl` and `Modal.S4`.
* `ModalCompanion.GeometricBarr`: Theorem 62, the propositional geometric case of Barr's
  theorem, by Gödel's ramification tree.
* `ModalCompanion.GoedelReverseTranslation`: the reverse translation `A ↦ A′` through
  distinguished matrices, Gödel's lemmas, and Theorem 63 (`S4 ⊢ A` gives `Int ⊢ A′`).
* `ModalCompanion.GoedelFaithfulness`: Lemma 9 (`U(A)′ ≡ A`) and Theorem 64
  (`S4 ⊢ U(A)` gives `Int ⊢ A`), with Foundation's `Modal.ModalCompanion Propositional.Int
  Modal.S4` as a corollary.
-/
