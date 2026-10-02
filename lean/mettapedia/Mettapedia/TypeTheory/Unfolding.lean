import Mettapedia.TypeTheory.Unfolding.ConversionTransport
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Syntax
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Judgments
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Decision
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Divergence
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Semantics
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Soundness
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Controls
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Checker
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.ObserverLink

/-!
# Definitional and propositional unfolding

`ConversionTransport` states, for any finitary rule system whose conversion is
split between a carved and a strong variant, when every strong derivation is
reflected into the carved variant: each shared rule consuming a definitional
equality needs a transport, each carved conversion rule a propositional
counterpart, and each strong-only conversion rule a propositional witness.
A decidable interface to the carved rules then makes the carved checker an
exact authority for the strong judgments read as themselves.

`AccessibleRecursion` instantiates this with a calculus of proposition codes
over the one-ground simple calculus and an accessibility recursor:

* the strong variant unfolds the recursor definitionally, the carved variant
  propositionally; every strong derivation of a code is a carved derivation
  of the same code (`Judgments`);
* carved definitional equality is beta conversion, decided by normalization
  (`Decision`);
* the strong evaluator has no normal form at an abstract accessibility proof
  (`Divergence`);
* both variants are sound in a standard model over `Prop` with a semantic
  recursor built without choice, hence consistent (`Semantics`,
  `Soundness`);
* positive and negative controls, including Curry's paradox for the
  unguarded unfolding (`Controls`);
* the carved checker and its authority for the strong variant (`Checker`);
* carved definitional equality as the relative equivalence of the normal-form
  readout (`ObserverLink`).
-/
