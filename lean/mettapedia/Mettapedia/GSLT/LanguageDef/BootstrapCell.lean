import Mettapedia.GSLT.LanguageDef.BootstrapCell.Replay
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCalculus
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCalculusCalibration
import Mettapedia.GSLT.LanguageDef.BootstrapCell.CheckingWeakness
import Mettapedia.GSLT.LanguageDef.BootstrapCell.CoreNIK
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCoreHOL
import Mettapedia.GSLT.LanguageDef.BootstrapCell.BootHost
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation
import Mettapedia.Logic.HOL.ReplayCore
import Mettapedia.Logic.HOL.ReplayCoreDefined
import Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayCoreDefinedHOL
import Mettapedia.Logic.Diagonal.Provability

/-!
# The bootstrap cell: NIK's replay presented, checked, and levelled

* `BootstrapCell.Replay`: goal-directed replay of raw certificates over an
  abstract signature (goals with decidable equality and a local rule map);
  exact correspondence with proof-relevant derivations, uniqueness of goals
  and of derivations, and soundness in every closed interpretation, all
  without choice.  The generic inference checker is replay in the signature
  of its calculus.
* `BootstrapCell.ReplayCalculus`: the reflexive cell.  The replay rules of a
  calculus, presented as a calculus whose judgment is `Accepts(goal, code)`;
  its derivations coincide with the checking derivations of the calculus, the
  generic checker agrees on both sides, and each acceptance judgment has at
  most one derivation.
* `BootstrapCell.ReplayCalculusCalibration`: the cells of the modus ponens and
  dependently typed calibration packages, a two-level tower, and negative
  controls (an unfaithful variant that validates, and mis-cached packages
  that do not).
* `BootstrapCell.CheckingWeakness`: the theory–model Galois connection at the
  level of checking; a kernel's theory is the weakest admissible theory
  exactly when the kernel is faithful.
* `BootstrapCell.CoreNIK`: the one-level refinement statement, which pins the
  implementation to replay; the separate semantic-qualification interface;
  and the reflexive cell as a bootstrap layer at host level one.
* `Logic.HOL.ReplayCore`: the replay core as a theory of higher-order logic
  in the deep embedding: seven axioms (the recursion equations of
  acceptance, the closure rules of derivability, and induction on
  certificates as one sentence), an object derivation of soundness, and a
  junk model with a cyclic certificate in which induction and soundness
  fail.
* `BootstrapCell.ReplayCoreHOL`: the standard model of that theory, NIK's raw
  certificates with acceptance by replay; each axiom holds by a clause of the
  replay core, and the interpretation of the derived sentence is the
  soundness of replay, recovered from the object derivation.
* `Logic.HOL.ReplayCoreDefined`: the same core with acceptance and
  derivability defined as least predicates by the impredicative definition.
  Soundness and completeness are derivations from no assumption; the theory
  is induction on certificates and freeness of their constructors, which
  derive the old acceptance equations, so every old axiom is a theorem.
  Induction is needed only for checkers given by the replay equations; on
  genuine certificates, the inductive subset, even that needs no axiom.
* `BootstrapCell.ReplayCoreDefinedHOL`: its standard model on NIK's raw
  certificates, where the least acceptance is replay and the least
  derivability is derivability; soundness and completeness of replay and of
  the generic inference checker are read off the object derivations.
* `BootstrapCell.BootHost`: raw certificates as the initial algebra of
  `F X = Unit × RuleInstance × List X`, replay as the unique fold out of it,
  and non-well-founded hosts on which the fold is not unique or does not
  exist.
* `BootstrapCell.ReplayPresentation`: the replay presentation of every
  validated calculus satisfying explicit freshness conditions is valid; the
  conditions are inherited, so the bootstrap tower exists at every level and
  each level agrees with the base calculus; a modus ponens tower as positive
  control, and a child-name collision and an atom clash as negative controls.
* `Logic.Diagonal.Provability`: provability stages with the derivability
  conditions; Löb's theorem and the second incompleteness theorem from the
  diagonal step, the stratified escape through a model one level up, and
  controls.
-/
