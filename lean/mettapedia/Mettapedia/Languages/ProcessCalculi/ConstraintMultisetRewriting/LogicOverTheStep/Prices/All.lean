import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.UnrestrictedStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.StaircaseStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.AdequacyPrice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.SearchPrice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.TerminationPrice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.CheckerTower

/-!
# The price of each guarantee

Reverse mathematics asks which principle a theorem is equivalent to over a weak base. For a language
designer the principle is a price: what a checker, a runtime or the ambient logic must supply for a
guarantee to hold. Each module states a guarantee, its exact price among the tree's named principles
(`Logic.ReverseMathematics.Omniscience`: LPO, WLPO, LLPO, MP; and the fan theorem `FAN`, added here),
and the cheapest design that does not pay it. A theorem called constructive here has no
`Classical.choice` in its axiom audit.

* `UnrestrictedStep`: on the first-order step with every rule instance admitted, one firing reaches
  every consistent extension of the knowledge. Observing the knowledge, or the knowledge and the bag
  of labels, finitary adequacy holds with no finite program and no finite cover
  (`knowledgeView_adequacy`, `storeView_adequacy_base`); for a coarser observation set invariant under
  renaming it fails (`unrestricted_adequacy_fails`), though it holds for that set under every finite
  program (`tagView_program_adequacy`).
* `StaircaseStep`: the failure needs only four atoms (`staircase_adequacy_fails`). On knowledge the
  unrestricted step is a reflexive, transitive tree that holds a staircase; every formula is eventually
  periodic on the stairs and imitates, at odd heights, a witness that alternates without bound
  (`period`, `alt_wit`, `alt_upper`).
* `AdequacyPrice`: finitary adequacy costs exactly LLPO on systems with explicit successor lists,
  decided observations and countably many atoms and labels (`listAdequacy_iff_llpo`), and exactly
  excluded middle with finite covers (`imageFiniteReflection_iff_em`, `coverAdequacy_iff_em`) or with
  undecided observations (`listPropAdequacy_iff_em`). Apartness with a witness costs nothing
  (`not_bisimilar_of_apart`, `apart_iff_exists_level`).
* `SearchPrice`: membership in a least fixpoint is a search found at a finite stage (`reaches_iff`);
  "a search that cannot fail forever succeeds" is Markov's principle (`mp_iff_search`), "reaching is
  decided" is LPO (`lpo_iff_search`), "avoiding is decided" is WLPO (`wlpo_iff_safety`).
* `TerminationPrice`: a bound from "every run finishes" costs the fan theorem in the bar form
  (`barBound_iff_fan`) and the fan theorem with Markov's principle in the negative form
  (`runBound_iff`); a rank or an inductive proof costs nothing (`bounded_of_rank`, `bounded_of_acc`);
  with infinite branching no bound exists (`Controls.fan_unbounded`). In the computable reading Markov's
  principle holds and the fan theorem fails, by Kleene's tree (`computable_reading`).
* `CheckerTower`: sound checkers form a directed family (`Checker.directed`); for an undecidable
  property they have no top, branch, and form infinite chains (`exists_strict_extension`,
  `exists_incomparable_extensions`, `exists_strict_chain`), as for least-fixpoint membership built from
  halting (`reachesHalting_no_top`); a decidable property has a greatest one
  (`greatest_of_computablePred`); a certificate-free checker is a computable choice of certificate on
  its region (`certificate_choice`, `checker_of_certificates`).
-/
