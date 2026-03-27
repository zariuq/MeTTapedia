import Mettapedia.Logic.HOL.Syntax.Type
import Mettapedia.Logic.HOL.Syntax.Term
import Mettapedia.Logic.HOL.Syntax.Subst
import Mettapedia.Logic.HOL.Syntax.Closed
import Mettapedia.Logic.HOL.Henkinization
import Mettapedia.Logic.HOL.HenkinizationStages
import Mettapedia.Logic.HOL.HenkinizationInfinity
import Mettapedia.Logic.HOL.Semantics.HeytingHenkin
import Mettapedia.Logic.HOL.Semantics.Henkin
import Mettapedia.Logic.HOL.Semantics.Extensionality
import Mettapedia.Logic.HOL.Semantics.Reduct
import Mettapedia.Logic.HOL.Semantics.SetBased
import Mettapedia.Logic.HOL.Probabilistic
import Mettapedia.Logic.HOL.Derivation
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.Lindenbaum
import Mettapedia.Logic.HOL.LindenbaumSet
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.CanonicalExtension
import Mettapedia.Logic.HOL.HenkinWitnessClosure
import Mettapedia.Logic.HOL.PrimeHenkinExtension
import Mettapedia.Logic.HOL.HenkinAxiomsInfinity
import Mettapedia.Logic.HOL.CanonicalKripke
import Mettapedia.Logic.HOL.CanonicalSemantics
import Mettapedia.Logic.HOL.CanonicalModel
import Mettapedia.Logic.HOL.PlainIntuitionistic
import Mettapedia.Logic.HOL.IntuitionisticCompleteness
import Mettapedia.Logic.HOL.OriginalReflectionReduction
import Mettapedia.Logic.HOL.OriginalReflectionObstruction
import Mettapedia.Logic.HOL.OriginalReflectionWitnessed
import Mettapedia.Logic.HOL.IntuitionisticSoundness
import Mettapedia.Logic.HOL.Soundness
import Mettapedia.Logic.HOL.Embedding.FirstOrder
import Mettapedia.Logic.HOL.WorldModel
import Mettapedia.Logic.HOL.WorldModelCompleteness
import Mettapedia.Logic.HOL.LogicalInduction

/-!
# Real Higher-Order Logic

Public entrypoint for the real Church-style HOL layer:

- intrinsically typed syntax,
- witness-provider and one-step Henkinization syntax infrastructure,
- stage-indexed and cumulative Henkinization syntax infrastructure,
- intuitionistic-extensional Heyting/Henkin-style semantics,
- classical `Prop`-valued Henkin semantics,
- direct set-based grounding into Henkin models,
- infinitary semantic probability over measurable indexed model spaces,
- hierarchical and infinite-order semantic probability over measures on those
  indexed model spaces,
- a small natural-deduction core, its extensional overlay, and soundness,
- a Lindenbaum-style closed-theory quotient over the extensional proof layer,
- a set-based Lindenbaum quotient over closed-theory provability,
- a typed closed-theory / canonical-world layer for the future completeness proof,
- extension lemmas for implication/consistency over those canonical theories,
- one-step and cumulative witness-closure infrastructure for the quantifier layer,
- a prime-extension theorem and cumulative Henkin axiom family for canonical worlds,
- a canonical Kripke/world semantics layer for closed formulas over those worlds,
- a canonical truth-event semantics for closed formulas over those worlds,
- a typed companion canonical model semantics over closed substitutions into the
  cumulative Henkin language,
- a plain-intuitionistic mainline entrypoint exposing the already formalized
  soundness theorem and the internal cumulative-Henkin completeness milestone,
- an internal finite closed-context completeness theorem for the cumulative
  Henkin language over canonical Henkin worlds,
- an auxiliary proof-theoretic reduction theorem isolating the exact remaining
  blockers in the constant-based original-reflection detour,
- an auxiliary obstruction showing that naive constant-based original reflection
  is false for empty-signature source semantics with empty admissible domains,
- a witnessed-source replacement layer showing that base-type source witnesses
  recursively yield closed terms at every simple type and recover existential
  source theorems of the form `∃ x : τ, ⊤`,
- first-order embedding,
- and the world-model bridge over pointed Henkin models.

Important status boundary:

- the corrected intuitionistic-extensional HOL core, soundness layer, cumulative
  Henkinization infrastructure, world-level canonical truth machinery, and an
  internal cumulative-Henkin finite-context completeness theorem are real;
- `/home/zar/claude/lean-projects/mettapedia/Mettapedia/Logic/HOL/PlainIntuitionistic.lean`
  is the intended public entrypoint for the plain intuitionistic metatheory;
- the old constant-based original-signature reflection target is now formally
  known to fail against the current source semantics;
- the original-reflection files remain auxiliary diagnostics / strengthened
  detours rather than the main route to plain intuitionistic completeness;
- the final typed original-signature canonical-model bridge and plain
  intuitionistic HOL completeness theorem are still in progress;
- the logical-induction and planner-facing belief/process files imported here are
  experimental overlays rather than part of the mature HOL metatheory.
-/
