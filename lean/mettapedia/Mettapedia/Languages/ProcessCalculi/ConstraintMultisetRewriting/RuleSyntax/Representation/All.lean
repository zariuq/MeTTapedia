import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Union
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Characterization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Equivariance
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Effective
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Hosting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Semidecidable

/-!
# Which steps are steps of programs

* **The step of a program is the least step of its rules** (`Union`), for every frame action: monotone in the
  program (`succ_mono`), the union of the steps on a union (`succ_union`), no transition on the empty program
  (`succ_empty`), the union over the rules (`succ_iff_rule`), least (`succ_least`). A firing uses one rule
  (`firingsByRule`). A program is a set of rules, so a rule stated twice adds no transition and no firing
  (`succ_union_self`, `firingsUnionSelf`). The step of a program is the step of all rules restricted to its
  rules (`succ_iff_restrict`); the step of all rules is the older first-order and dependent full steps
  restricted to fresh openings of rules (`firstOrder_all`, `dependent_all`).
* **Which relations on bags of rows are steps of positive programs** (`Characterization`), at the one
  first-order frame over rows with unknowns: for programs of any size, exactly the frame-closed relations
  (`presented_iff_frameClosed`, and on the step `presents_iff_frameClosed`). That direction asks nothing but
  frame closure, so a program of any size decides membership in an arbitrary set in one firing
  (`oracle_decides`). Frame closure is needed (`wholeStore_not_presented`).
* **A finite program** mentions finitely many constants of rows, so its rewriting is unchanged by exchanging two
  constants beyond them (`Equivariance`: `rewrites_equivariant`), and the oracle of the even constants is the
  rewriting of no finite list of rules (`oracle_evens_not_finite`). It consumes boundedly
  (`allAtOnce_not_finite`).
* **Finitely many results, in a bounded search** (`Effective`): a finite list of range-restricted rules
  rewrites a bag to finitely many bags (`successors_finite`, `results_finite`), found among the rules and the
  lists of rows of the bag for their takes and reads; range restriction is needed (`unrestricted_infinite`).

* **Three senses of hosting** (`Hosting`): the total relation is an operational correspondence between every
  two systems (`total`), excluded only by a sound observation (`total_not_sound`); the weak sense
  (`WeakCorrespondence`: silent steps lower a potential, one observed step per source step) adds no divergence
  (`acc_of_acc`) and forces finitely many successors through a finitely branching view
  (`successors_finite_of_view`, `successors_finite_of_program`), which an operational correspondence alone does
  not (`looping`, `looping_not_weak`); the may sense (`MayHosting`) transfers runs both ways
  (`MayHosting.reachable_iff`).
* **What the may sense hosts is semi-decidable** (`Semidecidable`): for a target whose step is a primitive
  recursive enumeration of successors, read through a primitive recursive encoding and representation,
  reachability of represented states is recursively enumerable (`reach_re`), and so is the reachability of a
  system hosted in the may sense (`may_re`). For a finite program, the coding of bags and a primitive recursive
  matcher are the hypothesis left open.

For finite programs the class of rewriting relations is the frame closure of finitely many schemas; no
characterization by properties of the one-step relation is proved (see `Characterization`).
-/
