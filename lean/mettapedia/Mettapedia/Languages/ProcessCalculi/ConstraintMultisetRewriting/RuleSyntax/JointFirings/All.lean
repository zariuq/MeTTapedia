import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Bags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Singletons
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Members
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OneAfterAnother
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Knowledge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Every
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.EveryControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Maximal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Clashes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Exec
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Independent
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SynchronousUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OneActiveRow
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.AllAtOnce
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Unique
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Collect
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.EmptyBag
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Tensor

/-!
# What one step commits: a bag of matches

The step of `RuleSyntax.Core` fires one rule, with one opening and one selection: one match. This folder
defines, over the same rules, states and firings, a step whose firing is a finite bag of matches at one
state, and compares the ways of choosing the bag.

## The general step and its readings

* `Bags`: members, bags, the joint selection and information, joint freshness, and three readings of
  joint admission: guards at the joint information (`Bag.Admits`), guards at each member's own
  information (`Bag.AdmitsOwn`), every member enabled on its own (`Bag.AdmitsSnapshot`). `bagStep` is an
  `Interface.Step.Standard` whose firings are bags with a member.
* `Clashes`: matches that want one row: refuse, take once at the entry state (`Bag.AdmitsAtEntry`), or a
  compatible part (`Bag.AdmitsPart`), separated at one state (`Shop.three_readings`).
* `Exec`: the reading of a store that is a set (`Bag.AdmitsAsSet`, `Bag.AdmitsEveryAsSet`).

## The candidates

* **One match**: `Singletons` (`succ_iff_single`: the step of the program is the bag step restricted to
  bags of one member).
* **Any compatible bag**: `bagStep`; `Tensor` (`admits_iff_tensor`: on ground rules a bag is one match of
  the tensor of its rules).
* **Every match**: `Every` (`Bag.AdmitsEvery`, `AdmitsEvery.keys_perm`, `every_same_label`),
  `EveryControls` (`every_not_box_one`, `every_not_dia_one`), `AllAtOnce` (`spendAll_made_rows`),
  `Collect` (what completeness asks, and what a collect query can say).
* **A maximal bag**: `Maximal` (`Bag.admitsMaximal_iff`, `MaximalControls.lone_not_maximal`).
* **Unique**: `Unique` (`Bag.AdmitsUnique`; `Neighbour`: a private neighbour switches `every`, `unique` and
  maximal bags off and leaves the one-match firing admitted).
* **The bag without members**: `EmptyBag`.

## When a bag is a run of single firings, and when it is not

* `Members`, `OneAfterAnother` (`peel`, `run_of_admitsOwn`, `admitsOwn_of_fixed`), `Independent`
  (`admitsOwn_iff_members`, `any_order`, `SharedUnknown`), `Runs` (`ownCorrespondence`,
  `jointCorrespondence`, `none_breaks_forward`, `knowledge_breaks_forward`).
* `Knowledge` (`stopped_and_fires`: with guards at the joint information, a bag is admitted that no
  member can begin), `SynchronousUpdate` (`Synchronous.no_run_reaches`: none queries judged at the entry state;
  `Between`: a neighbour sees the state between two members).
* `OneActiveRow`: on the machine of the partial recursive functions, whose states have one row, the bag
  step is the step of the program (`Partrec.bag_halts_iff`).

## Comm, exec, match

* `Exec`: MM2's exec is one step of `every` over its kernel and its solution rules
  (`ExecStep.exec_is_every`); a bag that skips a solution is not a step (`ExecControls.skipping_not_every`);
  `MatchAll`: every match of a rule that only reads is one step, its answers made rows of the one world.
-/
