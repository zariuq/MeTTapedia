import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Bounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Ambient
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.NoTop
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Cost
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.Buckets
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.FastPath
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.SearchBudgets
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeUnifier
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Prices.Regions.TreeChecker

/-!
# Regions with a certificate bound

A property of coded instances given by a decidable certificate relation (`CheckerTower.Certified`)
is checked in the ambient way by searching for a certificate. A **region** is a decidable set of
instances; the search is **bounded** on it when a computable function of the instance bounds the least
certificate. Coverage (which instances are answered) and cost (what answering costs) are separate
claims throughout.

* `Bounds`: **the region theorem**. On a decidable region, the search is computably bounded exactly
  when the property is decided, exactly when a computable function is a certificate on the certified
  part, which can be the least certificate (`region_theorem`, `certificate_iff_decided`,
  `least_certificate_of_decidedOn`). The decidability of the region cannot be dropped: on the certified
  region of halting the property is decided and the search is not bounded (`decided_not_bounded`,
  `halting_region_unbounded`). The algebra: union with the maximum of bounds, subregions, pullback of a
  certificate along a reduction, finite tables, and format invariance (`boundedOn_congr`).
* `Ambient`: on all instances a computable bound exists exactly when the property is decidable
  (`boundedOn_univ_iff`), and every computable bound is exceeded on infinitely many certified instances
  of an undecidable property (`exceeded_infinite`, `halting_exceeded_infinite`). The budget regions of
  the ambient search cover the property (`budgetRegion_covers`).
* `NoTop`: every bounded region of an undecidable property misses a certified and an uncertified
  instance (`misses_certified`, `misses_uncertified`), so it is strictly contained in another bounded
  region, the bound changing at one instance only (`exists_strict_extension`); infinite chains exist
  (`exists_strict_chain`); the bounds outrun every computable function (`bounds_exceed`). Sound checkers
  are the bounded regions inside the property (`soundChecker_certificate`,
  `soundChecker_of_boundedRegion`).
* `Cost`: the cost of a program is the least step index of bounded evaluation (`cost`). It satisfies
  Blum's two laws (`cost_dom_iff`; `cost_le_iff`, `costAtMost_primrec`, `costEq_iff`), charges more
  than the input (`input_lt_cost`, tight by `cost_zero`) and is not additive (`cost_comp_le`,
  `not_additive`). On the uncertified instances of a bounded region the ambient search has no cost and
  the region's decider has one (`bounded_against_unbounded`).
* `Buckets`: checking a supplied certificate is decidable exactly when the relation is computable
  (`check_decidable_iff`); having a certificate is semidecidable (`certified_re`) and for halting not
  decidable (`halting_bucket_two`); the truth of "never halts" is not semidecidable
  (`never_halting_not_re`), so every sound computable certificate relation for it misses a true claim
  (`sound_misses_never_halting`). Hints: sound for every hint, answered exactly when the hint is at
  least the least certificate, the same certificate found with any hint; a region with a bound is the
  hint computed from the instance (`hinted_sound`, `hinted_iff_least_le`, `hintedFind_agree`,
  `boundsOn_iff_hinted`).
* `FastPath`: a finite table with answers is answered at a cost fixed before the program
  (`fast_path`; for checkers answering `0` or `1`, fixed by the table of instances alone,
  `fast_path_checker`), while programs with the same answers can cost more than any bound (`padded`).
* `SearchBudgets`: the tree's budgeted certificate checker at budget `k`, the ambient search at budget
  `k` and a search with hint `k` say yes under one condition, the least certificate at most `k`
  (`certDecider_equal_iff`, `same_yes_condition`): a region does not find certificates sooner; what it
  adds is the no, which the ambient check never gives (`certDecider_never_different`).
* `TreeUnifier`: the unifier's round count is the least budget at which its run finishes
  (`drive_finished_iff`, `roundsWF_least`).
* `TreeChecker`: the definition checker's acceptance table is answered from budget 16 on
  (`table_answered`).
-/
