import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Families
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilySolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.StoppedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FamilyControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetNarrowing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PatternRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.LevelChoice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DomainRaising
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DomainRaisingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.RaiseContract
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ConditionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FitLevelChoice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Widening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrueMeetControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MeetLevelChoice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigid
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ArrowControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SeveralUnary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.LeastUniverse
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbMeet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerOpening
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerIntersection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerReading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerRules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerRank
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDecided
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.LowersToControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TowerGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidGlbControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.StrictInitiality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Trimming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbGroupsInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDomainsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.FlexRigidInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlb
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.TrimmingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbRound
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbDecided
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerGlbRoundControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PatternInitiality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerRunInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerInitialControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinContexts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinTyping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinSolverControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeet
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeetControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeetSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.JoinMeetSolverControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinNecessity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.GlbJoinInitialControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.SharedRankSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CrossAtNecessary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainForcing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainRule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainReading
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainDecompose
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainInitialControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainArrowsInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.UnionInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRank
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedStores
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRankJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRankGroups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.OneSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughLater
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughLaterControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentCodomains
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentCodomainsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentNarrowing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedJoinControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedObstructionControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughRead
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughReadControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhases
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.ThroughPhasesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentDecide
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.DependentDecideControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MixedGroupsControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.RankRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAudit
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAuditControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.WideMiller
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.WideMix
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.WideMixControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PermutedJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PermutedJoinControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PhasesInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PhasesInitialControls

/-!
# Unification in the tree's own dependent fibre

The re-founded unification, carried from its codes model into the tree's fibre (`ContextualDependentEta.frames`: typed
telescopes, typed terms up to typed βη-equality with cumulative subtyping, typed context morphisms) and its worklist
driver (`ContextualDependentWorklist`).

* `Families`: universe families and η-long unknowns; the rules **delete** and **inversion**, each an update of the
  driver and exact through `exact_iff_update`.
* `FamilySolver`: a solver of the tree's driver with these rules; the fragment of grouped families; **progress by
  shape** (`familyRound_ne_stuck`), the rules keep the fragment (`familyRound_stable`), and the driver decides it
  (`family_decided`): every store of the fragment has a principal answer (`principal_of_inFragment`).
* `StoppedRuns`: the same rules as exact transitions; every stopped run from the fragment is empty
  (`stopped_empty`).
* `FamilyControls`: a store decided by a kernel run; the cross store outside the fragment and postponed; an
  undecided level comparison postponed without a direction chosen; disagreeing annotations.
* `MeetNarrowing`: **meet narrowing** at any declaration, with the tree's semantic hypothesis `forced` proved from the
  shape of the equation, read from the codes, exact.
* `MeetControls`: the rule fires on the tree's `narrowStore` and the tree's solver then commits; narrowing below
  the meet loses a solution; the rule does not fire on the cross store.
* `PatternRules`: the tree's **pruning** and **intersection** updates, exact; their controls.
* `LevelChoice`: the rules read no level valuation; a step is stuck exactly when the comparison is undecided; in
  the tower the comparison is an entailment over all valuations, and the reading is one function at every valuation.
* `DomainRaising`: **domain raising**, the meet of two views when one of them is the meet, `G := λ x. F x`, with
  its forcing proved through the tree's context widening; exact.
* `DomainRaisingControls`: a store of the cross shape decided by it with a principal answer; on the cross store
  neither unknown fits the other.
* `RaiseContract`: domain raising on a whole store, the other equations re-read as `λ y. F y` where they read
  `λ y. G y` (no new redex); exact.
* `FitSolver`: a solver of the tree's driver with delete and domain raising, on the fragment of **fitting groups**
  (unary families; within a group, of two different unknowns one fits the other; declared domains may differ):
  progress by shape, kept by every rule, decided, every store with a principal answer.
* `FitControls`: kernel runs of that solver on a store of the cross shape and on a store where the re-reading is
  used; the cross store read, outside the grouping, and postponed.
* `ConditionControls`: a store just outside the condition that every declaration is a universe family: neither
  solver acts, the store is postponed and solvable.
* `FitLevelChoice`: the step of the solver of fitting groups is stuck exactly when neither unknown fits the other,
  and its reading is one function at every valuation of the tower.
* `MillerGlbRound`: the Miller solver without the chain of codomains. Its one stuck shape (two flex sides of
  different unknowns covering each other, incomparable codomains) becomes one round: both unknowns lowered, in
  place, to a greatest lower bound, then solved; the lowering keeps the reading and the rank, so the Miller rank
  orders the round.
* `MillerGlbDecided`: the Miller step is stuck only on that shape (`stepView_stuck`); the rounds keep the fragment
  without the chain; progress by shape for a total greatest lower bound; decided (`millerGlb_decided`).
* `MillerGlbRoundControls`: kernel runs in the tower: the permutation with incomparable codomains and a store pruned
  and then lowered commit, where the Miller solver is stuck; the Miller fragment and its refutations go through.
* `PatternInitiality`: **pattern-covered answers are epimorphisms** (`pattern_injective`, `epi_of_patternCovered`);
  the trimming theorem for answers whose mentioned unknowns are pattern-covered (`initial_of_patternTrimmed`).
* `MillerRunInitial`: the run invariant of the Miller solver (`MillerInv`), kept by every round, pruning in place
  included (`PatternCovered.pruned`); every solved run, trimmed, is the initial solution
  (`millerGlb_solved_initial`, `millerGlb_initial`).
* `MillerInitialControls`: the store whose two sides are pruned in place, outside the fixed-support trimming theorem,
  has an initial solution; so do the stores with incomparable codomains.
* `JoinContexts`: joins of telescopes (`JoinOf`); weak-head reduction and type equality carried into a wider
  telescope; **subtyping reflected by narrowing** for types of the wide telescope (`below_wide`).
* `JoinTyping`: **the join of typings** (`typed_join`): a normal term of a type over two telescopes has it over their
  join, by induction on the term through the kernel's bidirectional typing (synthesized types are the same or
  universes with a least upper bound, `TJoin`).
* `JoinForcing`: η-long forms are normal (`long_normal_at`); **the join widening for η-long types**
  (`long_type_join`); what the join forces at a flex–flex equation of families of one codomain, domains not
  necessarily comparable (`joinK_forced`).
* `JoinRule`: the rule that declares one unknown again at least upper bounds of the two domains, with a codomain below
  both, and sends both unknowns to its η-expansion; exact whenever every solution is so forced (`joinMK_exact`); with
  one codomain, the join (`joinK_exact`).
* `JoinControls`: twisted domains (`X : U0 → U1 → U1`, `Y : U1 → U0 → U1`) have a principal answer
  (`twist_principal`); a redex is not normal, and a typing over one telescope only does not survive the join
  (`join_needs_common_type`); the cross store shows that a condition on codomains is needed (`join_codomain_needed`).
* `JoinSolver`: the join solver (delete, join with re-reading of the other equations' sides); its fragment,
  flex–flex equations whose two unknowns have one codomain, domains in any order, is kept by the rounds, never stuck
  for a total join function, and **decided** (`joinK_decided`, `principal_of_inJoinFragmentK`).
* `JoinSolverControls`: kernel runs in the tower: the twisted store and a two-equation store outside the fragment of
  meet groups commit; the cross store lies outside and the solver is stuck on it.
* `JoinMeet`: **the join with a meet**, codomains comparable, domains in any order: exact under the crossing, position
  by position the joined domain is the smaller-codomain unknown's own or lies below its codomain (`joinMeetK_exact`);
  domain raising and the true meet are its comparable cases (`joins_of_below`, `joins_of_above`).
* `JoinMeetControls`: twisted domains with two codomains have a principal answer, outside both fragments
  (`meetTwist_principal`); the true meet's store is solved by the same rule; the cross store fails the crossing for
  every least upper bound and has no principal answer (`cross_no_crossing`).
* `JoinMeetSolver`: **the join-meet solver**: groups of pairwise compatible families (one codomain, or comparable
  codomains with the crossing toward the smaller), equivalent codomains equal; the redeclared unknown stays compatible
  with its group (`compatJ_join`); never stuck, kept by the rounds, **decided** (`joinMeetK_decided`,
  `principal_of_inJoinMeetFragmentK`); the fragment of meet groups is contained (`inJoinMeetFragmentK_of_meet`).
* `JoinMeetSolverControls`: kernel runs in the tower: twisted stores of one and of two codomains, a chained store of
  three unknowns outside both earlier fragments, and the true meet's store commit; the cross store lies outside.
* `GlbJoin`: **the glb join**, incomparable codomains together with incomparable domains in one rule: the right unknown
  declared again at least upper bounds of the domains and a greatest lower bound of the codomains. **The joint
  widening** (`typed_widen_both`): a normal type of the join telescope that is a type of `U_a` over one side and of
  `U_b` over the other is a type of `U_a` over the join, when each widened position lies below `a` as soon as its two
  declarations lie below `a` and `b`. Exact (`glbJoinK_exact`, `glbJoinRereadK_exact`) under `CrossAt`: a position
  whose domain lies below its own codomain on both sides has each domain below the other side's codomain.
* `GlbJoinSolver`: the glb-join solver; its fragment, groups of families crossing well with no condition comparing
  codomains, is kept by the rounds (`crossAt_join`: no antisymmetry of codomains is used), never stuck for total join
  and meet functions, and **decided** (`glbJoinK_decided`); it contains the join-meet fragment, whose condition that
  equivalent codomains are equal is dropped (`inGlbJoinFragmentK_of_joinMeet`).
* `GlbJoinControls`: kernel runs in the tower: a store with incomparable codomains and incomparable domains, outside
  the join-meet fragment and stuck there, commits with a principal answer; a store whose position has a domain above
  its codomain fails the join with a meet's crossing and commits; a store with equivalent, different codomains, which
  the join-meet fragment excludes, is inside; the earlier fragments' stores commit; the cross store lies outside.
* `GlbJoinNecessity`: the condition is needed with incomparable codomains: `X : U_a → U_a`, `Y : U0 → U_b` fails it at
  a position usable on both sides, is solvable, and has no principal answer (`ctr_no_principal`, `crossAt_needed`).
* `CrossAtNecessary`: **the condition is necessary wherever it fails** (`no_principal_of_not_crossAt`): a unary
  flex–flex equation failing it, in a store solved by the identity and by a constant family, leaves the store without
  a principal answer, in every setting (`no_common_answer_cross`); the counterexample and the cross store are instances.
* `GlbJoinInitial`: **initial solutions of join answers**: widening-covered answers are epimorphisms (`wide_equal`,
  `epi_of_wideCovered`), the trimming theorem for them (`initial_of_wideTrimmed`), a run invariant kept by the join
  step at any codomain below both (`JoinInv.join`); every solved run of the glb-join solver, trimmed, is initial
  (`glbJoin_solved_initial`, `glbJoin_initial`).
* `GlbJoinInitialControls`: committed runs in the tower have initial solutions; one join step, untrimmed, is principal
  and not initial (`equivJoin_not_initial`); on incomparable codomains and domains the step's answer declares `Y`
  again at `U1 → U1 → U_1` (`twinJoin_answer`, `twinJoin_principal`).
* `UnionSolver`: **one run for the decided fragments**: absorption of the meet groups with several parameters and of
  the glb groups into the glb-join fragment; the pieces (Miller patterns, arrow codes with codomains, flex–rigid with
  codomains, glb groups, the glb join), a run that reads the piece once (`unionRun`), **decided on the union**
  (`unionRun_decided`, `union_decided`); a store read into no piece is pending (`unionRun_of_none`).
* `UnionControls`: the tower's classifier; kernel runs of the one entry point on every piece, unknowns at codomains on
  both sides of a Π type included (`dec_union`); stores just outside each boundary read into no piece and pending: the
  glb join's condition, Miller's exact domains, `X y y`, a dependent Π type (`dep_union`), a store mixing families with
  arrow codes among them.
* `SharedRankSolver`: one solver of the tree's driver for the three pieces whose rank counts equations, reading the
  piece at every round; **decided on their union** (`shared_decided`).
* `CodomainForcing`: **unknowns at codomain positions**: a normal type whose weakening is a type of a universe is one
  already (`strengthen_normal`, the tree's typing reflection for normal terms at the weakening); a type of `U_u` equal to
  `Π (_ : A). C` makes `C` equal to a type of `U_u` (`small_codomain`); what a type of a universe forces at every type
  position of a normal type, codomains included (`HoldsAt.small`).
* `CodomainRule`: arrow codes with unknowns at codomains (`ArrowCod`), normal and typed; **narrowing to greatest lower
  bounds and solving, exact** for them (`codNarrowSolve_exact`).
* `CodomainReading`: arrow codes with codomains read soundly and completely (`arrowCod_of_B`, `arrowCodB_of_arrowCod`,
  `readFlexCod_complete`); the occurs check at codomains through the tree's full occurs check (`cod_occurs_refutes`);
  misfit heads at codomains, with no strengthening (`arrowCod_misfit`, `cod_misfitHead_refutes`); instantiation keeps
  the codes (`arrowCod_subst_solve`).
* `CodomainSolver`: **flex–rigid stores with unknowns at codomains, decided** (`flexCod_decided`): delete, the two
  refutations, narrowing to greatest lower bounds and solving; the fragment without the chain is contained
  (`inFlexCod_of_flexRigidGlb`).
* `CodomainControls`: `X ≐ Π (_ : U0). Y` over `X : U1, Y : U2`, outside the earlier flex–rigid fragments, has a
  principal answer by one exact step (`cod_principal`); so does `X ≐ Π (y : Y). Y`; kernel runs of the solver with
  codomains: commits, a refutation by the occurs check at a codomain, a refutation by a misfit head, a chain of two
  equations; the union run reads the store into the flex–rigid piece and commits.
* `CodomainDecompose`: **decomposition with unknowns at codomains, exact** (`decomposeCod_exact`):
  `Π (_ : A). B ≐ Π (_ : A'). B'` has exactly the solutions of `A ≐ A'` and `B ≐ B'`, by injectivity of Π types and
  strengthening of typed equality past the unused argument (`EqualStrengthening`); the codomains typed without the
  argument (`pi_cod_parts_typed`); clashes of a head with a Π type; rigid shapes read (`rigidCodOf_code`).
* `CodomainArrows`: **equations between arrow codes with unknowns at domains and codomains, decided**
  (`arrowsCod_decided`): delete, the full occurs check, misfit heads, narrowing to greatest lower bounds and solving
  in either orientation, decomposition into domains and codomains, clashes; rank (unknowns occurring, size). It
  contains the first-order fragment without its chain of declarations (`inArrowsCod_of_arrows`) and the flex–rigid
  fragment with codomains (`inArrowsCod_of_flexCod`).
* `CodomainArrowsControls`: kernel runs: unknowns at codomains on both sides commit (`dec_committedA`,
  `dec_principal`); the first-order stores, and the equation between unknowns at incomparable universes outside the
  first-order fragment, commit (`frLevelA_committed`); refutations (occurs check at a codomain, misfit head, clashes,
  domains clashing after decomposition); an equation over a telescope of families is inside and commits; just
  outside, each with a principal answer: a dependent Π type (`dep_principal`), a declaration mentioning the unknown
  met (`dd_principal`, answered over the instantiated telescope).
* The codomain rule and both codomain pieces ask only that **the unknowns met be declared at universes and no
  declaration mention them** (`CodSolvable.occurring`, `CodSolvable.apart`, `AtUniverses`, `SidesApart`), not that
  every declaration be a universe: the rule substitutes into the declarations through `subst_congr_support` and
  `subst_solveSub_fresh`.
* `CodomainInitial`: **answers with codomains, trimmed, are initial** (`flexCod_solved_initial`, `flexCod_initial`, over
  a telescope of universe families): the run invariant `CodInv` (widening covering at arity zero) is kept by narrowing
  and solving (`CodInv.narrowSolve`).
* `CodomainArrowsInitial`: **answers between arrow codes with codomains, trimmed, are initial**
  (`arrowsCod_solved_initial`, `arrowsCod_initial`): decomposition, equal heads and swapping keep `CodInv`
  (`CodInv.decompose`, `CodInv.swap`), and so does narrowing and solving over a store of arrow codes
  (`CodInv.narrowSolveCodes`).
* `UnionInitial`: **every solvable store of the union of the decided fragments, over a telescope of universe families,
  has an initial solution** (`union_initial`), from the initiality theorem of each piece.
* `CodomainInitialControls`: committed runs of both solvers have initial solutions; the union in the tower
  (`towerUnion_initial`, `decUnion_initial`); untrimmed, the cod store's principal answer is not initial
  (`codAnswer_not_initial`: `X` stays declared; the identity and the merge `X, Y := Y` agree on the answer).
* `CommonRank`: **one rank for the rules of the Miller solver and of the solver of arrow codes**, the weight of the
  occurring unknowns then the size (`commonRank`). Every Miller round lowers it on every store
  (`Miller.millerGlbRound_commonRank`: a deletion drops nodes, every other step keeps the number of equations and so
  lowers the weight); every round of the arrow solver lowers it on its fragment, where it is that solver's own rank
  (`weight_eq_count`, `arrowCodRound_commonRank`). Permutations keep it and the solutions (`commonRank_perm`,
  `equivalent_perm`); rounds carried between ranks (`retarget`) and along equivalences (`transport`).
* `MixedStores`: **a Miller round keeps an equation between arrow codes one** (`Miller.arrowEq_reread`: an unknown at
  a universe is answered by an unknown at a universe; `Miller.arrowEq_lowered`), and keeps Miller equations; a mixed
  store (a telescope of universe families, every equation a Miller equation or one between arrow codes) stays mixed
  (`Miller.millerGlbRound_mixed`). The other direction fails: an arrow answer `X := t` turns `λ ȳ. X` into `λ ȳ. t`.
* `MixedSolver`: **one solver, one rank, for stores mixing Miller patterns and arrow codes** (`mixedSolver`): the arrow
  round on stores of arrow codes, otherwise the Miller equations first; kept, never stuck, **decided**
  (`mixed_decided`). Its fragment contains the Miller fragment, the fragment of arrow codes and the flex–rigid fragment
  with codomains.
* `MixedControls`: the blend store, which the earlier union left pending, commits in both orders; a store sharing an
  unknown between a Miller equation under a binder and an equation between arrow codes commits in both orders; what
  an arrow-first order would leave is outside the fragment, pending, and solvable (`shLeft_*`); one round raises the
  Miller rank and lowers the common rank (`dec_round_ranks`).
* `CommonRankJoin`: the glb join lowers the common rank (`support_joinSide`, `occ_joinStore`, `weight_joinStore_lt`,
  `glbJoinRoundK_commonRank`), and so do the flex–rigid rules with codomains on their fragment
  (`flexCodRound_commonRank`).
* `CommonRankGroups`: the rules of the glb groups (delete, raising, the true meet, the greatest-lower-bound rule, both
  orientations) lower the common rank (`weight_contract_lt`, `weight_lowerHom`, `glbGroupRound_commonRank`).
* `OneSolver`: **one solver of the tree's driver, one rank, every piece** (`oneSolver`): the piece read at every round,
  arrow codes, the glb join, glb groups, the Miller equations first, or the families with parameters first; kept, never
  stuck, **decided** (`one_decided`); every piece of the earlier union lies inside (`inOne_of_piece`,
  `one_decided_of_piece`), and so do both kinds of mixed stores (`inOne_of_mixed`, `inOne_of_mixedJoin`).
* `MixedJoin`: **a glb-join step keeps an equation between arrow codes one** (`arrowEq_joinSide`: on unknowns at
  universes the step is a renaming); stores mixing glb-join families with arrow codes (`MixedJoinStore`) are decided by
  one solver with one rank, the families with parameters first (`mixedJoinSolver`, `mixedJoin_decided`).
* `MixedJoinControls`: the spare store's glb-join equation with an equation between arrow codes: in no piece of the
  earlier union, the Miller-and-arrows solver stuck on it, the mixed join solver commits in both orders.
* `MixedObstructionControls`: **where the one-rank solvers stop**: a Miller permutation with a glb-join equation sharing
  an unknown; each alone is decided, together solvable and in neither mixed fragment; either answer, instantiated in the
  other's side, leaves a β-redex that no reader reads (`mj_stuck_store`, `mj_stuck_redex`, `mj_stuck_join`). The tree's
  in-place solver decides it (`ThroughPhasesControls`).
* `ThroughLater`: **declarations that mention an unknown being solved**: an answer lifted past a later declaration
  instantiates it (`settles_later`, `later_target`, through `Update.lift`), an exchange of the two newest declarations
  reorders the telescope; the stores built so from a fragment (`Through`) are settled when the fragment is
  (`through_settles`); for the arrow codes, by a run of their solver (`throughArrows_settles`).
* `ThroughLaterControls`: the dd store is the store over `X : U1` read past `y : X`, settled, and its answer declares
  `y : Π (_ : U0). U0` (`dd_instantiated`); a store needing a reordering (`X ≐ Π (_ : Z). Z` over `X : U1, y : X, Z : U0`)
  is settled through an exchange and has a principal answer (`re_principal`).
* `DependentCodomains`: **solving needs no shape**: `X := t` is exact whenever `t` is a type of `X`'s universe, `X` does
  not occur in it and no declaration mentions `X` (`fitSolveUpdate`, `fitSolve_exact`, `fitSolve_principal`); codomains
  that use their argument included.
* `DependentNarrowing`: **narrowing through a binder whose codomain uses its argument**. Type positions read through
  every binder (`HoldsAtD`, `holdsAtD_of_support`); what a type of a universe forces there (`HoldsAtD.small`: the small
  Π type's codomain converted to the instantiated domain, the forcing under the lifted substitution, the normal form
  back through the weakening, `small_under`); dependent codes (`DepCode`: used bound variables bound by universes below
  `u`; the arrow codes with codomains among them, `depCode_of_arrowCod`) typed (`depCode_typed`); **narrowing and
  solving, exact** (`depNarrowSolveUpdate`, `depNarrowSolve_exact`); the occurs check and misfit heads through every
  binder (`dep_occurs_refutes`, `piCode_misfit`, `dep_misfitHead_refutes`); **one equation with a dependent code is
  decided** (`dep_settles`).
* `DependentCodomainsControls`: the dep store and `X ≐ Π (y : U0). Π (_ : Y). y` (an unknown inside a codomain that
  uses its argument) have principal answers by the rule that solves a right side that fits; with `Y` declared above
  `X`'s universe the store is settled by narrowing through the binder and has a principal answer
  (`depHigh_principal`); the occurs check and a misfit domain refute through the binder (`depOcc_refuted`,
  `depMis_refuted`).
* `ThroughRead`: **the reader of stores through later declarations**: with a budget of steps, the fragment's reader, or
  strip the newest declaration when every equation strengthens past it, or exchange the two newest declarations when
  the newer does not depend on the older; it returns the derivation it finds (`throughRead`, `throughRead_sound`,
  `throughRead_settles`); the one solver's fragment is settled, and so is every store through later declarations over
  it (`one_settles`, `throughOne_settles`).
* `ThroughReadControls`: the reader reads the dd store in one step and the reordering store in two; it does not read a
  store that meets a declaration mentioning an unknown (`met_unread`: `X ≐ Π (_ : U0). U0`, `y ≐ y'` over
  `X : U1, y : X, y' : X`), which is solvable; **the common rank is not lowered by an answer that instantiates a
  declaration into a Π-type** (`met_weight`, `met_after_weight`: 3 before, 4 after).
* `ThroughPhases`: **deciding in phases**: the equations that strengthen past the newest declaration first, their
  finished update lifted past it and the other equations instantiated and put in η-long form, then decided; or the two
  newest declarations exchanged; from any base decision (`Decided`, `Decided.ofRun`, `phaseAt`, `exchangeAt`,
  `phases`); every store so decided is settled (`phases_settles`).
* `ThroughPhasesControls`: the met store decided in two phases from the mixed solver, with a principal answer
  (`met_phases`, `met_principal`); the dd store in one, the reordering store through an exchange; with the mixed solver,
  the mixed join solver and the tree's in-place solver as the base, a store none of them decides alone is decided in
  two phases (`coop_alone`, `coop_phases`, `coop_principal`); the Miller-with-glb-join store and `y ≐ y'` alone are
  decided by the in-place solver (`mj_inPlace`, `metFlex_inPlace`).
* `DependentDecide`: **one equation with a dependent code, decided as data**: the equation read (`readFlexDep`,
  `depCodeB`, `depCode_of_B`), the heads read with a choice of heads (`headsFitB`, `misfitHead`), then deleted, refuted
  by the occurs check or a misfit head, or solved by narrowing (`depDecide`); a base decision for the phases (`depBase`);
  **complete on the class of `dep_settles`** whose heads the choice of heads types (`depCodeB_iff`,
  `readFlexDep_complete`, `depDecide_complete`).
* `DependentDecideControls`: the dependent-code stores decided by computation (`depHigh_decided` by narrowing,
  `depOcc_decided` and `depMis_decided` refuted); a store with a narrowing equation and `w ≐ w'` is decided in two
  phases only with the decision of dependent codes in the base (`dh_without`, `dh_phases`, `dh_principal`).
* `MixedGroupsControls`: the two-level-variable glb group with an equation between arrow codes is a mixed store, the
  level equation read by the Miller reader with its glb round; the mixed solver decides it (`lg_committed`,
  `lg_principal`), the solver of glb groups alone does not.
* `RankRuns`: **runs with no budget of rounds**, for every solver of the driver, since every progress lowers the
  solver's own rank: by well-founded recursion (`driveWF`, `runWF`), never cut off (`driveWF_finished`), equal to every
  run with a budget that finishes (`drive_eq_driveWF`), in particular at a budget of its own number of rounds
  (`drive_eq_driveWF_of_rounds`), and deciding exactly what some budget decides (`driveWF_decided_iff`); the same run
  by structural recursion with its budgets read off the rank, evaluated by the kernel (`runRank`,
  `driveRank_eq_driveWF`); fragments decided with no budget (`fragment_decidedWF`), the one solver's among them
  (`one_decidedWF`, `one_decidedWF_iff`).
* `InPlaceAudit`: in the tower, solutions, principal answers and initial solutions do not depend on the valuation of the
  level variables (`solvable_valuation_free`, `principal_valuation_free`, `initial_valuation_free`); decisions read off
  runs with no budget (`Decided.ofRank`), the same as every budget's that decides (`Decided.ofRank_eq_ofRun`,
  `Decided.ofRank_isSome_iff`).
* `InPlaceAuditControls`: the tree's in-place solver driven by its rank: level variables rigid (`clash_refuted`, though
  the controls' valuation gives both universes one level, `clash_levels_agree`; `max_committed`), cumulativity used
  (`cumul_committed`, `orient_committed` where the tree's step is stuck); stuck on a universe misfit that the mixed
  solver refutes and on codomains at incomparable level variables (`misfit_inPlace_stuck`, `level_inPlace_stuck`); the
  Miller-with-glb-join obstruction decided (`mj_rank_committed`), but with crossed domains every solver of the tree is
  stuck at every budget, though the store is solvable and each equation alone is decided (`cx_stuck_everywhere`,
  `cx_solvable`, `cx_parts_decided`); the met store decided in one run (`met_rank_committed`); the phases from bases
  with no budget of rounds (`coop_phases_rank`); the blend store committed by the common rank with no budget
  (`blend_rank_committed`).
* `WideMiller`: **wide Miller sides**, an unknown applied to distinct binders of universes below its domains, typed
  through a renaming that is a typed substitution (`sideRen_typedW`), read (`readFlexW`, `readWide`); a re-reading of
  every side on its own (`rereadStoreW`, `rereadStoreW_models`, `weight_value_ltW`); **the direction by domain order**,
  a Miller side of `X` against a wide side of `Y` solved by `X := λ x̄. Y x_σ`, exact (the forcing asks only that `X`'s
  domains be the binders') and lowering the common rank (`wideSolveRound`, `wideSolver`).
* `WideMix`: the glb join's answer as answer data for the Miller re-reading (`joinAnswer`, `opened_typedW`); **the join
  with the other equations re-read side by side**, exact, lowering the common rank (`joinMillerUpdate`,
  `occ_joinMiller`, `weight_joinMiller_lt`); **one solver, the common rank, for Miller patterns mixed with glb-join
  families** (`mixWideSolver`): families first, delete, join, Miller round, direction by domain order.
* `WideMixControls`: the residual of a join (`λ x y. F x y ≐ λ x y. Z y x`, read by neither earlier reader) solved;
  the crossed mix of `InPlaceAuditControls` and the obstruction store commit with principal answers (`cx_committed`,
  `mj_committed`); the earlier pieces commit; two wide unknowns crossed under a permutation stay stuck.
* `PermutedJoin`: β along a spine of variables typed by cumulativity (`beta_appsW`, `reread_equalW`); the re-reading of
  exact and wide sides (`rereadStoreP`); **declaring an unknown again with its arguments permuted**, exact for every
  value (`pruned_all`, `permuteUpdate`) and keeping the weight (`weight_permute_le`); **the glb join under a
  permutation as one round**, lowering the common rank (`permutedJoinStep`); the solver with it (`mixPermSolver`).
* `PermutedJoinControls`: the crossed permutation of two wide unknowns commits with a principal answer
  (`crossedWide_committed`); every store the mixed wide solver decides, it decides; the cross store, without a
  principal answer, is not committed, and no run can commit it (`cross_stuck`, `cross_no_commit`).
* `PhasesInitial`: epimorphic answers compose (`comp_epi`, `then_epi`); an answer with a section is one
  (`epi_of_section`), so is the exchange of the two newest declarations (`exchange_epi`); **the phases keep answers
  epimorphic** (`phaseAt_epi`, `exchangeAt_epi`, `phases_epi`), so **a store decided in phases from bases with
  epimorphic answers has an initial solution, whatever its telescope** (`phases_initial`); such a base: a run driven by
  the rank whose answer covers its frame (`Decided.ofRankCover`, `ofRankCover_epi`). Exchanging twice gives the store
  back (`exchange_twice_remaining`), so the phases bound their exchanges by a depth, not by a rank.
* `PhasesInitialControls`: from the in-place solver with covering answers, the reordering store (through an exchange),
  the dd store and the met store have initial solutions (`re_initial`, `dd_initial`, `met_initial`); the cooperation
  store, whose glb join declares an unknown again, is not decided so (`coop_not_covered`).
-/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

-- Families: the rules and their exactness
#print axioms TreeFibre.famCode_inj
#print axioms TreeFibre.etaExp_inj
#print axioms TreeFibre.etaExp_equal
#print axioms TreeFibre.flex_values_equal
#print axioms TreeFibre.delete_exact
#print axioms TreeFibre.invert_exact

-- FamilySolver: reading, progress by shape, stability, decision
#print axioms TreeFibre.readFlexData_complete
#print axioms TreeFibre.readFlexData_sound
#print axioms TreeFibre.FlexFlex.unique
#print axioms TreeFibre.transport_nonempty
#print axioms TreeFibre.inFragment_delete
#print axioms TreeFibre.inFragment_invert
#print axioms TreeFibre.familyRound_ne_stuck
#print axioms TreeFibre.familyRound_stable
#print axioms TreeFibre.familyRound_ne_refuted
#print axioms TreeFibre.family_decided
#print axioms TreeFibre.drive_ne_refuted
#print axioms TreeFibre.principal_of_inFragment
#print axioms TreeFibre.inFragment_of_B

-- StoppedRuns: the exact-transition reading
#print axioms TreeFibre.reaches_preserves
#print axioms TreeFibre.reaches_inFragment
#print axioms TreeFibre.stopped_empty
#print axioms TreeFibre.stopped_principal

-- FamilyControls
#print axioms TreeFibre.Controls.fit_inside
#print axioms TreeFibre.Controls.fit_committed
#print axioms TreeFibre.Controls.fit_principal
#print axioms TreeFibre.Controls.cross_unread
#print axioms TreeFibre.Controls.cross_outside
#print axioms TreeFibre.Controls.cross_postponed_by_families
#print axioms TreeFibre.Controls.level_undecided
#print axioms TreeFibre.Controls.level_read
#print axioms TreeFibre.Controls.level_stuck
#print axioms TreeFibre.Controls.level_postponed
#print axioms TreeFibre.Controls.level_solvable
#print axioms TreeFibre.Controls.mixed_unread
#print axioms TreeFibre.Controls.mixed_unsolvable

-- MeetNarrowing
#print axioms TreeFibre.lookup_lowerAt_self
#print axioms TreeFibre.lookup_lowerAt_ne
#print axioms TreeFibre.lowerAt_narrows
#print axioms TreeFibre.lowerAt_formed
#print axioms TreeFibre.forced_small
#print axioms TreeFibre.forced_meet
#print axioms TreeFibre.meet_exact
#print axioms TreeFibre.holdsVar_of_mem
#print axioms TreeFibre.readMeetData_sound
#print axioms TreeFibre.meetRule_exact

-- MeetControls
#print axioms TreeFibre.Controls.narrow_meet_fires
#print axioms TreeFibre.Controls.narrowMeet_committed
#print axioms TreeFibre.Controls.narrow_principal_by_meet
#print axioms TreeFibre.Controls.over_meet_fires
#print axioms TreeFibre.Controls.over_solution_models
#print axioms TreeFibre.Controls.over_narrowing_loses
#print axioms TreeFibre.Controls.cross_no_meet

-- PatternRules
#print axioms TreeFibre.intersectRule_exact
#print axioms TreeFibre.pruneFlexFlex_exact
#print axioms TreeFibre.Controls.intersection_found_exact
#print axioms TreeFibre.Controls.intersection_principal
#print axioms TreeFibre.Controls.twice_principal
#print axioms TreeFibre.Controls.pruned_exact

-- LevelChoice
#print axioms TreeFibre.stepOf_stuck_iff
#print axioms TreeFibre.tower_cumulative_iff
#print axioms TreeFibre.readFlexData_valuation_free
#print axioms TreeFibre.allFamiliesB_valuation_free

-- DomainRaising
#print axioms TreeFibre.raised_typed
#print axioms TreeFibre.beta_fresh
#print axioms TreeFibre.raise_forced
#print axioms TreeFibre.raise_exact

-- DomainRaisingControls
#print axioms TreeFibre.Controls.raise_principal
#print axioms TreeFibre.Controls.raise_unread
#print axioms TreeFibre.Controls.cross_no_fit
#print axioms TreeFibre.Controls.cross_no_fit_swapped

-- RaiseContract
#print axioms TreeFibre.etaExp_congr
#print axioms TreeFibre.contractSide_cases
#print axioms TreeFibre.contract_sound
#print axioms TreeFibre.contract_complete
#print axioms TreeFibre.raise_head_solved
#print axioms TreeFibre.raiseContract_exact

-- FitSolver
#print axioms TreeFibre.FitFlex.unique
#print axioms TreeFibre.readFitData_complete
#print axioms TreeFibre.readFitData_sound
#print axioms TreeFibre.contractSide_reread
#print axioms TreeFibre.contractSide_keep
#print axioms TreeFibre.contract_view
#print axioms TreeFibre.inFitFragment_delete
#print axioms TreeFibre.inFitFragment_raise
#print axioms TreeFibre.fitRound_ne_stuck
#print axioms TreeFibre.fitRound_stable
#print axioms TreeFibre.fitRound_ne_refuted
#print axioms TreeFibre.fit_decided
#print axioms TreeFibre.principal_of_inFitFragment
#print axioms TreeFibre.inFitFragment_of_B

-- FitControls
#print axioms TreeFibre.Controls.raise_inside_fit
#print axioms TreeFibre.Controls.raise_fit_committed
#print axioms TreeFibre.Controls.raise_fit_principal
#print axioms TreeFibre.Controls.three_inside
#print axioms TreeFibre.Controls.three_committed
#print axioms TreeFibre.Controls.three_principal
#print axioms TreeFibre.Controls.cross_fit_read
#print axioms TreeFibre.Controls.cross_not_fit_inside
#print axioms TreeFibre.Controls.cross_fit_stuck
#print axioms TreeFibre.Controls.cross_postponed_by_fit

-- ConditionControls
#print axioms TreeFibre.Controls.dependent_unread
#print axioms TreeFibre.Controls.dependent_stuck_families
#print axioms TreeFibre.Controls.dependent_stuck_fit
#print axioms TreeFibre.Controls.dependent_solvable

-- FitLevelChoice
#print axioms TreeFibre.stepFit_stuck_iff
#print axioms TreeFibre.readFitData_valuation_free

-- Widening: the meet lemma on normal forms
#print axioms TreeFibre.NarrowsBelow.narrows
#print axioms TreeFibre.NarrowsBelow.lookup
#print axioms TreeFibre.typed_widen
#print axioms TreeFibre.small_of_widen

-- TrueMeet: the forcing at the meet, the lowering, the rule
#print axioms TreeFibre.famCode_isType
#print axioms TreeFibre.meet_forced
#print axioms TreeFibre.setFamAt_substMor
#print axioms TreeFibre.setFamAt_formed
#print axioms TreeFibre.lower_exact
#print axioms TreeFibre.trueMeet_exact

-- MeetGroups: the fragment of meet groups, decided by shape
#print axioms TreeFibre.Compat.meet
#print axioms TreeFibre.inMeetFragment_of_fit
#print axioms TreeFibre.inMeetFragment_raise
#print axioms TreeFibre.lower_view
#print axioms TreeFibre.meetComparable_lowered
#print axioms TreeFibre.inMeetFragment_meet
#print axioms TreeFibre.meetGroupRound_ne_stuck
#print axioms TreeFibre.meetGroupRound_stable
#print axioms TreeFibre.meetGroupRound_ne_refuted
#print axioms TreeFibre.meetGroup_decided
#print axioms TreeFibre.principal_of_inMeetFragment
#print axioms TreeFibre.inMeetFragment_of_B

-- TrueMeetControls
#print axioms TreeFibre.Controls.meet_inside
#print axioms TreeFibre.Controls.meet_not_fit
#print axioms TreeFibre.Controls.meet_fit_stuck
#print axioms TreeFibre.Controls.meet_committed
#print axioms TreeFibre.Controls.meet_principal
#print axioms TreeFibre.Controls.overMeet_solution_models
#print axioms TreeFibre.Controls.over_meet_loses
#print axioms TreeFibre.Controls.chain_inside
#print axioms TreeFibre.Controls.chain_committed
#print axioms TreeFibre.Controls.chain_principal
#print axioms TreeFibre.Controls.cross_only_crossing_fails
#print axioms TreeFibre.Controls.crossing_needed
#print axioms TreeFibre.Controls.cross_not_meet_inside
#print axioms TreeFibre.Controls.cross_meet_stuck
#print axioms TreeFibre.Controls.cross_postponed_by_meet

-- SeveralForcing: raising and the meet under several binders
#print axioms TreeFibre.forall₂_trans
#print axioms TreeFibre.forall₂_below
#print axioms TreeFibre.beta_open
#print axioms TreeFibre.openK_typed
#print axioms TreeFibre.raisedK_typed
#print axioms TreeFibre.raiseK_forced
#print axioms TreeFibre.meetK_small

-- SeveralRules: the rules with several parameters
#print axioms TreeFibre.FlexK.unique
#print axioms TreeFibre.etaExpK_congr
#print axioms TreeFibre.raiseK_value
#print axioms TreeFibre.contractK_sound
#print axioms TreeFibre.contractK_complete
#print axioms TreeFibre.raiseK_head_solved
#print axioms TreeFibre.raiseContractK_exact
#print axioms TreeFibre.meetK_forced
#print axioms TreeFibre.lowerK_exact
#print axioms TreeFibre.trueMeetK_exact

-- SeveralGroups: meet groups with several parameters, decided by shape
#print axioms TreeFibre.CompatK.meet
#print axioms TreeFibre.contract_viewK
#print axioms TreeFibre.inMeetFragmentK_raise
#print axioms TreeFibre.lower_viewK
#print axioms TreeFibre.meetComparableK_lowered
#print axioms TreeFibre.inMeetFragmentK_meet
#print axioms TreeFibre.readFlexK_complete
#print axioms TreeFibre.readFlexK_sound
#print axioms TreeFibre.meetGroupRoundK_ne_stuck
#print axioms TreeFibre.meetGroupRoundK_stable
#print axioms TreeFibre.meetGroupRoundK_ne_refuted
#print axioms TreeFibre.meetGroupK_decided
#print axioms TreeFibre.principal_of_inMeetFragmentK
#print axioms TreeFibre.inMeetFragmentK_of_B

-- SeveralControls
#print axioms TreeFibre.Controls.binFit_inside
#print axioms TreeFibre.Controls.binFit_unread
#print axioms TreeFibre.Controls.binFit_committed
#print axioms TreeFibre.Controls.binFit_principal
#print axioms TreeFibre.Controls.binMeet_inside
#print axioms TreeFibre.Controls.binMeet_no_fit
#print axioms TreeFibre.Controls.binMeet_committed
#print axioms TreeFibre.Controls.binMeet_principal
#print axioms TreeFibre.Controls.binMixed_inside
#print axioms TreeFibre.Controls.binMixed_committed
#print axioms TreeFibre.Controls.binMixed_principal
#print axioms TreeFibre.Controls.meet_insideK
#print axioms TreeFibre.Controls.meet_committedK
#print axioms TreeFibre.Controls.chain_committedK
#print axioms TreeFibre.Controls.cross_not_meet_insideK
#print axioms TreeFibre.Controls.cross_meet_stuckK
#print axioms TreeFibre.Controls.cross_postponed_by_meetK
#print axioms TreeFibre.Controls.twist_solvable
#print axioms TreeFibre.Controls.twist_not_inside
#print axioms TreeFibre.Controls.twist_stuck

-- MeetLevelChoice
#print axioms TreeFibre.stepMeetGroup_stuck_iff
#print axioms TreeFibre.stepMeetGroupK_stuck_iff
#print axioms TreeFibre.readFlexK_valuation_free
#print axioms TreeFibre.meetComparableKB_valuation_free

-- FlexRigid: arrow codes, narrow-and-solve, the refutations
#print axioms TreeFibre.subst_solveSub_fixed
#print axioms TreeFibre.arrow_subst_solve
#print axioms TreeFibre.arrow_domainOccurrence
#print axioms TreeFibre.arrow_typed
#print axioms TreeFibre.arrow_misfit
#print axioms TreeFibre.lowerSet_narrows
#print axioms TreeFibre.lowerSet_formed
#print axioms TreeFibre.narrowSolve_typed
#print axioms TreeFibre.misfit_forced
#print axioms TreeFibre.narrowSolve_exact
#print axioms TreeFibre.occurs_refutes
#print axioms TreeFibre.misfit_refutes

-- FlexRigidSolver: the fragment of flex-rigid stores, decided by shape
#print axioms TreeFibre.readFlexArrow_complete
#print axioms TreeFibre.narrowSolve_view
#print axioms TreeFibre.narrowed_chain
#print axioms TreeFibre.inFlexRigid_narrowSolve
#print axioms TreeFibre.solvable_of_B
#print axioms TreeFibre.misfit_apart
#print axioms TreeFibre.flexRigidRound_ne_stuck
#print axioms TreeFibre.flexRigidRound_stable
#print axioms TreeFibre.flexRigid_decided
#print axioms TreeFibre.inFlexRigid_of_B

-- FlexRigidControls
#print axioms TreeFibre.Controls.frNarrow_inside
#print axioms TreeFibre.Controls.frNarrow_committed
#print axioms TreeFibre.Controls.frNarrow_principal
#print axioms TreeFibre.Controls.frChain_inside
#print axioms TreeFibre.Controls.frChain_committed
#print axioms TreeFibre.Controls.frChain_principal
#print axioms TreeFibre.Controls.frOccurs_inside
#print axioms TreeFibre.Controls.frOccurs_refuted
#print axioms TreeFibre.Controls.frOccurs_unsolvable
#print axioms TreeFibre.Controls.frMisfit_inside
#print axioms TreeFibre.Controls.frMisfit_refuted
#print axioms TreeFibre.Controls.frMisfit_unsolvable
#print axioms TreeFibre.Controls.frTooLarge_refuted
#print axioms TreeFibre.Controls.frLevel_outside
#print axioms TreeFibre.Controls.frLevel_stuck
#print axioms TreeFibre.Controls.frLevel_solvable
#print axioms TreeFibre.Controls.frOver_outside
#print axioms TreeFibre.Controls.frOver_stuck
#print axioms TreeFibre.Controls.frOver_solvable
#print axioms TreeFibre.Controls.frTwice_outside
#print axioms TreeFibre.Controls.frTwice_stuck

-- ArrowRules: decomposition, equal heads, clashes
#print axioms TreeFibre.head_typed_everywhere
#print axioms TreeFibre.pi_parts_typed
#print axioms TreeFibre.decompose_exact
#print axioms TreeFibre.headEq_exact
#print axioms TreeFibre.headClash_refutes
#print axioms TreeFibre.headPi_refutes
#print axioms TreeFibre.piHead_refutes
#print axioms TreeFibre.codomainClash_refutes

-- ArrowSolver: the rank and the step
#print axioms TreeFibre.filter_length_lt
#print axioms TreeFibre.rank_drop
#print axioms TreeFibre.arrowRank_swap
#print axioms TreeFibre.occursIn_solved
#print axioms TreeFibre.rank_solved
#print axioms TreeFibre.inArrows_solved
#print axioms TreeFibre.rigidOf_arrow

-- ArrowDecision: equations between arrow codes, decided by shape
#print axioms TreeFibre.readArrowEq_complete
#print axioms TreeFibre.inArrows_decompose
#print axioms TreeFibre.stepArrow_ne_stuck
#print axioms TreeFibre.stepArrow_stable
#print axioms TreeFibre.arrowRound_ne_stuck
#print axioms TreeFibre.arrowRound_stable
#print axioms TreeFibre.arrows_decided
#print axioms TreeFibre.inArrows_of_B

-- ArrowControls
#print axioms TreeFibre.inArrows_of_flexRigid
#print axioms TreeFibre.Controls.twiceArrow_inside
#print axioms TreeFibre.Controls.twiceArrow_committed
#print axioms TreeFibre.Controls.twiceArrow_principal
#print axioms TreeFibre.Controls.orient_outside_flexRigid
#print axioms TreeFibre.Controls.orient_inside
#print axioms TreeFibre.Controls.orient_committed
#print axioms TreeFibre.Controls.decompose_inside
#print axioms TreeFibre.Controls.decompose_committed
#print axioms TreeFibre.Controls.decompose_principal
#print axioms TreeFibre.Controls.headClash_refuted
#print axioms TreeFibre.Controls.piHead_refuted
#print axioms TreeFibre.Controls.codomainClash_refuted
#print axioms TreeFibre.Controls.codomainClash_unsolvable
#print axioms TreeFibre.Controls.level_outside_arrows
#print axioms TreeFibre.Controls.level_stuck_arrows
#print axioms TreeFibre.Controls.over_outside_arrows
#print axioms TreeFibre.Controls.over_stuck_arrows

-- SeveralUnary: the unary fragments inside the fragment with several parameters
#print axioms TreeFibre.compatK_of_compat
#print axioms TreeFibre.inMeetFragmentK_of_meet
#print axioms TreeFibre.inMeetFragmentK_of_fit
#print axioms TreeFibre.meetGroupK_decides_unary

-- LeastUniverse: the principal-universe lemma for normal types
#print axioms TreeFibre.least_universe_spine
#print axioms TreeFibre.least_universe
#print axioms TreeFibre.least_universe_widen

-- GlbMeet: incomparable codomains, lowered to a greatest lower bound
#print axioms TreeFibre.IsGlb.symm
#print axioms TreeFibre.narrowsBelow_of_widens
#print axioms TreeFibre.small_of_glb
#print axioms TreeFibre.glb_value
#print axioms TreeFibre.glbMeets_of_meets
#print axioms TreeFibre.fitFlex_opened
#print axioms TreeFibre.glb_forced_left
#print axioms TreeFibre.glb_forced_right
#print axioms TreeFibre.CodomainLowering.families
#print axioms TreeFibre.lowerAtUpdate
#print axioms TreeFibre.lowerAt_exact
#print axioms TreeFibre.glbLowerLeft_forced
#print axioms TreeFibre.glbLowerRight_forced
#print axioms TreeFibre.glbFits
#print axioms TreeFibre.glbMeetUpdate
#print axioms TreeFibre.glbMeet_exact

-- GlbControls: the tower's greatest lower bound, U3's postponed store decided by the rule, least universes
#print axioms TreeFibre.Controls.eval_le_zeroed
#print axioms TreeFibre.Controls.glb_Ua_Ub
#print axioms TreeFibre.Controls.glb_U1_U2
#print axioms TreeFibre.Controls.not_glb_U0_U1_U2
#print axioms TreeFibre.Controls.level_glbMeets
#print axioms TreeFibre.Controls.level_glb_principal
#print axioms TreeFibre.Controls.lowers_outside
#print axioms TreeFibre.Controls.lowers_inside
#print axioms TreeFibre.Controls.least_U0
#print axioms TreeFibre.Controls.not_least_U0_U2

-- MillerOpening: binders, spines of locals, opening and β
#print axioms TreeFibre.Miller.subst_lams
#print axioms TreeFibre.Miller.index_cases
#print axioms TreeFibre.Miller.loc_injective
#print axioms TreeFibre.Miller.opened_eq
#print axioms TreeFibre.Miller.spineRen_ctxRen
#print axioms TreeFibre.Miller.subsAt_substMor
#print axioms TreeFibre.Miller.lams_typed
#print axioms TreeFibre.Miller.opened_typed
#print axioms TreeFibre.Miller.eta_opened
#print axioms TreeFibre.Miller.lams_equal_iff
#print axioms TreeFibre.Miller.apps_congr
#print axioms TreeFibre.Miller.beta_apps

-- MillerForcing: what a Miller equation forces, by substitution
#print axioms TreeFibre.Miller.subst_flexSide_opened
#print axioms TreeFibre.Miller.flexSide_typed
#print axioms TreeFibre.Miller.solves_opened
#print axioms TreeFibre.Miller.solves_of_opened
#print axioms TreeFibre.Miller.pull_cancel
#print axioms TreeFibre.Miller.pullSub_substMor
#print axioms TreeFibre.Miller.flexFlex_forced
#print axioms TreeFibre.Miller.flexLocal_forced
#print axioms TreeFibre.Miller.var_ne_head
#print axioms TreeFibre.Miller.scope_refutes
#print axioms TreeFibre.Miller.locals_refute

-- MillerIntersection: intersection forced through normal forms, pruning forced by substitution
#print axioms TreeFibre.Miller.keptPos_injective
#print axioms TreeFibre.Miller.kept_fixed
#print axioms TreeFibre.Miller.intersect_forced
#print axioms TreeFibre.Miller.prune_forced

-- MillerReading: readers that check what they read, and read every code of their shape
#print axioms TreeFibre.Miller.readFam_famCode
#print axioms TreeFibre.Miller.readFlex_flexSide
#print axioms TreeFibre.Miller.readLocal_localSide
#print axioms TreeFibre.Miller.readSide_flex
#print axioms TreeFibre.Miller.readSide_rigid

-- MillerRules: telescopes declared again in place, the answer, exactness from factoring, β re-reading
#print axioms TreeFibre.Miller.setFamAt_formed_families
#print axioms TreeFibre.Miller.redecl_families
#print axioms TreeFibre.Miller.redecl_chain
#print axioms TreeFibre.Miller.replace_exact
#print axioms TreeFibre.Miller.opened_lams
#print axioms TreeFibre.Miller.factor_of_opened
#print axioms TreeFibre.Miller.reread_equal
#print axioms TreeFibre.Miller.rereadStore_models

-- MillerSteps: delete, value, prune, refutations
#print axioms TreeFibre.Miller.subst_flexBody_opened
#print axioms TreeFibre.Miller.eq_opened
#print axioms TreeFibre.Miller.deleteSame_exact
#print axioms TreeFibre.Miller.locals_unsolvable
#print axioms TreeFibre.Miller.scope_unsolvable

-- MillerRank: supports and the rank
#print axioms TreeFibre.Miller.support_subst_sub
#print axioms TreeFibre.Miller.support_flexSide
#print axioms TreeFibre.Miller.support_localSide
#print axioms TreeFibre.Miller.occ_reread
#print axioms TreeFibre.Miller.rank_delete
#print axioms TreeFibre.Miller.weight_value_lt
#print axioms TreeFibre.Miller.weight_prune_lt

-- MillerSolver: what re-reading keeps, the steps
#print axioms TreeFibre.Miller.readEq_isSome_of_view
#print axioms TreeFibre.Miller.familyB_iff
#print axioms TreeFibre.Miller.rename_flexBody
#print axioms TreeFibre.Miller.project_shape
#print axioms TreeFibre.Miller.flex_shape
#print axioms TreeFibre.Miller.rereadSide_view
#print axioms TreeFibre.Miller.views_reread

-- MillerDecision, MillerDecided: the dispatch, progress, stability, decision
#print axioms TreeFibre.Miller.opens_flexFlex
#print axioms TreeFibre.Miller.inMiller_value
#print axioms TreeFibre.Miller.inMiller_prune
#print axioms TreeFibre.Miller.millerRound_stable
#print axioms TreeFibre.Miller.millerRound_ne_stuck
#print axioms TreeFibre.Miller.miller_decided
#print axioms TreeFibre.Miller.principal_or_unsolvable

-- MillerControls
#print axioms TreeFibre.Miller.chain_of_B
#print axioms TreeFibre.Miller.inMiller_of_B
#print axioms TreeFibre.Miller.Controls.perm_inside
#print axioms TreeFibre.Miller.Controls.perm_committed
#print axioms TreeFibre.Miller.Controls.perm_principal
#print axioms TreeFibre.Miller.Controls.prune_inside
#print axioms TreeFibre.Miller.Controls.prune_committed
#print axioms TreeFibre.Miller.Controls.prune_principal
#print axioms TreeFibre.Miller.Controls.both_inside
#print axioms TreeFibre.Miller.Controls.both_committed
#print axioms TreeFibre.Miller.Controls.both_principal
#print axioms TreeFibre.Miller.Controls.inter_inside
#print axioms TreeFibre.Miller.Controls.inter_committed
#print axioms TreeFibre.Miller.Controls.inter_principal
#print axioms TreeFibre.Miller.Controls.project_inside
#print axioms TreeFibre.Miller.Controls.project_committed
#print axioms TreeFibre.Miller.Controls.project_principal
#print axioms TreeFibre.Miller.Controls.chain_inside
#print axioms TreeFibre.Miller.Controls.chain_committed
#print axioms TreeFibre.Miller.Controls.scope_inside
#print axioms TreeFibre.Miller.Controls.scope_refuted
#print axioms TreeFibre.Miller.Controls.scope_unsolvable
#print axioms TreeFibre.Miller.Controls.locals_inside
#print axioms TreeFibre.Miller.Controls.locals_refuted
#print axioms TreeFibre.Miller.Controls.locals_unsolvable'
#print axioms TreeFibre.Miller.Controls.twice_unread
#print axioms TreeFibre.Miller.Controls.twice_postponed
#print axioms TreeFibre.Miller.misfit_unsolvable
#print axioms TreeFibre.Miller.Controls.misfit_inside
#print axioms TreeFibre.Miller.Controls.misfit_refuted
#print axioms TreeFibre.Miller.Controls.misfit_unsolvable'

-- LowersToControls: the glb rule's domain condition is needed
#print axioms TreeFibre.Controls.cross_glb
#print axioms TreeFibre.Controls.cross_not_lowers_right
#print axioms TreeFibre.Controls.glb_lowering_loses
#print axioms TreeFibre.Controls.lowersTo_needed

-- TowerGlb: the greatest lower bound of two universes of the tower
#print axioms TreeFibre.LevelGlb.mem_interParams
#print axioms TreeFibre.LevelGlb.sorted_interParams
#print axioms TreeFibre.LevelGlb.glbNF_le_left
#print axioms TreeFibre.LevelGlb.glbNF_le_right
#print axioms TreeFibre.LevelGlb.le_glbNF
#print axioms TreeFibre.LevelGlb.glbNF_wf
#print axioms TreeFibre.LevelGlb.eval_toExpr
#print axioms TreeFibre.LevelGlb.towerGlb_total
#print axioms TreeFibre.LevelGlb.towerGlb_isGlb

-- GlbGroups: the greatest-lower-bound rule inside a decided fragment
#print axioms TreeFibre.BelowPair.symm
#print axioms TreeFibre.GlbCompat.symm
#print axioms TreeFibre.below_of_not_compat
#print axioms TreeFibre.belowPair_of_meets
#print axioms TreeFibre.GlbCompat.cases
#print axioms TreeFibre.GlbCompat.lower
#print axioms TreeFibre.glbComparable_of_meetComparable
#print axioms TreeFibre.glbComparable_lowered
#print axioms TreeFibre.inGlbFragment_of_meet
#print axioms TreeFibre.inGlbFragment_delete
#print axioms TreeFibre.lowering_view
#print axioms TreeFibre.glbComparable_meet
#print axioms TreeFibre.glbComparable_glb
#print axioms TreeFibre.inGlbFragment_raise
#print axioms TreeFibre.inGlbFragment_meet
#print axioms TreeFibre.inGlbFragment_glb
#print axioms TreeFibre.glbBranch_ne_refuted
#print axioms TreeFibre.stepGlbGroup_ne_refuted
#print axioms TreeFibre.glbGroupRound_ne_refuted
#print axioms TreeFibre.glbBranch_ne_stuck
#print axioms TreeFibre.stepGlbGroup_ne_stuck
#print axioms TreeFibre.glbGroupRound_ne_stuck
#print axioms TreeFibre.glbGroupRound_stable
#print axioms TreeFibre.glbGroup_decided
#print axioms TreeFibre.principal_of_inGlbFragment
#print axioms TreeFibre.glbComparable_of_B
#print axioms TreeFibre.inGlbFragment_of_B

-- GlbGroupControls
#print axioms TreeFibre.Controls.towerGlb_Ua_Ub
#print axioms TreeFibre.Controls.towerGlb_Ua_Ua1
#print axioms TreeFibre.Controls.towerGlb_U1_Ua
#print axioms TreeFibre.Controls.below_level
#print axioms TreeFibre.Controls.not_compat_level
#print axioms TreeFibre.Controls.not_below_cross
#print axioms TreeFibre.Controls.level_glb_inside
#print axioms TreeFibre.Controls.level_not_meet_inside
#print axioms TreeFibre.Controls.level_meet_stuck
#print axioms TreeFibre.Controls.level_glb_committed
#print axioms TreeFibre.Controls.level_inside_principal
#print axioms TreeFibre.Controls.glbChain_inside
#print axioms TreeFibre.Controls.glbChain_committed
#print axioms TreeFibre.Controls.glbChain_principal
#print axioms TreeFibre.Controls.cross_only_below_crossing_fails
#print axioms TreeFibre.Controls.below_crossing_needed
#print axioms TreeFibre.Controls.cross_not_glb_inside
#print axioms TreeFibre.Controls.cross_glb_stuck

-- FlexRigidGlb: flex-rigid equations without the chain
#print axioms TreeFibre.lookup_lowerTo_some
#print axioms TreeFibre.lookup_lowerTo_none
#print axioms TreeFibre.lowerTo_narrows
#print axioms TreeFibre.lowerTo_formed
#print axioms TreeFibre.glbTarget_some
#print axioms TreeFibre.glbTarget_of_misfit
#print axioms TreeFibre.glbNarrowed_typed
#print axioms TreeFibre.glbNarrowSolve_typed
#print axioms TreeFibre.glb_misfit_forced
#print axioms TreeFibre.glbNarrowSolve_exact
#print axioms TreeFibre.inFlexRigidGlb_of_chain
#print axioms TreeFibre.glbNarrowSolve_view
#print axioms TreeFibre.inFlexRigidGlb_narrowSolve
#print axioms TreeFibre.glbSolvable_of_B
#print axioms TreeFibre.flexRigidGlbRound_ne_stuck
#print axioms TreeFibre.flexRigidGlbRound_stable
#print axioms TreeFibre.flexRigidGlb_decided
#print axioms TreeFibre.inFlexRigidGlb_of_B

-- FlexRigidGlbControls
#print axioms TreeFibre.Controls.frLevel_glb_inside
#print axioms TreeFibre.Controls.frLevel_glb_committed
#print axioms TreeFibre.Controls.frLevel_glb_principal
#print axioms TreeFibre.Controls.chain_not_needed
#print axioms TreeFibre.Controls.frThree_outside_chain
#print axioms TreeFibre.Controls.frThree_glb_inside
#print axioms TreeFibre.Controls.frThree_glb_committed
#print axioms TreeFibre.Controls.frThree_glb_principal
#print axioms TreeFibre.Controls.frNarrow_glb_committed
#print axioms TreeFibre.Controls.frChain_glb_committed
#print axioms TreeFibre.Controls.frOccurs_glb_refuted
#print axioms TreeFibre.Controls.frMisfit_glb_refuted
#print axioms TreeFibre.Controls.frOver_glb_outside
#print axioms TreeFibre.Controls.frOver_glb_stuck
#print axioms TreeFibre.Controls.frTwice_glb_outside
#print axioms TreeFibre.Controls.frTwice_glb_stuck

-- StrictInitiality: covered principal answers are initial; solving in place is not
#print axioms TreeFibre.epi_of_covered
#print axioms TreeFibre.initial_of_covered
#print axioms TreeFibre.id_covered
#print axioms TreeFibre.CodomainLowering.covered
#print axioms TreeFibre.Controls.levelTarget_lookup
#print axioms TreeFibre.Controls.levelMerge_answer
#print axioms TreeFibre.Controls.levelMerge_agrees
#print axioms TreeFibre.Controls.level_answer_not_initial

-- Trimming: deleting solved unknowns makes principal answers initial
#print axioms TreeFibre.lookup_famTeleOf
#print axioms TreeFibre.famTeleOf_formed
#print axioms TreeFibre.keptOf_nodup
#print axioms TreeFibre.mem_keptOf
#print axioms TreeFibre.get_keptAt
#print axioms TreeFibre.trim_back
#print axioms TreeFibre.initial_of_trimmed
#print axioms TreeFibre.Controls.level_same
#print axioms TreeFibre.Controls.level_fixedSupport
#print axioms TreeFibre.Controls.level_lowered
#print axioms TreeFibre.Controls.levelView'_universes
#print axioms TreeFibre.Controls.level_trimmed_initial
#print axioms TreeFibre.Controls.level_kept

-- TrimmingControls: the solver's own answer, trimmed
#print axioms TreeFibre.Controls.chainState_finished
#print axioms TreeFibre.Controls.chainState_principal
#print axioms TreeFibre.Controls.chain_same
#print axioms TreeFibre.Controls.chain_declared
#print axioms TreeFibre.Controls.chain_universes
#print axioms TreeFibre.Controls.chain_fixedSupport
#print axioms TreeFibre.Controls.chain_lowered_facts
#print axioms TreeFibre.Controls.chain_kept
#print axioms TreeFibre.Controls.chain_trimmed_initial
#print axioms TreeFibre.Controls.threeState_finished
#print axioms TreeFibre.Controls.threeState_principal
#print axioms TreeFibre.Controls.three_same
#print axioms TreeFibre.Controls.three_declared
#print axioms TreeFibre.Controls.three_universes
#print axioms TreeFibre.Controls.three_fixedSupport
#print axioms TreeFibre.Controls.three_lowered_facts
#print axioms TreeFibre.Controls.three_kept
#print axioms TreeFibre.Controls.three_trimmed_initial
#print axioms TreeFibre.Controls.permState_finished
#print axioms TreeFibre.Controls.permState_principal
#print axioms TreeFibre.Controls.perm_fixedSupport
#print axioms TreeFibre.Controls.perm_lowered_facts
#print axioms TreeFibre.Controls.perm_kept
#print axioms TreeFibre.Controls.perm_trimmed_initial
#print axioms TreeFibre.Controls.both_same
#print axioms TreeFibre.Controls.both_not_fixedSupport
#print axioms TreeFibre.Controls.ctxABW_views
#print axioms TreeFibre.Controls.glbChain_initial

-- GlbGroupsInitial: every solved run of the solver of glb groups, trimmed, is initial
#print axioms TreeFibre.mem_support_etaExp_one
#print axioms TreeFibre.subst_eq_var
#print axioms TreeFibre.etaExp_ne_var
#print axioms TreeFibre.InPlaceData.pending
#print axioms TreeFibre.InPlaceData.step
#print axioms TreeFibre.contract_avoids
#print axioms TreeFibre.lowering_keeps
#print axioms TreeFibre.meetLowering_keeps
#print axioms TreeFibre.decl_same
#print axioms TreeFibre.sub_raise
#print axioms TreeFibre.decl_meet
#print axioms TreeFibre.decl_glb
#print axioms TreeFibre.glbGroupRound_inPlace
#print axioms TreeFibre.drive_inPlace
#print axioms TreeFibre.glbGroup_solved_initial
#print axioms TreeFibre.glbGroup_initial

-- FlexRigidInitial: every solved run of the flex-rigid solver without the chain, trimmed, is initial
#print axioms TreeFibre.arrow_support
#print axioms TreeFibre.InPlaceFR.pending
#print axioms TreeFibre.InPlaceFR.step
#print axioms TreeFibre.flexRigidGlbRound_inPlace
#print axioms TreeFibre.driveFR_inPlace
#print axioms TreeFibre.flexRigidGlb_solved_initial
#print axioms TreeFibre.flexRigidGlb_initial_or_refuted

-- MillerGlb: Miller patterns with incomparable codomains, lowered to a greatest lower bound
#print axioms TreeFibre.Miller.millerGlb_forced
#print axioms TreeFibre.Miller.millerLowerF_forced
#print axioms TreeFibre.Miller.millerLowerG_forced
#print axioms TreeFibre.Miller.millerGlb_exact
#print axioms TreeFibre.Miller.Controls.levelPerm_outside
#print axioms TreeFibre.Miller.Controls.levelPerm_stuck
#print axioms TreeFibre.Miller.Controls.ctxAB2_families
#print axioms TreeFibre.Miller.Controls.levelPerm_step_some
#print axioms TreeFibre.Miller.Controls.levelPerm_lowered_committed
#print axioms TreeFibre.Miller.Controls.levelPerm_principal

-- MillerDomainsControls: the Miller fragment's exact domains are needed
#print axioms TreeFibre.Miller.Controls.cross_miller_reading
#print axioms TreeFibre.Miller.Controls.exact_domains_needed

-- MillerGlbRound / MillerGlbDecided: the Miller solver without the chain of codomains
#print axioms TreeFibre.Miller.lowering_families
#print axioms TreeFibre.Miller.lowering_views
#print axioms TreeFibre.Miller.occ_lowered
#print axioms TreeFibre.Miller.weight_lowered
#print axioms TreeFibre.Miller.millerRank_lowered
#print axioms TreeFibre.Miller.roundAfter_ne_stuck
#print axioms TreeFibre.Miller.roundAfter_progress
#print axioms TreeFibre.Miller.lowered_opens
#print axioms TreeFibre.Miller.glbSolveRound
#print axioms TreeFibre.Miller.millerGlbSolver
#print axioms TreeFibre.Miller.inMillerGlb_of_inMiller
#print axioms TreeFibre.Miller.solveRound_stableGlb
#print axioms TreeFibre.Miller.glbSolveRound_stable
#print axioms TreeFibre.Miller.stepFlexFlex_stuck
#print axioms TreeFibre.Miller.stepView_stuck
#print axioms TreeFibre.Miller.millerGlbRound_stable
#print axioms TreeFibre.Miller.millerGlbRound_ne_stuck
#print axioms TreeFibre.Miller.millerGlb_decided
#print axioms TreeFibre.Miller.principal_or_unsolvable_glb
#print axioms TreeFibre.Miller.inMillerGlb_of_B
#print axioms TreeFibre.Miller.Controls.millerGlbTower_decided
#print axioms TreeFibre.Miller.Controls.levelPerm_insideGlb
#print axioms TreeFibre.Miller.Controls.levelPerm_committedGlb
#print axioms TreeFibre.Miller.Controls.levelPerm_stuckOld
#print axioms TreeFibre.Miller.Controls.levelPerm_principalGlb
#print axioms TreeFibre.Miller.Controls.pruneGlb_outside
#print axioms TreeFibre.Miller.Controls.pruneGlb_insideGlb
#print axioms TreeFibre.Miller.Controls.pruneGlb_stuck
#print axioms TreeFibre.Miller.Controls.pruneGlb_committed
#print axioms TreeFibre.Miller.Controls.pruneGlb_principal
#print axioms TreeFibre.Miller.Controls.perm_committedGlb
#print axioms TreeFibre.Miller.Controls.scope_refutedGlb
#print axioms TreeFibre.Miller.Controls.twice_unreadGlb
#print axioms TreeFibre.Miller.Controls.twice_postponedGlb

-- PatternInitiality / MillerRunInitial / MillerInitialControls: initial solutions, pruning in place included
#print axioms TreeFibre.Miller.pattern_injective
#print axioms TreeFibre.Miller.epi_of_patternCovered
#print axioms TreeFibre.Miller.initial_of_patternCovered
#print axioms TreeFibre.Miller.fixed_patternCovered
#print axioms TreeFibre.Miller.initial_of_patternTrimmed
#print axioms TreeFibre.Miller.MillerInv.pending
#print axioms TreeFibre.Miller.PatternCovered.transport
#print axioms TreeFibre.Miller.MillerInv.lowering
#print axioms TreeFibre.Miller.MillerInv.answerStep
#print axioms TreeFibre.Miller.PatternCovered.pruned
#print axioms TreeFibre.Miller.pruneStep_inv
#print axioms TreeFibre.Miller.glbSolveRound_inv
#print axioms TreeFibre.Miller.millerGlbRound_inv
#print axioms TreeFibre.Miller.drive_inv
#print axioms TreeFibre.Miller.millerGlb_solved_initial
#print axioms TreeFibre.Miller.millerGlb_initial
#print axioms TreeFibre.Miller.Controls.both_committedGlb
#print axioms TreeFibre.Miller.Controls.both_fixedSupport_fails
#print axioms TreeFibre.Miller.Controls.both_initialGlb
#print axioms TreeFibre.Miller.Controls.levelPerm_initialGlb
#print axioms TreeFibre.Miller.Controls.pruneGlb_initialGlb
#print axioms TreeFibre.Miller.Controls.perm_initialGlb

-- JoinContexts / JoinTyping: the join of typings
#print axioms TreeFibre.JoinOf.narrows_left
#print axioms TreeFibre.JoinOf.narrows_right
#print axioms TreeFibre.JoinOf.lookup
#print axioms TreeFibre.redTy_wide
#print axioms TreeFibre.typeEq_wide
#print axioms TreeFibre.belowWide_of_algorithmic
#print axioms TreeFibre.below_wide
#print axioms TreeFibre.isLub_join4
#print axioms TreeFibre.universe_of_tjoin
#print axioms TreeFibre.same_of_tjoin
#print axioms TreeFibre.rigidShape_not_universe
#print axioms TreeFibre.RigidShape.wide
#print axioms TreeFibre.check_of_synth
#print axioms TreeFibre.join_typing
#print axioms TreeFibre.typed_join

-- JoinForcing / JoinRule / JoinControls: the join widening, the rule, twisted domains
#print axioms TreeFibre.no_root_step
#print axioms TreeFibre.long_normal_at
#print axioms TreeFibre.JoinsK.universes
#print axioms TreeFibre.isType_join
#print axioms TreeFibre.long_type_join
#print axioms TreeFibre.typed_long_join
#print axioms TreeFibre.beta_open_below
#print axioms TreeFibre.eta_join_side
#print axioms TreeFibre.join_body
#print axioms TreeFibre.joinK_open
#print axioms TreeFibre.joinK_forced
#print axioms TreeFibre.joinK_head_solved
#print axioms TreeFibre.joinKUpdate
#print axioms TreeFibre.joinK_exact
#print axioms TreeFibre.isLub_left
#print axioms TreeFibre.isLub_right
#print axioms TreeFibre.Controls.twistJoins
#print axioms TreeFibre.Controls.twist_joined
#print axioms TreeFibre.Controls.twist_value
#print axioms TreeFibre.Controls.twist_exact
#print axioms TreeFibre.Controls.twist_principal
#print axioms TreeFibre.Controls.twist_outside_meet
#print axioms TreeFibre.Controls.redex_not_normal
#print axioms TreeFibre.Controls.joinX
#print axioms TreeFibre.Controls.join_needs_common_type
#print axioms TreeFibre.Controls.join_codomain_needed
#print axioms TreeFibre.joinK_factors

-- JoinSolver / JoinSolverControls: the join solver, decided
#print axioms TreeFibre.joinsOf_sound
#print axioms TreeFibre.joinsOf_total
#print axioms TreeFibre.joinSide_sound
#print axioms TreeFibre.joinSide_reread
#print axioms TreeFibre.joinSide_keep
#print axioms TreeFibre.join_viewK
#print axioms TreeFibre.joinRereadKUpdate
#print axioms TreeFibre.joinRereadK_exact
#print axioms TreeFibre.inJoinFragmentK_delete
#print axioms TreeFibre.inJoinFragmentK_join
#print axioms TreeFibre.joinRoundK_ne_refuted
#print axioms TreeFibre.joinRoundK_ne_stuck
#print axioms TreeFibre.joinRoundK_stable
#print axioms TreeFibre.joinFragmentK
#print axioms TreeFibre.joinK_decided
#print axioms TreeFibre.principal_of_inJoinFragmentK
#print axioms TreeFibre.Controls.towerJoin_sound
#print axioms TreeFibre.Controls.towerJoin_total
#print axioms TreeFibre.Controls.inJoinFragmentK_of_B
#print axioms TreeFibre.Controls.joinTower_principal
#print axioms TreeFibre.Controls.twist_insideJ
#print axioms TreeFibre.Controls.twist_committedJ
#print axioms TreeFibre.Controls.twist_principalJ
#print axioms TreeFibre.Controls.chain_insideJ
#print axioms TreeFibre.Controls.chain_not_meet_insideJ
#print axioms TreeFibre.Controls.chain_committedJ
#print axioms TreeFibre.Controls.chain_second_join_needed
#print axioms TreeFibre.Controls.chain_principalJ
#print axioms TreeFibre.Controls.cross_not_join_inside
#print axioms TreeFibre.Controls.cross_join_stuck

-- JoinRule (general) / JoinMeet / JoinMeetControls: the join with a meet
#print axioms TreeFibre.joinMKHom
#print axioms TreeFibre.joinMK_head_solved
#print axioms TreeFibre.joinMK_factors
#print axioms TreeFibre.joinMKUpdate
#print axioms TreeFibre.joinMK_exact
#print axioms TreeFibre.joinK_forces
#print axioms TreeFibre.join_body_meet
#print axioms TreeFibre.joinMeetK_open
#print axioms TreeFibre.joinMeetK_forces
#print axioms TreeFibre.joinMeetK_exact
#print axioms TreeFibre.joinMeetRereadK_exact
#print axioms TreeFibre.joins_of_below
#print axioms TreeFibre.crossesK_keep_all
#print axioms TreeFibre.joins_of_above
#print axioms TreeFibre.Controls.meetTwistCrosses
#print axioms TreeFibre.Controls.meetTwist_joined
#print axioms TreeFibre.Controls.meetTwist_value
#print axioms TreeFibre.Controls.meetTwist_exact
#print axioms TreeFibre.Controls.meetTwist_principal
#print axioms TreeFibre.Controls.meetTwist_not_meet_inside
#print axioms TreeFibre.Controls.meetTwist_not_join_inside
#print axioms TreeFibre.Controls.binMeet_comparable
#print axioms TreeFibre.Controls.binMeet_joinMeet_principal
#print axioms TreeFibre.Controls.cross_no_crossing

-- JoinMeetSolver / JoinMeetSolverControls: the join-meet solver, decided
#print axioms TreeFibre.CompatJ.symm
#print axioms TreeFibre.joinsOf_cons
#print axioms TreeFibre.crosses_of_crossOK
#print axioms TreeFibre.crossOK_join_above
#print axioms TreeFibre.crossOK_join_both_above
#print axioms TreeFibre.crossOK_join_below
#print axioms TreeFibre.compatJ_join
#print axioms TreeFibre.inJoinMeetFragmentK_delete
#print axioms TreeFibre.inJoinMeetFragmentK_swap
#print axioms TreeFibre.inJoinMeetFragmentK_step
#print axioms TreeFibre.joinK_forces_left
#print axioms TreeFibre.joinMeetRoundK_ne_refuted
#print axioms TreeFibre.joinMeetRoundK_ne_stuck
#print axioms TreeFibre.joinMeetRoundK_stable
#print axioms TreeFibre.joinMeetFragmentK
#print axioms TreeFibre.joinMeetK_decided
#print axioms TreeFibre.principal_of_inJoinMeetFragmentK
#print axioms TreeFibre.crossOK_of_le
#print axioms TreeFibre.crossOK_of_bounded
#print axioms TreeFibre.compatJ_of_compatK
#print axioms TreeFibre.inJoinMeetFragmentK_of_meet
#print axioms TreeFibre.Controls.towerJoin_bias
#print axioms TreeFibre.Controls.groupCompat_of_B
#print axioms TreeFibre.Controls.inJoinMeetFragmentK_of_B
#print axioms TreeFibre.Controls.joinMeetTower_principal
#print axioms TreeFibre.Controls.meetTwist_insideJM
#print axioms TreeFibre.Controls.meetTwist_committedJM
#print axioms TreeFibre.Controls.twist_insideJM
#print axioms TreeFibre.Controls.twist_committedJM
#print axioms TreeFibre.Controls.triple_inside
#print axioms TreeFibre.Controls.triple_committed
#print axioms TreeFibre.Controls.triple_second_needed
#print axioms TreeFibre.Controls.triple_principal
#print axioms TreeFibre.Controls.triple_not_meet_inside
#print axioms TreeFibre.Controls.triple_not_join_inside
#print axioms TreeFibre.Controls.binMeet_insideJM
#print axioms TreeFibre.Controls.binMeet_committedJM
#print axioms TreeFibre.Controls.cross_not_joinMeet_inside
#print axioms TreeFibre.Controls.cross_joinMeet_stuck

-- GlbJoin: the glb join, its joint widening and its exactness
#print axioms TreeFibre.CrossAt.symm
#print axioms TreeFibre.crossAt_same_all
#print axioms TreeFibre.crossAt_of_crossOK
#print axioms TreeFibre.WidensBoth.narrows_left
#print axioms TreeFibre.WidensBoth.narrows_right
#print axioms TreeFibre.WidensBoth.lookup
#print axioms TreeFibre.typed_widen_both
#print axioms TreeFibre.glb_join_body
#print axioms TreeFibre.glbJoinK_open
#print axioms TreeFibre.glbJoinK_forces
#print axioms TreeFibre.glbJoinK_exact
#print axioms TreeFibre.glbJoinRereadK_exact

-- GlbJoinSolver: the glb-join solver, decided
#print axioms TreeFibre.CrossCompat.symm
#print axioms TreeFibre.crossAt_join
#print axioms TreeFibre.crossAt_joined_left
#print axioms TreeFibre.crossCompat_of_compatJ
#print axioms TreeFibre.inGlbJoinFragmentK_delete
#print axioms TreeFibre.inGlbJoinFragmentK_step
#print axioms TreeFibre.glbJoinRoundK_ne_refuted
#print axioms TreeFibre.glbJoinRoundK_ne_stuck
#print axioms TreeFibre.glbJoinRoundK_stable
#print axioms TreeFibre.glbJoinFragmentK
#print axioms TreeFibre.glbJoinK_decided
#print axioms TreeFibre.principal_of_inGlbJoinFragmentK
#print axioms TreeFibre.inGlbJoinFragmentK_of_joinMeet

-- GlbJoinControls
#print axioms TreeFibre.Controls.groupCross_of_B
#print axioms TreeFibre.Controls.inGlbJoinFragmentK_of_B
#print axioms TreeFibre.Controls.glbJoinTower_decided
#print axioms TreeFibre.Controls.glbJoinTower_principal
#print axioms TreeFibre.Controls.twin_incomparable
#print axioms TreeFibre.Controls.twin_inside
#print axioms TreeFibre.Controls.twin_not_joinMeet_inside
#print axioms TreeFibre.Controls.twin_joinMeet_stuck
#print axioms TreeFibre.Controls.twin_committed
#print axioms TreeFibre.Controls.twin_suspended_before
#print axioms TreeFibre.Controls.twin_principal
#print axioms TreeFibre.Controls.spare_crossing_fails
#print axioms TreeFibre.Controls.spare_inside
#print axioms TreeFibre.Controls.spare_not_joinMeet_inside
#print axioms TreeFibre.Controls.spare_joinMeet_stuck
#print axioms TreeFibre.Controls.spare_committed
#print axioms TreeFibre.Controls.spare_principal
#print axioms TreeFibre.Controls.equiv_codomains
#print axioms TreeFibre.Controls.equiv_not_joinMeet_inside
#print axioms TreeFibre.Controls.equiv_inside
#print axioms TreeFibre.Controls.equiv_committed
#print axioms TreeFibre.Controls.equiv_joinMeet_committed
#print axioms TreeFibre.Controls.equiv_principal
#print axioms TreeFibre.Controls.twist_insideGJ
#print axioms TreeFibre.Controls.twist_committedGJ
#print axioms TreeFibre.Controls.meetTwist_insideGJ
#print axioms TreeFibre.Controls.meetTwist_committedGJ
#print axioms TreeFibre.Controls.triple_insideGJ
#print axioms TreeFibre.Controls.triple_committedGJ
#print axioms TreeFibre.Controls.binMeet_insideGJ
#print axioms TreeFibre.Controls.binMeet_committedGJ
#print axioms TreeFibre.Controls.level_insideGJ
#print axioms TreeFibre.Controls.level_committedGJ
#print axioms TreeFibre.Controls.cross_not_crossAt
#print axioms TreeFibre.Controls.cross_not_glbJoin_inside
#print axioms TreeFibre.Controls.cross_glbJoin_stuck

-- GlbJoinNecessity: the condition is needed, with incomparable codomains
#print axioms TreeFibre.Controls.ctr_usable_fails
#print axioms TreeFibre.Controls.ctr_two_answers
#print axioms TreeFibre.Controls.ctr_solvable
#print axioms TreeFibre.Controls.ctr_glb
#print axioms TreeFibre.Controls.ctr_no_principal
#print axioms TreeFibre.Controls.ctr_not_inside
#print axioms TreeFibre.Controls.ctr_stuck
#print axioms TreeFibre.Controls.crossAt_needed

-- CrossAtNecessary: the condition is necessary wherever it fails
#print axioms TreeFibre.no_common_answer_cross
#print axioms TreeFibre.factored_value
#print axioms TreeFibre.no_principal_of_right_apart
#print axioms TreeFibre.no_principal_of_left_apart
#print axioms TreeFibre.no_principal_of_not_crossAt
#print axioms TreeFibre.Controls.ctrIdentity_values
#print axioms TreeFibre.Controls.ctrConstant_values
#print axioms TreeFibre.Controls.ctr_no_principal_general
#print axioms TreeFibre.Controls.crossIdentity_right
#print axioms TreeFibre.Controls.crossConstant_right
#print axioms TreeFibre.Controls.cross_no_principal_general

-- GlbJoinInitial / GlbJoinInitialControls: initial solutions of join answers
#print axioms TreeFibre.mem_support_etaExp
#print axioms TreeFibre.wide_equal
#print axioms TreeFibre.epi_of_wideCovered
#print axioms TreeFibre.initial_of_wideCovered
#print axioms TreeFibre.fixed_wideCovered
#print axioms TreeFibre.initial_of_wideTrimmed
#print axioms TreeFibre.JoinInv.pending
#print axioms TreeFibre.JoinInv.delete
#print axioms TreeFibre.WideCovered.transport
#print axioms TreeFibre.WideCovered.joined
#print axioms TreeFibre.JoinInv.join
#print axioms TreeFibre.glbJoinRoundK_inv
#print axioms TreeFibre.drive_joinInv
#print axioms TreeFibre.glbJoin_solved_initial
#print axioms TreeFibre.glbJoin_initial
#print axioms TreeFibre.Controls.initial_of_commitGJ
#print axioms TreeFibre.Controls.glbJoinTower_initial
#print axioms TreeFibre.Controls.twin_initial
#print axioms TreeFibre.Controls.spare_initial
#print axioms TreeFibre.Controls.equiv_initial
#print axioms TreeFibre.Controls.triple_initialGJ
#print axioms TreeFibre.Controls.meetTwist_initialGJ
#print axioms TreeFibre.Controls.equivFamilies
#print axioms TreeFibre.Controls.equivGlb
#print axioms TreeFibre.Controls.equivTarget_lookup
#print axioms TreeFibre.Controls.equivMerge_answer
#print axioms TreeFibre.Controls.equivMerge_agrees
#print axioms TreeFibre.Controls.equivJoin_principal
#print axioms TreeFibre.Controls.equivJoin_not_initial
#print axioms TreeFibre.Controls.twinFamilies
#print axioms TreeFibre.Controls.twin_glb
#print axioms TreeFibre.Controls.twinGlb
#print axioms TreeFibre.Controls.twinJoins
#print axioms TreeFibre.Controls.twinCross
#print axioms TreeFibre.Controls.twinJoin_answer
#print axioms TreeFibre.Controls.twinJoin_principal

-- UnionSolver / UnionControls / SharedRankSolver: one solver for the decided fragments
#print axioms TreeFibre.crossCompat_of_glbCompat
#print axioms TreeFibre.inGlbJoinFragmentK_of_meetK
#print axioms TreeFibre.inGlbJoinFragmentK_of_glbGroups
#print axioms TreeFibre.unionRun_of_picked
#print axioms TreeFibre.unionRun_of_none
#print axioms TreeFibre.piece_decided
#print axioms TreeFibre.unionRun_decided
#print axioms TreeFibre.firstPiece_sound
#print axioms TreeFibre.firstPiece_complete
#print axioms TreeFibre.union_decided
#print axioms TreeFibre.Controls.towerClassify_sound
#print axioms TreeFibre.Controls.towerUnion_decided
#print axioms TreeFibre.Controls.levelPerm_piece
#print axioms TreeFibre.Controls.levelPerm_union
#print axioms TreeFibre.Controls.scope_piece
#print axioms TreeFibre.Controls.scope_union
#print axioms TreeFibre.Controls.decompose_piece
#print axioms TreeFibre.Controls.decompose_union
#print axioms TreeFibre.Controls.frThree_piece
#print axioms TreeFibre.Controls.frThree_union
#print axioms TreeFibre.Controls.frLevel_piece
#print axioms TreeFibre.Controls.frMisfit_union
#print axioms TreeFibre.Controls.twin_piece
#print axioms TreeFibre.Controls.twin_union
#print axioms TreeFibre.Controls.spare_piece
#print axioms TreeFibre.Controls.spare_union
#print axioms TreeFibre.Controls.ctr_piece
#print axioms TreeFibre.Controls.ctr_union
#print axioms TreeFibre.Controls.cross_piece
#print axioms TreeFibre.Controls.cross_union
#print axioms TreeFibre.Controls.twice_piece
#print axioms TreeFibre.Controls.over_piece
#print axioms TreeFibre.Controls.blend_solvable
#print axioms TreeFibre.Controls.blend_parts
#print axioms TreeFibre.Controls.blend_piece
#print axioms TreeFibre.Controls.blend_union
#print axioms TreeFibre.sharedRound_stable
#print axioms TreeFibre.sharedRound_ne_stuck
#print axioms TreeFibre.sharedFragment
#print axioms TreeFibre.shared_decided

-- CodomainForcing / CodomainRule / CodomainControls: unknowns at codomain positions
#print axioms TreeFibre.HoldsAt.of_holdsVar
#print axioms TreeFibre.normal_pi_domain
#print axioms TreeFibre.normal_pi_codomain
#print axioms TreeFibre.normal_of_rename
#print axioms TreeFibre.strengthen_normal
#print axioms TreeFibre.small_codomain
#print axioms TreeFibre.HoldsAt.small
#print axioms TreeFibre.arrowCod_of_arrow
#print axioms TreeFibre.PiCode.rename
#print axioms TreeFibre.PiCode.normal
#print axioms TreeFibre.holdsAt_of_support
#print axioms TreeFibre.subst_solveSub_absent
#print axioms TreeFibre.arrowCod_typed
#print axioms TreeFibre.codNarrowed_typed
#print axioms TreeFibre.codNarrowSolve_typed
#print axioms TreeFibre.cod_forced
#print axioms TreeFibre.cod_misfit_forced
#print axioms TreeFibre.codNarrowSolve_exact
#print axioms TreeFibre.Controls.U0_typed_below_U1
#print axioms TreeFibre.Controls.codSolvable
#print axioms TreeFibre.Controls.cod_exact
#print axioms TreeFibre.Controls.cod_principal
#print axioms TreeFibre.Controls.cod_outside
#print axioms TreeFibre.Controls.cod_piece
#print axioms TreeFibre.Controls.cod_union
#print axioms TreeFibre.Controls.cod_frGlb_stuck
#print axioms TreeFibre.arrowCod_of_B
#print axioms TreeFibre.arrowCodB_of_arrowCod
#print axioms TreeFibre.readFlexCod_complete
#print axioms TreeFibre.FlexCod.unique
#print axioms TreeFibre.arrowCod_subst_solve
#print axioms TreeFibre.codHeads_subst_solve
#print axioms TreeFibre.within_of_support
#print axioms TreeFibre.cod_occurs_refutes
#print axioms TreeFibre.arrowCod_misfit
#print axioms TreeFibre.cod_misfitHead_refutes
#print axioms TreeFibre.inFlexCod_delete
#print axioms TreeFibre.mem_codHeads_of_arrow
#print axioms TreeFibre.inFlexCod_of_flexRigidGlb
#print axioms TreeFibre.codNarrowed_lookup
#print axioms TreeFibre.codNarrowSolve_view
#print axioms TreeFibre.inFlexCod_narrowSolve
#print axioms TreeFibre.codSolvable_of_B
#print axioms TreeFibre.flexCodRound_ne_stuck
#print axioms TreeFibre.flexCodRound_stable
#print axioms TreeFibre.flexCodFragment
#print axioms TreeFibre.flexCod_decided
#print axioms TreeFibre.inFlexCod_of_B
#print axioms TreeFibre.Controls.flexCodTower_decided
#print axioms TreeFibre.Controls.cod_inside
#print axioms TreeFibre.Controls.cod_committed
#print axioms TreeFibre.Controls.over_insideCod
#print axioms TreeFibre.Controls.over_committedCod
#print axioms TreeFibre.Controls.occ_inside
#print axioms TreeFibre.Controls.occ_refuted
#print axioms TreeFibre.Controls.occ_unsolvable
#print axioms TreeFibre.Controls.mis_inside
#print axioms TreeFibre.Controls.mis_refuted
#print axioms TreeFibre.Controls.chainCod_inside
#print axioms TreeFibre.Controls.chainCod_committed
#print axioms TreeFibre.Controls.chainCod_suspended_before
#print axioms TreeFibre.Controls.frThree_insideCod
#print axioms TreeFibre.Controls.frThree_committedCod
#print axioms TreeFibre.Controls.over_union
#print axioms TreeFibre.Controls.dec_solvable
#print axioms TreeFibre.Controls.dec_piece
#print axioms TreeFibre.Controls.dec_union
#print axioms TreeFibre.Controls.dec_suspended_before
#print axioms TreeFibre.Controls.frLevel_arrows
#print axioms TreeFibre.Controls.dep_solvable
#print axioms TreeFibre.Controls.dep_piece
#print axioms TreeFibre.Controls.dep_union

-- CodomainDecompose / CodomainArrows / CodomainArrowsControls: arrow codes with codomains, decided
#print axioms TreeFibre.arrowCod_pi_parts
#print axioms TreeFibre.pi_cod_parts_typed
#print axioms TreeFibre.normal_weak_codomain
#print axioms TreeFibre.leftParts_typed
#print axioms TreeFibre.rightParts_typed
#print axioms TreeFibre.decomposeCod_exact
#print axioms TreeFibre.headPiCod_refutes
#print axioms TreeFibre.piHeadCod_refutes
#print axioms TreeFibre.rigidCodOf_head
#print axioms TreeFibre.rigidCodOf_pi
#print axioms TreeFibre.rigidCodOf_code
#print axioms TreeFibre.mem_support_pi_wk
#print axioms TreeFibre.support_subst_solve
#print axioms TreeFibre.mem_codHeads_pi
#print axioms TreeFibre.occursCod_cons
#print axioms TreeFibre.codRank_drop
#print axioms TreeFibre.codRank_swap
#print axioms TreeFibre.codRank_decompose
#print axioms TreeFibre.allArrowCod_of_B
#print axioms TreeFibre.allArrowCodB_of
#print axioms TreeFibre.occursCod_solved
#print axioms TreeFibre.codRank_solved
#print axioms TreeFibre.InArrowsCod.codes
#print axioms TreeFibre.inArrowsCod_drop
#print axioms TreeFibre.inArrowsCod_swap
#print axioms TreeFibre.inArrowsCod_of_arrows
#print axioms TreeFibre.inArrowsCod_of_flexCod
#print axioms TreeFibre.inArrowsCod_solved
#print axioms TreeFibre.inArrowsCod_decompose
#print axioms TreeFibre.readArrowCodEq_sound
#print axioms TreeFibre.readArrowCodEq_complete
#print axioms TreeFibre.solvableCod_in_fragment
#print axioms TreeFibre.flexStepCod_ne_stuck
#print axioms TreeFibre.flexStepCod_stable
#print axioms TreeFibre.swapRoundCod_ne_stuck
#print axioms TreeFibre.swapRoundCod_progress
#print axioms TreeFibre.rigidStepCod_ne_stuck
#print axioms TreeFibre.rigidStepCod_stable
#print axioms TreeFibre.stepArrowCod_ne_stuck
#print axioms TreeFibre.stepArrowCod_stable
#print axioms TreeFibre.arrowCodRound_ne_stuck
#print axioms TreeFibre.arrowCodRound_stable
#print axioms TreeFibre.arrowCodFragment
#print axioms TreeFibre.arrowsCod_decided
#print axioms TreeFibre.inArrowsCod_of_B
#print axioms TreeFibre.Controls.arrowCodTower_decided
#print axioms TreeFibre.Controls.dec_insideA
#print axioms TreeFibre.Controls.dec_committedA
#print axioms TreeFibre.Controls.dec_suspendedA
#print axioms TreeFibre.Controls.dec_principal
#print axioms TreeFibre.Controls.decomposeA_inside
#print axioms TreeFibre.Controls.decomposeA_committed
#print axioms TreeFibre.Controls.twiceA_inside
#print axioms TreeFibre.Controls.twiceA_committed
#print axioms TreeFibre.Controls.orientA_inside
#print axioms TreeFibre.Controls.orientA_committed
#print axioms TreeFibre.Controls.frLevelA_outside_first
#print axioms TreeFibre.Controls.frLevelA_inside
#print axioms TreeFibre.Controls.frLevelA_committed
#print axioms TreeFibre.Controls.frLevelA_principal
#print axioms TreeFibre.Controls.codA_inside
#print axioms TreeFibre.Controls.codA_committed
#print axioms TreeFibre.Controls.overA_inside
#print axioms TreeFibre.Controls.overA_committed
#print axioms TreeFibre.Controls.chainCodA_inside
#print axioms TreeFibre.Controls.chainCodA_committed
#print axioms TreeFibre.Controls.occA_refuted
#print axioms TreeFibre.Controls.misA_refuted
#print axioms TreeFibre.Controls.headClashA_refuted
#print axioms TreeFibre.Controls.piHeadA_refuted
#print axioms TreeFibre.Controls.codomainClashA_refuted
#print axioms TreeFibre.Controls.decClash_inside
#print axioms TreeFibre.Controls.decClash_refuted
#print axioms TreeFibre.Controls.decClash_unsolvable
#print axioms TreeFibre.Controls.dep_outsideA
#print axioms TreeFibre.Controls.dep_stuckA
#print axioms TreeFibre.Controls.blendArrow_insideA
#print axioms TreeFibre.Controls.blendArrow_committedA
#print axioms TreeFibre.Controls.dd_outsideA
#print axioms TreeFibre.Controls.dd_piece
#print axioms TreeFibre.Controls.dd_principal
#print axioms TreeFibre.Controls.dep_principal
#print axioms TreeFibre.Controls.blendArrow_union

-- The telescope: only the unknowns met and the declarations mentioning them
#print axioms TreeFibre.liftSub_agree
#print axioms TreeFibre.subst_congr_support
#print axioms TreeFibre.subst_solveSub_fresh
#print axioms TreeFibre.apart_of_universes
#print axioms TreeFibre.SidesApart.swap
#print axioms TreeFibre.sidesApart_of_B
#print axioms TreeFibre.sidesApartB_of
#print axioms TreeFibre.sidesApart_of_universes
#print axioms TreeFibre.atUniverses_of_B
#print axioms TreeFibre.atUniversesB_of
#print axioms TreeFibre.universe_of_atUniverses
#print axioms TreeFibre.codApart_of_sides
#print axioms TreeFibre.codNarrowed_atUniverse
#print axioms TreeFibre.atUniverses_solved
#print axioms TreeFibre.sidesApart_solved

-- CodomainInitial / CodomainInitialControls: initial solutions of answers with codomains
#print axioms TreeFibre.CodInv.pending
#print axioms TreeFibre.CodInv.delete
#print axioms TreeFibre.families_of_universes
#print axioms TreeFibre.codNarrowed_decl
#print axioms TreeFibre.families_codNarrowed
#print axioms TreeFibre.CodInv.narrowSolve
#print axioms TreeFibre.flexCodRound_inv
#print axioms TreeFibre.drive_codInv
#print axioms TreeFibre.flexCod_solved_initial
#print axioms TreeFibre.flexCod_initial
#print axioms TreeFibre.Controls.initial_of_commitCod
#print axioms TreeFibre.Controls.codA_initial
#print axioms TreeFibre.Controls.overA_initial
#print axioms TreeFibre.Controls.chainCodA_initial
#print axioms TreeFibre.Controls.codTarget_lookupX
#print axioms TreeFibre.Controls.codTarget_lookupY
#print axioms TreeFibre.Controls.codMerge_answer
#print axioms TreeFibre.Controls.codMerge_agrees
#print axioms TreeFibre.Controls.codAnswer_not_initial
#print axioms TreeFibre.CodInv.swap
#print axioms TreeFibre.CodInv.decompose
#print axioms TreeFibre.CodInv.narrowSolveCodes
#print axioms TreeFibre.flexStepCod_inv
#print axioms TreeFibre.rigidStepCod_inv
#print axioms TreeFibre.stepArrowCod_inv
#print axioms TreeFibre.arrowCodRound_inv
#print axioms TreeFibre.drive_codInvA
#print axioms TreeFibre.arrowsCod_solved_initial
#print axioms TreeFibre.arrowsCod_initial
#print axioms TreeFibre.Controls.initial_of_commitArrowCod
#print axioms TreeFibre.Controls.decA_initial
#print axioms TreeFibre.Controls.decomposeA_initial
#print axioms TreeFibre.Controls.frLevelA_initial
#print axioms TreeFibre.union_initial
#print axioms TreeFibre.Controls.towerUnion_initial
#print axioms TreeFibre.Controls.decUnion_initial
#print axioms TreeFibre.Controls.overSolvableCod
#print axioms TreeFibre.Controls.overCod_exact
#print axioms TreeFibre.Controls.overCod_principal
#print axioms TreeFibre.Controls.over_outside_flexRigidGlb
#print axioms TreeFibre.Controls.codOccurs_absent_fails
#print axioms TreeFibre.Controls.codMisfitHead_fails

-- CommonRank: one rank for the Miller rules and the rules of arrow codes
#print axioms TreeFibre.commonRank_drop
#print axioms TreeFibre.commonRank_of_millerRank
#print axioms TreeFibre.occ_perm
#print axioms TreeFibre.storeSize_perm
#print axioms TreeFibre.commonRank_perm
#print axioms TreeFibre.applyStore_length
#print axioms TreeFibre.equivalent_perm
#print axioms TreeFibre.Miller.rereadStore_length
#print axioms TreeFibre.Miller.stepLocals_commonRank
#print axioms TreeFibre.Miller.stepFlexLocal_commonRank
#print axioms TreeFibre.Miller.solveRound_commonRank
#print axioms TreeFibre.Miller.stepFlexFlex_commonRank
#print axioms TreeFibre.Miller.stepView_commonRank
#print axioms TreeFibre.Miller.glbSolveRound_commonRank
#print axioms TreeFibre.Miller.stepViewGlb_commonRank
#print axioms TreeFibre.Miller.millerGlbRound_commonRank
#print axioms TreeFibre.famArity_head
#print axioms TreeFibre.occursCod_iff
#print axioms TreeFibre.weight_eq_count
#print axioms TreeFibre.commonRank_eq_codRank
#print axioms TreeFibre.arrowCodRound_commonRank
#print axioms TreeFibre.retarget_progress
#print axioms TreeFibre.retarget_ne_stuck
#print axioms TreeFibre.transport_progress
#print axioms TreeFibre.transport_ne_stuck

-- MixedStores: Miller rounds keep equations between arrow codes, and mixed stores
#print axioms TreeFibre.Miller.not_mem_support_famCode
#print axioms TreeFibre.Miller.famCode_eq_head
#print axioms TreeFibre.Miller.reread_nil
#print axioms TreeFibre.Miller.sidesApart_of_families
#print axioms TreeFibre.Miller.inArrowsCod_iff
#print axioms TreeFibre.Miller.inArrowsCodB_of
#print axioms TreeFibre.Miller.arrowEq_lowered
#print axioms TreeFibre.Miller.rereadSide_code_universe
#print axioms TreeFibre.Miller.rereadEq_universe
#print axioms TreeFibre.Miller.arrowEq_reread
#print axioms TreeFibre.Miller.MixedStore.tail
#print axioms TreeFibre.Miller.MixedStore.perm
#print axioms TreeFibre.Miller.MixedStore.of_miller
#print axioms TreeFibre.Miller.MixedStore.of_arrows
#print axioms TreeFibre.Miller.mixed_lowered
#print axioms TreeFibre.Miller.mixed_value
#print axioms TreeFibre.Miller.mixed_prune
#print axioms TreeFibre.Miller.solveRound_mixed
#print axioms TreeFibre.Miller.stepFlexLocal_mixed
#print axioms TreeFibre.Miller.stepLocals_mixed
#print axioms TreeFibre.Miller.stepFlexFlex_mixed
#print axioms TreeFibre.Miller.stepView_mixed
#print axioms TreeFibre.Miller.glbSolveRound_mixed
#print axioms TreeFibre.Miller.stepViewGlb_mixed
#print axioms TreeFibre.Miller.millerGlbRound_mixed
#print axioms TreeFibre.Miller.millerGlbRound_ne_stuck_head

-- MixedSolver / MixedControls: one solver, one rank, mixed stores decided
#print axioms TreeFibre.millerFirst_perm
#print axioms TreeFibre.inMixed_of_miller
#print axioms TreeFibre.inMixed_of_arrows
#print axioms TreeFibre.inMixed_of_flexCod
#print axioms TreeFibre.inMixed_of_B
#print axioms TreeFibre.mixed_of_not_arrows
#print axioms TreeFibre.mixedRound_stable
#print axioms TreeFibre.mixedRound_ne_stuck
#print axioms TreeFibre.mixed_decided
#print axioms TreeFibre.mixed_principal_or_unsolvable
#print axioms TreeFibre.Controls.towerMixed_decided
#print axioms TreeFibre.Controls.blend_inMixed
#print axioms TreeFibre.Controls.blend_mixed_committed
#print axioms TreeFibre.Controls.blend_mixed_suspended_before
#print axioms TreeFibre.Controls.blendSwapped_committed
#print axioms TreeFibre.Controls.blendSwapped_arrows_suspended
#print axioms TreeFibre.Controls.shared_piece
#print axioms TreeFibre.Controls.shared_inMixed
#print axioms TreeFibre.Controls.shared_committed
#print axioms TreeFibre.Controls.shared_suspended_before
#print axioms TreeFibre.Controls.sharedSwapped_committed
#print axioms TreeFibre.Controls.shLeft_outside
#print axioms TreeFibre.Controls.shLeft_suspended
#print axioms TreeFibre.Controls.shLeft_solvable
#print axioms TreeFibre.Controls.dec_inMixed
#print axioms TreeFibre.Controls.dec_ranks
#print axioms TreeFibre.Controls.dec_round_ranks
#print axioms TreeFibre.Controls.dec_round_raises_millerRank
#print axioms TreeFibre.Controls.dec_round_lowers_commonRank
#print axioms TreeFibre.Controls.dec_mixed_committed
#print axioms TreeFibre.Controls.levelPerm_mixed_committed
#print axioms TreeFibre.Controls.scope_mixed_refuted
#print axioms TreeFibre.Controls.dep_outside_mixed
#print axioms TreeFibre.Controls.dep_mixed_suspended

-- CommonRankJoin / CommonRankGroups: the glb join, the flex–rigid rules and the glb groups lower the common rank
#print axioms TreeFibre.mem_support_etaExp_of
#print axioms TreeFibre.mem_support_etaExp_var
#print axioms TreeFibre.support_joinSide
#print axioms TreeFibre.occ_joinStore
#print axioms TreeFibre.weight_joinStore_lt
#print axioms TreeFibre.glbJoinRoundK_commonRank
#print axioms TreeFibre.flexCodRound_commonRank
#print axioms TreeFibre.support_contractSide
#print axioms TreeFibre.weight_contract_lt
#print axioms TreeFibre.weight_swap
#print axioms TreeFibre.weight_lowerHom
#print axioms TreeFibre.glbGroupRound_commonRank

-- OneSolver: one solver, one rank, every piece
#print axioms TreeFibre.millerFirstRound_stable
#print axioms TreeFibre.millerFirstRound_ne_stuck
#print axioms TreeFibre.oneRound_stable
#print axioms TreeFibre.oneRound_ne_stuck
#print axioms TreeFibre.one_decided
#print axioms TreeFibre.inOne_of_piece
#print axioms TreeFibre.inOne_of_mixed
#print axioms TreeFibre.one_decided_of_piece

-- ThroughLater / ThroughLaterControls: instantiated, reordered telescopes
#print axioms TreeFibre.Settles.principal_or_unsolvable
#print axioms TreeFibre.settles_later
#print axioms TreeFibre.later_target
#print axioms TreeFibre.Settles.equivalent
#print axioms TreeFibre.Settles.after
#print axioms TreeFibre.through_settles
#print axioms TreeFibre.arrows_settles
#print axioms TreeFibre.throughArrows_settles
#print axioms TreeFibre.throughArrows_principal_or_unsolvable
#print axioms TreeFibre.Controls.equivalent_of_codes
#print axioms TreeFibre.Controls.towerThrough_settles
#print axioms TreeFibre.Controls.ddStore0_inside
#print axioms TreeFibre.Controls.dd_equivalent
#print axioms TreeFibre.Controls.dd_through
#print axioms TreeFibre.Controls.dd_settles
#print axioms TreeFibre.Controls.dd_settled_principal
#print axioms TreeFibre.Controls.ddStore0_committed
#print axioms TreeFibre.Controls.dd_instantiated
#print axioms TreeFibre.Controls.re_outside
#print axioms TreeFibre.Controls.reStore0_inside
#print axioms TreeFibre.Controls.re_exchanged_equivalent
#print axioms TreeFibre.Controls.re_through
#print axioms TreeFibre.Controls.re_settles
#print axioms TreeFibre.Controls.re_solvable
#print axioms TreeFibre.Controls.re_principal

-- DependentCodomains / DependentCodomainsControls: solving a right side that fits, any shape
#print axioms TreeFibre.fitSolve_typed
#print axioms TreeFibre.fitSolve_exact
#print axioms TreeFibre.fitSolve_principal
#print axioms TreeFibre.Controls.dep_fit_principal
#print axioms TreeFibre.Controls.depY_outside
#print axioms TreeFibre.Controls.depY_piece
#print axioms TreeFibre.Controls.depY_fit_principal
#print axioms TreeFibre.Controls.depHigh_outside
#print axioms TreeFibre.Controls.depHigh_piece
#print axioms TreeFibre.Controls.depHigh_solvable
#print axioms TreeFibre.Controls.depHigh_settles
#print axioms TreeFibre.Controls.depHigh_principal
#print axioms TreeFibre.Controls.depOcc_refuted
#print axioms TreeFibre.Controls.depMis_refuted

-- DependentNarrowing: narrowing through a binder whose codomain uses its argument
#print axioms TreeFibre.holdsAtD_of_support
#print axioms TreeFibre.small_under
#print axioms TreeFibre.HoldsAtD.small
#print axioms TreeFibre.DepCode.piCode
#print axioms TreeFibre.DepCode.rename
#print axioms TreeFibre.depCode_of_arrowCod
#print axioms TreeFibre.depCode_typed
#print axioms TreeFibre.depNarrowed_narrows
#print axioms TreeFibre.depNarrowed_typed
#print axioms TreeFibre.depNarrowSolve_typed
#print axioms TreeFibre.dep_forced
#print axioms TreeFibre.dep_misfit_forced
#print axioms TreeFibre.depNarrowSolve_exact
#print axioms TreeFibre.depNarrowSolve_principal
#print axioms TreeFibre.within_of_support_pi
#print axioms TreeFibre.dep_occurs_refutes
#print axioms TreeFibre.piCode_misfit
#print axioms TreeFibre.dep_misfitHead_refutes
#print axioms TreeFibre.dep_settles

-- MixedJoin / MixedJoinControls / OneSolver: glb-join families mixed with arrow codes
#print axioms TreeFibre.arrowCod_subst_vars
#print axioms TreeFibre.codHeads_subst_vars
#print axioms TreeFibre.joinKSub_on_arrows
#print axioms TreeFibre.arrowEq_joinSide
#print axioms TreeFibre.arrows_of_flexK_nil
#print axioms TreeFibre.InGlbJoinFragmentK.sub
#print axioms TreeFibre.isFamEq_of_view
#print axioms TreeFibre.not_arrows_of_isFamEq
#print axioms TreeFibre.joinFirst_perm
#print axioms TreeFibre.joinFirst_parts
#print axioms TreeFibre.glbJoinRoundK_mixed
#print axioms TreeFibre.glbJoinRoundK_ne_stuck_head
#print axioms TreeFibre.mixedJoin_of_not_arrows
#print axioms TreeFibre.joinFirst_cons
#print axioms TreeFibre.mixedJoinRound_stable
#print axioms TreeFibre.mixedJoinRound_ne_stuck
#print axioms TreeFibre.mixedJoin_decided
#print axioms TreeFibre.joinFirstRound_stable
#print axioms TreeFibre.joinFirstRound_ne_stuck
#print axioms TreeFibre.inOne_of_mixedJoin
#print axioms TreeFibre.Controls.towerMixedJoin_decided
#print axioms TreeFibre.Controls.sj_piece
#print axioms TreeFibre.Controls.sj_mixed_suspended
#print axioms TreeFibre.Controls.sj_inMixedJoin
#print axioms TreeFibre.Controls.sj_committed
#print axioms TreeFibre.Controls.sj_suspended_before
#print axioms TreeFibre.Controls.sjSwapped_committed

-- MixedObstructionControls: Miller patterns with glb-join families
#print axioms TreeFibre.Controls.mj_readers
#print axioms TreeFibre.Controls.mjMiller_committed
#print axioms TreeFibre.Controls.mjJoin_committed
#print axioms TreeFibre.Controls.mj_solvable
#print axioms TreeFibre.Controls.mj_outside_mixed
#print axioms TreeFibre.Controls.mj_outside_mixedJoin
#print axioms TreeFibre.Controls.mj_mixed_suspended
#print axioms TreeFibre.Controls.mj_mixedJoin_suspended
#print axioms TreeFibre.Controls.mj_stuck_store
#print axioms TreeFibre.Controls.mj_stuck_redex
#print axioms TreeFibre.Controls.mj_stuck_join

-- ThroughRead / ThroughReadControls: the reader of later declarations
#print axioms TreeFibre.throughRead_sound
#print axioms TreeFibre.throughRead_settles
#print axioms TreeFibre.one_settles
#print axioms TreeFibre.throughOne_settles
#print axioms TreeFibre.Controls.towerOne_settles
#print axioms TreeFibre.Controls.towerRead_settles
#print axioms TreeFibre.Controls.dd_read
#print axioms TreeFibre.Controls.dd_read_zero
#print axioms TreeFibre.Controls.dd_read_settles
#print axioms TreeFibre.Controls.re_read
#print axioms TreeFibre.Controls.re_read_one
#print axioms TreeFibre.Controls.re_read_settles
#print axioms TreeFibre.Controls.met_unread
#print axioms TreeFibre.Controls.metFlex_unread
#print axioms TreeFibre.Controls.metArrow_read
#print axioms TreeFibre.Controls.met_solvable
#print axioms TreeFibre.Controls.metAnswer_solves
#print axioms TreeFibre.Controls.met_weight
#print axioms TreeFibre.Controls.met_after_weight

-- ThroughPhases / ThroughPhasesControls: deciding in phases
#print axioms TreeFibre.Decided.settles
#print axioms TreeFibre.phases_settles
#print axioms TreeFibre.Controls.principal_of_decided
#print axioms TreeFibre.Controls.met_phases
#print axioms TreeFibre.Controls.met_phases_one
#print axioms TreeFibre.Controls.met_settles
#print axioms TreeFibre.Controls.met_principal
#print axioms TreeFibre.Controls.met_second_phase
#print axioms TreeFibre.Controls.dd_phases
#print axioms TreeFibre.Controls.re_phases
#print axioms TreeFibre.Controls.metFlex_pieces
#print axioms TreeFibre.Controls.metFlex_inPlace
#print axioms TreeFibre.Controls.coop_alone
#print axioms TreeFibre.Controls.coop_phases
#print axioms TreeFibre.Controls.coop_phases_one
#print axioms TreeFibre.Controls.coop_principal
#print axioms TreeFibre.Controls.mj_inPlace
#print axioms TreeFibre.Controls.mj_principal

-- DependentDecide / DependentDecideControls: dependent codes decided as data
#print axioms TreeFibre.depBound_spec
#print axioms TreeFibre.depCode_of_B
#print axioms TreeFibre.depCodeB_of
#print axioms TreeFibre.depCodeB_iff
#print axioms TreeFibre.readFlexDep_complete
#print axioms TreeFibre.headsFit_of_B
#print axioms TreeFibre.misfitHead_spec
#print axioms TreeFibre.headsFitB_of_none
#print axioms TreeFibre.depDecide
#print axioms TreeFibre.depDecide_complete
#print axioms TreeFibre.Controls.dep_decided
#print axioms TreeFibre.Controls.depY_decided
#print axioms TreeFibre.Controls.depHigh_decided
#print axioms TreeFibre.Controls.depOcc_decided
#print axioms TreeFibre.Controls.depMis_decided
#print axioms TreeFibre.Controls.dh_without
#print axioms TreeFibre.Controls.dh_phases
#print axioms TreeFibre.Controls.dh_principal

-- MixedGroupsControls: a glb group with arrow codes
#print axioms TreeFibre.Controls.lg_inMixed
#print axioms TreeFibre.Controls.lg_committed
#print axioms TreeFibre.Controls.lg_principal
#print axioms TreeFibre.Controls.lg_groups_alone

-- RankRuns: runs with no budget of rounds
#print axioms TreeFibre.below_iff
#print axioms TreeFibre.driveWF
#print axioms TreeFibre.driveWF_eq
#print axioms TreeFibre.driveWF_done
#print axioms TreeFibre.driveWF_next
#print axioms TreeFibre.drive_eq_driveWF
#print axioms TreeFibre.driveWF_finished
#print axioms TreeFibre.driveWF_eventually
#print axioms TreeFibre.driveWF_decided_iff
#print axioms TreeFibre.roundsWF
#print axioms TreeFibre.roundsWF_done
#print axioms TreeFibre.roundsWF_next
#print axioms TreeFibre.drive_eq_driveWF_of_rounds
#print axioms TreeFibre.innerRun
#print axioms TreeFibre.outerRun
#print axioms TreeFibre.driveRank
#print axioms TreeFibre.runRank
#print axioms TreeFibre.innerRun_eq
#print axioms TreeFibre.outerRun_eq
#print axioms TreeFibre.driveRank_eq_driveWF
#print axioms TreeFibre.runRank_eq_runWF
#print axioms TreeFibre.runRank_finished
#print axioms TreeFibre.run_eq_runRank
#print axioms TreeFibre.runRank_eventually
#print axioms TreeFibre.runRank_decided_iff
#print axioms TreeFibre.runRank_refuted
#print axioms TreeFibre.runRank_solved_principal
#print axioms TreeFibre.fragment_decidedWF
#print axioms TreeFibre.fragment_decidedRank
#print axioms TreeFibre.one_decidedWF
#print axioms TreeFibre.one_decidedWF_iff
#print axioms TreeFibre.one_run_eq_runWF

-- InPlaceAudit: level variables are parameters; decisions with no budget of rounds
#print axioms TreeFibre.rules_valuation_free
#print axioms TreeFibre.roles_valuation_free
#print axioms TreeFibre.models_valuation_free
#print axioms TreeFibre.solvable_valuation_free
#print axioms TreeFibre.principal_valuation_free
#print axioms TreeFibre.initial_valuation_free
#print axioms TreeFibre.Decided.ofRank
#print axioms TreeFibre.finished_of_ofRun
#print axioms TreeFibre.Decided.ofRank_eq_ofRun
#print axioms TreeFibre.Decided.ofRank_isSome_iff

-- InPlaceAuditControls: the in-place solver with level variables, cumulativity and no budget
#print axioms TreeFibre.AuditControls.undecided_every_budget
#print axioms TreeFibre.AuditControls.principal_of_rankCommit
#print axioms TreeFibre.AuditControls.clash_levels_agree
#print axioms TreeFibre.AuditControls.clash_refuted
#print axioms TreeFibre.AuditControls.clash_unsolvable
#print axioms TreeFibre.AuditControls.clash_unsolvable_every_valuation
#print axioms TreeFibre.AuditControls.max_committed
#print axioms TreeFibre.AuditControls.cumul_committed
#print axioms TreeFibre.AuditControls.orient_committed
#print axioms TreeFibre.AuditControls.orient_principal
#print axioms TreeFibre.AuditControls.orient_step_stuck
#print axioms TreeFibre.AuditControls.misfit_inPlace_stuck
#print axioms TreeFibre.AuditControls.misfit_mixed_refuted
#print axioms TreeFibre.AuditControls.misfit_unsolvable
#print axioms TreeFibre.AuditControls.level_inPlace_stuck
#print axioms TreeFibre.AuditControls.level_mixed_committed
#print axioms TreeFibre.AuditControls.mj_rank_committed
#print axioms TreeFibre.AuditControls.mj_principal_every_valuation
#print axioms TreeFibre.AuditControls.cx_readers
#print axioms TreeFibre.AuditControls.cx_parts_decided
#print axioms TreeFibre.AuditControls.cx_solvable
#print axioms TreeFibre.AuditControls.cx_stuck_everywhere
#print axioms TreeFibre.AuditControls.cx_inPlace_undecided
#print axioms TreeFibre.AuditControls.met_rank_committed
#print axioms TreeFibre.AuditControls.dd_rank_committed
#print axioms TreeFibre.AuditControls.coop_phases_rank
#print axioms TreeFibre.AuditControls.coop_base_rank_alone
#print axioms TreeFibre.AuditControls.blend_budget_three
#print axioms TreeFibre.AuditControls.blend_rank_committed

-- WideMiller: wide sides, side-by-side re-reading, the direction by domain order
#print axioms TreeFibre.Miller.spineRen_substMorW
#print axioms TreeFibre.Miller.sideRen_typedW
#print axioms TreeFibre.Miller.flexBody_value_typedW
#print axioms TreeFibre.Miller.FlexDataW.ofExact
#print axioms TreeFibre.Miller.readFlexW
#print axioms TreeFibre.Miller.readWide
#print axioms TreeFibre.Miller.opensW
#print axioms TreeFibre.Miller.occurs_wide
#print axioms TreeFibre.Miller.rereadSideW_E
#print axioms TreeFibre.Miller.rereadEqW_E
#print axioms TreeFibre.Miller.rereadStoreW_models
#print axioms TreeFibre.Miller.occ_rereadW
#print axioms TreeFibre.Miller.weight_value_ltW
#print axioms TreeFibre.Miller.valueUpdateW
#print axioms TreeFibre.Miller.wideSolveRound
#print axioms TreeFibre.Miller.wideRound
#print axioms TreeFibre.Miller.wideSolver

-- WideMix: the join with the Miller sides re-read; one solver for the mix
#print axioms TreeFibre.Miller.opened_typedW
#print axioms TreeFibre.Miller.joinAnswer
#print axioms TreeFibre.Miller.joinMillerUpdate
#print axioms TreeFibre.Miller.joinMillerUpdate_remaining
#print axioms TreeFibre.Miller.rereadSideW_code
#print axioms TreeFibre.Miller.rereadEqW_codes
#print axioms TreeFibre.Miller.occ_joinMiller
#print axioms TreeFibre.Miller.weight_joinMiller_lt
#print axioms TreeFibre.Miller.joinMillerStep
#print axioms TreeFibre.Miller.mixWideRound0
#print axioms TreeFibre.Miller.mixWideRound
#print axioms TreeFibre.Miller.mixWideSolver

-- WideMixControls
#print axioms TreeFibre.WideControls.residual_readers
#print axioms TreeFibre.WideControls.residual_committed
#print axioms TreeFibre.WideControls.residual_principal
#print axioms TreeFibre.WideControls.residual_earlier_stuck
#print axioms TreeFibre.WideControls.cx_committed
#print axioms TreeFibre.WideControls.cx_principal
#print axioms TreeFibre.WideControls.mj_committed
#print axioms TreeFibre.WideControls.mj_principal_rank
#print axioms TreeFibre.WideControls.pieces_committed
#print axioms TreeFibre.WideControls.crossedWide_solvable
#print axioms TreeFibre.WideControls.crossedWide_stuck
#print axioms TreeFibre.WideControls.crossedWide_undecided

-- PermutedJoin: the glb join under a permutation
#print axioms TreeFibre.Miller.apps_congrW
#print axioms TreeFibre.Miller.typed_rename_of_substMor
#print axioms TreeFibre.Miller.beta_appsW
#print axioms TreeFibre.Miller.shift_substMor
#print axioms TreeFibre.Miller.reread_equalW
#print axioms TreeFibre.Miller.rereadSideP_E
#print axioms TreeFibre.Miller.rereadSideP_code
#print axioms TreeFibre.Miller.rereadEqP_E
#print axioms TreeFibre.Miller.rereadEqP_codes
#print axioms TreeFibre.Miller.rereadStoreP_models
#print axioms TreeFibre.Miller.occ_rereadP
#print axioms TreeFibre.Miller.pruned_all
#print axioms TreeFibre.Miller.weight_permute_le
#print axioms TreeFibre.Miller.permuteUpdate
#print axioms TreeFibre.Miller.permuteUpdate_remaining
#print axioms TreeFibre.Miller.permutedJoinStep
#print axioms TreeFibre.Miller.mixPermRound
#print axioms TreeFibre.Miller.mixPermSolver

-- PermutedJoinControls
#print axioms TreeFibre.PermutedControls.crossedWide_committed
#print axioms TreeFibre.PermutedControls.crossedWide_principal
#print axioms TreeFibre.PermutedControls.earlier_committed
#print axioms TreeFibre.PermutedControls.cross_stuck
#print axioms TreeFibre.PermutedControls.cross_no_commit

-- InPlaceAuditControls: the earlier uses with no budget
#print axioms TreeFibre.AuditControls.isSome_of_kind
#print axioms TreeFibre.AuditControls.mj_inPlace_agrees
#print axioms TreeFibre.AuditControls.metFlex_inPlace_agrees

-- PhasesInitial: initial solutions beyond telescopes of universe families
#print axioms TreeFibre.comp_epi
#print axioms TreeFibre.then_epi
#print axioms TreeFibre.epi_of_section
#print axioms TreeFibre.exchange_epi
#print axioms TreeFibre.exchange_twice_remaining
#print axioms TreeFibre.Decided.Epi
#print axioms TreeFibre.Decided.initial_of_epi
#print axioms TreeFibre.Decided.after_epi
#print axioms TreeFibre.Decided.equivalent_epi
#print axioms TreeFibre.decideNewest_epi
#print axioms TreeFibre.decideTwo_epi
#print axioms TreeFibre.phaseAt_epi
#print axioms TreeFibre.exchangeAt_epi
#print axioms TreeFibre.phases_epi
#print axioms TreeFibre.phases_initial
#print axioms TreeFibre.Decided.ofRankCover
#print axioms TreeFibre.ofRankCover_epi

-- PhasesInitialControls
#print axioms TreeFibre.InitialControls.coverBase_epi
#print axioms TreeFibre.InitialControls.initial_of_cover
#print axioms TreeFibre.InitialControls.re_base_alone
#print axioms TreeFibre.InitialControls.re_phases
#print axioms TreeFibre.InitialControls.re_initial
#print axioms TreeFibre.InitialControls.dd_phases
#print axioms TreeFibre.InitialControls.dd_initial
#print axioms TreeFibre.InitialControls.met_phases
#print axioms TreeFibre.InitialControls.met_initial
#print axioms TreeFibre.InitialControls.coop_not_covered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
