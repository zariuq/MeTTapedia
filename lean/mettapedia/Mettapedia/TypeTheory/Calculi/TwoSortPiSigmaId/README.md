# Two-sort dependent calculus with products, sums, and identity formation

`TwoSortPiSigmaId` names a concrete mathematical calculus extracted from the
historical MeTTa-Pure experiment. It is neither MeTTa Zero nor a selected
Prime kernel. The syntax is intrinsically **scoped**, not intrinsically
typed: typing is a separate judgment.

## Exact calculus

`Syntax.lean` defines scoped terms with a distinguished ground type
`u0`, an untyped formation marker `u1`, dependent products and sums,
identity formation and reflexivity, lambda/application and pair/projections.
The syntax also admits declaration constants.

The fixed head axiom is `u0 : u1`. Product and sum formation use the
marker at domain, codomain and result. There is no cumulative universe
hierarchy, quantification over a universe of types, or identity eliminator.
The three root reductions are function beta and the two pair projections.
Declaration-aware reduction is a separate relation in
`DeclarationSemantics.lean`.

## Distinct judgments

`Permissive.Typing.HasType` is the older permissive relation. It omits formation
premises at several introductions and at conversion. It must not be used
as evidence for the regularity of a new candidate.

`Regular.RegularHasType` is a separate presupposition-closed
relation restricted to declaration-free syntax. `RegularJudgment` also
requires `RegularCtx`: a typing derivation over an arbitrary raw context
is not the complete admissibility contract.

The difference is proved, not merely documented:
`regular_strictly_below_raw` separates the judgments. The old relation
accepts an identity lambda over the untyped marker; the regular relation
rejects it. The staged presentation's old embedding follows the permissive
relation, and `RegularTwoSortImage.nativeRegularExactness_false` proves it
does not automatically implement the regular one.

## Reusable results and boundaries

`Regular/Structural.lean` proves substitution and type presupposition directly
for the regular judgment. `Regular/SubjectReduction.lean`,
`Regular/Fundamental.lean`, and `Regular/Normalization.lean` establish preservation
and executable normalization on the regular fragment.
`Regular/BidirectionalCompleteness.lean` states the precise public checking
contract; it is not an unqualified inference algorithm for every raw term.

`Regular/SyntacticCwf.lean` packages formed contexts and the actual substitutions
with raw syntax equality. The represented-family modules instantiate
generic CwF/Yoneda results at that concrete calculus. Conversion remains
separate: these are not a conversion quotient, initiality, a universe
hierarchy, or a proof of CeTTa implementation refinement.

The declaration modules and Bool/Nat/Unit examples use separate
declaration-aware judgments. Their existence does not extend the
declaration-free normalization theorem.

## Dependency boundary

`Regular/Typing.lean` owns the regular rules, context formation and
declaration-free conversion. The normalization, checking and syntactic-CwF
import closures are independent of MeTTa encodings. MeTTa Pattern quotation,
presentation comparisons and runtime services live downstream in
`Languages/MeTTa/Experimental/TwoSortPiSigmaId`.

The generic CwF/Yoneda constructions live in `TypeTheory` and do not depend
on this calculus. Their application here tests them at a concrete instance;
it does not make either typing relation the Prime specification.

`Logic/Relation/Normalization.lean` owns the syntax-independent normalization
algorithm, normal-form uniqueness and strategy-independence laws. The regular
calculus supplies its certified step selector and proved accessibility;
the intrinsic simply typed fragment uses the same algorithm. The generic
module imports only Mathlib. Its independent controls compare different
numeric strategies and reject uniqueness without confluence and termination
in the presence of a self-loop.

Run `python3 scripts/check_two_sort_boundaries.py` from the Lean project root
to check this dependency direction, unique typing authorities and retired
module references. The historical paper is `papers/PureMeTTa.tex` at repository
root; its title and statements describe this bounded experiment.
