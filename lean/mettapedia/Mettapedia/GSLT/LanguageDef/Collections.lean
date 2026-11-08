import Mettapedia.Algebra.Collections.Folds
import Mettapedia.Algebra.Collections.Sequences
import Mettapedia.Algebra.Collections.Rest
import Mettapedia.Algebra.Collections.Unification
import Mettapedia.Algebra.Collections.CanonicalForm
import Mettapedia.Algebra.Collections.SupportObservation
import Mettapedia.Algebra.Collections.Free
import Mettapedia.Algebra.Collections.SequencePatterns
import Mettapedia.Algebra.Collections.BoundedSequenceControls
import Mettapedia.Algebra.Collections.NamedBoundedSequence
import Mettapedia.Algebra.Collections.FlatBagBasisControls
import Mettapedia.Algebra.Collections.SyntacticUnification
import Mettapedia.Algebra.Collections.TermBagBasisControls
import Mettapedia.Logic.Unification.ListSpliceTerms
import Mettapedia.Logic.Unification.ListSpliceEncoding
import Mettapedia.Logic.Unification.ListPrefixMeeting
import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.GSLT.LanguageDef.Collections.CoreList
import Mettapedia.GSLT.LanguageDef.Collections.Layouts
import Mettapedia.GSLT.LanguageDef.Collections.NativeLayout
import Mettapedia.GSLT.LanguageDef.Collections.SkewLayoutControls
import Mettapedia.GSLT.LanguageDef.Collections.Spines
import Mettapedia.GSLT.LanguageDef.Collections.Evaluation
import Mettapedia.GSLT.LanguageDef.Collections.EvaluationControls
import Mettapedia.GSLT.LanguageDef.Collections.ListQueries
import Mettapedia.GSLT.LanguageDef.Collections.ElementPatterns
import Mettapedia.GSLT.LanguageDef.Collections.LinearPatterns
import Mettapedia.GSLT.LanguageDef.Collections.WirePrinting
import Mettapedia.GSLT.LanguageDef.Collections.FunctionalEvaluationControls
import Mettapedia.GSLT.LanguageDef.Collections.HECorrespondenceProbes
import Mettapedia.Algebra.Collections.ObservationalQuotient
import Mettapedia.Algebra.Collections.FoldRespect
import Mettapedia.GSLT.LanguageDef.Collections.Presentations
import Mettapedia.GSLT.LanguageDef.Collections.NodeFamilies
import Mettapedia.GSLT.LanguageDef.Collections.TypedCertificates
import Mettapedia.GSLT.LanguageDef.Collections.StructureByProof
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls
import Mettapedia.Languages.MeTTa.SpaceQueryPolicy
import Mettapedia.Languages.MeTTa.CollectionPatternQuery

/-!
# Collections: tuples, lists, bags and sets

The theory of finite collections used by LanguageDefs and by the MeTTa
dialects that realize them.

## The theories and their maps

* **Tuples** of arity `n` are the power `Fin n → α`, with the product's
  universal property (`Algebra.Collections.tupleMaps`). An expression of arity
  `n` is such a tuple; a head's signature fixes the arity
  (`Algebra.Collections.Sequences.Tuple.applied_iff`).
* **Lists** are the disjoint union of the tuple types
  (`Algebra.Collections.Sequences.Tuple.sigmaEquiv`) and the free monoid. Their
  inductive presentation by `nil` and `cons` is the LanguageDef core list,
  written `LNil` and `LCons` on the wire.
* **Bags** are the free commutative monoid (`Algebra.Collections.bagLift`) and
  **sets** the free join-semilattice with a least element
  (`Algebra.Collections.setLift`); both lifts are natural in the alphabet and
  in the target. The universal folds and their exact consumption conditions
  are there too (`Algebra.Collections.foldList_factors_bag_iff`,
  `Algebra.Collections.foldList_factors_set_iff`); `Algebra.Collections.Folds` derives a
  monoid from any fold that respects flattening.
* **The forgetful chain** tuple → list → bag → set forgets arity, then order,
  then multiplicity. Each step is the unique homomorphism keeping singletons
  and a reflection (`Algebra.Collections.existsUnique_factor_toBag`,
  `Algebra.Collections.existsUnique_factor_toSet`). Sorting is a section of
  `toBag` and of the composite to sets, with images the sorted and the
  strictly sorted lists, and never a homomorphic section
  (`Algebra.Collections.Controls.no_hom_section`).
* **Conversions** are named by the kind of their result: `list:from` (an
  expression's elements as a list), `tuple:from` (a list's elements as an
  expression), `bag:from` and `set:from` along the forgetful chain. They are
  homomorphisms and choose nothing. The way back from a bag or a set to a list
  is `list:sorted`, a section that depends on an order of the atoms.
* **Nested collections**, with kinds given by commutativity and idempotence,
  have canonical forms that decide equality at every depth
  (`Algebra.Collections.CanonicalForm.normalize_eq_iff`).

## Partial lists and their representations

* A list value is proper, open or improper: its abstraction is its explicit
  elements with a terminal (`Collections.Spines.abstractOf`,
  `Collections.Layouts.Terminal`). Binding an open rest appends
  (`Collections.Spines.abstractOf_bind_tail`). Terms are finite trees
  (`Collections.Spines.no_cyclic_list`).
* The flat representation with rests and the cons-cell representation present
  the same terms, with substitution commuting
  (`Logic.Unification.ListSplice.Encoding.encode_eq_iff`,
  `Logic.Unification.ListSplice.Encoding.encode_subst`).
* Physical layouts are specified through the abstraction, and every
  observation of the abstraction, including the polynomial fingerprint, agrees
  across layouts (`Collections.Layouts.Layout.agree`).
* CeTTa's layout, one flat array for a complete list and cells before an open
  or improper rest, is such a layout (`Collections.NativeLayout.native`), and
  decoding the roots it writes gives back its abstraction
  (`Collections.NativeLayout.readRoot_toRoot_reading`). A prepend into shared
  front slack realizes the layout's prepend and keeps every other holder's
  value (`Collections.NativeLayout.prepend_realizes`,
  `Collections.NativeLayout.prepend_keeps`).
* A persistent skew layout, small arrays, a skew-binary forest of full blocks
  and a bounded chain of deltas, is another (`Collections.SkewLayout.skew`);
  prepend and tail keep its shape invariants
  (`Collections.SkewLayout.valid_cons`, `Collections.SkewLayout.valid_tail`).
  Its cost model, kept apart from correctness and from measured running
  times, bounds a prepend by a constant and a lookup by a logarithm
  (`Collections.SkewLayout.consCost_le`, `Collections.SkewLayout.nthCost_le`),
  and repeated prepends onto a shared value by a linear total
  (`Collections.SkewLayout.sharedSkew_total`).
* Each dialect's manifestation of the core list (HE expressions, PeTTa cons
  cells, list values of extended PeTTa and Prime, the wire) satisfies one
  contract with that dialect's own operations
  (`Collections.CoreList.Contract`, `Collections.CoreList.Contract.agree`).

## Matching and unification

| Theory | Fragment | Type | Results |
|---|---|---|---|
| syntactic (tuples, cons view) | first-order terms, list values with rests | unitary, with occurs check | `Algebra.Collections.SyntacticUnification.unitary` |
| free monoid (sequence patterns) | matching against a list | finitary | `Algebra.Collections.SequencePatterns.matches_iff` |
| free monoid | unification, variables on both sides | infinitary | `Algebra.Collections.Unification.plotkin_infinitary` |
| free monoid | bounded images of active named variables | finite symbolic families, complete within the bound | `Algebra.Collections.Unification.NamedBoundedSequence.complete` |
| regular patterns over elements | membership | decided | `Collections.ElementPatterns.listMatch_iff` |
| bags (AC) | flat elements, two independent rests | finite complete irredundant families | `Algebra.Collections.FlatBagBasis.executable_irredundant` |
| bags (AC) | first-order element terms, two independent rests | finitary, not unitary; finite complete irredundant families | `Algebra.Collections.TermBagBasis.minimal_complete`, `Algebra.Collections.TermBagBasis.Controls.swap_not_unitary` |
| sets (ACI) | flat patterns, disjoint rests | finitary with disequalities | `Algebra.Collections.Unification.flat_set_unify_iff` |
| sets (ACI) | rests not required disjoint | rests not determined: `2 ^ k` | `Algebra.Collections.Rest.card_setRests` |

The bounded solver collects its actual input names and constants. It does not
require a finite ambient alphabet. Residual parameters can represent infinitely
many concrete answers, and their expansion can exceed the original bound, so
bounded concrete readout retains its length check. The reference enumeration
does not claim a minimal family or efficient runtime search.

Flat-bag candidate element equations are solved jointly by the existing total
unifier. A proved finite-context factorization checker drives stable pruning;
arbitrary-variable finite-basis existence is separately classical. The basis
preserves solutions, not raw occurrence-derivation multiplicity or identical
representative order under input permutations. Aliased rests and nested AC
terms are not silently admitted as independent flat rests.

Bags of first-order terms have one family per consistent partial matching:
the occurs-checked total unifier of the matched pairs, with each rest the
other side's unmatched elements plus one common bag
(`Algebra.Collections.TermBagUnifiers.realizes_iff`). A finite-context checker
decides generality by clipping witnesses to subterms
(`Algebra.Collections.TermBagSubsumption.check_iff`), and the pruned basis is
sound, complete and irredundant; sides without a rest are its instances with
an empty rest (`Algebra.Collections.TermBagBasis.closed_solves_iff`), and a rest
shared by both sides cancels
(`Algebra.Collections.TermBagBasis.shared_rest_solves_iff`). The flat
development is the function-free instance: the flat families and the flat
basis are the decoded term families and term basis, in the same order
(`Algebra.Collections.TermBagFunctionFree.flat_basis_eq`). Bags below the root
of an element are not free syntax
(`Algebra.Collections.TermBagBasis.Controls.inner_bag_is_not_free_syntax`) and
are not covered.

For tuples and list spines, unitarity means zero solutions on failure and one
most-general class on success. It does not mean a single raw substitution.

For linear sequence patterns, regex acceptance is equivalent to the existing
matcher returning a capture (`Collections.LinearPatterns.listMatch_iff_matchFrom_ne_nil`).
This holds even for an empty alphabet. Total-assignment readout has its separate
inhabitance condition; repeated variables can make erasure admit spurious words.

The actual wire encoder and renderer obey the ordered `LCons`/`LNil` printing
laws in `Collections.WirePrinting`. Symbols are rendered verbatim, so these
laws do not assert unrestricted text injectivity or a parser round trip.

## Structure found by proof

* **Observational quotients**: storing representatives of an equivalence is
  sound in every context exactly when the equivalence is contained in
  contextual equivalence over bags of answers
  (`Algebra.Collections.ObservationalQuotient.Machine.store_sound_iff`).
* **Folds that respect bags or sets**: a right fold factors through the bag of
  its elements exactly when its step is left-commutative, and through the set
  exactly when the step is also left-idempotent
  (`Algebra.Collections.FoldRespect.foldr_factors_bag_iff`,
  `Algebra.Collections.FoldRespect.foldr_factors_set_iff`).
* **Cell families**: every term is uniquely a maximal chain of cells of a
  constructor family followed by a term that is not a cell
  (`Collections.Presentations.Family.equivCanonical`).
* **Node families**: every term is uniquely a tree of cells over the terms that
  are not cells (`Collections.NodeFamilies.Nodes.equivTree`).
* **Typed certificates**: checking with recorded judgments gives the full
  judgment, and a loop checking each new argument costs a linear total instead
  of a quadratic one (`Collections.TypedCertificates.Judgment.check_eq`,
  `Collections.TypedCertificates.incremental_total`).
* **Recognized recursions**: a recognized structural recursion answers on a
  spine as on its end, mapped by the fold of the cells, open and improper ends
  included (`Collections.StructureByProof.Recognized.answers_spine`); no rule
  that sees only constructors and operations decides when a quotient is sound
  (`Collections.StructureByProof.no_shape_only_admission`).

## Typed calls

PeTTa's `get-type` is a relation with multiplicity, and a typed call continues
once for every answer that meets its formal
(`Collections.TypedCalls.guard`). Under functional declarations every guard
succeeds at most once, and exactly once at a type variable nothing else names
(`Collections.TypedCalls.card_guard_fresh`). A constructor application typed at
a closed named type inverts through one-way matching of the declared result
(`Collections.TypedCalls.ctor_inversion`), its fields build it back
(`Collections.TypedCalls.ctor_construction`), and at a metatype name the guard
is not the relation (`Collections.TypedCalls.Controls.metatype_guard_without_relation`).
A trusted version, whose calls to itself skip the protocol, has the protocol's
answers at every fuel for every relation the analysis accepts
(`Collections.TypedCalls.accepted_version_eq_protocol`). Alpha-equivalent
declaration rows are one row in every observation
(`Collections.TypedCalls.idemAlpha_addRow`, `Collections.TypedCalls.typedCall_repeat`),
and the inline protocol of a declared builtin is the row's protocol on values
and variables (`Collections.TypedCalls.inline_eq_protocol`). With shared type
variables a call's store is a common instance of them
(`Collections.TypedCalls.chainCall_shared`); a call through a variable runs
natively for every callee without an `Atom` parameter
(`Collections.TypedCalls.nativeRoute_eq_hostRoute`); and a fold certified by a
recorded judgment answers as the recognized recursion and costs less than the
untyped fold (`Collections.TypedCalls.TypedFolds.certified_list_answers`,
`Collections.TypedCalls.TypedFolds.certifiedPass_lt_untypedPass`).

## Evaluation

List literals, data parameters, stored atoms and elements chosen by
`superpose` are data; templates run once their pattern has matched; the
dialects differ by their binding rule and their result rule
(`Collections.Evaluation`, with the probe controls in
`Collections.EvaluationControls`). Matching a pattern against every element of
a list is a query of the list as a small space, a function of its bag up to
the order of the answers (`Collections.ListQueries.toBag_matchAll`,
`Collections.ListQueries.toFinsupp_matchAll`).

`Collections.FunctionalEvaluation.eval_unique` derives uniqueness of successful
values from independent native/rule functionality, disjoint dispatch and
syntax-closure conditions. Its hereditary fragment includes calls, constructors,
lists, quotation, pattern lets, unification and map, but excludes `superpose`
and stored `match`. Actual unifier-image closure follows from its global MGU
property via `Logic.LP.UnificationRestriction.unifyTotal_respects`.
The original probe program satisfies this profile for every declared dialect;
all five probe rows have exact-result laws. This is neither a termination law
nor an adequacy theorem for a native interpreter.

HE's result rule is compared with HE's executable interpreter on the call
fragment (`Collections.HECorrespondence`). Evaluating a call's result again
means evaluating its raw result once more at the declared type, native outputs
included; a counterexample separates that from evaluating it twice, and the
model's rule was repaired to it (`Collections.HECorrespondence.Counterexample.model_w`,
`Collections.HECorrespondence.Counterexample.twice_w`). HE's interpreter gives
the counterexample's answer and the HE column of the probe table at every
budget from a stated least one, with the budget a variable of the proof
(`Collections.HECorrespondence.Interpreter.he_w`,
`Collections.HECorrespondence.Interpreter.he_probe_table`).
-/
