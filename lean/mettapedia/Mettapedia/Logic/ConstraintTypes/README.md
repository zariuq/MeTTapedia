# Predicate contracts, symbolic types and delayed membership

Import `Mettapedia.Logic.ConstraintTypes` for the generic foundation. The
maintained typing judgment is `DeclarationTyping.HasType`. Closed checking,
open-value compilation and the field-determined recognizer are proved against
that same judgment. They are algorithms and specializations of one theory.

## Values, proper types and declarations

Values are finite ranked trees. Proper types are finite terms over named types,
type constructors and scheme parameters. Named types and constructors may form
infinite universes; equality must be decidable for executable checking. Type
parameters and program variables are different sorts. Argument evaluation modes
are separate observations, rather than arbitrary instances of type parameters.

A constructor rule has a result type and optional field requirements. Choosing
it introduces fresh parameters, shared between that result and every required
field. Membership is an inductive derivation from those rules. Recursive rules
therefore describe recursive value languages without cyclic type terms.

A nominal declaration instead matches a whole value against a pattern. Patterns
may repeat variables. A matching fact establishes its declared whole-value type;
it establishes no constructor-field invariant. `ValuePatterns.matchValue_iff`
proves exact matching without modifying the queried value.

A fact can explicitly link a type parameter to a variable occurring in its value
pattern. `Fact.bindings` records these links with occurrence proofs; `readType`
decodes the matched value's type representation. These are separate variable
sorts connected by an explicit relation, rather than coincident variable names.
For example, a tag containing the representation of `Number` determines the
index of `Tagged Number`, while saying nothing about the tag's payload.
The decoder belongs to the representation and is not a reflective membership
oracle. Facts with no links retain their original independent scheme semantics.

A normalized call signature shares one type assignment between all proper input
and result positions. Multiple signatures form an existential disjunction. They
supply evidence for admitting a call, not additional executions of its body.
The admissible type algebra and primitive membership rules are explicit model
parameters. The generic theory does not require every semantic predicate to be
an admissible type instance or allow nominal facts to override a language's
protected primitive sorts.

## Explicit wildcards and proper type witnesses

`CheckingPatterns` distinguishes a checking expression from a proper type.
Its `any` node omits an explicitly written requirement; its `proper` node uses
the maintained declaration judgment and a proper type scheme. A parameter's
assignment still ranges over the proper type algebra. No wildcard node is added
to that algebra, even inside compound types. A genuine common nominal type may
still serve as a shared witness when the declaration interpretation admits it.

Positive checking operators decompose a subject into finite alternative sets of
child queries. Their arguments are sorted: a list-element predicate checks
values, whereas an exact tag index checks proper types. This supports nested
wildcards without assuming that every nominal type constructor is covariant.
`Coherent` states the compatibility certificate required before expanding an
existing proper constructor into such an operator. A whole-value nominal fact
alone cannot supply a structural field invariant. Wildcard weakening of an
operator is proved unconditionally; transferring that law to an existing proper
constructor requires its compatibility certificate.

`compile_correct` proves the pattern compiler exact relative to the certified
proper-membership compiler. It reuses scoped equations and the same unifier.
`weakening_preserves_witness` proves that replacing explicit requirements by
wildcards preserves each existing proper assignment. Substitution also remains
within proper types; it cannot turn a parameter into checking syntax.

For a structural list operator, `ListOf any` means a list whose individual
elements have no membership requirement. It does **not** mean
`exists T, ListOf T`: the latter retains one shared proper witness and can reject
a heterogeneous list. A wildcard index omits that index check, while an exact
index remains exact. `PatternControls` checks these distinctions using the
existing constructor and nominal declaration judgment, including nested lists,
shared parameters, exact tags and compound indices. A bad known Number-list head
is proved impossible under every tail completion. The open binding law is
extensional; it does not supply a new native incremental propagator.

`PatternContracts.frame_exact` extends staged boundaries to these checking
expressions. It keeps one assignment across an entire signature and filters
one body trace. An admitted unrestricted result preserves that complete trace,
including its values, effects and faults. Body equivalence is preserved. All
weakening laws hold for a fixed body, arity and prepared arguments, with input
evaluation modes unchanged. They do not justify replacing an evaluated input
by a held input or changing arity dispatch.

`RuntimeTyping.CheckingPolicy` specifies the proposed source convention:
literal input `Atom` holds; `_` and `%Undefined%` evaluate; all three omit a
requirement in explicit value-checking positions. Its proper-name vocabulary
excludes those reserved wildcard spellings. Type assignments use that proper
vocabulary, including recursively inside constructor applications. Results have
checks and no staging switch; an explicit template is computed by the body.
This source-policy specification does not modify an existing evaluator's
Atom-result quotation behavior or prove that behavior invalid. It introduces
no `Data` keyword, general subtyping lattice or implicit result evaluation.
`CheckingPolicy.checkedRuntime` connects this normalized declaration layer to
the source-atom call protocol: mode selection reads the inputs' explicit modes,
and its worker invokes the certified pattern boundary. The saturated-worker
theorem proves that connection; the existing direct/indirect/partial route
laws apply to this runtime instance. Source parsing, evaluator compilation and
native constraint propagation remain separate implementation obligations.

## Unshared parameters and the cost of checks

`UnsharedParameters` states when a check can be dropped. A parameter that is the
whole check of one input, and occurs in no other input or in the result,
constrains that value only to belong to some proper type. `waive_entry_iff` and
`waive_joint_iff` prove that replacing such a check by the wildcard changes no
admitted call and no allowed result, given that the value has a proper type.
`untyped_value_rejected` shows the hypothesis is needed. `matches_congr` is the
supporting law: a check depends on an assignment only through the parameters it
mentions. `allowed_map_iff` lifts a per-signature rewrite to overloaded
declarations. A shared parameter is unaffected; `shared_parameter_iff_common_type`
remains its meaning. Values are finite trees, so finiteness belongs to the
value domain; an implementation that admits cyclic terms is outside these laws.
`RuntimeTyping.CanonicalTypes` discharges the hypothesis for PeTTa: every
ground atom has a canonical type (a primitive or grounded type, `Symbol` or a
declared nominal type, or the structural tuple of its elements), so in any PeTTa
model containing these facts an unshared parameter imposes no check on a ground
argument (`waive_entry_iff_on_ground`, `waive_joint_iff_on_ground`).

`RuntimeTyping.UnclassifiedWitnesses` compares two witnesses for a symbol
without a proper declaration: one `UnclassifiedSymbol` for every such symbol
(`merged`), or a separate witness for a callable symbol, which `get-metatype`
reports as `Grounded` (`split`). Contracts read a value through the metatype
patterns, the primitive tests, host types and declared types; the concepts of
the resulting apartness (the distinction calculus's `Exclusion.IsConcept`) are
the classes no reading splits. The split witness of an undeclared symbol is
exactly the class of values no reading tells apart from it
(`split_extent_eq_conceptOf`) and fixes the metatype of its members
(`split_metatype_of_witness`). The merged witness is a concept but not the class
of any member, and no table from witnesses to metatypes exists for it
(`merged_extent_ne_conceptOf`, `merged_no_metatype_table`). Coverage and the
waiver hold under both policies; the split policy refuses exactly the merged
sharings between undeclared symbols of different metatypes (`share_split_iff`),
and its witness changes exactly when the metatype does (`split_witness_eq_iff`).

`CheckCost` counts element checks for a structural element-wise check.
Re-checking every known element after each arrival costs `n (n + 1) / 2` checks
for `n` arrivals (`revalidation_quadratic`). Checking each arrival once costs `n`
and gives the same verdict after every arrival (`incremental_exact`). A
recursive walk that checks its argument on every call also costs
`n (n + 1) / 2` (`walk_quadratic`). For a fixed predicate, passing the entry check
implies that every suffix passes (`entry_check_covers_suffixes`), so the inner
checks can be skipped. A check that reads state a body may edit is not a fixed
predicate. `CheckCostControls.matches_list_iff` proves that the structural list
operator is such an element-wise check, and two controls compare an unshared
parameter with its waived form on an accepted and a rejected call. These are
laws of the abstract checker and its cost measure, not measurements of an
implementation.

## The symbolic algorithm and its correctness

`SymbolicTypes` translates the existing `TypeExpr` representation losslessly to
the existing first-order term representation. It reuses the total, occurs-checked
Martelli–Montanari unifier in `Logic.LP.TotalUnification`; there is no second
unification algorithm. Soundness, completeness and principality transfer through
the representation isomorphism.

`ScopedConstraints` represents fresh parameters by disjoint sums. Its projection
theorem says exactly which assignments to public parameters an MGU describes
after private parameters are existentially hidden. A successful unifier has a
ground type instance when the proper type algebra has one inhabitant; this is
not a premise that some program value inhabits that type.

`ConstructorTyping.compile_correct` proves that finite rule alternatives compile
exactly to these scoped equations. `DeclarationTyping.check_iff` extends this to
constructor and nominal declarations. The result is a total executable checker
for finite values and finite declaration alternatives, even when a value such as
an empty list has infinitely many proper type instances. It does not enumerate
possible type assignments. Hidden existential field parameters are supported.

`ValuePatterns.specialize_iff` proves that reading linked pattern fields and
normalizing their equations gives exactly the original scheme's admissible
instances. It reuses the same principal unifier. Matching determines every
referenced field; irrelevant unmatched variables cannot influence the result.
`DeclarationTyping.Fact.prepare_iff` connects this specialization to the single
declaration judgment used by the closed checker.

`DeterminedMembership` specializes this algorithm when every field parameter
occurs in the rule's result. The result type then determines all field types.
The emitted grammar recognizes exactly the general judgment. Rules with hidden
field parameters retain the general solver. Its state space can be infinite:
field determination alone does not imply a regular language, finite tree
automaton, or linear runtime bound.

## Open values and one joint residual condition

`ResidualConstraints` adds predicate requests to scoped type equations. Requests
are data; their interpretation is supplied separately. Principal normalization
substitutes through every request and preserves all its possible type witnesses.
It neither forgets an undecided predicate nor asserts its satisfiability.

`OpenTyping.compile_correct` connects open-value compilation to the same
declaration judgment under every ground valuation. Known constructor structure
compiles immediately, unknown leaves retain membership requests, and nominal
facts retain whole-pattern requests. `compileOverloads_correct` retains one
shared witness per entire signature and all signature alternatives together.
A result can select an input-compatible witness that was not the first possible
input witness. An open variable is never a reason to commit to one overload.
Binding and request-transfer laws preserve this denotation under substitution
in a fixed declaration interpretation. `checkRequest_correct` verifies the executable
interpreter used when a request is ready.

Linked fields additionally retain index-read requests tied to the same scheme
parameters. `factRequests_correct` proves that these requests jointly enforce
the pattern and all of its value/type links. Substitution transfers them without
forgetting a future binding. The controls include different tags rejected under
a shared parameter and a wrong known index rejected for every completion of an
otherwise open payload.

The smaller `Formula` compiler in `OpenMembership` is a ground-type grammar
specialization with incremental simplification. It rejects a known bad head
while another argument or tail remains open. `OpenContract`'s supplied-instance
utility and `WitnessSolver`'s finite-observation algorithm have their own explicit
completeness premises; neither replaces the general symbolic solver.

A suspended check is internal state, not a new answer constructor. Collection
copies the residual graph reachable from the returned value and discards
disconnected components. `Constraints` specifies that operational boundary.
This is not a satisfiability decision: it can discard an unsatisfiable hidden
component that has not awakened. The exact extra condition for agreement with
logical existential projection is characterized by
`Semantics.discard_hidden_iff_fibres_inhabited`. Native copying must realize the
stated reachability rule; the model does not prescribe a scanner on collections.

## Calls, effects and edits

`CallTyping.frame_exact` proves the staged closed-value call checker against the
joint input/result relation. Input type equations and signatures form the frame;
no declaration world is stored there. Result membership is compiled in the
result context. Alternative signatures filter one body trace, preserving answer
order, effects and terminal faults after successful entry. Reordering or
repeating declarations does not change admission. An undeclared body is
unchanged by definition in the model.

The normalized mode policy holds an argument only when every applicable
signature literally requests the selected raw mode. Empty or mixed requests
evaluate once. A proper type parameter cannot become a raw-mode request during
unification. This is an explicit staging policy, separate from proper membership.
Other language-specific source modes need their corresponding observation and
elaboration rules; they are not inferred by this mathematical convention.

An entered check may retain its own chosen rules. Later membership requests are
interpreted when they run, and the interpreter can use the then-current
declarations. No snapshot of a complete type environment is required. Binding
and propagation theorems keep their stated unchanged-world hypotheses; they do
not license moving checks across arbitrary effects, faults or edits.

`Refresh.update_eq_fresh_compile` proves selective recompilation correct for a
compiler with a sound dependency specification. It is not a proof that a
particular emitter records every dependency. Guard erasure likewise requires an
established invariant of the actual trace (`Trace.AllAnswers`), not an annotation
alone. Runtime checking of existential call instances does not prove universal
parametricity, semantic correctness of function-valued arguments, or static
preservation for arbitrary bodies.

## Generic semantic results

`Semantics` develops predicate languages, commuting idempotent restrictions,
reindexing and existential image, their Galois connection, and exact conditions
for dropping hidden constraints. `Saturation` proves uniqueness of arbitrary
finite quiescent propagation runs under monotonicity and contraction; existence
requires the stated well-foundedness condition. Neither result silently assumes
pairwise commutation of individual propagators.

`RegularTree` proves ranked-tree recognition, product intersection and closed
exclusion certificates. `Saturation` identifies grammar inhabitation with the
least fixed point of its monotone production operator. A finite-state instance
is a regular tree grammar. Infinite-state grammars have no unrestricted
emptiness or inclusion decision procedure supplied here.

## Verification and implementation boundary

The focused target includes generic proofs, executable controls, the source-atom
call-protocol adapter and axiom audits:

```sh
lake build RuntimeTypingTheory
```

The basic recognizers and constraints use `Std`. The symbolic solver reuses the
existing verified LP unifier and its measure proofs. Predicate-order and
fixed-point results reuse mathlib. The PeTTa adapter imports the existing atom
carrier and models saturated direct, indirect and completed partial calls.
Historical static typing and determinism systems are outside this target.

Controls cover symbolic list instances, shared parameters, existential fields,
nonlinear nominal patterns, unsafe field inversion, delayed requests, effect
multiplicity, result-time membership, occurs checks and open-tail rejection.
Audits report kernel axiom dependencies rather than a readiness percentage.

These proofs do not verify a source declaration parser, the SWI translator,
native attributes or copying, concurrent clause-update implementation, general
arity dispatch, arbitrary refinement predicates, or a Prolog code emitter.
The proper type equations use a free constructor algebra, not semantic type
equivalence or equi-recursive types. Execution observations are finite traces,
not a complete divergence semantics. There is no theorem about SWI inference
counts. Model-level body identity must be realized and benchmarked in the
implementation before claiming zero overhead on untyped programs.

## Mathematical references

- Saraswat, Rinard and Panangaden, *Semantic foundations of concurrent constraint
  programming*, POPL 1991 ([author-hosted paper](https://people.csail.mit.edu/rinard/paper/popl91.pdf)):
  constraints as valuation sets, monotone information and quiescent processes.
- Mycroft and O'Keefe, *A polymorphic type system for Prolog*, 1984
  ([publisher record](https://doi.org/10.1016/0004-3702(84)90017-1)):
  polymorphic logic-program type schemes. The runtime policy here is independent
  of that paper's static checking discipline.

These references provide context. The proved constructions and their hypotheses
are identified above; their complete calculi have not been formalized here.
