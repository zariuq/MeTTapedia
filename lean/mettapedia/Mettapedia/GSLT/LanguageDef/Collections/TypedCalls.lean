import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeRelation
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Constructors
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TrustedVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ChainPrograms
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.DeclaredBuiltins
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Polymorphic
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CalleeDemand
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeCompletion
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEReturns
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFolds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SharedAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDispatchDeopt
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ClosedSortEvidence
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RecognizedFolds
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StaticEvidence
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampKeys
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEErrorProtocol
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HETypedRuleControls
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSets
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ExactStaticTypes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypingTransfer
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PolymorphicAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenFormals
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.OpenRangeInstances
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.InferredTypeSetsScope
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ImpliedMeets
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.LetScopes
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ValueRows
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.CertifiedSpines
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.StampStoreInvariant
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.KnownArgumentClasses
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedFoldBound
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TwoWayTypedVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PrivateSpaceVersions
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ConstantInstances
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SealedSorts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SealedJudgments

/-!
# Typed calls

A declaration is information for a fast path, never a reason to decline it:
a check the dialect requires travels inside the fast path with its exact
failure behaviour, and every answer bag, multiplicity included, stays the
protocol's.

* `TypeRelation`: PeTTa's `get-type` as a compositional judgment with
  multiplicity, over finite terms; the guard `get-type *-> true ;
  get-metatype`; under functional declarations at most one answer at every
  request and exactly one at a fresh type variable; the rows of a symbol as a
  bag; alpha-equivalent rows as one row (`idemAlpha_addRow`).
* `Constructors`: the constructor class the analysis inverts; the count of a
  constructor application at a closed named type; inversion through one-way
  matching of the result, construction, and tuple-type exclusion; the guard
  at a metatype name is not the relation.
* `Protocol`: the typed call, row by row, with demand, shared type variables
  and result guards; closed rows factor into counts; alpha-equivalent rows are
  one alternative and distinct rows add; HE's errors where PeTTa answers
  nothing.
* `TrustedVersions`: entry facts at metatype names are guard facts and
  elsewhere relation facts; the version theorem, the analysis of patterns,
  constructions, calls to itself and results, and its soundness: an accepted
  relation's version has the protocol's answers at every fuel.
* `ChainPrograms`: a program of several heads, its right-hand sides read as
  outcomes, values or calls in tail positions; the analysis gives the machine's
  chain hypotheses for every program it accepts, so the machine runs it as its
  protocol does.
* `DeclaredBuiltins`: for values and variables the guard at a value class is a
  class test, whatever the declarations, and the inline protocol is the row's
  protocol; symbols and expressions take the full guard.
* `Polymorphic`: a formal with private type variables is guarded without the
  store, once exactly when the value is typed at some instance; inversion and
  construction at instances; rows with private parameters factor and their
  versions are their protocols; with shared variables a store is a common
  instance, and an answer counts once exactly when one instance types every
  argument and the answer.
* `CalleeDemand`: a call through a variable delivers by its callee's demand;
  the native route is the host route for every callee without an `Atom`
  parameter; deciding per call observes the host route and costs no more than
  the program-wide rule, through `Machines.AdmissionRewriting.LocalDeclines`.
* `RangeCompletion`: in HE's interpreter, a typed head with a range other than
  `Atom` answers as the untyped head through a range check of the value, and
  the range check of a value is a class test with HE's `BadType` error.
* `HEReturns`: in HE's interpreter, a typed head evaluates its results once at
  its range and an untyped head at the expected type, so a value is cast at the
  range of the innermost typed head that returns it; a value signature's typed
  call is its class tests and its results at the range; a parameter range and
  `if` bind their range variable once; the static reading of where a call's
  answers are cast agrees with the interpreter.
* `TypedFolds`: on terms judged `(List Number)` or `Nat`, a recognized fold's
  answers are its base answers folded over integers or a count, and in the
  cost model of a pass the certified fold is cheaper than the untyped one.
* `SharedAdmission`: carrier-parametric boundaries and exact ordered/bag
  instances, checked regional call chains, alpha-invariance, ordered stamp
  inference, two-way uninterpreted binding, and open-range transport laws.
  Its module map states the current native/source correspondence boundaries.
* `HEDispatchDeopt`: a typed HE call factors into applicability on the
  argument expressions, argument evaluation, and delivery of the call with
  evaluated arguments at its range; a prepared delivery that falls back to the
  canonical one at that step is exact; the call node's selection streams
  successes and holds errors to the batch's close; the expected type matters
  only through applicability.
* `ClosedSortEvidence`: a certificate at a closed sort, read through its
  inversion, discharges the guards of a structural recursion exactly when
  each counts one, makes equation search keyed and exhaustive, and turns a
  typed fold over a certified list into the native fold of its elements.
* `RecognizedFolds`: a head whose two equations fold a free constructor with
  `+` or `*` is answered by one walk of its argument's spine; the walk's exact
  right fold declines exactly where a right partial value leaves the machine
  integers, a forward sum with the bound is that fold, and the machine's route
  has the equations' answers on every argument; a typed head keeps them when
  its formal inverts through the cells.
* `StaticEvidence`: PeTTa's identical check of the same value, or of a value
  whose range a callee's version proves, is discharged exactly; on HE's
  typings, field inversion through one closed arrow, checked builds typable
  (and exactly typed) at their range, and a value statically at a closed
  parameter continuing its check; a parameter declared `%Undefined%` gives its
  field no static type, and `%Undefined%` inside a parameter is no wildcard.
* `StampKeys`: a transition table keyed by adequate child keys answers as
  inference in any order of recording; keying a literal child by its grounded
  kind is not adequate where the native-handle classification reads a string
  kind, and the corrected key is adequate for every other head.
* `HEErrorProtocol`: an error answer of `let`'s value or of `switch`'s key is
  the call's answer, with nothing bound; an expression key's answers are the
  streaming selection of its interpretation; `Empty` is neutral in the cast
  walker's join.
* `HETypedRuleControls`: HE's interpreter and typing rule against these rules:
  an undeclared head's application passes every argument check, a typed fold
  without inversion answers an error where the walk answers a value, a field
  declared `%Undefined%` fails the check a static type would skip, and a
  constructor value is answered as itself typed or untyped.
* `InferredTypeSets`: typing sets of an HE program's untyped heads, members read
  as lower bounds; on HE's semantics every value reaching a node is covered by its
  set under a fixpoint, and the run that skips the discharged builds, arguments
  and returns reaches exactly HE's values; a field the range does not fix, a
  failing combination of lower bounds read as no value, a head named as a value
  with its call sites' parameters, and `%Undefined%` inside an argument's typing
  are the controls.
* `ExactStaticTypes`: exact typings (literals, classes, checked builds over exact
  children) are the ones a run may record, and `get-type` then answers them alone;
  a lower bound is not one (`(Pair Nil Nil)` under `(List Number)` formals).
* `TypingTransfer`: a copy's typings are its source's, a copy walk recording the
  source's validated typings keeps the address store sound, and the run's
  recorded answer typing is HE's while its arena's epoch holds.
* `PolymorphicAdmission`: a PeTTa head entered at its version's instance and at
  private formals typed once at some instance is its signature's protocol on
  every argument; for a head mixing instance and private formals, equations the
  analysis accepts at the formals as the version reads them give that.
* `OpenFormals`: a typed fold at a formal with type variables whose constructor's
  recursive field is the formal at every instance (what CeTTa's unifier check
  gives) passes every check of its calls to itself, in HE at the outer call's
  instance and in PeTTa's protocol at the private formal, where it has the
  machine's answers; an argument at such a formal whose every typing-set member
  allows an instance of it passes HE's check.
* `OpenRangeInstances`: an open range is shown at every instance by arguments at
  the range's own formal, symbols declared at it and `if`s of those, so skipping
  its instance there changes no answer; a tail call shows it only through the
  meet with the instance, and skipping the instance there changes HE's error
  into the callee's value.
* `InferredTypeSetsScope`: a literal whose type names `%Undefined%` below its top
  is unknown, which covers it and only widens; without dynamic calls the heads a
  program names as values do not matter, so no escape condition is needed.
* `ImpliedMeets`: a head's own tail call whose argument at each formal the range
  reads is the parameter there or a checked build over it at a field declared at
  the constructor's range owes exactly its own instances, so every meet along such
  a run succeeds and skipping the instance changes no answer; a field of the
  matched parameter keeps its caller's instances but never takes part in a run
  that returns a value; a run of fields only owes the first activation's
  instances; skipping is exact for heads whose implied steps are all builds or all
  fields; an expression's own type row binds HE's instance first.
* `LetScopes`: the machine's scoped binders answer as HE's persistent bindings on
  every body whose ended scopes retire their variables, a later binder of a
  retired variable being rejected; `chain` does not retire; PeTTa's rule 8 is
  exact where its variable is neither bound nor retired after its bound expression.
* `ValueRows`: HE's argument check binds the formal at the first typing that
  unifies and evaluates the argument there, its arguments in turn at their
  instances; on a value with no type row on any node it succeeds exactly where the
  machine's check does, and a row on an argument's head makes it fail where the
  machine's check passes; CeTTa's hereditary guard and its memo admit only such
  values.
* `CertifiedSpines`: a ground value typed at `(List τ)` (or `Nat`) is a spine of
  the sort's own cells exactly when no other declaration offers a type at the sort
  (`ListClosed`, `NatClosed`); a second constructor, a tuple type or a variable
  tail is certified and is no spine; under functional declarations a typed entry
  over an untyped producer is discharged exactly when each value's one derivation
  meets the formal.
* `StampStoreInvariant`: every way the type stamp store keeps a typing keeps its
  invariant that a kept node is row-free below, so the machine's check, store first,
  is HE's; leaves-up typing keeps inference's states in any order; the noted build's
  typing follows it through a collection; PeTTa's result guard and the let-bound
  argument's guard go exactly where the callee's arguments meet its version's entry
  facts, ground ones included.
* `KnownArgumentClasses`: a call site whose arguments' classes compilation reads
  (a literal's, a register's, a typed call's range, agreeing arms, a `let` body's)
  passes the typed argument check on every run, so skipping it changes no outcome,
  and the check it stands for is PeTTa's guard passing once; the reader is sound
  because return checks and shown ranges are proved together by fuel; a structural
  check decided at compilation passes on every argument vector.
* `TypedFoldBound`: in PeTTa a typed fold costs at least the best fold of its
  untyped twin: dropping the cell test is sound exactly on spines, typing
  licenses it only at a closed sort, which a typed producer of the sort opens,
  and every piece of typed evidence there is shape evidence at the same cost;
  sealed sorts, whose function rows type answers and not held applications,
  would make the typing a representation.
* `TwoWayTypedVersions`: trusted versions under logic variables, with every entry fact
  that claims groundness (GROUND, INSTANCE, the polymorphic pair, ANY, space) and
  the type claims the analysis reads: the typed analysis is sound, head unification
  of admitted arguments keeps the facts, and the version is the protocol at every
  fuel, multiplicity included, for closed, pair and instance rows; an open argument
  at a GROUND parameter, which the guard passes and the entry test refuses, would
  double an answer.
* `PrivateSpaceVersions`: under functional declarations a guard at a formal whose
  variables no other formal names continues once when the argument is typed at some
  instance and binds nothing another guard reads, so ANY and space parameters at
  private type variables ask nothing and GROUND at a private formal is its
  instance's version; space parameters are the ANY parameters a `match` reads, and
  a version reads only the spaces its entry admits.
* `ConstantInstances`: a constant parameter's instance as the C derives it, the most
  general unifier of the formal and the constant's declaration with
  `contract_fixes_closed`, is exactly the set of instances the protocol's guard on
  the constant allows; a closing derivation gives the INSTANCE entry fact, and the
  version at the derived instance is the signature's protocol.
* `SealedSorts`: the type relation of PeTTa's `ai` profile reads heads from
  `termRows` and leaves from the declarations, so a function's name keeps its
  arrow type and only held applications of functions are typed otherwise; a
  sealed-closed list or Peano sort is a representation, a producer's version
  proves its range in that relation, and a fold over the producer's answers
  drops its cell test with exactly the equations' answers.
* `SealedJudgments`: the profile's two judgments: the value judgment certifies data
  and a held call is never certified at a sealed sort; the computation judgment
  (a call typed by its head's declared rows) only refutes, exactly when no ground
  value of the declared result passes the request (by head path, not by
  unification: `Nil` is both a `(List Number)` and a `(List String)`); PeTTa's
  protocol is stated over any relation, and over the profile's a trusted version
  is the full checked call.
-/
