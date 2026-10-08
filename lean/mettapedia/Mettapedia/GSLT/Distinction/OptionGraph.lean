import Mettapedia.GSLT.Distinction.RouteGrades
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Option graphs: options, interpretations, observers and witnesses

An option graph keeps the options of a design question side by side, those
still open, those selected and those ruled out, together with what compares
them.

* **Options** (`Node`) belong to a question (`Question`). Each records the
  standings decided for it (`Standing`), the evidence for each standing, and
  optionally a principle ledger (`LedgerRef`: an assumption structure, a ledger
  structure of derived and refuted facts, and the theorem filling the ledger
  from the assumptions) and a closed theory of the theory graph.
* **Arrows** (`Arrow`) interpret one option in another, each with grade claims
  (`GradeClaim`) read in the vocabulary of `RouteGrades` and `NonFactorization`.
  An exact arrow has distortion zero (`RouteGrades.DistortsAtMost`), hence grade
  one; a defect `δ` (`RouteGrades.ExpandsAtMost`) gives grade at least `1 - δ`,
  and grades compose in the Łukasiewicz quantale (`RouteGrades.grade_comp`).
  A view arrow says that the target's denotation is a function of the source's
  (`NonFactorization.Factors`); a lossy arrow forgets a distinction, which a
  non-trivial fibre exhibits. `GradeClaim.vocabulary` names the declarations a
  cited statement must mention for a claim to be read that way.
* **Observers** (`Observer`) are desiderata and tests. Each declares the kind of
  evidence its verdicts are meant to rest on.
* **Witnesses** (`Witness`) give, for two options of one question, an observer,
  the concrete case and each option's verdict with its own evidence. A witness
  is kernel-checked when both verdicts rest on theorems
  (`Witness.kernelChecked`).

Evidence (`Evidence`) has five kinds. A theorem cites declarations of the
checked environment, with the binders its statement must or must not take and
whether host choice must be absent. A fixture names a test of the C draft and
lines of its expected output. An argument names a document, a heading in it and
the claim made there. A decision records a date, a quotation, and the document
that records it. An external check records a run of another proof checker on a
pinned file and preamble, with the theorems cited. Only theorems are checked by
this kernel; the other kinds are recorded as what they are, and an external
check is never counted as a kernel-checked verdict.

**Two checks.** Every option standing rejected, or rejected as a default,
carries a witness (`Graph.rejectedWitnessed_iff`), and no profile named as a
default is an option ruled out (`Graph.defaultsAdmissible_iff`).

**Kinds and contracts.** Every arrow has a kind (`ArrowKind`: restriction,
observational quotient, booleanization, interpretation, equivalence, or
unclassified) and a preservation contract (`Contract`): which formula classes,
dependent operations, evidence and commitments it preserves, each citing a theorem;
which it does not, each citing a counterexample; which are unknown; and the named
hypotheses it is conditional on. `Graph.contractsCited_iff` and
`Graph.quotientsHonest_iff` state the checks, `Graph.contractConflicts` finds a
claim contradicted by a recorded counterexample, and `Graph.lossyCounterexampled_iff`
says that an arrow claiming to forget a distinction names a counterexample.

**Upgrades.** When a theorem replaces an argument or a fixture behind a verdict, the
replaced evidence stays on the verdict as history (`Verdict.superseded`); it is not
evidence. A ledger a correction replaced stays on its option (`Node.supersededLedgers`).

**Named hypotheses and refutations.** An option may be conditional on named hypotheses
(`NamedHypothesis`) and may record hypotheses as refuted (`Refutation`).
`Graph.hypothesesUnrefuted_iff` says that no option is conditional on a hypothesis the
registry records as refuted.

**Replay pins.** A fixture's evidence was replayed at the source hashes its pin records
(`FixturePin`), and an external checker's at the hashes of its file, preamble and binary
(`ExternalCheck`). `Graph.fixturesPinned_iff` says that every cited fixture has a pin; the
generator recomputes the hashes and marks an item stale when one has moved.

**Instances.** An option may carry its denotation, its membership relation and its readings
by aspect, and an arrow the function realizing it. From these the manifest generates the
proposition a contract entry claims at the actual endpoints, for the arrow kinds whose
contracts have a uniform shape, and checks the cited theorem against it by elaboration.

**The frontier map.** Every pair of options left on the frontier has a target
(`FrontierTarget`): the one theorem or fixture that would separate or identify them, with the
verdicts it expects, the module it would live in, and ratings of confidence and value.
`Graph.frontierMapped` says that the map covers the frontier exactly, so closing a pair retires
its target.

**Obligations.** A result of the literature that options feed has obligations
(`Obligation`): each says which results it feeds, its status (proved, refuted, open), the
declaration stating it when there is one, and what proves or refutes it.
`Graph.obligationsCited_iff` says that proved and refuted obligations cite declarations and
open ones cite none.

**Exact kernels.** An exact kernel, readout, quotient or extension grade
(`GradeClaim.exactKernel`) is neither `exact` (distortion zero) nor the weaker
`preserved`: the readout's equality is exactly the behavioural equivalence, the
readout is carried over with equality, the quotient identifies nothing further, or
the two options define the same thing. Options joined by exact kernel, quotient or
extension arrows make exactly the same identifications (`Graph.identified`,
`Graph.equivalences`).

**Six qualifications** (`Qualification`) are kept apart for every claim: host
dependencies, declared laws, observer restrictions, theorem evidence, fixture
evidence, and evidence from an external checker.

**The frontier** (`Graph.frontier`) lists the pairs of options of one question
that no witness separates and no exact kernel identifies. Separation spreads along coarsening arrows (views
and rung refinements) when the observer asks whether an option identifies the
two cases: a case identified by a coarse option and kept apart by a finer one
stays identified by every coarser option (`NonTrivialFiber.coarsen`) and kept
apart by every finer one (`NonTrivialFiber.refine`). Exact kernel arrows count as
coarsening in both directions. Unordered pairs that a witness or this spreading
separates leave the frontier (`Graph.not_separated_of_mem_frontier`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.NonFactorization

universe uA uS uV uW

/-- **A fibre of a coarser invariant is a fibre of any finer one.** Values that
differ after recovery differed before it. -/
def NonTrivialFiber.refine {A : Sort uA} {S : Sort uS} {V : Sort uV} {W : Sort uW}
    {shadow : A → S} {invariant : A → V} {finer : A → W} {recover : W → V}
    (recovers : ∀ a, invariant a = recover (finer a))
    (fiber : NonTrivialFiber shadow invariant) : NonTrivialFiber shadow finer where
  left := fiber.left
  right := fiber.right
  sameShadow := fiber.sameShadow
  differentValue := fun same =>
    fiber.differentValue (by rw [recovers fiber.left, recovers fiber.right, same])

end Mettapedia.GSLT.Core.NonFactorization

namespace Mettapedia.GSLT.Distinction.OptionGraph

open Lean (Name)

/-! ## Evidence -/

/-- The kinds of evidence. Only a theorem is checked by this kernel; an external
checker's run is recorded as what it is. -/
inductive EvidenceKind where
  | «theorem»
  | fixture
  | argument
  | decision
  | external
  deriving DecidableEq, Repr

def EvidenceKind.label : EvidenceKind → String
  | .«theorem» => "theorem"
  | .fixture => "fixture"
  | .argument => "argument"
  | .decision => "decision"
  | .external => "external checker"

/-- A run of an external proof checker: the checker, the directory of its tree the
command runs in, the command, the checked file and its SHA-256, the preamble the
file is checked against and its SHA-256, the theorems of the file cited, and
declarations of the preamble cited. -/
structure ExternalCheck where
  checker : String
  directory : String
  command : String
  file : String
  fileSha256 : String
  preamble : String
  preambleSha256 : String
  theorems : List String
  preambleDeclarations : List String := []
  /-- The checker's binary, by path in its tree, and the SHA-256 it was run at. -/
  binary : String := ""
  binarySha256 : String := ""
  deriving Repr

/-- A file of a replayed evidence item, by path, and the SHA-256 it was replayed at. -/
structure PinnedFile where
  path : String
  sha256 : String
  deriving Repr

/-- The source hashes at which a fixture was last replayed: its test and its expected output, and
for a fixture checked by a gate script that script, by path relative to the root of the source
tree its suite names. The suite names the tree; where the tree lives is the generator's
business. -/
structure FixturePin where
  suite : String
  test : String
  files : List PinnedFile
  deriving Repr

/-- A declaration cited as kernel-checked evidence. `binds` are binder names
its statement must take, `avoids` are binder names it must not take, and
`choiceFree` asks that its axioms exclude host choice. -/
structure Citation where
  declaration : Name
  binds : List Name := []
  avoids : List Name := []
  choiceFree : Bool := false
  deriving Repr

/-- Evidence for a standing, an arrow or a verdict. -/
inductive Evidence where
  /-- Declarations of the checked environment. -/
  | «theorem» (citations : List Citation)
  /-- A test of the C draft: its suite, its name, and lines its expected output
  contains; no lines means the whole expected output. -/
  | fixture (suite test : String) (expected : List String)
  /-- A document (by key), a heading or phrase in it, and the claim it makes. -/
  | argument (document anchor claim : String)
  /-- A decision: its date, its words, and the document (by key) recording them. -/
  | decision (date quotation recordedIn : String)
  /-- A run of an external proof checker. It is never kernel-checked evidence here. -/
  | external (check : ExternalCheck)
  deriving Repr

def Evidence.kind : Evidence → EvidenceKind
  | .«theorem» _ => .«theorem»
  | .fixture .. => .fixture
  | .argument .. => .argument
  | .decision .. => .decision
  | .external _ => .external

/-- The documents an evidence item names. -/
def Evidence.documents : Evidence → List String
  | .argument document _ _ => [document]
  | .decision _ _ recordedIn => [recordedIn]
  | _ => []

/-- The declarations an evidence item cites. -/
def Evidence.declarations : Evidence → List Name
  | .«theorem» citations => citations.map (·.declaration)
  | _ => []

/-- Theorem evidence citing declarations with no further requirement. -/
def cites (names : List Name) : Evidence :=
  .«theorem» (names.map fun name => { declaration := name })

/-- A document that arguments and decisions refer to. -/
structure Document where
  key : String
  title : String
  date : String
  deriving Repr

/-! ## Options -/

/-- Where an option stands. -/
inductive Standing where
  /-- Explored, with no decision. -/
  | undecided
  /-- Chosen by a recorded decision. -/
  | selected
  /-- Ruled out. -/
  | rejected
  /-- Ruled out as a default; it may remain as an explicit opt-in. -/
  | rejectedAsDefault
  /-- Kept as an explicit opt-in bubble. -/
  | admittedAsBubble
  deriving DecidableEq, Repr

def Standing.label : Standing → String
  | .undecided => "undecided"
  | .selected => "selected"
  | .rejected => "rejected"
  | .rejectedAsDefault => "rejected as default"
  | .admittedAsBubble => "admitted as bubble"

/-- A standing ruled out: rejected, or rejected as a default. -/
def Standing.rulesOut : Standing → Bool
  | .rejected | .rejectedAsDefault => true
  | _ => false

structure StandingRecord where
  standing : Standing
  evidence : List Evidence
  deriving Repr

/-- A principle ledger: the structure of assumed principles, when there is one,
the structure of derived and refuted facts, and the theorem that fills the
second from the first. -/
structure LedgerRef where
  assumptions : Option Name
  ledger : Name
  proof : Name
  deriving Repr

/-- A design question: the options of one choice point. -/
structure Question where
  id : String
  title : String
  summary : String
  ledger : Option LedgerRef := none
  facts : List Evidence := []
  deriving Repr

/-- Classes of formulas. -/
inductive FormulaClass where
  | atomic
  /-- Bounded formulas built from atomic ones with conjunction, disjunction and
  bounded existentials. -/
  | boundedPositive
  | bounded
  | firstOrder
  | higherOrder
  deriving DecidableEq, Repr

def FormulaClass.label : FormulaClass → String
  | .atomic => "atomic formulas"
  | .boundedPositive => "positive bounded formulas"
  | .bounded => "bounded formulas"
  | .firstOrder => "first-order formulas"
  | .higherOrder => "higher-order formulas"

/-- Dependent operations. -/
inductive DependentOperation where
  | sigma
  | pi
  | identity
  | wType
  | substitution
  deriving DecidableEq, Repr

def DependentOperation.label : DependentOperation → String
  | .sigma => "Σ"
  | .pi => "Π"
  | .identity => "Id/J"
  | .wType => "W"
  | .substitution => "substitution"

/-- What a piece of evidence carries beyond its conclusion. -/
inductive EvidenceAspect where
  | witnesses
  | occurrences
  | provenance
  | cost
  deriving DecidableEq, Repr

def EvidenceAspect.label : EvidenceAspect → String
  | .witnesses => "witnesses"
  | .occurrences => "occurrences"
  | .provenance => "provenance"
  | .cost => "cost"

/-- Set-theoretic commitments beyond logic. -/
inductive Commitment where
  | choice
  | collection
  | universes
  deriving DecidableEq, Repr

def Commitment.label : Commitment → String
  | .choice => "choice"
  | .collection => "Collection"
  | .universes => "universes"

/-- What a contract entry is about. -/
inductive Aspect where
  | formulas (formulaClass : FormulaClass)
  | operation (operation : DependentOperation)
  | evidence (aspect : EvidenceAspect)
  | commitment (commitment : Commitment)
  /-- The logical operations on truth values: meets, joins and the top. -/
  | connectives
  /-- The laws of the source theory hold in the target. -/
  | laws
  /-- The distinctions the source makes. -/
  | distinctions
  /-- The verdicts stated for the cases the arrow is about. -/
  | verdicts
  deriving DecidableEq, Repr

def Aspect.label : Aspect → String
  | .formulas kind => kind.label
  | .operation dependent => dependent.label
  | .evidence carried => carried.label
  | .commitment made => made.label
  | .connectives => "connectives"
  | .laws => "laws of the source"
  | .distinctions => "distinctions"
  | .verdicts => "verdicts"

/-- A named hypothesis some facts of an option are conditional on: the proposition,
the facts it conditions, and the declarations that prove it, if any. A declaration
that proves it is checked to conclude in it. -/
structure NamedHypothesis where
  name : Name
  conditions : String := ""
  provedBy : List Name := []
  deriving Repr

/-- A hypothesis recorded as refuted: a declaration stating the proposition, the scope of
the refutation, and the theorems refuting it. A refuting theorem is checked to conclude in
the negation of the proposition. -/
structure Refutation where
  hypothesis : Name
  scope : String := ""
  refutedBy : List Name
  deriving Repr

/-- An option. `cProfile` is the name of the C draft's profile realizing it, and
`theory` a closed theory of the theory graph presenting it. No standing means
undecided. -/
structure Node where
  id : String
  question : String
  title : String
  summary : String
  standings : List StandingRecord := []
  cProfile : Option String := none
  ledger : Option LedgerRef := none
  theory : Option Name := none
  facts : List Evidence := []
  /-- The option's denotation on the cases its question compares: a function whose value is
  what the option makes of a case. -/
  denotation : Option Name := none
  /-- The option's membership relation, when it is a carrier of sets. -/
  membership : Option Name := none
  /-- Readings of the option by aspect: the function whose value an aspect is about. -/
  readings : List (Aspect × Name) := []
  /-- Named hypotheses some of the facts are conditional on. -/
  hypotheses : List NamedHypothesis := []
  /-- Hypotheses recorded as refuted for this option. -/
  refuted : List Refutation := []
  /-- Ledgers a correction replaced, kept as history. They are not evidence. -/
  supersededLedgers : List LedgerRef := []
  deriving Repr

/-- An option ruled out, as a whole or as a default. -/
def Node.ruledOut (node : Node) : Bool :=
  node.standings.any fun record => record.standing.rulesOut

/-! ## Arrows -/

/-- What an arrow is. The kind is separate from the grades the arrow claims and from
its preservation contract. -/
inductive ArrowKind where
  /-- The target is a sub-carrier or bubble of the source, with membership (or the
  relevant structure) restricted; for example the well-founded part. -/
  | restriction
  /-- The target is a reading of the source: its identifications include the
  source's; read with `Factors` and the exact kernel grades. -/
  | observationalQuotient
  /-- The target is the double-negation (regular) part of the source's truth values. -/
  | booleanization
  /-- The source is modelled in the target, possibly under named hypotheses. -/
  | interpretation
  /-- Source and target correspond both ways on what the contract states. -/
  | equivalence
  /-- Not yet classified. -/
  | unclassified
  deriving DecidableEq, Repr

def ArrowKind.label : ArrowKind → String
  | .restriction => "restriction"
  | .observationalQuotient => "observational quotient"
  | .booleanization => "booleanization"
  | .interpretation => "interpretation"
  | .equivalence => "equivalence"
  | .unclassified => "unclassified"

def ArrowKind.all : List ArrowKind :=
  [.restriction, .observationalQuotient, .booleanization, .interpretation, .equivalence,
    .unclassified]

/-- Kinds whose target identifies whatever the source identifies. -/
def ArrowKind.coarsens : ArrowKind → Bool
  | .observationalQuotient | .booleanization => true
  | _ => false

/-! ## Preservation contracts -/

inductive ContractStatus where
  | preserved
  | notPreserved
  | unknown
  deriving DecidableEq, Repr

def ContractStatus.label : ContractStatus → String
  | .preserved => "preserves"
  | .notPreserved => "does not preserve"
  | .unknown => "unknown"

/-- One entry of a contract. A preserved entry cites the theorem that proves it; an
entry not preserved cites a counterexample; an unknown entry cites nothing. -/
structure ContractEntry where
  aspect : Aspect
  status : ContractStatus
  citations : List Name := []
  /-- The scope of the entry, when it is narrower than the aspect. -/
  scope : String := ""
  deriving Repr

/-- A preserved entry with the theorems proving it. -/
def ContractEntry.keeps (aspect : Aspect) (citations : List Name) (scope : String := "") :
    ContractEntry :=
  { aspect, status := .preserved, citations, scope }

/-- An entry not preserved, with the counterexamples. -/
def ContractEntry.loses (aspect : Aspect) (citations : List Name) (scope : String := "") :
    ContractEntry :=
  { aspect, status := .notPreserved, citations, scope }

/-- An entry whose status is not known. -/
def ContractEntry.unknownAt (aspect : Aspect) (scope : String := "") : ContractEntry :=
  { aspect, status := .unknown, scope }

/-- What an arrow preserves and what it does not, and the named hypotheses it is
conditional on. -/
structure Contract where
  entries : List ContractEntry := []
  hypotheses : List Name := []
  deriving Repr

/-- Every claim cites: a preserved or refuted entry cites a declaration, an unknown
entry cites none. -/
def ContractEntry.wellCited (entry : ContractEntry) : Bool :=
  match entry.status with
  | .unknown => entry.citations.isEmpty
  | _ => !entry.citations.isEmpty

def Contract.wellCited (contract : Contract) : Bool :=
  contract.entries.all (·.wellCited)

def Contract.claims (contract : Contract) (status : ContractStatus) (aspect : Aspect) : Bool :=
  contract.entries.any fun entry => entry.status == status && entry.aspect == aspect

/-- The four forms of an exact kernel claim. -/
inductive ExactForm where
  /-- Equality of the readout is exactly the behavioural equivalence. -/
  | kernel
  /-- The readout is carried over exactly: its value is equal before and after. -/
  | readout
  /-- The quotient by the behavioural equivalence makes no further identification. -/
  | quotient
  /-- The two options define the same thing: the same property, the same values, a bijection,
  or a unique isomorphism respecting the structure. -/
  | extension
  deriving DecidableEq, Repr

def ExactForm.label : ExactForm → String
  | .kernel => "exact kernel"
  | .readout => "exact readout"
  | .quotient => "exact quotient"
  | .extension => "same extension"

/-- The statement shape an exact form requires of one of the cited declarations,
in words. -/
def ExactForm.shape : ExactForm → String
  | .kernel => "an equivalence one side of which is an equality of readouts"
  | .readout => "an equality of readouts"
  | .quotient => "injectivity of the quotient's readout, or an equivalence with equality"
  | .extension => "an equivalence, an equality, a bijection, or a unique isomorphism between \
      what the two options define"

/-- What an arrow preserves. -/
inductive GradeClaim where
  /-- Distortion zero: grade one. -/
  | exact
  /-- Distances grow by at most the stated defect: grade at least one minus it. -/
  | defect (bound : String)
  /-- The target's denotation is a function of the source's: no distinction is
  invented. -/
  | factors
  /-- Some distinction is forgotten: a non-trivial fibre. -/
  | lossy
  /-- The stated relation is preserved and reflected. -/
  | preserved
  /-- The target's distance never exceeds the source's. -/
  | ordered
  /-- An exact kernel, readout, quotient or extension theorem. It is not `exact`, which is
  distortion zero for observers given as tolerances, and it is stronger than
  `preserved`: the behavioural equivalence is exactly the kernel of the readout,
  the readout is carried over with equality, the quotient identifies nothing
  further, or the two options define the same thing. `ExactForm.shape` states what a
  cited statement must conclude. -/
  | exactKernel (form : ExactForm)
  /-- No grade is claimed. -/
  | ungraded
  deriving Repr

def GradeClaim.label : GradeClaim → String
  | .exact => "exact"
  | .defect _ => "defect"
  | .factors => "factors"
  | .lossy => "lossy"
  | .preserved => "preserved"
  | .ordered => "ordered"
  | .exactKernel form => form.label
  | .ungraded => "ungraded"

/-- The exact form a claim requires, if it is an exact kernel claim. -/
def GradeClaim.exactForm? : GradeClaim → Option ExactForm
  | .exactKernel form => some form
  | _ => none

/-- An exact kernel, quotient or extension claim: the two options identify exactly the
same pairs, or define the same thing. -/
def GradeClaim.identifiesExactly : GradeClaim → Bool
  | .exactKernel .kernel | .exactKernel .quotient | .exactKernel .extension => true
  | _ => false

/-- Declarations one of which a cited statement must mention for the claim to be
read in the vocabulary of route grades or of factorization. -/
def GradeClaim.vocabulary : GradeClaim → List Name
  | .exact => [``Mettapedia.GSLT.Distinction.RouteGrades.DistortsAtMost]
  | .defect _ => [``Mettapedia.GSLT.Distinction.RouteGrades.ExpandsAtMost]
  | .factors => [``Mettapedia.GSLT.Core.NonFactorization.Factors]
  | .lossy => [``Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber,
      ``Mettapedia.GSLT.Core.NonFactorization.Factors]
  | _ => []

structure Arrow where
  id : String
  source : String
  target : String
  kind : ArrowKind
  grades : List GradeClaim
  summary : String
  evidence : List Evidence
  contract : Contract := {}
  /-- The function realizing the arrow, when it has one: for a restriction, the embedding of
  the target's carrier into the source's. -/
  map : Option Name := none
  deriving Repr

/-- The declarations an arrow's contract cites, hypotheses included. -/
def Arrow.contractDeclarations (arrow : Arrow) : List Name :=
  arrow.contract.entries.flatMap (·.citations) ++ arrow.contract.hypotheses

/-- The arrow's target identifies whatever its source identifies: its kind says so,
or it claims a factorization. -/
def Arrow.coarsens (arrow : Arrow) : Bool :=
  arrow.kind.coarsens || arrow.grades.any fun claim => claim matches .factors

/-- An arrow whose grades include an exact kernel, quotient or extension claim. -/
def Arrow.identifiesExactly (arrow : Arrow) : Bool :=
  arrow.grades.any (·.identifiesExactly)

/-! ## The five qualifications of a claim -/

/-- What a claim of the graph is qualified by, kept apart:
the host's foundations the cited declarations depend on, the laws a statement or a
fixture declares instead of proving, the observer or admissible class a claim is
relative to, and whether the claim rests on a theorem or on a fixture. -/
inductive Qualification where
  /-- Axioms of the host, such as choice inherited from multisets, finite sets or
  real suprema, as against a choice-free statement. -/
  | hostDependency
  /-- Laws declared rather than proved: hypotheses of a statement, and the axioms,
  rules and profiles a fixture declares. -/
  | declaredLaw
  /-- The observer or admissible class a claim is relative to. -/
  | observerRestriction
  /-- Evidence checked by the kernel. -/
  | theoremEvidence
  /-- Evidence from a test of the C draft. -/
  | fixtureEvidence
  /-- Evidence from a run of another proof checker, never counted as kernel-checked. -/
  | externalEvidence
  deriving DecidableEq, Repr

def Qualification.label : Qualification → String
  | .hostDependency => "host dependency"
  | .declaredLaw => "declared law"
  | .observerRestriction => "observer restriction"
  | .theoremEvidence => "theorem evidence"
  | .fixtureEvidence => "fixture evidence"
  | .externalEvidence => "external checker evidence"

def Qualification.all : List Qualification :=
  [.hostDependency, .declaredLaw, .observerRestriction, .theoremEvidence, .fixtureEvidence,
    .externalEvidence]

/-! ## Observers and witnesses -/

/-- A desideratum or a test. `identifies` marks an observer asking whether an
option identifies the two cases of a witness. -/
structure Observer where
  id : String
  title : String
  reads : String
  kind : EvidenceKind
  desideratum : Bool := false
  identifies : Bool := false
  deriving Repr

structure Verdict where
  reading : String
  evidence : List Evidence
  /-- Evidence an upgrade replaced, kept as history. It is not evidence for the verdict. -/
  superseded : List Evidence := []
  deriving Repr

/-- Two options of one question, an observer, the concrete case and the verdict
of each option. For an identifying observer the left option identifies the
case and the right one keeps it apart. `pending` names declarations that would
carry a verdict as a theorem once their modules can be checked; they are not
evidence. -/
structure Witness where
  id : String
  observer : String
  left : String
  right : String
  case : String
  leftVerdict : Verdict
  rightVerdict : Verdict
  pending : List Name := []
  deriving Repr

def Verdict.kernelChecked (verdict : Verdict) : Bool :=
  !verdict.evidence.isEmpty && verdict.evidence.all fun evidence => evidence.kind == .«theorem»

/-- Both verdicts rest on theorems only. -/
def Witness.kernelChecked (witness : Witness) : Bool :=
  witness.leftVerdict.kernelChecked && witness.rightVerdict.kernelChecked

def Witness.involves (witness : Witness) (id : String) : Bool :=
  witness.left == id || witness.right == id

def Witness.evidence (witness : Witness) : List Evidence :=
  witness.leftVerdict.evidence ++ witness.rightVerdict.evidence

/-- The evidence the witness's verdicts keep as history. -/
def Witness.superseded (witness : Witness) : List Evidence :=
  witness.leftVerdict.superseded ++ witness.rightVerdict.superseded

/-! ## The graph -/

/-- The status of an obligation. -/
inductive ObligationStatus where
  | proved
  | refuted
  | «open»
  deriving DecidableEq, Repr

def ObligationStatus.label : ObligationStatus → String
  | .proved => "proved"
  | .refuted => "refuted"
  | .«open» => "open"

/-- An obligation that a result of the literature needs: the results it feeds, the document
they are in, the declaration stating it when it is stated, its status, and the declarations
that prove or refute it. A proving declaration is checked to conclude in the statement, a
refuting one in its negation. -/
structure Obligation where
  id : String
  title : String
  /-- The results it feeds, such as "Theorem 3.7". -/
  feeds : List String
  /-- The document the results are in, by key. -/
  source : String
  status : ObligationStatus
  statement : Option Name := none
  evidence : List Name := []
  hypotheses : List NamedHypothesis := []
  note : String := ""
  deriving Repr

/-- A proved or refuted obligation cites declarations; an open one cites none. -/
def Obligation.cited (obligation : Obligation) : Bool :=
  match obligation.status with
  | .«open» => obligation.evidence.isEmpty
  | _ => !obligation.evidence.isEmpty

/-- What a frontier target would do to its pair: separate the two options, or identify them. -/
inductive TargetOutcome where
  | separation
  | identification
  deriving DecidableEq, Repr

def TargetOutcome.label : TargetOutcome → String
  | .separation => "separation"
  | .identification => "identification"

/-- The one theorem or fixture that would close a pair of options left on the frontier: its
statement, the verdict expected of each option, the module it would most naturally live in, how
confident one is that it is provable with the current infrastructure, and how much closing the
pair is worth, both in percent. -/
structure FrontierTarget where
  first : String
  second : String
  outcome : TargetOutcome := .separation
  kind : EvidenceKind := .«theorem»
  statement : String
  firstVerdict : String
  secondVerdict : String
  module : String
  confidence : Nat
  value : Nat
  deriving Repr

/-- The target is about the pair of these two options, in either order. -/
def FrontierTarget.joins (target : FrontierTarget) (first second : String) : Bool :=
  (target.first == first && target.second == second) ||
    (target.first == second && target.second == first)

structure Graph where
  documents : List Document
  questions : List Question
  nodes : List Node
  arrows : List Arrow
  observers : List Observer
  witnesses : List Witness
  /-- Obligations of constructions in the literature that options feed. -/
  obligations : List Obligation := []
  /-- The source hashes at which each cited fixture was last replayed. -/
  fixturePins : List FixturePin := []
  /-- For each pair of options left on the frontier, the one theorem or fixture that would
  close it. -/
  frontierTargets : List FrontierTarget := []
  deriving Repr

namespace Graph

variable (graph : Graph)

def hasNode (id : String) : Bool :=
  graph.nodes.any (·.id == id)

def questionOf (id : String) : Option String :=
  (graph.nodes.find? (·.id == id)).map (·.question)

def observer? (id : String) : Option Observer :=
  graph.observers.find? (·.id == id)

/-- Every evidence item of the graph. -/
def evidence : List Evidence :=
  graph.questions.flatMap (·.facts) ++
    graph.nodes.flatMap (fun node => node.facts ++ node.standings.flatMap (·.evidence)) ++
    graph.arrows.flatMap (·.evidence) ++ graph.witnesses.flatMap (·.evidence)

/-- Every declaration cited by the graph, with repetitions, contracts included. -/
def declarations : List Name :=
  graph.evidence.flatMap (·.declarations) ++ graph.arrows.flatMap (·.contractDeclarations) ++
    graph.nodes.flatMap (fun node => node.hypotheses.flatMap (fun hypothesis =>
      hypothesis.name :: hypothesis.provedBy) ++
      node.refuted.flatMap fun refutation => refutation.hypothesis :: refutation.refutedBy) ++
    graph.obligations.flatMap fun obligation => obligation.statement.toList ++ obligation.evidence ++
      obligation.hypotheses.flatMap fun hypothesis => hypothesis.name :: hypothesis.provedBy

/-- Identifiers are unique; arrows and witnesses join options that exist, a
witness joins two options of one question through a known observer, every
witness verdict and every arrow has evidence, an observer's declared kind is used
by its witnesses, and every document named is listed. -/
def wellFormed : Bool :=
  decide (graph.nodes.map (·.id)).Nodup &&
    decide (graph.questions.map (·.id)).Nodup &&
    decide (graph.arrows.map (·.id)).Nodup &&
    decide (graph.observers.map (·.id)).Nodup &&
    decide (graph.witnesses.map (·.id)).Nodup &&
    decide (graph.documents.map (·.key)).Nodup &&
    graph.nodes.all (fun node => graph.questions.any (·.id == node.question)) &&
    graph.arrows.all (fun arrow =>
      graph.hasNode arrow.source && graph.hasNode arrow.target && arrow.source != arrow.target &&
        !arrow.evidence.isEmpty) &&
    graph.witnesses.all (fun witness =>
      graph.hasNode witness.left && graph.hasNode witness.right && witness.left != witness.right &&
        graph.questionOf witness.left == graph.questionOf witness.right &&
        !witness.leftVerdict.evidence.isEmpty && !witness.rightVerdict.evidence.isEmpty &&
        match graph.observer? witness.observer with
        | some observer => witness.evidence.any (·.kind == observer.kind)
        | none => false) &&
    (graph.evidence.flatMap (·.documents) ++
        graph.witnesses.flatMap (fun witness => witness.superseded.flatMap (·.documents)) ++
        graph.obligations.map (·.source)).all
      fun key => graph.documents.any (·.key == key)

/-! ### The two checks -/

/-- Every option ruled out carries a witness. -/
def rejectedWitnessed : Bool :=
  graph.nodes.all fun node => !node.ruledOut || graph.witnesses.any (·.involves node.id)

theorem rejectedWitnessed_iff :
    graph.rejectedWitnessed = true ↔
      ∀ node ∈ graph.nodes, node.ruledOut = true →
        ∃ witness ∈ graph.witnesses, witness.involves node.id = true := by
  simp only [rejectedWitnessed, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_true]
  constructor
  · intro holds node member ruled
    rcases holds node member with notRuled | witnessed
    · rw [ruled] at notRuled
      exact absurd notRuled (by decide)
    · exact witnessed
  · intro holds node member
    cases ruled : node.ruledOut
    · exact Or.inl rfl
    · exact Or.inr (holds node member ruled)

/-- No profile named as a default is realized by an option ruled out. -/
def defaultsAdmissible (defaults : List String) : Bool :=
  defaults.all fun profile =>
    graph.nodes.all fun node => !(node.cProfile == some profile && node.ruledOut)

theorem defaultsAdmissible_iff (defaults : List String) :
    graph.defaultsAdmissible defaults = true ↔
      ∀ profile ∈ defaults, ∀ node ∈ graph.nodes,
        node.cProfile = some profile → node.ruledOut = false := by
  simp only [defaultsAdmissible, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq]
  constructor
  · intro holds profile member node nodeMember realizes
    rcases holds profile member node nodeMember with different | notRuled
    · exact absurd (by rw [realizes]) different
    · exact notRuled
  · intro holds profile member node nodeMember
    by_cases realizes : node.cProfile = some profile
    · exact Or.inr (holds profile member node nodeMember realizes)
    · exact Or.inl (by simpa using realizes)

/-! ### Contracts -/

/-- Every arrow's contract cites what it claims. -/
def contractsCited : Bool :=
  graph.arrows.all (·.contract.wellCited)

theorem contractsCited_iff :
    graph.contractsCited = true ↔ ∀ arrow ∈ graph.arrows, arrow.contract.wellCited = true := by
  simp [contractsCited, List.all_eq_true]

/-- No observational quotient claims to preserve every first-order formula without a
cited theorem. -/
def quotientsHonest : Bool :=
  graph.arrows.all fun arrow =>
    arrow.kind != .observationalQuotient ||
      arrow.contract.entries.all fun entry =>
        !(entry.aspect == .formulas .firstOrder && entry.status == .preserved &&
          entry.citations.isEmpty)

theorem quotientsHonest_iff :
    graph.quotientsHonest = true ↔
      ∀ arrow ∈ graph.arrows, arrow.kind = .observationalQuotient →
        ∀ entry ∈ arrow.contract.entries,
          entry.aspect = .formulas .firstOrder → entry.status = .preserved →
            entry.citations ≠ [] := by
  simp only [quotientsHonest, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, List.isEmpty_eq_false_iff]
  constructor
  · intro holds arrow member kind entry entryMember aspect status
    rcases holds arrow member with notQuotient | entries
    · exact absurd kind notQuotient
    · rcases entries entry entryMember with (different | different) | cited
      · exact absurd aspect different
      · exact absurd status different
      · exact cited
  · intro holds arrow member
    by_cases kind : arrow.kind = .observationalQuotient
    · refine Or.inr fun entry entryMember => ?_
      by_cases aspect : entry.aspect = .formulas .firstOrder
      · by_cases status : entry.status = .preserved
        · exact Or.inr (holds arrow member kind entry entryMember aspect status)
        · exact Or.inl (Or.inr status)
      · exact Or.inl (Or.inl aspect)
    · exact Or.inl kind

/-- Claims that contradict a recorded counterexample: an arrow claims to preserve an
aspect that an arrow of the same kind between the same options records as not
preserved. Each conflict
names the claiming arrow, the aspect, and the counterexamples. -/
def contractConflicts : List (String × Aspect × List Name) :=
  graph.arrows.flatMap fun arrow =>
    (arrow.contract.entries.filter (·.status == .preserved)).flatMap fun entry =>
      (graph.arrows.filter fun other =>
          other.source == arrow.source && other.target == arrow.target &&
            other.kind == arrow.kind).flatMap fun other =>
        (other.contract.entries.filter fun refuted =>
            refuted.status == .notPreserved && refuted.aspect == entry.aspect).map fun refuted =>
          (arrow.id, entry.aspect, refuted.citations)

def contractsConsistent : Bool :=
  graph.contractConflicts.isEmpty

/-- Every hypothesis the registry records as refuted. -/
def refutations : List Refutation :=
  graph.nodes.flatMap (·.refuted)

/-- Named hypotheses of options that the registry also records as refuted: the option, the
hypothesis, and the theorems refuting it. -/
def refutedHypotheses : List (String × Name × List Name) :=
  graph.nodes.flatMap fun node => node.hypotheses.flatMap fun hypothesis =>
    (graph.refutations.filter (·.hypothesis == hypothesis.name)).map fun refutation =>
      (node.id, hypothesis.name, refutation.refutedBy)

/-- The fixtures the graph cites as evidence, by suite and test. -/
def fixtureKeys : List (String × String) :=
  graph.evidence.filterMap fun
    | .fixture suite test _ => some (suite, test)
    | _ => none

/-- Every cited fixture has a replay pin. -/
def fixturesPinned : Bool :=
  graph.fixtureKeys.all fun (suite, test) =>
    graph.fixturePins.any fun pin => pin.suite == suite && pin.test == test

theorem fixturesPinned_iff :
    graph.fixturesPinned = true ↔
      ∀ key ∈ graph.fixtureKeys, ∃ pin ∈ graph.fixturePins, pin.suite = key.1 ∧ pin.test = key.2 := by
  unfold fixturesPinned
  rw [List.all_eq_true]
  refine forall_congr' fun key => forall_congr' fun _ => ?_
  rw [List.any_eq_true]
  refine exists_congr fun pin => and_congr_right fun _ => ?_
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]

/-- Every proved or refuted obligation cites declarations, and no open one does. -/
def obligationsCited : Bool :=
  graph.obligations.all (·.cited)

theorem obligationsCited_iff :
    graph.obligationsCited = true ↔ ∀ obligation ∈ graph.obligations, obligation.cited = true :=
  List.all_eq_true

/-- No option is conditional on a hypothesis the registry records as refuted. -/
def hypothesesUnrefuted : Bool :=
  graph.refutedHypotheses.isEmpty

omit graph in
/-- A filter is empty when the predicate fails everywhere; proved here without the host's
choice, which the library lemma uses. -/
theorem filter_eq_nil_iff_forall {α : Type _} (p : α → Bool) :
    ∀ l : List α, l.filter p = [] ↔ ∀ a ∈ l, p a = false
  | [] => ⟨fun _ _ member => (nomatch member), fun _ => rfl⟩
  | a :: rest => by
    rw [List.filter_cons]
    cases h : p a with
    | false =>
      rw [if_neg (by decide : ¬ (false = true)), filter_eq_nil_iff_forall p rest]
      constructor
      · intro holds b member
        cases member with
        | head => exact h
        | tail _ member => exact holds b member
      · intro holds b member
        exact holds b (List.Mem.tail a member)
    | true =>
      rw [if_pos rfl]
      constructor
      · intro cons
        exact nomatch cons
      · intro holds
        have := holds a (List.Mem.head rest)
        rw [h] at this
        exact nomatch this

theorem hypothesesUnrefuted_iff :
    graph.hypothesesUnrefuted = true ↔
      ∀ node ∈ graph.nodes, ∀ hypothesis ∈ node.hypotheses,
        ∀ refutation ∈ graph.refutations, refutation.hypothesis ≠ hypothesis.name := by
  unfold hypothesesUnrefuted refutedHypotheses
  rw [List.isEmpty_iff, List.flatMap_eq_nil_iff]
  refine forall_congr' fun node => forall_congr' fun _ => ?_
  rw [List.flatMap_eq_nil_iff]
  refine forall_congr' fun hypothesis => forall_congr' fun _ => ?_
  rw [List.map_eq_nil_iff, filter_eq_nil_iff_forall]
  refine forall_congr' fun refutation => forall_congr' fun _ => ?_
  constructor
  · intro different same
    rw [same, beq_self_eq_true] at different
    exact nomatch different
  · intro different
    cases equal : (refutation.hypothesis == hypothesis.name)
    · rfl
    · exact absurd (beq_iff_eq.mp equal) different

/-- Every arrow that claims to forget a distinction says, in its contract, what it does
not preserve, with a counterexample. -/
def lossyCounterexampled : Bool :=
  graph.arrows.all fun arrow =>
    !(arrow.grades.any fun claim => claim matches .lossy) ||
      arrow.contract.entries.any (·.status == .notPreserved)

theorem lossyCounterexampled_iff :
    graph.lossyCounterexampled = true ↔
      ∀ arrow ∈ graph.arrows, (arrow.grades.any fun claim => claim matches .lossy) = true →
        ∃ entry ∈ arrow.contract.entries, entry.status = .notPreserved := by
  unfold lossyCounterexampled
  rw [List.all_eq_true]
  refine forall_congr' fun arrow => forall_congr' fun _ => ?_
  rw [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true]
  simp only [beq_iff_eq]
  constructor
  · rintro (notLossy | entries) lossy
    · exact absurd (lossy.symm.trans notLossy) (by decide)
    · exact entries
  · intro holds
    cases lossy : (arrow.grades.any fun claim => claim matches .lossy)
    · exact Or.inl rfl
    · exact Or.inr (holds lossy)

/-! ### The frontier -/

/-- The options a coarsening arrow leaves an option for, transitively, by at most
as many steps as there are arrows. -/
def coarser (id : String) : List String :=
  let step (current : List String) : List String :=
    current ++ (graph.arrows.filter fun arrow =>
      (arrow.coarsens || arrow.identifiesExactly) && current.contains arrow.source).map
        (·.target) ++
      (graph.arrows.filter fun arrow =>
        arrow.identifiesExactly && current.contains arrow.target).map (·.source)
  (Nat.iterate step graph.arrows.length [id]).eraseDups

/-- The options joined to an option by exact kernel, quotient or extension arrows, in either
direction, transitively: they identify exactly the same pairs. -/
def exactlyIdentified (id : String) : List String :=
  let step (current : List String) : List String :=
    current ++ (graph.arrows.filter fun arrow =>
      arrow.identifiesExactly && current.contains arrow.source).map (·.target) ++
      (graph.arrows.filter fun arrow =>
        arrow.identifiesExactly && current.contains arrow.target).map (·.source)
  (Nat.iterate step graph.arrows.length [id]).eraseDups

/-- Two options proved to make exactly the same identifications. -/
def identified (first second : String) : Bool :=
  (graph.exactlyIdentified first).contains second

/-- A witness separates the unordered pair directly, or by spreading along
coarsening arrows when its observer identifies. -/
def separatedBy (witness : Witness) (first second : String) : Bool :=
  let direct := (witness.left == first && witness.right == second) ||
    (witness.left == second && witness.right == first)
  let spreads := match graph.observer? witness.observer with
    | some observer => observer.identifies
    | none => false
  let spread (coarse fine : String) : Bool :=
    (graph.coarser witness.left).contains coarse && (graph.coarser fine).contains witness.right
  direct || (spreads && (spread first second || spread second first))

def separated (first second : String) : Bool :=
  graph.witnesses.any fun witness => graph.separatedBy witness first second

/-- The unordered pairs of a list, each once. -/
def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | head :: tail => tail.map (head, ·) ++ pairs tail

/-- Pairs of options of one question that no witness separates and no exact
kernel, quotient or extension identifies. -/
def frontier : List (String × String) :=
  graph.questions.flatMap fun question =>
    ((pairs (graph.nodes.filter (·.question == question.id))).filter fun (first, second) =>
      !graph.separated first.id second.id && !graph.identified first.id second.id).map
        fun (first, second) => (first.id, second.id)

/-- Pairs of options of one question proved to make exactly the same
identifications. -/
def equivalences : List (String × String) :=
  graph.questions.flatMap fun question =>
    ((pairs (graph.nodes.filter (·.question == question.id))).filter fun (first, second) =>
      graph.identified first.id second.id).map fun (first, second) => (first.id, second.id)

/-- Frontier pairs that no target addresses. -/
def unmappedFrontier (pairs : List (String × String) := graph.frontier) :
    List (String × String) :=
  pairs.filter fun (first, second) => !graph.frontierTargets.any (·.joins first second)

/-- Targets whose pair is no longer on the frontier: closed, or never there. -/
def staleTargets (pairs : List (String × String) := graph.frontier) : List FrontierTarget :=
  graph.frontierTargets.filter fun target =>
    !pairs.any fun (first, second) => target.joins first second

/-- Every frontier pair has a target, every target names a frontier pair, and the ratings are
percentages. The frontier is computed once. -/
def frontierMapped : Bool :=
  let pairs := graph.frontier
  (graph.unmappedFrontier pairs).isEmpty && (graph.staleTargets pairs).isEmpty &&
    graph.frontierTargets.all fun target => target.confidence ≤ 100 && target.value ≤ 100

theorem not_separated_of_mem_frontier {first second : String}
    (member : (first, second) ∈ graph.frontier) :
    graph.separated first second = false ∧ graph.identified first second = false := by
  simp only [frontier, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', Prod.mk.injEq] at member
  obtain ⟨_, _, ⟨left, right⟩, ⟨_, unseparated, unidentified⟩, rfl, rfl⟩ := member
  exact ⟨unseparated, unidentified⟩

end Graph

end Mettapedia.GSLT.Distinction.OptionGraph
