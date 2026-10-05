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

Evidence (`Evidence`) has four kinds. A theorem cites declarations of the
checked environment, with the binders its statement must or must not take and
whether host choice must be absent. A fixture names a test of the C draft and
lines of its expected output. An argument names a document, a heading in it and
the claim made there. A decision records a date, a quotation, and the document
that records it. Only theorems are checked by the kernel; the other kinds are
recorded as what they are.

**Two checks.** Every option standing rejected, or rejected as a default,
carries a witness (`Graph.rejectedWitnessed_iff`), and no profile named as a
default is an option ruled out (`Graph.defaultsAdmissible_iff`).

**Exact kernels.** An exact kernel, readout or quotient grade
(`GradeClaim.exactKernel`) is neither `exact` (distortion zero) nor the weaker
`preserved`: the readout's equality is exactly the behavioural equivalence, the
readout is carried over with equality, or the quotient identifies nothing further.
Options joined by exact kernel or quotient arrows make exactly the same
identifications (`Graph.identified`, `Graph.equivalences`).

**Five qualifications** (`Qualification`) are kept apart for every claim: host
dependencies, declared laws, observer restrictions, theorem evidence and fixture
evidence.

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

/-- The four kinds of evidence. Only a theorem is checked by the kernel. -/
inductive EvidenceKind where
  | «theorem»
  | fixture
  | argument
  | decision
  deriving DecidableEq, Repr

def EvidenceKind.label : EvidenceKind → String
  | .«theorem» => "theorem"
  | .fixture => "fixture"
  | .argument => "argument"
  | .decision => "decision"

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
  deriving Repr

def Evidence.kind : Evidence → EvidenceKind
  | .«theorem» _ => .«theorem»
  | .fixture .. => .fixture
  | .argument .. => .argument
  | .decision .. => .decision

/-- The documents an evidence item names. -/
def Evidence.documents : Evidence → List String
  | .argument document _ _ => [document]
  | .decision _ _ recordedIn => [recordedIn]
  | _ => []

/-- The declarations an evidence item cites. -/
def Evidence.declarations : Evidence → List Name
  | .«theorem» citations => citations.map (·.declaration)
  | _ => []

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
  deriving Repr

/-- An option ruled out, as a whole or as a default. -/
def Node.ruledOut (node : Node) : Bool :=
  node.standings.any fun record => record.standing.rulesOut

/-! ## Arrows -/

inductive ArrowKind where
  /-- The source read inside the target. -/
  | interpretation
  /-- A relation between observed carriers. -/
  | route
  /-- The target's denotation is a function of the source's. -/
  | view
  /-- A map of carriers preserving and reflecting membership, injective. -/
  | embedding
  /-- Agreement at the source implies agreement at the target. -/
  | refinement
  /-- Every observer of the source is one of the target. -/
  | inclusion
  /-- An arrow of the theory graph. -/
  | comorphism
  deriving DecidableEq, Repr

def ArrowKind.label : ArrowKind → String
  | .interpretation => "interpretation"
  | .route => "route"
  | .view => "view"
  | .embedding => "embedding"
  | .refinement => "refinement"
  | .inclusion => "inclusion"
  | .comorphism => "comorphism"

/-- The target identifies whatever the source identifies. -/
def ArrowKind.coarsens : ArrowKind → Bool
  | .view | .refinement => true
  | _ => false

/-- The three forms of an exact kernel claim. -/
inductive ExactForm where
  /-- Equality of the readout is exactly the behavioural equivalence. -/
  | kernel
  /-- The readout is carried over exactly: its value is equal before and after. -/
  | readout
  /-- The quotient by the behavioural equivalence makes no further identification. -/
  | quotient
  deriving DecidableEq, Repr

def ExactForm.label : ExactForm → String
  | .kernel => "exact kernel"
  | .readout => "exact readout"
  | .quotient => "exact quotient"

/-- The statement shape an exact form requires of one of the cited declarations,
in words. -/
def ExactForm.shape : ExactForm → String
  | .kernel => "an equivalence one side of which is an equality of readouts"
  | .readout => "an equality of readouts"
  | .quotient => "injectivity of the quotient's readout, or an equivalence with equality"

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
  /-- An exact kernel, readout or quotient theorem. It is not `exact`, which is
  distortion zero for observers given as tolerances, and it is stronger than
  `preserved`: the behavioural equivalence is exactly the kernel of the readout,
  the readout is carried over with equality, or the quotient identifies nothing
  further. `ExactForm.shape` states what a cited statement must conclude. -/
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

/-- An exact kernel or quotient claim: the two options identify exactly the same
pairs. -/
def GradeClaim.identifiesExactly : GradeClaim → Bool
  | .exactKernel .kernel | .exactKernel .quotient => true
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
  deriving Repr

/-- An arrow whose grades include an exact kernel or quotient claim. -/
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
  deriving DecidableEq, Repr

def Qualification.label : Qualification → String
  | .hostDependency => "host dependency"
  | .declaredLaw => "declared law"
  | .observerRestriction => "observer restriction"
  | .theoremEvidence => "theorem evidence"
  | .fixtureEvidence => "fixture evidence"

def Qualification.all : List Qualification :=
  [.hostDependency, .declaredLaw, .observerRestriction, .theoremEvidence, .fixtureEvidence]

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

/-! ## The graph -/

structure Graph where
  documents : List Document
  questions : List Question
  nodes : List Node
  arrows : List Arrow
  observers : List Observer
  witnesses : List Witness
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

/-- Every declaration cited by the graph, with repetitions. -/
def declarations : List Name :=
  graph.evidence.flatMap (·.declarations)

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
    (graph.evidence.flatMap (·.documents)).all fun key => graph.documents.any (·.key == key)

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

/-! ### The frontier -/

/-- The options a coarsening arrow leaves an option for, transitively, by at most
as many steps as there are arrows. -/
def coarser (id : String) : List String :=
  let step (current : List String) : List String :=
    current ++ (graph.arrows.filter fun arrow =>
      (arrow.kind.coarsens || arrow.identifiesExactly) && current.contains arrow.source).map
        (·.target) ++
      (graph.arrows.filter fun arrow =>
        arrow.identifiesExactly && current.contains arrow.target).map (·.source)
  (Nat.iterate step graph.arrows.length [id]).eraseDups

/-- The options joined to an option by exact kernel or quotient arrows, in either
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
kernel identifies. -/
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

theorem not_separated_of_mem_frontier {first second : String}
    (member : (first, second) ∈ graph.frontier) :
    graph.separated first second = false ∧ graph.identified first second = false := by
  simp only [frontier, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', Prod.mk.injEq] at member
  obtain ⟨_, _, ⟨left, right⟩, ⟨_, unseparated, unidentified⟩, rfl, rfl⟩ := member
  exact ⟨unseparated, unidentified⟩

end Graph

end Mettapedia.GSLT.Distinction.OptionGraph
