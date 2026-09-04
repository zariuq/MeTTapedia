import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Evidence-bearing authority semantics

This module isolates the authority algebra used by partial, resource-bounded,
and plural type-theoretic decision procedures.  It is independent of any
particular object language or runtime.

An authority fixes the meaning of a judgment and the proof-relevant evidence
accepted for its positive and negative polarities.  Its semantic outcome is
the informative four-way sum

* established evidence;
* checked obstruction;
* a stable boundary outside the authority's fragment; or
* a restartable resource frontier.

Operational failure is deliberately outside this sum.  Two refinement
relations distinguish increasing resources for one authority from moving to
a stronger authority.  The compact Boolean and public-status observations are
derived quotients.

The same data are also presented as strictly-positive indexed polynomials.
The representation equivalences make the external Lean structures models of
ordinary indexed families rather than permanent metalanguage primitives.
-/

namespace Mettapedia.TypeTheory.AuthorityTheory

universe u v w x y z k b c p

/-! ## Authorities -/

/-- An authority fixes a judgment's meaning and the evidence accepted for
both polarities. -/
structure Authority (Judgment : Type u) where
  Holds : Judgment → Prop
  Evidence : Judgment → Sort v
  Obstruction : Judgment → Sort w
  evidenceSound : ∀ judgment, Evidence judgment → Holds judgment
  obstructionSound : ∀ judgment, Obstruction judgment → ¬ Holds judgment

namespace Authority

variable {Judgment : Type u} (authority : Authority Judgment)
variable {judgment : Judgment}

/-- No sound authority can establish and refute the same judgment. -/
theorem evidence_obstruction_disjoint
    (evidence : authority.Evidence judgment)
    (obstruction : authority.Obstruction judgment) : False :=
  authority.obstructionSound judgment obstruction
    (authority.evidenceSound judgment evidence)

end Authority

/-! ## Type-valued authority families

An object theory cannot use Lean's `Prop` as a hidden oracle.  The following
record is the proof-relevant, type-valued form suitable for coding one level
up in a universe hierarchy. -/

/-- A fully proof-relevant authority family.  Its contradiction map is data:
an obstruction and a witness of the judgment's meaning produce `Empty`. -/
structure DataAuthority (Judgment : Type u) where
  Holds : Judgment → Type u
  Evidence : Judgment → Type u
  Obstruction : Judgment → Type u
  evidenceSound : ∀ judgment, Evidence judgment → Holds judgment
  obstructionSound : ∀ judgment,
    Obstruction judgment → Holds judgment → False

namespace DataAuthority

variable {Judgment : Type u} (authority : DataAuthority Judgment)
variable {judgment : Judgment}

theorem evidence_obstruction_disjoint
    (evidence : authority.Evidence judgment)
    (obstruction : authority.Obstruction judgment) : False :=
  authority.obstructionSound judgment obstruction
    (authority.evidenceSound judgment evidence)

/-- A proposition-valued external authority has a canonical proof-relevant
model one universe up.  Both truth and polarity evidence are lifted as data;
nothing is replaced by a Boolean decision. -/
def ofProp (authority : Authority.{u, 0, 0} Judgment) :
    DataAuthority Judgment where
  Holds := fun judgment => ULift.{u} (PLift (authority.Holds judgment))
  Evidence := fun judgment =>
    ULift.{u} (PLift (authority.Evidence judgment))
  Obstruction := fun judgment =>
    ULift.{u} (PLift (authority.Obstruction judgment))
  evidenceSound := by
    intro judgment evidence
    exact ⟨⟨authority.evidenceSound judgment evidence.down.down⟩⟩
  obstructionSound := by
    intro judgment obstruction holds
    exact (authority.obstructionSound judgment obstruction.down.down)
      holds.down.down

end DataAuthority

/-! ## Semantic outcomes -/

/-- One authority outcome.  Positive and negative evidence have independent
types, so checking, synthesis, and formation can share the carrier without
erasing the meaning of their payloads. -/
inductive Outcome (Established : Sort u) (Refuted : Sort v)
    (Boundary : Type w) (Incomplete : Type x) : Type (max u v w x) where
  | established (evidence : Established)
  | refuted (obstruction : Refuted)
  | outsideFragment (reason : Boundary)
  | incomplete (receipt : Incomplete)

namespace Outcome

variable {Established : Sort u} {Refuted : Sort v}
variable {Boundary : Type w} {Incomplete : Type x}

/-- The Boolean observation is intentionally partial. -/
def asBool : Outcome Established Refuted Boundary Incomplete → Option Bool
  | .established _ => some true
  | .refuted _ => some false
  | .outsideFragment _ => none
  | .incomplete _ => none

/-- A proof that an outcome contains a checked decision. -/
inductive Decided : Outcome Established Refuted Boundary Incomplete → Prop where
  | established (evidence : Established) : Decided (.established evidence)
  | refuted (obstruction : Refuted) : Decided (.refuted obstruction)

def isDecided : Outcome Established Refuted Boundary Incomplete → Bool
  | .established _ => true
  | .refuted _ => true
  | .outsideFragment _ => false
  | .incomplete _ => false

theorem decided_iff_isDecided
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    Decided outcome ↔ outcome.isDecided = true := by
  cases outcome <;> constructor <;> intro hypothesis
  · rfl
  · exact .established _
  · rfl
  · exact .refuted _
  · cases hypothesis
  · cases hypothesis
  · cases hypothesis
  · cases hypothesis

/-- The display vocabulary is a quotient of the evidence-bearing sum. -/
inductive PublicStatus where
  | established
  | refuted
  | undetermined
  | incomplete
deriving DecidableEq, Repr

def publicStatus :
    Outcome Established Refuted Boundary Incomplete → PublicStatus
  | .established _ => .established
  | .refuted _ => .refuted
  | .outsideFragment _ => .undetermined
  | .incomplete _ => .incomplete

/-- Functoriality in the positive payload. -/
def mapEstablished {Established' : Sort y} (map : Established → Established') :
    Outcome Established Refuted Boundary Incomplete →
      Outcome Established' Refuted Boundary Incomplete
  | .established evidence => .established (map evidence)
  | .refuted obstruction => .refuted obstruction
  | .outsideFragment reason => .outsideFragment reason
  | .incomplete receipt => .incomplete receipt

@[simp] theorem publicStatus_mapEstablished {Established' : Sort y}
    (map : Established → Established')
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    (outcome.mapEstablished map).publicStatus = outcome.publicStatus := by
  cases outcome <;> rfl

theorem asBool_eq_false_iff
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    outcome.asBool = some false ↔
      ∃ obstruction, outcome = .refuted obstruction := by
  cases outcome <;> simp [asBool]

theorem asBool_eq_true_iff
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    outcome.asBool = some true ↔
      ∃ evidence, outcome = .established evidence := by
  cases outcome <;> simp [asBool]

/-- Search may discard an occurrence only after checked refutation. -/
def safeRetain : Outcome Established Refuted Boundary Incomplete → Bool
  | .refuted _ => false
  | _ => true

/-- Execution requires checked positive evidence. -/
def executable : Outcome Established Refuted Boundary Incomplete → Bool
  | .established _ => true
  | _ => false

theorem safeRetain_false_iff
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    outcome.safeRetain = false ↔
      ∃ obstruction, outcome = .refuted obstruction := by
  cases outcome <;> simp [safeRetain]

theorem executable_true_iff
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    outcome.executable = true ↔
      ∃ evidence, outcome = .established evidence := by
  cases outcome <;> simp [executable]

/-! ### Orthogonal refinement axes -/

/-- Refinement obtained by increasing the budget for one fixed authority.
Only an incomplete outcome may resolve; fragment membership is stable. -/
inductive BudgetRefines :
    Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete → Prop where
  | established (before after : Established) :
      BudgetRefines (.established before) (.established after)
  | refuted (before after : Refuted) :
      BudgetRefines (.refuted before) (.refuted after)
  | outsideFragment (reason : Boundary) :
      BudgetRefines (.outsideFragment reason) (.outsideFragment reason)
  | incomplete (before after : Incomplete) :
      BudgetRefines (.incomplete before) (.incomplete after)
  | incompleteEstablished (before : Incomplete) (after : Established) :
      BudgetRefines (.incomplete before) (.established after)
  | incompleteRefuted (before : Incomplete) (after : Refuted) :
      BudgetRefines (.incomplete before) (.refuted after)

/-- Refinement obtained by moving to a stronger or revised authority.  Only
an outside-fragment outcome may resolve; resource state is not a proxy for
authority coverage. -/
inductive AuthorityRefines :
    Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete → Prop where
  | established (before after : Established) :
      AuthorityRefines (.established before) (.established after)
  | refuted (before after : Refuted) :
      AuthorityRefines (.refuted before) (.refuted after)
  | incomplete (before after : Incomplete) :
      AuthorityRefines (.incomplete before) (.incomplete after)
  | outsideFragment (before after : Boundary) :
      AuthorityRefines (.outsideFragment before) (.outsideFragment after)
  | outsideEstablished (before : Boundary) (after : Established) :
      AuthorityRefines (.outsideFragment before) (.established after)
  | outsideRefuted (before : Boundary) (after : Refuted) :
      AuthorityRefines (.outsideFragment before) (.refuted after)
  | outsideIncomplete (before : Boundary) (after : Incomplete) :
      AuthorityRefines (.outsideFragment before) (.incomplete after)

/-! The relations above are proposition-valued support readouts.  Prime's
internal metatheory needs their proof-relevant witnesses as ordinary data. -/

/-- Proof-relevant evidence for a fixed-authority budget refinement. -/
inductive BudgetRefinementEvidence
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x} :
    Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete → Type (max u v w x)
  | established (before after : Established) :
      BudgetRefinementEvidence (.established before) (.established after)
  | refuted (before after : Refuted) :
      BudgetRefinementEvidence (.refuted before) (.refuted after)
  | outsideFragment (reason : Boundary) :
      BudgetRefinementEvidence
        (.outsideFragment reason) (.outsideFragment reason)
  | incomplete (before after : Incomplete) :
      BudgetRefinementEvidence (.incomplete before) (.incomplete after)
  | incompleteEstablished (before : Incomplete) (after : Established) :
      BudgetRefinementEvidence (.incomplete before) (.established after)
  | incompleteRefuted (before : Incomplete) (after : Refuted) :
      BudgetRefinementEvidence (.incomplete before) (.refuted after)

/-- Proof-relevant evidence for refinement by a stronger authority. -/
inductive AuthorityRefinementEvidence
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x} :
    Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete → Type (max u v w x)
  | established (before after : Established) :
      AuthorityRefinementEvidence (.established before) (.established after)
  | refuted (before after : Refuted) :
      AuthorityRefinementEvidence (.refuted before) (.refuted after)
  | incomplete (before after : Incomplete) :
      AuthorityRefinementEvidence (.incomplete before) (.incomplete after)
  | outsideFragment (before after : Boundary) :
      AuthorityRefinementEvidence
        (.outsideFragment before) (.outsideFragment after)
  | outsideEstablished (before : Boundary) (after : Established) :
      AuthorityRefinementEvidence
        (.outsideFragment before) (.established after)
  | outsideRefuted (before : Boundary) (after : Refuted) :
      AuthorityRefinementEvidence (.outsideFragment before) (.refuted after)
  | outsideIncomplete (before : Boundary) (after : Incomplete) :
      AuthorityRefinementEvidence
        (.outsideFragment before) (.incomplete after)

/-! ## One refinement family, indexed by the source of improvement -/

/-- The two monotonicity claims differ by what changed: resources for one
fixed authority, or the authority itself.  Making that distinction an index
prevents evidence for one order from being replayed as evidence for the
other. -/
inductive RefinementAxis where
  | budget
  | authority
deriving DecidableEq, Repr

/-- The informative refinement family.  Constructors shared by both orders
retain the axis.  Resource resolution exists only in the budget fibre;
coverage expansion exists only in the authority fibre. -/
inductive AxisRefinementEvidence
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x} :
    RefinementAxis →
      Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete →
      Type (max u v w x) where
  | established (axis : RefinementAxis) (before after : Established) :
      AxisRefinementEvidence axis (.established before) (.established after)
  | refuted (axis : RefinementAxis) (before after : Refuted) :
      AxisRefinementEvidence axis (.refuted before) (.refuted after)
  | incomplete (axis : RefinementAxis) (before after : Incomplete) :
      AxisRefinementEvidence axis (.incomplete before) (.incomplete after)
  | budgetOutsideFragment (reason : Boundary) :
      AxisRefinementEvidence .budget
        (.outsideFragment reason) (.outsideFragment reason)
  | budgetIncompleteEstablished
      (before : Incomplete) (after : Established) :
      AxisRefinementEvidence .budget
        (.incomplete before) (.established after)
  | budgetIncompleteRefuted (before : Incomplete) (after : Refuted) :
      AxisRefinementEvidence .budget (.incomplete before) (.refuted after)
  | authorityOutsideFragment (before after : Boundary) :
      AxisRefinementEvidence .authority
        (.outsideFragment before) (.outsideFragment after)
  | authorityOutsideEstablished (before : Boundary) (after : Established) :
      AxisRefinementEvidence .authority
        (.outsideFragment before) (.established after)
  | authorityOutsideRefuted (before : Boundary) (after : Refuted) :
      AxisRefinementEvidence .authority
        (.outsideFragment before) (.refuted after)
  | authorityOutsideIncomplete (before : Boundary) (after : Incomplete) :
      AxisRefinementEvidence .authority
        (.outsideFragment before) (.incomplete after)

namespace AxisRefinementEvidence

variable {Established : Type u} {Refuted : Type v}
variable {Boundary : Type w} {Incomplete : Type x}

def fromBudget
    {before after : Outcome Established Refuted Boundary Incomplete} :
    BudgetRefinementEvidence before after →
      AxisRefinementEvidence .budget before after
  | .established before after => .established .budget before after
  | .refuted before after => .refuted .budget before after
  | .outsideFragment reason => .budgetOutsideFragment reason
  | .incomplete before after => .incomplete .budget before after
  | .incompleteEstablished before after =>
      .budgetIncompleteEstablished before after
  | .incompleteRefuted before after => .budgetIncompleteRefuted before after

def toBudget
    {before after : Outcome Established Refuted Boundary Incomplete} :
    AxisRefinementEvidence .budget before after →
      BudgetRefinementEvidence before after := by
  intro evidence
  cases evidence with
  | established _ before after => exact .established before after
  | refuted _ before after => exact .refuted before after
  | incomplete _ before after => exact .incomplete before after
  | budgetOutsideFragment reason => exact .outsideFragment reason
  | budgetIncompleteEstablished before after =>
      exact .incompleteEstablished before after
  | budgetIncompleteRefuted before after =>
      exact .incompleteRefuted before after

@[simp] theorem toBudget_fromBudget
    {before after : Outcome Established Refuted Boundary Incomplete}
    (evidence : BudgetRefinementEvidence before after) :
    toBudget (fromBudget evidence) = evidence := by
  cases evidence <;> rfl

@[simp] theorem fromBudget_toBudget
    {before after : Outcome Established Refuted Boundary Incomplete}
    (evidence : AxisRefinementEvidence .budget before after) :
    fromBudget (toBudget evidence) = evidence := by
  cases evidence <;> rfl

/-- The former budget relation is exactly the budget fibre of the unified
axis-indexed family. -/
def budgetEquiv
    {before after : Outcome Established Refuted Boundary Incomplete} :
    AxisRefinementEvidence .budget before after ≃
      BudgetRefinementEvidence before after where
  toFun := toBudget
  invFun := fromBudget
  left_inv := fromBudget_toBudget
  right_inv := toBudget_fromBudget

def fromAuthority
    {before after : Outcome Established Refuted Boundary Incomplete} :
    AuthorityRefinementEvidence before after →
      AxisRefinementEvidence .authority before after
  | .established before after => .established .authority before after
  | .refuted before after => .refuted .authority before after
  | .incomplete before after => .incomplete .authority before after
  | .outsideFragment before after =>
      .authorityOutsideFragment before after
  | .outsideEstablished before after =>
      .authorityOutsideEstablished before after
  | .outsideRefuted before after => .authorityOutsideRefuted before after
  | .outsideIncomplete before after =>
      .authorityOutsideIncomplete before after

def toAuthority
    {before after : Outcome Established Refuted Boundary Incomplete} :
    AxisRefinementEvidence .authority before after →
      AuthorityRefinementEvidence before after := by
  intro evidence
  cases evidence with
  | established _ before after => exact .established before after
  | refuted _ before after => exact .refuted before after
  | incomplete _ before after => exact .incomplete before after
  | authorityOutsideFragment before after =>
      exact .outsideFragment before after
  | authorityOutsideEstablished before after =>
      exact .outsideEstablished before after
  | authorityOutsideRefuted before after =>
      exact .outsideRefuted before after
  | authorityOutsideIncomplete before after =>
      exact .outsideIncomplete before after

@[simp] theorem toAuthority_fromAuthority
    {before after : Outcome Established Refuted Boundary Incomplete}
    (evidence : AuthorityRefinementEvidence before after) :
    toAuthority (fromAuthority evidence) = evidence := by
  cases evidence <;> rfl

@[simp] theorem fromAuthority_toAuthority
    {before after : Outcome Established Refuted Boundary Incomplete}
    (evidence : AxisRefinementEvidence .authority before after) :
    fromAuthority (toAuthority evidence) = evidence := by
  cases evidence <;> rfl

/-- The former authority relation is exactly the authority fibre of the
unified axis-indexed family. -/
def authorityEquiv
    {before after : Outcome Established Refuted Boundary Incomplete} :
    AxisRefinementEvidence .authority before after ≃
      AuthorityRefinementEvidence before after where
  toFun := toAuthority
  invFun := fromAuthority
  left_inv := fromAuthority_toAuthority
  right_inv := toAuthority_fromAuthority

end AxisRefinementEvidence

/-- Proposition-valued support is a derived readout selected by the same
axis. -/
def AxisRefines
    {Established : Sort u} {Refuted : Sort v}
    {Boundary : Type w} {Incomplete : Type x}
    (axis : RefinementAxis)
    (before after : Outcome Established Refuted Boundary Incomplete) : Prop :=
  match axis with
  | .budget => BudgetRefines before after
  | .authority => AuthorityRefines before after

def BudgetRefinementEvidence.support
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    BudgetRefinementEvidence before after → BudgetRefines before after
  | .established _ _ => .established _ _
  | .refuted _ _ => .refuted _ _
  | .outsideFragment _ => .outsideFragment _
  | .incomplete _ _ => .incomplete _ _
  | .incompleteEstablished _ _ => .incompleteEstablished _ _
  | .incompleteRefuted _ _ => .incompleteRefuted _ _

theorem nonempty_budgetRefinementEvidence_iff
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    Nonempty (BudgetRefinementEvidence before after) ↔
      BudgetRefines before after := by
  constructor
  · rintro ⟨evidence⟩
    exact evidence.support
  · intro support
    cases support with
    | established _ _ => exact ⟨.established _ _⟩
    | refuted _ _ => exact ⟨.refuted _ _⟩
    | outsideFragment _ => exact ⟨.outsideFragment _⟩
    | incomplete _ _ => exact ⟨.incomplete _ _⟩
    | incompleteEstablished _ _ => exact ⟨.incompleteEstablished _ _⟩
    | incompleteRefuted _ _ => exact ⟨.incompleteRefuted _ _⟩

def AuthorityRefinementEvidence.support
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    AuthorityRefinementEvidence before after →
      AuthorityRefines before after
  | .established _ _ => .established _ _
  | .refuted _ _ => .refuted _ _
  | .incomplete _ _ => .incomplete _ _
  | .outsideFragment _ _ => .outsideFragment _ _
  | .outsideEstablished _ _ => .outsideEstablished _ _
  | .outsideRefuted _ _ => .outsideRefuted _ _
  | .outsideIncomplete _ _ => .outsideIncomplete _ _

theorem nonempty_authorityRefinementEvidence_iff
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    Nonempty (AuthorityRefinementEvidence before after) ↔
      AuthorityRefines before after := by
  constructor
  · rintro ⟨evidence⟩
    exact evidence.support
  · intro support
    cases support with
    | established _ _ => exact ⟨.established _ _⟩
    | refuted _ _ => exact ⟨.refuted _ _⟩
    | incomplete _ _ => exact ⟨.incomplete _ _⟩
    | outsideFragment _ _ => exact ⟨.outsideFragment _ _⟩
    | outsideEstablished _ _ => exact ⟨.outsideEstablished _ _⟩
    | outsideRefuted _ _ => exact ⟨.outsideRefuted _ _⟩
    | outsideIncomplete _ _ => exact ⟨.outsideIncomplete _ _⟩

/-- Every proof-relevant witness has the proposition-valued support selected
by its axis. -/
def AxisRefinementEvidence.support
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    {axis : RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete}
    (evidence : AxisRefinementEvidence axis before after) :
    AxisRefines axis before after := by
  cases axis with
  | budget => exact (AxisRefinementEvidence.toBudget evidence).support
  | authority =>
      exact (AxisRefinementEvidence.toAuthority evidence).support

/-- The proposition-valued order forgets only which witness inhabits the
corresponding fibre; it neither adds nor removes legal transitions. -/
theorem nonempty_axisRefinementEvidence_iff
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x}
    {axis : RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete} :
    Nonempty (AxisRefinementEvidence axis before after) ↔
      AxisRefines axis before after := by
  constructor
  · rintro ⟨evidence⟩
    exact evidence.support
  · intro support
    cases axis with
    | budget =>
        change BudgetRefines before after at support
        rcases nonempty_budgetRefinementEvidence_iff.mpr support with
          ⟨evidence⟩
        exact ⟨AxisRefinementEvidence.fromBudget evidence⟩
    | authority =>
        change AuthorityRefines before after at support
        rcases nonempty_authorityRefinementEvidence_iff.mpr support with
          ⟨evidence⟩
        exact ⟨AxisRefinementEvidence.fromAuthority evidence⟩

/-! ### Histories retain the order and intermediate outcomes -/

/-- A refinement history is the free path generated by axis-labelled steps.
Unlike endpoint transitive closure, it retains every intermediate outcome,
the source of each improvement, and every proof-relevant step witness. -/
inductive RefinementPath
    {Established : Type u} {Refuted : Type v}
    {Boundary : Type w} {Incomplete : Type x} :
    Outcome Established Refuted Boundary Incomplete →
      Outcome Established Refuted Boundary Incomplete →
      Type (max (u + 1) (v + 1) w x) where
  | nil {outcome : Outcome Established Refuted Boundary Incomplete} :
      RefinementPath outcome outcome
  | cons {axis : RefinementAxis}
      {before middle after :
        Outcome Established Refuted Boundary Incomplete}
      (edge : AxisRefinementEvidence axis before middle)
      (rest : RefinementPath middle after) :
      RefinementPath before after

namespace RefinementPath

variable {Established : Type u} {Refuted : Type v}
variable {Boundary : Type w} {Incomplete : Type x}

/-- Regard one refinement witness as a one-edge history. -/
def single {axis : RefinementAxis}
    {before after : Outcome Established Refuted Boundary Incomplete}
    (edge : AxisRefinementEvidence axis before after) :
    RefinementPath before after :=
  .cons edge .nil

/-- Concatenation preserves rather than quotients the shared intermediate
outcome. -/
def append
    {first second third : Outcome Established Refuted Boundary Incomplete} :
    RefinementPath first second → RefinementPath second third →
      RefinementPath first third
  | .nil, later => later
  | .cons edge rest, later => .cons edge (append rest later)

@[simp] theorem nil_append
    {first second : Outcome Established Refuted Boundary Incomplete}
    (path : RefinementPath first second) :
    append (.nil (outcome := first)) path = path :=
  rfl

@[simp] theorem append_nil
    {first second : Outcome Established Refuted Boundary Incomplete}
    (path : RefinementPath first second) :
    append path (.nil (outcome := second)) = path := by
  induction path with
  | nil => rfl
  | cons edge rest ih => simp [append, ih]

@[simp] theorem append_assoc
    {first second third fourth :
      Outcome Established Refuted Boundary Incomplete}
    (earlier : RefinementPath first second)
    (middle : RefinementPath second third)
    (later : RefinementPath third fourth) :
    append (append earlier middle) later =
      append earlier (append middle later) := by
  induction earlier with
  | nil => rfl
  | cons edge rest ih => simp [append, ih]

/-- The label trace is a derived readout; the path remains the informative
object because it also retains intermediate outcomes and witnesses. -/
def axes {before after :
    Outcome Established Refuted Boundary Incomplete} :
    RefinementPath before after → List RefinementAxis
  | .nil => []
  | @cons _ _ _ _ axis _ _ _ _ rest => axis :: axes rest

@[simp] theorem axes_nil
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    axes (.nil (outcome := outcome)) = [] :=
  rfl

@[simp] theorem axes_cons
    {axis : RefinementAxis}
    {before middle after :
      Outcome Established Refuted Boundary Incomplete}
    (edge : AxisRefinementEvidence axis before middle)
    (rest : RefinementPath middle after) :
    axes (.cons edge rest) = axis :: axes rest :=
  rfl

@[simp] theorem axes_append
    {first second third : Outcome Established Refuted Boundary Incomplete}
    (earlier : RefinementPath first second)
    (later : RefinementPath second third) :
    axes (append earlier later) = axes earlier ++ axes later := by
  induction earlier with
  | nil => rfl
  | cons edge rest ih => simp [append, axes, ih]

/-- A stronger authority can expose a previously unavailable fragment, after
which additional resources can establish a result.  The history records both
changes and their order. -/
def authorityThenBudgetEstablished
    (boundary : Boundary) (frontier : Incomplete) (evidence : Established) :
    RefinementPath
      ((.outsideFragment boundary) :
        Outcome Established Refuted Boundary Incomplete)
      ((.established evidence) :
        Outcome Established Refuted Boundary Incomplete) :=
  .cons (.authorityOutsideIncomplete boundary frontier)
    (.cons (.budgetIncompleteEstablished frontier evidence)
      .nil)

@[simp] theorem axes_authorityThenBudgetEstablished
    (boundary : Boundary) (frontier : Incomplete) (evidence : Established) :
    axes (authorityThenBudgetEstablished
      (Refuted := Refuted) boundary frontier evidence) =
      [.authority, .budget] :=
  rfl

/-- Once a checked polarity has been reached, every legal later step retains
that polarity. -/
theorem preservesDecision
    {before after : Outcome Established Refuted Boundary Incomplete}
    (path : RefinementPath before after) {decision : Bool}
    (beforeDecided : before.asBool = some decision) :
    after.asBool = some decision := by
  induction path with
  | nil => exact beforeDecided
  | cons edge rest ih =>
      apply ih
      cases edge <;> simp_all [Outcome.asBool]

/-- No sequence of legal refinements can turn established evidence into a
checked refutation. -/
theorem establishedToRefuted_forbidden
    {evidence : Established} {obstruction : Refuted}
    (path : RefinementPath
      ((.established evidence) :
        Outcome Established Refuted Boundary Incomplete)
      ((.refuted obstruction) :
        Outcome Established Refuted Boundary Incomplete)) : False := by
  have impossible := path.preservesDecision (decision := true) rfl
  simp [Outcome.asBool] at impossible

/-- Dually, no sequence of legal refinements can turn checked refutation into
established evidence. -/
theorem refutedToEstablished_forbidden
    {obstruction : Refuted} {evidence : Established}
    (path : RefinementPath
      ((.refuted obstruction) :
        Outcome Established Refuted Boundary Incomplete)
      ((.established evidence) :
        Outcome Established Refuted Boundary Incomplete)) : False := by
  have impossible := path.preservesDecision (decision := false) rfl
  simp [Outcome.asBool] at impossible

end RefinementPath

theorem BudgetRefines.refl
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    BudgetRefines outcome outcome := by
  cases outcome <;> constructor

theorem BudgetRefines.trans
    {first second third : Outcome Established Refuted Boundary Incomplete}
    (firstSecond : BudgetRefines first second)
    (secondThird : BudgetRefines second third) :
    BudgetRefines first third := by
  cases firstSecond <;> cases secondThird <;> constructor

theorem AuthorityRefines.refl
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    AuthorityRefines outcome outcome := by
  cases outcome <;> constructor

theorem AuthorityRefines.trans
    {first second third : Outcome Established Refuted Boundary Incomplete}
    (firstSecond : AuthorityRefines first second)
    (secondThird : AuthorityRefines second third) :
    AuthorityRefines first third := by
  cases firstSecond <;> cases secondThird <;> constructor

theorem not_budget_flip_established_refuted
    (evidence : Established) (obstruction : Refuted) :
    ¬ BudgetRefines
      (.established evidence :
        Outcome Established Refuted Boundary Incomplete)
      (.refuted obstruction) := by
  intro refinement
  cases refinement

theorem not_budget_flip_refuted_established
    (obstruction : Refuted) (evidence : Established) :
    ¬ BudgetRefines
      (.refuted obstruction :
        Outcome Established Refuted Boundary Incomplete)
      (.established evidence) := by
  intro refinement
  cases refinement

theorem budget_does_not_resolve_outside
    (reason : Boundary) (later : Outcome Established Refuted Boundary Incomplete)
    (refinement : BudgetRefines (.outsideFragment reason) later) :
    later = .outsideFragment reason := by
  cases refinement
  rfl

theorem authority_does_not_resolve_incomplete
    (receipt : Incomplete)
    (later : Outcome Established Refuted Boundary Incomplete)
    (refinement : AuthorityRefines (.incomplete receipt) later) :
    ∃ laterReceipt, later = .incomplete laterReceipt := by
  cases refinement
  exact ⟨_, rfl⟩

end Outcome

/-- The outcome fiber selected by an authority and one judgment. -/
abbrev AuthorizedOutcome {Judgment : Type u}
    (authority : Authority Judgment) (Boundary : Type x)
    (Incomplete : Type y) (judgment : Judgment) :=
  Outcome (authority.Evidence judgment) (authority.Obstruction judgment)
    Boundary Incomplete

/-! ## Operational transport -/

/-- Operational failure encloses, but is not a constructor of, the semantic
result. -/
inductive RunResult (Failure : Type u) (Result : Type v) : Type (max u v) where
  | ok (result : Result)
  | fault (failure : Failure)

inductive PublicObservation (Failure : Type u) where
  | status (status : Outcome.PublicStatus)
  | operationalFault (failure : Failure)
  | invalidProtocol
deriving DecidableEq, Repr

namespace PublicObservation

def eraseFailure {Failure : Type u} :
    PublicObservation Failure → PublicObservation Unit
  | @PublicObservation.status _ value =>
      @PublicObservation.status Unit value
  | @PublicObservation.operationalFault _ _ =>
      @PublicObservation.operationalFault Unit ()
  | @PublicObservation.invalidProtocol _ =>
      @PublicObservation.invalidProtocol Unit

end PublicObservation

namespace RunResult

def mapResult {Failure : Type u} {Source : Type v} {Target : Type w}
    (map : Source → Target) : RunResult Failure Source → RunResult Failure Target
  | .ok result => .ok (map result)
  | .fault failure => .fault failure

@[simp] theorem mapResult_id {Failure : Type u} {Result : Type v}
    (result : RunResult Failure Result) :
    result.mapResult (fun value => value) = result := by
  cases result <;> rfl

@[simp] theorem mapResult_comp {Failure : Type u} {First : Type v}
    {Second : Type w} {Third : Type x} (earlier : First → Second)
    (later : Second → Third) (result : RunResult Failure First) :
    (result.mapResult earlier).mapResult later =
      result.mapResult (later ∘ earlier) := by
  cases result <;> rfl

/-- Changing only the successful result by an equivalence preserves the
outer operational-failure distinction exactly. -/
def mapResultEquiv {Failure : Type u} {Source : Type v} {Target : Type w}
    (equivalence : Source ≃ Target) :
    RunResult Failure Source ≃ RunResult Failure Target where
  toFun := mapResult equivalence
  invFun := mapResult equivalence.symm
  left_inv := by
    intro result
    cases result with
    | ok value => simp [mapResult]
    | fault failure => rfl
  right_inv := by
    intro result
    cases result with
    | ok value => simp [mapResult]
    | fault failure => rfl

def publicObservation {Failure : Type u} {Established : Sort v}
    {Refuted : Sort w} {Boundary : Type x} {Incomplete : Type y} :
    RunResult Failure (Outcome Established Refuted Boundary Incomplete) →
      PublicObservation Failure
  | .ok outcome => .status outcome.publicStatus
  | .fault failure => .operationalFault failure

theorem publicObservation_ne_invalid {Failure : Type u}
    {Established : Sort v} {Refuted : Sort w}
    {Boundary : Type x} {Incomplete : Type y}
    (result : RunResult Failure
      (Outcome Established Refuted Boundary Incomplete)) :
    result.publicObservation ≠ .invalidProtocol := by
  cases result <;> simp [publicObservation]

end RunResult

/-! ## Generic invocation receipts -/

/-- Metadata and the result of one invocation.  The requested budget and
actual cost are independent evidence: neither may be reconstructed from the
other.  Provenance and authority identity are parameters, not assumptions of
the semantic algebra. -/
structure Receipt {Judgment : Type u} (authority : Authority Judgment)
    (Boundary : Type x) (Incomplete : Type y) (Failure : Type z)
    (Budget : Type b) (Cost : Type c) (Provenance : Type p) (Key : Type k)
    (key : Key) (requested : Budget) (judgment : Judgment) where
  spent : Cost
  provenance : Provenance
  result : RunResult Failure
    (AuthorizedOutcome authority Boundary Incomplete judgment)

namespace Receipt

variable {Judgment : Type u} {authority : Authority Judgment}
variable {Boundary : Type x} {Incomplete : Type y} {Failure : Type z}
variable {Budget : Type b} {Cost : Type c} {Provenance : Type p} {Key : Type k}
variable {key : Key} {requested : Budget} {judgment : Judgment}

def publicObservation
    (receipt : Receipt authority Boundary Incomplete Failure Budget Cost
      Provenance Key key requested judgment) : PublicObservation Failure :=
  receipt.result.publicObservation

end Receipt

/-- A cached receipt retains the exact authority identity that licensed it. -/
structure CachedReceipt {Judgment : Type u} (authority : Authority Judgment)
    (Boundary : Type x) (Incomplete : Type y) (Failure : Type z)
    (Budget : Type b) (Cost : Type c) (Provenance : Type p) (Key : Type k)
    (judgment : Judgment) where
  key : Key
  requested : Budget
  receipt : Receipt authority Boundary Incomplete Failure Budget Cost
    Provenance Key key requested judgment

namespace CachedReceipt

variable {Judgment : Type u} {authority : Authority Judgment}
variable {Boundary : Type x} {Incomplete : Type y} {Failure : Type z}
variable {Budget : Type b} {Cost : Type c} {Provenance : Type p} {Key : Type k}
variable {judgment : Judgment}

def replay
    (cached : CachedReceipt authority Boundary Incomplete Failure Budget Cost
      Provenance Key judgment)
    (live : Key) (keyCurrent : cached.key = live)
    (liveBudget : Budget) (budgetCurrent : cached.requested = liveBudget) :
    Receipt authority Boundary Incomplete Failure Budget Cost Provenance Key
      live liveBudget judgment := by
  cases keyCurrent
  cases budgetCurrent
  exact cached.receipt

theorem replay_preserves_result
    (cached : CachedReceipt authority Boundary Incomplete Failure Budget Cost
      Provenance Key judgment)
    (live : Key) (keyCurrent : cached.key = live)
    (liveBudget : Budget) (budgetCurrent : cached.requested = liveBudget) :
    (cached.replay live keyCurrent liveBudget budgetCurrent).result =
      cached.receipt.result := by
  cases keyCurrent
  cases budgetCurrent
  rfl

end CachedReceipt

/-! ## Strictly-positive indexed encoding of outcomes -/

namespace OutcomeFamily

open IndexedPolynomial

/-- The four payload families of an outcome indexed by judgments. -/
structure Signature (Judgment : Type u) where
  Established : Judgment → Type u
  Refuted : Judgment → Type u
  Boundary : Judgment → Type u
  Incomplete : Judgment → Type u

/-- Supply boundary and frontier families to the semantic core of a
type-valued authority. -/
def Signature.ofAuthority {Judgment : Type u}
    (authority : DataAuthority Judgment)
    (Boundary Incomplete : Judgment → Type u) : Signature Judgment where
  Established := authority.Evidence
  Refuted := authority.Obstruction
  Boundary := Boundary
  Incomplete := Incomplete

inductive One : Type u where
  | star

inductive Void : Type u

/-- Constructor shapes retain the complete nonrecursive payload. -/
inductive Shape {Judgment : Type u} (signature : Signature Judgment) :
    Judgment → Type u where
  | established {judgment} : signature.Established judgment →
      Shape signature judgment
  | refuted {judgment} : signature.Refuted judgment →
      Shape signature judgment
  | outsideFragment {judgment} : signature.Boundary judgment →
      Shape signature judgment
  | incomplete {judgment} : signature.Incomplete judgment →
      Shape signature judgment

/-- No outcome constructor has a recursive argument.  Strict positivity is
therefore structural, rather than a separately asserted predicate. -/
def polynomial {Judgment : Type u} (signature : Signature Judgment) :
    IndexedPolynomial.{u, u, u, u}
      (One.{u}) (fun _ => Judgment) where
  Shape := fun _ judgment => Shape signature judgment
  Position := fun _ => Void
  next := fun _ position => nomatch position

abbrev Code {Judgment : Type u} (signature : Signature Judgment)
    (judgment : Judgment) : Type u :=
  Fix (polynomial signature) .star judgment

def noChildren {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} (shape : Shape signature judgment) :
    (position : (polynomial signature).Position (base := .star) shape) →
      Fix (polynomial signature) .star
        ((polynomial signature).next (base := .star) shape position) :=
  fun position => nomatch position

def established {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} (evidence : signature.Established judgment) :
    Code signature judgment :=
  .roll (.established evidence) (noChildren _)

def refuted {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} (obstruction : signature.Refuted judgment) :
    Code signature judgment :=
  .roll (.refuted obstruction) (noChildren _)

def outsideFragment {Judgment : Type u}
    {signature : Signature Judgment} {judgment : Judgment}
    (reason : signature.Boundary judgment) : Code signature judgment :=
  .roll (.outsideFragment reason) (noChildren _)

def incomplete {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} (frontier : signature.Incomplete judgment) :
    Code signature judgment :=
  .roll (.incomplete frontier) (noChildren _)

/-- Interpret the polynomial code as the semantic four-way sum. -/
def interpret {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} : Code signature judgment →
      Outcome (signature.Established judgment)
        (signature.Refuted judgment) (signature.Boundary judgment)
        (signature.Incomplete judgment)
  | .roll (.established evidence) _ => .established evidence
  | .roll (.refuted obstruction) _ => .refuted obstruction
  | .roll (.outsideFragment reason) _ => .outsideFragment reason
  | .roll (.incomplete frontier) _ => .incomplete frontier

/-- Reify a semantic outcome as an ordinary strictly-positive family value. -/
def reify {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} :
    Outcome (signature.Established judgment)
      (signature.Refuted judgment) (signature.Boundary judgment)
      (signature.Incomplete judgment) → Code signature judgment
  | .established evidence => established evidence
  | .refuted obstruction => refuted obstruction
  | .outsideFragment reason => outsideFragment reason
  | .incomplete frontier => incomplete frontier

@[simp] theorem interpret_reify {Judgment : Type u}
    {signature : Signature Judgment} {judgment : Judgment}
    (outcome : Outcome (signature.Established judgment)
      (signature.Refuted judgment) (signature.Boundary judgment)
      (signature.Incomplete judgment)) :
    interpret (reify outcome) = outcome := by
  cases outcome <;> rfl

@[simp] theorem reify_interpret {Judgment : Type u}
    {signature : Signature Judgment} {judgment : Judgment}
    (code : Code signature judgment) : reify (interpret code) = code := by
  exact
    @IndexedPolynomial.Fix.rec One (fun _ => Judgment)
      (polynomial signature) .star
      (fun index code => reify (interpret code) = code)
      (fun {index} shape children _hypotheses => by
        have childrenUnique : children = noChildren shape := by
          funext position
          exact nomatch position
        subst children
        cases shape <;> rfl)
      judgment code

/-- The external semantic carrier and internal polynomial family have exactly
the same information, constructor by constructor. -/
def representationEquiv {Judgment : Type u}
    (signature : Signature Judgment) (judgment : Judgment) :
    Code signature judgment ≃
      Outcome (signature.Established judgment)
        (signature.Refuted judgment) (signature.Boundary judgment)
        (signature.Incomplete judgment) where
  toFun := interpret
  invFun := reify
  left_inv := reify_interpret
  right_inv := interpret_reify

theorem established_ne_refuted {Judgment : Type u}
    {signature : Signature Judgment} {judgment : Judgment}
    (evidence : signature.Established judgment)
    (obstruction : signature.Refuted judgment) :
    established evidence ≠ (refuted obstruction : Code signature judgment) := by
  intro equality
  have interpreted := congrArg interpret equality
  cases interpreted

end OutcomeFamily

/-! ## Strictly-positive indexed encoding of run results -/

namespace RunFamily

open IndexedPolynomial

structure Signature (Judgment : Type u) where
  Failure : Judgment → Type u
  Result : Judgment → Type u

inductive One : Type u where
  | star

inductive Void : Type u

inductive Shape {Judgment : Type u} (signature : Signature Judgment) :
    Judgment → Type u where
  | ok {judgment} : signature.Result judgment → Shape signature judgment
  | fault {judgment} : signature.Failure judgment → Shape signature judgment

def polynomial {Judgment : Type u} (signature : Signature Judgment) :
    IndexedPolynomial.{u, u, u, u}
      (One.{u}) (fun _ => Judgment) where
  Shape := fun _ judgment => Shape signature judgment
  Position := fun _ => Void
  next := fun _ position => nomatch position

abbrev Code {Judgment : Type u} (signature : Signature Judgment)
    (judgment : Judgment) : Type u :=
  IndexedPolynomial.Fix (polynomial signature) .star judgment

def noChildren {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} (shape : Shape signature judgment) :
    (position : (polynomial signature).Position (base := .star) shape) →
      IndexedPolynomial.Fix (polynomial signature) .star
        ((polynomial signature).next (base := .star) shape position) :=
  fun position => nomatch position

def ok {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} (result : signature.Result judgment) :
    Code signature judgment :=
  .roll (.ok result) (noChildren _)

def fault {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} (failure : signature.Failure judgment) :
    Code signature judgment :=
  .roll (.fault failure) (noChildren _)

def interpret {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} : Code signature judgment →
      RunResult (signature.Failure judgment) (signature.Result judgment)
  | .roll (.ok result) _ => .ok result
  | .roll (.fault failure) _ => .fault failure

def reify {Judgment : Type u} {signature : Signature Judgment}
    {judgment : Judgment} :
    RunResult (signature.Failure judgment) (signature.Result judgment) →
      Code signature judgment
  | .ok result => ok result
  | .fault failure => fault failure

@[simp] theorem interpret_reify {Judgment : Type u}
    {signature : Signature Judgment} {judgment : Judgment}
    (result : RunResult (signature.Failure judgment)
      (signature.Result judgment)) :
    interpret (reify result) = result := by
  cases result <;> rfl

@[simp] theorem reify_interpret {Judgment : Type u}
    {signature : Signature Judgment} {judgment : Judgment}
    (code : Code signature judgment) : reify (interpret code) = code := by
  exact
    @IndexedPolynomial.Fix.rec One (fun _ => Judgment)
      (polynomial signature) .star
      (fun index code => reify (interpret code) = code)
      (fun {index} shape children _hypotheses => by
        have childrenUnique : children = noChildren shape := by
          funext position
          exact nomatch position
        subst children
        cases shape <;> rfl)
      judgment code

def representationEquiv {Judgment : Type u}
    (signature : Signature Judgment) (judgment : Judgment) :
    Code signature judgment ≃
      RunResult (signature.Failure judgment) (signature.Result judgment) where
  toFun := interpret
  invFun := reify
  left_inv := reify_interpret
  right_inv := interpret_reify

theorem ok_ne_fault {Judgment : Type u}
    {signature : Signature Judgment} {judgment : Judgment}
    (result : signature.Result judgment)
    (failure : signature.Failure judgment) :
    ok result ≠ (fault failure : Code signature judgment) := by
  intro equality
  have interpreted := congrArg interpret equality
  cases interpreted

end RunFamily

/-! ## Axiom audit -/

#print axioms Authority.evidence_obstruction_disjoint
#print axioms Outcome.BudgetRefines.trans
#print axioms Outcome.AuthorityRefines.trans
#print axioms Outcome.AxisRefinementEvidence.budgetEquiv
#print axioms Outcome.AxisRefinementEvidence.authorityEquiv
#print axioms Outcome.nonempty_axisRefinementEvidence_iff
#print axioms Outcome.RefinementPath.append_assoc
#print axioms Outcome.RefinementPath.preservesDecision
#print axioms Outcome.RefinementPath.establishedToRefuted_forbidden
#print axioms OutcomeFamily.representationEquiv
#print axioms RunFamily.representationEquiv

end Mettapedia.TypeTheory.AuthorityTheory
