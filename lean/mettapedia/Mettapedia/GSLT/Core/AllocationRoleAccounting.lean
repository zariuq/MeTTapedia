import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Exact role accounting for weighted events

Performance attribution is meaningful only when every measured occurrence is
assigned to exactly one role.  This module makes that condition structural:
a total classifier maps each event to one role, and the resulting sparse
account is the additive pushforward of event weights along that classifier.

The construction is independent of any runtime, allocator, language, or
choice of resource grade.  It works for every additive commutative grade.
Reclassification is an ordinary pushforward, with identity and composition
laws.  Consequently a fine accounting may be coarsened without changing its
conserved total.

The negative controls record the two common attribution failures.  Predicates
that overlap can count one occurrence twice; a partial classifier can hide an
unclassified occurrence.  Neither is representable as a total role account
without making the overlap or the unclassified role explicit.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.AllocationRoleAccounting

universe uEvent uFineRole uCoarseRole uThirdRole uGrade

variable {Event : Type uEvent}
  {FineRole : Type uFineRole} {CoarseRole : Type uCoarseRole}
  {ThirdRole : Type uThirdRole} {Grade : Type uGrade}

/-- A finite sparse account indexed by semantic role. -/
abbrev Account (Role : Type uFineRole) (Grade : Type uGrade) [Zero Grade] :=
  Role →₀ Grade

/-- Add the weight of each event to the unique role selected by a total
classifier.  Event order is retained by the source list but deliberately
forgotten by this commutative cost observation. -/
noncomputable def account
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (classify : Event → FineRole) (weight : Event → Grade) :
    List Event → Account FineRole Grade
  | [] => 0
  | event :: rest =>
      Finsupp.single (classify event) (weight event) +
        account classify weight rest

/-- Forget role distinctions and read the conserved aggregate grade. -/
noncomputable def Account.total [AddCommMonoid Grade]
    (receipt : Account FineRole Grade) : Grade :=
  receipt.sum fun _ amount => amount

@[simp]
theorem Account.total_zero [AddCommMonoid Grade] :
    Account.total (0 : Account FineRole Grade) = 0 := by
  simp [Account.total]

@[simp]
theorem Account.total_single
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (role : FineRole) (amount : Grade) :
    Account.total (Finsupp.single role amount) = amount := by
  simp [Account.total, Finsupp.sum_single_index]

@[simp]
theorem Account.total_add
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (left right : Account FineRole Grade) :
    Account.total (left + right) =
      Account.total left + Account.total right := by
  simp [Account.total, Finsupp.sum_add_index']

@[simp]
theorem account_nil
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (classify : Event → FineRole) (weight : Event → Grade) :
    account classify weight [] = 0 :=
  rfl

@[simp]
theorem account_cons
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (classify : Event → FineRole) (weight : Event → Grade)
    (event : Event) (events : List Event) :
    account classify weight (event :: events) =
      Finsupp.single (classify event) (weight event) +
        account classify weight events :=
  rfl

/-- Concatenating two chronological event batches adds their role accounts. -/
theorem account_append
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (classify : Event → FineRole) (weight : Event → Grade)
    (first second : List Event) :
    account classify weight (first ++ second) =
      account classify weight first + account classify weight second := by
  induction first with
  | nil => simp
  | cons event rest inductionHypothesis =>
      simp [inductionHypothesis, add_assoc]

/-- The sum of all exact role buckets is exactly the positional event total. -/
theorem account_total
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (classify : Event → FineRole) (weight : Event → Grade)
    (events : List Event) :
    (account classify weight events).total = (events.map weight).sum := by
  induction events with
  | nil => simp
  | cons event rest inductionHypothesis =>
      simp [inductionHypothesis]

/-! ## Reclassification as additive pushforward -/

/-- Merge fine roles along an arbitrary role map.  Colliding fine roles add
their grades in the target account. -/
noncomputable def Account.pushforward
    [DecidableEq FineRole] [DecidableEq CoarseRole]
    [AddCommMonoid Grade]
    (mapRole : FineRole → CoarseRole)
    (receipt : Account FineRole Grade) : Account CoarseRole Grade :=
  receipt.sum fun fineRole amount =>
    Finsupp.single (mapRole fineRole) amount

@[simp]
theorem Account.pushforward_zero
    [DecidableEq FineRole] [DecidableEq CoarseRole]
    [AddCommMonoid Grade]
    (mapRole : FineRole → CoarseRole) :
    Account.pushforward mapRole (0 : Account FineRole Grade) = 0 := by
  simp [Account.pushforward]

@[simp]
theorem Account.pushforward_single
    [DecidableEq FineRole] [DecidableEq CoarseRole]
    [AddCommMonoid Grade]
    (mapRole : FineRole → CoarseRole) (role : FineRole) (amount : Grade) :
    Account.pushforward mapRole (Finsupp.single role amount) =
      Finsupp.single (mapRole role) amount := by
  simp [Account.pushforward, Finsupp.sum_single_index]

@[simp]
theorem Account.pushforward_add
    [DecidableEq FineRole] [DecidableEq CoarseRole]
    [AddCommMonoid Grade]
    (mapRole : FineRole → CoarseRole)
    (left right : Account FineRole Grade) :
    Account.pushforward mapRole (left + right) =
      Account.pushforward mapRole left +
        Account.pushforward mapRole right := by
  simp [Account.pushforward, Finsupp.sum_add_index']

/-- Reclassifying the account of a batch is the same as classifying every
event directly into the coarser role. -/
theorem Account.pushforward_account
    [DecidableEq FineRole] [DecidableEq CoarseRole]
    [AddCommMonoid Grade]
    (mapRole : FineRole → CoarseRole)
    (classify : Event → FineRole) (weight : Event → Grade)
    (events : List Event) :
    Account.pushforward mapRole (account classify weight events) =
      account (mapRole ∘ classify) weight events := by
  induction events with
  | nil => simp
  | cons event rest inductionHypothesis =>
      simp [inductionHypothesis, Function.comp_apply]

/-- Pushing an account through the identity role map changes nothing. -/
theorem Account.pushforward_id
    [DecidableEq FineRole] [AddCommMonoid Grade]
    (receipt : Account FineRole Grade) :
    Account.pushforward id receipt = receipt := by
  classical
  induction receipt using Finsupp.induction with
  | zero => simp
  | single_add role amount rest _ _ inductionHypothesis =>
      calc
        Account.pushforward id (Finsupp.single role amount + rest) =
            Account.pushforward id (Finsupp.single role amount) +
              Account.pushforward id rest :=
          Account.pushforward_add id _ _
        _ = Finsupp.single role amount + rest := by
          rw [Account.pushforward_single, inductionHypothesis]
          rfl

/-- Role pushforward is functorial: two successive coarsenings equal their
composite. -/
theorem Account.pushforward_comp
    [DecidableEq FineRole] [DecidableEq CoarseRole]
    [DecidableEq ThirdRole] [AddCommMonoid Grade]
    (first : FineRole → CoarseRole) (second : CoarseRole → ThirdRole)
    (receipt : Account FineRole Grade) :
    Account.pushforward second (Account.pushforward first receipt) =
      Account.pushforward (second ∘ first) receipt := by
  classical
  induction receipt using Finsupp.induction with
  | zero => simp
  | single_add role amount rest _ _ inductionHypothesis =>
      calc
        Account.pushforward second
              (Account.pushforward first
                (Finsupp.single role amount + rest)) =
            Account.pushforward second
              (Account.pushforward first (Finsupp.single role amount) +
                Account.pushforward first rest) := by
          rw [Account.pushforward_add]
        _ = Account.pushforward second
              (Account.pushforward first (Finsupp.single role amount)) +
            Account.pushforward second
              (Account.pushforward first rest) := by
          rw [Account.pushforward_add]
        _ = Finsupp.single (second (first role)) amount +
              Account.pushforward (second ∘ first) rest := by
          rw [Account.pushforward_single, Account.pushforward_single,
            inductionHypothesis]
        _ = Account.pushforward (second ∘ first)
              (Finsupp.single role amount + rest) := by
          rw [Account.pushforward_add, Account.pushforward_single]
          rfl

/-- Coarse and fine classifiers form a lawful refinement when a role map
commutes pointwise with classification. -/
structure ClassificationRefinement
    (fine : Event → FineRole) (coarse : Event → CoarseRole) where
  mapRole : FineRole → CoarseRole
  commutes : ∀ event, mapRole (fine event) = coarse event

namespace ClassificationRefinement

variable {fine : Event → FineRole} {coarse : Event → CoarseRole}

/-- A lawful classification refinement pushes every exact finite account to
the corresponding coarse account. -/
theorem account_exact
    [DecidableEq FineRole] [DecidableEq CoarseRole]
    [AddCommMonoid Grade]
    (refinement : ClassificationRefinement fine coarse)
    (weight : Event → Grade) (events : List Event) :
    Account.pushforward refinement.mapRole (account fine weight events) =
      account coarse weight events := by
  rw [Account.pushforward_account]
  congr 1
  funext event
  exact refinement.commutes event

end ClassificationRefinement

/-! ## Positive and negative controls -/

namespace Canaries

inductive SampleEvent
  | matchNode
  | bodyNode
  | answerNode
deriving DecidableEq

inductive SampleFineRole
  | matching
  | construction
  | publication
deriving DecidableEq

inductive SampleCoarseRole
  | execution
  | publication
deriving DecidableEq

def classify : SampleEvent → SampleFineRole
  | .matchNode => .matching
  | .bodyNode => .construction
  | .answerNode => .publication

def weight : SampleEvent → Nat
  | .matchNode => 2
  | .bodyNode => 5
  | .answerNode => 3

def coarsen : SampleFineRole → SampleCoarseRole
  | .matching | .construction => .execution
  | .publication => .publication

def coarseClassify : SampleEvent → SampleCoarseRole :=
  coarsen ∘ classify

def refinement : ClassificationRefinement classify coarseClassify where
  mapRole := coarsen
  commutes := fun _ => rfl

/-- Three disjoint roles conserve the complete ten-byte sample. -/
example :
    let receipt :=
      account classify weight [.matchNode, .bodyNode, .answerNode]
    receipt .matching = 2 ∧
      receipt .construction = 5 ∧
      receipt .publication = 3 ∧
      receipt.total = 10 := by
  simp [account, Account.total, classify, weight,
    Finsupp.sum_add_index', Finsupp.sum_single_index]

/-- Merging matching and construction into execution is exact pushforward,
not a new measurement. -/
example :
    Account.pushforward coarsen
        (account classify weight [.matchNode, .bodyNode, .answerNode]) =
      account coarseClassify weight
        [.matchNode, .bodyNode, .answerNode] := by
  exact refinement.account_exact weight _

inductive OverlapRole
  | first
  | second
deriving DecidableEq

def selected : OverlapRole → SampleEvent → Bool
  | .first, .bodyNode => true
  | .second, .bodyNode => true
  | _, _ => false

def predicateTotal (role : OverlapRole)
    (events : List SampleEvent) : Nat :=
  ((events.filter fun event => selected role event).map weight).sum

/-- Two overlapping predicates count one five-byte event as ten.  This is
why roles must come from a total function rather than independent filters. -/
example :
    predicateTotal .first [.bodyNode] +
        predicateTotal .second [.bodyNode] = 10 ∧
      ([.bodyNode].map weight).sum = 5 := by
  decide

def partiallyClassify : SampleEvent → Option SampleFineRole
  | .bodyNode => none
  | event => some (classify event)

/-- A partial instrument stays conservative only when its missing events are
retained in an explicit `none` bucket.  Dropping that bucket would report two
instead of the true seven. -/
example :
    let receipt :=
      account partiallyClassify weight [.matchNode, .bodyNode]
    receipt (some .matching) = 2 ∧
      receipt none = 5 ∧
      receipt.total = 7 := by
  simp [account, Account.total, partiallyClassify, classify, weight,
    Finsupp.sum_add_index', Finsupp.sum_single_index]

end Canaries

#print axioms account_append
#print axioms account_total
#print axioms Account.pushforward_account
#print axioms Account.pushforward_id
#print axioms Account.pushforward_comp
#print axioms ClassificationRefinement.account_exact

end Mettapedia.GSLT.Core.AllocationRoleAccounting
