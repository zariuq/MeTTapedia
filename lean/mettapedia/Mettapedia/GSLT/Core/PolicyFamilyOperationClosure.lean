import Mettapedia.GSLT.Core.PolicyFamilyTransport
import Mathlib.Data.Setoid.Basic

/-!
# Operation-stable policy families

A sufficient readout for the current observations need not support the same
observations after an operation.  An operation-reindex witness closes this
gap: every requested target observation after the operation is reconstructed
from a named source policy coordinate.  Source and target families, their
policy indices, and their dependent result types may all differ.

The witness derives preservation of policy equivalence.  It therefore gives
both an operation on observational classes and an executable action on the
canonical policy vectors.  Identity, composition, and restriction laws retain
the scope of the declared families.  Restricting the source family requires
that the needed coordinates remain available; an arbitrary smaller current
observation does not inherit operation closure.

The coordinate witness is sufficient, not necessary for every congruent
operation.  An operation using several source answers may need an additional
joint policy coordinate or a more general supplied readout runner.

These are semantic laws for supplied state operations.  They neither choose
a global observer nor certify object-language binding, substitution, identity
reflection, or a compact implementation of an infinite policy vector.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core

universe uSource uMiddle uTarget uLast
  uSourcePolicy uMiddlePolicy uTargetPolicy uLastPolicy
  uSourceResult uMiddleResult uTargetResult uLastResult uReadout

namespace PolicyFamily

variable {Source : Type uSource} {Middle : Type uMiddle}
  {Target : Type uTarget} {Last : Type uLast}

/-- Every target observation after an operation is a translated coordinate
of the source policy family.  The result translation accommodates genuinely
heterogeneous policies; exact precomposition closure uses identity translations.
The agreement field is a coordinate law, not an assumed congruence theorem. -/
structure OperationReindex
    (source : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source)
    (target : PolicyFamily.{uTarget, uTargetPolicy, uTargetResult} Target)
    (operation : Source -> Target) where
  select : target.Policy -> source.Policy
  mapResult : (policy : target.Policy) ->
    source.Result (select policy) -> target.Result policy
  agrees : forall policy state,
    mapResult policy (source.decide (select policy) state) =
      target.decide policy (operation state)

section ObservationalQuotient

variable (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source)

/-- The setoid determined by all policies in this particular family. -/
def policySetoid : Setoid Source where
  r := family.PolicyEquivalent
  iseqv := ⟨family.policyEquivalent_refl,
    fun equivalent => equivalent.symm,
    fun earlier later => earlier.trans later⟩

/-- Observational classes are scoped to a family, not a global state identity. -/
def ObservationClass : Type uSource := Quotient family.policySetoid

/-- Forget precisely the distinctions not requested by the family. -/
def toObservationClass (state : Source) : family.ObservationClass :=
  Quotient.mk family.policySetoid state

theorem observationClass_eq_iff (first second : Source) :
    family.toObservationClass first = family.toObservationClass second <->
      family.PolicyEquivalent first second :=
  Quotient.eq

/-- Every requested policy runs directly on the compatible quotient.
No representative selection or classical choice is needed. -/
def observationClassRealization :
    family.ReadoutRealization family.toObservationClass where
  run := fun policy => Quotient.lift (family.decide policy)
    (fun _ _ equivalent => equivalent policy)
  agrees := fun _ _ => rfl

end ObservationalQuotient

namespace OperationReindex

variable
  {source : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source}
  {middle : PolicyFamily.{uMiddle, uMiddlePolicy, uMiddleResult} Middle}
  {target : PolicyFamily.{uTarget, uTargetPolicy, uTargetResult} Target}
  {last : PolicyFamily.{uLast, uLastPolicy, uLastResult} Last}
  {operation : Source -> Target}

/-- The unchanged state needs the unchanged observation coordinate. -/
def id (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source) :
    OperationReindex family family _root_.id where
  select := _root_.id
  mapResult := fun _ => _root_.id
  agrees := fun _ _ => rfl

/-- Operation witnesses compose by reindexing twice and composing the
dependent result translations. -/
def comp {earlier : Source -> Middle} {later : Middle -> Target}
    (first : OperationReindex source middle earlier)
    (second : OperationReindex middle target later) :
    OperationReindex source target (later ∘ earlier) where
  select := first.select ∘ second.select
  mapResult := fun policy =>
    second.mapResult policy ∘ first.mapResult (second.select policy)
  agrees := by
    intro policy state
    exact (congrArg (second.mapResult policy)
      (first.agrees (second.select policy) state)).trans
        (second.agrees policy (earlier state))

@[simp] theorem id_comp (witness : OperationReindex source target operation) :
    (id source).comp witness = witness := by
  cases witness
  rfl

@[simp] theorem comp_id (witness : OperationReindex source target operation) :
    witness.comp (id target) = witness := by
  cases witness
  rfl

theorem comp_assoc
    {firstMap : Source -> Middle} {secondMap : Middle -> Target}
    {thirdMap : Target -> Last}
    (first : OperationReindex source middle firstMap)
    (second : OperationReindex middle target secondMap)
    (third : OperationReindex target last thirdMap) :
    (first.comp second).comp third = first.comp (second.comp third) :=
  rfl

/-- Closure under the requested precompositions derives operation
compatibility: equivalent inputs remain equivalent at the target family. -/
theorem preserves_policyEquivalent
    (witness : OperationReindex source target operation)
    {first second : Source} (equivalent : source.PolicyEquivalent first second) :
    target.PolicyEquivalent (operation first) (operation second) := by
  intro policy
  exact (witness.agrees policy first).symm.trans
    ((congrArg (witness.mapResult policy) (equivalent (witness.select policy))).trans
      (witness.agrees policy second))

/-- Any readout whose collisions respect the source policies also respects
the target policies after the operation.  No nonemptiness or choice is needed. -/
theorem compatibleReadout
    (witness : OperationReindex source target operation)
    {Readout : Type uReadout} {readout : Source -> Readout}
    (compatible : source.CompatibleReadout readout) :
    (target.pullback operation).CompatibleReadout readout := by
  intro first second sameReadout
  exact witness.preserves_policyEquivalent (compatible first second sameReadout)

/-- A concrete source runner also realizes every requested observation after
the operation, from the original readout alone. -/
def readoutRealization
    (witness : OperationReindex source target operation)
    {Readout : Type uReadout} {readout : Source -> Readout}
    (realization : source.ReadoutRealization readout) :
    (target.pullback operation).ReadoutRealization readout where
  run := fun policy observed =>
    witness.mapResult policy (realization.run (witness.select policy) observed)
  agrees := by
    intro policy state
    exact (congrArg (witness.mapResult policy)
      (realization.agrees (witness.select policy) state)).trans
        (witness.agrees policy state)

/-- Readout support is stable under an operation whose required policy
precompositions are represented by the source family. -/
theorem supportsReadout
    (witness : OperationReindex source target operation)
    {Readout : Type uReadout} {readout : Source -> Readout}
    (supported : source.SupportsReadout readout) :
    (target.pullback operation).SupportsReadout readout := by
  obtain ⟨realization⟩ := supported
  exact ⟨witness.readoutRealization realization⟩

/-- The constructive action on complete policy vectors, including vectors
not known to arise from a retained state. -/
def vectorMap (witness : OperationReindex source target operation) :
    source.Vector -> target.Vector :=
  fun values policy => witness.mapResult policy (values (witness.select policy))

@[simp] theorem vectorMap_vector
    (witness : OperationReindex source target operation) (state : Source) :
    witness.vectorMap (source.vector state) = target.vector (operation state) := by
  funext policy
  exact witness.agrees policy state

theorem vectorMap_id
    (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source) :
    (id family).vectorMap = _root_.id :=
  rfl

theorem vectorMap_comp {earlier : Source -> Middle} {later : Middle -> Target}
    (first : OperationReindex source middle earlier)
    (second : OperationReindex middle target later) :
    (first.comp second).vectorMap = second.vectorMap ∘ first.vectorMap :=
  rfl

/-- The state operation descends because its policy congruence was derived
from the coordinate witness above. -/
def classMap (witness : OperationReindex source target operation) :
    source.ObservationClass -> target.ObservationClass :=
  Quotient.map operation fun _ _ equivalent =>
    witness.preserves_policyEquivalent equivalent

@[simp] theorem classMap_toObservationClass
    (witness : OperationReindex source target operation) (state : Source) :
    witness.classMap (source.toObservationClass state) =
      target.toObservationClass (operation state) :=
  rfl

/-- The induced class operation is determined by its action on retained
states, independently of the chosen coordinate witness. -/
theorem classMap_unique
    (witness : OperationReindex source target operation)
    (candidate : source.ObservationClass -> target.ObservationClass)
    (agrees : forall state, candidate (source.toObservationClass state) =
      target.toObservationClass (operation state)) :
    candidate = witness.classMap := by
  funext stateClass
  induction stateClass using Quotient.inductionOn with
  | _ state => exact agrees state

theorem classMap_id
    (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source) :
    (id family).classMap = _root_.id := by
  funext stateClass
  induction stateClass using Quotient.inductionOn with
  | _ state => rfl

theorem classMap_comp {earlier : Source -> Middle} {later : Middle -> Target}
    (first : OperationReindex source middle earlier)
    (second : OperationReindex middle target later) :
    (first.comp second).classMap = second.classMap ∘ first.classMap := by
  funext stateClass
  induction stateClass using Quotient.inductionOn with
  | _ state => rfl

/-- Selecting fewer requested observations is itself an operation witness
for the identity state map.  No closure of that smaller family under other
operations is implied. -/
def restriction
    (family : PolicyFamily.{uSource, uSourcePolicy, uSourceResult} Source)
    {RequestedPolicy : Type*} (select : RequestedPolicy -> family.Policy) :
    OperationReindex family (family.reindex select) _root_.id where
  select := select
  mapResult := fun _ => _root_.id
  agrees := fun _ _ => rfl

/-- Restricting the target request is always safe: the source still retains
every coordinate used by the original witness. -/
def reindexTarget (witness : OperationReindex source target operation)
    {RequestedPolicy : Type*} (select : RequestedPolicy -> target.Policy) :
    OperationReindex source (target.reindex select) operation :=
  witness.comp (restriction target select)

private theorem cast_coordinate
    {Index : Type*} {Result : Index -> Type*} (values : (index : Index) -> Result index)
    {first second : Index} (same : first = second) :
    cast (congrArg Result same) (values first) = values second := by
  cases same
  rfl

/-- Restrict both sides only when the target's needed precomposition
coordinates stay inside the selected source family.  This is the closure
premise that arbitrary restriction would lose. -/
def reindex (witness : OperationReindex source target operation)
    {SourcePolicy : Type*} {TargetPolicy : Type*}
    (sourceSelect : SourcePolicy -> source.Policy)
    (targetSelect : TargetPolicy -> target.Policy)
    (select : TargetPolicy -> SourcePolicy)
    (closed : forall policy,
      sourceSelect (select policy) = witness.select (targetSelect policy)) :
    OperationReindex (source.reindex sourceSelect) (target.reindex targetSelect)
      operation where
  select := select
  mapResult := fun policy value => witness.mapResult (targetSelect policy)
    (cast (congrArg source.Result (closed policy)) value)
  agrees := by
    intro policy state
    change witness.mapResult (targetSelect policy)
      (cast (congrArg source.Result (closed policy))
        (source.decide (sourceSelect (select policy)) state)) = _
    rw [cast_coordinate (fun coordinate => source.decide coordinate state) (closed policy)]
    exact witness.agrees (targetSelect policy) state

/-- Coordinate projection commutes with the restricted executable vector
action, including its dependent result transports. -/
theorem vectorMap_reindex (witness : OperationReindex source target operation)
    {SourcePolicy : Type*} {TargetPolicy : Type*}
    (sourceSelect : SourcePolicy -> source.Policy)
    (targetSelect : TargetPolicy -> target.Policy)
    (select : TargetPolicy -> SourcePolicy)
    (closed : forall policy,
      sourceSelect (select policy) = witness.select (targetSelect policy))
    (values : source.Vector) :
    (witness.reindex sourceSelect targetSelect select closed).vectorMap
        (fun policy => values (sourceSelect policy)) =
      fun policy => witness.vectorMap values (targetSelect policy) := by
  funext policy
  change witness.mapResult (targetSelect policy)
    (cast (congrArg source.Result (closed policy))
      (values (sourceSelect (select policy)))) = _
  rw [cast_coordinate values (closed policy)]
  rfl

/-- Forgetting to closed subfamilies commutes with the descended operation. -/
theorem classMap_reindex (witness : OperationReindex source target operation)
    {SourcePolicy : Type*} {TargetPolicy : Type*}
    (sourceSelect : SourcePolicy -> source.Policy)
    (targetSelect : TargetPolicy -> target.Policy)
    (select : TargetPolicy -> SourcePolicy)
    (closed : forall policy,
      sourceSelect (select policy) = witness.select (targetSelect policy)) :
    (witness.reindex sourceSelect targetSelect select closed).classMap ∘
        (restriction source sourceSelect).classMap =
      (restriction target targetSelect).classMap ∘ witness.classMap := by
  funext stateClass
  induction stateClass using Quotient.inductionOn with
  | _ state => rfl

end OperationReindex

/-! ## Recomputing a cached answer: positive and negative controls -/

namespace OperationClosureCanary

/-- A retained count, its last reported emptiness answer, and an unrequested
cache tag.  The cached answer need not already agree with the count. -/
structure State where
  count : Nat
  reportedEmpty : Bool
  cacheTag : Nat
deriving DecidableEq

inductive Query where
  | count
  | reportedEmpty
deriving DecidableEq

/-- Counts and Boolean answers have different result types.  Cache tags
are deliberately outside this consumer's policy family. -/
def family : PolicyFamily State where
  Policy := Query
  Result
    | .count => Nat
    | .reportedEmpty => Bool
  decide
    | .count => State.count
    | .reportedEmpty => State.reportedEmpty

/-- Recompute the cached answer from retained data. -/
def refresh (state : State) : State :=
  { state with reportedEmpty := state.count == 0 }

/-- Both requested post-operation observations are reconstructed from the
count coordinate, with a Nat-to-Bool translation for the refreshed answer. -/
def refreshWitness : OperationReindex family family refresh where
  select := fun _ => .count
  mapResult
    | .count => _root_.id
    | .reportedEmpty => fun count : Nat => count == 0
  agrees := by
    intro policy state
    cases policy <;> rfl

theorem refresh_preserves_family_equivalence
    {first second : State} (equivalent : family.PolicyEquivalent first second) :
    family.PolicyEquivalent (refresh first) (refresh second) :=
  refreshWitness.preserves_policyEquivalent equivalent

/-- A concrete readout retains the two requested coordinates and omits the
cache tag. -/
def compactReadout (state : State) : Nat × Bool :=
  (state.count, state.reportedEmpty)

def compactRealization : family.ReadoutRealization compactReadout where
  run
    | .count => Prod.fst
    | .reportedEmpty => Prod.snd
  agrees := by
    intro policy state
    cases policy <;> rfl

/-- The refreshed readout is compiled from the generic realization
transport, not computed from a retained source representative. -/
def compactRefresh (observed : Nat × Bool) : Nat × Bool :=
  ((refreshWitness.readoutRealization compactRealization).run .count observed,
    (refreshWitness.readoutRealization compactRealization).run .reportedEmpty observed)

theorem compactRefresh_agrees (state : State) :
    compactRefresh (compactReadout state) = compactReadout (refresh state) := by
  apply Prod.ext
  · exact (refreshWitness.readoutRealization compactRealization).agrees .count state
  · exact (refreshWitness.readoutRealization compactRealization).agrees .reportedEmpty state

/-- Recomputing changes a stale answer and preserves an already-correct one. -/
theorem compactRefresh_executes :
    compactRefresh (0, false) = (0, true) ∧
      compactRefresh (3, false) = (3, false) :=
  ⟨rfl, rfl⟩

/-- The positive quotient is genuinely lossy: different cache tags remain
unobservable both before and after the operation. -/
theorem unrequested_tag_can_be_forgotten :
    (⟨2, false, 4⟩ : State) ≠ ⟨2, false, 9⟩ ∧
      family.toObservationClass ⟨2, false, 4⟩ =
        family.toObservationClass ⟨2, false, 9⟩ ∧
      family.toObservationClass (refresh ⟨2, false, 4⟩) =
        family.toObservationClass (refresh ⟨2, false, 9⟩) := by
  have equivalent : family.PolicyEquivalent ⟨2, false, 4⟩ ⟨2, false, 9⟩ := by
    intro policy
    cases policy <;> rfl
  exact ⟨by decide, (family.observationClass_eq_iff _ _).2 equivalent,
    (family.observationClass_eq_iff _ _).2
      (refreshWitness.preserves_policyEquivalent equivalent)⟩

def countOnly : PolicyFamily State :=
  family.reindex (fun _ : Unit => Query.count)

/-- A smaller family that retains the needed coordinate remains closed. -/
def countOnlyRefreshWitness : OperationReindex countOnly countOnly refresh :=
  refreshWitness.reindex (fun _ : Unit => Query.count)
    (fun _ : Unit => Query.count) _root_.id (fun _ => rfl)

def currentAnswer : PolicyFamily State :=
  family.reindex (fun _ : Unit => Query.reportedEmpty)

theorem currentAnswer_supports_current_readout :
    currentAnswer.SupportsReadout State.reportedEmpty := by
  refine ⟨{ run := fun _ => _root_.id, agrees := ?_ }⟩
  intro _ _
  rfl

/-- The same current Boolean answer can hide counts that the next refresh
distinguishes.  Current sufficiency therefore is not operation stability. -/
theorem same_current_answer_separated_after_refresh :
    currentAnswer.PolicyEquivalent ⟨0, false, 4⟩ ⟨1, false, 4⟩ ∧
      ¬ currentAnswer.PolicyEquivalent
        (refresh ⟨0, false, 4⟩) (refresh ⟨1, false, 4⟩) := by
  constructor
  · intro _
    rfl
  · intro equivalent
    have impossible : true = false := equivalent ()
    exact Bool.noConfusion impossible

/-- No alternative coordinate witness can repair the missing count in this
restricted family: any such witness would contradict derived congruence. -/
theorem currentAnswer_has_no_refresh_witness :
    ¬ Nonempty (OperationReindex currentAnswer currentAnswer refresh) := by
  rintro ⟨witness⟩
  exact same_current_answer_separated_after_refresh.2
    (witness.preserves_policyEquivalent
      same_current_answer_separated_after_refresh.1)

/-- There is no well-defined refresh operation on current-answer classes
whose action agrees with refresh on every retained state. -/
theorem refresh_does_not_descend_to_current_answer :
    ¬ NonFactorization.Factors currentAnswer.toObservationClass
      (currentAnswer.toObservationClass ∘ refresh) := by
  intro factors
  have sameClass := (currentAnswer.observationClass_eq_iff _ _).2
    same_current_answer_separated_after_refresh.1
  have sameAfter := factors.constantOnFibers _ _ sameClass
  exact same_current_answer_separated_after_refresh.2
    ((currentAnswer.observationClass_eq_iff _ _).1 sameAfter)

/-- Executable support for the present answer cannot be reused to execute
the refreshed answer from that answer alone. -/
theorem current_readout_refuses_refreshed_answer :
    ¬ (currentAnswer.pullback refresh).SupportsReadout State.reportedEmpty := by
  apply (currentAnswer.pullback refresh).not_supportsReadout_of_policy_collision
    State.reportedEmpty (first := ⟨0, false, 4⟩) (second := ⟨1, false, 4⟩) rfl ()
  change true ≠ false
  decide

end OperationClosureCanary

#print axioms observationClassRealization
#print axioms OperationReindex.preserves_policyEquivalent
#print axioms OperationReindex.compatibleReadout
#print axioms OperationReindex.readoutRealization
#print axioms OperationReindex.supportsReadout
#print axioms OperationReindex.id_comp
#print axioms OperationReindex.comp_id
#print axioms OperationReindex.comp_assoc
#print axioms OperationReindex.vectorMap_comp
#print axioms OperationReindex.classMap_unique
#print axioms OperationReindex.classMap_id
#print axioms OperationReindex.classMap_comp
#print axioms OperationReindex.reindex
#print axioms OperationReindex.vectorMap_reindex
#print axioms OperationReindex.classMap_reindex
#print axioms OperationClosureCanary.compactRefresh_agrees
#print axioms OperationClosureCanary.compactRefresh_executes
#print axioms OperationClosureCanary.unrequested_tag_can_be_forgotten
#print axioms OperationClosureCanary.countOnlyRefreshWitness
#print axioms OperationClosureCanary.same_current_answer_separated_after_refresh
#print axioms OperationClosureCanary.currentAnswer_has_no_refresh_witness
#print axioms OperationClosureCanary.refresh_does_not_descend_to_current_answer
#print axioms OperationClosureCanary.current_readout_refuses_refreshed_answer

end PolicyFamily

end Mettapedia.GSLT.Core
