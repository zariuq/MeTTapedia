import Mettapedia.GSLT.Core.NonFactorization

/-!
# Policy families and their least sufficient readout

A readout may safely replace retained semantic state for a declared family of
policies exactly when it retains the complete vector of policy answers.  The
policy vector is therefore the least informative sufficient readout: every
other sufficient readout factors onto it, while it retains no distinction
that all declared policies ignore.

The realization is proof-relevant data rather than only an existence claim.
This lets a later admission layer retain the actual functions run after the
factorization has been established.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core

universe uState uPolicy uResult uReadout

/-- A dependent family of decisions or observations over one retained state
space.  Different policies may return values of different types. -/
structure PolicyFamily (State : Type uState) where
  Policy : Type uPolicy
  Result : Policy -> Type uResult
  decide : (policy : Policy) -> State -> Result policy

namespace PolicyFamily

variable {State : Type uState}

/-- The complete vector of answers requested by a policy family. -/
abbrev Vector (family : PolicyFamily.{uState, uPolicy, uResult} State) :=
  (policy : family.Policy) -> family.Result policy

/-- The canonical readout that retains exactly every requested answer. -/
def vector (family : PolicyFamily.{uState, uPolicy, uResult} State) :
    State -> family.Vector :=
  fun state policy => family.decide policy state

/-- Restrict or reindex a policy family without changing its retained state.
This is the formal subrequest operation used when a consumer asks for fewer
capabilities. -/
def reindex (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {RequestedPolicy : Type*} (select : RequestedPolicy -> family.Policy) :
    PolicyFamily State where
  Policy := RequestedPolicy
  Result := fun policy => family.Result (select policy)
  decide := fun policy => family.decide (select policy)

/-- Executable policy functions over a proposed readout, together with their
agreement with the policies on every retained state. -/
structure ReadoutRealization
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout) where
  run : (policy : family.Policy) -> Readout -> family.Result policy
  agrees : forall policy state,
    run policy (readout state) = family.decide policy state

/-- Propositional support is inhabited executable realization data. -/
def SupportsReadout
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout) : Prop :=
  Nonempty (family.ReadoutRealization readout)

/-- The canonical policy vector evaluates each requested coordinate. -/
def vectorRealization
    (family : PolicyFamily.{uState, uPolicy, uResult} State) :
    family.ReadoutRealization family.vector where
  run := fun policy values => values policy
  agrees := by
    intro policy state
    rfl

/-- A realization of a larger family realizes every reindexed subfamily by
forgetting the unrequested runners. -/
def ReadoutRealization.reindex
    {family : PolicyFamily.{uState, uPolicy, uResult} State}
    {Readout : Type uReadout} {readout : State -> Readout}
    (realization : family.ReadoutRealization readout)
    {RequestedPolicy : Type*} (select : RequestedPolicy -> family.Policy) :
    (family.reindex select).ReadoutRealization readout where
  run := fun policy => realization.run (select policy)
  agrees := fun policy state => realization.agrees (select policy) state

/-- Every executable realization makes the canonical policy vector factor
through its readout. -/
theorem ReadoutRealization.vectorFactors
    {family : PolicyFamily.{uState, uPolicy, uResult} State}
    {Readout : Type uReadout} {readout : State -> Readout}
    (realization : family.ReadoutRealization readout) :
    NonFactorization.Factors readout family.vector := by
  refine ⟨fun observed policy => realization.run policy observed, fun state => ?_⟩
  funext policy
  exact realization.agrees policy state

/-- **Exact family-sufficiency criterion.**  A readout supports every policy
exactly when the canonical vector factors through it. -/
theorem supportsReadout_iff_vectorFactors
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout) :
    family.SupportsReadout readout <->
      NonFactorization.Factors readout family.vector := by
  constructor
  · rintro ⟨realization⟩
    exact realization.vectorFactors
  · rintro ⟨recover, recovers⟩
    refine ⟨{
      run := fun policy observed => recover observed policy
      agrees := ?_ }⟩
    intro policy state
    exact congrFun (recovers state) policy

/-- **Least-sufficient-readout universal property.**  The policy vector is
itself sufficient, and every sufficient readout refines it by a fixed
forgetful map. -/
theorem vector_isLeastSufficient
    (family : PolicyFamily.{uState, uPolicy, uResult} State) :
    family.SupportsReadout family.vector /\
      forall (Readout : Type uReadout) (readout : State -> Readout),
        family.SupportsReadout readout ->
          NonFactorization.Factors readout family.vector := by
  constructor
  · exact ⟨family.vectorRealization⟩
  · intro Readout readout supported
    exact (family.supportsReadout_iff_vectorFactors readout).1 supported

/-- The complete vector of a larger family refines the vector of every
reindexed subfamily by coordinate projection. -/
theorem vector_refines_reindexedVector
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {RequestedPolicy : Type*} (select : RequestedPolicy -> family.Policy) :
    NonFactorization.Factors family.vector (family.reindex select).vector := by
  exact ⟨fun values policy => values (select policy), fun _ => rfl⟩

/-- Supporting a request is monotone under removal of policies. -/
theorem supportsReadout_reindex
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} {readout : State -> Readout}
    {RequestedPolicy : Type*} (select : RequestedPolicy -> family.Policy)
    (supported : family.SupportsReadout readout) :
    (family.reindex select).SupportsReadout readout := by
  obtain ⟨realization⟩ := supported
  exact ⟨realization.reindex select⟩

/-- Equality of canonical vectors is exactly observational equivalence for
every policy in the family. -/
theorem vector_eq_iff
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    (first second : State) :
    family.vector first = family.vector second <->
      forall policy, family.decide policy first = family.decide policy second := by
  constructor
  · intro same policy
    exact congrFun same policy
  · intro same
    funext policy
    exact same policy

/-! ## Compression compatibility

The factorization criterion above is the constructive admission interface: a
consumer receives the actual runners.  The following fibrewise formulation is
the extensional mathematical boundary.  A compression is compatible with a
policy family exactly when every pair it identifies receives the same answer
from every requested policy.

The reverse direction for an arbitrary key type is classically existential:
unreachable keys need arbitrary results.  Runtime admission must therefore
retain a concrete `ReadoutRealization`; the classical characterization is a
specification, not an executable kernel-selection oracle.
-/

/-- Two retained states are indistinguishable to a complete policy family. -/
def PolicyEquivalent
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    (first second : State) : Prop :=
  forall policy,
    family.decide policy first = family.decide policy second

/-- A readout is extensionally compatible with a policy family when every
readout collision is policy-indistinguishable. -/
def CompatibleReadout
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout) : Prop :=
  forall first second,
    readout first = readout second -> family.PolicyEquivalent first second

theorem policyEquivalent_refl
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    (state : State) :
    family.PolicyEquivalent state state := by
  intro policy
  rfl

theorem PolicyEquivalent.symm
    {family : PolicyFamily.{uState, uPolicy, uResult} State}
    {first second : State}
    (equivalent : family.PolicyEquivalent first second) :
    family.PolicyEquivalent second first := by
  intro policy
  exact (equivalent policy).symm

theorem PolicyEquivalent.trans
    {family : PolicyFamily.{uState, uPolicy, uResult} State}
    {first second third : State}
    (earlier : family.PolicyEquivalent first second)
    (later : family.PolicyEquivalent second third) :
    family.PolicyEquivalent first third := by
  intro policy
  exact (earlier policy).trans (later policy)

/-- Compatibility is exactly constancy of the complete policy vector on the
fibres of the readout. -/
theorem compatibleReadout_iff_vector_constantOnFibers
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout) :
    family.CompatibleReadout readout <->
      NonFactorization.ConstantOnFibers readout family.vector := by
  constructor
  · intro compatible first second sameReadout
    exact (family.vector_eq_iff first second).2
      (compatible first second sameReadout)
  · intro constant first second sameReadout
    exact (family.vector_eq_iff first second).1
      (constant first second sameReadout)

/-- Every admitted executable readout is extensionally compatible.  This
direction is constructive and is the safety theorem used by admission. -/
theorem supportsReadout_implies_compatible
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout)
    (supported : family.SupportsReadout readout) :
    family.CompatibleReadout readout := by
  rw [family.compatibleReadout_iff_vector_constantOnFibers readout]
  exact ((family.supportsReadout_iff_vectorFactors readout).1 supported).constantOnFibers

/-- A supplied section turns fibrewise compatibility into an executable
realization without choice.  This is the strongest directly computational
form of the criterion: a native implementation supplies the representative
function and the proof that every key is represented. -/
def readoutRealizationOfSection
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout)
    (representative : Readout -> State)
    (represents : Function.RightInverse representative readout)
    (compatible : family.CompatibleReadout readout) :
    family.ReadoutRealization readout where
  run := fun policy observed => family.decide policy (representative observed)
  agrees := by
    intro policy state
    exact compatible (representative (readout state)) state
      (represents (readout state)) policy

/-- With a concrete section, compatibility and executable support coincide
constructively. -/
theorem supportsReadout_iff_compatible_of_section
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout)
    (representative : Readout -> State)
    (represents : Function.RightInverse representative readout) :
    family.SupportsReadout readout <-> family.CompatibleReadout readout := by
  constructor
  · exact family.supportsReadout_implies_compatible readout
  · intro compatible
    exact ⟨family.readoutRealizationOfSection readout representative
      represents compatible⟩

/-- **Exact extensional compression criterion.**  On a nonempty retained
state space, a readout supports a complete policy family exactly when every
pair it identifies is policy-equivalent.

The reverse implication uses classical choice only to assign results to
unreachable readout values.  A NIK admission record still carries an explicit
`ReadoutRealization`; this theorem does not synthesize production code. -/
theorem supportsReadout_iff_compatible
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    [Nonempty State]
    {Readout : Type uReadout} (readout : State -> Readout) :
    family.SupportsReadout readout <-> family.CompatibleReadout readout := by
  constructor
  · exact family.supportsReadout_implies_compatible readout
  · intro compatible
    classical
    let fallback : family.Vector :=
      family.vector (Classical.choice (inferInstance : Nonempty State))
    let recover : Readout -> family.Vector := fun observed =>
      if witnessed : exists state, readout state = observed then
        family.vector (Classical.choose witnessed)
      else
        fallback
    rw [family.supportsReadout_iff_vectorFactors readout]
    refine ⟨recover, fun state => ?_⟩
    have witnessed : exists candidate, readout candidate = readout state :=
      ⟨state, rfl⟩
    simp only [recover, dif_pos witnessed]
    exact (family.vector_eq_iff (Classical.choose witnessed) state).2
      (compatible (Classical.choose witnessed) state
        (Classical.choose_spec witnessed))

/-- One readout collision separated by one declared policy refutes support
for the complete family. -/
theorem not_supportsReadout_of_policy_collision
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Readout : Type uReadout} (readout : State -> Readout)
    {first second : State} (sameReadout : readout first = readout second)
    (policy : family.Policy)
    (differentDecision :
      family.decide policy first ≠ family.decide policy second) :
    Not (family.SupportsReadout readout) := by
  rintro ⟨realization⟩
  apply differentDecision
  calc
    family.decide policy first = realization.run policy (readout first) :=
      (realization.agrees policy first).symm
    _ = realization.run policy (readout second) :=
      congrArg (realization.run policy) sameReadout
    _ = family.decide policy second := realization.agrees policy second

/-- Sufficiency is monotone in retained information: anything that can
reconstruct a sufficient readout is itself sufficient. -/
theorem supportsReadout_of_refinement
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Fine : Type uReadout} {Coarse : Type*}
    {fine : State -> Fine} {coarse : State -> Coarse}
    (refines : NonFactorization.Factors fine coarse)
    (coarseSupports : family.SupportsReadout coarse) :
    family.SupportsReadout fine := by
  rw [family.supportsReadout_iff_vectorFactors] at coarseSupports ⊢
  obtain ⟨forget, forgets⟩ := refines
  obtain ⟨recover, recovers⟩ := coarseSupports
  refine ⟨recover ∘ forget, fun state => ?_⟩
  simp only [Function.comp_apply]
  calc
    recover (forget (fine state)) = recover (coarse state) :=
      congrArg recover (forgets state)
    _ = family.vector state := recovers state

end PolicyFamily

/-! ## A small positive and negative control -/

namespace PolicyFamilyCanary

inductive Axis where
  | work
  | span
deriving DecidableEq

structure WorkSpan where
  work : Nat
  span : Nat
deriving DecidableEq

/-- Both scheduling coordinates are declared as policies over one state. -/
def bothAxes : PolicyFamily WorkSpan where
  Policy := Axis
  Result := fun _ => Nat
  decide := fun
    | .work => WorkSpan.work
    | .span => WorkSpan.span

/-- Retaining the complete state supports both declared coordinates. -/
theorem identity_supports_bothAxes :
    bothAxes.SupportsReadout (id : WorkSpan -> WorkSpan) := by
  refine ⟨{
    run := fun
      | .work => WorkSpan.work
      | .span => WorkSpan.span
    agrees := ?_ }⟩
  intro policy state
  cases policy <;> rfl

/-- Work alone cannot support the two-policy family because equal work can
hide different span. -/
theorem workOnly_refuses_bothAxes :
    Not (bothAxes.SupportsReadout WorkSpan.work) := by
  apply bothAxes.not_supportsReadout_of_policy_collision WorkSpan.work
      (first := ⟨2, 1⟩) (second := ⟨2, 2⟩) rfl .span
  change (1 : Nat) ≠ 2
  decide

/-- The refusal is family-relative: work alone does support the family that
asks only for work. -/
def workAxis : PolicyFamily WorkSpan :=
  bothAxes.reindex (fun _ : Unit => Axis.work)

theorem workOnly_supports_workAxis :
    workAxis.SupportsReadout WorkSpan.work := by
  refine ⟨{
    run := fun _ observed => observed
    agrees := ?_ }⟩
  intro policy state
  rfl

end PolicyFamilyCanary

#print axioms PolicyFamily.supportsReadout_iff_vectorFactors
#print axioms PolicyFamily.vector_isLeastSufficient
#print axioms PolicyFamily.vector_refines_reindexedVector
#print axioms PolicyFamily.supportsReadout_reindex
#print axioms PolicyFamily.vector_eq_iff
#print axioms PolicyFamily.compatibleReadout_iff_vector_constantOnFibers
#print axioms PolicyFamily.supportsReadout_implies_compatible
#print axioms PolicyFamily.readoutRealizationOfSection
#print axioms PolicyFamily.supportsReadout_iff_compatible_of_section
#print axioms PolicyFamily.supportsReadout_iff_compatible
#print axioms PolicyFamily.not_supportsReadout_of_policy_collision
#print axioms PolicyFamily.supportsReadout_of_refinement
#print axioms PolicyFamilyCanary.identity_supports_bothAxes
#print axioms PolicyFamilyCanary.workOnly_refuses_bothAxes
#print axioms PolicyFamilyCanary.workOnly_supports_workAxis

end Mettapedia.GSLT.Core
