import Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticContextualCategory

/-!
# Lazy gradual evidence over dependent native capabilities

Prime's gradual boundary does not add an unknown constructor to kernel
conversion.  Instead, a raw judgment remains executable while an optional
displayed capability is suspended, established, or refuted.  This file gives
that arrangement its dependent structure.

An exact map always transports positive evidence.  Negative evidence is more
subtle: a refutation can move forward only when the map reflects exact
evidence.  Without reflection the safe transport deliberately returns to the
suspended state.  This is the cache-invalidation law needed by substitution
and language transport; it prevents a failure established for one dependent
fibre from being reused in another merely because their raw carriers map.

Demand uses the existing proof-relevant Need protocol.  The structures below
are an indexed view of its suspended/value/stable-fault states, not a second
evaluation protocol.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability

open CategoryTheory
open Mettapedia.GSLT.Dynamics
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.SyntacticContextual

universe uRaw uExact uKey uRetry uCell uRaw' uExact' uRawTwo uExactTwo
  uRevision uTy

/-! ## A capability displayed over unchanged raw semantics -/

/-- One exact native capability family displayed over a raw carrier.  The raw
value is not reconstructed from evidence and therefore remains available when
evidence is absent or invalidated. -/
structure Fibre where
  Raw : Type uRaw
  Exact : Raw -> Type uExact

/-- Stable blame is proof-relevant and local: it names a path and refutes the
exact capability for this particular raw value. -/
structure Refutation (fibre : Fibre.{uRaw, uExact}) (raw : fibre.Raw) where
  path : List Nat
  refutes : fibre.Exact raw -> False

/-- The three live gradual evidence states over one fixed raw value.  The raw
index is shared definitionally by all constructors. -/
inductive State (fibre : Fibre.{uRaw, uExact}) (raw : fibre.Raw) where
  | suspended
  | exact (evidence : fibre.Exact raw)
  | refuted (blame : Refutation fibre raw)

namespace Fibre

/-- Product of two displayed capabilities.  Its raw carrier is the ordinary
product, while exactness retains evidence for both components. -/
def product (left : Fibre.{uRaw, uExact})
    (right : Fibre.{uRaw', uExact'}) :
    Fibre.{max uRaw uRaw', max uExact uExact'} where
  Raw := left.Raw × right.Raw
  Exact := fun raw => left.Exact raw.1 × right.Exact raw.2

/-- Dependent sum of displayed capabilities.  The second raw carrier and its
exact evidence may depend on the first raw value. -/
def sigma (base : Fibre.{uRaw, uExact})
    (next : base.Raw -> Fibre.{uRaw', uExact'}) :
    Fibre.{max uRaw uRaw', max uExact uExact'} where
  Raw := Sigma fun raw => (next raw).Raw
  Exact := fun raw => base.Exact raw.1 × (next raw.1).Exact raw.2

end Fibre

namespace State

variable {fibre : Fibre.{uRaw, uExact}} {raw : fibre.Raw}

/-- Precision fills a suspension but never changes the underlying raw value.
Exact evidence and stable blame are rigid leaves of this flat evidence
domain. -/
inductive Refines : State fibre raw -> State fibre raw -> Prop where
  | refl (state : State fibre raw) : Refines state state
  | exact_suspended (evidence : fibre.Exact raw) :
      Refines (.exact evidence) .suspended
  | refuted_suspended (blame : Refutation fibre raw) :
      Refines (.refuted blame) .suspended

namespace Refines

theorem trans {first middle last : State fibre raw}
    (firstRefines : Refines first middle)
    (middleRefines : Refines middle last) : Refines first last := by
  cases firstRefines with
  | refl => exact middleRefines
  | exact_suspended evidence =>
      cases middleRefines with
      | refl => exact .exact_suspended evidence
  | refuted_suspended blame =>
      cases middleRefines with
      | refl => exact .refuted_suspended blame

/-- Exact evidence has no proper precision refinement. -/
theorem exact_rigid {refined : State fibre raw}
    {evidence : fibre.Exact raw}
    (precision : Refines refined (.exact evidence)) :
    refined = .exact evidence := by
  cases precision
  rfl

/-- Stable blame is likewise rigid until its cache identity changes. -/
theorem refuted_rigid {refined : State fibre raw}
    {blame : Refutation fibre raw}
    (precision : Refines refined (.refuted blame)) :
    refined = .refuted blame := by
  cases precision
  rfl

/-- Evidence and blame cannot refine one another inside one current fibre. -/
theorem exact_not_refines_refuted (evidence : fibre.Exact raw)
    (blame : Refutation fibre raw) :
    ¬ Refines (.exact evidence) (.refuted blame) := by
  intro precision
  cases precision

end Refines

/-! ## Constructional combination -/

/-- Combine two gradual capabilities.  Exact evidence is constructed only
when both components are exact.  Every other combination retains the raw
pair and suspends the optional product capability; component blame cannot be
promoted to blame for the product without an additional reflection law. -/
def combine {left : Fibre.{uRaw, uExact}}
    {right : Fibre.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw} :
    State left leftRaw -> State right rightRaw ->
      State (Fibre.product left right) (leftRaw, rightRaw)
  | .exact leftEvidence, .exact rightEvidence =>
      .exact (leftEvidence, rightEvidence)
  | _, _ => .suspended

theorem combine_left_mono {left : Fibre.{uRaw, uExact}}
    {right : Fibre.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw} {refined coarse : State left leftRaw}
    (precision : Refines refined coarse) (rightState : State right rightRaw) :
    Refines (combine refined rightState) (combine coarse rightState) := by
  cases precision with
  | refl => exact .refl _
  | exact_suspended evidence =>
      cases rightState with
      | exact rightEvidence =>
          show Refines
            (State.exact (fibre := Fibre.product left right)
              (raw := (leftRaw, rightRaw)) (evidence, rightEvidence))
            (State.suspended (fibre := Fibre.product left right)
              (raw := (leftRaw, rightRaw)))
          exact @Refines.exact_suspended (Fibre.product left right)
            (leftRaw, rightRaw) (evidence, rightEvidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases rightState <;> exact .refl _

theorem combine_right_mono {left : Fibre.{uRaw, uExact}}
    {right : Fibre.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw} (leftState : State left leftRaw)
    {refined coarse : State right rightRaw}
    (precision : Refines refined coarse) :
    Refines (combine leftState refined) (combine leftState coarse) := by
  cases precision with
  | refl => exact .refl _
  | exact_suspended evidence =>
      cases leftState with
      | exact leftEvidence =>
          show Refines
            (State.exact (fibre := Fibre.product left right)
              (raw := (leftRaw, rightRaw)) (leftEvidence, evidence))
            (State.suspended (fibre := Fibre.product left right)
              (raw := (leftRaw, rightRaw)))
          exact @Refines.exact_suspended (Fibre.product left right)
            (leftRaw, rightRaw) (leftEvidence, evidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases leftState <;> exact .refl _

/-- Product combination is monotone in both precision coordinates. -/
theorem combine_mono {left : Fibre.{uRaw, uExact}}
    {right : Fibre.{uRaw', uExact'}} {leftRaw : left.Raw}
    {rightRaw : right.Raw}
    {leftRefined leftCoarse : State left leftRaw}
    {rightRefined rightCoarse : State right rightRaw}
    (leftPrecision : Refines leftRefined leftCoarse)
    (rightPrecision : Refines rightRefined rightCoarse) :
    Refines (combine leftRefined rightRefined)
      (combine leftCoarse rightCoarse) :=
  Refines.trans
    (combine_left_mono leftPrecision rightRefined)
    (combine_right_mono leftCoarse rightPrecision)

/-- Dependent capability combination retains the dependency of the second
fibre on the unchanged first raw value. -/
def combineDependent {base : Fibre.{uRaw, uExact}}
    {next : base.Raw -> Fibre.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw} :
    State base baseRaw -> State (next baseRaw) nextRaw ->
      State (Fibre.sigma base next) ⟨baseRaw, nextRaw⟩
  | .exact baseEvidence, .exact nextEvidence =>
      .exact (baseEvidence, nextEvidence)
  | _, _ => .suspended

theorem combineDependent_left_mono {base : Fibre.{uRaw, uExact}}
    {next : base.Raw -> Fibre.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw}
    {refined coarse : State base baseRaw}
    (precision : Refines refined coarse)
    (nextState : State (next baseRaw) nextRaw) :
    Refines (combineDependent refined nextState)
      (combineDependent coarse nextState) := by
  cases precision with
  | refl => exact .refl _
  | exact_suspended evidence =>
      cases nextState with
      | exact nextEvidence =>
          show Refines
            (State.exact (fibre := Fibre.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩) (evidence, nextEvidence))
            (State.suspended (fibre := Fibre.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩))
          exact @Refines.exact_suspended (Fibre.sigma base next)
            ⟨baseRaw, nextRaw⟩ (evidence, nextEvidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases nextState <;> exact .refl _

theorem combineDependent_right_mono {base : Fibre.{uRaw, uExact}}
    {next : base.Raw -> Fibre.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw} (baseState : State base baseRaw)
    {refined coarse : State (next baseRaw) nextRaw}
    (precision : Refines refined coarse) :
    Refines (combineDependent baseState refined)
      (combineDependent baseState coarse) := by
  cases precision with
  | refl => exact .refl _
  | exact_suspended evidence =>
      cases baseState with
      | exact baseEvidence =>
          show Refines
            (State.exact (fibre := Fibre.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩) (baseEvidence, evidence))
            (State.suspended (fibre := Fibre.sigma base next)
              (raw := ⟨baseRaw, nextRaw⟩))
          exact @Refines.exact_suspended (Fibre.sigma base next)
            ⟨baseRaw, nextRaw⟩ (baseEvidence, evidence)
      | suspended => exact .refl _
      | refuted => exact .refl _
  | refuted_suspended =>
      cases baseState <;> exact .refl _

theorem combineDependent_mono {base : Fibre.{uRaw, uExact}}
    {next : base.Raw -> Fibre.{uRaw', uExact'}} {baseRaw : base.Raw}
    {nextRaw : (next baseRaw).Raw}
    {baseRefined baseCoarse : State base baseRaw}
    {nextRefined nextCoarse : State (next baseRaw) nextRaw}
    (basePrecision : Refines baseRefined baseCoarse)
    (nextPrecision : Refines nextRefined nextCoarse) :
    Refines (combineDependent baseRefined nextRefined)
      (combineDependent baseCoarse nextCoarse) :=
  Refines.trans
    (combineDependent_left_mono basePrecision nextRefined)
    (combineDependent_right_mono baseCoarse nextPrecision)

/-! ## Exact maps and the variance of blame -/

/-- A constructional map of native capabilities.  It maps raw semantics and
transports exact evidence; no reflection or blame transport is assumed. -/
structure ExactMap (source : Fibre.{uRaw, uExact})
    (target : Fibre.{uRaw', uExact'}) where
  mapRaw : source.Raw -> target.Raw
  mapExact : {raw : source.Raw} ->
    source.Exact raw -> target.Exact (mapRaw raw)

namespace ExactMap

/-- Exact maps compose in the same direction as constructional execution. -/
def comp {first : Fibre.{uRaw, uExact}}
    {second : Fibre.{uRaw', uExact'}}
    {third : Fibre.{uRawTwo, uExactTwo}}
    (later : ExactMap second third) (earlier : ExactMap first second) :
    ExactMap first third where
  mapRaw := fun raw => later.mapRaw (earlier.mapRaw raw)
  mapExact := fun evidence => later.mapExact (earlier.mapExact evidence)

/-- Identity transports both the raw value and exact evidence unchanged. -/
def id (fibre : Fibre.{uRaw, uExact}) : ExactMap fibre fibre where
  mapRaw := fun raw => raw
  mapExact := fun evidence => evidence

/-- Reflection is precisely the extra proof-relevant capability needed to
move a refutation forward. -/
structure ReflectsExact {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target) where
  reflect : {raw : source.Raw} ->
    target.Exact (map.mapRaw raw) -> source.Exact raw

def reflects_id (fibre : Fibre.{uRaw, uExact}) :
    (ExactMap.id fibre).ReflectsExact := by
  exact ⟨fun evidence => evidence⟩

def reflects_comp {first : Fibre.{uRaw, uExact}}
    {second : Fibre.{uRaw', uExact'}}
    {third : Fibre.{uRawTwo, uExactTwo}}
    {later : ExactMap second third} {earlier : ExactMap first second}
    (laterReflects : later.ReflectsExact)
    (earlierReflects : earlier.ReflectsExact) :
    (later.comp earlier).ReflectsExact := by
  exact ⟨fun evidence =>
    earlierReflects.reflect (laterReflects.reflect evidence)⟩

/-! ### Proof-relevant construction squares -/

/-- A commuting square of constructional capability maps.  Raw commutation
is stated as equality of the constructed values.  Exact commutation is
proof-relevant and therefore uses heterogeneous equality: before the raw
square is identified, the two pieces of exact evidence inhabit fibres over
propositionally equal rather than definitionally equal raw values. -/
structure Square {northWest : Fibre.{uRaw, uExact}}
    {northEast : Fibre.{uRaw', uExact'}}
    {southWest : Fibre.{uRawTwo, uExactTwo}}
    {southEast : Fibre.{uKey, uRetry}}
    (north : ExactMap northWest northEast)
    (west : ExactMap northWest southWest)
    (east : ExactMap northEast southEast)
    (south : ExactMap southWest southEast) where
  raw_commutes : ∀ raw,
    east.mapRaw (north.mapRaw raw) = south.mapRaw (west.mapRaw raw)
  exact_commutes : ∀ {raw} (evidence : northWest.Exact raw),
    HEq (east.mapExact (north.mapExact evidence))
      (south.mapExact (west.mapExact evidence))

end ExactMap

/-- Map a refutation through an exact-reflecting capability map. -/
def mapRefutation {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target)
    (reflects : map.ReflectsExact) {raw : source.Raw}
    (blame : Refutation source raw) :
    Refutation target (map.mapRaw raw) where
  path := blame.path
  refutes := fun evidence => blame.refutes (reflects.reflect evidence)

/-- Safe transport preserves exact evidence and invalidates negative evidence
when reflection has not been established. -/
def mapSafe {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target)
    {raw : source.Raw} : State source raw -> State target (map.mapRaw raw)
  | .suspended => .suspended
  | .exact evidence => .exact (map.mapExact evidence)
  | .refuted _ => .suspended

/-- A reflecting map transports every live state, including stable blame. -/
def mapFull {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target)
    (reflects : map.ReflectsExact) {raw : source.Raw} :
    State source raw -> State target (map.mapRaw raw)
  | .suspended => .suspended
  | .exact evidence => .exact (map.mapExact evidence)
  | .refuted blame => .refuted (mapRefutation map reflects blame)

namespace ExactMap.Square

private theorem suspended_heq_of_raw_eq
    {fibre : Fibre.{uRaw, uExact}} {leftRaw rightRaw : fibre.Raw}
    (rawEquality : leftRaw = rightRaw) :
    HEq (State.suspended : State fibre leftRaw)
      (State.suspended : State fibre rightRaw) := by
  subst rightRaw
  rfl

private theorem exact_heq_of_raw_eq_of_evidence_heq
    {fibre : Fibre.{uRaw, uExact}} {leftRaw rightRaw : fibre.Raw}
    {leftEvidence : fibre.Exact leftRaw}
    {rightEvidence : fibre.Exact rightRaw}
    (rawEquality : leftRaw = rightRaw)
    (evidenceEquality : HEq leftEvidence rightEvidence) :
    HEq (State.exact leftEvidence) (State.exact rightEvidence) := by
  subst rightRaw
  have equalEvidence : leftEvidence = rightEvidence := eq_of_heq evidenceEquality
  subst rightEvidence
  rfl

/-- A construction square commutes on all safely transported gradual states.
This includes suspended and refuted inputs: safe maps deliberately invalidate
blame unless reflection has separately been proved, so neither route can
smuggle a negative judgment into the target fibre. -/
theorem mapSafe_commutes {northWest : Fibre.{uRaw, uExact}}
    {northEast : Fibre.{uRaw', uExact'}}
    {southWest : Fibre.{uRawTwo, uExactTwo}}
    {southEast : Fibre.{uKey, uRetry}}
    {north : ExactMap northWest northEast}
    {west : ExactMap northWest southWest}
    {east : ExactMap northEast southEast}
    {south : ExactMap southWest southEast}
    (square : ExactMap.Square north west east south)
    {raw : northWest.Raw} (state : State northWest raw) :
    HEq (mapSafe east (mapSafe north state))
      (mapSafe south (mapSafe west state)) := by
  cases state with
  | suspended =>
      exact suspended_heq_of_raw_eq (square.raw_commutes raw)
  | refuted blame =>
      exact suspended_heq_of_raw_eq (square.raw_commutes raw)
  | exact evidence =>
      exact exact_heq_of_raw_eq_of_evidence_heq
        (square.raw_commutes raw) (square.exact_commutes evidence)

end ExactMap.Square

@[simp] theorem mapSafe_exact {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target)
    {raw : source.Raw} (evidence : source.Exact raw) :
    mapSafe map (.exact evidence) = .exact (map.mapExact evidence) :=
  rfl

@[simp] theorem mapSafe_refuted {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} (map : ExactMap source target)
    {raw : source.Raw} (blame : Refutation source raw) :
    mapSafe map (.refuted blame) = .suspended :=
  rfl

theorem Refines.mapSafe {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} {map : ExactMap source target}
    {raw : source.Raw} {refined coarse : State source raw}
    (precision : Refines refined coarse) :
    Refines (mapSafe map refined) (mapSafe map coarse) := by
  cases precision with
  | refl => exact .refl _
  | exact_suspended evidence => exact .exact_suspended (map.mapExact evidence)
  | refuted_suspended blame => exact .refl .suspended

theorem Refines.mapFull {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}} {map : ExactMap source target}
    (reflects : map.ReflectsExact)
    {raw : source.Raw} {refined coarse : State source raw}
    (precision : Refines refined coarse) :
    Refines (mapFull map reflects refined) (mapFull map reflects coarse) := by
  cases precision with
  | refl => exact .refl _
  | exact_suspended evidence => exact .exact_suspended (map.mapExact evidence)
  | refuted_suspended blame =>
      exact .refuted_suspended (mapRefutation map reflects blame)

/-! ## Demand through the existing Need protocol -/

/-- A dependent check result is indexed by the exact raw value it decided. -/
inductive Decision (fibre : Fibre.{uRaw, uExact}) (Retry : Type uRetry)
    (raw : fibre.Raw) where
  | exact (evidence : fibre.Exact raw)
  | refuted (blame : Refutation fibre raw)
  | retry (reason : Retry)

/-- A boundary checker decides a displayed capability for each raw value. -/
structure Checker (fibre : Fibre.{uRaw, uExact}) (Retry : Type uRetry) where
  check : (raw : fibre.Raw) -> Decision fibre Retry raw

structure EvidenceBundle (fibre : Fibre.{uRaw, uExact}) where
  raw : fibre.Raw
  evidence : fibre.Exact raw

abbrev BlameBundle (fibre : Fibre.{uRaw, uExact}) :=
  Sigma (Refutation fibre)

abbrev RetryBundle (fibre : Fibre.{uRaw, uExact}) (Retry : Type uRetry) :=
  fibre.Raw × Retry

/-- Forget the dependent result into the existing uniform Need outcome.  The
raw index is retained in every payload. -/
def Checker.toNeedChecker {fibre : Fibre.{uRaw, uExact}}
    {Retry : Type uRetry} (checker : Checker fibre Retry) :
    GradualExecutionPlan.Checker fibre.Raw (EvidenceBundle fibre)
      (BlameBundle fibre) (RetryBundle fibre Retry) where
  check raw :=
    match checker.check raw with
    | .exact evidence => .value ⟨raw, evidence⟩
    | .refuted blame => .stableFault ⟨raw, blame⟩
    | .retry reason => .retryableFault (raw, reason)

/-- The dependent view of the state produced by one demand. -/
def Checker.demandState {fibre : Fibre.{uRaw, uExact}}
    {Retry : Type uRetry} (checker : Checker fibre Retry)
    (raw : fibre.Raw) : State fibre raw :=
  match checker.check raw with
  | .exact evidence => .exact evidence
  | .refuted blame => .refuted blame
  | .retry _ => .suspended

theorem Checker.demandState_refines_suspended
    {fibre : Fibre.{uRaw, uExact}} {Retry : Type uRetry}
    (checker : Checker fibre Retry) (raw : fibre.Raw) :
    Refines (checker.demandState raw) (.suspended : State fibre raw) := by
  unfold Checker.demandState
  split
  · exact .exact_suspended _
  · exact .refuted_suspended _
  · exact .refl _

/-- A checked dependent capability is an ordinary checked plan whose raw
term and obligation are the same indexed value. -/
def checkedPlan {fibre : Fibre.{uRaw, uExact}} {Key : Type uKey}
    (key : Key) (raw : fibre.Raw) :
    CheckedPlan fibre.Raw Key fibre.Raw where
  term := raw
  origin := ⟨key, raw⟩

@[simp] theorem checkedPlan_runs_raw {fibre : Fibre.{uRaw, uExact}}
    {Key : Type uKey} {Ty : Type uTy}
    {HasType : fibre.Raw -> Ty -> Prop} (key : Key) (raw : fibre.Raw) :
    (Plan.checked (Ty := Ty) (HasType := HasType)
      (checkedPlan (fibre := fibre) key raw)).run id = raw :=
  rfl

/-- The uniform Need target produced by demand is exactly the bundled form of
the dependent demand state. -/
theorem demandCheck_target_eq
    {fibre : Fibre.{uRaw, uExact}} {Key : Type uKey}
    {Retry : Type uRetry} (checker : Checker fibre Retry)
    (key : Key) (raw : fibre.Raw) (cell : Cell) :
    ((checkedPlan (fibre := fibre) key raw).demandCheck
      checker.toNeedChecker cell).1 =
      match checker.demandState raw with
      | .suspended => .suspended (CheckOrigin.mk key raw)
      | .exact evidence =>
          .cachedValue (CheckOrigin.mk key raw) ⟨raw, evidence⟩
      | .refuted blame =>
          .cachedStableFault (CheckOrigin.mk key raw) ⟨raw, blame⟩ := by
  cases outcome : checker.check raw <;>
    simp [CheckedPlan.demandCheck, Checker.toNeedChecker,
      Checker.demandState, checkedPlan, outcome]

/-- Demand performs exactly one evaluation in the established Need model. -/
theorem demandCheck_evaluationCount
    {fibre : Fibre.{uRaw, uExact}} {Key : Type uKey}
    {Retry : Type uRetry} (checker : Checker fibre Retry)
    (key : Key) (raw : fibre.Raw) (cell : Cell) :
    ((checkedPlan (fibre := fibre) key raw).demandCheck
      checker.toNeedChecker cell).2.evaluationCount = 1 :=
  CheckedPlan.demandCheck_evaluationCount _ _ _

/-! ## Revision invalidation -/

/-- Forget all cached capability evidence while retaining the raw index. -/
def invalidate (_state : State fibre raw) : State fibre raw := .suspended

theorem refines_invalidate (state : State fibre raw) :
    Refines state state.invalidate := by
  cases state with
  | suspended => exact .refl _
  | exact evidence => exact .exact_suspended evidence
  | refuted blame => exact .refuted_suspended blame

/-- A cached state is active only at its exact revision. -/
def activateAt {Revision : Type uRevision} [DecidableEq Revision]
    (cached current : Revision) (state : State fibre raw) : State fibre raw :=
  if cached = current then state else state.invalidate

@[simp] theorem activateAt_current {Revision : Type uRevision}
    [DecidableEq Revision]
    (revision : Revision) (state : State fibre raw) :
    state.activateAt revision revision = state := by
  simp [activateAt]

theorem activateAt_stale {Revision : Type uRevision} [DecidableEq Revision]
    {cached current : Revision} (stale : cached ≠ current)
    (state : State fibre raw) :
    state.activateAt cached current = .suspended := by
  simp [activateAt, stale, invalidate]

/-! ## Formed Prime judgments as a dependent instance -/

namespace FormedJudgment

/-- A raw formed-judgment candidate retains its proposed type and term but no
typing evidence. -/
structure Raw {rules : Rules Head} (context : FormedContext rules) where
  type : TypeOver context
  term : Tm Head context.arity

/-- Exact evidence is the existing declaration-aware typing judgment. -/
def judgmentFibre {rules : Rules Head}
    (context : FormedContext rules) : Fibre where
  Raw := Raw context
  Exact := fun candidate =>
    PLift (HasType rules context.context candidate.term candidate.type.code)

/-- Typed context substitution is a constructional exact map. -/
def reindexMap {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target) :
    ExactMap (judgmentFibre target) (judgmentFibre source) where
  mapRaw := fun candidate =>
    { type := candidate.type.reindex morphism
      term := subst morphism.substitution candidate.term }
  mapExact := fun evidence => ⟨by
    change HasType rules source.context
      (subst morphism.substitution _)
      (subst morphism.substitution _)
    exact evidence.down.substitute morphism.typed⟩

/-- Substitution transports positive typing evidence without invoking a
checker. -/
@[simp] theorem reindex_exact {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target)
    (candidate : Raw target)
    (evidence : (judgmentFibre target).Exact candidate) :
    mapSafe (reindexMap morphism) (.exact evidence) =
      .exact ((reindexMap morphism).mapExact evidence) :=
  rfl

/-- In the absence of a reflection theorem, a cached source-context
refutation is invalidated by substitution. -/
@[simp] theorem reindex_refuted_invalidates {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target)
    (candidate : Raw target)
    (blame : Refutation (judgmentFibre target) candidate) :
    mapSafe (reindexMap morphism) (.refuted blame) = .suspended :=
  rfl

/-- If a particular substitution reflects typing on the named candidate,
stable blame can be transported as well. -/
def reindexFull {rules : Rules Head}
    {source target : FormedContext rules} (morphism : source ⟶ target)
    (reflects : (reindexMap morphism).ReflectsExact)
    {candidate : Raw target} :
    State (judgmentFibre target) candidate ->
      State (judgmentFibre source) ((reindexMap morphism).mapRaw candidate) :=
  mapFull (reindexMap morphism) reflects

end FormedJudgment

/-! ## Positive and negative controls -/

namespace Canary

/-- A small source fibre with one supported and one unsupported raw value. -/
def source : Fibre where
  Raw := Bool
  Exact := fun value => PLift (value = true)

/-- The target forgets the source distinction and accepts its sole value. -/
def target : Fibre where
  Raw := PUnit
  Exact := fun _ => PUnit

def collapse : ExactMap source target where
  mapRaw := fun _ => PUnit.unit
  mapExact := fun _ => PUnit.unit

def supported : State source true := .exact ⟨rfl⟩

theorem supported_maps_exact :
    mapSafe collapse supported = .exact PUnit.unit :=
  rfl

def unsupportedBlame : Refutation source false where
  path := [0]
  refutes := by
    intro impossible
    exact Bool.false_ne_true impossible.down

/-- Negative evidence is invalidated rather than smuggled through a
non-reflecting collapse. -/
theorem unsupported_blame_invalidates :
    mapSafe collapse (.refuted unsupportedBlame) = .suspended :=
  rfl

/-- The collapse really does not reflect exact evidence: its target accepts
the image of the unsupported source point. -/
theorem collapse_not_reflects : ¬ Nonempty collapse.ReflectsExact := by
  rintro ⟨reflects⟩
  have impossible : PLift (false = true) :=
    reflects.reflect (raw := false) PUnit.unit
  exact Bool.false_ne_true impossible.down

theorem stale_supported_falls_back :
    supported.activateAt (0 : Nat) 1 = .suspended := by
  exact activateAt_stale (by decide) supported

theorem current_supported_remains_exact :
    supported.activateAt (1 : Nat) 1 = supported :=
  activateAt_current 1 supported

end Canary

#print axioms State.Refines.trans
#print axioms State.Refines.exact_rigid
#print axioms State.combine_mono
#print axioms State.combineDependent_mono
#print axioms State.Refines.mapSafe
#print axioms State.Refines.mapFull
#print axioms ExactMap.Square.mapSafe_commutes
#print axioms Checker.demandState_refines_suspended
#print axioms demandCheck_target_eq
#print axioms demandCheck_evaluationCount
#print axioms FormedJudgment.reindex_exact
#print axioms FormedJudgment.reindex_refuted_invalidates
#print axioms Canary.collapse_not_reflects

end State

end Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
