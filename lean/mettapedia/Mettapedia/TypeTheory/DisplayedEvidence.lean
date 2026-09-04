import Mathlib.Logic.Equiv.Defs

/-!
# Displayed exact evidence and gradual precision

An exact capability may be displayed over an unchanged raw value without
turning the raw language, propositions, or theoremhood into approximate
objects.  A status is suspended, carries exact evidence, or carries a local
refutation.  Precision fills a suspension but never changes the raw index.

The central characterization is observer-relative: an observation satisfies
the dynamic gradual guarantee exactly when it factors through the raw value.
Evidence-sensitive observations need not be gradual, and a negative control
shows that this distinction is real.

Exact evidence transports covariantly along constructional maps.  Refutations
do not: they transport only when the map also reflects exact evidence.
Without reflection, safe transport returns a refutation to suspension.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedEvidence

universe uRaw uExact uReason uRaw' uExact' uOutput

/-- An exact evidence family displayed over a raw carrier. -/
structure Family where
  Raw : Type uRaw
  Exact : Raw → Type uExact

/-- A proof-relevant reason why exact evidence is impossible at one raw
value. -/
structure Refutation (family : Family.{uRaw, uExact})
    (Reason : Type uReason) (raw : family.Raw) where
  reason : Reason
  refutes : family.Exact raw → False

/-- Live evidence at one fixed raw value. -/
inductive Status (family : Family.{uRaw, uExact})
    (Reason : Type uReason) (raw : family.Raw) where
  | suspended
  | established (evidence : family.Exact raw)
  | refuted (obstruction : Refutation family Reason raw)

namespace Status

variable {family : Family.{uRaw, uExact}} {Reason : Type uReason}
  {raw : family.Raw}

/-- `Refines precise coarse` means that `precise` contains at least the
information of `coarse`.  Exact evidence and refutation both refine a
suspension; neither silently refines the other. -/
inductive Refines : Status family Reason raw → Status family Reason raw → Prop
  | refl (status : Status family Reason raw) : Refines status status
  | established_suspended (evidence : family.Exact raw) :
      Refines (.established evidence) .suspended
  | refuted_suspended (obstruction : Refutation family Reason raw) :
      Refines (.refuted obstruction) .suspended

namespace Refines

theorem trans {first middle last : Status family Reason raw}
    (firstMiddle : Refines first middle)
    (middleLast : Refines middle last) : Refines first last := by
  cases firstMiddle with
  | refl => exact middleLast
  | established_suspended evidence =>
      cases middleLast with
      | refl => exact .established_suspended evidence
  | refuted_suspended obstruction =>
      cases middleLast with
      | refl => exact .refuted_suspended obstruction

/-- Every evidence state refines the same suspended raw state. -/
theorem toSuspended (status : Status family Reason raw) :
    Refines status .suspended := by
  cases status with
  | suspended => exact .refl _
  | established evidence => exact .established_suspended evidence
  | refuted obstruction => exact .refuted_suspended obstruction

/-- Established evidence is rigid in the precision order. -/
theorem established_rigid {precise : Status family Reason raw}
    {evidence : family.Exact raw}
    (precision : Refines precise (.established evidence)) :
    precise = .established evidence := by
  cases precision
  rfl

/-- A current refutation is rigid in the precision order. -/
theorem refuted_rigid {precise : Status family Reason raw}
    {obstruction : Refutation family Reason raw}
    (precision : Refines precise (.refuted obstruction)) :
    precise = .refuted obstruction := by
  cases precision
  rfl

/-- Exact evidence cannot refine a refutation at the same raw value. -/
theorem established_not_refines_refuted (evidence : family.Exact raw)
    (obstruction : Refutation family Reason raw) :
    ¬ Refines (.established evidence) (.refuted obstruction) := by
  intro precision
  cases precision

end Refines

/-! ## Observer-relative graduality -/

/-- An observation ignores gradual evidence exactly when it factors through
the underlying raw value. -/
def FactorsThroughRaw {Output : Type uOutput} (observe :
    ∀ raw : family.Raw, Status family Reason raw → Output) : Prop :=
  ∃ readRaw : family.Raw → Output,
    ∀ (raw : family.Raw) (status : Status family Reason raw),
      observe raw status = readRaw raw

/-- A type-valued observation is precision invariant when refinement cannot
change its result type. -/
def PrecisionInvariant {Output : Type uOutput} (observe :
    ∀ raw : family.Raw, Status family Reason raw → Output) : Prop :=
  ∀ (raw : family.Raw) {precise coarse : Status family Reason raw},
    Refines precise coarse → observe raw precise = observe raw coarse

/-- The dynamic gradual guarantee is exactly raw factorization.  This theorem
states both the positive rule and its boundary: evidence-sensitive observers
are outside the guarantee unless a separate invariance theorem is supplied. -/
theorem factorsThroughRaw_iff_precisionInvariant
    {Output : Type uOutput}
    (observe : ∀ raw : family.Raw, Status family Reason raw → Output) :
    FactorsThroughRaw observe ↔ PrecisionInvariant observe := by
  constructor
  · rintro ⟨readRaw, factors⟩ raw precise coarse _precision
    rw [factors raw precise, factors raw coarse]
  · intro invariant
    refine ⟨fun raw => observe raw .suspended, ?_⟩
    intro raw status
    exact invariant raw (Refines.toSuspended status)

end Status

/-! ## Constructional maps and the variance of refutation -/

/-- A constructional map transports raw values and exact evidence forward. -/
structure ExactMap (source : Family.{uRaw, uExact})
    (target : Family.{uRaw', uExact'}) where
  mapRaw : source.Raw → target.Raw
  mapExact : {raw : source.Raw} →
    source.Exact raw → target.Exact (mapRaw raw)

namespace ExactMap

variable {source : Family.{uRaw, uExact}}
  {target : Family.{uRaw', uExact'}}

/-- Reflection is the extra property required to transport negative
evidence in the same direction as an exact map. -/
structure ReflectsExact (map : ExactMap source target) where
  reflect : {raw : source.Raw} →
    target.Exact (map.mapRaw raw) → source.Exact raw

/-- Safe covariant transport preserves exact evidence and invalidates a
refutation to suspension. -/
def mapSafe (map : ExactMap source target) {Reason : Type uReason}
    {raw : source.Raw} :
    Status source Reason raw → Status target Reason (map.mapRaw raw)
  | .suspended => .suspended
  | .established evidence => .established (map.mapExact evidence)
  | .refuted _ => .suspended

/-- A reflecting exact map may transport refutation constructively. -/
def mapReflecting (map : ExactMap source target)
    (reflection : map.ReflectsExact) {Reason : Type uReason}
    {raw : source.Raw} :
    Status source Reason raw → Status target Reason (map.mapRaw raw)
  | .suspended => .suspended
  | .established evidence => .established (map.mapExact evidence)
  | .refuted obstruction => .refuted
      { reason := obstruction.reason
        refutes := fun targetEvidence =>
          obstruction.refutes (reflection.reflect targetEvidence) }

/-- Safe transport is monotone in precision. -/
theorem mapSafe_mono (map : ExactMap source target)
    {Reason : Type uReason} {raw : source.Raw}
    {precise coarse : Status source Reason raw}
    (precision : Status.Refines precise coarse) :
    Status.Refines (map.mapSafe precise) (map.mapSafe coarse) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      exact .established_suspended (map.mapExact evidence)
  | refuted_suspended obstruction => exact .refl _

/-- Reflecting transport is also monotone, while retaining refutations. -/
theorem mapReflecting_mono (map : ExactMap source target)
    (reflection : map.ReflectsExact)
    {Reason : Type uReason} {raw : source.Raw}
    {precise coarse : Status source Reason raw}
    (precision : Status.Refines precise coarse) :
    Status.Refines (map.mapReflecting reflection precise)
      (map.mapReflecting reflection coarse) := by
  cases precision with
  | refl => exact .refl _
  | established_suspended evidence =>
      exact .established_suspended (map.mapExact evidence)
  | refuted_suspended obstruction =>
      exact .refuted_suspended
        { reason := obstruction.reason
          refutes := fun targetEvidence =>
            obstruction.refutes (reflection.reflect targetEvidence) }

end ExactMap

/-! ## Positive and negative controls -/

namespace Canary

/-- A genuinely varying exact family: evidence is impossible at `false` and
inhabited at `true`. -/
def varying : Family where
  Raw := Bool
  Exact
    | false => PEmpty
    | true => PUnit

/-- The varying evidence family is not equivalent to one constant fibre. -/
theorem varying_not_constant :
    ¬ ∃ Uniform : Type,
      ∀ raw : varying.Raw, Nonempty ((varying.Exact raw) ≃ Uniform) := by
  rintro ⟨Uniform, uniform⟩
  obtain ⟨trueEquiv⟩ := uniform true
  obtain ⟨falseEquiv⟩ := uniform false
  have inhabitant : Uniform := trueEquiv.toFun PUnit.unit
  have impossible : PEmpty := by
    exact falseEquiv.symm.toFun inhabitant
  exact PEmpty.elim impossible

/-- A raw-indexed observation ignores evidence. -/
def rawObservation (raw : varying.Raw)
    (_status : Status varying Unit raw) : Bool := raw

theorem rawObservation_is_gradual :
    Status.PrecisionInvariant rawObservation := by
  rw [← Status.factorsThroughRaw_iff_precisionInvariant]
  exact ⟨id, fun _ _ => rfl⟩

/-- A small constant family used to show that evidence-sensitive observation
does not satisfy the gradual guarantee automatically. -/
def unitFamily : Family where
  Raw := Unit
  Exact := fun _ => Unit

def evidenceObservation (_raw : unitFamily.Raw) :
    Status unitFamily Unit () → Bool
  | .suspended => false
  | .established _ => true
  | .refuted _ => true

/-- Negative control: observing whether evidence is present does not factor
through raw semantics and changes along a precision refinement. -/
theorem evidenceObservation_not_gradual :
    ¬ Status.PrecisionInvariant evidenceObservation := by
  intro invariant
  have changed := invariant ()
    (Status.Refines.established_suspended (family := unitFamily)
      (Reason := Unit) ())
  simp [evidenceObservation] at changed

/-- An empty source family maps covariantly into an inhabited target family,
but cannot reflect exact evidence. -/
def emptyFamily : Family where
  Raw := Unit
  Exact := fun _ => Empty

def emptyToUnit : ExactMap emptyFamily unitFamily where
  mapRaw := id
  mapExact := fun impossible => nomatch impossible

def emptyRefutation : Refutation emptyFamily Unit () where
  reason := ()
  refutes := fun impossible => nomatch impossible

theorem safe_transport_invalidates_unreflected_refutation :
    emptyToUnit.mapSafe (.refuted emptyRefutation) =
      (Status.suspended : Status unitFamily Unit ()) :=
  rfl

/-- Negative evidence cannot be transported to the inhabited target: this is
why reflection is a real obligation rather than bookkeeping. -/
theorem target_refutation_impossible :
    ¬ Nonempty (Refutation unitFamily Unit ()) := by
  rintro ⟨obstruction⟩
  exact obstruction.refutes ()

end Canary

/-! ## Axiom audit -/

#print axioms Status.Refines.trans
#print axioms Status.factorsThroughRaw_iff_precisionInvariant
#print axioms ExactMap.mapSafe_mono
#print axioms ExactMap.mapReflecting_mono
#print axioms Canary.varying_not_constant
#print axioms Canary.rawObservation_is_gradual
#print axioms Canary.evidenceObservation_not_gradual
#print axioms Canary.target_refutation_impossible

end Mettapedia.TypeTheory.DisplayedEvidence
