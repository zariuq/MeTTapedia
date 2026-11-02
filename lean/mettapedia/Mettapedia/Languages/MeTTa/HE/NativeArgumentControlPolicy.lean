import Mettapedia.Languages.MeTTa.HE.NativeArgumentProjection

/-!
# Profile-explicit demand for the native argument controller

The branches follow the native argument frame's ENTER phase. Classification
of operation positions, dependent domains, Need references and callable values
is supplied at a named service boundary. These flags are not a claim that the
native classifiers implement the corresponding independent semantics.

HE Atom demand, PeTTa's eager callables and already-held variable values,
the Prime draft's held `Atom` and `(Data T)` and its evaluated top type `Proc`,
normalization, control continuations and error-as-data are kept distinct. No
profile silently imports another.

Prime spells holding with one marker: a parameter declared `Atom`, or with the
`Data` modifier, receives its argument as written; a parameter declared `Proc`,
the top type, receives the argument's value. Until 2026-10-29 the Prime draft
spelled these `Data` and `Atom`, and held an `Atom` parameter only for grounded
operations and for library declarations written in HE; that convention is
gone, and holding no longer depends on who wrote the declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentControlPolicy

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Dialect where
  | he | petta | prime
  deriving Repr, DecidableEq

structure Policy where
  dialect : Dialect
  normalize : Bool := false
  controlContinuation : Bool := false
  explicitData : Bool := false
  dataDomain : Bool := false
  eagerCallable : Bool := false
  observableReference : Bool := false
  errorAsData : Bool := false
  dependentTelescope : Bool := false
  deriving Repr, DecidableEq

inductive EvaluationMode where
  | normalForm | untyped | heTypedInEnvironment | typed
  deriving Repr, DecidableEq

/-- Prime's top type `Proc`: a parameter of this type receives its argument's value. -/
def procType : Atom := .symbol "Proc"

def Policy.atomRaw (policy : Policy) (domain : Atom) : Bool :=
  domain == Atom.atomType &&
    !(decide (policy.dialect = .petta) && policy.eagerCallable)

def Policy.boundValue (policy : Policy) (original bound : Atom) : Bool :=
  decide (policy.dialect = .petta) && original.isVariable && !bound.isVariable

def Policy.raw (policy : Policy) (original domain bound : Atom) : Bool :=
  !policy.normalize && (policy.explicitData || policy.dataDomain || policy.atomRaw domain ||
    policy.boundValue original bound || bound.isVariable)

/-- Independent demand alternatives; the source variable and substituted
value play different roles in HE and PeTTa. -/
inductive RawRel (policy : Policy) (original domain bound : Atom) : Prop where
  | explicit : policy.normalize = false → policy.explicitData = true → RawRel policy original domain bound
  | data : policy.normalize = false → policy.dataDomain = true → RawRel policy original domain bound
  | atom : policy.normalize = false → domain = Atom.atomType →
      (policy.dialect ≠ .petta ∨ policy.eagerCallable = false) → RawRel policy original domain bound
  | held : policy.normalize = false → policy.dialect = .petta →
      original.isVariable = true → bound.isVariable = false → RawRel policy original domain bound
  | unbound : policy.normalize = false → bound.isVariable = true → RawRel policy original domain bound

theorem atomRaw_iff (policy : Policy) (domain : Atom) : policy.atomRaw domain = true ↔
    domain = Atom.atomType ∧ (policy.dialect ≠ .petta ∨ policy.eagerCallable = false) := by
  simp only [Policy.atomRaw, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_iff_eq]

theorem raw_iff (policy : Policy) (original domain bound : Atom) :
    policy.raw original domain bound = true ↔ RawRel policy original domain bound := by
  simp only [Policy.raw, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true,
    atomRaw_iff, Policy.boundValue, decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨normalized, (((explicit | data) | atom) | held) | unbound⟩
    · exact .explicit normalized explicit
    · exact .data normalized data
    · exact .atom normalized atom.1 atom.2
    · exact .held normalized held.1.1 held.1.2 held.2
    · exact .unbound normalized unbound
  · intro raw
    cases raw with
    | explicit normalized explicit => exact ⟨normalized, Or.inl (Or.inl (Or.inl (Or.inl explicit)))⟩
    | data normalized data => exact ⟨normalized, Or.inl (Or.inl (Or.inl (Or.inr data)))⟩
    | atom normalized atom nonEager => exact ⟨normalized, Or.inl (Or.inl (Or.inr ⟨atom, nonEager⟩))⟩
    | held normalized dialect original bound => exact ⟨normalized, Or.inl (Or.inr ⟨⟨dialect, original⟩, bound⟩)⟩
    | unbound normalized unbound => exact ⟨normalized, Or.inr unbound⟩

def Policy.mode (policy : Policy) (domain : Atom) : EvaluationMode :=
  if policy.normalize then .normalForm
  else if (domain == Atom.atomType && decide (policy.dialect = .petta) && policy.eagerCallable) ||
      (domain == procType && decide (policy.dialect = .prime)) then .untyped
  else if policy.dialect = .he then .heTypedInEnvironment else .typed

def Policy.reify (policy : Policy) (domain : Atom) : Bool :=
  !policy.controlContinuation && (policy.dataDomain || domain == Atom.atomType) &&
    policy.observableReference

def Policy.transform (policy : Policy) (domain : Atom) : Bool :=
  policy.reify domain || policy.dataDomain

theorem ordinary_he_raw (original domain bound : Atom) (explicitData : Bool) :
    ({dialect := .he, explicitData := explicitData} : Policy).raw original domain bound =
      NativeArgumentProjection.rawDemand false explicitData domain bound := by
  simp [Policy.raw, Policy.atomRaw, Policy.boundValue, NativeArgumentProjection.rawDemand]

def boolData (value : Bool) : Atom := .symbol (if value then "True" else "False")

def readBool : Atom → Option Bool
  | .symbol "True" => some true
  | .symbol "False" => some false
  | _ => none

@[simp] theorem readBool_boolData (value : Bool) : readBool (boolData value) = some value := by
  cases value <;> rfl

def dialectData : Dialect → Atom
  | .he => .symbol "he"
  | .petta => .symbol "petta"
  | .prime => .symbol "prime"

def readDialect : Atom → Option Dialect
  | .symbol "he" => some .he
  | .symbol "petta" => some .petta
  | .symbol "prime" => some .prime
  | _ => none

@[simp] theorem readDialect_dialectData (dialect : Dialect) :
    readDialect (dialectData dialect) = some dialect := by cases dialect <;> rfl

def policyData (policy : Policy) : Atom :=
  .expression [.symbol "he-native-argument-policy-v2", dialectData policy.dialect,
    boolData policy.normalize, boolData policy.controlContinuation, boolData policy.explicitData,
    boolData policy.dataDomain, boolData policy.eagerCallable,
    boolData policy.observableReference, boolData policy.errorAsData, boolData policy.dependentTelescope]

def readPolicy : Atom → Option Policy
  | .expression [.symbol "he-native-argument-policy-v2", dialect,
      normalized, control, explicit, data, eager, observable, errors, telescope] => do
      return ⟨← readDialect dialect, ← readBool normalized, ← readBool control,
        ← readBool explicit, ← readBool data, ← readBool eager,
        ← readBool observable, ← readBool errors, ← readBool telescope⟩
  | _ => none

@[simp] theorem readPolicy_policyData (policy : Policy) : readPolicy (policyData policy) = some policy := by
  cases policy
  simp [policyData, readPolicy]

theorem policyData_injective : Function.Injective policyData := by
  intro left right equal
  have decoded := congrArg readPolicy equal
  simpa using decoded

end Mettapedia.Languages.MeTTa.HE.NativeArgumentControlPolicy
