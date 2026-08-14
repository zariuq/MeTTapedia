/-!
# Megalodon Mathdata proof kernel

This module gives a direct, executable Lean model of the typed terms and proof
terms checked by Megalodon's `Mathdata` kernel.  It deliberately stops before
document parsing and hash computation: theory primitives, signature terms,
definitions, and known propositions enter through an explicit finite
environment.

Normalization is fuel-bounded.  Exhausting fuel is rejection, matching the
fail-closed role of Megalodon's beta and term resource limits.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.MathdataKernel

abbrev Name := String

/-- Megalodon's polymorphic simple types. -/
inductive Tp where
  | var : Nat → Tp
  | prop : Tp
  | base : Nat → Tp
  | arr : Tp → Tp → Tp
  | all : Tp → Tp
deriving DecidableEq, Repr

/-- Megalodon's typed terms and propositions. -/
inductive Tm where
  | db : Nat → Tm
  | named : Name → Tm
  | prim : Nat → Tm
  | app : Tm → Tm → Tm
  | lam : Tp → Tm → Tm
  | imp : Tm → Tm → Tm
  | all : Tp → Tm → Tm
  | typeApp : Tm → Tp → Tm
  | typeLam : Tm → Tm
  | typeAll : Tm → Tm
deriving DecidableEq, Repr

/-- Megalodon's proof terms.  `gpa` is retained in the exact syntax but is not
accepted by the ordinary `extr_propofpf` kernel. -/
inductive Pf where
  | gpa : Name → Pf
  | hyp : Nat → Pf
  | known : Name → Pf
  | termApp : Pf → Tm → Pf
  | proofApp : Pf → Pf → Pf
  | proofLam : Tm → Pf → Pf
  | termLam : Tp → Pf → Pf
  | typeApp : Pf → Tp → Pf
  | typeLam : Pf → Pf
deriving DecidableEq, Repr

/-- One named term in a checked Megalodon signature. -/
structure TermDecl where
  name : Name
  type : Tp
  definition : Option Tm := none
deriving DecidableEq, Repr

/-- One named proposition in a checked Megalodon signature. -/
structure KnownDecl where
  name : Name
  proposition : Tm
deriving DecidableEq, Repr

/-- The finite authority needed by the Mathdata proof kernel. -/
structure Environment where
  primitives : List Tp := []
  terms : List TermDecl := []
  known : List KnownDecl := []
deriving DecidableEq, Repr

def lookupTermList? : List TermDecl → Name → Option TermDecl
  | [], _ => none
  | declaration :: declarations, name =>
      if declaration.name == name then some declaration
      else lookupTermList? declarations name

def lookupKnownList? : List KnownDecl → Name → Option Tm
  | [], _ => none
  | declaration :: declarations, name =>
      if declaration.name == name then some declaration.proposition
      else lookupKnownList? declarations name

def Environment.lookupTerm? (environment : Environment) (name : Name) :
    Option TermDecl :=
  lookupTermList? environment.terms name

def Environment.lookupKnown? (environment : Environment) (name : Name) :
    Option Tm :=
  lookupKnownList? environment.known name

namespace Tp

/-- Plain types exclude `all`; Megalodon admits `all` only as a prefix through
`check_ptp`. -/
def plainWellFormed (typeDepth : Nat) : Tp → Bool
  | .var index => decide (index < typeDepth)
  | .prop | .base _ => true
  | .arr domain codomain =>
      plainWellFormed typeDepth domain && plainWellFormed typeDepth codomain
  | .all _ => false

/-- Prefix-polymorphic type formation, corresponding to `check_ptp`. -/
def polyWellFormed (typeDepth : Nat) : Tp → Bool
  | .all body => polyWellFormed (typeDepth + 1) body
  | type => plainWellFormed typeDepth type

/-- Shift type variables at and above one cutoff. -/
def shift (cutoff amount : Nat) : Tp → Tp
  | .var index =>
      if index < cutoff then .var index else .var (index + amount)
  | .prop => .prop
  | .base index => .base index
  | .arr domain codomain =>
      .arr (shift cutoff amount domain) (shift cutoff amount codomain)
  | .all body => .all (shift (cutoff + 1) amount body)

/-- Instantiate one type-variable level, removing it from the result. -/
def instantiateAt (depth : Nat) (replacement : Tp) : Tp → Tp
  | .var index =>
      if index < depth then .var index
      else if index = depth then shift 0 depth replacement
      else .var (index - 1)
  | .prop => .prop
  | .base index => .base index
  | .arr domain codomain =>
      .arr (instantiateAt depth replacement domain)
        (instantiateAt depth replacement codomain)
  | .all body => .all (instantiateAt (depth + 1) replacement body)

def instantiate (replacement body : Tp) : Tp :=
  instantiateAt 0 replacement body

/-- Remove one unused type-variable level. -/
def dropAt? (cutoff : Nat) : Tp → Option Tp
  | .var index =>
      if index < cutoff then some (.var index)
      else if index = cutoff then none
      else some (.var (index - 1))
  | .prop => some .prop
  | .base index => some (.base index)
  | .arr domain codomain =>
      return .arr (← dropAt? cutoff domain) (← dropAt? cutoff codomain)
  | .all body => return .all (← dropAt? (cutoff + 1) body)

end Tp

namespace Tm

/-- Shift term variables at and above one cutoff. -/
def shift (cutoff amount : Nat) : Tm → Tm
  | .db index =>
      if index < cutoff then .db index else .db (index + amount)
  | .named name => .named name
  | .prim index => .prim index
  | .app function argument =>
      .app (shift cutoff amount function) (shift cutoff amount argument)
  | .lam type body => .lam type (shift (cutoff + 1) amount body)
  | .imp domain codomain =>
      .imp (shift cutoff amount domain) (shift cutoff amount codomain)
  | .all type body => .all type (shift (cutoff + 1) amount body)
  | .typeApp function type => .typeApp (shift cutoff amount function) type
  | .typeLam body => .typeLam (shift cutoff amount body)
  | .typeAll body => .typeAll (shift cutoff amount body)

/-- Shift type variables throughout a term. -/
def typeShift (cutoff amount : Nat) : Tm → Tm
  | .db index => .db index
  | .named name => .named name
  | .prim index => .prim index
  | .app function argument =>
      .app (typeShift cutoff amount function)
        (typeShift cutoff amount argument)
  | .lam type body =>
      .lam (Tp.shift cutoff amount type) (typeShift cutoff amount body)
  | .imp domain codomain =>
      .imp (typeShift cutoff amount domain)
        (typeShift cutoff amount codomain)
  | .all type body =>
      .all (Tp.shift cutoff amount type) (typeShift cutoff amount body)
  | .typeApp function type =>
      .typeApp (typeShift cutoff amount function)
        (Tp.shift cutoff amount type)
  | .typeLam body => .typeLam (typeShift (cutoff + 1) amount body)
  | .typeAll body => .typeAll (typeShift (cutoff + 1) amount body)

/-- Instantiate one type-variable level throughout a term. -/
def typeInstantiateAt (depth : Nat) (replacement : Tp) : Tm → Tm
  | .db index => .db index
  | .named name => .named name
  | .prim index => .prim index
  | .app function argument =>
      .app (typeInstantiateAt depth replacement function)
        (typeInstantiateAt depth replacement argument)
  | .lam type body =>
      .lam (Tp.instantiateAt depth replacement type)
        (typeInstantiateAt depth replacement body)
  | .imp domain codomain =>
      .imp (typeInstantiateAt depth replacement domain)
        (typeInstantiateAt depth replacement codomain)
  | .all type body =>
      .all (Tp.instantiateAt depth replacement type)
        (typeInstantiateAt depth replacement body)
  | .typeApp function type =>
      .typeApp (typeInstantiateAt depth replacement function)
        (Tp.instantiateAt depth replacement type)
  | .typeLam body =>
      .typeLam (typeInstantiateAt (depth + 1) replacement body)
  | .typeAll body =>
      .typeAll (typeInstantiateAt (depth + 1) replacement body)

def typeInstantiate (replacement : Tp) (body : Tm) : Tm :=
  typeInstantiateAt 0 replacement body

/-- Instantiate one term-variable level, removing it from the result. -/
def instantiateAt (depth : Nat) (replacement : Tm) : Tm → Tm
  | .db index =>
      if index < depth then .db index
      else if index = depth then shift 0 depth replacement
      else .db (index - 1)
  | .named name => .named name
  | .prim index => .prim index
  | .app function argument =>
      .app (instantiateAt depth replacement function)
        (instantiateAt depth replacement argument)
  | .lam type body => .lam type (instantiateAt (depth + 1) replacement body)
  | .imp domain codomain =>
      .imp (instantiateAt depth replacement domain)
        (instantiateAt depth replacement codomain)
  | .all type body => .all type (instantiateAt (depth + 1) replacement body)
  | .typeApp function type =>
      .typeApp (instantiateAt depth replacement function) type
  | .typeLam body => .typeLam (instantiateAt depth replacement body)
  | .typeAll body => .typeAll (instantiateAt depth replacement body)

def instantiate (replacement body : Tm) : Tm :=
  instantiateAt 0 replacement body

/-- Remove one unused term-variable level. -/
def dropAt? (cutoff : Nat) : Tm → Option Tm
  | .db index =>
      if index < cutoff then some (.db index)
      else if index = cutoff then none
      else some (.db (index - 1))
  | .named name => some (.named name)
  | .prim index => some (.prim index)
  | .app function argument =>
      return .app (← dropAt? cutoff function) (← dropAt? cutoff argument)
  | .lam type body => return .lam type (← dropAt? (cutoff + 1) body)
  | .imp domain codomain =>
      return .imp (← dropAt? cutoff domain) (← dropAt? cutoff codomain)
  | .all type body => return .all type (← dropAt? (cutoff + 1) body)
  | .typeApp function type => return .typeApp (← dropAt? cutoff function) type
  | .typeLam body => return .typeLam (← dropAt? cutoff body)
  | .typeAll body => return .typeAll (← dropAt? cutoff body)

/-- Remove one unused type-variable level throughout a term. -/
def typeDropAt? (cutoff : Nat) : Tm → Option Tm
  | .db index => some (.db index)
  | .named name => some (.named name)
  | .prim index => some (.prim index)
  | .app function argument =>
      return .app (← typeDropAt? cutoff function)
        (← typeDropAt? cutoff argument)
  | .lam type body =>
      return .lam (← Tp.dropAt? cutoff type) (← typeDropAt? cutoff body)
  | .imp domain codomain =>
      return .imp (← typeDropAt? cutoff domain)
        (← typeDropAt? cutoff codomain)
  | .all type body =>
      return .all (← Tp.dropAt? cutoff type) (← typeDropAt? cutoff body)
  | .typeApp function type =>
      return .typeApp (← typeDropAt? cutoff function)
        (← Tp.dropAt? cutoff type)
  | .typeLam body => return .typeLam (← typeDropAt? (cutoff + 1) body)
  | .typeAll body => return .typeAll (← typeDropAt? (cutoff + 1) body)

/-- One bottom-up beta/eta normalization pass.  The Boolean is true exactly
when the pass found no redex. -/
def normalizeOne : Tm → Tm × Bool
  | .app function argument =>
      let (functionResult, functionStable) := normalizeOne function
      let (argumentResult, argumentStable) := normalizeOne argument
      match functionResult with
      | .lam _ body =>
          (instantiate argumentResult body, false)
      | _ =>
          (.app functionResult argumentResult,
            functionStable && argumentStable)
  | .lam type body =>
      let (bodyResult, bodyStable) := normalizeOne body
      match bodyResult with
      | .app function (.db 0) =>
          match dropAt? 0 function with
          | some contracted => (contracted, false)
          | none => (.lam type bodyResult, bodyStable)
      | _ => (.lam type bodyResult, bodyStable)
  | .typeApp function type =>
      let (functionResult, functionStable) := normalizeOne function
      match functionResult with
      | .typeLam body => (typeInstantiate type body, false)
      | _ => (.typeApp functionResult type, functionStable)
  | .typeLam body =>
      let (bodyResult, bodyStable) := normalizeOne body
      match bodyResult with
      | .typeApp function (.var 0) =>
          match typeDropAt? 0 function with
          | some contracted => (contracted, false)
          | none => (.typeLam bodyResult, bodyStable)
      | _ => (.typeLam bodyResult, bodyStable)
  | .imp domain codomain =>
      let (domainResult, domainStable) := normalizeOne domain
      let (codomainResult, codomainStable) := normalizeOne codomain
      (.imp domainResult codomainResult, domainStable && codomainStable)
  | .all type body =>
      let (bodyResult, bodyStable) := normalizeOne body
      (.all type bodyResult, bodyStable)
  | .typeAll body =>
      let (bodyResult, bodyStable) := normalizeOne body
      (.typeAll bodyResult, bodyStable)
  | term => (term, true)

/-- Iterate beta/eta normalization.  A redex remaining when fuel reaches zero
is an explicit resource failure. -/
def normalize : Nat → Tm → Option Tm
  | 0, term =>
      let (result, stable) := normalizeOne term
      if stable then some result else none
  | fuel + 1, term =>
      let (result, stable) := normalizeOne term
      if stable then some result else normalize fuel result

end Tm

/-- Expand named definitions under a finite resource bound. -/
def deltaNormalize (environment : Environment) : Nat → Tm → Option Tm
  | 0, .named name =>
      match environment.lookupTerm? name with
      | some ⟨_, _, some _⟩ => none
      | _ => some (.named name)
  | fuel + 1, .named name =>
      match environment.lookupTerm? name with
      | some ⟨_, _, some definition⟩ =>
          deltaNormalize environment fuel definition
      | _ => some (.named name)
  | fuel, .app function argument =>
      return .app (← deltaNormalize environment fuel function)
        (← deltaNormalize environment fuel argument)
  | fuel, .lam type body =>
      return .lam type (← deltaNormalize environment fuel body)
  | fuel, .imp domain codomain =>
      return .imp (← deltaNormalize environment fuel domain)
        (← deltaNormalize environment fuel codomain)
  | fuel, .all type body =>
      return .all type (← deltaNormalize environment fuel body)
  | fuel, .typeApp function type =>
      return .typeApp (← deltaNormalize environment fuel function) type
  | fuel, .typeLam body =>
      return .typeLam (← deltaNormalize environment fuel body)
  | fuel, .typeAll body =>
      return .typeAll (← deltaNormalize environment fuel body)
  | _, term => some term

def normalize (environment : Environment) (fuel : Nat) (term : Tm) :
    Option Tm := do
  Tm.normalize fuel (← deltaNormalize environment fuel term)

/-- Synthesize the type of one term, corresponding to Megalodon's
`extr_tpoftm`. -/
def inferTerm (environment : Environment) :
    (typeDepth : Nat) → List Tp → Tm → Option Tp
  | _, termContext, .db index => termContext[index]?
  | _, _, .prim index => environment.primitives[index]?
  | _, _, .named name => (environment.lookupTerm? name).map TermDecl.type
  | typeDepth, termContext, .app function argument => do
      let .arr domain codomain ← inferTerm environment typeDepth termContext function
        | none
      let actual ← inferTerm environment typeDepth termContext argument
      if actual = domain then some codomain else none
  | typeDepth, termContext, .typeApp function type => do
      if !type.plainWellFormed typeDepth then none else
      let .all body ← inferTerm environment typeDepth termContext function | none
      some (Tp.instantiate type body)
  | typeDepth, termContext, .lam type body => do
      if !type.plainWellFormed typeDepth then none else
      return .arr type (← inferTerm environment typeDepth (type :: termContext) body)
  | typeDepth, termContext, .typeLam body => do
      let shiftedContext := termContext.map (Tp.shift 0 1)
      return .all (← inferTerm environment (typeDepth + 1) shiftedContext body)
  | typeDepth, termContext, .imp domain codomain => do
      if (← inferTerm environment typeDepth termContext domain) != .prop then none
      if (← inferTerm environment typeDepth termContext codomain) != .prop then none
      some .prop
  | typeDepth, termContext, .all type body => do
      if !type.plainWellFormed typeDepth then none else
      if (← inferTerm environment typeDepth (type :: termContext) body) != .prop then
        none
      some .prop
  | _, _, .typeAll _ => none

/-- Check a proposition, including Megalodon's prefix type-universal form. -/
def checkProposition (environment : Environment) :
    (typeDepth : Nat) → List Tp → Tm → Bool
  | typeDepth, _, .typeAll body =>
      checkProposition environment (typeDepth + 1) [] body
  | typeDepth, termContext, proposition =>
      inferTerm environment typeDepth termContext proposition = some .prop

/-- Synthesize the normalized proposition proved by a proof term. -/
def inferProof (environment : Environment) (fuel : Nat) :
    (typeDepth : Nat) → List Tp → List Tm → Pf → Option Tm
  | _, _, proofContext, .hyp index => proofContext[index]?
  | _, _, _, .gpa _ => none
  | _, _, _, .known name => do
      normalize environment fuel (← environment.lookupKnown? name)
  | typeDepth, termContext, proofContext, .termApp function argument => do
      let .all domain body ←
        inferProof environment fuel typeDepth termContext proofContext function
        | none
      let actual ← inferTerm environment typeDepth termContext argument
      if actual != domain then none else
      let normalizedArgument ← deltaNormalize environment fuel argument
      normalize environment fuel (Tm.instantiate normalizedArgument body)
  | typeDepth, termContext, proofContext, .proofApp function argument => do
      let .imp domain codomain ←
        inferProof environment fuel typeDepth termContext proofContext function
        | none
      let actual ←
        inferProof environment fuel typeDepth termContext proofContext argument
      if actual = domain then some codomain else none
  | typeDepth, termContext, proofContext, .termLam type body => do
      if !type.plainWellFormed typeDepth then none else
      let shiftedProofContext := proofContext.map (Tm.shift 0 1)
      return .all type
        (← inferProof environment fuel typeDepth (type :: termContext)
          shiftedProofContext body)
  | typeDepth, termContext, proofContext, .proofLam proposition body => do
      if !checkProposition environment typeDepth termContext proposition then none
      let normalized ← normalize environment fuel proposition
      return .imp normalized
        (← inferProof environment fuel typeDepth termContext
          (normalized :: proofContext) body)
  | typeDepth, termContext, proofContext, .typeApp function type => do
      let .typeAll body ←
        inferProof environment fuel typeDepth termContext proofContext function
        | none
      some (Tm.typeInstantiate type body)
  | typeDepth, termContext, proofContext, .typeLam body =>
      if termContext.isEmpty && proofContext.isEmpty then
        return .typeAll
          (← inferProof environment fuel (typeDepth + 1) [] [] body)
      else none

/-- Check against a proposition that is already in Megalodon's
beta-eta-delta normal form. -/
def checkNormalizedProof (environment : Environment) (fuel : Nat)
    (typeDepth : Nat) (termContext : List Tp) (proofContext : List Tm)
    (proof : Pf) (proposition : Tm) : Bool :=
  inferProof environment fuel typeDepth termContext proofContext proof =
    some proposition

/-- Check a proof against source-level proposition syntax.  Megalodon's
document checker normalizes the declared proposition before comparing it with
the proposition synthesized from the proof term; normalization failure is
therefore rejection. -/
def checkProof (environment : Environment) (fuel : Nat)
    (typeDepth : Nat) (termContext : List Tp) (proofContext : List Tm)
    (proof : Pf) (proposition : Tm) : Bool :=
  match normalize environment fuel proposition with
  | some normalized =>
      checkNormalizedProof environment fuel typeDepth termContext proofContext
        proof normalized
  | none => false

/-! ## Executable calibration against real Megalodon proof shapes -/

def forallIdentityEnvironment : Environment :=
  { terms :=
      [{ name := "p", type := .arr (.base 0) .prop }] }

def forallIdentityBody : Tm :=
  .app (.named "p") (.db 0)

def forallIdentityDomain : Tm :=
  .all (.base 0) forallIdentityBody

def forallIdentityGoal : Tm :=
  .imp forallIdentityDomain forallIdentityDomain

def forallIdentityProof : Pf :=
  .proofLam forallIdentityDomain
    (.termLam (.base 0) (.termApp (.hyp 0) (.db 0)))

example :
    inferProof forallIdentityEnvironment 16 0 [] [] forallIdentityProof =
      some forallIdentityGoal := by
  simp [inferProof, forallIdentityEnvironment, forallIdentityProof,
    forallIdentityGoal, forallIdentityDomain, forallIdentityBody,
    checkProposition, inferTerm, normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?, Tm.shift,
    Tm.instantiate, Tm.instantiateAt, Tp.plainWellFormed]

/-- A term of type `Prop` cannot instantiate the `set` quantifier. -/
def wrongTermApplication : Pf :=
  .proofLam forallIdentityDomain
    (.termApp (.hyp 0) (.named "p"))

example :
    inferProof forallIdentityEnvironment 16 0 [] [] wrongTermApplication =
      none := by
  simp [inferProof, forallIdentityEnvironment, wrongTermApplication,
    forallIdentityDomain, forallIdentityBody, checkProposition, inferTerm,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?, Tp.plainWellFormed]

/-- The type-polymorphic proof constructor is accepted only at empty term and
proof contexts, exactly as in `Mathdata.extr_propofpf`. -/
def polymorphicIdentityProof : Pf :=
  .typeLam (.proofLam (.named "q") (.hyp 0))

def polymorphicEnvironment : Environment :=
  { terms := [{ name := "q", type := .prop }] }

example :
    inferProof polymorphicEnvironment 16 0 [] [] polymorphicIdentityProof =
      some (.typeAll (.imp (.named "q") (.named "q"))) := by
  simp [inferProof, polymorphicEnvironment, polymorphicIdentityProof,
    checkProposition, inferTerm, normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?]

example :
    inferProof polymorphicEnvironment 16 0 [.prop] []
      polymorphicIdentityProof = none := by
  decide

/-! A second checked theorem may reuse a previously admitted polymorphic
proposition.  This is the smallest Mathdata specimen that exercises all three
of `Known`, proof-level type application, and proof-level term application. -/

def polymorphicReuseType : Tp := .arr (.var 0) .prop

def polymorphicReuseBody : Tm :=
  .all polymorphicReuseType
    (.imp
      (.all (.var 0) (.app (.db 1) (.db 0)))
      (.all (.var 0) (.app (.db 1) (.db 0))))

def polymorphicReuseGoal : Tm := .typeAll polymorphicReuseBody

def polymorphicReuseName : Name :=
  "f71ec9f41c53443ff77a8757c271db97e1353d99fa1f8e8c1c8537d5efd94cc5"

def polymorphicReuseEnvironment : Environment :=
  { known :=
      [{ name := polymorphicReuseName,
         proposition := polymorphicReuseGoal }] }

def polymorphicReuseProof : Pf :=
  .typeLam
    (.termLam polymorphicReuseType
      (.termApp
        (.typeApp (.known polymorphicReuseName) (.var 0))
        (.db 0)))

theorem polymorphic_known_reuse_accepted :
    inferProof polymorphicReuseEnvironment 16 0 [] []
        polymorphicReuseProof =
      some polymorphicReuseGoal := by
  simp [inferProof, polymorphicReuseEnvironment, polymorphicReuseProof,
    polymorphicReuseGoal, polymorphicReuseBody, polymorphicReuseType,
    polymorphicReuseName, Environment.lookupKnown?, lookupKnownList?,
    inferTerm, normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Tm.typeInstantiate, Tm.typeInstantiateAt, Tm.instantiate,
    Tm.instantiateAt, Tm.shift, Tp.instantiateAt,
    Tp.shift, Tp.plainWellFormed]

def polymorphicUnknownReuseProof : Pf :=
  .typeLam
    (.termLam polymorphicReuseType
      (.termApp
        (.typeApp (.known "not-an-admitted-proposition") (.var 0))
        (.db 0)))

theorem polymorphic_unknown_reuse_rejected :
    inferProof polymorphicReuseEnvironment 16 0 [] []
      polymorphicUnknownReuseProof = none := by
  simp [inferProof, polymorphicReuseEnvironment,
    polymorphicUnknownReuseProof, polymorphicReuseType,
    polymorphicReuseName, Environment.lookupKnown?, lookupKnownList?,
    inferTerm, Tp.plainWellFormed]

/-! A real source definition is retained in the environment and participates
in the final conversion check.  This mirrors the accepted Megalodon document
whose theorem states `idp p → p` and proves it by the identity proof. -/

def definitionConversionEnvironment : Environment :=
  { terms :=
      [{ name := "idp", type := .arr .prop .prop,
         definition := some (.lam .prop (.db 0)) },
       { name := "p", type := .prop }] }

def definitionConversionDomain : Tm :=
  .app (.named "idp") (.named "p")

def definitionConversionGoal : Tm :=
  .imp definitionConversionDomain (.named "p")

def definitionConversionProof : Pf :=
  .proofLam definitionConversionDomain (.hyp 0)

theorem definition_conversion_accepted :
    checkProof definitionConversionEnvironment 16 0 [] []
      definitionConversionProof definitionConversionGoal = true := by
  simp [checkProof, checkNormalizedProof, definitionConversionEnvironment,
    definitionConversionProof, definitionConversionGoal,
    definitionConversionDomain, inferProof, checkProposition, inferTerm,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?, Tm.instantiate,
    Tm.instantiateAt, Tm.shift]

/-- Merely declaring `idp` at the same type is insufficient: without its
definition, the source theorem is not convertible to the proposition proved
by the identity article. -/
def opaqueIdentityEnvironment : Environment :=
  { terms :=
      [{ name := "idp", type := .arr .prop .prop },
       { name := "p", type := .prop }] }

theorem opaque_identity_rejected :
    checkProof opaqueIdentityEnvironment 16 0 [] []
      definitionConversionProof definitionConversionGoal = false := by
  simp [checkProof, checkNormalizedProof, opaqueIdentityEnvironment,
    definitionConversionProof, definitionConversionGoal,
    definitionConversionDomain, inferProof, checkProposition, inferTerm,
    normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Environment.lookupTerm?, lookupTermList?]

/-- Ordinary term beta reduction is part of the checked conversion boundary. -/
example :
    Tm.normalize 4 (.app (.lam (.base 0) (.db 0)) (.named "x")) =
      some (.named "x") := by
  decide

/-- Type-level beta reduction uses the independent type-variable axis. -/
example :
    Tm.normalize 4
      (.typeApp (.typeLam (.all (.var 0) (.db 0))) (.base 0)) =
      some (.all (.base 0) (.db 0)) := by
  decide

end Mettapedia.Languages.Megalodon.MathdataKernel
