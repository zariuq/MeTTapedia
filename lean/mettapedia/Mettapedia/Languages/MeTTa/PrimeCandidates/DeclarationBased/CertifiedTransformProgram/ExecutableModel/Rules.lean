import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Confluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DeclaredComputations

/-!
# The executable package of the certified-transform program

The part of the program whose runs the runtime executes, as one rule package
for the normalization model: the natural numbers `num` with `zero`, `suc` and
the recursor `num-rec`; the sets `set` with `Power`; addition and the iterated
power set by structural recursion; identity elimination with its linear rule;
the definitions `eqAt`, `sucMove`, `keepCert`, `transportCert`,
`composeCert`, `returnIter` and `sucStep`; and the iterator `iterCert` by
structural recursion. Declared types and equations are those of the program.
The native proof family and the constants typed by it are not part of this
package.

Every constant with computation contributes one root computation, and the
package computes by their union. The stages of the package, in which the
declared types and right-hand sides are typed, restrict one table of
declarations and computations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality.Normalization
open TelescopeAbstraction (closeType applyClosed)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName U0 numT jType numRecType eqAtType sucMoveType keepType
  transportType composeType iterType returnIterType sucStepType stepFamily familyTelescope
  eqAtTelescope transportTelescope composeTelescope iterTelescope returnIterResult)

/-- The fields of a constructor. -/
abbrev CtorField := Presentation.TypedEquality.Normalization.Field Tower.Head

/-! ## Names -/

abbrev numN : DeclName := SetProfile.baseName .num
abbrev setN : DeclName := SetProfile.baseName .set
abbrev zeroN : DeclName := SetProfile.constantName .zero
abbrev sucN : DeclName := SetProfile.constantName .suc
abbrev addN : DeclName := SetProfile.constantName .add
abbrev powerN : DeclName := SetProfile.constantName .power
abbrev powN : DeclName := SetProfile.constantName .pow

/-- The constructors of `num`. -/
def ctors : List (DeclName × List CtorField) := [(zeroN, []), (sucN, [.recursive])]

/-! ## Declared types and equations -/

section Terms

variable {n : Nat}

abbrev setT : Tower.Tm n := .const setN

end Terms

def addType : Tower.Tm 0 := .pi numT (.pi numT numT)
def powerType : Tower.Tm 0 := .pi setT setT
def powType : Tower.Tm 0 := .pi numT (.pi setT setT)

/-- The telescope of addition: two numbers. -/
def addEntries : (i : Nat) → Tower.Tm i := fun _ => numT

/-- The telescope of the iterated power set: a number, then a set. -/
def powEntries : (i : Nat) → Tower.Tm i
  | 0 => numT
  | _ + 1 => setT

/-- The telescope of the iterator: the count, the carrier, the family, the
step, the value and its evidence. -/
def iterEntries : (i : Nat) → Tower.Tm i
  | 0 => numT
  | 1 => U0
  | 2 => .pi (.var 0) U0
  | 3 => stepFamily
  | 4 => .var 2
  | 5 => .app (.var 2) (.var 0)
  | _ + 6 => U0

/-- The iterator's result type. -/
def iterResult : Tower.Tm 6 := .sigma (.var 4) (.app (.var 4) (.var 0))

/-- The right-hand sides of addition, the recursive call abstracted:
`add n zero = n` and `add n (suc m) = suc h`. -/
def addBody : (k : DeclName) → (fields : List CtorField) →
    Tower.Tm (1 + fields.length + 0 + (recPositions fields).length)
  | _, [] => (.var 0 : Tower.Tm 1)
  | _, [.recursive] => (.app (.const sucN) (.var 0) : Tower.Tm 3)
  | _, _ => .const addN

/-- The right-hand sides of the iterated power set: `pow zero X = X` and
`pow (suc n) X = Power (h X)`. -/
def powBody : (k : DeclName) → (fields : List CtorField) →
    Tower.Tm (0 + fields.length + 1 + (recPositions fields).length)
  | _, [] => (.var 0 : Tower.Tm 1)
  | _, [.recursive] => (.app (.const powerN) (.app (.var 0) (.var 1)) : Tower.Tm 3)
  | _, _ => .const powN

/-- The right-hand sides of the iterator: the pair at zero, and at a successor
one shared use of the step, then the recursive call `h A P step`. -/
def iterBody : (k : DeclName) → (fields : List CtorField) →
    Tower.Tm (0 + fields.length + 5 + (recPositions fields).length)
  | _, [] => (.pair (.var 1) (.var 0) : Tower.Tm 5)
  | _, [.recursive] =>
      (CertifiedTransforms.shared (.var 3) (.app (.app (.app (.var 0) (.var 5)) (.var 4)) (.var 3))
        (.var 2) (.var 1) : Tower.Tm 7)
  | _, _ => .const iterName

/-- The telescopes and right-hand sides of the definitions by one equation. -/
abbrev eqAtTele : Tower.Ctx 1 := .snoc .nil numT
abbrev keepTele : Tower.Ctx 4 := .snoc (.snoc familyTelescope (.var 1)) (.app (.var 1) (.var 0))
abbrev returnIterTele : Tower.Ctx 1 := .snoc .nil U0

def eqAtRhs : Tower.Tm 1 := Package.eqAtEquation.2.2
def sucMoveRhs : Tower.Tm 2 := Package.sucMoveEquation.2.2
def keepRhs : Tower.Tm 4 := Package.keepEquation.2.2
def transportRhs : Tower.Tm 6 := Package.transportEquation.2.2
def composeRhs : Tower.Tm 6 := Package.composeEquation.2.2
def returnIterRhs : Tower.Tm 1 := Package.returnIterEquation.2.2
def sucStepRhs : Tower.Tm 2 := Package.sucStepEquation.2.2

/-! ## The table -/

/-- Every declaration of the package, with its declared type. -/
def declarations : List (DeclName × Tower.Tm 0) :=
  [(numN, U0), (setN, U0), (zeroN, numT), (sucN, .pi numT numT), (addN, addType),
   (powerN, powerType), (powN, powType), (numRecName, numRecType), (jName, jType),
   (eqAtName, eqAtType), (sucMoveName, sucMoveType), (keepName, keepType),
   (transportName, transportType), (composeName, composeType), (iterName, iterType),
   (returnIterName, returnIterType), (sucStepName, sucStepType)]

/-- The declared type of a name. -/
def allTypes (name : DeclName) : Option (Tower.Tm 0) := declarations.lookup name

/-- The root computation of each constant with computation. -/
def computations : List (DeclName × RootComputation Tower.Head) :=
  [(numRecName, iotaComputation numRecName ctors),
   (addN, recursionComputation addN ctors addEntries 1 0 addBody),
   (powN, recursionComputation powN ctors powEntries 0 1 powBody),
   (jName, eliminatorComputation jName),
   (eqAtName, definitionComputation eqAtName eqAtTele eqAtRhs),
   (sucMoveName, definitionComputation sucMoveName eqAtTelescope sucMoveRhs),
   (keepName, definitionComputation keepName keepTele keepRhs),
   (transportName, definitionComputation transportName transportTelescope transportRhs),
   (composeName, definitionComputation composeName composeTelescope composeRhs),
   (iterName, recursionComputation iterName ctors iterEntries 0 5 iterBody),
   (returnIterName, definitionComputation returnIterName returnIterTele returnIterRhs),
   (sucStepName, definitionComputation sucStepName eqAtTelescope sucStepRhs)]

/-- The stage of the package with the allowed names: their declarations and
their computations. -/
def stage (allowed : DeclName → Bool) : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name => if allowed name then allTypes name else none
    computation := RootComputation.unionAll (computations.filter fun entry => allowed entry.1) }

/-- The whole package. -/
def rules : Rules Tower.Head := stage fun _ => true

/-- A larger stage contains a smaller one. -/
theorem stage_sub {allowed allowed' : DeclName → Bool}
    (le : ∀ name, allowed name = true → allowed' name = true) :
    RulesSub (stage allowed) (stage allowed') where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    change (if allowed name then allTypes name else none) = some type at declared
    change (if allowed' name then allTypes name else none) = some type
    by_cases h : allowed name = true
    · rw [if_pos h] at declared
      rw [if_pos (le name h)]
      exact declared
    · rw [if_neg h] at declared
      cases declared
  computation := by
    intro n l r step
    obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
    rw [List.mem_filter] at mem
    exact RootComputation.step_unionAll
      (List.mem_filter.mpr ⟨mem.1, le entry.1 mem.2⟩) h

/-- Every stage is inside the package. -/
theorem stage_sub_rules (allowed : DeclName → Bool) : RulesSub (stage allowed) rules :=
  stage_sub fun _ _ => rfl

/-! ## Roles -/

/-- What a constant other than `num` does: construct, compute, or nothing. -/
inductive Behaviour where
  | constructor (arity : Nat)
  | computes (arity : Nat) (inspect : InspectTree)
  | rigid

def Behaviour.role : Behaviour → Role Tower.Head
  | .constructor arity => .constructor arity
  | .computes arity inspect => .computes arity inspect
  | .rigid => .rigid

def behaviour (name : DeclName) : Behaviour :=
  if name = zeroN then .constructor 0
  else if name = sucN then .constructor 1
  else if name = numRecName then .computes 4 (.split 3 .constructor fun _ => .leaf)
  else if name = addN then .computes 2 (.split 1 .constructor fun _ => .leaf)
  else if name = powN then .computes 2 (.split 0 .constructor fun _ => .leaf)
  else if name = jName then .computes 6 (.split 5 .constructor fun _ => .leaf)
  else if name = eqAtName then .computes 1 .leaf
  else if name = sucMoveName then .computes 2 .leaf
  else if name = keepName then .computes 4 .leaf
  else if name = transportName then .computes 6 .leaf
  else if name = composeName then .computes 6 .leaf
  else if name = iterName then .computes 6 (.split 0 .constructor fun _ => .leaf)
  else if name = returnIterName then .computes 1 .leaf
  else if name = sucStepName then .computes 2 .leaf
  else .rigid

def roles : Roles Tower.Head := fun name =>
  if name = numN then .inductive ctors else (behaviour name).role

theorem roles_num : roles numN = .inductive ctors := rfl
theorem roles_zero : roles zeroN = .constructor 0 := rfl
theorem roles_suc : roles sucN = .constructor 1 := rfl
theorem roles_numRec : roles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) := rfl
theorem roles_add : roles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) := rfl
theorem roles_pow : roles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_j : roles jName = .computes 6 (.split 5 .constructor fun _ => .leaf) := rfl
theorem roles_eqAt : roles eqAtName = .computes 1 .leaf := rfl
theorem roles_sucMove : roles sucMoveName = .computes 2 .leaf := rfl
theorem roles_keep : roles keepName = .computes 4 .leaf := rfl
theorem roles_transport : roles transportName = .computes 6 .leaf := rfl
theorem roles_compose : roles composeName = .computes 6 .leaf := rfl
theorem roles_iter : roles iterName = .computes 6 (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_returnIter : roles returnIterName = .computes 1 .leaf := rfl
theorem roles_sucStep : roles sucStepName = .computes 2 .leaf := rfl
theorem roles_set : roles setN = .rigid := rfl
theorem roles_power : roles powerN = .rigid := rfl

/-- The only inductive type is `num`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List CtorField)}
    (role : roles T = .inductive cs) : T = numN ∧ cs = ctors := by
  by_cases h : T = numN
  · subst h
    exact ⟨rfl, (Role.inductive.inj role).symm⟩
  · exfalso
    change (if T = numN then .inductive ctors else (behaviour T).role) = _ at role
    rw [if_neg h] at role
    generalize behaviour T = b at role
    cases b <;> cases role

/-- A property of both branches of a conditional holds of the conditional. -/
private theorem ite_of {α : Sort _} (P : α → Prop) {p : Prop} [Decidable p] {a b : α}
    (ha : P a) (hb : P b) : P (if p then a else b) := by
  by_cases h : p
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

/-- A behaviour whose skeleton, if it computes, inspects only constructor forms. -/
private def InspectsConstructors : Behaviour → Prop
  | .computes _ inspect => inspect.OnlyConstructors
  | _ => True

/-- The behaviours of the package inspect only constructor forms. -/
theorem behaviour_onlyConstructors {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (computes : behaviour c = .computes arity inspect) : inspect.OnlyConstructors := by
  have key : InspectsConstructors (behaviour c) := by
    unfold behaviour
    repeat' apply ite_of InspectsConstructors
    all_goals first
      | trivial
      | exact InspectTree.OnlyConstructors.leaf
      | exact InspectTree.OnlyConstructors.split fun _ => .leaf
  rw [computes] at key
  exact key

/-- The computing constants of the package inspect only constructor forms. -/
theorem roles_onlyConstructors {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : roles c = .computes arity inspect) : inspect.OnlyConstructors := by
  by_cases h : c = numN
  · subst h
    cases role
  · change (if c = numN then .inductive ctors else (behaviour c).role) = _ at role
    rw [if_neg h] at role
    generalize hb : behaviour c = b at role
    cases b with
    | computes k t =>
        cases role
        exact behaviour_onlyConstructors hb
    | constructor k => cases role
    | rigid => cases role

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := roles_inductive role
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact roles_zero
    · exact roles_suc
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := roles_inductive role
    decide

/-! ## The shape of the computation -/

theorem computations_spine : ∀ entry ∈ computations, SpineShaped roles entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ step => IotaStep.spine roles_num roles_numRec constructorsDeclared step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_add step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_pow step
  · exact eliminatorComputation_spine roles_j
  · exact definitionComputation_spine roles_eqAt
  · exact definitionComputation_spine roles_sucMove
  · exact definitionComputation_spine roles_keep
  · exact definitionComputation_spine roles_transport
  · exact definitionComputation_spine roles_compose
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_iter step
  · exact definitionComputation_spine roles_returnIter
  · exact definitionComputation_spine roles_sucStep

theorem computations_headed : ∀ entry ∈ computations, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_headed
  · exact recursionComputation_headed
  · exact recursionComputation_headed
  · exact eliminatorComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed
  · exact recursionComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed

theorem computations_deterministic : ∀ entry ∈ computations, Deterministic entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := numN) roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact eliminatorComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic

theorem computations_distinct : (computations.map Prod.fst).Nodup := by
  decide

theorem shape : RootShape rules roles where
  spine := by
    intro n t u step
    have filtered : computations.filter (fun entry => (fun _ => true) entry.1) = computations :=
      List.filter_eq_self.mpr fun _ _ => rfl
    have step' : (RootComputation.unionAll computations).step t u := by
      have h := step
      change (RootComputation.unionAll (computations.filter
        fun entry => (fun _ => true) entry.1)).step t u at h
      rwa [filtered] at h
    exact RootComputation.unionAll_spine computations_spine step'
  deterministic := by
    intro n t u u' step step'
    have filtered : computations.filter (fun entry => (fun _ => true) entry.1) = computations :=
      List.filter_eq_self.mpr fun _ _ => rfl
    change (RootComputation.unionAll (computations.filter
      fun entry => (fun _ => true) entry.1)).step t u at step
    change (RootComputation.unionAll (computations.filter
      fun entry => (fun _ => true) entry.1)).step t u' at step'
    rw [filtered] at step step'
    exact (RootComputation.unionAll_deterministic computations_distinct computations_headed
      computations_deterministic step step').symm

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
