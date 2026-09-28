import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ScopedComputationTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PartialSubstitution
import Mathlib.Data.Finset.Sort

/-!
# Checked capture packets for scoped computation returns

A static resume table contains scoped bodies and their native input and result
types. A dynamic packet contains a finite table label and only the older value
coordinates used by that interface. It contains no host-language continuation.

Checked resumption traverses the reified body using its partial environment.
The compilation theorem compares that operation to the existing dense source
substitution. Ambient transport and typed return binding then follow from the
native substitution algebra. The support inventory is syntactic, including
type dependencies; it is not a semantic dead-code analysis or a native GC root
map for opaque handles, effect handlers or unification stores.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ScopedComputation

variable {Head Operation : Type} {n m k : Nat}

namespace Code

def support : {n : Nat} → Code Head Operation n → Finset (Fin n)
  | _, .returnValue term => term.support
  | _, .sequence first body | _, .sequenceSigma first body =>
      first.support ∪ outerSupport body.support
  | _, .choose left right => left.support ∪ right.support
  | _, .call _ argument => argument.support

/-- A missing used capture is a rejected reconstruction, not logical failure. -/
def substitutePartial {n m : Nat} (environment : PartialSub Head n m) :
    Code Head Operation n → Option (Code Head Operation m)
  | .returnValue term => (substPartial environment term).map Code.returnValue
  | .sequence first body => do
      let first ← substitutePartial environment first
      let body ← substitutePartial (liftPartialSub environment) body
      pure (.sequence first body)
  | .sequenceSigma first body => do
      let first ← substitutePartial environment first
      let body ← substitutePartial (liftPartialSub environment) body
      pure (.sequenceSigma first body)
  | .choose left right => do
      let left ← substitutePartial environment left
      let right ← substitutePartial environment right
      pure (.choose left right)
  | .call operation argument => (substPartial environment argument).map (Code.call operation)

theorem substitutePartial_eq (code : Code Head Operation n)
    {partialEnv : PartialSub Head n m} {environment : Sub Head n m}
    (agree : ∀ index, index ∈ code.support → partialEnv index = some (environment index)) :
    code.substitutePartial partialEnv = some (code.substitute environment) := by
  induction code generalizing m with
  | returnValue term => rw [substitutePartial, substPartial_eq term agree]; rfl
  | sequence first body ihFirst ihBody =>
      rw [substitutePartial, ihFirst (fun i hi => agree i (Finset.mem_union_left _ hi)),
        ihBody (liftPartialSub_agrees (fun i hi => agree i (Finset.mem_union_right _ hi)))]
      rfl
  | sequenceSigma first body ihFirst ihBody =>
      rw [substitutePartial, ihFirst (fun i hi => agree i (Finset.mem_union_left _ hi)),
        ihBody (liftPartialSub_agrees (fun i hi => agree i (Finset.mem_union_right _ hi)))]
      rfl
  | choose left right ihLeft ihRight =>
      rw [substitutePartial, ihLeft (fun i hi => agree i (Finset.mem_union_left _ hi)),
        ihRight (fun i hi => agree i (Finset.mem_union_right _ hi))]
      rfl
  | call operation argument => rw [substitutePartial, substPartial_eq argument agree]; rfl

theorem substitutePartial_defined (code : Code Head Operation n)
    (environment : PartialSub Head n m) :
    (code.substitutePartial environment).isSome = true ↔
      ∀ index, index ∈ code.support → (environment index).isSome = true := by
  induction code generalizing m with
  | returnValue term =>
      simpa only [substitutePartial, Option.isSome_map, support] using substPartial_defined term environment
  | sequence first body ihFirst ihBody =>
      simp only [substitutePartial, Option.assemble_two_isSome, Bool.and_eq_true,
        ihFirst, ihBody, liftPartialSub_defined, support,
        Finset.mem_union, or_imp, forall_and]
  | sequenceSigma first body ihFirst ihBody =>
      simp only [substitutePartial, Option.assemble_two_isSome, Bool.and_eq_true,
        ihFirst, ihBody, liftPartialSub_defined, support,
        Finset.mem_union, or_imp, forall_and]
  | choose left right ihLeft ihRight =>
      simp only [substitutePartial, Option.assemble_two_isSome, Bool.and_eq_true,
        ihLeft, ihRight, support, Finset.mem_union, or_imp, forall_and]
  | call operation argument =>
      simpa only [substitutePartial, Option.isSome_map, support] using substPartial_defined argument environment

end Code

namespace Captures

/-- Static code and interface, with the returned value at body coordinate zero. -/
structure Template (Head Operation : Type) where
  arity : Nat
  input : Tm Head arity
  result : Tm Head (arity + 1)
  body : Code Head Operation (arity + 1)

def Template.support (template : Template Head Operation) : Finset (Fin template.arity) :=
  template.input.support ∪ outerSupport template.result.support ∪
    outerSupport template.body.support

def Template.slots (template : Template Head Operation) : List (Fin template.arity) :=
  template.support.sort (· ≤ ·)

@[simp] theorem Template.mem_slots (template : Template Head Operation)
    (index : Fin template.arity) : index ∈ template.slots ↔ index ∈ template.support := by
  simp [slots]

/-- Every table is finite, while different labels may have different captures. -/
structure Program (Head Operation : Type) where
  labels : Nat
  entry : Fin labels → Template Head Operation

abbrev Environment (Head : Type) (n m : Nat) := List (Fin n × Tm Head m)

def lookup : Environment Head n m → PartialSub Head n m
  | [], _ => none
  | (slot, value) :: rest, index => if index = slot then some value else lookup rest index

def capture (slots : List (Fin n)) (environment : Sub Head n m) : Environment Head n m :=
  slots.map fun index => (index, environment index)

theorem lookup_capture {slots : List (Fin n)} (environment : Sub Head n m)
    {index : Fin n} (present : index ∈ slots) :
    lookup (capture slots environment) index = some (environment index) := by
  induction slots with
  | nil => simp at present
  | cons slot rest ih =>
      simp only [capture, List.map_cons, lookup]
      by_cases same : index = slot
      · simp [same]
      · rw [if_neg same]
        exact ih ((List.mem_cons.mp present).resolve_left same)

/-- The runtime packet names immutable code and stores first-order captures. -/
structure Packet (program : Program Head Operation) (m : Nat) where
  label : Fin program.labels
  values : Environment Head (program.entry label).arity m

def compile (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) : Packet program m :=
  ⟨label, capture (program.entry label).slots environment⟩

def Packet.input? {program : Program Head Operation} (packet : Packet program m) :
    Option (Tm Head m) :=
  substPartial (lookup packet.values) (program.entry packet.label).input

/-- Reconstruct both the remaining source code and its selected result type. -/
def Packet.resume? {program : Program Head Operation} (packet : Packet program m)
    (answer : Tm Head m) : Option (Code Head Operation m × Tm Head m) := do
  let _ ← packet.input?
  let template := program.entry packet.label
  let environment := Fin.cases (some answer) (lookup packet.values)
  let code ← template.body.substitutePartial environment
  let type ← substPartial environment template.result
  pure (code, type)

theorem compile_input (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) :
    (compile program label environment).input? =
      some (subst environment (program.entry label).input) := by
  apply substPartial_eq
  intro index present
  apply lookup_capture environment
  apply (Template.mem_slots _ _).mpr
  exact Finset.mem_union_left _ (Finset.mem_union_left _ present)

private theorem compile_agrees (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) (answer : Tm Head m)
    {slots : Finset (Fin ((program.entry label).arity + 1))}
    (supported : outerSupport slots ⊆ (program.entry label).support) :
    ∀ index, index ∈ slots →
      Fin.cases (some answer) (lookup (compile program label environment).values) index =
        some (consSub answer environment index) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · intro _
    rfl
  · intro prior present
    simp only [Fin.cases_succ, consSub_succ]
    exact lookup_capture environment
      ((Template.mem_slots _ _).mpr (supported (mem_outerSupport.mpr present)))

/-- Sparse capture and checked reconstruction equal dense source opening. -/
theorem compile_resume (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) (answer : Tm Head m) :
    (compile program label environment).resume? answer =
      some ((program.entry label).body.substitute (consSub answer environment),
        subst (consSub answer environment) (program.entry label).result) := by
  have inputExact := compile_input program label environment
  have codeExact := Code.substitutePartial_eq _ (compile_agrees program label environment answer
    (fun _ present => Finset.mem_union_right _ present))
  have typeExact := substPartial_eq _ (compile_agrees program label environment answer
    (fun _ present => Finset.mem_union_left _ (Finset.mem_union_right _ present)))
  dsimp only [Packet.resume?, compile] at *
  rw [inputExact, codeExact, typeExact]
  rfl

def Packet.transport {program : Program Head Operation} (packet : Packet program m)
    (substitution : Sub Head m k) : Packet program k :=
  ⟨packet.label, packet.values.map fun item => (item.1, subst substitution item.2)⟩

theorem transport_compile (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) (substitution : Sub Head m k) :
    (compile program label environment).transport substitution =
      compile program label (subComp substitution environment) := by
  simp [Packet.transport, compile, capture, List.map_map, Function.comp_def, subComp]

/-- Ambient substitution commutes with supplying the return value, including
the dependent output family. Program labels remain unchanged. -/
theorem transport_resume (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m)
    (substitution : Sub Head m k) (answer : Tm Head m) :
    ((compile program label environment).transport substitution).resume? (subst substitution answer) =
      ((compile program label environment).resume? answer).map
        (fun result => (result.1.substitute substitution, subst substitution result.2)) := by
  rw [transport_compile, compile_resume, compile_resume]
  simp only [Option.map_some, Code.substitute_comp, subst_subComp, subComp_consSub]

/-- Native typing survives reconstruction when the return value is admitted
at this template's instantiated input type. This is not a runtime type checker. -/
theorem resume_typed (program : Program Head Operation) (label : Fin program.labels)
    {R : Rules Head} {signature : OperationSignature Head Operation}
    {Γ : Ctx Head (program.entry label).arity} {Δ : Ctx Head m}
    {environment : Sub Head (program.entry label).arity m} {answer : Tm Head m}
    (bodyTyped : Typing R signature (.snoc Γ (program.entry label).input)
      (program.entry label).body (program.entry label).result)
    (environmentTyped : FormationSensitive.CtxMor R Γ Δ environment)
    (answerTyped : FormationSensitive.Typing R Δ answer
      (subst environment (program.entry label).input))
    {result : Code Head Operation m × Tm Head m}
    (resumed : (compile program label environment).resume? answer = some result) :
    Typing R signature Δ result.1 result.2 := by
  rw [compile_resume, Option.some.injEq] at resumed
  subst result
  exact bodyTyped.substitute (extendEnvironment environmentTyped answerTyped)

/-- Capture storage contains one entry per used older coordinate, regardless
of how many times that variable occurs in the body. -/
theorem compile_size (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) :
    (compile program label environment).values.length = (program.entry label).support.card := by
  simp [compile, capture, Template.slots]

theorem compile_size_le_arity (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) :
    (compile program label environment).values.length ≤ (program.entry label).arity := by
  rw [compile_size]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

theorem compile_keys (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) :
    (compile program label environment).values.map Prod.fst = (program.entry label).slots := by
  simp [compile, capture, List.map_map, Function.comp_def]

theorem compile_keys_nodup (program : Program Head Operation) (label : Fin program.labels)
    (environment : Sub Head (program.entry label).arity m) :
    ((compile program label environment).values.map Prod.fst).Nodup := by
  rw [compile_keys]
  exact Finset.sort_nodup (program.entry label).support (· ≤ ·)

theorem returnEnvironment_defined (slots : Finset (Fin (n + 1)))
    (environment : PartialSub Head n m) (answer : Tm Head m) :
    (∀ index, index ∈ slots →
      ((Fin.cases (some answer) environment : PartialSub Head (n + 1) m) index).isSome = true) ↔
      ∀ index, index ∈ outerSupport slots → (environment index).isSome = true := by
  constructor
  · intro all index present
    exact all index.succ (mem_outerSupport.mp present)
  · intro all index
    refine Fin.cases ?_ ?_ index
    · intro _
      rfl
    · intro prior present
      exact all prior (mem_outerSupport.mpr present)

/-- This characterizes admission for arbitrary packets, not only the compiler's
output. Type-only dependencies are required too. -/
theorem Packet.resume_defined {program : Program Head Operation} (packet : Packet program m)
    (answer : Tm Head m) :
    (packet.resume? answer).isSome = true ↔
      ∀ index, index ∈ (program.entry packet.label).support →
        (lookup packet.values index).isSome = true := by
  simp only [Packet.resume?, Packet.input?, Option.assemble_three_isSome, Bool.and_eq_true,
    substPartial_defined, Code.substitutePartial_defined, returnEnvironment_defined,
    Template.support, Finset.mem_union, or_imp, forall_and]
  tauto

theorem Packet.missing_capture_rejected {program : Program Head Operation} (packet : Packet program m)
    (answer : Tm Head m) {index : Fin (program.entry packet.label).arity}
    (used : index ∈ (program.entry packet.label).support)
    (missing : lookup packet.values index = none) : packet.resume? answer = none := by
  cases result : packet.resume? answer with
  | none => rfl
  | some value =>
      have available := (packet.resume_defined answer).mp (by simp [result]) index used
      simp [missing] at available

end Captures
end ScopedComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
