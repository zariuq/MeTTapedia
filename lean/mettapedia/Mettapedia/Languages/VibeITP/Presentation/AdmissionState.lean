import Mettapedia.Languages.VibeITP.Presentation.ProofCorrespondence
import Mettapedia.Languages.VibeITP.Spec.ProtocolAdmission

/-!
# Resolved static Vibe declaration admission

The state retains the phase, internally allocated identities and complete
ordered theory data. Declaration operands are already resolved symbols and
terms. Slot placement and binary parsing are separate interface operations.
The protocol projection connects these logical updates to its existing
allocation and admitted-theory invariants.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission

open ComputationalData ComputationalShift ComputationalDefinitions ComputationalProofs

structure AdmissionState where
  phase : Spec.Phase
  nextFresh : Nat
  table : SignatureTable
  axioms : List Spec.Term
  definitions : List Spec.Definition

namespace AdmissionState

def theory (state : AdmissionState) : Spec.Theory :=
  theoryOf state.table state.axioms state.definitions

def protocol (state : AdmissionState) : Spec.State :=
  { Spec.initialState with
    phase := state.phase
    fresh := fun identity => signatureOf state.table (.fresh identity)
    nextFresh := state.nextFresh
    axioms := state.axioms
    definitions := state.definitions }

def allocate (state : AdmissionState) (info : Spec.SymInfo) : AdmissionState :=
  { state with
    nextFresh := state.nextFresh + 1
    table := (.fresh state.nextFresh, info) :: state.table }

def addAxiom (state : AdmissionState) (statement : Spec.Term) : AdmissionState :=
  { state with axioms := state.axioms ++ [statement] }

def define (state : AdmissionState) (parameters : List Spec.SymId) (body : Spec.Term) : AdmissionState :=
  { state.allocate (Spec.definitionInfo (signatureOf state.table) parameters) with
    definitions := state.definitions ++ [⟨.fresh state.nextFresh, parameters, body⟩] }

end AdmissionState

def initialAdmission : AdmissionState :=
  ⟨.setup, 0, allocatedSnapshot Spec.initialState.theory 0, [], []⟩

inductive Declaration where
  | fvar (arity : Nat)
  | constant (binders : List Nat)
  | axiom (statement : Spec.Term)
  | definition (parameters : List Spec.SymId) (hints : List Nat) (body : Spec.Term)
  | enterProofs

def admit (state : AdmissionState) : Declaration → Option AdmissionState
  | .fvar arity => some (state.allocate (Spec.SymInfo.fvarOf arity))
  | .constant binders => some (state.allocate ⟨.constant, binders⟩)
  | .axiom statement =>
      if state.phase = .setup ∧ Spec.WellFormed (signatureOf state.table) statement = true ∧
          Spec.depth (signatureOf state.table) statement = 0 then
        some (state.addAxiom statement)
      else none
  | .definition parameters hints body =>
      if Spec.WellFormed (signatureOf state.table) body &&
          Spec.definitionAdmissible (signatureOf state.table) parameters hints body then
        some (state.define parameters body)
      else none
  | .enterProofs => some { state with phase := .proofs }

inductive Admits : AdmissionState → Declaration → AdmissionState → Prop where
  | fvar (state : AdmissionState) (arity : Nat) :
      Admits state (.fvar arity) (state.allocate (Spec.SymInfo.fvarOf arity))
  | constant (state : AdmissionState) (binders : List Nat) :
      Admits state (.constant binders) (state.allocate ⟨.constant, binders⟩)
  | axiom {state : AdmissionState} {statement : Spec.Term} :
      state.phase = .setup → Spec.WellFormed (signatureOf state.table) statement = true →
      Spec.depth (signatureOf state.table) statement = 0 →
      Admits state (.axiom statement) (state.addAxiom statement)
  | definition {state : AdmissionState} {parameters : List Spec.SymId} {hints : List Nat} {body : Spec.Term} :
      Spec.WellFormed (signatureOf state.table) body = true →
      Spec.definitionAdmissible (signatureOf state.table) parameters hints body = true →
      Admits state (.definition parameters hints body) (state.define parameters body)
  | enterProofs (state : AdmissionState) :
      Admits state .enterProofs { state with phase := .proofs }

theorem admit_eq_some_iff (state after : AdmissionState) (declaration : Declaration) :
    admit state declaration = some after ↔ Admits state declaration after := by
  constructor
  · intro computed
    cases declaration with
    | fvar arity => cases Option.some.inj computed; exact .fvar _ _
    | constant binders => cases Option.some.inj computed; exact .constant _ _
    | «axiom» statement =>
        simp only [admit] at computed
        split at computed
        · rename_i guards
          cases Option.some.inj computed
          exact .axiom guards.1 guards.2.1 guards.2.2
        · cases computed
    | definition parameters hints body =>
        simp only [admit] at computed
        split at computed
        · rename_i guards
          cases Option.some.inj computed
          exact .definition (Bool.and_eq_true_iff.mp guards).1 (Bool.and_eq_true_iff.mp guards).2
        · cases computed
    | enterProofs => cases Option.some.inj computed; exact .enterProofs _
  · intro admitted
    cases admitted <;> simp_all [admit]

def admitRun (state : AdmissionState) : List Declaration → Option AdmissionState
  | [] => some state
  | declaration :: rest => (admit state declaration).bind fun after => admitRun after rest

inductive AdmissionRun : AdmissionState → List Declaration → AdmissionState → Prop where
  | nil (state : AdmissionState) : AdmissionRun state [] state
  | cons {before middle after : AdmissionState} {declaration : Declaration} {rest : List Declaration} :
      Admits before declaration middle → AdmissionRun middle rest after →
      AdmissionRun before (declaration :: rest) after

theorem admitRun_eq_some_iff (state after : AdmissionState) (declarations : List Declaration) :
    admitRun state declarations = some after ↔ AdmissionRun state declarations after := by
  induction declarations generalizing state with
  | nil => constructor <;> intro h
           · cases Option.some.inj h; exact .nil _
           · cases h; rfl
  | cons declaration rest ih =>
      constructor
      · intro computed
        cases step : admit state declaration with
        | none => simp [admitRun, step] at computed
        | some middle =>
            exact .cons ((admit_eq_some_iff _ _ _).mp step)
              ((ih middle).mp (by simpa [admitRun, step] using computed))
      · intro run
        cases run with
        | cons step tail => simp [admitRun, (admit_eq_some_iff _ _ _).mpr step, (ih _).mpr tail]

def encodePhase : Spec.Phase → Mettapedia.GSLT.LanguageDef.DeterministicEquations.Term
  | .setup => .sym "Setup"
  | .proofs => .sym "Proofs"

open Mettapedia.GSLT.LanguageDef.DeterministicEquations in
def encodeState (state : AdmissionState) : Term :=
  .list [.sym "Vibe:Admission", encodePhase state.phase, natural state.nextFresh,
    encodeTable state.table, encodeAxioms state.axioms, encodeDefinitions state.definitions]

open Mettapedia.GSLT.LanguageDef.DeterministicEquations in
def encodeAdmissionResult : Option AdmissionState → Term
  | none => .sym "None"
  | some state => .expr [.sym "Some", encodeState state]

open Mettapedia.GSLT.LanguageDef.DeterministicEquations in
def encodeDeclaration : Declaration → Term
  | .fvar arity => .list [.sym "Declare:Fvar", natural arity]
  | .constant binders => .list [.sym "Declare:Constant", encodeBinders binders]
  | .axiom statement => .list [.sym "Declare:Axiom", encode statement]
  | .definition parameters hints body =>
      .list [.sym "Declare:Definition", encodeSymbols parameters, encodeBinders hints, encode body]
  | .enterProofs => .list [.sym "Declare:Proofs"]

open Mettapedia.GSLT.LanguageDef.DeterministicEquations in
def encodeDeclarations (declarations : List Declaration) : Term := .list (declarations.map encodeDeclaration)

def checkAdmitted (state : AdmissionState) (declarations : List Declaration)
    (witness : ProofWitness) (claimed : Spec.Term) : Bool :=
  match admitRun state declarations with
  | none => false
  | some after => ProofWitness.check after.theory witness claimed

def checkStatic (declarations : List Declaration) (witness : ProofWitness) (claimed : Spec.Term) : Bool :=
  checkAdmitted initialAdmission declarations witness claimed

end Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission
