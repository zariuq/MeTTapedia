import Mettapedia.Machines.PreparedComputation

/-!
# Reading normalized callers with retained computation roles

The prepared node language distinguishes operations from invocations. Their
ordinary syntax can have exactly the same head and children. Lowering therefore
projects both syntax and a role plan; reading the syntax against a later table
of callable names is a different operation.

The reader below checks the independently stored plan and syntax, including
operand counts and binding/branch layouts. It reconstructs every node of the
existing register-node language. Its execution then uses that common node
semantics, with the current call-answer function and the branch's registers.
It does not freeze future callee answers. Native pointer ownership, C byte
encoding, source debit placement and additional dialect forms are separate
correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedCallerProjection

open RegisterCode

variable {L P H V : Type}

/-- A normalized operation and an invocation share application syntax. -/
inductive Syntax (L P H : Type) where
  | literal (value : L)
  | port (index : Nat)
  | application (head : H) (children : List (Syntax L P H))
  | branch (condition yes no : Syntax L P H)
  | binding (pattern : P) (producer body : Syntax L P H)

/-- No runtime value or binding state is stored in this metadata. -/
inductive Plan where
  | value
  | construct (children : List Plan)
  | invoke (children : List Plan)
  | branch (condition yes no : Plan)
  | sequence (producer body : Plan)

mutual
  def project : Node L H P H → Plan
    | .lit _ | .slot _ => .value
    | .op _ children => .construct (projectArgs children)
    | .call _ children => .invoke (projectArgs children)
    | .ite condition yes no => .branch (project condition) (project yes) (project no)
    | .bind producer _ body => .sequence (project producer) (project body)

  def projectArgs : List (Node L H P H) → List Plan
    | [] => []
    | node :: rest => project node :: projectArgs rest
end

mutual
  def readback : Node L H P H → Syntax L P H
    | .lit value => .literal value
    | .slot index => .port index
    | .op head children | .call head children => .application head (readbackArgs children)
    | .ite condition yes no => .branch (readback condition) (readback yes) (readback no)
    | .bind producer pattern body => .binding pattern (readback producer) (readback body)

  def readbackArgs : List (Node L H P H) → List (Syntax L P H)
    | [] => []
    | node :: rest => readback node :: readbackArgs rest
end

mutual
  /-- The role word chooses construct versus invoke. Syntax supplies only
  the operands, literal payloads, value ports and pattern. -/
  def read : Plan → Syntax L P H → Option (Node L H P H)
    | .value, .literal value => some (.lit value)
    | .value, .port index => some (.slot index)
    | .construct plans, .application head children =>
        (readArgs plans children).map (.op head)
    | .invoke plans, .application head children =>
        (readArgs plans children).map (.call head)
    | .branch condition yes no, .branch c t e => do
        let c' ← read condition c
        let t' ← read yes t
        let e' ← read no e
        pure (.ite c' t' e')
    | .sequence producer body, .binding pattern c b => do
        let c' ← read producer c
        let b' ← read body b
        pure (.bind c' pattern b')
    | _, _ => none

  def readArgs : List Plan → List (Syntax L P H) → Option (List (Node L H P H))
    | [], [] => some []
    | plan :: plans, term :: terms => do
        let node ← read plan term
        let rest ← readArgs plans terms
        pure (node :: rest)
    | _, _ => none
end

mutual
  /-- Projection and readback are independent traversals. Their checked
  reader recovers all operations, ordered operands, ports and lexical binds. -/
  theorem read_project (node : Node L H P H) :
      read (project node) (readback node) = some node := by
    cases node with
    | lit value => rfl
    | slot index => rfl
    | op head children => simp [project, readback, read, readArgs_project children]
    | call head children => simp [project, readback, read, readArgs_project children]
    | ite c t e => simp [project, readback, read, read_project c, read_project t, read_project e]
    | bind producer pattern body =>
        simp [project, readback, read, read_project producer, read_project body]

  theorem readArgs_project (nodes : List (Node L H P H)) :
      readArgs (projectArgs nodes) (readbackArgs nodes) = some nodes := by
    cases nodes with
    | nil => rfl
    | cons node rest =>
        simp [projectArgs, readbackArgs, readArgs, read_project node, readArgs_project rest]
end

/-- Execution uses the current call-answer function, not a saved result or
an invocation reconstructed from its printed head. -/
def execute (sem : Sem V L H P H) (answer : H → List V → Option V)
    (registers : Regs V) (plan : Plan) (term : Syntax L P H) : Option (V × Regs V) :=
  (read plan term).bind (eval sem answer registers)

theorem execution_refines (sem : Sem V L H P H) (answer : H → List V → Option V)
    (registers : Regs V) (node : Node L H P H) :
    execute sem answer registers (project node) (readback node) =
      eval sem answer registers node := by
  simp [execute, read_project]

/-- Compiling the reconstructed caller uses the existing register lowering,
with its original scope, temporary-register and primitive obligations. -/
theorem register_lowering_agrees (node : Node L H P H) (fuses : H → Nat → Bool)
    (tail : Bool) (destination next : Nat) :
    (read (project node) (readback node)).map
      (fun caller => compile fuses caller tail destination next) =
        some (compile fuses node tail destination next) := by
  rw [read_project]
  rfl

/-- No source-head lookup participates in the saved interpretation. The
function here describes the unsafe alternative, for comparison below. -/
def liveHeadReading (known : H → Bool) (head : H) (children : List (Node L H P H)) :
    Node L H P H :=
  if known head then .call head children else .op head children

theorem same_syntax_distinct_roles (head : H) (children : List (Node L H P H)) :
    readback (.op head children) = readback (.call head children) ∧
      project (.op head children) ≠ project (.call head children) := by
  exact ⟨rfl, by simp [project]⟩

theorem late_declaration_changes_reading (head : H) (children : List (Node L H P H)) :
    liveHeadReading (fun _ => false) head children ≠
      liveHeadReading (fun _ => true) head children := by
  simp [liveHeadReading]

theorem saved_constructor_survives_declaration (head : H) (children : List (Node L H P H)) :
    read (project (.op head children)) (readback (.op head children)) =
      some (liveHeadReading (fun _ => false) head children) ∧
    read (project (.op head children)) (readback (.op head children)) ≠
      some (liveHeadReading (fun _ => true) head children) := by
  simp [read_project, liveHeadReading]

theorem captured_payload_stays_value (payload : L) :
    read Plan.value (Syntax.literal payload : Syntax L P H) = some (.lit payload) := by rfl

theorem missing_operand_refused (head : H) :
    read (.construct [.value]) (Syntax.application head [] : Syntax L P H) = none := by rfl

theorem extra_operand_refused (head : H) (payload : L) :
    read (.invoke []) (Syntax.application head [.literal payload] : Syntax L P H) = none := by rfl

theorem wrong_binding_layout_refused (pattern : P) (a b : Syntax L P H) :
    read (.construct [.value, .value]) (.binding pattern a b) = none := by rfl

/-- A constructor cone contains only completed literals, value ports and
pure data construction. It contains no primitive or invocation instruction. -/
inductive ValueTemplate (L H : Type) where
  | literal (value : L)
  | port (index : Nat)
  | construct (head : H) (children : List (ValueTemplate L H))

mutual
  def ValueTemplate.code : ValueTemplate L H → Node L H P H
    | .literal value => .lit value
    | .port index => .slot index
    | .construct head children => .op head (ValueTemplate.codes children)

  def ValueTemplate.codes : List (ValueTemplate L H) → List (Node L H P H)
    | [] => []
    | node :: rest => node.code :: ValueTemplate.codes rest
end

mutual
  /-- Value publication substitutes ports and builds data directly. It has
  neither a call-answer function nor an instruction dispatcher. -/
  def ValueTemplate.instantiate (literal : L → V) (construct : H → List V → V)
      (registers : Regs V) : ValueTemplate L H → Option V
    | .literal value => some (literal value)
    | .port index => registers index
    | .construct head children =>
        (ValueTemplate.instantiateArgs literal construct registers children).map (construct head)

  def ValueTemplate.instantiateArgs (literal : L → V) (construct : H → List V → V)
      (registers : Regs V) : List (ValueTemplate L H) → Option (List V)
    | [] => some []
    | node :: rest => do
        let value ← node.instantiate literal construct registers
        let values ← ValueTemplate.instantiateArgs literal construct registers rest
        pure (value :: values)
end

mutual
  theorem value_place_refines (sem : Sem V L H P H) (construct : H → List V → V)
      (constructorLaw : ∀ head values, sem.op head values = some (construct head values))
      (answer : H → List V → Option V) (registers : Regs V) (value : ValueTemplate L H) :
      eval sem answer registers value.code =
        (value.instantiate sem.lit construct registers).map (fun v => (v, registers)) := by
    cases value with
    | literal value => rfl
    | port index => simp [ValueTemplate.code, ValueTemplate.instantiate, eval]
    | construct head children =>
        simp only [ValueTemplate.code, eval,
          value_places_refine sem construct constructorLaw answer registers children,
          ValueTemplate.instantiate]
        cases ValueTemplate.instantiateArgs sem.lit construct registers children <;>
          simp [constructorLaw]

  theorem value_places_refine (sem : Sem V L H P H) (construct : H → List V → V)
      (constructorLaw : ∀ head values, sem.op head values = some (construct head values))
      (answer : H → List V → Option V) (registers : Regs V) (values : List (ValueTemplate L H)) :
      evalList sem answer registers (ValueTemplate.codes values) =
        (ValueTemplate.instantiateArgs sem.lit construct registers values).map
          (fun vs => (vs, registers)) := by
    cases values with
    | nil => rfl
    | cons node rest =>
        simp only [ValueTemplate.codes, evalList,
          value_place_refines sem construct constructorLaw answer registers node,
          ValueTemplate.instantiateArgs]
        cases first : node.instantiate sem.lit construct registers with
        | none => simp
        | some value =>
            simp only [Option.map_some, Option.bind_some]
            rw [value_places_refine sem construct constructorLaw answer registers rest]
            cases remaining : ValueTemplate.instantiateArgs sem.lit construct registers rest <;>
              simp
end

theorem completed_constructor_ignores_callee_changes
    (sem : Sem V L H P H) (construct : H → List V → V)
    (constructorLaw : ∀ head values, sem.op head values = some (construct head values))
    (before after : H → List V → Option V) (registers : Regs V) (value : ValueTemplate L H) :
    eval sem before registers value.code = eval sem after registers value.code := by
  rw [value_place_refines sem construct constructorLaw,
      value_place_refines sem construct constructorLaw]

end Mettapedia.Machines.PreparedCallerProjection

#print axioms Mettapedia.Machines.PreparedCallerProjection.read_project
#print axioms Mettapedia.Machines.PreparedCallerProjection.execution_refines
#print axioms Mettapedia.Machines.PreparedCallerProjection.saved_constructor_survives_declaration
