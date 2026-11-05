import Mettapedia.Languages.MeTTa.PeTTa.PureData

/-!
# A kit for proving that a MeTTa library computes its Lean model

A *library* is a quoted source loaded over a base program, together with the heads it owns and
their formal parameters. One decidable `Library.check`, evaluated once per library by the kernel,
gives everything a head proof needs:

- `lift`: a computation of the base program runs unchanged in the library's runtime, when its code
  calls no owned head;
- `call`: calling an owned head evaluates its body under the formals bound to the arguments;
- `capture`: a call whose argument code evaluates to captured values behaves like the call on those
  values, so a proved fact about a head at values applies at every call site.

The evaluator's forms with their side conditions discharged are in `BridgeForms`.

`metta_body` replaces `L.body head` in a goal by the literal body read from the quoted source,
checked by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open SpaceSemantics (Program Equation)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval

/-- The evaluator's special forms. An authored head is never one of them. -/
def specialForms : List String := ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"]

/-- The head an arrow declaration `(: head (-> …))` declares. -/
def arrowHead : Atom → Option String
  | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => some head
  | _ => none

/-- A source loaded over a base program. Its heads are the ones starting with one of its prefixes;
the base defines none of them. Ownership by literal prefixes keeps the kernel's check cheap. -/
structure Library where
  base : Program
  source : Program
  prefixes : List String

namespace Library

variable (L : Library)

/-- The base with the source loaded after it. -/
def runtime : Program := L.base.append L.source

/-- Whether the library owns a head. -/
def owns (head : String) : Bool := L.prefixes.any fun start => head.startsWith start

/-- The heads the library leaves to its base. -/
def inherited (head : String) : Bool := !L.owns head

/-- The variables among an equation's arguments. -/
def formalNames (equation : Equation) : List String :=
  equation.arguments.filterMap fun | .var name => some name | _ => none

/-- The source equation of a head. -/
def equationOf (head : String) : Option Equation := L.source.equations.find? (·.head == head)

/-- The body of an owned head. -/
def body (head : String) : Atom := ((L.equationOf head).map (·.body)).getD (.symbol "missing")

/-- The formals of an owned head. -/
def formals (head : String) : List String := ((L.equationOf head).map formalNames).getD []

/-- A source equation is the only one of its head, an ordinary function of distinct variables, and
takes its arguments raw. -/
def equationReady (equation : Equation) : Bool :=
  equation.arguments == (formalNames equation).map Atom.var && decide (formalNames equation).Nodup &&
  (L.source.equations.filter (·.head == equation.head)).length == 1 &&
  !specialForms.contains equation.head && !ioHead equation.head && !StdLib.known equation.head &&
  (List.range (formalNames equation).length).all (argumentIsRaw L.source equation.head)

/-- An owned head that a proof may call: its source equation is ready. Decided per head. -/
def headReady (head : String) : Bool := ((L.equationOf head).map L.equationReady).getD false

/-- What the lemmas of the library rest on, as one kernel-decidable test: the base keeps to its own
heads, and the source defines and declares only owned heads. Each called head is checked by
`headReady` where it is called. -/
def check : Bool :=
  L.inherited "let" &&
  (L.base.equations.all fun equation => L.inherited equation.head && codeWithin L.inherited equation.body) &&
  (L.source.equations.all fun equation => L.owns equation.head) &&
  (L.source.declarations.all fun declaration => (arrowHead declaration).all L.owns)

variable {L}

private theorem check_parts (checked : L.check = true) :
    L.inherited "let" = true ∧
    (L.base.equations.all fun equation => L.inherited equation.head && codeWithin L.inherited equation.body) = true ∧
    (L.source.equations.all fun equation => L.owns equation.head) = true ∧
    (L.source.declarations.all fun declaration => (arrowHead declaration).all L.owns) = true := by
  simpa only [check, Bool.and_eq_true, and_assoc] using checked

/-- The base is closed under the heads it keeps. -/
theorem closed (checked : L.check = true) : ProgramClosed L.inherited L.base := by
  obtain ⟨binding, bodies, _⟩ := check_parts checked
  refine ⟨binding, fun equation member _ => ?_⟩
  have row := List.all_eq_true.mp bodies equation member
  simp only [Bool.and_eq_true] at row
  exact row.2

/-- The runtime agrees with the base on every inherited head. -/
theorem agreement (checked : L.check = true) : ProgramAgreementOn L.inherited L.base L.runtime := by
  obtain ⟨_, _, equations, declarations⟩ := check_parts checked
  apply appended_program_agreement
  · intro equation member
    have row := List.all_eq_true.mp equations equation member
    simp [inherited, row]
  · intro name types member
    have owned := List.all_eq_true.mp declarations _ member
    simpa [arrowHead, inherited] using owned

/-- An owned head has exactly its component's source equations, including
multi-clause definitions. Conservative loading excludes shadowing base rows. -/
theorem owned_equations (checked : L.check = true) {head : String} (owned : L.owns head = true) :
    L.runtime.equations.filter (·.head == head) = L.source.equations.filter (·.head == head) := by
  obtain ⟨_, bases, _, _⟩ := check_parts checked
  have below : L.base.equations.filter (·.head == head) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro other member selected
    have kept := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp bases other member)).1
    rw [beq_iff_eq.mp selected] at kept
    simp only [inherited, owned, Bool.not_true, Bool.false_eq_true] at kept
  simp only [runtime, SpaceSemantics.Program.append, List.filter_append, below, List.nil_append]

/-- **A base computation runs unchanged in the runtime**, when its code calls no owned head. -/
theorem lift (checked : L.check = true) {caller : Subst} {before after : State} {code answer : Atom}
    (supported : codeWithin L.inherited code = true)
    (returned : PureReturns L.base caller before code after answer) :
    PureReturns L.runtime caller before code after answer :=
  path_of_closed_agreement (closed checked) (agreement checked) ⟨supported, rfl⟩ returned

/-- The bindings of formals to values, innermost first. -/
def bind (names : List String) (values : List Atom) : Subst := (names.zip values).reverse

/-- What the check gives about a defined head. -/
private theorem defined_parts (checked : L.check = true) {head : String} {equation : Equation}
    (found : L.equationOf head = some equation) (ready : L.headReady head = true) :
    L.runtime.equations.filter (·.head == head) = [equation] ∧
    equation.arguments = (L.formals head).map Atom.var ∧ (L.formals head).Nodup ∧
    specialForms.contains head = false ∧ ioHead head = false ∧ StdLib.known head = false ∧
    ∀ index < (L.formals head).length, argumentIsRaw L.runtime head index = true := by
  obtain ⟨_, bases, sources, _⟩ := check_parts checked
  have same : equation.head = head := by simpa using List.find?_some found
  have member := List.mem_of_find?_eq_some found
  have owned := List.all_eq_true.mp sources equation member
  have row : L.equationReady equation = true := by simpa [headReady, found] using ready
  simp only [equationReady, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true, List.mem_range] at row
  obtain ⟨⟨⟨⟨⟨⟨arguments, distinct⟩, single⟩, ordinary⟩, notIO⟩, notNative⟩, raw⟩ := row
  subst same
  have formals : L.formals equation.head = formalNames equation := by simp [formals, found]
  rw [formals]
  refine ⟨?_, arguments, distinct, ordinary, notIO, notNative, ?_⟩
  · have own : L.source.equations.filter (·.head == equation.head) = [equation] := by
      obtain ⟨only, rows⟩ := List.length_eq_one_iff.mp single
      have present : equation ∈ L.source.equations.filter (·.head == equation.head) :=
        List.mem_filter.mpr ⟨member, by simp⟩
      rw [rows] at present ⊢
      rw [List.mem_singleton.mp present]
    rw [owned_equations checked owned]
    exact own
  · intro index bounded
    have fromSource := raw index bounded
    simp only [argumentIsRaw, notNative, Bool.false_eq_true, ↓reduceIte] at fromSource ⊢
    simp only [runtime, SpaceSemantics.Program.append, List.any_append, fromSource, Bool.or_true]

/-- **Calling an owned head** evaluates its body under its formals. -/
theorem call (checked : L.check = true) {head : String} (ready : L.headReady head = true)
    (caller : Subst) (before after : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = (L.formals head).length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns L.runtime (bind (L.formals head) values) before (L.body head) after answer) :
    PureReturns L.runtime caller before (.expression (.symbol head :: arguments)) after answer := by
  obtain ⟨equation, found⟩ : ∃ equation, L.equationOf head = some equation := by
    cases found : L.equationOf head with
    | none => simp [headReady, found] at ready
    | some equation => exact ⟨equation, rfl⟩
  obtain ⟨rows, arguments', distinct, ordinary, notIO, notNative, raw⟩ := defined_parts checked found ready
  have bodyEq : L.body head = equation.body := by simp [body, found]
  rw [bodyEq] at returned
  apply PureData.raw_authored_call_return L.runtime caller (bind (L.formals head) values) before after head arguments
    equation.body answer
  · intro special
    have : specialForms.contains head = true := by simpa [specialForms] using special
    rw [this] at ordinary
    cases ordinary
  · exact notIO
  · exact notNative
  · have present : equation ∈ L.runtime.equations.filter (·.head == head) := by rw [rows]; simp
    exact List.any_eq_true.mpr ⟨equation, (List.mem_filter.mp present).1, (List.mem_filter.mp present).2⟩
  · intro index bounded
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    exact raw index (by omega)
  · rw [captured]
    exact PureData.named_equation_clause L.runtime head equation (L.formals head) values rows arguments' distinct length
  · exact returned

/-- **A call at evaluated arguments** behaves like the call at their values. -/
theorem capture (checked : L.check = true) {head : String} (ready : L.headReady head = true)
    (caller : Subst) (before after : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = (L.formals head).length) (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns L.runtime [] before (.expression (.symbol head :: values)) after answer) :
    PureReturns L.runtime caller before (.expression (.symbol head :: arguments)) after answer := by
  obtain ⟨equation, found⟩ : ∃ equation, L.equationOf head = some equation := by
    cases found : L.equationOf head with
    | none => simp [headReady, found] at ready
    | some equation => exact ⟨equation, rfl⟩
  obtain ⟨rows, _, _, ordinary, notIO, notNative, raw⟩ := defined_parts checked found ready
  have present : equation ∈ L.runtime.equations.filter (·.head == head) := by rw [rows]; simp
  apply PureData.raw_capture_returns L.runtime [] caller before after head values arguments answer
  · have found := List.mem_filter.mp present
    simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact Or.inr ⟨equation, found.1, by simpa using found.2⟩
  · intro index bounded
    exact raw index (by omega)
  · intro special
    have : specialForms.contains head = true := by simpa [specialForms] using special
    rw [this] at ordinary
    cases ordinary
  · have unchanged : values.map (applySubst []) = values := by
      have identity : applySubst [] = id := by
        funext value
        exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
      simp only [identity, List.map_id]
    rw [unchanged, captured]
  · exact returned

/-- Unfold a small library's owned body while executing directly in an agreeing target program. -/
theorem call_in {allowed : String → Bool} {program : Program}
    (checked : L.check = true) (agreement : ProgramAgreementOn allowed L.runtime program)
    {head : String} (supported : allowed head = true) (ready : L.headReady head = true)
    (caller : Subst) (before after : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = (L.formals head).length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program (bind (L.formals head) values) before (L.body head) after answer) :
    PureReturns program caller before (.expression (.symbol head :: arguments)) after answer := by
  obtain ⟨equation, found⟩ : ∃ equation, L.equationOf head = some equation := by
    cases found : L.equationOf head with
    | none => simp [headReady, found] at ready
    | some equation => exact ⟨equation, rfl⟩
  obtain ⟨rows, arguments', distinct, ordinary, notIO, notNative, raw⟩ := defined_parts checked found ready
  have bodyEq : L.body head = equation.body := by simp [body, found]
  rw [bodyEq] at returned
  apply PureData.raw_authored_call_return program caller (bind (L.formals head) values) before after
    head arguments equation.body answer
  · intro special
    have : specialForms.contains head = true := by simpa [specialForms] using special
    rw [this] at ordinary
    cases ordinary
  · exact notIO
  · exact notNative
  · rw [← agreement.dispatch head supported]
    have present : equation ∈ L.runtime.equations.filter (·.head == head) := by rw [rows]; simp
    exact List.any_eq_true.mpr ⟨equation, (List.mem_filter.mp present).1, (List.mem_filter.mp present).2⟩
  · intro index bounded
    rw [← agreement.demand head index supported]
    have same : arguments.length = values.length := by simpa using congrArg List.length captured
    exact raw index (by omega)
  · rw [captured]
    have sourceSelected := PureData.named_equation_clause L.runtime head equation (L.formals head) values
      rows arguments' distinct length
    apply PureData.selected_clause_agreement agreement supported
    simpa only [bind] using sourceSelected
  · exact returned

/-- Reuse an owned raw call under equal capture in the target program, without scanning its rows. -/
theorem capture_in {allowed : String → Bool} {program : Program}
    (checked : L.check = true) (agreement : ProgramAgreementOn allowed L.runtime program)
    {head : String} (supported : allowed head = true) (ready : L.headReady head = true)
    (caller : Subst) (before after : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = (L.formals head).length)
    (captured : arguments.map (applySubst caller) = values)
    (returned : PureReturns program [] before (.expression (.symbol head :: values)) after answer) :
    PureReturns program caller before (.expression (.symbol head :: arguments)) after answer := by
  obtain ⟨equation, found⟩ : ∃ equation, L.equationOf head = some equation := by
    cases found : L.equationOf head with
    | none => simp [headReady, found] at ready
    | some equation => exact ⟨equation, rfl⟩
  obtain ⟨rows, _, _, ordinary, notIO, notNative, raw⟩ := defined_parts checked found ready
  apply PureData.raw_capture_returns program [] caller before after head values arguments answer
  · rw [← agreement.dispatch head supported]
    have present : equation ∈ L.runtime.equations.filter (·.head == head) := by rw [rows]; simp
    simp only [notIO, notNative, Bool.false_or]
    exact List.any_eq_true.mpr ⟨equation, (List.mem_filter.mp present).1, (List.mem_filter.mp present).2⟩
  · intro index bounded
    rw [← agreement.demand head index supported]
    exact raw index (by omega)
  · intro special
    have : specialForms.contains head = true := by simpa [specialForms] using special
    rw [this] at ordinary
    cases ordinary
  · have unchanged : values.map (applySubst []) = values := by
      have identity : applySubst [] = id := by
        funext value
        exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
      simp only [identity, List.map_id]
    rw [unchanged, captured]
  · exact returned

end Library

/-- Transport a constructor template using only dispatch agreement for its literal heads.
Captured variables retain arbitrary values; their payloads are never checked as code. -/
theorem template_in_program {allowed : String → Bool} {first second : Program}
    (agreement : ProgramAgreementOn allowed first second) {code : Atom}
    (template : PureData.Template first code) (supported : codeWithin allowed code = true) :
    PureData.Template second code := by
  induction template with
  | captured name => exact .captured name
  | grounded value => exact .grounded value
  | symbol name => exact .symbol name
  | constructor head arguments inert ordinary children ih =>
      simp only [codeWithin, expressionHeadWithin, Bool.and_eq_true,
        atomsWithin_eq_all, List.all_eq_true] at supported
      refine .constructor head arguments ?_ ordinary ?_
      · rw [← agreement.dispatch head supported.1.1.1]
        exact inert
      · intro child member
        exact ih child member (supported.2 child (List.mem_cons_of_mem _ member))

/-! ## Literal bodies -/

section Literal

open Lean Meta Elab Tactic

private def groundedToExpr : GroundedValue → Expr
  | .int value => mkApp (mkConst ``GroundedValue.int) (toExpr value)
  | .string value => mkApp (mkConst ``GroundedValue.string) (toExpr value)
  | .bool value => mkApp (mkConst ``GroundedValue.bool) (toExpr value)
  | .custom name value => mkApp2 (mkConst ``GroundedValue.custom) (toExpr name) (toExpr value)

/-- An atom as the Lean term that builds it. -/
partial def atomToExpr : Atom → Expr
  | .symbol value => mkApp (mkConst ``Atom.symbol) (toExpr value)
  | .var value => mkApp (mkConst ``Atom.var) (toExpr value)
  | .grounded value => mkApp (mkConst ``Atom.grounded) (groundedToExpr value)
  | .expression values =>
      let elements := values.map atomToExpr
      mkApp (mkConst ``Atom.expression)
        (elements.foldr (fun element rest => mkApp3 (mkConst ``List.cons [.zero]) (mkConst ``Atom) element rest)
          (mkApp (mkConst ``List.nil [.zero]) (mkConst ``Atom)))

/-- Rewrite one closed subterm by its value, read by evaluation and checked by the kernel. -/
def rewriteByValue (application literal : Expr) : TacticM Unit := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let equality ← mkEq application literal
  let decidable ← synthInstance (mkApp (mkConst ``Decidable) equality)
  let proof := mkApp3 (mkConst ``of_decide_eq_true) equality decidable
    (mkApp2 (mkConst ``Eq.refl [.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  let rewritten ← (← getMainGoal).rewrite target proof
  let next ← (← getMainGoal).replaceTargetEq rewritten.eNew rewritten.eqProof
  replaceMainGoal (next :: rewritten.mvarIds)

/-- Replace every closed `Library.body L head` and `Library.formals L head` in the goal by its
literal value, read by evaluating the quoted source and checked by the kernel. -/
elab "metta_literal" : tactic => do
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 64 do
    changed := false
    rounds := rounds + 1
    let target ← instantiateMVars (← getMainTarget)
    let closed := fun (expression : Expr) => !expression.hasFVar && !expression.hasMVar
    if let some application := target.find? fun expression =>
        expression.isAppOfArity ``Library.body 2 && closed expression then
      let atom ← unsafe evalExpr Atom (mkConst ``Atom) application
      rewriteByValue application (atomToExpr atom)
      changed := true
    else if let some application := target.find? fun expression =>
        expression.isAppOfArity ``Library.formals 2 && closed expression then
      let names ← unsafe evalExpr (List String) (mkApp (mkConst ``List [.zero]) (mkConst ``String)) application
      rewriteByValue application (toExpr names)
      changed := true

end Literal

end Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

#print axioms Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.Library.call_in
#print axioms Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.Library.capture_in
#print axioms Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.template_in_program
