import Mathlib.Data.List.Basic
import Mettapedia.GSLT.Core.Composition

/-!
# Compiling an inference-rule package to a register-machine program

The bytecode experiments derive *which rules exist* from an authored package,
but their instruction semantics are handwritten in C: the accompanying
"semantics" inventory declares judgment names (`step`, `encode`, `decode`,
`origin`, `refines`) and supplies no rules for any of them.  This module
supplies the missing content for the backward-via-forward Hilbert search
(Nil Geisweiller's `obfc`): the authored rule package, the machine IR, the
compiler between them, and the theorem that the compiled program *means* the
authored rules.

The two sides are written independently and in different styles:

* `applyRule` is **declarative** — it matches on the rule and states the
  resulting judgment directly, in the vocabulary of the object logic.
* `runBlock` is **operational** — it walks a flat instruction list through a
  register file, knowing nothing about axioms, implication, or proofs.

`run_compile_eq_applyRule` proves the two agree for every rule and state.
That is the authority direction: the register machine is a *realization* of
the authored package, not a second semantics.

Unification is a **parameter**, not an assumption.  Both sides receive the
same `unify`, so the theorem holds however unification behaves; unifier
correctness is a separate, orthogonal obligation and is deliberately not
laundered into this one.

Scope, stated honestly: this covers the rule → instruction-block compiler and
its meaning.  It does *not* cover the binary encoding/decoding, the search
schedule over the emitted states, or conformance of any particular existing
byte format to this IR — those remain open, and a concrete encoder claiming
to realize this IR would owe its own round-trip and conformance theorems.
-/

namespace Mettapedia.GSLT.LanguageDef.RuleMachineCompilation

/-! ## Object language -/

/-- Object types.  `imp` is the object implication `→`; `fn` is the machine's
pending-hypothesis arrow `->`, which is how a partially applied proof records
the hypotheses it still needs. -/
inductive Ty where
  | mvar : Nat → Ty
  | atom : String → Ty
  | imp : Ty → Ty → Ty
  | fn : Ty → Ty → Ty
  | neg : Ty → Ty
deriving DecidableEq, Repr

/-- Proof terms: the identity combinator, axiom constants, application of a
partial proof to an axiom, and the inverse-modus-ponens wrapper. -/
inductive Proof where
  | id : Proof
  | ax : String → Proof
  | app : Proof → Proof → Proof
  | inv : String → Proof → Proof
deriving DecidableEq, Repr

/-- A substitution as a total map on metavariable indices. -/
abbrev Subst := Nat → Option Ty

/-- Apply a substitution structurally. -/
def substTy (σ : Subst) : Ty → Ty
  | .mvar n => (σ n).getD (.mvar n)
  | .atom s => .atom s
  | .imp a b => .imp (substTy σ a) (substTy σ b)
  | .fn a b => .fn (substTy σ a) (substTy σ b)
  | .neg a => .neg (substTy σ a)

/-- The empty substitution acts as the identity: a rule that never unifies
leaves the types it moves untouched. -/
@[simp] theorem substTy_empty (t : Ty) : substTy (fun _ => none) t = t := by
  induction t with
  | mvar n => rfl
  | atom s => rfl
  | imp a b iha ihb => simp [substTy, iha, ihb]
  | fn a b iha ihb => simp [substTy, iha, ihb]
  | neg a iha => simp [substTy, iha]

/-- Shift every metavariable index, used to freshen an axiom schema before it
meets the current goal. -/
def shiftTy (k : Nat) : Ty → Ty
  | .mvar n => .mvar (n + k)
  | .atom s => .atom s
  | .imp a b => .imp (shiftTy k a) (shiftTy k b)
  | .fn a b => .fn (shiftTy k a) (shiftTy k b)
  | .neg a => .neg (shiftTy k a)

/-! ## The authored rule package -/

/-- The two admitted rule forms of the backward-via-forward package.  An
`axiomRule` discharges one pending hypothesis by matching it against the axiom's
schema; `inverseMP` introduces one, expanding the search backwards while the
chainer runs forwards. -/
inductive Rule where
  | axiomRule (id : String) (schema : Ty) (label : String)
  | inverseMP (id : String) (label : String)
deriving Repr

/-- Every rule carries its identity; compilation must preserve it. -/
def Rule.id : Rule → String
  | .axiomRule id _ _ => id
  | .inverseMP id _ => id

/-- An authored package is an ordered rule inventory. -/
structure Package where
  rules : List Rule
deriving Repr

/-- Nil Geisweiller's propositional Hilbert package with inverse modus ponens:
the sole semantic rule inventory of the backward-via-forward search. -/
def hilbertPackage : Package where
  rules :=
    [ .axiomRule "ax1" (.imp (.mvar 0) (.imp (.mvar 1) (.mvar 0))) "ax1"
    , .axiomRule "ax2"
        (.imp (.imp (.mvar 0) (.imp (.mvar 1) (.mvar 2)))
              (.imp (.imp (.mvar 0) (.mvar 1)) (.imp (.mvar 0) (.mvar 2))))
        "ax2"
    , .axiomRule "ax3"
        (.imp (.imp (.neg (.mvar 0)) (.neg (.mvar 1))) (.imp (.mvar 1) (.mvar 0)))
        "ax3"
    , .inverseMP "mpi" "mpi" ]

/-! ## Search state and the declarative meaning of a rule -/

/-- A search state: the type still to be discharged, the proof built so far,
the count of pending hypotheses, and the next unused metavariable index. -/
structure MState where
  ty : Ty
  proof : Proof
  hyps : Nat
  fresh : Nat
deriving DecidableEq, Repr

/-- **Declarative** meaning of applying a rule to a state.  Written in the
object logic's own vocabulary, with no registers and no instruction list. -/
def applyRule (unify : Ty → Ty → Option Subst) : Rule → MState → Option MState
  | .axiomRule _ schema label, s =>
      match s.ty with
      | .fn dom cod =>
          match unify dom (shiftTy s.fresh schema) with
          | some σ =>
              some { ty := substTy σ cod
                   , proof := .app s.proof (.ax label)
                   , hyps := s.hyps - 1
                   , fresh := s.fresh + 1 }
          | none => none
      | _ => none
  | .inverseMP _ label, s =>
      match s.ty with
      | .fn dom cod =>
          some { ty := .fn (.imp (.mvar s.fresh) dom) (.fn (.mvar s.fresh) cod)
               , proof := .inv label s.proof
               , hyps := s.hyps + 1
               , fresh := s.fresh + 1 }
      | _ => none

/-! ## The machine IR -/

abbrev Reg := Nat

/-- Machine instructions.  The instruction set knows about registers, types
and proof-term shape; it knows nothing about axioms or implication. -/
inductive Instr where
  | requireFun (dom cod : Reg)
  | template (dst : Reg)
  | unifyRegs (a b : Reg)
  | setType (src : Reg)
  | proofApply (label : String)
  | proofWrap (label : String)
  | freshMVar (dst : Reg)
  | makeImp (dst a b : Reg)
  | makeFun (dst a b : Reg)
  | hypDec
  | hypInc
  | emit
deriving DecidableEq, Repr

/-- A compiled rule: its preserved identity, its freshened schema (absent for
rules with no template), and its instruction block. -/
structure CompiledRule where
  id : String
  schema : Option Ty
  code : List Instr
deriving Repr

/-! ## The compiler -/

/-- Compile one authored rule to an instruction block. -/
def compileRule : Rule → CompiledRule
  | .axiomRule id schema label =>
      { id := id
      , schema := some schema
      , code :=
          [ .requireFun 0 1
          , .template 2
          , .unifyRegs 0 2
          , .setType 1
          , .proofApply label
          , .hypDec
          , .emit ] }
  | .inverseMP id label =>
      { id := id
      , schema := none
      , code :=
          [ .requireFun 0 1
          , .freshMVar 2
          , .makeImp 3 2 0
          , .makeFun 4 2 1
          , .makeFun 5 3 4
          , .setType 5
          , .proofWrap label
          , .hypInc
          , .emit ] }

/-- Compile a package, preserving authored order. -/
def compilePackage (p : Package) : List CompiledRule :=
  p.rules.map compileRule

/-! ## Operational semantics of a block -/

/-- Machine configuration: a register file, the state under construction, the
substitution accumulated by unification, and whether `emit` has fired. -/
structure Config where
  regs : Reg → Option Ty
  st : MState
  σ : Subst
  emitted : Bool

def Config.write (c : Config) (r : Reg) (t : Ty) : Config :=
  { c with regs := fun q => if q = r then some t else c.regs q }

/-- **Operational** execution of an instruction block.  Walks the list; every
instruction is interpreted only in terms of registers and the configuration. -/
def runBlock (unify : Ty → Ty → Option Subst) (schema : Option Ty) :
    List Instr → Config → Option Config
  | [], c => some c
  | .requireFun dom cod :: rest, c =>
      match c.st.ty with
      | .fn a b => runBlock unify schema rest ((c.write dom a).write cod b)
      | _ => none
  | .template dst :: rest, c =>
      match schema with
      | some t => runBlock unify schema rest (c.write dst (shiftTy c.st.fresh t))
      | none => none
  | .unifyRegs a b :: rest, c =>
      match c.regs a, c.regs b with
      | some ta, some tb =>
          match unify ta tb with
          | some σ => runBlock unify schema rest { c with σ := σ }
          | none => none
      | _, _ => none
  | .setType src :: rest, c =>
      match c.regs src with
      | some t => runBlock unify schema rest { c with st := { c.st with ty := substTy c.σ t } }
      | none => none
  | .proofApply label :: rest, c =>
      runBlock unify schema rest
        { c with st := { c.st with proof := .app c.st.proof (.ax label) } }
  | .proofWrap label :: rest, c =>
      runBlock unify schema rest
        { c with st := { c.st with proof := .inv label c.st.proof } }
  | .freshMVar dst :: rest, c =>
      runBlock unify schema rest (c.write dst (.mvar c.st.fresh))
  | .makeImp dst a b :: rest, c =>
      match c.regs a, c.regs b with
      | some ta, some tb => runBlock unify schema rest (c.write dst (.imp ta tb))
      | _, _ => none
  | .makeFun dst a b :: rest, c =>
      match c.regs a, c.regs b with
      | some ta, some tb => runBlock unify schema rest (c.write dst (.fn ta tb))
      | _, _ => none
  | .hypDec :: rest, c =>
      runBlock unify schema rest { c with st := { c.st with hyps := c.st.hyps - 1 } }
  | .hypInc :: rest, c =>
      runBlock unify schema rest { c with st := { c.st with hyps := c.st.hyps + 1 } }
  | .emit :: rest, c =>
      runBlock unify schema rest { c with emitted := true }

/-- Initial configuration for executing a block against a state. -/
def initConfig (s : MState) : Config :=
  { regs := fun _ => none, st := s, σ := fun _ => none, emitted := false }

/-- The state produced by running a compiled rule, with the fresh counter
advanced exactly once per rule application. -/
def runCompiled (unify : Ty → Ty → Option Subst) (cr : CompiledRule) (s : MState) :
    Option MState :=
  (runBlock unify cr.schema cr.code (initConfig s)).map
    (fun c => { c.st with fresh := s.fresh + 1 })

/-! ## The authority theorem -/

/-- **The compiled program means the authored rule.**  For every rule and
state, executing the generated instruction block through the register machine
produces exactly the state the declarative rule semantics specifies.  The
machine is therefore a realization of the authored package rather than an
independent semantics. -/
theorem run_compile_eq_applyRule (unify : Ty → Ty → Option Subst)
    (r : Rule) (s : MState) :
    runCompiled unify (compileRule r) s = applyRule unify r s := by
  cases r with
  | axiomRule id schema label =>
      cases hty : s.ty with
      | fn a b =>
          cases hu : unify a (shiftTy s.fresh schema) with
          | none => simp [runCompiled, compileRule, runBlock, initConfig,
              Config.write, applyRule, hty, hu]
          | some σ => simp [runCompiled, compileRule, runBlock, initConfig,
              Config.write, applyRule, hty, hu]
      | mvar n => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]
      | atom t => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]
      | imp a b => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]
      | neg a => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]
  | inverseMP id label =>
      cases hty : s.ty with
      | fn a b => simp [runCompiled, compileRule, runBlock, initConfig,
          Config.write, applyRule, hty, substTy]
      | mvar n => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]
      | atom t => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]
      | imp a b => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]
      | neg a => simp [runCompiled, compileRule, runBlock, initConfig, applyRule, hty]

/-! ## Certified realization interface -/

/-- One authored rule compiles to one register-machine block while preserving
its complete state-transformer observation.  The observation is intentionally
the whole partial transformer, not only success or rule identity. -/
def ruleRealization (unify : Ty → Ty → Option Subst) :
    Mettapedia.GSLT.SimpleRealization Rule CompiledRule
      (MState → Option MState) where
  compile := fun _ rule => compileRule rule
  observeSource := fun _ rule => applyRule unify rule
  observeArtifact := fun _ compiled => runCompiled unify compiled
  adequate := by
    intro _ rule
    funext state
    exact run_compile_eq_applyRule unify rule state

@[simp] theorem ruleRealization_compile
    (unify : Ty → Ty → Option Subst) (rule : Rule) :
    (ruleRealization unify).compile () rule = compileRule rule :=
  rfl

/-- Package compilation is the componentwise realization of every authored
rule, retaining authored order and the complete transformer for each block. -/
def packageRealization (unify : Ty → Ty → Option Subst) :
    Mettapedia.GSLT.SimpleRealization Package (List CompiledRule)
      (List (MState → Option MState)) where
  compile := fun _ package => compilePackage package
  observeSource := fun _ package => package.rules.map (applyRule unify)
  observeArtifact := fun _ compiled => compiled.map (runCompiled unify)
  adequate := by
    intro _ package
    simp only [compilePackage, List.map_map]
    apply List.map_congr_left
    intro rule _
    funext state
    exact run_compile_eq_applyRule unify rule state

@[simp] theorem packageRealization_compile
    (unify : Ty → Ty → Option Subst) (package : Package) :
    (packageRealization unify).compile () package = compilePackage package :=
  rfl

/-- Package-level corollary: every compiled rule of an authored package means
its source rule. -/
theorem runCompiled_mem_package (unify : Ty → Ty → Option Subst)
    (p : Package) (r : Rule) (_ : r ∈ p.rules) (s : MState) :
    runCompiled unify (compileRule r) s = applyRule unify r s :=
  run_compile_eq_applyRule unify r s

/-! ## Structural obligations the bytecode experiments declared but left open -/

/-- Rule identity survives compilation (`source-rule-single-authority`). -/
@[simp] theorem compileRule_id (r : Rule) : (compileRule r).id = r.id := by
  cases r <;> rfl

/-- Compilation preserves authored order and rule count. -/
theorem compilePackage_ids (p : Package) :
    (compilePackage p).map CompiledRule.id = p.rules.map Rule.id := by
  simp [compilePackage, List.map_map, Function.comp_def]

/-- Every compiled block ends in exactly one `emit`: a rule application
contributes one answer occurrence (`proof-occurrence-preservation`). -/
theorem compileRule_emit_count (r : Rule) :
    (compileRule r).code.count Instr.emit = 1 := by
  cases r <;> rfl

/-- A template instruction is generated exactly when the rule carries a
schema, so `template` can never read an absent schema. -/
theorem template_iff_schema (r : Rule) :
    (∃ d, Instr.template d ∈ (compileRule r).code) ↔ (compileRule r).schema.isSome := by
  cases r with
  | axiomRule id schema label =>
      exact ⟨fun _ => rfl, fun _ => ⟨2, by simp [compileRule]⟩⟩
  | inverseMP id label =>
      constructor
      · rintro ⟨d, hd⟩; simp [compileRule] at hd
      · intro h; simp [compileRule] at h

/-- Compilation is total on the authored fragment: every rule of the Hilbert
package compiles, and the emitted inventory has one block per source rule. -/
theorem hilbertPackage_compiles :
    (compilePackage hilbertPackage).length = hilbertPackage.rules.length := by
  simp [compilePackage]

/-! ## Witnesses that the correspondence is not vacuous

Both directions are exhibited on the authored package: a rule application that
succeeds and changes the state, and one that fails.  Without these the
agreement theorem could hold merely because both sides always return `none`. -/

/-- The trivial unifier used by the witnesses: it succeeds with the empty
substitution.  Unifier quality is orthogonal to the correspondence. -/
private def trivialUnify : Ty → Ty → Option Subst := fun _ _ => some (fun _ => none)

/-- A state with one pending hypothesis awaiting an implication. -/
private def startState : MState :=
  { ty := .fn (.atom "h") (.atom "goal"), proof := .id, hyps := 1, fresh := 0 }

/-- **Positive witness.**  Applying `ax1` discharges the hypothesis, extends
the proof term, and the compiled block computes exactly that state — so the
agreement theorem is not holding merely because both sides fail. -/
example :
    runCompiled trivialUnify (compileRule (Rule.axiomRule "ax1" (.mvar 0) "ax1"))
        startState
      = some { ty := .atom "goal", proof := .app .id (.ax "ax1"), hyps := 0
             , fresh := 1 } := by
  rfl

/-- **Positive witness, inverse modus ponens.**  The rule introduces a pending
hypothesis and wraps the proof term. -/
example :
    runCompiled trivialUnify (compileRule (Rule.inverseMP "mpi" "mpi")) startState
      = some { ty := .fn (.imp (.mvar 0) (.atom "h")) (.fn (.mvar 0) (.atom "goal"))
             , proof := .inv "mpi" .id, hyps := 2, fresh := 1 } := by
  rfl

/-- **Negative witness.**  A state whose type is not a pending-hypothesis
arrow admits no rule application, on either side of the correspondence. -/
example :
    runCompiled trivialUnify (compileRule (Rule.inverseMP "mpi" "mpi"))
        { startState with ty := .atom "done" } = none := by
  rfl

/-- **Negative witness, failed unification.**  When the unifier rejects, the
axiom rule produces no state. -/
example :
    runCompiled (fun _ _ => none)
        (compileRule (Rule.axiomRule "ax1" (.mvar 0) "ax1")) startState = none := by
  rfl


end Mettapedia.GSLT.LanguageDef.RuleMachineCompilation
