import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables.Views
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Laws

/-!
# A call through a function variable: the clauses

A tuple whose head is not a symbol, `($f a₁ … aₙ)`, names no function where it is written, so no
declaration and no strategy says there how its arguments are passed. `Clause` lists the readings; the
elaboration `elabH` is `Elaboration.elabText` on the readings that keep a tuple's elements, with the
clause as a parameter.

* `Clause.asWritten`: the tuple is called as it stands, its elements held text. This is the clause of
  `Elaboration.elabText`: `elabH_eq` (the two elaborations are equal on every text under this clause).
* `Clause.static pass`: the head is a position that wants a value (a variable is taken by the way it was
  passed, a call is computed at its own arrow), and each argument is passed as `pass` decides from the
  text alone: evaluated at its own arrow, or as written.
  * `Clause.byValue`: every argument evaluated (a `hold` mark still decides by itself).
  * `Clause.declared holds`: an argument is held when the type declared for the head variable holds
    that parameter, and evaluated otherwise.
* `Clause.atRunTime`: the tuple is run as text when the alternative reaches it; the program's reading of
  text as code then consults the declarations of the head the store has bound.

**Laws.**
* Every clause agrees with `Elaboration.elabText` on text in which no tuple with a head that is not a
  symbol stands at a position the reading reaches (`elabH_eq`): the clauses differ on such tuples only.
* A static clause runs no computed value (`valuesH_never_run`); the run-time clause runs the whole tuple
  (`atRunTime_reruns`).
* Under a static clause, a call through a variable that holds a value has the code of the direct call of
  a function taking its arguments the way the clause passes them, with the variable in place of the
  function's symbol (`naming`); for the clause by value, those are the undeclared functions of a
  reading by value (`passOf_byValue`). A function that holds a parameter is outside this law: the
  control is `ExampleHolding`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Elaboration

/-! ## The clauses -/

/-- **How a tuple whose head is not a symbol is read** at a position that wants a value. -/
inductive Clause where
  /-- The tuple is called as it stands: its elements are held text. -/
  | asWritten
  /-- The tuple is run as text when the alternative reaches it. -/
  | atRunTime
  /-- The head is a position that wants a value; each argument is passed as decided where the tuple is
  written, from the head's reading, the argument's index and its reading. -/
  | static (pass : HView → ℕ → HView → Pass)

/-- A `hold` mark decides by itself; any other argument is evaluated at its own arrow. -/
def passByValue : HView → Pass
  | .holdMark _ u => .text u
  | _ => .evaluate none

/-- **By value**: every argument of a tuple whose head is not a symbol is evaluated at its own arrow. -/
def Clause.byValue : Clause := .static fun _ _ a => passByValue a

/-- **Declared**: an argument is held when the type declared for the head variable holds that parameter
(`holds x i`), and evaluated otherwise; a mark decides by itself. -/
def Clause.declared (holds : Name mkeys → ℕ → Bool) : Clause :=
  .static fun head i a =>
    match a with
    | .holdMark _ u => .text u
    | .runMark _ _ => .evaluate none
    | _ =>
      match head with
      | .var _ x => if holds x i then .text a.orig else .evaluate none
      | _ => .evaluate none

/-- A head taken as it is written: a variable that holds a value, held text, or text that is no
position. Any other head is computed first, at its own arrow. -/
def headDatum (modes : Name mkeys → VarMode) : HView → Option MData
  | .var o x => if modes x = .value then some o else none
  | .holdMark _ u => some u
  | .inert o => some o
  | .symbol o _ => some o
  | _ => none

/-! ## The elaboration with the clause as a parameter -/

variable (cl : Clause) (π : Params) (decls : List Decl)

mutual
/-- **Text at a position that wants a value**, under the clause. Every case but the tuple whose head is
not a symbol is `Elaboration.elabText`'s. -/
def elabH (modes : Name mkeys → VarMode) (path : List ℕ) : HView → Comp mkeys [] () MTy
  | .holdMark _ u => .ret u
  | .runMark _ inner =>
      match inner with
      | .var o _ => .run o
      | other => elabH modes path other
  | .var o x => varAt π (modes x) o
  | .symbol o _ => .apply o
  | .call _ f args =>
      elabArgsH (fun i a => passOf π decls f i a.forget) (finish decls f) modes path 0 args []
  | .inert o => .ret o
  | .other o [] => .apply o
  | .other o (head :: args) =>
      match cl with
      | .asWritten => .apply o
      | .atRunTime => .run o
      | .static pass =>
          match headDatum modes head with
          | some d =>
              elabArgsH (pass head) (fun done => .apply (tuple (d :: done))) modes path 0 args []
          | none =>
              .let_ (path ++ [args.length]) (slot (path ++ [args.length]))
                (elabH modes (path ++ [args.length]) head)
                (elabArgsH (pass head) (fun done => .apply (tuple (slot (path ++ [args.length]) :: done)))
                  modes path 0 args [])

/-- The arguments of a call, left to right, each passed as `pass` says; `done` holds the passed data so
far, newest first; `fin` makes the call of the passed data. -/
def elabArgsH (pass : ℕ → HView → Pass) (fin : List MData → Comp mkeys [] () MTy)
    (modes : Name mkeys → VarMode) (path : List ℕ) (i : ℕ) :
    List HView → List MData → Comp mkeys [] () MTy
  | [], done => fin done.reverse
  | a :: rest, done =>
      match pass i a with
      | .text u => elabArgsH pass fin modes path (i + 1) rest (u :: done)
      | .byName => elabArgsH pass fin modes path (i + 1) rest (a.orig :: done)
      | .evaluate none =>
          .let_ (path ++ [i]) (slot (path ++ [i])) (elabH modes (path ++ [i]) a)
            (elabArgsH pass fin modes path (i + 1) rest (slot (path ++ [i]) :: done))
      | .evaluate (some T) =>
          .let_ (path ++ [i]) (slot (path ++ [i])) (.check T (elabH modes (path ++ [i]) a))
            (elabArgsH pass fin modes path (i + 1) rest (slot (path ++ [i]) :: done))
      | .byNeed =>
          .delay (path ++ [i]) (slot (path ++ [i])) (elabH modes (path ++ [i]) a)
            (elabArgsH pass fin modes path (i + 1) rest (slot (path ++ [i]) :: done))
end

/-- Elaborate a surface computation under the clause; let-bound names are values. -/
def elabCompH (modes : Name mkeys → VarMode) (path : List ℕ) : SComp → Comp mkeys [] () MTy
  | .text t => elabH cl π decls modes path (hview t)
  | .let_ s p c k => .let_ s p (elabCompH modes (path ++ [0]) c) (elabCompH modes (path ++ [1]) k)
  | .choice c d => .choice (elabCompH modes (path ++ [0]) c) (elabCompH modes (path ++ [1]) d)
  | .fail => .fail
  | .query sp p k => .query sp p (elabCompH modes (path ++ [0]) k)
  | .add sp t k => .add sp t (elabCompH modes (path ++ [0]) k)
  | .remove sp t k => .remove sp t (elabCompH modes (path ++ [0]) k)
  | .new s x k => .new s x (elabCompH modes (path ++ [0]) k)

/-- The body of an equation under the clause (`Elaboration.elabBody` with `elabH`). -/
def elabBodyH (e : SEquation) : Comp mkeys [] () MTy :=
  match e.body with
  | .text t =>
      match hview t with
      | .holdMark _ u => .ret u
      | .runMark _ inner => elabH cl π decls (paramModes π decls e) (1 :: e.site) (.runMark t inner)
      | v =>
          match declOf decls e.head with
          | some d => if d.result.held && !π.heldResultComputes then .ret t
              else elabH cl π decls (paramModes π decls e) (1 :: e.site) v
          | none => elabH cl π decls (paramModes π decls e) (1 :: e.site) v
  | b => elabCompH cl π decls (paramModes π decls e) (1 :: e.site) b

/-- An elaborated equation, under the clause. -/
def elabEquationH (e : SEquation) : Equation mkeys [] () MTy :=
  ⟨e.site, tuple (sym e.head :: e.params), elabBodyH cl π decls e⟩

/-- **The elaborated program under the clause**: its equations, and the reading of text as code at run
time, which is the elaboration's own (`Elaboration.reading`). -/
def elaborateH (P : SProgram) : Program mkeys [] () MTy :=
  ⟨P.equations.map (elabEquationH cl π P.decls), reading π P.decls⟩

/-- A query under the clause: elaborated at the sites below `[3]`, its variables values. -/
def elabQueryH (P : SProgram) (q : SComp) : Comp mkeys [] () MTy :=
  elabCompH cl π P.decls (fun _ => .value) [3] q

/-! ## The clauses differ only on tuples whose head is not a symbol -/

/-- No tuple with a head that is not a symbol stands at a position the reading reaches. -/
def SymbolHeaded : HView → Prop
  | .holdMark _ _ => True
  | .runMark _ inner => SymbolHeaded inner
  | .var _ _ => True
  | .symbol _ _ => True
  | .call _ _ args => SymbolHeadedArgs args
  | .inert _ => True
  | .other _ [] => True
  | .other _ (_ :: _) => False
where
  /-- Every argument is so. -/
  SymbolHeadedArgs : List HView → Prop
    | [] => True
    | a :: rest => SymbolHeaded a ∧ SymbolHeadedArgs rest

mutual
/-- **The elaboration under the clause is `Elaboration.elabText`** under the clause that calls the tuple
as it stands, on every text; and under every clause, on text in which no tuple with a head that is not a
symbol stands at a position the reading reaches. -/
theorem elabH_eq (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ v : HView, cl = .asWritten ∨ SymbolHeaded v →
      elabH cl π decls modes path v = elabText π decls modes path v.forget
  | .holdMark _ _, _ => rfl
  | .runMark _ inner, agree => by
      cases inner with
      | var o x => rfl
      | holdMark o u => rfl
      | runMark o i => exact elabH_eq modes path (.runMark o i) agree
      | symbol o f => rfl
      | call o f args => exact elabH_eq modes path (.call o f args) agree
      | inert o => rfl
      | other o elements => exact elabH_eq modes path (.other o elements) agree
  | .var _ _, _ => rfl
  | .symbol _ _, _ => rfl
  | .call _ f args, agree => by
      simp only [elabH, HView.forget, elabText]
      exact elabArgsH_eq modes path f 0 args [] agree
  | .inert _, _ => rfl
  | .other _ [], _ => rfl
  | .other _ (_ :: _), agree => by
      rcases agree with rfl | none
      · rfl
      · exact absurd none (by simp [SymbolHeaded])

theorem elabArgsH_eq (modes : Name mkeys → VarMode) (path : List ℕ) (f : String) :
    ∀ (i : ℕ) (args : List HView) (done : List MData),
      cl = .asWritten ∨ SymbolHeaded.SymbolHeadedArgs args →
      elabArgsH cl π decls (fun i a => passOf π decls f i a.forget) (finish decls f) modes path i args done =
        elabArgs π decls modes path f i (HView.forget.forgetAll args) done
  | _, [], _, _ => rfl
  | i, a :: rest, done, agree => by
      have first := elabH_eq modes (path ++ [i]) a (agree.imp id And.left)
      have others := fun done' => elabArgsH_eq modes path f (i + 1) rest done' (agree.imp id And.right)
      cases passed : passOf π decls f i a.forget with
      | text u => simp only [elabArgsH, HView.forget.forgetAll, elabArgs, passed, others]
      | evaluate check =>
          cases check with
          | none => simp only [elabArgsH, HView.forget.forgetAll, elabArgs, passed, others, first]
          | some T => simp only [elabArgsH, HView.forget.forgetAll, elabArgs, passed, others, first]
      | byName =>
          simp only [elabArgsH, HView.forget.forgetAll, elabArgs, passed, others, HView.forget_orig]
      | byNeed => simp only [elabArgsH, HView.forget.forgetAll, elabArgs, passed, others, first]
end

/-- Under the clause that calls the tuple as it stands, the elaboration is `Elaboration.elabText`. -/
theorem elabH_asWritten (modes : Name mkeys → VarMode) (path : List ℕ) (v : HView) :
    elabH .asWritten π decls modes path v = elabText π decls modes path v.forget :=
  elabH_eq .asWritten π decls modes path v (.inl rfl)

/-- **Under the clause that calls the tuple as it stands, the elaborated equations are the
elaboration's.** -/
theorem elabEquationH_asWritten (e : SEquation) :
    elabEquationH .asWritten π decls e = elabEquation π decls e := by
  unfold elabEquationH elabEquation elabBodyH elabBody
  congr 1
  rcases e with ⟨site, head, params, body⟩
  cases body with
  | text t =>
      dsimp only
      rw [← forget_hview t]
      cases hview t with
      | holdMark o u => rfl
      | runMark o inner =>
          exact elabH_eq .asWritten π decls _ _ (.runMark t inner) (.inl rfl)
      | var o x => simp only [elabH_asWritten, HView.forget]; rfl
      | symbol o f => simp only [elabH_asWritten, HView.forget]; rfl
      | call o f args => simp only [elabH_asWritten, HView.forget]; rfl
      | inert o => simp only [elabH_asWritten, HView.forget]; rfl
      | other o elements => simp only [elabH_asWritten, HView.forget]; rfl
  | let_ s p c k => exact elabCompH_asWritten _ _ _
  | choice c d => exact elabCompH_asWritten _ _ _
  | fail => rfl
  | query sp p k => exact elabCompH_asWritten _ _ _
  | add sp t k => exact elabCompH_asWritten _ _ _
  | remove sp t k => exact elabCompH_asWritten _ _ _
  | new s x k => exact elabCompH_asWritten _ _ _
where
  /-- Surface computations, likewise. -/
  elabCompH_asWritten (modes : Name mkeys → VarMode) : (path : List ℕ) → (c : SComp) →
      elabCompH .asWritten π decls modes path c = elabComp π decls modes path c
    | path, .text t => by
        simp only [elabCompH, elabComp]
        rw [← forget_hview t]
        exact elabH_eq .asWritten π decls modes path (hview t) (.inl rfl)
    | path, .let_ s p c k => by
        simp only [elabCompH, elabComp, elabCompH_asWritten modes (path ++ [0]) c,
          elabCompH_asWritten modes (path ++ [1]) k]
    | path, .choice c d => by
        simp only [elabCompH, elabComp, elabCompH_asWritten modes (path ++ [0]) c,
          elabCompH_asWritten modes (path ++ [1]) d]
    | _, .fail => rfl
    | path, .query sp p k => by
        simp only [elabCompH, elabComp, elabCompH_asWritten modes (path ++ [0]) k]
    | path, .add sp t k => by
        simp only [elabCompH, elabComp, elabCompH_asWritten modes (path ++ [0]) k]
    | path, .remove sp t k => by
        simp only [elabCompH, elabComp, elabCompH_asWritten modes (path ++ [0]) k]
    | path, .new s x k => by
        simp only [elabCompH, elabComp, elabCompH_asWritten modes (path ++ [0]) k]

/-- **Under the clause that calls the tuple as it stands, the elaborated program is the
elaboration's.** -/
theorem elaborateH_asWritten (P : SProgram) : elaborateH .asWritten π P = elaborate π P := by
  simp only [elaborateH, elaborate]
  congr 1
  exact List.map_congr_left fun e _ => elabEquationH_asWritten π P.decls e

/-! ## A computed value never runs again under a static clause -/

/-- Text with no explicit `run` mark, all of whose variables hold computed values. -/
def ValueTextH (modes : Name mkeys → VarMode) : HView → Prop
  | .holdMark _ _ => True
  | .runMark _ _ => False
  | .var _ x => modes x = .value
  | .symbol _ _ => True
  | .call _ _ args => ValueArgsH modes args
  | .inert _ => True
  | .other _ elements => ValueArgsH modes elements
where
  /-- Every element is so. -/
  ValueArgsH (modes : Name mkeys → VarMode) : List HView → Prop
    | [] => True
    | a :: rest => ValueTextH modes a ∧ ValueArgsH modes rest

theorem finish_runs_nothing (f : String) (done : List MData) : Laws.reruns (finish decls f done) = [] := by
  simp only [finish]
  split
  · split <;> rfl
  · rfl

mutual
/-- **A computed value never runs again** under a clause that is not the run-time one: the elaboration
of text without explicit `run` marks, whose variables hold computed values, runs nothing and forces
nothing. -/
theorem valuesH_never_run (notRun : cl ≠ .atRunTime) (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ v : HView, ValueTextH modes v → Laws.reruns (elabH cl π decls modes path v) = []
  | .holdMark _ _, _ => rfl
  | .runMark _ _, valued => absurd valued (by simp [ValueTextH])
  | .var o x, valued => by
      simp only [ValueTextH] at valued
      simp only [elabH, varAt, valued]
      rfl
  | .symbol _ _, _ => rfl
  | .call _ f args, valued => by
      simp only [elabH]
      exact valueArgsH_never_run notRun _ _ (finish_runs_nothing decls f) modes path 0 args [] valued
  | .inert _, _ => rfl
  | .other _ [], _ => rfl
  | .other o (head :: args), valued => by
      have parts : ValueTextH modes head ∧ ValueTextH.ValueArgsH modes args := valued
      have atHead := valuesH_never_run notRun modes (path ++ [args.length]) head parts.1
      have atArgs := fun (pass : ℕ → HView → Pass) (fin : List MData → Comp mkeys [] () MTy)
          (quiet : ∀ done, Laws.reruns (fin done) = []) =>
        valueArgsH_never_run notRun pass fin quiet modes path 0 args [] parts.2
      cases cl with
      | asWritten => rfl
      | atRunTime => exact absurd rfl notRun
      | static pass =>
          simp only [elabH]
          split
          · exact atArgs _ _ (fun _ => rfl)
          · simp only [Laws.reruns]
            rw [atHead, atArgs (pass head)
              (fun done => Comp.apply (tuple (slot (path ++ [args.length]) :: done))) (fun _ => rfl)]
            rfl

theorem valueArgsH_never_run (notRun : cl ≠ .atRunTime) (pass : ℕ → HView → Pass)
    (fin : List MData → Comp mkeys [] () MTy) (quiet : ∀ done, Laws.reruns (fin done) = [])
    (modes : Name mkeys → VarMode) (path : List ℕ) :
    ∀ (i : ℕ) (args : List HView) (done : List MData), ValueTextH.ValueArgsH modes args →
      Laws.reruns (elabArgsH cl π decls pass fin modes path i args done) = []
  | _, [], done, _ => by
      simp only [elabArgsH]
      exact quiet _
  | i, a :: rest, done, ⟨first, others⟩ => by
      simp only [elabArgsH]
      split
      · exact valueArgsH_never_run notRun pass fin quiet modes path (i + 1) rest _ others
      · exact valueArgsH_never_run notRun pass fin quiet modes path (i + 1) rest _ others
      · simp only [Laws.reruns, valuesH_never_run notRun modes (path ++ [i]) a first,
          valueArgsH_never_run notRun pass fin quiet modes path (i + 1) rest _ others, List.append_nil]
      · simp only [Laws.reruns, valuesH_never_run notRun modes (path ++ [i]) a first,
          valueArgsH_never_run notRun pass fin quiet modes path (i + 1) rest _ others, List.append_nil]
      · simp only [Laws.reruns, valuesH_never_run notRun modes (path ++ [i]) a first,
          valueArgsH_never_run notRun pass fin quiet modes path (i + 1) rest _ others, List.append_nil]
end

/-- **The run-time clause runs the whole tuple**, whatever its variables hold. -/
theorem atRunTime_reruns (modes : Name mkeys → VarMode) (path : List ℕ) (o : MData) (head : HView)
    (args : List HView) :
    Laws.reruns (elabH .atRunTime π decls modes path (.other o (head :: args))) = [o] := rfl

/-! ## Naming a function -/

/-- **A call through a variable that holds a value**, under a static clause: the arguments passed as the
clause says, then the call of the tuple with the variable at its head. -/
theorem through_value_variable (pass : HView → ℕ → HView → Pass) (modes : Name mkeys → VarMode)
    (path : List ℕ) (o ho : MData) (x : Name mkeys) (args : List HView) (value : modes x = .value) :
    elabH (.static pass) π decls modes path (.other o (.var ho x :: args)) =
      elabArgsH (.static pass) π decls (pass (.var ho x)) (fun done => .apply (tuple (ho :: done)))
        modes path 0 args [] := by
  simp only [elabH, headDatum, value, ↓reduceIte]

/-- **Naming a function does not change the code of its call**, when the function takes its arguments
the way the clause passes them and its result is not checked: the call through a variable that holds a
value and the direct call are one code, at the variable and at the function's symbol. -/
theorem naming (pass : HView → ℕ → HView → Pass) (modes : Name mkeys → VarMode) (path : List ℕ)
    (o o' ho : MData) (x : Name mkeys) (f : String) (args : List HView) (value : modes x = .value)
    (same : ∀ i a, pass (.var ho x) i a = passOf π decls f i a.forget)
    (unchecked : finish decls f = fun done => .apply (tuple (sym f :: done))) :
    ∃ code : MData → Comp mkeys [] () MTy,
      elabH (.static pass) π decls modes path (.other o (.var ho x :: args)) = code ho ∧
        elabH (.static pass) π decls modes path (.call o' f args) = code (sym f) := by
  refine ⟨fun H => elabArgsH (.static pass) π decls (pass (.var ho x))
    (fun done => .apply (tuple (H :: done))) modes path 0 args [],
    through_value_variable π decls pass modes path o ho x args value, ?_⟩
  simp only [elabH, unchecked]
  congr 1
  funext i a
  exact (same i a).symm

/-- An undeclared function of a reading by value takes its arguments the way the clause by value passes
them. -/
theorem passOf_byValue (byValue : ∀ f i, π.strategy f i = .value) (f : String) (i : ℕ) :
    ∀ a : HView, passByValue a = passOf π [] f i a.forget
  | .holdMark _ _ => rfl
  | .runMark _ _ => rfl
  | .var _ _ => by simp [passByValue, HView.forget, passOf, declOf, byValue]
  | .symbol _ _ => by simp [passByValue, HView.forget, passOf, declOf, byValue]
  | .call _ _ _ => by simp [passByValue, HView.forget, passOf, declOf, byValue]
  | .inert _ => by simp [passByValue, HView.forget, passOf, declOf, byValue]
  | .other _ _ => by simp [passByValue, HView.forget, passOf, declOf, byValue]

#print axioms elabH_eq
#print axioms elabEquationH_asWritten
#print axioms elaborateH_asWritten
#print axioms valuesH_never_run
#print axioms atRunTime_reruns
#print axioms through_value_variable
#print axioms naming
#print axioms passOf_byValue

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.FunctionVariables
