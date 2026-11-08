import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingContracts

/-!
# Controls for membership contracts as firings

A small declaration world: numbers, strings and booleans, each with its constructor rule; a nominal
fact that makes every value an `Atom`; and a type `Void` that nothing inhabits. `Atom` is the reserved
name: type helpers may not take it.

* **Proper parameters.** `(same 1 "s")` under `(: same (-> $a $a Bool))` is refused
  (`same_mixed_refused`), `(same 1 2)` is admitted (`same_numbers_admitted`). If helpers could take
  `Atom`, `Atom` would solve the shared parameter and `(same 1 "s")` would be admitted
  (`atom_solves_shared_parameter`).
* **An open argument** (`(same 1 X)`, `X` a program variable). The call is admitted while `X` is
  unbound (`open_pending`); its requirement waits in the knowledge, correlated with `1` through the
  shared parameter. Telling `X ≐ "s"` is then refused (`contradicting_refused`); telling `X ≐ 2` is
  admitted (`consistent_accepted`). Both are steps of one run (`lifecycle_run`).
* **What the runtime does not decide** (`void_trap`). For `(: absurd (-> Void Bool))` on an unbound
  `X`, the runtime's decided check accepts: the type equations of the residual formula are
  satisfiable and the membership request waits. The step refuses: no binding can ever meet it.
* **A guard at a shared parameter** (`guard_refuses_shared_parameter`). Asking `1 ∈ $a` and `2 ∈ $a` as
  guards refuses `(same 1 2)`, because some solution gives `$a` the type `String`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingContractsControls

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Logic.ConstraintTypes renaming Tree → VTree
open Mettapedia.Logic.ConstraintTypes.SymbolicTypes (Expr Closed)
open TypingFirings

inductive Sym where
  | number (n : Nat)
  | text (s : String)
  | bool (b : Bool)

def valueArity : Sym → Nat := fun _ => 0

inductive Name where
  | number | string | bool | atom | void
  deriving DecidableEq

def typeArity : Empty → Nat := fun e => e.elim

abbrev Ty := Closed Name Empty typeArity
abbrev Value := VTree Sym valueArity

def sortOf : Sym → Name
  | .number _ => .number
  | .text _ => .string
  | .bool _ => .bool

def leaf (s : Sym) : Value := .node s Fin.elim0

def rules (s : Sym) : List (ConstructorTyping.Rule Empty Name Empty typeArity (valueArity s)) :=
  [⟨Fin.elim0, .closed (sortOf s)⟩]

/-- Every value is an `Atom`. -/
def atomFact : DeclarationTyping.Fact Unit Empty Name Empty Sym typeArity valueArity where
  pattern := .var ()
  type := .closed .atom

def decls : DeclarationTyping.Declarations Unit Unit Empty Name Empty Sym typeArity valueArity where
  childContext _ _ _ := ()
  constructors _ := rules
  facts _ := [atomFact]

theorem leaf_typed (s : Sym) : DeclarationTyping.HasType decls () (leaf s) (.closed (sortOf s)) :=
  DeclarationTyping.HasType.constructor (declarations := decls) (context := ()) (symbol := s)
    (children := Fin.elim0) ⟨Fin.elim0, .closed (sortOf s)⟩ (List.mem_singleton.mpr rfl) Empty.elim
    (fun i => i.elim0)

theorem ofTree_typed (ρ : Nat → Value) (s : Sym) :
    DeclarationTyping.HasType decls () ((ofTree (leaf s)).evaluate ρ) (.closed (sortOf s)) := by
  rw [evaluate_ofTree]
  exact leaf_typed s

theorem atom_typed (v : Value) : DeclarationTyping.HasType decls () v (.closed .atom) :=
  .nominal atomFact (List.mem_singleton.mpr rfl) (fun _ => v) rfl Empty.elim
    (fun _ present => by cases present)

/-- A value has its own sort and `Atom`, and nothing else. -/
theorem types_of_node (s : Sym) (children : Fin (valueArity s) → Value) (τ : Ty)
    (typed : DeclarationTyping.HasType decls () (.node s children) τ) :
    τ = .closed (sortOf s) ∨ τ = .closed .atom := by
  rcases (DeclarationTyping.hasType_node_iff decls () s children τ).1 typed with
    ⟨rule, present, _, rfl, _⟩ | ⟨fact, present, _, _, _, _, rfl⟩
  · have same : rule = ⟨Fin.elim0, .closed (sortOf s)⟩ := List.mem_singleton.mp present
    subst same
    exact .inl rfl
  · have same : fact = atomFact := List.mem_singleton.mp present
    subst same
    exact .inr rfl

theorem void_empty (v : Value) : ¬ DeclarationTyping.HasType decls () v (.closed .void) := by
  intro typed
  cases v with
  | node s children =>
      rcases types_of_node s children _ typed with same | same <;>
        · simp only [TypeExpr.closed.injEq] at same
          cases s <;> cases same

/-! ## The term language and the step -/

/-- `Atom` is reserved: helpers may not take it. -/
def isAtom (q : Name) : Prop := q = .atom

/-- No reserved names. -/
def nothing (_ : Name) : Prop := False

abbrev T := Term Unit Nat Nat Name Empty Sym typeArity valueArity
abbrev Pt (reserved : Name → Prop) := Point Nat Nat Name Empty Sym typeArity valueArity reserved

def label : Nat → T := fun _ => .yes

def start : Configuration T Nat := ⟨[], ∅⟩

theorem proper_closed (reserved : Name → Prop) {q : Name} (allowed : ¬ reserved q) :
    Proper reserved (.closed q : Ty) := by
  intro q' written
  simp only [names, List.mem_singleton] at written
  subst written
  exact allowed

theorem atom_improper (θ : Ty) (proper : Proper isAtom θ) : θ ≠ .closed .atom := by
  rintro rfl
  exact proper .atom (List.mem_singleton.mpr rfl) rfl

/-- A point giving every program variable `v` and every helper `τ`. -/
def pointAt (reserved : Name → Prop) (v : Value) (q : Name) (allowed : ¬ reserved q) : Pt reserved :=
  ⟨fun _ => v, fun _ => .closed q, fun _ => proper_closed reserved allowed⟩

def seed : Pt isAtom := pointAt isAtom (leaf (.number 0)) .number (by simp [isAtom])

theorem holds_start (reserved : Name → Prop) (ρ : Pt reserved) :
    Holds decls reserved ρ start.equations :=
  fun _ member => by cases member

theorem start_solvable (reserved : Name → Prop) (ρ : Pt reserved) :
    ∃ ρ : Pt reserved, Holds decls reserved ρ start.equations :=
  ⟨ρ, holds_start reserved ρ⟩

/-- The one helper the calls below use. -/
def ν : Unit → Nat := fun _ => 0

theorem ν_injective : Function.Injective ν := fun _ _ _ => rfl

/-! ## Proper parameters -/

/-- `(: same (-> $a $a Bool))`. -/
def same : Signature Unit Name Empty typeArity 2 := ⟨fun _ => .parameter (), .closed .bool⟩

def sameCall (reserved : Name → Prop) (x y : Value) :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Empty Sym typeArity valueArity reserved) Nat :=
  callFiring ν same () () (fun i => ofTree (![x, y] i)) (ofTree (leaf (.bool true)))

theorem same_mixed_refused :
    ¬ (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := start)
      (sameCall isAtom (leaf (.number 1)) (leaf (.text "s"))) := by
  rw [sameCall, closed_call_admits_iff label start (start_solvable isAtom seed) ν_injective
    (avoids_nil ν)]
  rintro ⟨θ, proper, inputs, _⟩
  have first := types_of_node (.number 1) Fin.elim0 _ (inputs 0)
  have second := types_of_node (.text "s") Fin.elim0 _ (inputs 1)
  have improper := atom_improper (θ ()) (proper ())
  change θ () = _ ∨ θ () = _ at first second
  rcases first with first | first
  · rcases second with second | second
    · rw [first] at second
      cases second
    · exact improper second
  · exact improper first

theorem same_numbers_admitted :
    (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := start)
      (sameCall isAtom (leaf (.number 1)) (leaf (.number 2))) := by
  rw [sameCall, closed_call_admits_iff label start (start_solvable isAtom seed) ν_injective
    (avoids_nil ν)]
  refine ⟨fun _ => .closed .number, fun _ => proper_closed isAtom (by simp [isAtom]), ?_,
    leaf_typed (.bool true)⟩
  intro i
  fin_cases i
  · exact leaf_typed (.number 1)
  · exact leaf_typed (.number 2)

/-- **Without the sort restriction, `Atom` solves the shared parameter.** -/
theorem atom_solves_shared_parameter :
    (AnnotatedRuns.firstOrder (action decls nothing) label).Admits (s := start)
      (sameCall nothing (leaf (.number 1)) (leaf (.text "s"))) := by
  rw [sameCall, closed_call_admits_iff label start
    (start_solvable nothing (pointAt nothing (leaf (.number 0)) .number id)) ν_injective
    (avoids_nil ν)]
  exact ⟨fun _ => .closed .atom, fun _ _ _ impossible => impossible, fun _ => atom_typed _,
    leaf_typed (.bool true)⟩

/-! ## An open argument: pending, refused, accepted -/

/-- `(same 1 X)` with `X` the program variable `0`. -/
def openCall :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Empty Sym typeArity valueArity isAtom) Nat :=
  callFiring ν same () () ![ofTree (leaf (.number 1)), .var 0] (ofTree (leaf (.bool true)))

theorem open_pending :
    (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := start) openCall := by
  rw [openCall, call_admits_iff label seed start ν_injective (avoids_nil ν)]
  refine ⟨seed, holds_start isAtom seed, ?_⟩
  refine ⟨fun _ => (TypeExpr.closed Name.number : Ty), fun _ => proper_closed isAtom (by simp [isAtom]),
    ?_, ofTree_typed _ (.bool true)⟩
  intro i
  fin_cases i
  · exact ofTree_typed _ (.number 1)
  · exact leaf_typed (.number 0)

/-- The configuration after the open call: its requirement waits in the knowledge. -/
def afterCall : Configuration T Nat :=
  (AnnotatedRuns.firstOrder (action decls isAtom) label).result (s := start) openCall open_pending

/-- Bind `X`. -/
def bind (v : Value) :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Empty Sym typeArity valueArity isAtom) Nat :=
  tellFiring [(.value (.var 0), .value (ofTree v))]

theorem afterCall_equations :
    afterCall.equations = callTells ν same () () ![ofTree (leaf (.number 1)), .var 0]
      (ofTree (leaf (.bool true))) := by
  show (openCall.result label start).equations = _
  rw [openCall, callFiring, tell_result_equations]
  rfl

theorem holds_bind_iff (ρ : Pt isAtom) (v : Value) :
    Holds decls isAtom ρ [(.value (.var 0), .value (ofTree v))] ↔ ρ.values 0 = v := by
  simp [Holds, Term.meaning, OpenTree.evaluate]

theorem contradicting_refused :
    ¬ (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := afterCall)
      (bind (leaf (.text "s"))) := by
  rw [bind, tell_admits_iff, consistent_iff seed, afterCall_equations]
  rintro ⟨ρ, holds⟩
  obtain ⟨tells, bound⟩ := holds_append.mp holds
  obtain ⟨inputs, _⟩ := (holds_callTells ν same () () _ _ ρ).mp tells
  have value := (holds_bind_iff ρ _).mp bound
  have zero := inputs 0
  change DeclarationTyping.HasType decls () ((ofTree (leaf (.number 1))).evaluate ρ.values)
    (ρ.types 0) at zero
  rw [evaluate_ofTree] at zero
  have first := types_of_node (.number 1) Fin.elim0 _ zero
  have second := inputs 1
  change DeclarationTyping.HasType decls () (ρ.values 0) _ at second
  rw [value] at second
  have second' := types_of_node (.text "s") Fin.elim0 _ second
  have improper := atom_improper (ρ.types 0) (ρ.proper 0)
  change ρ.types 0 = _ ∨ ρ.types 0 = _ at first second'
  rcases first with first | first
  · rcases second' with second' | second'
    · rw [first] at second'
      cases second'
    · exact improper second'
  · exact improper first

theorem consistent_accepted :
    (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := afterCall)
      (bind (leaf (.number 2))) := by
  rw [bind, tell_admits_iff, consistent_iff seed, afterCall_equations]
  refine ⟨pointAt isAtom (leaf (.number 2)) .number (by simp [isAtom]),
    holds_append.mpr ⟨(holds_callTells ν same () () _ _ _).mpr ⟨?_, ofTree_typed _ (.bool true)⟩,
      (holds_bind_iff _ _).mpr rfl⟩⟩
  intro i
  fin_cases i
  · exact ofTree_typed _ (.number 1)
  · exact leaf_typed (.number 2)

/-- **The lifecycle as one run of the step**: the open call, then the consistent binding. -/
def lifecycle_run : (AnnotatedRuns.firstOrder (action decls isAtom) label).Run start :=
  .cons openCall open_pending (.cons (bind (leaf (.number 2))) consistent_accepted (.nil _))

/-! ## What the runtime does not decide -/

/-- `(: absurd (-> Void Bool))`. -/
def absurdSig : Signature Empty Name Empty typeArity 1 := ⟨fun _ => .closed .void, .closed .bool⟩

def absurdArgs : Fin 1 → OpenTree Nat Sym valueArity := fun _ => .var 0

def absurdCall :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Empty Sym typeArity valueArity nothing) Nat :=
  callFiring (Empty.elim : Empty → Nat) absurdSig () () absurdArgs (ofTree (leaf (.bool true)))

/-- The runtime's decided check accepts: the type equations are satisfiable, the request waits. -/
theorem void_runtime_accepts :
    ScopedConstraints.accept
      ((OpenTyping.compileOverloads decls [callQueries absurdSig () () absurdArgs
        (ofTree (leaf (.bool true)))]).map ResidualConstraints.Problem.equations) = true := by
  cbv

/-- **The trap**: the runtime keeps the requirement pending, and the step refuses the call, because
no binding of `X` can ever meet it. -/
theorem void_trap :
    ScopedConstraints.accept
        ((OpenTyping.compileOverloads decls [callQueries absurdSig () () absurdArgs
          (ofTree (leaf (.bool true)))]).map ResidualConstraints.Problem.equations) = true ∧
      ¬ (AnnotatedRuns.firstOrder (action decls nothing) label).Admits (s := start) absurdCall := by
  refine ⟨void_runtime_accepts, ?_⟩
  rw [absurdCall, call_admits_iff label (pointAt nothing (leaf (.number 0)) .number id) start
    (fun e _ _ => e.elim) (avoids_nil _)]
  rintro ⟨ρ, _, _, _, inputs, _⟩
  exact void_empty _ (inputs 0)

/-! ## A guard at a shared parameter -/

/-- `1 ∈ $a` and `2 ∈ $a` as guards, nothing told. -/
def guardedSame :
    AnnotatedRuns.Firing T (Instantiation Nat Nat Name Empty Sym typeArity valueArity isAtom) Nat :=
  ⟨⟨[], [], [], [guard () (ofTree (leaf (.number 1))) (.parameter 0),
    guard () (ofTree (leaf (.number 2))) (.parameter 0)], []⟩, [], ⟨[], [], []⟩⟩

/-- **The guard reading refuses a call the contract admits** (`same_numbers_admitted`): the guard is
asked at the solution that gives the shared helper the type `String`. -/
theorem guard_refuses_shared_parameter :
    ¬ (AnnotatedRuns.firstOrder (action decls isAtom) label).Admits (s := start) guardedSame := by
  rw [guardedSame, checked_admits_iff]
  rintro ⟨_, asked⟩
  let stringy : Pt isAtom := pointAt isAtom (leaf (.number 0)) .string (by simp [isAtom])
  have holds := asked _ (List.mem_cons_self) stringy.embed (fun _ member => by cases member) seed
  change Term.meaning decls seed ((Term.member () (ofTree (leaf (.number 1))) (.parameter 0)).subst
      stringy.embed) = Term.meaning decls seed ((Term.yes : T).subst stringy.embed) at holds
  rw [Term.meaning_subst, Term.meaning_subst, Point.after_embed] at holds
  simp only [Term.meaning, evaluate_ofTree, Meaning.truth.injEq, eq_iff_iff, iff_true] at holds
  rcases types_of_node (.number 1) Fin.elim0 _ holds with wrong | wrong <;> cases wrong

#print axioms types_of_node
#print axioms void_empty
#print axioms same_mixed_refused
#print axioms same_numbers_admitted
#print axioms atom_solves_shared_parameter
#print axioms open_pending
#print axioms contradicting_refused
#print axioms consistent_accepted
#print axioms lifecycle_run
#print axioms void_runtime_accepts
#print axioms void_trap
#print axioms guard_refuses_shared_parameter

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingContractsControls
