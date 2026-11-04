import Mettapedia.Logic.ConstraintTypes.RegularTree

/-!
# Shared polymorphic membership contracts

A type universe supplies membership predicates. Type constructors act on that
universe; a scheme quantifies one assignment for its entire argument/result
vector. Overloads are a disjunction of such schemes, never a generator of
additional evaluations. Finite instance lists give an executable check; its
completeness is explicitly relative to that list.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes

universe u v w

inductive TypeExpr (Parameter : Type u) (TypeName : Type v)
    (Constructor : Type w) (arity : Constructor → Nat) where
  | parameter (name : Parameter)
  | closed (name : TypeName)
  | app (name : Constructor)
      (arguments : Fin (arity name) → TypeExpr Parameter TypeName Constructor arity)

namespace TypeExpr

variable {P : Type u} {Q : Type v} {C : Type w} {arity : C → Nat}

def instantiate (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (assignment : P → Q) : TypeExpr P Q C arity → Q
  | .parameter p => assignment p
  | .closed q => q
  | .app c args => construct c (fun i => instantiate construct assignment (args i))

def rename {P' : Type u} (f : P → P') :
    TypeExpr P Q C arity → TypeExpr P' Q C arity
  | .parameter p => .parameter (f p)
  | .closed q => .closed q
  | .app c args => .app c (fun i => rename f (args i))

def substitute {P' : Type u} (assignment : P → TypeExpr P' Q C arity) :
    TypeExpr P Q C arity → TypeExpr P' Q C arity
  | .parameter p => assignment p
  | .closed q => .closed q
  | .app c args => .app c (fun i => substitute assignment (args i))

theorem substitute_id (term : TypeExpr P Q C arity) :
    term.substitute TypeExpr.parameter = term := by
  induction term with
  | parameter _ | closed _ => rfl
  | app c args ih => exact congrArg (TypeExpr.app c) (funext ih)

theorem substitute_comp {P' P'' : Type u}
    (first : P → TypeExpr P' Q C arity) (second : P' → TypeExpr P'' Q C arity)
    (term : TypeExpr P Q C arity) :
    (term.substitute first).substitute second =
      term.substitute (fun p => (first p).substitute second) := by
  induction term with
  | parameter _ | closed _ => rfl
  | app c args ih => exact congrArg (TypeExpr.app c) (funext ih)

theorem substitute_rename {P' P'' : Type u} (rename : P → P')
    (assignment : P' → TypeExpr P'' Q C arity) (term : TypeExpr P Q C arity) :
    (term.rename rename).substitute assignment = term.substitute (assignment ∘ rename) := by
  induction term with
  | parameter _ | closed _ => rfl
  | app c args ih => exact congrArg (TypeExpr.app c) (funext ih)

theorem rename_substitute {P' P'' : Type u} (rename : P' → P'')
    (assignment : P → TypeExpr P' Q C arity) (term : TypeExpr P Q C arity) :
    (term.substitute assignment).rename rename =
      term.substitute (fun p => (assignment p).rename rename) := by
  induction term with
  | parameter _ | closed _ => rfl
  | app c args ih => exact congrArg (TypeExpr.app c) (funext ih)

def variables : TypeExpr P Q C arity → List P
  | .parameter p => [p]
  | .closed _ => []
  | .app c fields => (List.finRange (arity c)).flatMap fun i => variables (fields i)

theorem substitute_congr {P' : Type u} (left right : P → TypeExpr P' Q C arity)
    (term : TypeExpr P Q C arity)
    (agree : ∀ p ∈ term.variables, left p = right p) :
    term.substitute left = term.substitute right := by
  induction term with
  | parameter p => exact agree p List.mem_cons_self
  | closed _ => rfl
  | app c fields ih =>
      exact congrArg (TypeExpr.app c) (funext fun i => ih i
        (fun p member => agree p (List.mem_flatMap.2 ⟨i, List.mem_finRange i, member⟩)))

/-- In the free constructor algebra, the instantiated expression determines
each parameter occurring in it. -/
theorem parameters_determined {P' : Type u} (left right : P → TypeExpr P' Q C arity)
    (term : TypeExpr P Q C arity) (same : term.substitute left = term.substitute right) :
    ∀ p ∈ term.variables, left p = right p := by
  induction term with
  | parameter p =>
      intro q member
      have equal : q = p := List.mem_singleton.1 member
      subst q
      exact same
  | closed _ => intro p impossible; cases impossible
  | app c fields ih =>
      have sameFields : (fun i => (fields i).substitute left) = (fun i => (fields i).substitute right) := by
        simpa only [substitute, TypeExpr.app.injEq, heq_eq_eq, true_and] using same
      intro p member
      obtain ⟨i, _, fieldMember⟩ := List.mem_flatMap.1 member
      exact ih i (congrFun sameFields i) p fieldMember

/-- Instantiation respects alpha-renaming of scheme parameters. -/
theorem instantiate_rename {P' : Type u} (f : P → P')
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (assignment : P' → Q) (t : TypeExpr P Q C arity) :
    (t.rename f).instantiate construct assignment =
      t.instantiate construct (assignment ∘ f) := by
  induction t with
  | parameter _ => rfl
  | closed _ => rfl
  | app c args ih =>
      simp only [rename, instantiate]
      exact congrArg (construct c) (funext ih)

end TypeExpr

structure Signature (P : Type u) (Q : Type v) (C : Type w)
    (arity : C → Nat) (inputs : Nat) where
  argument : Fin inputs → TypeExpr P Q C arity
  result : TypeExpr P Q C arity

namespace Signature

variable {P : Type u} {Q : Type v} {C : Type w} {arity : C → Nat}
    {V W : Type} {n : Nat}

def acceptsInstance (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (world : W) (sig : Signature P Q C arity n) (assignment : P → Q)
    (args : Fin n → V) (out : V) : Bool :=
  (List.finRange n).all (fun i =>
    member world ((sig.argument i).instantiate construct assignment) (args i)) &&
  member world (sig.result.instantiate construct assignment) out

def Satisfies (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (world : W) (sig : Signature P Q C arity n)
    (args : Fin n → V) (out : V) : Prop :=
  ∃ assignment : P → Q,
    (∀ i, member world ((sig.argument i).instantiate construct assignment) (args i) = true) ∧
      member world (sig.result.instantiate construct assignment) out = true

theorem acceptsInstance_iff (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (world : W) (sig : Signature P Q C arity n) (assignment : P → Q)
    (args : Fin n → V) (out : V) :
    sig.acceptsInstance member construct world assignment args out = true ↔
      (∀ i, member world ((sig.argument i).instantiate construct assignment) (args i) = true) ∧
        member world (sig.result.instantiate construct assignment) out = true := by
  simp [acceptsInstance, List.all_eq_true]

end Signature

namespace Overloads

variable {P : Type u} {Q : Type v} {C : Type w} {arity : C → Nat}
    {V W : Type} {n : Nat}

def check (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (instances : List (P → Q)) (declarations : List (Signature P Q C arity n))
    (world : W) (args : Fin n → V) (out : V) : Bool :=
  declarations.any fun sig => instances.any fun assignment =>
    sig.acceptsInstance member construct world assignment args out

theorem check_iff (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (instances : List (P → Q)) (declarations : List (Signature P Q C arity n))
    (world : W) (args : Fin n → V) (out : V) :
    check member construct instances declarations world args out = true ↔
      ∃ sig ∈ declarations, ∃ assignment ∈ instances,
        (∀ i, member world ((sig.argument i).instantiate construct assignment) (args i) = true) ∧
          member world (sig.result.instantiate construct assignment) out = true := by
  simp only [check, List.any_eq_true, Signature.acceptsInstance_iff]

theorem check_sound (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (instances : List (P → Q)) (declarations : List (Signature P Q C arity n))
    (world : W) (args : Fin n → V) (out : V)
    (h : check member construct instances declarations world args out = true) :
    ∃ sig ∈ declarations, sig.Satisfies member construct world args out := by
  obtain ⟨sig, hs, assignment, _, ha⟩ := (check_iff _ _ _ _ _ _ _).1 h
  exact ⟨sig, hs, assignment, ha⟩

/-- A complete enumerator yields completeness of the executable check.
This utility does not solve an unbounded instance search. SymbolicTypes and
DeclarationTyping supply that solver for the free constructor-type algebra. -/
theorem enumerated_check_complete (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (instances : List (P → Q)) (complete : ∀ assignment, assignment ∈ instances)
    (declarations : List (Signature P Q C arity n))
    (world : W) (args : Fin n → V) (out : V)
    (h : ∃ sig ∈ declarations, sig.Satisfies member construct world args out) :
    check member construct instances declarations world args out = true := by
  obtain ⟨sig, hs, assignment, ha⟩ := h
  exact (check_iff _ _ _ _ _ _ _).2 ⟨sig, hs, assignment, complete _, ha⟩

theorem duplicate_declaration (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (instances : List (P → Q)) (sig : Signature P Q C arity n)
    (rest : List (Signature P Q C arity n)) (world : W) (args : Fin n → V) (out : V) :
    check member construct instances (sig :: sig :: rest) world args out =
      check member construct instances (sig :: rest) world args out := by
  simp [check]

/-- Overload order and multiplicity are evidence presentation, not an ordering
or multiplicity of executions. -/
theorem declaration_membership_congr (member : W → Q → V → Bool)
    (construct : (c : C) → (Fin (arity c) → Q) → Q)
    (instances : List (P → Q)) (left right : List (Signature P Q C arity n))
    (same : ∀ signature, signature ∈ left ↔ signature ∈ right)
    (world : W) (args : Fin n → V) (out : V) :
    check member construct instances left world args out =
      check member construct instances right world args out := by
  have accepted : check member construct instances left world args out = true ↔
      check member construct instances right world args out = true := by
    simp only [check_iff]
    constructor
    · rintro ⟨signature, hs, rest⟩
      exact ⟨signature, (same signature).1 hs, rest⟩
    · rintro ⟨signature, hs, rest⟩
      exact ⟨signature, (same signature).2 hs, rest⟩
  cases hl : check member construct instances left world args out <;>
    cases hr : check member construct instances right world args out <;> simp_all

end Overloads

end Mettapedia.Logic.ConstraintTypes
