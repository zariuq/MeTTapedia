import Mettapedia.Logic.ConstraintTypes.CallTyping
import Mettapedia.Logic.ConstraintTypes.OpenTyping
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# Typing as firings, rung one: membership contracts in the one-frame step

A declaration `(: f (-> A B C))` read as a membership contract becomes a firing of the one-frame
instance of the candidate step (`AnnotatedRuns.firstOrder`). The judgment is the existing
`DeclarationTyping.HasType`; nothing about membership is restated.

## The constraint domain (`action`)

* **Terms** (`Term`): program values with program variables (`value`), proper type expressions over
  type helpers (`type`), membership atoms `member Γ v τ` read in the declaration view `Γ`, and `yes`.
* **Instantiations** (`Instantiation`) bind program variables to program values and type helpers to
  type expressions. Type helpers are **sort-restricted**: an instantiation may give a helper only a
  proper type, one that writes no reserved name (`Proper`; in PeTTa the reserved name is `Atom`).
* **Points** (`Point`) are ground instantiations: closed values, and closed proper types.
* **Equivalence**: two terms are equivalent when they mean the same at every point (`Term.meaning`). A
  membership atom means its `HasType` judgment, so the equation `member Γ v τ ≐ yes` (`require`) is
  the residual requirement "`v` belongs to `τ` in `Γ`". This is the constraint-domain reading of
  constraint logic programming: constraints are interpreted in a structure, here the ground
  declaration model.
* **Solvability is ground solvability** (`consistent_iff`): a store has a solution exactly when some
  point satisfies it. So the step's admission asks whether a requirement *can still be met by some
  binding*.

## The typed-call firing (`callFiring`)

It tells one requirement per input, at the entry view, and one for the result, at the return view.
The signature's parameters are renamed to type helpers (`ν`); program variables stay knowledge
metavariables, so a call never binds them.

* **Adequacy, open values** (`call_admits_iff`): with fresh helpers, the firing is admitted exactly
  when some point satisfying the old knowledge also satisfies `Joint_d` at the values it gives the
  open arguments.
* **Adequacy, closed values** (`closed_call_admits_iff`): from solvable knowledge, the firing is
  admitted exactly when `Joint_d` holds: one proper assignment for the inputs and the result.
* **The existing judgment** (`joint_iff_allowed`): without reserved names, `Joint_d` is
  `CallTyping.Allowed`, the relation the staged checker decides (`CallTyping.frame_exact`).
* **The runtime's residual formula** (`call_admits_iff_residual`): admission is the existence of a
  binding satisfying `OpenTyping.compileOverloads`, the formula the runtime keeps.

## What is decided

* The runtime decides the type equations of that formula (`ScopedConstraints.accept`); a refusal
  there is a refusal of the step (`runtime_accepts_of_admits`). It does not decide the pending
  membership requests: whether a requirement can still be met is inhabitation of the requested
  types under the shared assignment. The step's admission is that closed-point question
  (`TypingContractsControls.void_trap`).
* **Guards versus tells** (`guard_admits_iff`): a closed membership whose type has no helpers may
  equally be a guard asked at every solution. At a shared parameter it may not: the guard is asked
  at every solution, including those giving the parameter another type
  (`TypingContractsControls.guard_refuses_shared_parameter`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingFirings

open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Logic.ConstraintTypes renaming Tree → VTree
open Mettapedia.Logic.ConstraintTypes.SymbolicTypes (Expr Closed embedClosed close_embed)

/-! ## Type names and proper types -/

section Names

variable {P Q C : Type} {arity : C → Nat}

/-- The type names written in a type expression. -/
def names : TypeExpr P Q C arity → List Q
  | .parameter _ => []
  | .closed q => [q]
  | .app c args => (List.finRange (arity c)).flatMap fun i => names (args i)

/-- **A proper type** writes no reserved name. -/
def Proper (reserved : Q → Prop) (t : TypeExpr P Q C arity) : Prop := ∀ q ∈ names t, ¬ reserved q

theorem names_substitute {P' : Type} (σ : P → TypeExpr P' Q C arity) (t : TypeExpr P Q C arity)
    {q : Q} (written : q ∈ names (t.substitute σ)) :
    q ∈ names t ∨ ∃ p ∈ t.variables, q ∈ names (σ p) := by
  induction t with
  | parameter p => exact .inr ⟨p, by simp [TypeExpr.variables], written⟩
  | closed _ => exact .inl written
  | app c args ih =>
      simp only [TypeExpr.substitute, names, List.mem_flatMap, List.mem_finRange, true_and] at written
      obtain ⟨i, inside⟩ := written
      rcases ih i inside with here | ⟨p, occurs, there⟩
      · exact .inl (by simp only [names, List.mem_flatMap, List.mem_finRange, true_and]; exact ⟨i, here⟩)
      · exact .inr ⟨p, by
          simp only [TypeExpr.variables, List.mem_flatMap, List.mem_finRange, true_and]
          exact ⟨i, occurs⟩, there⟩

theorem names_rename {P' : Type} (f : P → P') (t : TypeExpr P Q C arity) :
    names (t.rename f) = names t := by
  induction t with
  | parameter _ | closed _ => rfl
  | app c args ih =>
      simp only [TypeExpr.rename, names]
      exact congrArg (List.flatMap · (List.finRange (arity c))) (funext ih)

theorem Proper.substitute {reserved : Q → Prop} {P' : Type} {σ : P → TypeExpr P' Q C arity}
    {t : TypeExpr P Q C arity} (proper : Proper reserved t) (each : ∀ p, Proper reserved (σ p)) :
    Proper reserved (t.substitute σ) := fun q written =>
  (names_substitute σ t written).elim (proper q) fun ⟨p, _, there⟩ => each p q there

theorem Proper.rename {reserved : Q → Prop} {P' : Type} (f : P → P') {t : TypeExpr P Q C arity}
    (proper : Proper reserved t) : Proper reserved (t.rename f) := by
  intro q written
  rw [names_rename] at written
  exact proper q written

theorem proper_parameter (reserved : Q → Prop) (p : P) :
    Proper reserved (TypeExpr.parameter p : TypeExpr P Q C arity) := by
  intro q written
  simp [names] at written

end Names

/-! ## Program values -/

section Values

variable {V W X Sym : Type} {valueArity : Sym → Nat}

/-- A closed value as a program value. -/
def ofTree : VTree Sym valueArity → OpenTree V Sym valueArity
  | .node s children => .node s fun i => ofTree (children i)

@[simp] theorem evaluate_ofTree (ρ : V → VTree Sym valueArity) (t : VTree Sym valueArity) :
    (ofTree t).evaluate ρ = t := by
  induction t with
  | node s children ih => exact congrArg (Mettapedia.Logic.ConstraintTypes.Tree.node s) (funext ih)

@[simp] theorem substitute_ofTree (σ : V → OpenTree W Sym valueArity) (t : VTree Sym valueArity) :
    (ofTree t : OpenTree V Sym valueArity).substitute σ = ofTree t := by
  induction t with
  | node s children ih => exact congrArg (OpenTree.node s) (funext ih)

theorem substitute_var (t : OpenTree V Sym valueArity) : t.substitute OpenTree.var = t := by
  induction t with
  | var _ => rfl
  | node s children ih => exact congrArg (OpenTree.node s) (funext ih)

theorem substitute_substitute (σ : V → OpenTree W Sym valueArity) (τ : W → OpenTree X Sym valueArity)
    (t : OpenTree V Sym valueArity) :
    (t.substitute σ).substitute τ = t.substitute fun x => (σ x).substitute τ := by
  induction t with
  | var _ => rfl
  | node s children ih => exact congrArg (OpenTree.node s) (funext ih)

end Values

/-! ## The constraint domain -/

variable {Ctx U P V A Q C Sym : Type} {typeArity : C → Nat} {valueArity : Sym → Nat}

variable (Ctx V A Q C Sym typeArity valueArity) in
/-- Terms of the typing knowledge. -/
inductive Term where
  | value (v : OpenTree V Sym valueArity)
  | type (τ : Expr A Q C typeArity)
  | member (context : Ctx) (v : OpenTree V Sym valueArity) (τ : Expr A Q C typeArity)
  | yes

variable (Q C Sym typeArity valueArity) in
/-- What a ground term means. -/
inductive Meaning where
  | value (t : VTree Sym valueArity)
  | type (τ : Closed Q C typeArity)
  | truth (p : Prop)

variable (V A Q C Sym typeArity valueArity) in
/-- **An instantiation**: program variables to program values, type helpers to proper types. -/
structure Instantiation (reserved : Q → Prop) where
  values : V → OpenTree V Sym valueArity
  types : A → Expr A Q C typeArity
  proper : ∀ a, Proper reserved (types a)

variable (V A Q C Sym typeArity valueArity) in
/-- **A point**: a ground instantiation, closed values and closed proper types. -/
structure Point (reserved : Q → Prop) where
  values : V → VTree Sym valueArity
  types : A → Closed Q C typeArity
  proper : ∀ a, Proper reserved (types a)

namespace Point

variable {reserved : Q → Prop}

theorem ext' {ρ ρ' : Point V A Q C Sym typeArity valueArity reserved} (values : ρ.values = ρ'.values)
    (types : ρ.types = ρ'.types) : ρ = ρ' := by
  cases ρ
  cases ρ'
  cases values
  cases types
  rfl

/-- The point reached by instantiating, then reading at `ρ`. -/
def after (ρ : Point V A Q C Sym typeArity valueArity reserved)
    (σ : Instantiation V A Q C Sym typeArity valueArity reserved) :
    Point V A Q C Sym typeArity valueArity reserved where
  values x := (σ.values x).evaluate ρ.values
  types a := (σ.types a).substitute ρ.types
  proper a := (σ.proper a).substitute ρ.proper

/-- A point as an instantiation. -/
def embed (ρ : Point V A Q C Sym typeArity valueArity reserved) :
    Instantiation V A Q C Sym typeArity valueArity reserved where
  values x := ofTree (ρ.values x)
  types a := embedClosed (ρ.types a)
  proper a := (ρ.proper a).rename _

theorem after_embed (ρ' ρ : Point V A Q C Sym typeArity valueArity reserved) :
    ρ'.after ρ.embed = ρ :=
  ext' (funext fun _ => evaluate_ofTree _ _) (funext fun _ => close_embed _ _)

end Point

namespace Term

variable {reserved : Q → Prop}

/-- Instantiate a term. -/
def subst (σ : Instantiation V A Q C Sym typeArity valueArity reserved) :
    Term Ctx V A Q C Sym typeArity valueArity → Term Ctx V A Q C Sym typeArity valueArity
  | .value v => .value (v.substitute σ.values)
  | .type τ => .type (τ.substitute σ.types)
  | .member Γ v τ => .member Γ (v.substitute σ.values) (τ.substitute σ.types)
  | .yes => .yes

/-- The meaning of a term at a point. A membership atom means the declaration judgment. -/
def meaning (decls : DeclarationTyping.Declarations Ctx U P Q C Sym typeArity valueArity)
    (ρ : Point V A Q C Sym typeArity valueArity reserved) :
    Term Ctx V A Q C Sym typeArity valueArity → Meaning Q C Sym typeArity valueArity
  | .value v => .value (v.evaluate ρ.values)
  | .type τ => .type (τ.substitute ρ.types)
  | .member Γ v τ => .truth (DeclarationTyping.HasType decls Γ (v.evaluate ρ.values) (τ.substitute ρ.types))
  | .yes => .truth True

/-- The type helpers a term mentions. -/
def helpers : Term Ctx V A Q C Sym typeArity valueArity → List A
  | .value _ => []
  | .type τ => τ.variables
  | .member _ _ τ => τ.variables
  | .yes => []

theorem meaning_subst (decls : DeclarationTyping.Declarations Ctx U P Q C Sym typeArity valueArity)
    (ρ : Point V A Q C Sym typeArity valueArity reserved)
    (σ : Instantiation V A Q C Sym typeArity valueArity reserved)
    (t : Term Ctx V A Q C Sym typeArity valueArity) :
    (t.subst σ).meaning decls ρ = t.meaning decls (ρ.after σ) := by
  cases t with
  | value v => exact congrArg Meaning.value (OpenTree.evaluate_substitute _ _ _)
  | type τ => exact congrArg Meaning.type (TypeExpr.substitute_comp _ _ _)
  | member Γ v τ =>
      simp only [subst, meaning, Point.after, OpenTree.evaluate_substitute, TypeExpr.substitute_comp]
  | yes => rfl

/-- The meaning reads type helpers only where the term mentions them. -/
theorem meaning_congr (decls : DeclarationTyping.Declarations Ctx U P Q C Sym typeArity valueArity)
    {ρ ρ' : Point V A Q C Sym typeArity valueArity reserved} (values : ρ.values = ρ'.values)
    (t : Term Ctx V A Q C Sym typeArity valueArity) (types : ∀ a ∈ t.helpers, ρ.types a = ρ'.types a) :
    t.meaning decls ρ = t.meaning decls ρ' := by
  cases t with
  | value v => simp only [meaning, values]
  | type τ => exact congrArg Meaning.type (TypeExpr.substitute_congr _ _ τ types)
  | member Γ v τ =>
      simp only [meaning, values, TypeExpr.substitute_congr _ _ τ types]
  | yes => rfl

end Term

variable (decls : DeclarationTyping.Declarations Ctx U P Q C Sym typeArity valueArity)
  (reserved : Q → Prop)

/-- **The typing constraint domain as a substitution action.** Two terms are equivalent when they
mean the same at every point; instantiations act by substitution. -/
def action :
    SubstitutionAction (Term Ctx V A Q C Sym typeArity valueArity)
      (Instantiation V A Q C Sym typeArity valueArity reserved) where
  E s t := ∀ ρ : Point V A Q C Sym typeArity valueArity reserved,
    s.meaning decls ρ = t.meaning decls ρ
  equivalence := ⟨fun _ _ => rfl, fun same ρ => (same ρ).symm, fun one two ρ => (one ρ).trans (two ρ)⟩
  apply σ t := t.subst σ
  identity := ⟨OpenTree.var, TypeExpr.parameter, proper_parameter reserved⟩
  compose outer inner :=
    ⟨fun x => (inner.values x).substitute outer.values, fun a => (inner.types a).substitute outer.types,
      fun a => (inner.proper a).substitute outer.proper⟩
  apply_identity t := by
    cases t <;> simp only [Term.subst, substitute_var, TypeExpr.substitute_id]
  apply_compose outer inner t := by
    cases t <;> simp only [Term.subst, substitute_substitute, TypeExpr.substitute_comp]
  preserves σ s t same ρ := by
    rw [Term.meaning_subst, Term.meaning_subst]
    exact same _

/-- A store holds at a point. -/
def Holds (ρ : Point V A Q C Sym typeArity valueArity reserved)
    (store : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) : Prop :=
  ∀ e ∈ store, e.1.meaning decls ρ = e.2.meaning decls ρ

variable {decls reserved}

theorem holds_append {ρ : Point V A Q C Sym typeArity valueArity reserved}
    {one two : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)} :
    Holds decls reserved ρ (one ++ two) ↔ Holds decls reserved ρ one ∧ Holds decls reserved ρ two := by
  simp only [Holds, List.forall_mem_append]

theorem models_iff (σ : Instantiation V A Q C Sym typeArity valueArity reserved)
    (store : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    (action decls reserved).Models σ store ↔
      ∀ ρ : Point V A Q C Sym typeArity valueArity reserved, Holds decls reserved (ρ.after σ) store := by
  simp only [SubstitutionAction.Models, SubstitutionAction.Solves, action, Holds, Term.meaning_subst]
  exact ⟨fun solved ρ e member => solved e member ρ, fun solved e member ρ => solved ρ e member⟩

/-- **Solvability is ground solvability**, given one point. -/
theorem consistent_iff (seed : Point V A Q C Sym typeArity valueArity reserved)
    (store : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    (action decls reserved).Consistent store ↔ ∃ ρ : Point V A Q C Sym typeArity valueArity reserved,
      Holds decls reserved ρ store := by
  constructor
  · rintro ⟨σ, solved⟩
    exact ⟨seed.after σ, (models_iff σ store).mp solved seed⟩
  · rintro ⟨ρ, holds⟩
    refine ⟨ρ.embed, (models_iff _ store).mpr fun ρ' => ?_⟩
    rw [Point.after_embed]
    exact holds

/-! ## Requirements -/

/-- **The residual requirement** "`v` belongs to `τ` in the view `Γ`". -/
def require (Γ : Ctx) (v : OpenTree V Sym valueArity) (τ : Expr A Q C typeArity) :
    Equation (Term Ctx V A Q C Sym typeArity valueArity) :=
  (.member Γ v τ, .yes)

theorem holds_require (ρ : Point V A Q C Sym typeArity valueArity reserved) (Γ : Ctx)
    (v : OpenTree V Sym valueArity) (τ : Expr A Q C typeArity) :
    Holds decls reserved ρ [require Γ v τ] ↔
      DeclarationTyping.HasType decls Γ (v.evaluate ρ.values) (τ.substitute ρ.types) := by
  simp [Holds, require, Term.meaning]

/-- A store avoids the helpers `ν` names. -/
def Avoids {Θ : Type} (ν : Θ → A) (store : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    Prop :=
  ∀ e ∈ store, ∀ a ∈ e.1.helpers ++ e.2.helpers, ∀ t, ν t ≠ a

theorem avoids_nil {Θ : Type} (ν : Θ → A) :
    Avoids ν ([] : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) := by
  intro e member
  cases member

namespace Point

variable {Θ : Type}

/-- Give the helpers `ν` names the types `θ`, and keep every other helper. -/
noncomputable def reassign (ρ : Point V A Q C Sym typeArity valueArity reserved) (ν : Θ → A)
    (θ : Θ → Closed Q C typeArity) (proper : ∀ t, Proper reserved (θ t)) :
    Point V A Q C Sym typeArity valueArity reserved where
  values := ρ.values
  types := Function.extend ν θ ρ.types
  proper a := by
    classical
    rw [Function.extend_def]
    split
    · exact proper _
    · exact ρ.proper a

theorem reassign_types_apply (ρ : Point V A Q C Sym typeArity valueArity reserved) {ν : Θ → A}
    (injective : Function.Injective ν) (θ : Θ → Closed Q C typeArity) (proper : ∀ t, Proper reserved (θ t))
    (t : Θ) : (ρ.reassign ν θ proper).types (ν t) = θ t :=
  injective.extend_apply θ ρ.types t

theorem reassign_types_of_not (ρ : Point V A Q C Sym typeArity valueArity reserved) (ν : Θ → A)
    (θ : Θ → Closed Q C typeArity) (proper : ∀ t, Proper reserved (θ t)) {a : A}
    (outside : ∀ t, ν t ≠ a) : (ρ.reassign ν θ proper).types a = ρ.types a :=
  Function.extend_apply' θ ρ.types a fun ⟨t, same⟩ => outside t same

end Point

/-- Reassigning helpers a store avoids keeps it holding. -/
theorem holds_reassign {Θ : Type} {ν : Θ → A}
    {store : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)} (avoid : Avoids ν store)
    (ρ : Point V A Q C Sym typeArity valueArity reserved) (θ : Θ → Closed Q C typeArity)
    (proper : ∀ t, Proper reserved (θ t)) :
    Holds decls reserved (ρ.reassign ν θ proper) store ↔ Holds decls reserved ρ store := by
  have same : ∀ e ∈ store, ∀ s ∈ [e.1, e.2],
      s.meaning decls (ρ.reassign ν θ proper) = s.meaning decls ρ := by
    intro e member s side
    refine Term.meaning_congr decls (ρ := ρ.reassign ν θ proper) (ρ' := ρ) rfl s ?_
    intro a mentioned
    apply Point.reassign_types_of_not
    apply avoid e member a
    rcases List.mem_pair.mp side with rfl | rfl
    · exact List.mem_append_left _ mentioned
    · exact List.mem_append_right _ mentioned
  constructor
  · intro holds e member
    rw [← same e member e.1 (by simp), ← same e member e.2 (by simp)]
    exact holds e member
  · intro holds e member
    rw [same e member e.1 (by simp), same e member e.2 (by simp)]
    exact holds e member

/-! ## Contracts -/

variable (decls reserved) in
/-- **`Joint_d`**: one proper assignment of the signature's parameters admits every input at the
entry view `Γ₀` and the result at the return view `Γ₁`. -/
def Joint {Θ : Type} {n : Nat} (sig : Signature Θ Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → VTree Sym valueArity) (out : VTree Sym valueArity) : Prop :=
  ∃ θ : Θ → Closed Q C typeArity, (∀ t, Proper reserved (θ t)) ∧
    (∀ i, DeclarationTyping.HasType decls Γ₀ (args i) ((sig.argument i).substitute θ)) ∧
      DeclarationTyping.HasType decls Γ₁ out (sig.result.substitute θ)

/-- A signature with its inputs permuted. -/
def permuteInputs {Θ : Type} {n : Nat} (sig : Signature Θ Q C typeArity n) (e : Fin n ≃ Fin n) :
    Signature Θ Q C typeArity n :=
  ⟨fun i => sig.argument (e i), sig.result⟩

/-- **`Joint_d` does not depend on the order of the arguments.** -/
theorem joint_permute {Θ : Type} {n : Nat} (sig : Signature Θ Q C typeArity n) (e : Fin n ≃ Fin n)
    (Γ₀ Γ₁ : Ctx) (args : Fin n → VTree Sym valueArity) (out : VTree Sym valueArity) :
    Joint decls reserved (permuteInputs sig e) Γ₀ Γ₁ (args ∘ e) out ↔
      Joint decls reserved sig Γ₀ Γ₁ args out := by
  refine exists_congr fun θ => and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine ⟨fun inputs i => ?_, fun inputs i => inputs (e i)⟩
  have moved := inputs (e.symm i)
  change DeclarationTyping.HasType decls Γ₀ (args (e (e.symm i)))
    ((sig.argument (e (e.symm i))).substitute θ) at moved
  rwa [Equiv.apply_symm_apply] at moved

/-- A signature as a staged declaration whose every position is a proper type. -/
def asDeclaration (Mode : Type) {n : Nat} (sig : Signature P Q C typeArity n) :
    CallTyping.Declaration P Q C Mode typeArity n :=
  ⟨fun i => .inr (sig.argument i), .inr sig.result⟩

/-- **Without reserved names, `Joint_d` is the existing staged call relation**, the relation that
`CallTyping.frame_exact` compiles and `CallTyping.resultAccepted` decides. -/
theorem joint_iff_allowed [DecidableEq P] [DecidableEq U] [DecidableEq Q] [DecidableEq C]
    [DecidableEq Sym] {Mode : Type} (noReserved : ∀ q, ¬ reserved q)
    (observe : Ctx → Mode → VTree Sym valueArity → Bool) {n : Nat} (sig : Signature P Q C typeArity n)
    (Γ₀ Γ₁ : Ctx) (args : Fin n → VTree Sym valueArity) (out : VTree Sym valueArity) :
    Joint decls reserved sig Γ₀ Γ₁ args out ↔
      CallTyping.Allowed (DeclarationTyping.asSystem decls) observe Γ₀ Γ₁ args out [asDeclaration Mode sig] := by
  simp only [Joint, CallTyping.Allowed, List.mem_singleton, exists_eq_left, asDeclaration,
    CallTyping.Fits, DeclarationTyping.asSystem_iff]
  constructor
  · rintro ⟨θ, _, inputs, result⟩
    exact ⟨θ, inputs, result⟩
  · rintro ⟨θ, inputs, result⟩
    exact ⟨θ, fun _ q _ => noReserved q, inputs, result⟩

/-! ## Firings that tell -/

variable {O : Type} [DecidableEq O]

/-- A rule that only tells. -/
def tellRule (tells : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    RuleInstance (Term Ctx V A Q C Sym typeArity valueArity) :=
  ⟨[], [], tells, [], []⟩

/-- **A firing that only tells**: it takes, reads and makes nothing. -/
def tellFiring (tells : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    AnnotatedRuns.Firing (Term Ctx V A Q C Sym typeArity valueArity)
      (Instantiation V A Q C Sym typeArity valueArity reserved) O :=
  ⟨tellRule tells, [], ⟨[], [], []⟩⟩

omit [DecidableEq O] in
theorem empty_problem (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (rule : RuleInstance (Term Ctx V A Q C Sym typeArity valueArity)) (hTake : rule.take = [])
    (hRead : rule.read = []) (before : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O) :
    (⟨[], [], []⟩ : Selection O).problem label rule before = before.equations ++ rule.tell := by
  simp [Selection.problem, Selection.equations, hTake, hRead]

theorem empty_enabled (label : O → Term Ctx V A Q C Sym typeArity valueArity) (present : Finset O) :
    MeTTaCalculus.OccurrenceCommits.Enabled label present
      ((⟨[], [], []⟩ : Selection O).commit (T := Term Ctx V A Q C Sym typeArity valueArity)) :=
  ⟨by simp [Selection.commit], by simp [Selection.commit], by simp [Selection.commit],
    by simp [Selection.commit], by simp [Selection.commit]⟩

/-- **Admission of a firing with tells and checks and no occurrences**: its knowledge with the tells
is solvable, and every check is asked at every solution. -/
theorem checked_admits_iff (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    (tells : EquationStore (Term Ctx V A Q C Sym typeArity valueArity))
    (checks : List (Check (Term Ctx V A Q C Sym typeArity valueArity))) :
    (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (⟨⟨[], [], tells, checks, []⟩, [], ⟨[], [], []⟩⟩ :
          AnnotatedRuns.Firing (Term Ctx V A Q C Sym typeArity valueArity)
            (Instantiation V A Q C Sym typeArity valueArity reserved) O) ↔
      (action decls reserved).Consistent (C₀.equations ++ tells) ∧
        ∀ check ∈ checks, (action decls reserved).Entails (C₀.equations ++ tells)
          (fun σ => check.Holds (action decls reserved) σ label C₀.present) := by
  have problem := empty_problem (Q := Q) (C := C) label ⟨[], [], tells, checks, []⟩ rfl rfl C₀
  show PredicateQueryAdmission.Valid _ _ _ [] _ _ ↔ _
  rw [PredicateQueryAdmission.valid_empty_iff]
  show Selection.Valid (action decls reserved) (⟨[], [], []⟩ : Selection O) label
    ⟨[], [], tells, checks, []⟩ C₀ ↔ _
  constructor
  · intro valid
    have consistent := valid.consistent
    have checked := valid.checks
    rw [problem] at consistent checked
    exact ⟨consistent, checked⟩
  · rintro ⟨consistent, asked⟩
    refine ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, empty_enabled label C₀.present, ?_, ?_⟩
    · rw [problem]
      exact consistent
    · rw [problem]
      exact asked

theorem tell_admits_iff (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    (tells : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀) (tellFiring tells) ↔
      (action decls reserved).Consistent (C₀.equations ++ tells) := by
  rw [tellFiring, tellRule, checked_admits_iff]
  simp

/-- After a firing that only tells, the knowledge is the old knowledge with the tells. -/
theorem tell_result_equations (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    (tells : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    ((tellFiring (reserved := reserved) tells : AnnotatedRuns.Firing _ _ O).result label C₀).equations =
      C₀.equations ++ tells :=
  empty_problem label (tellRule tells) rfl rfl C₀

theorem tell_result_present (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    (tells : EquationStore (Term Ctx V A Q C Sym typeArity valueArity)) :
    ((tellFiring (reserved := reserved) tells : AnnotatedRuns.Firing _ _ O).result label C₀).present =
      C₀.present := by
  simp [tellFiring, AnnotatedRuns.Firing.result, Selection.result, Selection.commit,
    MeTTaCalculus.OccurrenceCommits.fire]

/-! ## The typed-call firing -/

/-- The requirements of one call: every input at the entry view, the result at the return view,
the signature's parameters renamed to the helpers `ν`. -/
def callTells {Θ : Type} (ν : Θ → A) {n : Nat} (sig : Signature Θ Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity) :
    EquationStore (Term Ctx V A Q C Sym typeArity valueArity) :=
  (List.finRange n).map (fun i => require Γ₀ (args i) ((sig.argument i).rename ν)) ++
    [require Γ₁ out (sig.result.rename ν)]

/-- **The typed-call firing.** -/
def callFiring {Θ : Type} (ν : Θ → A) {n : Nat} (sig : Signature Θ Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity) :
    AnnotatedRuns.Firing (Term Ctx V A Q C Sym typeArity valueArity)
      (Instantiation V A Q C Sym typeArity valueArity reserved) O :=
  tellFiring (callTells ν sig Γ₀ Γ₁ args out)

theorem holds_callTells {Θ : Type} (ν : Θ → A) {n : Nat} (sig : Signature Θ Q C typeArity n)
    (Γ₀ Γ₁ : Ctx) (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity)
    (ρ : Point V A Q C Sym typeArity valueArity reserved) :
    Holds decls reserved ρ (callTells ν sig Γ₀ Γ₁ args out) ↔
      (∀ i, DeclarationTyping.HasType decls Γ₀ ((args i).evaluate ρ.values)
        ((sig.argument i).substitute (ρ.types ∘ ν))) ∧
      DeclarationTyping.HasType decls Γ₁ (out.evaluate ρ.values) (sig.result.substitute (ρ.types ∘ ν)) := by
  have single : ∀ (Γ : Ctx) (v : OpenTree V Sym valueArity) (τ : Expr Θ Q C typeArity),
      (require Γ v (τ.rename ν)).1.meaning decls ρ = (require Γ v (τ.rename ν)).2.meaning decls ρ ↔
        DeclarationTyping.HasType decls Γ (v.evaluate ρ.values) (τ.substitute (ρ.types ∘ ν)) := by
    intro Γ v τ
    have := holds_require (decls := decls) ρ Γ v (τ.rename ν)
    simp only [Holds, List.mem_singleton, forall_eq] at this
    rw [this, TypeExpr.substitute_rename]
  rw [callTells]
  constructor
  · intro holds
    exact ⟨fun i => (single _ _ _).mp (holds _ (List.mem_append_left _
        (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))),
      (single _ _ _).mp (holds _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))⟩
  · rintro ⟨inputs, result⟩ e member
    rcases List.mem_append.mp member with inside | last
    · obtain ⟨i, _, rfl⟩ := List.mem_map.mp inside
      exact (single _ _ _).mpr (inputs i)
    · rw [List.mem_singleton.mp last]
      exact (single _ _ _).mpr result

/-- **Adequacy for open values.** With fresh helpers, the typed-call firing is admitted exactly when
some point satisfying the old knowledge satisfies `Joint_d` at the values it gives the arguments:
the requirement can still be met by some binding. -/
theorem call_admits_iff (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (seed : Point V A Q C Sym typeArity valueArity reserved)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    {Θ : Type} {ν : Θ → A} (injective : Function.Injective ν) (fresh : Avoids ν C₀.equations)
    {n : Nat} (sig : Signature Θ Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity) :
    (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (callFiring ν sig Γ₀ Γ₁ args out) ↔
      ∃ ρ : Point V A Q C Sym typeArity valueArity reserved, Holds decls reserved ρ C₀.equations ∧
        Joint decls reserved sig Γ₀ Γ₁ (fun i => (args i).evaluate ρ.values) (out.evaluate ρ.values) := by
  rw [callFiring, tell_admits_iff, consistent_iff seed]
  constructor
  · rintro ⟨ρ, holds⟩
    obtain ⟨old, tells⟩ := holds_append.mp holds
    obtain ⟨inputs, result⟩ := (holds_callTells ν sig Γ₀ Γ₁ args out ρ).mp tells
    exact ⟨ρ, old, ρ.types ∘ ν, fun t => ρ.proper (ν t), inputs, result⟩
  · rintro ⟨ρ, old, θ, proper, inputs, result⟩
    refine ⟨ρ.reassign ν θ proper, holds_append.mpr ⟨(holds_reassign fresh ρ θ proper).mpr old, ?_⟩⟩
    have types : (ρ.reassign ν θ proper).types ∘ ν = θ :=
      funext fun t => Point.reassign_types_apply ρ injective θ proper t
    apply (holds_callTells ν sig Γ₀ Γ₁ args out _).mpr
    rw [types]
    exact ⟨inputs, result⟩

/-- **Adequacy for closed values (`Joint_d`).** From solvable knowledge, the typed-call firing on
closed inputs and a closed result is admitted exactly when one proper assignment admits the inputs
at the entry view and the result at the return view. -/
theorem closed_call_admits_iff (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    (solvable : ∃ ρ : Point V A Q C Sym typeArity valueArity reserved, Holds decls reserved ρ C₀.equations)
    {Θ : Type} {ν : Θ → A} (injective : Function.Injective ν) (fresh : Avoids ν C₀.equations)
    {n : Nat} (sig : Signature Θ Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → VTree Sym valueArity) (out : VTree Sym valueArity) :
    (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (callFiring ν sig Γ₀ Γ₁ (fun i => ofTree (args i)) (ofTree out)) ↔
      Joint decls reserved sig Γ₀ Γ₁ args out := by
  obtain ⟨seed, old⟩ := solvable
  rw [call_admits_iff label seed C₀ injective fresh]
  simp only [evaluate_ofTree]
  exact ⟨fun ⟨_, _, joint⟩ => joint, fun joint => ⟨seed, old, joint⟩⟩

/-- **Closed calls are decided by the existing staged checker.** Without reserved names, the
typed-call firing on closed values is admitted exactly when `CallTyping.resultAccepted` accepts the
result against the frame prepared from the inputs. -/
theorem closed_call_admits_iff_accepted [DecidableEq P] [DecidableEq U] [DecidableEq Q]
    [DecidableEq C] [DecidableEq Sym] {Mode : Type} (observe : Ctx → Mode → VTree Sym valueArity → Bool)
    (closedSeed : Closed Q C typeArity) (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (noReserved : ∀ q, ¬ reserved q) (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    (solvable : ∃ ρ : Point V A Q C Sym typeArity valueArity reserved, Holds decls reserved ρ C₀.equations)
    {ν : P → A} (injective : Function.Injective ν) (fresh : Avoids ν C₀.equations)
    {n : Nat} (sig : Signature P Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → VTree Sym valueArity) (out : VTree Sym valueArity) :
    (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (callFiring ν sig Γ₀ Γ₁ (fun i => ofTree (args i)) (ofTree out)) ↔
      CallTyping.resultAccepted (DeclarationTyping.asSystem decls) observe Γ₁ out
        (CallTyping.prepare (DeclarationTyping.asSystem decls) observe Γ₀ args
          [asDeclaration Mode sig]) = true := by
  rw [closed_call_admits_iff label C₀ solvable injective fresh, joint_iff_allowed noReserved observe,
    CallTyping.resultAccepted_iff closedSeed]

/-! ## The runtime's residual formula -/

/-- The proper-membership queries of one call, as the open compiler takes them. -/
def callQueries {n : Nat} (sig : Signature P Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity) :
    List (OpenTyping.Query V P Q C Sym Ctx typeArity valueArity) :=
  (List.finRange n).map (fun i => ⟨Γ₀, args i, sig.argument i⟩) ++ [⟨Γ₁, out, sig.result⟩]

theorem joint_iff_queries (noReserved : ∀ q, ¬ reserved q) {n : Nat} (sig : Signature P Q C typeArity n)
    (Γ₀ Γ₁ : Ctx) (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity)
    (values : V → VTree Sym valueArity) :
    Joint decls reserved sig Γ₀ Γ₁ (fun i => (args i).evaluate values) (out.evaluate values) ↔
      ∃ θ : P → Closed Q C typeArity, ∀ query ∈ callQueries sig Γ₀ Γ₁ args out,
        DeclarationTyping.HasType decls query.context (query.value.evaluate values)
          (query.type.substitute θ) := by
  simp only [Joint, callQueries, List.forall_mem_append, List.forall_mem_map, List.mem_finRange,
    true_implies, List.mem_singleton, forall_eq]
  constructor
  · rintro ⟨θ, _, inputs, result⟩
    exact ⟨θ, inputs, result⟩
  · rintro ⟨θ, inputs, result⟩
    exact ⟨θ, fun _ q _ => noReserved q, inputs, result⟩

/-- **Admission is a binding satisfying the runtime's residual formula.** Without reserved names, the
typed-call firing is admitted exactly when some point satisfying the old knowledge satisfies the
formula `OpenTyping.compileOverloads` keeps for the call. -/
theorem call_admits_iff_residual [DecidableEq P] (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (noReserved : ∀ q, ¬ reserved q) (seed : Point V A Q C Sym typeArity valueArity reserved)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    {ν : P → A} (injective : Function.Injective ν) (fresh : Avoids ν C₀.equations)
    {n : Nat} (sig : Signature P Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity) :
    (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (callFiring ν sig Γ₀ Γ₁ args out) ↔
      ∃ ρ : Point V A Q C Sym typeArity valueArity reserved, Holds decls reserved ρ C₀.equations ∧
        ResidualConstraints.alternativesModel
          (OpenTyping.compileOverloads decls [callQueries sig Γ₀ Γ₁ args out])
          (OpenTyping.model decls ρ.values) Empty.elim := by
  rw [call_admits_iff label seed C₀ injective fresh]
  refine exists_congr fun ρ => and_congr Iff.rfl ?_
  rw [joint_iff_queries noReserved, OpenTyping.compileOverloads_correct]
  simp only [List.mem_singleton, exists_eq_left]

/-- **What the runtime decides.** The type equations of the residual formula are decided by the
total unifier. If no alternative's equations are satisfiable, no binding meets the requirement, so
the step refuses the call too: an admitted call passes the runtime's decided check. -/
theorem runtime_accepts_of_admits [DecidableEq P] [DecidableEq Q] [DecidableEq C]
    (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (noReserved : ∀ q, ¬ reserved q) (seed : Point V A Q C Sym typeArity valueArity reserved)
    (closedSeed : Closed Q C typeArity)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O)
    {ν : P → A} (injective : Function.Injective ν) (fresh : Avoids ν C₀.equations)
    {n : Nat} (sig : Signature P Q C typeArity n) (Γ₀ Γ₁ : Ctx)
    (args : Fin n → OpenTree V Sym valueArity) (out : OpenTree V Sym valueArity)
    (admitted : (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (callFiring ν sig Γ₀ Γ₁ args out)) :
    ScopedConstraints.accept
      ((OpenTyping.compileOverloads decls [callQueries sig Γ₀ Γ₁ args out]).map
        ResidualConstraints.Problem.equations) = true := by
  obtain ⟨ρ, _, problem, member, inner, solved, _⟩ :=
    (call_admits_iff_residual label noReserved seed C₀ injective fresh sig Γ₀ Γ₁ args out).mp admitted
  rw [ScopedConstraints.accept_closed_iff closedSeed]
  exact ⟨problem.equations, List.mem_map.mpr ⟨problem, member, rfl⟩, inner, solved⟩

/-! ## Guards versus tells -/

/-- A membership as a guard: the check `member Γ v τ ≐ yes`, asked at every solution. -/
def guard (Γ : Ctx) (v : OpenTree V Sym valueArity) (τ : Expr A Q C typeArity) :
    Check (Term Ctx V A Q C Sym typeArity valueArity) :=
  .equal (.member Γ v τ) .yes

omit [DecidableEq O] in
/-- **A closed membership with no helpers is a guard.** For a closed value and a closed type, the
guard holds at a solution exactly when the membership holds. -/
theorem guard_holds_iff (label : O → Term Ctx V A Q C Sym typeArity valueArity) (present : Finset O)
    (seed : Point V A Q C Sym typeArity valueArity reserved)
    (σ : Instantiation V A Q C Sym typeArity valueArity reserved) (Γ : Ctx) (v : VTree Sym valueArity)
    (τ : Closed Q C typeArity) :
    (guard Γ (ofTree v) (embedClosed τ)).Holds (action decls reserved) σ label present ↔
      DeclarationTyping.HasType decls Γ v τ := by
  change (∀ ρ : Point V A Q C Sym typeArity valueArity reserved,
    ((Term.member Γ (ofTree v) (embedClosed τ)).subst σ).meaning decls ρ =
      ((Term.yes : Term Ctx V A Q C Sym typeArity valueArity).subst σ).meaning decls ρ) ↔ _
  simp only [Term.meaning_subst]
  simp only [Term.meaning, evaluate_ofTree, close_embed, Meaning.truth.injEq, eq_iff_iff, iff_true]
  exact ⟨fun holds => holds seed, fun holds _ => holds⟩

/-- **The guard reading and the tell reading agree on closed memberships with no helpers.** -/
theorem guard_admits_iff (label : O → Term Ctx V A Q C Sym typeArity valueArity)
    (seed : Point V A Q C Sym typeArity valueArity reserved)
    (C₀ : Configuration (Term Ctx V A Q C Sym typeArity valueArity) O) (Γ : Ctx)
    (v : VTree Sym valueArity) (τ : Closed Q C typeArity) :
    (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (⟨⟨[], [], [], [guard Γ (ofTree v) (embedClosed τ)], []⟩, [], ⟨[], [], []⟩⟩ :
          AnnotatedRuns.Firing (Term Ctx V A Q C Sym typeArity valueArity)
            (Instantiation V A Q C Sym typeArity valueArity reserved) O) ↔
      (AnnotatedRuns.firstOrder (action decls reserved) label).Admits (s := C₀)
        (tellFiring [require Γ (ofTree v) (embedClosed τ)]) := by
  rw [checked_admits_iff, tell_admits_iff, consistent_iff seed, consistent_iff seed]
  simp only [List.append_nil, List.mem_singleton, forall_eq]
  have constant : ∀ ρ : Point V A Q C Sym typeArity valueArity reserved,
      Holds decls reserved ρ [require Γ (ofTree v) (embedClosed τ)] ↔
        DeclarationTyping.HasType decls Γ v τ := by
    intro ρ
    rw [holds_require, evaluate_ofTree, close_embed]
  constructor
  · rintro ⟨⟨ρ, holds⟩, asked⟩
    obtain ⟨σ, solved⟩ := (consistent_iff seed C₀.equations).mpr ⟨ρ, holds⟩
    have member := (guard_holds_iff label C₀.present seed σ Γ v τ).mp (asked σ solved)
    exact ⟨ρ, holds_append.mpr ⟨holds, (constant ρ).mpr member⟩⟩
  · rintro ⟨ρ, holds⟩
    obtain ⟨old, tell⟩ := holds_append.mp holds
    exact ⟨⟨ρ, old⟩, fun σ _ => (guard_holds_iff label C₀.present seed σ Γ v τ).mpr ((constant ρ).mp tell)⟩

#print axioms consistent_iff
#print axioms holds_require
#print axioms joint_iff_allowed
#print axioms joint_permute
#print axioms tell_admits_iff
#print axioms call_admits_iff
#print axioms closed_call_admits_iff
#print axioms closed_call_admits_iff_accepted
#print axioms call_admits_iff_residual
#print axioms runtime_accepts_of_admits
#print axioms guard_holds_iff
#print axioms guard_admits_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TypingFirings
