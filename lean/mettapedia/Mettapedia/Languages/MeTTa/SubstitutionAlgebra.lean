import Mathlib.Data.List.Basic
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Substitution as an algebra

These laws identify which term construction is semantically necessary when a
first-order simultaneous substitution is observed. They do not assign a
physical allocation cost; that belongs to a separately validated realization.

* Substitution depends only on the variables occurring in the term
  (`subst_congr_on_vars`).  Substitution is the identity on a ground term
  (`subst_of_vars_eq_nil`), which licenses—but does not itself prove—physical
  reuse, and a term paired with an environment may narrow that environment to
  the term's support (`subst_restrict_vars`).
* Two substitutions in sequence are one substitution by the composed
  environment (`subst_subst`).  An implementation may therefore compose
  environments and materialise a term at most once, at observation.
* Substitutions whose supports do not touch commute (`comp_comm_of_disjoint`).
  This licenses reordering at an explicit conjunction or reconciliation
  boundary.  Disjunctive answers remain separate environments and require no
  merge operation.

This is the algebra of explicit substitutions (Abadi, Cardelli, Curien and
Lévy) over the shared first-order `OSLFCore.Atom` carrier. A dialect operation
uses these laws when it implements this substitution contract. Opaque quotation
and binding-aware object-language substitution have separate contracts; the
shared atom datatype alone does not identify them with this operation.
-/

namespace Mettapedia.Languages.MeTTa.SubstitutionAlgebra

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Simultaneous substitution and its support -/

/-- Variable names, as MeTTa spells them. -/
abbrev Var := String

/-- A simultaneous substitution: what an environment offers for each variable. -/
abbrev Subst := Var → Option Atom

/-- The substitution which binds no variable. -/
def empty : Subst := fun _ => none

/-- Variables occurring in an atom, in occurrence order. -/
def vars : Atom → List Var
  | .var v => [v]
  | .expression es => varsList es
  | .symbol _ => []
  | .grounded _ => []
where
  varsList : List Atom → List Var
    | [] => []
    | a :: as => vars a ++ varsList as

/-- One-pass simultaneous substitution.  An unbound variable stays itself. -/
def subst (σ : Subst) : Atom → Atom
  | .var v => (σ v).getD (.var v)
  | .expression es => .expression (substList σ es)
  | .symbol s => .symbol s
  | .grounded g => .grounded g
where
  substList (σ : Subst) : List Atom → List Atom
    | [] => []
    | a :: as => subst σ a :: substList σ as

/-- Restrict a substitution to a set of variables. -/
def restrict (σ : Subst) (support : List Var) : Subst :=
  fun v => if v ∈ support then σ v else none

/-- Composition of substitutions: apply `σ`, then `τ` to what `σ` produced,
falling through to `τ` where `σ` is silent. -/
def comp (σ τ : Subst) : Subst :=
  fun v =>
    match σ v with
    | some a => some (subst τ a)
    | none => τ v

theorem substList_congr (σ τ : Subst) (as : List Atom)
    (ih : ∀ a ∈ as, (∀ v ∈ vars a, σ v = τ v) → subst σ a = subst τ a)
    (h : ∀ v ∈ vars.varsList as, σ v = τ v) :
    subst.substList σ as = subst.substList τ as := by
  induction as with
  | nil => rfl
  | cons a as ihs =>
    simp only [subst.substList]
    have ha : ∀ v ∈ vars a, σ v = τ v := fun v hv =>
      h v (by simp [vars.varsList, hv])
    have has : ∀ v ∈ vars.varsList as, σ v = τ v := fun v hv =>
      h v (by simp [vars.varsList, hv])
    rw [ih a (List.mem_cons_self ..) ha,
      ihs (fun b hb => ih b (List.mem_cons_of_mem a hb)) has]

/-- Substitution depends only on the variables that occur in the term. -/
theorem subst_congr_on_vars (σ τ : Subst) (a : Atom)
    (h : ∀ v ∈ vars a, σ v = τ v) : subst σ a = subst τ a := by
  match a with
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .var v =>
    simp only [subst]
    rw [h v (by simp [vars])]
  | .expression es =>
    simp only [subst]
    rw [substList_congr σ τ es
      (fun b _ hb => subst_congr_on_vars σ τ b hb) (by simpa [vars] using h)]
termination_by sizeOf a

/-- The empty substitution is the identity on every atom. -/
theorem subst_empty (a : Atom) : subst empty a = a := by
  match a with
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .var _ => rfl
  | .expression es =>
    simp only [subst]
    rw [substList_empty es (fun b _ => subst_empty b)]
where
  substList_empty (as : List Atom)
      (ih : ∀ a ∈ as, subst empty a = a) :
      subst.substList empty as = as := by
    induction as with
    | nil => rfl
    | cons first rest inductionHypothesis =>
      simp only [subst.substList]
      rw [ih first (List.mem_cons_self ..),
        inductionHypothesis
          (fun b member => ih b (List.mem_cons_of_mem first member))]
/-- Substitution is extensionally inert on a ground term.  A runtime may use
this equality to return the existing representation without traversing or
rebuilding it; physical reuse is not part of this theorem. -/
theorem subst_of_vars_eq_nil (σ : Subst) (a : Atom) (h : vars a = []) :
    subst σ a = a := by
  have same : subst σ a = subst empty a :=
    subst_congr_on_vars σ empty a (by simp [h])
  rw [same, subst_empty]

/-- An environment may be narrowed to the term's own support without
changing the result: the exactness law for closures `(term, env|support)`. -/
theorem subst_restrict_vars (σ : Subst) (a : Atom) :
    subst (restrict σ (vars a)) a = subst σ a :=
  subst_congr_on_vars _ _ a (fun v hv => by simp [restrict, hv])

theorem substList_comp (σ τ : Subst) (as : List Atom)
    (ih : ∀ a ∈ as, subst τ (subst σ a) = subst (comp σ τ) a) :
    subst.substList τ (subst.substList σ as) = subst.substList (comp σ τ) as := by
  induction as with
  | nil => rfl
  | cons a as ihs =>
    simp only [subst.substList]
    rw [ih a (List.mem_cons_self ..),
      ihs (fun b hb => ih b (List.mem_cons_of_mem a hb))]

/-- Sequential application is one application of the composed environment:
the license for composing environments instead of rebuilding terms. -/
theorem subst_subst (σ τ : Subst) (a : Atom) :
    subst τ (subst σ a) = subst (comp σ τ) a := by
  match a with
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .var v =>
    simp only [subst, comp]
    cases σ v <;> simp [subst]
  | .expression es =>
    simp only [subst]
    rw [substList_comp σ τ es (fun b _ => subst_subst σ τ b)]
termination_by sizeOf a

/-- The empty substitution is a left identity for composition. -/
@[simp] theorem empty_comp (σ : Subst) : comp empty σ = σ := by
  funext v
  simp [comp, empty]

/-- The empty substitution is a right identity for composition. -/
@[simp] theorem comp_empty (σ : Subst) : comp σ empty = σ := by
  funext v
  cases bound : σ v with
  | none => simp [comp, empty, bound]
  | some a => simp [comp, bound, subst_empty]

/-- Composition is associative.  A chain of suspended substitutions therefore
has one canonical environment regardless of how a runtime batches it. -/
theorem comp_assoc (σ τ υ : Subst) :
    comp (comp σ τ) υ = comp σ (comp τ υ) := by
  funext v
  cases bound : σ v with
  | none => simp [comp, bound]
  | some a => simp [comp, bound, subst_subst]

/-! ## Closures: a term paired with its environment -/

/-- A suspended substitution.  Materialising it is `force`. -/
abbrev Closure := Atom × Subst

/-- Materialise a closure. -/
def force (c : Closure) : Atom := subst c.2 c.1

/-- Extend a closure without materialising its term. -/
def extend (c : Closure) (τ : Subst) : Closure :=
  (c.1, comp c.2 τ)

/-- A closure may carry only the environment its term can see. -/
theorem force_restrict (a : Atom) (σ : Subst) :
    force (a, restrict σ (vars a)) = force (a, σ) :=
  subst_restrict_vars σ a

/-- Substituting into a materialised closure is materialising a closure with
a composed environment; nothing intermediate need exist. -/
theorem force_subst (a : Atom) (σ τ : Subst) :
    subst τ (force (a, σ)) = force (a, comp σ τ) :=
  subst_subst σ τ a

/-- Extending a closure and then forcing it is exactly one composed
substitution application. -/
theorem force_extend (c : Closure) (τ : Subst) :
    force (extend c τ) = subst τ (force c) := by
  rcases c with ⟨a, σ⟩
  exact (force_subst a σ τ).symm

/-- Repeated closure extension is associative at the representation level. -/
theorem extend_assoc (c : Closure) (σ τ : Subst) :
    extend (extend c σ) τ = extend c (comp σ τ) := by
  rcases c with ⟨a, υ⟩
  simp only [extend]
  rw [comp_assoc]

/-! ## Independent supports commute -/

/-- The variables a substitution is silent on. -/
def SilentOn (σ : Subst) (a : Atom) : Prop := ∀ v ∈ vars a, σ v = none

/-- A substitution silent on every variable of a term leaves it unchanged. -/
theorem subst_eq_self_of_silentOn (σ : Subst) (a : Atom) (h : SilentOn σ a) :
    subst σ a = a := by
  have hid : subst σ a = subst (fun _ => none) a :=
    subst_congr_on_vars σ (fun _ => none) a (fun v hv => by simp [h v hv])
  rw [hid]
  exact subst_empty a

/-- Two substitutions are independent when neither binds a variable the other
binds, and neither mentions the other's domain in its values. -/
structure Independent (σ τ : Subst) : Prop where
  /-- No variable is bound by both. -/
  disjoint : ∀ v, σ v = none ∨ τ v = none
  /-- Values produced by `σ` do not mention variables `τ` binds. -/
  left_silent : ∀ v a, σ v = some a → SilentOn τ a
  /-- Values produced by `τ` do not mention variables `σ` binds. -/
  right_silent : ∀ v a, τ v = some a → SilentOn σ a

/-- Independent substitutions compose in either order: the extensions made by
independent branches of a search may be merged commutatively. -/
theorem comp_comm_of_disjoint (σ τ : Subst) (h : Independent σ τ) :
    comp σ τ = comp τ σ := by
  funext v
  cases hσ : σ v with
  | none =>
    cases hτ : τ v with
    | none => simp [comp, hσ, hτ]
    | some b =>
      simp [comp, hσ, hτ, subst_eq_self_of_silentOn σ b (h.right_silent v b hτ)]
  | some a =>
    cases hτ : τ v with
    | none =>
      simp [comp, hσ, hτ, subst_eq_self_of_silentOn τ a (h.left_silent v a hσ)]
    | some b =>
      exfalso
      rcases h.disjoint v with h1 | h1
      · exact absurd h1 (by simp [hσ])
      · exact absurd h1 (by simp [hτ])

/-! ## Syntax insertion and finite unification

Here `quote` is an ordinary expression constructor: it may inhibit evaluation,
but this first-order substitution algebra does not make it a binder or a scope
boundary. A staged language with opaque quotation needs a different operation.

A one-pass substitution may insert a term that contains its domain variable.
That does not make it a unifier of the variable and that term, and applying the
substitution again need not be inert. These laws separate syntax construction
from the acyclic logical-store contract without choosing a dialect's `let` rule.
-/

namespace Insertion

/-- Substitute one variable, leaving other variables untouched. -/
def single (v : Var) (value : Atom) : Subst :=
  fun name => if name = v then some value else none

/-- An ordinary unary expression, including syntax such as `(quote payload)`. -/
def wrap (head : String) (payload : Atom) : Atom :=
  .expression [.symbol head, payload]

@[simp] theorem subst_single_variable (v : Var) (value : Atom) :
    subst (single v value) (.var v) = value := by
  simp [subst, single]

@[simp] theorem subst_wrap (σ : Subst) (head : String) (payload : Atom) :
    subst σ (wrap head payload) = wrap head (subst σ payload) := by
  simp [wrap, subst, subst.substList]

/-- Insertion in a template does not recursively insert into the supplied value. -/
theorem insert_into_quoted_template (v : Var) (head : String) (value : Atom) :
    subst (single v value) (wrap "quote" (wrap head (.var v))) =
      wrap "quote" (wrap head value) := by
  simp

/-- The requested nested quotation is an ordinary, finite substitution result,
even though the supplied value contains the substituted variable. -/
theorem self_containing_quotation_is_constructible (v : Var) :
    subst (single v (wrap "quote" (wrap "f" (.var v))))
      (wrap "quote" (wrap "g" (.var v))) =
    wrap "quote" (wrap "g" (wrap "quote" (wrap "f" (.var v)))) :=
  insert_into_quoted_template v "g" _

/-- A finite tree cannot equal two new constructors wrapped around itself. -/
theorem finite_atom_ne_double_wrap (atom : Atom) (outer inner : String) :
    atom ≠ wrap outer (wrap inner atom) := by
  intro equal
  have sizes := congrArg sizeOf equal
  simp [wrap] at sizes
  omega

/-- No substitution into finite atoms solves `x = (quote (f x))` when quote
is an ordinary constructor and the two occurrences denote the same variable. -/
theorem self_containing_quotation_has_no_finite_unifier (σ : Subst) (v : Var) :
    subst σ (.var v) ≠
      subst σ (wrap "quote" (wrap "f" (.var v))) := by
  simp only [subst_wrap]
  exact finite_atom_ne_double_wrap _ "quote" "f"

/-- Reapplying the insertion descends into the previously inserted value and
changes it. This is the negative control for one-pass materialization. -/
theorem self_insertion_is_not_idempotent (v : Var) :
    let σ := single v (wrap "quote" (wrap "f" (.var v)))
    subst σ (subst σ (.var v)) ≠ subst σ (.var v) := by
  dsimp
  simp only [subst_single_variable, subst_wrap]
  exact (finite_atom_ne_double_wrap _ "quote" "f").symm

/-- A distinct destination constructs the same quoted result while leaving
the payload's variable free: no recursive logical equation is required. -/
theorem fresh_destination_preserves_payload (destination payloadVariable : Var)
    (distinct : payloadVariable ≠ destination) :
    let value := wrap "quote" (wrap "f" (.var payloadVariable))
    let σ := single destination value
    subst σ (wrap "quote" (wrap "g" (.var destination))) =
        wrap "quote" (wrap "g" value) ∧
      subst σ value = value := by
  dsimp
  constructor
  · exact insert_into_quoted_template _ _ _
  · simp [subst, single, distinct]

/-- In contrast with self-binding, the fresh-destination substitution really
is a unifier: both sides are sent to the same finite value. -/
theorem fresh_destination_is_finite_unifier (destination payloadVariable : Var)
    (distinct : payloadVariable ≠ destination) :
    let value := wrap "quote" (wrap "f" (.var payloadVariable))
    let σ := single destination value
    subst σ (.var destination) = subst σ value := by
  dsimp
  rw [subst_single_variable,
    (fresh_destination_preserves_payload destination payloadVariable distinct).2]

end Insertion

#print axioms Insertion.self_containing_quotation_is_constructible
#print axioms Insertion.self_containing_quotation_has_no_finite_unifier
#print axioms Insertion.self_insertion_is_not_idempotent
#print axioms Insertion.fresh_destination_preserves_payload
#print axioms Insertion.fresh_destination_is_finite_unifier
#print axioms subst_congr_on_vars
#print axioms subst_of_vars_eq_nil
#print axioms subst_restrict_vars
#print axioms subst_subst
#print axioms comp_assoc
#print axioms force_restrict
#print axioms force_extend
#print axioms comp_comm_of_disjoint

end Mettapedia.Languages.MeTTa.SubstitutionAlgebra
