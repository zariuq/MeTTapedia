import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderConservativeExtension
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Crossing

/-!
# Scope support and preservation of unreachable caller components

Lexically fresh pattern names have local identities; crossing retains shared
identities. Support avoidance connects these existing scope operations to the
equation-extension theorem. The protected component must be closed under old
equations: merely omitting a written root does not hide its passed alias.

Solver relevance fixes variables outside the solver's complete input support.
It must not be applied only to new equations while ignoring old aliases.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderScopeNoninterference

open Mettapedia.Logic.LP
open FirstOrderAskLocality FirstOrderConservativeExtension

universe u v
variable {signature : LPSignature.{u, u, v, u}} [DecidableEq signature.vars]

theorem avoids_iff_eqVars (component : Set signature.vars) (equations : EquationStore (Term signature)) :
    Avoids component equations ↔ ∀ name ∈ eqVars equations, name ∉ component := by
  constructor
  · intro avoids name member
    obtain ⟨equation, inEquations, occurs⟩ := mem_eqVars.mp member
    exact avoids equation inEquations name (Finset.mem_union.mpr occurs)
  · intro outside equation member name occurs
    exact outside name (mem_eqVars.mpr ⟨equation, member, Finset.mem_union.mp occurs⟩)

theorem avoids_of_supported_disjoint (component exposed : Set signature.vars)
    (equations : EquationStore (Term signature))
    (supported : ∀ name ∈ eqVars equations, name ∈ exposed)
    (separate : Disjoint component exposed) : Avoids component equations := by
  apply (avoids_iff_eqVars component equations).mpr
  intro name member inside
  exact Set.disjoint_left.mp separate inside (supported name member)

/-- Relevance concerns all equations supplied to this solver invocation. -/
theorem accepted_fixes_avoided [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
    (component : Set signature.vars) (equations : EquationStore (Term signature))
    (answer : Subst signature) (accepted : unifyTotal equations = some answer)
    (avoids : Avoids component equations) (name : signature.vars) (inside : name ∈ component) :
    answer name = .var name := by
  apply (unifyTotal_relevantIdempotent equations answer accepted).fixes name
  intro member
  exact (avoids_iff_eqVars component equations).mp avoids name member inside

theorem plain_pattern_has_no_shared_support (scope : Nat) (used : List signature.vars)
    (term : Term signature) (supported : ∀ name ∈ term.freeVars, name ∈ used)
    (name : signature.vars) :
    Sum.inr name ∉ (Crossing.termAt scope none used term).freeVars := by
  intro member
  obtain ⟨source, inTerm, image⟩ :=
    (Term.mem_freeVars_renameVars (Crossing.nameAt scope none used) term (.inr name)).mp member
  rw [Crossing.plain_pattern_is_fresh scope used source (supported source inTerm)] at image
  cases image

/-- Crossing makes the existing shared identity genuinely present in support. -/
theorem crossed_name_occurs_as_shared (scope : Nat) (crossing used : List signature.vars)
    (term : Term signature) (name : signature.vars)
    (occurs : name ∈ term.freeVars) (crossed : name ∈ crossing) :
    Sum.inr name ∈ (Crossing.termAt scope (some crossing) used term).freeVars :=
  (Term.mem_freeVars_renameVars (Crossing.nameAt scope (some crossing) used) term (.inr name)).mpr
    ⟨name, occurs, Crossing.crossed_name_is_shared scope crossing used name crossed⟩

theorem conservative_of_supported_addition (component exposed : Set signature.vars)
    (old added : EquationStore (Term signature)) (closed : Closed component old)
    (supported : ∀ name ∈ eqVars added, name ∈ exposed)
    (separate : Disjoint component exposed)
    (consistent : (FirstOrder.action signature).Consistent (old ++ added)) :
    ConservativeOn component old (old ++ added) :=
  conservative_of_closed_avoiding component old added closed
    (avoids_of_supported_disjoint component exposed added supported separate) consistent

theorem selected_conservative_of_supported_addition {O : Type*} [DecidableEq O]
    (component exposed : Set signature.vars) (label : O → Term signature)
    (rule : RuleInstance (Term signature)) (picked : Selection O) (before : Configuration (Term signature) O)
    (valid : picked.Valid (FirstOrder.action signature) label rule before)
    (closed : Closed component before.equations)
    (supported : ∀ name ∈ eqVars (GuardFreeProcessOrders.added label rule picked), name ∈ exposed)
    (separate : Disjoint component exposed) :
    ConservativeOn component before.equations (picked.result label rule before).equations :=
  selected_conservative_of_closed_avoiding component label rule picked before valid closed
    (avoids_of_supported_disjoint component exposed _ supported separate)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderScopeNoninterference
