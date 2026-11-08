import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDispatch

/-!
# Heterogeneous equations: postponement and wake-up

An equation of the store compares two judged terms whose types need not be known to agree.
It holds at a solution exactly when its **type equation** holds there and its terms are equal at
the left type (`solves_iff`). Such an equation is kept heterogeneous until its type equation is
solved, following Gundry and McBride: the two sides keep their own types, and nothing is
assumed about the types before they are shown equal.

* **Postponement loses no solution**: an equation moved behind the rest of the store, or kept
  while the rest is solved, keeps exactly the solutions of the store (`postpone`, `defer`).
* **Wake-up**: once an answer makes the type equation hold, the transported equation is aligned
  at the left type: its right side is retyped by the type equation, with the same solutions at
  every later context (`wake`, `wake_equivalent`). An update of the rest of the store whose
  answer solves the type equation becomes an update of the whole store whose residual starts with
  that homogeneous equation (`wakeAfter`, `wakeAfter_remaining`).
* The type equation is solved by such an answer whenever the rest of the store entails it and
  the update finished (`typesAgree_of_entails`); in any case it holds at every solution of the
  residual store (`typesAgree_of_residual`).

Agreement of types is stable under further instantiation (`TypesAgree.comp`), so a woken
equation stays homogeneous at every later context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentTwins

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentDispatch

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

/-! ## The type equation of an equation -/

/-- **The type equation** of an equation holds at a solution: its endpoint types agree there. -/
def TypesAgree {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (equation : Equation (TotalTerm Γ)) : Prop :=
  TypeEq rules Δ.raw (subst σ.substitution equation.1.1.code)
    (subst σ.substitution equation.2.1.code)

variable (levels : LevelModel rules L)

/-- **A heterogeneous equation holds** exactly when its type equation holds and its endpoints
are equal at the left type. -/
theorem solves_iff {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (equation : Equation (TotalTerm Γ)) :
    (frames levels).Solves σ equation ↔
      TypesAgree σ equation ∧
        Equal rules Δ.raw (subst σ.substitution equation.1.2.code)
          (subst σ.substitution equation.2.2.code) (subst σ.substitution equation.1.1.code) :=
  equivalent_iff levels _ _

theorem typesAgree_of_solves {Γ Δ : Context rules} {σ : Δ ⟶ Γ}
    {equation : Equation (TotalTerm Γ)} (solved : (frames levels).Solves σ equation) :
    TypesAgree σ equation :=
  ((solves_iff levels σ equation).mp solved).1

/-- **Agreement of types survives further instantiation.** -/
theorem TypesAgree.comp {Γ Δ Θ : Context rules} {σ : Δ ⟶ Γ}
    {equation : Equation (TotalTerm Γ)} (agree : TypesAgree σ equation) (τ : Θ ⟶ Δ) :
    TypesAgree (τ ≫ σ) equation := by
  have moved := reindex_typeEquality agree τ
  rw [subst_subComp, subst_subComp] at moved
  exact moved

/-! ## Postponement -/

theorem postpone_equivalent {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    (rest : EquationStore (TotalTerm Γ)) :
    (frames levels).Equivalent (equation :: rest) (rest ++ [equation]) := by
  intro Δ σ
  constructor
  · intro solved entry member
    rcases List.mem_append.mp member with inRest | inLast
    · exact solved entry (List.mem_cons.mpr (.inr inRest))
    · obtain rfl := List.mem_singleton.mp inLast
      exact solved _ (List.mem_cons.mpr (.inl rfl))
  · intro solved entry member
    rcases List.mem_cons.mp member with rfl | inRest
    · exact solved _ (List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl)))
    · exact solved entry (List.mem_append.mpr (.inl inRest))

/-- **Postponing an equation loses no solution**: the store with the equation moved behind the
rest has exactly the same solutions. -/
def postpone {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    (rest : EquationStore (TotalTerm Γ)) : Update levels (equation :: rest) :=
  (Update.pending levels (rest ++ [equation])).rephrase (postpone_equivalent levels equation rest)

theorem postpone_remaining {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    (rest : EquationStore (TotalTerm Γ)) :
    (postpone levels equation rest).remaining = rest ++ [equation] := rfl

/-- **Keeping an equation while the rest is solved loses no solution**: it is transported along
the answer of the rest, and the combined update factors every solution of the whole store. -/
def defer {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    {rest : EquationStore (TotalTerm Γ)} (update : Update levels rest) :
    Update levels (equation :: rest) :=
  update.keepLeft [equation]

theorem defer_remaining {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    {rest : EquationStore (TotalTerm Γ)} (update : Update levels rest) :
    (defer levels equation update).remaining =
      ((frames levels).act update.answer equation.1, (frames levels).act update.answer equation.2)
        :: update.remaining := rfl

/-! ## Wake-up -/

variable {levels}

/-- **Wake-up**: once an answer makes the type equation hold, the transported equation is
aligned at the transported left type. The right side keeps its term and is retyped by the type
equation. -/
def wake {Γ M : Context rules} (θ : M ⟶ Γ) (equation : Equation (TotalTerm Γ))
    (agree : TypesAgree θ equation) :
    Aligned levels (equation.1.1.reindex θ)
      ((frames levels).act θ equation.1, (frames levels).act θ equation.2) where
  left := (equation.1.reindex θ).2
  right := (equation.2.reindex θ).2.convertType (equation.1.1.reindex θ) (TypeEq.symm agree)
  leftSame := ((frames levels).equivalence M).refl _
  rightSame := ⟨TypeEq.symm agree, .refl (equation.2.reindex θ).2.typed⟩

/-- The woken equation: both endpoints at the transported left type. -/
def woken {Γ M : Context rules} (θ : M ⟶ Γ) (equation : Equation (TotalTerm Γ))
    (agree : TypesAgree θ equation) : Equation (TotalTerm M) :=
  ((⟨equation.1.1.reindex θ, (equation.1.reindex θ).2⟩ : TotalTerm M),
    (⟨equation.1.1.reindex θ,
      (equation.2.reindex θ).2.convertType (equation.1.1.reindex θ) (TypeEq.symm agree)⟩ :
        TotalTerm M))

theorem woken_homogeneous {Γ M : Context rules} (θ : M ⟶ Γ) (equation : Equation (TotalTerm Γ))
    (agree : TypesAgree θ equation) :
    (woken θ equation agree).1.1 = (woken θ equation agree).2.1 := rfl

/-- The woken equation keeps the terms of the transported equation. -/
theorem woken_codes {Γ M : Context rules} (θ : M ⟶ Γ) (equation : Equation (TotalTerm Γ))
    (agree : TypesAgree θ equation) :
    (woken θ equation agree).1.2.code = subst θ.substitution equation.1.2.code ∧
      (woken θ equation agree).2.2.code = subst θ.substitution equation.2.2.code :=
  ⟨rfl, rfl⟩

/-- **The woken equation has the same solutions** as the transported heterogeneous one, beside
any further equations, at every later context. -/
theorem wake_equivalent {Γ M : Context rules} (θ : M ⟶ Γ) (equation : Equation (TotalTerm Γ))
    (agree : TypesAgree θ equation) (rest : EquationStore (TotalTerm M)) :
    (frames levels).Equivalent
      (((frames levels).act θ equation.1, (frames levels).act θ equation.2) :: rest)
      (woken θ equation agree :: rest) :=
  (wake θ equation agree).models_iff rest

/-- **Solve the type equation first, then wake the term equation.** An update of the rest of the
store whose answer solves the postponed equation's type equation is an update of the whole
store whose residual starts with the homogeneous woken equation. -/
def wakeAfter {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    {rest : EquationStore (TotalTerm Γ)} (update : Update levels rest)
    (agree : TypesAgree update.answer equation) : Update levels (equation :: rest) :=
  (defer levels equation update).then
    ((Update.pending levels (woken update.answer equation agree :: update.remaining)).rephrase
      (wake_equivalent update.answer equation agree update.remaining))

theorem wakeAfter_remaining {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    {rest : EquationStore (TotalTerm Γ)} (update : Update levels rest)
    (agree : TypesAgree update.answer equation) :
    (wakeAfter equation update agree).remaining =
      woken update.answer equation agree :: update.remaining := rfl

theorem wakeAfter_answer {Γ : Context rules} (equation : Equation (TotalTerm Γ))
    {rest : EquationStore (TotalTerm Γ)} (update : Update levels rest)
    (agree : TypesAgree update.answer equation) :
    (wakeAfter equation update agree).answer = 𝟙 update.target ≫ update.answer := rfl

/-- At every solution of the residual store, the type equation holds whenever the rest of the
store entails it. -/
theorem typesAgree_of_residual {Γ : Context rules} {equation : Equation (TotalTerm Γ)}
    {rest : EquationStore (TotalTerm Γ)} (update : Update levels rest)
    (entailed : (frames levels).Entails rest (fun _ σ => TypesAgree σ equation))
    {Δ : Context rules} (residual : Δ ⟶ update.target)
    (solved : (frames levels).Models residual update.remaining) :
    TypesAgree (residual ≫ update.answer) equation :=
  entailed Δ _ (update.sound Δ residual solved)

/-- **A finished update of the rest solves an entailed type equation at its answer**, so the
postponed equation wakes up there. -/
theorem typesAgree_of_entails {Γ : Context rules} {equation : Equation (TotalTerm Γ)}
    {rest : EquationStore (TotalTerm Γ)} (update : Update levels rest)
    (finished : update.remaining = [])
    (entailed : (frames levels).Entails rest (fun _ σ => TypesAgree σ equation)) :
    TypesAgree update.answer equation :=
  entailed _ _ (update.completed finished).sound

/-- Every equation entails its own type equation; so does every store containing it. -/
theorem entails_own_types {Γ : Context rules} {equation : Equation (TotalTerm Γ)}
    {store : EquationStore (TotalTerm Γ)} (member : equation ∈ store) :
    (frames levels).Entails store (fun _ σ => TypesAgree σ equation) :=
  fun _ _ solved => typesAgree_of_solves levels (solved equation member)

end ContextualDependentTwins
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
