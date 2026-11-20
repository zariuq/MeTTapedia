import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Correctness

/-!
# T2: the functional licence

A module is semantically exclusive (`Exclusive`) when two different rules never both hold at one
call. With range restriction and relation queries that bind no new variable (`QueriesBound`),
exclusivity makes `Derives` functional: a call has at most one value (`derives_functional`). Read by
demand, the closure then holds at most one value row per call (`valueRow_unique`).

Inside one rule the argument walks the premises in order: two substitutions that match the left side
to the same call agree on the left side's variables; a call premise's arguments are bound, so both
substitutions ask the same call, whose value is unique by induction, so they agree on the target's
variables; a query binds nothing new. They agree on the right side's variables at the end.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open OneFrame (Terms)
open SetStoreSyntax (consequence apply_eq_of_agree agree_of_apply_eq)

universe u

section Semantics

variable {ρ : LPSignature} [DecidableEq ρ.vars] {L : Type*} {M : L → ModuleRule ρ} {Rel : Set (Atom ρ)}

/-- **Two matches of one rule at one call agree on every bound variable**, when its calls are
functional at the first match and its queries bind nothing new. -/
theorem agree_on_bound (r : ModuleRule ρ) (rr : RangeRestricted r) (qb : QueriesBound r)
    {θ₁ θ₂ : Subst ρ} (sameLhs : θ₁.applyTerm r.lhs = θ₂.applyTerm r.lhs)
    (holds₂ : ∀ p ∈ r.premises, Holds M Rel θ₂ p)
    (functional : ∀ source target, Premise.call source target ∈ r.premises →
      ∀ w, Derives M Rel (θ₁.applyTerm source) w → θ₁.applyTerm target = w) :
    ∀ pre post, r.premises = pre ++ post → ∀ v ∈ r.bound pre, θ₁ v = θ₂ v := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro post _ v inside
    simp only [ModuleRule.bound, bindsAll, Finset.union_empty] at inside
    exact agree_of_apply_eq θ₁ θ₂ r.lhs sameLhs v inside
  | append_singleton pre p ih =>
    intro post split v inside
    have split' : r.premises = pre ++ p :: post := by simp [split]
    have earlier := ih (p :: post) split'
    have member : p ∈ r.premises := by rw [split']; exact List.mem_append_right _ List.mem_cons_self
    simp only [ModuleRule.bound, bindsAll_append, bindsAll, Finset.union_empty, Finset.mem_union] at inside
    rcases inside with inLhs | inPre | inP
    · exact earlier v (Finset.mem_union_left _ inLhs)
    · exact earlier v (Finset.mem_union_right _ inPre)
    · cases p with
      | call source target =>
        have sameSource : θ₁.applyTerm source = θ₂.applyTerm source :=
          apply_eq_of_agree θ₁ θ₂ source fun x mentions => earlier x (rr.calls pre source target post split' mentions)
        have second : Derives M Rel (θ₁.applyTerm source) (θ₂.applyTerm target) :=
          sameSource ▸ holds₂ _ member
        exact agree_of_apply_eq θ₁ θ₂ target (functional source target member _ second) v inP
      | query atom => exact earlier v (qb pre atom post split' inP)

/-- **T2.** Exclusivity, with range restriction and queries that bind no new variable, makes
`Derives` functional: a call has at most one value. -/
theorem derives_functional (rr : ∀ l, RangeRestricted (M l)) (qb : ∀ l, QueriesBound (M l))
    (exclusive : Exclusive M Rel) {C w₁ w₂ : Term ρ} (one : Derives M Rel C w₁)
    (two : Derives M Rel C w₂) : w₁ = w₂ := by
  induction one generalizing w₂ with
  | rule l θ₁ calls₁ queries₁ ih =>
    obtain ⟨l₂, θ₂, sameCall, rfl, holds₂⟩ := derives_iff.mp two
    have holds₁ : ∀ p ∈ (M l).premises, Holds M Rel θ₁ p := by
      intro p member
      cases p with
      | call source target => exact calls₁ source target member
      | query atom => exact queries₁ atom member
    by_cases same : l = l₂
    · subst same
      have agree := agree_on_bound (M l) (rr l) (qb l) sameCall holds₂
        (fun source target member w derives => ih source target member derives) (M l).premises []
        (List.append_nil _).symm
      exact apply_eq_of_agree θ₁ θ₂ (M l).rhs fun v inside => agree v ((rr l).rhs inside)
    · exact absurd holds₂ (exclusive l l₂ θ₁ θ₂ same sameCall holds₁)

end Semantics

section Closure

variable {σ : LPSignature.{u, u, u, u}} {L : Type u}
  [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L]
  {M : L → ModuleRule (readingSignature σ L)} {Rel : Finset (Atom (readingSignature σ L))}
  {C₀ : Term (readingSignature σ L)}

/-- **T2, read by demand.** Under the licence, the closure holds at most one value row per call. -/
theorem valueRow_unique (rr : ∀ l, RangeRestricted (M l)) (qb : ∀ l, QueriesBound (M l))
    (exclusive : Exclusive M ↑Rel) (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround)
    {C w₁ w₂ : Term (readingSignature σ L)}
    (one : valueRow C w₁ ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel))
    (two : valueRow C w₂ ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel)) :
    w₁ = w₂ :=
  derives_functional rr qb exclusive ((valueRow_mem_closure_iff rr ground relGround C w₁).mp one).2
    ((valueRow_mem_closure_iff rr ground relGround C w₂).mp two).2

end Closure

#print axioms agree_on_bound
#print axioms derives_functional
#print axioms valueRow_unique

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
