import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationStore

/-!
# Principal answers relative to an explicit observation interface

An answer introducing a fresh helper factors solutions on the variables and
terms already in the problem's interface, including its surviving frame.
It need not factor a separately prescribed value of that new helper.

The stronger all-terms principality contract implies this one. Sequential
solving retains the terms of new equations in the first interface, and guard
transport requires a proved invariance law for every retained observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace SubstitutionAction

universe uT uS
variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S)

/-- The interface must include every term whose value may be observed:
equations, checks, retained premises and shared surviving values. -/
structure PrincipalOn (store : EquationStore T) (answer : S) (observed : List T) : Prop where
  sound : A.Models answer store
  factors : ∀ candidate, A.Models candidate store → ∃ residual,
    ∀ term ∈ observed, A.E (A.apply candidate term) (A.apply (A.compose residual answer) term)

theorem Principal.on {store : EquationStore T} {answer : S}
    (principal : A.Principal store answer) (observed : List T) :
    A.PrincipalOn store answer observed :=
  ⟨principal.sound, fun candidate solved =>
    (principal.factors candidate solved).imp (fun _ through term _ => through term)⟩

theorem PrincipalOn.restrict {store : EquationStore T} {answer : S} {observed smaller : List T}
    (principal : A.PrincipalOn store answer observed)
    (included : ∀ term ∈ smaller, term ∈ observed) : A.PrincipalOn store answer smaller := by
  refine ⟨principal.sound, ?_⟩
  intro candidate solved
  obtain ⟨residual, through⟩ := principal.factors candidate solved
  exact ⟨residual, fun term member => through term (included term member)⟩

/-- New equation terms must be in the first answer's interface. The second
answer factors the first answer's instantiated observation terms. -/
theorem PrincipalOn.compose {old extra : EquationStore T} {first second : S} {observed : List T}
    (oldPrincipal : A.PrincipalOn old first observed)
    (covers : ∀ equation ∈ extra, equation.1 ∈ observed ∧ equation.2 ∈ observed)
    (residualPrincipal : A.PrincipalOn (A.applyStore first extra) second (observed.map (A.apply first))) :
    A.PrincipalOn (old ++ extra) (A.compose second first) observed := by
  refine ⟨(A.models_append _ _ _).mpr ⟨A.models_compose oldPrincipal.sound second,
    (A.models_applyStore second first extra).mp residualPrincipal.sound⟩, ?_⟩
  intro candidate solved
  obtain ⟨oldSolved, extraSolved⟩ := (A.models_append _ _ _).mp solved
  obtain ⟨middle, throughFirst⟩ := oldPrincipal.factors candidate oldSolved
  have residualSolved : A.Models middle (A.applyStore first extra) := by
    apply (A.models_applyStore middle first extra).mpr
    intro equation member
    exact A.equivalence.trans (A.equivalence.symm (throughFirst equation.1 (covers equation member).1))
      (A.equivalence.trans (extraSolved equation member) (throughFirst equation.2 (covers equation member).2))
  obtain ⟨last, throughSecond⟩ := residualPrincipal.factors middle residualSolved
  refine ⟨last, fun term member => ?_⟩
  have next := throughSecond (A.apply first term) (List.mem_map.mpr ⟨term, member, rfl⟩)
  simp only [A.apply_compose] at next ⊢
  exact A.equivalence.trans
    (by simpa only [A.apply_compose] using throughFirst term member) next

/-- A predicate may be transported through a principal answer only after
proving that its truth is determined by the retained observation interface. -/
theorem PrincipalOn.entails_iff {store : EquationStore T} {answer : S} {observed : List T}
    (principal : A.PrincipalOn store answer observed) (predicate : S → Prop)
    (respects : ∀ first second,
      (∀ term ∈ observed, A.E (A.apply first term) (A.apply second term)) →
        (predicate first ↔ predicate second)) :
    A.Entails store predicate ↔ ∀ residual, predicate (A.compose residual answer) := by
  constructor
  · intro all residual
    exact all _ (A.models_compose principal.sound residual)
  · intro all candidate solved
    obtain ⟨residual, through⟩ := principal.factors candidate solved
    exact (respects candidate (A.compose residual answer) through).mpr (all residual)

end SubstitutionAction
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
