import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-!
# Related substitutions at a binder

Lifting retains the new bound variable and weakens the evidence for
each older variable. Instantiation supplies evidence for the replacement
at zero and retains all older variables. Both constructions accept
propositional relations and proof-relevant relations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.RelatedSubstitution

universe u
variable {Head : Type} {E : {n : Nat} → Tm Head n → Tm Head n → Sort u}

def lift {n m : Nat} {source target : Sub Head n m}
    (variableEvidence : E (.var (0 : Fin (m + 1))) (.var 0))
    (weakenEvidence : ∀ {left right : Tm Head m}, E left right →
      E (rename wk left) (rename wk right))
    (related : ∀ i, E (source i) (target i)) :
    ∀ i, E (liftSub source i) (liftSub target i) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact variableEvidence
  · intro prior
    exact weakenEvidence (related prior)

def instantiate {n : Nat} {arg arg' : Tm Head n} {body body' : Tm Head (n + 1)}
    (substitute : ∀ {source target : Sub Head (n + 1) n},
      (∀ i, E (source i) (target i)) → E body body' →
        E (subst source body) (subst target body'))
    (variableEvidence : ∀ i : Fin n, E (.var i) (.var i))
    (argument : E arg arg') (inner : E body body') :
    E (inst0 arg body) (inst0 arg' body') := by
  apply substitute (source := subst0 arg) (target := subst0 arg') _ inner
  intro i
  refine Fin.cases ?_ ?_ i
  · exact argument
  · intro prior
    exact variableEvidence prior

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.RelatedSubstitution
