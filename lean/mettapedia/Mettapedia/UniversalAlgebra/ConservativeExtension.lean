import Mettapedia.UniversalAlgebra.EquationalLogic
import Mettapedia.Logic.RuleConservativeExtension

/-!
# Conservative extension of equation systems

An equation-system extension is conservative when every added equation was
already an equational consequence of the original system.  This file proves
that criterion from substitution admissibility and also proves its sharp
negative boundary: adjoining a genuinely underivable equation changes the
consequence relation.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open Mettapedia.Logic

universe u

variable {S : Signature.{u}}

namespace Term

/-- Two successive simultaneous substitutions compose pointwise. -/
theorem subst_subst (first second : Nat → Term S) :
    ∀ term : Term S,
      (term.subst first).subst second =
        term.subst (fun variableIndex => (first variableIndex).subst second)
  | .var _ => rfl
  | .op operation arguments => by
      simp only [Term.subst_op]
      congr 1
      funext position
      exact subst_subst first second (arguments position)

end Term

namespace Equation

/-- Apply one simultaneous substitution to both sides of an equation. -/
def subst (equation : Equation S) (substitution : Nat → Term S) : Equation S :=
  (equation.1.subst substitution, equation.2.subst substitution)

end Equation

namespace EquationalConsequence

/-- Substitution is admissible for generated equational consequence, not only
for the input equation occurrences. -/
theorem subst {system : EquationSystem S} {equation : Equation S}
    (derivation : EquationalConsequence system equation)
    (substitution : Nat → Term S) :
    EquationalConsequence system (equation.subst substitution) := by
  refine Derives.least
    (fun equation => EquationalConsequence system
      (equation.subst substitution)) ?_ derivation
  intro premises conclusion rule premiseDerivations
  cases rule with
  | systemInstance member instanceSubstitution =>
      have composedDerivation :=
        Derives.node [] _
          (EquationalRule.systemInstance member
            (fun variableIndex =>
              (instanceSubstitution variableIndex).subst substitution))
          (by intro premise premiseMem; cases premiseMem)
      simpa only [EquationalConsequence, Equation.subst, Term.subst_subst]
        using composedDerivation
  | refl term =>
      exact Derives.node [] _ (EquationalRule.refl (term.subst substitution))
        (by intro premise premiseMem; cases premiseMem)
  | symm left right =>
      refine Derives.node
        [(left.subst substitution, right.subst substitution)] _
        (EquationalRule.symm _ _) ?_
      intro premise premiseMem
      simp only [List.mem_singleton] at premiseMem
      subst premise
      exact premiseDerivations (left, right) (by simp)
  | trans left middle right =>
      refine Derives.node
        [(left.subst substitution, middle.subst substitution),
          (middle.subst substitution, right.subst substitution)] _
        (EquationalRule.trans _ _ _) ?_
      intro premise premiseMem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at premiseMem
      rcases premiseMem with rfl | rfl
      · exact premiseDerivations (left, middle) (by simp)
      · exact premiseDerivations (middle, right) (by simp)
  | congruence operation left right =>
      refine Derives.node
        (List.ofFn fun position =>
          ((left position).subst substitution,
            (right position).subst substitution)) _
        (EquationalRule.congruence operation
          (fun position => (left position).subst substitution)
          (fun position => (right position).subst substitution)) ?_
      intro premise premiseMem
      rw [List.mem_ofFn] at premiseMem
      obtain ⟨position, rfl⟩ := premiseMem
      exact premiseDerivations (left position, right position) (by
        rw [List.mem_ofFn]
        exact ⟨position, rfl⟩)

/-- Every listed equation is a consequence of its own equation system. -/
theorem of_mem {system : EquationSystem S} {equation : Equation S}
    (member : equation ∈ system) :
    EquationalConsequence system equation := by
  have instanceDerivation : EquationalConsequence system
      (equation.subst Term.var) :=
    Derives.node [] _ (EquationalRule.systemInstance member Term.var)
      (by intro premise premiseMem; cases premiseMem)
  simpa only [Equation.subst, Term.subst_variables] using instanceDerivation

/-- If every input equation of `target` is already derivable from `source`,
then every consequence of `target` is a consequence of `source`. -/
theorem translate_axioms {source target : EquationSystem S}
    (axiomDerivable : ∀ equation, equation ∈ target →
      EquationalConsequence source equation)
    {conclusion : Equation S} :
    EquationalConsequence target conclusion →
      EquationalConsequence source conclusion := by
  apply Derives.least (EquationalConsequence source)
  intro premises conclusion rule premiseDerivations
  cases rule with
  | systemInstance member substitution =>
      exact subst (axiomDerivable _ member) substitution
  | refl term =>
      exact Derives.node [] _ (EquationalRule.refl term)
        (by intro premise premiseMem; cases premiseMem)
  | symm left right =>
      exact Derives.node [(left, right)] _ (EquationalRule.symm left right)
        premiseDerivations
  | trans left middle right =>
      exact Derives.node [(left, middle), (middle, right)] _
        (EquationalRule.trans left middle right) premiseDerivations
  | congruence operation left right =>
      exact Derives.node (List.ofFn fun position =>
          (left position, right position)) _
        (EquationalRule.congruence operation left right) premiseDerivations

end EquationalConsequence

namespace EquationSystem

/-- Append a finite list of equation occurrences to an equation system. -/
def extend (system : EquationSystem S) (additional : List (Equation S)) :
    EquationSystem S where
  equations := system.equations ++ additional

/-- Two equation systems have the same generated equational consequences. -/
def SameConsequences (left right : EquationSystem S) : Prop :=
  ∀ equation, EquationalConsequence left equation ↔
    EquationalConsequence right equation

/-- Adding only already-derivable equations preserves every equational
consequence, in both directions. -/
theorem extend_sameConsequences (system : EquationSystem S)
    (additional : List (Equation S))
    (redundant : ∀ equation ∈ additional,
      EquationalConsequence system equation) :
    SameConsequences (system.extend additional) system := by
  intro equation
  constructor
  · intro extensionDerivation
    apply EquationalConsequence.translate_axioms (source := system)
      (target := system.extend additional) _ extensionDerivation
    intro listedEquation listedEquationMem
    change listedEquation ∈ system.equations ++ additional at listedEquationMem
    rw [List.mem_append] at listedEquationMem
    rcases listedEquationMem with originalMem | additionalMem
    · exact EquationalConsequence.of_mem originalMem
    · exact redundant listedEquation additionalMem
  · intro originalDerivation
    exact EquationalConsequence.mono (fun listedEquation listedEquationMem => by
      change listedEquation ∈ system.equations ++ additional
      exact List.mem_append_left additional listedEquationMem) originalDerivation

/-- Negative boundary: adjoining one genuinely underivable equation cannot
preserve the consequence relation. -/
theorem extend_not_sameConsequences_of_not_consequence
    (system : EquationSystem S) (equation : Equation S)
    (notDerivable : ¬ EquationalConsequence system equation) :
    ¬ SameConsequences (system.extend [equation]) system := by
  intro sameConsequences
  have inExtension : equation ∈ system.extend [equation] := by
    change equation ∈ system.equations ++ [equation]
    exact List.mem_append_right _ (by simp)
  exact notDerivable ((sameConsequences equation).mp
    (EquationalConsequence.of_mem inExtension))

end EquationSystem

end Mettapedia.UniversalAlgebra
