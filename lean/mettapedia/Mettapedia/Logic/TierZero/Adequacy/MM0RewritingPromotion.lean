import Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
import Mettapedia.Languages.MM0.Kernel.DerivedTheoremExtension

/-!
# Contextual cut and conservative MM0 schema installation from guarded rewriting runs

A promoted schema is justified by an actual guarded rewriting run in its declared formal
context, under its retained hypotheses. Admissible substitution transports
that justification to every later instance. Installing the schema compiles a
normal request/read/make rule; applications do not replay its original run.

The result preserves reachable logical consequences. Computing a minimal
proof-use interface and authorizing live publication are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel

/-- Ordinary process reachability with an initially supplied request batch. -/
def Reaches (theory : Theory) (target : Context) (hypotheses : List Preterm) (expression : Preterm) : Prop :=
  ∃ requests after,
    Relation.ReflTransGen (process theory target (catalog theory)).Step
      (requestBag requests + hypothesisBag target hypotheses) after ∧
    proofValue target expression ∈ after

theorem reaches_iff {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    Reaches theory target hypotheses expression ↔
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression :=
  rewriting_reaches_iff_derives wellFormed formed hypotheses expression

/-- An accepted schematic judgment remains reachable under every admissible
substitution, with all instantiated hypotheses retained. -/
theorem reaches_substitution {theory : Theory} (wellFormed : theory.WellFormed) {formal target : Context}
    (formalFormed : Context.WellFormed theory.sortSignature formal)
    (targetFormed : Context.WellFormed theory.sortSignature target)
    {arguments hypotheses movedHypotheses : List Preterm} {conclusion movedConclusion : Preterm}
    (admitted : Substitution.Admissible theory.termSignature formal target arguments)
    (hypothesesMoved : List.Forall₂ (Preterm.Substitutes (Substitution.ofList arguments)) hypotheses movedHypotheses)
    (conclusionMoved : Preterm.Substitutes (Substitution.ofList arguments) conclusion movedConclusion)
    (accepted : Reaches theory formal hypotheses conclusion) :
    Reaches theory target movedHypotheses movedConclusion := by
  apply (reaches_iff wellFormed targetFormed _ _).mpr
  exact admitted.derives hypothesesMoved ((reaches_iff wellFormed formalFormed _ _).mp accepted) conclusionMoved

/-- Supplying native derivations of the retained instantiated hypotheses
allows contextual cut, without assuming that the conclusion displays them. -/
theorem contextual_cut {theory : Theory} (wellFormed : theory.WellFormed) {formal target : Context}
    (formalFormed : Context.WellFormed theory.sortSignature formal)
    (targetFormed : Context.WellFormed theory.sortSignature target)
    {arguments hypotheses movedHypotheses ambient : List Preterm} {conclusion movedConclusion : Preterm}
    (admitted : Substitution.Admissible theory.termSignature formal target arguments)
    (hypothesesMoved : List.Forall₂ (Preterm.Substitutes (Substitution.ofList arguments)) hypotheses movedHypotheses)
    (conclusionMoved : Preterm.Substitutes (Substitution.ofList arguments) conclusion movedConclusion)
    (accepted : Reaches theory formal hypotheses conclusion)
    (supplied : ∀ hypothesis ∈ movedHypotheses, Reaches theory target ambient hypothesis) :
    Reaches theory target ambient movedConclusion := by
  have transported := reaches_substitution wellFormed formalFormed targetFormed admitted hypothesesMoved conclusionMoved accepted
  apply (reaches_iff wellFormed targetFormed _ _).mpr
  apply ((reaches_iff wellFormed targetFormed _ _).mp transported).replaceHypotheses
  intro hypothesis member
  exact (reaches_iff wellFormed targetFormed _ _).mp (supplied hypothesis member)

/-- This certificate records a native schematic derivation. A proof of only
one concrete instance does not provide its `native` field. -/
structure Promotion (theory : Theory) where
  index : Nat
  declaration : TheoremDecl
  fresh : theory.theoremSignature index = none
  admitted : declaration.Admissible theory.sortSignature theory.termSignature
  native : Reaches theory declaration.arguments declaration.hypotheses declaration.conclusion

namespace Promotion

variable {theory : Theory} (promotion : Promotion theory)

def installed : Theory :=
  { theory with theorems := (promotion.index, promotion.declaration) :: theory.theorems }

theorem installed_theorems : promotion.installed.theoremSignature =
    TheoremSignature.extend theory.theoremSignature promotion.index promotion.declaration := by
  funext queried
  by_cases same : queried = promotion.index
  · simp [installed, Theory.theoremSignature, TheoremSignature.extend, same]
  · have compared : (queried == promotion.index) = false := by simp [same]
    simp [installed, Theory.theoremSignature, TheoremSignature.extend, List.lookup_cons, same, compared]

theorem justified (wellFormed : theory.WellFormed) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      promotion.declaration.arguments promotion.declaration.hypotheses promotion.declaration.conclusion :=
  (reaches_iff wellFormed promotion.admitted.context _ _).mp promotion.native

theorem installed_wellFormed (wellFormed : theory.WellFormed) : promotion.installed.WellFormed := by
  constructor
  · exact wellFormed.terms
  · exact wellFormed.definitions
  · intro index declaration known
    rw [promotion.installed_theorems] at known
    by_cases same : index = promotion.index
    · subst index
      have payload : promotion.declaration = declaration := by simpa [TheoremSignature.extend] using known
      subst declaration
      exact promotion.admitted
    · exact wellFormed.theorems index declaration (by simpa [TheoremSignature.extend, same] using known)

/-- Installing a derived schema adds no reachable consequences, in any
well-formed target context and under any local hypotheses. -/
theorem conservative (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    Reaches promotion.installed target hypotheses expression ↔ Reaches theory target hypotheses expression := by
  rw [reaches_iff (promotion.installed_wellFormed wellFormed) formed,
    reaches_iff wellFormed formed]
  change Derives theory.termSignature theory.definitionSignature promotion.installed.theoremSignature target hypotheses expression ↔ _
  rw [promotion.installed_theorems]
  exact TheoremSignature.extend_iff promotion.fresh (promotion.justified wellFormed) target hypotheses expression

end Promotion

theorem no_unjustified_reach {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target)
    (noTheorems : ∀ index, theory.theoremSignature index = none) (expression : Preterm) :
    ¬Reaches theory target [] expression := by
  intro accepted
  have derived := (reaches_iff wellFormed formed [] expression).mp accepted
  have empty : theory.theoremSignature = fun _ => none := funext noTheorems
  rw [empty] at derived
  exact no_derivation_without_hypotheses_or_theorems _ _ _ _ derived

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
