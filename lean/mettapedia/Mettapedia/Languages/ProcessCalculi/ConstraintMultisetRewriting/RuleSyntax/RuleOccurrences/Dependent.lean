import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.DependentEq

/-!
# The dependent full step restricted to a program, as the candidate with that program ambient

At the typed βη frames of the dependent unifier, with telescopes of fresh helpers as the extensions,
`RuleSyntax.Dependent.dependent_eq` says that the dependent full step restricted to the fresh
openings of a program `P` has the transitions of the present step of `P`. The ambient form of the
step of a program (`ambient_eq`) then gives, by composition of the two equalities of transition
relations:

* **`dependent_full_eq`**: the dependent full step restricted to the fresh openings of `P` is the
  candidate with ambient program `P` at the states that hold no rule.

**What stays outside**, exactly as for the present step (the header of `RuleSyntax/DependentEq`): the
unrestricted dependent full step fires rule instances at the extended frame that mention the state's
own unknowns directly, asks predicate queries over arbitrary regions with arbitrary answer predicates,
and makes rows as raw codes checked at admission. Of these, the candidate has the first in the form of
a held rule with arguments (`Held.args`, the closure's equations `RFiring.env`): a rule that mentions
unknowns of the state through its arguments. Turning an arbitrary instance into a code with arguments
needs the abstraction of a term over the unknowns it mentions, which a frame action alone does not
give; it is not constructed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)

universe uR uZ

variable {Head : Type} {rules : Rules Head} {O : Type} [DecidableEq O] {L : Type}
  [UniverseLevel.LevelOrder L] {levels : LevelModel rules L} {P : Program (Dependent.Terms rules)}
  {R : Type uR} [DecidableEq R] {Z : Type uZ}

/-- **The dependent full step restricted to a program is the candidate with that program ambient**,
at the states that hold no rule: through `Dependent.toState` and `holding`, the two transition
relations are equal. -/
theorem dependent_full_eq (code : R → Rule (Dependent.Terms rules)) (zone : R → Z)
    (s s' : Interface.DependentFull.State rules O) :
    Succ (Dependent.dependentOn levels P) s s' ↔
      Succ (rstep (frames levels) O R Dependent.helperExtensions (ofRules Z) P).toStep
        (holding (Dependent.toState s) ∅ code zone) (holding (Dependent.toState s') ∅ code zone) :=
  (Dependent.dependent_eq s s').trans
    (ambient_eq R (frames levels) Dependent.helperExtensions P code zone (Dependent.toState s)
      (Dependent.toState s')).symm

#print axioms dependent_full_eq

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
