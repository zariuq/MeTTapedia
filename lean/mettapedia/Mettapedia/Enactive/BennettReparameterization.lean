import Mettapedia.Cybernetics.ObservedVariety
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Fixed-vocabulary reparameterization and observer-relative weakness

Theorem A.31 of Michael Timothy Bennett's *The Wrong Razor* is a fixed-
semantics result.  A function-preserving reparameterization computes the same
function, so it satisfies the same programs in one fixed embodied vocabulary;
every extensional weakness readout is therefore unchanged.

This is compatible with observer relativity.  Changing the vocabulary or
observation map can change which programs and distinctions are visible, even
when the underlying function or state is unchanged.  The source-faithful
theorem and the observer-change counterexample below live in one interface so
the separating premise is explicit rather than rhetorical.

Reference: M. T. Bennett, *The Wrong Razor*, Definition A.30 and Theorem A.31
in the complete-proofs appendix (2026).  Bennett assumes a diffeomorphism of a
parameter space; the proof uses only the function-preservation equation, which
is isolated here.  The observer-relative comparison uses the distinction and
variety discipline developed from F. Heylighen's work.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.BennettReparameterization

universe uParameter uFunction uProgram uScore

/-- One embodied program vocabulary together with its satisfaction relation
on realized functions. -/
structure EmbodiedSemantics
    (Function : Type uFunction) (Program : Type uProgram) where
  vocabulary : Set Program
  satisfies : Function → Program → Prop

namespace EmbodiedSemantics

variable {Function : Type uFunction} {Program : Type uProgram}

/-- The policy presented by a realized function in this fixed vocabulary. -/
def policyMap (semantics : EmbodiedSemantics Function Program)
    (function : Function) : Set Program :=
  {program | program ∈ semantics.vocabulary ∧
    semantics.satisfies function program}

/-- Equal realized functions present equal policies in a fixed vocabulary. -/
theorem policyMap_congr (semantics : EmbodiedSemantics Function Program)
    {left right : Function} (equal : left = right) :
    semantics.policyMap left = semantics.policyMap right := by
  subst equal
  rfl

end EmbodiedSemantics

/-- A semantic reparameterization: parameter coordinates may change, but the
realized function does not. -/
def FunctionPreserving
    {Parameter : Type uParameter} {Function : Type uFunction}
    (realize : Parameter → Function) (reparameterize : Parameter ≃ Parameter) : Prop :=
  ∀ parameter, realize (reparameterize parameter) = realize parameter

/-- Bennett A.31, policy-map form.  The fixed embodied semantics is visibly
the same on both sides. -/
theorem policyMap_functionPreserving
    {Parameter : Type uParameter} {Function : Type uFunction}
    {Program : Type uProgram}
    (semantics : EmbodiedSemantics Function Program)
    (realize : Parameter → Function) (reparameterize : Parameter ≃ Parameter)
    (preserves : FunctionPreserving realize reparameterize)
    (parameter : Parameter) :
    semantics.policyMap (realize (reparameterize parameter)) =
      semantics.policyMap (realize parameter) :=
  semantics.policyMap_congr (preserves parameter)

/-- Bennett A.31, weakness form.  Any weakness functional defined extensionally
on policies inherits the fixed-vocabulary invariance. -/
theorem weakness_functionPreserving
    {Parameter : Type uParameter} {Function : Type uFunction}
    {Program : Type uProgram} {Score : Type uScore}
    (semantics : EmbodiedSemantics Function Program)
    (weakness : Set Program → Score)
    (realize : Parameter → Function) (reparameterize : Parameter ≃ Parameter)
    (preserves : FunctionPreserving realize reparameterize)
    (parameter : Parameter) :
    weakness (semantics.policyMap (realize (reparameterize parameter))) =
      weakness (semantics.policyMap (realize parameter)) := by
  rw [policyMap_functionPreserving semantics realize reparameterize preserves]

/-! ## Changing the observer is not reparameterizing a fixed semantics -/

namespace VocabularyCanary

/-- The same realized function satisfies both available programs. -/
def satisfies (_ : Unit) (_ : Bool) : Prop := True

def narrow : EmbodiedSemantics Unit Bool where
  vocabulary := {false}
  satisfies := satisfies

def broad : EmbodiedSemantics Unit Bool where
  vocabulary := Set.univ
  satisfies := satisfies

theorem narrow_policyMap : narrow.policyMap () = {false} := by
  ext program
  simp [EmbodiedSemantics.policyMap, narrow, satisfies]

theorem broad_policyMap : broad.policyMap () = Set.univ := by
  ext program
  simp [EmbodiedSemantics.policyMap, broad, satisfies]

/-- Holding the realized function fixed while changing the embodied
vocabulary changes finite policy cardinality.  The fixed-vocabulary premise in
A.31 is therefore essential. -/
theorem observer_change_changes_policy_cardinality :
    (narrow.policyMap ()).ncard = 1 ∧
      (broad.policyMap ()).ncard = 2 := by
  rw [narrow_policyMap, broad_policyMap]
  norm_num

/-- In particular there is no common cardinal readout for these two legitimate
vocabularies of the same realized function. -/
theorem no_vocabulary_independent_policy_cardinality :
    ¬ ∃ cardinal : Nat,
      (narrow.policyMap ()).ncard = cardinal ∧
        (broad.policyMap ()).ncard = cardinal := by
  rintro ⟨cardinal, narrowEqual, broadEqual⟩
  have values := observer_change_changes_policy_cardinality
  omega

end VocabularyCanary

/-- The two published-looking claims are jointly consistent: fixed-semantics
function-preserving reparameterization leaves policies unchanged, while the
existing observer-relativity canary rules out one observer-independent variety
cardinal.  The transformations quantified by the two theorems are different. -/
theorem fixed_semantics_invariance_and_observer_relativity
    {Parameter : Type uParameter} {Function : Type uFunction}
    {Program : Type uProgram}
    (semantics : EmbodiedSemantics Function Program)
    (realize : Parameter → Function) (reparameterize : Parameter ≃ Parameter)
    (preserves : FunctionPreserving realize reparameterize) :
    (∀ parameter,
      semantics.policyMap (realize (reparameterize parameter)) =
        semantics.policyMap (realize parameter)) ∧
      ¬ ∃ cardinal : Nat,
        Mettapedia.Cybernetics.Observer.ObserverRelativity.micro.cardinalOn
            Finset.univ = cardinal ∧
          Mettapedia.Cybernetics.Observer.ObserverRelativity.macroView.cardinalOn
            Finset.univ = cardinal := by
  constructor
  · exact policyMap_functionPreserving semantics realize reparameterize preserves
  · exact
      Mettapedia.Cybernetics.Observer.ObserverRelativity.no_observer_independent_cardinality

end Mettapedia.Enactive.BennettReparameterization

#print axioms Mettapedia.Enactive.BennettReparameterization.weakness_functionPreserving
#print axioms Mettapedia.Enactive.BennettReparameterization.VocabularyCanary.observer_change_changes_policy_cardinality
#print axioms Mettapedia.Enactive.BennettReparameterization.fixed_semantics_invariance_and_observer_relativity
