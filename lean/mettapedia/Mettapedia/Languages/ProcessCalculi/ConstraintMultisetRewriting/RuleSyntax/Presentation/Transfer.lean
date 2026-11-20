import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Substitutability

/-!
# Substitutability for `RuleSyntax.step`, through the instance-set form

`Substitutability.substitutability` is stated for the step of a program as a set of ground rule instances
(`ProgramAdequacy.program`), where `program_adequacy` applies. `RuleInstanceSets.instanceSet_eq` and
`FirstOrderEq.firstOrder_eq` equate its successors with those of the label-keeping step of the program
(`OneFrame.keeping`) at embedded states (`succ_keeping_iff`), and that step never leaves the embedded states
(`OneFrame.keeping_closed`). So bisimilarity transfers (`bisimilar_keeping_iff`), observing row barbs on states
(`stateBarbs`), and the barbed types at the stores of two embedded states agree exactly when the states are
bisimilar for `RuleSyntax.step`'s label-keeping firings (`substitutability_keeping`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic (Formula Env referenceStructure)
open NamesOnTheStep (Expr)
open NamesOnTheStep.IssuingControls (ground)
open LogicOverTheStep.ProgramAdequacy (program Supply)
open LogicOverTheStep.StepSpan (Succ stepSystem)
open OneFrame (bodies embed keeping)

universe uO

variable {O : Type uO} [DecidableEq O] (label : O → Expr) {rules : List (Rule Rows)}

/-- **Row barbs on states**: a row is present, under the state's labels. -/
def stateBarbs (t : Expr) (s : State Rows O) : Prop := t ∈ s.present.val.map s.label

omit [DecidableEq O] in
theorem stateBarbs_embed (t : Expr) (C : Configuration Expr O) :
    stateBarbs t (embed label C) ↔ barbs label t C := Iff.rfl

/-- **The step of the program as a set of ground instances and the label-keeping `RuleSyntax.step` have the same
successors**, through the embedding. -/
theorem succ_keeping_iff (positive : ∀ r ∈ rules, Positive r) (C C' : Configuration Expr O) :
    Succ (program ground label (bodies {r | r ∈ rules})) C C' ↔
      Succ (keeping ground {r | r ∈ rules}) (embed label C) (embed label C') :=
  (OneFrame.instanceSet_eq (fun _ _ _ _ _ => rfl) (fun r member => (positive r member).1) C C').trans
    (OneFrame.firstOrder_eq C C')

/-- **Bisimilarity transfers** between the two steps, observing row barbs. -/
theorem bisimilar_keeping_iff (positive : ∀ r ∈ rules, Positive r) (C D : Configuration Expr O) :
    (stepSystem (program ground label (bodies {r | r ∈ rules})) (barbs label)).Bisimilar C D ↔
      (stepSystem (keeping ground {r | r ∈ rules}) stateBarbs).Bisimilar (embed label C) (embed label D) := by
  constructor
  · rintro ⟨relation, ⟨forward, backward, atoms⟩, related⟩
    refine ⟨fun s t => ∃ A B, s = embed label A ∧ t = embed label B ∧ relation A B, ⟨?_, ?_, ?_⟩,
      C, D, rfl, rfl, related⟩
    · rintro _ _ ⟨A, B, rfl, rfl, linked⟩ _ next step
      obtain ⟨A', rfl⟩ := OneFrame.keeping_closed A step
      obtain ⟨B', stepB, linked'⟩ := forward linked () ((succ_keeping_iff label positive A A').mpr step)
      exact ⟨embed label B', (succ_keeping_iff label positive B B').mp stepB, A', B', rfl, rfl, linked'⟩
    · rintro _ _ ⟨A, B, rfl, rfl, linked⟩ _ next step
      obtain ⟨B', rfl⟩ := OneFrame.keeping_closed B step
      obtain ⟨A', stepA, linked'⟩ := backward linked () ((succ_keeping_iff label positive B B').mpr step)
      exact ⟨embed label A', (succ_keeping_iff label positive A A').mp stepA, A', B', rfl, rfl, linked'⟩
    · rintro _ _ ⟨A, B, rfl, rfl, linked⟩ t
      exact atoms linked t
  · rintro ⟨relation, ⟨forward, backward, atoms⟩, related⟩
    refine ⟨fun A B => relation (embed label A) (embed label B), ⟨?_, ?_, ?_⟩, related⟩
    · intro A B linked _ A' step
      obtain ⟨t, stepB, linked'⟩ := forward linked () ((succ_keeping_iff label positive A A').mp step)
      obtain ⟨B', rfl⟩ := OneFrame.keeping_closed B stepB
      exact ⟨B', (succ_keeping_iff label positive B B').mpr stepB, linked'⟩
    · intro A B linked _ B' step
      obtain ⟨t, stepA, linked'⟩ := backward linked () ((succ_keeping_iff label positive B B').mp step)
      obtain ⟨A', rfl⟩ := OneFrame.keeping_closed A stepA
      exact ⟨A', (succ_keeping_iff label positive A A').mpr stepA, linked'⟩
    · intro A B linked t
      exact atoms linked t

/-- **Substitutability for `RuleSyntax.step`**: for a finite program of the fragment, the barbed types at the stores
of two embedded states with trivial knowledge agree exactly when the states are bisimilar for the label-keeping
firings of `RuleSyntax.step`, observing row barbs. -/
theorem substitutability_keeping {relEnv : RelationEnv} (supply : Supply label) (positive : ∀ r ∈ rules, Positive r)
    {C D : Configuration Expr O} (knowledgeC : Trivial C.equations) (knowledgeD : Trivial D.equations) :
    (∀ φ : Formula 0, Barbed φ →
      ((referenceStructure relEnv (present rules)).sat Env.closed φ (stateStore (embed label C)) ↔
        (referenceStructure relEnv (present rules)).sat Env.closed φ (stateStore (embed label D)))) ↔
      (stepSystem (keeping ground {r | r ∈ rules}) stateBarbs).Bisimilar (embed label C) (embed label D) :=
  (substitutability label supply positive knowledgeC knowledgeD).trans (bisimilar_keeping_iff label positive C D)

#print axioms succ_keeping_iff
#print axioms bisimilar_keeping_iff
#print axioms substitutability_keeping

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation
