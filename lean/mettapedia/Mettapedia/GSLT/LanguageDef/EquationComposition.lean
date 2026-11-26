import Mettapedia.GSLT.LanguageDef.EquationPremiseStability

/-!
# Composing declarations of equations

Over a common grammar, combining two sets of premise-free equations
joins their generated contextual equivalences. Taking the union of
the already-computed equality relations is not generally transitive.
No normal forms, orientations, or termination hypotheses are involved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.EquationComposition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator PremisesAt)
open EquationSemantics
open EquationPremiseStability (derivedInstance_forward_of_same_grammar)

/-- An unconditional raw schema has the same instances in any
presentation that retains it, regardless of the directed rewrites. -/
private theorem instance_transport {base₁ base₂ : BasePremiseEvaluator} {source target : LanguageDef}
    {n : Nat} {p q : Pattern}
    (instanceAt : EquationInstanceAt base₁ source n p q)
    (sufficient : ∀ e ∈ source.equations, e ∈ target.equations)
    (inert : ∀ e ∈ source.equations, e.premises = [] ∧ e.bindings = none) :
    EquationInstanceAt base₂ target n p q := by
  cases instanceAt with
  | forward written retained matched holds result =>
    have emptyPremises := (inert _ written).1
    rw [emptyPremises] at holds
    cases holds
    exact .forward (sufficient _ written) retained matched
      (by rw [emptyPremises]; exact .nil _) result
  | reverse written retained matched holds result =>
    have emptyPremises := (inert _ written).1
    rw [emptyPremises] at holds
    cases holds
    exact .reverse (sufficient _ written) retained matched
      (by rw [emptyPremises]; exact .nil _) result
  | declared written notRaw _ =>
    rw [readsRaw_of_none (inert _ written).2] at notRaw
    contradiction

private theorem context_transport (source target : ValidatedLanguageDef)
    (types : source.language.types = target.language.types)
    (grammar : source.language.terms = target.language.terms)
    (included : source.language.equations ⊆ target.language.equations)
    (inert : ∀ e ∈ source.language.equations, e.premises = [] ∧ e.bindings = none)
    {base₁ base₂ : BasePremiseEvaluator} {p q : Pattern}
    (step : EquationContextStep base₁ source.language p q) :
    EquationContextStep base₂ target.language p q := by
  cases step with
  | inContext surrounding evidence =>
    apply EquationContextStep.inContext surrounding
    rcases evidence with ⟨fuel, authored⟩ | derived
    · exact .inl ⟨fuel, instance_transport authored (fun _ member => included member) inert⟩
    · exact .inr (derivedInstance_forward_of_same_grammar source target types grammar derived)

/-- Both parts and their combination use the same generated grammar laws.
All authored equations are unconditional and use the ordinary matcher.
This includes arbitrary cyclic compound equations. -/
theorem equation_classes_join (left right combined : ValidatedLanguageDef) (base : BasePremiseEvaluator)
    (leftTypes : left.language.types = combined.language.types)
    (leftGrammar : left.language.terms = combined.language.terms)
    (rightTypes : right.language.types = combined.language.types)
    (rightGrammar : right.language.terms = combined.language.terms)
    (written : combined.language.equations = left.language.equations ++ right.language.equations)
    (inert : ∀ e ∈ combined.language.equations, e.premises = [] ∧ e.bindings = none)
    (p q : Pattern) :
    EquationEquiv base combined.language p q ↔
      Relation.EqvGen (fun s t =>
        EquationEquiv base left.language s t ∨ EquationEquiv base right.language s t) p q := by
  have includeL : left.language.equations ⊆ combined.language.equations := by
    rw [written]
    exact fun _ h => List.mem_append_left _ h
  have includeR : right.language.equations ⊆ combined.language.equations := by
    rw [written]
    exact fun _ h => List.mem_append_right _ h
  have transferL (s t : Pattern) (h : EquationEquiv base left.language s t) :
      EquationEquiv base combined.language s t :=
    h.mono (fun _ _ => context_transport left combined leftTypes leftGrammar includeL
      (fun e found => inert e (includeL found)))
  have transferR (s t : Pattern) (h : EquationEquiv base right.language s t) :
      EquationEquiv base combined.language s t :=
    h.mono (fun _ _ => context_transport right combined rightTypes rightGrammar includeR
      (fun e found => inert e (includeR found)))
  constructor
  · intro equality
    apply equality.mono
    intro s t trace
    cases trace with
    | inContext context generator =>
      rcases generator with ⟨fuel, instanceAt⟩ | derived
      · cases instanceAt with
        | forward registered raw matched holds result =>
          have free := (inert _ registered).1
          rw [free] at holds
          cases holds
          rw [written] at registered
          rcases List.mem_append.mp registered with hl | hr
          · exact .inl (Relation.EqvGen.rel _ _
              (.inContext context (.inl ⟨fuel, .forward hl raw matched
                (by rw [free]; exact .nil _) result⟩)))
          · exact .inr (Relation.EqvGen.rel _ _
              (.inContext context (.inl ⟨fuel, .forward hr raw matched
                (by rw [free]; exact .nil _) result⟩)))
        | reverse registered raw matched holds result =>
          have free := (inert _ registered).1
          rw [free] at holds
          cases holds
          rw [written] at registered
          rcases List.mem_append.mp registered with hl | hr
          · exact .inl (Relation.EqvGen.rel _ _
              (.inContext context (.inl ⟨fuel, .reverse hl raw matched
                (by rw [free]; exact .nil _) result⟩)))
          · exact .inr (Relation.EqvGen.rel _ _
              (.inContext context (.inl ⟨fuel, .reverse hr raw matched
                (by rw [free]; exact .nil _) result⟩)))
        | declared registered notRaw _ =>
          rw [readsRaw_of_none (inert _ registered).2] at notRaw
          contradiction
      · exact .inl (Relation.EqvGen.rel _ _ (.inContext context
          (.inr (derivedInstance_forward_of_same_grammar combined left
            leftTypes.symm leftGrammar.symm derived))))
  · intro equality
    induction equality with
    | rel s t part => exact part.elim (transferL s t) (transferR s t)
    | refl s => exact .refl s
    | symm s t _ ih => exact .symm _ _ ih
    | trans s t u _ _ first second => exact .trans _ _ _ first second

section Controls

private def leftClass (a b : Nat) : Prop := (a == 0 || a == 1) = (b == 0 || b == 1)
private def rightClass (a b : Nat) : Prop := (a == 1 || a == 2) = (b == 1 || b == 2)

theorem equality_can_cross_the_import_boundary :
    ¬ (leftClass 0 2 ∨ rightClass 0 2) ∧
      Relation.EqvGen (fun a b => leftClass a b ∨ rightClass a b) 0 2 :=
  ⟨by unfold leftClass rightClass; decide,
    .trans 0 1 2 (.rel 0 1 (.inl rfl)) (.rel 1 2 (.inr rfl))⟩

end Controls

end Mettapedia.GSLT.LanguageDef.EquationComposition
