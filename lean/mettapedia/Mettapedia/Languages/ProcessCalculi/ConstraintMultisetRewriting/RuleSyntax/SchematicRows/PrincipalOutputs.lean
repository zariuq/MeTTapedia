import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema

/-!
# Principal result schemes retain exactly a protected interface

The result value and protected context are normalized by one principal answer.
The closure captures the normalized context. Its readings are exactly the
original solutions agreeing with the supplied caller on that interface.
Coverage is derived from principality, with no ground-value cardinality premise.

This projects a solution family. Reusing it as a program result additionally
requires the derivation-uniformity and operational laws; it is not a licence to
turn an arbitrary shared hypothesis into independently reusable data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalOutputs

open Interface (Frames)

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

def scheme (X : Frames Tm Hom) {a m : Obj} (answer : Hom a m)
    (context : List (Tm a)) (value : Tm a) : Closure Tm m :=
  ⟨⟨m, [], context.map (X.act answer), X.act answer value⟩, context.map (X.act answer)⟩

theorem reading_iff (X : Frames Tm Hom) {a m b : Obj}
    (information : EquationStore (Tm a)) (answer : Hom a m)
    (principal : X.Principal information answer) (context : List (Tm a)) (value : Tm a)
    (source : Hom m b) (observed : Tm b) :
    (scheme X answer context value).ReadsAt X source observed ↔
      ∃ candidate : Hom a b, X.Models candidate information ∧
        (∀ term ∈ context, X.E (X.act candidate term) (X.act source (X.act answer term))) ∧
        X.E (X.act candidate value) observed := by
  constructor
  · intro reading
    dsimp only [scheme, Closure.ReadsAt] at reading
    obtain ⟨locals, _, captures, output⟩ := reading
    refine ⟨X.comp locals answer, Frames.models_comp principal.sound locals, ?_, ?_⟩
    · intro term member
      have mapped : X.act answer term ∈ context.map (X.act answer) := List.mem_map_of_mem member
      have same := (List.forall₂_same.mp captures) _ mapped
      simpa only [X.act_comp] using same
    · simpa only [X.act_comp] using output
  · rintro ⟨candidate, solved, agrees, output⟩
    obtain ⟨locals, factors⟩ := principal.factors b candidate solved
    dsimp only [scheme, Closure.ReadsAt]
    refine ⟨locals, Frames.models_nil _, List.forall₂_same.mpr ?_, ?_⟩
    · intro term member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      have factor : X.E (X.act candidate original) (X.act locals (X.act answer original)) := by
        simpa only [X.act_comp] using factors original
      exact (X.equivalence b).trans ((X.equivalence b).symm factor) (agrees original inside)
    · have factor : X.E (X.act candidate value) (X.act locals (X.act answer value)) := by
        simpa only [X.act_comp] using factors value
      exact (X.equivalence b).trans ((X.equivalence b).symm factor) output

theorem solution_covered (X : Frames Tm Hom) {a m b : Obj}
    (information : EquationStore (Tm a)) (answer : Hom a m)
    (principal : X.Principal information answer) (context : List (Tm a)) (value : Tm a)
    (candidate : Hom a b) (solved : X.Models candidate information) :
    ∃ source : Hom m b,
      (∀ term ∈ context, X.E (X.act candidate term) (X.act source (X.act answer term))) ∧
        (scheme X answer context value).ReadsAt X source (X.act candidate value) := by
  obtain ⟨source, factors⟩ := principal.factors b candidate solved
  have agrees : ∀ term ∈ context,
      X.E (X.act candidate term) (X.act source (X.act answer term)) := by
    intro term _
    simpa only [X.act_comp] using factors term
  exact ⟨source, agrees, (reading_iff X information answer principal context value source _).mpr
    ⟨candidate, solved, agrees, (X.equivalence b).refl _⟩⟩

theorem wellFormed (X : Frames Tm Hom) {a m : Obj} (answer : Hom a m)
    (context : List (Tm a)) (value : Tm a) : (scheme X answer context value).WellFormed := rfl

#print axioms reading_iff
#print axioms solution_covered
#print axioms wellFormed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalOutputs
