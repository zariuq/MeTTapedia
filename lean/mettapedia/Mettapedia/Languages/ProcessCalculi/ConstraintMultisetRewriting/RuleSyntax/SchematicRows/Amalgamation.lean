import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Opening

/-!
# Deriving shared-interface amalgamation from actual fresh openings

The state's assignment and a schematic row's assignment are first combined by
the existing held-rule freshness condition. Closure equations then identify
captured parameters with ambient arguments. Thus compatibility over the shared
interface is derived from the actual firing information, not added as a new
freshness or solver axiom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Amalgamation

open Interface (Frames)
open RuleOccurrences Opening

universe uO uT uH uE uOcc uR uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {s : RState Tm O R C Z}
  (f : RFiring O R E codes s)

theorem readsAt_iff_opened (ambient : Set C) (available : s.Available ambient f.use)
    (fresh : f.Fresh X) (noTake : f.spec.body.take = []) (noRead : f.spec.body.read = [])
    (lengths : f.spec.params.length = (s.argsOf f.use).length)
    (term : Tm f.spec.locals) (produced : term ∈ f.spec.body.produce)
    {b : Obj} (σ : Hom s.frame b) (known : X.Models σ s.knowledge) (value : Tm b) :
    (rowClosure f term).ReadsAt X σ value ↔
      ∃ u : Hom (E.target f.ext) b, X.Models u (f.information X) ∧
        (∀ t, s.Mentions t →
          X.E (X.act u (X.act (E.weaken f.ext) t)) (X.act σ t)) ∧
        X.E (X.act u (X.act f.opening term)) value := by
  have trans := fun {x y z : Tm b} (first : X.E x y) (second : X.E y z) =>
    (X.equivalence b).trans first second
  have symm := fun {x y : Tm b} (same : X.E x y) => (X.equivalence b).symm same
  constructor
  · intro reading
    dsimp only [rowClosure, Closure.ReadsAt] at reading
    obtain ⟨h, localModel, captures, output⟩ := reading
    obtain ⟨u, source, localTerms⟩ := fresh b σ h
    refine ⟨u, (models_information_iff X f noTake noRead u lengths).mpr ⟨?_, ?_, ?_⟩,
      source, trans (localTerms term (produced_in_terms f term produced)) output⟩
    · intro equation inside
      simp only [Frames.Solves, X.act_comp]
      have left := source equation.1 (Or.inl (Or.inl (List.mem_map_of_mem inside)))
      have right := source equation.2 (Or.inl (Or.inr (Or.inl (List.mem_map_of_mem inside))))
      exact trans left (trans (known equation inside) (symm right))
    · intro equation inside
      simp only [Frames.Solves, X.act_comp]
      have left := localTerms equation.1 (tell_left_in_terms f equation inside)
      have right := localTerms equation.2 (tell_right_in_terms f equation inside)
      exact trans left (trans (localModel equation inside) (symm right))
    · apply List.forall₂_iff_zip.mpr
      refine ⟨lengths, ?_⟩
      intro parameter argument paired
      have parameterMember := (List.of_mem_zip paired).1
      have argumentMember := (List.of_mem_zip paired).2
      have left := localTerms parameter (parameter_in_terms f parameter parameterMember)
      have right := source argument (args_mentioned f ambient available argument argumentMember)
      exact trans left (trans (List.forall₂_zip captures paired) (symm right))
  · rintro ⟨u, solved, source, output⟩
    dsimp only [rowClosure, Closure.ReadsAt]
    obtain ⟨_, localModel, captures⟩ := (models_information_iff X f noTake noRead u lengths).mp solved
    refine ⟨X.comp u f.opening, localModel, ?_, ?_⟩
    · apply List.forall₂_iff_zip.mpr
      refine ⟨lengths, ?_⟩
      intro parameter argument paired
      rw [X.act_comp]
      exact trans (List.forall₂_zip captures paired)
        (source argument (args_mentioned f ambient available argument (List.of_mem_zip paired).2))
    · rw [X.act_comp]
      exact output

#print axioms readsAt_iff_opened

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Amalgamation
