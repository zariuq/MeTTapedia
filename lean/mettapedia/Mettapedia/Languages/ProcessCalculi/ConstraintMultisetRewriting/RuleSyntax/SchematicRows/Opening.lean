import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema

/-!
# The information of a fresh schematic-row activation

These statements use actual `RuleOccurrences.RFiring` values and their existing
extensions, openings and information. A premiseless row activation tells only
its local knowledge and the equations identifying its parameters with ambient
arguments. Length agreement prevents a truncated zip from dropping a capture.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Opening

open Interface (Frames)
open RuleOccurrences

universe uO uT uH uE uOcc uR uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {s : RState Tm O R C Z}
  (f : RFiring O R E codes s)

def rowClosure (value : Tm f.spec.locals) : Closure Tm s.frame :=
  ⟨⟨f.spec.locals, f.spec.body.tell, f.spec.params, value⟩, s.argsOf f.use⟩

theorem information_no_inputs (noTake : f.spec.body.take = []) (noRead : f.spec.body.read = []) :
    f.information X =
      X.applyStore (E.weaken f.ext) s.knowledge ++ X.applyStore f.opening f.spec.body.tell ++ f.env X := by
  simp [RFiring.information, Firing.information, Firing.matching, Firing.opened,
    RuleInstance.map, noTake, noRead, Frames.applyStore]

theorem models_env_iff {b : Obj} (u : Hom (E.target f.ext) b)
    (lengths : f.spec.params.length = (s.argsOf f.use).length) :
    X.Models u (f.env X) ↔
      List.Forall₂ (fun parameter argument =>
        X.E (X.act u (X.act f.opening parameter)) (X.act u (X.act (E.weaken f.ext) argument)))
        f.spec.params (s.argsOf f.use) := by
  have mapped :
      List.Forall₂ (fun parameter argument => X.E (X.act u parameter) (X.act u argument))
        (f.spec.params.map (X.act f.opening)) ((s.argsOf f.use).map (X.act (E.weaken f.ext))) ↔
      X.Models u (f.env X) := by
    rw [List.forall₂_iff_zip]
    constructor
    · rintro ⟨_, pairs⟩ equation member
      exact pairs member
    · intro solved
      refine ⟨by simpa only [List.length_map] using lengths, ?_⟩
      intro left right member
      exact solved (left, right) member
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at mapped
  exact mapped.symm

theorem models_information_iff (noTake : f.spec.body.take = []) (noRead : f.spec.body.read = [])
    {b : Obj} (u : Hom (E.target f.ext) b)
    (lengths : f.spec.params.length = (s.argsOf f.use).length) :
    X.Models u (f.information X) ↔
      X.Models (X.comp u (E.weaken f.ext)) s.knowledge ∧
      X.Models (X.comp u f.opening) f.spec.body.tell ∧
      List.Forall₂ (fun parameter argument =>
        X.E (X.act u (X.act f.opening parameter)) (X.act u (X.act (E.weaken f.ext) argument)))
        f.spec.params (s.argsOf f.use) := by
  rw [information_no_inputs X f noTake noRead, Frames.models_append, Frames.models_append,
    Frames.models_applyStore, Frames.models_applyStore, models_env_iff X f u lengths, and_assoc]

theorem args_mentioned (ambient : Set C) (available : s.Available ambient f.use)
    (argument : Tm s.frame) (inside : argument ∈ s.argsOf f.use) : s.Mentions argument := by
  cases use : f.use with
  | ambient code => simp [use, RState.argsOf] at inside
  | held occurrence =>
    have present : occurrence ∈ s.rules := by simpa [use, RState.Available] using available
    exact Or.inr ⟨occurrence, present, by simpa [use, RState.argsOf] using inside⟩

theorem parameter_in_terms (parameter : Tm f.spec.locals) (inside : parameter ∈ f.spec.params) :
    parameter ∈ f.spec.terms := by
  simp [Spec.terms, inside]

theorem produced_in_terms (value : Tm f.spec.locals) (inside : value ∈ f.spec.body.produce) :
    value ∈ f.spec.terms := by
  simp [Spec.terms, Rule.terms, inside]

theorem tell_left_in_terms (equation : Equation (Tm f.spec.locals)) (inside : equation ∈ f.spec.body.tell) :
    equation.1 ∈ f.spec.terms := by
  have member : equation.1 ∈ f.spec.body.tell.map Prod.fst := List.mem_map_of_mem inside
  simp [Spec.terms, Rule.terms, member]

theorem tell_right_in_terms (equation : Equation (Tm f.spec.locals)) (inside : equation ∈ f.spec.body.tell) :
    equation.2 ∈ f.spec.terms := by
  have member : equation.2 ∈ f.spec.body.tell.map Prod.snd := List.mem_map_of_mem inside
  simp [Spec.terms, Rule.terms, member]

#print axioms information_no_inputs
#print axioms models_env_iff
#print axioms models_information_iff
#print axioms args_mentioned

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Opening
