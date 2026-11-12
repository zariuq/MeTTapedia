import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# Predicate families as a category with families

Contexts are sets, types are predicates, terms are sections supplying a
proof at each point, and comprehension is the satisfying subtype. A judged
term over a context supplies a proof everywhere in that context. Consequently
its readings along any two substitutions agree, even though arbitrary types
can distinguish the substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateFamilies

open Mettapedia.GSLT.Core.ContextualLadder

universe u

def model : Cwf.{u + 1, u, u, u} where
  Ctx := Type u
  Sub source target := source → target
  idS _ := id
  compS first second := first ∘ second
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Ty context := context → Prop
  tySub predicate substitution := predicate ∘ substitution
  tySub_id _ := rfl
  tySub_comp _ _ _ := rfl
  Tm context predicate := ∀ point : context, PLift (predicate point)
  tmSub term substitution := fun point => term (substitution point)
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext context predicate := {point : context // predicate point}
  wk _ := Subtype.val
  vz _ := fun point => ⟨point.property⟩
  pair substitution _ term := fun point => ⟨substitution point, (term point).down⟩
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := Subsingleton.elim _ _
  pair_eta _ _ := rfl

/-- The model also has the chosen terminal context of the full CwF interface. -/
def modelWithTerminal : CwfWithTerminal.{u + 1, u, u, u} where
  toCwf := model
  empty := PUnit
  toEmpty _ := fun _ => PUnit.unit
  toEmpty_unique := by
    intro context substitution
    funext point
    cases substitution point
    rfl

theorem inhabited_types_agree {source target : Type u} (predicate : model.Ty target)
    (term : model.Tm target predicate) (first second : model.Sub source target) :
    model.tySub predicate first = model.tySub predicate second := by
  funext point
  exact propext ⟨fun _ => (term (second point)).down, fun _ => (term (first point)).down⟩

theorem judged_readings_agree {source target : Type u} (predicate : model.Ty target)
    (term : model.Tm target predicate) (first second : model.Sub source target) :
    (⟨model.tySub predicate first, model.tmSub term first⟩ : Σ type : model.Ty source, model.Tm source type) =
      ⟨model.tySub predicate second, model.tmSub term second⟩ := by
  have same := inhabited_types_agree predicate term first second
  apply Sigma.ext same
  have moved := congrArg (model.Tm source) same
  have unique : Subsingleton (model.Tm source (model.tySub predicate second)) := by
    dsimp only [model]
    infer_instance
  exact (cast_heq moved (model.tmSub term first)).symm.trans
    (heq_of_eq (unique.elim _ _))

theorem false_fibre_has_no_section : ¬ Nonempty (model.Tm Unit (fun _ => False)) := by
  rintro ⟨term⟩
  exact (term ()).down

theorem true_fibre_has_section : Nonempty (model.Tm Unit (fun _ => True)) :=
  ⟨fun _ => ⟨True.intro⟩⟩

end Mettapedia.TypeTheory.ContextualPredicateFamilies

#print axioms Mettapedia.TypeTheory.ContextualPredicateFamilies.judged_readings_agree
