import Mettapedia.Logic.LP.UnificationIdempotence
import Mettapedia.Logic.LP.UnificationRenaming

/-!
# Mutual finite-term instances differ only by variable renaming

The maps are extracted from the actual substitutions. A retraction forces
variable images on the observed support; no global permutation or restriction
on unused coordinates is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.MutualInstantiation

variable {σ : LPSignature}

def variableImage (substitution : Subst σ) (name : σ.vars) : σ.vars :=
  match substitution name with
  | .var image => image
  | _ => name

theorem variable_image_of_retraction [DecidableEq σ.vars]
    (forward backward : Subst σ) (term : Term σ)
    (recovered : backward.applyTerm (forward.applyTerm term) = term)
    (name : σ.vars) (present : name ∈ term.freeVars) :
    forward name = .var (variableImage forward name) := by
  have fixed : (backward ∘ₛ forward).applyTerm term = term := by
    rw [Subst.applyTerm_comp]
    exact recovered
  have named := Subst.var_fixed_of_applyTerm_eq_self fixed name present
  change backward.applyTerm (forward name) = .var name at named
  cases view : forward name with
  | var image => simp only [variableImage,view]
  | const value => simp only [view,Subst.applyTerm] at named; cases named
  | app head children => simp only [view,Subst.applyTerm] at named; cases named

theorem variable_images_retract [DecidableEq σ.vars]
    (forward backward : Subst σ) (term : Term σ)
    (recovered : backward.applyTerm (forward.applyTerm term) = term)
    (name : σ.vars) (present : name ∈ term.freeVars) :
    variableImage backward (variableImage forward name) = name := by
  have first := variable_image_of_retraction forward backward term recovered name present
  have fixed : (backward ∘ₛ forward).applyTerm term = term := by
    rw [Subst.applyTerm_comp]
    exact recovered
  have second := Subst.var_fixed_of_applyTerm_eq_self fixed name present
  change backward.applyTerm (forward name) = .var name at second
  rw [first] at second
  change backward (variableImage forward name) = .var name at second
  change (match backward (variableImage forward name) with
    | .var image => image
    | _ => variableImage forward name) = name
  rw [second]

theorem rename_of_retraction [DecidableEq σ.vars]
    (forward backward : Subst σ) (term : Term σ)
    (recovered : backward.applyTerm (forward.applyTerm term) = term) :
    UnificationRenaming.rename (variableImage forward) term = forward.applyTerm term := by
  apply Eq.symm
  apply Subst.applyTerm_congr
  intro name present
  exact variable_image_of_retraction forward backward term recovered name present

theorem mutual_instance_renamings [DecidableEq σ.vars]
    (forward backward : Subst σ) (first second : Term σ)
    (advanced : forward.applyTerm first = second)
    (recovered : backward.applyTerm second = first) :
    UnificationRenaming.rename (variableImage forward) first = second ∧
      UnificationRenaming.rename (variableImage backward) second = first := by
  constructor
  · exact (rename_of_retraction forward backward first (by rw [advanced,recovered])).trans advanced
  · exact (rename_of_retraction backward forward second (by rw [recovered,advanced])).trans recovered

theorem forward_injective_on_support [DecidableEq σ.vars]
    (forward backward : Subst σ) (term : Term σ)
    (recovered : backward.applyTerm (forward.applyTerm term) = term) :
    ∀ first ∈ term.freeVars, ∀ second ∈ term.freeVars,
      variableImage forward first = variableImage forward second → first = second := by
  intro first firstPresent second secondPresent same
  have one := variable_images_retract forward backward term recovered first firstPresent
  have two := variable_images_retract forward backward term recovered second secondPresent
  exact one.symm.trans ((congrArg (variableImage backward) same).trans two)

theorem moreGeneral_on_terms (first second : Subst σ) (general : first.moreGeneral second) :
    ∃ factor : Subst σ, ∀ term, second.applyTerm term = factor.applyTerm (first.applyTerm term) := by
  obtain ⟨factor,coordinates⟩ := general
  refine ⟨factor,?_⟩
  intro term
  have same : second = factor ∘ₛ first := funext coordinates
  rw [same,Subst.applyTerm_comp]

theorem mutually_general_renamings [DecidableEq σ.vars] (first second : Subst σ)
    (forward : first.moreGeneral second) (backward : second.moreGeneral first) :
    ∃ names inverse : σ.vars → σ.vars, ∀ term,
      UnificationRenaming.rename names (first.applyTerm term) = second.applyTerm term ∧
        UnificationRenaming.rename inverse (second.applyTerm term) = first.applyTerm term := by
  obtain ⟨next,advance⟩ := moreGeneral_on_terms first second forward
  obtain ⟨previous,recover⟩ := moreGeneral_on_terms second first backward
  refine ⟨variableImage next,variableImage previous,?_⟩
  intro term
  exact mutual_instance_renamings next previous (first.applyTerm term) (second.applyTerm term)
    (advance term).symm (recover term).symm

end Mettapedia.Logic.LP.MutualInstantiation
