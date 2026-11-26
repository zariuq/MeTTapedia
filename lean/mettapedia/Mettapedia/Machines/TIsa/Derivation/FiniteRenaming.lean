import Mettapedia.Logic.LP.MutualInstantiation
import Mathlib.Logic.Equiv.Fintype

/-!
# One renaming for simultaneous observations

Mutually instantiable finite families of first-order terms differ
by one variable permutation. The permutation is consistent across
the whole family, so it preserves sharing between terms. It agrees
with the witnessed substitution on the observed variables and need
not specify how unused variables are permuted.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.MutualInstantiation

open UnificationRenaming (rename)

variable {σ : LPSignature} [DecidableEq σ.vars]

def listSupport : List (Term σ) → Finset σ.vars
  | [] => ∅
  | term :: later => term.freeVars ∪ listSupport later

theorem mem_listSupport (terms : List (Term σ)) (x : σ.vars) :
    x ∈ listSupport terms ↔ ∃ term ∈ terms, x ∈ term.freeVars := by
  induction terms with
  | nil => simp [listSupport]
  | cons first rest ih => simp [listSupport, ih, List.mem_cons]

private theorem fixes_on_list {A : Type*} (terms : List A) (f : A → A) (mapped : terms.map f = terms) :
    ∀ t ∈ terms, f t = t := by
  induction terms with
  | nil => intro x member; cases member
  | cons first rest ih =>
    obtain ⟨head, later⟩ := List.cons.inj mapped
    intro t member
    rcases List.mem_cons.mp member with rfl | inside
    · exact head
    · exact ih later t inside

omit [DecidableEq σ.vars] in
private theorem returnTerm (forward backward : Subst σ) (first second : List (Term σ))
    (advanced : first.map forward.applyTerm = second) (recovered : second.map backward.applyTerm = first)
    (t : Term σ) (inside : t ∈ first) :
    backward.applyTerm (forward.applyTerm t) = t := by
  have roundTrip : first.map (fun entry => backward.applyTerm (forward.applyTerm entry)) = first := by
    change first.map (backward.applyTerm ∘ forward.applyTerm) = first
    rw [← List.map_map, advanced, recovered]
  exact fixes_on_list first _ roundTrip t inside

private theorem support_map (forward backward : Subst σ) (first second : List (Term σ))
    (advanced : first.map forward.applyTerm = second) (recovered : second.map backward.applyTerm = first)
    (name : σ.vars) (inside : name ∈ listSupport first) :
    variableImage forward name ∈ listSupport second ∧ variableImage backward (variableImage forward name) = name := by
  obtain ⟨term, observed, mentioned⟩ := (mem_listSupport first name).mp inside
  have returns := returnTerm forward backward first second advanced recovered term observed
  refine ⟨?_, variable_images_retract forward backward term returns name mentioned⟩
  apply (mem_listSupport second (variableImage forward name)).mpr
  refine ⟨forward.applyTerm term, advanced ▸ List.mem_map.mpr ⟨term, observed, rfl⟩, ?_⟩
  apply Subst.mem_freeVars_applyTerm.mpr
  refine ⟨name, mentioned, ?_⟩
  rw [variable_image_of_retraction forward backward term returns name mentioned]
  exact Term.mem_freeVars_var.mpr rfl

/-- A single permutation realizes both finite families, including
their shared variables. This extends a finite equivalence, not an
assumption that the substitutions were permutations everywhere. -/
theorem permutation_of_mutual_lists (forward backward : Subst σ) (first second : List (Term σ))
    (advanced : first.map forward.applyTerm = second) (recovered : second.map backward.applyTerm = first) :
    ∃ π : Equiv.Perm σ.vars,
      first.map (rename π) = second ∧
      ∀ name ∈ listSupport first, π name = variableImage forward name := by
  let equiv : {x // x ∈ listSupport first} ≃ {x // x ∈ listSupport second} :=
    { toFun := fun name => ⟨variableImage forward name, (support_map forward backward first second advanced recovered _ name.2).1⟩
      invFun := fun name => ⟨variableImage backward name, (support_map backward forward second first recovered advanced _ name.2).1⟩
      left_inv := fun name => Subtype.ext (support_map forward backward first second advanced recovered _ name.2).2
      right_inv := fun name => Subtype.ext (support_map backward forward second first recovered advanced _ name.2).2 }
  let π := equiv.extendSubtype
  have action (name : σ.vars) (inside : name ∈ listSupport first) : π name = variableImage forward name :=
    equiv.extendSubtype_apply_of_mem name inside
  refine ⟨π, ?_, action⟩
  have equal : first.map (rename π) = first.map forward.applyTerm := by
    apply List.map_congr_left
    intro term inside
    have returns := returnTerm forward backward first second advanced recovered term inside
    rw [← rename_of_retraction forward backward term returns]
    apply Subst.applyTerm_congr
    intro v mentioned
    exact congrArg Term.var (action v ((mem_listSupport first v).mpr ⟨term, inside, mentioned⟩))
  exact equal.trans advanced

end Mettapedia.Logic.LP.MutualInstantiation
