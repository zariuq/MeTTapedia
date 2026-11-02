import Mettapedia.GSLT.LanguageDef.SingleSortABT
import Mettapedia.TypeTheory.ScopeMapFactorization

/-!
# Scoped application with reordered, repeated and compound arguments

Finite renamings and simultaneous argument substitution act on the existing
one-axis ABT through its proved single-sort bridge. Context size checks do
not require injectivity. Injectivity is precisely the extra condition needed
for inverse renaming to be unique; ordinary application can contract slots.

The model concerns structural scope and capture-avoiding application. Object
typing, resource grades and logical admission qualify these operations
separately. No surface syntax or global conversion profile is selected.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication

open Mettapedia.TypeTheory.ScopeMapFactorization

variable {Head : Type} {n m p : ℕ}

/-- Extend a finite context map to loose indices outside its domain. The
outside tail is placed beyond the target context and cannot alias it. -/
def extend (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if inside : i < n then (f ⟨i, inside⟩).val else m + (i - n)

@[simp] theorem extend_inside (f : Fin n → Fin m) (i : Fin n) :
    extend f i.val = (f i).val := by simp [extend, i.isLt]

theorem extend_id : extend (id : Fin n → Fin n) = id := by
  funext i
  by_cases inside : i < n
  · simp [extend, inside]
  · simp only [extend, inside, ↓reduceDIte, id_eq]
    omega

theorem extend_comp (f : Fin n → Fin m) (g : Fin m → Fin p) :
    extend (fun i => g (f i)) = fun i => extend g (extend f i) := by
  funext i
  by_cases inside : i < n
  · simp only [extend, inside, ↓reduceDIte]
    rw [dif_pos (f ⟨i, inside⟩).isLt]
  · have outside : ¬m + (i - n) < m := by omega
    simp [extend, inside, outside]

theorem extend_injective (f : Fin n → Fin m) (injective : Function.Injective f) :
    Function.Injective (extend f) := by
  intro i j same
  by_cases hi : i < n <;> by_cases hj : j < n
  · simp only [extend, hi, hj, ↓reduceDIte] at same
    exact congrArg Fin.val (injective (Fin.ext same))
  · have upper := (f ⟨i, hi⟩).isLt
    simp only [extend, hi, hj, ↓reduceDIte] at same
    omega
  · have upper := (f ⟨j, hj⟩).isLt
    simp only [extend, hi, hj, ↓reduceDIte] at same
    omega
  · simp only [extend, hi, hj, ↓reduceDIte] at same
    omega

def applyRenaming (f : Fin n → Fin m) (body : Term Head) : Term Head :=
  Term.renameMany (extend f) body

@[simp] theorem applyRenaming_idx (f : Fin n → Fin m) (i : Fin n) :
    applyRenaming f (.idx i.val : Term Head) = .idx (f i).val := by
  simp [applyRenaming]

@[simp] theorem applyRenaming_id (body : Term Head) :
    applyRenaming (id : Fin n → Fin n) body = body := by
  simp [applyRenaming, extend_id]

theorem applyRenaming_comp (f : Fin n → Fin m) (g : Fin m → Fin p) (body : Term Head) :
    applyRenaming g (applyRenaming f body) = applyRenaming (fun i => g (f i)) body := by
  simp only [applyRenaming, Term.renameMany_comp, extend_comp]

theorem applyRenaming_supported (f : Fin n → Fin m) (body : Term Head)
    (wellScoped : Term.supportedAt n body = true) :
    Term.supportedAt m (applyRenaming f body) = true := by
  apply Term.renameMany_supported (source := n) _ body wellScoped
  intro i inside
  simpa only [extend, dif_pos inside] using (f ⟨i, inside⟩).isLt

theorem applyRenaming_injective_iff (f : Fin n → Fin m) :
    Function.Injective (applyRenaming f : Term Head → Term Head) ↔ Function.Injective f := by
  constructor
  · intro operation i j same
    have terms : applyRenaming f (.idx i.val : Term Head) = applyRenaming f (.idx j.val) := by
      simp [same]
    have sameTerms := operation terms
    exact Fin.ext (Term.idx.inj sameTerms)
  · intro injective
    have inverse := Function.leftInverse_invFun (extend_injective f injective)
    exact (Term.renameMany_leftInverse _ _ inverse).injective

theorem applyRenaming_factor (f : Fin n → Fin m) (injective : Function.Injective f)
    (body : Term Head) :
    applyRenaming f body =
      applyRenaming (ordered f injective) (applyRenaming (permutationIndex f injective) body) := by
  rw [applyRenaming_comp]
  have same : f = fun i => ordered f injective (permutationIndex f injective i) :=
    funext (factor f injective)
  rw [← same]

def argumentAt (arguments : List (Term Head)) (i : ℕ) : Term Head :=
  arguments[i]?.getD (.idx i)

/-- A contextual object's declared arity is retained even when some of its
parameters are unused. Application substitutes every slot simultaneously. -/
def graft (arity : ℕ) (arguments : List (Term Head)) (body : Term Head) : Option (Term Head) :=
  if arguments.length = arity ∧ Term.supportedAt arity body = true then
    some (Term.substituteMany (argumentAt arguments) body)
  else none

theorem graft_supported {arity target : ℕ} {arguments : List (Term Head)} {body result : Term Head}
    (argumentsScoped : ∀ arg ∈ arguments, Term.supportedAt target arg = true)
    (applied : graft arity arguments body = some result) :
    Term.supportedAt target result = true := by
  unfold graft at applied
  split at applied
  · rename_i qualified
    obtain ⟨count, bodyScoped⟩ := qualified
    have same := Option.some.inj applied
    rw [← same]
    apply Term.substituteMany_supported (source := arity) _ body bodyScoped
    intro i inside
    have member : i < arguments.length := by omega
    simpa [argumentAt, List.getElem?_eq_getElem member] using
      argumentsScoped arguments[i] (List.getElem_mem member)
  · cases applied

theorem graft_substitution {arity : ℕ} (arguments : List (Term Head)) (body : Term Head)
    (count : arguments.length = arity) (bodyScoped : Term.supportedAt arity body = true)
    (τ : ℕ → Term Head) :
    graft arity (arguments.map (Term.substituteMany τ)) body =
      (graft arity arguments body).map (Term.substituteMany τ) := by
  simp only [graft, List.length_map, count, bodyScoped, and_self, ↓reduceIte, Option.map_some]
  congr 1
  rw [Term.substituteMany_comp]
  apply Term.substituteMany_congr_scoped _ body bodyScoped
  intro i inside
  have member : i < arguments.length := by omega
  simp [argumentAt, List.getElem?_eq_getElem member, List.getElem?_eq_getElem
    (show i < (arguments.map (Term.substituteMany τ)).length by simpa using member)]

/-- A contextual value is an existing term with its scope retained. This
wrapper does not turn open code into closed code or introduce a new AST. -/
abbrev InScope (Head : Type) (width : ℕ) := { t : Term Head // Term.supportedAt width t = true }

def recontextualize (f : Fin n → Fin m) (value : InScope Head n) : InScope Head m :=
  ⟨applyRenaming f value.val, applyRenaming_supported f value.val value.property⟩

theorem firstField_scope {head : Head} {depth : ℕ} {body : Term Head} {rest : Fields Head}
    (valid : Term.supportedAt n (.node head (.cons depth body rest)) = true) :
    Term.supportedAt (n + depth) body = true := by
  simp only [Term.supportedAt, Term.Fields.supportedAt, Bool.and_eq_true] at valid
  exact valid.1

/-- Ordinary binder inspection can return the body with its enlarged scope,
without demanding a dependency annotation from the program. -/
def openFirst (value : InScope Head n) : Option (Σ depth, InScope Head (n + depth)) :=
  match value with
  | ⟨.node _ (.cons depth body _), valid⟩ =>
    some ⟨depth, body, firstField_scope valid⟩
  | _ => none

theorem openFirst_exact (head : Head) (depth : ℕ) (body : Term Head) (rest : Fields Head)
    (valid : Term.supportedAt n (.node head (.cons depth body rest)) = true) :
    ∃ bodyValid : Term.supportedAt (n + depth) body = true,
      openFirst ⟨.node head (.cons depth body rest), valid⟩ = some ⟨depth, body, bodyValid⟩ := by
  exact ⟨firstField_scope valid, rfl⟩

namespace Controls

local instance : DecidableEq (Term ℕ) := fun a b =>
  decidable_of_iff (SingleSort.encode a = SingleSort.encode b)
    ⟨fun same => SingleSort.encode_injective same, congrArg SingleSort.encode⟩

def pair (a b : Term ℕ) : Term ℕ := .node 2 (.cons 0 a (.cons 0 b .nil))
def lambda (body : Term ℕ) : Term ℕ := .node 1 (.cons 1 body .nil)

theorem reordered_application_is_legal :
    graft 2 [.idx 1, .idx 0] (pair (.idx 0) (.idx 1)) =
      some (pair (.idx 1) (.idx 0)) := by decide

theorem repeated_argument_application_is_legal :
    graft 2 [.idx 0, .idx 0] (pair (.idx 0) (.idx 1)) =
      some (pair (.idx 0) (.idx 0)) := by decide

theorem repeated_argument_application_loses_inverse_uniqueness :
    graft 2 [.idx 0, .idx 0] (.idx 0 : Term ℕ) =
      graft 2 [.idx 0, .idx 0] (.idx 1) ∧ (.idx 0 : Term ℕ) ≠ .idx 1 := by decide

theorem graft_does_not_capture_outer_argument :
    graft 1 [.idx 0] (lambda (.idx 1)) = some (lambda (.idx 1)) ∧
      graft 1 [.idx 0] (lambda (.idx 1)) ≠ some (lambda (.idx 0)) := by decide

theorem simultaneous_graft_is_not_sequential_replacement :
    graft 2 [.idx 1, .idx 0] (pair (.idx 0) (.idx 1)) =
      some (pair (.idx 1) (.idx 0)) ∧
    Term.substituteMany (fun i => if i = 1 then .idx 0 else .idx i)
        (Term.substituteMany (fun i => if i = 0 then .idx 1 else .idx i)
          (pair (.idx 0) (.idx 1))) ≠
      pair (.idx 1) (.idx 0) := by decide

theorem unused_parameter_remains_part_of_the_interface :
    graft 1 [] (.node 7 .nil : Term ℕ) = none ∧
      graft 1 [.idx 0] (.node 7 .nil : Term ℕ) = some (.node 7 .nil) := by decide

theorem compound_arguments_are_legal :
    graft 1 [pair (.idx 0) (.idx 1)] (.idx 0) =
      some (pair (.idx 0) (.idx 1)) := by decide

theorem an_unlisted_parameter_is_refused :
    graft 1 [.idx 0] (.idx 1 : Term ℕ) = none := by decide

end Controls
end Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
