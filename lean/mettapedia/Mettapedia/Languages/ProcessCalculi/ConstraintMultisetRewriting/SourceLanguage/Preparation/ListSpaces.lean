import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Services

/-!
# Space operations over a chosen key representation

Injective handle encoding licenses storing rows under different
keys, and reindexing transports the live rows and both update
operations. A key collision between distinct handles would break
the source law for insertion, even in an empty table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}

abbrev ListStorage (κ : Keys S) (Γ : Ctx S) (star : S.Srt) :=
  Term S Γ star → List (Row κ Γ star)

private def takeFirst {A : Type} (test : A → Bool) (items : List A) : Option (A × List A) :=
  match findFirst test items with
  | .found before item after _ _ => some (item, before ++ after)
  | .absent _ => none

def indexedSpaces {Key : Type} [DecidableEq Key] (encode : Term S Γ star → Key)
    (injective : Function.Injective encode) : Spaces κ Γ star (Key → List (Row κ Γ star)) where
  view storage handle := storage (encode handle)
  rows storage handle := storage (encode handle)
  rows_exact _ _ := rfl
  insert storage handle row := Function.update storage (encode handle) (row :: storage (encode handle))
  insert_exact storage handle row := by
    funext key
    by_cases same : key = handle
    · subst key
      rw [Function.update_self, setSpace_same, add_comm, Multiset.singleton_add]
      rfl
    · rw [Function.update_of_ne (fun equal => same (injective equal)), setSpace_other _ _ same]
  erase storage handle test :=
    (takeFirst test (storage (encode handle))).map fun (row, rest) =>
      (row, Function.update storage (encode handle) rest)
  erase_exact storage handle test := by
    unfold takeFirst
    cases findFirst test (storage (encode handle)) with
    | absent missing => exact missing
    | found before selected after selectedAt accepted =>
      refine ⟨accepted, (before ++ after : List (Row κ Γ star)), ?_, ?_⟩
      · have order : (storage (encode handle)).Perm (selected :: (before ++ after)) :=
          (List.Perm.of_eq selectedAt).trans List.perm_middle
        exact Multiset.coe_eq_coe.mpr order
      · funext key
        by_cases same : key = handle
        · subst key
          rw [Function.update_self, setSpace_same]
        · rw [Function.update_of_ne (fun equal => same (injective equal)), setSpace_other _ _ same]

abbrev listSpaces [DecidableEq (Term S Γ star)] : Spaces κ Γ star (ListStorage κ Γ star) :=
  indexedSpaces id Function.injective_id

def reindex {Key Target V : Type} (relocate : Key ≃ Target) (values : Key → V) : Target → V :=
  fun key => values (relocate.symm key)

private theorem reindex_update {Key Target V : Type} [DecidableEq Key] [DecidableEq Target]
    (relocate : Key ≃ Target) (values : Key → V) (site : Key) (value : V) :
    reindex relocate (Function.update values site value) =
      Function.update (reindex relocate values) (relocate site) value := by
  funext key
  by_cases same : key = relocate site
  · subst key
    simp [reindex]
  · have apart : relocate.symm key ≠ site := by
      intro equal
      exact same (by simpa using congrArg relocate equal)
    simp [reindex, Function.update_of_ne same, Function.update_of_ne apart]

section Relocation

variable {Key Target : Type} [DecidableEq Key] [DecidableEq Target]
    (relocate : Key ≃ Target) (encode : Term S Γ star → Key)
    (injective : Function.Injective encode) (storage : Key → List (Row κ Γ star))
    (handle : Term S Γ star)

theorem ordered_rows_reindex :
    (indexedSpaces (relocate ∘ encode) (relocate.injective.comp injective)).rows
      (reindex relocate storage) handle = (indexedSpaces encode injective).rows storage handle := by
  simp [indexedSpaces, reindex]

theorem indexed_insert_reindex (row : Row κ Γ star) :
    reindex relocate ((indexedSpaces encode injective).insert storage handle row) =
      (indexedSpaces (relocate ∘ encode) (relocate.injective.comp injective)).insert
        (reindex relocate storage) handle row := by
  simp [indexedSpaces, reindex_update, reindex]

theorem indexed_erase_reindex (test : Row κ Γ star → Bool) :
    ((indexedSpaces encode injective).erase storage handle test).map (fun (row, next) => (row, reindex relocate next)) =
      (indexedSpaces (relocate ∘ encode) (relocate.injective.comp injective)).erase
        (reindex relocate storage) handle test := by
  simp only [indexedSpaces, Function.comp_apply]
  have atHandle : reindex relocate storage (relocate (encode handle)) = storage (encode handle) := by
    simp [reindex]
  rw [atHandle]
  cases takeFirst test (storage (encode handle)) with
  | none => rfl
  | some returned =>
    obtain ⟨item, rest⟩ := returned
    exact congrArg (fun next => some (item, next)) (reindex_update relocate storage (encode handle) rest)

end Relocation

theorem insertion_requires_injective_keys {Key : Type} [DecidableEq Key] (encode : Term S Γ star → Key)
    (row : Row κ Γ star)
    (sourceLaw : ∀ (storage : Key → List (Row κ Γ star)) (handle : Term S Γ star),
      (fun key => (Function.update storage (encode handle) (row :: storage (encode handle)) (encode key) :
        Multiset (Row κ Γ star))) =
        setSpace (fun key => (storage (encode key) : Multiset (Row κ Γ star))) handle
          ((storage (encode handle) : Multiset (Row κ Γ star)) + {row})) :
    Function.Injective encode := by
  intro first second collision
  by_contra apart
  have framed := congrFun (sourceLaw (fun _ => []) first) second
  rw [setSpace_other _ _ (Ne.symm apart)] at framed
  simp [collision] at framed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation
