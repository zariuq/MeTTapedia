import Mettapedia.Languages.MeTTa.PeTTa.CollectionCopyReadout
import Mettapedia.Languages.MeTTa.PeTTa.AnswerReadout
import Mettapedia.Languages.ProcessCalculi.MORK.SubstitutionSupport

/-!
# The actual answer copier satisfies the independent source contract

Every occurrence uses its actual activation number. The copy is injective,
different occurrences are apart, and retained caller bindings cannot capture
new variables. Required caller freshness comes from the maintained allocation
invariant, rather than a new validation pass or reserved source spelling.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying.CollectionCopies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.ScopedString (Before)
open EagerDFS

theorem copies_length (use : Nat) (answers : List Answer) : (copies use answers).length = answers.length := by
  induction answers generalizing use with
  | nil => rfl
  | cons first rest ih => simp only [copies,List.length_cons,ih]

theorem copies_get (use : Nat) (answers : List Answer) (index : Nat) (bound : index < answers.length) :
    (copies use answers)[index]'(by rw [copies_length]; exact bound) =
      rename (use + index) (resolve answers[index].bindings answers[index].value) := by
  induction answers generalizing use index with
  | nil => cases bound
  | cons first rest ih =>
      cases index with
      | zero => simp only [copies,List.getElem_cons_zero,Nat.add_zero]
      | succ index =>
          simpa only [copies,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
            ih (use + 1) index (Nat.lt_of_succ_lt_succ bound)

theorem copies_disjoint (use : Nat) (answers : List Answer) (first second : Nat)
    (firstBound : first < answers.length) (secondBound : second < answers.length) (different : first ≠ second) :
    AtomRenaming.Apart
      ((copies use answers)[first]'(by rw [copies_length]; exact firstBound))
      ((copies use answers)[second]'(by rw [copies_length]; exact secondBound)) := by
  rw [copies_get use answers first firstBound,copies_get use answers second secondBound]
  intro name firstIn secondIn
  rw [ScopedSource.rename_freeVars] at firstIn secondIn
  obtain ⟨left,_,leftName⟩ := List.mem_map.mp firstIn
  obtain ⟨right,_,rightName⟩ := List.mem_map.mp secondIn
  have same := (ScopedSource.freshName_equal_iff _ _ _ _).mp (leftName.trans rightName.symm)
  exact different (Nat.add_left_cancel same.1)

theorem renamed_source_copy (protectedNames : Finset String) (start scope : Nat) (value : Atom)
    (allocated : ∀ name ∈ protectedNames, Before start name) (later : start ≤ scope) :
    Collection.IsCopy protectedNames value [] (rename scope value,[]) := by
  refine ⟨freshName scope,?_,?_,?_,rfl⟩
  · intro first _ second _ same
    exact ((ScopedSource.freshName_equal_iff scope scope first second).mp same).2
  · intro name _ captured
    exact Mettapedia.ScopedString.new_identity_is_fresh
      (Mettapedia.ScopedString.before_mono later (allocated _ captured)) name rfl
  · rw [CollectionCopyReadout.type_renaming]
    exact AnswerReadout.rename_as_variable_map scope value

/-- The independently specified source contract includes occurrence order,
per-answer injectivity, separation and avoidance of the caller's inventory. -/
theorem copies_valid (protectedNames : Finset String) (use : Nat) (answers : List Answer)
    (allocated : ∀ name ∈ protectedNames, Before use name) :
    Collection.Copies protectedNames
      (answers.map fun answer => (resolve answer.bindings answer.value,[]))
      ((copies use answers).map fun value => (value,[])) := by
  refine ⟨by simp only [List.length_map,copies_length],?_,?_⟩
  · intro index before after
    have bound : index < answers.length := by simpa only [List.length_map] using before
    simp only [List.getElem_map]
    rw [copies_get use answers index bound]
    exact renamed_source_copy protectedNames use (use + index) _ allocated (Nat.le_add_right _ _)
  · intro first second firstBound secondBound different name present
    simp only [List.getElem_map,CollectionCopyReadout.type_variables] at present ⊢
    exact copies_disjoint use answers first second
      (by simpa only [List.length_map,copies_length] using firstBound)
      (by simpa only [List.length_map,copies_length] using secondBound) different name present

theorem caller_cannot_capture (use scope : Nat) (bindings : Subst) (value : Atom)
    (allocated : SupportedBindings (Before use) bindings) (later : use ≤ scope) :
    resolve bindings (rename scope value) = rename scope value := by
  apply applySubst_fixed_of_no_keys
  intro name present
  rw [ScopedSource.rename_freeVars] at present
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp present
  exact allocated_bindings_have_no_future_key scope bindings
    (allocated.mono (fun _ earlier => Mettapedia.ScopedString.before_mono later earlier)) original

theorem caller_cannot_capture_collection (use : Nat) (bindings : Subst) (answers : List Answer)
    (allocated : SupportedBindings (Before use) bindings) :
    resolve bindings (.expression (copies use answers)) = .expression (copies use answers) := by
  apply applySubst_fixed_of_no_keys
  intro name present
  obtain ⟨term,inCopies,inTerm⟩ := AtomRenaming.variables_expression.mp present
  obtain ⟨index,inBounds,atIndex⟩ := List.mem_iff_getElem.mp inCopies
  have bound : index < answers.length := by simpa only [copies_length] using inBounds
  rw [← atIndex,copies_get use answers index bound,ScopedSource.rename_freeVars] at inTerm
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp inTerm
  exact allocated_bindings_have_no_future_key (use + index) bindings
    (allocated.mono (fun _ earlier => Mettapedia.ScopedString.before_mono (Nat.le_add_right _ _) earlier)) original

theorem copies_apart_from_old (use : Nat) (answers : List Answer) (old : Atom)
    (allocated : Supported (Before use) old) :
    ∀ copied ∈ copies use answers, AtomRenaming.Apart old copied := by
  intro copied present name oldVariable copiedVariable
  obtain ⟨index,inBounds,atIndex⟩ := List.mem_iff_getElem.mp present
  have bound : index < answers.length := by simpa only [copies_length] using inBounds
  rw [← atIndex,copies_get use answers index bound,ScopedSource.rename_freeVars] at copiedVariable
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp copiedVariable
  exact ScopedSource.later_scope_is_apart (Nat.le_add_right _ _) allocated original oldVariable

end Mettapedia.Languages.MeTTa.PeTTa.Unifying.CollectionCopies
