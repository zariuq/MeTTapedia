import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication

/-!
# General renaming on shared references

All variable references share one interned variable node. General renaming
uses the shared graft operation; it supports permutations and contraction,
without unfolding the source body. Scope checks and the denotation theorem
remain those of the common ABT carrier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication

variable {Head : Type} [DecidableEq Head]

/-- Intern one variable node and place it at each requested index. -/
def variablesR (store : Store Head) (indices : List Nat) : Store Head × List Ref :=
  match indices with
  | [] => (store, [])
  | _ :: _ =>
      let varNode := intern store .var
      (varNode.1, indices.map fun index => ⟨Thin.dropN index [true], varNode.2⟩)

theorem variablesR_spec (store : Store Head) (canonical : Canonical store) (indices : List Nat) :
    store <+: (variablesR store indices).1 ∧ Canonical (variablesR store indices).1 ∧
      (∀ r ∈ (variablesR store indices).2, CanonRef (variablesR store indices).1 r) ∧
      (variablesR store indices).2.map (unfold (variablesR store indices).1) = indices.map Term.idx := by
  cases indices with
  | nil => exact ⟨List.prefix_refl _, canonical, by simp [variablesR], rfl⟩
  | cons index rest =>
    refine ⟨intern_prefix _ _, intern_canonical canonical (nodeOk_var _), ?_, ?_⟩
    · intro r member
      change r ∈ (index :: rest).map (fun i => (⟨Thin.dropN i [true], (intern store .var).2⟩ : Ref)) at member
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
      exact (encodeR_spec store canonical (.idx i)).2.2.1
    · change ((index :: rest).map fun i =>
        (⟨Thin.dropN i [true], (intern store .var).2⟩ : Ref)).map (unfold (intern store .var).1) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact encodeR_unfold canonical (.idx i)

theorem variablesR_length (store : Store Head) (indices : List Nat) :
    (variablesR store indices).2.length = indices.length := by
  cases indices <;> simp [variablesR]

def renameR (store : Store Head) (indexMap : Nat → Nat) (body : Ref) : Store Head × Ref :=
  let prepared := variablesR store ((List.range body.thin.length).map indexMap)
  applyPrefixR body.thin.length prepared.2 prepared.1 body

omit [DecidableEq Head] in
theorem prefix_renaming (width : Nat) (indexMap : Nat → Nat) (body : Term Head)
    (scopedBody : Term.supportedAt width body = true) :
    applyPrefix width ((List.range width).map (fun i => Term.idx (indexMap i))) body =
      Term.renameMany indexMap body := by
  rw [← Term.substituteMany_renaming]
  unfold applyPrefix
  apply Term.substituteMany_congr_scoped _ body scopedBody
  intro index inside
  simp [prefixEnvironment, argumentAt, inside,
    show (fun i : Nat => i) = id from rfl]

/-- The executable reference operation computes arbitrary capture-free renaming. -/
theorem renameR_spec (store : Store Head) (canonical : Canonical store)
    (indexMap : Nat → Nat) (body : Ref) (validBody : CanonRef store body) :
    store <+: (renameR store indexMap body).1 ∧ Canonical (renameR store indexMap body).1 ∧
      CanonRef (renameR store indexMap body).1 (renameR store indexMap body).2 ∧
      unfold (renameR store indexMap body).1 (renameR store indexMap body).2 =
        Term.renameMany indexMap (unfold store body) := by
  obtain ⟨grows, nextCanonical, arguments, values⟩ :=
    variablesR_spec store canonical ((List.range body.thin.length).map indexMap)
  have count : (variablesR store ((List.range body.thin.length).map indexMap)).2.length = body.thin.length := by
    simp [variablesR_length]
  obtain ⟨more, finalCanonical, finalBody, applied⟩ :=
    applyPrefixR_spec body.thin.length _ _ body nextCanonical (validBody.prefix grows) arguments
      (Nat.le_of_eq count)
  refine ⟨grows.trans more, finalCanonical, finalBody, ?_⟩
  change unfold (applyPrefixR body.thin.length _ _ body).1 (applyPrefixR body.thin.length _ _ body).2 = _
  rw [applied, values, unfold_prefix canonical.topo grows validBody.valid]
  simp only [List.map_map, Function.comp_def]
  apply prefix_renaming
  rw [Scope.check_spec canonical validBody]
  simp [Scope.check]

namespace RenamingControls

def exchanged (index : Nat) : Nat := if index = 0 then 1 else if index = 1 then 0 else index

theorem shared_permutation_changes_slots :
    unfold (renameR Controls.stored.1 exchanged Controls.stored.2).1
      (renameR Controls.stored.1 exchanged Controls.stored.2).2 =
        Controls.pair (.idx 1) (.idx 0) := by decide

theorem shared_contraction_identifies_arguments :
    unfold (renameR Controls.stored.1 (fun _ => 0) Controls.stored.2).1
      (renameR Controls.stored.1 (fun _ => 0) Controls.stored.2).2 =
        Controls.pair (.idx 0) (.idx 0) := by decide

end RenamingControls
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedApplication
