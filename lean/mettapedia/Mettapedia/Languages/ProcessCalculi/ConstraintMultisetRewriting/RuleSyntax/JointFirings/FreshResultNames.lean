import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.List

/-!
# Fresh CMR result identities can be aligned without moving the source

Profile: finite made-occurrence lists beside one fixed source store. This
resource lemma is independent of bag/set labels, guard timing and firing
discipline. Positions in the produced list, not arbitrary cardinalities,
determine the correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FreshResultNames

variable {O : Type} [DecidableEq O]

theorem align (source : Finset O) : ∀ (first second : List O),
    first.Nodup → second.Nodup → first.length = second.length →
    (∀ o ∈ first, o ∉ source) → (∀ o ∈ second, o ∉ source) →
    ∃ rename : Equiv.Perm O, first.map rename = second ∧ ∀ o ∈ source, rename o = o := by
  intro first
  induction first with
  | nil =>
    intro second _ _ lengths _ _
    have empty : second = [] := List.length_eq_zero_iff.mp lengths.symm
    subst second
    exact ⟨Equiv.refl O, rfl, fun _ _ => rfl⟩
  | cons head rest ih =>
    intro second firstDistinct secondDistinct lengths firstFresh secondFresh
    cases second with
    | nil => cases lengths
    | cons target later =>
      obtain ⟨rename, maps, fixes⟩ := ih later (List.nodup_cons.mp firstDistinct).2
        (List.nodup_cons.mp secondDistinct).2 (Nat.succ.inj lengths)
        (fun o member => firstFresh o (List.mem_cons_of_mem _ member))
        (fun o member => secondFresh o (List.mem_cons_of_mem _ member))
      let combined : Equiv.Perm O := rename.trans (Equiv.swap (rename head) target)
      refine ⟨combined, ?_, ?_⟩
      · change Equiv.swap (rename head) target (rename head) ::
          rest.map (fun o => Equiv.swap (rename head) target (rename o)) = target :: later
        rw [Equiv.swap_apply_left]
        apply congrArg (target :: ·)
        have fixedLater : later.map (Equiv.swap (rename head) target) = later := by
          conv_rhs => rw [← List.map_id later]
          apply List.map_congr_left
          intro o member
          apply Equiv.swap_apply_of_ne_of_ne
          · intro same
            have mapped : o ∈ rest.map rename := by rw [maps]; exact member
            obtain ⟨old, oldMember, sameImage⟩ := List.mem_map.mp mapped
            have oldEq := rename.injective (sameImage.trans same)
            exact (List.nodup_cons.mp firstDistinct).1 (oldEq ▸ oldMember)
          · intro same
            exact (List.nodup_cons.mp secondDistinct).1 (same ▸ member)
        have mapped := congrArg (List.map (Equiv.swap (rename head) target)) maps
        simpa only [List.map_map, Function.comp_def] using mapped.trans fixedLater
      · intro o member
        change Equiv.swap (rename head) target (rename o) = o
        rw [fixes o member]
        apply Equiv.swap_apply_of_ne_of_ne
        · intro same
          have images : rename o = rename head := (fixes o member).trans same
          exact firstFresh head List.mem_cons_self (rename.injective images ▸ member)
        · intro same
          exact secondFresh target List.mem_cons_self (same ▸ member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.FreshResultNames
