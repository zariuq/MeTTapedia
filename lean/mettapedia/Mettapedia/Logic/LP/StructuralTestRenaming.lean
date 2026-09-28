import Mettapedia.Logic.LP.UnificationRenaming
import Mettapedia.Logic.LP.UnificationIdempotence

/-!
# Structural tests under a lossless renaming of variables

Two tests read their operands' structure and compare the operands' variables
only with one another: equality of terms, and being variants, where a renaming
of the first term's variables, one-to-one on them, gives the second.  Neither
binds a variable or looks at how one is spelled.

A lossless variable coordinate change (`UnificationRenaming`: a renaming with a
left inverse) applied to both operands leaves both answers unchanged
(`rename_eq_iff`, `variant_rename_iff`).  So either test asked of two values in
one coordinate system has the answer it has in another: a machine may answer it
over its own cells where its host would answer it over the variables the
machine hands over for them, one per cell.

Only the variables' identities are compared.  A test that reads a variable's
spelling has no such law (`TransactionalSearchHead.spelling_test_is_not_equivariant`),
and neither test survives a renaming that merges two variables
(`Controls.merge_breaks_variance`, `Controls.merge_breaks_equality`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.StructuralTestRenaming

open UnificationRenaming

variable {σ : LPSignature}

/-! ## Equality -/

/-- Equality is decided alike in both coordinate systems. -/
theorem rename_eq_iff (f g : σ.vars → σ.vars) (inverse : Function.LeftInverse g f)
    (a b : Term σ) : rename f a = rename f b ↔ a = b :=
  (rename_injective f g inverse).eq_iff

/-! ## Variants -/

section Variants

variable [DecidableEq σ.vars]

/-- A renamed term's variables are the renamed variables. -/
theorem mem_freeVars_rename {r : σ.vars → σ.vars} {t : Term σ} {x : σ.vars} :
    x ∈ (rename r t).freeVars ↔ ∃ v ∈ t.freeVars, x = r v := by
  have renamed := Subst.mem_freeVars_applyTerm
    (θ := (fun v => Term.var (r v) : Subst σ)) (t := t) (x := x)
  simp only [Term.mem_freeVars_var] at renamed
  exact renamed

/-- `a` and `b` are variants: a renaming of `a`'s variables, one-to-one on
them, takes `a` to `b`. -/
def Variant (a b : Term σ) : Prop :=
  ∃ r : σ.vars → σ.vars, Set.InjOn r ↑a.freeVars ∧ rename r a = b

/-- A lossless coordinate change neither creates nor destroys a variance. -/
theorem variant_rename_iff (f g : σ.vars → σ.vars) (inverse : Function.LeftInverse g f)
    (a b : Term σ) : Variant (rename f a) (rename f b) ↔ Variant a b := by
  constructor
  · rintro ⟨r, oneToOne, same⟩
    -- `r` sends each renamed variable of `a` to a renamed variable of `b`,
    -- where `g` undoes `f`.
    have image : ∀ v ∈ a.freeVars, ∃ w ∈ b.freeVars, r (f v) = f w := by
      intro v va
      have inTarget : r (f v) ∈ (rename f b).freeVars := by
        rw [← same, mem_freeVars_rename]
        exact ⟨f v, mem_freeVars_rename.mpr ⟨v, va, rfl⟩, rfl⟩
      exact mem_freeVars_rename.mp inTarget
    refine ⟨g ∘ r ∘ f, ?_, ?_⟩
    · intro x xa y ya equal
      obtain ⟨u, -, hu⟩ := image x xa
      obtain ⟨w, -, hw⟩ := image y ya
      have uw : u = w := by
        have back : g (r (f x)) = g (r (f y)) := equal
        rw [hu, hw, inverse u, inverse w] at back
        exact back
      have rr : r (f x) = r (f y) := by rw [hu, hw, uw]
      exact inverse.injective
        (oneToOne (mem_freeVars_rename.mpr ⟨x, xa, rfl⟩)
          (mem_freeVars_rename.mpr ⟨y, ya, rfl⟩) rr)
    · have composed : rename (g ∘ r ∘ f) a = rename g (rename r (rename f a)) := by
        rw [rename_comp, rename_comp, Function.comp_assoc]
      rw [composed, same]
      exact rename_leftInverse f g inverse b
  · rintro ⟨r, oneToOne, same⟩
    refine ⟨f ∘ r ∘ g, ?_, ?_⟩
    · intro x xa y ya equal
      obtain ⟨u, ua, rfl⟩ := mem_freeVars_rename.mp xa
      obtain ⟨w, wa, rfl⟩ := mem_freeVars_rename.mp ya
      have back : f (r (g (f u))) = f (r (g (f w))) := equal
      rw [inverse u, inverse w] at back
      exact congrArg f (oneToOne ua wa (inverse.injective back))
    · have composed : rename (f ∘ r ∘ g) (rename f a) = rename f (rename r a) := by
        rw [rename_comp, rename_comp]
        congr 1
        funext v
        simp only [Function.comp_apply, inverse v]
      rw [composed, same]

end Variants

/-! ## Controls -/

namespace Controls

open UnificationRenaming.Controls

private theorem arrow_fields {a b c d : Term sig} (same : arrow a b = arrow c d) :
    a = c ∧ b = d := by
  have children : (![a, b] : Fin 2 → Term sig) = ![c, d] := by
    injection same
  exact ⟨congrFun children 0, congrFun children 1⟩

private theorem rename_arrow (r : sig.vars → sig.vars) (a b : Term sig) :
    rename r (arrow a b) = arrow (rename r a) (rename r b) := by
  change Term.app _ _ = Term.app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Swapping two variables: `f(x, y)` and `f(y, x)` are variants. -/
theorem swapped_variant : Variant (arrow (.var 0) (.var 1)) (arrow (.var 1) (.var 0)) := by
  refine ⟨Equiv.swap (0 : sig.vars) 1,
    fun _ _ _ _ equal => (Equiv.swap (0 : sig.vars) 1).injective equal, ?_⟩
  rw [rename_arrow, rename_var, rename_var, Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- The variables of `f(x, x)` and `f(x, y)` are not in correspondence. -/
theorem shared_not_variant : ¬ Variant (arrow (.var 0) (.var 0)) (arrow (.var 0) (.var 1)) := by
  rintro ⟨r, -, same⟩
  rw [rename_arrow] at same
  obtain ⟨first, second⟩ := arrow_fields same
  rw [first] at second
  exact Nat.zero_ne_one (Term.var.inj second)

/-- Merging two variables makes a pair that is not a variant one: the change
must be lossless. -/
theorem merge_breaks_variance :
    ¬ Variant (arrow (.var 0) (.var 0)) (arrow (.var 0) (.var 1)) ∧
      Variant (rename (σ := sig) (fun _ => 0) (arrow (.var 0) (.var 0)))
        (rename (σ := sig) (fun _ => 0) (arrow (.var 0) (.var 1))) := by
  refine ⟨shared_not_variant, id, Set.injOn_id _, ?_⟩
  rw [rename_arrow, rename_arrow, rename_arrow]
  rfl

/-- Merging two variables makes distinct terms equal. -/
theorem merge_breaks_equality :
    (arrow (.var 0) (.var 1) : Term sig) ≠ arrow (.var 0) (.var 0) ∧
      rename (σ := sig) (fun _ => 0) (arrow (.var 0) (.var 1)) =
        rename (σ := sig) (fun _ => 0) (arrow (.var 0) (.var 0)) := by
  refine ⟨fun same => ?_, ?_⟩
  · obtain ⟨-, second⟩ := arrow_fields same
    exact Nat.one_ne_zero (Term.var.inj second)
  · rw [rename_arrow, rename_arrow]
    rfl

/-- A lossless change, `v ↦ v + 100` undone by `v ↦ v - 100`, keeps both
answers: `f(x, y)` and `f(y, x)` stay variants, `f(x, x)` and `f(x, y)` stay
not. -/
theorem shifted_answers :
    Variant (rename (σ := sig) (· + 100) (arrow (.var 0) (.var 1)))
        (rename (σ := sig) (· + 100) (arrow (.var 1) (.var 0))) ∧
      ¬ Variant (rename (σ := sig) (· + 100) (arrow (.var 0) (.var 0)))
        (rename (σ := sig) (· + 100) (arrow (.var 0) (.var 1))) := by
  have inverse : Function.LeftInverse (fun v : Nat => v - 100) (· + 100) := by
    intro v
    simp
  exact ⟨(variant_rename_iff (σ := sig) _ _ inverse _ _).mpr swapped_variant,
    fun shifted =>
      shared_not_variant ((variant_rename_iff (σ := sig) _ _ inverse _ _).mp shifted)⟩

end Controls

end Mettapedia.Logic.LP.StructuralTestRenaming
