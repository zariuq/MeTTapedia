import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.AlignedEliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.EliminatorsControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.InterpControls

/-!
# Controls for the laws of the interpretation of annotated terms

**η.**

* Positive: the identity and the function sending `p` to `(p.1, p.2)`, both carrying
  the domain `Σ A G`, are equal, for every continuous family (`eta_pair_equal`). The
  interpretation of terms whose functions carry no domain separates them
  (`InterpControls.eta_not_equal_interp`).
* Negative: η needs the typing. The universe is not the pair of its projections
  (`univ_not_eta_pair`), and not the function carrying the domain `ℕ` whose value at
  `y` is its application to `y` (`univ_not_eta_fun`).

**β.** Positive: the successor carrying the domain `ℕ` sends zero to one
(`clam_succ_zero`). Negative: the argument is seen only through the domain, so the
identity carrying the domain `ℕ` does not return the universe (`clam_id_univ`).

**Type generation.** Positive: `Σ ℕ ℕ` carrying its domain is type-generated
(`sigma_nat_nat_typeGenerated`). Negative: the family must take types at the elements
of the domain, and `Σ ℕ 0` is not type-generated (`sigma_nat_zero_not_typeGenerated`).

**Reflexivity.** Positive: `refl 0` is an element of `Id ℕ 0 0` (`refl_zero_typed`).
Negative: the endpoints must be above the point, and `refl 0` is not an element of
`Id ℕ 0 1` (`refl_zero_not_typed_zero_one`).

**The eliminator read at the reflexivity point.**

* Positive: `J ℕ 0 (λ y p. ℕ) 0 0 (refl 0)` denotes `0` (`jAligned_closed`).
* Negative: the refl fact is needed. At `J ℕ 0 (λ y p. Id ℕ y y) (refl 0) 0 (refl ⊥)`
  the arguments have spine facts and the method is an element of the instantiated
  type, but the path's parameter type `Id ℕ 0 0` is not an identity type between `⊥`
  and itself; there the eliminator read at the reflexivity point does not denote the
  method, while the eliminator of `Eliminators` does (`refl_fact_needed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace ChurchLawsControls

open Ideal
open EliminatorControls (rd natMotive natMotive_spine idMotive app_app_idMotive natI_type oneI
  oneI_not_mem_zero refl_zero_mem refl_bot_mem reflTag_not_mem mem_refl_arg
  univ_not_mem_projT_nat)

/-! ## η -/

/-- **Positive**: η for pairs, under functions carrying a dependent pair type as their
domain. -/
theorem eta_pair_equal {A : Ideal} {G : Ideal → Ideal} (hG : Cont G) :
    clam (csigma A G) (fun y => y) = clam (csigma A G) (fun y => pair (fst y) (snd y)) :=
  clam_ext fun _ hy => (pair_fst_snd_of_mem hG hy).symm

theorem univ_mem_univ : univIdeal.Mem (.tag .univ) := ent_of_mem List.mem_cons_self

/-- A function has no tag. -/
theorem lam_no_tag (F : List Tok → Ideal) (k : Kind) : ¬ (lam F).Mem (.tag k) := by
  intro h
  obtain ⟨X, Y, e, -⟩ := closure_tag h
  cases e

/-- **Negative**: the universe is not the pair of its projections. -/
theorem univ_not_eta_pair : pair (fst univIdeal) (snd univIdeal) ≠ univIdeal := by
  intro h
  have hu := univ_mem_univ
  rw [← h] at hu
  exact InterpControls.pair_no_tag _ _ .univ hu

/-- **Negative**: the universe is not the function carrying the domain `ℕ` whose value
at `y` is its application to `y`. -/
theorem univ_not_eta_fun : clam natI (fun y => app univIdeal y) ≠ univIdeal := by
  intro h
  have hu := univ_mem_univ
  rw [← h] at hu
  exact lam_no_tag _ _ hu

/-! ## β -/

/-- **Positive**: β for the successor carrying the domain `ℕ`. -/
theorem clam_succ_zero : app (clam natI succI) zeroI = oneI := by
  rw [app_clam cont_succI, projT_natI_zeroI]
  rfl

/-- **Negative**: the identity carrying the domain `ℕ` sees the universe only through
`ℕ`, and does not return it. -/
theorem clam_id_univ : app (clam natI fun y => y) univIdeal ≠ univIdeal := by
  rw [app_clam Cont.id]
  intro h
  have hu := univ_mem_univ
  rw [← h] at hu
  exact univ_not_mem_projT_nat univIdeal hu

/-! ## Type generation -/

/-- **Positive**: `Σ ℕ ℕ`, carrying its domain, is type-generated. -/
theorem sigma_nat_nat_typeGenerated : TypeGenerated (csigma natI fun _ => natI) :=
  typeGenerated_csigma (Cont.const natI) (typeGenerated_principal nat_type)
    fun _ _ => typeGenerated_principal nat_type

/-- Zero is not type-generated. -/
theorem zero_not_typeGenerated : ¬ TypeGenerated zeroI := by
  intro h
  obtain ⟨v, hv, ht⟩ := h (.tag .zero) zeroI_mem_zero
  rw [ent_tag, hasTag_iff] at ht
  have h2 := tyTok_tag_zero.1 (hv _ ht).2
  rw [Elem.univ, List.mem_singleton] at h2
  exact absurd (Tok.tag.inj h2) (by decide)

/-- **Negative**: `Σ ℕ 0` is not type-generated: its family is not a type at the
elements of `ℕ`. -/
theorem sigma_nat_zero_not_typeGenerated : ¬ TypeGenerated (csigma natI fun _ => zeroI) :=
  fun h => zero_not_typeGenerated (h.csigma_fam (Cont.const zeroI) projT_natI_zeroI)

/-! ## Reflexivity -/

/-- **Positive**: `refl 0` is an element of `Id ℕ 0 0`. -/
theorem refl_zero_typed : projT (ident natI zeroI zeroI) (refl zeroI) = refl zeroI :=
  semTyped_refl projT_natI_zeroI (le_refl _) (le_refl _)

/-- **Negative**: `refl 0` is not an element of `Id ℕ 0 1`: the endpoints must be above
the point. -/
theorem refl_zero_not_typed_zero_one :
    projT (ident natI zeroI oneI) (refl zeroI) ≠ refl zeroI := by
  intro h
  have hmem := mem_refl_arg (I := zeroI) zeroI_mem_zero
  rw [← h] at hmem
  exact reflTag_not_mem oneI_not_mem_zero hmem

/-! ## The eliminator read at the reflexivity point -/

/-- **Positive**: `J ℕ 0 (λ y p. ℕ) 0 0 (refl 0)` denotes `0`. -/
theorem jAligned_closed :
    appSpine (jAlignedConst rd ()) [natI, zeroI, natMotive, zeroI, zeroI, refl zeroI] = zeroI := by
  have spine := natMotive_spine projT_natI_zeroI refl_zero_mem
  refine jAlignedConst_linear rd () ⟨rfl, spine⟩ ⟨natI, ?_⟩
  exact dom_instPi_jType ((spineTyped_append (args := [natI, zeroI, natMotive, zeroI, zeroI])
    (args' := [refl zeroI])).1 spine).1

/-- The spine facts at `J ℕ 0 (λ y p. Id ℕ y y) (refl 0) 0 (refl ⊥)`. -/
theorem unaligned_spine :
    SpineTyped (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot] :=
  (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨natI_type,
    (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_natI_zeroI,
      (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_projT _ _,
        (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨by
            show projT (app (app idMotive zeroI) (refl zeroI)) (refl zeroI) = refl zeroI
            rw [app_app_idMotive, projT_natI_zeroI]
            exact refl_zero_mem,
          (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨projT_natI_zeroI,
            (spineTyped_cinterp_pi rd _ _ _ _ _).2 ⟨refl_bot_mem _ _ _, trivial⟩⟩⟩⟩⟩⟩

theorem unaligned_prefix :
    SpineTyped (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI] :=
  ((spineTyped_append (args := [natI, zeroI, idMotive, refl zeroI, zeroI])
    (args' := [refl bot])).1 unaligned_spine).1

/-- The instantiated type at `J ℕ 0 (λ y p. Id ℕ y y) (refl 0) 0 (refl ⊥)` is
`Id ℕ 0 0`. -/
theorem unaligned_type :
    instPi (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot] =
      ident natI zeroI zeroI := by
  rw [instPi_jType unaligned_spine, app_app_idMotive, projT_natI_zeroI]

/-- **The path's parameter type** at `J ℕ 0 (λ y p. Id ℕ y y) (refl 0) 0 (refl ⊥)` is not
an identity type between `⊥` and itself. -/
theorem no_refl_fact :
    ¬ ∃ T, dom .pi (instPi (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI]) =
      ident T bot bot := by
  rintro ⟨T, hT⟩
  rw [dom_instPi_jType unaligned_prefix] at hT
  have e := (ident_endpoints_eq hT).1
  exact bot_not_mem_tag Kind.zero (e ▸ zeroI_mem_zero)

/-- **Negative: the refl fact is needed.** At `J ℕ 0 (λ y p. Id ℕ y y) (refl 0) 0 (refl ⊥)`
the arguments have spine facts and the method `refl 0` is an element of the
instantiated type `Id ℕ 0 0`, but there is no refl fact; the eliminator of
`Eliminators` denotes the method there, and the eliminator read at the reflexivity
point does not. -/
theorem refl_fact_needed :
    SpineTyped (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot] ∧
      projT (instPi (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot])
        (refl zeroI) = refl zeroI ∧
      (¬ ∃ T, dom .pi (instPi (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI]) =
        ident T bot bot) ∧
      appSpine (jConst rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot] = refl zeroI ∧
      appSpine (jAlignedConst rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot] ≠
        refl zeroI := by
  have right : projT (instPi (jTypeI rd ()) [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot])
      (refl zeroI) = refl zeroI := by
    rw [unaligned_type]
    exact refl_zero_mem
  refine ⟨unaligned_spine, right, no_refl_fact, jConst_linear rd () ⟨rfl, unaligned_spine⟩ right,
    fun h => ?_⟩
  have e := appSpine_churchConst jAlignedRaw (churchTele_cinterp rd (jTypeC ()) Env.nil)
    (Nat.le_refl _) unaligned_spine
  rw [appSpine_jAlignedRaw, whenTag_of_mem (refl_mem_tag bot), reflPoint_refl,
    app_app_idMotive] at e
  have hmem := mem_refl_arg (I := zeroI) zeroI_mem_zero
  rw [← h] at hmem
  change (appSpine (projT (jTypeI rd ()) jAlignedRaw)
    [natI, zeroI, idMotive, refl zeroI, zeroI, refl bot]).Mem _ at hmem
  rw [e] at hmem
  exact reflTag_not_mem (fun hz => bot_not_mem_tag .zero (projT_le _ _ _ hz))
    (projT_le _ _ _ hmem)

end ChurchLawsControls
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
