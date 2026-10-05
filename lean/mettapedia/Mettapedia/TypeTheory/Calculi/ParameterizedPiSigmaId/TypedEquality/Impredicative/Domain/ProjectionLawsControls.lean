import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Domain.ProjectionLaws

/-!
# Controls for the laws of the projections

**Dependent pair types.**

* Positive: the projection of a pair is the pair of the projections, the second
  at the family's value at the projected first component (`projT_sigma_pair`);
  the pair of two zeros is its own projection onto `Σ ℕ ℕ` (`zeroPair_fixed`).
* Negative: the family's value must be taken at the *projected* first component.
  With the family that is the numbers at a first component observed to be the
  universe and the least element otherwise, the pair of the universe and zero is
  projected onto a pair whose second component loses zero, while projecting it
  onto the family's value at the unprojected first component keeps zero
  (`sigma_unprojected_family_fails`).

**Dependent function types.**

* Positive: the function that projects its argument onto `A` is its own
  projection onto `A → A` (`churchId_fixed`): a function carrying its domain is
  an element of its type.
* Negative: the identity function of the calculus without domains, which maps
  the universe to the universe, is not its own projection onto `ℕ → ℕ`
  (`curryId_not_fixed`); and the family's value must be taken at the projected
  argument (`pi_unprojected_family_fails`).

**The universe of codes.**

* Positive: a function type over types is its own projection onto the universe
  of codes, and decoding it returns it (`natToNat_code_fixed`,
  `natToNat_code_decodes`); the universe of codes is its own projection onto the
  universe (`codes_is_type`).
* Negative: zero is not a code (`zero_not_code`); a dependent function type
  whose family reads the untyped observations of its argument is not its own
  projection onto the universe of codes (`junk_code_not_fixed`), so the
  hypothesis of `Ideal.typeGenerated_former_pi` cannot be dropped.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace ProjectionControls

open Ideal

/-- The numbers, as an ideal. -/
def natI : Ideal := principal Elem.nat

/-- Zero, as an ideal. -/
def zeroI : Ideal := principal Elem.zero

theorem nat_type : Ty Elem.nat Elem.univ := Elem.ty_tag (k := .nat) trivial Elem.isUniv_univ

/-- The principal ideal of a typed compact element is its own projection. -/
theorem projT_principal_of_ty {T : Ideal} {a u : List Tok} (ha : Below a T)
    (hau : Ty a Elem.univ) (hu : Ty u a) : projT T (principal u) = principal u :=
  le_antisymm (projT_le _ _) fun _ ht =>
    ⟨u, fun s hs => ⟨ent_of_mem hs, a, ha, hau, hu s hs⟩, ht⟩

theorem zero_proj_nat : projT natI zeroI = zeroI :=
  projT_principal_of_ty (a := Elem.nat) (fun _ h => ent_of_mem h) nat_type
    (Elem.ty_zero List.mem_cons_self)

/-- The universe observed in an ideal of numbers: never. -/
theorem not_univ_typedAt_nat {k : Kind} (hk : k.IsFormer) : ¬ TypedAt natI (.tag k) := by
  rintro ⟨a, ha, -, hat⟩
  rcases (tyTok_tag_former hk).1 hat with h | h
  · exact absurd (mem_principal_tag.1 (ha _ h)) (by decide)
  · exact absurd (mem_principal_tag.1 (ha _ h)) (by decide)

/-- The projection of anything onto the numbers has no universe tag. -/
theorem univ_not_mem_projT_nat (I : Ideal) : ¬ (projT natI I).Mem (.tag .univ) :=
  fun h => not_univ_typedAt_nat (k := .univ) trivial (mem_projT_tag h).2

/-! ## Dependent pair types -/

/-- **Positive**: the projection of a pair onto a dependent pair type. -/
theorem projT_sigma_pair {A : Ideal} {F : List Tok → Ideal} (hF : Monotone F) (I J : Ideal) :
    projT (former .sigma A F) (pair I J) =
      pair (projT A I) (projT (fam .sigma (former .sigma A F) (projT A I)) J) := by
  rw [projT_sigma hF, fst_pair, snd_pair]

/-- **Positive**: the pair of two zeros is its own projection onto `Σ ℕ ℕ`. -/
theorem zeroPair_fixed :
    projT (former .sigma natI fun _ => natI) (pair zeroI zeroI) = pair zeroI zeroI := by
  rw [projT_sigma_pair (fun _ => le_refl natI), fam_former_const, zero_proj_nat]

/-- The family that is the numbers at an argument observed to be the universe,
and the least element otherwise. -/
def junkFam (X : List Tok) : Ideal := cond (hasTag .univ X) natI bot

theorem junkFam_monotone : Monotone junkFam := by
  intro X X' h
  unfold junkFam
  cases hX : hasTag .univ X
  · exact bot_le _
  · have hX' : hasTag .univ X' = true := by
      have := h _ (hasTag_iff.1 hX)
      rwa [ent_tag] at this
    rw [hX']
    exact le_refl _

theorem junkFam_univ : junkFam [.tag .univ] = natI := rfl

/-- At an argument with no universe tag, the junk family's values have no
number tag. -/
theorem nat_not_mem_fam_junk {k : Kind} {y : Ideal} (hy : ¬ y.Mem (.tag .univ)) :
    ¬ (fam k (former k natI junkFam) y).Mem (.tag .nat) := by
  intro h
  obtain ⟨Z, hZ, hm⟩ := (mem_fam_former junkFam_monotone).1 h
  unfold junkFam at hm
  cases hZu : hasTag .univ Z
  · rw [hZu] at hm
    change ent ([] : List Tok) (.tag .nat) = true at hm
    rw [ent_tag] at hm
    cases hm
  · exact hy (hZ _ (hasTag_iff.1 hZu))

theorem nat_mem_fam_junk_univ {k : Kind} :
    (fam k (former k natI junkFam) (principal Elem.univ)).Mem (.tag .nat) :=
  (mem_fam_former junkFam_monotone).2 ⟨[.tag .univ], fun _ h => ent_of_mem h,
    by rw [junkFam_univ]; exact ent_of_mem List.mem_cons_self⟩

/-- **Negative**: projecting the second component onto the family's value at the
unprojected first component is wrong. -/
theorem sigma_unprojected_family_fails :
    projT (former .sigma natI junkFam) (pair (principal Elem.univ) zeroI) ≠
      pair (projT natI (fst (pair (principal Elem.univ) zeroI)))
        (projT (fam .sigma (former .sigma natI junkFam) (fst (pair (principal Elem.univ) zeroI)))
          (snd (pair (principal Elem.univ) zeroI))) := by
  intro h
  have h' := congrArg snd h
  simp only [projT_sigma junkFam_monotone, snd_pair, fst_pair] at h'
  have keeps : (projT (fam .sigma (former .sigma natI junkFam) (principal Elem.univ)) zeroI).Mem
      (.tag .zero) := by
    refine subset_closure ⟨ent_of_mem List.mem_cons_self, Elem.nat, fun s hs => ?_, nat_type,
      tyTok_tag_zero.2 List.mem_cons_self⟩
    rw [List.mem_singleton.1 hs]
    exact nat_mem_fam_junk_univ
  rw [← h'] at keeps
  obtain ⟨-, b, hb, -, hbt⟩ := mem_projT_tag keeps
  exact nat_not_mem_fam_junk (univ_not_mem_projT_nat _) (hb _ (tyTok_tag_zero.1 hbt))

/-! ## Dependent function types -/

/-- **Positive**: the function that projects its argument onto `A` is its own
projection onto `A → A`. -/
theorem churchId_fixed (A : Ideal) : projT (former .pi A fun _ => A) (churchId A) = churchId A := by
  have e : ∀ X, piProj A (fun _ => A) (churchId A) X = projT A (principal X) := by
    intro X
    unfold piProj
    rw [fam_former_const, app_churchId, projT_projT, projT_projT]
  rw [projT_pi (fun _ => le_refl A)]
  exact congrArg lam (funext e)

/-- The identity function of the calculus without domains: its graph on all
inputs. -/
def curryId : Ideal := lam principal

theorem curryId_maps_univ : curryId.Mem (.fn .lam [] [.tag .univ] [.tag .univ]) :=
  (mem_lam_fn fun h => principal_mono h).2 fun _ h => ent_of_mem h

/-- **Negative**: the identity without a domain is not its own projection onto
`ℕ → ℕ`: it maps the universe to the universe. -/
theorem curryId_not_fixed : projT (former .pi natI fun _ => natI) curryId ≠ curryId := by
  intro h
  have hm := curryId_maps_univ
  rw [← h, projT_pi (fun _ => le_refl natI)] at hm
  have hY := (mem_lam_fn (piProj_monotone _ _ _)).1 hm _ List.mem_cons_self
  unfold piProj at hY
  rw [fam_former_const] at hY
  exact univ_not_mem_projT_nat _ hY

/-- The constant function with value zero. -/
def constZero : Ideal := lam fun _ => zeroI

theorem zero_mem_app_constZero (y : Ideal) : (app constZero y).Mem (.tag .zero) :=
  mem_app.2 ⟨[], [.tag .zero], fun _ h => absurd h List.not_mem_nil,
    (mem_lam_fn fun _ => le_refl zeroI).2 fun t ht => by
      rw [List.mem_singleton.1 ht]; exact ent_of_mem List.mem_cons_self,
    ent_of_mem List.mem_cons_self⟩

/-- **Negative**: projecting the value onto the family's value at the unprojected
argument is wrong. -/
theorem pi_unprojected_family_fails :
    projT (former .pi natI junkFam) constZero ≠
      lam fun X => projT (fam .pi (former .pi natI junkFam) (principal X))
        (app constZero (projT natI (principal X))) := by
  intro h
  have hG : Monotone fun X => projT (fam .pi (former .pi natI junkFam) (principal X))
      (app constZero (projT natI (principal X))) := by
    intro X X' hX
    exact le_trans (projT_mono_type (fam_mono (le_refl _) (principal_mono hX)) _)
      (projT_mono (app_mono (le_refl _) (projT_mono (principal_mono hX))))
  have keeps : (lam fun X => projT (fam .pi (former .pi natI junkFam) (principal X))
      (app constZero (projT natI (principal X)))).Mem
        (.fn .lam [] [.tag .univ] [.tag .zero]) := by
    refine (mem_lam_fn hG).2 fun t ht => ?_
    rw [List.mem_singleton.1 ht]
    refine subset_closure ⟨zero_mem_app_constZero _, Elem.nat, fun s hs => ?_, nat_type,
      tyTok_tag_zero.2 List.mem_cons_self⟩
    rw [List.mem_singleton.1 hs]
    exact nat_mem_fam_junk_univ
  rw [← h, projT_pi junkFam_monotone] at keeps
  have hY := (mem_lam_fn (piProj_monotone _ _ _)).1 keeps _ List.mem_cons_self
  obtain ⟨-, b, hb, -, hbt⟩ := mem_projT_tag hY
  exact nat_not_mem_fam_junk (univ_not_mem_projT_nat _) (hb _ (tyTok_tag_zero.1 hbt))

/-! ## The universe of codes -/

/-- The code of `ℕ → ℕ`. -/
def natToNatCode : Ideal := former .pi natI fun _ => natI

/-- **Positive**: a function type over types is its own projection onto the
universe of codes. -/
theorem natToNat_code_fixed : projT codesIdeal natToNatCode = natToNatCode :=
  projT_codes_eq_self_iff.2 (typeGenerated_former_const (.inl rfl)
    (typeGenerated_principal nat_type) (typeGenerated_principal nat_type))

/-- **Positive**: decoding it returns it. -/
theorem natToNat_code_decodes : app (churchId codesIdeal) natToNatCode = natToNatCode := by
  rw [app_churchId, natToNat_code_fixed]

/-- **Positive**: the universe of codes is its own projection onto the universe. -/
theorem codes_is_type : projT univIdeal codesIdeal = codesIdeal :=
  projT_univ_eq_self_iff.2 (typeGenerated_principal
    (Elem.ty_tag (k := .codes) trivial Elem.isUniv_univ))

/-- **Negative**: zero is not a code. -/
theorem zero_not_code : ¬ (projT codesIdeal zeroI).Mem (.tag .zero) := by
  intro h
  have := typedAt_codes_iff.1 (mem_projT_tag h).2
  exact absurd (tyTok_tag_zero.1 this) (by simp [Elem.univ])

/-- **Negative**: a dependent function type whose family reads the untyped
observations of its argument is not its own projection onto the universe of
codes: its entry at the universe is no code token. -/
theorem junk_code_not_fixed : projT codesIdeal (former .pi natI junkFam) ≠ former .pi natI junkFam := by
  intro h
  have hm : (former .pi natI junkFam).Mem (.fn .pi [] [.tag .univ] [.tag .nat]) :=
    (mem_former_fn junkFam_monotone).2 ⟨fun _ h => absurd h List.not_mem_nil,
      fun s hs => by rw [List.mem_singleton.1 hs, junkFam_univ]; exact ent_of_mem List.mem_cons_self⟩
  rw [← h] at hm
  obtain ⟨v, hv, hent⟩ := hm
  rw [ent_fn, Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hent
  have hnat := hent.2 _ List.mem_cons_self
  rw [ent_tag, hasTag_iff] at hnat
  obtain ⟨C, X', Y', hmem, hX', hY'⟩ := mem_fnApp'.1 hnat
  obtain ⟨hI, hty⟩ := hv _ hmem
  obtain ⟨hC, hY⟩ := (mem_former_fn junkFam_monotone).1 hI
  have hj := hY _ hY'
  unfold junkFam at hj
  cases hXu : hasTag .univ X'
  · rw [hXu] at hj
    change ent ([] : List Tok) (.tag .nat) = true at hj
    rw [ent_tag] at hj
    cases hj
  · have hunivX := hasTag_iff.1 hXu
    have htyped := (tyTok_family (.inl rfl)).1 (typedAt_codes_iff.1 hty)
    have hU := (tyTok_tag_former (k := .univ) trivial).1 (htyped.2.2.1 _ hunivX)
    rcases hU with hU | hU
    · exact absurd (mem_principal_tag.1 (hC _ hU)) (by decide)
    · exact absurd (mem_principal_tag.1 (hC _ hU)) (by decide)

end ProjectionControls
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
