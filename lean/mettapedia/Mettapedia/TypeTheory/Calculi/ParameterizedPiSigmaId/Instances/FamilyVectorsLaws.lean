import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyExpressionsLaws

/-!
# The laws of the family pack hold for vectors

For vectors over a type `A : U0` in the concrete setting of `FamilyExamples`, in every
context, the hypotheses of the family pack's laws hold (`vecView_rigid`, `vecView_per`,
`vecView_congr`, `vecView_recExt`), so reducible equality of vectors is symmetric and
transitive and its ends are reducible (`vec_eqTm_symm`, `vec_eqTm_trans`, `vec_eqTm_ends`).

The value fields of an extension have the packs of `num` and of the parameter `A`, which here
is any type: its pack is the pack the concrete reading gives to it, a simple inductive pack
or the pack of a neutral type. `RecursiveExt` has content: the tail of an extension sits at
the index given by the extension's own length field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace FamilyVectorsLaws

open Families FamilyExamples FamilyExpressionsLaws

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- Vectors over `A` read in the concrete setting. -/
abbrev vecView (Γ : Ctx Tower.Head n) (A : Tm Tower.Head n) : FamilyAt Tower.Head n :=
  FamilyVectors.view setting Γ u0 (typePack Γ) A

/-! ## The packs the reading gives are symmetric and transitive -/

theorem neutral_symm {T a b : Tm Tower.Head n} (h : (neutralPack setting Γ T).eqTm a b) :
    (neutralPack setting Γ T).eqTm b a := by
  obtain ⟨nf, nf', r, r', n₁, n₂, c⟩ := h
  exact ⟨nf', nf, r', r, n₂, n₁, laws.convNe_symm c⟩

theorem neutral_trans {T a b c : Tm Tower.Head n} (h : (neutralPack setting Γ T).eqTm a b)
    (h' : (neutralPack setting Γ T).eqTm b c) : (neutralPack setting Γ T).eqTm a c := by
  obtain ⟨nf, nf', r, r', n₁, n₂, conv⟩ := h
  obtain ⟨mf, mf', q, q', m₁, m₂, conv'⟩ := h'
  have same := RedTm.unique r' q (n₂.whnf setting.shape) (m₁.whnf setting.shape)
  subst same
  exact ⟨nf, mf', r, q', n₁, m₂, laws.convNe_trans conv conv'⟩

theorem neutral_ends {T a b : Tm Tower.Head n} (h : (neutralPack setting Γ T).eqTm a b) :
    (neutralPack setting Γ T).redTm a ∧ (neutralPack setting Γ T).redTm b := by
  obtain ⟨nf, nf', r, r', n₁, n₂, c⟩ := h
  exact ⟨⟨nf, r, n₁, laws.convNe_trans c (laws.convNe_symm c)⟩,
    ⟨nf', r', n₂, laws.convNe_trans (laws.convNe_symm c) c⟩⟩

/-- The three kinds of packs the concrete reading gives to a type. -/
theorem typePack_cases (T : Tm Tower.Head n) :
    typePack Γ T = indPack setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields ∨
      typePack Γ T = indPack setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields ∨
      typePack Γ T = neutralPack setting Γ T := by
  unfold typePack
  split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

theorem typePack_symm (T : Tm Tower.Head n) {a b : Tm Tower.Head n}
    (h : (typePack Γ T).eqTm a b) : (typePack Γ T).eqTm b a := by
  rcases typePack_cases (Γ := Γ) T with e | e | e <;> rw [e] at h ⊢
  · exact num_symm h
  · exact ty_symm h
  · exact neutral_symm h

theorem typePack_trans (T : Tm Tower.Head n) {a b c : Tm Tower.Head n}
    (h : (typePack Γ T).eqTm a b) (h' : (typePack Γ T).eqTm b c) : (typePack Γ T).eqTm a c := by
  rcases typePack_cases (Γ := Γ) T with e | e | e <;> rw [e] at h h' ⊢
  · exact num_trans h h'
  · exact ty_trans h h'
  · exact neutral_trans h h'

theorem typePack_ends (T : Tm Tower.Head n) {a b : Tm Tower.Head n}
    (h : (typePack Γ T).eqTm a b) : (typePack Γ T).redTm a ∧ (typePack Γ T).redTm b := by
  rcases typePack_cases (Γ := Γ) T with e | e | e <;> rw [e] at h ⊢
  · exact IndEqTm.ends laws (fun closed => absurd closed numCtors_noClosed) h
  · exact IndEqTm.ends laws (fun closed => absurd closed tyCtors_noClosed) h
  · exact neutral_ends h

/-- The value fields of vectors are numbers and elements of the parameter type. -/
theorem vecView_valuePack {A : Tm Tower.Head n} {P : Pack Tower.Head n}
    (value : IsValuePack (vecView Γ A) P) : ∃ T, P = typePack Γ T := by
  obtain ⟨c, mem, field⟩ := value
  rcases FamilyVectors.ctor_cases mem with rfl | rfl
  · exact nomatch field
  · rcases List.mem_cons.mp field with h | h
    · cases h
      exact ⟨_, rfl⟩
    rcases List.mem_cons.mp h with h | h
    · cases h
      exact ⟨_, rfl⟩
    · obtain h := List.mem_singleton.mp h
      cases h

/-! ## The hypotheses of the laws -/

theorem vecView_rigid {A : Tm Tower.Head n} : FormsRigid setting (vecView Γ A) :=
  FamilyDecl.view_rigid vecDecl_declared

theorem vecView_per {A : Tm Tower.Head n} : IndexPER (vecView Γ A) where
  symm := by
    intro P mem a b h
    obtain rfl := List.mem_singleton.mp mem
    exact typePack_symm _ h
  trans := by
    intro P mem a b c h h'
    obtain rfl := List.mem_singleton.mp mem
    exact typePack_trans _ h h'

/-- The family's type respects reducible equality of lengths, for a parameter that is a type
of `U0`. -/
theorem vecView_congr {A : Tm Tower.Head n} (typed : Typed rules Γ A (.head u0)) :
    TypeCongr setting Γ (vecView Γ A) := by
  intro is is' agree
  cases agree with
  | cons head tail =>
      cases tail
      have equal := indEq_equal head
      have applied : Typed rules Γ (.app (.const FamilyVectors.vec) A)
          (.pi (.const FamilyExpressions.num) (.head u0)) := .appElim vec_typed typed
      exact ⟨u0, u0_universe, Derivable.appCong (Derivable.refl applied) equal⟩

theorem vecView_recExt {A : Tm Tower.Head n} : RecursiveExt setting Γ (vecView Γ A) := by
  intro c fs fs' mem fields idx recMem
  rcases FamilyVectors.ctor_cases mem with rfl | rfl
  · exact nomatch recMem
  · cases fields with
    | value head tail =>
        cases tail with
        | value _ tail =>
            cases tail with
            | recursive _ tail =>
                cases tail
                rcases List.mem_cons.mp recMem with h | h
                · cases h
                rcases List.mem_cons.mp h with h | h
                · cases h
                · obtain h := List.mem_singleton.mp h
                  cases h
                  exact .cons head .nil

/-! ## The laws -/

/-- **Reducible equality of vectors is symmetric**, at every length. -/
theorem vec_eqTm_symm {A : Tm Tower.Head n} (typed : Typed rules Γ A (.head u0))
    {is : List (Tm Tower.Head n)} {t t' : Tm Tower.Head n}
    (h : FamEqTm setting Γ (vecView Γ A) is t t') : FamEqTm setting Γ (vecView Γ A) is t' t :=
  FamEqTm.symm laws vecView_per (vecView_congr typed) vecView_recExt
    (fun value _ _ h => by
      obtain ⟨T, rfl⟩ := vecView_valuePack value
      exact typePack_symm T h) h

/-- **Reducible equality of vectors is transitive**, at every length. -/
theorem vec_eqTm_trans {A : Tm Tower.Head n} (typed : Typed rules Γ A (.head u0))
    {is : List (Tm Tower.Head n)} {t t' t'' : Tm Tower.Head n}
    (h : FamEqTm setting Γ (vecView Γ A) is t t') (h' : FamEqTm setting Γ (vecView Γ A) is t' t'') :
    FamEqTm setting Γ (vecView Γ A) is t t'' :=
  FamEqTm.trans laws vecView_rigid vecView_per (vecView_congr typed) vecView_recExt
    (fun value _ _ _ h h' => by
      obtain ⟨T, rfl⟩ := vecView_valuePack value
      exact typePack_trans T h h') h h'

/-- **The ends of a reducible equality of vectors are reducible.** -/
theorem vec_eqTm_ends {A : Tm Tower.Head n} (typed : Typed rules Γ A (.head u0))
    {is : List (Tm Tower.Head n)} {t t' : Tm Tower.Head n}
    (h : FamEqTm setting Γ (vecView Γ A) is t t') :
    FamRedTm setting Γ (vecView Γ A) is t ∧ FamRedTm setting Γ (vecView Γ A) is t' :=
  FamEqTm.ends laws vecView_per (vecView_congr typed) vecView_recExt
    (fun value _ _ h => by
      obtain ⟨T, rfl⟩ := vecView_valuePack value
      exact typePack_ends T h) h

end FamilyVectorsLaws
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
