import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.FamilyExamples

/-!
# The laws of the family pack hold for typed expressions

The laws of the family pack (`Families.Laws`) take as hypotheses the rigidity of constructor
forms, the symmetry and transitivity of the index packs, that the family's type respects
reducible equality of indices (`TypeCongr`), and that reducibly equal fields give reducibly
equal indices to recursive fields (`RecursiveExt`). For typed expressions in the concrete
setting of `FamilyExamples`, in every context, all of them hold (`expView_rigid`,
`expView_per`, `expView_congr`, `expView_recExt`), so reducible equality of expressions is
symmetric and transitive and its ends are reducible (`exp_eqTm_symm`, `exp_eqTm_trans`,
`exp_eqTm_ends`).

`RecursiveExt` has content here: the branches of a conditional sit at the index given by the
conditional's own type field, so reducibly equal conditionals compare their branches at
reducibly equal, possibly different, indices.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace FamilyExpressionsLaws

open Families FamilyExamples

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- Expressions read in the concrete setting. -/
abbrev expView (Γ : Ctx Tower.Head n) : FamilyAt Tower.Head n :=
  FamilyExpressions.view setting Γ u0 (typePack Γ)

/-! ## Reducible equality at the simple index types -/

theorem tyCtors_noClosed {F : Tm Tower.Head 0} :
    ¬ IsClosedField (FamilyExpressions.tyCtors (Head := Tower.Head)) F := by
  rintro ⟨k, fields, mem, closed⟩
  rcases List.mem_cons.mp mem with h | h
  · cases (Prod.mk.inj h).2
    exact nomatch closed
  · cases (Prod.mk.inj (List.mem_singleton.mp h)).2
    exact nomatch closed

theorem numCtors_noClosed {F : Tm Tower.Head 0} :
    ¬ IsClosedField (FamilyVectors.numCtors (Head := Tower.Head)) F := by
  rintro ⟨k, fields, mem, closed⟩
  rcases List.mem_cons.mp mem with h | h
  · cases (Prod.mk.inj h).2
    exact nomatch closed
  · cases (Prod.mk.inj (List.mem_singleton.mp h)).2
    rcases List.mem_singleton.mp closed with h'
    cases h'

theorem ty_symm {a b : Tm Tower.Head n}
    (h : IndEqTm setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields a b) :
    IndEqTm setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields b a :=
  IndEqTm.symm laws (fun closed => absurd closed tyCtors_noClosed) h

theorem ty_trans {a b c : Tm Tower.Head n}
    (h : IndEqTm setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields a b)
    (h' : IndEqTm setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields b c) :
    IndEqTm setting Γ FamilyExpressions.ty FamilyExpressions.tyCtors noFields a c :=
  IndEqTm.trans laws
    (show setting.roles FamilyExpressions.ty = .inductive FamilyExpressions.tyCtors from roles_ty)
    (fun closed => absurd closed tyCtors_noClosed) h h'

theorem num_symm {a b : Tm Tower.Head n}
    (h : IndEqTm setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields a b) :
    IndEqTm setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields b a :=
  IndEqTm.symm laws (fun closed => absurd closed numCtors_noClosed) h

theorem num_trans {a b c : Tm Tower.Head n}
    (h : IndEqTm setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields a b)
    (h' : IndEqTm setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields b c) :
    IndEqTm setting Γ FamilyExpressions.num FamilyVectors.numCtors noFields a c :=
  IndEqTm.trans laws
    (show setting.roles FamilyExpressions.num = .inductive FamilyVectors.numCtors from roles_num)
    (fun closed => absurd closed numCtors_noClosed) h h'

/-- Reducibly equal terms of a simple inductive type are equal in the typed equality. -/
theorem indEq_equal {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    {a b : Tm Tower.Head n} (h : IndEqTm setting Γ T cs noFields a b) :
    Equal rules Γ a b (.const T) := by
  obtain ⟨red, red', conv, _⟩ := h
  exact .trans red.equal (.trans conv (.symm red'.equal))

/-! ## The hypotheses of the laws -/

theorem expView_rigid : FormsRigid setting (expView Γ) :=
  FamilyDecl.view_rigid expDecl_declared

theorem expView_per : IndexPER (expView Γ) where
  symm := by
    intro P mem a b h
    obtain rfl := List.mem_singleton.mp mem
    exact ty_symm h
  trans := by
    intro P mem a b c h h'
    obtain rfl := List.mem_singleton.mp mem
    exact ty_trans h h'

theorem expView_congr : TypeCongr setting Γ (expView Γ) := by
  intro is is' agree
  cases agree with
  | cons head tail =>
      cases tail
      have equal := indEq_equal head
      have applied := Derivable.appCong (Derivable.refl (exp_typed (Γ := Γ))) equal
      exact ⟨u0, u0_universe, applied⟩

/-- `tnum` and `tbool` are reducibly equal to themselves. -/
theorem tnum_self : (typePack Γ (.const FamilyExpressions.ty)).eqTm (.const FamilyExpressions.tnum)
    (.const FamilyExpressions.tnum) :=
  nullary_self (List.mem_cons_self ..) tnum_typed

theorem tbool_self :
    (typePack Γ (.const FamilyExpressions.ty)).eqTm (.const FamilyExpressions.tbool)
      (.const FamilyExpressions.tbool) :=
  nullary_self (List.mem_cons_of_mem _ (List.mem_singleton_self _)) tbool_typed

theorem expView_recExt : RecursiveExt setting Γ (expView Γ) := by
  intro c fs fs' mem fields idx recMem
  rcases FamilyExpressions.ctor_cases mem with rfl | rfl | rfl | rfl
  · rcases List.mem_singleton.mp recMem with h
    cases h
  · rcases List.mem_cons.mp recMem with h | h
    · cases h
      exact .cons tnum_self .nil
    · obtain h := List.mem_singleton.mp h
      cases h
      exact .cons tnum_self .nil
  · cases fields with
    | value head tail =>
        cases tail with
        | recursive _ tail =>
            cases tail with
            | recursive _ tail =>
                cases tail with
                | recursive _ tail =>
                    cases tail
                    rcases List.mem_cons.mp recMem with h | h
                    · cases h
                    rcases List.mem_cons.mp h with h | h
                    · cases h
                      exact .cons tbool_self .nil
                    rcases List.mem_cons.mp h with h | h
                    · cases h
                      exact .cons head .nil
                    · obtain h := List.mem_singleton.mp h
                      cases h
                      exact .cons head .nil
  · obtain h := List.mem_singleton.mp recMem
    cases h
    exact .cons tnum_self .nil

/-- The value fields of expressions are numbers and types. -/
theorem expView_valuePack {P : Pack Tower.Head n} (value : IsValuePack (expView Γ) P) :
    P = typePack Γ (.const FamilyExpressions.num) ∨ P = typePack Γ (.const FamilyExpressions.ty) := by
  obtain ⟨c, mem, field⟩ := value
  rcases FamilyExpressions.ctor_cases mem with rfl | rfl | rfl | rfl
  · obtain h := List.mem_singleton.mp field
    cases h
    exact .inl rfl
  · rcases List.mem_cons.mp field with h | h
    · cases h
    · obtain h := List.mem_singleton.mp h
      cases h
  · rcases List.mem_cons.mp field with h | h
    · cases h
      exact .inr rfl
    rcases List.mem_cons.mp h with h | h
    · cases h
    rcases List.mem_cons.mp h with h | h
    · cases h
    · obtain h := List.mem_singleton.mp h
      cases h
  · obtain h := List.mem_singleton.mp field
    cases h

theorem expView_valueSymm {P : Pack Tower.Head n} (value : IsValuePack (expView Γ) P)
    {a b : Tm Tower.Head n} (h : P.eqTm a b) : P.eqTm b a := by
  rcases expView_valuePack value with rfl | rfl
  · exact num_symm h
  · exact ty_symm h

theorem expView_valueTrans {P : Pack Tower.Head n} (value : IsValuePack (expView Γ) P)
    {a b c : Tm Tower.Head n} (h : P.eqTm a b) (h' : P.eqTm b c) : P.eqTm a c := by
  rcases expView_valuePack value with rfl | rfl
  · exact num_trans h h'
  · exact ty_trans h h'

theorem expView_valueEnds {P : Pack Tower.Head n} (value : IsValuePack (expView Γ) P)
    {a b : Tm Tower.Head n} (h : P.eqTm a b) : P.redTm a ∧ P.redTm b := by
  rcases expView_valuePack value with rfl | rfl
  · exact IndEqTm.ends laws (fun closed => absurd closed numCtors_noClosed) h
  · exact IndEqTm.ends laws (fun closed => absurd closed tyCtors_noClosed) h

/-! ## The laws -/

/-- **Reducible equality of expressions is symmetric**, at every index. -/
theorem exp_eqTm_symm {is : List (Tm Tower.Head n)} {t t' : Tm Tower.Head n}
    (h : FamEqTm setting Γ (expView Γ) is t t') : FamEqTm setting Γ (expView Γ) is t' t :=
  FamEqTm.symm laws expView_per expView_congr expView_recExt
    (fun value _ _ h => expView_valueSymm value h) h

/-- **Reducible equality of expressions is transitive**, at every index. -/
theorem exp_eqTm_trans {is : List (Tm Tower.Head n)} {t t' t'' : Tm Tower.Head n}
    (h : FamEqTm setting Γ (expView Γ) is t t') (h' : FamEqTm setting Γ (expView Γ) is t' t'') :
    FamEqTm setting Γ (expView Γ) is t t'' :=
  FamEqTm.trans laws expView_rigid expView_per expView_congr expView_recExt
    (fun value _ _ _ h h' => expView_valueTrans value h h') h h'

/-- **The ends of a reducible equality of expressions are reducible.** -/
theorem exp_eqTm_ends {is : List (Tm Tower.Head n)} {t t' : Tm Tower.Head n}
    (h : FamEqTm setting Γ (expView Γ) is t t') :
    FamRedTm setting Γ (expView Γ) is t ∧ FamRedTm setting Γ (expView Γ) is t' :=
  FamEqTm.ends laws expView_per expView_congr expView_recExt
    (fun value _ _ h => expView_valueEnds value h) h

end FamilyExpressionsLaws
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
