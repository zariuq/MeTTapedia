import Mettapedia.Logic.HOL.TypeSubstitutionCompositionSemantics

/-!
# Model-level coherence of standard-domain type reducts

The ambient interpretation of a substituted simple type is propositionally
equal to its interpretation under substituted carriers. The canonical carrier
equivalence is the cast along this equality, not an arbitrary equivalence.
This strengthens sentence-level coherence for these particular reducts without
identifying isomorphic models in general.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v v' v'' w z

variable {Base Base' Base'' : Type u}

namespace Ty

/-- Simple-type interpretation commutes with substitution as an equality of
ambient carrier types. This is structural recursion, not univalence. -/
theorem denote_substitute (σ : Base → Ty Base')
    (Carrier : Base' → Type (max (u + 1) w)) (a : Ty Base) :
    denote (fun b => denote Carrier (σ b)) a = denote Carrier (substitute σ a) := by
  induction a with
  | prop => rfl
  | base _ => rfl
  | arr a b iha ihb =>
      exact congrArg₂ (fun A B : Type (max (u + 1) w) => A → B) iha ihb

private theorem arrowCongr_cast {A B A' B' : Type z}
    (hA : A = A') (hB : B = B') :
    Equiv.arrowCongr (Equiv.cast hA) (Equiv.cast hB) =
      Equiv.cast (congrArg₂ (fun A B : Type z => A → B) hA hB) := by
  cases hA
  cases hB
  rfl

/-- The canonical substitution equivalence transports along the structural
carrier equality; it does not choose a permutation of its values. -/
theorem denoteSubstituteEquiv_eq_cast (σ : Base → Ty Base')
    (Carrier : Base' → Type (max (u + 1) w)) (a : Ty Base) :
    denoteSubstituteEquiv σ Carrier a = Equiv.cast (denote_substitute σ Carrier a) := by
  induction a with
  | prop => rfl
  | base _ => rfl
  | arr a b iha ihb =>
      simp only [denoteSubstituteEquiv, iha, ihb]
      exact arrowCongr_cast _ _

theorem denoteSubstituteEquiv_apply_heq (σ : Base → Ty Base')
    (Carrier : Base' → Type (max (u + 1) w)) (a : Ty Base)
    (x : denote (fun b => denote Carrier (σ b)) a) :
    HEq (denoteSubstituteEquiv σ Carrier a x) x := by
  rw [denoteSubstituteEquiv_eq_cast]
  exact cast_heq _ _

theorem denoteSubstituteEquiv_symm_apply_heq (σ : Base → Ty Base')
    (Carrier : Base' → Type (max (u + 1) w)) (a : Ty Base)
    (x : denote Carrier (substitute σ a)) :
    HEq ((denoteSubstituteEquiv σ Carrier a).symm x) x := by
  rw [denoteSubstituteEquiv_eq_cast]
  exact cast_heq _ _

end Ty

namespace HenkinModel

variable {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}
  {Const'' : Ty Base'' → Type v''}

/-- Premodel data determine a Henkin model; closure witnesses are propositions. -/
theorem ext_data {M N : HenkinModel.{u, v, w} Base Const}
    (carriers : M.Carrier = N.Carrier) (domains : HEq M.adm N.adm)
    (constants : HEq @M.constDen @N.constDen) : M = N := by
  cases M with
  | mk mp mt =>
      cases N with
      | mk np nt =>
          congr
          cases mp
          cases np
          cases carriers
          cases eq_of_heq domains
          cases eq_of_heq constants
          rfl

/-- Standard models agree when their carrier and constant data agree. -/
theorem standard_ext
    {C D : Base → Type (max (u + 1) w)}
    {f : ∀ {a}, Const a → Ty.denote C a}
    {g : ∀ {a}, Const a → Ty.denote D a}
    (carriers : C = D) (constants : ∀ {a} (c : Const a), HEq (f c) (g c)) :
    standard C f = standard D g := by
  cases carriers
  congr
  funext a c
  exact eq_of_heq (constants c)

theorem standard_eq_of_fullDomains (M : HenkinModel.{u, v, w} Base Const)
    (full : M.FullDomains) : standard M.Carrier M.constDen = M := by
  apply ext_data (M := standard M.Carrier M.constDen) (N := M) rfl
  · apply heq_of_eq
    funext a x
    exact propext ⟨fun _ => full a x, fun _ => True.intro⟩
  · rfl

/-- Full domains characterize literal equality with standardization. This
does not claim that sentence equivalence characterizes full domains. -/
theorem standard_eq_iff_fullDomains (M : HenkinModel.{u, v, w} Base Const) :
    standard M.Carrier M.constDen = M ↔ M.FullDomains := by
  constructor
  · intro equal
    rw [← equal]
    exact fullDomains_standard _ _
  · exact standard_eq_of_fullDomains M

/-- The identity type reduct is precisely standardization, as model data. -/
theorem standardTypeReduct_id (M : HenkinModel.{u, v, w} Base Const) :
    standardTypeReduct (Const' := Const) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ c) M =
      standard M.Carrier M.constDen := by
  apply standard_ext rfl
  intro a c
  refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
  congr 1 <;> simp

/-- Successive standard-domain type reducts agree as complete model data,
including carriers and constants. No fullness of the original target is
needed for this composition law. -/
theorem standardTypeReduct_comp
    (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    (first : ∀ {a}, Const a → Const' (Ty.substitute σ a))
    (second : ∀ {a}, Const' a → Const'' (Ty.substitute τ a))
    (M : HenkinModel.{u, v'', w} Base'' Const'') :
    standardTypeReduct σ first (standardTypeReduct τ second M) =
      standardTypeReduct (fun b => Ty.substitute τ (σ b))
        (composeTypeConstants σ τ first second) M := by
  apply standard_ext
  · funext b
    exact Ty.denote_substitute τ M.Carrier (σ b)
  · intro a c
    refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
    refine (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).trans ?_
    refine HEq.trans ?_ (Ty.denoteSubstituteEquiv_symm_apply_heq _ _ _ _).symm
    congr 1 <;> simp [composeTypeConstants, Ty.substitute_comp]

end HenkinModel

#print axioms Ty.denoteSubstituteEquiv_eq_cast
#print axioms HenkinModel.standardTypeReduct_id
#print axioms HenkinModel.standardTypeReduct_comp

end Mettapedia.Logic.HOL
