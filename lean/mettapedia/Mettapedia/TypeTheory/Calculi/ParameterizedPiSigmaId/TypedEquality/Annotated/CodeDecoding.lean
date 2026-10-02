import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationCodes

/-!
# Decoding quantified codes in the domain

The quantifier constant over a carrier `A` (`Ideal.allConst A`) sends a code-valued
family `f` to the code of the dependent function type over `A` whose value at `x` is
the code `f x` (`Ideal.app_allConst`), a type when `A` is (`Ideal.typeGenerated_allCode`).

**The decoding of a quantified code is valid** at every type-generated carrier, with no
hypothesis on the family (`Ideal.decode_allConst`): `holds (all@A f)` denotes the
dependent function type over `A` whose value at `x` is `holds (f x)`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Domain
namespace Ideal

/-- The code of the dependent function type over `A` with the codes of `g` as values,
continuous in the family. -/
theorem cont_allCode (A : Ideal) : Cont fun g => cpi A fun x => projT codesIdeal (app g x) := by
  have h : EnvCont fun ρ : Env 1 => former .pi A fun X =>
      projT codesIdeal (app (Env.cons (projT A (principal X)) ρ 1)
        (Env.cons (projT A (principal X)) ρ 0)) :=
    EnvCont.cformer (B := fun ρ' : Env 2 => projT codesIdeal (app (ρ' 1) (ρ' 0))) .pi
      (EnvCont.const A)
      (EnvCont.comp (cont_projT codesIdeal)
        (EnvCont.comp₂ cont₂_app (EnvCont.var 1) (EnvCont.var 0)))
  exact h.cons_left Env.nil

/-- The quantifier's function applied to a family. -/
theorem app_allRaw (A g : Ideal) : app (allRaw A) g = cpi A fun x => projT codesIdeal (app g x) :=
  app_lam_principal (cont_allCode A) g

/-- The code of the dependent function type over a type-generated carrier with the
codes of a family as values is type-generated. -/
theorem typeGenerated_allCode {A : Ideal} (hA : TypeGenerated A) (f : Ideal) :
    TypeGenerated (cpi A fun x => projT codesIdeal (app f x)) :=
  typeGenerated_cpi ((cont_projT codesIdeal).comp (cont₂_app.right f)) hA
    fun _ _ => typeGenerated_projT_codes _

/-- **The quantifier applied to a family** over a type-generated carrier is the code
of the dependent function type over the carrier with the family's codes as values. -/
theorem app_allConst {A : Ideal} (hA : TypeGenerated A) (f : Ideal) :
    app (allConst A) f = cpi A fun x => projT codesIdeal (app f x) := by
  have hF : Cont fun _ : Ideal => codesIdeal := Cont.const codesIdeal
  have inner : (cpi A fun x => projT codesIdeal
      (app (projT (cpi A fun _ => codesIdeal) f) x)) = cpi A fun x => projT codesIdeal (app f x) :=
    cpi_ext fun y hy => by rw [app_projT_cpi hF, projT_projT, hy]
  rw [allConst, app_projT_cpi hF, app_allRaw, inner]
  exact projT_codes_eq_self_iff.2 (typeGenerated_allCode hA f)

/-- The decoder is the identity on types. -/
theorem app_holdsConst_of_typeGenerated {c : Ideal} (hc : TypeGenerated c) :
    app holdsConst c = c := by
  rw [app_holdsConst, projT_codes_eq_self_iff.2 hc, projT_univ_eq_self_iff.2 hc]

/-- The decoder of a code: the code's projection onto the universe of codes. -/
theorem app_holdsConst_eq (c : Ideal) : app holdsConst c = projT codesIdeal c := by
  rw [app_holdsConst, projT_univ_eq_self_iff.2 (typeGenerated_projT_codes c)]

/-- **The decoding of a quantified code is valid** at every type-generated carrier:
`holds (all@A f)` denotes `Π (x : A). holds (f x)`. -/
theorem decode_allConst {A : Ideal} (hA : TypeGenerated A) (f : Ideal) :
    app holdsConst (app (allConst A) f) = cpi A fun x => app holdsConst (app f x) := by
  rw [app_allConst hA f, app_holdsConst_of_typeGenerated (typeGenerated_allCode hA f)]
  exact cpi_ext fun y _ => (app_holdsConst_eq _).symm

end Ideal
end Domain
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
