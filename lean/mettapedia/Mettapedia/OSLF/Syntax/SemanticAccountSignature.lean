import Mettapedia.OSLF.Syntax.SignatureMorphismMetas
import Mettapedia.OSLF.Syntax.BindingEquationFamilyModel

/-!
# A semantic account operator over a full binding signature

The original signature is included without changing its sorts, operations or
binding arities. One additional nonbinding operator marks a selected wrapped
sort with a signature value. Its equations belong to a separate semantic
presentation: they do not identify literal signatures in a runtime language.

Substitution still carries the entire mixed environment beneath every original
binder. This construction supplies a semantic presentation, not a language
transformer or an operational account implementation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SemanticAccountSignature

variable {S : Signature}

abbrev declarations (signatureSort wrappedSort : S.Srt) : List (MetaArity S) :=
  [([signatureSort, wrappedSort], wrappedSort)]

abbrev signature (S : Signature) (signatureSort wrappedSort : S.Srt) : Signature :=
  withMetas S (declarations signatureSort wrappedSort)

abbrev inclusion (signatureSort wrappedSort : S.Srt) :
    SigMor S (signature S signatureSort wrappedSort) :=
  metaInclusion S (declarations signatureSort wrappedSort)

def embedOriginal {signatureSort wrappedSort : S.Srt} {Γ : Ctx S} {sort : S.Srt}
    (value : Term S Γ sort) : Term (signature S signatureSort wrappedSort) Γ sort :=
  embed value

theorem embedOriginal_injective {signatureSort wrappedSort : S.Srt} {Γ : Ctx S}
    {sort : S.Srt} {first second : Term S Γ sort} :
    embedOriginal (signatureSort := signatureSort) (wrappedSort := wrappedSort) first =
      embedOriginal second → first = second := by
  apply embed_injective
  intro position
  obtain ⟨index, bounded⟩ := position
  have zero : index = 0 := by simpa only [declarations, List.length_singleton,
    Nat.lt_one_iff] using bounded
  subst index
  exact .var (.succ .zero)

def mark {signatureSort wrappedSort : S.Srt} {Γ : Ctx S}
    (account : Term (signature S signatureSort wrappedSort) Γ signatureSort)
    (value : Term (signature S signatureSort wrappedSort) Γ wrappedSort) :
    Term (signature S signatureSort wrappedSort) Γ wrappedSort :=
  .op (.inr (.mk ⟨0, by simp [declarations]⟩)) (.cons account (.cons value .nil))

theorem bind_mark {signatureSort wrappedSort : S.Srt} {Γ Δ : Ctx S}
    (environment : Sub (signature S signatureSort wrappedSort) Γ Δ)
    (account : Term (signature S signatureSort wrappedSort) Γ signatureSort)
    (value : Term (signature S signatureSort wrappedSort) Γ wrappedSort) :
    bind environment (mark account value) =
      mark (bind environment account) (bind environment value) := rfl

theorem rename_mark {signatureSort wrappedSort : S.Srt} {Γ Δ : Ctx S}
    (rho : Ren (signature S signatureSort wrappedSort) Γ Δ)
    (account : Term (signature S signatureSort wrappedSort) Γ signatureSort)
    (value : Term (signature S signatureSort wrappedSort) Γ wrappedSort) :
    rename rho (mark account value) =
      mark (rename rho account) (rename rho value) := rfl

/-- Existing operations and their exact typing profiles. No equation law is
assumed in this data. -/
structure Apparatus (S : Signature) (signatureSort baseSort wrappedSort : S.Srt) where
  unit : S.Op signatureSort
  unitArity : S.arity unit = []
  product : S.Op signatureSort
  productArity : S.arity product = [([], signatureSort), ([], signatureSort)]
  signed : S.Op wrappedSort
  signedArity : S.arity signed = [([], baseSort), ([], signatureSort)]

variable {signatureSort baseSort wrappedSort : S.Srt}

def unit (apparatus : Apparatus S signatureSort baseSort wrappedSort) {Γ : Ctx S} :
    Term (signature S signatureSort wrappedSort) Γ signatureSort :=
  .op (.inl apparatus.unit) (castArgsArity (T := signature S signatureSort wrappedSort) apparatus.unitArity.symm .nil)

def product (apparatus : Apparatus S signatureSort baseSort wrappedSort) {Γ : Ctx S}
    (first second : Term (signature S signatureSort wrappedSort) Γ signatureSort) :
    Term (signature S signatureSort wrappedSort) Γ signatureSort :=
  .op (.inl apparatus.product)
    (castArgsArity (T := signature S signatureSort wrappedSort) apparatus.productArity.symm (.cons first (.cons second .nil)))

def signed (apparatus : Apparatus S signatureSort baseSort wrappedSort) {Γ : Ctx S}
    (account : Term (signature S signatureSort wrappedSort) Γ signatureSort)
    (value : Term (signature S signatureSort wrappedSort) Γ baseSort) :
    Term (signature S signatureSort wrappedSort) Γ wrappedSort :=
  .op (.inl apparatus.signed)
    (castArgsArity (T := signature S signatureSort wrappedSort) apparatus.signedArity.symm
      (.cons value (.cons account .nil)))

def equation {Γ : Ctx S} {sort : S.Srt}
    (left right : Term (signature S signatureSort wrappedSort) Γ sort) :
    EqAxiom (signature S signatureSort wrappedSort) [] where
  ctx := Γ
  sort := sort
  lhs := embed left
  rhs := embed right

def markUnit (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    EqAxiom (signature S signatureSort wrappedSort) [] :=
  equation (Γ := [wrappedSort]) (mark (unit apparatus) (.var .zero)) (.var .zero)

def markProduct (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    EqAxiom (signature S signatureSort wrappedSort) [] :=
  equation (Γ := [signatureSort, signatureSort, wrappedSort])
    (mark (product apparatus (.var .zero) (.var (.succ .zero)))
      (.var (.succ (.succ .zero))))
    (mark (.var .zero) (mark (.var (.succ .zero)) (.var (.succ (.succ .zero)))))

def signedAccount (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    EqAxiom (signature S signatureSort wrappedSort) [] :=
  equation (Γ := [signatureSort, baseSort])
    (signed apparatus (.var .zero) (.var (.succ .zero)))
    (mark (.var .zero) (signed apparatus (unit apparatus) (.var (.succ .zero))))

def unitLeft (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    EqAxiom (signature S signatureSort wrappedSort) [] :=
  equation (Γ := [signatureSort]) (product apparatus (unit apparatus) (.var .zero))
    (.var .zero)

def unitRight (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    EqAxiom (signature S signatureSort wrappedSort) [] :=
  equation (Γ := [signatureSort]) (product apparatus (.var .zero) (unit apparatus))
    (.var .zero)

def productAssociative (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    EqAxiom (signature S signatureSort wrappedSort) [] :=
  equation (Γ := [signatureSort, signatureSort, signatureSort])
    (product apparatus (product apparatus (.var .zero) (.var (.succ .zero)))
      (.var (.succ (.succ .zero))))
    (product apparatus (.var .zero)
      (product apparatus (.var (.succ .zero)) (.var (.succ (.succ .zero)))))

/-- The account equations are declared only in this semantic presentation. -/
def laws (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    List (EqAxiom (signature S signatureSort wrappedSort) []) :=
  [markUnit apparatus, markProduct apparatus, signedAccount apparatus,
    unitLeft apparatus, unitRight apparatus, productAssociative apparatus]

def mapEquation (value : EqAxiom S []) :
    EqAxiom (signature S signatureSort wrappedSort) [] :=
  (inclusion signatureSort wrappedSort).mapEqAxiom value

/-- The original sorted family and the additional semantic account laws are
kept as distinct generators. No unsorted raw-pattern equivalence is used. -/
def family (original : EqAxiom S [] → Prop)
    (apparatus : Apparatus S signatureSort baseSort wrappedSort)
    (value : EqAxiom (signature S signatureSort wrappedSort) []) : Prop :=
  (∃ source, original source ∧ value = mapEquation source) ∨ value ∈ laws apparatus

noncomputable abbrev algebra (original : EqAxiom S [] → Prop)
    (apparatus : Apparatus S signatureSort baseSort wrappedSort) :=
  BindingEquationFamilyModel.algebra (family original apparatus)

/-- Arbitrary contextual values satisfy the entire chosen semantic family;
the proof uses the existing full-environment equation quotient. -/
theorem full_contextual_satisfaction (original : EqAxiom S [] → Prop)
    (apparatus : Apparatus S signatureSort baseSort wrappedSort) :
    BindingEquationFamilyModel.Satisfies (algebra original apparatus)
      (family original apparatus) :=
  BindingEquationFamilyModel.algebra_satisfies _

end Mettapedia.OSLF.Binding.SemanticAccountSignature
