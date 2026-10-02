import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.FormFacts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationFundamental

/-!
# The weak-head forms of annotated types, read off the relation

**Two equal types are related over the least environment** (`CTypeEq.relatedBot`): at the
identity substitution, which is related to itself over the least environment
(`SubstRel.vars`, `Fits.bot`), the fundamental lemma relates the two types as far as every
type token of the left one's denotation observes. The context's entries are adequate types
by the fundamental lemma at their formations (`CCtxFormed.ctxAdequate`).

**A type former is read off its own denotation.** The denotation of a type former carries
the former's tag in every environment: `Π`, `Σ` and identity types their tags, a universe
the tag of universes, a ground head the tag of ground types, and the numbers the tag of
numbers. At that tag the relation reduces both types to the former, with judgmentally equal
components; a type that takes no head step is then the former itself
(`CTypeEq.formersMatch_of_normal`, `CTypeEq.inductive_of_normal`).

**Neutral types.** A type whose erasure is neutral takes no head step
(`HeadReduction.NeutralNormal`), and every weak-head form is normal
(`normal_of_typeForm`). So a neutral type equal to a type former is that former, which it is
not: the separation is read off the former's side of the equation, never off the neutral
side, whose denotation over the least environment may observe nothing
(`CTypeEq.neutral_not_former_sub`, `CTypeEq.neutral_not_inductive_sub`). Two neutral types
match with no further condition.

**The facts** (`CTypeEq.formsMatch_sub`, `CFormFacts.of_constAdequate`): equal types in
weak-head form match, for every equation derivable in a sub-package whose declared constants
are adequate; with every constant adequate, the facts hold for the package.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Impredicative.Domain
open Normalization (LevelModel Roles Neutral IsTypeForm Field)
open UniverseLevel (LevelOrder)

variable {Head : Type} {R : Rules Head}

/-! ## Conditions on the package -/

section Conditions

variable {P : ChurchRules R} {K : RigidTypes P}

/-- **Neutral types are normal**: a term whose erasure is neutral takes no head step. -/
def HeadReduction.NeutralNormal (H : HeadReduction P K) (roles : Roles Head) : Prop :=
  ∀ {n : Nat} {A : CTm Head n}, Neutral roles A.erase → H.Normal A

/-- **The inductive types are the numbers**: the type constant of every inductive type is
the rigid type of numbers, read with the tag of numbers. -/
def RigidTypes.InductiveNumbers (K : RigidTypes P) (roles : Roles Head) (Rd : Reading Head) :
    Prop :=
  ∀ {T : DeclName} {ctors : List (DeclName × List (Field Head))}, roles T = .inductive ctors →
    T = K.num ∧ (Rd.const T).Mem (.tag .nat)

end Conditions

/-! ## Weak-head forms are normal -/

section Normal

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {roles : Roles Head}

/-- **Every weak-head form of a type is normal**: type formers and the numbers by the
reduction's normal forms, neutral types by the condition. -/
theorem normal_of_typeForm (neutral : H.NeutralNormal roles)
    (inductives : K.InductiveNumbers roles Rd) {n : Nat} {A : CTm Head n}
    (form : IsTypeForm roles A.erase) : H.Normal A := by
  rcases typeForm_erase_cases form with former | ⟨T, ctors, role, rfl⟩ | hA
  · cases former with
    | head h => exact H.normal_head h
    | pi D E => exact H.normal_pi D E
    | sigma D E => exact H.normal_sigma D E
    | id C a b => exact H.normal_id C a b
  · rw [(inductives role).1]
    exact H.normal_num
  · exact neutral hA

end Normal

/-! ## Contexts formed in a sub-package -/

/-- A context formed in a sub-package is formed in the package. -/
theorem CCtxFormed.mono {R' : Rules Head} {Q : ChurchRules R'} {P : ChurchRules R}
    (sub : ChurchRulesSub Q P) {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed Q Γ) :
    CCtxFormed P Γ := by
  induction formed with
  | nil => exact .nil
  | snoc _ typeA ih =>
      obtain ⟨u, hu, typing⟩ := typeA
      exact .snoc ih ⟨u, sub.isUniverse hu, typing.mono sub⟩

/-! ## The forms -/

section Forms

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L] (levels : LevelModel R L) (valid : ReadingValid Rd P)
  (heads : K.GroundHeads Rd) (ground : GroundHeadEq R) (stuck : H.DecoderStuckAtUniverses)
  {R' : Rules Head} {Q : ChurchRules R'} (sub : ChurchRulesSub Q P)
  (consts : ∀ {c : DeclName} {D : CTm Head 0}, Q.constantType c = some D →
    ConstAdequateAt Rd H c)

include levels valid heads ground stuck sub consts in
/-- **A context formed in the sub-package is adequate**: every entry is an adequate type
over the entries before it, by the fundamental lemma at its formation. -/
theorem CCtxFormed.ctxAdequate {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed Q Γ) :
    CtxAdequate Rd H Γ := by
  induction formed with
  | nil => trivial
  | snoc formedΓ typeA ih =>
      obtain ⟨u, hu, typing⟩ := typeA
      have v := CDerivable.valid_sub levels valid heads ground stuck sub consts typing
        (CCtxFormed.mono sub formedΓ)
      exact ⟨ih, Adequate.adequateType levels valid.soundnessFacts (sub.isUniverse hu) v.1⟩

include levels valid heads ground stuck sub consts in
/-- **Two equal types are related over the least environment**: an equation of types
derivable in the sub-package over a context formed there relates the two types, at the
identity substitution, as far as every type token of the left type's denotation over the
least environment observes. -/
theorem CTypeEq.relatedBot {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}
    (equal : CTypeEq Q Γ A B) (formed : CCtxFormed Q Γ) {r : Tok}
    (hr : (cinterp Rd A fun _ => Ideal.bot).Mem r) (hrU : TyTok Elem.univ r) :
    RT H Γ false r A A B := by
  obtain ⟨u, hu, e⟩ := equal
  have sound := valid.soundnessFacts
  have formedP := CCtxFormed.mono sub formed
  have hu' := sub.isUniverse hu
  have v := CDerivable.valid_sub levels valid heads ground stuck sub consts e formedP
  have fits := Fits.bot sound formedP
  have hσ := SubstRel.vars (formed.ctxAdequate levels valid heads ground stuck sub consts) fits
    formedP (ξ := idRen) fun i => (CTm.rename_id _).symm
  have h := v.1.2.2 _ fits formedP hσ r hr (sound.typedAt_head hu' _ hrU)
  simp only [CTm.subst_var_comp, CTm.rename_id] at h
  exact RT.toType (typeKind_of_tyTok_univ hrU) (CRedTy.refl (CIsType.head_of_universe levels hu')) h

/-- A type tag is a type token. -/
theorem tyTok_univ_tag {k : Kind} (hk : k.IsFormer) : TyTok Elem.univ (.tag k) :=
  (tyTok_tag_former hk).2 Elem.isUniv_univ

include levels valid heads ground stuck sub consts in
/-- **A type former is read off its own denotation**: a type former equal to a type that
takes no head step, by an equation derivable in the sub-package over a context formed there,
matches it as a type former. -/
theorem CTypeEq.formersMatch_of_normal {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}
    (equal : CTypeEq Q Γ A B) (formed : CCtxFormed Q Γ) (former : CFormer A)
    (normal : H.Normal B) : CFormersMatch P Γ A B := by
  have rel : ∀ {r : Tok}, (cinterp Rd A fun _ => Ideal.bot).Mem r → TyTok Elem.univ r →
      RT H Γ false r A A B := fun hr hrU =>
    equal.relatedBot levels valid heads ground stuck sub consts formed hr hrU
  cases former with
  | head h =>
      obtain ⟨u, hu, e⟩ := equal
      have tA : CTyped P Γ (.head h) (.head u) :=
        (CEqual.typed levels (e.mono sub) (CCtxFormed.mono sub formed)).1
      obtain ⟨u', htyping, -⟩ := CDerivable.generation tA
      rcases heads htyping with hh | ⟨read, _⟩
      · have mem : (cinterp Rd (.head h : CTm Head n) fun _ => Ideal.bot).Mem (.tag .univ) := by
          show (Ideal.principal (Rd.head h)).Mem _
          rw [valid.universes hh]
          exact Ideal.mem_principal_tag.2 rfl
        obtain ⟨h₀, h', hA, hB, -, -, same⟩ := RT.ty_univ_iff.1 (rel mem (tyTok_univ_tag trivial))
        have e₁ := H.red_normal (H.normal_head h) hA.1
        have e₂ := H.red_normal normal hB.1
        injection e₁ with _ e₁
        subst e₁ e₂
        exact .inl ⟨h₀, h', rfl, rfl, same⟩
      · have mem : (cinterp Rd (.head h : CTm Head n) fun _ => Ideal.bot).Mem (.tag .ground) := by
          show (Ideal.principal (Rd.head h)).Mem _
          rw [read]
          exact Ideal.mem_principal_tag.2 rfl
        obtain ⟨g, -, hA, hB⟩ := RT.ty_ground_iff.1 (rel mem (tyTok_univ_tag trivial))
        have e₁ := H.red_normal (H.normal_head h) hA.1
        subst e₁
        have e₂ := H.red_normal normal hB.1
        subst e₂
        exact .inl ⟨h, h, rfl, rfl, .inl rfl⟩
  | pi D E =>
      obtain ⟨D₀, E₀, D', E', hp⟩ :=
        RT.ty_pi_iff.1 (rel (Ideal.mem_former_tag _ _ _) (tyTok_univ_tag trivial))
      have e₁ := H.red_normal (H.normal_pi D E) hp.1.1
      injection e₁ with _ eD eE
      subst eD eE
      have e₂ := H.red_normal normal hp.2.1.1
      subst e₂
      exact .inr (.inl ⟨D₀, E₀, D', E', rfl, rfl, hp.2.2.1, hp.2.2.2⟩)
  | sigma D E =>
      obtain ⟨D₀, E₀, D', E', hp⟩ :=
        RT.ty_sigma_iff.1 (rel (Ideal.mem_former_tag _ _ _) (tyTok_univ_tag trivial))
      have e₁ := H.red_normal (H.normal_sigma D E) hp.1.1
      injection e₁ with _ eD eE
      subst eD eE
      have e₂ := H.red_normal normal hp.2.1.1
      subst e₂
      exact .inr (.inr (.inl ⟨D₀, E₀, D', E', rfl, rfl, hp.2.2.1, hp.2.2.2⟩))
  | id C a b =>
      obtain ⟨C₀, a₀, b₀, C', a', b', hp⟩ :=
        RT.ty_ident_iff.1 (rel (Ideal.subset_closure (.inl rfl)) (tyTok_univ_tag trivial))
      have e₁ := H.red_normal (H.normal_id C a b) hp.1.1
      injection e₁ with _ eC ea eb
      subst eC ea eb
      have e₂ := H.red_normal normal hp.2.1.1
      subst e₂
      exact .inr (.inr (.inr ⟨C₀, a₀, b₀, C', a', b', rfl, rfl, hp.2.2.1, hp.2.2.2.1,
        hp.2.2.2.2⟩))

include levels valid heads ground stuck sub consts in
/-- **The type constant of an inductive type is read off its own denotation**: equal to a
type that takes no head step, it is that type. -/
theorem CTypeEq.inductive_of_normal {roles : Roles Head} (inductives : K.InductiveNumbers roles Rd)
    {n : Nat} {Γ : CCtx Head n} {T : DeclName} {ctors : List (DeclName × List (Field Head))}
    {B : CTm Head n} (equal : CTypeEq Q Γ (.const T) B) (formed : CCtxFormed Q Γ)
    (role : roles T = .inductive ctors) (normal : H.Normal B) : B = .const T := by
  obtain ⟨hT, mem⟩ := inductives role
  obtain ⟨-, hB⟩ := RT.ty_nat_iff.1
    (equal.relatedBot levels valid heads ground stuck sub consts formed mem (tyTok_univ_tag trivial))
  rw [← H.red_normal normal hB.1, hT]

include levels valid heads ground stuck sub consts in
/-- **A neutral type is equal to no type former**, by an equation derivable in the
sub-package over a context formed there. The former's tag relates the two types, and the
neutral type, which takes no head step, would be the former. -/
theorem CTypeEq.neutral_not_former_sub {roles : Roles Head} (neutral : H.NeutralNormal roles)
    {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n} (equal : CTypeEq Q Γ A B)
    (formed : CCtxFormed Q Γ) (hA : Neutral roles A.erase) (former : CFormer B) : False :=
  (equal.symm.formersMatch_of_normal levels valid heads ground stuck sub consts formed former
    (neutral hA)).right.not_neutral hA

include levels valid heads ground stuck sub consts in
/-- **A neutral type is equal to no type constant of an inductive type**, by an equation
derivable in the sub-package over a context formed there. -/
theorem CTypeEq.neutral_not_inductive_sub {roles : Roles Head} (neutral : H.NeutralNormal roles)
    (inductives : K.InductiveNumbers roles Rd) {n : Nat} {Γ : CCtx Head n} {A : CTm Head n}
    {T : DeclName} {ctors : List (DeclName × List (Field Head))} (equal : CTypeEq Q Γ A (.const T))
    (formed : CCtxFormed Q Γ) (hA : Neutral roles A.erase) (role : roles T = .inductive ctors) :
    False :=
  hA.ne_inductive role (congrArg CTm.erase
    (equal.symm.inductive_of_normal levels valid heads ground stuck sub consts inductives formed
      role (neutral hA)))

include levels valid heads ground stuck sub consts in
/-- **Equal types in weak-head form match**, for every equation derivable in a sub-package
whose declared constants are adequate, over a context formed there. A type former or the
numbers are read off their own side; a neutral type is matched from the other side, which is
neutral too. -/
theorem CTypeEq.formsMatch_sub {roles : Roles Head} (neutral : H.NeutralNormal roles)
    (inductives : K.InductiveNumbers roles Rd) {n : Nat} {Γ : CCtx Head n} {A B : CTm Head n}
    (equal : CTypeEq Q Γ A B) (formed : CCtxFormed Q Γ) (formA : IsTypeForm roles A.erase)
    (formB : IsTypeForm roles B.erase) : CFormsMatch P roles Γ A B := by
  have nB := normal_of_typeForm neutral inductives formB
  rcases typeForm_erase_cases formA with former | ⟨T, ctors, role, rfl⟩ | hA
  · exact .inl (equal.formersMatch_of_normal levels valid heads ground stuck sub consts formed
      former nB)
  · exact .inr (.inl ⟨T, ctors, role, rfl, equal.inductive_of_normal levels valid heads ground
      stuck sub consts inductives formed role nB⟩)
  · rcases typeForm_erase_cases formB with former | ⟨T, ctors, role, rfl⟩ | hB
    · exact (equal.neutral_not_former_sub levels valid heads ground stuck sub consts neutral formed
        hA former).elim
    · exact (equal.neutral_not_inductive_sub levels valid heads ground stuck sub consts neutral
        inductives formed hA role).elim
    · exact .inr (.inr ⟨hA, hB⟩)

end Forms

/-! ## The facts -/

section Facts

variable {Rd : Reading Head} {P : ChurchRules R} {K : RigidTypes P} {H : HeadReduction P K}
  {L : Type} [LevelOrder L]

/-- **The facts about the weak-head forms of types, from the relation**: for a valid
reading, rigid ground heads, head equality trivial on them, the decoder stuck at universes,
neutral types normal and the numbers the only inductive type, if every declared constant is
adequate then equal types of a formed context in weak-head form match. -/
theorem CFormFacts.of_constAdequate {roles : Roles Head} (levels : LevelModel R L)
    (valid : ReadingValid Rd P) (heads : K.GroundHeads Rd) (ground : GroundHeadEq R)
    (stuck : H.DecoderStuckAtUniverses) (neutral : H.NeutralNormal roles)
    (inductives : K.InductiveNumbers roles Rd) (consts : ConstAdequate Rd H) :
    CFormFacts P roles where
  forms equal formed formA formB :=
    CTypeEq.formsMatch_sub levels valid heads ground stuck (Q := P) (ChurchRulesSub.refl P)
      (fun _ => consts) neutral inductives equal formed formA formB

end Facts

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
