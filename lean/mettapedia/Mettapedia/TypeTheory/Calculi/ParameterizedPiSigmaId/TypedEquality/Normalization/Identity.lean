import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Pairs

/-!
# Validity of identity types

An identity type over a reducible type between two reducible terms is
reducible at the same level, with the type's pack as its carrier pack. From
this: validity of identity-type formation, of reflexivity, and of their
congruences. The eliminator is a declared constant and is not treated here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

section Identity

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- An identity type over a reducible type is reducible at the same level. -/
theorem LogRel.ident {l : L} {n : Nat} {Δ : Ctx Head n} {ty lhs rhs : Tm Head n} {P : Pack Head n}
    (reducible : LogRel S l Δ ty P) (hl : P.redTm lhs) (hr : P.redTm rhs) :
    LogRel S l Δ (.id ty lhs rhs) (idPack S Δ ty lhs rhs P) := by
  have e := LR.escape laws reducible
  obtain ⟨u, hu, tty⟩ := e.type
  obtain ⟨tl, cl⟩ := e.redTm hl
  obtain ⟨tr, cr⟩ := e.redTm hr
  have reflexive := LogRel.reflexive S l reducible
  have per := LR.eqTm_per laws reducible
  exact LR.ident (RedTy.refl ⟨u, hu, .idForm tty hu tl tr⟩) (laws.convTy_id e.refl cl cr) P
    reducible hl hr (reflexive.eqTm hl) (reflexive.eqTm hr) per.1 per.2

/-- The pack of an identity type over a reducible type. -/
theorem Reducible.ident {n : Nat} {Δ : Ctx Head n} {ty lhs rhs : Tm Head n} {P : Pack Head n}
    (reducible : Reducible S Δ ty P) (hl : P.redTm lhs) (hr : P.redTm rhs) :
    Reducible S Δ (.id ty lhs rhs) (idPack S Δ ty lhs rhs P) := by
  obtain ⟨l, r⟩ := reducible
  exact ⟨l, r.ident laws hl hr⟩

/-- Identity types with reducibly equal parts are reducibly equal. -/
theorem idPack_eqTy {n : Nat} {Δ : Ctx Head n} {ty ty' lhs lhs' rhs rhs' : Tm Head n}
    {P P' : Pack Head n} (reducible : Reducible S Δ ty P) (reducible' : Reducible S Δ ty' P')
    (hl' : P'.redTm lhs') (hr' : P'.redTm rhs')
    (eqTy : P.eqTy ty') (eqL : P.eqTm lhs lhs') (eqR : P.eqTm rhs rhs') :
    (idPack S Δ ty lhs rhs P).eqTy (.id ty' lhs' rhs') := by
  have e := reducible.escape laws
  have formed := ((reducible'.ident laws hl' hr').escape laws).type
  exact ⟨ty', lhs', rhs', RedTy.refl formed,
    laws.convTy_id (e.eqTy eqTy) (e.eqTm eqL) (e.eqTm eqR), eqTy, eqL, eqR⟩

/-- Reflexivity proofs at reducibly equal subjects are reducibly equal. -/
theorem idPack_refl_eqTm {n : Nat} {Δ : Ctx Head n} {ty lhs rhs x x' : Tm Head n}
    {P : Pack Head n} (reducible : Reducible S Δ ty P)
    (hlx : P.eqTm lhs x) (hlx' : P.eqTm lhs x') (hrx : P.eqTm rhs x) (hrx' : P.eqTm rhs x')
    (hxx : P.eqTm x x') (typing' : Typed S.R Δ (.refl x') (.id ty lhs rhs)) :
    (idPack S Δ ty lhs rhs P).eqTm (.refl x) (.refl x') := by
  have e := reducible.escape laws
  obtain ⟨_, hx⟩ := reducible.eqTm_redTm laws hlx
  obtain ⟨_, hx'⟩ := reducible.eqTm_redTm laws hlx'
  have tx := (e.redTm hx).1
  have tx' := (e.redTm hx').1
  have typeEq : TypeEq S.R Δ (.id ty x x) (.id ty lhs rhs) :=
    laws.convTy_sound (laws.convTy_id e.refl (e.eqTm (reducible.eqTm_symm laws hlx))
      (e.eqTm (reducible.eqTm_symm laws hrx)))
  have typing : Typed S.R Δ (.refl x) (.id ty lhs rhs) := Typed.convType (.reflIntro tx) typeEq
  exact ⟨.refl x, .refl x', RedTm.refl typing, RedTm.refl typing',
    laws.convTm_conv (laws.convTm_refl (e.eqTm hxx)) typeEq,
    .inl ⟨x, x', rfl, rfl, tx, tx', hlx, hlx', hrx, hrx'⟩⟩

/-- Identity types between valid terms of a valid type are valid types. -/
theorem ValidTy.ident {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    (validA : ValidTy S Γ A) (valida : ValidTm S Γ a A) (validb : ValidTm S Γ b A) :
    ValidTy S Γ (.id A a b) := by
  refine ⟨fun {m Δ σ} vσ => ?_, fun {m Δ σ σ'} vσ vσ' e Q r => ?_⟩
  · obtain ⟨P, rP⟩ := validA.red vσ
    exact ⟨_, rP.ident laws (valida.red vσ rP) (validb.red vσ rP)⟩
  · obtain ⟨P, rP⟩ := validA.red vσ
    obtain ⟨P', rP'⟩ := validA.red vσ'
    have rId := rP.ident laws (valida.red vσ rP) (validb.red vσ rP)
    rw [r.unique laws rId]
    exact idPack_eqTy laws rP rP' (valida.red vσ' rP') (validb.red vσ' rP')
      (validA.ext vσ vσ' e rP)
      (valida.ext vσ vσ' e rP) (validb.ext vσ vσ' e rP)

/-- Identity types between validly equal terms are validly equal types. -/
theorem ValidTy.ident_eq {n : Nat} {Γ : Ctx Head n} {A a a' b b' : Tm Head n}
    (validA : ValidTy S Γ A) (equala : ValidEq S Γ a a' A) (equalb : ValidEq S Γ b b' A) :
    ValidTyEq S Γ (.id A a b) (.id A a' b') := by
  refine ⟨validA.ident laws equala.left equalb.left, validA.ident laws equala.right equalb.right,
    fun {m Δ σ} vσ Q r => ?_⟩
  obtain ⟨P, rP⟩ := validA.red vσ
  have rId := rP.ident laws (equala.left.red vσ rP) (equalb.left.red vσ rP)
  rw [r.unique laws rId]
  exact idPack_eqTy laws rP rP (equala.right.red vσ rP) (equalb.right.red vσ rP)
    rP.reflexive.eqTy
    (equala.eq vσ rP) (equalb.eq vσ rP)

/-- Identity types related in all three parts are related in a universe. -/
theorem ValidRel.ident {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n} {u : Head}
    (validA : ValidTm S Γ A (.head u)) (validA' : ValidTm S Γ A' (.head u))
    (relA : ValidRel S Γ A A' (.head u)) (hu : S.R.isUniverse u)
    (valida : ValidTm S Γ a A) (validb : ValidTm S Γ b A) (valida' : ValidTm S Γ a' A')
    (validb' : ValidTm S Γ b' A') (rela : ValidRel S Γ a a' A) (relb : ValidRel S Γ b b' A) :
    ValidRel S Γ (.id A a b) (.id A' a' b') (.head u) := by
  intro m Δ σ σ' vσ vσ' e P r
  rw [universe_pack laws hu vσ.formed r]
  obtain ⟨tA, cA, rA⟩ := validA.universe_at laws hu vσ
  obtain ⟨tA', _, rA'⟩ := validA'.universe_at laws hu vσ'
  have ra := valida.red vσ rA.reducible
  have rb := validb.red vσ rA.reducible
  have ra' := valida'.red vσ' rA'.reducible
  have rb' := validb'.red vσ' rA'.reducible
  have eA := rA.reducible.escape laws
  have eA' := rA'.reducible.escape laws
  obtain ⟨cAA', eqTyA⟩ := relA.universe_at laws hu vσ vσ' e
  have ea := rela vσ vσ' e rA.reducible
  have eb := relb vσ vσ' e rA.reducible
  have conv := laws.convTm_id cAA' hu (eA.eqTm ea) (eA.eqTm eb)
  exact universe_equal_intro (.idForm tA hu (eA.redTm ra).1 (eA.redTm rb).1)
    (.idForm tA' hu (eA'.redTm ra').1 (eA'.redTm rb').1) (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))
    (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) conv (rA.ident laws ra rb) (rA'.ident laws ra' rb')
    (idPack_eqTy laws rA.reducible rA'.reducible ra' rb' eqTyA ea eb)

/-- Formation of identity types in a universe. -/
theorem ValidTm.ident {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head}
    (validA : ValidTm S Γ A (.head u)) (hu : S.R.isUniverse u) (valida : ValidTm S Γ a A)
    (validb : ValidTm S Γ b A) : ValidTm S Γ (.id A a b) (.head u) := by
  refine ⟨ValidTy.universe hu, fun {m Δ σ} vσ P r => ?_,
    ValidRel.ident laws validA validA validA.rel hu valida validb valida validb valida.rel
      validb.rel⟩
  rw [universe_pack laws hu vσ.formed r]
  obtain ⟨tA, cA, rA⟩ := validA.universe_at laws hu vσ
  have ra := valida.red vσ rA.reducible
  have rb := validb.red vσ rA.reducible
  have eA := rA.reducible.escape laws
  obtain ⟨ta, ca⟩ := eA.redTm ra
  obtain ⟨tb, cb⟩ := eA.redTm rb
  exact universe_member_intro (.idForm tA hu ta tb) (laws.convTm_id cA hu ca cb)
    (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (rA.ident laws ra rb)

/-- Congruence of identity types. -/
theorem ValidEq.ident {n : Nat} {Γ : Ctx Head n} {A A' a a' b b' : Tm Head n} {u : Head}
    (equalA : ValidEq S Γ A A' (.head u)) (hu : S.R.isUniverse u)
    (equala : ValidEq S Γ a a' A) (equalb : ValidEq S Γ b b' A) :
    ValidEq S Γ (.id A a b) (.id A' a' b') (.head u) := by
  have tyEq := equalA.tyEq laws hu
  have valida' := equala.right.conv laws tyEq
  have validb' := equalb.right.conv laws tyEq
  refine ⟨equalA.left.ident laws hu equala.left equalb.left,
    equalA.right.ident laws hu valida' validb', fun vσ _ r => ?_⟩
  exact ValidRel.ident laws equalA.left equalA.right (equalA.rel laws) hu equala.left
    equalb.left valida' validb' (equala.rel laws) (equalb.rel laws) vσ vσ vσ.refl r

/-- Reflexivity. -/
theorem ValidTm.refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} (valid : ValidTm S Γ a A) :
    ValidTm S Γ (.refl a) (.id A a a) := by
  have validId := valid.type.ident laws valid valid
  refine ⟨validId, fun {m Δ σ} vσ P r => ?_, fun {m Δ σ σ'} vσ vσ' e P r => ?_⟩
  · obtain ⟨Q, rQ⟩ := valid.type.red vσ
    have ha := valid.red vσ rQ
    rw [r.unique laws (rQ.ident laws ha ha)]
    have e := rQ.escape laws
    obtain ⟨ta, ca⟩ := e.redTm ha
    have hr := rQ.reflexive.eqTm ha
    exact ⟨_, RedTm.refl (.reflIntro ta), laws.convTm_refl ca,
      .inl ⟨_, rfl, ta, hr, hr⟩⟩
  · obtain ⟨Q, rQ⟩ := valid.type.red vσ
    have ha := valid.red vσ rQ
    rw [r.unique laws (rQ.ident laws ha ha)]
    have eq := valid.ext vσ vσ' e rQ
    obtain ⟨Q', rQ'⟩ := validId.red vσ'
    have typeEq : TypeEq S.R Δ (Presentation.subst σ' (.id A a a))
        (Presentation.subst σ (.id A a a)) := by
      have rId := rQ.ident laws ha ha
      have eqId := validId.ext vσ vσ' e rId
      exact (laws.convTy_sound ((rId.escape laws).eqTy eqId)).symm
    obtain ⟨Q₂, rQ₂⟩ := valid.type.red vσ'
    have ha' := valid.red vσ' rQ₂
    have ta' := ((rQ₂.escape laws).redTm ha').1
    have hr := rQ.reflexive.eqTm ha
    exact idPack_refl_eqTm laws rQ hr eq hr eq eq (Typed.convType (.reflIntro ta') typeEq)

/-- Congruence of reflexivity. -/
theorem ValidEq.refl {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (equal : ValidEq S Γ a b A) : ValidEq S Γ (.refl a) (.refl b) (.id A a a) := by
  have validA := equal.left.type
  have right := (equal.right.refl laws).conv laws
    (ValidTyEq.symm laws (validA.ident_eq laws equal equal))
  refine ⟨equal.left.refl laws, right, fun {m Δ σ} vσ P r => ?_⟩
  obtain ⟨Q, rQ⟩ := validA.red vσ
  have ha := equal.left.red vσ rQ
  rw [r.unique laws (rQ.ident laws ha ha)]
  have eq := equal.eq vσ rQ
  have hr := rQ.reflexive.eqTm ha
  have hb := equal.right.red vσ rQ
  have tb := ((rQ.escape laws).redTm hb).1
  have e := rQ.escape laws
  have typeEq : TypeEq S.R Δ (.id (Presentation.subst σ A) (Presentation.subst σ b)
      (Presentation.subst σ b)) (.id (Presentation.subst σ A) (Presentation.subst σ a)
      (Presentation.subst σ a)) :=
    laws.convTy_sound (laws.convTy_id e.refl (e.eqTm (rQ.eqTm_symm laws eq))
      (e.eqTm (rQ.eqTm_symm laws eq)))
  exact idPack_refl_eqTm laws rQ hr eq hr eq eq (Typed.convType (.reflIntro tb) typeEq)

end Identity

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
