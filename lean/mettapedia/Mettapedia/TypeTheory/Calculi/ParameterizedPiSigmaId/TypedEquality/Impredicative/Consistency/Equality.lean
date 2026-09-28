import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Formation

/-!
# Equality, conversion and inclusion in the consistency model

Validly equal terms of a type form a partial equivalence. A valid term is equal
to itself, and equality is symmetric and transitive because the denotation of
a type is a partial equivalence and related substitutions relate the instances
of a valid term.

Equal terms of a universe are types with one denotation, so terms and
equalities move along them. Inclusion of denotations holds between equal types
of a universe and between cumulative universes, composes, and is preserved by
dependent function types with equal domains and by dependent pair types; terms
and equalities move along it.

An identity type between equal terms relates all terms. Every term is then a
proof of it and any two proofs are equal; in particular reflexivity proofs are
valid, and reflexivity proofs of equal terms are equal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Equality is a partial equivalence -/

/-- A valid term is validly equal to itself. -/
theorem ValidEq.refl {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} (valid : ValidTm M Γ a A) :
    ValidEq M Γ a a A :=
  ⟨valid, valid, valid.2⟩

/-- Valid equality is symmetric. -/
theorem ValidEq.symm (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEq M Γ a b A) : ValidEq M Γ b a A := by
  obtain ⟨valid₁, valid₂, rel⟩ := eq
  refine ⟨valid₂, valid₁, fun {_ _ _ _} e {R} den => ?_⟩
  obtain ⟨-, rel₁⟩ := valid₁
  obtain ⟨-, rel₂⟩ := valid₂
  exact den.trans laws (den.trans laws (rel₂ e den) (den.symm laws (rel e den))) (rel₁ e den)

/-- Valid equality is transitive. -/
theorem ValidEq.trans (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {a b c A : Tm Head n}
    (eq₁ : ValidEq M Γ a b A) (eq₂ : ValidEq M Γ b c A) : ValidEq M Γ a c A := by
  obtain ⟨valid₁, valid₂, rel₁⟩ := eq₁
  obtain ⟨-, valid₃, rel₂⟩ := eq₂
  refine ⟨valid₁, valid₃, fun {_ _ _ _} e {R} den => ?_⟩
  obtain ⟨-, rel⟩ := valid₂
  exact den.trans laws (den.trans laws (rel₁ e den) (den.symm laws (rel e den))) (rel₂ e den)

/-! ## Conversion -/

/-- Equal types of a universe have one denotation under the first of two
related substitutions. -/
theorem ValidEq.den_left (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {u : Head} (eq : ValidEq M Γ A B (.head u)) (hu : M.rules.isUniverse u) {m : Nat}
    {ξ : World M.reading m} {σ σ' : Sub Head n m} (e : EqSubst M Γ ξ σ σ') :
    ∃ R, Den M ξ (Presentation.subst σ A) R ∧ Den M ξ (Presentation.subst σ B) R := by
  obtain ⟨R, denA, denB'⟩ := ValidEq.den eq hu e
  obtain ⟨R', denB, denB''⟩ := ValidTm.validTy eq.2.1 hu e
  obtain rfl := Den.deterministic laws denB' denB''
  exact ⟨_, denA, denB⟩

/-- A term of a type is a term of every equal type of a universe. -/
theorem ValidTm.conv (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    {u : Head} (valid : ValidTm M Γ t A) (eq : ValidEq M Γ A B (.head u))
    (hu : M.rules.isUniverse u) : ValidTm M Γ t B := by
  obtain ⟨-, rel⟩ := valid
  refine ⟨ValidTm.validTy eq.2.1 hu, fun {_ _ _ _} e {R} den => ?_⟩
  obtain ⟨_, denA, denB⟩ := ValidEq.den_left laws eq hu e
  rw [Den.deterministic laws den denB]
  exact rel e denA

/-- Equal terms of a type are equal terms of every equal type of a universe. -/
theorem ValidEq.conv (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    {u : Head} (valid : ValidEq M Γ a b A) (eq : ValidEq M Γ A B (.head u))
    (hu : M.rules.isUniverse u) : ValidEq M Γ a b B := by
  obtain ⟨valid₁, valid₂, rel⟩ := valid
  refine ⟨ValidTm.conv laws valid₁ eq hu, ValidTm.conv laws valid₂ eq hu,
    fun {_ _ _ _} e {R} den => ?_⟩
  obtain ⟨_, denA, denB⟩ := ValidEq.den_left laws eq hu e
  rw [Den.deterministic laws den denB]
  exact rel e denA

/-! ## Inclusion -/

/-- Equal types of a universe are validly below one another. -/
theorem ValidLe.ofEq (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    {u : Head} (eq : ValidEq M Γ A B (.head u)) (hu : M.rules.isUniverse u) :
    ValidLe M Γ A B := by
  refine ⟨ValidTm.validTy eq.1 hu, ValidTm.validTy eq.2.1 hu,
    fun {_ _ _ _} e {R R'} den den' {_ _} h => ?_⟩
  obtain ⟨_, denA, denB⟩ := ValidEq.den_left laws eq hu e
  rw [Den.deterministic laws den denA] at h
  rw [Den.deterministic laws den' denB]
  exact h

/-- A universe is validly below every universe it is cumulative into. -/
theorem ValidLe.univ (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {u v : Head}
    (cumulative : M.rules.cumulative u v) : ValidLe M Γ (.head u) (.head v) := by
  obtain ⟨hu, hv, le⟩ := M.levels.cumulative_universe cumulative
  refine ⟨ValidTy.sort hu, ValidTy.sort hv, fun {_ _ _ _} _ {R R'} den den' {_ _} h => ?_⟩
  rw [Den.sort_inv laws hu den] at h
  rw [Den.sort_inv laws hv den']
  exact universeAt.mono le h

/-- A term of a type is a term of every type validly above it. -/
theorem ValidTm.below {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n}
    (valid : ValidTm M Γ t A) (le : ValidLe M Γ A B) : ValidTm M Γ t B := by
  obtain ⟨-, rel⟩ := valid
  obtain ⟨validA, validB, incl⟩ := le
  refine ⟨validB, fun {_ _ _ _} e {R'} den' => ?_⟩
  obtain ⟨R, den, -⟩ := validA e
  exact incl e den den' (rel e den)

/-- Equal terms of a type are equal terms of every type validly above it. -/
theorem ValidEq.below {n : Nat} {Γ : Ctx Head n} {a b A B : Tm Head n}
    (valid : ValidEq M Γ a b A) (le : ValidLe M Γ A B) : ValidEq M Γ a b B := by
  obtain ⟨valid₁, valid₂, rel⟩ := valid
  refine ⟨ValidTm.below valid₁ le, ValidTm.below valid₂ le, fun {_ _ _ _} e {R'} den' => ?_⟩
  obtain ⟨validA, -, incl⟩ := le
  obtain ⟨R, den, -⟩ := validA e
  exact incl e den den' (rel e den)

/-- Valid inclusion is transitive. -/
theorem ValidLe.trans {n : Nat} {Γ : Ctx Head n} {A B C : Tm Head n}
    (le₁ : ValidLe M Γ A B) (le₂ : ValidLe M Γ B C) : ValidLe M Γ A C := by
  obtain ⟨validA, validB, incl₁⟩ := le₁
  obtain ⟨-, validC, incl₂⟩ := le₂
  refine ⟨validA, validC, fun {_ _ _ _} e {R R''} den den'' {_ _} h => ?_⟩
  obtain ⟨R', den', -⟩ := validB e
  exact incl₂ e den' den'' (incl₁ e den den' h)

/-- A dependent function type is validly below another with an equal domain of a
universe and a codomain validly above its own. -/
theorem ValidLe.pi (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} {w : Head} (validPi : ValidTy M Γ (.pi A B))
    (validPi' : ValidTy M Γ (.pi A' B')) (eqA : ValidEq M Γ A A' (.head w))
    (hw : M.rules.isUniverse w) (leB : ValidLe M (.snoc Γ A) B B') :
    ValidLe M Γ (.pi A B) (.pi A' B') := by
  obtain ⟨-, -, inclB⟩ := leB
  refine ⟨validPi, validPi', fun {_ _ σ σ'} e {R R'} den den' {f g} h => ?_⟩
  obtain ⟨l, interp⟩ := den
  obtain ⟨l', interp'⟩ := den'
  obtain ⟨P, rfl, domI, codI, -⟩ := InterpAt.pi_inv laws interp
  obtain ⟨P', rfl, domI', codI', -⟩ := InterpAt.pi_inv laws interp'
  intro _ _ ρ mor a b ha' hab'
  have eρ := EqSubst.rename laws e mor
  have denA := domI mor
  have denA' := domI' mor
  rw [rename_subst] at denA denA'
  obtain ⟨D, denD, denD'⟩ := ValidEq.den_left laws eqA hw eρ
  have dom : P'.dom mor = P.dom mor :=
    (Den.deterministic laws ⟨l', denA'⟩ denD').trans
      (Den.deterministic laws ⟨l, denA⟩ denD).symm
  have ha : P.dom mor a a := by
    rw [← dom]
    exact ha'
  have hab : P.dom mor a b := by
    rw [← dom]
    exact hab'
  have codB := codI mor ha
  have codB' := codI' mor ha'
  rw [inst0_rename_subst_liftSub] at codB codB'
  exact inclB (EqSubst.cons eρ ⟨l, denA⟩ ha) ⟨l, codB⟩ ⟨l', codB'⟩ (h mor ha hab)

/-- A dependent pair type is validly below another whose domain and codomain are
validly above its own. -/
theorem ValidLe.sigma (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A A' : Tm Head n}
    {B B' : Tm Head (n + 1)} (validS : ValidTy M Γ (.sigma A B))
    (validS' : ValidTy M Γ (.sigma A' B')) (leA : ValidLe M Γ A A')
    (leB : ValidLe M (.snoc Γ A) B B') : ValidLe M Γ (.sigma A B) (.sigma A' B') := by
  obtain ⟨-, -, inclA⟩ := leA
  obtain ⟨-, -, inclB⟩ := leB
  refine ⟨validS, validS', fun {_ ξ σ σ'} e {R R'} den den' {p q} h => ?_⟩
  obtain ⟨l, interp⟩ := den
  obtain ⟨l', interp'⟩ := den'
  obtain ⟨P, rfl, domI, codI, -⟩ := InterpAt.sigma_inv laws interp
  obtain ⟨P', rfl, domI', codI', -⟩ := InterpAt.sigma_inv laws interp'
  obtain ⟨hp, hpq, hc⟩ := h
  have denA := domI (Morph.id ξ)
  have denA' := domI' (Morph.id ξ)
  rw [rename_id] at denA denA'
  have hp' := inclA e ⟨l, denA⟩ ⟨l', denA'⟩ hp
  have codB := codI (Morph.id ξ) hp
  have codB' := codI' (Morph.id ξ) hp'
  rw [liftRen_id, rename_id, inst0_subst_liftSub] at codB codB'
  exact ⟨hp', inclA e ⟨l, denA⟩ ⟨l', denA'⟩ hpq,
    inclB (EqSubst.cons e ⟨l, denA⟩ hp) ⟨l, codB⟩ ⟨l', codB'⟩ hc⟩

/-! ## Identity types -/

/-- An identity type whose endpoints are related in the denotation of its
carrier denotes the relation that relates all terms exactly when the endpoints
are related. -/
theorem Den.ident {n : Nat} {ξ : World M.reading n} {A a b : Tm Head n} {R : Rel Head n}
    (den : Den M ξ A R) (ha : R a a) (hb : R b b) :
    Den M ξ (.id A a b) (fun _ _ => R a b) := by
  obtain ⟨l, interp⟩ := den
  exact ⟨l, Interp.ident .refl R interp ha hb⟩

/-- An identity type between valid terms of a type is a valid type. -/
theorem ValidTy.ident (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    (valid₁ : ValidTm M Γ a A) (valid₂ : ValidTm M Γ b A) : ValidTy M Γ (.id A a b) := by
  obtain ⟨validA, rel₁⟩ := valid₁
  obtain ⟨-, rel₂⟩ := valid₂
  intro m _ σ σ' e
  obtain ⟨R, den, den'⟩ := validA e
  have ha := rel₁ e den
  have hb := rel₂ e den
  have same : (fun _ _ : Tm Head m => R (Presentation.subst σ' a) (Presentation.subst σ' b)) =
      fun _ _ => R (Presentation.subst σ a) (Presentation.subst σ b) := by
    funext _ _
    exact propext ⟨fun h => den.trans laws (den.trans laws ha h) (den.symm laws hb),
      fun h => den.trans laws (den.trans laws (den.symm laws ha) h) hb⟩
  refine ⟨_, Den.ident den (den.refl_left laws ha) (den.refl_left laws hb), ?_⟩
  rw [← same]
  exact Den.ident den' (den.refl_right laws ha) (den.refl_right laws hb)

/-- Under related substitutions, an identity type between equal terms relates
all terms. -/
theorem ValidEq.ident_rel (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEq M Γ a b A) {m : Nat} {ξ : World M.reading m} {σ σ' : Sub Head n m}
    (e : EqSubst M Γ ξ σ σ') {R : Rel Head m}
    (den : Den M ξ (Presentation.subst σ (.id A a b)) R) (t u : Tm Head m) : R t u := by
  obtain ⟨-, ⟨-, rel₂⟩, rel⟩ := eq
  obtain ⟨l, interp⟩ := den
  obtain ⟨RA, rfl, interpA, -, -⟩ := InterpAt.id_inv laws interp
  have denA : Den M ξ (Presentation.subst σ A) RA := ⟨l, interpA⟩
  exact denA.trans laws (rel e denA) (denA.symm laws (rel₂ e denA))

/-- Any two terms are validly equal proofs of an identity between equal terms. -/
theorem ValidEq.ident_irrelevant (laws : M.Laws) {n : Nat} {Γ : Ctx Head n}
    {a b A : Tm Head n} (eq : ValidEq M Γ a b A) (t u : Tm Head n) :
    ValidEq M Γ t u (.id A a b) := by
  have validId : ValidTy M Γ (.id A a b) := ValidTy.ident laws eq.1 eq.2.1
  exact ⟨⟨validId, fun {_ _ _ _} e {_} den => ValidEq.ident_rel laws eq e den _ _⟩,
    ⟨validId, fun {_ _ _ _} e {_} den => ValidEq.ident_rel laws eq e den _ _⟩,
    fun {_ _ _ _} e {_} den => ValidEq.ident_rel laws eq e den _ _⟩

/-- Reflexivity proves the identity of a valid term with itself. -/
theorem ValidTm.refl (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n}
    (valid : ValidTm M Γ a A) : ValidTm M Γ (.refl a) (.id A a a) :=
  (ValidEq.ident_irrelevant laws (ValidEq.refl valid) (.refl a) (.refl a)).1

/-- Reflexivity proofs of equal terms are equal. -/
theorem ValidEq.reflCong (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (eq : ValidEq M Γ a b A) : ValidEq M Γ (.refl a) (.refl b) (.id A a a) :=
  ValidEq.ident_irrelevant laws (ValidEq.refl eq.1) (.refl a) (.refl b)

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
