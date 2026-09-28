import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Validity

/-!
# Reducible types in weak-head normal form

A reducible type that is already a dependent function, pair or identity type
has the pack of that shape, with reducible parts. The derivation cannot be of
another shape, because a weak-head normal form reduces only to itself.

The parts of a dependent function or pair type are packaged once: parts that
are reducible in every world, with the packs `packOf`, give the canonical
pack family of the type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- A weak-head normal form reduces only to itself. -/
theorem WhRed.eq_of_whnf {n : Nat} {t u : Tm Head n} (normal : Whnf S.R S.roles t)
    (red : WhRed S.R S.roles t u) : u = t := by
  cases red using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head step _ => exact absurd step (normal _)

/-! ## Function, pair and identity types -/

/-- A reducible dependent function type, with the pack family of its derivation. -/
theorem Reducible.pi_raw {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} {P : Pack Head n} (reducible : Reducible S Γ (.pi dom cod) P) :
    ∃ PP : PolyPack S Γ dom cod, P = piPack S Γ dom cod PP ∧ IsType S.R Γ dom ∧
      IsType S.R (.snoc Γ dom) cod ∧ S.E.convTy Γ (.pi dom cod) (.pi dom cod) ∧
      (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
        Reducible S Δ (Presentation.rename ρ dom) (PP.domPack w)) ∧
      (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
        (ha : (PP.domPack w).redTm a),
        Reducible S Δ (inst0 a (Presentation.rename (liftRen ρ) cod)) (PP.codPack w ha)) := by
  obtain ⟨l, r⟩ := reducible
  have normal : Whnf S.R S.roles (.pi dom cod : Tm Head n) := pi_whnf S.shape dom cod
  cases r with
  | sort _ _ _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | neutral red neutral =>
      exact absurd (WhRed.eq_of_whnf normal red.red) (neutral.not_former.2.1 _ _)
  | ground _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | pi red domType codType refl PP domAdequate codAdequate =>
      obtain ⟨rfl, rfl⟩ := Tm.pi.inj (WhRed.eq_of_whnf normal red.red)
      exact ⟨PP, rfl, domType, codType, refl, fun w => ⟨l, domAdequate w⟩,
        fun w _ ha => ⟨l, codAdequate w ha⟩⟩
  | sigma red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | ident red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | inductiveType red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)

/-- A reducible dependent pair type, with the pack family of its derivation. -/
theorem Reducible.sigma_raw {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} {P : Pack Head n} (reducible : Reducible S Γ (.sigma dom cod) P) :
    ∃ PP : PolyPack S Γ dom cod, P = sigmaPack S Γ dom cod PP ∧ IsType S.R Γ dom ∧
      IsType S.R (.snoc Γ dom) cod ∧ S.E.convTy Γ (.sigma dom cod) (.sigma dom cod) ∧
      (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
        Reducible S Δ (Presentation.rename ρ dom) (PP.domPack w)) ∧
      (∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
        (ha : (PP.domPack w).redTm a),
        Reducible S Δ (inst0 a (Presentation.rename (liftRen ρ) cod)) (PP.codPack w ha)) := by
  obtain ⟨l, r⟩ := reducible
  have normal : Whnf S.R S.roles (.sigma dom cod : Tm Head n) := sigma_whnf S.shape dom cod
  cases r with
  | sort _ _ _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | neutral red neutral =>
      exact absurd (WhRed.eq_of_whnf normal red.red) (neutral.not_former.2.2.1 _ _)
  | ground _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | pi red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | sigma red domType codType refl PP domAdequate codAdequate =>
      obtain ⟨rfl, rfl⟩ := Tm.sigma.inj (WhRed.eq_of_whnf normal red.red)
      exact ⟨PP, rfl, domType, codType, refl, fun w => ⟨l, domAdequate w⟩,
        fun w _ ha => ⟨l, codAdequate w ha⟩⟩
  | ident red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | inductiveType red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)

/-- A reducible identity type. -/
theorem Reducible.id_view {n : Nat} {Γ : Ctx Head n} {ty lhs rhs : Tm Head n}
    {P : Pack Head n} (reducible : Reducible S Γ (.id ty lhs rhs) P) :
    ∃ tyPack : Pack Head n, P = idPack S Γ ty lhs rhs tyPack ∧
      S.E.convTy Γ (.id ty lhs rhs) (.id ty lhs rhs) ∧ Reducible S Γ ty tyPack ∧
      tyPack.redTm lhs ∧ tyPack.redTm rhs := by
  obtain ⟨l, r⟩ := reducible
  have normal : Whnf S.R S.roles (.id ty lhs rhs : Tm Head n) := id_whnf S.shape ty lhs rhs
  cases r with
  | sort _ _ _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | neutral red neutral =>
      exact absurd (WhRed.eq_of_whnf normal red.red) (neutral.not_former.2.2.2 _ _ _)
  | ground _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | pi red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | sigma red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | ident red refl tyPack tyAdequate lhsRed rhsRed =>
      obtain ⟨rfl, rfl, rfl⟩ := Tm.id.inj (WhRed.eq_of_whnf normal red.red)
      exact ⟨tyPack, rfl, refl, ⟨l, tyAdequate⟩, lhsRed, rhsRed⟩
  | inductiveType red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)

/-! ## Simple inductive types -/

/-- A reducible inductive type constant has the pack of its constructors, with
reducible closed field types. -/
theorem Reducible.inductive_view {n : Nat} {Γ : Ctx Head n} {T : DeclName}
    {ctors : List (DeclName × List (Field Head))} (role : S.roles T = .inductive ctors)
    {P : Pack Head n} (reducible : Reducible S Γ (.const T) P) :
    ∃ fieldPack : Tm Head 0 → Pack Head n, P = indPack S Γ T ctors fieldPack ∧
      ∀ {k : DeclName} {fields : List (Field Head)} {F : Tm Head 0},
        (k, fields) ∈ ctors → Field.closed F ∈ fields →
        Reducible S Γ (liftClosed F) (fieldPack F) := by
  obtain ⟨l, r⟩ := reducible
  have normal : Whnf S.R S.roles (.const T : Tm Head n) := inductive_whnf S.shape role
  cases r with
  | sort _ _ _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | neutral red neutral =>
      exact absurd (WhRed.eq_of_whnf normal red.red) (neutral.ne_inductive role)
  | ground _ red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | pi red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | sigma red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | ident red => exact absurd (WhRed.eq_of_whnf normal red.red) (by intro h; cases h)
  | inductiveType red role' _ _ fieldPack fieldAdequate =>
      have same := Tm.const.inj (WhRed.eq_of_whnf normal red.red)
      subst same
      have sameCtors := role'.symm.trans role
      injection sameCtors with sameCtors
      subst sameCtors
      exact ⟨fieldPack, rfl, fun mem closed => ⟨l, fieldAdequate mem closed⟩⟩

/-! ## Canonical pack families -/

/-- Reducibly equal arguments give reducibly equal codomains, with the packs
`packOf`. -/
def CodExt (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (dom : Tm Head n)
    (cod : Tm Head (n + 1)) : Prop :=
  ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ → ∀ {a b : Tm Head m},
    (packOf S Δ (Presentation.rename ρ dom)).redTm a →
    (packOf S Δ (Presentation.rename ρ dom)).redTm b →
    (packOf S Δ (Presentation.rename ρ dom)).eqTm a b →
    (packOf S Δ (inst0 a (Presentation.rename (liftRen ρ) cod))).eqTy
      (inst0 b (Presentation.rename (liftRen ρ) cod))

/-- The pack family whose packs are `packOf` of the parts. -/
def canonicalPoly (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (dom : Tm Head n)
    (cod : Tm Head (n + 1)) (ext : CodExt S Γ dom cod) : PolyPack S Γ dom cod where
  domPack := fun {_} {Δ} {ρ} _ => packOf S Δ (Presentation.rename ρ dom)
  codPack := fun {_} {Δ} {ρ} _ {a} _ => packOf S Δ (inst0 a (Presentation.rename (liftRen ρ) cod))
  codExt := fun {_} {_} {_} w {_} {_} ha hb hab => ext w ha hb hab

@[simp] theorem canonicalPoly_domPack {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (ext : CodExt S Γ dom cod) {m : Nat} {Δ : Ctx Head m}
    {ρ : Ren n m} (w : World S Γ Δ ρ) :
    (canonicalPoly S Γ dom cod ext).domPack w = packOf S Δ (Presentation.rename ρ dom) :=
  rfl

@[simp] theorem canonicalPoly_codPack {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (ext : CodExt S Γ dom cod) {m : Nat} {Δ : Ctx Head m}
    {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
    (ha : ((canonicalPoly S Γ dom cod ext).domPack w).redTm a) :
    (canonicalPoly S Γ dom cod ext).codPack w ha =
      packOf S Δ (inst0 a (Presentation.rename (liftRen ρ) cod)) :=
  rfl

/-- A pack family whose packs are those of the parts is the canonical one. -/
theorem PolyPack.eq_canonical {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (PP : PolyPack S Γ dom cod)
    (hdom : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      PP.domPack w = packOf S Δ (Presentation.rename ρ dom))
    (hcod : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ) {a : Tm Head m}
      (ha : (PP.domPack w).redTm a),
      PP.codPack w ha = packOf S Δ (inst0 a (Presentation.rename (liftRen ρ) cod))) :
    ∃ ext, PP = canonicalPoly S Γ dom cod ext := by
  cases PP with
  | mk domPack codPack codExt =>
    have e : @domPack = fun {m} {Δ} {ρ} (_ : World S Γ Δ ρ) =>
        packOf S Δ (Presentation.rename ρ dom) := by
      funext m Δ ρ w
      exact hdom w
    subst e
    have e' : @codPack = fun {m} {Δ} {ρ} (_ : World S Γ Δ ρ) {a}
        (_ : (packOf S Δ (Presentation.rename ρ dom)).redTm a) =>
        packOf S Δ (inst0 a (Presentation.rename (liftRen ρ) cod)) := by
      funext m Δ ρ w a ha
      exact hcod w ha
    subst e'
    exact ⟨fun w _ _ ha hb hab => codExt w ha hb hab, rfl⟩

/-- Parts of a dependent function or pair type that are reducible in every
world, with the packs `packOf`. -/
structure PolyParts (S : Setting Head L) {n : Nat} (Γ : Ctx Head n) (dom : Tm Head n)
    (cod : Tm Head (n + 1)) : Prop where
  domType : IsType S.R Γ dom
  codType : IsType S.R (.snoc Γ dom) cod
  domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ →
    Reducible S Δ (Presentation.rename ρ dom) (packOf S Δ (Presentation.rename ρ dom))
  codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ → ∀ {a : Tm Head m},
    (packOf S Δ (Presentation.rename ρ dom)).redTm a →
    Reducible S Δ (inst0 a (Presentation.rename (liftRen ρ) cod))
      (packOf S Δ (inst0 a (Presentation.rename (liftRen ρ) cod)))
  ext : CodExt S Γ dom cod

section Views

variable (laws : S.E.Laws S.R S.roles)
include laws

/-- A reducible dependent function type has the canonical pack family. -/
theorem Reducible.pi_view {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} {P : Pack Head n} (reducible : Reducible S Γ (.pi dom cod) P) :
    ∃ parts : PolyParts S Γ dom cod,
      P = piPack S Γ dom cod (canonicalPoly S Γ dom cod parts.ext) ∧
      S.E.convTy Γ (.pi dom cod) (.pi dom cod) := by
  obtain ⟨PP, rfl, domType, codType, refl, domAdequate, codAdequate⟩ := reducible.pi_raw
  have hdom : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      PP.domPack w = packOf S Δ (Presentation.rename ρ dom) :=
    fun w => (domAdequate w).eq_packOf laws
  obtain ⟨ext, rfl⟩ := PP.eq_canonical hdom (fun w _ ha => (codAdequate w ha).eq_packOf laws)
  refine ⟨⟨domType, codType, fun w => domAdequate w, fun w _ ha => codAdequate w ha, ext⟩,
    rfl, refl⟩

/-- A reducible dependent pair type has the canonical pack family. -/
theorem Reducible.sigma_view {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} {P : Pack Head n} (reducible : Reducible S Γ (.sigma dom cod) P) :
    ∃ parts : PolyParts S Γ dom cod,
      P = sigmaPack S Γ dom cod (canonicalPoly S Γ dom cod parts.ext) ∧
      S.E.convTy Γ (.sigma dom cod) (.sigma dom cod) := by
  obtain ⟨PP, rfl, domType, codType, refl, domAdequate, codAdequate⟩ := reducible.sigma_raw
  have hdom : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m} (w : World S Γ Δ ρ),
      PP.domPack w = packOf S Δ (Presentation.rename ρ dom) :=
    fun w => (domAdequate w).eq_packOf laws
  obtain ⟨ext, rfl⟩ := PP.eq_canonical hdom (fun w _ ha => (codAdequate w ha).eq_packOf laws)
  refine ⟨⟨domType, codType, fun w => domAdequate w, fun w _ ha => codAdequate w ha, ext⟩,
    rfl, refl⟩

end Views

/-- Parts reducible at level `l` in every world, with the packs `packOf`. -/
structure PolyReducible (S : Setting Head L) (l : L) {n : Nat} (Γ : Ctx Head n)
    (dom : Tm Head n) (cod : Tm Head (n + 1)) : Prop where
  domType : IsType S.R Γ dom
  codType : IsType S.R (.snoc Γ dom) cod
  domain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ →
    LogRel S l Δ (Presentation.rename ρ dom) (packOf S Δ (Presentation.rename ρ dom))
  codomain : ∀ {m : Nat} {Δ : Ctx Head m} {ρ : Ren n m}, World S Γ Δ ρ → ∀ {a : Tm Head m},
    (packOf S Δ (Presentation.rename ρ dom)).redTm a →
    LogRel S l Δ (inst0 a (Presentation.rename (liftRen ρ) cod))
      (packOf S Δ (inst0 a (Presentation.rename (liftRen ρ) cod)))
  ext : CodExt S Γ dom cod

/-- The pack family of reducible parts. -/
abbrev PolyReducible.polyPack {l : L} {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (parts : PolyReducible S l Γ dom cod) : PolyPack S Γ dom cod :=
  canonicalPoly S Γ dom cod parts.ext

/-- A dependent function type with reducible parts is reducible. -/
theorem PolyReducible.pi {l : L} {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (parts : PolyReducible S l Γ dom cod)
    (formed : IsType S.R Γ (.pi dom cod)) (refl : S.E.convTy Γ (.pi dom cod) (.pi dom cod)) :
    LogRel S l Γ (.pi dom cod) (piPack S Γ dom cod parts.polyPack) :=
  .pi (RedTy.refl formed) parts.domType parts.codType refl parts.polyPack
    (fun w => parts.domain w) (fun {_} {_} {_} w {_} ha => parts.codomain w ha)

/-- A dependent pair type with reducible parts is reducible. -/
theorem PolyReducible.sigma {l : L} {n : Nat} {Γ : Ctx Head n} {dom : Tm Head n}
    {cod : Tm Head (n + 1)} (parts : PolyReducible S l Γ dom cod)
    (formed : IsType S.R Γ (.sigma dom cod))
    (refl : S.E.convTy Γ (.sigma dom cod) (.sigma dom cod)) :
    LogRel S l Γ (.sigma dom cod) (sigmaPack S Γ dom cod parts.polyPack) :=
  .sigma (RedTy.refl formed) parts.domType parts.codType refl parts.polyPack
    (fun w => parts.domain w) (fun {_} {_} {_} w {_} ha => parts.codomain w ha)

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
