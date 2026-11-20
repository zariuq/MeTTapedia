import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Families.Laws
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Reduction

/-!
# The identity type is a family

The identity type `Id ty lhs rhs` is the family whose parameter is the carrier `ty`, which
reflexivity does not store, whose two indices are the endpoints, both of type `ty`, and
whose one constructor is reflexivity, with one field, its point `x : ty`, targeting the
indices `(x, x)`. This is the formulation with both endpoints as indices, and the grammar's
own reading of reflexivity: an inspection reads `refl x` as a constructor whose field list is
`[x]`.

The family pack at this reading and the identity pack `idPack` are defined separately.
When the carrier's pack is the pack of a reducible type that is symmetric and transitive
(the premises of the identity case of the relation), the two packs have the same reducibly
equal types, the same reducible terms and the same reducible equalities, so they are equal
(`identity_pack_eq`). The family pack asks the point to be reducible and reducibly equal
to both endpoints; the identity pack asks the point to be typed and reducibly equal to both
endpoints; reducibility and typing of the point follow from each other through the
carrier's pack.

The hypotheses the laws of the family pack ask for hold at this reading under the same
premises (`identityFamily_rigid` and the others).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization
namespace Families

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-! ## The reading -/

section Reading

variable {n : Nat}

/-- Reflexivity read as a family constructor: its canonical forms are `refl x`, with the one
field `x`, and it targets the indices `(x, x)`. -/
def identityCtor (tyPack : Pack Head n) : CtorAt Head n where
  form nf fs := ∃ x, fs = [x] ∧ nf = .refl x
  fields := [.value tyPack]
  target fs := fs ++ fs

/-- The identity type at the carrier `ty` read as a family. Another identity type is the same
family when its carrier is reducibly equal to `ty`: the carrier is the type of the field and
of both indices. -/
def identityFamily (ty : Tm Head n) (tyPack : Pack Head n) : FamilyAt Head n where
  type is := .id ty (is.headD ty) (is.tail.headD ty)
  ctors := [identityCtor tyPack]
  indexPacks := [tyPack, tyPack]
  sameFormer X is := ∃ ty' a b, X = .id ty' a b ∧ is = [a, b] ∧ tyPack.eqTy ty'

end Reading

/-! ## The same packs -/

section Same

variable {n : Nat} {Γ : Ctx Head n} {ty lhs rhs : Tm Head n} {tyPack : Pack Head n}

theorem identity_eqTy {B : Tm Head n} :
    (familyPack S Γ (identityFamily ty tyPack) [lhs, rhs]).eqTy B ↔
      (idPack S Γ ty lhs rhs tyPack).eqTy B := by
  constructor
  · rintro ⟨X, is', red, ⟨ty', a, b, rfl, rfl, eqTy'⟩, conv, agree⟩
    cases agree with
    | cons l rest =>
        cases rest with
        | cons r _ => exact ⟨ty', a, b, red, conv, eqTy', l, r⟩
  · rintro ⟨ty', a, b, red, conv, eqTy', l, r⟩
    exact ⟨.id ty' a b, [a, b], red, ⟨ty', a, b, rfl, rfl, eqTy'⟩, conv, .cons l (.cons r .nil)⟩

theorem identity_redTm
    (tyEnds : ∀ {a b : Tm Head n}, tyPack.eqTm a b → tyPack.redTm a ∧ tyPack.redTm b)
    (tyTyped : ∀ {a : Tm Head n}, tyPack.redTm a → Typed S.R Γ a ty) {t : Tm Head n} :
    (familyPack S Γ (identityFamily ty tyPack) [lhs, rhs]).redTm t ↔
      (idPack S Γ ty lhs rhs tyPack).redTm t := by
  constructor
  · rintro ⟨red, conv, normal⟩
    cases normal with
    | ctor mem form fields agree =>
        obtain rfl := List.mem_singleton.mp mem
        obtain ⟨x, rfl, rfl⟩ := form
        cases fields with
        | value head _ =>
            change IndexAgree [tyPack, tyPack] [lhs, rhs] [x, x] at agree
            cases agree with
            | cons l rest =>
                cases rest with
                | cons r _ => exact ⟨_, red, conv, .inl ⟨x, rfl, tyTyped head, l, r⟩⟩
    | neutral nNf convN => exact ⟨_, red, conv, .inr ⟨nNf, convN⟩⟩
  · rintro ⟨nf, red, conv, prop⟩
    rcases prop with ⟨x, rfl, _, l, r⟩ | ⟨nNf, convN⟩
    · exact .mk red conv (.ctor (List.mem_singleton_self _) ⟨x, rfl, rfl⟩
        (.value (tyEnds l).2 .nil) (.cons l (.cons r .nil)))
    · exact .mk red conv (.neutral nNf convN)

theorem identity_eqTm
    (tyEnds : ∀ {a b : Tm Head n}, tyPack.eqTm a b → tyPack.redTm a ∧ tyPack.redTm b)
    (tyTyped : ∀ {a : Tm Head n}, tyPack.redTm a → Typed S.R Γ a ty)
    (tySymm : ∀ {a b : Tm Head n}, tyPack.eqTm a b → tyPack.eqTm b a)
    (tyTrans : ∀ {a b c : Tm Head n}, tyPack.eqTm a b → tyPack.eqTm b c → tyPack.eqTm a c)
    {t t' : Tm Head n} :
    (familyPack S Γ (identityFamily ty tyPack) [lhs, rhs]).eqTm t t' ↔
      (idPack S Γ ty lhs rhs tyPack).eqTm t t' := by
  constructor
  · rintro ⟨red, red', conv, normal⟩
    cases normal with
    | ctor mem form form' fields agree agree' =>
        obtain rfl := List.mem_singleton.mp mem
        obtain ⟨x, rfl, rfl⟩ := form
        obtain ⟨x', rfl, rfl⟩ := form'
        change IndexAgree [tyPack, tyPack] [lhs, rhs] [x, x] at agree
        change IndexAgree [tyPack, tyPack] [lhs, rhs] [x', x'] at agree'
        cases agree with
        | cons l rest =>
            cases rest with
            | cons r _ =>
                cases agree' with
                | cons l' rest' =>
                    cases rest' with
                    | cons r' _ =>
                        exact ⟨_, _, red, red', conv, .inl ⟨x, x', rfl, rfl,
                          tyTyped (tyEnds l).2, tyTyped (tyEnds l').2, l, l', r, r'⟩⟩
    | neutral nNf nNf' convN => exact ⟨_, _, red, red', conv, .inr ⟨nNf, nNf', convN⟩⟩
  · rintro ⟨nf, nf', red, red', conv, prop⟩
    rcases prop with ⟨x, x', rfl, rfl, _, _, l, l', r, r'⟩ | ⟨nNf, nNf', convN⟩
    · exact .mk red red' conv (.ctor (List.mem_singleton_self _) ⟨x, rfl, rfl⟩ ⟨x', rfl, rfl⟩
        (.value (tyTrans (tySymm l) l') .nil) (.cons l (.cons r .nil))
        (.cons l' (.cons r' .nil)))
    · exact .mk red red' conv (.neutral nNf nNf' convN)

/-- **The identity pack is the family pack at the identity reading**, under the premises of
the identity case of the relation: a reducible carrier whose reducible equality is
symmetric and transitive. -/
theorem identity_pack_eq (laws : S.E.Laws S.R S.roles) {l : L} {rec : L → RedRel Head}
    (tyAdequate : LR S l rec Γ ty tyPack)
    (tySymm : ∀ {a b : Tm Head n}, tyPack.eqTm a b → tyPack.eqTm b a)
    (tyTrans : ∀ {a b c : Tm Head n}, tyPack.eqTm a b → tyPack.eqTm b c → tyPack.eqTm a c) :
    familyPack S Γ (identityFamily ty tyPack) [lhs, rhs] = idPack S Γ ty lhs rhs tyPack := by
  have tyEnds : ∀ {a b : Tm Head n}, tyPack.eqTm a b → tyPack.redTm a ∧ tyPack.redTm b :=
    fun h => tyAdequate.eqTm_redTm laws h
  have tyTyped : ∀ {a : Tm Head n}, tyPack.redTm a → Typed S.R Γ a ty :=
    fun h => ((tyAdequate.escape laws).redTm h).1
  exact PackEquiv.eq ⟨identity_eqTy, identity_redTm tyEnds tyTyped,
    identity_eqTm tyEnds tyTyped tySymm tyTrans⟩

end Same

/-! ## The hypotheses of the laws hold -/

section Hypotheses

variable {n : Nat} {Γ : Ctx Head n} {ty : Tm Head n} {tyPack : Pack Head n}

theorem identityFamily_rigid : FormsRigid S (identityFamily ty tyPack) where
  whnf := by
    intro c nf fs mem form
    obtain rfl := List.mem_singleton.mp mem
    obtain ⟨x, rfl, rfl⟩ := form
    exact refl_whnf S.shape x
  not_neutral := by
    intro c nf fs mem form nNf
    obtain rfl := List.mem_singleton.mp mem
    obtain ⟨x, rfl, rfl⟩ := form
    exact nNf.ne_refl rfl
  unique := by
    intro c c' nf fs fs' mem mem' form form'
    obtain rfl := List.mem_singleton.mp mem
    obtain rfl := List.mem_singleton.mp mem'
    obtain ⟨x, rfl, rfl⟩ := form
    obtain ⟨x', rfl, e⟩ := form'
    cases e
    exact ⟨rfl, rfl⟩

theorem identityFamily_per
    (tySymm : ∀ {a b : Tm Head n}, tyPack.eqTm a b → tyPack.eqTm b a)
    (tyTrans : ∀ {a b c : Tm Head n}, tyPack.eqTm a b → tyPack.eqTm b c → tyPack.eqTm a c) :
    IndexPER (identityFamily ty tyPack) where
  symm := by
    intro P mem a b h
    have hP : P = tyPack := by
      rcases List.mem_cons.mp mem with rfl | mem
      · rfl
      · exact List.mem_singleton.mp mem
    subst hP
    exact tySymm h
  trans := by
    intro P mem a b c h h'
    have hP : P = tyPack := by
      rcases List.mem_cons.mp mem with rfl | mem
      · rfl
      · exact List.mem_singleton.mp mem
    subst hP
    exact tyTrans h h'

theorem identityFamily_congr (laws : S.E.Laws S.R S.roles) {l : L} {rec : L → RedRel Head}
    (tyAdequate : LR S l rec Γ ty tyPack) : TypeCongr S Γ (identityFamily ty tyPack) := by
  intro is is' agree
  have esc := tyAdequate.escape laws
  cases agree with
  | cons l rest =>
      cases rest with
      | cons r tail =>
          cases tail
          exact laws.convTy_sound (laws.convTy_id esc.refl (esc.eqTm l) (esc.eqTm r))

theorem identityFamily_recExt : RecursiveExt S Γ (identityFamily ty tyPack) := by
  intro c fs fs' mem _ idx recMem
  obtain rfl := List.mem_singleton.mp mem
  cases List.mem_singleton.mp recMem

end Hypotheses

end Families
end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
