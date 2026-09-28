import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Families

/-!
# Structural inclusion of types on the value side

**Structural inclusion** (`SLe`) of types is read in one world, between two
denoted types:

* types of one shape whose packs have one relation (conversion, and a type with
  itself);
* universes, by level (cumulativity);
* dependent function types whose domains have one pack and one shape at every
  world reached by a morphism, and whose codomains are included at every valid
  argument (inclusion of function types keeps domains equal);
* dependent pair types whose domains and codomains are included;
* and the composites of these.

Over every realizer algebra it includes value relations (`SLe.rel`), and it
carries hereditary totality forward (`SLe.total`). Its inversion at a dependent
function type on the right (`SLe.pi_right`) is the step of a spine: either the
type is hereditarily total, or the included type is a dependent function type
too, with a domain of one pack and with included codomains. A type included
structurally above a universe is itself a universe (`SLe.univ_left`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-! ## Structural inclusion in a world -/

variable (V) in
/-- **Structural inclusion** of types in a world. -/
inductive SLe : {n : Nat} → World V.reading n → Tm Head n → Tm Head n → Prop
  /-- Types of one shape whose packs have one relation. -/
  | shape {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n} {P P' : Pack V n}
      (left : DenS V ξ X P) (right : DenS V ξ Y P') (same : P.rel = P'.rel)
      (d : Shape V (DenS V) .pair ξ X Y) : SLe ξ X Y
  /-- Universes, by level. -/
  | univ {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n} {u v : Head}
      (red : WhRed V.rules V.roles X (.head u)) (red' : WhRed V.rules V.roles Y (.head v))
      (isUniverse : V.rules.isUniverse u) (isUniverse' : V.rules.isUniverse v)
      (level : V.levels.level u ≤ V.levels.level v) : SLe ξ X Y
  /-- Dependent function types whose domains have one pack and one shape at every
  world reached by a morphism, and whose codomains are included at every valid
  argument. -/
  | pi {n : Nat} {ξ : World V.reading n} {X Y A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      {P P' : Pack V n} (left : DenS V ξ X P) (right : DenS V ξ Y P')
      (red : WhRed V.rules V.roles X (.pi A B)) (red' : WhRed V.rules V.roles Y (.pi A' B'))
      (dom : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        ∃ D, DenS V ξ' (Presentation.rename ρ A) D ∧
          DenS V ξ' (Presentation.rename ρ A') D ∧
          Shape V (DenS V) .pair ξ' (Presentation.rename ρ A)
            (Presentation.rename ρ A'))
      (cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
        ∀ {D : Pack V m}, DenS V ξ' (Presentation.rename ρ A) D →
          ∀ {a : Tm Head m}, D.Val a →
            SLe ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
              (inst0 a (Presentation.rename (liftRen ρ) B'))) : SLe ξ X Y
  /-- Dependent pair types whose domains, and codomains at valid points, are
  included. -/
  | sigma {n : Nat} {ξ : World V.reading n} {X Y A A' : Tm Head n} {B B' : Tm Head (n + 1)}
      {P P' : Pack V n} (left : DenS V ξ X P) (right : DenS V ξ Y P')
      (red : WhRed V.rules V.roles X (.sigma A B))
      (red' : WhRed V.rules V.roles Y (.sigma A' B')) (dom : SLe ξ A A')
      (cod : ∀ {D : Pack V n}, DenS V ξ A D → ∀ {a : Tm Head n}, D.Val a →
        SLe ξ (inst0 a B) (inst0 a B')) : SLe ξ X Y
  /-- Inclusions compose. -/
  | trans {n : Nat} {ξ : World V.reading n} {X Y Z : Tm Head n} (first : SLe ξ X Y)
      (second : SLe ξ Y Z) : SLe ξ X Z

namespace SLe

/-- Both types of an inclusion are denoted. -/
theorem den {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n} (le : SLe V ξ X Y) :
    (∃ P, DenS V ξ X P) ∧ ∃ P, DenS V ξ Y P := by
  induction le with
  | shape left right => exact ⟨⟨_, left⟩, ⟨_, right⟩⟩
  | univ red red' hu hv =>
      exact ⟨⟨_, ValueSide.DenS.expand red (ValueSide.DenS.sort hu _)⟩,
        ⟨_, ValueSide.DenS.expand red' (ValueSide.DenS.sort hv _)⟩⟩
  | pi left right => exact ⟨⟨_, left⟩, ⟨_, right⟩⟩
  | sigma left right => exact ⟨⟨_, left⟩, ⟨_, right⟩⟩
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩

section Laws

variable (laws : V.Laws)
include laws

/-- **Inclusion of relations.** -/
theorem rel {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n} (le : SLe V ξ X Y) :
    ∀ {P P' : Pack V n}, DenS V ξ X P → DenS V ξ Y P' →
      ∀ {a b : Tm Head n}, P.rel a b → P'.rel a b := by
  have facts := DenS.facts laws
  induction le with
  | shape left right same =>
      intro P P' den den' a b h
      obtain rfl := DenS.deterministic laws den left
      obtain rfl := DenS.deterministic laws den' right
      exact same ▸ h
  | univ red red' hu hv level =>
      intro P P' den den' a b h
      rw [ValueSide.DenS.univ_inv laws den red hu] at h
      rw [ValueSide.DenS.univ_inv laws den' red' hv]
      exact universeAt.mono laws level h
  | pi left right red red' dom cod codIH =>
      intro P P' den den' f g h
      obtain ⟨Q, rfl, iQ⟩ := facts.piPack den red
      obtain ⟨Q', rfl, iQ'⟩ := facts.piPack den' red'
      intro m ξ' ρ w x y hx' hxy'
      obtain ⟨D, hA, hA', -⟩ := dom w
      have e : Q'.dom w = Q.dom w :=
        (DenS.deterministic laws (iQ'.dom w) hA').trans
          (DenS.deterministic laws hA (iQ.dom w))
      have hx : (Q.dom w).Val x := e ▸ hx'
      have hxy : (Q.dom w).rel x y := e ▸ hxy'
      exact codIH w (iQ.dom w) hx (iQ.cod w hx) (iQ'.cod w hx') (h w hx hxy)
  | sigma left right red red' _ _ domIH codIH =>
      intro P P' den den' p q h
      obtain ⟨Q, rfl, iQ⟩ := facts.sigmaPack den red
      obtain ⟨Q', rfl, iQ'⟩ := facts.sigmaPack den' red'
      obtain ⟨hp, hpq, hc⟩ := h
      have hp' := domIH iQ.dom_id iQ'.dom_id hp
      exact ⟨hp', domIH iQ.dom_id iQ'.dom_id hpq,
        codIH iQ.dom_id hp (iQ.cod_id hp) (iQ'.cod_id hp') hc⟩
  | trans first _ ih₁ ih₂ =>
      intro P P' den den' a b h
      obtain ⟨-, Q, hQ⟩ := first.den
      exact ih₂ hQ den' (ih₁ den hQ h)

/-- **Hereditary totality passes forward** along inclusion. -/
theorem total {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n} (le : SLe V ξ X Y) :
    Shape V (DenS V) .total ξ X X → Shape V (DenS V) .total ξ Y Y := by
  have facts := DenS.facts laws
  induction le with
  | shape _ right _ d =>
      intro t
      exact Shape.total_transfer laws facts (d.symm facts) t ⟨_, right⟩
  | univ red _ hu => intro t; exact (t.total_not_head laws red hu).elim
  | pi _ right red red' dom _ codIH =>
      intro t
      have parts := t.total_pi laws red
      refine .totalPi red' ⟨_, right⟩ (fun w => ?_) (fun {_ _ _} w {D'} hD' {a} ha => ?_)
      · obtain ⟨D, -, hA', s⟩ := dom w
        exact (s.symm facts).trans laws facts s ⟨D, hA'⟩ ⟨D, hA'⟩
      · obtain ⟨D, hA, hA', -⟩ := dom w
        obtain rfl := DenS.deterministic laws hD' hA'
        exact codIH w hA ha (parts.codShape w hA ha)
  | sigma _ right red red' dom _ domIH codIH =>
      intro t
      have parts := t.total_sigma laws red
      obtain ⟨⟨DA, hA⟩, -⟩ := dom.den
      refine .totalSigma red' ⟨_, right⟩ (domIH parts.domShape) (fun {_} _ {a} _ => ?_)
      have ha : DA.Val a := Shape.total_rel facts parts.domShape hA a a
      exact codIH hA ha (parts.codShape hA ha)
  | trans _ _ ih₁ ih₂ => exact fun t => ih₂ (ih₁ t)

end Laws

/-- A relation of one universe gives an inclusion: one pack and one shape. -/
theorem of_universe (laws : V.Laws) {k : L} {n : Nat} {ξ : World V.reading n}
    {X Y : Tm Head n} (related : (universeAt V k ξ).rel X Y) : SLe V ξ X Y := by
  obtain ⟨P, hX, hY, s⟩ := universeAt.den related
  exact .shape ⟨k, hX⟩ ⟨k, hY⟩ rfl
    (s.mono (InterpAt.facts laws k) (fun h => ⟨k, h⟩) (DenS.facts laws).deterministic)

end SLe

/-! ## Inversion at dependent function types -/

variable (V) in
/-- The premises of the clause of dependent function types: domains of one pack
and one shape at every world reached by a morphism, and codomains included at
every valid argument. -/
def PiLe {n : Nat} (ξ : World V.reading n) (A A' : Tm Head n) (B B' : Tm Head (n + 1)) :
    Prop :=
  (∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∃ D, DenS V ξ' (Presentation.rename ρ A) D ∧
      DenS V ξ' (Presentation.rename ρ A') D ∧
      Shape V (DenS V) .pair ξ' (Presentation.rename ρ A)
        (Presentation.rename ρ A')) ∧
  ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∀ {D : Pack V m}, DenS V ξ' (Presentation.rename ρ A) D →
      ∀ {a : Tm Head m}, D.Val a →
        SLe V ξ' (inst0 a (Presentation.rename (liftRen ρ) B))
          (inst0 a (Presentation.rename (liftRen ρ) B'))

section Inversion

variable (laws : V.Laws)
include laws

/-- **Inversion at a dependent function type on the right.** A type included in
a dependent function type is hereditarily total there, or is a dependent
function type with a domain of one pack and one shape and included codomains. -/
theorem SLe.pi_right {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n}
    (le : SLe V ξ X Y) :
    ∀ {A' : Tm Head n} {B' : Tm Head (n + 1)}, WhRed V.rules V.roles Y (.pi A' B') →
      Shape V (DenS V) .total ξ Y Y ∨
        ∃ A B, WhRed V.rules V.roles X (.pi A B) ∧ PiLe V ξ A A' B B' := by
  have facts := DenS.facts laws
  induction le with
  | shape _ _ _ d =>
      intro A' B' red'
      rcases d.pair_pi_right laws red' with ⟨-, tY⟩ | ⟨A, B, red, parts⟩
      · exact .inl tY
      · refine .inr ⟨A, B, red, fun w => ?_, fun {_ _ _} w {D} hD {a} ha => ?_⟩
        · obtain ⟨D, D', hA, hA', e⟩ := parts.domPacks w
          subst e
          exact ⟨D, hA, hA', parts.domShape w⟩
        · obtain ⟨C, C', hC, hC', e⟩ := parts.codPacks w hD ha
          exact .shape hC hC' e (parts.codShape w hD ha)
  | univ _ red'' _ _ =>
      intro A' B' red'
      cases laws.unique red'' red' (head_whnf laws.shape _)
        (pi_whnf laws.shape _ _)
  | pi _ _ red red'' dom cod =>
      intro A' B' red'
      cases laws.unique red'' red' (pi_whnf laws.shape _ _)
        (pi_whnf laws.shape _ _)
      exact .inr ⟨_, _, red, dom, cod⟩
  | sigma _ _ _ red'' =>
      intro A' B' red'
      cases laws.unique red'' red' (sigma_whnf laws.shape _ _)
        (pi_whnf laws.shape _ _)
  | trans _ second ih₁ ih₂ =>
      intro A' B' red'
      rcases ih₂ red' with tY | ⟨AM, BM, redM, domM, codM⟩
      · exact .inl tY
      rcases ih₁ redM with tM | ⟨A, B, red, dom, cod⟩
      · exact .inl (second.total laws tM)
      refine .inr ⟨A, B, red, fun w => ?_, fun {_ _ _} w {D} hD {a} ha => ?_⟩
      · obtain ⟨D₁, h₁, h₁M, s₁⟩ := dom w
        obtain ⟨D₂, h₂M, h₂, s₂⟩ := domM w
        obtain rfl := DenS.deterministic laws h₁M h₂M
        exact ⟨D₁, h₁, h₂, s₁.trans laws facts s₂ ⟨_, h₁⟩ ⟨_, h₂⟩⟩
      · obtain ⟨D₁, h₁, h₁M, -⟩ := dom w
        obtain rfl := DenS.deterministic laws hD h₁
        exact .trans (cod w h₁ ha) (codM w h₁M ha)

/-- A hereditarily total dependent function type has hereditarily total
codomains at the valid arguments of its domain. -/
theorem total_cod {n : Nat} {ξ : World V.reading n} {X A : Tm Head n} {B : Tm Head (n + 1)}
    (t : Shape V (DenS V) .total ξ X X) (red : WhRed V.rules V.roles X (.pi A B))
    {D : Pack V n} (hD : DenS V ξ A D) {a : Tm Head n} (ha : D.Val a) :
    Shape V (DenS V) .total ξ (inst0 a B) (inst0 a B) := by
  have parts := t.total_pi laws red
  have hD' : DenS V ξ (Presentation.rename idRen A) D := by rwa [rename_id]
  have h := parts.codShape (Morph.id ξ) hD' ha
  rwa [liftRen_id, rename_id] at h

end Inversion

/-! ## Universes on the left -/

/-- **A type structurally above a universe reduces to a universe.** -/
theorem SLe.univ_left (laws : V.Laws) {n : Nat} {ξ : World V.reading n} {X Y : Tm Head n}
    (le : SLe V ξ X Y) {u : Head} (red : WhRed V.rules V.roles X (.head u))
    (hu : V.rules.isUniverse u) :
    ∃ v, WhRed V.rules V.roles Y (.head v) ∧ V.rules.isUniverse v := by
  induction le generalizing u with
  | shape _ _ _ d =>
      obtain ⟨v, red', hv, -⟩ := Shape.pair_head_left laws d red hu
      exact ⟨v, red', hv⟩
  | univ _ red' _ hv _ => exact ⟨_, red', hv⟩
  | pi _ _ red₁ =>
      cases laws.unique red red₁ (head_whnf laws.shape _) (pi_whnf laws.shape _ _)
  | sigma _ _ red₁ =>
      cases laws.unique red red₁ (head_whnf laws.shape _) (sigma_whnf laws.shape _ _)
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨v, red', hv⟩ := ih₁ red hu
      exact ih₂ red' hv

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
