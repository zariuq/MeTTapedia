import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Levels

/-!
# Universes, families, functions, pairs and identity types on the value side

Facts about denotations that hold over every realizer algebra:

* **Universes.** A universe denotes the pack of its level (`DenS.sort_inv`):
  types with one pack and one shape at every world reached by a morphism. The
  relation grows with the level and is carried along world morphisms. A head
  at a level is interpreted, and is of one shape with itself: a universe below
  the level by its level, any other head as a leaf (`head_shape`).
* **Families.** Dependent function and pair types with related domains, and
  codomains related at related arguments, are interpreted at a level by one
  family (`interp_family`), the one that describes the domain and the codomain
  at every world reached by a morphism (`PiPack.ofFamily`); and they are of one
  shape by the clauses of dependent function and pair types (`shape_family`).
* **Functions.** Abstractions are related when their bodies are
  (`PiPack.rel_lam`); related functions send related arguments to related
  results at the codomain instantiated at the first argument (`DenS.pi_app`),
  and the codomain has one denotation at related arguments (`DenS.pi_cod`).
* **Pairs.** Related pairs have valid, related first projections and second
  projections related at the codomain instantiated at the first projection;
  pairs are related as soon as their components are (`DenS.sigma_pair`).
* **Identity types.** Identity types over related carriers with related
  endpoints have one pack, and are of one shape as leaves (`interp_ident`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization (WhRed WhStep)
open UniverseLevel (LevelOrder)
open Consistency (World Morph)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-! ## The pack of a universe -/

variable (V) in
/-- The pack of the universe at level `k`. -/
abbrev universeAt (k : L) {n : Nat} (ξ : World V.reading n) : Pack V n :=
  universePack V (InterpAt V k) ξ

/-- A universe denotes the pack of its level. -/
theorem DenS.sort_inv (laws : V.Laws) {u : Head} (isUniverse : V.rules.isUniverse u)
    {n : Nat} {ξ : World V.reading n} {P : Pack V n} (den : DenS V ξ (.head u) P) :
    P = universeAt V (V.levels.level u) ξ :=
  DenS.univ_inv laws den .refl isUniverse

/-- Types related in a universe have one pack and one shape at its level. -/
theorem universeAt.den {k : L} {n : Nat} {ξ : World V.reading n} {A B : Tm Head n}
    (h : (universeAt V k ξ).rel A B) :
    ∃ P, InterpAt V k ξ A P ∧ InterpAt V k ξ B P ∧ Shape V (InterpAt V k) .pair ξ A B :=
  universePack_rel_self h

/-- Universes are cumulative. -/
theorem universeAt.mono (laws : V.Laws) {k k' : L} (le : k ≤ k') {n : Nat}
    {ξ : World V.reading n} {A B : Tm Head n} (h : (universeAt V k ξ).rel A B) :
    (universeAt V k' ξ).rel A B :=
  universePack_mono laws le h

/-- Related types of a universe stay related at every world reached by a
morphism. -/
theorem universeAt.rename {k : L} {n m : Nat} {ξ : World V.reading n} {ξ' : World V.reading m}
    {ρ : Ren n m} (w : Morph ξ ξ' ρ) {A B : Tm Head n} (h : (universeAt V k ξ).rel A B) :
    (universeAt V k ξ').rel (Presentation.rename ρ A) (Presentation.rename ρ B) :=
  (universePack_renamed w).rel h

/-- A head at a level is interpreted, and is of one shape with itself: a universe
below the level by its level, any other head as a leaf. -/
theorem head_shape (laws : V.Laws) {k : L} {h : Head}
    (below : V.rules.isUniverse h → V.levels.level h < k) {n : Nat} (ξ : World V.reading n) :
    ∃ P, InterpAt V k ξ (.head h) P ∧ Shape V (InterpAt V k) .pair ξ (.head h) (.head h) := by
  rcases V.levels.universe_decided h with hh | hh
  · exact ⟨_, SInterp.sort (V := V) hh (below hh) .refl, .univ .refl .refl hh hh rfl⟩
  · have leaf : Shape V (InterpAt V k) .total ξ (.head h) (.head h) :=
      Shape.of_methodForm laws (SInterp.ground (V := V) hh .refl) .refl (.inl ⟨h, rfl, hh⟩)
    exact ⟨_, SInterp.ground (V := V) hh .refl, .total leaf leaf⟩

/-- Two universes are at most at the level of their join. -/
theorem level_join {u v w : Head} (join : V.rules.join u v w) :
    V.levels.level u ≤ V.levels.level w ∧ V.levels.level v ≤ V.levels.level w := by
  rw [(V.levels.join_level join).2]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

/-! ## Families at one level -/

variable (V) in
/-- The family of a dependent function or pair type whose domain and codomain
are read at level `k`, at every world reached by a morphism: the packs
described by their interpretations there. -/
def PiPack.ofFamily (k : L) {n : Nat} (ξ : World V.reading n) (A : Tm Head n)
    (B : Tm Head (n + 1)) : PiPack V ξ where
  dom := fun {_ ξ' ρ} _ => Pack.describe V fun Q => InterpAt V k ξ' (Presentation.rename ρ A) Q
  cod := fun {_ ξ' ρ} _ {a} _ =>
    Pack.describe V fun Q => InterpAt V k ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) Q

theorem PiPack.ofFamily_dom (laws : V.Laws) {k : L} {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {B : Tm Head (n + 1)} {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}
    (w : Morph ξ ξ' ρ) {P : Pack V m} (interp : InterpAt V k ξ' (Presentation.rename ρ A) P) :
    (PiPack.ofFamily V k ξ A B).dom w = P :=
  Pack.describe_eq laws.alg interp fun _ h => InterpAt.deterministic laws h interp

theorem PiPack.ofFamily_cod (laws : V.Laws) {k : L} {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {B : Tm Head (n + 1)} {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}
    (w : Morph ξ ξ' ρ) {a : Tm Head m} (ha : ((PiPack.ofFamily V k ξ A B).dom w).Val a)
    {P : Pack V m} (interp : InterpAt V k ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) P) :
    (PiPack.ofFamily V k ξ A B).cod w ha = P :=
  Pack.describe_eq laws.alg interp fun _ h => InterpAt.deterministic laws h interp

/-- A family that interprets the domain and codomain of a dependent function
type interprets the type by its function pack. -/
theorem PiPack.Interprets.pi {k : L} {n : Nat} {ξ : World V.reading n} {Q : PiPack V ξ}
    {A : Tm Head n} {B : Tm Head (n + 1)} (interprets : Q.Interprets (InterpAt V k) A B) :
    InterpAt V k ξ (.pi A B) Q.piPack :=
  SInterp.pi .refl Q interprets.dom interprets.cod interprets.codRespect

/-- A family that interprets the domain and codomain of a dependent pair type
interprets the type by its pair pack. -/
theorem PiPack.Interprets.sigma {k : L} {n : Nat} {ξ : World V.reading n} {Q : PiPack V ξ}
    {A : Tm Head n} {B : Tm Head (n + 1)} (interprets : Q.Interprets (InterpAt V k) A B) :
    InterpAt V k ξ (.sigma A B) Q.sigmaPack :=
  SInterp.sigma .refl Q interprets.dom interprets.cod interprets.codRespect

section Families

variable {k : L} {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n} {B B' : Tm Head (n + 1)}
  (dom : (universeAt V k ξ).rel A A')
  (cod : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
    ∀ {P : Pack V m} {a b : Tm Head m},
      InterpAt V k ξ' (Presentation.rename ρ A) P → P.rel a b →
        (universeAt V k ξ').rel (inst0 a (Presentation.rename (liftRen ρ) B))
          (inst0 b (Presentation.rename (liftRen ρ) B')))
include dom cod

/-- **One pack.** Dependent function and pair types with related domains, and
codomains related at related arguments, are interpreted at the level by one
family. -/
theorem interp_family (laws : V.Laws) :
    ∃ Q : PiPack V ξ, Q.Interprets (InterpAt V k) A B ∧ Q.Interprets (InterpAt V k) A' B' := by
  let Q := PiPack.ofFamily V k ξ A B
  have domI : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ),
      InterpAt V k ξ' (Presentation.rename ρ A) (Q.dom w) ∧
        InterpAt V k ξ' (Presentation.rename ρ A') (Q.dom w) := by
    intro _ _ _ w
    obtain ⟨P, hA, hA', -⟩ := dom w
    rw [PiPack.ofFamily_dom laws w hA]
    exact ⟨hA, hA'⟩
  have codI : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : (Q.dom w).Val a),
      InterpAt V k ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) (Q.cod w ha) ∧
        InterpAt V k ξ' (inst0 a (Presentation.rename (liftRen ρ) B')) (Q.cod w ha) := by
    intro _ _ _ w a ha
    obtain ⟨C, hB, hB', -⟩ := universeAt.den (cod w (domI w).1 ha)
    rw [PiPack.ofFamily_cod laws w ha hB]
    exact ⟨hB, hB'⟩
  have respect : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a b : Tm Head m} (ha : (Q.dom w).Val a) (hb : (Q.dom w).Val b),
      (Q.dom w).rel a b → Q.cod w ha = Q.cod w hb := by
    intro _ _ _ w a b ha hb hab
    obtain ⟨C₁, hBa, hB'b, -⟩ := universeAt.den (cod w (domI w).1 hab)
    obtain ⟨C₂, hBb, hB'b₂, -⟩ := universeAt.den (cod w (domI w).1 hb)
    rw [PiPack.ofFamily_cod laws w ha hBa, PiPack.ofFamily_cod laws w hb hBb]
    exact InterpAt.deterministic laws hB'b hB'b₂
  exact ⟨Q, ⟨fun w => (domI w).1, fun {_ _ _} w {_} ha => (codI w ha).1, respect⟩,
    ⟨fun w => (domI w).2, fun {_ _ _} w {_} ha => (codI w ha).2, respect⟩⟩

/-- **One shape.** Dependent function types with related domains, and codomains
related at related arguments, are of one shape by the clause of dependent
function types, and so are the dependent pair types. -/
theorem shape_family :
    Shape V (InterpAt V k) .pair ξ (.pi A B) (.pi A' B') ∧
      Shape V (InterpAt V k) .pair ξ (.sigma A B) (.sigma A' B') := by
  have codHere : ∀ {P : Pack V n}, InterpAt V k ξ A P → ∀ {a b : Tm Head n},
      P.rel a b → ∃ C, InterpAt V k ξ (inst0 a B) C ∧ InterpAt V k ξ (inst0 b B') C ∧
        Shape V (InterpAt V k) .pair ξ (inst0 a B) (inst0 b B') := by
    intro P hP a b hab
    have hP' : InterpAt V k ξ (Presentation.rename idRen A) P := by
      rw [rename_id]
      exact hP
    obtain ⟨C, hB, hB', s⟩ := universeAt.den (cod (Morph.id ξ) hP' hab)
    simp only [liftRen_id, rename_id] at hB hB' s
    exact ⟨C, hB, hB', s⟩
  refine ⟨.pi .refl .refl (fun w => ?_) (fun w => ?_) (fun {_ _ _} w {_} hP {_ _} hab => ?_)
      (fun {_ _ _} w {_} hP {_ _} hab => ?_),
    .sigma .refl .refl ?_ ?_ (fun {_} hP {_ _} hab => ?_) (fun {_} hP {_ _} hab => ?_)⟩
  · obtain ⟨P, hA, hA', -⟩ := dom w
    exact ⟨P, P, hA, hA', rfl⟩
  · obtain ⟨P, -, -, s⟩ := dom w
    exact s
  · obtain ⟨C, hB, hB', -⟩ := universeAt.den (cod w hP hab)
    exact ⟨C, C, hB, hB', rfl⟩
  · obtain ⟨C, -, -, s⟩ := universeAt.den (cod w hP hab)
    exact s
  · obtain ⟨P, hA, hA', -⟩ := universeAt.den dom
    exact ⟨P, P, hA, hA', rfl⟩
  · obtain ⟨P, -, -, s⟩ := universeAt.den dom
    exact s
  · obtain ⟨C, hB, hB', -⟩ := codHere hP hab
    exact ⟨C, C, hB, hB', rfl⟩
  · obtain ⟨C, -, -, s⟩ := codHere hP hab
    exact s

end Families

/-! ## Identity types -/

/-- Identity types over carriers related in a universe, whose endpoints are
related in the carrier's pack, have one pack, and are of one shape as leaves. -/
theorem interp_ident (laws : V.Laws) {k : L} {n : Nat} {ξ : World V.reading n}
    {A A' a a' b b' : Tm Head n} (ty : (universeAt V k ξ).rel A A')
    (lhs : ∀ {R : Pack V n}, InterpAt V k ξ A R → R.rel a a')
    (rhs : ∀ {R : Pack V n}, InterpAt V k ξ A R → R.rel b b') :
    ∃ P, InterpAt V k ξ (.id A a b) P ∧ InterpAt V k ξ (.id A' a' b') P ∧
      Shape V (InterpAt V k) .pair ξ (.id A a b) (.id A' a' b') := by
  obtain ⟨R, hA, hA', -⟩ := universeAt.den ty
  have ha := lhs hA
  have hb := rhs hA
  have per := InterpAt.per laws hA
  have same : R.rel a b ↔ R.rel a' b' :=
    ⟨fun h => per.trans (per.trans (per.symm ha) h) hb,
      fun h => per.trans ha (per.trans h (per.symm hb))⟩
  have first : InterpAt V k ξ (.id A a b) (identPack R a b) :=
    SInterp.ident .refl R hA (per.refl_left ha) (per.refl_left hb)
  have second : InterpAt V k ξ (.id A' a' b') (identPack R a b) := by
    have e : identPack R a b = identPack R a' b' := by
      unfold identPack
      rw [propext same]
    rw [e]
    exact SInterp.ident .refl R hA' (per.refl_right ha) (per.refl_right hb)
  exact ⟨_, first, second,
    .total (Shape.of_methodForm laws first .refl (.inr (.inl ⟨_, _, _, rfl⟩)))
      (Shape.of_methodForm laws second .refl (.inr (.inl ⟨_, _, _, rfl⟩)))⟩

/-- An identity type whose endpoints are valid values of the pack of its carrier
denotes the identity pack. -/
theorem DenS.ident {n : Nat} {ξ : World V.reading n} {A a b : Tm Head n} {R : Pack V n}
    (den : DenS V ξ A R) (ha : R.Val a) (hb : R.Val b) :
    DenS V ξ (.id A a b) (identPack R a b) := by
  obtain ⟨l, interp⟩ := den
  exact ⟨l, SInterp.ident .refl R interp ha hb⟩

/-! ## Functions -/

section Functions

variable (laws : V.Laws)
include laws

/-- At related arguments, the codomain of a family that interprets a dependent
type has one denotation. -/
theorem interprets_cod_den {l : L} {n : Nat} {ξ : World V.reading n} {Q : PiPack V ξ}
    {A : Tm Head n} {B : Tm Head (n + 1)} (interprets : Q.Interprets (InterpAt V l) A B)
    {a b : Tm Head n} (hab : ∀ {PA : Pack V n}, DenS V ξ A PA → PA.rel a b) {PB : Pack V n}
    (denB : DenS V ξ (inst0 a B) PB) : DenS V ξ (inst0 b B) PB := by
  have domI : DenS V ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  have hab' := hab domI
  have ha := domI.refl_left laws hab'
  have hb := domI.refl_right laws hab'
  rw [DenS.deterministic laws denB ⟨l, interprets.cod_id ha⟩,
    interprets.codRespect (Morph.id ξ) ha hb hab']
  exact ⟨l, interprets.cod_id hb⟩

/-- Abstractions are related at a dependent function type when, at every world
reached by a morphism, their bodies instantiated at related arguments are
related at the codomain. -/
theorem PiPack.rel_lam {l : L} {n : Nat} {ξ : World V.reading n} {Q : PiPack V ξ}
    {B : Tm Head (n + 1)}
    (codInterp : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a : Tm Head m} (ha : (Q.dom w).Val a),
      InterpAt V l ξ' (inst0 a (Presentation.rename (liftRen ρ) B)) (Q.cod w ha))
    {body body' : Tm Head (n + 1)}
    (bodies : ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ)
      {a b : Tm Head m} (ha : (Q.dom w).Val a), (Q.dom w).rel a b →
        (Q.cod w ha).rel (inst0 a (Presentation.rename (liftRen ρ) body))
          (inst0 b (Presentation.rename (liftRen ρ) body'))) :
    Q.rel (.lam body) (.lam body') := by
  intro m ξ' ρ w a b ha hab
  have expansive := InterpAt.expansive laws (codInterp w ha)
  exact expansive.left (.single (WhStep.beta _ a))
    (expansive.right (.single (WhStep.beta _ b)) (bodies w ha hab))

/-- Related functions send related arguments to results related at the codomain
instantiated at the first argument. -/
theorem DenS.pi_app {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {P : Pack V n} (den : DenS V ξ (.pi A B) P) {f g a b : Tm Head n} (hfg : P.rel f g)
    (hab : ∀ {PA : Pack V n}, DenS V ξ A PA → PA.rel a b) {PB : Pack V n}
    (denB : DenS V ξ (inst0 a B) PB) : PB.rel (.app f a) (.app g b) := by
  obtain ⟨l, Q, rfl, interprets⟩ := DenS.pi_inv laws den
  have domI : DenS V ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  have ha := domI.refl_left laws (hab domI)
  rw [DenS.deterministic laws denB ⟨l, interprets.cod_id ha⟩]
  have h := hfg (Morph.id ξ) ha (hab domI)
  simp only [rename_id] at h
  exact h

/-- Related functions applied to related arguments give results related at a
denotation of the codomain instantiated at the first argument. -/
theorem DenS.pi_app_exists {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (den : DenS V ξ (.pi A B) P) {f g a b : Tm Head n}
    (hfg : P.rel f g) (hab : ∀ {PA : Pack V n}, DenS V ξ A PA → PA.rel a b) :
    ∃ PB, DenS V ξ (inst0 a B) PB ∧ PB.rel (.app f a) (.app g b) := by
  obtain ⟨l, Q, rfl, interprets⟩ := DenS.pi_inv laws den
  have domI : DenS V ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  have denB : DenS V ξ (inst0 a B) (Q.cod (Morph.id ξ) (domI.refl_left laws (hab domI))) :=
    ⟨l, interprets.cod_id _⟩
  exact ⟨_, denB, DenS.pi_app laws den hfg hab denB⟩

/-- At related arguments, the codomain of a dependent function type has one
denotation. -/
theorem DenS.pi_cod {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {P : Pack V n} (den : DenS V ξ (.pi A B) P) {a b : Tm Head n}
    (hab : ∀ {PA : Pack V n}, DenS V ξ A PA → PA.rel a b) {PB : Pack V n}
    (denB : DenS V ξ (inst0 a B) PB) : DenS V ξ (inst0 b B) PB := by
  obtain ⟨_, _, -, interprets⟩ := DenS.pi_inv laws den
  exact interprets_cod_den laws interprets hab denB

end Functions

/-! ## Pairs -/

section Pairs

variable (laws : V.Laws)
include laws

/-- A term that weak-head reduces to a valid value is a valid value, related to
it. -/
theorem DenS.val_expand {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) {t t' : Tm Head n} (red : WhRed V.rules V.roles t t') (h : P.Val t') :
    P.Val t ∧ P.rel t t' := by
  have expansive := den.expansive laws
  have rel := expansive.left red h
  exact ⟨expansive.right red rel, rel⟩

/-- Related pairs have valid first projections. -/
theorem DenS.sigma_fst_val {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (den : DenS V ξ (.sigma A B) P) {p q : Tm Head n}
    (h : P.rel p q) {PA : Pack V n} (denA : DenS V ξ A PA) :
    PA.Val (.fst p) ∧ PA.Val (.fst q) := by
  obtain ⟨l, Q, rfl, interprets⟩ := DenS.sigma_inv laws den
  obtain rfl := DenS.deterministic laws denA ⟨l, interprets.dom_id⟩
  obtain ⟨hp, hpq, _⟩ := h
  exact ⟨hp, denA.refl_right laws hpq⟩

/-- Related pairs have first projections related at the domain. -/
theorem DenS.sigma_fst {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (den : DenS V ξ (.sigma A B) P) {p q : Tm Head n}
    (h : P.rel p q) {PA : Pack V n} (denA : DenS V ξ A PA) : PA.rel (.fst p) (.fst q) := by
  obtain ⟨l, Q, rfl, interprets⟩ := DenS.sigma_inv laws den
  obtain rfl := DenS.deterministic laws denA ⟨l, interprets.dom_id⟩
  obtain ⟨_, hfst, _⟩ := h
  exact hfst

/-- Related pairs have second projections related at the codomain instantiated
at the first projection. -/
theorem DenS.sigma_snd {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (den : DenS V ξ (.sigma A B) P) {p q : Tm Head n}
    (h : P.rel p q) {PB : Pack V n} (denB : DenS V ξ (inst0 (.fst p) B) PB) :
    PB.rel (.snd p) (.snd q) := by
  obtain ⟨l, Q, rfl, interprets⟩ := DenS.sigma_inv laws den
  obtain ⟨hp, _, hsnd⟩ := h
  rw [DenS.deterministic laws denB ⟨l, interprets.cod_id hp⟩]
  exact hsnd

/-- At related arguments, the codomain of a dependent pair type has one
denotation. -/
theorem DenS.sigma_cod {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (den : DenS V ξ (.sigma A B) P) {a b : Tm Head n}
    (hab : ∀ {PA : Pack V n}, DenS V ξ A PA → PA.rel a b) {PB : Pack V n}
    (denB : DenS V ξ (inst0 a B) PB) : DenS V ξ (inst0 b B) PB := by
  obtain ⟨_, _, -, interprets⟩ := DenS.sigma_inv laws den
  exact interprets_cod_den laws interprets hab denB

/-- Pairs are related at a dependent pair type when their first components are
related at the domain and their second components are related at the codomain
instantiated at the first component. -/
theorem DenS.sigma_pair {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (den : DenS V ξ (.sigma A B) P)
    {a a' b b' : Tm Head n} (haa' : ∀ {PA : Pack V n}, DenS V ξ A PA → PA.rel a a')
    (hb : ∀ {PB : Pack V n}, DenS V ξ (inst0 a B) PB → PB.rel b b') :
    P.rel (.pair a b) (.pair a' b') := by
  obtain ⟨l, Q, rfl, interprets⟩ := DenS.sigma_inv laws den
  have domI : DenS V ξ A (Q.dom (Morph.id ξ)) := ⟨l, interprets.dom_id⟩
  have domE := domI.expansive laws
  have va := domI.refl_left laws (haa' domI)
  have fst : WhRed V.rules V.roles (.fst (.pair a b)) a := .single (.fstPair a b)
  have fst' : WhRed V.rules V.roles (.fst (.pair a' b')) a' := .single (.fstPair a' b')
  have fv : (Q.dom (Morph.id ξ)).Val (.fst (.pair a b)) := domE.left fst (domE.right fst va)
  have frel : (Q.dom (Morph.id ξ)).rel (.fst (.pair a b)) a := domE.left fst va
  refine ⟨fv, domE.left fst (domE.right fst' (haa' domI)), ?_⟩
  rw [interprets.codRespect (Morph.id ξ) fv va frel]
  have codI : DenS V ξ (inst0 a B) (Q.cod (Morph.id ξ) va) := ⟨l, interprets.cod_id va⟩
  have codE := codI.expansive laws
  exact codE.left (.single (.sndPair a b)) (codE.right (.single (.sndPair a' b')) (hb codI))

end Pairs

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
