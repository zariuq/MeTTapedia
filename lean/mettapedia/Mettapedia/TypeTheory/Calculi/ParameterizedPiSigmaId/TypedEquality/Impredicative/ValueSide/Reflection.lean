import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.InterpPER

/-!
# The daimon in every type, realizers of related values, shapes of universes

Every interpretation relates any two daimonic terms, when the interpretations
below read every daimonic type by the total pack, as the daimonic clause does
at every level:

* at a universe, daimonic types are read by the total pack at every world
  reached by a morphism, since renaming keeps them daimonic; they reduce to no
  universe, type constant or type former, so they are leaves, of one shape;
* at a dependent function type, daimonic functions applied to any arguments
  are daimonic, and at a dependent pair type the projections of daimonic pairs
  are daimonic, so the domain and codomain relate them;
* at an inductive type, daimonic terms are related as stuck on the daimon; at
  the codes, daimonic codes are neutral and share the neutral meaning;
* every other clause relates all terms.

In particular the daimon is a valid value of every type.

Related values have the same realizers, by the laws of the realizer algebra.
At a dependent function type, related functions have related results at every
valid argument, which have one realizer. At a dependent pair type,
related pairs have valid first projections on both sides, related first
projections with one realizer and one codomain, and related second
projections, so the meets over the validity of the two first projections are
meets of one candidate. At an inductive type, related terms have shapes with
one realizer each way, a term reducing to at most one listed constructor
spine, so the meets over their shapes agree. Every other clause realizes all
of its values alike.

The numbers are the inductive type with the constructors `zero` and `suc`:
the shapes of a number are those of the shapes of numbers, and its realizers
are the meet of the realizers of its shapes of numbers (`numIndPack_real`).

The universe relation carries shapes, which the packs of types do not
determine. For universes `u₀`, `u₁` of different levels, `Π u₀ ⋆` and `Π u₁ ⋆`
are still related in every universe above both, while their domains are not:
the class lemma fails. But the two universes are of no one shape, so the
clause of dependent function types never relates the two types: every shape
relating them makes both hereditarily total, and between hereditarily total
types the transport compares no domains (`shape_separates_universes`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph Truth)
open Realizability (Daimonic HasShape)
open StrongNormalization (NumShape)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

/-! ## Daimonic types are leaves -/

namespace Model.Laws

variable (laws : V.Laws)
include laws

/-- A daimonic type reduces to no dependent pair type. -/
theorem daimonic_not_sigma {n : Nat} {u : Tm Head n} (daimonic : Daimonic V.roles V.star u) :
    ∀ A B, ¬ WhRed V.rules V.roles u (.sigma A B) := fun A B r =>
  (laws.daimonic_not_former daimonic).2.2.1 A B (whRed_of_whnf (laws.daimonic_whnf daimonic) r).symm

/-- A daimonic type read by the total pack is a leaf. -/
theorem daimonic_leaf {I : IPack V} {n : Nat} {ξ : World V.reading n} {u : Tm Head n}
    (daimonic : Daimonic V.roles V.star u) (interp : I ξ u (Pack.total V n)) : Leaf V I ξ u where
  interp := ⟨_, interp, fun _ _ => trivial⟩
  notUniv := fun h r _ =>
    (laws.daimonic_not_former daimonic).1 h (whRed_of_whnf (laws.daimonic_whnf daimonic) r).symm
  notConst := fun _ hc r =>
    laws.daimonic_ne_typeConst daimonic hc (whRed_of_whnf (laws.daimonic_whnf daimonic) r).symm
  notPi := fun A B r =>
    (laws.daimonic_not_former daimonic).2.1 A B (whRed_of_whnf (laws.daimonic_whnf daimonic) r).symm

/-- Daimonic types read by the total pack are of one shape: both are
hereditarily total leaves. -/
theorem daimonic_shape {I : IPack V} {n : Nat} {ξ : World V.reading n} {u u' : Tm Head n}
    (daimonic : Daimonic V.roles V.star u) (daimonic' : Daimonic V.roles V.star u')
    (interp : I ξ u (Pack.total V n)) (interp' : I ξ u' (Pack.total V n)) :
    Shape V I .pair ξ u u' :=
  .total (.leaf (laws.daimonic_leaf daimonic interp) (laws.daimonic_not_sigma daimonic))
    (.leaf (laws.daimonic_leaf daimonic' interp') (laws.daimonic_not_sigma daimonic'))

end Model.Laws

/-! ## The daimon in every type -/

section Reflection

variable {l : L} {below : L → IPack V}

/-- Every interpretation relates daimonic terms, when the interpretations below
read every daimonic type by the total pack. -/
theorem SInterp.daimonic_related (laws : V.Laws)
    (belowDaimonic : ∀ k, k < l → ∀ {m : Nat} {ξ : World V.reading m} {u : Tm Head m},
      Daimonic V.roles V.star u → below k ξ u (Pack.total V m))
    {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ A P) :
    ∀ {d d' : Tm Head n}, Daimonic V.roles V.star d → Daimonic V.roles V.star d' →
      P.rel d d' := by
  induction interp with
  | sort _ level _ =>
      intro d d' daimonic daimonic' m ξ' ρ _
      have interp := belowDaimonic _ level (ξ := ξ') (daimonic.rename ρ)
      have interp' := belowDaimonic _ level (ξ := ξ') (daimonic'.rename ρ)
      exact ⟨Pack.total V m, interp, interp',
        laws.daimonic_shape (daimonic.rename ρ) (daimonic'.rename ρ) interp interp'⟩
  | ground => exact fun _ _ => trivial
  | pi _ _ _ _ _ _ codIH =>
      intro d d' daimonic daimonic' m ξ' ρ w a b ha _
      exact codIH w ha (.app (daimonic.rename ρ)) (.app (daimonic'.rename ρ))
  | sigma _ Q _ _ _ domIH codIH =>
      intro d d' daimonic daimonic'
      have fstVal : (Q.dom (Morph.id _)).Val (.fst d) :=
        domIH (Morph.id _) daimonic.fst daimonic.fst
      exact ⟨fstVal, domIH (Morph.id _) daimonic.fst daimonic'.fst,
        codIH (Morph.id _) fstVal daimonic.snd daimonic'.snd⟩
  | ident => exact fun _ _ => trivial
  | ind => exact fun daimonic daimonic' => .star .refl daimonic .refl daimonic'
  | prop =>
      exact fun daimonic daimonic' => ⟨_, .neutral .refl daimonic, .neutral .refl daimonic'⟩
  | holds => exact fun _ _ => trivial
  | rigid => exact fun _ _ => trivial
  | daimon => exact fun _ _ => trivial

/-- The daimon is a valid value of every type, when the interpretations below
read every daimonic type by the total pack. -/
theorem SInterp.star_val (laws : V.Laws)
    (belowDaimonic : ∀ k, k < l → ∀ {m : Nat} {ξ : World V.reading m} {u : Tm Head m},
      Daimonic V.roles V.star u → below k ξ u (Pack.total V m))
    {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ A P) : P.Val (.const V.star) :=
  interp.daimonic_related laws belowDaimonic .star .star

end Reflection

/-- The interpretations below a level read every daimonic type by the total
pack. -/
theorem levelsBelow_daimonic {l k : L} (lt : k < l) {n : Nat} {ξ : World V.reading n}
    {u : Tm Head n} (daimonic : Daimonic V.roles V.star u) :
    levelsBelow V l k ξ u (Pack.total V n) :=
  (levelsBelow_iff lt ξ u _).mpr (SInterp.daimon .refl daimonic)

/-- A type at a level relates daimonic terms. -/
theorem InterpAt.daimonic_related (laws : V.Laws) {l : L} {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {P : Pack V n} (interp : InterpAt V l ξ A P) {d d' : Tm Head n}
    (daimonic : Daimonic V.roles V.star d) (daimonic' : Daimonic V.roles V.star d') :
    P.rel d d' :=
  SInterp.daimonic_related laws (fun _ lt {_ _ _} => levelsBelow_daimonic lt) interp daimonic
    daimonic'

/-- **The daimon is a valid value of every type at every level.** -/
theorem InterpAt.star_val (laws : V.Laws) {l : L} {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {P : Pack V n} (interp : InterpAt V l ξ A P) : P.Val (.const V.star) :=
  interp.daimonic_related laws .star .star

/-! ## Realizers of related values -/

section Realizers

variable {n : Nat} {cs : List (DeclName × List (Field Head))}

/-- Terms related at an inductive type have shapes with one realizer: every
shape of the one is matched by a shape of the other. -/
theorem IndRel.shape_real (laws : V.Laws) {T : DeclName} (role : V.roles T = .inductive cs)
    {field : Tm Head 0 → Pack V n}
    (fieldReal : ∀ {F : Tm Head 0}, F ∈ closedFields cs → ∀ {a b : Tm Head n},
      (field F).rel a b → (field F).real a = (field F).real b)
    {t t' : Tm Head n} (related : IndRel V cs field t t') {s : IndShape Head n}
    (shape : HasIndShape V cs t s) :
    ∃ s', HasIndShape V cs t' s' ∧ s.real V T field = s'.real V T field := by
  have key : ∀ {t t' : Tm Head n}, IndRel V cs field t t' → ∀ {s : IndShape Head n},
      HasIndShape V cs t s →
        ∃ s', HasIndShape V cs t' s' ∧ s.real V T field = s'.real V T field := by
    intro t t' related
    refine IndRel.rec
      (motive_1 := fun t t' _ => ∀ {s : IndShape Head n}, HasIndShape V cs t s →
        ∃ s', HasIndShape V cs t' s' ∧ s.real V T field = s'.real V T field)
      (motive_2 := fun fs as as' _ => (∀ {F : Tm Head 0}, Field.closed F ∈ fs →
        F ∈ closedFields cs) →
          ∀ {fields : IndShapes Head n}, HasIndShapes V cs fs as fields →
          ∃ fields', HasIndShapes V cs fs as' fields' ∧
            IndShapes.reals V T field fields = IndShapes.reals V T field fields')
      ?_ ?_ ?_ ?_ ?_ related
    · intro k fs t t' as as' mem red red' _ ih s shape
      cases shape with
      | ctor mem₁ red₁ shapes₁ =>
          obtain ⟨rfl, rfl, rfl⟩ := laws.ctorSpine_unique role mem₁ mem red₁ red
          obtain ⟨fields', shapes', e⟩ := ih (fun hF => mem_closedFields mem₁ hF) shapes₁
          exact ⟨.ctor _ fields', .ctor mem₁ red' shapes', by simp only [IndShape.real, e]⟩
      | star red₁ daimonic₁ =>
          exact (laws.ctorSpine_not_daimonic role mem red red₁ daimonic₁).elim
    · intro t t' u u' red daimonic red' daimonic' s shape
      cases shape with
      | ctor mem₁ red₁ _ =>
          exact (laws.ctorSpine_not_daimonic role mem₁ red₁ red daimonic).elim
      | star _ _ => exact ⟨.star, .star red' daimonic', rfl⟩
    · intro _ fields shapes
      cases shapes
      exact ⟨.nil, .nil, rfl⟩
    · intro fs t t' as as' _ _ ihHead ihRest closed fields shapes
      cases shapes with
      | recursive shape rest =>
          obtain ⟨s', shape', e⟩ := ihHead shape
          obtain ⟨rest', restShapes', e'⟩ :=
            ihRest (fun hF => closed (List.mem_cons_of_mem _ hF)) rest
          exact ⟨.recursive s' rest', .recursive shape' restShapes',
            by simp only [IndShapes.reals, e, e']⟩
    · intro F fs t t' as as' hF _ ihRest closed fields shapes
      cases shapes with
      | closed rest =>
          obtain ⟨rest', restShapes', e'⟩ :=
            ihRest (fun hF' => closed (List.mem_cons_of_mem _ hF')) rest
          exact ⟨.closed F t' rest', .closed restShapes',
            by simp only [IndShapes.reals, fieldReal (closed List.mem_cons_self) hF, e']⟩
  exact key related shape

/-- Related values of an inductive type have one realizer, when those of its
closed field types do. -/
theorem indPack_real_eq (laws : V.Laws) {T : DeclName} (role : V.roles T = .inductive cs)
    {field : Tm Head 0 → Pack V n}
    (fieldSymm : ∀ {F : Tm Head 0}, F ∈ closedFields cs → ∀ {a b : Tm Head n},
      (field F).rel a b → (field F).rel b a)
    (fieldReal : ∀ {F : Tm Head 0}, F ∈ closedFields cs → ∀ {a b : Tm Head n},
      (field F).rel a b → (field F).real a = (field F).real b)
    {t t' : Tm Head n} (related : IndRel V cs field t t') :
    (indPack V T cs field).real t = (indPack V T cs field).real t' := by
  refine laws.alg.meet_congr _ _ (fun s => ?_) (fun s' => ?_)
  · obtain ⟨s', shape', e⟩ := IndRel.shape_real laws role fieldReal related s.2
    exact ⟨⟨s', shape'⟩, e⟩
  · obtain ⟨s, shape, e⟩ :=
      IndRel.shape_real laws role fieldReal (IndRel.symm fieldSymm related) s'.2
    exact ⟨⟨s, shape⟩, e.symm⟩

end Realizers

section RealizersAtLevel

variable {l : L} {below : L → IPack V}

/-- **Related values have the same realizers**, when the interpretations below
have the facts of an interpretation. -/
theorem SInterp.real_eq_of_rel (laws : V.Laws)
    (belowFacts : ∀ k, k < l → InterpFacts V (below k)) {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {P : Pack V n} (interp : SInterp V l below ξ A P) :
    ∀ {a b : Tm Head n}, P.rel a b → P.real a = P.real b := by
  induction interp with
  | sort => exact fun _ => rfl
  | ground => exact fun _ => rfl
  | pi _ Q _ _ _ _ codIH =>
      intro f g related
      show V.alg.piOver _ _ = V.alg.piOver _ _
      congr 1
      funext x
      exact codIH x.morph x.valid (related x.morph x.valid x.valid)
  | sigma _ Q domInterp _ codRespect domIH codIH =>
      rintro p q ⟨hp, hpq, hc⟩
      have hq : (Q.dom (Morph.id _)).Val (.fst q) :=
        ((domInterp (Morph.id _)).per laws belowFacts).refl_right hpq
      have same : ∀ (h : (Q.dom (Morph.id _)).Val (.fst p))
          (h' : (Q.dom (Morph.id _)).Val (.fst q)),
          V.alg.sigmaOver ((Q.dom (Morph.id _)).real (.fst p))
              ((Q.cod (Morph.id _) h).real (.snd p)) =
            V.alg.sigmaOver ((Q.dom (Morph.id _)).real (.fst q))
              ((Q.cod (Morph.id _) h').real (.snd q)) := by
        intro h h'
        have e := codRespect (Morph.id _) h h' hpq
        have sndRel : (Q.cod (Morph.id _) h').rel (.snd p) (.snd q) := by
          rw [← e]
          exact hc
        rw [domIH (Morph.id _) hpq, e, codIH (Morph.id _) h' sndRel]
      exact laws.alg.meet_congr _ _ (fun i => ⟨⟨hq⟩, same i.down hq⟩)
        (fun j => ⟨⟨hp⟩, same hp j.down⟩)
  | ident => exact fun _ => rfl
  | ind _ role _ fieldInterp fieldIH =>
      exact indPack_real_eq laws role
        (fun hF => ((fieldInterp hF).per laws belowFacts).symm) (fun hF => fieldIH hF)
  | prop => exact fun _ => rfl
  | holds => exact fun _ => rfl
  | rigid => exact fun _ => rfl
  | daimon => exact fun _ => rfl

end RealizersAtLevel

/-! ## The numbers -/

variable (V) in
/-- The shape of a value of the inductive type of the numbers for a shape of
numbers. -/
def numIndShape {n : Nat} : NumShape → IndShape Head n
  | .zero => .ctor V.zero .nil
  | .suc s => .ctor V.suc (.recursive (numIndShape s) .nil)
  | .star => .star

/-- The realizers of a shape of numbers are those of its inductive shape. -/
theorem numIndShape_real {n : Nat} (field : Tm Head 0 → Pack V n) (s : NumShape) :
    (numIndShape V s : IndShape Head n).real V V.num field =
      V.alg.numReal V.num V.zero V.suc s := by
  induction s with
  | zero => rfl
  | suc s ih =>
      simp only [numIndShape, IndShape.real, IndShapes.reals, ih, RealizerAlgebra.numReal]
  | star => rfl

/-- A term with a shape of numbers has its inductive shape. -/
theorem hasIndShape_num {n : Nat} {t : Tm Head n} {s : NumShape}
    (shape : HasShape V.toSetting V.star t s) :
    HasIndShape V (numConstructors V) t (numIndShape V s) := by
  induction shape with
  | zero red => exact .ctor (as := []) List.mem_cons_self red .nil
  | suc red _ ih =>
      exact .ctor (as := [_]) (List.mem_cons_of_mem _ List.mem_cons_self) red (.recursive ih .nil)
  | star red daimonic => exact .star red daimonic

/-- Every shape of a value of the numbers, as an inductive type, is the
inductive shape of one of its shapes of numbers. -/
theorem numShape_of_hasIndShape {n : Nat} {t : Tm Head n} {s : IndShape Head n}
    (shape : HasIndShape V (numConstructors V) t s) :
    ∃ ns, HasShape V.toSetting V.star t ns ∧ s = numIndShape V ns := by
  refine HasIndShape.rec
    (motive_1 := fun t s _ => ∃ ns, HasShape V.toSetting V.star t ns ∧ s = numIndShape V ns)
    (motive_2 := fun fs as fields _ => (fs = [] → as = [] ∧ fields = .nil) ∧
      (fs = [.recursive] → ∃ a ns, as = [a] ∧ HasShape V.toSetting V.star a ns ∧
        fields = .recursive (numIndShape V ns) .nil))
    ?_ ?_ ?_ ?_ ?_ shape
  · intro k fs t as fields mem red _ ih
    rcases List.mem_cons.mp mem with e | mem
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨rfl, rfl⟩ := ih.1 rfl
      exact ⟨.zero, .zero red, rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp mem)
      obtain ⟨a, ns, rfl, hns, rfl⟩ := ih.2 rfl
      exact ⟨.suc ns, .suc red hns, rfl⟩
  · intro t u red daimonic
    exact ⟨.star, .star red daimonic, rfl⟩
  · exact ⟨fun _ => ⟨rfl, rfl⟩, fun e => (by cases e)⟩
  · intro fs a as shape rest _ _ ihShape ihRest
    refine ⟨fun e => (by cases e), fun e => ?_⟩
    obtain ⟨-, rfl⟩ := List.cons.inj e
    obtain ⟨rfl, rfl⟩ := ihRest.1 rfl
    obtain ⟨ns, hns, rfl⟩ := ihShape
    exact ⟨a, ns, rfl, hns, rfl⟩
  · intro F fs a as rest _ _
    exact ⟨fun e => (by cases e), fun e => (by cases (List.cons.inj e).1)⟩

/-- The relation of the numbers, as an inductive type: terms with a common
shape of numbers. -/
theorem numIndPack_rel {n : Nat} {t t' : Tm Head n} :
    (numIndPack V n).rel t t' ↔
      ∃ s, HasShape V.toSetting V.star t s ∧ HasShape V.toSetting V.star t' s :=
  indRel_num_iff

/-- **The realizers of the numbers are the realizers of the shapes of
numbers**: the meet, over the shapes of numbers of a value, of the realizers
the algebra gives them. -/
theorem numIndPack_real (laws : V.Laws) {n : Nat} (a : Tm Head n) :
    (numIndPack V n).real a =
      V.alg.meet fun s : {s : NumShape // HasShape V.toSetting V.star a s} =>
        V.alg.numReal V.num V.zero V.suc s.1 := by
  refine laws.alg.meet_congr _ _ (fun s => ?_) (fun s => ?_)
  · obtain ⟨ns, hns, e⟩ := numShape_of_hasIndShape s.2
    refine ⟨⟨ns, hns⟩, ?_⟩
    rw [e]
    exact numIndShape_real _ ns
  · exact ⟨⟨numIndShape V s.1, hasIndShape_num s.2⟩, numIndShape_real _ s.1⟩

/-! ## Shapes separate universes -/

variable (V) in
/-- `Π u ⋆`: the dependent function type from the universe `u` into the
daimon. -/
def univStar {n : Nat} (u : Head) : Tm Head n :=
  .pi (.head u) (.const V.star)

/-- The family of `Π u ⋆` at level `l`, for `u` of level `k`: the universe of
level `k` at every world, and the total pack of the daimon. -/
def univStarFamily (l k : L) {n : Nat} (ξ : World V.reading n) : PiPack V ξ where
  dom := fun {_ ξ' _} _ => universePack V (levelsBelow V l k) ξ'
  cod := fun {m _ _} _ {_} _ => Pack.total V m

/-- `Π u ⋆` denotes the pack of its family at every level above `u`. -/
theorem interp_univStar {l : L} {u : Head} (hu : V.rules.isUniverse u)
    (lt : V.levels.level u < l) {n : Nat} (ξ : World V.reading n) :
    InterpAt V l ξ (univStar V u) (univStarFamily l (V.levels.level u) ξ).piPack :=
  SInterp.pi .refl _ (fun {_ _ _} _ => SInterp.sort hu lt .refl)
    (fun {_ _ _} _ {_} _ => SInterp.daimon .refl .star) (fun {_ _ _} _ {_ _} _ _ _ => rfl)

/-- The pack of `Π u ⋆` does not depend on the universe: it relates every pair,
and it is realized by the function space from the realizers of types to
`top`. -/
theorem univStar_piPack (laws : V.Laws) {l : L} {u : Head} (hu : V.rules.isUniverse u)
    (lt : V.levels.level u < l) {n : Nat} (ξ : World V.reading n) :
    (univStarFamily l (V.levels.level u) ξ).piPack =
      { rel := fun _ _ => True, real := fun _ => V.alg.arrow V.alg.univ V.alg.top } := by
  have star : ((univStarFamily l (V.levels.level u) ξ).dom (Morph.id ξ)).Val (.const V.star) :=
    InterpAt.star_val laws (SInterp.sort (below := levelsBelow V l) (ξ := ξ) hu lt .refl)
  unfold PiPack.piPack
  congr 1
  · funext f g
    exact propext ⟨fun _ => trivial, fun _ {_ _ _} _ {_ _} _ _ => trivial⟩
  · funext f
    exact laws.alg.piOver_congr _ _ _ _ (fun _ => ⟨(), rfl, rfl⟩)
      (fun _ => ⟨⟨_, ξ, idRen, Morph.id ξ, _, star⟩, rfl, rfl⟩)

/-- `Π u ⋆` is hereditarily total at every level above `u`: its domain is of
one shape with itself, and its codomain is a leaf. -/
theorem univStar_total (laws : V.Laws) {l : L} {u : Head} (hu : V.rules.isUniverse u)
    (lt : V.levels.level u < l) {n : Nat} (ξ : World V.reading n) :
    Shape V (InterpAt V l) .total ξ (univStar V u) (univStar V u) :=
  .totalPi .refl ⟨_, interp_univStar hu lt ξ⟩ (fun {_ _ _} _ => .univ .refl .refl hu hu rfl)
    fun {_ _ _} _ {_} _ {_} _ =>
      .leaf (laws.daimonic_leaf .star (SInterp.daimon .refl .star)) (laws.daimonic_not_sigma .star)

/-- **Shapes separate universes; the Π class lemma fails.** For universes `u₀`,
`u₁` of different levels and a level `k` above both:

* `Π u₀ ⋆` and `Π u₁ ⋆` are related in the universe of level `k`, while their
  domains are not: types related in a universe need not have related domains;
* over every interpretation, the two domains are of no one shape, so every
  shape relating the two types makes both hereditarily total: the clause of
  dependent function types, where the transport compares domains, never
  applies. -/
theorem shape_separates_universes (laws : V.Laws) {u₀ u₁ : Head}
    (hu₀ : V.rules.isUniverse u₀) (hu₁ : V.rules.isUniverse u₁)
    (lt : V.levels.level u₀ < V.levels.level u₁) {k : L} (lt' : V.levels.level u₁ < k)
    {n : Nat} (ξ : World V.reading n) :
    (universePack V (InterpAt V k) ξ).rel (univStar V u₀) (univStar V u₁) ∧
      ¬ (universePack V (InterpAt V k) ξ).rel (.head u₀) (.head u₁) ∧
      ∀ I : IPack V, ¬ Shape V I .pair ξ (.head u₀) (.head u₁) ∧
        (Shape V I .pair ξ (univStar V u₀) (univStar V u₁) →
          Shape V I .total ξ (univStar V u₀) (univStar V u₀) ∧
            Shape V I .total ξ (univStar V u₁) (univStar V u₁)) := by
  have lt₀ : V.levels.level u₀ < k := lt_trans lt lt'
  have separated : ∀ {m : Nat} {ζ : World V.reading m} (I : IPack V),
      ¬ Shape V I .pair ζ (.head u₀) (.head u₁) := fun I d => by
    obtain ⟨u', r, _, e⟩ := d.pair_head_left laws .refl hu₀
    cases whRed_of_whnf (head_whnf laws.shape _) r
    exact absurd e (ne_of_lt lt)
  refine ⟨fun {m ξ' ρ} _ => ?_, fun related => ?_, fun I => ⟨separated I, fun d => ?_⟩⟩
  · refine ⟨_, interp_univStar hu₀ lt₀ ξ', ?_,
      .total (univStar_total laws hu₀ lt₀ ξ') (univStar_total laws hu₁ lt' ξ')⟩
    rw [univStar_piPack laws hu₀ lt₀ ξ', ← univStar_piPack laws hu₁ lt' ξ']
    exact interp_univStar hu₁ lt' ξ'
  · obtain ⟨_, _, _, s⟩ := related (Morph.id ξ)
    exact separated _ s
  · rcases d.pair_pi_left laws .refl with totals | ⟨A', B', red', parts⟩
    · exact totals
    · cases whRed_of_whnf (pi_whnf laws.shape _ _) red'
      exact (separated I (parts.domShape (Morph.id ξ))).elim

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
