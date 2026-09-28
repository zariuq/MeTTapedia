import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Facts

/-!
# Denotations of types in the value model

A type's denotation is its pack at some level. Interpretations are cumulative,
so a type has at most one denotation. The denotation relation has the facts of
an interpretation (`DenS.facts`), so the laws of shapes and of the transport
hold over it: its value relations are partial equivalences, closed under
weak-head expansion of either side, carried along world morphisms, and related
values have one realizer; the daimon is a valid value of every denoted type;
denoted types reduce to type forms; and the relation of a universe grows with
its level.

A denotation of a type in normal form is given by the clause of its former:

* a dependent function or pair type, by a family of packs that interprets its
  domain and codomain at a level;
* a universe, by the universe pack over the interpretation at its level;
* an identity type, by the identity pack of the pack of its carrier;
* a simple inductive type, by its inductive pack over packs that denote its
  closed field types, and the numbers by the inductive pack of the numbers;
* the codes, by their meanings, and a decoding, by the meaning of its code.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph Truth)
open Realizability (Daimonic)

variable {Head L : Type} [LevelOrder L] {V : Model Head L}

variable (V) in
/-- The denotation of a type in a world: its pack at some level. -/
def DenS : IPack V := fun ⦃_⦄ ξ A P => ∃ l, InterpAt V l ξ A P

/-! ## Laws of denotations -/

section Laws

variable (laws : V.Laws)
include laws

/-- A type has at most one denotation. -/
theorem DenS.deterministic {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P P' : Pack V n}
    (first : DenS V ξ A P) (second : DenS V ξ A P') : P = P' := by
  obtain ⟨l, hl⟩ := first
  obtain ⟨l', hl'⟩ := second
  exact InterpAt.deterministic laws (hl.cumul (le_max_left l l')) (hl'.cumul (le_max_right l l'))

/-- Along a world morphism, a renamed type has a denotation that relates the
renamed terms. -/
theorem DenS.rename {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    ∃ P', DenS V ξ' (Presentation.rename ρ A) P' ∧ P.Renamed ρ P' := by
  obtain ⟨l, hl⟩ := den
  obtain ⟨P', h', renamed⟩ := hl.rename laws w
  exact ⟨P', ⟨l, h'⟩, renamed⟩

/-- The value relation of a denotation is closed under weak-head expansion of
either side. -/
theorem DenS.expansive {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) : P.Expansive := by
  obtain ⟨_, hl⟩ := den
  exact hl.expansive laws

/-- A type has the denotation of each of its weak-head reducts. -/
theorem DenS.reduce {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) (red : WhRed V.rules V.roles A A') : DenS V ξ A' P := by
  obtain ⟨l, hl⟩ := den
  exact ⟨l, SInterp.reduce laws hl red⟩

/-- The daimon is a valid value of every denoted type. -/
theorem DenS.star_val {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) : P.Val (.const V.star) := by
  obtain ⟨_, hl⟩ := den
  exact hl.star_val laws

/-- A denoted type relates daimonic terms. -/
theorem DenS.daimonic_related {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {P : Pack V n} (den : DenS V ξ A P) {d d' : Tm Head n}
    (daimonic : Daimonic V.roles V.star d) (daimonic' : Daimonic V.roles V.star d') :
    P.rel d d' := by
  obtain ⟨_, hl⟩ := den
  exact hl.daimonic_related laws daimonic daimonic'

/-- The value relation of a denotation is a partial equivalence. -/
theorem DenS.per {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) : P.IsPER := by
  obtain ⟨_, hl⟩ := den
  exact hl.per laws

/-- Related values of a denotation have one realizer. -/
theorem DenS.real_eq_of_rel {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) {a b : Tm Head n} (related : P.rel a b) : P.real a = P.real b := by
  obtain ⟨_, hl⟩ := den
  exact hl.real_eq_of_rel laws related

/-- **The denotation relation has the facts of an interpretation**, so the laws
of shapes hold over it. -/
theorem DenS.facts : InterpFacts V (DenS V) where
  deterministic := fun first second => DenS.deterministic laws first second
  symm := fun ⟨l, h⟩ => (InterpAt.facts laws l).symm h
  trans := fun ⟨l, h⟩ => (InterpAt.facts laws l).trans h
  expand := fun red ⟨l, h⟩ => ⟨l, InterpAt.expand red h⟩
  expandRel := fun ⟨l, h⟩ => (InterpAt.facts laws l).expandRel h
  rename := fun {_ _ _ _} ⟨l, h⟩ {_ _ _} w => by
    obtain ⟨P', h', renamed⟩ := InterpAt.rename laws h w
    exact ⟨P', ⟨l, h'⟩, renamed.rel⟩
  piPack := fun ⟨l, h⟩ red => by
    obtain ⟨Q, e, interprets⟩ := (InterpAt.facts laws l).piPack h red
    exact ⟨Q, e, interprets.mono fun h' => ⟨l, h'⟩⟩
  sigmaPack := fun ⟨l, h⟩ red => by
    obtain ⟨Q, e, interprets⟩ := (InterpAt.facts laws l).sigmaPack h red
    exact ⟨Q, e, interprets.mono fun h' => ⟨l, h'⟩⟩
  univPack := fun ⟨l, h⟩ red isUniverse =>
    (InterpAt.facts laws l).univPack h red isUniverse
  propPack := fun ⟨l, h⟩ red => (InterpAt.facts laws l).propPack h red
  indPack := fun ⟨l, h⟩ red role => by
    obtain ⟨field, e, fieldInterp⟩ := (InterpAt.facts laws l).indPack h red role
    exact ⟨field, e, fun hF => ⟨l, fieldInterp hF⟩⟩
  daimonic := fun ⟨l, h⟩ red daimonic =>
    (InterpAt.facts laws l).daimonic h red daimonic
  daimonicRel := fun ⟨_, h⟩ => h.daimonic_related laws
  realEq := fun ⟨_, h⟩ => h.real_eq_of_rel laws
  typeForm := fun ⟨_, h⟩ => SInterp.typeForm h
  univMono := fun {_ _ _ _ _ _ _ _} ⟨l, hX⟩ ⟨l', hZ⟩ rX rZ hu hu' le {_ _} related =>
    (InterpAt.facts laws (max l l')).univMono (hX.cumul (le_max_left l l'))
      (hZ.cumul (le_max_right l l')) rX rZ hu hu' le related

/-- The value relation of a denotation is symmetric. -/
theorem DenS.symm {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) {t u : Tm Head n} (h : P.rel t u) : P.rel u t :=
  (den.per laws).symm h

/-- The value relation of a denotation is transitive. -/
theorem DenS.trans {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) {t u v : Tm Head n} (h : P.rel t u) (h' : P.rel u v) : P.rel t v :=
  (den.per laws).trans h h'

/-- A value related to something by a denotation is valid. -/
theorem DenS.refl_left {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) {t u : Tm Head n} (h : P.rel t u) : P.Val t :=
  (den.per laws).refl_left h

/-- A value something is related to by a denotation is valid. -/
theorem DenS.refl_right {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (den : DenS V ξ A P) {t u : Tm Head n} (h : P.rel t u) : P.Val u :=
  (den.per laws).refl_right h

end Laws

/-- A type has the denotation of its weak-head reducts. -/
theorem DenS.expand {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n} {P : Pack V n}
    (red : WhRed V.rules V.roles A A') (den : DenS V ξ A' P) : DenS V ξ A P := by
  obtain ⟨l, hl⟩ := den
  exact ⟨l, InterpAt.expand red hl⟩

/-! ## The universe relation -/

/-- Types related by the universe relation over `I` have one pack and one shape
in the world itself. -/
theorem universePack_rel_self {I : IPack V} {n : Nat} {ξ : World V.reading n}
    {A B : Tm Head n} (related : (universePack V I ξ).rel A B) :
    ∃ P, I ξ A P ∧ I ξ B P ∧ Shape V I .pair ξ A B := by
  obtain ⟨P, hA, hB, s⟩ := related (Morph.id ξ)
  simp only [rename_id] at hA hB s
  exact ⟨P, hA, hB, s⟩

/-- A universe below a level denotes there the universe pack over the
interpretation at its own level. -/
theorem InterpAt.sort {l : L} {u : Head} (isUniverse : V.rules.isUniverse u)
    (lt : V.levels.level u < l) {n : Nat} (ξ : World V.reading n) :
    InterpAt V l ξ (.head u) (universePack V (InterpAt V (V.levels.level u)) ξ) := by
  have h : InterpAt V l ξ (.head u) (universePack V (levelsBelow V l (V.levels.level u)) ξ) :=
    SInterp.sort isUniverse lt .refl
  rwa [levelsBelow_eq lt] at h

/-- **A universe denotes the universe pack over the interpretation at its
level.** -/
theorem DenS.sort {u : Head} (isUniverse : V.rules.isUniverse u) {n : Nat}
    (ξ : World V.reading n) :
    DenS V ξ (.head u) (universePack V (InterpAt V (V.levels.level u)) ξ) :=
  ⟨_, InterpAt.sort isUniverse (LevelOrder.lt_succ (V.levels.level u)) ξ⟩

/-! ## Denotations of type formers -/

section Inversion

variable (laws : V.Laws)
include laws

/-- A dependent function type at a level denotes the functions of a family that
interprets its domain and codomain at that level. -/
theorem InterpAt.pi_inv {l : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (interp : InterpAt V l ξ (.pi A B) P) :
    ∃ Q : PiPack V ξ, P = Q.piPack ∧ Q.Interprets (InterpAt V l) A B :=
  SInterp.pi_inv laws interp .refl

/-- A dependent pair type at a level denotes the pairs of a family that
interprets its domain and codomain at that level. -/
theorem InterpAt.sigma_inv {l : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (interp : InterpAt V l ξ (.sigma A B) P) :
    ∃ Q : PiPack V ξ, P = Q.sigmaPack ∧ Q.Interprets (InterpAt V l) A B :=
  SInterp.sigma_inv laws interp .refl

/-- A dependent function type denotes the functions of a family that interprets
its domain and codomain at some level. -/
theorem DenS.pi_inv {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {B : Tm Head (n + 1)}
    {P : Pack V n} (den : DenS V ξ (.pi A B) P) :
    ∃ l, ∃ Q : PiPack V ξ, P = Q.piPack ∧ Q.Interprets (InterpAt V l) A B := by
  obtain ⟨l, interp⟩ := den
  exact ⟨l, InterpAt.pi_inv laws interp⟩

/-- A dependent pair type denotes the pairs of a family that interprets its
domain and codomain at some level. -/
theorem DenS.sigma_inv {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {P : Pack V n} (den : DenS V ξ (.sigma A B) P) :
    ∃ l, ∃ Q : PiPack V ξ, P = Q.sigmaPack ∧ Q.Interprets (InterpAt V l) A B := by
  obtain ⟨l, interp⟩ := den
  exact ⟨l, InterpAt.sigma_inv laws interp⟩

/-- A type that reduces to a universe denotes at a level the universe pack over
the interpretation at the universe's level, which is below. -/
theorem InterpAt.univ_inv {l : L} {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {u : Head}
    {P : Pack V n} (interp : InterpAt V l ξ X P) (red : WhRed V.rules V.roles X (.head u))
    (isUniverse : V.rules.isUniverse u) :
    V.levels.level u < l ∧ P = universePack V (InterpAt V (V.levels.level u)) ξ := by
  obtain ⟨lt, rfl⟩ := SInterp.univ_inv laws interp red isUniverse
  rw [levelsBelow_eq lt]
  exact ⟨lt, rfl⟩

/-- A type that reduces to a universe denotes the universe pack over the
interpretation at the universe's level. -/
theorem DenS.univ_inv {n : Nat} {ξ : World V.reading n} {X : Tm Head n} {u : Head}
    {P : Pack V n} (den : DenS V ξ X P) (red : WhRed V.rules V.roles X (.head u))
    (isUniverse : V.rules.isUniverse u) :
    P = universePack V (InterpAt V (V.levels.level u)) ξ := by
  obtain ⟨_, interp⟩ := den
  exact (InterpAt.univ_inv laws interp red isUniverse).2

/-- A head that is not a universe denotes the total pack. -/
theorem DenS.ground_inv {n : Nat} {ξ : World V.reading n} {h : Head} {P : Pack V n}
    (den : DenS V ξ (.head h) P) (notUniverse : ¬ V.rules.isUniverse h) : P = Pack.total V n := by
  obtain ⟨_, interp⟩ := den
  exact InterpAt.deterministic laws interp (SInterp.ground notUniverse .refl)

/-- An identity type denotes the identity pack of a denotation of its carrier,
at which its endpoints are valid. -/
theorem DenS.id_inv {n : Nat} {ξ : World V.reading n} {A a b : Tm Head n} {P : Pack V n}
    (den : DenS V ξ (.id A a b) P) :
    ∃ R : Pack V n, P = identPack R a b ∧ DenS V ξ A R ∧ R.Val a ∧ R.Val b := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨R, rfl, tyInterp, lhsVal, rhsVal⟩ := SInterp.id_inv laws interp .refl
  exact ⟨R, rfl, ⟨l, tyInterp⟩, lhsVal, rhsVal⟩

/-- An identity type relates every pair of terms. -/
theorem DenS.id_rel {n : Nat} {ξ : World V.reading n} {A a b : Tm Head n} {P : Pack V n}
    (den : DenS V ξ (.id A a b) P) (t u : Tm Head n) : P.rel t u := by
  obtain ⟨_, rfl, -, -, -⟩ := den.id_inv laws
  trivial

/-- An identity type is realized by the identity candidate of the relation of
its endpoints in the denotation of its carrier. -/
theorem DenS.id_real {n : Nat} {ξ : World V.reading n} {A a b : Tm Head n} {P : Pack V n}
    (den : DenS V ξ (.id A a b) P) {RA : Pack V n} (denA : DenS V ξ A RA) (t : Tm Head n) :
    P.real t = V.alg.ident (RA.rel a b) := by
  obtain ⟨R, rfl, denR, -, -⟩ := den.id_inv laws
  rw [DenS.deterministic laws denA denR]
  rfl

/-- A simple inductive type denotes its inductive pack, over packs that denote
its closed field types. -/
theorem DenS.ind_inv {n : Nat} {ξ : World V.reading n} {T : DeclName}
    {cs : List (DeclName × List (Field Head))} {P : Pack V n} (den : DenS V ξ (.const T) P)
    (role : V.roles T = .inductive cs) :
    ∃ field : Tm Head 0 → Pack V n, P = indPack V T cs field ∧
      ∀ {F : Tm Head 0}, F ∈ closedFields cs → DenS V ξ (liftClosed F) (field F) := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨field, rfl, fieldInterp⟩ := SInterp.ind_inv laws interp .refl role
  exact ⟨field, rfl, fun hF => ⟨l, fieldInterp hF⟩⟩

/-- **The numbers denote the inductive pack of the numbers.** -/
theorem DenS.num_inv {n : Nat} {ξ : World V.reading n} {P : Pack V n}
    (den : DenS V ξ (.const V.num) P) : P = numIndPack V n := by
  obtain ⟨l, interp⟩ := den
  exact InterpAt.deterministic laws interp (InterpAt.num laws l .refl)

/-- The numbers are denoted. -/
theorem DenS.num {n : Nat} (ξ : World V.reading n) : DenS V ξ (.const V.num) (numIndPack V n) :=
  ⟨LevelOrder.bot, InterpAt.num laws _ .refl⟩

/-- The codes denote the codes with one meaning. -/
theorem DenS.prop_inv {n : Nat} {ξ : World V.reading n} {P : Pack V n}
    (den : DenS V ξ (.const V.prop) P) : P = propPack V ξ := by
  obtain ⟨_, interp⟩ := den
  exact InterpAt.deterministic laws interp (SInterp.prop .refl)

/-- A decoding denotes the pack of the meaning of its code. -/
theorem DenS.holds_inv {n : Nat} {ξ : World V.reading n} {c : Tm Head n} {P : Pack V n}
    (den : DenS V ξ (.app (.const V.holds) c) P) :
    ∃ X : V.alg.Cand, Truth V.reading ξ c X ∧ P = holdsPack V n X := by
  obtain ⟨_, interp⟩ := den
  exact SInterp.holds_inv laws interp .refl

end Inversion

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
