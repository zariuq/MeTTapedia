import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.InterpLaws

/-!
# Partial equivalences, expansion, renaming and cumulativity

The value relation of a type at a level is:

* a partial equivalence, when the interpretations below have the facts of an
  interpretation (`InterpFacts`): at a universe, symmetry and transitivity of
  the universe relation are those of shapes (`Shape.symm`, `Shape.trans`);
* closed under weak-head expansion of either side, when the interpretations
  below are closed under weak-head expansion of types: at a universe, shapes
  are (`Shape.expand`);
* carried along world morphisms: a renamed type has a pack that relates the
  renamed terms. The realizers of a renamed value are no business of the
  value side's laws: inclusion of realizers is a membership fact of a model.

An interpretation at a level is one at every higher level whose
interpretations below agree with it. The interpretations below a level are
those at the lower levels (`levelsBelow_eq`); the facts of an interpretation
hold at every level, by induction over the level order, once the daimon and the
realizers of related values are in place (`Facts`).

The renamed pack of an inductive type reads its closed field types at the new
world. Their packs there are *described* rather than chosen: the pack
described by a property relates what every pack with the property relates and
is realized by the meet of their realizers, and a property of exactly one pack
describes that pack (`Pack.describe_eq`), by the law of meets of constant
families.

The laws at an inductive type use that its constructors are declared as
constructors (`ConstructorsDeclared`, a law of the value model): a term
reduces to at most one spine of a listed constructor, and to none when it
reduces to a daimonic term. The other laws of the value model do not give
this: a value model with all of them whose inductive type lists a computing
constant has an inductive relation that is not transitive
(`UndeclaredControl.interpAt_facts_needs_declared`).
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

/-! ## Laws of packs -/

/-- The value relation of a pack is a partial equivalence. -/
structure Pack.IsPER {n : Nat} (P : Pack V n) : Prop where
  symm : ∀ {t u : Tm Head n}, P.rel t u → P.rel u t
  trans : ∀ {t u v : Tm Head n}, P.rel t u → P.rel u v → P.rel t v

/-- A value related to something is valid. -/
theorem Pack.IsPER.refl_left {n : Nat} {P : Pack V n} (per : P.IsPER) {t u : Tm Head n}
    (h : P.rel t u) : P.Val t :=
  per.trans h (per.symm h)

/-- A value something is related to is valid. -/
theorem Pack.IsPER.refl_right {n : Nat} {P : Pack V n} (per : P.IsPER) {t u : Tm Head n}
    (h : P.rel t u) : P.Val u :=
  per.trans (per.symm h) h

/-- The value relation of a pack is closed under weak-head expansion of either
side. -/
structure Pack.Expansive {n : Nat} (P : Pack V n) : Prop where
  left : ∀ {t t' u : Tm Head n}, WhRed V.rules V.roles t t' → P.rel t' u → P.rel t u
  right : ∀ {t u u' : Tm Head n}, WhRed V.rules V.roles u u' → P.rel t u' → P.rel t u

/-- `P'` is a pack of a type renamed along `ρ` whose relation contains the
renamed pairs of that of `P`. -/
structure Pack.Renamed {n m : Nat} (P : Pack V n) (ρ : Ren n m) (P' : Pack V m) : Prop where
  rel : ∀ {a b : Tm Head n}, P.rel a b →
    P'.rel (Presentation.rename ρ a) (Presentation.rename ρ b)

/-- A renamed valid value is valid. -/
theorem Pack.Renamed.val {n m : Nat} {P : Pack V n} {ρ : Ren n m} {P' : Pack V m}
    (renamed : P.Renamed ρ P') {a : Tm Head n} (valid : P.Val a) :
    P'.Val (Presentation.rename ρ a) :=
  renamed.rel valid

/-! ## Described packs -/

variable (V) in
/-- The pack described by a property of packs: it relates what every pack with
the property relates, and realizes a value by the meet of their realizers. -/
def Pack.describe {n : Nat} (Q : Pack V n → Prop) : Pack V n where
  rel := fun a b => ∀ P, Q P → P.rel a b
  real := fun a => V.alg.meet fun P : {P : Pack V n // Q P} => P.1.real a

/-- **A property of exactly one pack describes that pack.** The meet of a
nonempty family of one candidate is that candidate, so no pack is chosen. -/
theorem Pack.describe_eq (alg : V.alg.Laws) {n : Nat} {Q : Pack V n → Prop} {P : Pack V n}
    (holds : Q P) (unique : ∀ P', Q P' → P' = P) : Pack.describe V Q = P := by
  cases P with
  | mk rel real =>
      unfold Pack.describe
      congr 1
      · funext a b
        refine propext ⟨fun h => h _ holds, fun h P' hP' => ?_⟩
        rw [unique P' hP']
        exact h
      · funext a
        exact alg.meet_const _ _ (fun P' => by rw [unique P'.1 P'.2]) ⟨⟨_, holds⟩⟩

/-! ## Families along a morphism -/

/-- A dependent function or pair family read from a world reached by a
morphism: its domain and codomain packs at every further world. -/
def PiPack.rename {n m : Nat} {ξ : World V.reading n} {ξ' : World V.reading m} {ρ : Ren n m}
    (P : PiPack V ξ) (w : Morph ξ ξ' ρ) : PiPack V ξ' where
  dom := fun {_ _ _} w' => P.dom (w.comp' w')
  cod := fun {_ _ _} w' {_} ha => P.cod (w.comp' w') ha

/-! ## Shapes under expansion -/

section ShapeExpand

variable {I : IPack V} (laws : V.Laws)
  (expandI : ∀ {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n} {P : Pack V n},
    WhRed V.rules V.roles A A' → I ξ A' P → I ξ A P)
include laws expandI

/-- A leaf is a leaf at each of its weak-head expansions. -/
theorem Leaf.expand {n : Nat} {ξ : World V.reading n} {X X' : Tm Head n}
    (red : WhRed V.rules V.roles X X') (leaf : Leaf V I ξ X') : Leaf V I ξ X where
  interp := by
    obtain ⟨P, hP, total⟩ := leaf.interp
    exact ⟨P, expandI red hP, total⟩
  notUniv := fun u r =>
    leaf.notUniv u (WhRed.to_whnf laws.shape r (head_whnf laws.shape _) red)
  notConst := fun c hc r =>
    leaf.notConst c hc (WhRed.to_whnf laws.shape r (hc.whnf laws) red)
  notPi := fun A B r =>
    leaf.notPi A B (WhRed.to_whnf laws.shape r (pi_whnf laws.shape _ _) red)

/-- A hereditarily total type is hereditarily total at each of its weak-head
expansions. -/
theorem Shape.expand_total {n : Nat} {ξ : World V.reading n} {X X' : Tm Head n}
    (red : WhRed V.rules V.roles X X') (total : Shape V I .total ξ X' X') :
    Shape V I .total ξ X X := by
  cases total with
  | leaf leaf notSigma =>
      exact .leaf (leaf.expand laws expandI red)
        (fun A B r => notSigma A B (WhRed.to_whnf laws.shape r (sigma_whnf laws.shape _ _) red))
  | totalPi r interp domShape codShape =>
      obtain ⟨P, hP⟩ := interp
      exact .totalPi (red.trans r) ⟨P, expandI red hP⟩ domShape codShape
  | totalSigma r interp domShape codShape =>
      obtain ⟨P, hP⟩ := interp
      exact .totalSigma (red.trans r) ⟨P, expandI red hP⟩ domShape codShape

/-- Types of one shape stay of one shape when the left one is replaced by a
term that weak-head reduces to it. -/
theorem Shape.expand_left {n : Nat} {ξ : World V.reading n} {X X' Y : Tm Head n}
    (red : WhRed V.rules V.roles X X') (d : Shape V I .pair ξ X' Y) : Shape V I .pair ξ X Y := by
  cases d with
  | total left right => exact .total (Shape.expand_total laws expandI red left) right
  | univ r r' hu hu' level => exact .univ (red.trans r) r' hu hu' level
  | const hc r r' => exact .const hc (red.trans r) r'
  | pi r r' domPacks domShape codPacks codShape =>
      exact .pi (red.trans r) r' domPacks domShape codPacks codShape
  | sigma r r' domPacks domShape codPacks codShape =>
      exact .sigma (red.trans r) r' domPacks domShape codPacks codShape

/-- Types of one shape stay of one shape when the right one is replaced by a
term that weak-head reduces to it. -/
theorem Shape.expand_right {n : Nat} {ξ : World V.reading n} {X Y Y' : Tm Head n}
    (red : WhRed V.rules V.roles Y Y') (d : Shape V I .pair ξ X Y') : Shape V I .pair ξ X Y := by
  cases d with
  | total left right => exact .total left (Shape.expand_total laws expandI red right)
  | univ r r' hu hu' level => exact .univ r (red.trans r') hu hu' level
  | const hc r r' => exact .const hc r (red.trans r')
  | pi r r' domPacks domShape codPacks codShape =>
      exact .pi r (red.trans r') domPacks domShape codPacks codShape
  | sigma r r' domPacks domShape codPacks codShape =>
      exact .sigma r (red.trans r') domPacks domShape codPacks codShape

/-- **Shapes are closed under weak-head expansion** of both types, when the
interpretation is. -/
theorem Shape.expand {n : Nat} {ξ : World V.reading n} {X X' Y Y' : Tm Head n}
    (red : WhRed V.rules V.roles X X') (red' : WhRed V.rules V.roles Y Y')
    (d : Shape V I .pair ξ X' Y') : Shape V I .pair ξ X Y :=
  Shape.expand_left laws expandI red (Shape.expand_right laws expandI red' d)

end ShapeExpand

/-! ## The universe relation -/

section Universe

variable {I : IPack V}

/-- The relation of a universe is a partial equivalence over an interpretation
with the facts: symmetric by symmetry of shapes, transitive by determinism and
transitivity of shapes. -/
theorem universePack_isPER (laws : V.Laws) (facts : InterpFacts V I) {n : Nat}
    (ξ : World V.reading n) : (universePack V I ξ).IsPER where
  symm := fun {_ _} h {_ _ _} w => by
    obtain ⟨P, hA, hB, s⟩ := h w
    exact ⟨P, hB, hA, s.symm facts⟩
  trans := fun {_ _ _} h h' {_ _ _} w => by
    obtain ⟨P, hA, hB, s⟩ := h w
    obtain ⟨P', hB', hC, s'⟩ := h' w
    obtain rfl := facts.deterministic hB hB'
    exact ⟨P, hA, hC, s.trans laws facts s' ⟨P, hA⟩ ⟨P, hC⟩⟩

/-- The relation of a universe is closed under weak-head expansion when the
interpretation is. -/
theorem universePack_expansive (laws : V.Laws)
    (expandI : ∀ {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n} {P : Pack V n},
      WhRed V.rules V.roles A A' → I ξ A' P → I ξ A P)
    {n : Nat} (ξ : World V.reading n) : (universePack V I ξ).Expansive where
  left := fun {_ _ _} red h {_ _ ρ} w => by
    obtain ⟨P, hA, hB, s⟩ := h w
    exact ⟨P, expandI (red.rename ρ) hA, hB, Shape.expand_left laws expandI (red.rename ρ) s⟩
  right := fun {_ _ _} red h {_ _ ρ} w => by
    obtain ⟨P, hA, hB, s⟩ := h w
    exact ⟨P, hA, expandI (red.rename ρ) hB, Shape.expand_right laws expandI (red.rename ρ) s⟩

/-- The universe relation at a world reached by a morphism contains the renamed
pairs of the universe relation. -/
theorem universePack_renamed {n m : Nat} {ξ : World V.reading n} {ξ' : World V.reading m}
    {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    (universePack V I ξ).Renamed ρ (universePack V I ξ') where
  rel := fun {_ _} h {_ _ _} w' => by
    simp only [rename_comp]
    exact h (w.comp' w')

end Universe

/-! ## Inductive types -/

section Inductive

variable {n : Nat} {cs : List (DeclName × List (Field Head))}

/-- The relation at an inductive type is symmetric when those of its closed
field types are. -/
theorem IndRel.symm {field : Tm Head 0 → Pack V n}
    (fieldSymm : ∀ {F : Tm Head 0}, F ∈ closedFields cs → ∀ {a b : Tm Head n},
      (field F).rel a b → (field F).rel b a)
    {t t' : Tm Head n} (related : IndRel V cs field t t') : IndRel V cs field t' t := by
  refine IndRel.rec (motive_1 := fun t t' _ => IndRel V cs field t' t)
    (motive_2 := fun fs as as' _ => (∀ {F : Tm Head 0}, Field.closed F ∈ fs →
      F ∈ closedFields cs) → IndFields V cs field fs as' as) ?_ ?_ ?_ ?_ ?_ related
  · intro k fs t t' as as' mem red red' _ ih
    exact .ctor mem red' red (ih fun hF => mem_closedFields mem hF)
  · intro t t' u u' red daimonic red' daimonic'
    exact .star red' daimonic' red daimonic
  · intro _
    exact .nil
  · intro fs t t' as as' _ _ ihHead ihRest closed
    exact .recursive ihHead (ihRest fun hF => closed (List.mem_cons_of_mem _ hF))
  · intro F fs t t' as as' hF _ ihRest closed
    exact .closed (fieldSymm (closed List.mem_cons_self) hF)
      (ihRest fun hF' => closed (List.mem_cons_of_mem _ hF'))

/-- The relation at an inductive type is transitive when those of its closed
field types are: a term reduces to at most one spine of a listed constructor,
with the listed fields, and to none when it reduces to a daimonic term. -/
theorem IndRel.trans (laws : V.Laws) {T : DeclName}
    (role : V.roles T = .inductive cs) {field : Tm Head 0 → Pack V n}
    (fieldTrans : ∀ {F : Tm Head 0}, F ∈ closedFields cs → ∀ {a b c : Tm Head n},
      (field F).rel a b → (field F).rel b c → (field F).rel a c)
    {t u v : Tm Head n} (first : IndRel V cs field t u) (second : IndRel V cs field u v) :
    IndRel V cs field t v := by
  have key : ∀ {t u : Tm Head n}, IndRel V cs field t u →
      ∀ {v : Tm Head n}, IndRel V cs field u v → IndRel V cs field t v := by
    intro t u first
    refine IndRel.rec
      (motive_1 := fun t u _ => ∀ {v : Tm Head n}, IndRel V cs field u v →
        IndRel V cs field t v)
      (motive_2 := fun fs as bs _ => (∀ {F : Tm Head 0}, Field.closed F ∈ fs →
        F ∈ closedFields cs) → ∀ {rs : List (Tm Head n)}, IndFields V cs field fs bs rs →
          IndFields V cs field fs as rs) ?_ ?_ ?_ ?_ ?_ first
    · intro k fs t u as bs mem red red' _ ih v second
      cases second with
      | ctor mem₂ red₂ red₂' fields₂ =>
          obtain ⟨rfl, rfl, rfl⟩ := laws.ctorSpine_unique role mem mem₂ red' red₂
          exact .ctor mem red red₂' (ih (fun hF => mem_closedFields mem hF) fields₂)
      | star red₂ daimonic₂ _ _ =>
          exact (laws.ctorSpine_not_daimonic role mem red' red₂ daimonic₂).elim
    · intro t u w w' red daimonic red' daimonic' v second
      cases second with
      | ctor mem₂ red₂ _ _ =>
          exact (laws.ctorSpine_not_daimonic role mem₂ red₂ red' daimonic').elim
      | star _ _ red₂' daimonic₂' => exact .star red daimonic red₂' daimonic₂'
    · intro _ rs fields
      exact fields
    · intro fs t u as bs _ _ ihHead ihRest closed rs second
      cases second with
      | recursive head₂ rest₂ =>
          exact .recursive (ihHead head₂)
            (ihRest (fun hF => closed (List.mem_cons_of_mem _ hF)) rest₂)
    · intro F fs t u as bs hF _ ihRest closed rs second
      cases second with
      | closed hF₂ rest₂ =>
          exact .closed (fieldTrans (closed List.mem_cons_self) hF hF₂)
            (ihRest (fun hF' => closed (List.mem_cons_of_mem _ hF')) rest₂)
  exact key first second

/-- Related terms at an inductive type stay related when the left one is
replaced by a term that weak-head reduces to it. -/
theorem IndRel.expand_left {field : Tm Head 0 → Pack V n} {t t' u : Tm Head n}
    (red : WhRed V.rules V.roles t t') (related : IndRel V cs field t' u) :
    IndRel V cs field t u := by
  cases related with
  | ctor mem r r' fields => exact .ctor mem (red.trans r) r' fields
  | star r daimonic r' daimonic' => exact .star (red.trans r) daimonic r' daimonic'

/-- Related terms at an inductive type stay related when the right one is
replaced by a term that weak-head reduces to it. -/
theorem IndRel.expand_right {field : Tm Head 0 → Pack V n} {t u u' : Tm Head n}
    (red : WhRed V.rules V.roles u u') (related : IndRel V cs field t u') :
    IndRel V cs field t u := by
  cases related with
  | ctor mem r r' fields => exact .ctor mem r (red.trans r') fields
  | star r daimonic r' daimonic' => exact .star r daimonic (red.trans r') daimonic'

/-- Along a renaming, related terms at an inductive type are related renamed,
when the renamed packs of its closed field types relate the renamed values. -/
theorem IndRel.rename {m : Nat} (ρ : Ren n m) {field : Tm Head 0 → Pack V n}
    {field' : Tm Head 0 → Pack V m}
    (fieldRename : ∀ {F : Tm Head 0}, F ∈ closedFields cs → ∀ {a b : Tm Head n},
      (field F).rel a b → (field' F).rel (Presentation.rename ρ a) (Presentation.rename ρ b))
    {t t' : Tm Head n} (related : IndRel V cs field t t') :
    IndRel V cs field' (Presentation.rename ρ t) (Presentation.rename ρ t') := by
  refine IndRel.rec
    (motive_1 := fun t t' _ =>
      IndRel V cs field' (Presentation.rename ρ t) (Presentation.rename ρ t'))
    (motive_2 := fun fs as as' _ => (∀ {F : Tm Head 0}, Field.closed F ∈ fs →
      F ∈ closedFields cs) →
        IndFields V cs field' fs (as.map (Presentation.rename ρ))
          (as'.map (Presentation.rename ρ)))
    ?_ ?_ ?_ ?_ ?_ related
  · intro k fs t t' as as' mem red red' _ ih
    have r := red.rename ρ
    have r' := red'.rename ρ
    rw [rename_appSpine] at r r'
    exact .ctor mem r r' (ih fun hF => mem_closedFields mem hF)
  · intro t t' u u' red daimonic red' daimonic'
    exact .star (red.rename ρ) (daimonic.rename ρ) (red'.rename ρ) (daimonic'.rename ρ)
  · intro _
    exact .nil
  · intro fs t t' as as' _ _ ihHead ihRest closed
    exact .recursive ihHead (ihRest fun hF => closed (List.mem_cons_of_mem _ hF))
  · intro F fs t t' as as' hF _ ihRest closed
    exact .closed (fieldRename (closed List.mem_cons_self) hF)
      (ihRest fun hF' => closed (List.mem_cons_of_mem _ hF'))

end Inductive

/-! ## Partial equivalence -/

variable {l : L} {below : L → IPack V}

/-- **The value relation of a type is a partial equivalence** when the
interpretations below have the facts of an interpretation. -/
theorem SInterp.per (laws : V.Laws)
    (belowFacts : ∀ k, k < l → InterpFacts V (below k)) {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {P : Pack V n} (interp : SInterp V l below ξ A P) : P.IsPER := by
  induction interp with
  | sort _ level _ => exact universePack_isPER laws (belowFacts _ level) _
  | ground => exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | pi _ Q _ _ codRespect domIH codIH =>
      refine ⟨fun {f g} h => ?_, fun {f g k} hfg hgk => ?_⟩
      · intro m ξ' ρ w a b ha hab
        have hb : (Q.dom w).Val b := (domIH w).refl_right hab
        rw [codRespect w ha hb hab]
        exact (codIH w hb).symm (h w hb ((domIH w).symm hab))
      · intro m ξ' ρ w a b ha hab
        exact (codIH w ha).trans (hfg w ha ha) (hgk w ha hab)
  | sigma _ Q _ _ codRespect domIH codIH =>
      refine ⟨fun {p q} h => ?_, fun {p q r} h h' => ?_⟩
      · obtain ⟨hp, hpq, hc⟩ := h
        have hq : (Q.dom (Morph.id _)).Val (.fst q) := (domIH _).refl_right hpq
        refine ⟨hq, (domIH _).symm hpq, ?_⟩
        rw [← codRespect (Morph.id _) hp hq hpq]
        exact (codIH (Morph.id _) hp).symm hc
      · obtain ⟨hp, hpq, hc⟩ := h
        obtain ⟨hq, hqr, hc'⟩ := h'
        refine ⟨hp, (domIH _).trans hpq hqr, ?_⟩
        have e := codRespect (Morph.id _) hp hq hpq
        rw [e] at hc ⊢
        exact (codIH (Morph.id _) hq).trans hc hc'
  | ident => exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | ind _ role _ _ fieldIH =>
      exact ⟨IndRel.symm fun hF => (fieldIH hF).symm,
        IndRel.trans laws role fun hF => (fieldIH hF).trans⟩
  | prop =>
      refine ⟨?_, ?_⟩
      · rintro t u ⟨X, ht, hu⟩
        exact ⟨X, hu, ht⟩
      · rintro t u v ⟨X, ht, hu⟩ ⟨X', hu', hv⟩
        obtain rfl := Consistency.Truth.deterministic laws.reading hu hu'
        exact ⟨X, ht, hv⟩
  | holds => exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | rigid => exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | daimon => exact ⟨fun _ => trivial, fun _ _ => trivial⟩

/-! ## Expansion of related terms -/

/-- **The value relation of a type is closed under weak-head expansion** of
either side when the interpretations below are closed under weak-head
expansion of types. -/
theorem SInterp.expandRel (laws : V.Laws)
    (belowExpand : ∀ k, k < l → ∀ {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n}
      {P : Pack V n}, WhRed V.rules V.roles A A' → below k ξ A' P → below k ξ A P)
    {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n}
    (interp : SInterp V l below ξ A P) : P.Expansive := by
  induction interp with
  | sort _ level _ => exact universePack_expansive laws (belowExpand _ level) _
  | ground => exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | pi _ Q _ _ _ _ codIH =>
      refine ⟨fun {f f' g} red h => ?_, fun {f g g'} red h => ?_⟩
      · intro m ξ' ρ w a b ha hab
        exact (codIH w ha).left ((red.rename ρ).app a) (h w ha hab)
      · intro m ξ' ρ w a b ha hab
        exact (codIH w ha).right ((red.rename ρ).app b) (h w ha hab)
  | sigma _ Q _ _ codRespect domIH codIH =>
      refine ⟨fun {p p' q} red h => ?_, fun {p q q'} red h => ?_⟩
      · obtain ⟨hp', hpq, hc⟩ := h
        have hpp' : (Q.dom (Morph.id _)).rel (.fst p) (.fst p') := (domIH _).left red.fst hp'
        have hp : (Q.dom (Morph.id _)).Val (.fst p) := (domIH _).right red.fst hpp'
        refine ⟨hp, (domIH _).left red.fst hpq, ?_⟩
        rw [codRespect (Morph.id _) hp hp' hpp']
        exact (codIH (Morph.id _) hp').left red.snd hc
      · obtain ⟨hp, hpq', hc⟩ := h
        exact ⟨hp, (domIH _).right red.fst hpq', (codIH (Morph.id _) hp).right red.snd hc⟩
  | ident => exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | ind => exact ⟨IndRel.expand_left, IndRel.expand_right⟩
  | prop =>
      refine ⟨?_, ?_⟩
      · rintro t t' u red ⟨X, ht, hu⟩
        exact ⟨X, ht.expand red, hu⟩
      · rintro t u u' red ⟨X, ht, hu⟩
        exact ⟨X, ht, hu.expand red⟩
  | holds => exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | rigid => exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | daimon => exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩

/-! ## Renaming along world morphisms -/

/-- **Along a world morphism, a renamed type has an interpretation at the same
level that relates the renamed terms.** -/
theorem SInterp.rename (laws : V.Laws) {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {P : Pack V n} (interp : SInterp V l below ξ A P) :
    ∀ {m : Nat} {ξ' : World V.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∃ P', SInterp V l below ξ' (Presentation.rename ρ A) P' ∧ P.Renamed ρ P' := by
  induction interp with
  | sort isUniverse level red =>
      intro m ξ' ρ w
      exact ⟨_, .sort isUniverse level (red.rename ρ), universePack_renamed w⟩
  | ground notUniverse red =>
      intro m ξ' ρ w
      exact ⟨_, .ground notUniverse (red.rename ρ), ⟨fun _ => trivial⟩⟩
  | pi red P domInterp codInterp codRespect =>
      intro m ξ' ρ w
      refine ⟨_, .pi (red.rename ρ) (P.rename w) ?_ ?_ ?_, ⟨?_⟩⟩
      · intro k ξ'' ρ' w'
        rw [rename_comp]
        exact domInterp (w.comp' w')
      · intro k ξ'' ρ' w' a ha
        rw [rename_rename_lift]
        exact codInterp (w.comp' w') ha
      · intro k ξ'' ρ' w' a b ha hb hab
        exact codRespect (w.comp' w') ha hb hab
      · intro f g h k ξ'' ρ' w' a b ha hab
        simp only [rename_comp]
        exact h (w.comp' w') ha hab
  | @sigma n ξ A dom cod red P domInterp codInterp codRespect domIH codIH =>
      intro m ξ' ρ w
      -- The domain and codomain packs at `ξ`, renamed, are those at `ξ'`.
      have domR : (P.dom (Morph.id ξ)).Renamed ρ (P.dom w) := by
        obtain ⟨D, domI, domR⟩ := domIH (Morph.id ξ) w
        rw [rename_id] at domI
        obtain rfl : D = P.dom w := domI.deterministic laws (domInterp w)
        exact domR
      have codR : ∀ {a : Tm Head n} (ha : (P.dom (Morph.id ξ)).Val a)
          (ha' : (P.dom w).Val (Presentation.rename ρ a)),
          (P.cod (Morph.id ξ) ha).Renamed ρ (P.cod w ha') := by
        intro a ha ha'
        obtain ⟨C, codI, codR⟩ := codIH (Morph.id ξ) ha w
        rw [rename_inst0, liftRen_id, rename_id] at codI
        obtain rfl : C = P.cod w ha' := codI.deterministic laws (codInterp w ha')
        exact codR
      refine ⟨_, .sigma (red.rename ρ) (P.rename w) ?_ ?_ ?_, ⟨?_⟩⟩
      · intro k ξ'' ρ' w'
        rw [rename_comp]
        exact domInterp (w.comp' w')
      · intro k ξ'' ρ' w' a ha
        rw [rename_rename_lift]
        exact codInterp (w.comp' w') ha
      · intro k ξ'' ρ' w' a b ha hb hab
        exact codRespect (w.comp' w') ha hb hab
      · rintro p q ⟨hp, hpq, hc⟩
        have hp' := domR.val hp
        exact ⟨hp', domR.rel hpq, (codR hp hp').rel hc⟩
  | ident red R _ lhsVal rhsVal tyIH =>
      intro m ξ' ρ w
      obtain ⟨R', tyI, tyR⟩ := tyIH w
      exact ⟨_, .ident (red.rename ρ) R' tyI (tyR.val lhsVal) (tyR.val rhsVal),
        ⟨fun _ => trivial⟩⟩
  | @ind n ξ A T cs red role field fieldInterp fieldIH =>
      intro m ξ' ρ w
      -- The packs of the closed field types at `ξ'` are described, not chosen.
      have fieldAt : ∀ {F : Tm Head 0}, F ∈ closedFields cs →
          SInterp V l below ξ' (liftClosed F)
              (Pack.describe V fun Q => SInterp V l below ξ' (liftClosed F) Q) ∧
            (field F).Renamed ρ
              (Pack.describe V fun Q => SInterp V l below ξ' (liftClosed F) Q) := by
        intro F hF
        obtain ⟨P', hP', renamed⟩ := fieldIH hF w
        rw [rename_liftClosed] at hP'
        rw [Pack.describe_eq laws.alg hP' fun Q hQ => hQ.deterministic laws hP']
        exact ⟨hP', renamed⟩
      exact ⟨_, .ind (red.rename ρ) role
          (fun F => Pack.describe V fun Q => SInterp V l below ξ' (liftClosed F) Q)
          (fun hF => (fieldAt hF).1),
        ⟨IndRel.rename ρ fun hF => (fieldAt hF).2.rel⟩⟩
  | prop red =>
      intro m ξ' ρ w
      refine ⟨_, .prop (red.rename ρ), ⟨?_⟩⟩
      rintro a b ⟨X, ha, hb⟩
      exact ⟨X, ha.rename w, hb.rename w⟩
  | holds red truth =>
      intro m ξ' ρ w
      exact ⟨_, .holds (red.rename ρ) (truth.rename w), ⟨fun _ => trivial⟩⟩
  | rigid red role notProp notHolds =>
      intro m ξ' ρ w
      have red' := red.rename ρ
      rw [rename_appSpine] at red'
      exact ⟨_, .rigid red' role notProp notHolds, ⟨fun _ => trivial⟩⟩
  | daimon red daimonic =>
      intro m ξ' ρ w
      exact ⟨_, .daimon (red.rename ρ) (daimonic.rename ρ), ⟨fun _ => trivial⟩⟩

/-! ## Cumulativity -/

/-- **An interpretation at a level is one at every higher level** whose
interpretations below agree with it. -/
theorem SInterp.cumul {l l' : L} (le : l ≤ l') {below below' : L → IPack V}
    (agree : ∀ k, k < l → ∀ {n : Nat} (ξ : World V.reading n) (A : Tm Head n) (P : Pack V n),
      below k ξ A P ↔ below' k ξ A P)
    {n : Nat} {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n} :
    SInterp V l below ξ A P → SInterp V l' below' ξ A P := by
  intro interp
  induction interp with
  | @sort n ξ A u isUniverse level red =>
      have same : below (V.levels.level u) = below' (V.levels.level u) := by
        funext m ξ' B Q
        exact propext (agree _ level ξ' B Q)
      rw [same]
      exact .sort isUniverse (lt_of_lt_of_le level le) red
  | ground notUniverse red => exact .ground notUniverse red
  | pi red P _ _ codRespect domIH codIH => exact .pi red P domIH codIH codRespect
  | sigma red P _ _ codRespect domIH codIH => exact .sigma red P domIH codIH codRespect
  | ident red R _ lhsVal rhsVal tyIH => exact .ident red R tyIH lhsVal rhsVal
  | ind red role field _ fieldIH => exact .ind red role field fieldIH
  | prop red => exact .prop red
  | holds red truth => exact .holds red truth
  | rigid red role notProp notHolds => exact .rigid red role notProp notHolds
  | daimon red daimonic => exact .daimon red daimonic

/-! ## The interpretations below a level -/

/-- Only levels below `l` are interpreted below `l`. -/
theorem levelsBelow_lt {l k : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {P : Pack V n} (h : levelsBelow V l k ξ A P) : k < l := by
  rcases lt_or_ge k l with lt | ge
  · exact lt
  · exact absurd h (levelsBelow_of_not_lt (not_lt.mpr ge) ξ A P)

/-- **Below `l`, a lower level is read by the interpretation at that level.** -/
theorem levelsBelow_eq {l k : L} (h : k < l) : levelsBelow V l k = InterpAt V k := by
  unfold levelsBelow InterpAt
  rw [UniverseLevel.below_of_lt _ _ h]
  rfl

/-- The interpretations below a level are deterministic. -/
theorem levelsBelow_deterministic (laws : V.Laws) {l : L} (k : L) {n : Nat}
    {ξ : World V.reading n} {A : Tm Head n} {P P' : Pack V n} (first : levelsBelow V l k ξ A P)
    (second : levelsBelow V l k ξ A P') : P = P' := by
  have lt := levelsBelow_lt first
  rw [levelsBelow_eq lt] at first second
  exact SInterp.deterministic laws first second

/-- The interpretations below a level are closed under weak-head expansion of
types. -/
theorem levelsBelow_expand {l : L} (k : L) {n : Nat} {ξ : World V.reading n}
    {A A' : Tm Head n} {P : Pack V n} (red : WhRed V.rules V.roles A A')
    (h : levelsBelow V l k ξ A' P) : levelsBelow V l k ξ A P := by
  have lt := levelsBelow_lt h
  rw [levelsBelow_eq lt] at h ⊢
  exact SInterp.expand red h

/-! ## Laws at a level -/

section Levels

variable (laws : V.Laws)

include laws in
/-- A type has at most one interpretation at a level. -/
theorem InterpAt.deterministic {l : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {P P' : Pack V n} (first : InterpAt V l ξ A P) (second : InterpAt V l ξ A P') : P = P' :=
  SInterp.deterministic laws first second

include laws in
/-- The value relation of a type at a level is closed under weak-head expansion
of either side. -/
theorem InterpAt.expansive {l : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {P : Pack V n} (interp : InterpAt V l ξ A P) : P.Expansive :=
  SInterp.expandRel (below := levelsBelow V l) laws
    (fun k _ {_ _ _ _ _} red h => levelsBelow_expand k red h) interp

include laws in
/-- Along a world morphism, a renamed type has an interpretation at the same
level that relates the renamed terms. -/
theorem InterpAt.rename {l : L} {n : Nat} {ξ : World V.reading n} {A : Tm Head n}
    {P : Pack V n} (interp : InterpAt V l ξ A P) {m : Nat} {ξ' : World V.reading m}
    {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    ∃ P', InterpAt V l ξ' (Presentation.rename ρ A) P' ∧ P.Renamed ρ P' :=
  SInterp.rename laws interp w

end Levels

/-- A type has the interpretation at a level of its weak-head reducts. -/
theorem InterpAt.expand {l : L} {n : Nat} {ξ : World V.reading n} {A A' : Tm Head n}
    {P : Pack V n} (red : WhRed V.rules V.roles A A') (interp : InterpAt V l ξ A' P) :
    InterpAt V l ξ A P :=
  SInterp.expand red interp

/-- **An interpretation at a level is one at every higher level.** -/
theorem InterpAt.cumul {k l : L} (le : k ≤ l) {n : Nat} {ξ : World V.reading n}
    {A : Tm Head n} {P : Pack V n} (interp : InterpAt V k ξ A P) : InterpAt V l ξ A P :=
  SInterp.cumul le (fun _ lt {_} ξ A P =>
    (levelsBelow_iff lt ξ A P).trans (levelsBelow_iff (lt_of_lt_of_le lt le) ξ A P).symm) interp

/-- Below `l`, an interpretation at a lower level is one at every higher level
below `l`. -/
theorem levelsBelow_mono {l k k' : L} (le : k ≤ k') (lt : k' < l) {n : Nat}
    {ξ : World V.reading n} {A : Tm Head n} {P : Pack V n} (h : levelsBelow V l k ξ A P) :
    levelsBelow V l k' ξ A P := by
  have lt₀ := levelsBelow_lt h
  rw [levelsBelow_eq lt₀] at h
  rw [levelsBelow_eq lt]
  exact h.cumul le

/-! ## Constructors must be declared

The laws at an inductive type read its listed constructors as constructors: a
term reduces to at most one of their spines, and not both to such a spine and
to a daimonic term. That is why `Model.Laws` declares them: without that law
the relation of an inductive type need not be transitive, in a value model
with every other law. In the package below, the inductive type `T` lists the
constant `k`, which computes (`k x ⟶ x`). The pack of `T` relates `k 0` to
`k ⋆` (one listed constructor, the fields related at a total type) and `k ⋆`
to `⋆` (both reduce to the daimon), but not `k 0` to `⋆`: `k 0` reduces to
`0`, which is neither a spine of `k` nor daimonic. -/

namespace UndeclaredControl

/-- The constants of the package, by number: `0`, `suc`, `imp`, the numbers,
the codes, the decoder, the daimon, `T`, `k`, and a rigid type `R`, numbered
`0` to `9`. -/
def name (i : Nat) : DeclName := .num .anonymous i

/-- The one computation of the package: `k x ⟶ x`. -/
def computation : RootComputation Empty where
  step := fun t u => ∃ x, t = .app (.const (name 8)) x ∧ u = x
  rename := fun {_ _} ρ {_ _} ⟨x, e, e'⟩ =>
    ⟨Presentation.rename ρ x, by subst e; rfl, by subst e'; rfl⟩
  substitute := fun {_ _} σ {_ _} ⟨x, e, e'⟩ =>
    ⟨subst σ x, by subst e; rfl, by subst e'; rfl⟩

/-- The roles: `0`, `suc` and `imp` are constructors; the numbers and `T` are
inductive, `T` listing `k` with one field of type `R`; `k` computes; every
other constant is rigid. -/
def roles : Roles Empty
  | .num .anonymous 0 => .constructor 0
  | .num .anonymous 1 => .constructor 1
  | .num .anonymous 2 => .constructor 2
  | .num .anonymous 3 => .inductive [(name 0, []), (name 1, [.recursive])]
  | .num .anonymous 7 => .inductive [(name 8, [.closed (.const (name 9))])]
  | .num .anonymous 8 => .computes 1 .leaf
  | _ => .rigid

/-- The package: no heads, and the computation of `k`. -/
def rules : Rules Empty where
  headTyping := fun _ _ => False
  isUniverse := fun _ => False
  join := fun _ _ _ => False
  cumulative := fun _ _ => False
  headEq := fun _ _ => False
  computation := computation

theorem rootShape : RootShape rules roles where
  spine := fun {_ _ _} ⟨x, e, _⟩ => ⟨name 8, 1, .leaf, [x], rfl, e, rfl, .leaf _⟩
  deterministic := fun {_ _ _ _} ⟨x, e, e'⟩ ⟨y, f, f'⟩ => by
    subst e' f'
    rw [e] at f
    exact (Tm.app.inj f).2

/-- The setting of the package: no quantifiers or equations. -/
def setting : Consistency.Setting Empty where
  rules := rules
  roles := roles
  zero := name 0
  suc := name 1
  imp := name 2
  allCarrier := fun _ => none
  eqCarrier := fun _ => none

theorem setting_laws : setting.Laws where
  shape := rootShape
  zero := rfl
  suc := rfl
  imp := rfl
  all := fun h => nomatch h
  eq := fun h => nomatch h
  impNotEq := rfl

/-- The levels of the package: it has no universes. -/
def levelModel : LevelModel rules ℕ where
  level := fun _ => 0
  successor := fun hu => False.elim hu
  universe_typing := fun hu _ => False.elim hu
  ground_typing := fun h => False.elim h
  cumulative_universe := fun h => False.elim h
  headEq_level := fun h => False.elim h
  join_level := fun h => False.elim h
  join_exists := fun hu _ => False.elim hu
  join_upper := fun h => False.elim h
  cumulative_refl := fun hu => False.elim hu
  headEq_symm := fun h => False.elim h
  headEq_trans := fun h _ => False.elim h
  universe_decided := fun _ => .inr id

/-- The realizer algebra with one candidate. -/
def unitAlgebra : RealizerAlgebra Empty where
  Cand := Unit
  top := ()
  univ := ()
  codes := ()
  meet := fun _ => ()
  piOver := fun _ _ => ()
  sigmaOver := fun _ _ => ()
  ident := fun _ => ()
  ctorReal := fun _ _ _ => ()
  stuckReal := fun _ => ()

theorem unitAlgebra_laws : unitAlgebra.Laws where
  meet_const := fun _ _ _ _ => rfl
  meet_congr := fun _ _ _ _ => rfl
  piOver_congr := fun _ _ _ _ _ _ => rfl

/-- The value model of the package, with the daimon `name 6`. -/
def model : Model Empty Nat where
  toSetting := setting
  num := name 3
  prop := name 4
  holds := name 5
  levels := levelModel
  star := name 6
  alg := unitAlgebra

/-- The value model has every law but the declared constructors: those of the
consistency model, the daimon rigid and distinct from the codes and the
decoder, and the laws of the algebra. -/
theorem model_laws_but_declared :
    model.toModel.Laws ∧ model.roles model.star = .rigid ∧ model.star ≠ model.prop ∧
      model.star ≠ model.holds ∧ model.alg.Laws :=
  ⟨⟨setting_laws, rfl, rfl, rfl⟩, rfl, by decide, by decide, unitAlgebra_laws⟩

/-- The constructors `T` lists are not declared: `k` computes. -/
theorem not_declared : ¬ ConstructorsDeclared model.roles := fun declared => by
  have h := declared.arity (T := name 7) (constructors := [(name 8, [.closed (.const (name 9))])])
    (k := name 8) (fields := [.closed (.const (name 9))]) rfl List.mem_cons_self
  have e : model.roles (name 8) = .computes 1 .leaf := rfl
  rw [e] at h
  cases h

/-- The value model has not all of its laws. -/
theorem not_laws : ¬ model.Laws := fun laws => not_declared laws.declared

/-- **Without the law of declared constructors, the interpretation has not the
facts of an interpretation at any level**, although the value model has every
other law: the relation of `T` is not transitive. -/
theorem interpAt_facts_needs_declared :
    (model.toModel.Laws ∧ model.roles model.star = .rigid ∧ model.star ≠ model.prop ∧
        model.star ≠ model.holds ∧ model.alg.Laws) ∧
      ¬ ConstructorsDeclared model.roles ∧ ∀ l : Nat, ¬ InterpFacts model (InterpAt model l) := by
  refine ⟨model_laws_but_declared, not_declared, fun l facts => ?_⟩
  let cs : List (DeclName × List (Field Empty)) := [(name 8, [.closed (.const (name 9))])]
  let field : Tm Empty 0 → Pack model 0 := fun _ => Pack.total model 0
  have interp : InterpAt model l Consistency.World.closed (.const (name 7))
      (indPack model (name 7) cs field) := by
    refine SInterp.ind .refl rfl field fun {F} hF => ?_
    obtain rfl : F = .const (name 9) := List.mem_singleton.mp hF
    exact SInterp.rigid (args := []) .refl rfl (by decide) (by decide)
  have first : IndRel model cs field (.app (.const (name 8)) (.const (name 0)))
      (.app (.const (name 8)) (.const (name 6))) :=
    .ctor (as := [.const (name 0)]) (as' := [.const (name 6)]) List.mem_cons_self .refl .refl
      (.closed trivial .nil)
  have second : IndRel model cs field (.app (.const (name 8)) (.const (name 6)))
      (.const (name 6)) :=
    .star (Relation.ReflTransGen.single (.root ⟨_, rfl, rfl⟩)) .star .refl .star
  have third := facts.trans interp first second
  have normal : ∀ i, (∀ arity inspect, model.roles (name i) ≠ .computes arity inspect) →
      Whnf model.rules model.roles (.const (name i) : Tm Empty 0) :=
    fun _ notComputing => constSpine_whnf rootShape notComputing (args := [])
  cases third with
  | ctor mem _ red' _ =>
      have e := whRed_of_whnf (normal 6 fun _ _ h => nomatch h) red'
      obtain ⟨rfl, -⟩ := Consistency.appSpine_const_eq_const e
      cases List.mem_singleton.mp mem
  | star red daimonic _ _ =>
      have e := WhRed.whnf_unique rootShape red
        (Relation.ReflTransGen.single (.root ⟨_, rfl, rfl⟩))
        ((daimonic.neutral rfl).whnf rootShape) (normal 0 fun _ _ h => nomatch h)
      subst e
      rcases daimonic.constSpine (args := []) rfl with same | ⟨_, _, computes⟩
      · exact absurd same (by decide)
      · exact nomatch computes

end UndeclaredControl

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
