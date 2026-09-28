import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpLaws

/-!
# Partial equivalences of the interpretation

The relation a type denotes at a level is symmetric and transitive when the
interpretations below are deterministic. Related terms stay related under
weak-head expansion of either side when the interpretations below are closed
under weak-head expansion of types. Along a world morphism, a renamed type has
an interpretation that relates the renamed terms. An interpretation at a level
is one at every higher level whose interpretations below agree with it.

The interpretations below a level are deterministic and closed under weak-head
expansion, so at `InterpAt` these laws hold without hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Transport of a dependent family along a morphism -/

/-- A dependent function or pair family read from a world reached by a
morphism: its domain and codomain at every further world. -/
def PiRel.rename {n m : Nat} {ξ : World M.reading n} {ξ' : World M.reading m} {ρ : Ren n m} (P : PiRel Head ξ)
    (w : Morph ξ ξ' ρ) : PiRel Head ξ' where
  dom := fun {_ _ _} w' => P.dom (w.comp' w')
  cod := fun {_ _ _} w' {_} ha => P.cod (w.comp' w') ha

section Below

variable {l : L} {below : L → IRel M.reading}

/-! ## Partial equivalence -/

/-- The relation of a type is symmetric and transitive when the interpretations
below are deterministic. -/
theorem Interp.per (laws : M.Laws)
    (belowDet : ∀ k {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R R' : Rel Head n},
      below k ξ A R → below k ξ A R' → R = R')
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (interp : Interp M l below ξ A R) :
    (∀ {t u : Tm Head n}, R t u → R u t) ∧
      ∀ {t u v : Tm Head n}, R t u → R u v → R t v := by
  induction interp with
  | sort =>
      constructor
      · intro t u h m ξ' ρ w
        obtain ⟨R, ht, hu⟩ := h w
        exact ⟨R, hu, ht⟩
      · intro t u v h h' m ξ' ρ w
        obtain ⟨R, ht, hu⟩ := h w
        obtain ⟨R', hu', hv⟩ := h' w
        obtain rfl := belowDet _ hu hu'
        exact ⟨R, ht, hv⟩
  | ground => exact ⟨fun _ => trivial, fun _ _ => trivial⟩
  | pi _ _ _ _ codRespect domIH codIH =>
      constructor
      · intro f g h m ξ' ρ w a b ha hab
        have hba := (domIH w).1 hab
        have hb := (domIH w).2 hba hab
        rw [codRespect w ha hb hab]
        exact (codIH w hb).1 (h w hb hba)
      · intro f g k hfg hgk m ξ' ρ w a b ha hab
        exact (codIH w ha).2 (hfg w ha ha) (hgk w ha hab)
  | sigma _ _ _ _ codRespect domIH codIH =>
      constructor
      · rintro p q ⟨hp, hpq, hc⟩
        have hqp := (domIH (Morph.id _)).1 hpq
        have hq := (domIH (Morph.id _)).2 hqp hpq
        refine ⟨hq, hqp, ?_⟩
        rw [← codRespect (Morph.id _) hp hq hpq]
        exact (codIH (Morph.id _) hp).1 hc
      · rintro p q r ⟨hp, hpq, hc⟩ ⟨hq, hqr, hc'⟩
        refine ⟨hp, (domIH (Morph.id _)).2 hpq hqr, ?_⟩
        rw [codRespect (Morph.id _) hp hq hpq] at hc ⊢
        exact (codIH (Morph.id _) hq).2 hc hc'
  | ident => exact ⟨fun h => h, fun h _ => h⟩
  | num =>
      constructor
      · rintro t u ⟨k, ht, hu⟩
        exact ⟨k, hu, ht⟩
      · rintro t u v ⟨k, ht, hu⟩ ⟨k', hu', hv⟩
        obtain rfl := NumVal.deterministic laws.truth hu hu'
        exact ⟨k, ht, hv⟩
  | prop =>
      constructor
      · rintro t u ⟨P, ht, hu⟩
        exact ⟨P, hu, ht⟩
      · rintro t u v ⟨P, ht, hu⟩ ⟨P', hu', hv⟩
        obtain rfl := Truth.deterministic laws.reading hu hu'
        exact ⟨P, ht, hv⟩
  | holds => exact ⟨fun h => h, fun h _ => h⟩
  | rigid => exact ⟨fun _ => trivial, fun _ _ => trivial⟩

/-- The relation of a type is symmetric when the interpretations below are
deterministic. -/
theorem Interp.symm (laws : M.Laws)
    (belowDet : ∀ k {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R R' : Rel Head n},
      below k ξ A R → below k ξ A R' → R = R')
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (interp : Interp M l below ξ A R) :
    ∀ {t u : Tm Head n}, R t u → R u t :=
  (interp.per laws belowDet).1

/-- The relation of a type is transitive when the interpretations below are
deterministic. -/
theorem Interp.trans (laws : M.Laws)
    (belowDet : ∀ k {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R R' : Rel Head n},
      below k ξ A R → below k ξ A R' → R = R')
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (interp : Interp M l below ξ A R) :
    ∀ {t u v : Tm Head n}, R t u → R u v → R t v :=
  (interp.per laws belowDet).2

/-! ## Expansion of related terms -/

/-- If the interpretations below are closed under weak-head expansion of types,
related terms stay related when either side is replaced by a term that
weak-head reduces to it. -/
theorem Interp.expandLeftRight
    (belowExpand : ∀ k {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n} {R : Rel Head n},
      WhRed M.rules M.roles A A' → below k ξ A' R → below k ξ A R)
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (interp : Interp M l below ξ A R) :
    (∀ {t t' u : Tm Head n}, WhRed M.rules M.roles t t' → R t' u → R t u) ∧
      ∀ {t u u' : Tm Head n}, WhRed M.rules M.roles u u' → R t u' → R t u := by
  induction interp with
  | sort =>
      constructor
      · intro t t' u red h m ξ' ρ w
        obtain ⟨R, ht, hu⟩ := h w
        exact ⟨R, belowExpand _ (red.rename ρ) ht, hu⟩
      · intro t u u' red h m ξ' ρ w
        obtain ⟨R, ht, hu⟩ := h w
        exact ⟨R, ht, belowExpand _ (red.rename ρ) hu⟩
  | ground => exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  | pi _ _ _ _ _ _ codIH =>
      constructor
      · intro f f' g red h m ξ' ρ w a b ha hab
        exact (codIH w ha).1 ((red.rename ρ).app a) (h w ha hab)
      · intro f g g' red h m ξ' ρ w a b ha hab
        exact (codIH w ha).2 ((red.rename ρ).app b) (h w ha hab)
  | sigma _ _ _ _ codRespect domIH codIH =>
      constructor
      · rintro p p' q red ⟨hp', hpq, hc⟩
        have hpp' := (domIH (Morph.id _)).1 red.fst hp'
        have hp := (domIH (Morph.id _)).2 red.fst hpp'
        refine ⟨hp, (domIH (Morph.id _)).1 red.fst hpq, ?_⟩
        rw [codRespect (Morph.id _) hp hp' hpp']
        exact (codIH (Morph.id _) hp').1 red.snd hc
      · rintro p q q' red ⟨hp, hpq, hc⟩
        exact ⟨hp, (domIH (Morph.id _)).2 red.fst hpq, (codIH (Morph.id _) hp).2 red.snd hc⟩
  | ident => exact ⟨fun _ h => h, fun _ h => h⟩
  | num =>
      constructor
      · rintro t t' u red ⟨k, ht, hu⟩
        exact ⟨k, ht.expand red, hu⟩
      · rintro t u u' red ⟨k, ht, hu⟩
        exact ⟨k, ht, hu.expand red⟩
  | prop =>
      constructor
      · rintro t t' u red ⟨P, ht, hu⟩
        exact ⟨P, ht.expand red, hu⟩
      · rintro t u u' red ⟨P, ht, hu⟩
        exact ⟨P, ht, hu.expand red⟩
  | holds => exact ⟨fun _ h => h, fun _ h => h⟩
  | rigid => exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩

/-- Related terms stay related when the left side is replaced by a term that
weak-head reduces to it. -/
theorem Interp.expandLeft
    (belowExpand : ∀ k {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n} {R : Rel Head n},
      WhRed M.rules M.roles A A' → below k ξ A' R → below k ξ A R)
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (interp : Interp M l below ξ A R) :
    ∀ {t t' u : Tm Head n}, WhRed M.rules M.roles t t' → R t' u → R t u :=
  (interp.expandLeftRight belowExpand).1

/-- Related terms stay related when the right side is replaced by a term that
weak-head reduces to it. -/
theorem Interp.expandRight
    (belowExpand : ∀ k {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n} {R : Rel Head n},
      WhRed M.rules M.roles A A' → below k ξ A' R → below k ξ A R)
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} (interp : Interp M l below ξ A R) :
    ∀ {t u u' : Tm Head n}, WhRed M.rules M.roles u u' → R t u' → R t u :=
  (interp.expandLeftRight belowExpand).2

/-! ## Monotonicity along world morphisms -/

/-- Along a world morphism, a renamed type has an interpretation that relates
the renamed terms. -/
theorem Interp.rename (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}
    (interp : Interp M l below ξ A R) :
    ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∃ R', Interp M l below ξ' (Presentation.rename ρ A) R' ∧
        ∀ {a b : Tm Head n}, R a b →
          R' (Presentation.rename ρ a) (Presentation.rename ρ b) := by
  induction interp with
  | sort isUniverse level red =>
      intro m ξ' ρ w
      refine ⟨_, .sort isUniverse level (red.rename ρ), ?_⟩
      intro a b h k ξ'' ρ' w'
      simp only [rename_comp]
      exact h (w.comp' w')
  | ground notUniverse red =>
      intro m ξ' ρ w
      exact ⟨_, .ground notUniverse (red.rename ρ), fun _ => trivial⟩
  | pi red P domInterp codInterp codRespect =>
      intro m ξ' ρ w
      refine ⟨_, .pi (red.rename ρ) (P.rename w) ?_ ?_ ?_, ?_⟩
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
      refine ⟨_, .sigma (red.rename ρ) (P.rename w) ?_ ?_ ?_, ?_⟩
      · intro k ξ'' ρ' w'
        rw [rename_comp]
        exact domInterp (w.comp' w')
      · intro k ξ'' ρ' w' a ha
        rw [rename_rename_lift]
        exact codInterp (w.comp' w') ha
      · intro k ξ'' ρ' w' a b ha hb hab
        exact codRespect (w.comp' w') ha hb hab
      · rintro p q ⟨hp, hpq, hc⟩
        obtain ⟨D, domI, domR⟩ := domIH (Morph.id ξ) w
        rw [rename_id] at domI
        obtain rfl : D = P.dom w := Interp.deterministic laws domI (domInterp w)
        have hp' : P.dom w (Presentation.rename ρ (.fst p)) (Presentation.rename ρ (.fst p)) :=
          domR hp
        obtain ⟨C, codI, codR⟩ := codIH (Morph.id ξ) hp w
        rw [rename_inst0, liftRen_id, rename_id] at codI
        obtain rfl : C = P.cod w hp' := Interp.deterministic laws codI (codInterp w hp')
        exact ⟨hp', domR hpq, codR hc⟩
  | ident red _ _ lhsRefl rhsRefl tyIH =>
      intro m ξ' ρ w
      obtain ⟨R', tyI, tyR⟩ := tyIH w
      exact ⟨_, .ident (red.rename ρ) R' tyI (tyR lhsRefl) (tyR rhsRefl), fun h => tyR h⟩
  | num red =>
      intro m ξ' ρ w
      refine ⟨_, .num (red.rename ρ), ?_⟩
      rintro a b ⟨k, ha, hb⟩
      exact ⟨k, ha.rename ρ, hb.rename ρ⟩
  | prop red =>
      intro m ξ' ρ w
      refine ⟨_, .prop (red.rename ρ), ?_⟩
      rintro a b ⟨P, ha, hb⟩
      exact ⟨P, Truth.rename w ha, Truth.rename w hb⟩
  | holds red good =>
      intro m ξ' ρ w
      obtain ⟨P, hP⟩ := good
      refine ⟨_, .holds (red.rename ρ) ⟨P, Truth.rename w hP⟩, ?_⟩
      rintro a b ⟨Q, hQ, q⟩
      exact ⟨Q, Truth.rename w hQ, q⟩
  | rigid red role notProp notHolds =>
      intro m ξ' ρ w
      have red' := red.rename ρ
      rw [rename_appSpine] at red'
      exact ⟨_, .rigid red' role notProp notHolds, fun _ => trivial⟩

end Below

/-! ## Cumulativity -/

/-- An interpretation at a level is one at every higher level whose
interpretations below agree with it. -/
theorem Interp.cumul {l l' : L} (le : l ≤ l') {below below' : L → IRel M.reading}
    (agree : ∀ k, k < l → ∀ {n : Nat} (ξ : World M.reading n) (A : Tm Head n) (R : Rel Head n),
      below k ξ A R ↔ below' k ξ A R)
    {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n} :
    Interp M l below ξ A R → Interp M l' below' ξ A R := by
  intro interp
  induction interp with
  | @sort n ξ A u isUniverse level red =>
      have same : universeRel (below (M.levels.level u)) ξ =
          universeRel (below' (M.levels.level u)) ξ := by
        funext a b
        apply propext
        constructor
        · intro h m ξ' ρ w
          obtain ⟨R, ha, hb⟩ := h w
          exact ⟨R, (agree _ level _ _ _).mp ha, (agree _ level _ _ _).mp hb⟩
        · intro h m ξ' ρ w
          obtain ⟨R, ha, hb⟩ := h w
          exact ⟨R, (agree _ level _ _ _).mpr ha, (agree _ level _ _ _).mpr hb⟩
      rw [same]
      exact .sort isUniverse (lt_of_lt_of_le level le) red
  | ground notUniverse red => exact .ground notUniverse red
  | pi red P _ _ codRespect domIH codIH => exact .pi red P domIH codIH codRespect
  | sigma red P _ _ codRespect domIH codIH => exact .sigma red P domIH codIH codRespect
  | ident red R _ lhsRefl rhsRefl tyIH => exact .ident red R tyIH lhsRefl rhsRefl
  | num red => exact .num red
  | prop red => exact .prop red
  | holds red good => exact .holds red good
  | rigid red role notProp notHolds => exact .rigid red role notProp notHolds

/-! ## The interpretation at a level -/

section Levels

variable {l : L}

/-- Only levels below `l` are interpreted below `l`. -/
theorem levelsBelow_lt {k : L} {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {R : Rel Head n} (h : levelsBelow M l k ξ A R) : k < l := by
  by_contra hk
  unfold levelsBelow at h
  rw [UniverseLevel.below_eq _ _ l] at h
  simp only [if_neg hk, IRel.empty] at h

/-- The interpretations below a level are deterministic. -/
theorem levelsBelow_deterministic (laws : M.Laws) (k : L) {n : Nat} {ξ : World M.reading n}
    {A : Tm Head n} {R R' : Rel Head n} (first : levelsBelow M l k ξ A R)
    (second : levelsBelow M l k ξ A R') : R = R' :=
  have lt := levelsBelow_lt first
  Interp.deterministic laws ((levelsBelow_iff M lt ξ A R).mp first)
    ((levelsBelow_iff M lt ξ A R').mp second)

/-- The interpretations below a level are closed under weak-head expansion of
types. -/
theorem levelsBelow_expand (k : L) {n : Nat} {ξ : World M.reading n} {A A' : Tm Head n} {R : Rel Head n}
    (red : WhRed M.rules M.roles A A') (h : levelsBelow M l k ξ A' R) :
    levelsBelow M l k ξ A R :=
  have lt := levelsBelow_lt h
  (levelsBelow_iff M lt ξ A R).mpr (Interp.expand red ((levelsBelow_iff M lt ξ A' R).mp h))

/-- A type has at most one interpretation at a level. -/
theorem InterpAt.deterministic (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {R R' : Rel Head n} (first : InterpAt M l ξ A R) (second : InterpAt M l ξ A R') : R = R' :=
  Interp.deterministic laws first second

/-- The relation of a type at a level is symmetric. -/
theorem InterpAt.symm (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}
    (interp : InterpAt M l ξ A R) : ∀ {t u : Tm Head n}, R t u → R u t :=
  Interp.symm laws (levelsBelow_deterministic laws) interp

/-- The relation of a type at a level is transitive. -/
theorem InterpAt.trans (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}
    (interp : InterpAt M l ξ A R) : ∀ {t u v : Tm Head n}, R t u → R u v → R t v :=
  Interp.trans laws (levelsBelow_deterministic laws) interp

/-- Related terms at a level stay related when the left side is replaced by a
term that weak-head reduces to it. -/
theorem InterpAt.expandLeft {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}
    (interp : InterpAt M l ξ A R) :
    ∀ {t t' u : Tm Head n}, WhRed M.rules M.roles t t' → R t' u → R t u :=
  Interp.expandLeft levelsBelow_expand interp

/-- Related terms at a level stay related when the right side is replaced by a
term that weak-head reduces to it. -/
theorem InterpAt.expandRight {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}
    (interp : InterpAt M l ξ A R) :
    ∀ {t u u' : Tm Head n}, WhRed M.rules M.roles u u' → R t u' → R t u :=
  Interp.expandRight levelsBelow_expand interp

/-- Along a world morphism, a renamed type has an interpretation at the same
level that relates the renamed terms. -/
theorem InterpAt.rename (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n} {R : Rel Head n}
    (interp : InterpAt M l ξ A R) :
    ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∃ R', InterpAt M l ξ' (Presentation.rename ρ A) R' ∧
        ∀ {a b : Tm Head n}, R a b →
          R' (Presentation.rename ρ a) (Presentation.rename ρ b) :=
  Interp.rename laws interp

end Levels

/-- An interpretation at a level is one at every higher level. -/
theorem InterpAt.cumul {l l' : L} (le : l ≤ l') {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {R : Rel Head n} (interp : InterpAt M l ξ A R) : InterpAt M l' ξ A R :=
  Interp.cumul le (fun _ lt {_} ξ A R =>
    (levelsBelow_iff M lt ξ A R).trans
      (levelsBelow_iff M (lt_of_lt_of_le lt le) ξ A R).symm) interp

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
