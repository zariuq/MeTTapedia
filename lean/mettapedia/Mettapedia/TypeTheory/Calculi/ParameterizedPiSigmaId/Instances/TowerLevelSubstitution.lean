import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerAnnotated
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.HeadMorphism
import Mettapedia.TypeTheory.UniverseLevel.Bounded

/-!
# Level substitution in the tower, with bounded level parameters

A universe of the tower carries a level expression, which may mention level parameters. This
file treats the parameters as variables with bounds.

* **Bounded packages** (`boundedRules`, `boundedChurch`). A package over the heads of the tower
  with bounds `Δ` on its level parameters has the same rules, declarations and steps; its
  universes are compared at the valuations that respect the bounds (`CumulativeUnder`,
  `HeadEqUnder`), so `U_l ⊑ U_c` holds for a parameter `l` bounded by `c`.
* **Level substitution** (`substLevelsHead`) replaces the parameters of every head by level
  expressions. An admissible substitution from the bounds `Δ` to the bounds `Δ'` is a morphism
  of annotated packages (`substLevels_morphism`), when it keeps the declared types and the
  steps of the package. So derivations are stable under admissible level substitution
  (`CDerivable.substLevels`).
* **One check, every level** (`CDerivable.instantiateLevel`). A statement derived with a level
  parameter bounded by `c` yields, for every closed level `d < c`, the derived statement with
  `d` for the parameter, in the package without bounds.

Positive examples: the identity on the universe at any level expression, a parameter included,
is typed in every package over the tower (`identity_typed`); under `l < c`, the universe at `l`
is a member of the universe at `c`
(`sort_param_typed_bound`), and so, for every `d < c`, is the universe at `d`
(`sort_const_typed_bound`, by instantiation). Negative example: a substitution that is not
admissible does not keep the comparison of universes: under `l < 3` the universe at `l + 1` is
below the universe at `3`, and at `l := 5` it is not (`cumulativeUnder_not_stable`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace LevelTower

open TypedEquality TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open LevelBounds (LeUnder EqUnder Admissible leUnder_subst eqUnder_subst unbounded
  valid_unbounded admissible_instantiate)

variable {L : Type}

/-- Substitute level expressions for the level parameters of a head. -/
def substLevelsHead (σ : Nat → LevelExpr L) : Head L → Head L
  | .legacyGround => .legacyGround
  | .sort e => .sort (e.subst σ)

variable [LevelOrder L]

/-- Cumulativity of the universes when the level parameters range below their bounds. -/
def CumulativeUnder (Δ : LevelBounds L) : Head L → Head L → Prop
  | .sort left, .sort right => LeUnder Δ left right
  | _, _ => False

/-- Equality of heads when the level parameters range below their bounds. -/
def HeadEqUnder (Δ : LevelBounds L) : Head L → Head L → Prop
  | .legacyGround, .legacyGround => True
  | .sort left, .sort right => EqUnder Δ left right
  | _, _ => False

/-- **A package over the heads of the tower with its level parameters bounded**: the same
rules, with the universes compared at the valuations that respect the bounds. -/
def boundedRules (R : Rules (Head L)) (Δ : LevelBounds L) : Rules (Head L) :=
  { R with cumulative := CumulativeUnder Δ, headEq := HeadEqUnder Δ }

/-- The annotation of a bounded package: the declarations and steps of the package. -/
def boundedChurch {R : Rules (Head L)} (P : ChurchRules R) (Δ : LevelBounds L) :
    ChurchRules (boundedRules R Δ) where
  constantType := P.constantType
  computation := P.computation
  erase_constantType := P.erase_constantType
  erase_step := P.erase_step

/-- A rule package that types its heads and forms its types as the tower does. -/
structure TowerFormation (R : Rules (Head L)) : Prop where
  headTyping : ∀ {h u : Head L}, R.headTyping h u ↔ HeadTyping h u
  isUniverse : ∀ {u : Head L}, R.isUniverse u ↔ IsUniverse u
  join : ∀ {u v w : Head L}, R.join u v w ↔ Join u v w

/-- A rule package whose universe rules are those of the tower: formation, and the comparison
of universes at every valuation of the level parameters. -/
structure OverTower (R : Rules (Head L)) : Prop extends TowerFormation R where
  cumulative : ∀ {u v : Head L}, R.cumulative u v ↔ Cumulative u v
  headEq : ∀ {h h' : Head L}, R.headEq h h' ↔ HeadEq h h'

/-- The tower is over itself. -/
theorem overTower_rules : OverTower (rules L) :=
  ⟨⟨Iff.rfl, Iff.rfl, Iff.rfl⟩, Iff.rfl, Iff.rfl⟩

/-- Bounding the level parameters keeps the formation of types. -/
theorem TowerFormation.bounded {R : Rules (Head L)} (formation : TowerFormation R)
    (Δ : LevelBounds L) : TowerFormation (boundedRules R Δ) :=
  ⟨formation.headTyping, formation.isUniverse, formation.join⟩

/-- **Level substitution is a morphism of bounded packages**: an admissible substitution of
level expressions for level parameters maps the package with bounds `Δ` into the package with
bounds `Δ'`, when it keeps the declared types of the package and maps its steps, with their
premises, to steps. -/
theorem substLevels_morphism {R : Rules (Head L)} {P : ChurchRules R} (tower : OverTower R)
    {Δ Δ' : LevelBounds L} {σ : Nat → LevelExpr L} (admissible : Admissible Δ' Δ σ)
    (constants : ∀ {c : DeclName} {T : CTm (Head L) 0}, P.constantType c = some T →
      T.mapHead (substLevelsHead σ) = T)
    (steps : ∀ {n : Nat} {l r : CTm (Head L) n}, P.computation.step l r →
      P.computation.step (l.mapHead (substLevelsHead σ)) (r.mapHead (substLevelsHead σ)))
    (requires : ∀ {n : Nat} {l r : CTm (Head L) n} {premises : List (CPremise (Head L) n)},
      P.computation.step l r → P.computation.requires l r premises →
        ∃ premises', P.computation.requires (l.mapHead (substLevelsHead σ))
            (r.mapHead (substLevelsHead σ)) premises' ∧
          ∀ premise ∈ premises', ∃ source ∈ premises,
            premise = source.mapHead (substLevelsHead σ)) :
    (boundedChurch P Δ).Morphism (boundedChurch P Δ') (substLevelsHead σ) where
  headTyping := by
    intro h u typing
    have known : HeadTyping h u := tower.headTyping.mp typing
    refine tower.headTyping.mpr ?_
    cases known with
    | legacyGround => exact .legacyGround
    | sort level => exact .sort _
  isUniverse := by
    intro u isUniverse
    have known : IsUniverse u := tower.isUniverse.mp isUniverse
    refine tower.isUniverse.mpr ?_
    cases known with
    | sort level => exact .sort _
  join := by
    intro u v w joined
    have known : Join u v w := tower.join.mp joined
    refine tower.join.mpr ?_
    cases known with
    | sorts left right => exact .sorts _ _
  cumulative := by
    intro u v below
    cases u with
    | legacyGround => exact below.elim
    | sort left =>
      cases v with
      | legacyGround => exact below.elim
      | sort right => exact leUnder_subst below admissible
  headEq := by
    intro h h' same
    cases h with
    | legacyGround =>
      cases h' with
      | legacyGround => trivial
      | sort _ => exact same.elim
    | sort left =>
      cases h' with
      | legacyGround => exact same.elim
      | sort right => exact eqUnder_subst same admissible
  constantType := by
    intro c T declared
    change P.constantType c = some (T.mapHead (substLevelsHead σ))
    rw [constants declared]
    exact declared
  computation := steps
  requires := requires

/-- **Derivations are stable under admissible level substitution.** -/
theorem CDerivable.substLevels {R : Rules (Head L)} {P : ChurchRules R} (tower : OverTower R)
    {Δ Δ' : LevelBounds L} {σ : Nat → LevelExpr L} (admissible : Admissible Δ' Δ σ)
    (constants : ∀ {c : DeclName} {T : CTm (Head L) 0}, P.constantType c = some T →
      T.mapHead (substLevelsHead σ) = T)
    (steps : ∀ {n : Nat} {l r : CTm (Head L) n}, P.computation.step l r →
      P.computation.step (l.mapHead (substLevelsHead σ)) (r.mapHead (substLevelsHead σ)))
    (requires : ∀ {n : Nat} {l r : CTm (Head L) n} {premises : List (CPremise (Head L) n)},
      P.computation.step l r → P.computation.requires l r premises →
        ∃ premises', P.computation.requires (l.mapHead (substLevelsHead σ))
            (r.mapHead (substLevelsHead σ)) premises' ∧
          ∀ premise ∈ premises', ∃ source ∈ premises,
            premise = source.mapHead (substLevelsHead σ))
    {s : CStatement (Head L)} (derivation : CDerivable (boundedChurch P Δ) s) :
    CDerivable (boundedChurch P Δ') (s.mapHead (substLevelsHead σ)) :=
  derivation.mapHead (substLevels_morphism tower admissible constants steps requires)

/-- Without bounds, the bounded package is the package. -/
theorem unbounded_morphism {R : Rules (Head L)} (tower : OverTower R) (P : ChurchRules R) :
    (boundedChurch P (unbounded L)).Morphism P (fun h => h) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := by
    intro u v below
    refine tower.cumulative.mpr ?_
    cases u with
    | legacyGround => exact below.elim
    | sort left =>
      cases v with
      | legacyGround => exact below.elim
      | sort right => exact fun ν => below ν (valid_unbounded ν)
  headEq := by
    intro h h' same
    refine tower.headEq.mpr ?_
    cases h with
    | legacyGround =>
      cases h' with
      | legacyGround => trivial
      | sort _ => exact same.elim
    | sort left =>
      cases h' with
      | legacyGround => exact same.elim
      | sort right => exact fun ν => same ν (valid_unbounded ν)
  constantType := fun declared => by
    rw [CTm.mapHead_id]
    exact declared
  computation := fun step => by
    rw [CTm.mapHead_id, CTm.mapHead_id]
    exact step
  requires := fun {_ _ _ premises} _ required =>
    ⟨premises, by rw [CTm.mapHead_id, CTm.mapHead_id]; exact required,
      fun premise member => ⟨premise, member, (CPremise.mapHead_id premise).symm⟩⟩

/-- The package is contained in each of its bounded versions: an order of universes at every
valuation holds at the valuations that respect the bounds. -/
theorem bounded_morphism {R : Rules (Head L)} (tower : OverTower R) (P : ChurchRules R)
    (Δ : LevelBounds L) : P.Morphism (boundedChurch P Δ) (fun h => h) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := by
    intro u v below
    have known : Cumulative u v := tower.cumulative.mp below
    cases u with
    | legacyGround => exact known.elim
    | sort left =>
      cases v with
      | legacyGround => exact known.elim
      | sort right => exact fun ν _ => known ν
  headEq := by
    intro h h' same
    have known : HeadEq h h' := tower.headEq.mp same
    cases h with
    | legacyGround =>
      cases h' with
      | legacyGround => trivial
      | sort _ => exact known.elim
    | sort left =>
      cases h' with
      | legacyGround => exact known.elim
      | sort right => exact fun ν _ => known ν
  constantType := fun declared => by
    rw [CTm.mapHead_id]
    exact declared
  computation := fun step => by
    rw [CTm.mapHead_id, CTm.mapHead_id]
    exact step
  requires := fun {_ _ _ premises} _ required =>
    ⟨premises, by rw [CTm.mapHead_id, CTm.mapHead_id]; exact required,
      fun premise member => ⟨premise, member, (CPremise.mapHead_id premise).symm⟩⟩

/-- **Derivations of the package hold under every bounds.** -/
theorem CDerivable.bounded {R : Rules (Head L)} {P : ChurchRules R} (tower : OverTower R)
    (Δ : LevelBounds L) {s : CStatement (Head L)} (derivation : CDerivable P s) :
    CDerivable (boundedChurch P Δ) s :=
  derivation.of_morphism (bounded_morphism tower P Δ)

/-- **One check, every level.** A statement derived with the level parameter `x` bounded by
`c`, and no other parameter bounded, yields for every closed level `d < c` the derived
statement with `d` for `x`, in the package without bounds. -/
theorem CDerivable.instantiateLevel {R : Rules (Head L)} {P : ChurchRules R}
    (tower : OverTower R) {Δ : LevelBounds L} {x : Nat} {c : L} (bound : Δ x = some c)
    (others : ∀ i, i ≠ x → Δ i = none) {d : L} (below : d < c)
    (constants : ∀ {k : DeclName} {T : CTm (Head L) 0}, P.constantType k = some T →
      T.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d))) = T)
    (steps : ∀ {n : Nat} {l r : CTm (Head L) n}, P.computation.step l r →
      P.computation.step (l.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d))))
        (r.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d)))))
    (requires : ∀ {n : Nat} {l r : CTm (Head L) n} {premises : List (CPremise (Head L) n)},
      P.computation.step l r → P.computation.requires l r premises →
        ∃ premises', P.computation.requires
            (l.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d))))
            (r.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d)))) premises' ∧
          ∀ premise ∈ premises', ∃ source ∈ premises,
            premise = source.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d))))
    {s : CStatement (Head L)} (derivation : CDerivable (boundedChurch P Δ) s) :
    CDerivable P (s.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d)))) := by
  have admissible : Admissible (unbounded L) Δ (LevelExpr.instantiate x (.const d)) :=
    admissible_instantiate
      (fun i other k known => by
        rw [others i other] at known
        cases known)
      (fun k known => by
        rw [bound] at known
        cases known
        exact fun _ _ => LevelOrder.succ_le_of_lt below)
  exact (CDerivable.substLevels tower admissible constants steps requires derivation).of_morphism
    (unbounded_morphism tower P)

/-- **The identity on the universe at a level expression**, in every package over the tower:
`λ (A : U_e). λ (a : A). a` has type `Π (A : U_e). A → A`. The level may be a parameter. -/
theorem identity_typed {R : Rules (Head L)} {P : ChurchRules R} (tower : TowerFormation R)
    (e : LevelExpr L) :
    CDerivable P
      (.typing .nil (.lam (.head (.sort e)) (.lam (.var 0) (.var 0)))
        (.pi (.head (.sort e)) (.pi (.var 0) (.var 1)))) := by
  have isSort {u : LevelExpr L} : R.isUniverse (.sort u) :=
    tower.isUniverse.mpr (IsUniverse.sort u)
  have typed : CDerivable P
      (.typing .nil (.head (.sort e)) (.head (.sort (.succ e)))) :=
    .headType (tower.headTyping.mpr (HeadTyping.sort e))
  have member : CDerivable P
      (.typing (.snoc .nil (.head (.sort e))) (.var 0) (.head (.sort e))) := .var 0
  have again : CDerivable P
      (.typing (.snoc (.snoc .nil (.head (.sort e))) (.var 0)) (.var 1) (.head (.sort e))) :=
    .var 1
  have element : CDerivable P
      (.typing (.snoc (.snoc .nil (.head (.sort e))) (.var 0)) (.var 0) (.var 1)) := .var 0
  have inner : CDerivable P
      (.typing (.snoc .nil (.head (.sort e))) (.pi (.var 0) (.var 1))
        (.head (.sort (.max e e)))) :=
    .piForm member isSort again isSort (tower.join.mpr (Join.sorts _ _))
  have whole : CDerivable P
      (.typing .nil (.pi (.head (.sort e)) (.pi (.var 0) (.var 1)))
        (.head (.sort (.max (.succ e) (.max e e))))) :=
    .piForm typed isSort inner isSort (tower.join.mpr (Join.sorts _ _))
  have body : CDerivable P
      (.typing (.snoc .nil (.head (.sort e))) (.lam (.var 0) (.var 0)) (.pi (.var 0) (.var 1))) :=
    .lamIntro member isSort inner isSort element
  exact .lamIntro typed isSort whole isSort body

/-! ## Examples on the tower without declarations -/

section Examples

open TypedEquality.Annotated.TowerControls (P₀)

/-- The annotated tower keeps every substitution: it declares nothing. -/
theorem tower_instantiateLevel {Δ : LevelBounds L} {x : Nat} {c : L} (bound : Δ x = some c)
    (others : ∀ i, i ≠ x → Δ i = none) {d : L} (below : d < c)
    {s : CStatement (Head L)} (derivation : CDerivable (boundedChurch (P₀ (L := L)) Δ) s) :
    CDerivable (P₀ (L := L))
      (s.mapHead (substLevelsHead (LevelExpr.instantiate x (.const d)))) :=
  CDerivable.instantiateLevel (P := P₀ (L := L)) overTower_rules bound others below
    (fun {_ T} (declared : (none : Option (CTm (Head L) 0)) = some T) => nomatch declared)
    (fun step => step.elim)
    (fun _ _ => ⟨[], rfl, fun _ impossible => nomatch impossible⟩) derivation

/-- The bounds with the parameter `0` below `c` and no other bound. -/
def oneBound (c : L) : LevelBounds L := fun i => if i = 0 then some c else none

omit [LevelOrder L] in
theorem oneBound_zero (c : L) : oneBound c 0 = some c := if_pos rfl

omit [LevelOrder L] in
theorem oneBound_other (c : L) (i : Nat) (other : i ≠ 0) : oneBound c i = none := if_neg other

/-- **Under `l < c`, the universe at `l` is a member of the universe at `c`.** -/
theorem sort_param_typed_bound (c : L) :
    CDerivable (boundedChurch (P₀ (L := L)) (oneBound c))
      (.typing .nil (.head (.sort (.param 0))) (.head (.sort (.const c)))) :=
  .sub (.headType (HeadTyping.sort _))
    (.subUniv (fun _ valid => LevelOrder.succ_le_of_lt (valid 0 c (oneBound_zero c))))

/-- **For every `d < c`, the universe at `d` is a member of the universe at `c`**, from the one
derivation under the bound. -/
theorem sort_const_typed_bound {c d : L} (below : d < c) :
    CDerivable (P₀ (L := L))
      (.typing .nil (.head (.sort (.const d))) (.head (.sort (.const c)))) := by
  have instance_ := tower_instantiateLevel (oneBound_zero c) (oneBound_other c) below
    (sort_param_typed_bound c)
  have atZero : LevelExpr.instantiate 0 (LevelExpr.const d) 0 = (.const d : LevelExpr L) := by
    show (if (0 : Nat) = 0 then (LevelExpr.const d : LevelExpr L) else .param 0) = .const d
    exact if_pos rfl
  simpa only [CStatement.mapHead, CCtx.mapHead, CTm.mapHead, substLevelsHead, LevelExpr.subst,
    atZero] using instance_

end Examples

/-- **A substitution that is not admissible does not keep the comparison of universes.** Over
the natural numbers, under `l < 3` the universe at `l + 1` is below the universe at `3`; with
`5` for `l` it is not. -/
theorem cumulativeUnder_not_stable :
    CumulativeUnder (fun i => if i = 0 then some 3 else none)
        (.sort (.succ (.param 0)) : Head Nat) (.sort (.const 3)) ∧
      ¬ Cumulative (substLevelsHead (LevelExpr.instantiate 0 (.const 5))
          (.sort (.succ (.param 0)) : Head Nat))
        (substLevelsHead (LevelExpr.instantiate 0 (.const 5)) (.sort (.const 3))) := by
  constructor
  · intro ν valid
    exact LevelOrder.succ_le_of_lt (valid 0 3 (if_pos rfl))
  · intro below
    have at_zero := below (fun _ => 0)
    exact absurd at_zero (by decide)

end LevelTower
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
