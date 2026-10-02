import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelDecoders
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.TypedInstances

/-!
# The set models of the level names and their families

Relative to `CofinalInaccessibles`, the tower with level names (`LevelNames`) and an admitted
list of families (`LevelFamilies`) has models in the set tower, at every valuation of the
level parameters that respects the bounds. The models differ in what they take the names to
be.

* **Readings of the names** (`NameSets`). A reading gives, for every level, a set of names
  below it: it contains the universes below the level and no other universe, lies in the
  universe at the level, and grows with the level. The *standard* reading takes exactly the
  universes below the level (`standardNames`). The *seeded* reading has one more name, which
  names no level (`seededNames`).
* **Heads** (`headValue`). The type of the names below a level is its set of names, and the
  name of a level is the universe at it; the heads of the tower keep their values. These values
  satisfy the rules of the heads under bounds `Δ` at every valuation that respects `Δ`
  (`universeModel`, `headEq_values`).
* **Families** (`familyValue`). A family denotes the function that sends the universe at a
  level below its bound to the value of the family's value at that level, and a name that is
  no universe to a chosen value. Given such values of the family's type (`ExtraTyped`), the
  family lies in its declared type, and its root steps hold where their premise does
  (`familyModel`).
* **Soundness and relative consistency** in the standard reading (`sound`, `consistent`):
  every derivation of the package of an admitted list holds at every valuation that respects
  its bounds, and no closed term has type `Π (X : U₀). X`.

**The judgment is weaker than its standard model.** In the standard reading the decoders at
two bounds agree at a *variable* name (`decoders_agree_holds`): the names are the universes
below the bound and nothing else, so two functions that agree at every name of a level agree.
The judgment does not derive that equation (`decoders_agree_not_derivable`): in the seeded
reading the two decoders differ at the name that names no level. The judgment computes at
the names of level expressions; that there are no other names is a fact of the standard
reading, and no rule says it.

Further negative examples.

* A family with one value that is not of its type has no set model
  (`untyped_instance_no_setModel`).
* The bound of a level parameter is needed: without it the universe above the parameter is not
  a member of the universe at a closed level (`next_not_typed_unbounded`).
* Without the root steps the decoder at a name is not provably the universe it names
  (`rigid_not_equal`): the declared types alone have a model in which the decoder is constant.

Positive example over the notations below `ε₀`: the package with the decoders below `ω` and
below `ω + 1` is consistent (`finiteLevels_consistent`).

Scope: the annotated judgment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace LevelNames

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.TypeTheory.UniverseLevel
open LevelBounds (LeUnder EqUnder Admissible unbounded valid_unbounded positive_unbounded)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet universeSet_mem_of_lt universeSet_mono
  universeSet_injective earlierStages earlierStages_mem mem_earlierStages
  universeSet_no_self_membership insert_seed_earlierStages_mem seed_mem_universeSet)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)
open ZFSetReplayInterpretation (UniverseModel)

universe u

variable {L : Type} [LevelOrder L]

/-! ## Readings of the names -/

/-- **A reading of the types of names**: for every level a set of names below it, which
contains the universes below the level and no other universe, lies in the universe at the
level, and grows with the level. -/
structure NameSets (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (L : Type)
    [LevelOrder L] where
  /-- The set of the names below a level. -/
  names : L → ZFSet.{u}
  universe_mem : ∀ {d b : L}, d < b → universeSet h seed d ∈ names b
  lt_of_universe_mem : ∀ {d b : L}, universeSet h seed d ∈ names b → d < b
  mem_universe : ∀ b : L, names b ∈ universeSet h seed b
  mono : ∀ {b b' : L}, b ≤ b' → names b ⊆ names b'

/-- **The standard reading**: the names below a level are the universes below it. -/
noncomputable def standardNames (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    NameSets h seed L where
  names := earlierStages h seed
  universe_mem := fun below => mem_earlierStages.mpr ⟨_, below, rfl⟩
  lt_of_universe_mem := fun mem => by
    obtain ⟨d', below, same⟩ := mem_earlierStages.mp mem
    exact universeSet_injective h seed same ▸ below
  mem_universe := earlierStages_mem h seed
  mono := fun le x hx => by
    obtain ⟨d, below, rfl⟩ := mem_earlierStages.mp hx
    exact mem_earlierStages.mpr ⟨d, lt_of_lt_of_le below le, rfl⟩

/-- **The seeded reading**: besides the universes below a level, the seed is a name below
every level. It names no level. -/
noncomputable def seededNames (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    NameSets h seed L where
  names := fun b => insert seed (earlierStages h seed b)
  universe_mem := fun below =>
    ZFSet.mem_insert_of_mem _ (mem_earlierStages.mpr ⟨_, below, rfl⟩)
  lt_of_universe_mem := by
    intro d b mem
    rcases ZFSet.mem_insert_iff.mp mem with same | standard
    · have member : universeSet h seed d ∈ universeSet h seed d :=
        Eq.subst (motive := fun x => x ∈ universeSet h seed d) same.symm
          (seed_mem_universeSet h seed d)
      exact absurd member (ZFSet.mem_irrefl _)
    · obtain ⟨d', below, known⟩ := mem_earlierStages.mp standard
      exact universeSet_injective h seed known ▸ below
  mem_universe := insert_seed_earlierStages_mem h seed
  mono := by
    intro b b' le x hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl | standard
    · exact ZFSet.mem_insert _ _
    · obtain ⟨d, below, rfl⟩ := mem_earlierStages.mp standard
      exact ZFSet.mem_insert_of_mem _
        (mem_earlierStages.mpr ⟨d, lt_of_lt_of_le below le, rfl⟩)

/-! ## The values of the heads -/

section Heads

variable {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} (N : NameSets h seed L)
  (ground : ZFSet.{u}) (ν : Nat → L)

/-- **The values of the heads** in a reading of the names: the heads of the tower keep their
values; the type of the names below a level is its set of names; the name of a level is the
universe at it. -/
noncomputable def headValue : Head L → ZFSet.{u}
  | .tower t => interpretHead h seed ground ν t
  | .names b => N.names (b.eval ν)
  | .name e => universeSet h seed (e.eval ν)

/-- A head and the head with its level expressions evaluated have one value. -/
theorem headValue_evalHead (k : Head L) :
    headValue N ground ν (evalHead ν k) = headValue N ground ν k := by
  cases k with
  | tower t =>
    cases t with
    | legacyGround => rfl
    | sort e => rfl
  | names b => rfl
  | name e => rfl

/-- A term and the term with its level expressions evaluated have one value. -/
theorem ev_evalHead (consts : DeclName → ZFSet.{u}) {n : Nat} (t : CTm (Head L) n)
    (ρ : Env.{u} n) :
    ev (headValue N ground ν) consts (t.mapHead (evalHead ν)) ρ =
      ev (headValue N ground ν) consts t ρ := by
  have same : (fun k => headValue N ground ν (evalHead ν k)) = headValue N ground ν :=
    funext (headValue_evalHead N ground ν)
  rw [ev_mapHead, same]

variable {ground ν}

/-- **The values of the heads satisfy the rules of the heads**, at every valuation that
respects the bounds. -/
theorem universeModel {Δ : LevelBounds L} (valid : Δ.Valid ν)
    (groundTyped : ground ∈ universeSet h seed (LevelOrder.bot : L)) (Fs : List (Family L)) :
    UniverseModel (rules Δ Fs) (headValue N ground ν) where
  headTyping_mem := by
    intro head level typed
    have known : HeadTyping Δ head level := typed
    cases known with
    | tower towerTyped =>
      exact ZFSetReplayUniverseFormation.headTyping_membership h seed ground ν groundTyped
        towerTyped
    | names b => exact N.mem_universe (b.eval ν)
    | name below => exact N.universe_mem (LevelOrder.lt_of_succ_le (below ν valid))
  cumulative_subset := by
    intro lower upper below
    have known : Cumulative Δ lower upper := below
    cases lower with
    | tower s =>
      cases upper with
      | tower t =>
        cases s with
        | legacyGround => exact known.elim
        | sort left =>
          cases t with
          | legacyGround => exact known.elim
          | sort right => exact universeSet_mono h seed (known ν valid)
      | names _ => exact known.elim
      | name _ => exact known.elim
    | names b =>
      cases upper with
      | tower _ => exact known.elim
      | names b' => exact N.mono (known ν valid)
      | name _ => exact known.elim
    | name _ => exact known.elim
  pi_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    have known : Join domainLevel bodyLevel level := joined
    cases known with
    | tower towerJoined =>
      exact (ZFSetReplayUniverseModel.universeModel h seed ground ν groundTyped).pi_mem
        towerJoined domainTyped B bodyTyped
  sigma_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    have known : Join domainLevel bodyLevel level := joined
    cases known with
    | tower towerJoined =>
      exact (ZFSetReplayUniverseModel.universeModel h seed ground ν groundTyped).sigma_mem
        towerJoined domainTyped B bodyTyped
  identity_mem := by
    intro level isUniverse P
    have known : IsUniverse level := isUniverse
    cases known with
    | tower towerUniverse =>
      exact (ZFSetReplayUniverseModel.universeModel h seed ground ν groundTyped).identity_mem
        towerUniverse P

/-- **Heads that are equal under the bounds have one value**, at every valuation that respects
the bounds. -/
theorem headEq_values {Δ : LevelBounds L} (valid : Δ.Valid ν) {k k' : Head L}
    (same : HeadEq Δ k k') : headValue N ground ν k = headValue N ground ν k' := by
  cases k with
  | tower s =>
    cases k' with
    | tower t =>
      cases s with
      | legacyGround =>
        cases t with
        | legacyGround => rfl
        | sort _ => exact same.elim
      | sort left =>
        cases t with
        | legacyGround => exact same.elim
        | sort right => exact congrArg (universeSet h seed) (same ν valid)
    | names _ => exact same.elim
    | name _ => exact same.elim
  | names b =>
    cases k' with
    | tower _ => exact same.elim
    | names b' => exact congrArg N.names (same ν valid)
    | name _ => exact same.elim
  | name e =>
    cases k' with
    | tower _ => exact same.elim
    | names _ => exact same.elim
    | name e' => exact congrArg (universeSet h seed) (same ν valid)

end Heads

/-! ## The values of the families -/

section Model

variable (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})

/-- A set that is the universe at a level below a bound. -/
def IsStandard (c : L) (x : ZFSet.{u}) : Prop := ∃ d, d < c ∧ universeSet h seed d = x

/-- The level of a universe below a bound. -/
noncomputable def levelOf (c : L) (U : ZFSet.{u}) : L :=
  haveI := Classical.propDecidable (IsStandard h seed c U)
  if known : IsStandard h seed c U then Classical.choose known else LevelOrder.bot

/-- A universe below the bound determines its level. -/
theorem levelOf_universeSet (c : L) {d : L} (below : d < c) :
    levelOf h seed c (universeSet h seed d) = d := by
  have known : IsStandard h seed c (universeSet h seed d) := ⟨d, below, rfl⟩
  unfold levelOf
  rw [dif_pos known]
  exact universeSet_injective h seed (Classical.choose_spec known).2

variable {h seed}

open Classical in
/-- **The value of a family** in a reading of the names, under an assignment of values to the
constants: the function on the names below the bound that sends the universe at a level to
the value of the family's value at that level, and a name that is no such universe to a chosen
value. -/
noncomputable def familyValue (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    (consts : DeclName → ZFSet.{u}) (extra : DeclName → ZFSet.{u} → ZFSet.{u})
    (F : Family L) : ZFSet.{u} :=
  traceLam (graph (N.names F.bound) fun x =>
    if IsStandard h seed F.bound x then
      ev heads consts (F.body (.const (levelOf h seed F.bound x))) Fin.elim0
    else extra F.name x)

/-- The value of a family at the universe at a level below its bound. -/
theorem familyValue_at (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    (consts : DeclName → ZFSet.{u}) (extra : DeclName → ZFSet.{u} → ZFSet.{u}) (F : Family L)
    {d : L} (below : d < F.bound) :
    traceApp (familyValue N heads consts extra F) (universeSet h seed d) =
      ev heads consts (F.body (.const d)) Fin.elim0 := by
  rw [familyValue, traceApp_graph_beta _ (N.universe_mem below), if_pos ⟨d, below, rfl⟩,
    levelOf_universeSet h seed F.bound below]

/-- The value of a family at a name that is no universe below its bound. -/
theorem familyValue_extra (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    (consts : DeclName → ZFSet.{u}) (extra : DeclName → ZFSet.{u} → ZFSet.{u}) (F : Family L)
    {x : ZFSet.{u}} (hx : x ∈ N.names F.bound) (other : ¬ IsStandard h seed F.bound x) :
    traceApp (familyValue N heads consts extra F) x = extra F.name x := by
  rw [familyValue, traceApp_graph_beta _ hx, if_neg other]

/-- The value of a family reads only the constants its values at the closed levels below its
bound mention. -/
theorem familyValue_congr (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    {consts consts' : DeclName → ZFSet.{u}} (extra : DeclName → ZFSet.{u} → ZFSet.{u})
    (F : Family L)
    (same : ∀ d, d < F.bound → ∀ n ∈ termConsts (F.body (.const d)), consts n = consts' n) :
    familyValue N heads consts extra F = familyValue N heads consts' extra F := by
  unfold familyValue
  congr 1
  refine graph_congr fun x _ => ?_
  by_cases standard : IsStandard h seed F.bound x
  · rw [if_pos standard, if_pos standard]
    obtain ⟨d, below, rfl⟩ := standard
    rw [levelOf_universeSet h seed F.bound below]
    exact ev_congr_consts heads consts _ (same d below) Fin.elim0
  · rw [if_neg standard, if_neg standard]

/-- **An assignment of values fits a list of families** when it gives each family its value. -/
def Fits (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    (extra : DeclName → ZFSet.{u} → ZFSet.{u}) :
    List (Family L) → (DeclName → ZFSet.{u}) → Prop
  | [], _ => True
  | F :: Fs, consts =>
      Fits N heads extra Fs consts ∧ consts F.name = familyValue N heads consts extra F

/-- **The chosen values at the names that are no universes are of the families' types.** -/
def ExtraTyped (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    (extra : DeclName → ZFSet.{u} → ZFSet.{u}) (consts : DeclName → ZFSet.{u})
    (Fs : List (Family L)) : Prop :=
  ∀ F ∈ Fs, ∀ x ∈ N.names F.bound, ¬ IsStandard h seed F.bound x →
    extra F.name x ∈ ev heads consts F.type (extend Fin.elim0 x)

/-- In the standard reading every name is a universe below the bound. -/
theorem standard_extraTyped (heads : Head L → ZFSet.{u})
    (extra : DeclName → ZFSet.{u} → ZFSet.{u}) (consts : DeclName → ZFSet.{u})
    (Fs : List (Family L)) : ExtraTyped (standardNames h seed) heads extra consts Fs :=
  fun _ _ _ hx other => absurd (mem_earlierStages.mp hx) other

/-- **The set model of the tower with level names and an admitted list of families**, in a
reading of the names and relative to `CofinalInaccessibles.{u}`: at every fitting assignment of
values with chosen values of the families' types at the names that are no universes, and for
the package with bounds at every valuation that respects them. -/
theorem familyModel (N : NameSets h seed L) {Fs : List (Family L)} (admitted : Admitted Fs)
    (ground : ZFSet.{u}) (ν : Nat → L)
    (groundTyped : ground ∈ universeSet h seed (LevelOrder.bot : L))
    (extra : DeclName → ZFSet.{u} → ZFSet.{u}) :
    ∀ {consts : DeclName → ZFSet.{u}},
      Fits N (headValue N ground ν) extra Fs consts →
      ExtraTyped N (headValue N ground ν) extra consts Fs →
      ∀ {Δ : LevelBounds L}, Δ.Valid ν →
        SetModel (headValue N ground ν) consts (church Δ Fs) := by
  induction admitted with
  | nil =>
    intro consts _ _ Δ valid
    exact
      { universes := universeModel N valid groundTyped []
        headEq := fun same => headEq_values N valid same
        constants := fun {_ T} (found : (none : Option (CTm (Head L) 0)) = some T) =>
          nomatch found
        steps := by
          intro n Γ left right premises step
          cases step with
          | family mem _ => cases mem }
  | @cons F Fs level earlier fresh unused selfFree stable formed instances ih =>
    intro consts fits extraTyped Δ valid
    have whole : Admitted (F :: Fs) :=
      .cons level earlier fresh unused selfFree stable formed instances
    have earlierTyped : ExtraTyped N (headValue N ground ν) extra consts Fs :=
      fun F' mem => extraTyped F' (List.mem_cons_of_mem _ mem)
    have before := ih fits.1 earlierTyped valid
    refine
      { universes := universeModel N valid groundTyped (F :: Fs)
        headEq := fun same => headEq_values N valid same
        constants := ?_
        steps := ?_ }
    · intro n T found
      change (if n = F.name then some (.pi (levelsBelow (.const F.bound)) F.type)
        else declared Fs n) = some T at found
      by_cases isFamily : n = F.name
      · rw [if_pos isFamily] at found
        cases found
        subst isFamily
        change consts F.name ∈ tracePiSet (N.names F.bound)
          (fun x => ev (headValue N ground ν) consts F.type (extend Fin.elim0 x))
        rw [fits.2]
        refine traceLam_graph_mem fun x hx => ?_
        by_cases standard : IsStandard h seed F.bound x
        · rw [if_pos standard]
          obtain ⟨d, below, rfl⟩ := standard
          rw [levelOf_universeSet h seed F.bound below]
          have typed := CDerivable.sound (ih fits.1 earlierTyped (valid_unbounded ν))
            (instances (unbounded L) positive_unbounded (.const d) (stable.fires_const d)
              (fun _ _ => LevelOrder.succ_le_of_lt below)) Fin.elim0 (sat_nil _ _ Fin.elim0)
          rw [ev_inst0] at typed
          exact typed
        · rw [if_neg standard]
          exact extraTyped F (.head _) x hx standard
      · rw [if_neg isFamily] at found
        exact before.constants found
    · intro n Γ left right premises step required holds ρ sat
      cases step with
      | @family F' e mem fires =>
        obtain ⟨F'', mem'', same, rfl⟩ : ∃ F'' ∈ F :: Fs, F''.name = F'.name ∧
            premises = [.typing (levelName e) (levelsBelow (.const F''.bound))] := by
          cases required with
          | family mem'' same => exact ⟨_, mem'', same, rfl⟩
        obtain rfl := whole.eq_of_name_eq mem'' mem same
        have named : universeSet h seed (e.eval ν) ∈ N.names F''.bound :=
          holds _ (List.mem_singleton_self _) ρ sat
        have strict : e.eval ν < F''.bound := N.lt_of_universe_mem named
        rcases List.mem_cons.mp mem with isLatest | earlierMember
        · subst isLatest
          change traceApp (consts F''.name) (universeSet h seed (e.eval ν)) =
            ev (headValue N ground ν) consts (F''.body e).liftClosed ρ
          rw [ev_liftClosed, fits.2, familyValue_at N _ _ extra F'' strict,
            ← ev_evalHead N ground ν consts (F''.body e), stable.body_eval ν fires,
            ev_evalHead]
        · exact before.steps (.family earlierMember fires) (.family earlierMember rfl) holds
            ρ sat

/-! ### Fitting values exist -/

/-- **The values of the constants** of a list of families, built from the earliest family
on. -/
noncomputable def familyValues (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    (extra : DeclName → ZFSet.{u} → ZFSet.{u}) : List (Family L) → DeclName → ZFSet.{u}
  | [] => fun _ => ∅
  | F :: Fs => fun n =>
      if n = F.name then familyValue N heads (familyValues N heads extra Fs) extra F
      else familyValues N heads extra Fs n

/-- Fitting is kept by an assignment that agrees on the declared names and on the constants
the values of the families mention. -/
theorem Fits.congr {N : NameSets h seed L} {heads : Head L → ZFSet.{u}}
    {extra : DeclName → ZFSet.{u} → ZFSet.{u}} :
    ∀ {Fs : List (Family L)} {consts consts' : DeclName → ZFSet.{u}},
      (∀ n, declared Fs n ≠ none → consts' n = consts n) →
      (∀ F ∈ Fs, ∀ d, d < F.bound → ∀ n ∈ termConsts (F.body (.const d)),
        consts' n = consts n) →
      Fits N heads extra Fs consts → Fits N heads extra Fs consts'
  | [], _, _, _, _, _ => trivial
  | F :: Fs, consts, consts', same, bodies, fits => by
    refine ⟨Fits.congr (fun n known => same n ?_)
      (fun F' mem => bodies F' (List.mem_cons_of_mem _ mem)) fits.1, ?_⟩
    · change (if n = F.name then some (CTm.pi (levelsBelow (.const F.bound)) F.type)
        else declared Fs n) ≠ none
      by_cases isFamily : n = F.name
      · rw [if_pos isFamily]
        exact fun impossible => nomatch impossible
      · rw [if_neg isFamily]
        exact known
    · have known : declared (F :: Fs) F.name ≠ none := declared_ne_none_of_mem (.head _)
      rw [same F.name known, fits.2]
      exact familyValue_congr N heads extra F
        (fun d below n mem => (bodies F (.head _) d below n mem).symm)

omit [LevelOrder L] in
/-- A name the package with one more family declared is declared after the family is added. -/
theorem declared_cons_ne_none {F : Family L} {Fs : List (Family L)} {n : DeclName}
    (known : declared Fs n ≠ none) : declared (F :: Fs) n ≠ none := by
  unfold declared
  split
  · exact fun impossible => nomatch impossible
  · exact known

/-- **The values of an admitted family mention only names the package declares**: they are
typed in it. -/
theorem Admitted.body_declared {Fs : List (Family L)} (admitted : Admitted Fs) :
    ∀ F ∈ Fs, ∀ d, d < F.bound → ∀ n ∈ termConsts (F.body (.const d)), declared Fs n ≠ none := by
  induction admitted with
  | nil => exact fun _ mem => nomatch mem
  | @cons F Fs level earlier fresh unused selfFree stable formed instances ih =>
    intro F' mem d below n used
    rcases List.mem_cons.mp mem with rfl | earlierMem
    · have typed := instances (unbounded L) positive_unbounded (.const d) (stable.fires_const d)
        (fun _ _ => LevelOrder.succ_le_of_lt below)
      exact declared_cons_ne_none (CDerivable.consts_declared typed n used)
    · exact declared_cons_ne_none (ih F' earlierMem d below n used)

omit [LevelOrder L] in
/-- A name the package declares is the name of one of its families. -/
theorem exists_family_of_declared :
    ∀ {Fs : List (Family L)} {n : DeclName}, declared Fs n ≠ none → ∃ F ∈ Fs, n = F.name
  | [], _, known => absurd rfl known
  | F :: Fs, n, known => by
    unfold declared at known
    split at known
    · next same => exact ⟨F, .head _, same⟩
    · obtain ⟨F', mem, named⟩ := exists_family_of_declared known
      exact ⟨F', List.mem_cons_of_mem _ mem, named⟩

/-- **The values of the constants fit an admitted list of families.** -/
theorem familyValues_fits (N : NameSets h seed L) (heads : Head L → ZFSet.{u})
    (extra : DeclName → ZFSet.{u} → ZFSet.{u}) {Fs : List (Family L)}
    (admitted : Admitted Fs) : Fits N heads extra Fs (familyValues N heads extra Fs) := by
  induction admitted with
  | nil => trivial
  | @cons F Fs level earlier fresh unused selfFree stable formed instances ih =>
    have elsewhere : ∀ {n : DeclName}, n ≠ F.name →
        familyValues N heads extra (F :: Fs) n = familyValues N heads extra Fs n :=
      fun other => if_neg other
    refine ⟨Fits.congr (fun n known => elsewhere ?_)
      (fun F' mem d below n used => elsewhere ?_) ih, ?_⟩
    · rintro rfl
      exact known fresh
    · rintro rfl
      exact unused F' mem d below used
    · change (if F.name = F.name then
          familyValue N heads (familyValues N heads extra Fs) extra F
        else familyValues N heads extra Fs F.name) =
        familyValue N heads (familyValues N heads extra (F :: Fs)) extra F
      rw [if_pos rfl]
      refine familyValue_congr N heads extra F fun d below n used => (elsewhere ?_).symm
      rintro rfl
      exact selfFree d below used

end Model

/-! ## Soundness and relative consistency -/

section Consistency

/-- `Π (X : U₀). X`, the type without a closed term, over the heads with level names. -/
def emptyType : CTm (Head L) 0 := (TowerInterpretation.emptyType (L := L)).mapHead .tower

/-- It has no element in any reading of the names. -/
theorem ev_emptyType {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} (N : NameSets h seed L)
    (ground : ZFSet.{u}) (ν : Nat → L) (consts : DeclName → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∉ ev (headValue N ground ν) consts (emptyType (L := L)) Fin.elim0 := by
  rw [emptyType, ev_mapHead]
  exact TowerInterpretation.ev_emptyType h seed ground ν consts z

/-- The values of the constants in the standard reading over the empty seed. -/
noncomputable abbrev standardValues (h : CofinalInaccessibles.{u}) (ν : Nat → L)
    (Fs : List (Family L)) : DeclName → ZFSet.{u} :=
  familyValues (standardNames h ∅) (headValue (standardNames h ∅) ∅ ν) (fun _ _ => ∅) Fs

/-- **Soundness** of the annotated judgment of the tower with level names and an admitted list
of families, in the standard reading: a derivation under bounds holds at every valuation that
respects them. -/
theorem sound {Fs : List (Family L)} (admitted : Admitted Fs) (h : CofinalInaccessibles.{u})
    {Δ : LevelBounds L} {ν : Nat → L} (valid : Δ.Valid ν) {s : CStatement (Head L)}
    (derivation : CDerivable (church Δ Fs) s) :
    Holds (headValue (standardNames h ∅) ∅ ν) (standardValues h ν Fs) s :=
  CDerivable.sound
    (familyModel (standardNames h ∅) admitted ∅ ν (empty_mem_universeSet h ∅ LevelOrder.bot)
      (fun _ _ => ∅) (familyValues_fits _ _ _ admitted) (standard_extraTyped _ _ _ _) valid)
    derivation

/-- **Relative consistency.** Under `CofinalInaccessibles.{u}`, no closed annotated term of the
tower with level names and an admitted list of families has type `Π (X : U₀). X`, under any
bounds that some valuation respects. -/
theorem consistent {Fs : List (Family L)} (admitted : Admitted Fs)
    (h : CofinalInaccessibles.{u}) {Δ : LevelBounds L} {ν : Nat → L} (valid : Δ.Valid ν)
    (t : CTm (Head L) 0) : ¬ CDerivable (church Δ Fs) (.typing .nil t emptyType) :=
  CDerivable.no_closed_inhabitant
    (familyModel (standardNames h ∅) admitted ∅ ν (empty_mem_universeSet h ∅ LevelOrder.bot)
      (fun _ _ => ∅) (familyValues_fits _ _ _ admitted) (standard_extraTyped _ _ _ _) valid)
    (ev_emptyType _ ∅ ν _) t

end Consistency

/-! ## The judgment and its standard model at a variable name -/

section Variable

variable {c c' : L} {univ el univ' el' : DeclName}

omit [LevelOrder L] in
/-- The value of the decoder at a closed level is the universe at that level. -/
theorem univ_body_const (c : L) (univ : DeclName) (d : L) :
    (univFamily c univ).body (.const d) = CU d := by
  show universeAt (LevelExpr.instantiate 0 (.const d) 0) = _
  rw [instantiate_zero]

/-- **In the standard reading, the decoders at two bounds agree at a variable name below the
smaller bound.** The names below a level are the universes below it and nothing else, so the
two functions agree on all of them. -/
theorem decoders_agree_holds (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (ν : Nat → L) (lower : c ≤ c') (extra : DeclName → ZFSet.{u} → ZFSet.{u})
    {consts : DeclName → ZFSet.{u}}
    (fits : Fits (standardNames h seed) (headValue (standardNames h seed) ground ν) extra
      (decoders c' univ' el' ++ decoders c univ el) consts) :
    Holds (headValue (standardNames h seed) ground ν) consts
      (.equality (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0))
        (.app (.const univ') (.var 0)) (CU c')) := by
  intro ρ sat
  have named : ρ 0 ∈ earlierStages h seed c := sat 0
  obtain ⟨d, below, known⟩ := mem_earlierStages.mp named
  have lowerValue : consts univ = familyValue (standardNames h seed)
      (headValue (standardNames h seed) ground ν) consts extra (univFamily c univ) :=
    fits.1.1.1.2
  have upperValue : consts univ' = familyValue (standardNames h seed)
      (headValue (standardNames h seed) ground ν) consts extra (univFamily c' univ') :=
    fits.1.2
  have atLower : traceApp (consts univ) (ρ 0) = universeSet h seed d := by
    rw [← known, lowerValue, familyValue_at _ _ _ _ (univFamily c univ) below, univ_body_const]
    rfl
  have atUpper : traceApp (consts univ') (ρ 0) = universeSet h seed d := by
    rw [← known, upperValue,
      familyValue_at _ _ _ _ (univFamily c' univ') (lt_of_lt_of_le below lower),
      univ_body_const]
    rfl
  refine ⟨atLower.trans atUpper.symm, ?_⟩
  change traceApp (consts univ) (ρ 0) ∈ universeSet h seed c'
  rw [atLower]
  exact universeSet_mem_of_lt h seed (lt_of_lt_of_le below lower)

/-! ### The seeded reading separates them -/

variable (L) in
/-- **Values of the four decoders at the name that names no level**: the upper decoder is the
least universe there and the lower one the empty set, with the decoders of members the
identities on those two sets. -/
noncomputable def seededDecoderValue (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u})
    (el univ' el' : DeclName) (n : DeclName) (_x : ZFSet.{u}) : ZFSet.{u} :=
  if n = univ' then universeSet h seed (LevelOrder.bot : L)
  else if n = el' then traceLam (graph (universeSet h seed (LevelOrder.bot : L)) fun A => A)
  else if n = el then traceLam (graph ∅ fun A => A)
  else ∅

/-- In the seeded reading a name that is no universe below the bound is the seed. -/
theorem eq_seed_of_other {h : CofinalInaccessibles.{u}} {seed : ZFSet.{u}} {b : L}
    {x : ZFSet.{u}} (hx : x ∈ (seededNames h seed (L := L)).names b)
    (other : ¬ IsStandard h seed b x) : x = seed := by
  rcases ZFSet.mem_insert_iff.mp hx with same | standard
  · exact same
  · exact absurd (mem_earlierStages.mp standard) other

/-- The seed is a name below every level in the seeded reading, and no universe. -/
theorem seed_other (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (b : L) :
    seed ∈ (seededNames h seed (L := L)).names b ∧ ¬ IsStandard h seed b seed := by
  refine ⟨ZFSet.mem_insert _ _, ?_⟩
  rintro ⟨d, _, same⟩
  have member : universeSet h seed d ∈ universeSet h seed d :=
    Eq.subst (motive := fun x => x ∈ universeSet h seed d) same.symm
      (seed_mem_universeSet h seed d)
  exact ZFSet.mem_irrefl _ member

section SeededValues

variable (h : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) (x : ZFSet.{u})

/-- At the extra name the upper decoder is the least universe. -/
theorem seededDecoderValue_upper :
    seededDecoderValue L h seed el univ' el' univ' x =
      universeSet h seed (LevelOrder.bot : L) := if_pos rfl

/-- At the extra name the upper decoder of members is the identity on the least universe. -/
theorem seededDecoderValue_upperEl (distinct' : el' ≠ univ') :
    seededDecoderValue L h seed el univ' el' el' x =
      traceLam (graph (universeSet h seed (LevelOrder.bot : L)) fun A => A) := by
  rw [seededDecoderValue, if_neg distinct', if_pos rfl]

/-- At the extra name the lower decoder is the empty set. -/
theorem seededDecoderValue_lower (distinct : el ≠ univ) (univNotUniv : univ' ≠ univ)
    (elNotUniv : el' ≠ univ) : seededDecoderValue L h seed el univ' el' univ x = ∅ := by
  rw [seededDecoderValue, if_neg (Ne.symm univNotUniv), if_neg (Ne.symm elNotUniv),
    if_neg (Ne.symm distinct)]

/-- At the extra name the lower decoder of members is the function on the empty set. -/
theorem seededDecoderValue_lowerEl (univNotEl : univ' ≠ el) (elNotEl : el' ≠ el) :
    seededDecoderValue L h seed el univ' el' el x = traceLam (graph ∅ fun A => A) := by
  rw [seededDecoderValue, if_neg (Ne.symm univNotEl), if_neg (Ne.symm elNotEl), if_pos rfl]

end SeededValues

/-- **The chosen values of the four decoders at the extra name are of their types.** -/
theorem seeded_extraTyped (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (ν : Nat → L) (positive' : LevelOrder.bot < c') (distinct : el ≠ univ)
    (distinct' : el' ≠ univ') (univNotEl : univ' ≠ el) (univNotUniv : univ' ≠ univ)
    (elNotEl : el' ≠ el) (elNotUniv : el' ≠ univ) {consts : DeclName → ZFSet.{u}}
    (fits : Fits (seededNames h seed) (headValue (seededNames h seed) ground ν)
      (seededDecoderValue L h seed el univ' el') (decoders c' univ' el' ++ decoders c univ el)
      consts) :
    ExtraTyped (seededNames h seed) (headValue (seededNames h seed) ground ν)
      (seededDecoderValue L h seed el univ' el') consts
      (decoders c' univ' el' ++ decoders c univ el) := by
  have upperValue : consts univ' = familyValue (seededNames h seed)
      (headValue (seededNames h seed) ground ν) consts
      (seededDecoderValue L h seed el univ' el') (univFamily c' univ') := fits.1.2
  have lowerValue : consts univ = familyValue (seededNames h seed)
      (headValue (seededNames h seed) ground ν) consts
      (seededDecoderValue L h seed el univ' el') (univFamily c univ) := fits.1.1.1.2
  have upperApp : traceApp (consts univ') seed = universeSet h seed (LevelOrder.bot : L) := by
    rw [upperValue, familyValue_extra _ _ _ _ (univFamily c' univ') (seed_other h seed c').1
      (seed_other h seed c').2]
    exact seededDecoderValue_upper h seed seed
  have lowerApp : traceApp (consts univ) seed = ∅ := by
    rw [lowerValue, familyValue_extra _ _ _ _ (univFamily c univ) (seed_other h seed c).1
      (seed_other h seed c).2]
    exact seededDecoderValue_lower h seed seed distinct univNotUniv elNotUniv
  intro F mem x hx other
  rw [eq_seed_of_other hx other]
  rcases List.mem_cons.mp mem with rfl | mem
  · change seededDecoderValue L h seed el univ' el' el' seed ∈
      tracePiSet (traceApp (consts univ') seed) (fun _ => universeSet h seed c')
    rw [seededDecoderValue_upperEl h seed seed distinct', upperApp]
    exact traceLam_graph_mem fun A hA => universeSet_mono h seed (LevelOrder.bot_le c') hA
  · rcases List.mem_cons.mp mem with rfl | mem
    · change seededDecoderValue L h seed el univ' el' univ' seed ∈ universeSet h seed c'
      rw [seededDecoderValue_upper]
      exact universeSet_mem_of_lt h seed positive'
    · rcases List.mem_cons.mp mem with rfl | mem
      · change seededDecoderValue L h seed el univ' el' el seed ∈
          tracePiSet (traceApp (consts univ) seed) (fun _ => universeSet h seed c)
        rw [seededDecoderValue_lowerEl h seed seed univNotEl elNotEl, lowerApp]
        exact traceLam_graph_mem fun A hA => absurd hA (ZFSet.notMem_empty A)
      · obtain rfl := List.mem_singleton.mp mem
        change seededDecoderValue L h seed el univ' el' univ seed ∈ universeSet h seed c
        rw [seededDecoderValue_lower h seed seed distinct univNotUniv elNotUniv]
        exact empty_mem_universeSet h seed c

/-- **The judgment does not derive that the decoders at two bounds agree at a variable name.**
Relative to `CofinalInaccessibles.{u}`: in the seeded reading the two decoders differ at the
name that names no level. With `decoders_agree_holds`: the equation holds in the standard
reading and is not derivable. -/
theorem decoders_agree_not_derivable (h : CofinalInaccessibles.{u})
    (positive : LevelOrder.bot < c) (positive' : LevelOrder.bot < c') (distinct : el ≠ univ)
    (distinct' : el' ≠ univ') (univNotEl : univ' ≠ el) (univNotUniv : univ' ≠ univ)
    (elNotEl : el' ≠ el) (elNotUniv : el' ≠ univ) :
    ¬ CDerivable (church (unbounded L) (decoders c' univ' el' ++ decoders c univ el))
      (.equality (.snoc .nil (levelsBelow (.const c))) (.app (.const univ) (.var 0))
        (.app (.const univ') (.var 0)) (CU c')) := by
  intro derivation
  have admitted := twoDecoders_admitted (c := c) (c' := c') positive positive' distinct
    distinct' univNotEl univNotUniv elNotEl elNotUniv
  obtain ⟨consts, fits⟩ : ∃ consts : DeclName → ZFSet.{u},
      Fits (seededNames h ∅) (headValue (seededNames h ∅) ∅ fun _ => (LevelOrder.bot : L))
        (seededDecoderValue L h ∅ el univ' el')
        (decoders c' univ' el' ++ decoders c univ el) consts :=
    ⟨_, familyValues_fits _ _ _ admitted⟩
  have extraTyped := seeded_extraTyped h ∅ ∅ (fun _ => (LevelOrder.bot : L)) positive'
    distinct distinct' univNotEl univNotUniv elNotEl elNotUniv fits
  have model := familyModel (seededNames h ∅) admitted ∅ (fun _ => LevelOrder.bot)
    (empty_mem_universeSet h ∅ LevelOrder.bot) _ fits extraTyped (valid_unbounded _)
  have holds := CDerivable.sound model derivation (extend Fin.elim0 ∅)
    ((sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, (seed_other h ∅ c).1⟩)
  have equal : traceApp (consts univ) ∅ = traceApp (consts univ') ∅ := holds.1
  have upperValue : consts univ' = familyValue (seededNames h ∅)
      (headValue (seededNames h ∅) ∅ fun _ => (LevelOrder.bot : L)) consts
      (seededDecoderValue L h ∅ el univ' el') (univFamily c' univ') := fits.1.2
  have lowerValue : consts univ = familyValue (seededNames h ∅)
      (headValue (seededNames h ∅) ∅ fun _ => (LevelOrder.bot : L)) consts
      (seededDecoderValue L h ∅ el univ' el') (univFamily c univ) := fits.1.1.1.2
  rw [lowerValue, familyValue_extra _ _ _ _ (univFamily c univ) (seed_other h ∅ c).1
      (seed_other h ∅ c).2, upperValue,
    familyValue_extra _ _ _ _ (univFamily c' univ') (seed_other h ∅ c').1
      (seed_other h ∅ c').2] at equal
  have atSeed : seededDecoderValue L h ∅ el univ' el' univ ∅ =
      seededDecoderValue L h ∅ el univ' el' univ' ∅ := equal
  rw [seededDecoderValue_lower h ∅ ∅ distinct univNotUniv elNotUniv,
    seededDecoderValue_upper] at atSeed
  have member : (∅ : ZFSet.{u}) ∈ universeSet h ∅ (LevelOrder.bot : L) :=
    empty_mem_universeSet h ∅ LevelOrder.bot
  rw [← atSeed] at member
  exact ZFSet.notMem_empty _ member

end Variable

/-! ## Further negative examples -/

section Controls

/-- A family with the value `U_c` at the type `U_c` at every level. -/
def selfFamily (c : L) (self : DeclName) : Family L :=
  Family.pointwise self c (CU c) (fun _ => CU c)

/-- **A family with a value that is not of its type has no set model**: with the value `U_c`
at the type `U_c`, the root step at the name of a level below `c` would make the universe at
`c` a member of itself. -/
theorem untyped_instance_no_setModel (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (ν : Nat → L) (consts : DeclName → ZFSet.{u}) {c d : L} (below : d < c) (self : DeclName) :
    ¬ SetModel (headValue (standardNames h seed) ground ν) consts
      (church (unbounded L) [selfFamily c self]) := by
  intro model
  have typed : consts self ∈
      tracePiSet (earlierStages h seed c) (fun _ => universeSet h seed c) :=
    model.constants (c := self) (T := .pi (levelsBelow (.const c)) (CU c)) (if_pos rfl)
  have step : CStep [selfFamily c self]
      (.app (.const self) (levelName (.const d)) : CTm (Head L) 0) (CU c) :=
    CStep.family (n := 0) (F := selfFamily c self) (e := .const d) (.head _) ⟨d, rfl⟩
  have inBound : universeSet h seed d ∈ earlierStages h seed c :=
    mem_earlierStages.mpr ⟨d, below, rfl⟩
  have equal : traceApp (consts self) (universeSet h seed d) = universeSet h seed c :=
    model.steps (Γ := .nil) step (.family (F := selfFamily c self) (.head _) rfl)
      (by
        intro premise member
        obtain rfl := List.mem_singleton.mp member
        exact fun _ _ => inBound)
      Fin.elim0 (sat_nil _ _ Fin.elim0)
  have member : traceApp (consts self) (universeSet h seed d) ∈ universeSet h seed c :=
    traceApp_mem_fibre typed inBound
  rw [equal] at member
  exact universeSet_no_self_membership h seed c member

/-- **Without the bound the universe above a level parameter is not a member of the universe
at a closed level**: at the parameter's value `c` the universe above `c` would be a member of
the universe at `c`. Relative to `CofinalInaccessibles.{u}`. -/
theorem next_not_typed_unbounded (h : CofinalInaccessibles.{u}) (c : L) :
    ¬ CDerivable (church (unbounded L) ([] : List (Family L)))
      (.typing .nil nextTerm (CU c)) := by
  intro typed
  have holds : universeSet h ∅ (LevelOrder.succ c) ∈ universeSet h ∅ c :=
    sound .nil h (valid_unbounded fun _ => c) typed Fin.elim0 (sat_nil _ _ Fin.elim0)
  exact ZFSet.mem_asymm holds (universeSet_mem_of_lt h ∅ (LevelOrder.lt_succ c))

/-! ### The declared types without the root steps -/

/-- The rule package with the declared types of a list of families and no root step. -/
def declaredRules (Fs : List (Family L)) : Rules (Head L) :=
  { baseRules (unbounded L) with constantType := fun n => (declared Fs n).map CTm.erase }

/-- The annotation of the package without root steps. -/
def declaredChurch (Fs : List (Family L)) : ChurchRules (declaredRules Fs) where
  constantType := declared Fs
  computation := .empty
  erase_constantType := fun _ => rfl
  erase_step := fun step => step.elim

variable (h : CofinalInaccessibles.{u}) (c : L) (univ el : DeclName)

/-- A value of the decoder that is constant: every name is sent to the universe at the least
level. -/
noncomputable def constantUnivValue : ZFSet.{u} :=
  traceLam (graph (earlierStages h ∅ c) fun _ => universeSet h ∅ (LevelOrder.bot : L))

/-- The matching value of the decoder of members: the identity on the least universe. -/
noncomputable def constantElValue : ZFSet.{u} :=
  traceLam (graph (earlierStages h ∅ c) fun _ =>
    traceLam (graph (universeSet h ∅ (LevelOrder.bot : L)) fun A => A))

/-- The constants with the decoder constant. -/
noncomputable def constantValue (n : DeclName) : ZFSet.{u} :=
  if n = univ then constantUnivValue h c
  else if n = el then constantElValue h c
  else ∅

variable {univ el}

/-- The set model of the declared types of the decoders with the constant decoder. -/
theorem rigidModel (positive : LevelOrder.bot < c) (distinct : el ≠ univ) :
    SetModel (headValue (standardNames h ∅) ∅ fun _ => (LevelOrder.bot : L))
      (constantValue h c univ el) (declaredChurch (decoders c univ el)) where
  universes :=
    { universeModel (standardNames h ∅) (Δ := unbounded L) (valid_unbounded _)
        (empty_mem_universeSet h ∅ LevelOrder.bot) [] with }
  headEq := fun same =>
    headEq_values (standardNames h ∅) (Δ := unbounded L) (valid_unbounded _) same
  constants := by
    intro n T found
    change (if n = el then some (CTm.pi (levelsBelow (.const c)) (elFamily c univ el).type)
      else if n = univ then some (CTm.pi (levelsBelow (.const c)) (CU c))
      else none) = some T at found
    have univValue : constantValue h c univ el univ = constantUnivValue h c := if_pos rfl
    by_cases isEl : n = el
    · rw [if_pos isEl] at found
      cases found
      subst isEl
      have elValue : constantValue h c univ n n = constantElValue h c := by
        rw [constantValue, if_neg distinct, if_pos rfl]
      change constantValue h c univ n n ∈ tracePiSet (earlierStages h ∅ c)
        (fun x => tracePiSet (traceApp (constantValue h c univ n univ) x)
          (fun _ => universeSet h ∅ c))
      rw [elValue, univValue]
      refine traceLam_graph_mem fun x hx => ?_
      show traceLam (graph (universeSet h ∅ (LevelOrder.bot : L)) fun A => A) ∈
        tracePiSet (traceApp (constantUnivValue h c) x) (fun _ => universeSet h ∅ c)
      rw [constantUnivValue, traceApp_graph_beta _ hx]
      exact traceLam_graph_mem fun A hA => universeSet_mono h ∅ (le_of_lt positive) hA
    · rw [if_neg isEl] at found
      by_cases isUniv : n = univ
      · rw [if_pos isUniv] at found
        cases found
        subst isUniv
        change constantValue h c n el n ∈
          tracePiSet (earlierStages h ∅ c) (fun _ => universeSet h ∅ c)
        rw [univValue]
        exact traceLam_graph_mem fun _ _ => universeSet_mem_of_lt h ∅ positive
      · rw [if_neg isUniv] at found
        cases found
  steps := fun step => step.elim

include h in
/-- **Without the root steps the decoder at a name is not provably the universe it names**,
for a name of a level above the least one: in the model with the constant decoder the two have
different values. -/
theorem rigid_not_equal (distinct : el ≠ univ) {d : L} (positive : LevelOrder.bot < d)
    (below : d < c) :
    ¬ CDerivable (declaredChurch (decoders c univ el))
      (.equality .nil (.app (.const univ) (levelName (.const d))) (CU d) (CU c)) := by
  intro equal
  have holds := CDerivable.sound (rigidModel h c (lt_trans positive below) distinct) equal
    Fin.elim0 (sat_nil _ _ Fin.elim0)
  have values : traceApp (constantValue h c univ el univ) (universeSet h ∅ d) =
      universeSet h ∅ d := holds.1
  have univValue : constantValue h c univ el univ = constantUnivValue h c := if_pos rfl
  rw [univValue, constantUnivValue,
    traceApp_graph_beta _ (mem_earlierStages.mpr ⟨d, below, rfl⟩)] at values
  exact ne_of_lt positive (universeSet_injective h ∅ values)

end Controls

/-! ## Over the notations below `ε₀` -/

/-- **Over the notations, the package with the decoders below `ω` and below `ω + 1` is
consistent**, relative to `CofinalInaccessibles.{u}`: the package in which the type of the
families of types over the finite levels is a member of the universe named by `ω`. -/
theorem finiteLevels_consistent (h : CofinalInaccessibles.{u}) (t : CTm (Head Level) 0) :
    ¬ CDerivable
      (church (unbounded Level)
        (decoders (LevelOrder.succ Level.omega) (.str .anonymous "univAbove")
            (.str .anonymous "elAbove") ++
          decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.typing .nil t emptyType) :=
  consistent
    (twoDecoders_admitted Level.isLimit_omega.1
      (lt_trans Level.isLimit_omega.1 (LevelOrder.lt_succ Level.omega))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    h (valid_unbounded fun _ => LevelOrder.bot) t

/-- **Over the notations, the decoder below `ω` and the decoder below `ω + 1` are not provably
equal at a variable name of a finite level**, relative to `CofinalInaccessibles.{u}`, although
they are equal at the name of every finite level (`decoders_agree_at`). -/
theorem finiteDecoders_agree_not_derivable (h : CofinalInaccessibles.{u}) :
    ¬ CDerivable
      (church (unbounded Level)
        (decoders (LevelOrder.succ Level.omega) (.str .anonymous "univAbove")
            (.str .anonymous "elAbove") ++
          decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.equality (.snoc .nil (levelsBelow (.const Level.omega)))
        (.app (.const (.str .anonymous "univ")) (.var 0))
        (.app (.const (.str .anonymous "univAbove")) (.var 0))
        (CU (LevelOrder.succ Level.omega))) :=
  decoders_agree_not_derivable h Level.isLimit_omega.1
    (lt_trans Level.isLimit_omega.1 (LevelOrder.lt_succ Level.omega))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end LevelNames
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
