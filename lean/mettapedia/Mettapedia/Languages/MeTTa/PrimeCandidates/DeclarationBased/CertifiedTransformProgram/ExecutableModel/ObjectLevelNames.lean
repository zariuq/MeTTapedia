import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.LevelNamesModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MappedSchemas
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEmbedding

/-!
# The object package with level names

The object package has the numbers, the sets, the propositions and their recursors, at the
universes `U₀` and `U₁` of the tower over the finite levels. The tower with level names, over
any level order, has types of names of levels and families of constants over them, among them
the polymorphic identity. This module puts the two in one judgment and gives it one set model.

* **The package** (`objectNames Δ Fs`), over a level order `L`: the tower with level names and
  a list of families `Fs`, together with the object package read at the heads with level names
  (`objectAtNames`): its finite levels are sent to the finite levels of `L` (`towerHead`). Its
  steps are the steps of the families and the instances of the object package's schemas at
  terms of the larger language.
* **Both parts are contained in it**: every derivation of the tower with level names
  (`objectNames_of_names`), and every derivation of the object package with its heads mapped
  (`objectNames_of_object`), when the families' names are not names of the object package.
* **One set model** (`objectNames_model`), relative to `CofinalInaccessibles`: the tower over
  `L` seeded with the natural numbers, in the standard reading of the names, with the object
  package's values at its names and the families' values at theirs. The finite stages of the
  tower over `L` are the stages of the tower over the natural numbers
  (`objectNamesHeads_tower`), so the object package keeps its values. Hence soundness
  (`objectNames_sound`) and consistency (`objectNames_consistent`): the type `Π (X : U₀). X`
  has no closed term.

Positive examples: the polymorphic identity at the name of the least level, applied to the type
of the numbers and to the numeral one, is typed at the numbers and equal to the numeral one
(`identity_num_one`); over the natural numbers with names below `3` (`identity_num_one_nat`),
and over the ordinal notations with the names of all finite levels (`identity_num_one_omega`).
The identity law, proved once for every level below the bound, applies to the numbers
(`polyId_law_num_one`, `polyId_law_num_one_omega`): the type of the numbers is a member of the
universe a name names, because the decoders compute at the name.
Negative examples: no closed term has the empty type (`objectNames_consistent`), and a family
that takes the name of the numbers is not apart from the object package (`not_apart_num`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet)
open LevelNames (church baseRules Family Admitted declared headValue standardNames
  familyModel familyValues familyValues_fits standard_extraTyped universeModel headEq_values
  Fits levelName universeAt levelsBelow identityFamily decoders identity_admitted identity_at
  exists_family_of_declared declared_eq_none polyId polyId_law decoders_admitted univ_at
  el_step)

universe u

namespace CodeModel

variable {L : Type} [LevelOrder L]

/-! ## The package -/

section Package

variable (L) in
/-- A head of the tower over the finite levels as a head of the tower over `L` with level
names: its level constants are the finite levels of `L`. -/
def towerHead : Tower.Head → LevelNames.Head L := fun t =>
  .tower (LevelTower.Head.map (LevelOrder.Embedding.ofNat L) t)

/-- The order of the universes under bounds contains the order at every valuation. -/
theorem cumulativeUnder_of_cumulative (Δ : LevelBounds L) :
    ∀ {u v : LevelTower.Head L}, LevelTower.Cumulative u v → LevelTower.CumulativeUnder Δ u v
  | .sort _, .sort _, below => fun ν _ => below ν
  | .legacyGround, .legacyGround, below => below.elim
  | .legacyGround, .sort _, below => below.elim
  | .sort _, .legacyGround, below => below.elim

/-- The equality of the heads under bounds contains the equality at every valuation. -/
theorem headEqUnder_of_headEq (Δ : LevelBounds L) :
    ∀ {u v : LevelTower.Head L}, LevelTower.HeadEq u v → LevelTower.HeadEqUnder Δ u v
  | .sort _, .sort _, same => fun ν _ => same ν
  | .legacyGround, .legacyGround, _ => trivial
  | .legacyGround, .sort _, same => same.elim
  | .sort _, .legacyGround, same => same.elim

/-- The object package read at the heads of the tower over `L` with level names. -/
def objectAtNames (Δ : LevelBounds L) :
    ChurchRules (Rules.mapSchemas (towerHead L) (baseRules Δ) objectRules objectSchemas) :=
  ChurchRules.mapSchemas (towerHead L) (baseRules Δ) objectRules objectSchemas

/-- **The object package with level names**, and with a list of families of constants over the
names. -/
def objectNames (Δ : LevelBounds L) (Fs : List (Family L)) :
    ChurchRules (Rules.sum (LevelNames.rules Δ Fs)
      (Rules.mapSchemas (towerHead L) (baseRules Δ) objectRules objectSchemas)) :=
  (church Δ Fs).sum (objectAtNames Δ)

/-- The names of the families are not names of the object package. -/
def Apart (Fs : List (Family L)) : Prop := ∀ F ∈ Fs, objectDeclared F.name = false

/-- **The object package maps into its reading at the heads with level names.** -/
theorem objectAtNames_morphism (Δ : LevelBounds L) :
    objectChurch.Morphism (objectAtNames Δ) (towerHead L) :=
  ChurchRules.mapSchemas_morphism (towerHead L) (baseRules Δ) objectRules objectSchemas
    objectRules_presents
    (fun typing => LevelNames.HeadTyping.tower
      ((LevelTower.morphism (LevelOrder.Embedding.ofNat L)).headTyping typing))
    (fun isUniverse => LevelNames.IsUniverse.tower
      ((LevelTower.morphism (LevelOrder.Embedding.ofNat L)).isUniverse isUniverse))
    (fun joined => LevelNames.Join.tower
      ((LevelTower.morphism (LevelOrder.Embedding.ofNat L)).join joined))
    (fun below => cumulativeUnder_of_cumulative Δ
      ((LevelTower.morphism (LevelOrder.Embedding.ofNat L)).cumulative below))
    (fun same => headEqUnder_of_headEq Δ
      ((LevelTower.morphism (LevelOrder.Embedding.ofNat L)).headEq same))

/-- A name the object package declares at the heads with level names is one of its names. -/
theorem objectAtNames_declared {Δ : LevelBounds L} {c : DeclName}
    {D : CTm (LevelNames.Head L) 0} (known : (objectAtNames Δ).constantType c = some D) :
    objectDeclared c = true := by
  have known' : mapDecls (towerHead L) (elabDeclarations objectRules.constantType) c =
      some D := by
    rw [← ChurchRules.mapSchemas_constantType (towerHead L) (baseRules Δ) objectRules
      objectSchemas]
    exact known
  unfold objectDeclared
  cases found : objectRules.constantType c with
  | none =>
    unfold mapDecls elabDeclarations at known'
    rw [found] at known'
    exact nomatch known'
  | some _ => rfl

/-- The families declare none of the object package's names. -/
theorem objectNames_fresh {Δ : LevelBounds L} {Fs : List (Family L)} (apart : Apart Fs)
    {c : DeclName} {D : CTm (LevelNames.Head L) 0}
    (known : (objectAtNames Δ).constantType c = some D) : (church Δ Fs).constantType c = none :=
  declared_eq_none fun F mem same => by
    have here := objectAtNames_declared known
    rw [same, apart F mem] at here
    exact nomatch here

/-- **Every derivation of the tower with level names is a derivation of the package.** -/
theorem objectNames_of_names {Δ : LevelBounds L} {Fs : List (Family L)}
    {s : CStatement (LevelNames.Head L)} (derivation : CDerivable (church Δ Fs) s) :
    CDerivable (objectNames Δ Fs) s :=
  CDerivable.sum_left _ derivation

/-- **Every derivation of the object package is a derivation of the package**, with its heads
read as heads of the tower over `L` with level names. -/
theorem objectNames_of_object {Δ : LevelBounds L} {Fs : List (Family L)} (apart : Apart Fs)
    {s : CStatement Tower.Head} (derivation : CDerivable objectChurch s) :
    CDerivable (objectNames Δ Fs) (s.mapHead (towerHead L)) :=
  (CDerivable.mapHead (objectAtNames_morphism Δ) derivation).mono
    (ChurchRulesSub.sum_right (church Δ Fs) (objectAtNames Δ) id id id id id
      fun known => objectNames_fresh apart known)

end Package

/-! ## The set model -/

section Model

variable (h : CofinalInaccessibles.{u})

variable (L) in
/-- The values of the heads: the tower over `L` seeded with the natural numbers, in the
standard reading of the names, at the least valuation of the level parameters. -/
noncomputable abbrev objectNamesHeads : LevelNames.Head L → ZFSet.{u} :=
  headValue (standardNames h ZFSet.omega) ∅ fun _ => LevelOrder.bot

/-- **The heads of the object package keep their values**: the finite stages of the tower over
`L` are the stages of the tower over the natural numbers. -/
theorem objectNamesHeads_tower :
    (fun t => objectNamesHeads L h (towerHead L t)) = objHeads h := by
  funext t
  cases t with
  | legacyGround => rfl
  | sort e =>
    show universeSet h ZFSet.omega
        ((e.map (LevelOrder.Embedding.ofNat L)).eval fun _ => LevelOrder.bot) =
      universeSet h ZFSet.omega (e.eval fun _ => 0)
    have value := LevelExpr.eval_map (LevelOrder.Embedding.ofNat L) (fun _ => 0) e
    have least : (fun _ : Nat => (LevelOrder.bot : L)) =
        fun i => (LevelOrder.Embedding.ofNat L) ((fun _ : Nat => (0 : Nat)) i) := rfl
    rw [least, value]
    exact ZFSetInterpretation.universeSet_map h ZFSet.omega (LevelOrder.Embedding.ofNat L)
      (LevelOrder.Embedding.ofNat_initial L) _

variable (L) in
/-- **The values of the constants**: the object package's at its names, the families' at
theirs. -/
noncomputable def objectNamesConsts (Fs : List (Family L)) : DeclName → ZFSet.{u} := fun c =>
  if objectDeclared c = true then objectSetConsts h c
  else familyValues (standardNames h ZFSet.omega) (objectNamesHeads L h) (fun _ _ => ∅) Fs c

theorem objectNamesConsts_object {Fs : List (Family L)} {c : DeclName}
    (known : objectDeclared c = true) : objectSetConsts h c = objectNamesConsts L h Fs c :=
  (if_pos known).symm

theorem objectNamesConsts_family {Fs : List (Family L)} {c : DeclName}
    (other : objectDeclared c = false) :
    objectNamesConsts L h Fs c =
      familyValues (standardNames h ZFSet.omega) (objectNamesHeads L h) (fun _ _ => ∅) Fs c :=
  if_neg (by rw [other]; exact fun impossible => nomatch impossible)

/-- The values fit the families: at the families' names and in the families' values they are
the families' own. -/
theorem objectNames_fits {Fs : List (Family L)} (admitted : Admitted Fs) (apart : Apart Fs) :
    Fits (standardNames h ZFSet.omega) (objectNamesHeads L h) (fun _ _ => ∅) Fs
      (objectNamesConsts L h Fs) := by
  have family : ∀ n, declared Fs n ≠ none →
      objectNamesConsts L h Fs n =
        familyValues (standardNames h ZFSet.omega) (objectNamesHeads L h) (fun _ _ => ∅)
          Fs n := by
    intro n known
    obtain ⟨F, mem, rfl⟩ := exists_family_of_declared known
    exact objectNamesConsts_family h (apart F mem)
  exact Fits.congr family
    (fun F mem d below n used => family n (admitted.body_declared F mem d below n used))
    (familyValues_fits _ _ _ admitted)

/-- **The object package with level names has a set model**, relative to
`CofinalInaccessibles`: for an admitted list of families whose names are not names of the
object package, and positive bounds on the level parameters. -/
theorem objectNames_model {Fs : List (Family L)} (admitted : Admitted Fs) (apart : Apart Fs)
    {Δ : LevelBounds L} (positive : Δ.Positive) :
    SetModel (objectNamesHeads L h) (objectNamesConsts L h Fs) (objectNames Δ Fs) :=
  SetModel.sum
    (familyModel (standardNames h ZFSet.omega) admitted ∅ (fun _ => LevelOrder.bot)
      (empty_mem_universeSet h ZFSet.omega LevelOrder.bot) (fun _ _ => ∅)
      (objectNames_fits h admitted apart) (standard_extraTyped _ _ _ _) positive.valid_bot)
    (SetModel.mapSchemas (towerHead L)
      { (universeModel (standardNames h ZFSet.omega) positive.valid_bot
          (empty_mem_universeSet h ZFSet.omega LevelOrder.bot) Fs) with }
      (fun same => headEq_values (standardNames h ZFSet.omega) positive.valid_bot same)
      (fun known => by
        rw [objectNamesHeads_tower h]
        exact (objectSetModel_agreeing h
          fun _ declared => objectNamesConsts_object h declared).constants known)
      (by
        rw [objectNamesHeads_tower h]
        exact fun rule =>
          (SetTower.objectSchemas_valid h rule).of_closed (objectSchemas_closed rule)
            fun _ declared => objectNamesConsts_object h declared))

/-- **Soundness**: every derivable statement of the package holds in the model. -/
theorem objectNames_sound {Fs : List (Family L)} (admitted : Admitted Fs) (apart : Apart Fs)
    {Δ : LevelBounds L} (positive : Δ.Positive) {s : CStatement (LevelNames.Head L)}
    (derivation : CDerivable (objectNames Δ Fs) s) :
    Holds (objectNamesHeads L h) (objectNamesConsts L h Fs) s :=
  CDerivable.sound (objectNames_model h admitted apart positive) derivation

include h in
/-- **Consistency**, relative to `CofinalInaccessibles`: no closed term of the package has the
type `Π (X : U₀). X`. -/
theorem objectNames_consistent {Fs : List (Family L)} (admitted : Admitted Fs)
    (apart : Apart Fs) {Δ : LevelBounds L} (positive : Δ.Positive)
    (t : CTm (LevelNames.Head L) 0) :
    ¬ CDerivable (objectNames Δ Fs) (.typing .nil t LevelNames.emptyType) :=
  CDerivable.no_closed_inhabitant (objectNames_model h admitted apart positive)
    (LevelNames.ev_emptyType _ ∅ _ _) t

end Model

/-! ## The polymorphic identity at the numbers -/

section Client

omit [LevelOrder L] in
/-- Negative: a list with a family that takes the name of the type of the numbers is not apart
from the object package. -/
theorem not_apart_num (F : Family L) (named : F.name = numN) (Fs : List (Family L)) :
    ¬ Apart (F :: Fs) := fun apart => by
  have here := apart F (.head _)
  rw [named] at here
  exact absurd here (by decide)

/-- **The polymorphic identity at the name of the least level, applied to the type of the
numbers and to the numeral one, is the numeral one**, at the type of the numbers: one judgment
with the level names, a family over them and the object package's numbers. The family computes
at the name, and the two abstractions of its value are applied by the judgment's own rule. -/
theorem identity_num_one {c : L} (positive : LevelOrder.bot < c) {univ el identity : DeclName}
    (distinct : el ≠ univ) (notUniv : identity ≠ univ) (notEl : identity ≠ el)
    (apart : Apart (identityFamily c univ el identity :: decoders c univ el))
    {Δ : LevelBounds L} (positiveBounds : Δ.Positive) :
    CDerivable (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.equality .nil
        (.app (.app (.app (.const identity) (levelName (.const LevelOrder.bot)))
          (.const numN)) (.app (.const sucN) (.const zeroN)))
        (.app (.const sucN) (.const zeroN)) (.const numN)) := by
  have atZero : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.equality .nil (.app (.const identity) (levelName (.const LevelOrder.bot)))
        (.lam (universeAt (.const LevelOrder.bot)) (.lam (.var 0) (.var 0)))
        (.pi (universeAt (.const LevelOrder.bot)) (.pi (.var 0) (.var 1)))) :=
    objectNames_of_names
      (identity_at positive distinct notUniv notEl positiveBounds
        fun _ _ => LevelOrder.succ_le_of_lt positive)
  have numTyped : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing .nil (.const numN) (universeAt (.const LevelOrder.bot))) :=
    objectNames_of_object apart (cnum_typed (Γ := .nil))
  have numInContext : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing (.snoc .nil (.const numN)) (.const numN) (universeAt (.const LevelOrder.bot))) :=
    objectNames_of_object apart (cnum_typed (Γ := .snoc .nil cnum))
  have oneTyped : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing .nil (.app (.const sucN) (.const zeroN)) (.const numN)) :=
    objectNames_of_object apart (csuc_typed (Γ := .nil) czero_typed)
  have isSort {e : LevelExpr L} :
      (Rules.sum (LevelNames.rules Δ (identityFamily c univ el identity :: decoders c univ el))
        (Rules.mapSchemas (towerHead L) (baseRules Δ) objectRules
          objectSchemas)).isUniverse (.tower (.sort e)) :=
    LevelNames.IsUniverse.tower (.sort e)
  have universeTyped : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing .nil (universeAt (.const LevelOrder.bot))
        (universeAt (.succ (.const LevelOrder.bot)))) :=
    .headType (LevelNames.HeadTyping.tower (.sort _))
  have member : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing (.snoc .nil (universeAt (.const LevelOrder.bot))) (.var 0)
        (universeAt (.const LevelOrder.bot))) := .var 0
  have again : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing (.snoc (.snoc .nil (universeAt (.const LevelOrder.bot))) (.var 0)) (.var 1)
        (universeAt (.const LevelOrder.bot))) := .var 1
  have element : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing (.snoc (.snoc .nil (universeAt (.const LevelOrder.bot))) (.var 0)) (.var 0)
        (.var 1)) := .var 0
  have inner : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing (.snoc .nil (universeAt (.const LevelOrder.bot))) (.pi (.var 0) (.var 1))
        (universeAt (.max (.const LevelOrder.bot) (.const LevelOrder.bot)))) :=
    .piForm member isSort again isSort (LevelNames.Join.tower (.sorts _ _))
  have whole : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing .nil (.pi (universeAt (.const LevelOrder.bot)) (.pi (.var 0) (.var 1)))
        (universeAt (.max (.succ (.const LevelOrder.bot))
          (.max (.const LevelOrder.bot) (.const LevelOrder.bot))))) :=
    .piForm universeTyped isSort inner isSort (LevelNames.Join.tower (.sorts _ _))
  have body : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing (.snoc .nil (universeAt (.const LevelOrder.bot))) (.lam (.var 0) (.var 0))
        (.pi (.var 0) (.var 1))) :=
    .lamIntro member isSort inner isSort element
  have applied : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.equality .nil
        (.app (.app (.const identity) (levelName (.const LevelOrder.bot))) (.const numN))
        (.app (.lam (universeAt (.const LevelOrder.bot)) (.lam (.var 0) (.var 0))) (.const numN))
        (.pi (.const numN) (.const numN))) :=
    .appCong atZero (.refl numTyped)
  have unfolded : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.equality .nil
        (.app (.lam (universeAt (.const LevelOrder.bot)) (.lam (.var 0) (.var 0))) (.const numN))
        (.lam (.const numN) (.var 0)) (.pi (.const numN) (.const numN))) :=
    .betaPi whole isSort body numTyped
  have numPi : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing .nil (.pi (.const numN) (.const numN))
        (universeAt (.max (.const LevelOrder.bot) (.const LevelOrder.bot)))) :=
    .piForm numTyped isSort numInContext isSort (LevelNames.Join.tower (.sorts _ _))
  have variable_ : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.typing (.snoc .nil (.const numN)) (.var 0) (.const numN)) := .var 0
  have atOne : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.equality .nil
        (.app (.app (.app (.const identity) (levelName (.const LevelOrder.bot)))
          (.const numN)) (.app (.const sucN) (.const zeroN)))
        (.app (.lam (.const numN) (.var 0)) (.app (.const sucN) (.const zeroN)))
        (.const numN)) :=
    .appCong (.trans applied unfolded) (.refl oneTyped)
  have computed : CDerivable
      (objectNames Δ (identityFamily c univ el identity :: decoders c univ el))
      (.equality .nil
        (.app (.lam (.const numN) (.var 0)) (.app (.const sucN) (.const zeroN)))
        (.app (.const sucN) (.const zeroN)) (.const numN)) :=
    .betaPi numPi isSort variable_ oneTyped
  exact .trans atOne computed

/-- **The identity law at the numbers.** The proof of the identity law for every level below
the bound (`LevelNames.polyId_law`), applied to the name of the least level, to the type of the
numbers and to the numeral one, proves that the polymorphic identity sends the numeral one to
itself. The numbers are a member of the universe the name names, and the numeral one an
element of what they decode to, because the two decoders compute at the name. -/
theorem polyId_law_num_one {c : L} (positive : LevelOrder.bot < c) {univ el : DeclName}
    (distinct : el ≠ univ) (apart : Apart (decoders c univ el)) {Δ : LevelBounds L}
    (positiveBounds : Δ.Positive) :
    CDerivable (objectNames Δ (decoders c univ el))
      (.typing .nil
        (.app (.app (.app
          (.lam (levelsBelow (.const c)) (.lam (.app (.const univ) (.var 0))
            (.lam (.app (.app (.const el) (.var 1)) (.var 0)) (.refl (.var 0)))))
          (levelName (.const LevelOrder.bot))) (.const numN))
          (.app (.const sucN) (.const zeroN)))
        (.id (.app (.app (.const el) (levelName (.const LevelOrder.bot))) (.const numN))
          (.app (.app (.app (polyId c univ el) (levelName (.const LevelOrder.bot)))
            (.const numN)) (.app (.const sucN) (.const zeroN)))
          (.app (.const sucN) (.const zeroN)))) := by
  have admitted := decoders_admitted (c := c) (univ := univ) (el := el) positive distinct
  have below : LevelBounds.LeUnder Δ (.succ (.const LevelOrder.bot)) (.const c) :=
    fun _ _ => LevelOrder.succ_le_of_lt positive
  have law := objectNames_of_names (Δ := Δ) (polyId_law (Δ := Δ) admitted)
  have name : CDerivable (objectNames Δ (decoders c univ el))
      (.typing .nil (levelName (.const LevelOrder.bot)) (levelsBelow (.const c))) :=
    objectNames_of_names (LevelNames.lift_bare (LevelNames.levelName_typed below))
  have numTyped : CDerivable (objectNames Δ (decoders c univ el))
      (.typing .nil (.const numN) (universeAt (.const LevelOrder.bot))) :=
    objectNames_of_object apart (cnum_typed (Γ := .nil))
  have oneTyped : CDerivable (objectNames Δ (decoders c univ el))
      (.typing .nil (.app (.const sucN) (.const zeroN)) (.const numN)) :=
    objectNames_of_object apart (csuc_typed (Γ := .nil) czero_typed)
  have isSort {e : LevelExpr L} :
      (Rules.sum (LevelNames.rules Δ (decoders c univ el))
        (Rules.mapSchemas (towerHead L) (baseRules Δ) objectRules
          objectSchemas)).isUniverse (.tower (.sort e)) :=
    LevelNames.IsUniverse.tower (.sort e)
  have univEq : CDerivable (objectNames Δ (decoders c univ el))
      (.equality .nil (.app (.const univ) (levelName (.const LevelOrder.bot)))
        (universeAt (.const LevelOrder.bot)) (LevelNames.CU c)) :=
    objectNames_of_names (univ_at admitted positiveBounds below)
  have numMember : CDerivable (objectNames Δ (decoders c univ el))
      (.typing .nil (.const numN) (.app (.const univ) (levelName (.const LevelOrder.bot)))) :=
    .conv numTyped (.symm univEq) isSort
  have stepped : CDerivable (objectNames Δ (decoders c univ el))
      (.equality .nil (.app (.const el) (levelName (.const LevelOrder.bot)))
        (.lam (universeAt (.const LevelOrder.bot)) (.var 0))
        (.pi (.app (.const univ) (levelName (.const LevelOrder.bot))) (LevelNames.CU c))) :=
    objectNames_of_names (el_step admitted positiveBounds below)
  have applied : CDerivable (objectNames Δ (decoders c univ el))
      (.equality .nil
        (.app (.app (.const el) (levelName (.const LevelOrder.bot))) (.const numN))
        (.app (.lam (universeAt (.const LevelOrder.bot)) (.var 0)) (.const numN))
        (LevelNames.CU c)) :=
    .appCong (A := .app (.const univ) (levelName (.const LevelOrder.bot)))
      (B := LevelNames.CU c) stepped (.refl numMember)
  have source : CDerivable (objectNames Δ (decoders c univ el))
      (.typing .nil
        (.pi (universeAt (.const LevelOrder.bot)) (universeAt (.const LevelOrder.bot)))
        (universeAt (.max (.succ (.const LevelOrder.bot)) (.succ (.const LevelOrder.bot))))) :=
    .piForm (.headType (LevelNames.HeadTyping.tower (.sort _))) isSort
      (.headType (LevelNames.HeadTyping.tower (.sort _))) isSort
      (LevelNames.Join.tower (.sorts _ _))
  have reduced : CDerivable (objectNames Δ (decoders c univ el))
      (.equality .nil (.app (.lam (universeAt (.const LevelOrder.bot)) (.var 0)) (.const numN))
        (.const numN) (universeAt (.const LevelOrder.bot))) :=
    .betaPi (A := universeAt (.const LevelOrder.bot)) (B := universeAt (.const LevelOrder.bot))
      (body := .var 0) (a := .const numN) source isSort (.var 0) numTyped
  have elEq : CDerivable (objectNames Δ (decoders c univ el))
      (.equality .nil
        (.app (.app (.const el) (levelName (.const LevelOrder.bot))) (.const numN))
        (.const numN) (LevelNames.CU c)) :=
    .trans applied (.subEq reduced (.subUniv fun _ _ => le_of_lt positive))
  have oneMember : CDerivable (objectNames Δ (decoders c univ el))
      (.typing .nil (.app (.const sucN) (.const zeroN))
        (.app (.app (.const el) (levelName (.const LevelOrder.bot))) (.const numN))) :=
    .conv oneTyped (.symm elEq) isSort
  exact .appElim (.appElim (.appElim law name) numMember) oneMember

omit [LevelOrder L] in
/-- The names of the decoders and of the identity in the two examples are not names of the
object package. -/
theorem exampleNames_apart (c : L) :
    Apart (identityFamily c (.str .anonymous "univ") (.str .anonymous "el")
        (.str .anonymous "identity") ::
      decoders c (.str .anonymous "univ") (.str .anonymous "el")) := by
  intro F mem
  simp only [decoders, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact (by decide : objectDeclared (.str .anonymous "identity") = false)
  · exact (by decide : objectDeclared (.str .anonymous "el") = false)
  · exact (by decide : objectDeclared (.str .anonymous "univ") = false)

/-- Over the natural numbers, with the names of the levels below `3`. -/
theorem identity_num_one_nat {Δ : LevelBounds Nat} (positive : Δ.Positive) :
    CDerivable
      (objectNames Δ
        (identityFamily 3 (.str .anonymous "univ") (.str .anonymous "el")
            (.str .anonymous "identity") ::
          decoders 3 (.str .anonymous "univ") (.str .anonymous "el")))
      (.equality .nil
        (.app (.app (.app (.const (.str .anonymous "identity")) (levelName (.const 0)))
          (.const numN)) (.app (.const sucN) (.const zeroN)))
        (.app (.const sucN) (.const zeroN)) (.const numN)) :=
  identity_num_one (c := 3) (by decide) (by decide) (by decide) (by decide)
    (exampleNames_apart 3) positive

/-- **Over the ordinal notations, with the names of all finite levels**: the polymorphic
identity over the levels below `ω`, at the name of the level `0`, applied to the type of the
numbers and to the numeral one, is the numeral one. -/
theorem identity_num_one_omega {Δ : LevelBounds Level} (positive : Δ.Positive) :
    CDerivable
      (objectNames Δ
        (identityFamily Level.omega (.str .anonymous "univ") (.str .anonymous "el")
            (.str .anonymous "identity") ::
          decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.equality .nil
        (.app (.app (.app (.const (.str .anonymous "identity"))
          (levelName (.const Level.zero))) (.const numN))
          (.app (.const sucN) (.const zeroN)))
        (.app (.const sucN) (.const zeroN)) (.const numN)) :=
  identity_num_one Level.isLimit_omega.1 (by decide) (by decide) (by decide)
    (exampleNames_apart Level.omega) positive

/-- **The identity law at the numbers, over the ordinal notations**: the one proof for all
finite levels, applied to the name of the level `0`, the numbers and the numeral one. -/
theorem polyId_law_num_one_omega {Δ : LevelBounds Level} (positive : Δ.Positive) :
    CDerivable
      (objectNames Δ (decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.typing .nil
        (.app (.app (.app
          (.lam (levelsBelow (.const Level.omega))
            (.lam (.app (.const (.str .anonymous "univ")) (.var 0))
              (.lam (.app (.app (.const (.str .anonymous "el")) (.var 1)) (.var 0))
                (.refl (.var 0)))))
          (levelName (.const Level.zero))) (.const numN))
          (.app (.const sucN) (.const zeroN)))
        (.id (.app (.app (.const (.str .anonymous "el")) (levelName (.const Level.zero)))
            (.const numN))
          (.app (.app (.app
            (polyId Level.omega (.str .anonymous "univ") (.str .anonymous "el"))
            (levelName (.const Level.zero))) (.const numN))
            (.app (.const sucN) (.const zeroN)))
          (.app (.const sucN) (.const zeroN)))) :=
  polyId_law_num_one Level.isLimit_omega.1 (by decide)
    (fun F mem => exampleNames_apart Level.omega F (List.mem_cons_of_mem _ mem)) positive

/-- In the model over the ordinal notations the judgment holds: the value of the application
is the numeral one. -/
theorem identity_num_one_omega_holds (h : CofinalInaccessibles.{u}) :
    Holds (objectNamesHeads Level h)
      (objectNamesConsts Level h
        (identityFamily Level.omega (.str .anonymous "univ") (.str .anonymous "el")
            (.str .anonymous "identity") ::
          decoders Level.omega (.str .anonymous "univ") (.str .anonymous "el")))
      (.equality .nil
        (.app (.app (.app (.const (.str .anonymous "identity"))
          (levelName (.const Level.zero))) (.const numN))
          (.app (.const sucN) (.const zeroN)))
        (.app (.const sucN) (.const zeroN)) (.const numN)) :=
  objectNames_sound h
    (identity_admitted Level.isLimit_omega.1 (by decide) (by decide) (by decide))
    (exampleNames_apart Level.omega) (Δ := LevelBounds.unbounded Level)
    LevelBounds.positive_unbounded (identity_num_one_omega LevelBounds.positive_unbounded)

end Client

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
