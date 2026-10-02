import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.CandidateSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Square

/-!
# Rigid proposition codes over the tower: lifting, soundness and consistency

The proposition codes of System F over the cumulative tower, without the decoding of codes
(`rigidCodes`): the type of codes `prop : U₀`, the decoder `holds : prop → U₀`, implication
`imp : prop → prop → prop` and the quantifier `allProp : (prop → prop) → prop` are declared
constants with no root step. The package is rigid (`rigidCodes_rigid`): its declared types have
no abstraction. It is not pure (`rigidCodes_not_pure`), so the theorem for pure packages does
not apply to it.

* **Lifting** (`codesLiftingFacts`, `codes_lifts`): the theorem for rigid packages
  (`LiftingFacts.ofRigid`), with the tower's universe laws and head reading, and strong
  normalization inherited from System F's package of codes, of which the rigid codes are a
  sub-package (`rigidCodes_sub_systemF`, `rigidCodes_sn`).
* **The set model** (`codesModel`): the declared constants are interpreted by values in the
  values of their declared types. `prop` is the set of truth values `Ω = 𝒫 {∅}`, `holds` the
  identity on it, `imp` and `allProp` implication and quantification of truth values.
* **Soundness** (`Derivable.sound_codes`, from the theorem for rigid packages
  `Derivable.sound_rigid`): every derivation of the rigid codes over a formed context is the
  erasure of an annotated derivation that holds in the tower model, relative to
  `CofinalInaccessibles`, which enters as a parameter.
* **Relative consistency** (`codes_consistent`, `codes_not_all_true`): no closed term has type
  `Π (X : U₀). X`, and none has type `Π (p : prop). holds p`: not every code holds.

Controls: the rigid codes derive the typings of their constants (`prop_typed`, `holds_typed`,
`imp_typed`, `allProp_typed`), and the decoding of a code is the code (`ev_holds_code`); a
package declaring a constant at a type with an abstraction is not rigid
(`lamDeclared_not_rigid`), although it has no root step either.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization (CtxFormed RulesSub)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open Square (omega truthCode_mem_omega)

universe u

/-! ## The package -/

/-- **The rigid proposition codes over the tower**: System F's code constants, declared, with
no root step. -/
def rigidCodes : Rules Tower.Head := { Tower.rules with constantType := SystemF.codes.codeType }

theorem holds_ne_prop : SystemF.codes.holds ≠ SystemF.codes.prop := by decide

theorem imp_ne : SystemF.codes.imp ≠ SystemF.codes.prop ∧ SystemF.codes.imp ≠ SystemF.codes.holds :=
  by decide

theorem allProp_ne : SystemF.allProp ≠ SystemF.codes.prop ∧ SystemF.allProp ≠ SystemF.codes.holds ∧
    SystemF.allProp ≠ SystemF.codes.imp := by decide

/-- **The declared types of the codes**: `prop : U₀`, `holds : prop → U₀`,
`imp : prop → prop → prop`, `allProp : (prop → prop) → prop`. -/
theorem codeType_cases {c : DeclName} {T : Tower.Tm 0}
    (declared : SystemF.codes.codeType c = some T) :
    (c = SystemF.codes.prop ∧ T = .head (.sort Tower.zero)) ∨
      (c = SystemF.codes.holds ∧ T = SystemF.codes.holdsType) ∨
      (c = SystemF.codes.imp ∧ T = SystemF.codes.impType) ∨
      (c = SystemF.allProp ∧ T = SystemF.codes.allType (.const SystemF.codes.prop)) := by
  unfold Codes.codeType at declared
  split at declared
  · rename_i hc
    cases declared
    exact .inl ⟨hc, rfl⟩
  · split at declared
    · rename_i _ hc
      cases declared
      exact .inr (.inl ⟨hc, rfl⟩)
    · split at declared
      · rename_i _ _ hc
        cases declared
        exact .inr (.inr (.inl ⟨hc, rfl⟩))
      · split at declared
        · rename_i A carrier
          cases declared
          change [(SystemF.allProp, (.const SystemF.codes.prop : Tower.Tm 0))].lookup c = some A
            at carrier
          by_cases hc : c = SystemF.allProp
          · subst hc
            have e : A = .const SystemF.codes.prop := by
              simp only [List.lookup, beq_self_eq_true] at carrier
              exact (Option.some.inj carrier).symm
            exact .inr (.inr (.inr ⟨rfl, by rw [e]⟩))
          · simp only [List.lookup] at carrier
            split at carrier
            · rename_i same
              exact absurd (beq_iff_eq.mp same) hc
            · cases carrier
        · change (none : Option (Tower.Tm 0)).map _ = some T at declared
          cases declared

/-- **The rigid codes are a rigid package**: no root step, and declared types without
abstractions. -/
theorem rigidCodes_rigid : rigidCodes.Rigid where
  noSteps := fun h => h
  lamFree := fun declared => by
    rcases codeType_cases declared with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- **The rigid codes are not pure**: they declare the type of codes. -/
theorem rigidCodes_not_pure : ¬ rigidCodes.Pure := fun pure => by
  have undeclared := pure.noConstants SystemF.codes.prop
  change SystemF.codes.codeType SystemF.codes.prop = none at undeclared
  rw [Codes.codeType_prop] at undeclared
  cases undeclared

/-! ## Strong normalization and the lifting -/

/-- **The rigid codes are a sub-package of System F's package of codes**, which also decodes
them. -/
theorem rigidCodes_sub_systemF : RulesSub rigidCodes SystemF.rules where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => SystemF.codes.extend_constantType_of_code Tower.rules declared
  computation := fun h => h.elim

/-- **Strong normalization of the rigid codes**: every term typed in a formed context is
strongly normalizing. -/
theorem rigidCodes_sn {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed rigidCodes Γ) (typed : Typed rigidCodes Γ t A) :
    StrongNormalization.SN rigidCodes t :=
  StrongNormalization.SN.of_rootSub (R := rigidCodes) (R' := SystemF.rules) (fun h => h.elim)
    (SystemF.rules_sn (formed.mono rigidCodes_sub_systemF)
      (Normalization.Derivable.mono rigidCodes_sub_systemF typed)).1

/-- The tower's universe laws, for the rigid codes. -/
abbrev codesLevels : Normalization.LevelModel rigidCodes ℕ := { towerLevels with }

theorem codesAlgebra : Normalization.CumulativeAlgebra rigidCodes :=
  { Normalization.TowerModel.algebra with }

/-- The tower's reading of heads, for the rigid codes. -/
def codesHeadReading : HeadReading rigidCodes := { towerHeadReading with }

theorem codes_groundHeadEq : GroundHeadEq rigidCodes := tower_groundHeadEq

/-- **The annotation of the rigid codes**: each declared type annotated as it is written, since
it has no abstraction; no root step. -/
def codesChurch : ChurchRules rigidCodes where
  constantType := fun c => (SystemF.codes.codeType c).map liftTm
  computation := .empty
  erase_constantType := fun c => by
    change ((SystemF.codes.codeType c).map liftTm).map CTm.erase = SystemF.codes.codeType c
    cases SystemF.codes.codeType c <;> simp [erase_liftTm]
  erase_step := fun h => h.elim

/-- **The facts the lifting needs, for the rigid codes**, from the theorem for rigid
packages. -/
theorem codesLiftingFacts : LiftingFacts codesChurch :=
  LiftingFacts.ofRigid codesLevels codesAlgebra codesHeadReading codes_groundHeadEq
    tower_universe rigidCodes_sn rigidCodes_rigid

/-- **The Church–Curry correspondence for the rigid codes**: every derivation lifts to the
annotation, over every formed annotated context erasing to its context. -/
theorem codes_lifts {statement : Statement Tower.Head}
    (derivation : Derivable rigidCodes statement) : Lifts codesChurch statement :=
  lifts codesLevels codesLiftingFacts derivation

/-! ## The set model -/

/-- The value of the decoder: the identity on truth values. -/
noncomputable def holdsValue : ZFSet.{u} := traceLam (graph omega (fun x => x))

/-- The value of implication of truth values. -/
noncomputable def impValue : ZFSet.{u} :=
  traceLam (graph omega fun p =>
    traceLam (graph omega fun q => truthCode ((∅ : ZFSet.{u}) ∈ p → (∅ : ZFSet.{u}) ∈ q)))

/-- The value of quantification over truth values. -/
noncomputable def allValue : ZFSet.{u} :=
  traceLam (graph (tracePiSet omega fun _ => omega) fun f =>
    truthCode (∀ x ∈ omega.{u}, (∅ : ZFSet.{u}) ∈ traceApp f x))

/-- **The values of the code constants.** -/
noncomputable def codeValue (c : DeclName) : ZFSet.{u} :=
  if c = SystemF.codes.prop then omega
  else if c = SystemF.codes.holds then holdsValue
  else if c = SystemF.codes.imp then impValue
  else if c = SystemF.allProp then allValue
  else ∅

theorem codeValue_prop : codeValue.{u} SystemF.codes.prop = omega := if_pos rfl

theorem codeValue_holds : codeValue.{u} SystemF.codes.holds = holdsValue := by
  rw [codeValue, if_neg holds_ne_prop, if_pos rfl]

theorem codeValue_imp : codeValue.{u} SystemF.codes.imp = impValue := by
  rw [codeValue, if_neg imp_ne.1, if_neg imp_ne.2, if_pos rfl]

theorem codeValue_allProp : codeValue.{u} SystemF.allProp = allValue := by
  rw [codeValue, if_neg allProp_ne.1, if_neg allProp_ne.2.1, if_neg allProp_ne.2.2, if_pos rfl]

/-- The truth values lie in every level of the tower. -/
theorem omega_mem_universeSet (h : CofinalInaccessibles.{u}) (k : Nat) :
    omega.{u} ∈ universeSet h ∅ k :=
  (universeSet_closed h ∅ k).power_mem ((universeSet_closed h ∅ k).singleton_mem
    ((universeSet_closed h ∅ k).empty_mem (seed_mem_universeSet h ∅ k)))

/-- **The tower model of the rigid codes**, relative to `CofinalInaccessibles.{u}`: the tower's
universes, and the code constants at their values. -/
theorem codesModel (h : CofinalInaccessibles.{u}) :
    SetModel (interpretHead h ∅ ∅ (fun _ => 0)) codeValue.{u} codesChurch where
  universes := { (standardTowerModel h).universes with }
  headEq := (standardTowerModel h).headEq
  constants := by
    intro c T declared
    change (SystemF.codes.codeType c).map liftTm = some T at declared
    cases hc : SystemF.codes.codeType c with
    | none =>
        rw [hc] at declared
        cases declared
    | some T₀ =>
        rw [hc] at declared
        cases declared
        have mem := omega_mem_universeSet h (Tower.zero.eval fun _ => 0)
        rcases codeType_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [codeValue_prop]
          exact mem
        · rw [codeValue_holds]
          change holdsValue ∈ tracePiSet (codeValue SystemF.codes.prop)
            (fun _ => universeSet h ∅ (Tower.zero.eval fun _ => 0))
          rw [codeValue_prop]
          exact traceLam_graph_mem fun x hx =>
            (universeSet_closed h ∅ _).transitive _ mem hx
        · rw [codeValue_imp]
          change impValue ∈ tracePiSet (codeValue SystemF.codes.prop)
            (fun _ => tracePiSet (codeValue SystemF.codes.prop)
              (fun _ => codeValue SystemF.codes.prop))
          rw [codeValue_prop]
          exact traceLam_graph_mem fun _ _ =>
            traceLam_graph_mem fun _ _ => truthCode_mem_omega _
        · rw [codeValue_allProp]
          change allValue ∈ tracePiSet (tracePiSet (codeValue SystemF.codes.prop)
            (fun _ => codeValue SystemF.codes.prop)) (fun _ => codeValue SystemF.codes.prop)
          rw [codeValue_prop]
          exact traceLam_graph_mem fun _ _ => truthCode_mem_omega _
  steps := fun step => step.elim

/-- **Soundness of every derivation of the rigid codes in the set tower.** Under
`CofinalInaccessibles.{u}`, every derivation of `rigidCodes` over a formed context is the
erasure of an annotated derivation whose statement holds in the tower model, with the code
constants at their values. -/
theorem Derivable.sound_codes (h : CofinalInaccessibles.{u}) {statement : Statement Tower.Head}
    (derivation : Derivable rigidCodes statement) (formed : statement.CtxFormed rigidCodes) :
    ∃ s : CStatement Tower.Head, CDerivable codesChurch s ∧ s.erase = statement ∧
      Holds (interpretHead h ∅ ∅ (fun _ => 0)) codeValue.{u} s :=
  Derivable.sound_rigid rigidCodes_rigid codesLevels codesAlgebra codesHeadReading
    codes_groundHeadEq tower_universe rigidCodes_sn (codesModel h) derivation formed

/-! ## Relative consistency -/

/-- **Relative consistency of the rigid codes.** Under `CofinalInaccessibles.{u}`, no closed
term of the rigid codes has type `Π (X : U₀). X`. -/
theorem codes_consistent (h : CofinalInaccessibles.{u}) (t : Tower.Tm 0) :
    ¬ Derivable rigidCodes (.typing .nil t emptyType.erase) :=
  Derivable.no_closed_inhabitant codesLevels codesLiftingFacts (codesModel h) rfl
    (ev_emptyType h ∅ ∅ _ _) t

/-- `Π (p : prop). holds p`: every code holds. -/
def allTrue : Tower.Tm 0 := .pi SystemF.codes.propT (SystemF.codes.holdsOf (.var 0))

/-- The decoding of a code is the code: the value of `holds c` at a truth value is it. -/
theorem ev_holds_code {n : Nat} (h : CofinalInaccessibles.{u}) (c : CTm Tower.Head n)
    (ρ : Env.{u} n) (hc : ev (interpretHead h ∅ ∅ (fun _ => 0)) codeValue c ρ ∈ omega.{u}) :
    ev (interpretHead h ∅ ∅ (fun _ => 0)) codeValue (.app (.const SystemF.codes.holds) c) ρ =
      ev (interpretHead h ∅ ∅ (fun _ => 0)) codeValue c ρ := by
  change traceApp (codeValue SystemF.codes.holds) _ = _
  rw [codeValue_holds, holdsValue, traceApp_graph_beta _ hc]

/-- `Π (p : prop). holds p` is empty in the tower model: the false truth value has no proof. -/
theorem ev_allTrue_empty (h : CofinalInaccessibles.{u}) (z : ZFSet.{u}) :
    z ∉ ev (interpretHead h ∅ ∅ (fun _ => 0)) codeValue (liftTm allTrue) Fin.elim0 := by
  intro member
  change z ∈ tracePiSet (codeValue SystemF.codes.prop)
    (fun x => traceApp (codeValue SystemF.codes.holds) x) at member
  rw [codeValue_prop] at member
  have empty : (∅ : ZFSet.{u}) ∈ omega.{u} := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  have value := traceApp_mem_fibre member empty
  rw [codeValue_holds, holdsValue, traceApp_graph_beta _ empty] at value
  exact ZFSet.notMem_empty _ value

/-- **Not every code holds.** Under `CofinalInaccessibles.{u}`, no closed term of the rigid
codes has type `Π (p : prop). holds p`. -/
theorem codes_not_all_true (h : CofinalInaccessibles.{u}) (t : Tower.Tm 0) :
    ¬ Derivable rigidCodes (.typing .nil t allTrue) :=
  Derivable.no_closed_inhabitant codesLevels codesLiftingFacts (codesModel h) rfl
    (ev_allTrue_empty h) t

/-! ## Controls -/

/-- **Positive control: the rigid codes derive the type of codes**, a rigid constant of
`U₀`. -/
theorem prop_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rigidCodes Γ SystemF.codes.propT Impredicative.U0 :=
  Derivable.const (type := .head SystemF.codes.proofs) (Codes.codeType_prop SystemF.codes)
    (.headType (LevelTower.HeadTyping.sort Tower.zero)) (LevelTower.IsUniverse.sort _)

/-- The decoder's typing. -/
theorem holds_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rigidCodes Γ (.const SystemF.codes.holds) (.pi SystemF.codes.propT Impredicative.U0) :=
  Derivable.const (type := SystemF.codes.holdsType) (SystemF.codes.codeType_holds holds_ne_prop)
    (.piForm prop_typed (LevelTower.IsUniverse.sort _) (.headType (LevelTower.HeadTyping.sort Tower.zero))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _))
    (LevelTower.IsUniverse.sort _)

/-- Implication's typing. -/
theorem imp_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rigidCodes Γ (.const SystemF.codes.imp)
      (.pi SystemF.codes.propT (.pi SystemF.codes.propT SystemF.codes.propT)) :=
  Derivable.const (type := SystemF.codes.impType) (SystemF.codes.codeType_imp imp_ne)
    (.piForm prop_typed (LevelTower.IsUniverse.sort _)
      (.piForm prop_typed (LevelTower.IsUniverse.sort _) prop_typed (LevelTower.IsUniverse.sort _)
        (LevelTower.Join.sorts _ _))
      (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _))
    (LevelTower.IsUniverse.sort _)

/-- The quantifier's typing. -/
theorem allProp_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed rigidCodes Γ (.const SystemF.allProp)
      (.pi (.pi SystemF.codes.propT SystemF.codes.propT) SystemF.codes.propT) :=
  Derivable.const (type := SystemF.codes.allType (.const SystemF.codes.prop))
    (SystemF.codes.codeType_all allProp_ne rfl)
    (.piForm (.piForm prop_typed (LevelTower.IsUniverse.sort _) prop_typed (LevelTower.IsUniverse.sort _)
        (LevelTower.Join.sorts _ _))
      (LevelTower.IsUniverse.sort _) prop_typed (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _))
    (LevelTower.IsUniverse.sort _)

/-- The type `Π (p : prop). holds p` is formed: the consistency statement is not vacuous. -/
theorem allTrue_formed :
    Typed rigidCodes .nil allTrue (.head (.sort (.max Tower.zero Tower.zero))) :=
  .piForm prop_typed (LevelTower.IsUniverse.sort _) (.appElim holds_typed (.var 0))
    (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)

/-- A name for a constant declared at a type with an abstraction. -/
def lamName : DeclName := `lamDeclared

/-- `(λ X. X) U₀`: a type, β-equal to `U₀`, written with an abstraction. -/
def lamType : Tower.Tm 0 := .app (.lam (.var 0)) Impredicative.U0

/-- **Negative control: a package whose declared type has an abstraction.** It declares
`lamDeclared : (λ X. X) U₀` and has no root step. -/
def lamDeclared : Rules Tower.Head :=
  { Tower.rules with constantType := fun c => if c = lamName then some lamType else none }

/-- **The hypothesis rejects it**: a declared type with an abstraction is not rigid. -/
theorem lamDeclared_not_rigid : ¬ lamDeclared.Rigid := fun rigid => by
  have declared : lamDeclared.constantType lamName = some lamType := by
    show (if lamName = lamName then some lamType else none) = _
    exact if_pos rfl
  have h := rigid.lamFree declared
  cases h

/-- It has no root step: the rejection is the abstraction's alone. -/
theorem lamDeclared_noSteps {n : Nat} {l r : Tower.Tm n} : ¬ lamDeclared.computation.step l r :=
  fun h => h

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
