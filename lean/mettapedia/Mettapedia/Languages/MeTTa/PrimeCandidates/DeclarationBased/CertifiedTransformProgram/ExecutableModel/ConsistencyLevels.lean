import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelPackage
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Eliminators

/-!
# Identity elimination, the recursor and the iterator at every level in the consistency model

In the consistency model of the executable package (`model`):

* **identity elimination**, a cast on the model's value side, is a valid term of
  `elimType u w` for every carrier universe `u` and every motive universe `w`
  (`valid_j_at`), and without hypotheses at every pair of universes of the tower
  (`valid_j_sorts`);
* **the recursor on the numbers** is valid with its motive into every universe
  (`valid_numRec_at`), without hypotheses at every universe of the tower
  (`valid_numRec_sorts`);
* **the iterator** is valid with its carrier and family in any universes
  (`valid_iter_at`, `valid_iter_sorts`);
* so **the object package at every level** (`objectRulesAt`) is sound for the
  model (`objectSoundAt`), and it is consistent (`objectRulesAt_consistent`).

In route T's consistency model `tmodelC`, identity elimination transports its
method along its motive. It is valid at every level pair when the transport is
coherent in the consistency model at the motive's level
(`tmodelC_valid_j_of_coherent`): between types with one interpretation, the
transport of a valid value is related to it. That coherence is not a
consequence of the transport table. The consistency model has no daimon clause,
and a transport whose rows reach the daimon is no number: `coe U0 num 0` is
stuck on the daimon, and no denotation of the numbers relates it to itself
(`tmodelC_coe_universe_num_not_number`); on model SN's value side every type
relates it to the daimon.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative.Consistency
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic transportJ_step)
open CertifiedTransforms (stepOver subst_stepOver)
open SetProfile (zeroNative sucNative)
open Package (jName numRecName iterName numT U0 numRecApp iterApp)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## The tower without constants -/

/-- The tower is sound for the consistency model: its universe rules are the
model's, and it has no constants and no computations. -/
theorem tower_sound : Sound Tower.rules (model v) where
  laws := model_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => step.elim
  constants := fun declared => nomatch declared

/-! ## Identity elimination -/

/-- On the model's value side, identity elimination returns its method on every
path. -/
theorem model_j_castStep {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tower.Tm m) :
    (model v).rules.computation.step (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, a₅]) a₃ :=
  model_step (modelListed 3 (by decide)) ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩

/-- **Identity elimination is valid at every carrier universe `u` and every
motive universe `w`** in the consistency model, when its type is valid with
valid parts. -/
theorem valid_j_at {u w : Tower.Head} (hw : (model v).rules.isUniverse w)
    (validType : ValidTy (model v) .nil (elimType u w))
    (partsType : Structured (model v) .nil (elimType u w)) :
    ValidTm (model v) .nil (.const jName) (elimType u w) :=
  ValidTm.castEliminator (model_laws v) hw (model_j_castStep v) validType partsType

/-- **Identity elimination is valid at every pair of universes of the tower** in
the consistency model. -/
theorem valid_j_sorts (lu lw : LevelExpr Nat) :
    ValidTm (model v) .nil (.const jName) (elimType (.sort lu) (.sort lw)) := by
  obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed lu lw
  obtain ⟨validT, partsT, _⟩ := Derivable.valid (tower_sound v) typed trivial
  exact valid_j_at v (LevelTower.IsUniverse.sort lw) (validT.validTy hw) partsT

/-! ## The recursor at every level -/

/-- The step's type at a number `a`: `P a → P (suc a)`. -/
private theorem inst0_stepType {n : Nat} (P a : Tower.Tm n) :
    Presentation.inst0 a (.pi (.app (Presentation.rename wk P) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1)))) =
      .pi (.app P a) (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) := by
  show Tm.pi (.app (Presentation.inst0 a (Presentation.rename wk P)) a)
      (.app (Presentation.subst (liftSub (subst0 a))
          (Presentation.rename wk (Presentation.rename wk P)))
        (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, subst_liftSub_wk]
  show Tm.pi (.app P a) (.app (Presentation.rename wk
      (Presentation.inst0 a (Presentation.rename wk P))) (sucNative (Presentation.rename wk a))) = _
  rw [inst0_rename_wk]

/-- The motive at the successor of a number, over one more variable,
instantiated at a value. -/
private theorem inst0_sucApp {n : Nat} (P a h : Tower.Tm n) :
    Presentation.inst0 h (.app (Presentation.rename wk P) (sucNative (Presentation.rename wk a))) =
      .app P (sucNative a) := by
  show Tm.app (Presentation.inst0 h (Presentation.rename wk P))
      (sucNative (Presentation.inst0 h (Presentation.rename wk a))) = _
  rw [inst0_rename_wk, inst0_rename_wk]

/-- A motive related to another at `num → w` sends numbers with one numeral to
types with one denotation. -/
theorem numRec_motive_at {w : Tower.Head} (hw : (model v).rules.isUniverse w) {m : Nat}
    {ξ : World (model v).reading m} {RP : Rel Tower.Head m}
    (den : Den (model v) ξ (.pi numT (.head w)) RP) {P P' : Tower.Tm m} (related : RP P P')
    {a b : Tower.Tm m} {k : Nat} (left : NumVal (model v).toSetting a k)
    (right : NumVal (model v).toSetting b k) :
    ∃ R, Den (model v) ξ (.app P a) R ∧ Den (model v) ξ (.app P' b) R := by
  obtain ⟨RU, denU, types⟩ := Den.pi_app_exists (model_laws v) den related fun denA => by
    rw [Den.num_inv (model_laws v) denA]
    exact ⟨k, left, right⟩
  have denU' : Den (model v) ξ (.head w) RU := denU
  rw [Den.sort_inv (model_laws v) hw denU'] at types
  obtain ⟨R, first, second⟩ := universeAt.den types
  exact ⟨R, ⟨_, first⟩, ⟨_, second⟩⟩

/-- A step related to another at `Π n : num. P n → P (suc n)` sends numbers
with one numeral and values related at the motive to values related at the
motive at the successor. -/
theorem numRec_step_related {m : Nat} {ξ : World (model v).reading m} {P s s' : Tower.Tm m}
    {RS : Rel Tower.Head m}
    (den : Den (model v) ξ (.pi numT (.pi (.app (Presentation.rename wk P) (.var 0))
      (.app (Presentation.rename wk (Presentation.rename wk P)) (sucNative (.var 1))))) RS)
    (related : RS s s') {a b h h' : Tower.Tm m} {k : Nat}
    (left : NumVal (model v).toSetting a k) (right : NumVal (model v).toSetting b k)
    (values : ∀ {R : Rel Tower.Head m}, Den (model v) ξ (.app P a) R → R h h')
    {R : Rel Tower.Head m} (denSuc : Den (model v) ξ (.app P (sucNative a)) R) :
    R (.app (.app s a) h) (.app (.app s' b) h') := by
  obtain ⟨R₁, den₁, related₁⟩ := Den.pi_app_exists (model_laws v) den related fun denA => by
    rw [Den.num_inv (model_laws v) denA]
    exact ⟨k, left, right⟩
  rw [inst0_stepType] at den₁
  obtain ⟨R₂, den₂, related₂⟩ := Den.pi_app_exists (model_laws v) den₁ related₁ values
  rw [inst0_sucApp] at den₂
  rw [Den.deterministic (model_laws v) denSuc den₂]
  exact related₂

/-- **The recursor on the numbers is valid with its motive into every universe**
in the consistency model, when its type is valid with valid parts. -/
theorem valid_numRec_at (w : Tower.Head) (hw : (model v).rules.isUniverse w)
    (validType : ValidTy (model v) .nil (numRecTypeAt w))
    (partsType : Structured (model v) .nil (numRecTypeAt w)) :
    ValidTm (model v) .nil (.const numRecName) (numRecTypeAt w) := by
  obtain ⟨_, validResult, _⟩ := ValidTy.close_parts (.snoc (numRecTelescopeAt w) numT)
    (C := .app (.var 3) (.var 0)) validType partsType
  refine ValidTm.close (model_laws v) (.snoc (numRecTelescopeAt w) numT)
    (C := .app (.var 3) (.var 0)) (f := .const numRecName) validType partsType
    ⟨validResult, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨⟨⟨⟨-, RP, denP, relP⟩, RZ, denZ, relZ⟩, RS, denS, relS⟩, RT, denT, relT⟩ := e
  change Den (model v) ξ (.pi numT (.head w)) RP at denP
  change RP (σ 3) (σ' 3) at relP
  change Den (model v) ξ (.app (σ 3) zeroNative) RZ at denZ
  change RZ (σ 2) (σ' 2) at relZ
  change Den (model v) ξ (.pi numT (.pi (.app (Presentation.rename wk (σ 3)) (.var 0))
    (.app (Presentation.rename wk (Presentation.rename wk (σ 3))) (sucNative (.var 1))))) RS
    at denS
  change RS (σ 1) (σ' 1) at relS
  change Den (model v) ξ (.const (model v).num) RT at denT
  change RT (σ 0) (σ' 0) at relT
  change Den (model v) ξ (.app (σ 3) (σ 0)) R at den
  show R (numRecApp (σ 3) (σ 2) (σ 1) (σ 0)) (numRecApp (σ' 3) (σ' 2) (σ' 1) (σ' 0))
  rw [Den.num_inv (model_laws v) denT] at relT
  obtain ⟨k, number, number'⟩ := relT
  exact numRec_related v
    (numRec_motive_at v hw denP (Den.refl_left (model_laws v) denP relP))
    (fun denZ' => by
      rw [Den.deterministic (model_laws v) denZ' denZ]
      exact relZ)
    (numRec_step_related v denS relS) k number number' den

/-- **Large elimination of the numbers in the consistency model**: the recursor
with its motive into every universe of the tower is valid. -/
theorem valid_numRec_sorts (lw : LevelExpr Nat) :
    ValidTm (model v) .nil (.const numRecName) (numRecTypeAt (.sort lw)) := by
  have sound₀ := stage_sound_of v (names := [numN, zeroN, sucN]) fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact valid_num v
    · exact valid_zero v
    · exact valid_suc v
  obtain ⟨validT, partsT, _⟩ := Derivable.valid sound₀ (numRecTypeAt_typed lw) trivial
  exact valid_numRec_at v (.sort lw) (LevelTower.IsUniverse.sort lw)
    (validT.validTy (LevelTower.IsUniverse.sort _)) partsT

/-! ## The iterator at large families -/

/-- A family applied to the newest variable, instantiated at a point. -/
private theorem inst0_family {n : Nat} (x P : Tower.Tm n) :
    Presentation.inst0 x (.app (Presentation.rename wk P) (.var 0)) = .app P x := by
  show Tm.app (Presentation.inst0 x (Presentation.rename wk P)) x = _
  rw [inst0_rename_wk]

/-- **The iterator is valid with its carrier in any universe `k` and its family
into any universe `l`** in the consistency model, when its type is valid with
valid parts. -/
theorem valid_iter_at (k l : Tower.Head)
    (validType : ValidTy (model v) .nil (iterTypeAt k l))
    (partsType : Structured (model v) .nil (iterTypeAt k l)) :
    ValidTm (model v) .nil (.const iterName) (iterTypeAt k l) := by
  have laws := model_laws v
  obtain ⟨_, validC, _⟩ := ValidTy.close_parts (iterSucTelescopeAt k l) (C := iterResult)
    validType partsType
  refine ValidTm.close laws (iterSucTelescopeAt k l) (C := iterResult) (f := .const iterName)
    validType partsType ⟨validC, ?_⟩
  intro m ξ σ σ' e R den
  obtain ⟨⟨⟨⟨⟨⟨_, RN, denN, hN⟩, _, _, _⟩, _, _, _⟩, RS, denS, hS⟩, RX, denX, hX⟩, RE, denE, hE⟩ :=
    e
  obtain rfl := Den.num_inv laws denN
  obtain ⟨j, hj, hj'⟩ := hN
  change Den (model v) ξ (Presentation.subst (tailSub (tailSub (tailSub σ)))
    (stepOver (.var 1) (.app (.var 1) (.var 0)))) RS at denS
  rw [subst_stepOver] at denS
  change Den (model v) ξ (stepOver (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) RS
    at denS
  change RS (σ 2) (σ' 2) at hS
  change Den (model v) ξ (σ 4) RX at denX
  change RX (σ 1) (σ' 1) at hX
  change Den (model v) ξ (.app (σ 3) (σ 1)) RE at denE
  change Den (model v) ξ (.sigma (σ 4) (.app (Presentation.rename wk (σ 3)) (.var 0))) R at den
  change NumVal (model v).toSetting (σ 5) j at hj
  change NumVal (model v).toSetting (σ' 5) j at hj'
  show R (iterApp (σ 5) (σ 4) (σ 3) (σ 2) (σ 1) (σ 0))
    (iterApp (σ' 5) (σ' 4) (σ' 3) (σ' 2) (σ' 1) (σ' 0))
  exact iter_related v den denS hS j hj hj'
    (fun denA => by rw [Den.deterministic laws denA denX]; exact hX)
    (fun denA => by rw [Den.deterministic laws denA denE]; exact hE)

/-- **The iterator is valid at large families of the tower** in the consistency
model: its carrier in `U lk` and its family into `U ll`. -/
theorem valid_iter_sorts (lk ll : LevelExpr Nat) :
    ValidTm (model v) .nil (.const iterName) (iterTypeAt (.sort lk) (.sort ll)) := by
  have sound₀ := stage_sound_of v (names := [numN]) fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    obtain rfl := Option.some.inj declared
    exact valid_num v
  obtain ⟨validT, partsT, _⟩ := Derivable.valid sound₀ (iterTypeAt_typed lk ll) trivial
  exact valid_iter_at v (.sort lk) (.sort ll) (validT.validTy (LevelTower.IsUniverse.sort _)) partsT

/-! ## The object package at every level -/

/-- **The object package at every level is sound for the consistency model**:
identity elimination at `elimType (U lu) (U lw)` is valid by the cast, the
recursor with its motive into `U lr` by large elimination, and every other
constant and every root step as in the object package. -/
theorem objectSoundAt (lu lw lr : LevelExpr Nat) : Sound (objectRulesAt lu lw lr) (model v) where
  laws := model_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := (objectSound v).root
  constants := by
    intro name type declared
    by_cases hj : name = jName
    · subst hj
      rw [objectRulesAt_j] at declared
      cases declared
      exact valid_j_sorts v lu lw
    by_cases hr : name = numRecName
    · subst hr
      rw [objectRulesAt_numRec] at declared
      cases declared
      exact valid_numRec_sorts v lr
    rw [objectRulesAt_other lu lw lr hj hr] at declared
    exact (objectSound v).constants declared

/-- **Consistency of the object package at every level**: no closed term proves
`∀ n : num, zero = suc n`. -/
theorem objectRulesAt_consistent (lu lw lr : LevelExpr Nat) (t : Tower.Tm 0) :
    ¬ Typed (objectRulesAt lu lw lr) .nil t (programCodes.holdsOf (falseCode (n := 0))) :=
  no_closed_proof (objectSoundAt (fun _ => 0) lu lw lr) (falseCode_truth fun _ => 0)
    (fun all => Nat.zero_ne_one (numClass_injective (model_laws fun _ => 0).truth.numerals
      ((all (numClass _ 0)).trans (sucClass_numClass 0)))) t

/-! ## Route T's consistency model: identity elimination by transport -/

/-- The tower is sound for route T's consistency model. -/
theorem tower_sound_tmodelC : Sound Tower.rules (tmodelC v) where
  laws := tmodelC_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => step.elim
  constants := fun declared => nomatch declared

/-- In route T's consistency model, identity elimination transports its method
along its motive. -/
theorem tmodelC_j_step {m : Nat} (a₀ a₁ a₂ a₃ a₄ a₅ : Tower.Tm m) :
    (tmodelC v).rules.computation.step (appSpine (.const jName) [a₀, a₁, a₂, a₃, a₄, a₅])
      (appSpine (.const coeN) [.app (.app a₂ a₁) (.refl a₁), .app (.app a₂ a₄) a₅, a₃]) :=
  tmodel_step v (tmodelListed v 3 (by decide)) (transportJ_step a₀ a₁ a₂ a₃ a₄ a₅)

/-- **In route T's consistency model, identity elimination by transport is valid
at every carrier universe and every motive universe `U lw` of the tower, when
the transport is coherent at the level of `U lw`.** The coherence is the open
premise: it is not a consequence of the transport table in this model
(`tmodelC_coe_universe_num_not_number`). -/
theorem tmodelC_valid_j_of_coherent (lu lw : LevelExpr Nat)
    (coherent : TransportCoherent (tmodelC v) coeN ((tmodelC v).levels.level (.sort lw))) :
    ValidTm (tmodelC v) .nil (.const jName) (elimType (.sort lu) (.sort lw)) := by
  obtain ⟨w, hw, typed⟩ := TowerEliminatorModel.elimType_typed lu lw
  obtain ⟨validT, partsT, _⟩ := Derivable.valid (tower_sound_tmodelC v) typed trivial
  exact ValidTm.transportEliminator_of_coherent (tmodelC_laws v) (LevelTower.IsUniverse.sort lw)
    (tmodelC_j_step v) coherent (validT.validTy hw) partsT

/-- The transport from the lowest universe into the numbers is stuck on the
daimon in route T's value model: its target is a type constant its source is
not, so the row of the numbers gives the daimon. -/
theorem tmodelC_coe_universe_num {n : Nat} (d : Tower.Tm n) :
    ∃ w, WhRed (tmodelC v).rules (tmodelC v).roles
      (appSpine (.const coeN) [U0, numT, d]) w ∧ Daimonic (tmodelC v).roles starN w :=
  ⟨_, .head ((tmodel_coeTable v).step_coe .num)
      (.single ((tmodel_coeTable v).step_num (.star ⟨_, .head _⟩ fun e => by cases e))),
    .star⟩

/-- **The transport's daimon rows give no value in the consistency model.** In
route T's consistency model, `coe U0 num 0` is stuck on the daimon, and no
denotation of the numbers relates it to itself: a term stuck on the daimon
reduces to no numeral. On model SN's value side every type relates it to the
daimon, which is what coherence there reads; the consistency model has no such
clause, so its coherence must come from the forms of types with one
interpretation. -/
theorem tmodelC_coe_universe_num_not_number {n : Nat} (ξ : World (tmodelC v).reading n)
    {R : Rel Tower.Head n} (den : Den (tmodelC v) ξ numT R) :
    ¬ R (appSpine (.const coeN) [U0, numT, .const zeroN])
      (appSpine (.const coeN) [U0, numT, .const zeroN]) := by
  have laws := tmodelC_laws v
  rw [Den.num_inv laws den]
  rintro ⟨k, hk, -⟩
  obtain ⟨w, red, daimonic⟩ := tmodelC_coe_universe_num v (n := n) (.const zeroN)
  have normal : Whnf (tmodelC v).rules (tmodelC v).roles w :=
    (daimonic.neutral tmodelRoles_star).whnf (tmodelShape v)
  cases hk with
  | zero red' =>
      have e := WhRed.whnf_unique (tmodelShape v) red red' normal
        (constSpine_whnf (tmodelShape v) (args := []) fun _ _ role => by
          change tmodelRoles zeroN = _ at role
          rw [tmodelRoles_zero] at role
          cases role)
      subst e
      rcases daimonic.constSpine (c := zeroN) (args := []) rfl with e | ⟨_, _, role⟩
      · exact absurd e (by decide)
      · change tmodelRoles zeroN = _ at role
        rw [tmodelRoles_zero] at role
        cases role
  | suc red' _ =>
      have e := WhRed.whnf_unique (tmodelShape v) red red' normal
        (constSpine_whnf (tmodelShape v) (args := [_]) fun _ _ role => by
          change tmodelRoles sucN = _ at role
          rw [tmodelRoles_suc] at role
          cases role)
      subst e
      rcases daimonic.constSpine (c := sucN) (args := [_]) rfl with e | ⟨_, _, role⟩
      · exact absurd e (by decide)
      · change tmodelRoles sucN = _ at role
        rw [tmodelRoles_suc] at role
        cases role

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
