import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueLevelControls

/-!
# The object package at every level is sound for the transport value model

The object package at every level (`objectRulesAt lu lw lr`) declares identity
elimination at `elimType (U lu) (U lw)` and the recursor with its motive into
`U lr`, and computes as the object package does. On the skeleton-free value side
of the transport value model (`vmodel`):

* every declared constant is a valid term of its declared type: identity
  elimination by transport at every pair of universes of the tower
  (`TExtension.valid_j_sorts`), the recursor by large elimination
  (`valid_numRecS_sorts`), and every other constant as in the object package;
* every root step is validated: identity elimination's linear rule at its typed
  instances, at the package's own declared type (`TExtension.jRoot_typed_at`), every
  other step semantically.

So the package is sound for the model (`vmodel_soundS_at`), and every term typed
in a formed context of it is strongly normalizing under its own reduction, and so
is its type (`objectRulesAt_sn`, `objectRulesAt_equal_sn`); in particular the
language's own declaration, at the level parameters (`polyRules_sn`). The
consistency model gives its consistency (`objectRulesAt_consistent`).

## Controls

* **The transport client.** In the package at carrier level one, identity
  elimination with the motive `λ Z _. Z` transports a term of `X` along a path
  `p : Id U0 X Y` into `Y`: typed (`transportJ_typed_at`) and strongly
  normalizing (`transportJ_sn_at`), and at reflexivity it computes to its method
  (`largeReflJ_equal_at`, `largeReflJ_sn_at`).
* **Large elimination of the numbers.** In the package with the recursor's
  motive at level one, the large motive `λ y _. num-rec (λ_. U0) num (λ_ _. num → num) y`
  is typed (`largeMotiveAt_typed_at`), and identity elimination over it from `0`
  to `1` is typed and strongly normalizing (`largeMotiveJ_typed_at`,
  `largeMotiveJ_sn_at`).
* **One instance serves the levels below it.** The package at carrier level one
  types identity elimination at the carrier `num`, a type of the lowest universe,
  as well as at `U0` (`numJ_typed_at`).
* **Without the level.** The object package, whose identity elimination has its
  carrier in the lowest universe, does not type the transport client at the
  numbers (`numTransportJ_untypable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Package (U0 numT jName numRecName)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## Soundness -/

/-- **Every root step of the package at every level is validated by the model**:
identity elimination's linear rule at its typed instances, at
`elimType (U lu) (U lw)`, and every other step semantically. -/
theorem vmodel_root_at (lu lw lr : LevelExpr Nat) {n : Nat} {l r : Tower.Tm n}
    (step : (objectRulesAt lu lw lr).computation.step l r) :
    ModelSN.RootSemanticS (vmodel v) l r ∨ ModelSN.TypedRootS (objectRulesAt lu lw lr) (vmodel v) l r := by
  rcases step with step | step
  · exact objectTExt.stage_root v (allowed := fun _ => true)
      (fun _ => ⟨.sort lu, .sort lw, LevelTower.IsUniverse.sort lw, objectRulesAt_j lu lw lr⟩) step
  · exact .inl (ModelSN.ModelRootS.semantic (vmodel_laws v) (vprogramDecodes v) (.inr step))

/-- **Every declared constant of the package at every level is valid**: identity
elimination by transport, the recursor by large elimination, and every other
constant as in the object package. -/
theorem vmodel_valid_at (lu lw lr : LevelExpr Nat) {name : DeclName} {type : Tower.Tm 0}
    (declared : (objectRulesAt lu lw lr).constantType name = some type) :
    ModelSN.ValidTmS (vmodel v) .nil (.const name) type := by
  by_cases hj : name = jName
  · subst hj
    rw [objectRulesAt_j] at declared
    cases declared
    exact objectTExt.valid_j_sorts v lu lw
  by_cases hr : name = numRecName
  · subst hr
    rw [objectRulesAt_numRec] at declared
    cases declared
    exact objectTExt.valid_numRecS_sorts v lr
  rw [objectRulesAt_other lu lw lr hj hr] at declared
  exact (vmodel_soundS_objectRules v).constants declared

/-- **The object package at every level is sound for the transport value
model.** -/
theorem vmodel_soundS_at (lu lw lr : LevelExpr Nat) :
    ModelSN.TypedSoundS (objectRulesAt lu lw lr) (vmodel v) where
  laws := vmodel_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := vmodel_root_at v lu lw lr
  constants := vmodel_valid_at v lu lw lr

end CodeModel

/-! ## Strong normalization -/

open CodeModel in
/-- **Strong normalization of the object package at every level.** Every term
typed in a formed context of the package is strongly normalizing under the
package's own reduction, and so is its type. -/
theorem objectRulesAt_sn (lu lw lr : LevelExpr Nat) {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed (objectRulesAt lu lw lr) Γ) (typed : Typed (objectRulesAt lu lw lr) Γ t A) :
    SN (objectRulesAt lu lw lr) t ∧ SN (objectRulesAt lu lw lr) A :=
  ModelSN.Typed.sn (vmodel_soundS_at (fun _ => 0) lu lw lr) formed typed

open CodeModel in
/-- Both sides of a derivable equality of the object package at every level, in
a formed context, are strongly normalizing, and so is their type. -/
theorem objectRulesAt_equal_sn (lu lw lr : LevelExpr Nat) {n : Nat} {Γ : Tower.Ctx n}
    {a b A : Tower.Tm n} (formed : CtxFormed (objectRulesAt lu lw lr) Γ)
    (equal : Derivable (objectRulesAt lu lw lr) (.equality Γ a b A)) :
    SN (objectRulesAt lu lw lr) a ∧ SN (objectRulesAt lu lw lr) b ∧ SN (objectRulesAt lu lw lr) A :=
  ModelSN.Equal.sn (vmodel_soundS_at (fun _ => 0) lu lw lr) formed equal

open CodeModel in
/-- **Strong normalization of the language's declaration**: the package at the
level parameters, with identity elimination at `identityEliminateType`. -/
theorem polyRules_sn {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed polyRules Γ) (typed : Typed polyRules Γ t A) :
    SN polyRules t ∧ SN polyRules A :=
  objectRulesAt_sn (.param 0) (.param 1) (.param 2) formed typed

namespace CodeModel

/-! ## Controls -/

/-- A formed context persists into a larger package. -/
private theorem ctxFormed_mono {R' R : Rules Tower.Head} (sub : RulesSub R' R) :
    ∀ {n : Nat} {Γ : Tower.Ctx n}, CtxFormed R' Γ → CtxFormed R Γ
  | _, _, .nil => .nil
  | _, _, .snoc formed ⟨u, hu, typed⟩ =>
      .snoc (ctxFormed_mono sub formed) ⟨u, sub.isUniverse hu, Derivable.mono sub typed⟩

/-- A control package whose declarations are the package's is contained in
it. -/
theorem controlRules_sub_objectRulesAt {types : DeclName → Option (Tower.Tm 0)}
    {names : List DeclName} {lu lw lr : LevelExpr Nat}
    (sameTypes : ∀ {name : DeclName} {type : Tower.Tm 0}, types name = some type →
      (objectRulesAt lu lw lr).constantType name = some type) :
    RulesSub (controlRules types names) (objectRulesAt lu lw lr) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := sameTypes
  computation := fun step => .inl ((stage_sub_rules _).computation step)

/-- The declaration of identity elimination at carrier `U1` and motive `U0` is
the package's at carrier level one. -/
theorem carrierTypes_at (lr : LevelExpr Nat) {name : DeclName} {type : Tower.Tm 0}
    (declared : carrierTypes name = some type) :
    (objectRulesAt (.succ Tower.zero) Tower.zero lr).constantType name = some type := by
  unfold carrierTypes at declared
  split_ifs at declared with h
  subst h
  cases declared
  exact objectRulesAt_j _ _ _

/-- The declarations of the first control are the package's with the recursor's
motive at level one. -/
theorem largeTypes_at {name : DeclName} {type : Tower.Tm 0} (declared : largeTypes name = some type) :
    (objectRulesAt Tower.zero Tower.zero (.succ Tower.zero)).constantType name = some type := by
  unfold largeTypes at declared
  split_ifs at declared with h₁ h₂ h₃
  · subst h₁
    cases declared
    exact objectRulesAt_numRec _ _ _
  · subst h₂
    cases declared
    rw [jType_eq]
    exact objectRulesAt_j _ _ _
  · have mem : name ∈ [numN, zeroN, sucN] := by simpa [allowedIn] using h₃
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;>
      rw [objectRulesAt_other _ _ _ (by decide) (by decide)] <;> exact declared

/-! ### The transport client -/

section Transport

variable (lr : LevelExpr Nat)

/-- **The transport client is typed in the package at carrier level one**:
`J U0 X (λ Z _. Z) d Y p : Y` in the context `X Y : U0, p : Id U0 X Y, d : X`. -/
theorem transportJ_typed_at :
    Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) transportContext transportJ (.var 2) :=
  Derivable.mono (controlRules_sub_objectRulesAt (carrierTypes_at lr)) transportJ_typed

theorem transportContext_formed_at :
    CtxFormed (objectRulesAt (.succ Tower.zero) Tower.zero lr) transportContext :=
  ctxFormed_mono (controlRules_sub_objectRulesAt (carrierTypes_at lr)) transportContext_formed

/-- **The transport client is strongly normalizing** in the package, and so is its
type. -/
theorem transportJ_sn_at :
    SN (objectRulesAt (.succ Tower.zero) Tower.zero lr) transportJ ∧
      SN (objectRulesAt (.succ Tower.zero) Tower.zero lr) (.var 2 : Tower.Tm 4) :=
  objectRulesAt_sn _ _ lr (transportContext_formed_at lr) (transportJ_typed_at lr)

/-- **At reflexivity the transport client computes to its method** in the
package: `J U0 X (λ Z _. Z) d X (refl X) ≡ d : X`. -/
theorem largeReflJ_equal_at :
    Equal (objectRulesAt (.succ Tower.zero) Tower.zero lr) largeReflContext largeReflJ (.var 0)
      (.var 1) :=
  Derivable.mono (controlRules_sub_objectRulesAt (carrierTypes_at lr)) largeReflJ_equal

/-- Both sides of the computation at reflexivity are strongly normalizing in the
package, and so is their type. -/
theorem largeReflJ_sn_at :
    SN (objectRulesAt (.succ Tower.zero) Tower.zero lr) largeReflJ ∧
      SN (objectRulesAt (.succ Tower.zero) Tower.zero lr) (.var 0 : Tower.Tm 2) ∧
      SN (objectRulesAt (.succ Tower.zero) Tower.zero lr) (.var 1 : Tower.Tm 2) :=
  objectRulesAt_equal_sn _ _ lr
    (ctxFormed_mono (controlRules_sub_objectRulesAt (carrierTypes_at lr)) largeReflContext_formed)
    (largeReflJ_equal_at lr)

end Transport

/-! ### Large elimination of the numbers -/

/-- **The large motive is typed** in the package with the recursor's motive at
level one. -/
theorem largeMotiveAt_typed_at :
    Typed (objectRulesAt Tower.zero Tower.zero (.succ Tower.zero)) .nil largeMotiveAt
      (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0)) :=
  Derivable.mono (controlRules_sub_objectRulesAt largeTypes_at) largeMotiveAt_typed

/-- **Identity elimination over the large motive is typed**: along a path
`p : Id num 0 1`, `J num 0 P 0 1 p : P 1 p`. -/
theorem largeMotiveJ_typed_at :
    Typed (objectRulesAt Tower.zero Tower.zero (.succ Tower.zero)) pathContext
      (largeMotiveJ (.var 0)) (.app (.app largeMotiveAt oneT) (.var 0)) :=
  Derivable.mono (controlRules_sub_objectRulesAt largeTypes_at) largeMotiveJ_typed

/-- **Identity elimination over the large motive is strongly normalizing** in the
package, and so is its type. -/
theorem largeMotiveJ_sn_at :
    SN (objectRulesAt Tower.zero Tower.zero (.succ Tower.zero)) (largeMotiveJ (.var 0) : Tower.Tm 1) ∧
      SN (objectRulesAt Tower.zero Tower.zero (.succ Tower.zero))
        (.app (.app largeMotiveAt oneT) (.var 0) : Tower.Tm 1) :=
  objectRulesAt_sn _ _ _
    (ctxFormed_mono (controlRules_sub_objectRulesAt largeTypes_at) pathContext_formed)
    largeMotiveJ_typed_at

/-! ### One instance serves the levels below it -/

section Lower

variable (lu lw lr : LevelExpr Nat) {n : Nat} {Γ : Tower.Ctx n}

/-- A dependent function type between types of one universe is a type of it. -/
private theorem piAt {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {level : LevelExpr Nat}
    (hA : Typed (objectRulesAt lu lw lr) Γ A (sortTm level))
    (hB : Typed (objectRulesAt lu lw lr) (.snoc Γ A) B (sortTm level)) :
    Typed (objectRulesAt lu lw lr) Γ (.pi A B) (sortTm level) :=
  .cumul (.piForm hA (.sort level) hB (.sort level) (.sorts level level))
    fun valuation => (max_self (LevelExpr.eval valuation level)).le

/-- **One instance serves the levels below it**: the package at carrier level one
types identity elimination at the carrier `num`, a type of the lowest universe,
as it types the transport client at the carrier `U0`:
`J num 0 (λ_ _. num) 0 0 (refl 0) : (λ_ _. num) 0 (refl 0)`. -/
theorem numJ_typed_at :
    Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) .nil reflJ
      (.app (.app constMotive (.const zeroN)) (.refl (.const zeroN))) := by
  have sub := ctorStage_sub_objectRulesAt (.succ Tower.zero) Tower.zero lr
  have numMem : numN ∈ [numN, zeroN, sucN] := by simp
  have zeroMem : zeroN ∈ [numN, zeroN, sucN] := by simp
  have tNum : ∀ {m : Nat} {Δ : Tower.Ctx m},
      Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) Δ numT U0 :=
    fun {_ _} => Derivable.mono sub (numT_typed numMem)
  have tZero : ∀ {m : Nat} {Δ : Tower.Ctx m},
      Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) Δ (.const zeroN) numT :=
    fun {_ _} => Derivable.mono sub (zero_typed numMem zeroMem)
  have tU0 : ∀ {m : Nat} {Δ : Tower.Ctx m},
      Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) Δ U0 (sortTm (.succ Tower.zero)) :=
    fun {_ _} => .headType (.sort _)
  have up : ∀ {m : Nat} {Δ : Tower.Ctx m} {T : Tower.Tm m},
      Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) Δ T U0 →
        Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) Δ T (sortTm (.succ Tower.zero)) :=
    fun typed => .cumul typed fun _ => Nat.zero_le _
  obtain ⟨w, hw, typedJ⟩ := objectRulesAt_j_typed (.succ Tower.zero) Tower.zero lr
  have hJ : Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) .nil (.const jName)
      (liftClosed (elimType (.sort (.succ Tower.zero)) (.sort Tower.zero))) :=
    .const (objectRulesAt_j _ _ _) typedJ hw
  -- the motive `λ_ _. num : Π y : num. Id num 0 y → U0`
  have tInner : Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) (.snoc .nil numT)
      (.pi (.id numT (.const zeroN) (.var 0)) U0) (sortTm (.succ Tower.zero)) :=
    piAt _ _ _ (up (.idForm tNum (.sort _) tZero (.var 0))) tU0
  have tOuter : Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) .nil
      (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0)) (sortTm (.succ Tower.zero)) :=
    piAt _ _ _ (up tNum) tInner
  have tMotive : Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) .nil constMotive
      (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0)) :=
    .lamIntro tOuter (.sort _) (.lamIntro tInner (.sort _) tNum)
  -- the method: `(λ_ _. num) 0 (refl 0) ≡ num`
  have tRefl : Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) .nil (.refl (.const zeroN))
      (.id numT (.const zeroN) (.const zeroN)) :=
    .reflIntro tZero
  have eMotive : Equal (objectRulesAt (.succ Tower.zero) Tower.zero lr) .nil
      (.app (.app constMotive (.const zeroN)) (.refl (.const zeroN))) numT U0 :=
    .trans (.appCong (.betaPi tOuter (.sort _) (.lamIntro tInner (.sort _) tNum) tZero)
        (.refl tRefl))
      (.betaPi (piAt _ _ _ (up (.idForm tNum (.sort _) tZero tZero)) tU0) (.sort _) tNum tRefl)
  have tD : Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) .nil (.const zeroN)
      (.app (.app constMotive (.const zeroN)) (.refl (.const zeroN))) :=
    .conv tZero (.symm eMotive) (.sort _)
  exact Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (Derivable.appElim (Derivable.appElim hJ (up tNum)) tZero) tMotive) tD) tZero) tRefl

end Lower

/-! ### Without the level -/

/-- The transport client at the numbers: `J U0 num (λ Z _. Z) 0 num (refl num)`. -/
abbrev numTransportJ : Tower.Tm 0 :=
  appSpine (.const jName) [U0, numT, idMotive, .const zeroN, numT, .refl numT]

/-- **Without its level, identity elimination does not transport between types**:
the object package, whose identity elimination has its carrier in the lowest
universe, does not type the transport client at the numbers. The typing facts of
its spine would make `U0` a value of the lowest universe, or the numbers a
hereditarily total type. -/
theorem numTransportJ_untypable : ¬ Typed objectRules .nil numTransportJ numT := by
  intro typed
  have laws := vmodel_valueLaws (fun _ => 0)
  let empty : Sub Tower.Head 0 0 := fun i => Fin.elim0 i
  rcases ModelSN.Typed.spineFacts (vmodel_soundS_objectRules fun _ => 0) typed trivial rfl
      objectRules_declared_j (ξ := Consistency.World.closed) (σ := empty) (σ' := empty)
      (ς := empty) trivial with ok | total
  · -- the first argument, `U0`, would be a value of the lowest universe
    obtain ⟨A, B, red, ⟨P, den, val, -⟩, -⟩ := ok
    rw [TelescopeAbstraction.liftClosed_zero, Package.jType_eq] at red
    cases ValueSide.whRed_of_whnf (pi_whnf laws.shape _ _) red
    rw [ModelSN.DenS.sort_inv (vmodel_laws fun _ => 0) (LevelTower.IsUniverse.sort _) den] at val
    obtain ⟨Q, interp, -, -⟩ := ModelSN.universeAt.den val
    exact lt_irrefl _ (ValueSide.InterpAt.univ_inv laws interp .refl (LevelTower.IsUniverse.sort _)).1
  · -- the numbers would relate `0` to `1`
    have related := total.total_rel (ValueSide.DenS.facts laws) (ValueSide.DenS.num laws _)
      (.const zeroN) (.app (.const sucN) (.const zeroN))
    obtain ⟨s, hz, hs⟩ := ValueSide.numIndPack_rel.mp related
    have zero := Realizability.HasShape.deterministic laws.values.truth laws.star hz (.zero .refl)
    have suc := Realizability.HasShape.deterministic laws.values.truth laws.star hs
      (.suc .refl (.zero .refl))
    rw [zero] at suc
    cases suc

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
