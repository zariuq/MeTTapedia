import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueLevels
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound

/-!
# Controls for identity elimination and large elimination at every level

Controls on the transport value model on the skeleton-free value side
(`vmodel`), each a typed term of a small package whose declarations are valid
(`controlRules_typedSoundS`), hence valid by the fundamental lemma:

1. **Large elimination under identity elimination.** The motive
   `λ y _. num-rec (λ_. U0) num (λ_ _. num → num) y` computes the numbers at `0`
   and `num → num` at successors; it needs the recursor with its motive into
   `U1`. It is valid (`largeMotive_valid`), and identity elimination over it,
   from `0` to `1` along a path variable, is valid at `P 1 p`
   (`largeMotiveJ_valid`), and strongly normalizing in the object package
   (`largeMotiveJ_sn`). A cast, returning the method `0`, would give no value
   there: `0` is no value of `num → num` (`vnumArrow_not_rel_zero`).
2. **Identity elimination at a large carrier.** With `X Y : U0`, a path
   `p : Id U0 X Y` and `d : X`, identity elimination with the motive
   `λ Z _. Z` is the transport of `d` from `X` to `Y`: it computes to it on the
   value side (`transportJ_red`), it is a valid term of `Y` (`transportJ_valid`),
   and at reflexivity between the numbers it computes to its method
   (`transportJ_refl_red`).
3. **Identity elimination at a large carrier, with its computation.** The family
   `λ Z _. Z` lives over the carrier `U0`, of level one, where identity
   elimination is valid by transport (`vmodel_valid_j_sorts`). The package
   of control 2 with identity elimination's linear rule is sound
   (`carrierJRules_typedSoundS`), by the typed step of identity elimination at
   carrier level one, and the computation `J U0 X (λ Z _. Z) d X (refl X) ≡ d : X`
   is derivable (`largeReflJ_equal`), validly equal in the model
   (`largeReflJ_valid`), and strongly normalizing on both sides
   (`largeReflJ_sn`).
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
open TelescopeAbstraction (subst_empty liftClosed_zero)
open SetProfile (zeroNative sucNative)
open Package (U0 numT jName numRecName)

namespace CodeModel

variable (v : Nat → Nat)

/-! ## Control packages -/

/-- The tower with the given declarations and the computations of the listed
names. -/
def controlRules (types : DeclName → Option (Tower.Tm 0)) (names : List DeclName) :
    Rules Tower.Head :=
  { Tower.rules with
    constantType := types
    computation := (stage (allowedIn names)).computation }

section Toolkit

variable {types : DeclName → Option (Tower.Tm 0)} {names : List DeclName} {n : Nat}
  {Γ : Tower.Ctx n}

theorem sortC (level : LevelExpr Nat) :
    Typed (controlRules types names) Γ (sortTm level) (sortTm (.succ level)) :=
  .headType (.sort level)

theorem raiseC {T : Tower.Tm n} {a b : LevelExpr Nat}
    (typed : Typed (controlRules types names) Γ T (sortTm a))
    (le : ∀ ν, LevelExpr.eval ν a ≤ LevelExpr.eval ν b) :
    Typed (controlRules types names) Γ T (sortTm b) :=
  .cumul typed le

theorem piC {A : Tower.Tm n} {B : Tower.Tm (n + 1)} {level : LevelExpr Nat}
    (hA : Typed (controlRules types names) Γ A (sortTm level))
    (hB : Typed (controlRules types names) (.snoc Γ A) B (sortTm level)) :
    Typed (controlRules types names) Γ (.pi A B) (sortTm level) :=
  .cumul (.piForm hA (.sort level) hB (.sort level) (.sorts level level))
    fun ν => (max_self (LevelExpr.eval ν level)).le

/-- A stage whose declarations the control package declares alike, and whose
names it lists, is contained in it. -/
theorem stage_sub_control {allowed : DeclName → Bool}
    (sameTypes : ∀ name, allowed name = true → types name = allTypes name)
    (sameNames : ∀ name, allowed name = true → allowedIn names name = true) :
    RulesSub (stage allowed) (controlRules types names) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    change (if allowed name then allTypes name else none) = some type at declared
    change types name = some type
    by_cases h : allowed name = true
    · rw [if_pos h] at declared
      rw [sameTypes name h]
      exact declared
    · rw [if_neg h] at declared
      cases declared
  computation := (stage_sub sameNames).computation

/-- The tower is contained in every control package. -/
theorem tower_sub_control : RulesSub Tower.rules (controlRules types names) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => nomatch declared
  computation := fun step => step.elim

end Toolkit

/-- **A control package whose declared constants are valid is sound for the model**,
when it declares identity elimination at `elimType u w`, with `w` a universe,
wherever it lists its computation: its root steps are steps of a stage of the
executable package, and identity elimination's holds at its typed instances. -/
theorem controlRules_typedSoundS {types : DeclName → Option (Tower.Tm 0)} {names : List DeclName}
    (declaredJ : jName ∈ names → ∃ u w, (vmodel v).rules.isUniverse w ∧
      types jName = some (elimType u w))
    (constants : ∀ {name : DeclName} {type : Tower.Tm 0}, types name = some type →
      ModelSN.ValidTmS (vmodel v) .nil (.const name) type) :
    ModelSN.TypedSoundS (controlRules types names) (vmodel v) where
  laws := vmodel_laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := vstage_root v (allowed := allowedIn names)
    fun allowedJ => declaredJ (by simpa [allowedIn] using allowedJ)
  constants := constants

/-! ## Control 1: large elimination under identity elimination -/

/-- The declarations of the first control: the numbers and their
constructors, the recursor with its motive into `U1`, and identity elimination
at the lowest universes. -/
def largeTypes (name : DeclName) : Option (Tower.Tm 0) :=
  if name = numRecName then some (numRecTypeAt (.sort (.succ Tower.zero)))
  else if name = jName then some Package.jType
  else if allowedIn [numN, zeroN, sucN] name then allTypes name
  else none

/-- The first control package: its computations are the recursor's. -/
abbrev largeRules : Rules Tower.Head := controlRules largeTypes [numN, zeroN, sucN, numRecName]

/-- The stage of the numbers and their constructors is contained in the first
control package. -/
theorem ctorStage_sub_large : RulesSub ctorStage largeRules :=
  stage_sub_control
    (fun name h => by
      have mem : name ∈ [numN, zeroN, sucN] := by simpa [allowedIn] using h
      have h₁ : name ≠ numRecName := by
        rintro rfl
        revert mem
        decide
      have h₂ : name ≠ jName := by
        rintro rfl
        revert mem
        decide
      simp only [largeTypes, if_neg h₁, if_neg h₂, if_pos h])
    (fun name h => by
      have mem : name ∈ [numN, zeroN, sucN] := by simpa [allowedIn] using h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> decide)

/-- **The first control package is sound for the model**: the recursor with its
motive into `U1` is valid by large elimination, identity elimination by
transport, and the numbers and their constructors as declared. -/
theorem largeRules_soundS : ModelSN.TypedSoundS largeRules (vmodel v) :=
  controlRules_typedSoundS v (fun h => absurd h (by decide)) fun {name type} declared => by
    change largeTypes name = some type at declared
    unfold largeTypes at declared
    split_ifs at declared with h₁ h₂ h₃
    · subst h₁
      cases declared
      exact valid_numRecS_sorts v (.succ Tower.zero)
    · subst h₂
      cases declared
      exact vmodel_valid_j v
    · have mem : name ∈ [numN, zeroN, sucN] := by simpa [allowedIn] using h₃
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
      · exact vmodel_valid_num v
      · exact vmodel_valid_zero v
      · exact vmodel_valid_suc v

section LargeTypings

variable {n : Nat} {Γ : Tower.Ctx n}

/-- `num-rec (λ_. U0) num (λ_ _. num → num) t`: the numbers at zero,
`num → num` at every successor. -/
abbrev bigRec (t : Tower.Tm n) : Tower.Tm n :=
  appSpine (.const numRecName) [.lam U0, numT, arrowStep, t]

/-- The large motive `λ y _. num-rec (λ_. U0) num (λ_ _. num → num) y` in every
scope. -/
abbrev largeMotiveAt : Tower.Tm n := .lam (.lam (bigRec (.var 1)))

theorem largeMotiveAt_zero : (largeMotiveAt : Tower.Tm 0) = largeMotive := rfl

theorem num_typedL : Typed largeRules Γ numT U0 :=
  Derivable.mono ctorStage_sub_large (numT_typed (by simp))

theorem zero_typedL : Typed largeRules Γ (.const zeroN) numT :=
  Derivable.mono ctorStage_sub_large (zero_typed (by simp) (by simp))

theorem suc_typedL : Typed largeRules Γ (.const sucN) (.pi numT numT) :=
  Derivable.mono ctorStage_sub_large (suc_typed (by simp) (by simp))

theorem one_typedL : Typed largeRules Γ oneT numT := .appElim suc_typedL zero_typedL

/-- The recursor at its large type. -/
theorem numRec_typedL :
    Typed largeRules Γ (.const numRecName) (liftClosed (numRecTypeAt (.sort (.succ Tower.zero)))) :=
  .const (by show largeTypes numRecName = _; unfold largeTypes; rw [if_pos rfl])
    (Derivable.mono ctorStage_sub_large (numRecTypeAt_typed (.succ Tower.zero))) (.sort _)

/-- `λ_. U0 : num → U1`. -/
theorem constU0_typed : Typed largeRules Γ (.lam U0) (.pi numT (sortTm (.succ Tower.zero))) :=
  .lamIntro (piC (raiseC num_typedL fun _ => Nat.zero_le _) (sortC _)) (.sort _) (sortC _)

/-- `(λ_. U0) a ≡ U0`. -/
theorem constU0_beta {a : Tower.Tm n} (ha : Typed largeRules Γ a numT) :
    Equal largeRules Γ (.app (.lam U0) a) U0 (sortTm (.succ Tower.zero)) :=
  .betaPi (piC (raiseC num_typedL fun _ => Nat.zero_le _) (sortC (.succ Tower.zero))) (.sort _)
    (sortC _) ha

/-- The step `λ_ _. num → num : Π n : num. (λ_. U0) n → (λ_. U0) (suc n)`. -/
theorem arrowStep_typed :
    Typed largeRules Γ arrowStep
      (.pi numT (.pi (.app (.lam U0) (.var 0)) (.app (.lam U0) (sucNative (.var 1))))) := by
  have tDom : Typed largeRules (.snoc Γ numT) (.app (.lam U0) (.var 0))
      (sortTm (.succ Tower.zero)) := .appElim constU0_typed (.var 0)
  have tCod : Typed largeRules (.snoc (.snoc Γ numT) (.app (.lam U0) (.var 0)))
      (.app (.lam U0) (sucNative (.var 1))) (sortTm (.succ Tower.zero)) :=
    .appElim constU0_typed (.appElim suc_typedL (.var 1))
  have tInner : Typed largeRules (.snoc Γ numT)
      (.pi (.app (.lam U0) (.var 0)) (.app (.lam U0) (sucNative (.var 1))))
      (sortTm (.succ Tower.zero)) := piC tDom tCod
  have tBody : Typed largeRules (.snoc (.snoc Γ numT) (.app (.lam U0) (.var 0)))
      (.pi numT numT) (.app (.lam U0) (sucNative (.var 1))) :=
    .conv (piC num_typedL num_typedL) (.symm (constU0_beta (.appElim suc_typedL (.var 1))))
      (.sort _)
  exact .lamIntro (piC (raiseC num_typedL fun _ => Nat.zero_le _) tInner) (.sort _)
    (.lamIntro tInner (.sort _) tBody)

/-- **Large elimination of the numbers, typed**: `num-rec (λ_. U0) num
(λ_ _. num → num) t` is a type of `U0` at every number `t`. -/
theorem bigRec_typed {t : Tower.Tm n} (ht : Typed largeRules Γ t numT) :
    Typed largeRules Γ (bigRec t) U0 := by
  have hNum : Typed largeRules Γ numT (.app (.lam U0) (.const zeroN)) :=
    .conv num_typedL (.symm (constU0_beta zero_typedL)) (.sort _)
  have h := Derivable.appElim (Derivable.appElim (Derivable.appElim
    (Derivable.appElim numRec_typedL constU0_typed) hNum) arrowStep_typed) ht
  exact .conv h (constU0_beta ht) (.sort _)

/-- The type `Π y : num. Id num 0 y → U0` of the large motive. -/
theorem largeMotiveType_typed :
    Typed largeRules Γ (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0))
      (sortTm (.succ Tower.zero)) :=
  piC (raiseC num_typedL fun _ => Nat.zero_le _)
    (piC (raiseC (.idForm num_typedL (.sort _) zero_typedL (.var 0)) fun _ => Nat.zero_le _)
      (sortC _))

/-- **The large motive is typed** at `Π y : num. Id num 0 y → U0`. -/
theorem largeMotiveAt_typed :
    Typed largeRules Γ largeMotiveAt (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0)) :=
  .lamIntro largeMotiveType_typed (.sort _)
    (.lamIntro (piC (raiseC (.idForm num_typedL (.sort _) zero_typedL (.var 0))
      fun _ => Nat.zero_le _) (sortC _)) (.sort _) (bigRec_typed (.var 1)))

/-- The large motive at `0` and reflexivity computes the numbers: by two β-steps
and the recursor's step at zero. -/
theorem largeMotive_zero_equal :
    Equal largeRules Γ (.app (.app largeMotiveAt (.const zeroN)) (.refl (.const zeroN))) numT U0 := by
  have tInner : Typed largeRules (.snoc Γ numT) (.pi (.id numT (.const zeroN) (.var 0)) U0)
      (sortTm (.succ Tower.zero)) :=
    piC (raiseC (.idForm num_typedL (.sort _) zero_typedL (.var 0)) fun _ => Nat.zero_le _)
      (sortC _)
  have tReflZero : Typed largeRules Γ (.refl (.const zeroN))
      (.id numT (.const zeroN) (.const zeroN)) := .reflIntro zero_typedL
  have tInnerZero : Typed largeRules Γ (.pi (.id numT (.const zeroN) (.const zeroN)) U0)
      (sortTm (.succ Tower.zero)) :=
    piC (raiseC (.idForm num_typedL (.sort _) zero_typedL zero_typedL) fun _ => Nat.zero_le _)
      (sortC _)
  have e₁ : Equal largeRules Γ (.app (.app largeMotiveAt (.const zeroN)) (.refl (.const zeroN)))
      (.app (.lam (bigRec (.const zeroN))) (.refl (.const zeroN))) U0 :=
    .appCong (.betaPi largeMotiveType_typed (.sort _)
      (.lamIntro tInner (.sort _) (bigRec_typed (.var 1))) zero_typedL) (.refl tReflZero)
  have e₂ : Equal largeRules Γ (.app (.lam (bigRec (.const zeroN))) (.refl (.const zeroN)))
      (bigRec (.const zeroN)) U0 :=
    .betaPi tInnerZero (.sort _) (bigRec_typed zero_typedL) tReflZero
  have iota : (iotaComputation numRecName ctors).step (bigRec (.const zeroN) : Tower.Tm n) numT :=
    ⟨.lam U0, [numT, arrowStep], 0, zeroN, [], [], numT, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have mem : computations[0] ∈ computations.filter
      (fun entry => allowedIn [numN, zeroN, sucN, numRecName] entry.1) :=
    List.mem_filter.mpr ⟨listed 0 (by decide), by decide⟩
  have step : largeRules.computation.step (bigRec (.const zeroN)) numT :=
    RootComputation.step_unionAll mem iota
  exact .trans (.trans e₁ e₂) (.root step (bigRec_typed zero_typedL) num_typedL)

/-- Identity elimination over the large motive, from `0` to `1` along `p`. -/
abbrev largeMotiveJ (p : Tower.Tm n) : Tower.Tm n :=
  appSpine (.const jName) [numT, .const zeroN, largeMotiveAt, .const zeroN, oneT, p]

/-- The context of a path from `0` to `1`. -/
abbrev pathContext : Tower.Ctx 1 := .snoc .nil (.id numT (.const zeroN) oneT)

theorem pathContext_formed : CtxFormed largeRules pathContext :=
  .snoc .nil ⟨_, .sort _, .idForm num_typedL (.sort _) zero_typedL one_typedL⟩

/-- **Identity elimination over the large motive is typed**: along a path
`p : Id num 0 1`, `J num 0 P 0 1 p : P 1 p`. -/
theorem largeMotiveJ_typed :
    Typed largeRules pathContext (largeMotiveJ (.var 0)) (.app (.app largeMotiveAt oneT) (.var 0)) := by
  obtain ⟨w, hw, typedJ⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
  have hJ : Typed largeRules pathContext (.const jName) (liftClosed Package.jType) :=
    .const (by show largeTypes jName = _; unfold largeTypes; rw [if_neg (by decide), if_pos rfl])
      (Derivable.mono tower_sub_control typedJ) hw
  have hZero : Typed largeRules pathContext (.const zeroN)
      (.app (.app largeMotiveAt (.const zeroN)) (.refl (.const zeroN))) :=
    .conv zero_typedL (.symm largeMotive_zero_equal) (.sort _)
  exact Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (Derivable.appElim (Derivable.appElim hJ num_typedL) zero_typedL) largeMotiveAt_typed) hZero)
    one_typedL) (.var 0)

end LargeTypings

/-- **The large motive is valid** in the transport value model, at
`Π y : num. Id num 0 y → U0`. -/
theorem largeMotive_valid :
    ModelSN.ValidTmS (vmodel v) .nil largeMotive
      (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0)) :=
  ModelSN.Typed.validS (largeRules_soundS v) largeMotiveAt_typed trivial

/-- **Identity elimination over the large motive is valid**: `J num 0 P 0 1 p`
is a valid term of `P 1 p` along every path variable `p : Id num 0 1`. -/
theorem largeMotiveJ_valid :
    ModelSN.ValidTmS (vmodel v) pathContext (largeMotiveJ (.var 0))
      (.app (.app largeMotiveAt oneT) (.var 0)) :=
  ModelSN.Typed.validS (largeRules_soundS v) largeMotiveJ_typed
    (ModelSN.CtxFormed.validS (largeRules_soundS v) pathContext_formed)

/-- Identity elimination over the large motive is strongly normalizing under the
object package's reduction, and so is its type. -/
theorem largeMotiveJ_sn :
    SN objectRules (largeMotiveJ (.var 0) : Tower.Tm 1) ∧
      SN objectRules (.app (.app largeMotiveAt oneT) (.var 0) : Tower.Tm 1) :=
  ModelSN.Typed.sn (largeRules_soundS fun _ => 0) pathContext_formed largeMotiveJ_typed

/-! ## Control 2: identity elimination at a large carrier -/

/-- The declaration of the second control: identity elimination with its carrier
in `U1` and its motive into `U0`. -/
def carrierTypes (name : DeclName) : Option (Tower.Tm 0) :=
  if name = jName then some (elimType (.sort (.succ Tower.zero)) (.sort Tower.zero)) else none

/-- The second control package: no computations. -/
abbrev carrierRules : Rules Tower.Head := controlRules carrierTypes []

/-- **The second control package is sound for the model**: identity elimination
at the carrier `U1` is valid by transport. -/
theorem carrierRules_soundS : ModelSN.TypedSoundS carrierRules (vmodel v) :=
  controlRules_typedSoundS v (fun h => absurd h (by simp)) fun {name type} declared => by
    change carrierTypes name = some type at declared
    unfold carrierTypes at declared
    split_ifs at declared with h
    subst h
    cases declared
    exact vmodel_valid_j_sorts v (.succ Tower.zero) Tower.zero

/-- The motive `λ Z _. Z`. -/
abbrev idMotive {n : Nat} : Tower.Tm n := .lam (.lam (.var 1))

/-- The context of two types of `U0`, a path between them, and a term of the
first: `X : U0, Y : U0, p : Id U0 X Y, d : X`. -/
abbrev transportContext : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil U0) U0) (.id U0 (.var 1) (.var 0))) (.var 2)

/-- Identity elimination at the carrier `U0` with the motive `λ Z _. Z`:
`J U0 X (λ Z _. Z) d Y p`. -/
abbrev transportJ : Tower.Tm 4 :=
  appSpine (.const jName) [U0, .var 3, idMotive, .var 0, .var 2, .var 1]

theorem transportContext_formed : CtxFormed carrierRules transportContext :=
  .snoc (.snoc (.snoc (.snoc .nil ⟨_, .sort _, sortC Tower.zero⟩) ⟨_, .sort _, sortC Tower.zero⟩)
    ⟨_, .sort _, .idForm (sortC Tower.zero) (.sort _) (.var 1) (.var 0)⟩) ⟨_, .sort _, .var 2⟩

/-- **Identity elimination at a large carrier is typed**: `J U0 X (λ Z _. Z) d Y p`
is a term of `Y`. -/
theorem transportJ_typed : Typed carrierRules transportContext transportJ (.var 2) := by
  obtain ⟨w, hw, typedJ⟩ := TowerEliminatorModel.elimType_typed (.succ Tower.zero) Tower.zero
  have hJ : Typed carrierRules transportContext (.const jName)
      (liftClosed (elimType (.sort (.succ Tower.zero)) (.sort Tower.zero))) :=
    .const (by show carrierTypes jName = _; unfold carrierTypes; rw [if_pos rfl])
      (Derivable.mono tower_sub_control typedJ) hw
  have tU0 : ∀ {m : Nat} {Δ : Tower.Ctx m}, Typed carrierRules Δ U0 (sortTm (.succ Tower.zero)) :=
    fun {_ _} => sortC Tower.zero
  -- the motive `λ Z _. Z`
  have tInner : Typed carrierRules (.snoc transportContext U0) (.pi (.id U0 (.var 4) (.var 0)) U0)
      (sortTm (.succ Tower.zero)) :=
    piC (.idForm tU0 (.sort _) (.var 4) (.var 0)) tU0
  have tOuter : Typed carrierRules transportContext (.pi U0 (.pi (.id U0 (.var 4) (.var 0)) U0))
      (sortTm (.succ Tower.zero)) := piC tU0 tInner
  have tBody : Typed carrierRules (.snoc transportContext U0) (.lam (.var 1))
      (.pi (.id U0 (.var 4) (.var 0)) U0) := .lamIntro tInner (.sort _) (.var 1)
  have tMotive : Typed carrierRules transportContext idMotive
      (.pi U0 (.pi (.id U0 (.var 4) (.var 0)) U0)) := .lamIntro tOuter (.sort _) tBody
  -- the method: `(λ Z _. Z) X (refl X) ≡ X`
  have tReflX : Typed carrierRules transportContext (.refl (.var 3)) (.id U0 (.var 3) (.var 3)) :=
    .reflIntro (.var 3)
  have eX : Equal carrierRules transportContext (.app (.app idMotive (.var 3)) (.refl (.var 3)))
      (.var 3) U0 :=
    .trans (.appCong (.betaPi tOuter (.sort _) tBody (.var 3)) (.refl tReflX))
      (.betaPi (piC (.idForm tU0 (.sort _) (.var 3) (.var 3)) tU0) (.sort _) (.var 4) tReflX)
  have tD : Typed carrierRules transportContext (.var 0)
      (.app (.app idMotive (.var 3)) (.refl (.var 3))) :=
    .conv (.var 0) (.symm eX) (.sort _)
  -- the result: `(λ Z _. Z) Y p ≡ Y`
  have eY : Equal carrierRules transportContext (.app (.app idMotive (.var 2)) (.var 1))
      (.var 2) U0 :=
    .trans (.appCong (.betaPi tOuter (.sort _) tBody (.var 2)) (.refl (.var 1)))
      (.betaPi (piC (.idForm tU0 (.sort _) (.var 3) (.var 2)) tU0) (.sort _) (.var 3) (.var 1))
  have h := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (Derivable.appElim (Derivable.appElim hJ tU0) (.var 3)) tMotive) tD) (.var 2)) (.var 1)
  exact .conv h eY (.sort _)

/-- **Identity elimination at a large carrier is valid**: a valid term of `Y` in
the context of two types, a path between them, and a term of the first. -/
theorem transportJ_valid : ModelSN.ValidTmS (vmodel v) transportContext transportJ (.var 2) :=
  ModelSN.Typed.validS (carrierRules_soundS v) transportJ_typed
    (ModelSN.CtxFormed.validS (carrierRules_soundS v) transportContext_formed)

/-- **Identity elimination at a large carrier computes to the transport** on the
value side: of `d` from `(λ Z _. Z) X (refl X)` into `(λ Z _. Z) Y p`. -/
theorem transportJ_red :
    WhRed (vmodel v).rules (vmodel v).roles transportJ
      (ValueSide.coeApp coeN (.app (.app idMotive (.var 3)) (.refl (.var 3)))
        (.app (.app idMotive (.var 2)) (.var 1)) (.var 0)) :=
  .single (.root (vmodel_j_rootStep v _ _ _ _ _ _))

/-- `(λ Z _. Z) T e` computes `T`. -/
theorem idMotive_red {n : Nat} (T e : Tower.Tm n) :
    WhRed (vmodel v).rules (vmodel v).roles (.app (.app idMotive T) e) T := by
  have red : WhRed (vmodel v).rules (vmodel v).roles (.app (.app idMotive T) e)
      (Presentation.inst0 e (Presentation.rename wk T)) :=
    .head (.appFun (.beta _ _)) (.single (.beta _ _))
  rwa [inst0_rename_wk] at red

/-- **At reflexivity between the numbers the transport returns its method**:
`J U0 num (λ Z _. Z) 0 num (refl num)` computes to `0`. -/
theorem transportJ_refl_red :
    WhRed (vmodel v).rules (vmodel v).roles
      (appSpine (.const jName) [U0, numT, idMotive, .const zeroN, numT, .refl numT] : Tower.Tm 0)
      (.const zeroN) :=
  .head (.root (vmodel_j_rootStep v _ _ _ _ _ _))
    ((vmodel_coeRules v).const (c := numN) (.inr ⟨_, tmodelRoles_num⟩) (idMotive_red v _ _)
      (idMotive_red v _ _))

/-! ## Control 3: identity elimination at a large carrier, with its computation -/

/-- The third control package: identity elimination with its carrier in `U1` and
its motive into `U0`, with its linear computation rule. -/
abbrev carrierJRules : Rules Tower.Head := controlRules carrierTypes [jName]

/-- Identity elimination is declared at carrier `U1` and motive `U0`. -/
theorem carrierTypes_j :
    carrierTypes jName = some (elimType (.sort (.succ Tower.zero)) (.sort Tower.zero)) := by
  unfold carrierTypes
  rw [if_pos rfl]

/-- **The third control package is sound for the model**: identity elimination
at carrier level one computes by its linear rule, which holds at its typed
instances. -/
theorem carrierJRules_typedSoundS : ModelSN.TypedSoundS carrierJRules (vmodel v) :=
  controlRules_typedSoundS v
    (fun _ => ⟨.sort (.succ Tower.zero), .sort Tower.zero, LevelTower.IsUniverse.sort _, carrierTypes_j⟩)
    fun {name type} declared => by
      change carrierTypes name = some type at declared
      unfold carrierTypes at declared
      split_ifs at declared with h
      subst h
      cases declared
      exact vmodel_valid_j_sorts v (.succ Tower.zero) Tower.zero

/-- The context of a type of `U0` and a term of it: `X : U0, d : X`. -/
abbrev largeReflContext : Tower.Ctx 2 := .snoc (.snoc .nil U0) (.var 0)

/-- Identity elimination at the carrier `U0`, with the motive `λ Z _. Z`, along
reflexivity: `J U0 X (λ Z _. Z) d X (refl X)`. -/
abbrev largeReflJ : Tower.Tm 2 :=
  appSpine (.const jName) [U0, .var 1, idMotive, .var 0, .var 1, .refl (.var 1)]

theorem largeReflContext_formed : CtxFormed carrierJRules largeReflContext :=
  .snoc (.snoc .nil ⟨_, .sort _, sortC Tower.zero⟩) ⟨_, .sort _, .var 0⟩

/-- **Identity elimination at a large carrier along reflexivity is typed**:
`J U0 X (λ Z _. Z) d X (refl X)` is a term of `X`. -/
theorem largeReflJ_typed : Typed carrierJRules largeReflContext largeReflJ (.var 1) := by
  obtain ⟨w, hw, typedJ⟩ := TowerEliminatorModel.elimType_typed (.succ Tower.zero) Tower.zero
  have hJ : Typed carrierJRules largeReflContext (.const jName)
      (liftClosed (elimType (.sort (.succ Tower.zero)) (.sort Tower.zero))) :=
    .const carrierTypes_j (Derivable.mono tower_sub_control typedJ) hw
  have tU0 : ∀ {m : Nat} {Δ : Tower.Ctx m}, Typed carrierJRules Δ U0 (sortTm (.succ Tower.zero)) :=
    fun {_ _} => sortC Tower.zero
  -- the motive `λ Z _. Z`
  have tInner : Typed carrierJRules (.snoc largeReflContext U0) (.pi (.id U0 (.var 2) (.var 0)) U0)
      (sortTm (.succ Tower.zero)) :=
    piC (.idForm tU0 (.sort _) (.var 2) (.var 0)) tU0
  have tOuter : Typed carrierJRules largeReflContext (.pi U0 (.pi (.id U0 (.var 2) (.var 0)) U0))
      (sortTm (.succ Tower.zero)) := piC tU0 tInner
  have tBody : Typed carrierJRules (.snoc largeReflContext U0) (.lam (.var 1))
      (.pi (.id U0 (.var 2) (.var 0)) U0) := .lamIntro tInner (.sort _) (.var 1)
  have tMotive : Typed carrierJRules largeReflContext idMotive
      (.pi U0 (.pi (.id U0 (.var 2) (.var 0)) U0)) := .lamIntro tOuter (.sort _) tBody
  -- the method and the result: `(λ Z _. Z) X (refl X) ≡ X`
  have tReflX : Typed carrierJRules largeReflContext (.refl (.var 1)) (.id U0 (.var 1) (.var 1)) :=
    .reflIntro (.var 1)
  have eX : Equal carrierJRules largeReflContext (.app (.app idMotive (.var 1)) (.refl (.var 1)))
      (.var 1) U0 :=
    .trans (.appCong (.betaPi tOuter (.sort _) tBody (.var 1)) (.refl tReflX))
      (.betaPi (piC (.idForm tU0 (.sort _) (.var 1) (.var 1)) tU0) (.sort _) (.var 2) tReflX)
  have tD : Typed carrierJRules largeReflContext (.var 0)
      (.app (.app idMotive (.var 1)) (.refl (.var 1))) :=
    .conv (.var 0) (.symm eX) (.sort _)
  have h := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (Derivable.appElim (Derivable.appElim hJ tU0) (.var 1)) tMotive) tD) (.var 1)) tReflX
  exact .conv h eX (.sort _)

/-- **Identity elimination at a large carrier computes at reflexivity**: in the
third control package `J U0 X (λ Z _. Z) d X (refl X) ≡ d : X`, by its linear
rule between two terms of `X`. -/
theorem largeReflJ_equal : Equal carrierJRules largeReflContext largeReflJ (.var 0) (.var 1) :=
  .root (RootComputation.step_unionAll (List.mem_filter.mpr ⟨listed 3 (by decide), by decide⟩)
    ⟨_, _, _, _, _, _, rfl, rfl⟩) largeReflJ_typed (.var 0)

/-- **The computation at a large carrier is valid in the model**, by the typed
step of identity elimination: `J U0 X (λ Z _. Z) d X (refl X)` and `d` are validly
equal at `X`. -/
theorem largeReflJ_valid : ModelSN.ValidEqS (vmodel v) largeReflContext largeReflJ (.var 0) (.var 1) :=
  (ModelSN.Derivable.validTS (carrierJRules_typedSoundS v) largeReflJ_equal
    (ModelSN.CtxFormed.validS (carrierJRules_typedSoundS v) largeReflContext_formed)).1

/-- Both sides of the computation at a large carrier, and their type, are strongly
normalizing under the object package's reduction. -/
theorem largeReflJ_sn :
    SN objectRules largeReflJ ∧ SN objectRules (.var 0 : Tower.Tm 2) ∧
      SN objectRules (.var 1 : Tower.Tm 2) :=
  ModelSN.Equal.sn (carrierJRules_typedSoundS fun _ => 0) largeReflContext_formed largeReflJ_equal

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
