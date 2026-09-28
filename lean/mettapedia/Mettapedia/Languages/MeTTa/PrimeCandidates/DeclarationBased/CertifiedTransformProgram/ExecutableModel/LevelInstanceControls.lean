import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelInstancesSound
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.Inversion

/-!
# One term with two instances of identity elimination

In the context `A B : U0, p : Id U0 A B, a : A` with a consumer
`useLowest : elimType U0 U0 → U0` of identity elimination at its lowest type
(`mixedContext`), the term

`(useLowest J, J U0 A (λ Z _. Z) a B p) : Σ (T : U0). B`

uses identity elimination twice: whole, at its lowest type, and as transport at
the universe carrier `U0`, which needs carrier level one.

* **With one constant per instance it is typed.** In the package with every
  level instance, with the whole use the instance `jAt 0 0` and the transport the
  instance `jAt 1 0` (`mixedTerm`), the term is typed at `Σ (T : U0). B`
  (`mixedTerm_typed`) and strongly normalizing (`mixedTerm_sn`). Each use alone
  is typed with a single constant, the whole use in the object package
  (`wholeUse_typed`) and the transport in the package at carrier level one
  (`transportUse_typed_at`).
* **With one constant for both uses it is typed in no package at every level**
  (`mixedTermOne_untypable`): for all levels `lu lw lr`, the term whose two uses
  are the single `id:eliminate` of `objectRulesAt lu lw lr` is not typed at
  `Σ (T : U0). B`. It is the mixed term with its levels erased
  (`mixedTerm_eraseLevels`).

The untypability is read in the transport value model, at the valuation
`A, B ↦ num`, `p ↦ refl num`, `a ↦ 0`, `useLowest ↦ λ _. num`. Generation reads
the derivation's types, and each step of conversion, cumulativity and subtyping
is structural inclusion (`TypeLe.structural`). The whole use makes identity
elimination's declared type `elimType (U lu) (U lw)` structurally included in
`elimType U0 U0`, since the consumer's domain has one pack and one shape with the
type of its argument; inclusion of dependent function types keeps domains of one
pack, so `U lu` and `U0` have one pack. The transport's first argument `U0` is
then a value of the pack of `U0`, which it is not. Every branch in which a type
along the way is hereditarily total is refuted by the numbers, the lowest
universe or the lowest type of identity elimination, none of which is.
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

/-! ## The mixed term -/

/-- The declared type of identity elimination at the lowest universes,
`elimType U0 U0`. -/
abbrev lowestJType : Tower.Tm 0 := elimType (.sort Tower.zero) (.sort Tower.zero)

/-- **The context of the mixed term**: `A B : U0, p : Id U0 A B, a : A`, and a
consumer `useLowest : elimType U0 U0 → U0` of identity elimination at its lowest
type. -/
abbrev mixedContext : Tower.Ctx 5 := .snoc transportContext (.pi (liftClosed lowestJType) U0)

/-- The type `Σ (T : U0). B` of the mixed term. -/
abbrev mixedType : Tower.Tm 5 := .sigma U0 (.var 4)

/-- The whole use of identity elimination by the constant `J`, passed to
`useLowest`. -/
abbrev wholeUse (J : DeclName) : Tower.Tm 5 := .app (.var 0) (.const J)

/-- The transport of `a` from `A` to `B` along `p` by the constant `J`:
`J U0 A (λ Z _. Z) a B p`. -/
abbrev transportUse (J : DeclName) : Tower.Tm 5 :=
  appSpine (.const J) [U0, .var 4, idMotive, .var 1, .var 3, .var 2]

/-- The mixed term with its whole use by `whole` and its transport by
`transport`. -/
abbrev mixedTermWith (whole transport : DeclName) : Tower.Tm 5 :=
  .pair (wholeUse whole) (transportUse transport)

/-- **The mixed term with one constant per instance**: the whole use by the
lowest instance `jAt 0 0`, the transport by the instance `jAt 1 0` of carrier
level one. -/
abbrev mixedTerm : Tower.Tm 5 :=
  mixedTermWith (jAt Tower.zero Tower.zero) (jAt (.succ Tower.zero) Tower.zero)

/-- Erasing levels sends the mixed term to the term whose two uses are the single
constant `id:eliminate`. -/
theorem mixedTerm_eraseLevels : mixedTerm.mapConst eraseLevels = mixedTermWith jName jName := by
  simp only [mixedTermWith, wholeUse, transportUse, Tm.mapConst, Tm.mapConst_appSpine,
    eraseLevels_jAt, List.map_cons, List.map_nil]
  rfl

/-! ## Typed with one constant per instance -/

/-- The package at carrier level one of the transport control renames into the
package with every instance: its identity elimination to the instance `jAt 1 0`,
and it has no computation. -/
theorem carrierRules_renames (lr : LevelExpr) :
    RulesRenaming carrierRules objectRulesInstances
      (instanceRenaming (.succ Tower.zero) Tower.zero lr) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    change carrierTypes name = some type at declared
    unfold carrierTypes at declared
    split_ifs at declared with h
    subst h
    cases declared
    rw [instanceRenaming_j, objectRulesInstances_j,
      mapConst_plain (instanceRenaming_plain _ _ _) rfl]
  computation := by
    intro n l r step
    obtain ⟨entry, mem, -⟩ := RootComputation.unionAll_step step
    have allowed := (List.mem_filter.mp mem).2
    simp [allowedIn] at allowed

/-- The tower is contained in the package with every instance. -/
theorem tower_sub_objectRulesInstances : RulesSub Tower.rules objectRulesInstances where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => nomatch declared
  computation := fun step => step.elim

/-- Identity elimination's lowest type is typed in the package with every
instance, at a universe. -/
theorem lowestJType_typed :
    ∃ w, objectRulesInstances.isUniverse w ∧
      Typed objectRulesInstances .nil lowestJType (.head w) := by
  obtain ⟨w, hw, typedJ⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
  exact ⟨w, hw, Derivable.mono tower_sub_objectRulesInstances typedJ⟩

/-- The declared type of the consumer is a type of the package with every
instance. -/
theorem consumerType_typed {n : Nat} {Γ : Tower.Ctx n} :
    IsType objectRulesInstances Γ (.pi (liftClosed lowestJType) U0) := by
  obtain ⟨w, hw, typedJ⟩ := lowestJType_typed
  have typedJ' : Typed objectRulesInstances Γ (liftClosed lowestJType) (.head w) :=
    typedJ.rename (fun i => Fin.elim0 i)
  cases hw with
  | sort level =>
      have u0 : Typed objectRulesInstances (.snoc Γ (liftClosed lowestJType)) U0
          (sortTm (.succ Tower.zero)) := .headType (.sort _)
      exact ⟨_, .sort _, Derivable.piForm typedJ' (.sort level) u0 (.sort _) (.sorts level _)⟩

/-- **The context of the mixed term is formed** in the package with every
instance. -/
theorem mixedContext_formed : CtxFormed objectRulesInstances mixedContext :=
  .snoc (CtxFormed.mapConst (carrierRules_renames Tower.zero) transportContext_formed)
    consumerType_typed

/-- **The mixed term with one constant per instance is typed**:
`(useLowest (jAt 0 0), jAt 1 0 U0 A (λ Z _. Z) a B p) : Σ (T : U0). B`. -/
theorem mixedTerm_typed : Typed objectRulesInstances mixedContext mixedTerm mixedType := by
  -- the type `Σ (T : U0). B`
  have tSigma : Typed objectRulesInstances mixedContext mixedType
      (sortTm (.max (.succ Tower.zero) Tower.zero)) :=
    .sigmaForm (.headType (.sort _)) (.sort _) (.var 4) (.sort _) (.sorts _ _)
  -- the whole use, by the lowest instance
  obtain ⟨w, hw, typedJ₀⟩ := lowestJType_typed
  have hJ : Typed objectRulesInstances mixedContext (.const (jAt Tower.zero Tower.zero))
      (liftClosed lowestJType) :=
    .const (objectRulesInstances_j _ _) typedJ₀ hw
  have hUse : Typed objectRulesInstances mixedContext (.var 0) (.pi (liftClosed lowestJType) U0) :=
    .var 0
  have tWhole : Typed objectRulesInstances mixedContext (wholeUse (jAt Tower.zero Tower.zero)) U0 :=
    .appElim hUse hJ
  -- the transport, by the instance of carrier level one
  have tTransport : Typed objectRulesInstances transportContext
      (appSpine (.const (jAt (.succ Tower.zero) Tower.zero))
        [U0, .var 3, idMotive, .var 0, .var 2, .var 1]) (.var 2) :=
    Typed.mapConst (carrierRules_renames Tower.zero) transportJ_typed
  have tTransport' : Typed objectRulesInstances mixedContext
      (transportUse (jAt (.succ Tower.zero) Tower.zero)) (.var 3) :=
    Typed.weaken tTransport
  exact .pairIntro tSigma (.sort _) tWhole tTransport'

/-- **The mixed term with one constant per instance is strongly normalizing**
under the reduction of the package with every instance, and so is its type. -/
theorem mixedTerm_sn :
    SN objectRulesInstances mixedTerm ∧ SN objectRulesInstances mixedType :=
  objectRulesInstances_sn mixedContext_formed mixedTerm_typed

/-! ## Each use alone is typed with a single constant -/

/-- The whole use alone is typed in the object package, by its own identity
eliminator at the lowest universes. -/
theorem wholeUse_typed : Typed objectRules mixedContext (wholeUse jName) U0 := by
  obtain ⟨w, hw, typedJ⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
  have typedJ₀ : Typed objectRules .nil lowestJType (.head w) := by
    rw [← objectRulesAt_zero]
    exact Derivable.mono (tower_sub_objectRulesAt Tower.zero Tower.zero Tower.zero) typedJ
  have hUse : Typed objectRules mixedContext (.var 0) (.pi (liftClosed lowestJType) U0) := .var 0
  have hJ : Typed objectRules mixedContext (.const jName) (liftClosed lowestJType) :=
    .const objectRules_declared_j typedJ₀ hw
  exact .appElim hUse hJ

/-- The transport alone is typed in the package at carrier level one. -/
theorem transportUse_typed_at (lr : LevelExpr) :
    Typed (objectRulesAt (.succ Tower.zero) Tower.zero lr) mixedContext (transportUse jName)
      (.var 3) :=
  Typed.weaken (transportJ_typed_at lr)

/-! ## The closed transport and large elimination by instances -/

/-- **The closed transport at the numbers by its instance of carrier level one is
typed**: `jAt 1 0 U0 num (λ Z _. Z) 0 num (refl num) : num`. The object package,
whose `id:eliminate` has its carrier in the lowest universe, does not type it
(`numTransportJ_untypable`). -/
theorem numTransportInstance_typed :
    Typed objectRulesInstances .nil
      (numTransportJ.mapConst (instanceRenaming (.succ Tower.zero) Tower.zero Tower.zero)) numT := by
  have transport : Typed objectRulesInstances transportContext
      (appSpine (.const (jAt (.succ Tower.zero) Tower.zero))
        [U0, .var 3, idMotive, .var 0, .var 2, .var 1]) (.var 2) :=
    Typed.mapConst (carrierRules_renames Tower.zero) transportJ_typed
  have num : Typed objectRulesInstances .nil numT U0 :=
    Derivable.mono objectRules_sub_objectRulesInstances num_typedO
  have zero : Typed objectRulesInstances .nil (.const zeroN) numT :=
    Derivable.mono objectRules_sub_objectRulesInstances zero_typedO
  have values : SubstMor objectRulesInstances transportContext .nil
      (consSub (.const zeroN) (consSub (.refl numT) (consSub numT (consSub numT
        fun i => Fin.elim0 i)))) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact zero
    refine Fin.cases ?_ (fun i => ?_) i
    · exact .reflIntro num
    refine Fin.cases ?_ (fun i => ?_) i
    · exact num
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    · exact num
  exact transport.substitute values

/-- Erasing levels sends it back to the object package's `numTransportJ`. -/
theorem numTransportInstance_eraseLevels :
    (numTransportJ.mapConst (instanceRenaming (.succ Tower.zero) Tower.zero Tower.zero)).mapConst
      eraseLevels = numTransportJ := by
  simp only [Tm.mapConst, Tm.mapConst_appSpine, instanceRenaming_j, eraseLevels_jAt, List.map_cons,
    List.map_nil]
  rfl

/-- The step `λ _ T. num → T` of the recursor at the large motive: the `n`-tuples of
numbers. -/
abbrev tupleStep {n : Nat} : Tower.Tm n := .lam (.lam (.pi numT (.var 1)))

/-- **The recursor at the large motive by its instance of motive level one**:
`numRecAt 1 (λ _. U0) num (λ _ T. num → T) 0`. -/
abbrev proposedLargeUse : Tower.Tm 0 :=
  appSpine (.const (numRecAt (.succ Tower.zero))) [.lam U0, numT, tupleStep, .const zeroN]

/-- The first control package, with the recursor's motive at level one, renames into
the package with every instance: its recursor to the instance `numRecAt 1` and its
identity elimination to the lowest instance. -/
theorem largeRules_renames :
    RulesRenaming largeRules objectRulesInstances
      (instanceRenaming Tower.zero Tower.zero (.succ Tower.zero)) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := by
    intro name type declared
    have ren := objectRulesAtWithoutSucMove_renames Tower.zero Tower.zero (.succ Tower.zero)
    exact ren.constantType (largeTypes_at declared)
  computation := by
    intro n l r step
    obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
    obtain ⟨listedIn, allowed⟩ := List.mem_filter.mp mem
    have ren := objectRulesAtWithoutSucMove_renames Tower.zero Tower.zero (.succ Tower.zero)
    refine ren.computation (.inl (RootComputation.step_unionAll
      (List.mem_filter.mpr ⟨listedIn, ?_⟩) h))
    simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
    rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | rfl
        | exact absurd allowed (by decide)

/-- `λ _ T. num → T : Π n : num. (λ_. U0) n → (λ_. U0) (suc n)`. -/
theorem tupleStep_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed largeRules Γ tupleStep
      (.pi numT (.pi (.app (.lam U0) (.var 0)) (.app (.lam U0) (SetProfile.sucNative (.var 1))))) := by
  have tDom : Typed largeRules (.snoc Γ numT) (.app (.lam U0) (.var 0))
      (sortTm (.succ Tower.zero)) := .appElim constU0_typed (.var 0)
  have tCod : Typed largeRules (.snoc (.snoc Γ numT) (.app (.lam U0) (.var 0)))
      (.app (.lam U0) (SetProfile.sucNative (.var 1))) (sortTm (.succ Tower.zero)) :=
    .appElim constU0_typed (.appElim suc_typedL (.var 1))
  have tInner : Typed largeRules (.snoc Γ numT)
      (.pi (.app (.lam U0) (.var 0)) (.app (.lam U0) (SetProfile.sucNative (.var 1))))
      (sortTm (.succ Tower.zero)) := piC tDom tCod
  have tT : Typed largeRules (.snoc (.snoc Γ numT) (.app (.lam U0) (.var 0))) (.var 0) U0 :=
    .conv (.var 0) (constU0_beta (.var 1)) (.sort _)
  have tBody : Typed largeRules (.snoc (.snoc Γ numT) (.app (.lam U0) (.var 0)))
      (.pi numT (.var 1)) (.app (.lam U0) (SetProfile.sucNative (.var 1))) :=
    .conv (piC num_typedL (Typed.weaken tT)) (.symm (constU0_beta (.appElim suc_typedL (.var 1))))
      (.sort _)
  exact .lamIntro (piC (raiseC num_typedL fun _ => Nat.zero_le _) tInner) (.sort _)
    (.lamIntro tInner (.sort _) tBody)

/-- **The recursor at the large motive by its instance is typed** at `U0`. -/
theorem proposedLargeUse_typed : Typed objectRulesInstances .nil proposedLargeUse U0 := by
  have tNum : Typed largeRules .nil numT (.app (.lam U0) (.const zeroN)) :=
    .conv num_typedL (.symm (constU0_beta zero_typedL)) (.sort _)
  have h := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    numRec_typedL constU0_typed) tNum) tupleStep_typed) zero_typedL
  have typed : Typed largeRules .nil
      (appSpine (.const numRecName) [.lam U0, numT, tupleStep, .const zeroN]) U0 :=
    .conv h (constU0_beta zero_typedL) (.sort _)
  exact Typed.mapConst largeRules_renames typed

/-! ## Typed in no package at every level with one constant -/

section OneConstant

open Presentation.TypedEquality.Impredicative.Consistency (World Morph)
open Presentation.TypedEquality.Impredicative.ValueSide (DenS Shape)

/-- A formed context persists into a larger package. -/
theorem ctxFormed_of_sub {R' R : Rules Tower.Head} (sub : RulesSub R' R) :
    ∀ {n : Nat} {Γ : Tower.Ctx n}, CtxFormed R' Γ → CtxFormed R Γ
  | _, _, .nil => .nil
  | _, _, .snoc formed ⟨u, hu, typed⟩ =>
      .snoc (ctxFormed_of_sub sub formed) ⟨u, sub.isUniverse hu, Derivable.mono sub typed⟩

/-- The context of the mixed term is formed in the tower, without constants. -/
theorem mixedContext_formed_tower : CtxFormed Tower.rules mixedContext := by
  have u0 : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed Tower.rules Γ U0 (sortTm (.succ Tower.zero)) :=
    fun {_ _} => .headType (.sort _)
  obtain ⟨w, hw, typedJ⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
  have consumer : IsType Tower.rules transportContext (.pi (liftClosed lowestJType) U0) := by
    have typedJ' : Typed Tower.rules transportContext (liftClosed lowestJType) (.head w) :=
      typedJ.rename (fun i => Fin.elim0 i)
    cases hw with
    | sort level =>
        exact ⟨_, .sort _, Derivable.piForm typedJ' (.sort level) u0 (.sort _) (.sorts level _)⟩
  exact .snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, .sort _, u0⟩) ⟨_, .sort _, u0⟩)
    ⟨_, .sort _, .idForm u0 (.sort _) (.var 1) (.var 0)⟩) ⟨_, .sort _, .var 2⟩) consumer

/-- The context of the mixed term is formed in the package at every level. -/
theorem mixedContext_formed_at (lu lw lr : LevelExpr) :
    CtxFormed (objectRulesAt lu lw lr) mixedContext :=
  ctxFormed_of_sub (tower_sub_objectRulesAt lu lw lr) mixedContext_formed_tower

/-- The transport value model at the valuation sending every level parameter to
`0`. -/
abbrev vmodel₀ : ModelS.SModel Tower.Head Nat := vmodel fun _ => 0

/-- **A closed valid term is a value of its closed type**, realized by itself, in
the closed world. -/
theorem closedValue {a T : Tower.Tm 0} (valid : ModelS.ValidTmS vmodel₀ .nil a T) :
    ∃ P, DenS vmodel₀.value World.closed T P ∧ P.rel a a ∧ (P.real a).mem a := by
  have e : ModelS.EqSubstS vmodel₀ .nil World.closed (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i : Sub Tower.Head 0 0) := trivial
  obtain ⟨P, den, -, -⟩ := valid.1 e
  have h := valid.2 e den
  simp only [TelescopeAbstraction.subst_empty, TelescopeAbstraction.liftClosed_zero] at den h
  exact ⟨P, den, h⟩

/-- Related valuations extend by a closed valid value. -/
theorem eqSubstS_snoc {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {σ : Sub Tower.Head (n + 1) 0}
    (rest : ModelS.EqSubstS vmodel₀ Γ World.closed (tailSub σ) (tailSub σ) (tailSub σ))
    {T : Tower.Tm 0} (entry : Presentation.subst (tailSub σ) A = T)
    (valid : ModelS.ValidTmS vmodel₀ .nil (σ 0) T) :
    ModelS.EqSubstS vmodel₀ (.snoc Γ A) World.closed σ σ σ := by
  obtain ⟨P, den, rel, mem⟩ := closedValue valid
  refine ⟨rest, P, ?_, rel, mem⟩
  rw [entry]
  exact den

/-! ### Closed values -/

/-- The object package is sound for the model at the valuation `0`. -/
abbrev objectSound₀ : ModelS.TypedSoundS objectRules vmodel₀ := vmodel_soundS_objectRules _

theorem valid_of_typed {a T : Tower.Tm 0} (typed : Typed objectRules .nil a T) :
    ModelS.ValidTmS vmodel₀ .nil a T :=
  ModelS.Typed.validS objectSound₀ typed trivial

/-- The inner type of the constant motive: `Π e : Id num 0 y. U0`. -/
theorem constMotiveInner_typed :
    Typed objectRules (.snoc .nil numT) (.pi (.id numT (.const zeroN) (.var 0)) U0)
      (sortTm (.succ Tower.zero)) :=
  piO (raiseO (.idForm num_typedO (.sort _) zero_typedO (.var 0))) U0_typedO

theorem constMotiveType_typed :
    Typed objectRules .nil (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0))
      (sortTm (.succ Tower.zero)) :=
  piO (raiseO num_typedO) constMotiveInner_typed

theorem constMotive_typed :
    Typed objectRules .nil constMotive (.pi numT (.pi (.id numT (.const zeroN) (.var 0)) U0)) :=
  .lamIntro constMotiveType_typed (.sort _)
    (.lamIntro constMotiveInner_typed (.sort _) num_typedO)

/-- The method of the constant motive at `0`: `(λ_ _. num) 0 (refl 0) ≡ num`. -/
theorem constMotive_zero_equal :
    Equal objectRules .nil (.app (.app constMotive (.const zeroN)) (.refl (.const zeroN)))
      numT U0 :=
  .trans (.appCong (.betaPi constMotiveType_typed (.sort _)
      (.lamIntro constMotiveInner_typed (.sort _) num_typedO) zero_typedO)
      (.refl (.reflIntro zero_typedO)))
    (.betaPi (piO (raiseO (.idForm num_typedO (.sort _) zero_typedO zero_typedO)) U0_typedO)
      (.sort _) num_typedO (.reflIntro zero_typedO))

/-- The consumer's value `λ _. num`. -/
theorem useValue_typed : Typed objectRules .nil (.lam numT) (.pi lowestJType U0) := by
  obtain ⟨w, hw, typedJ⟩ := TowerEliminatorModel.elimType_typed Tower.zero Tower.zero
  have typedJ' : Typed objectRules .nil lowestJType (.head w) := by
    rw [← objectRulesAt_zero]
    exact Derivable.mono (tower_sub_objectRulesAt Tower.zero Tower.zero Tower.zero) typedJ
  cases hw with
  | sort level =>
      have u0 : Typed objectRules (.snoc .nil lowestJType) U0 (sortTm (.succ Tower.zero)) :=
        .headType (.sort _)
      exact .lamIntro (Derivable.piForm typedJ' (.sort level) u0 (.sort _) (.sorts level _))
        (.sort _) num_typedO

/-- **The values of the context**: `A, B ↦ num`, `p ↦ refl num`, `a ↦ 0`,
`useLowest ↦ λ _. num`. -/
def mixedValues : Sub Tower.Head 5 0 :=
  consSub (.lam numT) (consSub (.const zeroN) (consSub (.refl numT)
    (consSub numT (consSub numT fun i => Fin.elim0 i))))

/-- The values are related valuations of the context of the mixed term. -/
theorem mixedValuation :
    ModelS.EqSubstS vmodel₀ mixedContext World.closed mixedValues mixedValues mixedValues :=
  eqSubstS_snoc (eqSubstS_snoc (eqSubstS_snoc (eqSubstS_snoc (eqSubstS_snoc trivial rfl
    (valid_of_typed num_typedO)) rfl (valid_of_typed num_typedO)) rfl
    (valid_of_typed (.reflIntro num_typedO))) rfl (valid_of_typed zero_typedO)) rfl
    (valid_of_typed useValue_typed)

/-! ### Types that are not hereditarily total -/

/-- The lowest universe is not hereditarily total. -/
theorem u0_not_total :
    ¬ Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed (U0 : Tower.Tm 0) U0 :=
  fun t => t.total_not_head (vmodel_laws _).value .refl (Tower.IsUniverse.sort _)

/-- The numbers are not hereditarily total: they do not relate `0` to `1`. -/
theorem num_pack_not_total {X : Tower.Tm 0}
    (red : WhRed vmodel₀.rules vmodel₀.roles X numT) :
    ¬ Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed X X := by
  intro total
  have laws := vmodel_valueLaws fun _ => 0
  have related := total.total_rel (ValueSide.DenS.facts laws)
    (ValueSide.DenS.expand red (ValueSide.DenS.num laws _))
    (.const zeroN) (.app (.const sucN) (.const zeroN))
  obtain ⟨s, hz, hs⟩ := ValueSide.numIndPack_rel.mp related
  have zero := Realizability.HasShape.deterministic laws.values.truth laws.star hz (.zero .refl)
  have suc := Realizability.HasShape.deterministic laws.values.truth laws.star hs
    (.suc .refl (.zero .refl))
  rw [zero] at suc
  cases suc

theorem num_not_total :
    ¬ Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed (numT : Tower.Tm 0) numT :=
  num_pack_not_total .refl

/-- `(λ _ _. num) 0 (refl 0)` computes the numbers. -/
theorem constMotive_zero_red :
    WhRed vmodel₀.rules vmodel₀.roles
      (.app (.app constMotive (.const zeroN)) (.refl (.const zeroN)) : Tower.Tm 0) numT :=
  .head (.appFun (.beta _ _)) (.single (.beta _ _))

/-- One step down a hereditarily total dependent function type, at a closed
valid argument. -/
theorem total_step {X A : Tower.Tm 0} {B : Tower.Tm 1}
    (t : Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed X X) (shape : X = .pi A B)
    {a : Tower.Tm 0} (valid : ModelS.ValidTmS vmodel₀ .nil a A) :
    Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed (inst0 a B) (inst0 a B) := by
  subst shape
  obtain ⟨P, den, rel, -⟩ := closedValue valid
  exact ModelS.total_cod (vmodel_laws _) t .refl den rel

/-- **The lowest type of identity elimination is not hereditarily total**: at the
arguments `num, 0, λ _ _. num, 0, 0, refl 0` its result is `(λ _ _. num) 0 (refl 0)`,
which computes the numbers. -/
theorem lowestJType_not_total :
    ¬ Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed lowestJType lowestJType := by
  intro t
  have t₁ := total_step t rfl (valid_of_typed num_typedO)
  have t₂ := total_step t₁ rfl (valid_of_typed zero_typedO)
  have t₃ := total_step t₂ rfl (valid_of_typed constMotive_typed)
  have t₄ := total_step t₃ rfl (valid_of_typed (.conv zero_typedO (.symm constMotive_zero_equal)
    (.sort _)))
  have t₅ := total_step t₄ rfl (valid_of_typed zero_typedO)
  have t₆ := total_step t₅ rfl (valid_of_typed (.reflIntro zero_typedO))
  exact num_pack_not_total constMotive_zero_red t₆

/-- **Types included in `Σ (T : U0). num`**: their domain is not hereditarily
total, nor are their codomains at the valid points of the domain. -/
theorem sigmaNum_facts {X : Tower.Tm 0} {Y : Tower.Tm 1}
    (le : Tm.sigma X Y = .sigma U0 numT ∨
      ModelS.SLe vmodel₀ World.closed (.sigma X Y) (.sigma U0 numT)) :
    ¬ Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed X X ∧
      ∀ {P : ValueSide.Pack vmodel₀.value 0}, DenS vmodel₀.value World.closed X P →
        ∀ {a : Tower.Tm 0}, P.Val a →
          ¬ Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed (inst0 a Y) (inst0 a Y) := by
  have laws := vmodel_laws fun _ => 0
  rcases le with same | le
  · obtain ⟨rfl, rfl⟩ := Tm.sigma.inj same
    exact ⟨u0_not_total, fun _ _ _ => num_not_total⟩
  · rcases ModelS.SLe.sigma_right laws le .refl with t | ⟨A, B, red, dom, cod⟩
    · have parts := t.total_sigma laws.value .refl
      exact absurd parts.domShape u0_not_total
    · obtain ⟨rfl, rfl⟩ := Tm.sigma.inj
        (ValueSide.whRed_of_whnf (sigma_whnf laws.value.shape _ _) red)
      exact ⟨fun t => u0_not_total (dom.total laws t),
        fun {_} hD {_} ha t => num_not_total ((cod hD ha).total laws t)⟩

/-- **With one constant for both uses, the mixed term is typed in no package at
every level**: for all levels `lu lw lr`, the term
`(useLowest J, J U0 A (λ Z _. Z) a B p)` whose two uses are the single
`id:eliminate` of `objectRulesAt lu lw lr` is not typed at `Σ (T : U0). B`. -/
theorem mixedTermOne_untypable (lu lw lr : LevelExpr) :
    ¬ Typed (objectRulesAt lu lw lr) mixedContext (mixedTermWith jName jName) mixedType := by
  intro typing
  have sound := vmodel_soundS_at (fun _ => 0) lu lw lr
  have laws := sound.laws
  have facts := ValueSide.DenS.facts laws.value
  have ctx := ModelS.CtxFormed.validS sound (mixedContext_formed_at lu lw lr)
  have e := mixedValuation
  have atValues : ∀ {X Y : Tower.Tm 5}, TypeLe (objectRulesAt lu lw lr) mixedContext X Y →
      Presentation.subst mixedValues X = Presentation.subst mixedValues Y ∨
        ModelS.SLe vmodel₀ World.closed (Presentation.subst mixedValues X)
          (Presentation.subst mixedValues Y) := by
    intro X Y le
    rcases ModelS.TypeLe.structural sound ctx le with same | le'
    · exact .inl (congrArg _ same)
    · exact .inr (le' e)
  -- generation: the pair, the whole use, and its consumer
  obtain ⟨A', B', u, -, -, t₁, t₂, le₁⟩ := Typed.generation typing
  obtain ⟨A'', B'', tV, tJ, le₂⟩ := Typed.generation t₁
  have le₃ : TypeLe (objectRulesAt lu lw lr) mixedContext (Ctx.lookup mixedContext 0)
      (.pi A'' B'') := Typed.generation tV
  -- the pair's type at the values
  obtain ⟨domNotTotal, codNotTotal⟩ := sigmaNum_facts (atValues le₁)
  -- the values of the uses
  have valid₁ := ModelS.Typed.validS sound t₁ ctx
  obtain ⟨P₁, den₁, -, -⟩ := valid₁.1 e
  have val₁ : P₁.Val (Presentation.subst mixedValues (wholeUse jName)) :=
    den₁.refl_left laws.value (valid₁.2 e den₁).1
  have validJ := ModelS.Typed.validS sound tJ ctx
  obtain ⟨PJ, denJ, -, -⟩ := validJ.1 e
  have valJ : PJ.Val (.const jName) := denJ.refl_left laws.value (validJ.2 e denJ).1
  -- the consumer's domain is not hereditarily total's escape
  have piNotTotal : ¬ Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed
      (Presentation.subst mixedValues (.pi A'' B'')) (Presentation.subst mixedValues (.pi A'' B'')) := by
    intro t
    have tc := ModelS.total_cod laws t .refl denJ valJ
    have tc' : Shape vmodel₀.value (DenS vmodel₀.value) .total World.closed
        (Presentation.subst mixedValues (inst0 (.const jName) B''))
        (Presentation.subst mixedValues (inst0 (.const jName) B'')) := by
      rw [subst_inst0]
      exact tc
    rcases atValues le₂ with same | le
    · rw [same] at tc'
      exact domNotTotal tc'
    · exact domNotTotal (le.total laws tc')
  -- the declared type of `id:eliminate` in the package
  obtain ⟨TJrest, TJshape⟩ : ∃ B, elimType (Tower.Head.sort lu) (Tower.Head.sort lw) =
      Tm.pi (.head (Tower.Head.sort lu)) B := ⟨_, rfl⟩
  obtain ⟨J₀rest, J₀shape⟩ : ∃ B, lowestJType = Tm.pi (.head (Tower.Head.sort Tower.zero)) B :=
    ⟨_, rfl⟩
  -- stage 1: the whole use includes identity elimination's type in its lowest type
  have toLowest : Presentation.subst mixedValues A'' = lowestJType ∨
      ModelS.SLe vmodel₀ World.closed (Presentation.subst mixedValues A'') lowestJType := by
    rcases atValues le₃ with same | le
    · left
      exact (Tm.pi.inj same).1.symm
    · rcases ModelS.SLe.pi_right laws le .refl with t | ⟨A, B, red, dom, -⟩
      · exact absurd t piNotTotal
      · obtain ⟨rfl, rfl⟩ := Tm.pi.inj (ValueSide.whRed_of_whnf (pi_whnf laws.value.shape _ _) red)
        obtain ⟨D, hJ, hA, d⟩ := dom (Morph.id World.closed)
        have lowest : Presentation.subst mixedValues
            (Presentation.rename wk (liftClosed lowestJType)) = lowestJType := by
          rw [rename_liftClosed, subst_liftClosed, TelescopeAbstraction.liftClosed_zero]
        simp only [rename_id, lowest] at hJ hA d
        exact .inr (.shape hA hJ rfl (d.symm facts))
  have spJ := ModelS.Typed.spineFacts sound tJ ctx (c := jName) (args := []) rfl
    (objectRulesAt_j lu lw lr) e
  have jIncl : ModelS.SLe vmodel₀ World.closed (elimType (.sort lu) (.sort lw)) lowestJType := by
    rcases spJ with ok | t
    · have ok' : ModelS.SLe vmodel₀ World.closed (elimType (.sort lu) (.sort lw))
          (Presentation.subst mixedValues A'') := by
        simpa only [ModelS.SpineOK, TelescopeAbstraction.liftClosed_zero, List.map_nil] using ok
      rcases toLowest with same | le
      · rw [same] at ok'
        exact ok'
      · exact .trans ok' le
    · exfalso
      rcases toLowest with same | le
      · rw [same] at t
        exact lowestJType_not_total t
      · exact lowestJType_not_total (le.total laws t)
  -- stage 2: inclusion of dependent function types keeps domains of one pack
  obtain ⟨D, hLu, hZero⟩ : ∃ D, DenS vmodel₀.value World.closed (.head (.sort lu)) D ∧
      DenS vmodel₀.value World.closed (.head (.sort Tower.zero)) D := by
    rw [J₀shape] at jIncl
    rcases ModelS.SLe.pi_right laws jIncl .refl with t | ⟨A, B, red, dom, -⟩
    · rw [← J₀shape] at t
      exact absurd t lowestJType_not_total
    · rw [TJshape] at red
      obtain ⟨rfl, rfl⟩ := Tm.pi.inj (ValueSide.whRed_of_whnf (pi_whnf laws.value.shape _ _) red)
      obtain ⟨D, h₁, h₂, -⟩ := dom (Morph.id World.closed)
      simp only [rename_id] at h₁ h₂
      exact ⟨D, h₁, h₂⟩
  -- stage 3: the transport's first argument `U0` would be a value of `U0`
  have spT := ModelS.Typed.spineFacts sound t₂ ctx (c := jName) rfl (objectRulesAt_j lu lw lr) e
  rcases spT with ok | t
  · obtain ⟨A, B, red, ⟨P, den, val, -⟩, -⟩ := ok
    rw [TelescopeAbstraction.liftClosed_zero, TJshape] at red
    obtain ⟨rfl, rfl⟩ := Tm.pi.inj (ValueSide.whRed_of_whnf (pi_whnf laws.value.shape _ _) red)
    obtain rfl := ValueSide.DenS.deterministic laws.value den hLu
    rw [ModelS.DenS.sort_inv laws (Tower.IsUniverse.sort _) hZero] at val
    obtain ⟨Q, interp, -, -⟩ := ModelS.universeAt.den val
    exact lt_irrefl _ (ValueSide.InterpAt.univ_inv laws.value interp .refl
      (Tower.IsUniverse.sort _)).1
  · rw [subst_inst0] at t
    exact codNotTotal den₁ val₁ t

end OneConstant

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
