import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Typings
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerArithmetic
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.RootCumulativityEta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativityClients
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerAccumulators
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerListAccumulators
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerWrittenDomains

/-!
# The executable package satisfies the hypotheses of the normalization model

Every constant of the executable package is declared by one of the records of
the model: `num` with its constructors and recursor as a simple inductive type,
addition, the iterated power set and the iterator by structural recursion,
identity elimination with its linear rule, and the remaining definitions by
one equation. Each record's types and right-hand sides are typed in the stage
of the package before its constant, and each stage's constants are semantic
by the records before it. So every declared constant is semantic, every root
step preserves typing, and the consequences of the model hold for the
package without hypotheses: typed terms have weak-head normal forms, reduction
preserves typing, dependent function types are injective, `zero` is not a
successor, the conversion algorithm is sound and complete, the typed equality is
decided between terms of a type, and the kernel's synthesized types are
principal, which makes its refutations theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open TelescopeAbstraction (closeType applyClosed)
open CertifiedTransforms (shared sharedBody stepOver evidenceFamily)
open SetProfile (zeroNative sucNative addNative)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName U0 numT jType numRecType eqAtType sucMoveType keepType
  transportType composeType iterType returnIterType sucStepType stepFamily familyTelescope
  eqAtTelescope transportTelescope composeTelescope iterTelescope returnIterResult eqAtApp)

/-! ## The setting -/

section Setting

variable (valuation : Nat → Nat)

/-- The tower's level model, for the executable package. -/
def levels : LevelModel rules ℕ where
  level := (TowerModel.levels valuation).level
  successor := (TowerModel.levels valuation).successor
  universe_typing := (TowerModel.levels valuation).universe_typing
  ground_typing := (TowerModel.levels valuation).ground_typing
  cumulative_universe := (TowerModel.levels valuation).cumulative_universe
  headEq_level := (TowerModel.levels valuation).headEq_level
  join_level := (TowerModel.levels valuation).join_level
  join_exists := (TowerModel.levels valuation).join_exists
  join_upper := (TowerModel.levels valuation).join_upper
  cumulative_refl := (TowerModel.levels valuation).cumulative_refl
  headEq_symm := (TowerModel.levels valuation).headEq_symm
  headEq_trans := (TowerModel.levels valuation).headEq_trans
  universe_decided := (TowerModel.levels valuation).universe_decided

/-- The normalization setting of the executable package, at a generic equality. -/
def settingAt (E : GenericEquality Tower.Head) : Setting Tower.Head ℕ where
  R := rules
  roles := roles
  E := E
  levels := levels valuation
  shape := shape
  constructors := constructorsDeclared

/-- The normalization setting of the executable package, at the typed equality. -/
abbrev setting : Setting Tower.Head ℕ := settingAt valuation (declarative rules)

theorem laws : (setting valuation).E.Laws (setting valuation).R (setting valuation).roles :=
  declarative_laws roles (levels valuation)

end Setting

/-! ## The table -/

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: l, a, b, h => by
      unfold List.lookup at h
      split at h
      · rename_i same
        have e := LawfulBEq.eq_of_beq same
        subst e
        cases h
        exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- A step of a listed computation is a step of the package. -/
theorem rules_step {entry : DeclName × RootComputation Tower.Head} (mem : entry ∈ computations)
    {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) : rules.computation.step l r :=
  RootComputation.step_unionAll (List.mem_filter.mpr ⟨mem, rfl⟩) h

theorem listed (i : Nat) (h : i < computations.length) : computations[i] ∈ computations :=
  List.getElem_mem h

theorem mem_zero : ((zeroN, []) : DeclName × List CtorField) ∈ ctors := List.mem_cons_self ..
theorem mem_suc : ((sucN, [.recursive]) : DeclName × List CtorField) ∈ ctors :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- The stage of the listed names is semantic when each listed constant is. -/
theorem allSemantic_of {S : Setting Tower.Head ℕ} {names : List DeclName}
    (semantic : ∀ name ∈ names, ∀ type, allTypes name = some type → SemanticConstant S name type) :
    AllSemantic S (stage (allowedIn names)) := by
  intro name type declared
  by_cases mem : name ∈ names
  · rw [stage_declared mem] at declared
    exact semantic name mem type declared
  · rw [stage_undeclared mem] at declared
    cases declared

theorem emptyStage_semantic {S : Setting Tower.Head ℕ} : AllSemantic S emptyStage :=
  allSemantic_of fun _ mem => absurd mem (List.not_mem_nil)

/-! ## The declarations -/

section Declarations

variable (valuation : Nat → Nat) {E : GenericEquality Tower.Head} (lawsE : E.Laws rules roles)
include lawsE

omit lawsE in
/-- The package declares `num` with `zero`, `suc` and its recursor. -/
theorem declaresNum :
    DeclaresInductive (settingAt valuation E) (constantFreeRules rules) numStage ctorStage numN
      (.sort Tower.zero) ctors numRecName (.sort Tower.zero) where
  role := roles_num
  recRole := roles_numRec
  hu := .sort _
  hv := .sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := stage_sub_rules _
  sub₂ := stage_sub_rules _
  semantic₀ := fun declared => nomatch declared
  stage₁ := by
    intro name type declared
    right
    by_cases h : name ∈ [numN]
    · rw [stage_declared h] at declared
      rw [List.mem_singleton] at h
      subst h
      exact ⟨rfl, (Option.some.inj declared).symm⟩
    · rw [stage_undeclared h] at declared
      cases declared
  stage₂ := by
    intro name type declared
    by_cases h : name ∈ [numN, zeroN, sucN]
    · rw [stage_declared h] at declared
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact .inl ((stage_declared (by simp)).trans declared)
      · exact .inr ⟨[], mem_zero, (Option.some.inj declared).symm⟩
      · exact .inr ⟨[.recursive], mem_suc, (Option.some.inj declared).symm⟩
    · rw [stage_undeclared h] at declared
      cases declared
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  recDeclared := rfl
  fieldTyped := by
    intro k fields F mem closed
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at closed
  ctorTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, .sort _, numT_typed (by simp)⟩
    · exact ⟨_, .sort _, piT (numT_typed (by simp)) (numT_typed (by simp))⟩
  recTyped := ⟨_, .sort _, numRecType_typed⟩
  iota := fun hms hi has hm =>
    rules_step (listed 0 (by decide)) ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

theorem sem_num : SemanticConstant (settingAt valuation E) numN U0 :=
  (declaresNum valuation).type_semantic lawsE

theorem sem_zero : SemanticConstant (settingAt valuation E) zeroN numT :=
  (declaresNum valuation).ctor_semantic lawsE mem_zero

theorem sem_suc : SemanticConstant (settingAt valuation E) sucN (.pi numT numT) :=
  (declaresNum valuation).ctor_semantic lawsE mem_suc

theorem sem_numRec : SemanticConstant (settingAt valuation E) numRecName numRecType :=
  (declaresNum valuation).rec_semantic lawsE

theorem sem_set : SemanticConstant (settingAt valuation E) setN U0 :=
  SemanticConstant.rigid (S := settingAt valuation E) lawsE (name := setN) rfl
    (U0_typed (allowed := fun _ => true))
    (.sort _) roles_set

theorem sem_power : SemanticConstant (settingAt valuation E) powerN powerType :=
  SemanticConstant.rigid (S := settingAt valuation E) lawsE (name := powerN) rfl
    (powerType_typed (names := [setN]) (by simp) |> Derivable.mono (stage_sub_rules _)) (.sort _)
    roles_power

/-- The package declares addition by recursion on its second argument. -/
theorem declaresAdd :
    DeclaresRecursion (settingAt valuation E) ctorStage addN numN ctors addEntries 1 0 numT addBody where
  role := roles_add
  scrutinee := rfl
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := (declaresNum valuation).semantic₂ lawsE
  typed := ⟨_, .sort _, addType_typed (by simp)⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed ctorStage (.snoc .nil numT)
      exact .snoc .nil ⟨_, .sort _, numT_typed (by simp)⟩
    · show CtxFormed ctorStage (.snoc (.snoc (.snoc .nil numT) numT) numT)
      exact .snoc (.snoc (.snoc .nil ⟨_, .sort _, numT_typed (by simp)⟩)
        ⟨_, .sort _, numT_typed (by simp)⟩) ⟨_, .sort _, numT_typed (by simp)⟩
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed ctorStage (.snoc .nil numT) (.var 0) numT
      exact .var 0
    · show Typed ctorStage (.snoc (.snoc (.snoc .nil numT) numT) numT)
        (.app (.const sucN) (.var 0)) numT
      exact sucApp_typed (by simp) (by simp) (.var 0)
  rule := by
    intro k fields mem m σ as has
    exact rules_step (listed 1 (by decide)) ⟨_, _, σ, as, mem, has, rfl, rfl⟩

theorem sem_add : SemanticConstant (settingAt valuation E) addN addType :=
  (declaresAdd valuation lawsE).semantic lawsE (declaresNum valuation)

/-- The package declares the iterated power set by recursion on the count. -/
theorem declaresPow :
    DeclaresRecursion (settingAt valuation E) powStage powN numN ctors powEntries 0 1 setT powBody where
  role := roles_pow
  scrutinee := rfl
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := allSemantic_of fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact @sem_num valuation E lawsE
    · exact @sem_zero valuation E lawsE
    · exact @sem_suc valuation E lawsE
    · exact @sem_set valuation E lawsE
    · exact @sem_power valuation E lawsE
  typed := ⟨_, .sort _, powType_typed (by simp) (by simp)⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed powStage (.snoc .nil setT)
      exact .snoc .nil ⟨_, .sort _, setT_typed (by simp)⟩
    · show CtxFormed powStage (.snoc (.snoc (.snoc .nil numT) setT) (.pi setT setT))
      exact .snoc (.snoc (.snoc .nil ⟨_, .sort _, numT_typed (by simp)⟩)
        ⟨_, .sort _, setT_typed (by simp)⟩)
        ⟨_, .sort _, piT (setT_typed (by simp)) (setT_typed (by simp))⟩
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed powStage (.snoc .nil setT) (.var 0) setT
      exact .var 0
    · show Typed powStage (.snoc (.snoc (.snoc .nil numT) setT) (.pi setT setT))
        (.app (.const powerN) (.app (.var 0) (.var 1))) setT
      exact .appElim (B := setT) (power_typed (by simp) (by simp))
        (.appElim (B := setT) (.var 0) (.var 1))
  rule := by
    intro k fields mem m σ as has
    exact rules_step (listed 2 (by decide)) ⟨_, _, σ, as, mem, has, rfl, rfl⟩

theorem sem_pow : SemanticConstant (settingAt valuation E) powN powType :=
  (declaresPow valuation lawsE).semantic lawsE (declaresNum valuation)

omit lawsE in
/-- The package declares identity elimination at the lowest universe. -/
theorem declaresJ :
    DeclaresEliminator (settingAt valuation E) jName (.sort Tower.zero) (.sort Tower.zero) where
  role := roles_j
  declared := rfl
  rule := by
    intro n a₀ a₁ a₂ a₃ a₄ a₅
    exact rules_step (listed 3 (by decide)) ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩
  hu := .sort _
  hv := .sort _
  typed := jType_typed

theorem sem_j : SemanticConstant (settingAt valuation E) jName jType :=
  (declaresJ valuation).semantic lawsE

theorem declaresEqAt :
    DeclaresDefinition (settingAt valuation E) eqAtStage eqAtName eqAtTele U0 eqAtRhs where
  role := roles_eqAt
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := allSemantic_of fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact @sem_num valuation E lawsE
    · exact @sem_zero valuation E lawsE
    · exact @sem_suc valuation E lawsE
    · exact @sem_add valuation E lawsE
  typed := ⟨_, .sort _, eqAtType_typed⟩
  body := eqAtBody_typed
  rule := fun σ => rules_step (listed 4 (by decide)) ⟨σ, rfl, rfl⟩

theorem sem_eqAt : SemanticConstant (settingAt valuation E) eqAtName eqAtType :=
  (declaresEqAt valuation lawsE).semantic lawsE

theorem declaresSucMove :
    DeclaresDefinition (settingAt valuation E) sucMoveStage sucMoveName eqAtTelescope
      (eqAtApp (sucNative (.var 1))) sucMoveRhs where
  role := roles_sucMove
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := allSemantic_of fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact @sem_num valuation E lawsE
    · exact @sem_zero valuation E lawsE
    · exact @sem_suc valuation E lawsE
    · exact @sem_add valuation E lawsE
    · exact @sem_j valuation E lawsE
    · exact @sem_eqAt valuation E lawsE
  typed := ⟨_, .sort _, sucMoveType_typed (by simp) (by simp) (by simp)⟩
  body := sucMoveBody_typed (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  rule := fun σ => rules_step (listed 5 (by decide)) ⟨σ, rfl, rfl⟩

theorem sem_sucMove : SemanticConstant (settingAt valuation E) sucMoveName sucMoveType :=
  (declaresSucMove valuation lawsE).semantic lawsE

omit lawsE in
theorem declaresKeep :
    DeclaresDefinition (settingAt valuation E) emptyStage keepName keepTele
      (.sigma (.var 3) (.app (.var 3) (.var 0))) keepRhs where
  role := roles_keep
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := emptyStage_semantic
  typed := ⟨_, .sort _, keepType_typed⟩
  body := keepBody_typed
  rule := fun σ => rules_step (listed 6 (by decide)) ⟨σ, rfl, rfl⟩

theorem sem_keep : SemanticConstant (settingAt valuation E) keepName keepType :=
  (declaresKeep valuation).semantic lawsE

omit lawsE in
theorem declaresTransport :
    DeclaresDefinition (settingAt valuation E) emptyStage transportName transportTelescope
      (.sigma (.var 5) (.app (.var 5) (.var 0))) transportRhs where
  role := roles_transport
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := emptyStage_semantic
  typed := ⟨_, .sort _, transportType_typed⟩
  body := transportBody_typed
  rule := fun σ => rules_step (listed 7 (by decide)) ⟨σ, rfl, rfl⟩

theorem sem_transport : SemanticConstant (settingAt valuation E) transportName transportType :=
  (declaresTransport valuation).semantic lawsE

omit lawsE in
theorem declaresCompose :
    DeclaresDefinition (settingAt valuation E) emptyStage composeName composeTelescope
      (.sigma (.var 5) (.app (.var 5) (.var 0))) composeRhs where
  role := roles_compose
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := emptyStage_semantic
  typed := ⟨_, .sort _, composeType_typed⟩
  body := composeBody_typed
  rule := fun σ => rules_step (listed 8 (by decide)) ⟨σ, rfl, rfl⟩

theorem sem_compose : SemanticConstant (settingAt valuation E) composeName composeType :=
  (declaresCompose valuation).semantic lawsE

/-- The type of the recursive call of the iterator: the iterator's type after
the count. -/
abbrev iterRest : Tower.Tm 6 :=
  .pi U0 (.pi (.pi (.var 0) U0) (.pi stepFamily (.pi (.var 2) (.pi (.app (.var 2) (.var 0))
    (.sigma (.var 4) (.app (.var 4) (.var 0)))))))

/-- The package declares the iterator by recursion on the count. -/
theorem declaresIter :
    DeclaresRecursion (settingAt valuation E) ctorStage iterName numN ctors iterEntries 0 5 iterResult
      iterBody where
  role := roles_iter
  scrutinee := rfl
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := (declaresNum valuation).semantic₂ lawsE
  typed := ⟨_, .sort _, iterType_typed (by simp)⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed ctorStage iterTelescope
      exact .snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, .sort _, U0_typed⟩)
        ⟨_, .sort _, piT (raiseT (.var 0)) U0_typed⟩) ⟨_, .sort _, stepFamily_typed⟩)
        ⟨_, .sort _, .var 2⟩) ⟨_, .sort _, .appElim (B := U0) (.var 2) (.var 0)⟩
    · show CtxFormed ctorStage (.snoc Package.iterSucTelescope iterRest)
      refine .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil
        ⟨_, .sort _, numT_typed (by simp)⟩) ⟨_, .sort _, U0_typed⟩)
        ⟨_, .sort _, piT (raiseT (.var 0)) U0_typed⟩) ⟨_, .sort _, stepFamily_typed⟩)
        ⟨_, .sort _, .var 2⟩) ⟨_, .sort _, .appElim (B := U0) (.var 2) (.var 0)⟩)
        ⟨.sort (.succ Tower.zero), .sort _, ?_⟩
      exact piT U0_typed (piT (piT (raiseT (.var 0)) U0_typed)
        (piT (raiseT stepFamily_typed)
          (piT (raiseT (.var 2))
            (piT (raiseT (.appElim (B := U0) (.var 2) (.var 0)))
              (raiseT (sigmaT (.var 4) (.appElim (B := U0) (.var 4) (.var 0))))))))
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed ctorStage iterTelescope (.pair (.var 1) (.var 0))
        (.sigma (.var 4) (.app (.var 4) (.var 0)))
      exact .pairIntro (sigmaT (.var 4) (.appElim (B := U0) (.var 4) (.var 0))) (.sort _)
        (.var 1) (.var 0)
    · show Typed ctorStage (.snoc Package.iterSucTelescope iterRest)
        (shared (.var 3) (.app (.app (.app (.var 0) (.var 5)) (.var 4)) (.var 3)) (.var 2) (.var 1))
        (.sigma (.var 5) (.app (.var 5) (.var 0)))
      have c1 := Derivable.appElim
        (Derivable.var (R := ctorStage) (Γ := .snoc Package.iterSucTelescope iterRest) 0)
        (Derivable.var 5)
      have c2 := Derivable.appElim c1 (Derivable.var 4)
      have continuation : Typed ctorStage (.snoc Package.iterSucTelescope iterRest)
          (.app (.app (.app (.var 0) (.var 5)) (.var 4)) (.var 3))
          (stepOver (.var 5) (.app (.var 5) (.var 0))) :=
        Derivable.appElim c2 (Derivable.var 3)
      have package : Typed ctorStage (.snoc (.snoc Package.iterSucTelescope iterRest)
          (.sigma (.var 5) (.app (.var 5) (.var 0))))
          (.var 0) (.sigma (.var 6) (.app (.var 6) (.var 0))) := .var 0
      have b1 := Derivable.appElim
        (continuation.weaken (extension := .sigma (.var 5) (.app (.var 5) (.var 0))))
        (Derivable.fstElim package)
      have b2 := Derivable.appElim b1 (Derivable.sndElim package)
      exact sharedT (A := .var 5) (P := .app (.var 5) (.var 0))
        (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0))) (.sort Tower.zero) (.sorts _ _)
        (fun valuation => by simp [LevelExpr.eval]) (.var 3) (.var 2) (.var 1) b2
  rule := by
    intro k fields mem m σ as has
    exact rules_step (listed 9 (by decide)) ⟨_, _, σ, as, mem, has, rfl, rfl⟩

theorem sem_iter : SemanticConstant (settingAt valuation E) iterName iterType :=
  (declaresIter valuation lawsE).semantic lawsE (declaresNum valuation)

theorem declaresReturnIter :
    DeclaresDefinition (settingAt valuation E) returnIterStage returnIterName returnIterTele
      returnIterResult returnIterRhs where
  role := roles_returnIter
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := allSemantic_of fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl <;> obtain rfl := Option.some.inj declared
    · exact @sem_num valuation E lawsE
    · exact @sem_zero valuation E lawsE
    · exact @sem_suc valuation E lawsE
    · exact @sem_iter valuation E lawsE
  typed := ⟨_, .sort _, returnIterType_typed (by simp)⟩
  body := returnIterBody_typed (by simp) (by simp)
  rule := fun σ => rules_step (listed 10 (by decide)) ⟨σ, rfl, rfl⟩

theorem sem_returnIter : SemanticConstant (settingAt valuation E) returnIterName returnIterType :=
  (declaresReturnIter valuation lawsE).semantic lawsE

theorem declaresSucStep :
    DeclaresDefinition (settingAt valuation E) sucStepStage sucStepName eqAtTelescope
      (.sigma numT (eqAtApp (.var 0))) sucStepRhs where
  role := roles_sucStep
  declared := rfl
  sub₀ := stage_sub_rules _
  semantic₀ := allSemantic_of fun name mem type declared => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      obtain rfl := Option.some.inj declared
    · exact @sem_num valuation E lawsE
    · exact @sem_zero valuation E lawsE
    · exact @sem_suc valuation E lawsE
    · exact @sem_add valuation E lawsE
    · exact @sem_j valuation E lawsE
    · exact @sem_eqAt valuation E lawsE
    · exact @sem_sucMove valuation E lawsE
    · exact @sem_transport valuation E lawsE
  typed := ⟨_, .sort _, sucStepType_typed⟩
  body := sucStepBody_typed
  rule := fun σ => rules_step (listed 11 (by decide)) ⟨σ, rfl, rfl⟩

theorem sem_sucStep : SemanticConstant (settingAt valuation E) sucStepName sucStepType :=
  (declaresSucStep valuation lawsE).semantic lawsE

/-- Every declared constant of the executable package is semantic, for any
generic equality with the laws. -/
theorem constantsAt : SemanticConstants (settingAt valuation E) := by
  intro name type w declared _ _
  have mem : (name, type) ∈ declarations := mem_of_lookup declared
  simp only [declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact @sem_num valuation E lawsE
  · exact @sem_set valuation E lawsE
  · exact @sem_zero valuation E lawsE
  · exact @sem_suc valuation E lawsE
  · exact @sem_add valuation E lawsE
  · exact @sem_power valuation E lawsE
  · exact @sem_pow valuation E lawsE
  · exact @sem_numRec valuation E lawsE
  · exact @sem_j valuation E lawsE
  · exact @sem_eqAt valuation E lawsE
  · exact @sem_sucMove valuation E lawsE
  · exact @sem_keep valuation E lawsE
  · exact @sem_transport valuation E lawsE
  · exact @sem_compose valuation E lawsE
  · exact @sem_iter valuation E lawsE
  · exact @sem_returnIter valuation E lawsE
  · exact @sem_sucStep valuation E lawsE

end Declarations

/-- Every declared constant of the executable package is semantic. -/
theorem constants (valuation : Nat → Nat) : SemanticConstants (setting valuation) :=
  constantsAt valuation (laws valuation)

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which every declared constant of the package is
semantic. -/
theorem facts : FormFacts rules roles :=
  .ofSemantic (S := setting fun _ => 0) (laws _) (constants _)

/-! ## Root steps and heads -/

/-- **Every root step of the package preserves typing in every package containing
it**, given the facts about the weak-head forms of that package's types. -/
theorem roots_in {S : Setting Tower.Head ℕ} (factsS : FormFacts S.R S.roles)
    (sub : RulesSub rules S.R) {n : Nat} {Γ : Tower.Ctx n} {l r A : Tower.Tm n}
    (formed : CtxFormed S.R Γ) (step : rules.computation.step l r) (typing : Typed S.R Γ l A) :
    Typed S.R Γ r A := by
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  have listedEntry := (List.mem_filter.mp mem).1
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedEntry
  have laws₀ := laws fun _ => 0
  rcases listedEntry with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (declaresNum (E := declarative rules) fun _ => 0).step_preserves factsS sub formed h
      typing
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    exact (declaresAdd (fun _ => 0) laws₀).rule_preserves factsS (declaresNum fun _ => 0) sub
      formed memk σ as has typing
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    exact (declaresPow (fun _ => 0) laws₀).rule_preserves factsS (declaresNum fun _ => 0) sub
      formed memk σ as has typing
  · obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩ := h
    exact (declaresJ (E := declarative rules) fun _ => 0).rule_preserves factsS sub formed typing
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact (declaresEqAt (fun _ => 0) laws₀).rule_preserves factsS sub formed σ typing
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact (declaresSucMove (fun _ => 0) laws₀).rule_preserves factsS sub formed σ typing
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact (declaresKeep (E := declarative rules) fun _ => 0).rule_preserves factsS sub formed σ
      typing
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact (declaresTransport (E := declarative rules) fun _ => 0).rule_preserves factsS sub formed
      σ typing
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact (declaresCompose (E := declarative rules) fun _ => 0).rule_preserves factsS sub formed
      σ typing
  · obtain ⟨k, fields, σ, as, memk, has, rfl, rfl⟩ := h
    exact (declaresIter (fun _ => 0) laws₀).rule_preserves factsS (declaresNum fun _ => 0) sub
      formed memk σ as has typing
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact (declaresReturnIter (fun _ => 0) laws₀).rule_preserves factsS sub formed σ typing
  · obtain ⟨σ, rfl, rfl⟩ := h
    exact (declaresSucStep (fun _ => 0) laws₀).rule_preserves factsS sub formed σ typing

/-- Every root step of the package preserves typing. -/
theorem roots : RootPreserving rules :=
  fun formed step typing => roots_in (S := setting fun _ => 0) facts (RulesSub.refl _) formed step
    typing

/-- Head equality steps preserve typing. -/
theorem heads : HeadPreserving rules := by
  intro n Γ h h' A same typing
  obtain ⟨w, headTyping, le⟩ := Typed.generation typing
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : rules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem algebra : CumulativeAlgebra rules where
  trans := TowerModel.algebra.trans
  same_left := TowerModel.algebra.same_left
  same_right := TowerModel.algebra.same_right
  join_least := TowerModel.algebra.join_least

theorem setting_roles_num (valuation : Nat → Nat) :
    (setting valuation).roles numN = .inductive ctors :=
  roles_num

/-! ## Consequences for the executable package -/

section Consequences

variable {n : Nat} {Γ : Tower.Ctx n}

/-- Every typed term of a formed context has a weak-head normal form. -/
theorem whnf_exists {t T : Tower.Tm n} (typing : Typed rules Γ t T) (formed : CtxFormed rules Γ) :
    ∃ nf, WhRed rules roles t nf ∧ Whnf rules roles nf :=
  Typed.whnf_exists (S := setting fun _ => 0) (laws _) (constants _) typing formed

/-- Reduction preserves typing, including every equation of the package. -/
theorem reduces_preserve {t t' T : Tower.Tm n} (formed : CtxFormed rules Γ)
    (red : Reduces rules t t') (typing : Typed rules Γ t T) :
    Typed rules Γ t' T ∧ Equal rules Γ t t' T :=
  Reduces.preserve (S := setting fun _ => 0) facts roots heads formed red typing

/-- Injectivity of dependent function types. -/
theorem pi_injective {A A' : Tower.Tm n} {B B' : Tower.Tm (n + 1)}
    (equal : TypeEq rules Γ (.pi A B) (.pi A' B')) (formed : CtxFormed rules Γ) :
    TypeEq rules Γ A A' ∧ TypeEq rules (.snoc Γ A) B B' :=
  TypeEq.pi_injective facts equal formed

/-- `zero` is not a successor. -/
theorem zero_ne_suc (formed : CtxFormed rules Γ) {a : Tower.Tm n} :
    ¬ Equal rules Γ (.const zeroN) (.app (.const sucN) a) numT :=
  Equal.ctor_discrimination (S := setting fun _ => 0) (laws _) (constants _) formed
    (setting_roles_num _) mem_zero mem_suc (by decide) (as := []) (bs := [a])

/-- In a typed elimination at reflexivity, the subject of the reflexivity proof
and the endpoint are equal to the point: the linear rule of `id:eliminate` fires
only where the comparisons it omits hold in the typed equality. -/
theorem j_endpoints (formed : CtxFormed rules Γ) {a x f d y z T : Tower.Tm n}
    (typing : Typed rules Γ (appSpine (.const jName) [a, x, f, d, y, .refl z]) T) :
    Equal rules Γ z x a ∧ Equal rules Γ y x a :=
  (declaresJ (E := declarative rules) fun _ => 0).endpoints facts (RulesSub.refl _) formed
    typing

/-- An elimination at reflexivity of `zero` whose endpoint is `suc zero` is not
typed. -/
theorem j_mismatch_untyped (formed : CtxFormed rules Γ) {f d T : Tower.Tm n} :
    ¬ Typed rules Γ (appSpine (.const jName) [numT, .const zeroN, f, d,
      .app (.const sucN) (.const zeroN), .refl (.const zeroN)]) T := by
  intro typing
  exact zero_ne_suc formed (.symm (j_endpoints formed typing).2)

/-- Soundness of the conversion algorithm. -/
theorem algorithm_sound {st : AlgorithmStatement Tower.Head} (derivation : Algorithm rules st) :
    AlgorithmSound (setting fun _ => 0) st :=
  Algorithm.sound (S := setting fun _ => 0) facts roots heads algebra derivation

/-- The declared constants of the package are semantic for the algorithmic
equality too. -/
theorem algorithmicConstants : SemanticConstants (algorithmicSetting (setting fun _ => 0)) :=
  constantsAt (fun _ => 0)
    (algorithmicSetting_laws (S := setting fun _ => 0) (laws _) (constants _) roots heads algebra)

/-- **The algorithmic equality is complete for the package**: derivably equal
terms of a formed context are algorithmically equal. -/
theorem complete : AlgorithmicComplete rules roles :=
  AlgorithmicComplete.ofSemantic (S := setting fun _ => 0) (laws _) (constants _) roots heads
    algebra algorithmicConstants

/-- Completeness of the conversion algorithm: derivably equal terms are
compared by it. -/
theorem algorithm_complete {t u T : Tower.Tm n} (formed : CtxFormed rules Γ)
    (equal : Equal rules Γ t u T) : Algorithm rules (.compare Γ t u T) :=
  Equal.algorithm (S := setting fun _ => 0) complete equal formed

/-- On typed terms of a formed context, the conversion algorithm derives
exactly the equalities of the typed equality. -/
theorem algorithm_iff {t u T : Tower.Tm n} (formed : CtxFormed rules Γ)
    (typedT : Typed rules Γ t T) (typedU : Typed rules Γ u T) :
    Algorithm rules (.compare Γ t u T) ↔ Equal rules Γ t u T :=
  algorithm_iff_equal (S := setting fun _ => 0) facts roots heads algebra complete formed typedT
    typedU

/-- Head equality of the package is decided. -/
theorem decideHeads (h h' : Tower.Head) : HeadSame rules h h' ∨ ¬ HeadSame rules h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

/-- The typed equality of the package is decided between two terms of a type:
the conversion algorithm terminates on them. -/
theorem equal_decide {t u T : Tower.Tm n} (formed : CtxFormed rules Γ)
    (typedT : Typed rules Γ t T) (typedU : Typed rules Γ u T) :
    Equal rules Γ t u T ∨ ¬ Equal rules Γ t u T :=
  Equal.decide (S := setting fun _ => 0) facts roots heads algebra decideHeads complete formed
    typedT typedU

/-- The equality of two types of the package is decided. -/
theorem typeEq_decide {A B : Tower.Tm n} (formed : CtxFormed rules Γ)
    (typeA : IsType rules Γ A) (typeB : IsType rules Γ B) :
    TypeEq rules Γ A B ∨ ¬ TypeEq rules Γ A B :=
  TypeEq.decide (S := setting fun _ => 0) facts roots heads algebra decideHeads complete formed
    typeA typeB

/-- Head typing of the package is a function. -/
theorem headsTyped {h u u' : Tower.Head} (first : rules.headTyping h u)
    (second : rules.headTyping h u') : u = u' := by
  cases first <;> cases second <;> rfl

/-- The universe order of the package is decided. -/
theorem decideCumulative (u v : Tower.Head) : rules.cumulative u v ∨ ¬ rules.cumulative u v :=
  Decidable.em (Tower.Cumulative u v)

/-- Whether a type of the package is usable at another is decided. -/
theorem below_decide {A B : Tower.Tm n} (formed : CtxFormed rules Γ)
    (typeA : IsType rules Γ A) (typeB : IsType rules Γ B) :
    Below rules Γ A B ∨ ¬ Below rules Γ A B :=
  Below.decide (S := setting fun _ => 0) facts roots heads algebra decideHeads complete
    decideCumulative formed typeA typeB

/-- On the bidirectional fragment the kernel checks a term against a type
exactly when the term has the type. -/
theorem check_iff_typed {t E : Tower.Tm n} (fragment : Bidirectional .check t)
    (formed : CtxFormed rules Γ) : Check rules roles Γ t E ↔ Typed rules Γ t E :=
  Check.iff_typed (S := setting fun _ => 0) facts algebra headsTyped fragment
    formed

/-- The kernel's synthesized type is principal: every type of the term lies
above it. -/
theorem synth_principal {t T : Tower.Tm n} (synth : Synth rules roles Γ t T)
    (formed : CtxFormed rules Γ) :
    Typed rules Γ t T ∧ ∀ {X}, Typed rules Γ t X → TypeLe rules Γ T X :=
  Synth.principal (S := setting fun _ => 0) facts algebra headsTyped synth formed

/-- A term does not have a type its synthesized type is not usable at. -/
theorem synth_not_typed {t T E : Tower.Tm n} (synth : Synth rules roles Γ t T)
    (formed : CtxFormed rules Γ) (notBelow : ¬ Below rules Γ T E) : ¬ Typed rules Γ t E :=
  Synth.not_typed (S := setting fun _ => 0) facts algebra headsTyped synth
    formed notBelow

/-- Terms whose synthesized types have no common upper bound are equal at no
type. -/
theorem synth_not_equal {t u T U C : Tower.Tm n} (st : Synth rules roles Γ t T)
    (su : Synth rules roles Γ u U) (formed : CtxFormed rules Γ)
    (apart : ¬ BoundedAbove rules Γ T U) : ¬ Equal rules Γ t u C :=
  Synth.not_equal_types (S := setting fun _ => 0) facts algebra headsTyped st su
    formed apart

end Consequences

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
