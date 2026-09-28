import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Rules
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerEliminator
/-!
# Typings in the stages of the executable package

The declaration records of the normalization model ask for the declared type
of each constant, and each right-hand side, to be typed in the stage of the
package before the constant. This module names the stages and gives those
typings in the typed judgment: formation of dependent function, pair and
identity types at a universe level, declared constants, and the conversions
by β, by the equation of `eqAt` and by the equations of addition that the
right-hand side of `sucMove` needs.
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
open CertifiedTransforms (shared sharedBody stepOver evidenceFamily step_application_type)
open SetProfile (zeroNative sucNative addNative)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName U0 numT jType numRecType eqAtType sucMoveType keepType
  transportType composeType iterType returnIterType sucStepType stepFamily familyTelescope
  eqAtTelescope transportTelescope composeTelescope iterTelescope returnIterResult eqAtApp)

/-! ## Stages -/

/-- The names in a list. -/
def allowedIn (names : List DeclName) : DeclName → Bool := fun name => decide (name ∈ names)

abbrev numStage : Rules Tower.Head := stage (allowedIn [numN])
abbrev ctorStage : Rules Tower.Head := stage (allowedIn [numN, zeroN, sucN])
abbrev powStage : Rules Tower.Head := stage (allowedIn [numN, zeroN, sucN, setN, powerN])
abbrev emptyStage : Rules Tower.Head := stage (allowedIn [])
abbrev eqAtStage : Rules Tower.Head := stage (allowedIn [numN, zeroN, sucN, addN])
abbrev sucMoveStage : Rules Tower.Head :=
  stage (allowedIn [numN, zeroN, sucN, addN, jName, eqAtName])
abbrev returnIterStage : Rules Tower.Head := stage (allowedIn [numN, zeroN, sucN, iterName])
abbrev sucStepStage : Rules Tower.Head :=
  stage (allowedIn [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName])

theorem stage_declared {names : List DeclName} {name : DeclName} (mem : name ∈ names) :
    (stage (allowedIn names)).constantType name = allTypes name := by
  show (if allowedIn names name then allTypes name else none) = _
  rw [if_pos (show allowedIn names name = true from decide_eq_true mem)]

theorem stage_undeclared {names : List DeclName} {name : DeclName} (mem : name ∉ names) :
    (stage (allowedIn names)).constantType name = none := by
  show (if allowedIn names name then allTypes name else none) = _
  rw [if_neg (show ¬ allowedIn names name = true by simpa [allowedIn] using mem)]

/-! ## Formation at a universe level -/

section Toolkit

variable {allowed : DeclName → Bool} {n : Nat} {Γ : Tower.Ctx n}

abbrev U1 : Tower.Tm n := sortTm (.succ Tower.zero)

theorem universe_typed (level : LevelExpr) :
    Typed (stage allowed) Γ (sortTm level) (sortTm (.succ level)) :=
  .headType (.sort level)

theorem U0_typed : Typed (stage allowed) Γ U0 U1 := universe_typed Tower.zero

theorem raiseT {type : Tower.Tm n} (typed : Typed (stage allowed) Γ type U0) :
    Typed (stage allowed) Γ type U1 :=
  .cumul typed (fun valuation => by simp [LevelExpr.eval, Tower.zero])

theorem piT {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)} {level : LevelExpr}
    (domainTyped : Typed (stage allowed) Γ domain (sortTm level))
    (codomainTyped : Typed (stage allowed) (.snoc Γ domain) codomain (sortTm level)) :
    Typed (stage allowed) Γ (.pi domain codomain) (sortTm level) :=
  .cumul (.piForm domainTyped (.sort level) codomainTyped (.sort level) (.sorts level level))
    (fun valuation => by simp [LevelExpr.eval])

theorem sigmaT {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)} {level : LevelExpr}
    (domainTyped : Typed (stage allowed) Γ domain (sortTm level))
    (codomainTyped : Typed (stage allowed) (.snoc Γ domain) codomain (sortTm level)) :
    Typed (stage allowed) Γ (.sigma domain codomain) (sortTm level) :=
  .cumul (.sigmaForm domainTyped (.sort level) codomainTyped (.sort level) (.sorts level level))
    (fun valuation => by simp [LevelExpr.eval])

theorem idT {carrier left right : Tower.Tm n} {level : LevelExpr}
    (carrierTyped : Typed (stage allowed) Γ carrier (sortTm level))
    (leftTyped : Typed (stage allowed) Γ left carrier)
    (rightTyped : Typed (stage allowed) Γ right carrier) :
    Typed (stage allowed) Γ (.id carrier left right) (sortTm level) :=
  .idForm carrierTyped (.sort level) leftTyped rightTyped

/-- A declared constant at its declared type. -/
theorem constT {name : DeclName} {type : Tower.Tm 0} {level : LevelExpr}
    (declared : (stage allowed).constantType name = some type)
    (typed : Typed (stage allowed) .nil type (sortTm level)) :
    Typed (stage allowed) Γ (.const name) (liftClosed type) :=
  .const declared typed (.sort level)

end Toolkit

/-! ## The natural numbers and the sets -/

section Numbers

variable {n : Nat} {Γ : Tower.Ctx n}

theorem numT_typed {names : List DeclName} (mem : numN ∈ names) :
    Typed (stage (allowedIn names)) Γ numT U0 :=
  constT (level := .succ Tower.zero) (stage_declared mem) U0_typed

theorem setT_typed {names : List DeclName} (mem : setN ∈ names) :
    Typed (stage (allowedIn names)) Γ setT U0 :=
  constT (level := .succ Tower.zero) (stage_declared mem) U0_typed

theorem zero_typed {names : List DeclName} (numMem : numN ∈ names) (mem : zeroN ∈ names) :
    Typed (stage (allowedIn names)) Γ (.const zeroN) numT :=
  constT (level := Tower.zero) (stage_declared mem) (numT_typed numMem)

theorem suc_typed {names : List DeclName} (numMem : numN ∈ names) (mem : sucN ∈ names) :
    Typed (stage (allowedIn names)) Γ (.const sucN) (.pi numT numT) :=
  constT (level := Tower.zero) (stage_declared mem)
    (piT (numT_typed numMem) (numT_typed numMem))

theorem addType_typed {names : List DeclName} (numMem : numN ∈ names) :
    Typed (stage (allowedIn names)) .nil addType U0 :=
  piT (numT_typed numMem) (piT (numT_typed numMem) (numT_typed numMem))

theorem add_typed {names : List DeclName} (numMem : numN ∈ names) (mem : addN ∈ names) :
    Typed (stage (allowedIn names)) Γ (.const addN) (liftClosed addType) :=
  constT (level := Tower.zero) (stage_declared mem) (addType_typed numMem)

theorem powerType_typed {names : List DeclName} (setMem : setN ∈ names) :
    Typed (stage (allowedIn names)) .nil powerType U0 :=
  piT (setT_typed setMem) (setT_typed setMem)

theorem powType_typed {names : List DeclName} (numMem : numN ∈ names) (setMem : setN ∈ names) :
    Typed (stage (allowedIn names)) .nil powType U0 :=
  piT (numT_typed numMem) (piT (setT_typed setMem) (setT_typed setMem))

theorem power_typed {names : List DeclName} (setMem : setN ∈ names) (mem : powerN ∈ names) :
    Typed (stage (allowedIn names)) Γ (.const powerN) (liftClosed powerType) :=
  constT (level := Tower.zero) (stage_declared mem) (powerType_typed setMem)

end Numbers

/-- The recursor's declared type is the recursor type of `num`. -/
theorem numRecType_eq : numRecType = recType numN (.sort Tower.zero) ctors := rfl

/-- The recursor's type is typed with the type and its constructors. -/
theorem numRecType_typed : Typed ctorStage .nil numRecType U1 := by
  have numMem : numN ∈ [numN, zeroN, sucN] := by simp
  have zeroMem : zeroN ∈ [numN, zeroN, sucN] := by simp
  have sucMem : sucN ∈ [numN, zeroN, sucN] := by simp
  have tNum : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed ctorStage Γ numT U0 :=
    fun {_ _} => numT_typed numMem
  have tZero : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed ctorStage Γ (.const zeroN) numT :=
    fun {_ _} => zero_typed numMem zeroMem
  have tSuc : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed ctorStage Γ (.const sucN) (.pi numT numT) :=
    fun {_ _} => suc_typed numMem sucMem
  -- the motive's type
  have tE0 : Typed ctorStage .nil (.pi numT U0) U1 := piT (raiseT tNum) U0_typed
  -- the case of zero
  let Γ₁ : Tower.Ctx 1 := .snoc .nil (.pi numT U0)
  have tE1 : Typed ctorStage Γ₁ (.app (.var 0) (.const zeroN)) U0 := .appElim (B := U0) (.var 0) tZero
  -- the case of the successor
  let Γ₂ : Tower.Ctx 2 := .snoc Γ₁ (.app (.var 0) (.const zeroN))
  let Γ₂x : Tower.Ctx 3 := .snoc Γ₂ numT
  have tIH : Typed ctorStage Γ₂x (.app (.var 2) (.var 0)) U0 := .appElim (B := U0) (.var 2) (.var 0)
  let Γ₂h : Tower.Ctx 4 := .snoc Γ₂x (.app (.var 2) (.var 0))
  have tSucX : Typed ctorStage Γ₂h (.app (.const sucN) (.var 1)) numT := .appElim tSuc (.var 1)
  have tGoal : Typed ctorStage Γ₂h (.app (.var 3) (.app (.const sucN) (.var 1))) U0 :=
    .appElim (B := U0) (.var 3) tSucX
  have tE2 : Typed ctorStage Γ₂ (.pi numT (.pi (.app (.var 2) (.var 0))
      (.app (.var 3) (.app (.const sucN) (.var 1))))) U0 :=
    piT tNum (piT tIH tGoal)
  -- the scrutinee and the result
  let Γ₃ : Tower.Ctx 3 := .snoc Γ₂ (.pi numT (.pi (.app (.var 2) (.var 0))
      (.app (.var 3) (.app (.const sucN) (.var 1)))))
  have tBody : Typed ctorStage (.snoc Γ₃ numT) (.app (.var 3) (.var 0)) U0 :=
    .appElim (B := U0) (.var 3) (.var 0)
  exact piT tE0 (piT (raiseT tE1) (piT (raiseT tE2) (piT (raiseT tNum) (raiseT tBody))))

/-! ## The identity eliminator -/

theorem jType_eq : jType = elimType (.sort Tower.zero) (.sort Tower.zero) := rfl

theorem jType_typed : ∃ w, Tower.IsUniverse w ∧
    Typed (constantFreeRules rules) .nil (elimType (.sort Tower.zero) (.sort Tower.zero))
      (.head w) :=
  TowerEliminatorModel.elimType_typed Tower.zero Tower.zero

/-! ## The definitions' declared types -/

section DeclaredTypes

theorem eqAtType_typed : Typed eqAtStage .nil eqAtType U1 :=
  piT (raiseT (numT_typed (by simp))) U0_typed

theorem eqAt_typed {n : Nat} {Γ : Tower.Ctx n} {names : List DeclName}
    (numMem : numN ∈ names) (mem : eqAtName ∈ names) :
    Typed (stage (allowedIn names)) Γ (.const eqAtName) (.pi numT U0) :=
  constT (level := .succ Tower.zero) (stage_declared mem)
    (piT (raiseT (numT_typed numMem)) U0_typed)

theorem sucMoveType_typed {names : List DeclName} (numMem : numN ∈ names) (sucMem : sucN ∈ names)
    (eqAtMem : eqAtName ∈ names) : Typed (stage (allowedIn names)) .nil sucMoveType U0 :=
  piT (numT_typed numMem)
    (piT (.appElim (eqAt_typed numMem eqAtMem) (.var 0))
      (.appElim (eqAt_typed numMem eqAtMem) (.appElim (suc_typed numMem sucMem) (.var 1))))

theorem keepType_typed {allowed : DeclName → Bool} : Typed (stage allowed) .nil keepType U1 :=
  piT U0_typed (piT (piT (raiseT (.var 0)) U0_typed)
    (piT (raiseT (.var 1))
      (piT (raiseT (.appElim (B := U0) (.var 1) (.var 0)))
        (raiseT (sigmaT (.var 3) (.appElim (B := U0) (.var 3) (.var 0)))))))

theorem transportType_typed {allowed : DeclName → Bool} :
    Typed (stage allowed) .nil transportType U1 :=
  piT U0_typed (piT (piT (raiseT (.var 0)) U0_typed)
    (piT (raiseT (piT (.var 1) (.var 2)))
      (piT
        (raiseT (piT (.var 2)
          (piT (.appElim (B := U0) (.var 2) (.var 0))
            (.appElim (B := U0) (.var 3) (.appElim (B := .var 5) (.var 2) (.var 1))))))
        (piT (raiseT (.var 3))
          (piT (raiseT (.appElim (B := U0) (.var 3) (.var 0)))
            (raiseT (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0)))))))))

/-- `Π x : A. P x → Σ y : A. P y` in the context `A, P`, extended by `Δ`. -/
theorem stepFamily_typed {allowed : DeclName → Bool} {n : Nat} {Γ : Tower.Ctx n} :
    Typed (stage allowed) (.snoc (.snoc Γ U0) (.pi (.var 0) U0)) stepFamily U0 :=
  piT (.var 1) (piT (.appElim (B := U0) (.var 1) (.var 0))
    (sigmaT (.var 3) (.appElim (B := U0) (.var 3) (.var 0))))

theorem composeType_typed {allowed : DeclName → Bool} :
    Typed (stage allowed) .nil composeType U1 :=
  piT U0_typed (piT (piT (raiseT (.var 0)) U0_typed)
    (piT (raiseT stepFamily_typed)
      (piT (raiseT (stepFamily_typed.weaken (extension := stepFamily)))
        (piT (raiseT (.var 3))
          (piT (raiseT (.appElim (B := U0) (.var 3) (.var 0)))
            (raiseT (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0)))))))))

theorem iterType_typed {names : List DeclName} (numMem : numN ∈ names) :
    Typed (stage (allowedIn names)) .nil iterType U1 :=
  piT (raiseT (numT_typed numMem)) (piT U0_typed (piT (piT (raiseT (.var 0)) U0_typed)
    (piT (raiseT stepFamily_typed)
      (piT (raiseT (.var 2))
        (piT (raiseT (.appElim (B := U0) (.var 2) (.var 0)))
          (raiseT (sigmaT (.var 4) (.appElim (B := U0) (.var 4) (.var 0)))))))))

theorem returnIterType_typed {names : List DeclName} (numMem : numN ∈ names) :
    Typed (stage (allowedIn names)) .nil returnIterType U1 :=
  piT U0_typed (piT (piT (raiseT (.var 0)) U0_typed)
    (piT (raiseT (numT_typed numMem))
      (piT (raiseT (stepFamily_typed.weaken (extension := numT)))
        (piT (raiseT (.var 3))
          (piT (raiseT (.appElim (B := U0) (.var 3) (.var 0)))
            (raiseT (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0)))))))))

theorem sucStepType_typed : Typed sucStepStage .nil sucStepType U0 := by
  have numMem : numN ∈ [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName] := by
    simp
  have eqAtMem : eqAtName ∈
      [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName] := by
    simp
  exact piT (numT_typed numMem)
    (piT (.appElim (eqAt_typed numMem eqAtMem) (.var 0))
      (sigmaT (numT_typed numMem) (.appElim (eqAt_typed numMem eqAtMem) (.var 0))))

end DeclaredTypes

/-! ## Shared uses of a step -/

section Shared

variable {R : Rules Tower.Head} {n : Nat} {Γ : Tower.Ctx n}

/-- A step applied to a value and its evidence is a package of the family. -/
theorem stepAppT {A x evidence step : Tower.Tm n} {P : Tower.Tm (n + 1)}
    (stepTyped : Typed R Γ step (stepOver A P)) (value : Typed R Γ x A)
    (given : Typed R Γ evidence (inst0 x P)) :
    Typed R Γ (.app (.app step x) evidence) (evidenceFamily A P) := by
  have appliedValue := Derivable.appElim stepTyped value
  have appliedValue' : Typed R Γ (.app step x)
      (inst0 x (.pi P (rename wk (rename wk (evidenceFamily A P))))) := by
    simpa [stepOver] using appliedValue
  have appliedDomain := (step_application_type x P (evidenceFamily A P)) ▸ appliedValue'
  have appliedEvidence := Derivable.appElim appliedDomain given
  simpa [inst0_rename_wk] using appliedEvidence

/-- One shared use of a step, then a continuation reading both projections. -/
theorem sharedT {A x evidence step continuation : Tower.Tm n} {P : Tower.Tm (n + 1)}
    {u w : Tower.Head} (sigmaTyped : Typed R Γ (evidenceFamily A P) (.head u))
    (isUniv : R.isUniverse u) (joined : R.join u u w) (lowered : R.cumulative w u)
    (stepTyped : Typed R Γ step (stepOver A P)) (value : Typed R Γ x A)
    (given : Typed R Γ evidence (inst0 x P))
    (body : Typed R (.snoc Γ (evidenceFamily A P)) (sharedBody continuation)
      (rename wk (evidenceFamily A P))) :
    Typed R Γ (shared step continuation x evidence) (evidenceFamily A P) := by
  have package := stepAppT stepTyped value given
  have resultType : Typed R (.snoc Γ (evidenceFamily A P)) (rename wk (evidenceFamily A P))
      (.head u) := sigmaTyped.weaken
  have arrow := Derivable.cumul (Derivable.piForm sigmaTyped isUniv resultType isUniv joined)
    lowered
  have closure := Derivable.lamIntro arrow isUniv body
  have applied := Derivable.appElim closure package
  simpa [shared, inst0_rename_wk] using applied

end Shared

/-! ## The right-hand sides of the definitions by one equation -/

section Bodies

theorem addApp_typed {names : List DeclName} (numMem : numN ∈ names) (addMem : addN ∈ names)
    {n : Nat} {Γ : Tower.Ctx n} {a b : Tower.Tm n}
    (ta : Typed (stage (allowedIn names)) Γ a numT)
    (tb : Typed (stage (allowedIn names)) Γ b numT) :
    Typed (stage (allowedIn names)) Γ (addNative a b) numT :=
  .appElim (B := numT) (.appElim (B := .pi numT numT) (add_typed numMem addMem) ta) tb

theorem sucApp_typed {names : List DeclName} (numMem : numN ∈ names) (sucMem : sucN ∈ names)
    {n : Nat} {Γ : Tower.Ctx n} {a : Tower.Tm n}
    (ta : Typed (stage (allowedIn names)) Γ a numT) :
    Typed (stage (allowedIn names)) Γ (sucNative a) numT :=
  .appElim (B := numT) (suc_typed numMem sucMem) ta

theorem eqAtBody_typed : Typed eqAtStage eqAtTele eqAtRhs U0 := by
  have numMem : numN ∈ [numN, zeroN, sucN, addN] := by simp
  have zeroMem : zeroN ∈ [numN, zeroN, sucN, addN] := by simp
  have addMem : addN ∈ [numN, zeroN, sucN, addN] := by simp
  show Typed eqAtStage eqAtTele (.id numT (addNative zeroNative (.var 0)) (.var 0)) U0
  exact idT (numT_typed numMem)
    (addApp_typed numMem addMem (zero_typed numMem zeroMem) (.var 0)) (.var 0)

theorem keepBody_typed {allowed : DeclName → Bool} :
    Typed (stage allowed) keepTele keepRhs (.sigma (.var 3) (.app (.var 3) (.var 0))) := by
  show Typed (stage allowed) keepTele (.pair (.var 1) (.var 0)) _
  exact .pairIntro (sigmaT (.var 3) (.appElim (B := U0) (.var 3) (.var 0))) (.sort Tower.zero)
    (.var 1) (.var 0)

theorem transportBody_typed {allowed : DeclName → Bool} :
    Typed (stage allowed) transportTelescope transportRhs
      (.sigma (.var 5) (.app (.var 5) (.var 0))) := by
  show Typed (stage allowed) transportTelescope
    (.pair (.app (.var 3) (.var 1)) (Package.app2 (.var 2) (.var 1) (.var 0))) _
  have value := Derivable.appElim (B := .var 6)
    (Derivable.var (R := stage allowed) (Γ := transportTelescope) 3) (.var 1)
  have moved := Derivable.appElim
    (Derivable.appElim (Derivable.var (R := stage allowed) (Γ := transportTelescope) 2) (.var 1))
    (.var 0)
  exact .pairIntro (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0))) (.sort Tower.zero)
    value moved

theorem composeBody_typed {allowed : DeclName → Bool} :
    Typed (stage allowed) composeTelescope composeRhs
      (.sigma (.var 5) (.app (.var 5) (.var 0))) := by
  show Typed (stage allowed) composeTelescope (shared (.var 3) (.var 2) (.var 1) (.var 0)) _
  have package : Typed (stage allowed)
      (.snoc composeTelescope (.sigma (.var 5) (.app (.var 5) (.var 0))))
      (.var 0) (.sigma (.var 6) (.app (.var 6) (.var 0))) := .var 0
  have b1 := Derivable.appElim
    (Derivable.var (R := stage allowed)
      (Γ := .snoc composeTelescope (.sigma (.var 5) (.app (.var 5) (.var 0)))) 3)
    (Derivable.fstElim package)
  have b2 := Derivable.appElim b1 (Derivable.sndElim package)
  exact sharedT (A := .var 5) (P := .app (.var 5) (.var 0))
    (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0))) (.sort Tower.zero) (.sorts _ _)
    (fun valuation => by simp [LevelExpr.eval]) (.var 3) (.var 1) (.var 0) b2

theorem returnIterBody_typed {names : List DeclName} (numMem : numN ∈ names)
    (iterMem : iterName ∈ names) :
    Typed (stage (allowedIn names)) returnIterTele returnIterRhs returnIterResult := by
  have iterT : ∀ {n : Nat} {Γ : Tower.Ctx n},
      Typed (stage (allowedIn names)) Γ (.const iterName) (liftClosed iterType) :=
    fun {_ _} => constT (level := .succ Tower.zero) (stage_declared iterMem) (iterType_typed numMem)
  show Typed (stage (allowedIn names)) returnIterTele (.lam (.lam (.lam (.lam (.lam
    (Package.iterApp (.var 3) (.var 5) (.var 4) (.var 2) (.var 1) (.var 0))))))) _
  -- the innermost body, in the context `A, P, n, step, x, e`
  have i1 := Derivable.appElim (iterT (Γ := Package.returnContext6)) (Derivable.var 3)
  have i2 := Derivable.appElim i1 (Derivable.var 5)
  have i3 := Derivable.appElim i2 (Derivable.var 4)
  have i4 := Derivable.appElim i3 (Derivable.var 2)
  have i5 := Derivable.appElim i4 (Derivable.var 1)
  have body := Derivable.appElim i5 (Derivable.var 0)
  -- the formation of each remaining function type
  have fe : Typed (stage (allowedIn names)) Package.returnContext5
      (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))) U0 :=
    piT (.appElim (B := U0) (.var 3) (.var 0))
      (sigmaT (.var 5) (.appElim (B := U0) (.var 5) (.var 0)))
  have fx : Typed (stage (allowedIn names)) Package.returnContext4
      (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))))
      U0 :=
    piT (.var 3) fe
  have fs : Typed (stage (allowedIn names)) Package.returnContext3
      (.pi (rename wk stepFamily)
        (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0))))))
      U0 :=
    piT (stepFamily_typed.weaken (extension := numT)) fx
  have fn : Typed (stage (allowedIn names)) familyTelescope
      (.pi numT (.pi (rename wk stepFamily)
        (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))))))
      U0 :=
    piT (numT_typed numMem) fs
  have fp : Typed (stage (allowedIn names)) (.snoc .nil U0) returnIterResult U1 :=
    piT (piT (raiseT (.var 0)) U0_typed) (raiseT fn)
  exact .lamIntro fp (.sort _)
    (.lamIntro fn (.sort _)
      (.lamIntro fs (.sort _)
        (.lamIntro fx (.sort _)
          (.lamIntro fe (.sort _) body))))

theorem sucStepBody_typed :
    Typed sucStepStage eqAtTelescope sucStepRhs (.sigma numT (eqAtApp (.var 0))) := by
  have numMem : numN ∈ [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName] := by
    simp
  have sucMem : sucN ∈ [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName] := by
    simp
  have eqAtMem : eqAtName ∈
      [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName] := by
    simp
  have sucMoveMem : sucMoveName ∈
      [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName] := by
    simp
  have transportMem : transportName ∈
      [numN, zeroN, sucN, addN, jName, eqAtName, sucMoveName, transportName] := by
    simp
  show Typed sucStepStage eqAtTelescope (Package.transportApp numT (.const eqAtName)
    (.const sucN) (.const sucMoveName) (.var 1) (.var 0)) _
  have transportT : Typed sucStepStage eqAtTelescope (.const transportName)
      (liftClosed transportType) :=
    constT (level := .succ Tower.zero) (stage_declared transportMem) transportType_typed
  have sucMoveT : Typed sucStepStage eqAtTelescope (.const sucMoveName) (liftClosed sucMoveType) :=
    constT (level := Tower.zero) (stage_declared sucMoveMem)
      (sucMoveType_typed numMem sucMem eqAtMem)
  have t1 := Derivable.appElim transportT (numT_typed numMem)
  have t2 := Derivable.appElim t1 (eqAt_typed numMem eqAtMem)
  have t3 := Derivable.appElim t2 (suc_typed numMem sucMem)
  have t4 := Derivable.appElim t3 sucMoveT
  have t5 := Derivable.appElim t4 (Derivable.var 1)
  exact Derivable.appElim t5 (Derivable.var 0)

end Bodies

/-! ## Conversions -/

section Conversions

/-- Two β-steps of a family of types. -/
theorem betaTwoT {R : Rules Tower.Head} {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}
    {B : Tower.Tm (n + 1)} {M : Tower.Tm (n + 2)} {a b : Tower.Tm n} {level : LevelExpr}
    (formed : Typed R Γ (.pi A (.pi B U0)) (sortTm level)) (hl : R.isUniverse (.sort level))
    (formed₂ : Typed R (.snoc Γ A) (.pi B U0) (sortTm level))
    (body : Typed R (.snoc (.snoc Γ A) B) M U0)
    (ta : Typed R Γ a A) (tb : Typed R Γ b (inst0 a B)) :
    Equal R Γ (.app (.app (.lam (.lam M)) a) b)
      (inst0 b (Presentation.subst (liftSub (subst0 a)) M)) U0 := by
  have lamM : Typed R (.snoc Γ A) (.lam M) (.pi B U0) := .lamIntro formed₂ hl body
  have e₁ := Derivable.betaPi formed hl lamM ta
  have e₂ : Equal R Γ (.app (.app (.lam (.lam M)) a) b) (.app (inst0 a (.lam M)) b)
      (inst0 b U0) :=
    Derivable.appCong (A := inst0 a B) (B := U0) e₁ (.refl tb)
  have formedInst : Typed R Γ (.pi (inst0 a B) U0) (sortTm level) :=
    Typed.substitute formed₂ (SubstMor.single ta)
  have bodyInst : Typed R (.snoc Γ (inst0 a B)) (Presentation.subst (liftSub (subst0 a)) M) U0 :=
    Typed.substitute body (SubstMor.lift (SubstMor.single ta) B)
  have e₃ := Derivable.betaPi formedInst hl bodyInst tb
  exact .trans e₂ e₃

/-- The equation of `eqAt`, in a stage with it. -/
theorem eqAt_step {names : List DeclName} (eqAtMem : eqAtName ∈ names) {n : Nat}
    (t : Tower.Tm n) :
    (stage (allowedIn names)).computation.step (eqAtApp t)
      (.id numT (addNative zeroNative t) t) := by
  have listed : (eqAtName, definitionComputation eqAtName eqAtTele eqAtRhs) ∈ computations :=
    List.getElem_mem (l := computations) (by decide : 4 < computations.length)
  exact RootComputation.step_unionAll
    (List.mem_filter.mpr ⟨listed, decide_eq_true eqAtMem⟩) ⟨fun _ => t, rfl, rfl⟩

/-- The successor equation of addition, in a stage with it. -/
theorem add_suc_step {names : List DeclName} (addMem : addN ∈ names) {n : Nat}
    (a b : Tower.Tm n) :
    (stage (allowedIn names)).computation.step (addNative a (sucNative b))
      (sucNative (addNative a b)) := by
  have listed : (addN, recursionComputation addN ctors addEntries 1 0 addBody) ∈ computations :=
    List.getElem_mem (l := computations) (by decide : 1 < computations.length)
  exact RootComputation.step_unionAll
    (List.mem_filter.mpr ⟨listed, decide_eq_true addMem⟩)
    ⟨sucN, [.recursive], consSub (sucNative b) (consSub a fun i => Fin.elim0 i), [b],
      List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, rfl, rfl⟩

end Conversions

/-! ## The successor move -/

theorem sucMoveBody_typed {names : List DeclName} (numMem : numN ∈ names)
    (zeroMem : zeroN ∈ names) (sucMem : sucN ∈ names) (addMem : addN ∈ names)
    (jMem : jName ∈ names) (eqAtMem : eqAtName ∈ names) :
    Typed (stage (allowedIn names)) eqAtTelescope sucMoveRhs (eqAtApp (sucNative (.var 1))) := by
  show Typed (stage (allowedIn names)) eqAtTelescope
    (Package.jApp numT (addNative zeroNative (.var 1)) (Package.sucMotive (.var 1))
      (.refl (sucNative (addNative zeroNative (.var 1)))) (.var 1) (.var 0))
    (eqAtApp (sucNative (.var 1)))
  have point : Typed (stage (allowedIn names)) eqAtTelescope (addNative zeroNative (.var 1)) numT :=
    addApp_typed numMem addMem (zero_typed numMem zeroMem) (.var 1)
  -- the motive `λ y p. suc (add zero n) = suc y`
  have formed₂ : Typed (stage (allowedIn names)) (.snoc eqAtTelescope numT)
      (.pi (.id numT (addNative zeroNative (.var 2)) (.var 0)) U0) U1 :=
    piT (raiseT (idT (numT_typed numMem)
      (addApp_typed numMem addMem (zero_typed numMem zeroMem) (.var 2)) (.var 0))) U0_typed
  have formed : Typed (stage (allowedIn names)) eqAtTelescope
      (.pi numT (.pi (.id numT (addNative zeroNative (.var 2)) (.var 0)) U0)) U1 :=
    piT (raiseT (numT_typed numMem)) formed₂
  have bodyM : Typed (stage (allowedIn names))
      (.snoc (.snoc eqAtTelescope numT) (.id numT (addNative zeroNative (.var 2)) (.var 0)))
      (.id numT (sucNative (addNative zeroNative (.var 3))) (sucNative (.var 1))) U0 :=
    idT (numT_typed numMem)
      (sucApp_typed numMem sucMem (addApp_typed numMem addMem (zero_typed numMem zeroMem) (.var 3)))
      (sucApp_typed numMem sucMem (.var 1))
  have motiveTyped : Typed (stage (allowedIn names)) eqAtTelescope (Package.sucMotive (.var 1))
      (.pi numT (.pi (.id numT (addNative zeroNative (.var 2)) (.var 0)) U0)) :=
    .lamIntro formed (.sort _) (.lamIntro formed₂ (.sort _) bodyM)
  -- the reflexivity case, retyped by β
  have reflCase : Typed (stage (allowedIn names)) eqAtTelescope
      (.refl (sucNative (addNative zeroNative (.var 1))))
      (.app (.app (Package.sucMotive (.var 1)) (addNative zeroNative (.var 1)))
        (.refl (addNative zeroNative (.var 1)))) :=
    .conv (.reflIntro (sucApp_typed numMem sucMem point))
      (.symm (betaTwoT formed (.sort _) formed₂ bodyM point (.reflIntro point))) (.sort Tower.zero)
  -- the evidence, retyped by the equation of `eqAt`
  have eAt : Equal (stage (allowedIn names)) eqAtTelescope (eqAtApp (.var 1))
      (.id numT (addNative zeroNative (.var 1)) (.var 1)) U0 :=
    .root (eqAt_step eqAtMem (.var 1)) (.appElim (eqAt_typed numMem eqAtMem) (.var 1))
      (idT (numT_typed numMem) point (.var 1))
  have path : Typed (stage (allowedIn names)) eqAtTelescope (.var 0)
      (.id numT (addNative zeroNative (.var 1)) (.var 1)) :=
    .conv (.var 0) eAt (.sort Tower.zero)
  -- the eliminator
  obtain ⟨w, hw, tj⟩ := jType_typed
  have declJ : (stage (allowedIn names)).constantType jName = some jType :=
    (stage_declared jMem).trans rfl
  have j0 : Typed (stage (allowedIn names)) eqAtTelescope (.const jName) (liftClosed jType) :=
    .const declJ (Derivable.mono (RulesSub.constantFree _) tj) hw
  rw [Package.jType_eq] at j0
  have j1 := Derivable.appElim j0 (numT_typed numMem)
  have j2 := Derivable.appElim j1 point
  have j3 := Derivable.appElim j2 motiveTyped
  have j4 := Derivable.appElim j3 reflCase
  have j5 := Derivable.appElim j4 (Derivable.var 1)
  have j6 := Derivable.appElim j5 path
  -- the motive at the endpoint is `eqAt (suc n)`: β, `eqAt`, `add`
  have βend := betaTwoT formed (.sort _) formed₂ bodyM (Derivable.var 1) path
  have eqAtSuc : Equal (stage (allowedIn names)) eqAtTelescope (eqAtApp (sucNative (.var 1)))
      (.id numT (addNative zeroNative (sucNative (.var 1))) (sucNative (.var 1))) U0 :=
    .root (eqAt_step eqAtMem _)
      (.appElim (eqAt_typed numMem eqAtMem) (sucApp_typed numMem sucMem (.var 1)))
      (idT (numT_typed numMem)
        (addApp_typed numMem addMem (zero_typed numMem zeroMem) (sucApp_typed numMem sucMem (.var 1)))
        (sucApp_typed numMem sucMem (.var 1)))
  have addSuc : Equal (stage (allowedIn names)) eqAtTelescope
      (addNative zeroNative (sucNative (.var 1))) (sucNative (addNative zeroNative (.var 1))) numT :=
    .root (add_suc_step addMem _ _)
      (addApp_typed numMem addMem (zero_typed numMem zeroMem) (sucApp_typed numMem sucMem (.var 1)))
      (sucApp_typed numMem sucMem point)
  have idEq : Equal (stage (allowedIn names)) eqAtTelescope
      (.id numT (addNative zeroNative (sucNative (.var 1))) (sucNative (.var 1)))
      (.id numT (sucNative (addNative zeroNative (.var 1))) (sucNative (.var 1))) U0 :=
    .idCong (.refl (numT_typed numMem)) (.sort _) addSuc (.refl (sucApp_typed numMem sucMem (.var 1)))
  exact .conv j6 (.trans βend (.symm (.trans eqAtSuc idEq))) (.sort Tower.zero)

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
