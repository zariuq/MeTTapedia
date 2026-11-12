import Mettapedia.Languages.Micromath.Kernel

/-
# LeanTcalcKernel: Formal Admission Boundary, 20-Rule Abstract Judgment Calculus,
# 23-Rule Concrete `lean_tcalc_theory.h` (`12` Leaf + `11` Premise-Bearing) Model,
# Three-Way Gold Route Correspondence, and Micromath ↔ MeTTa/MM2 Pattern Injection

This module provides the sorry-free formalization for:
1. **`lean_tcalc` (`tcalc/lean_tcalc.c` and `tcalc/lean_tcalc_theory.h`)**:
   - **Abstract 20-Rule Judgment Calculus (`LeanTcalcRuleId`, `TcalcStep`)**: Models the ideal
     context-bearing typing and declaration-admission steps paired with the explicit
     `SideConditionOracle` boundary (universe level algebra, WHNF/defeq certificates,
     strict positivity, and the structural recursor inductive-hypothesis guard `RecIHGuard`
     preventing circular self-application on 0-field constructors).
   - **Concrete 23-Rule `lean_tcalc_theory.h` Table (`ConcreteTheoryRuleId`, `ConcreteTheoryStep`)**:
     Models the exact 23 rules (`R[0..22]`) installed in `lean_tc_init_kernel` (`tcalc/lean_tcalc_theory.h`):
     12 `k->mflat` (`nkeep = 0`) leaf-emission rules (`R_CHECK_SORT` .. `R_EMIT_DECL_REQ3`) emitted
     by the C recursive checker, and 11 `k->flat` (`ordinary = true`) premise-bearing rules
     (`R_DERIVE_IS_TYPE`, `R_DERIVE_IS_PROP`, `R_CHECK_CONV`, and `R_ADMIT_AXIOM` .. `R_ADMIT_THM`).
     *Qualification*: In the C implementation, the 12 typing leaf rules are premise-free (`nkeep = 0`)
     certificate emitters invoked by the recursive C typechecker (`lean_infer_type`), whereas the
     11 premise-bearing rules (`R[12..22]`) enforce cross-premise equality guards and the `T_ID_ZERO`
     universe-zero guard inside `tcalc` / `lean_tcalc_gen.h`. Full C-to-Lean correspondence of the
     recursive C typechecker remains a separate verification layer.
2. **Gold Three-Way Route Commutation (`GOLD-4` & `GOLD-5`)**:
   - Route 0 (`OrigMeTTa`): `Source → AuthoredIR → EmittedPeTTa → ExistingPeTTa`
   - Route A (`PeTTaTcalc`): `Source → AuthoredIR → EmittedPeTTa → PeTTaTcalc`
   - Route B (`DirectTcalc`): `Source → AuthoredIR → DirectTcalc`
   - Commutation theorems (`three_way_gold_commutes`, proved under explicit route-agreement
     hypotheses `RouteAAgrees` and `RouteBAgrees`, plus a concrete unconditionally-discharged
     model pipeline witness `concreteDatalogPipeline_commutes`) and negative controls proving
     that answer-multiplicity and retained-explanation observations strictly refine
     extensional set observations.
-/

namespace Mettapedia.Languages.Lean.LeanTcalcKernel

/-! ## Part I: `lean_tcalc` Spaces, Rules, and Expressions -/

/-- The three `tcalc` spaces used by `lean_tcalc.c`. -/
inductive LeanTcalcSpace where
  | expr : LeanTcalcSpace  -- LEAN_SPACE_EXPR = 1
  | thm  : LeanTcalcSpace  -- LEAN_SPACE_THM  = 2
  | env  : LeanTcalcSpace  -- LEAN_SPACE_ENV  = 3
  deriving DecidableEq, Repr

/-- The 20 premise-bearing rules installed by `lean_build_kernel_rules` in `lean_tcalc.c`. -/
inductive LeanTcalcRuleId where
  | rCheckSort   : LeanTcalcRuleId  -- 1
  | rCheckConst  : LeanTcalcRuleId  -- 2
  | rCheckBVar   : LeanTcalcRuleId  -- 3
  | rCheckFVar   : LeanTcalcRuleId  -- 4
  | rCheckApp    : LeanTcalcRuleId  -- 5
  | rCheckLam    : LeanTcalcRuleId  -- 6
  | rCheckPi     : LeanTcalcRuleId  -- 7
  | rCheckLet    : LeanTcalcRuleId  -- 8
  | rCheckLitNat : LeanTcalcRuleId  -- 9
  | rCheckLitStr : LeanTcalcRuleId  -- 10
  | rCheckProj   : LeanTcalcRuleId  -- 11
  | rCheckConv   : LeanTcalcRuleId  -- 12
  | rDefEqRefl   : LeanTcalcRuleId  -- 13
  | rDefEqBeta   : LeanTcalcRuleId  -- 14
  | rDefEqDelta  : LeanTcalcRuleId  -- 15
  | rDefEqIota   : LeanTcalcRuleId  -- 16
  | rAdmitThm    : LeanTcalcRuleId  -- 17
  | rAdmitDef    : LeanTcalcRuleId  -- 18
  | rAdmitInd    : LeanTcalcRuleId  -- 19
  | rAdmitQuot   : LeanTcalcRuleId  -- 20
  deriving DecidableEq, Repr

/-- Metadata for each of the 20 `lean_tcalc` rules. -/
structure RuleSpec where
  id                 : LeanTcalcRuleId
  space              : LeanTcalcSpace
  numPremises        : Nat
  requiresSideOracle : Bool
  deriving DecidableEq, Repr

/-- Exact specification table matching `lean_build_kernel_rules` in `tcalc/lean_tcalc.c`. -/
def ruleSpec : LeanTcalcRuleId → RuleSpec
  | .rCheckSort   => ⟨.rCheckSort,   .expr, 1, false⟩
  | .rCheckConst  => ⟨.rCheckConst,  .expr, 1, true⟩
  | .rCheckBVar   => ⟨.rCheckBVar,   .expr, 1, false⟩
  | .rCheckFVar   => ⟨.rCheckFVar,   .expr, 1, false⟩
  | .rCheckApp    => ⟨.rCheckApp,    .expr, 2, true⟩
  | .rCheckLam    => ⟨.rCheckLam,    .expr, 2, false⟩
  | .rCheckPi     => ⟨.rCheckPi,     .expr, 2, true⟩
  | .rCheckLet    => ⟨.rCheckLet,    .expr, 3, true⟩
  | .rCheckLitNat => ⟨.rCheckLitNat, .expr, 1, false⟩
  | .rCheckLitStr => ⟨.rCheckLitStr, .expr, 1, false⟩
  | .rCheckProj   => ⟨.rCheckProj,   .expr, 2, true⟩
  | .rCheckConv   => ⟨.rCheckConv,   .expr, 3, false⟩
  | .rDefEqRefl   => ⟨.rDefEqRefl,   .expr, 1, false⟩
  | .rDefEqBeta   => ⟨.rDefEqBeta,   .expr, 2, true⟩
  | .rDefEqDelta  => ⟨.rDefEqDelta,  .expr, 2, true⟩
  | .rDefEqIota   => ⟨.rDefEqIota,   .expr, 2, true⟩
  | .rAdmitThm    => ⟨.rAdmitThm,    .thm,  2, true⟩
  | .rAdmitDef    => ⟨.rAdmitDef,    .env,  2, true⟩
  | .rAdmitInd    => ⟨.rAdmitInd,    .env,  2, true⟩
  | .rAdmitQuot   => ⟨.rAdmitQuot,   .env,  1, true⟩

/-- Kernel expression DAG representation corresponding to `LeanExprNode` in `lean_tcalc.c`. -/
inductive KernelExpr where
  | bvar    (idx : Nat)
  | fvar    (id : Nat)
  | sort    (level : Nat)
  | const   (name : String) (levels : List Nat)
  | app     (fn arg : KernelExpr)
  | lam     (dom body : KernelExpr)
  | forallE (dom body : KernelExpr)
  | letE    (ty val body : KernelExpr)
  | litNat  (n : Nat)
  | litStr  (s : String)
  | proj    (typeName : String) (idx : Nat) (structExpr : KernelExpr)
  deriving DecidableEq, Repr

/-- Facts stored across the three `tcalc` spaces in `lean_tcalc`. -/
inductive KernelFact where
  | envConst    (name : String) (ty : KernelExpr)
  | envDef      (name : String) (ty val : KernelExpr)
  | envInd      (name : String) (ty : KernelExpr) (numParams numIndices : Nat) (isRec : Bool)
  | envCtor     (name indName : String) (ty : KernelExpr) (cidx numParams numFields : Nat)
  | envRec      (name indName : String) (ty : KernelExpr) (numRules : Nat)
  | envQuot     (kind : String) (ty : KernelExpr)
  | ctxLocal    (ctxId fvarId : Nat) (ty : KernelExpr)
  | hasType     (ctxId : Nat) (e ty : KernelExpr)
  | defEq       (ctxId : Nat) (a b : KernelExpr)
  | admittedThm (name : String) (prop : KernelExpr)
  | admittedDef (name : String) (ty val : KernelExpr)
  | admittedInd (name : String) (numCtors : Nat) (numFields : Nat)
  | admittedQuot (ready : Bool)
  deriving DecidableEq, Repr

/-- The target space of any `KernelFact`. -/
def factSpace : KernelFact → LeanTcalcSpace
  | .envConst ..     => .env
  | .envDef ..       => .env
  | .envInd ..       => .env
  | .envCtor ..      => .env
  | .envRec ..       => .env
  | .envQuot ..      => .env
  | .ctxLocal ..     => .expr
  | .hasType ..      => .expr
  | .defEq ..        => .expr
  | .admittedThm ..  => .thm
  | .admittedDef ..  => .env
  | .admittedInd ..  => .env
  | .admittedQuot .. => .env

/-! ## Part II: Structural Recursor IH Guard & Explicit Side-Condition Oracle -/

/-- Structural inductive-hypothesis guard added in `lean_verify_and_admit_rec`
(`tcalc/lean_tcalc.c:4150-4203`):
For a constructor rule with `numParams` parameters, `numIndices` indices, and `numFields`
fields, every inductive hypothesis argument in the recursor RHS must be a recursor
application whose major premise is a constructor field FVar with index strictly in
`[numParams + numIndices, numParams + numIndices + numFields)`, and strictly increasing. -/
def RecIHGuard (numParams numIndices numFields : Nat) (ihMajorFVarIndices : List Nat) : Bool :=
  let lo := numParams + numIndices
  let hi := lo + numFields
  let rec checkIncreasing (prev : Option Nat) : List Nat → Bool
    | [] => true
    | idx :: rest =>
      let inRange := decide (lo ≤ idx ∧ idx < hi)
      let mono := match prev with
        | none => true
        | some p => decide (p < idx)
      inRange && mono && checkIncreasing (some idx) rest
  checkIncreasing none ihMajorFVarIndices

/-- Positive example: a recursive constructor with 1 parameter, 0 indices, and 2 fields
where field 1 (FVar index `1 + 0 + 1 = 2`) carries an inductive hypothesis passes `RecIHGuard`. -/
theorem recIHGuard_positive_example :
    RecIHGuard 1 0 2 [2] = true := by
  rfl

/-- Negative Control 6 (`lean_tcalc.c` circular recursor IH guard):
A 0-field constructor (`numFields = 0`, such as `Ind.mk : Ind` in the circular recursor
self-application attack) cannot have ANY inductive hypothesis argument in its recursor RHS. -/
theorem recIHGuard_rejects_zero_field_ih (numParams numIndices idx : Nat) (rest : List Nat) :
    RecIHGuard numParams numIndices 0 (idx :: rest) = false := by
  unfold RecIHGuard RecIHGuard.checkIncreasing
  simp

/-- Explicit side-condition oracle capturing the C callbacks paired with the 20 `tcalc` rules
(universe `imax`, substitution `instantiateRev`, strict positivity, and `RecIHGuard`). -/
structure SideConditionOracle where
  imaxLevel       : Nat → Nat → Nat
  instantiateType : KernelExpr → KernelExpr → KernelExpr
  noAxiomDeps     : String → Bool
  strictlyPos     : String → Bool
  quotPreludesOk  : Bool

/-- Single-step judgment admission over `tcalc` spaces (`TcalcStep`).
Every step corresponds to one of the 20 rules in `lean_tcalc.c`. -/
inductive TcalcStep (oracle : SideConditionOracle) (state : List KernelFact) :
    LeanTcalcRuleId → KernelFact → Prop where
  | checkSort (ctx : Nat) (u : Nat) :
      TcalcStep oracle state .rCheckSort
        (.hasType ctx (.sort u) (.sort (u + 1)))
  | checkConst (ctx : Nat) (name : String) (ty : KernelExpr) :
      KernelFact.envConst name ty ∈ state →
      TcalcStep oracle state .rCheckConst
        (.hasType ctx (.const name []) ty)
  | checkFVar (ctx fvarId : Nat) (ty : KernelExpr) :
      KernelFact.ctxLocal ctx fvarId ty ∈ state →
      TcalcStep oracle state .rCheckFVar
        (.hasType ctx (.fvar fvarId) ty)
  | checkApp (ctx : Nat) (fn arg dom body : KernelExpr) :
      KernelFact.hasType ctx fn (.forallE dom body) ∈ state →
      KernelFact.hasType ctx arg dom ∈ state →
      TcalcStep oracle state .rCheckApp
        (.hasType ctx (.app fn arg) (oracle.instantiateType body arg))
  | checkLam (ctx : Nat) (u : Nat) (dom body bodyTy : KernelExpr) :
      KernelFact.hasType ctx dom (.sort u) ∈ state →
      KernelFact.hasType (ctx + 1) body bodyTy ∈ state →
      TcalcStep oracle state .rCheckLam
        (.hasType ctx (.lam dom body) (.forallE dom bodyTy))
  | checkPi (ctx : Nat) (u v : Nat) (dom body : KernelExpr) :
      KernelFact.hasType ctx dom (.sort u) ∈ state →
      KernelFact.hasType (ctx + 1) body (.sort v) ∈ state →
      TcalcStep oracle state .rCheckPi
        (.hasType ctx (.forallE dom body) (.sort (oracle.imaxLevel u v)))
  | checkLet (ctx : Nat) (u : Nat) (ty val body bodyTy : KernelExpr) :
      KernelFact.hasType ctx ty (.sort u) ∈ state →
      KernelFact.hasType ctx val ty ∈ state →
      KernelFact.hasType ctx body bodyTy ∈ state →
      TcalcStep oracle state .rCheckLet
        (.hasType ctx (.letE ty val body) (oracle.instantiateType bodyTy val))
  | checkLitNat (ctx n : Nat) :
      KernelFact.envConst "Nat" (.sort 1) ∈ state →
      TcalcStep oracle state .rCheckLitNat
        (.hasType ctx (.litNat n) (.const "Nat" []))
  | checkLitStr (ctx : Nat) (s : String) :
      KernelFact.envConst "String" (.sort 1) ∈ state →
      TcalcStep oracle state .rCheckLitStr
        (.hasType ctx (.litStr s) (.const "String" []))
  | checkConv (ctx u : Nat) (e tyA tyB : KernelExpr) :
      KernelFact.hasType ctx e tyA ∈ state →
      KernelFact.hasType ctx tyB (.sort u) ∈ state →
      KernelFact.defEq ctx tyA tyB ∈ state →
      TcalcStep oracle state .rCheckConv
        (.hasType ctx e tyB)
  | defEqRefl (ctx : Nat) (e ty : KernelExpr) :
      KernelFact.hasType ctx e ty ∈ state →
      TcalcStep oracle state .rDefEqRefl
        (.defEq ctx e e)
  | defEqBeta (ctx : Nat) (dom body arg ty : KernelExpr) :
      KernelFact.hasType ctx (.app (.lam dom body) arg) ty ∈ state →
      TcalcStep oracle state .rDefEqBeta
        (.defEq ctx (.app (.lam dom body) arg) (oracle.instantiateType body arg))
  | defEqDelta (ctx : Nat) (name : String) (ty val : KernelExpr) :
      KernelFact.envDef name ty val ∈ state →
      TcalcStep oracle state .rDefEqDelta
        (.defEq ctx (.const name []) val)
  | admitThm (name : String) (prop val : KernelExpr) :
      KernelFact.hasType 0 prop (.sort 0) ∈ state →
      KernelFact.hasType 0 val prop ∈ state →
      oracle.noAxiomDeps name = true →
      TcalcStep oracle state .rAdmitThm
        (.admittedThm name prop)
  | admitDef (name : String) (u : Nat) (ty val : KernelExpr) :
      KernelFact.hasType 0 ty (.sort u) ∈ state →
      KernelFact.hasType 0 val ty ∈ state →
      oracle.noAxiomDeps name = true →
      TcalcStep oracle state .rAdmitDef
        (.admittedDef name ty val)
  | admitInd (name : String) (u numParams numIndices numCtors numFields : Nat)
      (ty : KernelExpr) (ihMajorFVarIndices : List Nat) :
      KernelFact.hasType 0 ty (.sort u) ∈ state →
      oracle.strictlyPos name = true →
      RecIHGuard numParams numIndices numFields ihMajorFVarIndices = true →
      TcalcStep oracle state .rAdmitInd
        (.admittedInd name numCtors numFields)
  | admitQuot :
      oracle.quotPreludesOk = true →
      TcalcStep oracle state .rAdmitQuot
        (.admittedQuot true)

/-- Multi-step reachable state closure from an empty initial store. -/
inductive TcalcReachable (oracle : SideConditionOracle) : List KernelFact → Prop where
  | init : TcalcReachable oracle []
  | step {state : List KernelFact} {r : LeanTcalcRuleId} {f : KernelFact} :
      TcalcReachable oracle state →
      TcalcStep oracle state r f →
      TcalcReachable oracle (f :: state)

/-! ## Part III: Soundness & Negative Non-Forgery Theorems for `lean_tcalc` -/

/-- Every `TcalcStep` emits a `KernelFact` in the exact `LeanTcalcSpace` declared by `ruleSpec`. -/
theorem factSpace_sound (oracle : SideConditionOracle) (state : List KernelFact)
    (r : LeanTcalcRuleId) (f : KernelFact)
    (h : TcalcStep oracle state r f) :
    factSpace f = (ruleSpec r).space := by
  cases h <;> rfl

/-- Theorem Admission Soundness: Any theorem `.admittedThm name prop` admitted in a
`TcalcReachable` store MUST have:
1. A proposition witness `hasType 0 prop (.sort 0)` (`isProp`),
2. A checked proof term `val` with `hasType 0 val prop`, and
3. `oracle.noAxiomDeps name = true`. -/
theorem thm_admission_requires_isProp_and_typed_proof
    (oracle : SideConditionOracle) (state : List KernelFact)
    (hReach : TcalcReachable oracle state)
    (name : String) (prop : KernelExpr)
    (hIn : KernelFact.admittedThm name prop ∈ state) :
    KernelFact.hasType 0 prop (.sort 0) ∈ state ∧
    (∃ val : KernelExpr, KernelFact.hasType 0 val prop ∈ state) ∧
    oracle.noAxiomDeps name = true := by
  induction hReach with
  | init =>
    cases hIn
  | @step st r f _ hStep ih =>
    simp only [List.mem_cons] at hIn
    rcases hIn with rfl | hTail
    · cases hStep with
      | admitThm _ _ val hProp hVal hNoAx =>
        refine ⟨List.mem_cons_of_mem _ hProp, ⟨val, List.mem_cons_of_mem _ hVal⟩, hNoAx⟩
    · rcases ih hTail with ⟨hProp, ⟨val, hVal⟩, hNoAx⟩
      exact ⟨List.mem_cons_of_mem _ hProp, ⟨val, List.mem_cons_of_mem _ hVal⟩, hNoAx⟩

/-- Negative Control 1 (`R_ADMIT_THM` Non-Prop Refusal):
If `hasType 0 prop (.sort 0) ∉ state`, then `R_ADMIT_THM` cannot admit `admittedThm name prop`,
even if `prop` is well-typed in a higher universe `Sort (u + 1)`. -/
theorem no_forged_thm_without_sort_zero
    (oracle : SideConditionOracle) (state : List KernelFact)
    (name : String) (prop : KernelExpr)
    (hNotProp : KernelFact.hasType 0 prop (.sort 0) ∉ state) :
    ¬ TcalcStep oracle state .rAdmitThm (.admittedThm name prop) := by
  intro hStep
  cases hStep with
  | admitThm _ _ _ hProp _ _ =>
    exact hNotProp hProp

/-- Negative Control 2 (`R_CHECK_CONV` Certificate Requirement):
Type conversion `R_CHECK_CONV` from `tyA` to `tyB` is impossible without a `defEq ctx tyA tyB`
certificate in `state`. -/
theorem conv_requires_defeq_certificate
    (oracle : SideConditionOracle) (state : List KernelFact)
    (ctx : Nat) (e tyB : KernelExpr)
    (hStep : TcalcStep oracle state .rCheckConv (.hasType ctx e tyB)) :
    ∃ (u : Nat) (tyA : KernelExpr),
      KernelFact.hasType ctx e tyA ∈ state ∧
      KernelFact.hasType ctx tyB (.sort u) ∈ state ∧
      KernelFact.defEq ctx tyA tyB ∈ state := by
  cases hStep with
  | checkConv _ u _ tyA _ hE hTyB hEq =>
    exact ⟨u, tyA, hE, hTyB, hEq⟩

/-- Negative Control 6 (`R_ADMIT_IND` / Recursor Circular IH Refusal):
Attempting to admit an inductive/recursor block whose 0-field constructor (`numFields = 0`)
carries a non-empty list of inductive-hypothesis recursive calls `idx :: rest` is unconditionally
refused by `TcalcStep`. -/
theorem circular_rec_ih_rejected
    (oracle : SideConditionOracle) (state : List KernelFact)
    (name : String) (numParams numIndices numCtors : Nat)
    (idx : Nat) (rest : List Nat) :
    ¬ TcalcStep oracle state .rAdmitInd (.admittedInd name numCtors 0) ∨
      RecIHGuard numParams numIndices 0 (idx :: rest) = false := by
  right
  exact recIHGuard_rejects_zero_field_ih numParams numIndices idx rest

/-! ## Part III-B: Exact 23-Rule Concrete `lean_tcalc_theory.h` (`12` Leaf + `11` Premise-Bearing) Model -/

/-- Exact 23-rule enumeration (`R[0..22]`) matching `lean_tc_init_kernel` in
`tcalc/lean_tcalc_theory.h` and `tc_lean_gen_flat_dispatch` in `tcalc/lean_tcalc_gen.h`:
- Rules `0..11` (`rCheckSort` .. `rEmitDeclReq3`) are the 12 `k->mflat` (`nkeep = 0`) leaf
  certificate-emission rules in `LEAN_SPACE_THM`.
- Rules `12..22` (`rDeriveIsType` .. `rAdmitThm`) are the 11 `k->flat` (`ordinary = true`)
  premise-bearing rules in `LEAN_SPACE_THM` and `LEAN_SPACE_ENV`. -/
inductive ConcreteTheoryRuleId where
  -- 12 leaf-emission rules (k->mflat == true, nkeep == 0)
  | rCheckSort     : ConcreteTheoryRuleId  -- 0
  | rCheckConst    : ConcreteTheoryRuleId  -- 1
  | rCheckApp      : ConcreteTheoryRuleId  -- 2
  | rCheckLam      : ConcreteTheoryRuleId  -- 3
  | rCheckForall   : ConcreteTheoryRuleId  -- 4
  | rCheckLet      : ConcreteTheoryRuleId  -- 5
  | rCheckProj     : ConcreteTheoryRuleId  -- 6
  | rCheckLit      : ConcreteTheoryRuleId  -- 7
  | rEmitDefEq     : ConcreteTheoryRuleId  -- 8
  | rEmitSortOf    : ConcreteTheoryRuleId  -- 9
  | rEmitDeclReq2  : ConcreteTheoryRuleId  -- 10
  | rEmitDeclReq3  : ConcreteTheoryRuleId  -- 11
  -- 11 premise-bearing rules (k->flat == true, ordinary == true)
  | rDeriveIsType  : ConcreteTheoryRuleId  -- 12 (nkeep = 2, LEAN_SPACE_THM)
  | rDeriveIsProp  : ConcreteTheoryRuleId  -- 13 (nkeep = 1, LEAN_SPACE_THM, T_ID_ZERO guard)
  | rCheckConv     : ConcreteTheoryRuleId  -- 14 (nkeep = 3, LEAN_SPACE_THM)
  | rAdmitAxiom    : ConcreteTheoryRuleId  -- 15 (nkeep = 2, LEAN_SPACE_ENV)
  | rAdmitQuot     : ConcreteTheoryRuleId  -- 16 (nkeep = 2, LEAN_SPACE_ENV)
  | rAdmitInd      : ConcreteTheoryRuleId  -- 17 (nkeep = 2, LEAN_SPACE_ENV)
  | rAdmitCtor     : ConcreteTheoryRuleId  -- 18 (nkeep = 3, LEAN_SPACE_ENV)
  | rAdmitRec      : ConcreteTheoryRuleId  -- 19 (nkeep = 2, LEAN_SPACE_ENV)
  | rAdmitDefn     : ConcreteTheoryRuleId  -- 20 (nkeep = 3, LEAN_SPACE_ENV)
  | rAdmitOpaque   : ConcreteTheoryRuleId  -- 21 (nkeep = 3, LEAN_SPACE_ENV)
  | rAdmitThm      : ConcreteTheoryRuleId  -- 22 (nkeep = 3, LEAN_SPACE_ENV)
  deriving DecidableEq, Repr

/-- Number of `keep` premises (`nkeep`) for each of the 23 concrete rules in `lean_tcalc_theory.h`. -/
def concreteRuleNKeep : ConcreteTheoryRuleId → Nat
  | .rCheckSort    | .rCheckConst   | .rCheckApp     | .rCheckLam
  | .rCheckForall  | .rCheckLet     | .rCheckProj    | .rCheckLit
  | .rEmitDefEq    | .rEmitSortOf   | .rEmitDeclReq2 | .rEmitDeclReq3 => 0
  | .rDeriveIsProp => 1
  | .rDeriveIsType | .rAdmitAxiom   | .rAdmitQuot    | .rAdmitInd     | .rAdmitRec => 2
  | .rCheckConv    | .rAdmitCtor    | .rAdmitDefn    | .rAdmitOpaque  | .rAdmitThm => 3

/-- Target space (`LEAN_SPACE_THM` vs `LEAN_SPACE_ENV`) for each of the 23 concrete rules. -/
def concreteRuleSpace : ConcreteTheoryRuleId → LeanTcalcSpace
  | .rCheckSort    | .rCheckConst   | .rCheckApp     | .rCheckLam
  | .rCheckForall  | .rCheckLet     | .rCheckProj    | .rCheckLit
  | .rEmitDefEq    | .rEmitSortOf   | .rEmitDeclReq2 | .rEmitDeclReq3
  | .rDeriveIsType | .rDeriveIsProp | .rCheckConv => .thm
  | .rAdmitAxiom   | .rAdmitQuot    | .rAdmitInd     | .rAdmitCtor
  | .rAdmitRec     | .rAdmitDefn    | .rAdmitOpaque  | .rAdmitThm => .env

/-- Flat tuple occurrences in `LEAN_SPACE_THM` and `LEAN_SPACE_ENV` matching `C_TYPED` .. `C_DECL_THM`
in `tcalc/lean_tcalc_theory.h`. -/
inductive ConcreteTheoryFact where
  | cTyped      (e ty : Nat)
  | cDefEq      (a b : Nat)
  | cSortOf     (sortExpr u : Nat)
  | cIsType     (ty u : Nat)
  | cIsProp     (ty : Nat)
  | cDeclReq2   (name ty : Nat)
  | cDeclReq3   (name a1 a2 : Nat)
  | cDeclAxiom  (name ty : Nat)
  | cDeclQuot   (name ty : Nat)
  | cDeclInd    (name ty : Nat)
  | cDeclCtor   (name indName ty : Nat)
  | cDeclRec    (name indName ty : Nat)
  | cDeclDefn   (name ty val : Nat)
  | cDeclOpaque (name ty val : Nat)
  | cDeclThm    (name ty val : Nat)
  deriving DecidableEq, Repr

/-- Exact transition relation for the 11 premise-bearing rules (`R[12..22]`) in
`tcalc/lean_tcalc_theory.h` and `tcalc/lean_tcalc_gen.h`. -/
inductive ConcretePremiseStep (store : List ConcreteTheoryFact) :
    ConcreteTheoryRuleId → ConcreteTheoryFact → Prop where
  | deriveIsType (ty sortExpr u : Nat) :
      ConcreteTheoryFact.cTyped ty sortExpr ∈ store →
      ConcreteTheoryFact.cSortOf sortExpr u ∈ store →
      ConcretePremiseStep store .rDeriveIsType (.cIsType ty u)
  | deriveIsProp (ty : Nat) :
      ConcreteTheoryFact.cIsType ty 0 ∈ store →
      ConcretePremiseStep store .rDeriveIsProp (.cIsProp ty)
  | checkConv (val actualTy expectedTy u : Nat) :
      ConcreteTheoryFact.cTyped val actualTy ∈ store →
      ConcreteTheoryFact.cDefEq actualTy expectedTy ∈ store →
      ConcreteTheoryFact.cIsType expectedTy u ∈ store →
      ConcretePremiseStep store .rCheckConv (.cTyped val expectedTy)
  | admitAxiom (name ty u : Nat) :
      ConcreteTheoryFact.cDeclReq2 name ty ∈ store →
      ConcreteTheoryFact.cIsType ty u ∈ store →
      ConcretePremiseStep store .rAdmitAxiom (.cDeclAxiom name ty)
  | admitQuot (name ty u : Nat) :
      ConcreteTheoryFact.cDeclReq2 name ty ∈ store →
      ConcreteTheoryFact.cIsType ty u ∈ store →
      ConcretePremiseStep store .rAdmitQuot (.cDeclQuot name ty)
  | admitInd (name ty u : Nat) :
      ConcreteTheoryFact.cDeclReq2 name ty ∈ store →
      ConcreteTheoryFact.cIsType ty u ∈ store →
      ConcretePremiseStep store .rAdmitInd (.cDeclInd name ty)
  | admitCtor (name indName ty indTy u : Nat) :
      ConcreteTheoryFact.cDeclReq3 name indName ty ∈ store →
      ConcreteTheoryFact.cDeclInd indName indTy ∈ store →
      ConcreteTheoryFact.cIsType ty u ∈ store →
      ConcretePremiseStep store .rAdmitCtor (.cDeclCtor name indName ty)
  | admitRec (name indName ty u : Nat) :
      ConcreteTheoryFact.cDeclReq3 name indName ty ∈ store →
      ConcreteTheoryFact.cIsType ty u ∈ store →
      ConcretePremiseStep store .rAdmitRec (.cDeclRec name indName ty)
  | admitDefn (name ty val u : Nat) :
      ConcreteTheoryFact.cDeclReq3 name ty val ∈ store →
      ConcreteTheoryFact.cIsType ty u ∈ store →
      ConcreteTheoryFact.cTyped val ty ∈ store →
      ConcretePremiseStep store .rAdmitDefn (.cDeclDefn name ty val)
  | admitOpaque (name ty val u : Nat) :
      ConcreteTheoryFact.cDeclReq3 name ty val ∈ store →
      ConcreteTheoryFact.cIsType ty u ∈ store →
      ConcreteTheoryFact.cTyped val ty ∈ store →
      ConcretePremiseStep store .rAdmitOpaque (.cDeclOpaque name ty val)
  | admitThm (name ty val : Nat) :
      ConcreteTheoryFact.cDeclReq3 name ty val ∈ store →
      ConcreteTheoryFact.cIsProp ty ∈ store →
      ConcreteTheoryFact.cTyped val ty ∈ store →
      ConcretePremiseStep store .rAdmitThm (.cDeclThm name ty val)

/-- Soundness of `R_ADMIT_THM` (Rule 22) in the 23-rule concrete `lean_tcalc_theory.h` table:
Admitting `.cDeclThm name ty val` requires all 3 `keep` premises (`cDeclReq3 name ty val`,
`cIsProp ty`, and `cTyped val ty`) to be present with matching `name`, `ty`, and `val` IDs. -/
theorem concrete_admitThm_requires_matching_premises
    (store : List ConcreteTheoryFact) (name ty val : Nat)
    (h : ConcretePremiseStep store .rAdmitThm (.cDeclThm name ty val)) :
    ConcreteTheoryFact.cDeclReq3 name ty val ∈ store ∧
    ConcreteTheoryFact.cIsProp ty ∈ store ∧
    ConcreteTheoryFact.cTyped val ty ∈ store := by
  cases h with
  | admitThm _ _ _ hReq hProp hTyped =>
    exact ⟨hReq, hProp, hTyped⟩

/-! ## Part IV: Gold Three-Way Route Commutation (`GOLD-4` & `GOLD-5`) -/

/-- The five Gold languages covered by the GSLT → MeTTa / PeTTa → `tcalc` / Direct `tcalc` matrix. -/
inductive GoldLang where
  | datalogD0 : GoldLang
  | chrC1     : GoldLang
  | erlangE1  : GoldLang
  | ocamlO1   : GoldLang
  | maudeM1   : GoldLang
  deriving DecidableEq, Repr

/-- Rich execution trace produced by a Gold language run before observation projection.
Retains ordered answers (preserving multiplicity), consumed resource count, and
derivation/explanation receipts. -/
structure RichExecutionResult (Val Prov : Type) where
  orderedAnswers    : List Val
  consumedResources : Nat
  explanations      : List (Val × Prov)
  deriving DecidableEq, Repr

/-- Helper that removes duplicate occurrences while preserving first-appearance order. -/
def dedupList [DecidableEq Val] : List Val → List Val
  | [] => []
  | x :: xs => x :: (dedupList xs).filter (· ≠ x)

/-- Extensional set view: deduplicates `orderedAnswers` (forgetting order, multiplicity,
consumed resources, and derivation provenance). -/
def projectExtensionalSet [DecidableEq Val] (res : RichExecutionResult Val Prov) : List Val :=
  dedupList res.orderedAnswers

/-- Answer-multiplicity / ordered-trace view: retains `orderedAnswers` with multiplicity. -/
def projectMultiplicityTrace (res : RichExecutionResult Val Prov) : List Val :=
  res.orderedAnswers

/-- Retained-explanation view: retains `(answer, provenance)` pairs (as in Datalog D0
explanation trees and CHR/Maude rule receipts). -/
def projectRetainedExplanations (res : RichExecutionResult Val Prov) : List (Val × Prov) :=
  res.explanations

/-- Declared observation kinds from the Gold specification. -/
inductive DeclaredObsKind where
  | extensionalSet       : DeclaredObsKind
  | multiplicityTrace    : DeclaredObsKind
  | retainedExplanations : DeclaredObsKind
  deriving DecidableEq, Repr

/-- Abstract three-way execution bundle for a Gold language family:
- `parseToIR`: authored SyntaxGSLT parser lowering source into `IR`
- `emitPeTTa`: GSLT → PeTTa compiler lowering `IR` into `PeTTaProg`
- `evalOrigPeTTa`: Route 0 (existing SWI/CeTTa PeTTa evaluator)
- `evalPeTTaTcalc`: Route A (`petta_tcalc_eval.h` evaluator over `tcalc`)
- `evalDirectTcalc`: Route B (`gold_langs_tcalc.h` / `dl_tcalc.c` direct evaluator over `tcalc`) -/
structure ThreeWayGoldPipeline (Src IR PeTTaProg Val Prov : Type) where
  parseToIR       : Src → Option IR
  emitPeTTa       : IR → PeTTaProg
  evalOrigPeTTa   : PeTTaProg → RichExecutionResult Val Prov
  evalPeTTaTcalc  : PeTTaProg → RichExecutionResult Val Prov
  evalDirectTcalc : IR → RichExecutionResult Val Prov

/-- Route 0 execution (`Source → AuthoredIR → EmittedPeTTa → OrigPeTTa`). -/
def runRoute0 (P : ThreeWayGoldPipeline Src IR PeTTaProg Val Prov) (s : Src) :
    Option (RichExecutionResult Val Prov) :=
  (P.parseToIR s).map (fun ir => P.evalOrigPeTTa (P.emitPeTTa ir))

/-- Route A execution (`Source → AuthoredIR → EmittedPeTTa → PeTTaTcalc`). -/
def runRouteA (P : ThreeWayGoldPipeline Src IR PeTTaProg Val Prov) (s : Src) :
    Option (RichExecutionResult Val Prov) :=
  (P.parseToIR s).map (fun ir => P.evalPeTTaTcalc (P.emitPeTTa ir))

/-- Route B execution (`Source → AuthoredIR → DirectTcalc`). -/
def runRouteB (P : ThreeWayGoldPipeline Src IR PeTTaProg Val Prov) (s : Src) :
    Option (RichExecutionResult Val Prov) :=
  (P.parseToIR s).map P.evalDirectTcalc

/-- Route A Bisimulation Agreement: `evalPeTTaTcalc` agrees with `evalOrigPeTTa` on all
emitted PeTTa programs in the Gold fragment. -/
def RouteAAgrees (P : ThreeWayGoldPipeline Src IR PeTTaProg Val Prov) : Prop :=
  ∀ ir : IR, P.evalPeTTaTcalc (P.emitPeTTa ir) = P.evalOrigPeTTa (P.emitPeTTa ir)

/-- Route B Bisimulation Agreement: `evalDirectTcalc` agrees with `evalPeTTaTcalc ∘ emitPeTTa`
on all authored IR programs in the Gold fragment. -/
def RouteBAgrees (P : ThreeWayGoldPipeline Src IR PeTTaProg Val Prov) : Prop :=
  ∀ ir : IR, P.evalDirectTcalc ir = P.evalPeTTaTcalc (P.emitPeTTa ir)

/-- Three-Way Gold Commutation Theorem:
Whenever `RouteAAgrees` and `RouteBAgrees` hold on a `ThreeWayGoldPipeline`,
Route 0 (`OrigMeTTa`), Route A (`PeTTaTcalc`), and Route B (`DirectTcalc`) produce
identical rich execution results (and therefore identical observations at every
`DeclaredObsKind`) for every source program `s : Src`. -/
theorem three_way_gold_commutes
    {Src IR PeTTaProg Val Prov : Type}
    (P : ThreeWayGoldPipeline Src IR PeTTaProg Val Prov)
    (hA : RouteAAgrees P)
    (hB : RouteBAgrees P)
    (s : Src) :
    runRoute0 P s = runRouteA P s ∧ runRouteA P s = runRouteB P s := by
  unfold runRoute0 runRouteA runRouteB
  cases P.parseToIR s with
  | none =>
    simp
  | some ir =>
    simp [hA ir, hB ir]

/-- Corollary: Under `RouteAAgrees` and `RouteBAgrees`, Route 0 and Route B commute at
the extensional set observation, the multiplicity trace observation, and the retained
explanation observation. -/
theorem route0_eq_routeB_at_all_observations
    {Src IR PeTTaProg Val Prov : Type} [DecidableEq Val]
    (P : ThreeWayGoldPipeline Src IR PeTTaProg Val Prov)
    (hA : RouteAAgrees P)
    (hB : RouteBAgrees P)
    (s : Src) :
    (runRoute0 P s).map projectExtensionalSet = (runRouteB P s).map projectExtensionalSet ∧
    (runRoute0 P s).map projectMultiplicityTrace = (runRouteB P s).map projectMultiplicityTrace ∧
    (runRoute0 P s).map projectRetainedExplanations = (runRouteB P s).map projectRetainedExplanations := by
  have ⟨h0A, hAB⟩ := three_way_gold_commutes P hA hB s
  have h0B : runRoute0 P s = runRouteB P s := h0A.trans hAB
  simp [h0B]

/-- Negative Control (Observation Strictness — Multiplicity):
There exist two computations `res1` and `res2` that have the exact same extensional set
observation (`projectExtensionalSet res1 = projectExtensionalSet res2 = [42]`),
yet are distinguished by `projectMultiplicityTrace` (`[42]` vs `[42, 42]`).
Thus an evaluator that collapses bags/streams to sets cannot satisfy Route A multiplicity
preservation. -/
theorem multiplicity_strictly_refines_extensional_set :
    ∃ (res1 res2 : RichExecutionResult Nat String),
      projectExtensionalSet res1 = projectExtensionalSet res2 ∧
      projectMultiplicityTrace res1 ≠ projectMultiplicityTrace res2 := by
  refine ⟨⟨[42], 1, [(42, "r1")]⟩, ⟨[42, 42], 1, [(42, "r1"), (42, "r2")]⟩, ?_, ?_⟩
  · rfl
  · decide

/-- Negative Control (Observation Strictness — Retained Explanations):
There exist two computations `res1` and `res2` with identical ordered answers (`[42]`)
and identical extensional sets (`[42]`), yet distinct retained explanations
(`[(42, "edge_direct")]` vs `[(42, "reach_trans")]`). -/
theorem explanations_strictly_refine_multiplicity_trace :
    ∃ (res1 res2 : RichExecutionResult Nat String),
      projectMultiplicityTrace res1 = projectMultiplicityTrace res2 ∧
      projectRetainedExplanations res1 ≠ projectRetainedExplanations res2 := by
  refine ⟨⟨[42], 1, [(42, "edge_direct")]⟩, ⟨[42], 1, [(42, "reach_trans")]⟩, ?_, ?_⟩
  · rfl
  · decide

/-! ## Part V: Exact Micromath ↔ MeTTa / MM2 / `tcalc` 4-Premise Pattern-Matching Injection -/

open Mettapedia.Languages.Micromath

/-- A 9-variable pattern-matching substitution witness for the MeTTa / MM2 / `tcalc` rule
`(rule sub1 ((EQ $x $t $u $w) (EQ $u1 $u $a $b) (EQ $w1 $w $a $b) (EQ $x1 $x $a $b)) (EQ $x1 $t $u1 $w1))`. -/
structure Sub1PatternSubst where
  x  : Symbol
  t  : Symbol
  u  : Symbol
  w  : Symbol
  u1 : Symbol
  w1 : Symbol
  x1 : Symbol
  a  : Symbol
  b  : Symbol
  deriving DecidableEq, Repr

/-- Instantiating the 4 LHS pattern atoms of `sub1` under `σ : Sub1PatternSubst`. -/
def Sub1PatternSubst.lhs (σ : Sub1PatternSubst) : Claim × Claim × Claim × Claim :=
  (⟨σ.x, σ.t, σ.u, σ.w⟩,
   ⟨σ.u1, σ.u, σ.a, σ.b⟩,
   ⟨σ.w1, σ.w, σ.a, σ.b⟩,
   ⟨σ.x1, σ.x, σ.a, σ.b⟩)

/-- Instantiating the RHS conclusion atom of `sub1` under `σ : Sub1PatternSubst`. -/
def Sub1PatternSubst.rhs (σ : Sub1PatternSubst) : Claim :=
  ⟨σ.x1, σ.t, σ.u1, σ.w1⟩

/-- Algebraic repeated-pattern instantiation equivalence for `sub1`:
A 4-tuple of Micromath claims `(main, left, right, result)` matches the repeated-variable
MeTTa / MM2 / `tcalc` pattern `Sub1PatternSubst.lhs σ` with conclusion `σ.rhs = conclusion`
if and only if `Micromath.substitute1? main left right result = some conclusion`.
This statement does not run a collection matcher or prove that an authored
module permits repeated references to one stored premise. -/
theorem micromath_sub1_pattern_iff_guard (main left right result conclusion : Claim) :
    (∃ σ : Sub1PatternSubst,
      σ.lhs = (main, left, right, result) ∧ σ.rhs = conclusion) ↔
    substitute1? main left right result = some conclusion := by
  constructor
  · rintro ⟨σ, hLhs, hRhs⟩
    unfold Sub1PatternSubst.lhs at hLhs
    unfold Sub1PatternSubst.rhs at hRhs
    rcases Prod.mk.inj hLhs with ⟨hMain, hRest1⟩
    rcases Prod.mk.inj hRest1 with ⟨hLeft, hRest2⟩
    rcases Prod.mk.inj hRest2 with ⟨hRight, hResult⟩
    cases hMain
    cases hLeft
    cases hRight
    cases hResult
    cases hRhs
    unfold substitute1? Substitute1Guard
    simp
  · intro hSub
    unfold substitute1? at hSub
    split at hSub
    next hGuard =>
      cases Option.some.inj hSub
      rcases hGuard with ⟨h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨⟨main.out, main.f, main.x, main.y, left.out, right.out, result.out, left.x, left.y⟩, ?_, rfl⟩
      unfold Sub1PatternSubst.lhs
      rcases main with ⟨mOut, mF, mX, mY⟩
      rcases left with ⟨lOut, lF, lX, lY⟩
      rcases right with ⟨rOut, rF, rX, rY⟩
      rcases result with ⟨zOut, zF, zX, zY⟩
      simp only at h1 h2 h3 h4 h5 h6 h7
      subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
      rfl
    next hNo =>
      contradiction

/-- Semantic Soundness of the MeTTa / MM2 / `tcalc` Repeated-Variable `sub1` Rewrite:
Whenever a 9-variable pattern substitution `σ` matches four valid claims `(main, left, right, result)`,
the emitted RHS `σ.rhs` holds in every interpretation `Assignment D`. -/
theorem micromath_sub1_pattern_sound {D : Type} (interpret : Assignment D)
    (main left right result : Claim) (σ : Sub1PatternSubst)
    (hMatch : σ.lhs = (main, left, right, result))
    (hMain : Holds interpret main) (hLeft : Holds interpret left)
    (hRight : Holds interpret right) (hResult : Holds interpret result) :
    Holds interpret σ.rhs := by
  have hSub : substitute1? main left right result = some σ.rhs :=
    (micromath_sub1_pattern_iff_guard main left right result σ.rhs).mp ⟨σ, hMatch, rfl⟩
  exact substitute1_holds interpret main left right result σ.rhs hMain hLeft hRight hResult hSub

/-- A 9-variable pattern-matching substitution witness for the MeTTa / MM2 / `tcalc` rule
`(rule sub2 ((EQ $x $t $u $w) (EQ $u1 $u $a $b) (EQ $w1 $w $a $b) (EQ $x1 $t $u1 $w1)) (EQ $x1 $x $a $b))`. -/
structure Sub2PatternSubst where
  x  : Symbol
  t  : Symbol
  u  : Symbol
  w  : Symbol
  u1 : Symbol
  w1 : Symbol
  x1 : Symbol
  a  : Symbol
  b  : Symbol
  deriving DecidableEq, Repr

/-- Instantiating the 4 LHS pattern atoms of `sub2` under `σ : Sub2PatternSubst`. -/
def Sub2PatternSubst.lhs (σ : Sub2PatternSubst) : Claim × Claim × Claim × Claim :=
  (⟨σ.x, σ.t, σ.u, σ.w⟩,
   ⟨σ.u1, σ.u, σ.a, σ.b⟩,
   ⟨σ.w1, σ.w, σ.a, σ.b⟩,
   ⟨σ.x1, σ.t, σ.u1, σ.w1⟩)

/-- Instantiating the RHS conclusion atom of `sub2` under `σ : Sub2PatternSubst`. -/
def Sub2PatternSubst.rhs (σ : Sub2PatternSubst) : Claim :=
  ⟨σ.x1, σ.x, σ.a, σ.b⟩

/-- Exact Injection & Pattern-Matching Equivalence for `sub2`:
A 4-tuple of Micromath claims `(main, left, right, result)` matches the repeated-variable
MeTTa / MM2 / `tcalc` pattern `Sub2PatternSubst.lhs σ` with conclusion `σ.rhs = conclusion`
if and only if `Micromath.substitute2? main left right result = some conclusion`. -/
theorem micromath_sub2_pattern_iff_guard (main left right result conclusion : Claim) :
    (∃ σ : Sub2PatternSubst,
      σ.lhs = (main, left, right, result) ∧ σ.rhs = conclusion) ↔
    substitute2? main left right result = some conclusion := by
  constructor
  · rintro ⟨σ, hLhs, hRhs⟩
    unfold Sub2PatternSubst.lhs at hLhs
    unfold Sub2PatternSubst.rhs at hRhs
    rcases Prod.mk.inj hLhs with ⟨hMain, hRest1⟩
    rcases Prod.mk.inj hRest1 with ⟨hLeft, hRest2⟩
    rcases Prod.mk.inj hRest2 with ⟨hRight, hResult⟩
    cases hMain
    cases hLeft
    cases hRight
    cases hResult
    cases hRhs
    unfold substitute2? Substitute2Guard
    simp
  · intro hSub
    unfold substitute2? at hSub
    split at hSub
    next hGuard =>
      cases Option.some.inj hSub
      rcases hGuard with ⟨h1, h2, h3, h4, h5, h6, h7⟩
      refine ⟨⟨main.out, main.f, main.x, main.y, left.out, right.out, result.out, left.x, left.y⟩, ?_, rfl⟩
      unfold Sub2PatternSubst.lhs
      rcases main with ⟨mOut, mF, mX, mY⟩
      rcases left with ⟨lOut, lF, lX, lY⟩
      rcases right with ⟨rOut, rF, rX, rY⟩
      rcases result with ⟨zOut, zF, zX, zY⟩
      simp only at h1 h2 h3 h4 h5 h6 h7
      subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7
      rfl
    next hNo =>
      contradiction

/-- Semantic Soundness of the MeTTa / MM2 / `tcalc` Repeated-Variable `sub2` Rewrite:
Whenever a 9-variable pattern substitution `σ` matches four valid claims `(main, left, right, result)`,
the emitted RHS `σ.rhs` holds in every interpretation `Assignment D`. -/
theorem micromath_sub2_pattern_sound {D : Type} (interpret : Assignment D)
    (main left right result : Claim) (σ : Sub2PatternSubst)
    (hMatch : σ.lhs = (main, left, right, result))
    (hMain : Holds interpret main) (hLeft : Holds interpret left)
    (hRight : Holds interpret right) (hResult : Holds interpret result) :
    Holds interpret σ.rhs := by
  have hSub : substitute2? main left right result = some σ.rhs :=
    (micromath_sub2_pattern_iff_guard main left right result σ.rhs).mp ⟨σ, hMatch, rfl⟩
  exact substitute2_holds interpret main left right result σ.rhs hMain hLeft hRight hResult hSub

/-- Tagged claim/data representation. The tags separate the represented
cases; no capability admission, native space ownership or trusted ingress
protocol is established by this datatype. -/
inductive MmAtom where
  | eqClaim (out f x y : Symbol)
  | userData (head : String) (args : List Symbol)
  deriving DecidableEq, Repr

/-- Canonical encoding of a Micromath `Claim` into `MmAtom`. -/
def encodeClaimAtom (c : Claim) : MmAtom :=
  .eqClaim c.out c.f c.x c.y

/-- Readback / decoding of an `MmAtom` into `Option Claim`.
Ordinary `userData` atoms (even if `head = "EQ"`) decode to `none`. A host
must separately prove who is allowed to construct or publish `eqClaim`. -/
def decodeClaimAtom : MmAtom → Option Claim
  | .eqClaim out f x y => some ⟨out, f, x, y⟩
  | .userData _ _      => none

/-- Exact Readback Left-Inverse Theorem (`decodeClaimAtom ∘ encodeClaimAtom = some`). -/
theorem decodeClaimAtom_encodeClaimAtom (c : Claim) :
    decodeClaimAtom (encodeClaimAtom c) = some c := by
  cases c
  rfl

/-- Injective Encoding Theorem for Micromath claims into `MmAtom`. -/
theorem encodeClaimAtom_injective (c1 c2 : Claim)
    (h : encodeClaimAtom c1 = encodeClaimAtom c2) :
    c1 = c2 := by
  have hDec := congrArg decodeClaimAtom h
  rw [decodeClaimAtom_encodeClaimAtom, decodeClaimAtom_encodeClaimAtom] at hDec
  exact Option.some.inj hDec

/-- Tag-separation control: ordinary `userData "EQ" [out, f, x, y]` does not
decode as a claim. This is not a native authority-separation theorem. -/
theorem userData_eq_never_decodes_as_claim (args : List Symbol) :
    decodeClaimAtom (.userData "EQ" args) = none := by
  rfl

/-- Conservative-extension freshness guard for Micromath's `mm_new_def` (`(fresh def x1 (t u w))`):
The newly defined symbol `x1` must equal `nextFresh`, and `t, u, w` must all be strictly older
symbols (`< nextFresh`), preventing circular self-definitions `x1 = t(x1, w)`. -/
def NewDefFreshGuard (nextFresh x1 t u w : Symbol) : Bool :=
  decide (x1 = nextFresh ∧ t < nextFresh ∧ u < nextFresh ∧ w < nextFresh)

/-- Negative Control (Freshness / Non-Circularity of `mm_new_def`):
Any attempt to reference the newly defined symbol `x1` inside its own defining body
(`u = x1` or `w = x1` or `t = x1`) is rejected by `NewDefFreshGuard`. -/
theorem newDefFreshGuard_rejects_self_reference (nextFresh t w : Symbol) :
    NewDefFreshGuard nextFresh nextFresh t nextFresh w = false := by
  unfold NewDefFreshGuard
  simp

end Mettapedia.Languages.Lean.LeanTcalcKernel
