import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchReading
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetEliminators
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Square

/-!
# The values of the object package's constants in the set tower

The object package (`objectRules`, annotated by `objectChurch`) is read in the tower of closed
universes seeded with the natural numbers `ω` (`objHeads`), relative to the hypothesis
`CofinalInaccessibles`, which stays a parameter. The seed matters: the least closed universe
around the empty set lies inside the hereditarily finite sets, so it cannot hold `ω`
(`TowerInterpretation.omega_not_mem_univOf_empty`), while every level of the seeded tower holds
`ω` and the hereditarily finite sets `V_ω`.

**The values** (`ObjConst.setRaw`), constant by constant, following the stages of the domain
reading (`ObjConst.stage`):

* `num` is `ω`, `zero` is `∅` and `suc` the traced graph of the successor of numerals;
* `set` is `V_ω` and `Power` the traced graph of the power set, so nothing about the sets is
  degenerate; the declared types and rules ask only for a member of the lowest universe closed
  under an operation, and the reading gives the actual power set;
* `prop` is the set of truth values `Ω = 𝒫 {∅}`; `holds` is the identity on `Ω`, `imp`
  implication of truth values, `all@A` the truth value of quantification over the set of the
  simple type `A` (`simpleSet`), and `eq@A` the truth value of equality;
* `num-rec` is the traced graph of recursion on the naturals into the motive's values
  (`TowerInterpretation.numRecValue`), identity elimination the traced graph returning the
  method (`TowerInterpretation.jValue`);
* addition, the iterated power set (`powIter`) and the iterator (`iterPair`) are traced graphs
  of recursion on the naturals;
* the definitions by one equation are the abstractions of their elaborated right sides over
  their telescopes (`defSetRaw`), read in the values of the earlier stages.

The values are built stage by stage (`setValUpTo`), and the result is a fixed point
(`objectSetConsts_const`): every constant has its value in the values of all constants.

**Every declared constant's value lies in the value of its declared type**
(`objectSetConsts_typed`): the constants of the package, at every simple type for the
quantifiers and equations.
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
open Presentation.TypedEquality.Impredicative.Domain (termConsts lamsCtx pisCtx)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetDependentProducts (graph sigmaSet mem_sigmaSet)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open FormationSensitiveHOLInterface (typeAt)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName numT U0 eqAtTelescope transportTelescope composeTelescope)
open Mettapedia.Logic
open Mettapedia.SetTheory

universe u

namespace CodeModel

/-! ## The heads -/

/-- **The heads of the object package's set model**: level `k` is the `k`-th closed universe
of the tower seeded with the natural numbers. -/
noncomputable abbrev objHeads (h : CofinalInaccessibles.{u}) : Tower.Head → ZFSet.{u} :=
  interpretHead h ZFSet.omega ∅ (fun _ => 0)

/-- The lowest universe of the seeded tower. -/
noncomputable abbrev lowest (h : CofinalInaccessibles.{u}) : ZFSet.{u} :=
  universeSet h ZFSet.omega 0

theorem omega_mem_level (h : CofinalInaccessibles.{u}) (k : Nat) :
    ZFSet.omega.{u} ∈ universeSet h ZFSet.omega k :=
  seed_mem_universeSet h _ k

theorem finiteSets_mem_level (h : CofinalInaccessibles.{u}) (k : Nat) :
    finiteSets.{u} ∈ universeSet h ZFSet.omega k :=
  finiteSets_mem (universeSet_closed h _ k) (omega_mem_level h k)

theorem truthValues_mem_level (h : CofinalInaccessibles.{u}) (k : Nat) :
    Square.omega.{u} ∈ universeSet h ZFSet.omega k :=
  (universeSet_closed h _ k).power_mem ((universeSet_closed h _ k).singleton_mem
    ((universeSet_closed h _ k).empty_mem (seed_mem_universeSet h _ k)))

theorem empty_mem_level (h : CofinalInaccessibles.{u}) (k : Nat) :
    (∅ : ZFSet.{u}) ∈ universeSet h ZFSet.omega k :=
  (universeSet_closed h _ k).empty_mem (seed_mem_universeSet h _ k)

/-- A truth value lies in every level. -/
theorem truthCode_mem_level (h : CofinalInaccessibles.{u}) (k : Nat) (P : Prop) :
    truthCode P ∈ universeSet h ZFSet.omega k :=
  ZFSetTraceUniverseInterpretation.truthCode_mem h _ k P

/-! ## Simple types, the iterated power set and the iterator -/

/-- **The set of a simple type**: truth values at `prop`, the naturals at `num`, the
hereditarily finite sets at `set`, and trace functions at a function type. -/
noncomputable def simpleSet : HOL.Ty SetProfile.SetBase → ZFSet.{u}
  | .prop => Square.omega
  | .base .num => ZFSet.omega
  | .base .set => finiteSets
  | .arr a b => tracePiSet (simpleSet a) fun _ => simpleSet b

/-- A simple type, annotated, denotes its set when `prop`, `num` and `set` are read as truth
values, naturals and hereditarily finite sets. -/
theorem ev_typeAt {heads : Tower.Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
    (hprop : consts propN = Square.omega) (hnum : consts numN = ZFSet.omega)
    (hset : consts setN = finiteSets) :
    ∀ (type : HOL.Ty SetProfile.SetBase) {n : Nat} (ρ : Env.{u} n),
      ev heads consts (liftTm (typeAt SetProfile.types n type)) ρ = simpleSet type
  | .prop, _, _ => hprop
  | .base .num, _, _ => hnum
  | .base .set, _, _ => hset
  | .arr a b, n, ρ => by
      show tracePiSet (ev heads consts (liftTm (typeAt SetProfile.types n a)) ρ)
          (fun x => ev heads consts (liftTm (typeAt SetProfile.types (n + 1) b))
            (extend ρ x)) = tracePiSet (simpleSet a) fun _ => simpleSet b
      rw [ev_typeAt hprop hnum hset a ρ]
      congr 1
      funext x
      exact ev_typeAt hprop hnum hset b (extend ρ x)

/-- The iterated power set: `𝒫ᵏ X`. -/
noncomputable def powIter (X : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => X
  | k + 1 => ZFSet.powerset (powIter X k)

theorem powIter_mem {X : ZFSet.{u}} (hX : X ∈ finiteSets) : ∀ k, powIter X k ∈ finiteSets
  | 0 => hX
  | k + 1 => powerset_mem_finiteSets (powIter_mem hX k)

/-- The iterator's recursion: `k` uses of the step, each at the components of the last
pair. -/
noncomputable def iterPair (step : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u}
  | 0, p => p
  | k + 1, p => iterPair step k
      (traceApp (traceApp step (ZFSetOrderedPair.first p)) (ZFSetOrderedPair.second p))

/-- The steps `Π (x : A). P x → Σ (y : A). P y` over a carrier and a family. -/
noncomputable def stepSet (A P : ZFSet.{u}) : ZFSet.{u} :=
  tracePiSet A fun x => tracePiSet (traceApp P x) fun _ => sigmaSet A fun y => traceApp P y

/-- One use of a step keeps a pair in `Σ (y : A). P y`. -/
theorem step_mem {A P step p : ZFSet.{u}} (hstep : step ∈ stepSet A P)
    (hp : p ∈ sigmaSet A fun y => traceApp P y) :
    traceApp (traceApp step (ZFSetOrderedPair.first p)) (ZFSetOrderedPair.second p) ∈
      sigmaSet A fun y => traceApp P y := by
  have atFirst := traceApp_mem_fibre hstep (first_mem_sigmaSet hp)
  exact traceApp_mem_fibre atFirst (second_mem_sigmaSet hp)

/-- **The iterator keeps a pair in `Σ (y : A). P y`.** -/
theorem iterPair_mem {A P step : ZFSet.{u}} (hstep : step ∈ stepSet A P) :
    ∀ (k : ℕ) {p : ZFSet.{u}}, p ∈ (sigmaSet A fun y => traceApp P y) →
      iterPair step k p ∈ sigmaSet A fun y => traceApp P y
  | 0, _, hp => hp
  | k + 1, _, hp => iterPair_mem hstep k (step_mem hstep hp)

/-- A member of a dependent pair set is the pair of its projections. -/
theorem pair_first_second {A p : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} (hp : p ∈ sigmaSet A B) :
    ZFSet.pair (ZFSetOrderedPair.first p) (ZFSetOrderedPair.second p) = p := by
  obtain ⟨x, _, y, _, rfl⟩ := mem_sigmaSet.mp hp
  rw [ZFSetOrderedPair.first_pair, ZFSetOrderedPair.second_pair]

/-! ## The telescopes of the declared types -/

/-- `n : num`. -/
abbrev numTele : CCtx Tower.Head 1 := .snoc .nil cnum
/-- `n m : num`. -/
abbrev numNumTele : CCtx Tower.Head 2 := .snoc numTele cnum
/-- `X : set`. -/
abbrev setTele : CCtx Tower.Head 1 := .snoc .nil cset
/-- `n : num, X : set`. -/
abbrev numSetTele : CCtx Tower.Head 2 := .snoc numTele cset
/-- `p : prop`. -/
abbrev propTele : CCtx Tower.Head 1 := .snoc .nil (.const propN)
/-- `p q : prop`. -/
abbrev propPropTele : CCtx Tower.Head 2 := .snoc propTele (.const propN)

/-- `f : A → prop`, the telescope of the quantifier `all@A`. -/
abbrev allTele (type : HOL.Ty SetProfile.SetBase) : CCtx Tower.Head 1 :=
  .snoc .nil (liftTm (typeAt SetProfile.types 0 (.arr type .prop)))

/-- `x y : A`, the telescope of the equation `eq@A`. -/
abbrev eqTele (type : HOL.Ty SetProfile.SetBase) : CCtx Tower.Head 2 :=
  .snoc (.snoc .nil (liftTm (typeAt SetProfile.types 0 type)))
    (liftTm (typeAt SetProfile.types 1 type))

/-- The iterator's result `Σ (y : A). P y`, over its telescope `cIterSucTele`. -/
abbrev iterResult : CTm Tower.Head 6 := .sigma (.var 4) (.app (.var 4) (.var 0))

/-! ## The values -/

/-- The value of a definition by one equation: its elaborated right side abstracted over its
annotated telescope. -/
noncomputable def defSetRaw (heads : Tower.Head → ZFSet.{u}) (consts : DeclName → ZFSet.{u})
    (f : DeclName) {k : Nat} (Θ : Tower.Ctx k) (rhs : Tower.Tm k) : ZFSet.{u} :=
  ev heads consts (lamsCtx (liftCtx Θ) (defRhs f Θ rhs)) Fin.elim0

/-- **The value of each constant**, given the values of the constants of earlier stages. -/
noncomputable def ObjConst.setRaw (heads : Tower.Head → ZFSet.{u})
    (consts : DeclName → ZFSet.{u}) : ObjConst → ZFSet.{u}
  | .num => ZFSet.omega
  | .set => finiteSets
  | .prop => Square.omega
  | .zero => numeral 0
  | .suc => telescopeGraph heads consts numTele fun η => insert (η 0) (η 0)
  | .add => telescopeGraph heads consts numNumTele fun η =>
      numeral (natOf (η 1) + natOf (η 0))
  | .power => telescopeGraph heads consts setTele fun η => ZFSet.powerset (η 0)
  | .pow => telescopeGraph heads consts numSetTele fun η => powIter (η 0) (natOf (η 1))
  | .numRec => numRecValue heads consts numNames
  | .j => jValue heads consts (.sort Tower.zero)
  | .eqAt => defSetRaw heads consts eqAtName eqAtTele eqAtRhs
  | .sucMove => defSetRaw heads consts sucMoveName eqAtTelescope sucMoveRhs
  | .keep => defSetRaw heads consts keepName keepTele keepRhs
  | .transport => defSetRaw heads consts transportName transportTelescope transportRhs
  | .compose => defSetRaw heads consts composeName composeTelescope composeRhs
  | .iter => telescopeGraph heads consts cIterSucTele fun η =>
      iterPair (η 2) (natOf (η 5)) (ZFSet.pair (η 1) (η 0))
  | .returnIter => defSetRaw heads consts returnIterName returnIterTele returnIterRhs
  | .sucStep => defSetRaw heads consts sucStepName eqAtTelescope sucStepRhs
  | .holds => telescopeGraph heads consts propTele fun η => η 0
  | .imp => telescopeGraph heads consts propPropTele fun η =>
      truthCode ((∅ : ZFSet.{u}) ∈ η 1 → (∅ : ZFSet.{u}) ∈ η 0)
  | .all type => telescopeGraph heads consts (allTele type) fun η =>
      truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ traceApp (η 0) x)
  | .eq type => telescopeGraph heads consts (eqTele type) fun η => truthCode (η 1 = η 0)
  | .other => ∅

/-! ## The declared types over their telescopes -/

theorem declType_suc : ObjConst.declType .suc = pisCtx numTele cnum := rfl
theorem declType_add : ObjConst.declType .add = pisCtx numNumTele cnum := rfl
theorem declType_power : ObjConst.declType .power = pisCtx setTele cset := rfl
theorem declType_pow : ObjConst.declType .pow = pisCtx numSetTele cset := rfl
theorem declType_numRec :
    ObjConst.declType .numRec = pisCtx (nrTele numNames) (.app (.var 3) (.var 0)) := rfl
theorem declType_j :
    ObjConst.declType .j = pisCtx (jTele (.sort Tower.zero)) (.app (.app (.var 3) (.var 1)) (.var 0)) :=
  rfl
theorem declType_iter : ObjConst.declType .iter = pisCtx cIterSucTele iterResult := by decide
theorem declType_holds : ObjConst.declType .holds = pisCtx propTele cU0 := rfl
theorem declType_imp : ObjConst.declType .imp = pisCtx propPropTele (.const propN) := rfl
theorem declType_all (type : HOL.Ty SetProfile.SetBase) :
    ObjConst.declType (.all type) = pisCtx (allTele type) (.const propN) := rfl
theorem declType_eq (type : HOL.Ty SetProfile.SetBase) :
    ObjConst.declType (.eq type) = pisCtx (eqTele type) (.const propN) := rfl

/-! ## Stages -/

/-- The value of each constant reads only the constants of earlier stages. -/
theorem setRaw_congr {heads : Tower.Head → ZFSet.{u}} {consts consts' : DeclName → ZFSet.{u}}
    (tag : ObjConst) (agree : ∀ c, (objConst c).stage < tag.stage → consts c = consts' c) :
    tag.setRaw heads consts = tag.setRaw heads consts' := by
  have declared : ∀ c ∈ termConsts tag.declType, consts c = consts' c := fun c hc =>
    agree c (stagedBelow_declType tag c hc)
  have definition : ∀ {f : DeclName} {k : Nat} (Θ : Tower.Ctx k) (rhs : Tower.Tm k),
      stagedBelow tag.stage (lamsCtx (liftCtx Θ) (defRhs f Θ rhs)) = true →
        defSetRaw heads consts f Θ rhs = defSetRaw heads consts' f Θ rhs := fun Θ rhs staged =>
    ev_congr_consts heads consts _ (fun c hc => agree c (stagedBelow_spec staged c hc)) _
  cases tag with
  | suc =>
      rw [declType_suc] at declared
      show telescopeGraph heads consts numTele (fun η => insert (η 0) (η 0)) =
        telescopeGraph heads consts' numTele (fun η => insert (η 0) (η 0))
      exact telescopeGraph_congr heads consts numTele cnum declared _
  | add =>
      rw [declType_add] at declared
      show telescopeGraph heads consts numNumTele
          (fun η => numeral (natOf (η 1) + natOf (η 0))) =
        telescopeGraph heads consts' numNumTele (fun η => numeral (natOf (η 1) + natOf (η 0)))
      exact telescopeGraph_congr heads consts numNumTele cnum declared _
  | power =>
      rw [declType_power] at declared
      show telescopeGraph heads consts setTele (fun η => ZFSet.powerset (η 0)) =
        telescopeGraph heads consts' setTele (fun η => ZFSet.powerset (η 0))
      exact telescopeGraph_congr heads consts setTele cset declared _
  | pow =>
      rw [declType_pow] at declared
      show telescopeGraph heads consts numSetTele (fun η => powIter (η 0) (natOf (η 1))) =
        telescopeGraph heads consts' numSetTele (fun η => powIter (η 0) (natOf (η 1)))
      exact telescopeGraph_congr heads consts numSetTele cset declared _
  | numRec =>
      rw [declType_numRec] at declared
      show numRecValue heads consts numNames = numRecValue heads consts' numNames
      exact telescopeGraph_congr heads consts (nrTele numNames) _ declared _
  | j =>
      rw [declType_j] at declared
      show jValue heads consts (.sort Tower.zero) = jValue heads consts' (.sort Tower.zero)
      exact telescopeGraph_congr heads consts (jTele (.sort Tower.zero)) _ declared _
  | iter =>
      rw [declType_iter] at declared
      show telescopeGraph heads consts cIterSucTele
          (fun η => iterPair (η 2) (natOf (η 5)) (ZFSet.pair (η 1) (η 0))) =
        telescopeGraph heads consts' cIterSucTele
          (fun η => iterPair (η 2) (natOf (η 5)) (ZFSet.pair (η 1) (η 0)))
      exact telescopeGraph_congr heads consts cIterSucTele iterResult declared _
  | holds =>
      rw [declType_holds] at declared
      show telescopeGraph heads consts propTele (fun η => η 0) =
        telescopeGraph heads consts' propTele (fun η => η 0)
      exact telescopeGraph_congr heads consts propTele cU0 declared _
  | imp =>
      rw [declType_imp] at declared
      show telescopeGraph heads consts propPropTele
          (fun η => truthCode ((∅ : ZFSet.{u}) ∈ η 1 → (∅ : ZFSet.{u}) ∈ η 0)) =
        telescopeGraph heads consts' propPropTele
          (fun η => truthCode ((∅ : ZFSet.{u}) ∈ η 1 → (∅ : ZFSet.{u}) ∈ η 0))
      exact telescopeGraph_congr heads consts propPropTele (.const propN) declared _
  | all type =>
      rw [declType_all] at declared
      show telescopeGraph heads consts (allTele type)
          (fun η => truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ traceApp (η 0) x)) =
        telescopeGraph heads consts' (allTele type)
          (fun η => truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ traceApp (η 0) x))
      exact telescopeGraph_congr heads consts (allTele type) (.const propN) declared _
  | eq type =>
      rw [declType_eq] at declared
      show telescopeGraph heads consts (eqTele type) (fun η => truthCode (η 1 = η 0)) =
        telescopeGraph heads consts' (eqTele type) (fun η => truthCode (η 1 = η 0))
      exact telescopeGraph_congr heads consts (eqTele type) (.const propN) declared _
  | eqAt => exact definition (f := eqAtName) eqAtTele eqAtRhs (by decide)
  | sucMove => exact definition (f := sucMoveName) eqAtTelescope sucMoveRhs (by decide)
  | keep => exact definition (f := keepName) keepTele keepRhs (by decide)
  | transport => exact definition (f := transportName) transportTelescope transportRhs (by decide)
  | compose => exact definition (f := composeName) composeTelescope composeRhs (by decide)
  | returnIter => exact definition (f := returnIterName) returnIterTele returnIterRhs (by decide)
  | sucStep => exact definition (f := sucStepName) eqAtTelescope sucStepRhs (by decide)
  | num => rfl
  | set => rfl
  | prop => rfl
  | zero => rfl
  | other => rfl

/-- The values up to a stage: the constants of each stage read in the values of the stages
before. -/
noncomputable def setValUpTo (heads : Tower.Head → ZFSet.{u}) : Nat → ObjConst → ZFSet.{u}
  | 0 => ObjConst.setRaw heads fun _ => ∅
  | k + 1 => fun tag =>
      if tag.stage ≤ k then setValUpTo heads k tag
      else tag.setRaw heads fun c => setValUpTo heads k (objConst c)

/-- **The values of the object package's constants** in the seeded tower. -/
noncomputable def objectSetConsts (h : CofinalInaccessibles.{u}) (c : DeclName) : ZFSet.{u} :=
  setValUpTo (objHeads h) 5 (objConst c)

theorem setValUpTo_stable {heads : Tower.Head → ZFSet.{u}} {k : Nat} {tag : ObjConst}
    (hs : tag.stage ≤ k) : ∀ {j : Nat}, k ≤ j → setValUpTo heads j tag = setValUpTo heads k tag := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih =>
      show (if tag.stage ≤ j then setValUpTo heads j tag else _) = _
      rw [if_pos (Nat.le_trans hs hkj), ih]

/-- **The values are a fixed point**: every constant has its value in the values of all the
constants. -/
theorem objectSetConsts_const (h : CofinalInaccessibles.{u}) (c : DeclName) :
    objectSetConsts h c = (objConst c).setRaw (objHeads h) (objectSetConsts h) := by
  show setValUpTo (objHeads h) 5 (objConst c) = _
  generalize objConst c = tag
  rw [setValUpTo_stable (Nat.le_refl tag.stage) (ObjConst.stage_le tag)]
  have agreeUpTo : ∀ k, k ≤ 5 → ∀ c', (objConst c').stage ≤ k →
      setValUpTo (objHeads h) k (objConst c') = objectSetConsts h c' := fun _ hk _ hc' =>
    (setValUpTo_stable hc' hk).symm
  have h5 := ObjConst.stage_le tag
  match hs : tag.stage with
  | 0 =>
      show tag.setRaw (objHeads h) (fun _ => ∅) = _
      exact setRaw_congr tag fun c' lt => absurd (hs ▸ lt) (Nat.not_lt_zero _)
  | k + 1 =>
      show (if tag.stage ≤ k then setValUpTo (objHeads h) k tag
        else tag.setRaw (objHeads h) fun c => setValUpTo (objHeads h) k (objConst c)) = _
      rw [if_neg (by omega)]
      exact setRaw_congr tag fun c' lt => agreeUpTo k (by omega) c' (by omega)

theorem objectSetConsts_of (h : CofinalInaccessibles.{u}) {c : DeclName} {tag : ObjConst}
    (named : objConst c = tag) :
    objectSetConsts h c = tag.setRaw (objHeads h) (objectSetConsts h) :=
  named ▸ objectSetConsts_const h c


/-! ## The values of the constants -/

section Values

variable (h : CofinalInaccessibles.{u})

theorem setConst_num : objectSetConsts h numN = ZFSet.omega :=
  objectSetConsts_of h (show objConst numN = .num by decide)

theorem setConst_set : objectSetConsts h setN = finiteSets :=
  objectSetConsts_of h (show objConst setN = .set by decide)

theorem setConst_prop : objectSetConsts h propN = Square.omega :=
  objectSetConsts_of h (show objConst propN = .prop by decide)

theorem setConst_zero : objectSetConsts h zeroN = numeral 0 :=
  objectSetConsts_of h (show objConst zeroN = .zero by decide)

theorem ev_cnum {n : Nat} (ρ : Env.{u} n) :
    ev (objHeads h) (objectSetConsts h) (cnum : CTm Tower.Head n) ρ = ZFSet.omega :=
  setConst_num h

theorem ev_cset {n : Nat} (ρ : Env.{u} n) :
    ev (objHeads h) (objectSetConsts h) (cset : CTm Tower.Head n) ρ = finiteSets :=
  setConst_set h

theorem ev_cprop {n : Nat} (ρ : Env.{u} n) :
    ev (objHeads h) (objectSetConsts h) (.const propN : CTm Tower.Head n) ρ = Square.omega :=
  setConst_prop h

theorem ev_cU0 {n : Nat} (ρ : Env.{u} n) :
    ev (objHeads h) (objectSetConsts h) (cU0 : CTm Tower.Head n) ρ = lowest h :=
  rfl

/-- The simple types denote their sets. -/
theorem ev_objTypeAt (type : HOL.Ty SetProfile.SetBase) {n : Nat} (ρ : Env.{u} n) :
    ev (objHeads h) (objectSetConsts h) (liftTm (typeAt SetProfile.types n type)) ρ =
      simpleSet type :=
  ev_typeAt (setConst_prop h) (setConst_num h) (setConst_set h) type ρ

/-- The value of a definition by one equation is the traced graph of its right side's
values. -/
theorem defSetRaw_eq {heads : Tower.Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
    {f : DeclName} {k : Nat} (Θ : Tower.Ctx k) (rhs : Tower.Tm k) :
    defSetRaw heads consts f Θ rhs =
      telescopeGraph heads consts (liftCtx Θ) fun η => ev heads consts (defRhs f Θ rhs) η :=
  ev_lamsCtx heads consts (liftCtx Θ) (defRhs f Θ rhs)

/-! ### The successor, addition, the power set and the iterated power set -/

theorem suc_apply {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    traceApp (objectSetConsts h sucN) x = insert x x := by
  rw [objectSetConsts_of h (show objConst sucN = .suc by decide)]
  show traceApp (traceLam (graph (objectSetConsts h numN) fun y => insert y y)) x = insert x x
  rw [setConst_num h]
  exact traceApp_graph_beta (fun y => insert y y) hx

/-- The numbers are read as the naturals, zero as `∅` and the successor as the successor of
numerals. -/
theorem numberReading : NumberReading (objectSetConsts h) numNames where
  num := setConst_num h
  zero := setConst_zero h
  succ k := suc_apply h (numeral_mem_omega k)

theorem add_apply {a b : ZFSet.{u}} (ha : a ∈ ZFSet.omega) (hb : b ∈ ZFSet.omega) :
    traceApp (traceApp (objectSetConsts h addN) a) b = numeral (natOf a + natOf b) := by
  have ha' : a ∈ ev (objHeads h) (objectSetConsts h) (cnum : CTm Tower.Head 0) Fin.elim0 := by
    rw [ev_cnum h]
    exact ha
  have hb' : b ∈ ev (objHeads h) (objectSetConsts h) (cnum : CTm Tower.Head 1)
      (extend Fin.elim0 a) := by
    rw [ev_cnum h]
    exact hb
  have sat : Sat (objHeads h) (objectSetConsts h) numNumTele (extend (extend Fin.elim0 a) b) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, ha'⟩, hb'⟩
  have key := applyValues_telescopeGraph (objHeads h) (objectSetConsts h) numNumTele
    (fun η => numeral (natOf (η 1) + natOf (η 0))) _ sat
  rw [objectSetConsts_of h (show objConst addN = .add by decide)]
  exact key

theorem power_apply {x : ZFSet.{u}} (hx : x ∈ finiteSets) :
    traceApp (objectSetConsts h powerN) x = ZFSet.powerset x := by
  rw [objectSetConsts_of h (show objConst powerN = .power by decide)]
  show traceApp (traceLam (graph (objectSetConsts h setN) fun y => ZFSet.powerset y)) x =
    ZFSet.powerset x
  rw [setConst_set h]
  exact traceApp_graph_beta (fun y => ZFSet.powerset y) hx

theorem pow_apply {n X : ZFSet.{u}} (hn : n ∈ ZFSet.omega) (hX : X ∈ finiteSets) :
    traceApp (traceApp (objectSetConsts h powN) n) X = powIter X (natOf n) := by
  have hn' : n ∈ ev (objHeads h) (objectSetConsts h) (cnum : CTm Tower.Head 0) Fin.elim0 := by
    rw [ev_cnum h]
    exact hn
  have hX' : X ∈ ev (objHeads h) (objectSetConsts h) (cset : CTm Tower.Head 1)
      (extend Fin.elim0 n) := by
    rw [ev_cset h]
    exact hX
  have sat : Sat (objHeads h) (objectSetConsts h) numSetTele (extend (extend Fin.elim0 n) X) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hn'⟩, hX'⟩
  have key := applyValues_telescopeGraph (objHeads h) (objectSetConsts h) numSetTele
    (fun η => powIter (η 0) (natOf (η 1))) _ sat
  rw [objectSetConsts_of h (show objConst powN = .pow by decide)]
  exact key

/-! ### The codes -/

theorem holds_apply {p : ZFSet.{u}} (hp : p ∈ Square.omega) :
    traceApp (objectSetConsts h holdsN) p = p := by
  rw [objectSetConsts_of h (show objConst holdsN = .holds by decide)]
  show traceApp (traceLam (graph (objectSetConsts h propN) fun y => y)) p = p
  rw [setConst_prop h]
  exact traceApp_graph_beta (fun y => y) hp

theorem imp_apply {p q : ZFSet.{u}} (hp : p ∈ Square.omega) (hq : q ∈ Square.omega) :
    traceApp (traceApp (objectSetConsts h impN) p) q =
      truthCode ((∅ : ZFSet.{u}) ∈ p → (∅ : ZFSet.{u}) ∈ q) := by
  have hp' : p ∈ ev (objHeads h) (objectSetConsts h) (.const propN : CTm Tower.Head 0)
      Fin.elim0 := by
    rw [ev_cprop h]
    exact hp
  have hq' : q ∈ ev (objHeads h) (objectSetConsts h) (.const propN : CTm Tower.Head 1)
      (extend Fin.elim0 p) := by
    rw [ev_cprop h]
    exact hq
  have sat : Sat (objHeads h) (objectSetConsts h) propPropTele
      (extend (extend Fin.elim0 p) q) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hp'⟩, hq'⟩
  have key := applyValues_telescopeGraph (objHeads h) (objectSetConsts h) propPropTele
    (fun η => truthCode ((∅ : ZFSet.{u}) ∈ η 1 → (∅ : ZFSet.{u}) ∈ η 0)) _ sat
  rw [objectSetConsts_of h (show objConst impN = .imp by decide)]
  exact key

theorem all_apply (type : HOL.Ty SetProfile.SetBase) {f : ZFSet.{u}}
    (hf : f ∈ simpleSet (.arr type .prop)) :
    traceApp (objectSetConsts h (SetProfile.allName type)) f =
      truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ traceApp f x) := by
  rw [objectSetConsts_of h (objConst_allName type)]
  show traceApp (traceLam (graph (ev (objHeads h) (objectSetConsts h)
      (liftTm (typeAt SetProfile.types 0 (.arr type .prop))) Fin.elim0)
      fun g => truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ traceApp g x))) f = _
  rw [ev_objTypeAt h]
  exact traceApp_graph_beta
    (fun g => truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ traceApp g x)) hf

theorem eq_apply (type : HOL.Ty SetProfile.SetBase) {x y : ZFSet.{u}} (hx : x ∈ simpleSet type)
    (hy : y ∈ simpleSet type) :
    traceApp (traceApp (objectSetConsts h (SetProfile.eqName type)) x) y = truthCode (x = y) := by
  have hx' : x ∈ ev (objHeads h) (objectSetConsts h)
      (liftTm (typeAt SetProfile.types 0 type)) Fin.elim0 := by
    rw [ev_objTypeAt h]
    exact hx
  have hy' : y ∈ ev (objHeads h) (objectSetConsts h)
      (liftTm (typeAt SetProfile.types 1 type)) (extend Fin.elim0 x) := by
    rw [ev_objTypeAt h]
    exact hy
  have sat : Sat (objHeads h) (objectSetConsts h) (eqTele type)
      (extend (extend Fin.elim0 x) y) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hx'⟩, hy'⟩
  have key := applyValues_telescopeGraph (objHeads h) (objectSetConsts h) (eqTele type)
    (fun η => truthCode (η 1 = η 0)) _ sat
  rw [objectSetConsts_of h (objConst_eqName type)]
  exact key

/-! ### The recursor, identity elimination and the iterator -/

theorem numRec_value :
    objectSetConsts h numRecName = numRecValue (objHeads h) (objectSetConsts h) numNames :=
  objectSetConsts_of h (show objConst numRecName = .numRec by decide)

theorem j_value :
    objectSetConsts h jName = jValue (objHeads h) (objectSetConsts h) (.sort Tower.zero) :=
  objectSetConsts_of h (show objConst jName = .j by decide)

theorem iter_apply {η : Env.{u} 6} (sat : Sat (objHeads h) (objectSetConsts h) cIterSucTele η) :
    applyValues (objectSetConsts h iterName) 6 η =
      iterPair (η 2) (natOf (η 5)) (ZFSet.pair (η 1) (η 0)) := by
  rw [objectSetConsts_of h (show objConst iterName = .iter by decide)]
  exact applyValues_telescopeGraph (objHeads h) (objectSetConsts h) cIterSucTele
    (fun η => iterPair (η 2) (natOf (η 5)) (ZFSet.pair (η 1) (η 0))) η sat

/-- What a typed instance of the iterator's telescope says. -/
theorem iterTele_sat {η : Env.{u} 6}
    (sat : Sat (objHeads h) (objectSetConsts h) cIterSucTele η) :
    η 5 ∈ ZFSet.omega ∧ η 2 ∈ stepSet (η 4) (η 3) ∧ η 1 ∈ η 4 ∧ η 0 ∈ traceApp (η 3) (η 1) := by
  have count : η 5 ∈ objectSetConsts h numN := sat 5
  rw [setConst_num h] at count
  exact ⟨count, sat 2, sat 1, sat 0⟩

/-- **The iterator's value at a typed instance lies in `Σ (y : A). P y`.** -/
theorem iterPair_typed {η : Env.{u} 6}
    (sat : Sat (objHeads h) (objectSetConsts h) cIterSucTele η) :
    iterPair (η 2) (natOf (η 5)) (ZFSet.pair (η 1) (η 0)) ∈
      sigmaSet (η 4) fun y => traceApp (η 3) y := by
  obtain ⟨-, step, hx, he⟩ := iterTele_sat h sat
  exact iterPair_mem step _ (mem_sigmaSet.mpr ⟨_, hx, _, he, rfl⟩)

end Values

/-! ## The definitions by one equation -/

/-- The elaborated right sides of the definitions by one equation. -/
theorem defRhs_eqAt :
    defRhs eqAtName eqAtTele eqAtRhs = (.id cnum (cadd czero (.var 0)) (.var 0) : CTm Tower.Head 1) := by
  decide

theorem defRhs_keep : defRhs keepName keepTele keepRhs = (.pair (.var 1) (.var 0) : CTm Tower.Head 4) := by
  decide

theorem defRhs_transport :
    defRhs transportName transportTelescope transportRhs =
      (.pair (.app (.var 3) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)) : CTm Tower.Head 6) := by
  decide

theorem defRhs_compose :
    defRhs composeName composeTelescope composeRhs =
      (.app (.lam (.sigma (.var 5) (.app (.var 5) (.var 0)))
          (.app (.app (.var 3) (.fst (.var 0))) (.snd (.var 0))))
        (.app (.app (.var 3) (.var 1)) (.var 0)) : CTm Tower.Head 6) := by
  decide

/-- The step type `Π (x : A). P x → Σ (y : A). P y` three binders inside a telescope
`A, P, n`. -/
abbrev cStepAt : CTm Tower.Head 3 :=
  .pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))

theorem defRhs_returnIter :
    defRhs returnIterName returnIterTele returnIterRhs =
      (.lam (.pi (.var 0) cU0) (.lam cnum (.lam cStepAt (.lam (.var 3) (.lam (.app (.var 3) (.var 0))
        (.app (.app (.app (.app (.app (.app (.const iterName) (.var 3)) (.var 5)) (.var 4))
          (.var 2)) (.var 1)) (.var 0)))))) : CTm Tower.Head 1) := by
  decide

theorem defRhs_sucMove :
    defRhs sucMoveName eqAtTelescope sucMoveRhs =
      (.app (.app (.app (.app (.app (.app (.const jName) cnum) (cadd czero (.var 1))) cSucMotive)
        (.refl (csuc (cadd czero (.var 1))))) (.var 1)) (.var 0) : CTm Tower.Head 2) := by
  decide

theorem defRhs_sucStep :
    defRhs sucStepName eqAtTelescope sucStepRhs =
      (.app (.app (.app (.app (.app (.app (.const transportName) cnum) (.const eqAtName))
        (.const sucN)) (.const sucMoveName)) (.var 1)) (.var 0) : CTm Tower.Head 2) := by
  decide

/-- The declared types of the definitions, over their telescopes. -/
theorem declType_eqAt : ObjConst.declType .eqAt = pisCtx (liftCtx eqAtTele) cU0 := rfl

theorem declType_sucMove :
    ObjConst.declType .sucMove = pisCtx (liftCtx eqAtTelescope) (ceqAt (csuc (.var 1))) := by
  decide

theorem declType_keep :
    ObjConst.declType .keep = pisCtx (liftCtx keepTele) (.sigma (.var 3) (.app (.var 3) (.var 0))) := by
  decide

theorem declType_transport :
    ObjConst.declType .transport =
      pisCtx (liftCtx transportTelescope) (.sigma (.var 5) (.app (.var 5) (.var 0))) := by
  decide

theorem declType_compose :
    ObjConst.declType .compose =
      pisCtx (liftCtx composeTelescope) (.sigma (.var 5) (.app (.var 5) (.var 0))) := by
  decide

/-- The declared type of `returnIter` after its carrier. -/
abbrev returnIterRest : CTm Tower.Head 1 :=
  .pi (.pi (.var 0) cU0) (.pi cnum (.pi cStepAt (.pi (.var 3) (.pi (.app (.var 3) (.var 0))
    (.sigma (.var 5) (.app (.var 5) (.var 0)))))))

theorem declType_returnIter :
    ObjConst.declType .returnIter = pisCtx (liftCtx returnIterTele) returnIterRest := by
  decide

theorem declType_sucStep :
    ObjConst.declType .sucStep = pisCtx (liftCtx eqAtTelescope) (.sigma cnum (ceqAt (.var 0))) := by
  decide

section Definitions

variable (h : CofinalInaccessibles.{u})

/-- **A definition applied to a typed instance of its telescope is its right side there.** -/
theorem def_apply {f : DeclName} {tag : ObjConst} (named : objConst f = tag) {k : Nat}
    {Θ : Tower.Ctx k} {rhs : Tower.Tm k}
    (raw : tag.setRaw (objHeads h) (objectSetConsts h) =
      defSetRaw (objHeads h) (objectSetConsts h) f Θ rhs) {η : Env.{u} k}
    (sat : Sat (objHeads h) (objectSetConsts h) (liftCtx Θ) η) :
    applyValues (objectSetConsts h f) k η =
      ev (objHeads h) (objectSetConsts h) (defRhs f Θ rhs) η := by
  rw [objectSetConsts_of h named, raw, defSetRaw_eq]
  exact applyValues_telescopeGraph _ _ _ _ η sat

/-- **A definition lies in the value of its declared type** when its right side lies in the
codomain's values at every typed instance of its telescope. -/
theorem defSetRaw_typed {f : DeclName} {k : Nat} {Θ : Tower.Ctx k} {rhs : Tower.Tm k}
    {T : CTm Tower.Head k}
    (typed : ∀ η, Sat (objHeads h) (objectSetConsts h) (liftCtx Θ) η →
      ev (objHeads h) (objectSetConsts h) (defRhs f Θ rhs) η ∈
        ev (objHeads h) (objectSetConsts h) T η) :
    defSetRaw (objHeads h) (objectSetConsts h) f Θ rhs ∈
      ev (objHeads h) (objectSetConsts h) (pisCtx (liftCtx Θ) T) Fin.elim0 := by
  rw [defSetRaw_eq]
  exact telescopeGraph_mem_pisCtx _ _ (liftCtx Θ) T typed

/-- `eqAt n` is the truth value of `add zero n = n`. -/
theorem eqAt_apply {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    traceApp (objectSetConsts h eqAtName) n =
      truthCode (traceApp (traceApp (objectSetConsts h addN) (objectSetConsts h zeroN)) n = n) := by
  have hn' : n ∈ ev (objHeads h) (objectSetConsts h) (cnum : CTm Tower.Head 0) Fin.elim0 := by
    rw [ev_cnum h]
    exact hn
  have sat : Sat (objHeads h) (objectSetConsts h) (liftCtx eqAtTele) (extend Fin.elim0 n) :=
    (sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hn'⟩
  have key := def_apply h (show objConst eqAtName = .eqAt by decide) rfl sat
  rw [defRhs_eqAt] at key
  exact key

/-- `add zero n` is `n`. -/
theorem zeroAdd_apply {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    traceApp (traceApp (objectSetConsts h addN) (objectSetConsts h zeroN)) n = n := by
  rw [setConst_zero h, add_apply h (numeral_mem_omega 0) hn, natOf_numeral, Nat.zero_add,
    numeral_natOf hn]

theorem eqAt_typed :
    objectSetConsts h eqAtName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .eqAt) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst eqAtName = .eqAt by decide), declType_eqAt]
  apply defSetRaw_typed h
  intro η _
  rw [defRhs_eqAt]
  exact truthCode_mem_level h 0 _

theorem suc_typed :
    objectSetConsts h sucN ∈ ev (objHeads h) (objectSetConsts h) (ObjConst.declType .suc) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst sucN = .suc by decide), declType_suc]
  refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) numTele cnum
    (body := fun η => insert (η 0) (η 0)) fun η sat => ?_
  have number : η 0 ∈ objectSetConsts h numN := sat 0
  rw [setConst_num h] at number
  show insert (η 0) (η 0) ∈ objectSetConsts h numN
  rw [setConst_num h]
  exact insert_mem_omega number

/-- The motive of the successor move, `λ y p. suc (add zero n) = suc y`, at a number `n`, is a
family of the eliminator's motive type over `ω` and the point `add zero n`. -/
theorem sucMotive_typed (η : Env.{u} 2) :
    ev (objHeads h) (objectSetConsts h) cSucMotive η ∈
      tracePiSet (objectSetConsts h numN) fun y =>
        tracePiSet (truthCode (traceApp (traceApp (objectSetConsts h addN)
          (objectSetConsts h zeroN)) (η 1) = y)) fun _ => lowest h := by
  show traceLam (graph (objectSetConsts h numN) fun y =>
      traceLam (graph (truthCode (traceApp (traceApp (objectSetConsts h addN)
        (objectSetConsts h zeroN)) (η 1) = y)) fun _ =>
          truthCode (traceApp (objectSetConsts h sucN) (traceApp (traceApp (objectSetConsts h addN)
            (objectSetConsts h zeroN)) (η 1)) = traceApp (objectSetConsts h sucN) y))) ∈ _
  exact traceLam_graph_mem fun y _ => traceLam_graph_mem fun _ _ => truthCode_mem_level h 0 _

/-- **The successor move's right side has the value of reflexivity** at a typed instance: the
eliminator returns its method. -/
theorem sucMoveBody_value {η : Env.{u} 2}
    (sat : Sat (objHeads h) (objectSetConsts h) (liftCtx eqAtTelescope) η) :
    ev (objHeads h) (objectSetConsts h) (defRhs sucMoveName eqAtTelescope sucMoveRhs) η = ∅ := by
  obtain ⟨satN, he⟩ := sat_tail _ _ sat
  have hn : η 1 ∈ objectSetConsts h numN := satN 0
  rw [setConst_num h] at hn
  have he' : η 0 ∈ traceApp (objectSetConsts h eqAtName) (η 1) := he
  rw [eqAt_apply h hn] at he'
  rw [defRhs_sucMove]
  set x₀ := traceApp (traceApp (objectSetConsts h addN) (objectSetConsts h zeroN)) (η 1) with hx₀
  set P := ev (objHeads h) (objectSetConsts h) cSucMotive η with hP
  have hx₀ω : x₀ ∈ ZFSet.omega := by
    rw [hx₀, zeroAdd_apply h hn]
    exact hn
  -- the six arguments of the eliminator form a typed instance of its telescope
  let ρ : Env.{u} 6 := extend (extend (extend (extend (extend (extend Fin.elim0
    (objectSetConsts h numN)) x₀) P) ∅) (η 1)) (η 0)
  have s₁ : objectSetConsts h numN ∈ ev (objHeads h) (objectSetConsts h)
      (.head (.sort Tower.zero) : CTm Tower.Head 0) Fin.elim0 := by
    show objectSetConsts h numN ∈ lowest h
    rw [setConst_num h]
    exact omega_mem_level h 0
  have s₂ : x₀ ∈ ev (objHeads h) (objectSetConsts h) (.var 0 : CTm Tower.Head 1)
      (extend Fin.elim0 (objectSetConsts h numN)) := by
    show x₀ ∈ objectSetConsts h numN
    rw [setConst_num h]
    exact hx₀ω
  have s₃ : P ∈ ev (objHeads h) (objectSetConsts h)
      (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head (.sort Tower.zero))) :
        CTm Tower.Head 2) (extend (extend Fin.elim0 (objectSetConsts h numN)) x₀) :=
    sucMotive_typed h η
  have reflAt : traceApp (traceApp P x₀) ∅ = truthCode (traceApp (objectSetConsts h sucN) x₀ =
      traceApp (objectSetConsts h sucN) x₀) := by
    have atPoint : traceApp P x₀ = traceLam (graph (truthCode (x₀ = x₀)) fun _ =>
        truthCode (traceApp (objectSetConsts h sucN) x₀ = traceApp (objectSetConsts h sucN) x₀)) := by
      show traceApp (traceLam (graph (objectSetConsts h numN) fun y =>
        traceLam (graph (truthCode (x₀ = y)) fun _ =>
          truthCode (traceApp (objectSetConsts h sucN) x₀ = traceApp (objectSetConsts h sucN) y))))
        x₀ = _
      rw [traceApp_graph_beta _ (by rw [setConst_num h]; exact hx₀ω)]
    rw [atPoint, traceApp_graph_beta _ (empty_mem_truthCode_eq x₀)]
  have s₄ : (∅ : ZFSet.{u}) ∈ ev (objHeads h) (objectSetConsts h)
      (.app (.app (.var 0) (.var 1)) (.refl (.var 1)) : CTm Tower.Head 3)
      (extend (extend (extend Fin.elim0 (objectSetConsts h numN)) x₀) P) := by
    show (∅ : ZFSet.{u}) ∈ traceApp (traceApp P x₀) ∅
    rw [reflAt]
    exact empty_mem_truthCode_eq _
  have s₅ : η 1 ∈ ev (objHeads h) (objectSetConsts h) (.var 3 : CTm Tower.Head 4)
      (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN)) x₀) P) ∅) := by
    show η 1 ∈ objectSetConsts h numN
    rw [setConst_num h]
    exact hn
  have s₆ : η 0 ∈ ev (objHeads h) (objectSetConsts h) (.id (.var 4) (.var 3) (.var 0) :
      CTm Tower.Head 5)
      (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN)) x₀) P) ∅)
        (η 1)) := he'
  have satJ : Sat (objHeads h) (objectSetConsts h) (jTele (.sort Tower.zero)) ρ :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, s₁⟩, s₂⟩, s₃⟩, s₄⟩, s₅⟩, s₆⟩
  have key := jValue_apply satJ
  rw [← j_value h] at key
  exact key

theorem sucMove_typed :
    objectSetConsts h sucMoveName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .sucMove) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst sucMoveName = .sucMove by decide), declType_sucMove]
  apply defSetRaw_typed h
  intro η sat
  rw [sucMoveBody_value h sat]
  obtain ⟨satN, -⟩ := sat_tail _ _ sat
  have hn : η 1 ∈ objectSetConsts h numN := satN 0
  rw [setConst_num h] at hn
  have hs : traceApp (objectSetConsts h sucN) (η 1) ∈ ZFSet.omega := by
    rw [suc_apply h hn]
    exact insert_mem_omega hn
  show (∅ : ZFSet.{u}) ∈ traceApp (objectSetConsts h eqAtName)
    (traceApp (objectSetConsts h sucN) (η 1))
  rw [eqAt_apply h hs, zeroAdd_apply h hs]
  exact empty_mem_truthCode_eq _

/-- The transport certificate applied to a typed instance: the pair of the moved value and the
moved evidence. -/
theorem transport_apply {η : Env.{u} 6}
    (sat : Sat (objHeads h) (objectSetConsts h) (liftCtx transportTelescope) η) :
    applyValues (objectSetConsts h transportName) 6 η =
      ZFSet.pair (traceApp (η 3) (η 1)) (traceApp (traceApp (η 2) (η 1)) (η 0)) := by
  have key := def_apply h (show objConst transportName = .transport by decide) rfl sat
  rw [defRhs_transport] at key
  exact key

end Definitions

/-! ## Every constant lies in the value of its declared type -/

section Typing

variable (h : CofinalInaccessibles.{u})

theorem keep_typed :
    objectSetConsts h keepName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .keep) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst keepName = .keep by decide), declType_keep]
  apply defSetRaw_typed h
  intro η sat
  rw [defRhs_keep]
  have hx : η 1 ∈ η 3 := sat 1
  have he : η 0 ∈ traceApp (η 2) (η 1) := sat 0
  show ZFSet.pair (η 1) (η 0) ∈ sigmaSet (η 3) fun y => traceApp (η 2) y
  exact mem_sigmaSet.mpr ⟨_, hx, _, he, rfl⟩

theorem transport_typed :
    objectSetConsts h transportName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .transport) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst transportName = .transport by decide),
    declType_transport]
  apply defSetRaw_typed h
  intro η sat
  rw [defRhs_transport]
  have hf : η 3 ∈ tracePiSet (η 5) fun _ => η 5 := sat 3
  have hmove : η 2 ∈ tracePiSet (η 5) fun x =>
      tracePiSet (traceApp (η 4) x) fun _ => traceApp (η 4) (traceApp (η 3) x) := sat 2
  have hx : η 1 ∈ η 5 := sat 1
  have he : η 0 ∈ traceApp (η 4) (η 1) := sat 0
  have fx := traceApp_mem_fibre hf hx
  have moveAt := traceApp_mem_fibre hmove hx
  have moved := traceApp_mem_fibre moveAt he
  show ZFSet.pair (traceApp (η 3) (η 1)) (traceApp (traceApp (η 2) (η 1)) (η 0)) ∈
    sigmaSet (η 5) fun y => traceApp (η 4) y
  exact mem_sigmaSet.mpr ⟨_, fx, _, moved, rfl⟩

theorem compose_typed :
    objectSetConsts h composeName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .compose) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst composeName = .compose by decide), declType_compose]
  apply defSetRaw_typed h
  intro η sat
  rw [defRhs_compose]
  have hstep : η 3 ∈ stepSet (η 5) (η 4) := sat 3
  have hstep₂ : η 2 ∈ stepSet (η 5) (η 4) := sat 2
  have hx : η 1 ∈ η 5 := sat 1
  have he : η 0 ∈ traceApp (η 4) (η 1) := sat 0
  have atX := traceApp_mem_fibre hstep hx
  have hq := traceApp_mem_fibre atX he
  show traceApp (traceLam (graph (sigmaSet (η 5) fun y => traceApp (η 4) y) fun pack =>
      traceApp (traceApp (η 2) (ZFSetOrderedPair.first pack)) (ZFSetOrderedPair.second pack)))
      (traceApp (traceApp (η 3) (η 1)) (η 0)) ∈ sigmaSet (η 5) fun y => traceApp (η 4) y
  rw [traceApp_graph_beta _ hq]
  exact step_mem hstep₂ hq

theorem iter_typed :
    objectSetConsts h iterName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .iter) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst iterName = .iter by decide), declType_iter]
  exact telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) cIterSucTele iterResult
    (body := fun η => iterPair (η 2) (natOf (η 5)) (ZFSet.pair (η 1) (η 0)))
    fun η sat => iterPair_typed h sat

/-- The iterator applied to its six arguments, at a typed instance of its telescope. -/
theorem iter_apply_six {n A P step x e : ZFSet.{u}} (hn : n ∈ ZFSet.omega) (hA : A ∈ lowest h)
    (hP : P ∈ tracePiSet A fun _ => lowest h) (hstep : step ∈ stepSet A P) (hx : x ∈ A)
    (he : e ∈ traceApp P x) :
    traceApp (traceApp (traceApp (traceApp (traceApp (traceApp
      (objectSetConsts h iterName) n) A) P) step) x) e ∈ sigmaSet A fun y => traceApp P y := by
  have hn' : n ∈ objectSetConsts h numN := by
    rw [setConst_num h]
    exact hn
  have satIter : Sat (objHeads h) (objectSetConsts h) cIterSucTele
      (extend (extend (extend (extend (extend (extend Fin.elim0 n) A) P) step) x) e) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, hn'⟩, hA⟩, hP⟩, hstep⟩,
        hx⟩, he⟩
  have key := iter_apply h satIter
  have typed := iterPair_typed h satIter
  change applyValues (objectSetConsts h iterName) 6
      (extend (extend (extend (extend (extend (extend Fin.elim0 n) A) P) step) x) e) ∈
    sigmaSet A fun y => traceApp P y
  rw [key]
  exact typed

theorem returnIter_typed :
    objectSetConsts h returnIterName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .returnIter) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst returnIterName = .returnIter by decide),
    declType_returnIter]
  apply defSetRaw_typed h
  intro η sat
  rw [defRhs_returnIter]
  have hA : η 0 ∈ lowest h := sat 0
  refine ev_lam_mem_pi _ _ fun P hP => ?_
  refine ev_lam_mem_pi _ _ fun n hn => ?_
  refine ev_lam_mem_pi _ _ fun step hstep => ?_
  refine ev_lam_mem_pi _ _ fun x hx => ?_
  refine ev_lam_mem_pi _ _ fun e he => ?_
  have hn' : n ∈ objectSetConsts h numN := hn
  rw [setConst_num h] at hn'
  exact iter_apply_six h hn' hA hP hstep hx he

theorem sucStep_typed :
    objectSetConsts h sucStepName ∈
      ev (objHeads h) (objectSetConsts h) (ObjConst.declType .sucStep) Fin.elim0 := by
  rw [objectSetConsts_of h (show objConst sucStepName = .sucStep by decide), declType_sucStep]
  apply defSetRaw_typed h
  intro η sat
  rw [defRhs_sucStep]
  have hn : η 1 ∈ objectSetConsts h numN := sat 1
  have he : η 0 ∈ traceApp (objectSetConsts h eqAtName) (η 1) := sat 0
  have s₁ : objectSetConsts h numN ∈ lowest h := by
    rw [setConst_num h]
    exact omega_mem_level h 0
  have s₂ : objectSetConsts h eqAtName ∈
      tracePiSet (objectSetConsts h numN) fun _ => lowest h := eqAt_typed h
  have s₃ : objectSetConsts h sucN ∈
      tracePiSet (objectSetConsts h numN) fun _ => objectSetConsts h numN := suc_typed h
  have s₄ : objectSetConsts h sucMoveName ∈ tracePiSet (objectSetConsts h numN) fun x =>
      tracePiSet (traceApp (objectSetConsts h eqAtName) x) fun _ =>
        traceApp (objectSetConsts h eqAtName) (traceApp (objectSetConsts h sucN) x) :=
    sucMove_typed h
  have satT : Sat (objHeads h) (objectSetConsts h) (liftCtx transportTelescope)
      (extend (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN))
        (objectSetConsts h eqAtName)) (objectSetConsts h sucN)) (objectSetConsts h sucMoveName))
        (η 1)) (η 0)) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, s₁⟩, s₂⟩, s₃⟩, s₄⟩, hn⟩,
        he⟩
  have key := transport_apply h satT
  have sucAt := traceApp_mem_fibre s₃ hn
  have moveAt := traceApp_mem_fibre s₄ hn
  have moved := traceApp_mem_fibre moveAt he
  have typed : ZFSet.pair (traceApp (objectSetConsts h sucN) (η 1))
      (traceApp (traceApp (objectSetConsts h sucMoveName) (η 1)) (η 0)) ∈
        sigmaSet (objectSetConsts h numN) fun m => traceApp (objectSetConsts h eqAtName) m :=
    mem_sigmaSet.mpr ⟨_, sucAt, _, moved, rfl⟩
  show applyValues (objectSetConsts h transportName) 6
      (extend (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN))
        (objectSetConsts h eqAtName)) (objectSetConsts h sucN)) (objectSetConsts h sucMoveName))
        (η 1)) (η 0)) ∈
    sigmaSet (objectSetConsts h numN) fun m => traceApp (objectSetConsts h eqAtName) m
  rw [key]
  exact typed

/-- **The value of every constant lies in the value of its declared type.** -/
theorem setRaw_typed (tag : ObjConst) :
    tag.setRaw (objHeads h) (objectSetConsts h) ∈
      ev (objHeads h) (objectSetConsts h) tag.declType Fin.elim0 := by
  cases tag with
  | num => exact omega_mem_level h 0
  | set => exact finiteSets_mem_level h 0
  | prop => exact truthValues_mem_level h 0
  | other => exact empty_mem_level h 0
  | zero =>
      show numeral 0 ∈ objectSetConsts h numN
      rw [setConst_num h]
      exact numeral_mem_omega 0
  | suc =>
      rw [← objectSetConsts_of h (show objConst sucN = .suc by decide)]
      exact suc_typed h
  | add =>
      rw [declType_add]
      refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) numNumTele cnum
        (body := fun η => numeral (natOf (η 1) + natOf (η 0))) fun η _ => ?_
      show numeral (natOf (η 1) + natOf (η 0)) ∈ objectSetConsts h numN
      rw [setConst_num h]
      exact numeral_mem_omega _
  | power =>
      rw [declType_power]
      refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) setTele cset
        (body := fun η => ZFSet.powerset (η 0)) fun η sat => ?_
      have hx : η 0 ∈ objectSetConsts h setN := sat 0
      show ZFSet.powerset (η 0) ∈ objectSetConsts h setN
      rw [setConst_set h] at hx ⊢
      exact powerset_mem_finiteSets hx
  | pow =>
      rw [declType_pow]
      refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) numSetTele cset
        (body := fun η => powIter (η 0) (natOf (η 1))) fun η sat => ?_
      have hX : η 0 ∈ objectSetConsts h setN := sat 0
      show powIter (η 0) (natOf (η 1)) ∈ objectSetConsts h setN
      rw [setConst_set h] at hX ⊢
      exact powIter_mem hX _
  | numRec => exact numRecValue_mem (numberReading h)
  | j => exact jValue_mem _
  | eqAt =>
      rw [← objectSetConsts_of h (show objConst eqAtName = .eqAt by decide)]
      exact eqAt_typed h
  | sucMove =>
      rw [← objectSetConsts_of h (show objConst sucMoveName = .sucMove by decide)]
      exact sucMove_typed h
  | keep =>
      rw [← objectSetConsts_of h (show objConst keepName = .keep by decide)]
      exact keep_typed h
  | transport =>
      rw [← objectSetConsts_of h (show objConst transportName = .transport by decide)]
      exact transport_typed h
  | compose =>
      rw [← objectSetConsts_of h (show objConst composeName = .compose by decide)]
      exact compose_typed h
  | iter =>
      rw [← objectSetConsts_of h (show objConst iterName = .iter by decide)]
      exact iter_typed h
  | returnIter =>
      rw [← objectSetConsts_of h (show objConst returnIterName = .returnIter by decide)]
      exact returnIter_typed h
  | sucStep =>
      rw [← objectSetConsts_of h (show objConst sucStepName = .sucStep by decide)]
      exact sucStep_typed h
  | holds =>
      rw [declType_holds]
      refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) propTele cU0
        (body := fun η => η 0) fun η sat => ?_
      have hp : η 0 ∈ objectSetConsts h propN := sat 0
      rw [setConst_prop h] at hp
      exact (universeSet_closed h _ 0).transitive _ (truthValues_mem_level h 0) hp
  | imp =>
      rw [declType_imp]
      refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) propPropTele (.const propN)
        (body := fun η => truthCode ((∅ : ZFSet.{u}) ∈ η 1 → (∅ : ZFSet.{u}) ∈ η 0)) fun η _ => ?_
      show truthCode _ ∈ objectSetConsts h propN
      rw [setConst_prop h]
      exact Square.truthCode_mem_omega _
  | all type =>
      rw [declType_all]
      refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) (allTele type)
        (.const propN) (body := fun η =>
          truthCode (∀ x ∈ simpleSet.{u} type, (∅ : ZFSet.{u}) ∈ traceApp (η 0) x)) fun η _ => ?_
      show truthCode _ ∈ objectSetConsts h propN
      rw [setConst_prop h]
      exact Square.truthCode_mem_omega _
  | eq type =>
      rw [declType_eq]
      refine telescopeGraph_mem_pisCtx (objHeads h) (objectSetConsts h) (eqTele type) (.const propN)
        (body := fun η => truthCode (η 1 = η 0)) fun η _ => ?_
      show truthCode _ ∈ objectSetConsts h propN
      rw [setConst_prop h]
      exact Square.truthCode_mem_omega _

/-- **Every declared constant of the object package lies in the value of its declared type**,
in the seeded tower, relative to `CofinalInaccessibles`: the fixed constants, and the
quantifier and the equation at every simple type. -/
theorem objectSetConsts_typed {c : DeclName} {T : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some T) :
    objectSetConsts h c ∈ ev (objHeads h) (objectSetConsts h) T Fin.elim0 := by
  rw [declType_of_declared declared, objectSetConsts_const h c]
  exact setRaw_typed h (objConst c)

end Typing

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
