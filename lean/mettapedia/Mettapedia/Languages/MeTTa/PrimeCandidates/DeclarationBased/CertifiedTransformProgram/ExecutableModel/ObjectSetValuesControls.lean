import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSteps

/-!
# Controls for the set values of the object package

Positive controls are the theorems of `ObjectSetValues` and `ObjectSetSteps`. The negative
controls here show that each hypothesis and each value is doing work.

* **The seed.** The seeded tower holds `ω` at its lowest level (`seeded_lowest_omega`); the
  standard tower, seeded with the empty set, does not (`standard_lowest_no_omega`), so no
  reading of `num : U₀` as the naturals fits it.
* **The premises are needed.** Whatever the heads and the constants' values, the object
  package without the premises of its root steps has no set model
  (`objectChurch_withoutPremises_no_setModel`): the step of `keepCert` fails at an environment
  sending its carrier outside the lowest universe. With its premises the package has a set
  model in the seeded tower (`objectSetModel`), because its steps are valid at their typed
  instances (`SetTower.objectSchemas_valid`).
* **A wrong recursor.** The value that returns the value at zero at every number satisfies the
  iota step at zero but fails the iota step at a successor (`constantRec_zero_valid`,
  `constantRec_fails`).
* **Identity elimination needs its endpoint equations.** At an instance that types the
  metavariables but whose reflexivity point is not the endpoint, the path lies outside the
  identity value and the eliminator's value is the empty set, not the method
  (`j_needs_equations`).
* **A wrong decoder.** A decoder reading every code as true fails the decoding of an equation
  between two distinct numbers (`trueDecoder_fails`).
* **A wrong definition.** A value for `eqAt` that is not the traced graph of its right side
  fails its defining step (`falseEqAt_fails`).
* **Nothing degenerate about the sets.** `Power` is the power set: it sends `∅` to `{∅}`
  (`power_empty`), so it is not the identity.
* **A false code.** The quantification of every truth value, `all@prop (λ p. p)`, decodes to
  the empty set (`falsum_code_empty`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet universeSet_closed)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetDependentProducts (graph sigmaSet mem_sigmaSet)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta traceApp_graph_outside
  traceApp_empty)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open FormationSensitiveHOLInterface (typeAt)
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName eqAtName keepName)
open Mettapedia.Logic

universe u

namespace CodeModel

/-! ## The seed -/

/-- **Positive: the seeded tower holds the natural numbers at its lowest level.** -/
theorem seeded_lowest_omega (h : CofinalInaccessibles.{u}) :
    ZFSet.omega.{u} ∈ objHeads h (.sort Tower.zero) :=
  omega_mem_level h 0

/-- **Negative: the standard tower, seeded with the empty set, does not.** Its lowest level
lies inside the hereditarily finite sets, so `num : U₀` cannot be read as the naturals in it. -/
theorem standard_lowest_no_omega (h : CofinalInaccessibles.{u}) :
    ZFSet.omega.{u} ∉ interpretHead h ∅ ∅ (fun _ => 0) (.sort Tower.zero) := by
  change ZFSet.omega.{u} ∉ universeSet h ∅ 0
  rw [ZFSetInterpretation.universeSet_nat_zero]
  exact omega_not_mem_univOf_empty h

/-! ## No set model without the premises -/

theorem keep_elabLeft :
    elabLeft objectDecls (applyClosed keepTele Presentation.ids (.const keepName)) =
      (.app (.app (.app (.app (.const keepName) (.var 3)) (.var 2)) (.var 1)) (.var 0) :
        CTm Tower.Head 4) := by
  decide

theorem keep_elabRight :
    elabRight objectDecls (applyClosed keepTele Presentation.ids (.const keepName)) keepRhs =
      (.pair (.var 1) (.var 0) : CTm Tower.Head 4) :=
  defRhs_keep

/-- A pair is not the empty set. -/
theorem pair_ne_empty (x y : ZFSet.{u}) : ZFSet.pair x y ≠ ∅ := fun same => by
  have member : ({x} : ZFSet.{u}) ∈ ZFSet.pair x y := ZFSet.mem_insert _ _
  rw [same] at member
  exact ZFSet.notMem_empty _ member

/-- **Negative: the object package without the premises of its root steps has no set model**,
whatever the heads and the constants' values. With them it has one (`objectSetModel`). At four variables of the next universe, each
sent to the value of the lowest universe itself, the carrier of `keepCert` is outside the
domain of `keepCert`'s declared type: the left side of its step is the empty set and the
right side is a pair. -/
theorem objectChurch_withoutPremises_no_setModel (heads : Tower.Head → ZFSet.{u})
    (consts : DeclName → ZFSet.{u}) : ¬ SetModel heads consts objectChurch.withoutPremises := by
  intro model
  have step := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 6) (by decide))
    (L := applyClosed keepTele Presentation.ids (.const keepName)) (R := keepRhs) rfl
    (CTm.ids : CSub Tower.Head 4 4)
  rw [CTm.subst_ids, CTm.subst_ids, keep_elabLeft, keep_elabRight] at step
  have declared : objectChurch.withoutPremises.constantType keepName =
      some (liftTm Package.keepType) :=
    objectChurch_declared (c := keepName) (T := Package.keepType) (by decide) (by decide)
  have typed := model.constants declared
  have outside := traceApp_eq_empty_of_not_mem typed (ZFSet.mem_irrefl (heads (.sort Tower.zero)))
  have above : heads (.sort Tower.zero) ∈ heads (.sort (.succ Tower.zero)) :=
    model.universes.headTyping_mem (.sort Tower.zero)
  have sat : Sat heads consts
      (.snoc (.snoc (.snoc (.snoc .nil (.head (.sort (.succ Tower.zero))))
        (.head (.sort (.succ Tower.zero)))) (.head (.sort (.succ Tower.zero))))
        (.head (.sort (.succ Tower.zero))))
      (extend (extend (extend (extend Fin.elim0 (heads (.sort Tower.zero)))
        (heads (.sort Tower.zero))) (heads (.sort Tower.zero))) (heads (.sort Tower.zero))) :=
    (sat_snoc heads consts).mpr ⟨(sat_snoc heads consts).mpr ⟨(sat_snoc heads consts).mpr
      ⟨(sat_snoc heads consts).mpr ⟨sat_nil heads consts _, above⟩, above⟩, above⟩, above⟩
  have equal := model.steps (P := objectChurch.withoutPremises) step rfl
    (fun _ member => absurd member List.not_mem_nil) _ sat
  change traceApp (traceApp (traceApp (traceApp (consts keepName) (heads (.sort Tower.zero)))
    (heads (.sort Tower.zero))) (heads (.sort Tower.zero))) (heads (.sort Tower.zero)) =
    ZFSet.pair (heads (.sort Tower.zero)) (heads (.sort Tower.zero)) at equal
  rw [outside, traceApp_empty, traceApp_empty, traceApp_empty] at equal
  exact pair_ne_empty _ _ equal.symm

/-! ## Typed instances from a telescope -/

/-- A typed instance of a left side without reflexivity positions, from an environment
satisfying the telescope its positions require. -/
theorem typedInstance_of_sat {heads : Tower.Head → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
    {k : Nat} {L : Tm Tower.Head k} {Θ : CCtx Tower.Head k}
    (known : ∀ i, patternKnowledge objectDecls none L i = some (Θ.lookup i))
    (noEquations : patternEquations objectDecls none L = []) {η : Env.{u} k}
    (sat : Sat heads consts Θ η) : TypedInstance heads consts objectDecls L η := by
  refine ⟨fun i T found => ?_, fun e mem => ?_⟩
  · rw [known i] at found
    cases found
    exact sat i
  · rw [noEquations] at mem
    cases mem

theorem numRecSuc_equations :
    patternEquations objectDecls none (iotaLeft (Head := Tower.Head) numRecName sucN 2 1) = [] := by
  decide

theorem eqAt_knowledge : ∀ i, patternKnowledge objectDecls none
    (applyClosed eqAtTele Presentation.ids (.const eqAtName)) i =
      some ((liftCtx eqAtTele).lookup i) := by
  decide

theorem eqAt_equations :
    patternEquations objectDecls none (applyClosed eqAtTele Presentation.ids (.const eqAtName)) =
      [] := by
  decide

theorem eq_equations (type : HOL.Ty SetProfile.SetBase) :
    patternEquations objectDecls none (eqLeft type) = [] := by
  simp [patternEquations]

section Wrong

variable (h : CofinalInaccessibles.{u})

/-- The truth values at every number: a motive. -/
noncomputable def truthMotive : ZFSet.{u} := traceLam (graph ZFSet.omega fun _ => Square.omega)

/-- The step to the true truth value. -/
noncomputable def trueStep : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun _ => traceLam (graph Square.omega fun _ => {∅}))

theorem truthMotive_at {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) : traceApp truthMotive x = Square.omega :=
  traceApp_graph_beta _ hx

theorem empty_mem_truthValues : (∅ : ZFSet.{u}) ∈ Square.omega :=
  ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)

theorem true_mem_truthValues : ({∅} : ZFSet.{u}) ∈ Square.omega :=
  ZFSet.mem_powerset.mpr fun _ hz => hz

theorem empty_ne_true : (∅ : ZFSet.{u}) ≠ {∅} := fun same => by
  have member : (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_singleton.mpr rfl
  rw [← same] at member
  exact ZFSet.notMem_empty _ member

/-! ## A wrong recursor -/

/-- **A wrong value for the recursor**: the value at zero at every number, ignoring the
step. -/
noncomputable def constantRec : ZFSet.{u} :=
  telescopeGraph (objHeads h) (objectSetConsts h) (nrTele numNames) fun η => η 2

/-- The constants with the wrong recursor. -/
noncomputable def constantRecConsts : DeclName → ZFSet.{u} :=
  Function.update (objectSetConsts h) numRecName (constantRec h)

theorem constantRecConsts_of {c : DeclName} (distinct : c ≠ numRecName) :
    constantRecConsts h c = objectSetConsts h c :=
  Function.update_of_ne distinct _ _

/-- The recursor's telescope at the motive of truth values, the false value at zero, the step
to true and a number, in the values of a reading of the numbers. -/
theorem wrongInstance_sat {consts : DeclName → ZFSet.{u}} (hnum : consts numN = ZFSet.omega)
    (hzero : consts zeroN = numeral 0)
    (hsuc : ∀ {x : ZFSet.{u}}, x ∈ ZFSet.omega → traceApp (consts sucN) x ∈ ZFSet.omega)
    {n : ZFSet.{u}} (hn : n ∈ ZFSet.omega) :
    Sat (objHeads h) consts (nrTele numNames)
      (extend (extend (extend (extend Fin.elim0 truthMotive) ∅) trueStep) n) := by
  have s₁ : truthMotive ∈ tracePiSet (consts numN) fun _ => lowest h := by
    rw [hnum]
    exact traceLam_graph_mem fun _ _ => truthValues_mem_level h 0
  have s₂ : (∅ : ZFSet.{u}) ∈ traceApp truthMotive (consts zeroN) := by
    rw [hzero, truthMotive_at (numeral_mem_omega 0)]
    exact empty_mem_truthValues
  have s₃ : trueStep ∈ tracePiSet (consts numN) fun v =>
      tracePiSet (traceApp truthMotive v) fun _ => traceApp truthMotive (traceApp (consts sucN) v) := by
    rw [hnum]
    refine traceLam_graph_mem fun v hv => ?_
    show traceLam (graph Square.omega fun _ => {∅}) ∈
      tracePiSet (traceApp truthMotive v) fun _ => traceApp truthMotive (traceApp (consts sucN) v)
    rw [truthMotive_at hv, truthMotive_at (hsuc hv)]
    exact traceLam_graph_mem fun _ _ => true_mem_truthValues
  have s₄ : n ∈ consts numN := by
    rw [hnum]
    exact hn
  exact (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
    ⟨sat_nil _ _ Fin.elim0, s₁⟩, s₂⟩, s₃⟩, s₄⟩

theorem constantRec_num : constantRecConsts h numN = ZFSet.omega := by
  rw [constantRecConsts_of h (by decide), setConst_num h]

theorem constantRec_zero : constantRecConsts h zeroN = numeral 0 := by
  rw [constantRecConsts_of h (by decide), setConst_zero h]

theorem constantRec_suc {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    traceApp (constantRecConsts h sucN) x = insert x x := by
  rw [constantRecConsts_of h (by decide), suc_apply h hx]

/-- The recursor's telescope does not mention the recursor. -/
theorem cRecTele_fresh : ∀ i : Fin 3, ∀ c ∈ termConsts (cRecTele.lookup i), c ≠ numRecName := by
  decide

/-- **Positive: the wrong recursor still satisfies the iota step at zero.** -/
theorem constantRec_zero_valid :
    SchemaValid (objHeads h) (constantRecConsts h) objectDecls
      (iotaLeft numRecName zeroN 2 0) (iotaRight numRecName 2 0 ([] : List CtorField)) := by
  intro η typed
  have sat : Sat (objHeads h) (constantRecConsts h) cRecTele η := typed.sat numRecZero_knowledge
  rw [numRecZero_elabLeft, numRecZero_elabRight]
  have satC : Sat (objHeads h) (objectSetConsts h) cRecTele η := fun i => by
    have member := sat i
    rwa [ev_congr_consts (objHeads h) (constantRecConsts h) (consts' := objectSetConsts h)
      (cRecTele.lookup i) (fun c hc => constantRecConsts_of h (cRecTele_fresh i c hc)) η] at member
  have hz : objectSetConsts h zeroN ∈ objectSetConsts h numN := by
    rw [setConst_zero h, setConst_num h]
    exact numeral_mem_omega 0
  have satN : Sat (objHeads h) (objectSetConsts h) (nrTele numNames)
      (extend η (objectSetConsts h zeroN)) :=
    (sat_snoc _ _).mpr ⟨satC, hz⟩
  have key := applyValues_telescopeGraph (objHeads h) (objectSetConsts h) (nrTele numNames)
    (fun η => η 2) _ satN
  change applyValues (constantRecConsts h numRecName) 4 (extend η (constantRecConsts h zeroN)) = η 1
  have value : constantRecConsts h numRecName = constantRec h := Function.update_self _ _ _
  have zero : constantRecConsts h zeroN = objectSetConsts h zeroN := constantRecConsts_of h (by decide)
  rw [value, zero]
  exact key

/-- **Negative: the wrong recursor fails the iota step at a successor**: at the motive of
truth values, the false value at zero and the step to true, it gives false at one, where the
step gives true. -/
theorem constantRec_fails :
    ¬ SchemaValid (objHeads h) (constantRecConsts h) objectDecls
      (iotaLeft numRecName sucN 2 1) (iotaRight numRecName 2 1 [(.recursive : CtorField)]) := by
  intro valid
  have satW := wrongInstance_sat h (consts := constantRecConsts h) (constantRec_num h)
    (constantRec_zero h) (fun hx => by rw [constantRec_suc h hx]; exact insert_mem_omega hx)
    (numeral_mem_omega 0)
  have typed : TypedInstance (objHeads h) (constantRecConsts h) objectDecls
      (iotaLeft numRecName sucN 2 1)
      (extend (extend (extend (extend Fin.elim0 truthMotive) ∅) trueStep) (numeral 0)) :=
    typedInstance_of_sat numRecSuc_knowledge numRecSuc_equations satW
  have equal := valid _ typed
  rw [numRecSuc_elabLeft, numRecSuc_elabRight] at equal
  change applyValues (constantRecConsts h numRecName) 4
      (extend (extend (extend (extend Fin.elim0 truthMotive) ∅) trueStep)
        (traceApp (constantRecConsts h sucN) (numeral 0))) =
    traceApp (traceApp trueStep (numeral 0))
      (applyValues (constantRecConsts h numRecName) 4
        (extend (extend (extend (extend Fin.elim0 truthMotive) ∅) trueStep) (numeral 0))) at equal
  have value : constantRecConsts h numRecName = constantRec h := Function.update_self _ _ _
  have satC : ∀ {n : ZFSet.{u}}, n ∈ ZFSet.omega →
      Sat (objHeads h) (objectSetConsts h) (nrTele numNames)
        (extend (extend (extend (extend Fin.elim0 truthMotive) ∅) trueStep) n) := fun hn =>
    wrongInstance_sat h (setConst_num h) (setConst_zero h)
      (fun hx => by rw [suc_apply h hx]; exact insert_mem_omega hx) hn
  have hs : traceApp (constantRecConsts h sucN) (numeral 0) ∈ ZFSet.omega := by
    rw [constantRec_suc h (numeral_mem_omega 0)]
    exact insert_mem_omega (numeral_mem_omega 0)
  rw [value, constantRec,
    applyValues_telescopeGraph (objHeads h) (objectSetConsts h) _ _ _ (satC hs),
    applyValues_telescopeGraph (objHeads h) (objectSetConsts h) _ _ _
      (satC (numeral_mem_omega 0))] at equal
  change (∅ : ZFSet.{u}) = traceApp (traceApp trueStep (numeral 0)) ∅ at equal
  rw [trueStep, traceApp_graph_beta _ (numeral_mem_omega 0),
    traceApp_graph_beta _ empty_mem_truthValues] at equal
  exact empty_ne_true equal

/-! ## Identity elimination needs its endpoint equations -/

/-- The first five entries of the eliminator's telescope. -/
abbrev jTeleFive : CCtx Tower.Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.var 0))
    (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0)))
    (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))) (.var 3)

/-- The motive of truth values over the paths from zero. -/
noncomputable def pathMotive : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun y =>
    traceLam (graph (truthCode ((numeral 0 : ZFSet.{u}) = y)) fun _ => Square.omega))

/-- **Negative: the linear rule of identity elimination fails at an instance that types its
metavariables but whose reflexivity point is not the endpoint**: the path from zero to one
lies outside the identity value, so the eliminator gives the empty set, not the method. -/
theorem j_needs_equations :
    ∃ η : Env.{u} 6, Sat (objHeads h) (objectSetConsts h) cJTele η ∧
      ev (objHeads h) (objectSetConsts h) (elabLeft objectDecls (eliminatorLeft jName)) η ≠
        ev (objHeads h) (objectSetConsts h) (.var 2 : CTm Tower.Head 6) η := by
  have zeroOne : (numeral 0 : ZFSet.{u}) ≠ numeral 1 := fun same =>
    absurd (numeral_injective same) (by decide)
  have h0 : (numeral 0 : ZFSet.{u}) ∈ ZFSet.omega := numeral_mem_omega 0
  have h1 : (numeral 1 : ZFSet.{u}) ∈ ZFSet.omega := numeral_mem_omega 1
  have motiveAt : traceApp (traceApp pathMotive (numeral 0)) ∅ = Square.omega.{u} := by
    rw [pathMotive, traceApp_graph_beta _ h0, traceApp_graph_beta _ (empty_mem_truthCode_eq _)]
  have s₁ : objectSetConsts h numN ∈ lowest h := by
    rw [setConst_num h]
    exact omega_mem_level h 0
  have s₂ : (numeral 0 : ZFSet.{u}) ∈ objectSetConsts h numN := by
    rw [setConst_num h]
    exact h0
  have s₃ : pathMotive ∈ tracePiSet (objectSetConsts h numN) fun y =>
      tracePiSet (truthCode ((numeral 0 : ZFSet.{u}) = y)) fun _ => lowest h := by
    rw [setConst_num h]
    exact traceLam_graph_mem fun _ _ => traceLam_graph_mem fun _ _ => truthValues_mem_level h 0
  have s₄ : ({∅} : ZFSet.{u}) ∈ traceApp (traceApp pathMotive (numeral 0)) ∅ := by
    rw [motiveAt]
    exact true_mem_truthValues
  have s₅ : (numeral 1 : ZFSet.{u}) ∈ objectSetConsts h numN := by
    rw [setConst_num h]
    exact h1
  have satFive : Sat (objHeads h) (objectSetConsts h) jTeleFive
      (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN)) (numeral 0))
        pathMotive) {∅}) (numeral 1)) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr
      ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, s₁⟩, s₂⟩, s₃⟩, s₄⟩, s₅⟩
  refine ⟨extend (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN))
    (numeral 0)) pathMotive) {∅}) (numeral 1)) (numeral 0),
    (sat_snoc _ _).mpr ⟨satFive, s₂⟩, fun same => ?_⟩
  rw [j_elabLeft] at same
  change applyValues (objectSetConsts h jName) 6
      (extend (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN))
        (numeral 0)) pathMotive) {∅}) (numeral 1)) ∅) = {∅} at same
  rw [j_value h] at same
  change traceApp (applyValues (telescopeGraph (objHeads h) (objectSetConsts h) jTeleFive
      fun η => traceLam (graph (ev (objHeads h) (objectSetConsts h)
        (.id (.var 4) (.var 3) (.var 0) : CTm Tower.Head 5) η) fun x =>
          extend η x 2)) 5
      (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN)) (numeral 0))
        pathMotive) {∅}) (numeral 1))) ∅ = {∅} at same
  rw [applyValues_telescopeGraph _ _ _ _ _ satFive] at same
  change traceApp (traceLam (graph (truthCode ((numeral 0 : ZFSet.{u}) = numeral 1)) fun x =>
    extend (extend (extend (extend (extend (extend Fin.elim0 (objectSetConsts h numN))
      (numeral 0)) pathMotive) {∅}) (numeral 1)) x 2)) ∅ = {∅} at same
  rw [traceApp_graph_outside _ (fun member => zeroOne ((mem_truthCode _ _).mp member).2)] at same
  exact empty_ne_true same

/-! ## A wrong decoder -/

/-- **A wrong decoder**: every code holds. -/
noncomputable def trueDecoder : ZFSet.{u} :=
  telescopeGraph (objHeads h) (objectSetConsts h) propTele fun _ => {∅}

/-- The constants with the wrong decoder. -/
noncomputable def trueDecoderConsts : DeclName → ZFSet.{u} :=
  Function.update (objectSetConsts h) holdsN (trueDecoder h)

/-- **Negative: a decoder reading every code as true fails the decoding of an equation**:
`holds (eq@num 0 1)` would be true, while `Id num 0 1` is false. -/
theorem trueDecoder_fails :
    ¬ SchemaValid (objHeads h) (trueDecoderConsts h) objectDecls
      (eqLeft SetProfile.numTy) (eqRight SetProfile.numTy) := by
  intro valid
  have zeroOne : (numeral 0 : ZFSet.{u}) ≠ numeral 1 := fun same =>
    absurd (numeral_injective same) (by decide)
  have hnum : trueDecoderConsts h numN = ZFSet.omega := by
    rw [trueDecoderConsts, Function.update_of_ne (by decide), setConst_num h]
  have s₁ : (numeral 0 : ZFSet.{u}) ∈ trueDecoderConsts h numN := by
    rw [hnum]
    exact numeral_mem_omega 0
  have s₂ : (numeral 1 : ZFSet.{u}) ∈ trueDecoderConsts h numN := by
    rw [hnum]
    exact numeral_mem_omega 1
  have sat : Sat (objHeads h) (trueDecoderConsts h)
      (liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 SetProfile.numTy))
        (typeAt SetProfile.types 1 SetProfile.numTy)))
      (extend (extend Fin.elim0 (numeral 0)) (numeral 1)) :=
    (sat_snoc _ _).mpr ⟨(sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, s₁⟩, s₂⟩
  have equal := valid _ (typedInstance_of_sat (eq_knowledge SetProfile.numTy)
    (eq_equations SetProfile.numTy) sat)
  rw [elabLeft_firstOrder objectDecls rfl, eq_elabRight] at equal
  change traceApp (trueDecoderConsts h holdsN)
      (traceApp (traceApp (trueDecoderConsts h (SetProfile.eqName SetProfile.numTy)) (numeral 0))
        (numeral 1)) = truthCode ((numeral 0 : ZFSet.{u}) = numeral 1) at equal
  have code : traceApp (traceApp (trueDecoderConsts h (SetProfile.eqName SetProfile.numTy))
      (numeral 0)) (numeral 1) = truthCode ((numeral 0 : ZFSet.{u}) = numeral 1) := by
    rw [trueDecoderConsts, Function.update_of_ne (by decide)]
    exact eq_apply h SetProfile.numTy (numeral_mem_omega 0) (numeral_mem_omega 1)
  have decoded : traceApp (trueDecoderConsts h holdsN)
      (truthCode ((numeral 0 : ZFSet.{u}) = numeral 1)) = {∅} := by
    rw [trueDecoderConsts, Function.update_self, trueDecoder]
    show traceApp (traceLam (graph (objectSetConsts h propN) fun _ => {∅})) _ = _
    rw [setConst_prop h]
    exact traceApp_graph_beta _ (Square.truthCode_mem_omega _)
  rw [code, decoded] at equal
  have false : truthCode ((numeral 0 : ZFSet.{u}) = numeral 1) = ∅ := by
    apply ZFSet.ext
    intro z
    simp only [mem_truthCode, ZFSet.notMem_empty, iff_false, not_and]
    exact fun _ same => zeroOne same
  rw [false] at equal
  exact empty_ne_true equal.symm

/-! ## A wrong definition -/

/-- **A wrong value for `eqAt`**: false at every number. -/
noncomputable def falseEqAt : ZFSet.{u} :=
  telescopeGraph (objHeads h) (objectSetConsts h) numTele fun _ => ∅

/-- The constants with the wrong `eqAt`. -/
noncomputable def falseEqAtConsts : DeclName → ZFSet.{u} :=
  Function.update (objectSetConsts h) eqAtName (falseEqAt h)

/-- **Negative: a value for `eqAt` that is not the traced graph of its right side fails its
defining step**: at zero it gives false, where `add zero zero = zero` is true. -/
theorem falseEqAt_fails :
    ¬ SchemaValid (objHeads h) (falseEqAtConsts h) objectDecls
      (applyClosed eqAtTele Presentation.ids (.const eqAtName)) eqAtRhs := by
  intro valid
  have hnum : falseEqAtConsts h numN = ZFSet.omega := by
    rw [falseEqAtConsts, Function.update_of_ne (by decide), setConst_num h]
  have s₁ : (numeral 0 : ZFSet.{u}) ∈ falseEqAtConsts h numN := by
    rw [hnum]
    exact numeral_mem_omega 0
  have sat : Sat (objHeads h) (falseEqAtConsts h) (liftCtx eqAtTele)
      (extend Fin.elim0 (numeral 0)) :=
    (sat_snoc _ _).mpr ⟨sat_nil _ _ Fin.elim0, s₁⟩
  have equal := valid _ (typedInstance_of_sat eqAt_knowledge eqAt_equations sat)
  rw [elabLeft_firstOrder objectDecls (firstOrder_applyClosed eqAtTele eqAtName fun _ => rfl)]
    at equal
  change traceApp (falseEqAtConsts h eqAtName) (numeral 0) =
    ev (objHeads h) (falseEqAtConsts h) (defRhs eqAtName eqAtTele eqAtRhs)
      (extend Fin.elim0 (numeral 0)) at equal
  rw [defRhs_eqAt] at equal
  change traceApp (falseEqAtConsts h eqAtName) (numeral 0) =
    truthCode (traceApp (traceApp (falseEqAtConsts h addN) (falseEqAtConsts h zeroN)) (numeral 0) =
      numeral 0) at equal
  have left : traceApp (falseEqAtConsts h eqAtName) (numeral 0) = ∅ := by
    rw [falseEqAtConsts, Function.update_self, falseEqAt]
    show traceApp (traceLam (graph (objectSetConsts h numN) fun _ => ∅)) _ = _
    rw [setConst_num h]
    exact traceApp_graph_beta _ (numeral_mem_omega 0)
  have sum : traceApp (traceApp (falseEqAtConsts h addN) (falseEqAtConsts h zeroN)) (numeral 0) =
      numeral 0 := by
    rw [falseEqAtConsts, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    exact zeroAdd_apply h (numeral_mem_omega 0)
  rw [left, sum] at equal
  have true : (∅ : ZFSet.{u}) ∈ truthCode ((numeral 0 : ZFSet.{u}) = numeral 0) :=
    empty_mem_truthCode_eq _
  rw [← equal] at true
  exact ZFSet.notMem_empty _ true

end Wrong

/-! ## The sets and the codes -/

section Readings

variable (h : CofinalInaccessibles.{u})

theorem empty_mem_finiteSets : (∅ : ZFSet.{u}) ∈ finiteSets :=
  ZFSet.mem_vonNeumann.mpr (by rw [ZFSet.rank_empty]; exact Ordinal.omega0_pos)

/-- **Nothing degenerate about the sets: `Power` is the power set**, so it sends `∅` to a set
with the member `∅`, and it is not the identity. -/
theorem power_empty :
    (∅ : ZFSet.{u}) ∈ traceApp (objectSetConsts h powerN) ∅ ∧
      traceApp (objectSetConsts h powerN) ∅ ≠ ∅ := by
  rw [power_apply h empty_mem_finiteSets]
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  refine ⟨member, fun same => ?_⟩
  rw [same] at member
  exact ZFSet.notMem_empty _ member

/-- The identity on truth values, a code-valued function of codes. -/
noncomputable def truthIdentity : ZFSet.{u} := traceLam (graph Square.omega fun p => p)

/-- **A false code: the quantification of every truth value decodes to the empty set**, the
false truth value is a truth value without proof. -/
theorem falsum_code_empty :
    traceApp (objectSetConsts h holdsN)
      (traceApp (objectSetConsts h (SetProfile.allName .prop)) truthIdentity) = ∅ := by
  have identity : truthIdentity.{u} ∈ simpleSet (.arr .prop .prop) :=
    traceLam_graph_mem fun _ hp => hp
  rw [all_apply h .prop identity, holds_apply h (Square.truthCode_mem_omega _)]
  apply ZFSet.ext
  intro z
  simp only [mem_truthCode, ZFSet.notMem_empty, iff_false, not_and]
  intro _ all
  have atFalse := all ∅ empty_mem_truthValues
  rw [truthIdentity, traceApp_graph_beta _ empty_mem_truthValues] at atFalse
  exact ZFSet.notMem_empty _ atFalse

end Readings

/-! ## Assignments that agree on the names of the package -/

section Agreement

variable (h : CofinalInaccessibles.{u})

/-- Positive: **the value of a name the package does not declare is free.** Whatever set an
extension gives to a new name, the object package keeps its model. -/
theorem objectSetModel_update {fresh : DeclName} (undeclared : objectDeclared fresh = false)
    (x : ZFSet.{u}) :
    SetModel (objHeads h) (Function.update (objectSetConsts h) fresh x) objectChurch :=
  objectSetModel_agreeing h fun c declared => by
    have other : c ≠ fresh := fun same => by
      rw [same, undeclared] at declared
      exact nomatch declared
    rw [Function.update_of_ne other]

/-- Negative: **the value of a declared name is not free.** With the set of numbers empty,
`zero` has no value in its type. -/
theorem no_setModel_of_empty_numbers :
    ¬ SetModel (objHeads h) (Function.update (objectSetConsts h) numN ∅) objectChurch := by
  intro model
  have declared : objectChurch.constantType zeroN = some cnum :=
    objectChurch_declared (c := zeroN) (T := Package.numT) (by decide) rfl
  have member := model.constants declared
  have numbers : ev (objHeads h) (Function.update (objectSetConsts h) numN ∅)
      (cnum : CTm Tower.Head 0) Fin.elim0 = ∅ := by
    show Function.update (objectSetConsts h) numN ∅ numN = ∅
    rw [Function.update_self]
  rw [numbers] at member
  exact ZFSet.notMem_empty _ member

end Agreement

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
