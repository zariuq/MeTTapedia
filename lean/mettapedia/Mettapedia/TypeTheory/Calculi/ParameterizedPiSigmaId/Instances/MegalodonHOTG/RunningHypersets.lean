import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Hypersets

/-!
# A running stream keeps its hyperset value

The stream `from n = cons n (from (n + 1))` is a running term. One step of its running
relation unfolds the call into that cons. The hyperset value does not change
(`runStep_keeps_value`). The labelled transition of the term is the head and the tail
reached by that running: `from n` emits `n` and continues at `from (n + 1)`
(`from_emits`), and the value is the pair of that label with the value of the tail
(`emits_spec`).

That value is the hyperset of the labelled stream `n, n + 1, …` (`runValue_from_stream`).
On the lifted numbers, the same program is a deterministic labelled graph (`fromTrace`).
`solveLabelled` at `n` is the code of this value (`from_solveLabelledValue`), and the stream
package's `numbersFromSet n`, read positionwise as the code of the hyperset of the numeral
it holds, is the stream of label codes (`from_label_matches_numbers`).

The same running grammar works for labels drawn from any type that has a reading in the
hyperset universe (`labelStep_keeps_value`, `labelRun_isStream`). The reading is a
hypothesis there, so two readings can be compared: readings that agree on the labels a
program emits give one value (`labelValue_agree`), and a reading that identifies two
emitted labels collapses two programs (`distinct_programs_collapse`). Every set of the
package supplies such a reading. The nodes of a set are small, and `labelOf` sends a node
to the hyperset of its lower set (`setRun_keeps`, `setRun_isStream`).

The numerals are that instance. `runStep_keeps_value` and `runTerm_isStream` are the
reading `readNumber`. On the lifted numbers, `labelOf` agrees with `readNumber`
(`numeral_node_reading`), and the value of a numeral program is the value of its node
program (`runValue_setLabel`). The value of `iter` at successor, on a numeral, is the
stream package's `numbersFromSet`, and that running term lands in the same class
(`iter_constant_lands`). The value of `scons` of a numeral in front of that stream does
too (`scons_constant_lands`).

The unguarded equation `spin = spin` emits no label. Its running stays at `spin`
(`spin_reaches_spin`), and no deterministic labelled step exists when the label sort is
empty (`spin_no_deterministic_reading`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HSet
open ZFSetUniverseClosure (Closed CofinalInaccessibles univOf univOf_closed mem_univOf)
open ZFSetUniverseLift (carrierCode mem_carrierCode lift lift_mem_lift lift_empty lift_singleton
  lift_unorderedPair lowerValue lift_lowerValue lowerValue_lift carrierCode_transitive
  univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet)
open ZFSetDependentProducts (graph graph_congr)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta traceApp_empty)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)

universe u

/-! ## Running over any labels -/

section AnyLabels

variable {β : Type u}

/-- The positions of an endofunction, from a start label. -/
def iterated (step : β → β) (start : β) : ℕ → β
  | 0 => start
  | k + 1 => step (iterated step start k)

theorem iterated_zero (step : β → β) (start : β) : iterated step start 0 = start := rfl

theorem iterated_succ (step : β → β) (start : β) (k : ℕ) :
    iterated step start (k + 1) = step (iterated step start k) := rfl

theorem iterated_shift (step : β → β) (start : β) :
    ∀ k, iterated step (step start) k = iterated step start (k + 1)
  | 0 => rfl
  | k + 1 => by
      rw [iterated_succ, iterated_succ]
      exact congrArg step (iterated_shift step start k)

theorem iterated_const {b : β} (k : ℕ) : iterated (fun _ => b) b k = b := by
  cases k <;> rfl

/-- A running stream over labels `β`. `iterate start step` unfolds to
`cons start (iterate (step start) step)`. -/
inductive LabelRun (β : Type u) where
  | iterate (start : β) (step : β → β)
  | cons (head : β) (tail : LabelRun β)

/-- One step of running over labels. -/
inductive LabelStep : LabelRun β → LabelRun β → Prop where
  | unfold (start : β) (step : β → β) :
      LabelStep (.iterate start step) (.cons start (.iterate (step start) step))
  | under {a : β} {t u : LabelRun β} : LabelStep t u → LabelStep (.cons a t) (.cons a u)

/-- The hyperset value of a running stream, through a reading of its labels. -/
noncomputable def labelValue (ℓ : β → HSet.{u}) : LabelRun β → HSet.{u}
  | .iterate start step => streamOf ℓ (iterated step start)
  | .cons head tail => {kpair (ℓ head) (labelValue ℓ tail)}

/-- **A step of running keeps the hyperset value, for any reading of the labels.** -/
theorem labelStep_keeps_value {ℓ : β → HSet.{u}} {t u : LabelRun β} (h : LabelStep t u) :
    labelValue ℓ t = labelValue ℓ u := by
  induction h with
  | unfold start step =>
      have h0 : iterated step start 0 = start := iterated_zero step start
      have hrest : (fun n => iterated step start (n + 1)) = iterated step (step start) :=
        funext fun n => (iterated_shift step start n).symm
      simp only [labelValue]
      rw [streamOf_cons, h0, hrest]
  | under _ ih =>
      dsimp [labelValue]
      rw [ih]

/-- The value of a running stream is the stream of its label sequence. -/
theorem labelValue_streamOf (ℓ : β → HSet.{u}) (t : LabelRun β) :
    ∃ σ : ℕ → β, labelValue ℓ t = streamOf ℓ σ := by
  induction t with
  | iterate start step =>
      exact ⟨iterated step start, rfl⟩
  | cons head _ ih =>
      obtain ⟨σ, hσ⟩ := ih
      let τ : ℕ → β := fun k => if k = 0 then head else σ (k - 1)
      refine ⟨τ, ?_⟩
      have h0 : τ 0 = head := by simp [τ]
      have hrest : (fun k => τ (k + 1)) = σ := by
        funext k
        simp [τ]
      rw [labelValue, hσ, ← h0, ← hrest]
      exact (streamOf_cons τ).symm

/-- **Every closed running stream lands in the one-successor hypersets of its reading.** -/
theorem labelRun_isStream (ℓ : β → HSet.{u}) (t : LabelRun β) :
    IsStream ℓ (labelValue ℓ t) := by
  obtain ⟨σ, hσ⟩ := labelValue_streamOf ℓ t
  exact isStream_iff.mpr ⟨σ, hσ.symm⟩

/-- A label occurs on the stream a program emits. -/
def emitsLabel : LabelRun β → β → Prop
  | .iterate start step, b => ∃ k, iterated step start k = b
  | .cons head tail, b => b = head ∨ emitsLabel tail b

/-- **Readings that agree on the emitted labels give one value.** -/
theorem labelValue_agree {ℓ ℓ' : β → HSet.{u}} {t : LabelRun β}
    (agree : ∀ b, emitsLabel t b → ℓ b = ℓ' b) : labelValue ℓ t = labelValue ℓ' t := by
  induction t with
  | iterate start step =>
      simp only [labelValue]
      rw [streamOf, streamOf, decorateLabelled_eq_iff_comp_labels
        (deterministic_positionRel _) (deterministic_positionRel _)]
      rw [labels_positionRel]
      funext k
      simp only [Function.comp_apply, Nat.zero_add]
      exact agree _ ⟨k, rfl⟩
  | cons head tail ih =>
      simp only [labelValue]
      rw [agree head (Or.inl rfl), ih fun b hb => agree b (Or.inr hb)]

/-- The stream that emits `false` once and then `true`, and the stream of `true`. -/
def fromFalse : LabelRun (ULift.{u} Bool) :=
  .iterate ⟨false⟩ fun _ => ⟨true⟩

def fromTrue : LabelRun (ULift.{u} Bool) :=
  .iterate ⟨true⟩ fun _ => ⟨true⟩

/-- A reading of `Bool` that keeps the two bits apart. -/
def separateBool (b : ULift.{u} Bool) : HSet.{u} :=
  if b.down then numeralLabel 1 else numeralLabel 0

/-- A reading of `Bool` that sends both bits to one numeral. -/
def collapseBool : ULift.{u} Bool → HSet.{u} :=
  fun _ => numeralLabel 0

/-- **A reading that identifies two emitted labels collapses two programs.** The
programs differ, an injective reading of the bits keeps their values apart, and
the constant reading gives them one value. -/
theorem distinct_programs_collapse :
    fromFalse.{u} ≠ fromTrue.{u} ∧
      labelValue separateBool fromFalse ≠ labelValue separateBool fromTrue ∧
        labelValue collapseBool fromFalse = labelValue collapseBool fromTrue := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hstart := (LabelRun.iterate.inj h).1
    have : (false : Bool) = true := congrArg ULift.down hstart
    cases this
  · intro h
    have hseq := streamOf_eq_streamOf_iff.mp (by simpa [labelValue, fromFalse, fromTrue] using h)
    have h0 := congrFun hseq 0
    dsimp [iterated, separateBool] at h0
    exact absurd (numeralLabel_injective h0) (by decide : (0 : ℕ) ≠ 1)
  · simp only [fromFalse, fromTrue, labelValue]
    rw [streamOf_eq_streamOf_iff]
    funext _
    rfl

/-- The stream that emits only `true`. -/
def holdTrue : LabelRun (ULift.{u} Bool) :=
  .iterate ⟨true⟩ fun _ => ⟨true⟩

/-- `true` is read as the numeral `1`. `false` is read as `other`. -/
def bitRead (other : ℕ) (b : ULift.{u} Bool) : HSet.{u} :=
  if b.down then numeralLabel 1 else numeralLabel other

/-- **Only the emitted labels matter.** `holdTrue` emits `true`. Two readings that
agree on `true` and differ on `false` give it one value. -/
theorem emitted_reading_agree :
    (∀ b : ULift.{u} Bool, emitsLabel holdTrue.{u} b → bitRead.{u} 0 b = bitRead.{u} 2 b) ∧
      labelValue (bitRead.{u} 0) holdTrue.{u} = labelValue (bitRead.{u} 2) holdTrue.{u} ∧
        bitRead.{u} 0 (⟨false⟩ : ULift.{u} Bool) ≠ bitRead.{u} 2 ⟨false⟩ := by
  have agree : ∀ b : ULift.{u} Bool,
      emitsLabel holdTrue.{u} b → bitRead.{u} 0 b = bitRead.{u} 2 b := by
    intro b ⟨k, hk⟩
    have hb : b = ⟨true⟩ := by
      simpa [holdTrue, iterated_const] using hk.symm
    subst hb
    simp [bitRead]
  refine ⟨agree, labelValue_agree (β := ULift.{u} Bool) (t := holdTrue.{u}) agree, ?_⟩
  intro h
  have := numeralLabel_injective (by simpa [bitRead] using h)
  exact absurd this (by decide : (0 : ℕ) ≠ 2)

/-- **The package constructs the reading.** The nodes of any set of the next
universe are small, and `labelOf` sends each node to the hyperset of its lower
set. A step keeps that value. -/
theorem setRun_keeps {B : ZFSet.{u + 1}} {t u : LabelRun (nodeSetOf B)} (h : LabelStep t u) :
    labelValue (labelOf B) t = labelValue (labelOf B) u :=
  labelStep_keeps_value h

/-- A running stream over the nodes of any set lands in the one-successor hypersets
of `labelOf`. -/
theorem setRun_isStream {B : ZFSet.{u + 1}} (t : LabelRun (nodeSetOf B)) :
    IsStream (labelOf B) (labelValue (labelOf B) t) :=
  labelRun_isStream (labelOf B) t

end AnyLabels

/-! ## The running term -/

/-- A closed stream program: the numbers from `n` on, or a number in front of a program. -/
inductive RunTerm where
  | numbersFrom (n : ℕ)
  | cons (head : ℕ) (tail : RunTerm)

/-- One step of running. `from n` unfolds to `cons n (from (n + 1))`, and a step under a
number in front is a step of the tail. -/
inductive RunStep : RunTerm → RunTerm → Prop where
  | unfold (n : ℕ) : RunStep (.numbersFrom n) (.cons n (.numbersFrom (n + 1)))
  | under {n : ℕ} {t u : RunTerm} : RunStep t u → RunStep (.cons n t) (.cons n u)

/-- The hyperset value of a running term. `from n` is the stream of the numerals from `n`. -/
noncomputable def runValue : RunTerm → HSet.{u}
  | .numbersFrom n => fromStream n
  | .cons n t => {kpair (numeralLabel n) (runValue t)}

/-- The numeral program as a running stream over `ULift ℕ`, stepped by successor. -/
def toLabel : RunTerm → LabelRun (ULift.{u} ℕ)
  | .numbersFrom n => .iterate ⟨n⟩ fun b => ⟨b.down + 1⟩
  | .cons n t => .cons ⟨n⟩ (toLabel t)

theorem iterated_numeral (n : ℕ) : ∀ k,
    iterated (fun b : ULift.{u} ℕ => ⟨b.down + 1⟩) ⟨n⟩ k = ⟨n + k⟩
  | 0 => by simp [iterated]
  | k + 1 => by
      rw [iterated_succ, iterated_numeral n k]
      apply ULift.ext
      dsimp
      omega

theorem toLabel_step {t t' : RunTerm} (h : RunStep t t') :
    LabelStep (toLabel t) (toLabel t') := by
  induction h with
  | unfold n =>
      dsimp [toLabel]
      apply LabelStep.unfold
  | under _ ih =>
      dsimp [toLabel]
      exact LabelStep.under ih

theorem runValue_toLabel (t : RunTerm) : runValue t = labelValue readNumber (toLabel t) := by
  induction t with
  | numbersFrom n =>
      simp only [runValue, toLabel, labelValue]
      rw [fromStream_eq_streamOf]
      congr 1
      funext k
      exact (iterated_numeral n k).symm
  | cons n _ ih =>
      simp only [runValue, toLabel, labelValue, readNumber]
      rw [ih]

/-- **A step of running keeps the hyperset value.** The numerals are the instance
of `labelStep_keeps_value` read by `readNumber`. -/
theorem runStep_keeps_value {t u : RunTerm} (h : RunStep t u) : runValue t = runValue u := by
  rw [runValue_toLabel, runValue_toLabel]
  exact labelStep_keeps_value (toLabel_step h)

/-- Running for any number of steps keeps the hyperset value. -/
theorem runStar_keeps_value {t u : RunTerm} (h : Relation.ReflTransGen RunStep t u) :
    runValue t = runValue u := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (runStep_keeps_value step)

/-- A term exposes a head when it is a number in front of a continuation. -/
def Exposes (t : RunTerm) (b : ℕ) (u : RunTerm) : Prop :=
  t = .cons b u

/-- The labelled transition of a running term: running reaches a head, the label is that
head, and the successor is the tail. -/
def Emits (t : RunTerm) (b : ℕ) (u : RunTerm) : Prop :=
  ∃ s, Relation.ReflTransGen RunStep t s ∧ Exposes s b u

/-- **`from n` emits `n` and continues at `from (n + 1)`**, by one step of running. -/
theorem from_emits (n : ℕ) : Emits (.numbersFrom n) n (.numbersFrom (n + 1)) :=
  ⟨.cons n (.numbersFrom (n + 1)), Relation.ReflTransGen.single (RunStep.unfold n), rfl⟩

/-- A number already in front emits that number, with no step. -/
theorem cons_emits (n : ℕ) (t : RunTerm) : Emits (.cons n t) n t :=
  ⟨.cons n t, Relation.ReflTransGen.refl, rfl⟩

/-- The value of a term that emits `b` and continues at `u` is the pair of `b` with the value
of `u`. -/
theorem emits_spec {t : RunTerm} {b : ℕ} {u : RunTerm} (h : Emits t b u) :
    runValue t = {kpair (numeralLabel b) (runValue u)} := by
  obtain ⟨s, hs, hscons⟩ := h
  rw [runStar_keeps_value hs, hscons]
  rfl

/-- **The value of `from n` is the hyperset of `n, n + 1, …`.** -/
theorem runValue_from_stream (n : ℕ) :
    runValue (.numbersFrom n) = streamOf readNumber fun k => ⟨n + k⟩ := by
  simpa [runValue] using fromStream_eq_streamOf n

/-- Every closed running term is a one-successor hyperset over the numerals. -/
theorem runValue_streamOf (t : RunTerm) :
    ∃ σ : ℕ → ULift.{u} ℕ, runValue t = streamOf readNumber σ := by
  rw [runValue_toLabel]
  exact labelValue_streamOf readNumber (toLabel t)

/-- **The numeral programs land in the one-successor hypersets over the numerals.**
This is `labelRun_isStream` at `readNumber`. -/
theorem runTerm_isStream (t : RunTerm) : IsStream readNumber (runValue t) := by
  rw [runValue_toLabel]
  exact labelRun_isStream readNumber (toLabel t)

/-! ## The same program as a labelled graph, and the stream package -/

/-- The nodes of `from`: the lifted natural numbers. -/
def numberNodes : ZFSet.{u + 1} :=
  lift ZFSet.omega

theorem numberNodes_carrier : numberNodes.{u} ∈ carrierCode.{u} :=
  mem_carrierCode.mpr ⟨ZFSet.omega, rfl⟩

theorem numeral_lift_mem (k : ℕ) : lift (numeral k) ∈ numberNodes := by
  rw [numberNodes, lift_mem_lift]
  exact numeral_mem_omega k

/-- The small node of the numeral `k`. -/
noncomputable def nodeNumeral (k : ℕ) : nodeSetOf numberNodes :=
  nodeOfMember numberNodes_carrier (numeral_lift_mem k)

/-- The natural a small node names. -/
noncomputable def nodeIndex (i : nodeSetOf numberNodes) : ℕ :=
  natOf (lowerValue (upperNode numberNodes i))

theorem lower_upper (i : nodeSetOf numberNodes) :
    lowerValue (upperNode numberNodes i) = numeral (nodeIndex i) := by
  have hi := upperNode_mem numberNodes_carrier i
  have hc : upperNode numberNodes i ∈ carrierCode :=
    carrierCode_transitive numberNodes numberNodes_carrier hi
  have hω : lowerValue (upperNode numberNodes i) ∈ ZFSet.omega := by
    rw [← lift_mem_lift, lift_lowerValue hc]
    simpa [numberNodes] using hi
  exact (numeral_natOf hω).symm

theorem nodeIndex_numeral (k : ℕ) : nodeIndex (nodeNumeral k) = k := by
  unfold nodeIndex nodeNumeral
  rw [upperNode_nodeOfMember numberNodes_carrier (numeral_lift_mem k), lowerValue_lift,
    natOf_numeral]

theorem upper_inj {i j : nodeSetOf numberNodes}
    (h : lowerValue (upperNode numberNodes i) = lowerValue (upperNode numberNodes j)) :
    i = j := by
  have hi := upperNode_mem numberNodes_carrier i
  have hj := upperNode_mem numberNodes_carrier j
  have hci : upperNode numberNodes i ∈ carrierCode :=
    carrierCode_transitive numberNodes numberNodes_carrier hi
  have hcj : upperNode numberNodes j ∈ carrierCode :=
    carrierCode_transitive numberNodes numberNodes_carrier hj
  have same : upperNode numberNodes i = upperNode numberNodes j := by
    rw [← lift_lowerValue hci, ← lift_lowerValue hcj, h]
  have hleft := nodeOfMember_upperNode numberNodes_carrier i
  have hright := nodeOfMember_upperNode numberNodes_carrier j
  have sameNode :
      nodeOfMember numberNodes_carrier (upperNode_mem numberNodes_carrier i) =
        nodeOfMember numberNodes_carrier (upperNode_mem numberNodes_carrier j) := by
    unfold nodeOfMember
    congr 1
    exact Subtype.ext (congrArg lowerValue same)
  exact (hleft.symm.trans sameNode).trans hright

theorem index_inj {i j : nodeSetOf numberNodes} (h : nodeIndex i = nodeIndex j) : i = j :=
  upper_inj (by rw [lower_upper, lower_upper, h])

/-- The trace relation of `from`: from the numeral `m`, the label `m`, to `m + 1`. -/
noncomputable def fromTrace : ZFSet.{u + 1} :=
  traceLam (graph numberNodes fun a =>
    traceLam (graph numberNodes fun b =>
      traceLam (graph numberNodes fun c =>
        truthCode.{u + 1} (lowerValue b = lowerValue a ∧
          lowerValue c = insert (lowerValue a) (lowerValue a)))))

theorem fromTrace_mem :
    fromTrace ∈ tracePiSet numberNodes fun _ =>
      tracePiSet numberNodes fun _ =>
        tracePiSet numberNodes fun _ => truthValues.{u + 1} := by
  unfold fromTrace
  exact traceLam_graph_mem fun _ _ => traceLam_graph_mem fun _ _ =>
    traceLam_graph_mem fun _ _ => truthCode_mem_truthValues _

theorem from_labelRel_edge (i j k : nodeSetOf numberNodes) :
    labelRel numberNodes numberNodes fromTrace i j k ↔
      lowerValue (upperNode numberNodes j) = lowerValue (upperNode numberNodes i) ∧
        lowerValue (upperNode numberNodes k) =
          insert (lowerValue (upperNode numberNodes i))
            (lowerValue (upperNode numberNodes i)) := by
  unfold labelRel fromTrace
  rw [traceApp_graph_beta _ (upperNode_mem numberNodes_carrier i),
    traceApp_graph_beta _ (upperNode_mem numberNodes_carrier j),
    traceApp_graph_beta _ (upperNode_mem numberNodes_carrier k), mem_truthCode]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨rfl, h⟩

theorem from_labelRel_index (i j k : nodeSetOf numberNodes) :
    labelRel numberNodes numberNodes fromTrace i j k ↔
      nodeIndex j = nodeIndex i ∧ nodeIndex k = nodeIndex i + 1 := by
  rw [from_labelRel_edge]
  constructor
  · rintro ⟨hj, hk⟩
    have hj' : numeral (nodeIndex j) = numeral (nodeIndex i) := by
      rw [← lower_upper j, ← lower_upper i, hj]
    have hk' : numeral (nodeIndex k) = numeral (nodeIndex i + 1) := by
      rw [← lower_upper k, numeral_succ, ← lower_upper i, hk]
    exact ⟨numeral_injective hj', numeral_injective hk'⟩
  · intro h
    refine ⟨?_, ?_⟩
    · rw [lower_upper, lower_upper, h.1]
    · rw [lower_upper, lower_upper, h.2, numeral_succ]

/-- The graph of `from` has exactly one edge out of every node. -/
theorem deterministic_fromLabel :
    Deterministic (labelRel numberNodes numberNodes fromTrace) := by
  intro i
  refine ⟨(nodeNumeral (nodeIndex i), nodeNumeral (nodeIndex i + 1)), ?_, ?_⟩
  · show labelRel numberNodes numberNodes fromTrace i (nodeNumeral (nodeIndex i))
      (nodeNumeral (nodeIndex i + 1))
    rw [from_labelRel_index, nodeIndex_numeral, nodeIndex_numeral]
    exact ⟨rfl, rfl⟩
  · rintro ⟨j, k⟩ hrjk
    have h := (from_labelRel_index i j k).mp hrjk
    exact Prod.ext
      (index_inj (h.1.trans (nodeIndex_numeral (nodeIndex i)).symm))
      (index_inj (h.2.trans (nodeIndex_numeral _).symm))

theorem from_label_holds (k : ℕ) :
    labelRel numberNodes numberNodes fromTrace (nodeNumeral k) (nodeNumeral k)
      (nodeNumeral (k + 1)) := by
  rw [from_labelRel_index, nodeIndex_numeral, nodeIndex_numeral]
  exact ⟨rfl, rfl⟩

/-- The label sequence of `from n` on the lifted numbers is `k ↦ n + k`. -/
theorem labels_fromLabel (n : ℕ) :
    deterministic_fromLabel.labels (nodeNumeral n) = fun k => nodeNumeral (n + k) := by
  have h := deterministic_fromLabel.eq_of_path (a := nodeNumeral n)
    (p := fun k => nodeNumeral (n + k)) (σ := fun k => nodeNumeral (n + k)) rfl
    (fun k => by
      have step := from_label_holds (n + k)
      rw [show (n + k) + 1 = n + (k + 1) by omega] at step
      exact step)
  exact h.2.symm

theorem labelOf_nodeNumeral (k : ℕ) :
    labelOf numberNodes (nodeNumeral k) = numeralLabel k := by
  unfold labelOf numeralLabel nodeNumeral
  rw [upperNode_nodeOfMember numberNodes_carrier (numeral_lift_mem k), lowerValue_lift,
    mk_ofNat]

/-- On the lifted numbers, `labelOf` is `readNumber`. -/
theorem numeral_node_reading (k : ℕ) :
    labelOf numberNodes (nodeNumeral k) = readNumber (⟨k⟩ : ULift.{u} ℕ) := by
  rw [labelOf_nodeNumeral, readNumber]

/-- The numeral program as a running stream over the nodes of `lift ω`. -/
noncomputable def toNode : RunTerm → LabelRun (nodeSetOf numberNodes)
  | .numbersFrom n => .iterate (nodeNumeral n) fun i => nodeNumeral (nodeIndex i + 1)
  | .cons n t => .cons (nodeNumeral n) (toNode t)

theorem iterated_node (n : ℕ) : ∀ k,
    iterated (fun i : nodeSetOf numberNodes => nodeNumeral (nodeIndex i + 1))
        (nodeNumeral n) k =
      nodeNumeral (n + k)
  | 0 => by simp [iterated]
  | k + 1 => by
      rw [iterated_succ, iterated_node n k, nodeIndex_numeral]
      exact congrArg nodeNumeral (by omega)

theorem node_stream_readNumber (n : ℕ) :
    streamOf (labelOf numberNodes) (fun k => nodeNumeral (n + k)) =
      streamOf readNumber (fun k => (⟨n + k⟩ : ULift.{u} ℕ)) := by
  rw [streamOf, streamOf, decorateLabelled_eq_iff_comp_labels
      (deterministic_positionRel _) (deterministic_positionRel _)]
  rw [labels_positionRel, labels_positionRel]
  funext k
  simp only [Function.comp_apply, Nat.zero_add, numeral_node_reading]

/-- **The numeral value is the package reading of the node program.** -/
theorem runValue_setLabel (t : RunTerm) :
    runValue t = labelValue (labelOf numberNodes) (toNode t) := by
  induction t with
  | numbersFrom n =>
      simp only [runValue, toNode, labelValue]
      rw [fromStream_eq_streamOf]
      have hseq :
          iterated (fun i : nodeSetOf numberNodes => nodeNumeral (nodeIndex i + 1))
              (nodeNumeral n) =
            fun k => nodeNumeral (n + k) :=
        funext (iterated_node n)
      rw [hseq, node_stream_readNumber]
  | cons n _ ih =>
      simp only [runValue, toNode, labelValue]
      rw [numeral_node_reading, readNumber, ih]

/-- The decoration of the lifted graph at `n` is `from n`. -/
theorem from_decorate (n : ℕ) :
    decorateLabelled (labelRel numberNodes numberNodes fromTrace) (labelOf numberNodes)
        (nodeNumeral n) =
      fromStream.{u} n := by
  unfold fromStream
  rw [decorateLabelled_eq_iff_comp_labels deterministic_fromLabel deterministic_fromRel,
    labels_fromLabel, labels_fromRel]
  funext k
  simp only [Function.comp_apply, labelOf_nodeNumeral, readNumber]

/-- **`solveLabelled` at `n` is the code of the value of `from n`.** -/
theorem from_solveLabelledCode (n : ℕ) :
    solveLabelledCode numberNodes numberNodes fromTrace (lift (numeral n)) =
      code (runValue (.numbersFrom n)) := by
  rw [solveLabelledCode_eq numberNodes_carrier numberNodes_carrier (numeral_lift_mem n)]
  exact congrArg code (from_decorate n)

theorem from_solveLabelledValue (n : ℕ) :
    traceApp (traceApp (traceApp (traceApp solveLabelledValue numberNodes) numberNodes) fromTrace)
        (lift (numeral n)) =
      code (runValue (.numbersFrom n)) := by
  rw [solveLabelledValue_apply numberNodes_carrier numberNodes_carrier fromTrace_mem
      (numeral_lift_mem n),
    from_solveLabelledCode]

/-- At position `k`, the stream of label codes holds the code of the hyperset of the numeral
the stream package holds at `k` in `numbersFromSet n`. -/
theorem from_label_matches_numbers (n k : ℕ) :
    traceApp (labelCodeStream deterministic_fromLabel (nodeNumeral n)) (numeral.{u + 1} k) =
      code (ofZFSet (traceApp (Streams.numbersFromSet n) (numeral k))) := by
  rw [labelCodeStream_numeral, labels_fromLabel, labelOf_nodeNumeral, Streams.numbersFromSet,
    traceApp_graph_beta _ (numeral_mem_omega k), natOf_numeral, numeralLabel, mk_ofNat]

/-! ## The stream constants, read on the numerals -/

/-- Successor on the natural numbers, as a set function. -/
noncomputable def succOnOmega : ZFSet.{u} :=
  traceLam (graph ZFSet.omega fun x => insert x x)

theorem succOnOmega_step {x : ZFSet.{u}} (hx : x ∈ ZFSet.omega) :
    traceApp succOnOmega x = insert x x := by
  rw [succOnOmega, traceApp_graph_beta _ hx]

theorem succOnOmega_endo : ∀ x ∈ ZFSet.omega, traceApp succOnOmega x ∈ ZFSet.omega :=
  fun x hx => by
    rw [succOnOmega_step hx]
    exact insert_mem_omega hx

theorem succOnOmega_pi : succOnOmega ∈ tracePiSet ZFSet.omega fun _ => ZFSet.omega := by
  rw [succOnOmega]
  exact traceLam_graph_mem fun x hx => insert_mem_omega hx

theorem iterate_succ (n : ℕ) : ∀ k, Streams.iterate succOnOmega (numeral n) k = numeral (n + k)
  | 0 => by simp [Streams.iterate]
  | k + 1 => by
      rw [Streams.iterate, iterate_succ n k, succOnOmega_step (numeral_mem_omega (n + k))]
      rw [show n + (k + 1) = (n + k) + 1 by omega, ← numeral_succ]

theorem iterSet_succ_eq_numbers (n : ℕ) :
    Streams.iterSet succOnOmega (numeral n) = Streams.numbersFromSet n := by
  have hmem := Streams.iterSet_mem succOnOmega_endo (numeral_mem_omega n)
  refine Streams.streams_ext hmem (Streams.numbersFromSet_mem n) fun k => ?_
  rw [Streams.observeSet_eq_app hmem, Streams.observe_numbersFromSet, Streams.iterSet,
    traceApp_graph_beta _ (numeral_mem_omega k), natOf_numeral, iterate_succ]

theorem omega_mem_powerset : ZFSet.omega ∈ ZFSet.powerset ZFSet.omega :=
  ZFSet.mem_powerset.mpr fun _ hx => hx

/-- **The value of `iter` at the successor, on a numeral, is the stream from that numeral, and
its hyperset is a one-successor hyperset over the numerals.** -/
theorem iter_constant_lands (n : ℕ) :
    traceApp (traceApp (traceApp (Streams.iterValue (ZFSet.powerset ZFSet.omega)) ZFSet.omega)
        succOnOmega) (numeral n) =
      Streams.numbersFromSet n ∧
      Streams.numbersFromSet n ∈ Streams.streamSet ZFSet.omega ∧
        IsStream readNumber (runValue (.numbersFrom n)) := by
  refine ⟨?_, Streams.numbersFromSet_mem n, runTerm_isStream _⟩
  rw [Streams.iterValue_at (ZFSet.powerset ZFSet.omega) omega_mem_powerset succOnOmega_pi
      (numeral_mem_omega n),
    iterSet_succ_eq_numbers]

/-- **The value of `scons` of a numeral in front of the numbers from `n` is a stream, and the
running term has its hyperset in the one-successor hypersets over the numerals.** -/
theorem scons_constant_lands (a n : ℕ) :
    Streams.sconsFromSet a n ∈ Streams.streamSet ZFSet.omega ∧
      IsStream readNumber (runValue (.cons a (.numbersFrom n))) :=
  ⟨Streams.sconsFromSet_mem a n, runTerm_isStream _⟩

/-! ## `spin = spin` emits no label -/

/-- The unguarded call. -/
inductive Unguarded where
  | spin

/-- The only step of `spin = spin` returns `spin`. -/
inductive UnguardedStep : Unguarded → Unguarded → Prop where
  | loop : UnguardedStep .spin .spin

theorem spin_steps : UnguardedStep .spin .spin :=
  .loop

/-- **Running `spin` stays at `spin`.** No step exposes a head, because the only term reached
is the call itself. -/
theorem spin_reaches_spin {s : Unguarded} (h : Relation.ReflTransGen UnguardedStep .spin s) :
    s = .spin := by
  induction h with
  | refl => rfl
  | tail _ step ih =>
      cases step
      exact ih

/-- No deterministic labelled step exists when there is no label to emit. -/
theorem spin_no_deterministic_reading :
    ¬ ∃ r : PUnit.{u + 1} → PEmpty.{u + 1} → PUnit.{u + 1} → Prop, Deterministic r := by
  rintro ⟨r, hr⟩
  obtain ⟨e, _⟩ := (hr PUnit.unit).exists
  exact e.1.elim

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
