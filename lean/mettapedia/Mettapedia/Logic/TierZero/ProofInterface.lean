import Mettapedia.Logic.TierZero.ChildBound
import Mettapedia.Logic.TierZero.Extension

/-!
# The hypotheses actually reached by a checked proof

The executable analysis follows the proof's child graph backwards from its
selected root. A hypothesis child contributes its index; a node child
contributes the interface already computed for that earlier node. Thus unused
hypotheses and valid but root-unreachable proof nodes contribute nothing.

`checkCB_interface` proves sufficiency: any target context that derives every
selected hypothesis also derives the checked goal. The analysis retains
hypothesis occurrences by index, including equal judgments at different
positions. It does not infer the free variables of judgments or discharge a
logical assumption merely because the conclusion omits it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.ProofInterface

open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.ChildBound

universe u v

variable {P : Presentation.{u}}

abbrev Used := Finset Nat

/-- The interface named by one child, given interfaces for earlier nodes. -/
def useOfKid (hypothesisCount : Nat) (done : List Used) : Kid → Option Used
  | .hyp index => if index < hypothesisCount then some {index} else none
  | .node index => done[index]?

def joinUses : List Used → Used
  | [] => ∅
  | used :: rest => used ∪ joinUses rest

/-- The union of the interfaces of a node's children. -/
def useOfKids (hypothesisCount : Nat) (done : List Used) (kids : List Kid) : Option Used :=
  (kids.mapM (useOfKid hypothesisCount done)).map joinUses

/-- Analyze every node in topological order. Rule names are irrelevant to
reachability; the checker separately establishes that every cited child is
valid and that every rule application succeeds. -/
def runUses {Rule : Type v} (hypothesisCount : Nat) :
    List Used → List (Rule × List Kid) → Option (List Used)
  | done, [] => some done
  | done, (_, kids) :: rest => do
      let used ← useOfKids hypothesisCount done kids
      runUses hypothesisCount (done ++ [used]) rest

/-- The interface reached from the proof's selected root. -/
def infer {Rule : Type v} (hypothesisCount : Nat)
    (proof : List (Rule × List Kid)) (root : Kid) : Option Used := do
  let done ← runUses hypothesisCount [] proof
  useOfKid hypothesisCount done root

def Bounded (hypothesisCount : Nat) (used : Used) : Prop :=
  ∀ index ∈ used, index < hypothesisCount

theorem joinUses_bounded (hypothesisCount : Nat) :
    ∀ uses : List Used, (∀ used ∈ uses, Bounded hypothesisCount used) →
      Bounded hypothesisCount (joinUses uses)
  | [], _ => by simp [Bounded, joinUses]
  | used :: uses, bounded => by
      intro index member
      rcases Finset.mem_union.mp member with here | later
      · exact bounded used List.mem_cons_self index here
      · exact joinUses_bounded hypothesisCount uses
          (fun next present => bounded next (List.mem_cons_of_mem _ present)) index later

theorem useOfKid_bounded {hypothesisCount : Nat} {done : List Used}
    (doneBounded : ∀ used ∈ done, Bounded hypothesisCount used)
    {kid : Kid} {used : Used} (found : useOfKid hypothesisCount done kid = some used) :
    Bounded hypothesisCount used := by
  cases kid with
  | hyp index =>
      by_cases within : index < hypothesisCount
      · simp only [useOfKid, within, ↓reduceIte, Option.some.injEq] at found
        subst used
        simpa [Bounded] using within
      · simp [useOfKid, within] at found
  | node index =>
      unfold useOfKid at found
      exact doneBounded used (List.mem_of_getElem? found)

theorem exists_of_mem_mapM {α β : Type} (operation : α → Option β) :
    ∀ {inputs : List α} {outputs : List β}, inputs.mapM operation = some outputs →
      ∀ output ∈ outputs, ∃ input ∈ inputs, operation input = some output
  | [], outputs, ran, output, member => by simp at ran; subst outputs; simp at member
  | input :: inputs, outputs, ran, output, member => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at ran
      cases head : operation input with
      | none => simp [head] at ran
      | some first =>
          cases tail : inputs.mapM operation with
          | none => simp [head, tail] at ran
          | some rest =>
              simp only [head, tail, Option.bind_some, Option.some.injEq] at ran
              subst outputs
              rcases List.mem_cons.mp member with rfl | later
              · exact ⟨input, List.mem_cons_self, head⟩
              · obtain ⟨found, present, equation⟩ :=
                  exists_of_mem_mapM operation tail output later
                exact ⟨found, List.mem_cons_of_mem _ present, equation⟩

theorem runUses_bounded {Rule : Type v} (hypothesisCount : Nat) :
    ∀ {done out : List Used} {proof : List (Rule × List Kid)},
      (∀ used ∈ done, Bounded hypothesisCount used) →
      runUses hypothesisCount done proof = some out →
      ∀ used ∈ out, Bounded hypothesisCount used
  | done, _, [], doneBounded, ran => by
      simp only [runUses, Option.some.injEq] at ran
      subst ran
      exact doneBounded
  | done, out, (_, kids) :: proof, doneBounded, ran => by
      simp only [runUses] at ran
      cases found : kids.mapM (useOfKid hypothesisCount done) with
      | none => simp [useOfKids, found] at ran
      | some childUses =>
          simp only [useOfKids, found, Option.map_some, Option.bind_eq_bind,
            Option.bind_some] at ran
          have childrenBounded : ∀ used ∈ childUses, Bounded hypothesisCount used := by
            intro used member
            obtain ⟨kid, _, kidFound⟩ := exists_of_mem_mapM _ found used member
            exact useOfKid_bounded doneBounded kidFound
          have joined := joinUses_bounded hypothesisCount childUses childrenBounded
          exact runUses_bounded hypothesisCount
            (fun used member => by
              rcases List.mem_append.mp member with prior | added
              · exact doneBounded used prior
              · rw [List.mem_singleton.mp added]
                exact joined)
            ran

theorem infer_bounded {Rule : Type v} {hypothesisCount : Nat}
    {proof : List (Rule × List Kid)} {root : Kid}
    {used : Used} (found : infer hypothesisCount proof root = some used) :
    Bounded hypothesisCount used := by
  unfold infer at found
  cases ran : runUses hypothesisCount [] proof with
  | none => simp [ran] at found
  | some done =>
      simp only [ran] at found
      exact useOfKid_bounded (runUses_bounded hypothesisCount (by simp) ran) found

/-- Select source hypothesis occurrences in their original order. -/
def selectFrom (used : Used) : Nat → List P.J → List P.J
  | _, [] => []
  | position, hypothesis :: hypotheses =>
      if position ∈ used then hypothesis :: selectFrom used (position + 1) hypotheses
      else selectFrom used (position + 1) hypotheses

def select (used : Used) (hyps : List P.J) : List P.J := selectFrom (P := P) used 0 hyps

theorem getElem_mem_selectFrom (used : Used) :
    ∀ {hyps : List P.J} {position offset : Nat} (within : position < hyps.length),
      offset + position ∈ used →
        hyps.get ⟨position, within⟩ ∈ selectFrom (P := P) used offset hyps
  | [], position, _, within, _ => by simp at within
  | hypothesis :: hypotheses, 0, offset, _, selected => by
      have here : offset ∈ used := by simpa using selected
      simp [selectFrom, here]
  | hypothesis :: hypotheses, position + 1, offset, within, selected => by
      have tailWithin : position < hypotheses.length := by simpa using within
      have shifted : offset + 1 + position ∈ used := by
        rw [show offset + 1 + position = offset + (position + 1) by omega]
        exact selected
      by_cases here : offset ∈ used
      · simp only [selectFrom, here, ↓reduceIte, List.mem_cons]
        exact Or.inr (getElem_mem_selectFrom used tailWithin shifted)
      · simp only [selectFrom, here, ↓reduceIte]
        exact getElem_mem_selectFrom used tailWithin shifted

theorem getElem_mem_select (used : Used) {hyps : List P.J} {position : Nat}
    (within : position < hyps.length) (selected : position ∈ used) :
    hyps[position] ∈ select (P := P) used hyps := by
  exact getElem_mem_selectFrom used within (by simpa using selected)

theorem selectFrom_map (used : Used) (operation : P.J → P.J) :
    ∀ (offset : Nat) (hyps : List P.J),
      selectFrom (P := P) used offset (hyps.map operation) =
        (selectFrom (P := P) used offset hyps).map operation
  | _, [] => rfl
  | offset, hypothesis :: hypotheses => by
      by_cases here : offset ∈ used
      · simp [selectFrom, here, selectFrom_map]
      · simp [selectFrom, here, selectFrom_map]

theorem select_map (used : Used) (operation : P.J → P.J) (hyps : List P.J) :
    select (P := P) used (hyps.map operation) =
      (select (P := P) used hyps).map operation :=
  selectFrom_map used operation 0 hyps

/-- A judgment is supported by an interface when deriving each indexed source
hypothesis in a target context suffices to derive the judgment there. -/
def Supports (hyps target : List P.J) (used : Used) (judgment : P.J) : Prop :=
  (∀ index, index ∈ used →
      ∃ within : index < hyps.length, Derivable P target hyps[index]) →
    Derivable P target judgment

def Aligned (hyps target : List P.J) (done : List P.J) (uses : List Used) : Prop :=
  List.Forall₂ (fun judgment used => Supports (P := P) hyps target used judgment) done uses

theorem aligned_snoc {hyps target done : List P.J} {uses : List Used}
    {used : Used} {judgment : P.J}
    (aligned : Aligned (P := P) hyps target done uses)
    (supported : Supports (P := P) hyps target used judgment) :
    Aligned (P := P) hyps target (done ++ [judgment]) (uses ++ [used]) := by
  induction aligned with
  | nil => exact .cons supported .nil
  | cons related rest inductionHypothesis =>
      exact .cons related inductionHypothesis

theorem useOfKid_exists {hyps target done : List P.J} {uses : List Used}
    (aligned : Aligned (P := P) hyps target done uses) {kid : Kid} {judgment : P.J}
    (found : lookup hyps done kid = some judgment) :
    ∃ used, useOfKid hyps.length uses kid = some used := by
  cases kid with
  | hyp index =>
      have within := (List.getElem?_eq_some_iff.mp found).1
      exact ⟨{index}, by simp [useOfKid, within]⟩
  | node index =>
      have doneWithin := (List.getElem?_eq_some_iff.mp found).1
      have usesWithin : index < uses.length := by
        rw [← aligned.length_eq]
        exact doneWithin
      exact ⟨uses[index], by simp [useOfKid, List.getElem?_eq_getElem usesWithin]⟩

theorem useOfKids_exists {hyps target done : List P.J} {uses : List Used}
    (aligned : Aligned (P := P) hyps target done uses) :
    ∀ {kids : List Kid} {judgments : List P.J},
      kids.mapM (lookup hyps done) = some judgments →
      ∃ childUses, kids.mapM (useOfKid hyps.length uses) = some childUses
  | [], _, _ => ⟨[], rfl⟩
  | kid :: kids, judgments, found => by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at found
      cases headFound : lookup hyps done kid with
      | none => simp [headFound] at found
      | some actual =>
          cases tailFound : kids.mapM (lookup hyps done) with
          | none => simp [headFound, tailFound] at found
          | some actuals =>
              simp only [headFound, tailFound, Option.bind_some, Option.some.injEq] at found
              subst judgments
              obtain ⟨headUse, headUseFound⟩ := useOfKid_exists aligned headFound
              obtain ⟨tailUses, tailUsesFound⟩ :=
                useOfKids_exists aligned tailFound
              exact ⟨headUse :: tailUses, by
                simp [headUseFound, tailUsesFound]⟩

theorem useOfKid_support {hyps target done : List P.J} {uses : List Used}
    (aligned : Aligned (P := P) hyps target done uses)
    {kid : Kid} {judgment : P.J} {used : Used}
    (judgmentFound : lookup hyps done kid = some judgment)
    (useFound : useOfKid hyps.length uses kid = some used) :
    Supports (P := P) hyps target used judgment := by
  cases kid with
  | hyp index =>
      have within := (List.getElem?_eq_some_iff.mp judgmentFound).1
      have judgmentEq := (List.getElem?_eq_some_iff.mp judgmentFound).2
      simp only [useOfKid, if_pos within, Option.some.injEq] at useFound
      subst used
      intro supplied
      obtain ⟨_, derivation⟩ := supplied index (by simp)
      simpa only [judgmentEq] using derivation
  | node index =>
      have doneWithin := (List.getElem?_eq_some_iff.mp judgmentFound).1
      have doneValue : done.get ⟨index, doneWithin⟩ = judgment := by
        apply Option.some.inj
        exact (List.getElem?_eq_getElem doneWithin).symm.trans judgmentFound
      have usesWithin : index < uses.length := by
        rw [← aligned.length_eq]
        exact doneWithin
      have rawUse : uses[index]? = some used := by
        simpa only [useOfKid] using useFound
      have useValue : uses.get ⟨index, usesWithin⟩ = used := by
        apply Option.some.inj
        exact (List.getElem?_eq_getElem usesWithin).symm.trans rawUse
      have related := aligned.get doneWithin usesWithin
      rw [doneValue, useValue] at related
      exact related

theorem discharge_supported [DecidableEq P.J]
    {hyps target done : List P.J} {uses : List Used}
    (aligned : Aligned (P := P) hyps target done uses) :
    ∀ (premises : List P.J) (kids : List Kid) (childUses : List Used),
      discharge (lookup hyps done) premises kids = true →
      kids.mapM (useOfKid hyps.length uses) = some childUses →
      (∀ index, index ∈ joinUses childUses →
        ∃ within : index < hyps.length, Derivable P target hyps[index]) →
      ∀ premise ∈ premises, P.side premise = false → Derivable P target premise
  | [], _, _, _, _, _, premise, member, _ => by simp at member
  | premise :: premises, kids, childUses, discharged, usesFound, supplied,
      requested, member, requestedOrdinary => by
      by_cases side : P.side premise = true
      · have restDischarged : discharge (lookup hyps done) premises kids = true := by
          simpa [discharge, side] using discharged
        rcases List.mem_cons.mp member with rfl | rest
        · simp [side] at requestedOrdinary
        · exact discharge_supported aligned premises kids childUses restDischarged usesFound
            supplied requested rest requestedOrdinary
      · have ordinary : P.side premise = false := by simpa using side
        cases kids with
        | nil => simp [discharge, ordinary] at discharged
        | cons kid kids =>
            simp only [discharge, ordinary, Bool.false_eq_true, ↓reduceIte,
              Bool.and_eq_true, decide_eq_true_eq] at discharged
            simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at usesFound
            cases headUse : useOfKid hyps.length uses kid with
            | none => simp [headUse] at usesFound
            | some used =>
                cases tailUses : kids.mapM (useOfKid hyps.length uses) with
                | none => simp [headUse, tailUses] at usesFound
                | some restUses =>
                    simp only [headUse, tailUses, Option.bind_some, Option.some.injEq] at usesFound
                    subst childUses
                    rcases List.mem_cons.mp member with rfl | rest
                    · apply useOfKid_support aligned discharged.1 headUse
                      intro index selected
                      exact supplied index (by simp [joinUses, selected])
                    · exact discharge_supported aligned premises kids restUses discharged.2 tailUses
                        (fun index selected => supplied index (by simp [joinUses, selected]))
                        requested rest requestedOrdinary

theorem runCB_interface [DecidableEq P.J] (matcher : Matcher P) (hyps target : List P.J) :
    ∀ {done : List P.J} {proof : List (CNode P)} {out : List P.J} {uses : List Used},
      Aligned (P := P) hyps target done uses →
      runCB matcher hyps done proof = some out →
      ∃ outUses, runUses hyps.length uses proof = some outUses ∧
        Aligned (P := P) hyps target out outUses
  | done, [], out, uses, aligned, ran => by
      simp only [runCB, Option.some.injEq] at ran
      subst out
      exact ⟨uses, rfl, aligned⟩
  | done, (rule, kids) :: proof, out, uses, aligned, ran => by
      simp only [runCB] at ran
      cases kidsFound : kids.mapM (lookup hyps done) with
      | none => simp [kidsFound] at ran
      | some judgments =>
          simp only [kidsFound] at ran
          cases solved : matcher.solve rule judgments with
          | none => simp [solved] at ran
          | some arguments =>
              simp only [solved] at ran
              cases instanceFound : P.inst rule arguments with
              | none => simp [instanceFound] at ran
              | some result =>
                  obtain ⟨premises, conclusion⟩ := result
                  simp only [instanceFound] at ran
                  by_cases discharged : discharge (lookup hyps done) premises kids = true
                  · simp only [discharged, ↓reduceIte] at ran
                    obtain ⟨childUses, childUsesFound⟩ :=
                      useOfKids_exists aligned kidsFound
                    let used := joinUses childUses
                    have supported : Supports (P := P) hyps target used conclusion := by
                      intro supplied
                      exact Derivable.rule instanceFound
                        (discharge_supported aligned premises kids childUses discharged
                          childUsesFound supplied)
                    have nextAligned : Aligned (P := P) hyps target
                        (done ++ [conclusion]) (uses ++ [used]) :=
                      aligned_snoc aligned supported
                    obtain ⟨outUses, restUses, outAligned⟩ :=
                      runCB_interface matcher hyps target nextAligned ran
                    refine ⟨outUses, ?_, outAligned⟩
                    simp only [runUses, useOfKids, childUsesFound, Option.map_some,
                      Option.bind_eq_bind, Option.bind_some]
                    exact restUses
                  · simp [discharged] at ran

/-- The inferred root interface is sufficient in every target context. -/
theorem checkCB_interface [DecidableEq P.J] (matcher : Matcher P)
    {hyps target : List P.J} {proof : List (CNode P)} {root : Kid} {goal : P.J}
    (accepted : checkCB matcher hyps proof root goal = true) :
    ∃ used, infer hyps.length proof root = some used ∧
      Supports (P := P) hyps target used goal := by
  unfold checkCB at accepted
  cases ran : runCB matcher hyps [] proof with
  | none => simp [ran] at accepted
  | some out =>
      simp only [ran, decide_eq_true_eq] at accepted
      have initial : Aligned (P := P) hyps target [] [] := .nil
      obtain ⟨uses, usesRan, aligned⟩ :=
        runCB_interface matcher hyps target initial ran
      obtain ⟨used, rootUse⟩ := useOfKid_exists aligned accepted
      exact ⟨used, by simp [infer, usesRan, rootUse],
        useOfKid_support aligned accepted rootUse⟩

/-- The selected source occurrences themselves form a sufficient context. -/
theorem checkCB_selected [DecidableEq P.J] (matcher : Matcher P)
    {hyps : List P.J} {proof : List (CNode P)} {root : Kid} {goal : P.J}
    (accepted : checkCB matcher hyps proof root goal = true) :
    ∃ used, infer hyps.length proof root = some used ∧
      Derivable P (select (P := P) used hyps) goal := by
  obtain ⟨used, inferred, _⟩ :=
    checkCB_interface matcher (target := hyps) accepted
  obtain ⟨used', inferred', supported⟩ :=
    checkCB_interface matcher (target := select (P := P) used hyps) accepted
  have same : used' = used := Option.some.inj (inferred'.symm.trans inferred)
  subst used'
  refine ⟨used, inferred, supported ?_⟩
  intro position selected
  have within := infer_bounded inferred position selected
  exact ⟨within, Derivable.hyp (getElem_mem_select used within selected)⟩

/-- Every permitted presentation renaming transports the selected proof
interface. The interface indices are unchanged because they describe the
proof graph, while its selected judgments are renamed pointwise. -/
theorem checkCB_selected_rename [DecidableEq P.J] (matcher : Matcher P)
    (change : Renaming P) {hyps : List P.J} {proof : List (CNode P)}
    {root : Kid} {goal : P.J}
    (accepted : checkCB matcher hyps proof root goal = true) :
    ∃ used, infer hyps.length proof root = some used ∧
      Derivable P (select (P := P) used (hyps.map change.onJ)) (change.onJ goal) := by
  obtain ⟨used, inferred, derivation⟩ := checkCB_selected matcher accepted
  refine ⟨used, inferred, ?_⟩
  rw [select_map]
  exact derivation.rename change

namespace Controls

open Mettapedia.Logic.TierZero.ChildBound.Controls

def proof : List (CNode pres) :=
  [(.w0, []), (.wsucc, [.node 0]), (.t0, [.node 1]), (.t0, [.hyp 0])]

/-- The selected root uses only hypothesis 0. The valid three-node derivation
before it is root-unreachable and contributes no hypothesis. -/
theorem unreachable_nodes_do_not_contribute :
    infer 2 proof (.node 3) = some {0} := by decide

theorem changing_the_selected_hypothesis_can_change_the_goal :
    checkCB matcher [J.w 7, J.w 9] proof (.node 3) (J.t 7) = true ∧
      checkCB matcher [J.w 8, J.w 9] proof (.node 3) (J.t 7) = false := by decide

theorem an_unselected_hypothesis_does_not_change_the_goal :
    checkCB matcher [J.w 7, J.w 9] proof (.node 3) (J.t 7) = true ∧
      checkCB matcher [J.w 7, J.t 4] proof (.node 3) (J.t 7) = true := by decide

def shared : List (CNode pres) :=
  [(.t0, [.hyp 0]), (.t0, [.hyp 0]), (.t0, [.hyp 0])]

theorem repeated_reachability_retains_one_occurrence :
    infer 1 shared (.node 2) = some {0} := by decide

theorem equal_hypothesis_occurrences_keep_their_positions :
    infer 2 ([ (.t0, [.hyp 1]) ] : List (CNode pres)) (.node 0) = some {1} := by decide

end Controls

end Mettapedia.Logic.TierZero.ProofInterface
