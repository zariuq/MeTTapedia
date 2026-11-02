import Mettapedia.Languages.ProcessCalculi.Ambient.FullReflection
import Mettapedia.Languages.ProcessCalculi.Ambient.Comm

/-!
# The rule firings of mobile ambients with communication, by occurrence

An independent specification of the eight rules of `ambientCommCalc` (`AmbCommRawStep`): the moves of the pure calculus,
and communication between an input and an output side by side in a bag — of a name, or of a capability — the input's
body instantiated with the message. A step descends into a component of a bag, under a restriction or into the content
of an ambient. The authored rules fire exactly as the specification says (`step_iff_raw`), and every firing of the
pure calculus is one here (`AmbNuRawStep.toComm`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Comm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb par)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (AmbNuRawStep inRule outRule openRule parCongRule resCongRule
  ambCongRule openBindings inBindings outBindings open_match_inv in_match_inv out_match_inv parCong_match_inv
  resCong_match_inv ambCong_match_inv open_apply_exact in_apply_exact out_apply_exact parCong_apply_exact
  resCong_apply_exact ambCong_apply_exact open_matchRel in_matchRel out_matchRel binary_match_iff)

/-- The pairs of an input and the output it receives from: of a name, of a capability. -/
def channels : List (String × String) := [("AInName", "AOutName"), ("AInCap", "AOutCap")]

/-- **The firings of mobile ambients with communication, by occurrence.** -/
inductive AmbCommRawStep : Pattern → Pattern → Prop where
  /-- `open n.P | n[Q] | R ⟶ P | Q | R`. -/
  | «open» {elements : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      (name process content : Pattern)
      (capability : elements[i] = .apply "AOpen" [name, process])
      (boundary : (elements.eraseIdx i)[j] = amb name content) :
      AmbCommRawStep (.collection .hashBag elements tail)
        (.collection .hashBag (process :: content :: (elements.eraseIdx i).eraseIdx j) none)
  /-- `n[in m.P | R] | m[S] | T ⟶ m[n[P | R] | S] | T`. -/
  | enter {elements : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      (name target process host : Pattern) {inner : List Pattern} {innerTail : Option String}
      (k : ℕ) (hk : k < inner.length)
      (mover : elements[i] = amb name (.collection .hashBag inner innerTail))
      (capability : inner[k] = .apply "AIn" [target, process])
      (destination : (elements.eraseIdx i)[j] = amb target host) :
      AmbCommRawStep (.collection .hashBag elements tail)
        (.collection .hashBag
          (amb target (.collection .hashBag
            [amb name (.collection .hashBag (process :: inner.eraseIdx k) none), host] none) ::
            (elements.eraseIdx i).eraseIdx j) none)
  /-- `m[n[out m.P | R] | S] ⟶ n[P | R] | m[S]`. -/
  | exit {contents : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < contents.length) (name parent process : Pattern)
      {inner : List Pattern} {innerTail : Option String} (k : ℕ) (hk : k < inner.length)
      (mover : contents[i] = amb name (.collection .hashBag inner innerTail))
      (capability : inner[k] = .apply "AOut" [parent, process]) :
      AmbCommRawStep (amb parent (.collection .hashBag contents tail))
        (.collection .hashBag
          [amb name (.collection .hashBag (process :: inner.eraseIdx k) none),
            amb parent (.collection .hashBag (contents.eraseIdx i) none)] none)
  /-- `(x).P | ⟨M⟩ | R ⟶ P{x ← M} | R`, of a name or of a capability. -/
  | comm {elements : List Pattern} {tail : Option String} {input output : String}
      (listed : (input, output) ∈ channels)
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      (binder : Option String) (body message : Pattern)
      (receiving : elements[i] = .apply input [.lambda binder body])
      (sending : (elements.eraseIdx i)[j] = .apply output [message]) :
      AmbCommRawStep (.collection .hashBag elements tail)
        (.collection .hashBag (instantiateBVar message body :: (elements.eraseIdx i).eraseIdx j) none)
  /-- A component of a parallel composition reduces. -/
  | par {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) {target : Pattern}
      (inner : AmbCommRawStep elements[i] target) :
      AmbCommRawStep (.collection .hashBag elements tail) (.collection .hashBag (target :: elements.eraseIdx i) none)
  /-- A process reduces under a restriction. -/
  | res (binder : Option String) {source target : Pattern} (inner : AmbCommRawStep source target) :
      AmbCommRawStep (.apply "ANu" [.lambda binder source]) (.apply "ANu" [.lambda none target])
  /-- The content of an ambient reduces. -/
  | ambient (name : Pattern) {content target : Pattern} (inner : AmbCommRawStep content target) :
      AmbCommRawStep (amb name content) (amb name target)

/-- **Every firing of the pure calculus is a firing with communication.** -/
theorem AmbNuRawStep.toComm {source target : Pattern} (step : AmbNuRawStep source target) :
    AmbCommRawStep source target := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
      exact .open i hi j hj name process content capability boundary
  | enter i hi j hj name target process host k hk mover capability destination =>
      exact .enter i hi j hj name target process host k hk mover capability destination
  | exit i hi name parent process k hk mover capability => exact .exit i hi name parent process k hk mover capability
  | par i hi _ recurse => exact .par i hi recurse
  | res binder _ recurse => exact .res binder recurse
  | ambient name _ recurse => exact .ambient name recurse

/-! ## The bindings of communication -/

/-- The bindings of a communication: the message, the rest of the bag, the input's body. -/
def commBindings (slot : String) (body message : Pattern) (rest : List Pattern) : Bindings :=
  [(slot, message), ("rest", .collection .hashBag rest none), ("body", body)]

theorem commName_apply_exact (body name : Pattern) (rest : List Pattern) :
    applyBindingsForRule ambientCommCalc commNameRule (commBindings "n" body name rest) =
      .collection .hashBag (instantiateBVar name body :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [commNameRule, par, commBindings, applyBindings]

theorem commCap_apply_exact (body capability : Pattern) (rest : List Pattern) :
    applyBindingsForRule ambientCommCalc commCapRule (commBindings "m" body capability rest) =
      .collection .hashBag (instantiateBVar capability body :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [commCapRule, par, commBindings, applyBindings]

/-- An input over an abstraction matches its own terms. -/
theorem input_match_iff (label : String) (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply label [.lambda none (.fvar "body")]) target bindings ↔
      ∃ binder body, target = .apply label [.lambda binder body] ∧ bindings = [("body", body)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons bodyMatch last merged =>
        cases bodyMatch with
        | lambda bodyMatch =>
          cases bodyMatch
          cases last
          simp only [mergeBindings] at merged
          cases merged
          exact ⟨_, _, rfl, rfl⟩
  · rintro ⟨binder, body, rfl, rfl⟩
    exact .apply (.cons (.lambda .fvar) .nil rfl) rfl

/-- An output of one metavariable matches its own terms. -/
theorem output_match_iff (label slot : String) (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply label [.fvar slot]) target bindings ↔
      ∃ message, target = .apply label [message] ∧ bindings = [(slot, message)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons messageMatch last merged =>
        cases messageMatch
        cases last
        simp only [mergeBindings] at merged
        cases merged
        exact ⟨_, rfl, rfl⟩
  · rintro ⟨message, rfl, rfl⟩
    exact .apply (.cons .fvar .nil rfl) rfl

/-- **A communication rule matches an input and an output side by side.** -/
theorem comm_match_inv {input output slot : String} (fresh : slot ≠ "body" ∧ slot ≠ "rest")
    {source : Pattern} {bindings : Bindings}
    (matched : MatchRel (par [.apply input [.lambda none (.fvar "body")], .apply output [.fvar slot]]
      (some "rest")) source bindings) :
    ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
      (hj : j < (elements.eraseIdx i).length) (binder : Option String) (body message : Pattern),
      source = .collection .hashBag elements tail ∧ elements[i] = .apply input [.lambda binder body] ∧
        (elements.eraseIdx i)[j] = .apply output [message] ∧
        bindings = commBindings slot body message ((elements.eraseIdx i).eraseIdx j) := by
  have slotBody : (slot == "body") = false := beq_eq_false_iff_ne.mpr fresh.1
  have slotRest : (slot == "rest") = false := beq_eq_false_iff_ne.mpr fresh.2
  have bodySlot : ("body" == slot) = false := beq_eq_false_iff_ne.mpr (Ne.symm fresh.1)
  have restSlot : ("rest" == slot) = false := beq_eq_false_iff_ne.mpr (Ne.symm fresh.2)
  simp only [par] at matched
  cases matched with
  | collection _ bag =>
    cases bag with
    | cons i hi first remaining mergeFirst =>
      obtain ⟨binder, body, receiving, rfl⟩ := (input_match_iff _ _ _).mp first
      cases remaining with
      | cons j hj second last mergeRest =>
        obtain ⟨message, sending, rfl⟩ := (output_match_iff _ _ _ _).mp second
        cases last
        simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil] at mergeRest mergeFirst
        simp [List.find?, slotRest] at mergeRest
        subst mergeRest
        simp [List.find?, restSlot, bodySlot] at mergeFirst
        subst mergeFirst
        exact ⟨_, _, i, hi, j, hj, binder, body, message, rfl, receiving, sending, rfl⟩

/-- **A communication rule matches at a selected input and output.** -/
theorem comm_matchRel {input output slot : String} (fresh : slot ≠ "body" ∧ slot ≠ "rest")
    {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) (j : ℕ)
    (hj : j < (elements.eraseIdx i).length) (binder : Option String) (body message : Pattern)
    (receiving : elements[i] = .apply input [.lambda binder body])
    (sending : (elements.eraseIdx i)[j] = .apply output [message]) :
    MatchRel (par [.apply input [.lambda none (.fvar "body")], .apply output [.fvar slot]] (some "rest"))
      (.collection .hashBag elements tail) (commBindings slot body message ((elements.eraseIdx i).eraseIdx j)) := by
  have slotBody : (slot == "body") = false := beq_eq_false_iff_ne.mpr fresh.1
  have slotRest : (slot == "rest") = false := beq_eq_false_iff_ne.mpr fresh.2
  have bodySlot : ("body" == slot) = false := beq_eq_false_iff_ne.mpr (Ne.symm fresh.1)
  have restSlot : ("rest" == slot) = false := beq_eq_false_iff_ne.mpr (Ne.symm fresh.2)
  simp only [par]
  have sent : MatchBagRel [.apply output [.fvar slot]] (some "rest") .hashBag (elements.eraseIdx i)
      [("rest", .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none), (slot, message)] :=
    .cons j hj ((output_match_iff _ _ _ _).mpr ⟨message, sending, rfl⟩) .nilRest
      (by simp [mergeBindings, List.find?, slotRest])
  exact .collection (by decide) (.cons i hi ((input_match_iff _ _ _).mpr ⟨binder, body, receiving, rfl⟩) sent
    (by simp [mergeBindings, List.find?, restSlot, bodySlot, commBindings]))

/-! ## The rules fire as specified -/

private theorem raw_of_stepAt {fuel : ℕ} {source target : Pattern}
    (step : StepAt (engineBasePremises RelationEnv.empty) ambientCommCalc fuel source target) :
    AmbCommRawStep source target := by
  induction fuel using Nat.strong_induction_on generalizing source target with
  | h fuel ih =>
    cases step with
    | @rule innerFuel source target rule initial final member matching premises result =>
      rw [ambientCommCalc_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [matchPatternForRule_eq_syntactic] at matching
      have matchRel := matchPattern_iff_matchRel.mp matching
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨elements, tail, i, hi, j, hj, name, target, process, host, inner, innerTail, k, hk, rfl, atMover,
          atCapability, atDestination, rfl⟩ := in_match_inv matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [in_apply_exact] at result
        cases result
        exact .enter i hi j hj name target process host k hk atMover atCapability atDestination
      · obtain ⟨contents, tail, i, hi, name, parent, process, inner, innerTail, k, hk, rfl, atMover, atCapability,
          rfl⟩ := out_match_inv matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [out_apply_exact] at result
        cases result
        exact .exit i hi name parent process k hk atMover atCapability
      · obtain ⟨elements, tail, i, hi, j, hj, name, process, content, rfl, atCapability, atBoundary, rfl⟩ :=
          open_match_inv matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [open_apply_exact] at result
        cases result
        exact .open i hi j hj name process content atCapability atBoundary
      · obtain ⟨elements, tail, i, hi, j, hj, binder, body, name, rfl, receiving, sending, rfl⟩ :=
          comm_match_inv (by decide) matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [commName_apply_exact] at result
        cases result
        exact .comm (by simp [channels]) i hi j hj binder body name receiving sending
      · obtain ⟨elements, tail, i, hi, j, hj, binder, body, capability, rfl, receiving, sending, rfl⟩ :=
          comm_match_inv (by decide) matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [commCap_apply_exact] at result
        cases result
        exact .comm (by simp [channels]) i hi j hj binder body capability receiving sending
      · obtain ⟨elements, tail, i, hi, rfl, rfl⟩ := parCong_match_inv matchRel
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate),
                ("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [parCong_apply_exact] at result
            cases result
            exact .par i hi (ih innerFuel (by omega) (by simpa [applyBindings] using inner))
      · obtain ⟨binder, body, rfl, rfl⟩ := resCong_match_inv matchRel
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate), ("S", body)] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [resCong_apply_exact] at result
            cases result
            exact .res binder (ih innerFuel (by omega) (by simpa [applyBindings] using inner))
      · obtain ⟨name, content, rfl, rfl⟩ := ambCong_match_inv matchRel
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate), ("S", content), ("n", name)] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [ambCong_apply_exact] at result
            cases result
            exact .ambient name (ih innerFuel (by omega) (by simpa [applyBindings] using inner))

/-- **Every firing of the authored rules is a firing of the specification.** -/
theorem raw_of_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) ambientCommCalc source target) :
    AmbCommRawStep source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact raw_of_stepAt bounded

/-- **Every firing of the specification is a firing of the authored rules.** -/
theorem step_of_raw {source target : Pattern} (step : AmbCommRawStep source target) :
    Step (engineBasePremises RelationEnv.empty) ambientCommCalc source target := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
    refine ⟨1, .rule (rule := openRule) (by rw [ambientCommCalc_rewrites]; simp) ?_ (.nil _)
      (open_apply_exact name process content _)⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (open_matchRel i hi j hj name process content capability boundary)
  | enter i hi j hj name target process host k hk mover capability destination =>
    refine ⟨1, .rule (rule := inRule) (by rw [ambientCommCalc_rewrites]; simp) ?_ (.nil _)
      (in_apply_exact name target process host _ _)⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr
      (in_matchRel i hi j hj name target process host k hk mover capability destination)
  | exit i hi name parent process k hk mover capability =>
    refine ⟨1, .rule (rule := outRule) (by rw [ambientCommCalc_rewrites]; simp) ?_ (.nil _)
      (out_apply_exact name parent process _ _)⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (out_matchRel i hi name parent process k hk mover capability)
  | comm listed i hi j hj binder body message receiving sending =>
    simp only [channels, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
    rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨1, .rule (rule := commNameRule) (by rw [ambientCommCalc_rewrites]; simp) ?_ (.nil _)
        (commName_apply_exact body message _)⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (comm_matchRel (by decide) i hi j hj binder body message receiving sending)
    · refine ⟨1, .rule (rule := commCapRule) (by rw [ambientCommCalc_rewrites]; simp) ?_ (.nil _)
        (commCap_apply_exact body message _)⟩
      rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (comm_matchRel (by decide) i hi j hj binder body message receiving sending)
  | @par elements tail i hi target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := parCongRule)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])]) (by rw [ambientCommCalc_rewrites]; simp) ?_ ?_ (parCong_apply_exact _ _ _)⟩
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.collection (by decide) (.cons i hi .fvar .nilRest rfl))
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _
  | @res binder source target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := resCongRule)
      (initialBindings := [("S", source)]) (finalBindings := [("T", target), ("S", source)])
      ?_ ?_ ?_ (resCong_apply_exact source target)⟩
    · rw [ambientCommCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.apply (.cons (.lambda .fvar) .nil rfl) rfl)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _
  | @ambient name content target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := ambCongRule)
      (initialBindings := [("S", content), ("n", name)]) (finalBindings := [("T", target), ("S", content), ("n", name)])
      (by rw [ambientCommCalc_rewrites]; simp) ?_ ?_ (ambCong_apply_exact name content target)⟩
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr ((binary_match_iff "AAmb" "n" "S" (by decide) _ _).mpr ⟨name, content, rfl, rfl⟩)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _

/-- **The authored rules fire exactly as the specification says.** -/
theorem step_iff_raw (source target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) ambientCommCalc source target ↔ AmbCommRawStep source target :=
  ⟨raw_of_step, step_of_raw⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Comm
