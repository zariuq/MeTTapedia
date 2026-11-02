import Mettapedia.Languages.ProcessCalculi.Ambient.Full
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

/-!
# The rule firings of mobile ambients with restriction, by occurrence

An independent specification of the six rules of `ambientNuCalc` (`AmbNuRawStep`): a step selects occurrences in
parallel bags and rebuilds the bags around them, and descends into a component of a bag, under a restriction or into the
content of an ambient. Occurrence indices tell equal components apart. The authored rules fire exactly as the
specification says (`step_iff_raw`), so the specification can stand in for the matcher in proofs about the calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Full

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (amb par)

/-- **The firings of mobile ambients, by occurrence.** -/
inductive AmbNuRawStep : Pattern → Pattern → Prop where
  /-- `open n.P | n[Q] | R ⟶ P | Q | R`. -/
  | «open» {elements : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      (name process content : Pattern)
      (capability : elements[i] = .apply "AOpen" [name, process])
      (boundary : (elements.eraseIdx i)[j] = amb name content) :
      AmbNuRawStep (.collection .hashBag elements tail)
        (.collection .hashBag (process :: content :: (elements.eraseIdx i).eraseIdx j) none)
  /-- `n[in m.P | R] | m[S] | T ⟶ m[n[P | R] | S] | T`. -/
  | enter {elements : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      (name target process host : Pattern) {inner : List Pattern} {innerTail : Option String}
      (k : ℕ) (hk : k < inner.length)
      (mover : elements[i] = amb name (.collection .hashBag inner innerTail))
      (capability : inner[k] = .apply "AIn" [target, process])
      (destination : (elements.eraseIdx i)[j] = amb target host) :
      AmbNuRawStep (.collection .hashBag elements tail)
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
      AmbNuRawStep (amb parent (.collection .hashBag contents tail))
        (.collection .hashBag
          [amb name (.collection .hashBag (process :: inner.eraseIdx k) none),
            amb parent (.collection .hashBag (contents.eraseIdx i) none)] none)
  /-- A component of a parallel composition reduces. -/
  | par {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) {target : Pattern}
      (inner : AmbNuRawStep elements[i] target) :
      AmbNuRawStep (.collection .hashBag elements tail) (.collection .hashBag (target :: elements.eraseIdx i) none)
  /-- A process reduces under a restriction. -/
  | res (binder : Option String) {source target : Pattern} (inner : AmbNuRawStep source target) :
      AmbNuRawStep (.apply "ANu" [.lambda binder source]) (.apply "ANu" [.lambda none target])
  /-- The content of an ambient reduces. -/
  | ambient (name : Pattern) {content target : Pattern} (inner : AmbNuRawStep content target) :
      AmbNuRawStep (amb name content) (amb name target)

/-! ## The bindings of each rule

The rule applier reads no language, so each application below holds in every language. -/

/-- The bindings of an opening. -/
def openBindings (name process content : Pattern) (rest : List Pattern) : Bindings :=
  [("q", content), ("rest", .collection .hashBag rest none), ("p", process), ("n", name)]

/-- The bindings of an entry. -/
def inBindings (name target process host : Pattern) (inner rest : List Pattern) : Bindings :=
  [("s", host), ("rest", .collection .hashBag rest none), ("m", target), ("p", process),
    ("inner", .collection .hashBag inner none), ("n", name)]

/-- The bindings of an exit. -/
def outBindings (name parent process : Pattern) (inner rest : List Pattern) : Bindings :=
  [("n", name), ("inner", .collection .hashBag inner none), ("p", process),
    ("rest", .collection .hashBag rest none), ("m", parent)]

theorem open_apply_exact {language : LanguageDef} (name process content : Pattern) (rest : List Pattern) :
    applyBindingsForRule language openRule (openBindings name process content rest) =
      .collection .hashBag (process :: content :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [openRule, par, openBindings, applyBindings]

theorem in_apply_exact {language : LanguageDef} (name target process host : Pattern) (inner rest : List Pattern) :
    applyBindingsForRule language inRule (inBindings name target process host inner rest) =
      .collection .hashBag
        (amb target (.collection .hashBag [amb name (.collection .hashBag (process :: inner) none), host] none) ::
          rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [inRule, par, amb, inBindings, applyBindings]

theorem out_apply_exact {language : LanguageDef} (name parent process : Pattern) (inner rest : List Pattern) :
    applyBindingsForRule language outRule (outBindings name parent process inner rest) =
      .collection .hashBag
        [amb name (.collection .hashBag (process :: inner) none), amb parent (.collection .hashBag rest none)] none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [outRule, par, amb, outBindings, applyBindings]

theorem parCong_apply_exact {language : LanguageDef} (source target : Pattern) (rest : List Pattern) :
    applyBindingsForRule language parCongRule
      [("T", target), ("rest", .collection .hashBag rest none), ("S", source)] =
      .collection .hashBag (target :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [parCongRule, par, applyBindings]

theorem resCong_apply_exact {language : LanguageDef} (source target : Pattern) :
    applyBindingsForRule language resCongRule [("T", target), ("S", source)] =
      .apply "ANu" [.lambda none target] := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [resCongRule, applyBindings]

theorem ambCong_apply_exact {language : LanguageDef} (name source target : Pattern) :
    applyBindingsForRule language ambCongRule [("T", target), ("S", source), ("n", name)] = amb name target := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [ambCongRule, amb, applyBindings]

/-! ## The matcher at selected occurrences -/

theorem open_matchRel {elements : List Pattern} {tail : Option String}
    (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
    (name process content : Pattern)
    (capability : elements[i] = .apply "AOpen" [name, process])
    (boundary : (elements.eraseIdx i)[j] = amb name content) :
    MatchRel openRule.left (.collection .hashBag elements tail)
      (openBindings name process content ((elements.eraseIdx i).eraseIdx j)) := by
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons i hi
  · rw [capability]
    exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl
  · apply MatchBagRel.cons j hj
    · rw [boundary]
      exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl
    · exact .nilRest
    · rfl
  · simp [openBindings, mergeBindings]

theorem in_matchRel {elements : List Pattern} {tail : Option String}
    (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
    (name target process host : Pattern) {inner : List Pattern} {innerTail : Option String}
    (k : ℕ) (hk : k < inner.length)
    (mover : elements[i] = amb name (.collection .hashBag inner innerTail))
    (capability : inner[k] = .apply "AIn" [target, process])
    (destination : (elements.eraseIdx i)[j] = amb target host) :
    MatchRel inRule.left (.collection .hashBag elements tail)
      (inBindings name target process host (inner.eraseIdx k) ((elements.eraseIdx i).eraseIdx j)) := by
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons i hi
  · rw [mover]
    apply MatchRel.apply (.cons .fvar (.cons (.collection (by decide)
      (.cons k hk (by rw [capability]; exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl) .nilRest rfl))
      .nil rfl) rfl) rfl
  · apply MatchBagRel.cons j hj
    · rw [destination]
      exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl
    · exact .nilRest
    · rfl
  · simp [inBindings, mergeBindings]

theorem out_matchRel {contents : List Pattern} {tail : Option String}
    (i : ℕ) (hi : i < contents.length) (name parent process : Pattern)
    {inner : List Pattern} {innerTail : Option String} (k : ℕ) (hk : k < inner.length)
    (mover : contents[i] = amb name (.collection .hashBag inner innerTail))
    (capability : inner[k] = .apply "AOut" [parent, process]) :
    MatchRel outRule.left (amb parent (.collection .hashBag contents tail))
      (outBindings name parent process (inner.eraseIdx k) (contents.eraseIdx i)) := by
  simp only [outRule, amb, par]
  refine MatchRel.apply ?_ (by simp)
  apply MatchArgsRel.cons .fvar
  · apply MatchArgsRel.cons (.collection (by decide) (.cons i hi (by
      rw [mover]
      exact .apply (.cons .fvar (.cons (.collection (by decide)
        (.cons k hk (by rw [capability]; exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl) .nilRest rfl))
        .nil rfl) rfl) rfl) .nilRest rfl)) .nil rfl
  · simp [outBindings, mergeBindings]

/-! ## What the matcher finds -/

/-- A binary constructor over two metavariables matches its own terms. -/
theorem binary_match_iff (label first second : String) (distinct : first ≠ second) (target : Pattern)
    (bindings : Bindings) :
    MatchRel (.apply label [.fvar first, .fvar second]) target bindings ↔
      ∃ x y, target = .apply label [x, y] ∧ bindings = [(second, y), (first, x)] := by
  have notSame : (first == second) = false := by simpa [beq_eq_false_iff_ne] using distinct
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons firstMatch tail merged =>
        cases firstMatch
        cases tail with
        | cons secondMatch last mergedLast =>
          cases secondMatch
          cases last
          simp only [mergeBindings, List.foldlM_nil] at mergedLast merged
          cases mergedLast
          simp [List.find?, notSame] at merged
          exact ⟨_, _, rfl, merged.symm⟩
  · rintro ⟨x, y, rfl, rfl⟩
    exact .apply (.cons .fvar (.cons .fvar .nil rfl) (by simp [mergeBindings, List.find?, notSame])) rfl

/-- An ambient whose content is a bag holding a capability matches its own terms. -/
theorem ambientCapability_match_iff (capability : String) (target : Pattern) (bindings : Bindings) :
    MatchRel (amb (.fvar "n") (par [.apply capability [.fvar "m", .fvar "p"]] (some "inner"))) target bindings ↔
      ∃ (name parent process : Pattern) (inner : List Pattern) (innerTail : Option String) (k : ℕ)
        (hk : k < inner.length),
        target = amb name (.collection .hashBag inner innerTail) ∧ inner[k] = .apply capability [parent, process] ∧
          bindings = [("m", parent), ("p", process), ("inner", .collection .hashBag (inner.eraseIdx k) none),
            ("n", name)] := by
  constructor
  · intro matched
    simp only [amb, par] at matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons nameMatch tail merged =>
        cases nameMatch
        cases tail with
        | cons contentMatch last mergedLast =>
          cases last
          cases contentMatch with
          | collection _ bag =>
            cases bag with
            | cons k hk capabilityMatch remaining mergedCapability =>
              obtain ⟨parent, process, atCapability, rfl⟩ :=
                (binary_match_iff capability "m" "p" (by decide) _ _).mp capabilityMatch
              cases remaining
              simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil] at mergedLast merged mergedCapability
              simp [List.find?] at mergedCapability
              subst mergedCapability
              cases mergedLast
              simp [List.find?] at merged
              exact ⟨_, parent, process, _, _, k, hk, rfl, atCapability, merged.symm⟩
  · rintro ⟨name, parent, process, inner, innerTail, k, hk, rfl, atCapability, rfl⟩
    have contentMatch : MatchRel (par [.apply capability [.fvar "m", .fvar "p"]] (some "inner"))
        (.collection .hashBag inner innerTail)
        [("inner", .collection .hashBag (inner.eraseIdx k) none), ("p", process), ("m", parent)] :=
      .collection (by decide) (.cons k hk
        ((binary_match_iff capability "m" "p" (by decide) _ _).mpr ⟨parent, process, atCapability, rfl⟩) .nilRest
        (by simp [mergeBindings, List.find?]))
    simp only [amb, par] at contentMatch ⊢
    exact .apply (.cons .fvar (.cons contentMatch .nil rfl) (by simp [mergeBindings, List.find?])) rfl

theorem open_match_inv {source : Pattern} {bindings : Bindings} (matched : MatchRel openRule.left source bindings) :
    ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
      (hj : j < (elements.eraseIdx i).length) (name process content : Pattern),
      source = .collection .hashBag elements tail ∧ elements[i] = .apply "AOpen" [name, process] ∧
        (elements.eraseIdx i)[j] = amb name content ∧
        bindings = openBindings name process content ((elements.eraseIdx i).eraseIdx j) := by
  simp only [openRule, par] at matched
  cases matched with
  | collection _ bag =>
    cases bag with
    | cons i hi first remaining mergedFirst =>
      obtain ⟨name, process, atCapability, rfl⟩ := (binary_match_iff "AOpen" "n" "p" (by decide) _ _).mp first
      cases remaining with
      | cons j hj second last mergedSecond =>
        obtain ⟨name', content, atBoundary, rfl⟩ :=
          (binary_match_iff "AAmb" "n" "q" (by decide) _ _).mp (by simpa [amb] using second)
        cases last
        simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil] at mergedSecond mergedFirst
        simp [List.find?] at mergedSecond
        subst mergedSecond
        simp [List.find?] at mergedFirst
        obtain ⟨rfl, rfl⟩ := mergedFirst
        exact ⟨_, _, i, hi, j, hj, name, process, content, rfl, atCapability, by simpa [amb] using atBoundary, rfl⟩

theorem in_match_inv {source : Pattern} {bindings : Bindings} (matched : MatchRel inRule.left source bindings) :
    ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
      (hj : j < (elements.eraseIdx i).length) (name target process host : Pattern) (inner : List Pattern)
      (innerTail : Option String) (k : ℕ) (hk : k < inner.length),
      source = .collection .hashBag elements tail ∧ elements[i] = amb name (.collection .hashBag inner innerTail) ∧
        inner[k] = .apply "AIn" [target, process] ∧ (elements.eraseIdx i)[j] = amb target host ∧
        bindings = inBindings name target process host (inner.eraseIdx k) ((elements.eraseIdx i).eraseIdx j) := by
  simp only [inRule] at matched
  cases matched with
  | collection _ bag =>
    cases bag with
    | cons i hi first remaining mergedFirst =>
      obtain ⟨name, target, process, inner, innerTail, k, hk, atMover, atCapability, rfl⟩ :=
        (ambientCapability_match_iff "AIn" _ _).mp first
      cases remaining with
      | cons j hj second last mergedSecond =>
        obtain ⟨target', host, atDestination, rfl⟩ :=
          (binary_match_iff "AAmb" "m" "s" (by decide) _ _).mp (by simpa [amb] using second)
        cases last
        simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil] at mergedSecond mergedFirst
        simp [List.find?] at mergedSecond
        subst mergedSecond
        simp [List.find?] at mergedFirst
        obtain ⟨rfl, rfl⟩ := mergedFirst
        exact ⟨_, _, i, hi, j, hj, name, target, process, host, inner, innerTail, k, hk, rfl, atMover, atCapability,
          by simpa [amb] using atDestination, rfl⟩

theorem out_match_inv {source : Pattern} {bindings : Bindings} (matched : MatchRel outRule.left source bindings) :
    ∃ (contents : List Pattern) (tail : Option String) (i : ℕ) (hi : i < contents.length)
      (name parent process : Pattern) (inner : List Pattern) (innerTail : Option String) (k : ℕ)
      (hk : k < inner.length),
      source = amb parent (.collection .hashBag contents tail) ∧
        contents[i] = amb name (.collection .hashBag inner innerTail) ∧ inner[k] = .apply "AOut" [parent, process] ∧
        bindings = outBindings name parent process (inner.eraseIdx k) (contents.eraseIdx i) := by
  simp only [outRule, amb, par] at matched
  cases matched with
  | apply args _ =>
    cases args with
    | @cons _ parentTerm _ _ _ _ _ parentMatch tail merged =>
      cases parentMatch
      cases tail with
      | cons contentMatch last mergedLast =>
        cases last
        simp only [mergeBindings, List.foldlM_nil] at mergedLast
        cases mergedLast
        cases contentMatch with
        | collection _ bag =>
          cases bag with
          | cons i hi first remaining mergedFirst =>
            obtain ⟨name, parent', process, inner, innerTail, k, hk, atMover, atCapability, rfl⟩ :=
              (ambientCapability_match_iff "AOut" _ _).mp (by simpa [amb, par] using first)
            cases remaining
            simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil] at mergedFirst
            simp [List.find?] at mergedFirst
            subst mergedFirst
            by_cases same : parentTerm = parent'
            · subst same
              simp [mergeBindings, List.find?] at merged
              subst merged
              exact ⟨_, _, i, hi, name, parentTerm, process, inner, innerTail, k, hk, rfl, atMover, atCapability, rfl⟩
            · simp [mergeBindings, List.find?, same] at merged

theorem parCong_match_inv {source : Pattern} {bindings : Bindings}
    (matched : MatchRel parCongRule.left source bindings) :
    ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length),
      source = .collection .hashBag elements tail ∧
        bindings = [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])] := by
  simp only [parCongRule, par] at matched
  cases matched with
  | collection _ bag =>
    cases bag with
    | cons i hi first remaining merged =>
      cases first
      cases remaining
      simp [mergeBindings] at merged
      cases merged
      exact ⟨_, _, i, hi, rfl, rfl⟩

theorem ambCong_match_inv {source : Pattern} {bindings : Bindings}
    (matched : MatchRel ambCongRule.left source bindings) :
    ∃ name content, source = amb name content ∧ bindings = [("S", content), ("n", name)] := by
  obtain ⟨name, content, rfl, rfl⟩ := (binary_match_iff "AAmb" "n" "S" (by decide) _ _).mp
    (by simpa [ambCongRule, amb] using matched)
  exact ⟨name, content, rfl, rfl⟩

theorem resCong_match_inv {source : Pattern} {bindings : Bindings}
    (matched : MatchRel resCongRule.left source bindings) :
    ∃ binder body, source = .apply "ANu" [.lambda binder body] ∧ bindings = [("S", body)] := by
  simp only [resCongRule] at matched
  cases matched with
  | apply args _ =>
    cases args with
    | cons bodyMatch last merged =>
      cases bodyMatch with
      | lambda bodyMatch =>
        cases bodyMatch
        cases last
        simp [mergeBindings] at merged
        cases merged
        exact ⟨_, _, rfl, rfl⟩

/-! ## The rules fire as specified -/

private theorem raw_of_stepAt {fuel : ℕ} {source target : Pattern}
    (step : StepAt (engineBasePremises RelationEnv.empty) ambientNuCalc fuel source target) :
    AmbNuRawStep source target := by
  induction fuel using Nat.strong_induction_on generalizing source target with
  | h fuel ih =>
    cases step with
    | @rule innerFuel source target rule initial final member matching premises result =>
      rw [ambientNuCalc_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [matchPatternForRule_eq_syntactic] at matching
      have matchRel := matchPattern_iff_matchRel.mp matching
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
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
    (step : Step (engineBasePremises RelationEnv.empty) ambientNuCalc source target) : AmbNuRawStep source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact raw_of_stepAt bounded

/-- **Every firing of the specification is a firing of the authored rules.** -/
theorem step_of_raw {source target : Pattern} (step : AmbNuRawStep source target) :
    Step (engineBasePremises RelationEnv.empty) ambientNuCalc source target := by
  induction step with
  | «open» i hi j hj name process content capability boundary =>
    refine ⟨1, .rule (rule := openRule) (by rw [ambientNuCalc_rewrites]; simp) ?_ (.nil _)
      (open_apply_exact name process content _)⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (open_matchRel i hi j hj name process content capability boundary)
  | enter i hi j hj name target process host k hk mover capability destination =>
    refine ⟨1, .rule (rule := inRule) (by rw [ambientNuCalc_rewrites]; simp) ?_ (.nil _)
      (in_apply_exact name target process host _ _)⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr
      (in_matchRel i hi j hj name target process host k hk mover capability destination)
  | exit i hi name parent process k hk mover capability =>
    refine ⟨1, .rule (rule := outRule) (by rw [ambientNuCalc_rewrites]; simp) ?_ (.nil _)
      (out_apply_exact name parent process _ _)⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr (out_matchRel i hi name parent process k hk mover capability)
  | @par elements tail i hi target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := parCongRule)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])]) (by rw [ambientNuCalc_rewrites]; simp) ?_ ?_ (parCong_apply_exact _ _ _)⟩
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
    · rw [ambientNuCalc_rewrites]; simp
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
      (by rw [ambientNuCalc_rewrites]; simp) ?_ ?_ (ambCong_apply_exact name content target)⟩
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
    Step (engineBasePremises RelationEnv.empty) ambientNuCalc source target ↔ AmbNuRawStep source target :=
  ⟨raw_of_step, step_of_raw⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Full
