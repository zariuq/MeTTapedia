import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CertificateEquations

/-!
# Certificates for equations with binders, read with fresh values

The first-order equation check (`Certificate.equationCheck`) refuses equations with binders. An equation with binders
captures each metavariable under the binders around it on the matched side, and the scoped instantiation puts its value
under the binders around each use on the other side: lifted when it is used under more binders, as it is. Used under
fewer, the value would have to be lowered, and a bound variable of it would change binder. The fresh discipline
(`EquationDiscipline.fresh`) binds such a metavariable to a closed pattern, which is the side condition of laws like η,
`Lam (λx. App F x) = F` with `x` not free in `F`.

**Fresh tables** (`freshSpec`, `freshDepth`): read from one side to the other, a metavariable denotes a function of the
binders it is captured under, or a constant when the other side uses it under fewer. A model passes the check for an
equation (`Certificate.freshEquationCheck`) when, in both directions, both sides have one value under every fresh table,
read the way the scoped instantiation reads them (`outerValuation`).

Every instance of a checked equation keeps the value, at every environment of the bound variables around it
(`Certificate.fresh_direction_eval_eq`), so a model that passes the checks respects every reading of the equations whose
discipline is fresh or closed (`respectsEquations_of_freshEquationsValid`). The syntax theory is not respected in
general: there, `λy. Lam (λx. App x x)` is an η-instance of `λy. y`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.Framework.FiniteModels
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.MatchSpec (matchPattern_sound BindingsExtends)
open Mettapedia.GSLT.LanguageDef.WellSorted (isObjectPattern)

variable {A : Type}

/-! ## Use depths are occurrences -/

mutual
theorem mem_useDepths (name : String) : ∀ (depth : ℕ) (pattern : Pattern) (used : ℕ),
    used ∈ useDepths name depth pattern ↔ (name, used) ∈ occurrences depth pattern
  | depth, .fvar other, used => by
    simp only [useDepths, occurrences, List.mem_singleton, Prod.mk.injEq]
    split
    · rename_i same
      simp only [beq_iff_eq] at same
      subst same
      simp [eq_comm]
    · rename_i differs
      simp only [beq_iff_eq] at differs
      simp only [List.not_mem_nil, false_iff, not_and]
      exact fun same => absurd same.symm differs
  | _, .bvar _, _ => by simp [useDepths, occurrences]
  | depth, .apply _ arguments, used => by
    simp only [useDepths, occurrences]
    exact mem_useDepthsList name depth arguments used
  | depth, .lambda _ body, used => by
    simp only [useDepths, occurrences]
    exact mem_useDepths name (depth + 1) body used
  | depth, .multiLambda arity _ body, used => by
    simp only [useDepths, occurrences]
    exact mem_useDepths name (depth + arity) body used
  | depth, .subst body replacement, used => by
    simp only [useDepths, occurrences, List.mem_append, mem_useDepths name (depth + 1) body used,
      mem_useDepths name depth replacement used]
  | depth, .collection _ elements rest, used => by
    simp only [useDepths, occurrences, List.mem_append, mem_useDepthsList name depth elements used]
    cases rest with
    | none => simp
    | some restName =>
      by_cases same : restName = name
      · subst same
        simp [eq_comm]
      · simp [same, Ne.symm same]

theorem mem_useDepthsList (name : String) : ∀ (depth : ℕ) (patterns : List Pattern) (used : ℕ),
    used ∈ useDepthsList name depth patterns ↔ (name, used) ∈ occurrencesList depth patterns
  | _, [], _ => by simp [useDepthsList, occurrencesList]
  | depth, pattern :: patterns, used => by
    simp only [useDepthsList, occurrencesList, List.mem_append, mem_useDepths name depth pattern used,
      mem_useDepthsList name depth patterns used]
end

/-! ## Fresh tables -/

/-- **The depth of a metavariable's table**, read from the matched side to the instantiated one: the depth it is
captured at, or none of its binders when the instantiated side uses it under fewer, where fresh values bind it closed. -/
def freshDepth (matched instantiated : Pattern) (name : String) : ℕ :=
  match captureDepth name 0 matched with
  | some captured => if (useDepths name 0 instantiated).all (captured ≤ ·) then captured else 0
  | none => 0

/-- The metavariables of the matched side, each at the depth of its table. -/
def freshSpec (matched instantiated : Pattern) : List (String × ℕ) :=
  ((occurrences 0 matched).map (·.1)).dedup.map fun name => (name, freshDepth matched instantiated name)

/-- **The shape a fresh check needs**: both sides in scope, every metavariable of the matched side at the depth it is
captured at, and the instantiated side using only metavariables and rest variables of the matched side. -/
def freshShape (matched instantiated : Pattern) : Bool :=
  matched.isWellScopedAt 0 && instantiated.isWellScopedAt 0 &&
    (occurrences 0 matched).all (fun entry => captureDepth entry.1 0 matched == some entry.2) &&
    (occurrences 0 instantiated).all (fun entry => (captureDepth entry.1 0 matched).isSome) &&
    (restVars instantiated).all (· ∈ restVars matched)

theorem freshSpec_keys (matched instantiated : Pattern) : ((freshSpec matched instantiated).map Prod.fst).Nodup := by
  simp only [freshSpec, List.map_map]
  have : (Prod.fst ∘ fun name : String => (name, freshDepth matched instantiated name)) = id := rfl
  rw [this, List.map_id]
  exact List.nodup_dedup _

theorem mem_freshSpec {matched instantiated : Pattern} {entry : String × ℕ} (inside : entry ∈ occurrences 0 matched) :
    (entry.1, freshDepth matched instantiated entry.1) ∈ freshSpec matched instantiated := by
  simp only [freshSpec, List.mem_map, List.mem_dedup]
  exact ⟨entry.1, ⟨entry, inside, rfl⟩, rfl⟩

namespace Certificate

variable [DecidableEq A] (certificate : Certificate A)

/-- **One direction of an equation holds in the model**: under every fresh table, read the way the scoped
instantiation reads it, the two sides have one value. -/
def freshDirectionCheck (matched instantiated : Pattern) : Bool :=
  freshShape matched instantiated &&
    (tables certificate.elements (freshSpec matched instantiated)).all fun table =>
      eval certificate.model (outerValuation (freshDepth matched instantiated)
          (tableValuation certificate.model certificate.elements table)) [] matched ==
        eval certificate.model (outerValuation (freshDepth matched instantiated)
          (tableValuation certificate.model certificate.elements table)) [] instantiated

/-- **An equation, possibly with binders, holds in the model**, in both directions. -/
def freshEquationCheck (equation : Equation) : Bool :=
  freshDirectionCheck certificate equation.left equation.right &&
    freshDirectionCheck certificate equation.right equation.left

/-- **The model respects the language's equations, read with fresh values**: its collection laws, and every authored
equation in both directions. -/
def freshEquationsValid (language : LanguageDef) : Bool :=
  collectionLawsValid certificate language && language.equations.all (freshEquationCheck certificate)

variable {certificate}

theorem freshEquationsValid_collectionLaws {language : LanguageDef}
    (checked : freshEquationsValid certificate language = true) : collectionLawsValid certificate language = true := by
  simp only [freshEquationsValid, Bool.and_eq_true] at checked
  exact checked.1

theorem freshEquationsValid_equation {language : LanguageDef} (checked : freshEquationsValid certificate language = true)
    {equation : Equation} (member : equation ∈ language.equations) :
    freshDirectionCheck certificate equation.left equation.right = true ∧
      freshDirectionCheck certificate equation.right equation.left = true := by
  simp only [freshEquationsValid, Bool.and_eq_true, List.all_eq_true] at checked
  have this := checked.2 equation member
  simp only [freshEquationCheck, Bool.and_eq_true] at this
  exact this

/-! ## Instances keep the value -/

omit [DecidableEq A] in
/-- A closed pattern has one value at every environment. -/
theorem eval_closed (model : FiniteModel A) {pattern : Pattern} (closed : pattern.isWellScopedAt 0 = true)
    (env : List A) : eval model (stateValuation model) env pattern = eval model (stateValuation model) [] pattern := by
  have shifted := eval_shift model (stateValuation model) env pattern [] closed
  rw [show shiftValuation (stateValuation model) env = stateValuation model from rfl] at shifted
  simpa using shifted

omit [DecidableEq A] in
/-- A metavariable bound to a closed pattern has one value at every environment. -/
theorem bindingValuation_closed (model : FiniteModel A) {bindings : Bindings} {name : String}
    (closed : (applyBindings bindings (.fvar name)).isWellScopedAt 0 = true) (env env' : List A) :
    bindingValuation model bindings name env = bindingValuation model bindings name env' := by
  simp only [bindingValuation]
  cases found : bindings.find? (·.1 == name) with
  | none => rfl
  | some pair =>
    obtain ⟨_, bound⟩ := pair
    simp only [applyBindings, found] at closed
    simp only
    rw [eval_closed model closed env, eval_closed model closed env']

/-- The scoped instantiation reads the depth a metavariable of the matched side is captured at there. -/
theorem captureDepth_sites {matched : Pattern} {premises : List Premise} {name : String} {captured : ℕ}
    (found : captureDepth name 0 matched = some captured) :
    captureDepth name 0 (captureSitesOf matched premises) = some captured := by
  have first : ∀ (rest : List Pattern), captureDepthList name 0 (matched :: rest) = some captured := by
    intro rest
    simp [captureDepthList, found]
  have sitesList : ∃ rest, premises.foldl (fun sites premise => sites ++ premiseSites sites premise) [matched] =
      matched :: rest := by
    have general : ∀ (premises : List Premise) (start rest : List Pattern), start = matched :: rest →
        ∃ rest', premises.foldl (fun sites premise => sites ++ premiseSites sites premise) start = matched :: rest' := by
      intro premises
      induction premises with
      | nil => exact fun start rest same => ⟨rest, by simpa using same⟩
      | cons premise premises inductionHypothesis =>
        intro start rest same
        simp only [List.foldl_cons]
        exact inductionHypothesis _ (rest ++ premiseSites start premise) (by rw [same, List.cons_append])
    exact general premises [matched] [] rfl
  obtain ⟨rest, same⟩ := sitesList
  simp only [captureSitesOf, captureDepth, same]
  exact first rest

/-- **One direction of a checked equation keeps the value** at every environment, at an instance whose bindings are
fresh for it. -/
theorem fresh_direction_eval_eq (commutes : LeftCommutes certificate.model) {matched instantiated : Pattern}
    (checked : freshDirectionCheck certificate matched instantiated = true) {premises : List Premise}
    {source : Pattern} {initial final : Bindings} (matchedAt : initial ∈ matchPattern matched source)
    (extension : BindingsExtends initial final)
    (fresh : ScopedValues (captureSitesOf matched premises) instantiated final)
    (object : isObjectPattern source = true) (outer : List A) :
    eval certificate.model (stateValuation certificate.model) outer source =
      eval certificate.model (stateValuation certificate.model) outer
        (applyBindingsScoped (captureSitesOf matched premises) final 0 instantiated) := by
  simp only [freshDirectionCheck, freshShape, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
    at checked
  obtain ⟨⟨⟨⟨⟨matchedScoped, instantiatedScoped⟩, matchedDepths⟩, instantiatedCaptured⟩, restsCovered⟩, agree⟩ :=
    checked
  have relation := matchPattern_sound matchedAt
  have instantiatedBound : RestsBound final instantiated := fun entry inside =>
    restsBound_of_matchRel relation final extension entry (restsCovered entry inside)
  have sourceValue : eval certificate.model (stateValuation certificate.model) outer source =
      eval certificate.model (bindingValuation certificate.model final) outer matched := by
    rw [← eval_of_matchRel certificate.model commutes relation object final extension outer]
    exact eval_applyBindings certificate.model final matched (restsBound_of_matchRel relation final extension) outer
  have targetValue : eval certificate.model (stateValuation certificate.model) outer
        (applyBindingsScoped (captureSitesOf matched premises) final 0 instantiated) =
      eval certificate.model (scopedValuation certificate.model (captureSitesOf matched premises) final outer.length)
        outer instantiated :=
    eval_applyBindingsScoped certificate.model (captureSitesOf matched premises) final outer instantiated
      instantiatedBound []
  have shiftLeft := eval_shift certificate.model (bindingValuation certificate.model final) outer matched []
    matchedScoped
  have shiftRight := eval_shift certificate.model
    (scopedValuation certificate.model (captureSitesOf matched premises) final outer.length) outer instantiated []
    instantiatedScoped
  simp only [List.nil_append] at shiftLeft shiftRight
  rw [sourceValue, targetValue, shiftLeft, shiftRight]
  obtain ⟨table, tableMember, realizes⟩ := exists_table certificate.model certificate.elements certificate.complete
    (shiftValuation (bindingValuation certificate.model final) outer) (freshSpec matched instantiated)
    (freshSpec_keys matched instantiated)
  let read := outerValuation (freshDepth matched instantiated)
    (tableValuation certificate.model certificate.elements table)
  -- A metavariable used under fewer binders than it is captured under has a closed value.
  have closedOf : ∀ name captured, captureDepth name 0 matched = some captured →
      ¬ (useDepths name 0 instantiated).all (captured ≤ ·) = true →
      (applyBindings final (.fvar name)).isWellScopedAt 0 = true := by
    intro name captured found notAll
    refine fresh name captured (captureDepth_sites found) ?_
    simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at notAll
    obtain ⟨used, member, shallower⟩ := notAll
    exact ⟨used, member, by omega⟩
  -- With no binders around, the table reads a metavariable's value outside any binder.
  have atNone : ∀ name, (name, freshDepth matched instantiated name) ∈ freshSpec matched instantiated →
      freshDepth matched instantiated name = 0 →
      tableValuation certificate.model certificate.elements table name [] =
        bindingValuation certificate.model final name outer := by
    intro name member zero
    have := realizes (name, freshDepth matched instantiated name) member [] (by simp [zero])
    simpa [shiftValuation] using this
  have leftAgree : eval certificate.model (shiftValuation (bindingValuation certificate.model final) outer) []
      matched = eval certificate.model read [] matched :=
    eval_congr certificate.model matched [] fun entry inside inner length => by
      have home := matchedDepths entry inside
      have member := mem_freshSpec (instantiated := instantiated) inside
      simp only [read, outerValuation, shiftValuation]
      by_cases deep : (useDepths entry.1 0 instantiated).all (entry.2 ≤ ·) = true
      · have depthIs : freshDepth matched instantiated entry.1 = entry.2 := by
          simp only [freshDepth, home, deep, ↓reduceIte]
        rw [depthIs, length, Nat.sub_self, List.drop_zero]
        rw [depthIs] at member
        rw [realizes (entry.1, entry.2) member inner (by omega), List.take_of_length_le (by omega)]
        rfl
      · have depthIs : freshDepth matched instantiated entry.1 = 0 := by
          simp only [freshDepth, home, deep, ↓reduceIte, Bool.false_eq_true]
        rw [depthIs, Nat.sub_zero, List.drop_length]
        rw [depthIs] at member
        rw [atNone entry.1 (by rw [depthIs]; exact member) depthIs]
        exact bindingValuation_closed certificate.model (closedOf entry.1 entry.2 home deep) _ _
  have rightAgree : eval certificate.model
        (shiftValuation (scopedValuation certificate.model (captureSitesOf matched premises) final outer.length) outer)
        [] instantiated = eval certificate.model read [] instantiated :=
    eval_congr certificate.model instantiated [] fun entry inside inner length => by
      obtain ⟨captured, found⟩ := Option.isSome_iff_exists.mp (instantiatedCaptured entry inside)
      have occurs := mem_occurrences_of_captureDepth entry.1 0 matched captured found
      have member := mem_freshSpec (instantiated := instantiated) occurs
      have used : entry.2 ∈ useDepths entry.1 0 instantiated := (mem_useDepths entry.1 0 instantiated entry.2).mpr inside
      simp only [read, outerValuation, shiftValuation, scopedValuation, captureDepth_sites found]
      by_cases deep : (useDepths entry.1 0 instantiated).all (captured ≤ ·) = true
      · have depthIs : freshDepth matched instantiated entry.1 = captured := by
          simp only [freshDepth, found, deep, ↓reduceIte]
        have deeper : captured ≤ entry.2 := by
          simp only [List.all_eq_true, decide_eq_true_eq] at deep
          exact deep entry.2 used
        rw [depthIs] at member ⊢
        rw [realizes (entry.1, captured) member _ (by simp; omega), List.take_of_length_le (by simp; omega)]
        simp only [shiftValuation, bindingValuation]
        cases bound : final.find? (·.1 == entry.1) with
        | none => rfl
        | some pair =>
          obtain ⟨_, value⟩ := pair
          simp only [List.length_append]
          rw [show inner.length + outer.length - outer.length - captured = inner.length - captured by omega,
            List.drop_append_of_le_length (by omega)]
      · have depthIs : freshDepth matched instantiated entry.1 = 0 := by
          simp only [freshDepth, found, deep, ↓reduceIte, Bool.false_eq_true]
        rw [depthIs, Nat.sub_zero, List.drop_length]
        rw [depthIs] at member
        rw [atNone entry.1 (by rw [depthIs]; exact member) depthIs]
        have closed := closedOf entry.1 captured found deep
        have sameValue := bindingValuation_closed certificate.model closed
          ((inner ++ outer).drop ((inner ++ outer).length - outer.length - captured)) outer
        simp only [bindingValuation] at sameValue ⊢
        cases bound : final.find? (·.1 == entry.1) with
        | none => rfl
        | some pair =>
          rw [bound] at sameValue
          exact sameValue
  rw [leftAgree, rightAgree]
  exact agree table tableMember

/-- **The authored instances of a fresh or closed discipline keep the value**, at every environment. -/
theorem fresh_authored_eval_eq {relEnv : RelationEnv} {language : LanguageDef}
    (contextual : certificate.contextualValid language = true) (checked : freshEquationsValid certificate language = true)
    {discipline : EquationDiscipline} (strict : discipline.rank ≤ EquationDiscipline.fresh.rank) {source target : Pattern}
    (instance_ : DisciplinedEquation relEnv language discipline source target) (object : isObjectPattern source = true)
    (outer : List A) :
    eval certificate.model (stateValuation certificate.model) outer source =
      eval certificate.model (stateValuation certificate.model) outer target := by
  have commutes := Mettapedia.OSLF.Framework.FiniteModels.Certificate.preorder_commutes
    (Mettapedia.OSLF.Framework.FiniteModels.Certificate.contextual_preorder contextual)
  cases instance_ with
  | @forward equation _ initial final witnesses member _ matched premises _ scope =>
    have fresh : ScopedValues (captureSitesOf equation.left equation.premises) equation.right final := by
      cases discipline with
      | raw => exact absurd strict (by decide)
      | sorted => exact absurd strict (by decide)
      | fresh => exact scope
      | closed => exact scope
    exact fresh_direction_eval_eq commutes (freshEquationsValid_equation checked member).1 matched
      (premisesValid_extends premises) fresh object outer
  | @reverse equation _ initial final witnesses member _ matched premises _ scope =>
    have fresh : ScopedValues (captureSitesOf equation.right equation.premises) equation.left final := by
      cases discipline with
      | raw => exact absurd strict (by decide)
      | sorted => exact absurd strict (by decide)
      | fresh => exact scope
      | closed => exact scope
    exact fresh_direction_eval_eq commutes (freshEquationsValid_equation checked member).2 matched
      (premisesValid_extends premises) fresh object outer
  | declared raw _ _ _ =>
    subst raw
    exact absurd strict (by decide)
  | premised raw _ _ _ _ =>
    subst raw
    exact absurd strict (by decide)

end Certificate

/-- **A model that passes the fresh checks respects every reading of the equations whose discipline is fresh or
closed.** -/
theorem respectsEquations_of_freshEquationsValid [DecidableEq A] {certificate : Certificate A} {relEnv : RelationEnv}
    {language : LanguageDef} (contextual : certificate.contextualValid language = true)
    (checked : Certificate.freshEquationsValid certificate language = true) {reading : LanguageReading}
    (fresh : reading.equations.discipline.rank ≤ EquationDiscipline.fresh.rank) :
    RespectsEquations certificate relEnv language reading := by
  intro first second equivalent
  induction equivalent with
  | rel _ _ step =>
    obtain ⟨firstObject, -, step⟩ := step
    cases readingStep_discipline step with
    | @inContext context redex contractum generator =>
      have same : ∀ outer, eval certificate.model (stateValuation certificate.model) outer redex =
          eval certificate.model (stateValuation certificate.model) outer contractum := by
        rcases generator with authored | derived
        · exact Certificate.fresh_authored_eval_eq contextual checked fresh authored (object_of_fill context firstObject)
        · exact Certificate.derived_eval_eq contextual (Certificate.freshEquationsValid_collectionLaws checked) derived
      exact eval_fill_congr certificate.model (stateValuation certificate.model) same context []
  | refl => rfl
  | symm _ _ _ previous => exact previous.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **Terms the model tells apart are not equivalent** in a reading the model respects. -/
theorem not_objectEquivalent_of_value [DecidableEq A] {certificate : Certificate A} {relEnv : RelationEnv}
    {language : LanguageDef} {reading : LanguageReading} (respects : RespectsEquations certificate relEnv language reading)
    {first second : Pattern} (apart : value certificate.model first ≠ value certificate.model second) :
    ¬ ObjectEquivalent relEnv language reading first second :=
  fun equivalent => apart (respects first second equivalent)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
