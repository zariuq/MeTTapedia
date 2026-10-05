import Mettapedia.GSLT.Causality.ContextOperators
import Mettapedia.GSLT.Dynamics.DemandAgreement
import Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary

/-!
# Interventions by binding: explicit `do` against `do` derived from binding override

An intervention `do(x := v)` is a context.  It can be written in two ways.

* **Explicit `do`** (`OverrideAction.explicitRules`): a context is a partial
  assignment of values to keys, composed by letting the outer assignment win
  (`override`), and plugged by one simultaneous override.
* **Derived `do`** (`OverrideAction.derivedRules`): a context is a chain of
  bindings, Prime's first-class context (`DemandBoundary.Context`, the Lean
  model of `ctx:bind`, newest binding first), composed by grafting one chain on
  another (`graft`), and plugged one binding at a time, oldest first.

## On the ladder the choice evaporates

Plugging a chain is assigning its newest-wins lookup, up to the equations
(`bindingPlug_equiv_assign`).  So the chains whose keys lie in a region and
the finitely supported assignments whose support lies in it have the same
plug maps (`covers_derived_explicit`, `covers_explicit_derived`), and by
`ContextOperators.agree_iff_of_covers` they have the same three rungs and the
same distances (`explicit_derived_agree`,
`explicit_derived_interventionalDistance`,
`explicit_derived_counterfactualDistance`).  Over infinitely many keys an
explicit assignment can intervene on infinitely many keys at once, and no
chain can; the controls exhibit a pair that this separates.

Composition behaves as interventions should (`do_override`,
`commute_of_disjoint`, `do_commute_of_ne`), and a region of keys determines a
class of contexts (`regionDerived`, `regionExplicit`), monotone in the region
(`regionDerived_mono`).

## When the binding is a computation the choice is the demand choice

Prime's `ctx:bind` binds any expression, lazily, in one Need cell shared by
every read.  An explicit `do` takes a value, so a computation given to it is
evaluated where the intervention is made.  Over contexts that bind
computations (bags of answers) and a body that reads keys, three semantics
stand side by side:

* `explicitAnswers`: every binding is drawn once when made, used or not;
* `derivedAnswers`: one shared draw for each key the body reads;
* `experimentAnswers`: every read draws afresh (resampling).

For one binding read `n` times they are exactly eager sharing, lazy sharing
and resampling (`explicitAnswers_doBinding`, `derivedAnswers_doBinding`,
`experimentAnswers_doBinding`), so `Dynamics.DemandAgreement` decides when they
agree:

* explicit and derived `do` agree over bags exactly when the binding is read
  at least once or has one answer (`explicit_eq_derived_iff`), and over
  supports exactly when it is read or has an answer
  (`explicit_derived_support_iff`); they never differ on sharing, and they
  differ on effects whenever the binding is unread (`explicitDraws_doBinding`,
  `derivedDraws_doBinding`);
* the override law `do(x := a); do(x := b) = do(x := b)` holds for derived
  `do` always (`derived_override`) and for explicit `do` exactly when the
  shadowed computation has one answer or the newer one none
  (`explicit_override_iff`): a shadowed explicit intervention still runs;
* interventions on different keys commute under both (`explicit_commute`,
  `derived_commute`);
* **retention**: the counterfactual twin reads the exogenous cell twice,
  shared; the experiment resamples it.  They coincide exactly when the cell
  has at most one answer (`twin_eq_experiment_iff`), on supports exactly when
  its support has at most one element (`twin_experiment_support_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ContextBindings

open Mettapedia.GSLT
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.ContextOperators
open Mettapedia.GSLT.Causality.Identifiability
open Mettapedia.GSLT.Dynamics.DemandAgreement

universe uS uK uV uAtom uObs

/-! ## Assignments -/

section Assignments

variable {Key : Type uK} {Value : Type uV}

/-- **Composition of explicit interventions**: the outer assignment wins where
it assigns. -/
def override (outer inner : Key → Option Value) : Key → Option Value :=
  fun key => (outer key).or (inner key)

@[simp] theorem override_apply (outer inner : Key → Option Value) (key : Key) :
    override outer inner key = (outer key).or (inner key) :=
  rfl

theorem override_none_left (assignment : Key → Option Value) :
    override (fun _ => none) assignment = assignment :=
  rfl

theorem override_none_right (assignment : Key → Option Value) :
    override assignment (fun _ => none) = assignment := by
  funext key
  simp only [override_apply]
  cases assignment key <;> rfl

theorem override_assoc (first second third : Key → Option Value) :
    override (override first second) third = override first (override second third) := by
  funext key
  simp only [override_apply]
  cases first key <;> rfl

/-- Assignments with disjoint supports commute. -/
theorem override_comm {first second : Key → Option Value}
    (disjoint : ∀ key, first key = none ∨ second key = none) :
    override first second = override second first := by
  funext key
  rcases disjoint key with none₁ | none₂
  · simp only [override_apply, none₁, Option.none_or]
    cases second key <;> rfl
  · simp only [override_apply, none₂, Option.none_or]
    cases first key <;> rfl

/-- The keys an assignment assigns. -/
def support (assignment : Key → Option Value) : Set Key :=
  {key | (assignment key).isSome}

theorem support_none : support (fun _ : Key => (none : Option Value)) = ∅ := by
  ext key
  simp [support]

theorem support_override (outer inner : Key → Option Value) :
    support (override outer inner) ⊆ support outer ∪ support inner := by
  intro key member
  change (override outer inner key).isSome at member
  change (outer key).isSome ∨ (inner key).isSome
  rw [override_apply] at member
  cases hOuter : outer key with
  | none => rw [hOuter, Option.none_or] at member; exact Or.inr member
  | some _ => exact Or.inl rfl

variable [DecidableEq Key]

/-- The assignment of one value to one key. -/
def single (key : Key) (value : Value) : Key → Option Value :=
  fun other => if other = key then some value else none

/-- A single assignment, overriding one of the same key, wins. -/
theorem override_single_single (key : Key) (older newer : Value) :
    override (single key newer) (single key older) = single key newer := by
  funext other
  by_cases same : other = key <;> simp [single, same]

end Assignments

/-! ## Binding chains: the Lean model of `ctx:bind` -/

section Bindings

variable {Key : Type uK} {Value : Type uV}

/-- **Binding chains** are Prime's first-class contexts, newest binding
outermost (`DemandBoundary.Context`). -/
abbrev Bindings (Key : Type uK) (Value : Type uV) :=
  Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context Key Value

/-- Graft one chain on another: the outer chain's bindings are newer. -/
def graft : Bindings Key Value → Bindings Key Value → Bindings Key Value
  | .empty, inner => inner
  | .bind parent key value, inner => .bind (graft parent inner) key value

theorem graft_empty_right : ∀ bindings : Bindings Key Value, graft bindings .empty = bindings
  | .empty => rfl
  | .bind parent key value => by rw [graft, graft_empty_right parent]

theorem graft_assoc :
    ∀ first second third : Bindings Key Value,
      graft (graft first second) third = graft first (graft second third)
  | .empty, _, _ => rfl
  | .bind parent key value, second, third => by
      simp only [graft, graft_assoc parent second third]

/-- The keys a chain binds, newest first. -/
def keysOf (bindings : Bindings Key Value) : List Key :=
  bindings.entries.map Prod.fst

theorem keysOf_graft : ∀ outer inner : Bindings Key Value,
    keysOf (graft outer inner) = keysOf outer ++ keysOf inner
  | .empty, _ => rfl
  | .bind parent key value, inner => by
      change key :: keysOf (graft parent inner) = (key :: keysOf parent) ++ keysOf inner
      rw [keysOf_graft parent inner]
      rfl

variable [DecidableEq Key]

/-- The value a chain gives a key: its newest binding, or nothing. -/
def lookupValue (bindings : Bindings Key Value) (key : Key) : Option Value :=
  match bindings.lookup key with
  | .missing _ => none
  | .found value => some value

theorem lookupValue_empty : lookupValue (.empty : Bindings Key Value) = fun _ => none := by
  funext key
  rfl

theorem lookupValue_bind (parent : Bindings Key Value) (key : Key) (value : Value) :
    lookupValue (.bind parent key value) = override (single key value) (lookupValue parent) := by
  funext other
  by_cases same : other = key
  · subst same
    simp [lookupValue, single,
      Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.lookup]
  · simp [lookupValue, single, same,
      Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.lookup]

/-- **The lookup of a graft is the override of the lookups.** -/
theorem lookupValue_graft : ∀ outer inner : Bindings Key Value,
    lookupValue (graft outer inner) = override (lookupValue outer) (lookupValue inner)
  | .empty, inner => by rw [graft, lookupValue_empty, override_none_left]
  | .bind parent key value, inner => by
      rw [graft, lookupValue_bind, lookupValue_graft parent inner, lookupValue_bind,
        override_assoc]

theorem mem_keysOf_of_lookupValue : ∀ {bindings : Bindings Key Value} {key : Key},
    (lookupValue bindings key).isSome → key ∈ keysOf bindings
  | .empty, key, found => by simp [lookupValue_empty] at found
  | .bind parent bound value, key, found => by
      rw [lookupValue_bind] at found
      by_cases same : key = bound
      · simp [keysOf, same, Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.entries]
      · simp only [override_apply, single, same, if_false, Option.none_or] at found
        have := mem_keysOf_of_lookupValue found
        simp only [keysOf, Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.entries,
          List.map_cons, List.mem_cons] at this ⊢
        exact Or.inr this

/-- The keys a chain assigns lie among the keys it binds. -/
theorem support_lookupValue (bindings : Bindings Key Value) :
    support (lookupValue bindings) ⊆ {key | key ∈ keysOf bindings} :=
  fun _ found => mem_keysOf_of_lookupValue found

/-- A chain binding, in list order, every listed key that an assignment
assigns. -/
def bindingsOf (assignment : Key → Option Value) : List Key → Bindings Key Value
  | [] => .empty
  | key :: rest =>
      match assignment key with
      | some value => .bind (bindingsOf assignment rest) key value
      | none => bindingsOf assignment rest

theorem lookupValue_bindingsOf (assignment : Key → Option Value) :
    ∀ (keys : List Key) (key : Key),
      lookupValue (bindingsOf assignment keys) key = if key ∈ keys then assignment key else none
  | [], key => by simp [bindingsOf, lookupValue_empty]
  | first :: rest, key => by
      have inner := lookupValue_bindingsOf assignment rest key
      cases assigned : assignment first with
      | none =>
          simp only [bindingsOf, assigned]
          rw [inner]
          by_cases same : key = first
          · subst same
            simp [assigned]
          · simp [same]
      | some value =>
          simp only [bindingsOf, assigned]
          rw [lookupValue_bind]
          by_cases same : key = first
          · subst same
            simp [single, assigned]
          · simp [single, same, inner]

omit [DecidableEq Key] in
theorem keysOf_bindingsOf (assignment : Key → Option Value) :
    ∀ (keys : List Key) {key : Key}, key ∈ keysOf (bindingsOf assignment keys) → key ∈ keys
  | [], key, member => by simp [bindingsOf, keysOf,
      Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.entries] at member
  | first :: rest, key, member => by
      cases assigned : assignment first with
      | none =>
          simp only [bindingsOf, assigned] at member
          exact List.mem_cons_of_mem _ (keysOf_bindingsOf assignment rest member)
      | some value =>
          simp only [bindingsOf, assigned, keysOf,
            Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.entries,
            List.map_cons, List.mem_cons] at member
          rcases member with same | inner
          · exact same ▸ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (keysOf_bindingsOf assignment rest inner)

/-- **Every finitely supported assignment is the lookup of a chain.** -/
theorem exists_bindings_of_finite {assignment : Key → Option Value} (finite : (support assignment).Finite) :
    ∃ bindings : Bindings Key Value, lookupValue bindings = assignment ∧
      ∀ key ∈ keysOf bindings, key ∈ support assignment := by
  refine ⟨bindingsOf assignment finite.toFinset.toList, ?_, ?_⟩
  · funext key
    rw [lookupValue_bindingsOf]
    by_cases member : key ∈ support assignment
    · rw [if_pos (by simpa using member)]
    · rw [if_neg (by simpa using member)]
      have unassigned : (assignment key).isSome = false := by
        simpa [support] using member
      exact (Option.not_isSome_iff_eq_none.mp (by simpa using unassigned)).symm
  · intro key member
    simpa using keysOf_bindingsOf assignment _ member

end Bindings

/-! ## Two presentations over one GSLT -/

/-- **A GSLT whose terms carry values at keys that an assignment overrides**:
an action of the assignments, composed by `override`, up to the equations. -/
structure OverrideAction (S : GSLT.{uS}) (Key : Type uK) (Value : Type uV) where
  /-- Override the keys an assignment assigns. -/
  assign : (Key → Option Value) → S.Term → S.Term
  assign_none : ∀ term, S.Equiv (assign (fun _ => none) term) term
  assign_override : ∀ outer inner term,
    S.Equiv (assign (override outer inner) term) (assign outer (assign inner term))
  assign_resp : ∀ assignment {left right : S.Term}, S.Equiv left right →
    S.Equiv (assign assignment left) (assign assignment right)

namespace OverrideAction

variable {S : GSLT.{uS}} {Key : Type uK} {Value : Type uV} (O : OverrideAction S Key Value)

theorem assign_congr {first second : Key → Option Value} (same : first = second) (term : S.Term) :
    S.Equiv (O.assign first term) (O.assign second term) := by
  rw [same]
  exact S.equations.iseqv.refl _

/-- **Explicit `do`**: contexts are assignments. -/
def explicitRules : ContextualRules.{max uK uV, 0} S where
  Context := Key → Option Value
  identity := fun _ => none
  compose := override
  plug := O.assign
  plug_identity := O.assign_none
  plug_compose := O.assign_override
  plug_resp := O.assign_resp
  Rule := Unit
  fires _ := S.Step
  fires_resp_left := fun equivalent step => S.rewrites_resp_left equivalent step
  fires_resp_right := fun step equivalent => S.rewrites_resp_right step equivalent
  fires_step := fun step => step

/-- The finitely supported assignments whose support lies in a region. -/
def regionExplicit (region : Set Key) : AdmissibleClass O.explicitRules where
  Admissible assignment := (support assignment).Finite ∧ support assignment ⊆ region
  identity_mem := by
    change (support (fun _ : Key => (none : Option Value))).Finite ∧
      support (fun _ : Key => (none : Option Value)) ⊆ region
    rw [support_none]
    exact ⟨Set.finite_empty, Set.empty_subset _⟩
  compose_mem := fun outer inner =>
    ⟨(outer.1.union inner.1).subset (support_override _ _),
      (support_override _ _).trans (Set.union_subset outer.2 inner.2)⟩

variable [DecidableEq Key]

/-- Plug a chain one binding at a time, the oldest first: each binding is a
single override, as each `ctx:bind` is. -/
def bindingPlug : Bindings Key Value → S.Term → S.Term
  | .empty, term => term
  | .bind parent key value, term => O.assign (single key value) (bindingPlug parent term)

theorem bindingPlug_graft :
    ∀ (outer inner : Bindings Key Value) (term : S.Term),
      O.bindingPlug (graft outer inner) term = O.bindingPlug outer (O.bindingPlug inner term)
  | .empty, _, _ => rfl
  | .bind parent key value, inner, term => by
      simp only [graft, bindingPlug, bindingPlug_graft parent inner term]

theorem bindingPlug_resp :
    ∀ (bindings : Bindings Key Value) {left right : S.Term}, S.Equiv left right →
      S.Equiv (O.bindingPlug bindings left) (O.bindingPlug bindings right)
  | .empty, _, _, equivalent => equivalent
  | .bind parent _ _, _, _, equivalent => O.assign_resp _ (bindingPlug_resp parent equivalent)

/-- **Derived `do`**: contexts are binding chains, composed by grafting. -/
def derivedRules : ContextualRules.{max uK uV, 0} S where
  Context := Bindings Key Value
  identity := .empty
  compose := graft
  plug := O.bindingPlug
  plug_identity _ := S.equations.iseqv.refl _
  plug_compose outer inner term := by
    rw [bindingPlug_graft]
    exact S.equations.iseqv.refl _
  plug_resp := O.bindingPlug_resp
  Rule := Unit
  fires _ := S.Step
  fires_resp_left := fun equivalent step => S.rewrites_resp_left equivalent step
  fires_resp_right := fun step equivalent => S.rewrites_resp_right step equivalent
  fires_step := fun step => step

/-- **Derived `do` is explicit `do`**: plugging a chain is assigning its
newest-wins lookup, up to the equations. -/
theorem bindingPlug_equiv_assign :
    ∀ (bindings : Bindings Key Value) (term : S.Term),
      S.Equiv (O.bindingPlug bindings term) (O.assign (lookupValue bindings) term)
  | .empty, term => by
      rw [lookupValue_empty]
      exact S.equations.iseqv.symm (O.assign_none term)
  | .bind parent key value, term => by
      rw [lookupValue_bind]
      exact S.equations.iseqv.trans (O.assign_resp _ (bindingPlug_equiv_assign parent term))
        (S.equations.iseqv.symm (O.assign_override _ _ term))

/-- The chains whose keys lie in a region. -/
def regionDerived (region : Set Key) : AdmissibleClass O.derivedRules where
  Admissible bindings := ∀ key ∈ keysOf bindings, key ∈ region
  identity_mem := by
    intro key member
    change key ∈ keysOf (.empty : Bindings Key Value) at member
    simp [keysOf, Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.entries] at member
  compose_mem := by
    intro outer inner outerIn innerIn key member
    have split : key ∈ keysOf outer ++ keysOf inner :=
      Eq.mp (congrArg (fun keys => key ∈ keys) (keysOf_graft outer inner)) member
    rcases List.mem_append.mp split with inOuter | inInner
    · exact outerIn key inOuter
    · exact innerIn key inInner

/-- **A smaller region gives a smaller class.** -/
theorem regionDerived_mono {region region' : Set Key} (sub : region ⊆ region') :
    O.regionDerived region ≤ O.regionDerived region' :=
  fun _ admissible key member => sub (admissible key member)

omit [DecidableEq Key] in
theorem regionExplicit_mono {region region' : Set Key} (sub : region ⊆ region') :
    O.regionExplicit region ≤ O.regionExplicit region' :=
  fun _ admissible => ⟨admissible.1, admissible.2.trans sub⟩

/-- Every chain in a region is covered by a finitely supported assignment in
that region. -/
theorem covers_derived_explicit (region : Set Key) :
    Covers (O.regionDerived region) (O.regionExplicit region) := by
  intro bindings admissible
  refine ⟨lookupValue bindings, ⟨?_, ?_⟩, fun term => S.equations.iseqv.symm
    (O.bindingPlug_equiv_assign bindings term)⟩
  · exact (List.finite_toSet (keysOf bindings)).subset (support_lookupValue bindings)
  · exact fun key found => admissible key (support_lookupValue bindings found)

/-- Every finitely supported assignment in a region is covered by a chain in
that region. -/
theorem covers_explicit_derived (region : Set Key) :
    Covers (O.regionExplicit region) (O.regionDerived region) := by
  intro assignment admissible
  obtain ⟨bindings, same, keys⟩ := exists_bindings_of_finite admissible.1
  refine ⟨bindings, fun key member => admissible.2 (keys key member), fun term => ?_⟩
  change S.Equiv (O.bindingPlug bindings term) (O.assign assignment term)
  have := O.bindingPlug_equiv_assign bindings term
  rwa [same] at this

variable (observations : ContextualRules.Observations.{uAtom} S)

/-- **Explicit and derived `do` have the same ladder**, region by region. -/
theorem explicit_derived_agree (region : Set Key) (rung : Rung) (left right : S.Term) :
    Agree (O.regionExplicit region) observations rung left right ↔
      Agree (O.regionDerived region) observations rung left right :=
  agree_iff_of_covers observations (O.covers_explicit_derived region)
    (O.covers_derived_explicit region) rung left right

variable (base : GradedObservations.{uS, uObs} S) (discount : ℝ) (discount_nonneg : 0 ≤ discount)
  (discount_le_one : discount ≤ 1)

theorem explicit_derived_interventionalDistance (region : Set Key) (left right : S.Term) :
    interventionalDistance (O.regionExplicit region) base discount discount_nonneg discount_le_one
        left right =
      interventionalDistance (O.regionDerived region) base discount discount_nonneg discount_le_one
        left right :=
  interventionalDistance_eq_of_covers base discount discount_nonneg discount_le_one
    (O.covers_explicit_derived region) (O.covers_derived_explicit region) left right

theorem explicit_derived_counterfactualDistance (region : Set Key) (left right : S.Term) :
    counterfactualDistance (O.regionExplicit region) base discount discount_nonneg discount_le_one
        left right =
      counterfactualDistance (O.regionDerived region) base discount discount_nonneg discount_le_one
        left right :=
  counterfactualDistance_eq_of_covers base discount discount_nonneg discount_le_one
    (O.covers_explicit_derived region) (O.covers_derived_explicit region) left right

/-- **A smaller region separates less**, at every rung. -/
theorem agree_of_region_le {region region' : Set Key} (sub : region ⊆ region') (rung : Rung)
    {left right : S.Term} (agree : Agree (O.regionDerived region') observations rung left right) :
    Agree (O.regionDerived region) observations rung left right :=
  agree_antitone observations (O.regionDerived_mono sub) rung agree

theorem interventionalDistance_region_mono {region region' : Set Key} (sub : region ⊆ region')
    (left right : S.Term) :
    interventionalDistance (O.regionDerived region) base discount discount_nonneg discount_le_one
        left right ≤
      interventionalDistance (O.regionDerived region') base discount discount_nonneg discount_le_one
        left right :=
  interventionalDistance_mono _ base discount discount_nonneg discount_le_one
    (O.regionDerived_mono sub) left right

theorem counterfactualDistance_region_mono {region region' : Set Key} (sub : region ⊆ region')
    (left right : S.Term) :
    counterfactualDistance (O.regionDerived region) base discount discount_nonneg discount_le_one
        left right ≤
      counterfactualDistance (O.regionDerived region') base discount discount_nonneg discount_le_one
        left right :=
  saturatedGraded_logicalDistance_mono _ (O.regionDerived_mono sub) left right

/-! ### Composition of derived interventions -/

/-- `do(key := value)`: a chain of one binding. -/
def doBinding (key : Key) (value : Value) : Bindings Key Value :=
  .bind .empty key value

/-- Chains with the same lookup are plug-equivalent. -/
theorem plugEquiv_of_lookupValue_eq {first second : Bindings Key Value}
    (same : lookupValue first = lookupValue second) :
    PlugEquiv (rules := O.derivedRules) first second := fun term =>
  S.equations.iseqv.trans (O.bindingPlug_equiv_assign first term)
    (S.equations.iseqv.trans (O.assign_congr same term)
      (S.equations.iseqv.symm (O.bindingPlug_equiv_assign second term)))

/-- **Override**: `do(key := older)` then `do(key := newer)` is
`do(key := newer)`. -/
theorem do_override (key : Key) (older newer : Value) :
    PlugEquiv (rules := O.derivedRules)
      (O.derivedRules.compose (doBinding key newer) (doBinding key older)) (doBinding key newer) := by
  apply O.plugEquiv_of_lookupValue_eq
  change lookupValue (graft (doBinding key newer) (doBinding key older)) =
    lookupValue (doBinding key newer)
  rw [lookupValue_graft]
  simp only [doBinding, lookupValue_bind, lookupValue_empty, override_none_right,
    override_single_single]

/-- **Interventions on disjoint keys commute.** -/
theorem commute_of_disjoint {first second : Bindings Key Value}
    (disjoint : ∀ key ∈ keysOf first, key ∉ keysOf second) :
    ContextOperators.Commute (rules := O.derivedRules) first second := by
  apply O.plugEquiv_of_lookupValue_eq
  change lookupValue (graft first second) = lookupValue (graft second first)
  rw [lookupValue_graft, lookupValue_graft]
  apply override_comm
  intro key
  by_cases member : key ∈ keysOf first
  · right
    cases found : lookupValue second key with
    | none => rfl
    | some _ =>
        exact absurd (mem_keysOf_of_lookupValue (by rw [found]; rfl)) (disjoint key member)
  · left
    cases found : lookupValue first key with
    | none => rfl
    | some _ => exact absurd (mem_keysOf_of_lookupValue (by rw [found]; rfl)) member

theorem do_commute_of_ne {key key' : Key} (different : key ≠ key') (value : Value) (value' : Value) :
    ContextOperators.Commute (rules := O.derivedRules) (doBinding key value) (doBinding key' value') :=
  O.commute_of_disjoint fun other member member' => by
    simp only [doBinding, keysOf, Mettapedia.Languages.MeTTa.PrimeCandidates.DemandBoundary.Context.entries,
      List.map_cons, List.map_nil, List.mem_singleton] at member member'
    exact different (member.symm.trans member')

/-- **Closure under composition is a real constraint**: the chains of at most
one binding are not the admissible chains of any class, since two single
bindings compose to a chain of two. -/
theorem atMostOneBinding_not_class (key : Key) (value : Value) :
    ¬ ∃ A : AdmissibleClass O.derivedRules,
      A.Admissible = fun bindings : Bindings Key Value => bindings.depth ≤ 1 := by
  intro exists_class
  obtain ⟨_, closed⟩ := (exists_class_iff (rules := O.derivedRules) _).mp exists_class
  have two := closed (outer := doBinding key value) (inner := doBinding key value)
    (show (doBinding key value : Bindings Key Value).depth ≤ 1 from le_refl _)
    (show (doBinding key value : Bindings Key Value).depth ≤ 1 from le_refl _)
  have two' : (graft (doBinding key value) (doBinding key value) : Bindings Key Value).depth ≤ 1 :=
    two
  have depth : (graft (doBinding key value) (doBinding key value) : Bindings Key Value).depth = 2 :=
    rfl
  rw [depth] at two'
  exact absurd two' (by decide)

end OverrideAction

/-! ## Interventions that bind computations -/

section Demand

variable {Key : Type} [DecidableEq Key] {α : Type}

/-- Draw every binding once, newest first, used or not. -/
def drawAll : Bindings Key (Multiset α) → Multiset (Bindings Key α)
  | .empty => {.empty}
  | .bind parent key computation =>
      computation.bind fun value => (drawAll parent).map fun drawn => .bind drawn key value

/-- **Explicit `do` over computations**: every binding is evaluated where it is
made; the body then reads the newest values. -/
def explicitAnswers (bindings : Bindings Key (Multiset α)) (body : List Key) :
    Multiset (List (Option α)) :=
  (drawAll bindings).map fun drawn => body.map (lookupValue drawn)

/-- The number of draws explicit `do` makes: one per binding. -/
def explicitDraws (bindings : Bindings Key (Multiset α)) : ℕ :=
  bindings.depth

/-- One draw for each listed key that is bound. -/
def drawKeys (assignment : Key → Option (Multiset α)) : List Key → Multiset (Key → Option α)
  | [] => {fun _ => none}
  | key :: rest =>
      match assignment key with
      | none => drawKeys assignment rest
      | some computation => computation.bind fun value =>
          (drawKeys assignment rest).map fun environment => Function.update environment key (some value)

/-- **Derived `do` over computations**: each key the body reads is drawn once,
when first read, and every read of it shares that draw. -/
def derivedAnswers (bindings : Bindings Key (Multiset α)) (body : List Key) :
    Multiset (List (Option α)) :=
  (drawKeys (lookupValue bindings) body.dedup).map fun environment => body.map environment

/-- The number of draws derived `do` makes: one per bound key the body reads. -/
def derivedDraws (bindings : Bindings Key (Multiset α)) (body : List Key) : ℕ :=
  (body.dedup.filter fun key => (lookupValue bindings key).isSome).length

/-- Every read draws afresh. -/
def resampledReads (assignment : Key → Option (Multiset α)) : List Key → Multiset (List (Option α))
  | [] => {[]}
  | key :: rest =>
      match assignment key with
      | none => (resampledReads assignment rest).map (none :: ·)
      | some computation => computation.bind fun value =>
          (resampledReads assignment rest).map (some value :: ·)

/-- **The experiment**: every read of a bound key resamples it. -/
def experimentAnswers (bindings : Bindings Key (Multiset α)) (body : List Key) :
    Multiset (List (Option α)) :=
  resampledReads (lookupValue bindings) body

/-- The number of draws the experiment makes: one per read of a bound key. -/
def experimentDraws (bindings : Bindings Key (Multiset α)) (body : List Key) : ℕ :=
  (body.filter fun key => (lookupValue bindings key).isSome).length

/-! ### One binding read `n` times is the generic demand law -/

theorem lookupValue_doBinding_self {key : Key} {value : α} :
    lookupValue (OverrideAction.doBinding key value) key = some value := by
  simp [OverrideAction.doBinding, lookupValue_bind, single, lookupValue_empty]

omit [DecidableEq Key] in
theorem drawAll_doBinding (key : Key) (computation : Multiset α) :
    drawAll (OverrideAction.doBinding key computation) =
      computation.map fun value => OverrideAction.doBinding key value := by
  simp only [OverrideAction.doBinding, drawAll, Multiset.map_singleton]
  exact Multiset.bind_singleton _ _

theorem explicitAnswers_doBinding (key : Key) (computation : Multiset α) (uses : ℕ) :
    explicitAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) =
      (eagerShared uses computation).map (List.map some) := by
  rw [explicitAnswers, drawAll_doBinding, Multiset.map_map, eagerShared, Multiset.bind_singleton,
    Multiset.map_map]
  refine Multiset.map_congr rfl fun value _ => ?_
  simp [shareTuple, List.map_replicate, lookupValue_doBinding_self]

theorem derivedAnswers_doBinding (key : Key) (computation : Multiset α) (uses : ℕ) :
    derivedAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) =
      (lazyShared uses computation).map (List.map some) := by
  by_cases zero : uses = 0
  · subst zero
    simp [derivedAnswers, lazyShared, drawKeys]
  · rw [derivedAnswers, List.replicate_dedup zero, lazyShared, if_neg zero, Multiset.bind_singleton,
      Multiset.map_map]
    simp only [drawKeys, lookupValue_doBinding_self, Multiset.map_singleton]
    rw [Multiset.bind_singleton, Multiset.map_map]
    refine Multiset.map_congr rfl fun value _ => ?_
    simp [shareTuple, List.map_replicate]

theorem experimentAnswers_doBinding (key : Key) (computation : Multiset α) :
    ∀ uses : ℕ, experimentAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) =
      (resampledUses uses computation).map (List.map some)
  | 0 => by simp [experimentAnswers, resampledReads, resampledUses_zero]
  | uses + 1 => by
      have inner := experimentAnswers_doBinding key computation uses
      rw [experimentAnswers] at inner ⊢
      rw [List.replicate_succ, resampledReads, lookupValue_doBinding_self, resampledUses_succ,
        Multiset.map_bind]
      simp only
      refine Multiset.bind_congr fun value _ => ?_
      rw [inner, Multiset.map_map, Multiset.map_map]
      rfl

omit [DecidableEq Key] in
theorem explicitDraws_doBinding (key : Key) (computation : Multiset α) :
    explicitDraws (OverrideAction.doBinding key computation) = 1 :=
  rfl

theorem derivedDraws_doBinding (key : Key) (computation : Multiset α) (uses : ℕ) :
    derivedDraws (OverrideAction.doBinding key computation) (List.replicate uses key) =
      if uses = 0 then 0 else 1 := by
  by_cases zero : uses = 0
  · subst zero
    simp [derivedDraws]
  · rw [derivedDraws, List.replicate_dedup zero, if_neg zero]
    simp [lookupValue_doBinding_self]

theorem experimentDraws_doBinding (key : Key) (computation : Multiset α) (uses : ℕ) :
    experimentDraws (OverrideAction.doBinding key computation) (List.replicate uses key) = uses := by
  rw [experimentDraws, List.filter_replicate]
  simp [lookupValue_doBinding_self]

theorem map_some_injective : Function.Injective (Multiset.map (List.map (some : α → Option α))) :=
  Multiset.map_injective (List.map_injective_iff.mpr (Option.some_injective α))

/-- **Explicit and derived `do` agree over bags exactly when the binding is
read at least once or has one answer.** -/
theorem explicit_eq_derived_iff (key : Key) (computation : Multiset α) (uses : ℕ) :
    explicitAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) =
        derivedAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) ↔
      1 ≤ uses ∨ computation.card = 1 := by
  rw [explicitAnswers_doBinding, derivedAnswers_doBinding, map_some_injective.eq_iff]
  exact eagerShared_eq_lazyShared_iff uses computation

/-- **Explicit and derived `do` never differ on a binding that is read**: both
share one draw, so sharing never separates them. -/
theorem explicit_eq_derived_of_read (key : Key) (computation : Multiset α) {uses : ℕ}
    (read : 1 ≤ uses) :
    explicitAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) =
      derivedAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) :=
  (explicit_eq_derived_iff key computation uses).mpr (Or.inl read)

/-- **Derived `do` and the experiment agree over bags exactly when the binding
is read at most once or has at most one answer.** -/
theorem derived_eq_experiment_iff (key : Key) (computation : Multiset α) (uses : ℕ) :
    derivedAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) =
        experimentAnswers (OverrideAction.doBinding key computation) (List.replicate uses key) ↔
      uses ≤ 1 ∨ computation.card ≤ 1 := by
  rw [derivedAnswers_doBinding, experimentAnswers_doBinding, map_some_injective.eq_iff]
  exact lazyShared_eq_resampledUses_iff uses computation

theorem toFinset_map_some_injective [DecidableEq α] :
    Function.Injective (Finset.image (List.map (some : α → Option α))) :=
  Finset.image_injective (List.map_injective_iff.mpr (Option.some_injective α))

/-- **On supports, explicit and derived `do` agree exactly when the binding is
read or has an answer.** -/
theorem explicit_derived_support_iff [DecidableEq α] (key : Key) (computation : Multiset α)
    (uses : ℕ) :
    (explicitAnswers (OverrideAction.doBinding key computation) (List.replicate uses key)).toFinset =
        (derivedAnswers (OverrideAction.doBinding key computation)
          (List.replicate uses key)).toFinset ↔
      1 ≤ uses ∨ computation ≠ 0 := by
  rw [explicitAnswers_doBinding, derivedAnswers_doBinding, Multiset.toFinset_map,
    Multiset.toFinset_map, toFinset_map_some_injective.eq_iff]
  exact eagerShared_lazyShared_support_iff uses computation

/-! ### The override law -/

theorem lookupValue_override_doBinding (key : Key) (older newer : α) :
    lookupValue (graft (OverrideAction.doBinding key newer) (OverrideAction.doBinding key older)) =
      lookupValue (OverrideAction.doBinding key newer) := by
  rw [lookupValue_graft]
  simp only [OverrideAction.doBinding, lookupValue_bind, lookupValue_empty, override_none_right,
    override_single_single]

/-- **Derived `do` satisfies the override law**, for every body. -/
theorem derived_override (key : Key) (older newer : Multiset α) (body : List Key) :
    derivedAnswers (graft (OverrideAction.doBinding key newer) (OverrideAction.doBinding key older))
        body =
      derivedAnswers (OverrideAction.doBinding key newer) body := by
  rw [derivedAnswers, derivedAnswers, lookupValue_override_doBinding]

theorem experiment_override (key : Key) (older newer : Multiset α) (body : List Key) :
    experimentAnswers
        (graft (OverrideAction.doBinding key newer) (OverrideAction.doBinding key older)) body =
      experimentAnswers (OverrideAction.doBinding key newer) body := by
  rw [experimentAnswers, experimentAnswers, lookupValue_override_doBinding]

theorem explicitAnswers_override (key : Key) (older newer : Multiset α) (body : List Key) :
    explicitAnswers (graft (OverrideAction.doBinding key newer) (OverrideAction.doBinding key older))
        body =
      newer.bind fun value =>
        Multiset.replicate older.card (body.map (lookupValue (OverrideAction.doBinding key value))) := by
  simp only [explicitAnswers, graft, OverrideAction.doBinding, drawAll, Multiset.map_singleton]
  rw [Multiset.map_bind]
  refine Multiset.bind_congr fun value _ => ?_
  rw [Multiset.bind_singleton, Multiset.map_map, Multiset.map_map]
  have same : ∀ older' : α,
      body.map (lookupValue (.bind (.bind .empty key older') key value : Bindings Key α)) =
        body.map (lookupValue (.bind .empty key value : Bindings Key α)) := by
    intro older'
    have := lookupValue_override_doBinding key older' value
    simp only [graft, OverrideAction.doBinding] at this
    rw [this]
  simp only [Function.comp_def, same]
  exact Multiset.map_const' _ _

/-- **Explicit `do` satisfies the override law exactly when the shadowed
computation has one answer or the newer one has none**: a shadowed explicit
intervention still runs, and each of its answers contributes a copy. -/
theorem explicit_override_iff (key : Key) (older newer : Multiset α) (body : List Key) :
    explicitAnswers
        (graft (OverrideAction.doBinding key newer) (OverrideAction.doBinding key older)) body =
      explicitAnswers (OverrideAction.doBinding key newer) body ↔
      older.card = 1 ∨ newer = 0 := by
  rw [explicitAnswers_override, explicitAnswers, drawAll_doBinding, Multiset.map_map]
  constructor
  · intro same
    have cards := congrArg Multiset.card same
    simp only [Multiset.card_bind, Multiset.card_replicate, Multiset.card_map, Function.comp_def,
      Multiset.map_const', Multiset.sum_replicate, smul_eq_mul] at cards
    by_cases empty : newer = 0
    · exact Or.inr empty
    · left
      have positive : 0 < newer.card := Multiset.card_pos.mpr empty
      have : newer.card * older.card = newer.card * 1 := by rw [mul_one]; exact cards
      exact Nat.eq_of_mul_eq_mul_left positive this
  · rintro (one | empty)
    · obtain ⟨single, rfl⟩ := Multiset.card_eq_one.mp one
      simp only [Multiset.card_singleton, Multiset.replicate_one]
      rw [Multiset.bind_singleton]
      rfl
    · subst empty
      simp

/-! ### Different keys commute; the same key does not -/

theorem lookupValue_swap {key key' : Key} (different : key ≠ key') (value value' : α) :
    lookupValue (.bind (.bind .empty key' value') key value : Bindings Key α) =
      lookupValue (.bind (.bind .empty key value) key' value' : Bindings Key α) := by
  simp only [lookupValue_bind, lookupValue_empty, override_none_right]
  apply override_comm
  intro other
  by_cases same : other = key
  · right
    subst same
    simp [single, different]
  · left
    simp [single, same]

/-- **Explicit interventions on different keys commute.** -/
theorem explicit_commute {key key' : Key} (different : key ≠ key') (first second : Multiset α)
    (body : List Key) :
    explicitAnswers
        (graft (OverrideAction.doBinding key first) (OverrideAction.doBinding key' second)) body =
      explicitAnswers
        (graft (OverrideAction.doBinding key' second) (OverrideAction.doBinding key first)) body := by
  simp only [explicitAnswers, graft, OverrideAction.doBinding, drawAll, Multiset.map_singleton,
    Multiset.map_bind, Multiset.bind_singleton, Multiset.map_map]
  rw [Multiset.bind_map_comm]
  refine Multiset.bind_congr fun value' _ => Multiset.map_congr rfl fun value _ => ?_
  simp only [Function.comp_apply, lookupValue_swap different]

/-- **Derived interventions on different keys commute.** -/
theorem derived_commute {key key' : Key} (different : key ≠ key') (first second : Multiset α)
    (body : List Key) :
    derivedAnswers
        (graft (OverrideAction.doBinding key first) (OverrideAction.doBinding key' second)) body =
      derivedAnswers
        (graft (OverrideAction.doBinding key' second) (OverrideAction.doBinding key first)) body := by
  have same : lookupValue
      (graft (OverrideAction.doBinding key first) (OverrideAction.doBinding key' second)) =
      lookupValue
        (graft (OverrideAction.doBinding key' second) (OverrideAction.doBinding key first)) := by
    simpa only [graft, OverrideAction.doBinding] using lookupValue_swap different first second
  rw [derivedAnswers, derivedAnswers, same]

/-- **Two interventions on one key do not commute**: the newer one is read. -/
theorem derived_same_key_not_commute (key : Key) {first second : α} (different : first ≠ second) :
    derivedAnswers
        (graft (OverrideAction.doBinding key {first}) (OverrideAction.doBinding key {second}))
        [key] ≠
      derivedAnswers
        (graft (OverrideAction.doBinding key {second}) (OverrideAction.doBinding key {first}))
        [key] := by
  rw [derived_override, derived_override, derivedAnswers_doBinding' key, derivedAnswers_doBinding' key]
  intro same
  exact different (by simpa using same)
where
  derivedAnswers_doBinding' (key : Key) (value : α) :
      derivedAnswers (OverrideAction.doBinding key ({value} : Multiset α)) [key] = {[some value]} := by
    have := derivedAnswers_doBinding key ({value} : Multiset α) 1
    simpa [lazyShared, shareTuple] using this

/-! ### Retention: the twin shares the exogenous cell, the experiment resamples it -/

/-- **The counterfactual twin**: the factual and the counterfactual world read
one exogenous binding, so both reads share its cell. -/
def twin (exogenous : Key) (computation : Multiset α) : Multiset (List (Option α)) :=
  derivedAnswers (OverrideAction.doBinding exogenous computation) [exogenous, exogenous]

/-- **The experiment**: each world draws the exogenous binding afresh. -/
def experiment (exogenous : Key) (computation : Multiset α) : Multiset (List (Option α)) :=
  experimentAnswers (OverrideAction.doBinding exogenous computation) [exogenous, exogenous]

theorem twin_eq (exogenous : Key) (computation : Multiset α) :
    twin exogenous computation = (lazyShared 2 computation).map (List.map some) :=
  derivedAnswers_doBinding exogenous computation 2

theorem experiment_eq (exogenous : Key) (computation : Multiset α) :
    experiment exogenous computation = (resampledUses 2 computation).map (List.map some) :=
  experimentAnswers_doBinding exogenous computation 2

/-- **The twin and the experiment coincide exactly when the exogenous cell has
at most one answer**: the condition of `DemandAgreement`. -/
theorem twin_eq_experiment_iff (exogenous : Key) (computation : Multiset α) :
    twin exogenous computation = experiment exogenous computation ↔ computation.card ≤ 1 := by
  refine (derived_eq_experiment_iff exogenous computation 2).trans ?_
  constructor
  · rintro (two | one)
    · exact absurd two (by decide)
    · exact one
  · exact Or.inr

/-- On supports, the twin and the experiment coincide exactly when the
exogenous cell's support has at most one element. -/
theorem twin_experiment_support_iff [DecidableEq α] (exogenous : Key) (computation : Multiset α) :
    (twin exogenous computation).toFinset = (experiment exogenous computation).toFinset ↔
      computation.toFinset.card ≤ 1 := by
  rw [twin_eq, experiment_eq, Multiset.toFinset_map, Multiset.toFinset_map,
    toFinset_map_some_injective.eq_iff, lazyShared_resampledUses_support_iff]
  constructor
  · rintro (two | one)
    · exact absurd two (by decide)
    · exact one
  · exact Or.inr

end Demand

end Mettapedia.GSLT.Causality.ContextBindings
