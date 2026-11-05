import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.ReflectionClosure

/-!
# The MeTTa-calculus COMM and REFL rules as firings of the transform candidate

Meredith's COMM rule is `for(t <- x)P | for(u <- x)Q → P·σ̇ | Q·σ̇` with
`σ = unify(t, u)`; the dot quotes every bound value. `ReflectionClosure.Step`
states the displayed rules over MeTTa-IL patterns with an explicit unification
premise. Here COMM is one ordinary rule instance: take both inputs, tell the
equation `t = u`, and produce both bodies with the variables of `t` and `u`
already in quoted position. The store does the unification; the client reads
each body in a solution of the result store.

* `patternAction`: structural substitution of free variables is a
  substitution action on MeTTa-IL patterns.
* `applyBindings_eq_psubst`, `applyDot_eq`: on the first-order fragment (no
  explicit `subst` node, no collection rest) MeTTa-IL's `applyBindings` and the
  calculus's `applyDot` are this substitution.
* `comm_valid_iff`: the firing is valid exactly when the two inputs are
  distinct present occurrences, the outputs are fresh and labelled by the
  dotted bodies, and the store remains consistent with `t = u`.
* `comm_adequacy`: when `t = u` has a ground principal unifier `bs`, the firing
  is valid, `ReflectionClosure.Step.comm` relates the source to
  `par (applyDot bs P) (applyDot bs Q)`, and every solution of the result
  store reads exactly those two bodies when the bodies' variables are bound by
  the patterns.
* `reflect_adequacy`: one REFL step whose premise is a root COMM is also one
  firing: take the reflected occurrence, tell `t = u`, produce the listener.
  `nested_reflection_needs_its_own_shape` shows that this rule instance does
  not apply to a nested reflection; the nested step is another single firing
  (`nested_reflect_firing`). REFL is one firing per derivation shape.

Separating examples against the executable `MeTTaCalculus.step`:

* `executable_triangular_reduct`: the executable unifier returns a triangular
  binding list, which `applyDot` applies in one pass; one reduct keeps the
  variable `Y` that the principal unifier binds to `a`.
* `executable_capture`: the existing canary `demoCommSource` reduces to
  `@0 | @0` because the second process's free `a` is identified with the
  first process's bound `a`. Renaming that bound variable, as the manuscript's
  alpha rule allows, gives `@0 | a`.
* `executable_refuses_unrenamed`: `for(X <- @0)X | for(f(X) <- @0)0` has no
  executable reduct (the occurs check meets one shared name), while the firing
  with the two patterns opened apart is valid.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (fire)

/-! ## Structural substitution on MeTTa-IL patterns -/

/-- What a substitution offers for each free pattern variable. -/
abbrev PSubst := String → Option Pattern

/-- Structural substitution of free variables. Explicit `subst` nodes and
collection rests are kept as syntax. -/
def psubst (σ : PSubst) : Pattern → Pattern
  | .bvar n => .bvar n
  | .fvar x => (σ x).getD (.fvar x)
  | .apply c args => .apply c (psubstList σ args)
  | .lambda nm body => .lambda nm (psubst σ body)
  | .multiLambda n nms body => .multiLambda n nms (psubst σ body)
  | .subst body repl => .subst (psubst σ body) (psubst σ repl)
  | .collection ct elems rest => .collection ct (psubstList σ elems) rest
where
  psubstList (σ : PSubst) : List Pattern → List Pattern
    | [] => []
    | p :: ps => psubst σ p :: psubstList σ ps

/-- Apply `inner`, then `outer`. -/
def pcomp (outer inner : PSubst) : PSubst := fun x =>
  match inner x with
  | some value => some (psubst outer value)
  | none => outer x

theorem psubst_comp (outer inner : PSubst) (t : Pattern) :
    psubst outer (psubst inner t) = psubst (pcomp outer inner) t := by
  induction t using Pattern.rec
      (motive_2 := fun ps => psubst.psubstList outer (psubst.psubstList inner ps) =
        psubst.psubstList (pcomp outer inner) ps) with
  | bvar n => rfl
  | fvar x => cases h : inner x <;> simp [psubst, pcomp, h]
  | apply c args ih => simp only [psubst, ih]
  | lambda nm body ih => simp only [psubst, ih]
  | multiLambda n nms body ih => simp only [psubst, ih]
  | subst body repl ihb ihr => simp only [psubst, ihb, ihr]
  | collection ct elems rest ih => simp only [psubst, ih]
  | nil => rfl
  | cons p ps head tail => simp only [psubst.psubstList, head, tail]

theorem psubst_none (t : Pattern) : psubst (fun _ => none) t = t := by
  induction t using Pattern.rec
      (motive_2 := fun ps => psubst.psubstList (fun _ => none) ps = ps) with
  | bvar n => rfl
  | fvar x => rfl
  | apply c args ih => simp only [psubst, ih]
  | lambda nm body ih => simp only [psubst, ih]
  | multiLambda n nms body ih => simp only [psubst, ih]
  | subst body repl ihb ihr => simp only [psubst, ihb, ihr]
  | collection ct elems rest ih => simp only [psubst, ih]
  | nil => rfl
  | cons p ps head tail => simp only [psubst.psubstList, head, tail]

/-- Syntactic equality of MeTTa-IL patterns with structural substitution. -/
def patternAction : SubstitutionAction Pattern PSubst where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply := psubst
  identity := fun _ => none
  compose := pcomp
  apply_identity := psubst_none
  apply_compose outer inner t := (psubst_comp outer inner t).symm
  preserves σ {_ _} same := congrArg (psubst σ) same

/-- The free pattern variables, with repetitions. -/
def pvars : Pattern → List String
  | .bvar _ => []
  | .fvar x => [x]
  | .apply _ args => pvarsList args
  | .lambda _ body => pvars body
  | .multiLambda _ _ body => pvars body
  | .subst body repl => pvars body ++ pvars repl
  | .collection _ elems _ => pvarsList elems
where
  pvarsList : List Pattern → List String
    | [] => []
    | p :: ps => pvars p ++ pvarsList ps

theorem psubst_congr (σ τ : PSubst) (t : Pattern) (agree : ∀ x ∈ pvars t, σ x = τ x) :
    psubst σ t = psubst τ t := by
  revert agree
  induction t using Pattern.rec
      (motive_2 := fun ps => (∀ x ∈ pvars.pvarsList ps, σ x = τ x) →
        psubst.psubstList σ ps = psubst.psubstList τ ps) with
  | bvar n => intro _; rfl
  | fvar x =>
    intro agree
    simp only [psubst, agree x (by simp [pvars])]
  | apply c args ih =>
    intro agree
    simp only [psubst, ih (by simpa [pvars] using agree)]
  | lambda nm body ih =>
    intro agree
    simp only [psubst, ih (by simpa [pvars] using agree)]
  | multiLambda n nms body ih =>
    intro agree
    simp only [psubst, ih (by simpa [pvars] using agree)]
  | subst body repl ihb ihr =>
    intro agree
    simp only [pvars, List.mem_append] at agree
    simp only [psubst, ihb (fun x member => agree x (.inl member)),
      ihr (fun x member => agree x (.inr member))]
  | collection ct elems rest ih =>
    intro agree
    simp only [psubst, ih (by simpa [pvars] using agree)]
  | nil => rfl
  | cons p ps head tail =>
    rename_i agree
    simp only [pvars.pvarsList, List.mem_append] at agree
    simp only [psubst.psubstList, head (fun x member => agree x (.inl member)),
      tail (fun x member => agree x (.inr member))]

theorem psubst_of_pvars_nil (σ : PSubst) (t : Pattern) (closed : pvars t = []) : psubst σ t = t := by
  rw [psubst_congr σ (fun _ => none) t (by simp [closed]), psubst_none]

/-! ## Agreement with MeTTa-IL's binding application -/

/-- No explicit `subst` node and no collection rest. -/
def firstOrder : Pattern → Bool
  | .bvar _ => true
  | .fvar _ => true
  | .apply _ args => firstOrderList args
  | .lambda _ body => firstOrder body
  | .multiLambda _ _ body => firstOrder body
  | .subst _ _ => false
  | .collection _ elems rest => rest.isNone && firstOrderList elems
where
  firstOrderList : List Pattern → Bool
    | [] => true
    | p :: ps => firstOrder p && firstOrderList ps

theorem applyBindings_eq_psubst (bs : Bindings) (t : Pattern) (fo : firstOrder t = true) :
    applyBindings bs t = psubst bs.lookup t := by
  revert fo
  induction t using Pattern.rec
      (motive_2 := fun ps => firstOrder.firstOrderList ps = true →
        ps.map (applyBindings bs) = psubst.psubstList bs.lookup ps) with
  | bvar n => intro _; simp [applyBindings, psubst]
  | fvar x =>
    intro _
    cases h : bs.find? (fun entry => entry.1 == x) with
    | none => simp [applyBindings, psubst, Bindings.lookup, h]
    | some entry => simp [applyBindings, psubst, Bindings.lookup, h]
  | apply c args ih =>
    intro fo
    rw [applyBindings]
    simp only [psubst, ih (by simpa [firstOrder] using fo)]
  | lambda nm body ih =>
    intro fo
    rw [applyBindings]
    simp only [psubst, ih (by simpa [firstOrder] using fo)]
  | multiLambda n nms body ih =>
    intro fo
    rw [applyBindings]
    simp only [psubst, ih (by simpa [firstOrder] using fo)]
  | subst body repl _ _ => intro fo; simp [firstOrder] at fo
  | collection ct elems rest ih =>
    intro fo
    simp only [firstOrder, Bool.and_eq_true, Option.isNone_iff_eq_none] at fo
    obtain ⟨rfl, elemsFo⟩ := fo
    rw [applyBindings]
    simp only [psubst, ih elemsFo, List.append_nil]
  | nil => rfl
  | cons p ps head tail =>
    rename_i fo
    simp only [firstOrder.firstOrderList, Bool.and_eq_true] at fo
    simp only [List.map_cons, psubst.psubstList, head fo.1, tail fo.2]

theorem lookup_dotBindings (bs : Bindings) (x : String) :
    (dotBindings bs).lookup x = (bs.lookup x).map nQuote := by
  simp only [dotBindings, Bindings.lookup, List.find?_map, Option.map_map]
  rfl

/-- The calculus's dot substitution is structural substitution of quoted values. -/
theorem applyDot_eq (bs : Bindings) (P : Pattern) (fo : firstOrder P = true) :
    applyDot bs P = psubst (fun x => (bs.lookup x).map nQuote) P := by
  unfold applyDot
  rw [applyBindings_eq_psubst _ P fo]
  congr 1
  funext x
  exact lookup_dotBindings bs x

theorem psubst_nQuote (σ : PSubst) (p : Pattern) : psubst σ (nQuote p) = nQuote (psubst σ p) := rfl

theorem psubst_par (σ : PSubst) (p q : Pattern) : psubst σ (par p q) = par (psubst σ p) (psubst σ q) := rfl

theorem psubst_pFor (σ : PSubst) (t x k : Pattern) :
    psubst σ (pFor t x k) = pFor (psubst σ t) (psubst σ x) (psubst σ k) := rfl

theorem psubst_pReflect (σ : PSubst) (x p : Pattern) :
    psubst σ (pReflect x p) = pReflect (psubst σ x) (psubst σ p) := rfl

theorem psubst_tProc (σ : PSubst) (p : Pattern) : psubst σ (tProc p) = tProc (psubst σ p) := rfl

theorem psubst_pZero (σ : PSubst) : psubst σ pZero = pZero := rfl

/-! ## COMM as one firing -/

/-- Put the variables `vs` in quoted position, so that each one reads as the
quotation of its value: the manuscript's dot. -/
def quoteOn (vs : List String) : PSubst := fun x => if x ∈ vs then some (nQuote (.fvar x)) else none

/-- A continuation with the pattern variables `vs` in quoted position. -/
def dotted (vs : List String) (P : Pattern) : Pattern := psubst (quoteOn vs) P

/-- One COMM: take both inputs, tell `t = u`, produce both dotted bodies. -/
def commRule (t u channel P Q : Pattern) : RuleInstance Pattern :=
  ⟨[pFor t channel P, pFor u channel Q], [], [(t, u)], [],
    [dotted (pvars t ++ pvars u) P, dotted (pvars t ++ pvars u) Q]⟩

def commSelection {O : Type*} (first second made₁ made₂ : O) : Selection O :=
  ⟨[first, second], [], [made₁, made₂]⟩

/-- `bs` is a ground principal unifier of `t` and `u`: its keys are their
variables, it binds each of them to a closed pattern, it unifies them, and
every unifier agrees with it on those variables. -/
structure GroundPrincipal (t u : Pattern) (bs : Bindings) : Prop where
  keys : ∀ e ∈ bs, e.1 ∈ pvars t ++ pvars u
  covers : ∀ x ∈ pvars t ++ pvars u, ∃ v, bs.lookup x = some v ∧ pvars v = []
  solves : psubst bs.lookup t = psubst bs.lookup u
  principal : ∀ σ : PSubst, psubst σ t = psubst σ u →
    ∀ x ∈ pvars t ++ pvars u, ∀ v, bs.lookup x = some v → psubst σ (.fvar x) = v

theorem lookup_eq_none_of_keys {bs : Bindings} {vs : List String} (keys : ∀ e ∈ bs, e.1 ∈ vs)
    {x : String} (outside : x ∉ vs) : bs.lookup x = none := by
  unfold Bindings.lookup
  cases found : bs.find? (fun entry => entry.1 == x) with
  | none => rfl
  | some entry =>
    exfalso
    have member := List.mem_of_find?_eq_some found
    have same := List.find?_some found
    simp only [beq_iff_eq] at same
    exact outside (same ▸ keys entry member)

/-- Every unifier of `t` and `u` reads a dotted continuation as the dotted
substitution of the ground principal unifier, when the continuation's
variables are bound by the patterns. -/
theorem dotted_resolves {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs) {σ : PSubst}
    (solved : psubst σ t = psubst σ u) (P : Pattern) (fo : firstOrder P = true)
    (closed : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u) :
    psubst σ (dotted (pvars t ++ pvars u) P) = applyDot bs P := by
  rw [applyDot_eq bs P fo, dotted, psubst_comp]
  apply psubst_congr
  intro x member
  have inside := closed x member
  obtain ⟨v, found, _⟩ := gp.covers x inside
  have agree := gp.principal σ solved x inside v found
  simp only [pcomp, quoteOn, if_pos inside, found, Option.map_some, psubst_nQuote, agree]

/-- The principal solution itself reads every dotted continuation as the dot
substitution; continuation variables outside the patterns stay open. -/
theorem principal_dotted {t u : Pattern} {bs : Bindings} (gp : GroundPrincipal t u bs)
    (P : Pattern) (fo : firstOrder P = true) :
    psubst bs.lookup (dotted (pvars t ++ pvars u) P) = applyDot bs P := by
  rw [applyDot_eq bs P fo, dotted, psubst_comp]
  apply psubst_congr
  intro x _
  by_cases inside : x ∈ pvars t ++ pvars u
  · obtain ⟨v, found, closedValue⟩ := gp.covers x inside
    simp only [pcomp, quoteOn, if_pos inside, found, Option.map_some, psubst_nQuote]
    simp [psubst, found]
  · have none := lookup_eq_none_of_keys gp.keys inside
    simp only [pcomp, quoteOn, if_neg inside, none, Option.map_none]

variable {O : Type*} [DecidableEq O]

omit [DecidableEq O] in
theorem comm_problem (label : O → Pattern) (t u channel P Q : Pattern)
    (before : Configuration Pattern O) (first second made₁ made₂ : O) :
    (commSelection first second made₁ made₂).problem label (commRule t u channel P Q) before =
      before.equations ++ [(pFor t channel P, label first), (pFor u channel Q, label second), (t, u)] := by
  simp [Selection.problem, Selection.equations, commSelection, commRule]

theorem comm_valid_iff (label : O → Pattern) (t u channel P Q : Pattern)
    (before : Configuration Pattern O) (first second made₁ made₂ : O) :
    (commSelection first second made₁ made₂).Valid patternAction label (commRule t u channel P Q) before ↔
      first ≠ second ∧ made₁ ≠ made₂ ∧ first ∈ before.present ∧ second ∈ before.present ∧
        made₁ ∉ before.present ∧ made₂ ∉ before.present ∧
        label made₁ = dotted (pvars t ++ pvars u) P ∧ label made₂ = dotted (pvars t ++ pvars u) Q ∧
        patternAction.Consistent (before.equations ++
          [(pFor t channel P, label first), (pFor u channel Q, label second), (t, u)]) := by
  constructor
  · intro valid
    have distinct := valid.take_distinct
    have madeDistinct := valid.output_distinct
    have outputs := valid.outputs
    simp only [commSelection, List.nodup_cons, List.mem_singleton, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true] at distinct madeDistinct
    simp only [commSelection, commRule, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] at outputs
    have taken := valid.occurrences.taken_subset
    have fresh := valid.occurrences.fresh
    simp only [Selection.commit, commSelection] at taken fresh
    refine ⟨distinct, madeDistinct, taken (by simp), taken (by simp), ?_, ?_, outputs.1, outputs.2, ?_⟩
    · exact Finset.disjoint_left.mp fresh (by simp)
    · exact Finset.disjoint_left.mp fresh (by simp)
    · simpa [comm_problem] using valid.consistent
  · rintro ⟨distinct, madeDistinct, present₁, present₂, fresh₁, fresh₂, out₁, out₂, consistent⟩
    refine ⟨by simp [commSelection, distinct], by simp [commSelection, madeDistinct], rfl, rfl,
      by simp [commSelection, commRule, out₁, out₂], ?_, ?_, ?_⟩
    · refine ⟨?_, by simp [Selection.commit, commSelection], by simp [Selection.commit, commSelection], ?_, ?_⟩
      · intro o member
        simp only [Selection.commit, commSelection, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
        rcases member with rfl | rfl
        · exact present₁
        · exact present₂
      · rw [Finset.disjoint_left]
        intro o member
        simp only [Selection.commit, commSelection, List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.mem_insert, Finset.mem_singleton] at member
        rcases member with rfl | rfl
        · exact fresh₁
        · exact fresh₂
      · intro query member
        simp [Selection.commit] at member
    · rw [comm_problem]
      exact consistent
    · intro check member
      simp [commRule] at member

/-- A valid COMM firing requires the two payload patterns to unify. -/
theorem comm_valid_unifies {label : O → Pattern} {t u channel P Q : Pattern}
    {before : Configuration Pattern O} {first second made₁ made₂ : O}
    (valid : (commSelection first second made₁ made₂).Valid patternAction label
      (commRule t u channel P Q) before) :
    ∃ σ : PSubst, psubst σ t = psubst σ u := by
  obtain ⟨σ, solved⟩ := valid.consistent
  rw [comm_problem] at solved
  exact ⟨σ, solved (t, u) (by simp)⟩

/-- The variables of an equation store over patterns. -/
def storePVars (store : EquationStore Pattern) : List String :=
  store.flatMap fun e => pvars e.1 ++ pvars e.2

/-- **COMM adequacy on the ground-principal fragment.** The firing is valid,
the source and target are related by the manuscript's COMM rule as stated in
`ReflectionClosure.Step`, and every solution of the result store reads the
two outputs as the dotted continuations. -/
theorem comm_adequacy (label : O → Pattern) (t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : firstOrder P = true) (foQ : firstOrder Q = true)
    (closedP : ∀ x ∈ pvars P, x ∈ pvars t ++ pvars u)
    (closedQ : ∀ x ∈ pvars Q, x ∈ pvars t ++ pvars u)
    (before : Configuration Pattern O) (first second made₁ made₂ : O)
    (labelFirst : label first = pFor t channel P) (labelSecond : label second = pFor u channel Q)
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ before.present) (present₂ : second ∈ before.present)
    (fresh₁ : made₁ ∉ before.present) (fresh₂ : made₂ ∉ before.present)
    (out₁ : label made₁ = dotted (pvars t ++ pvars u) P)
    (out₂ : label made₂ = dotted (pvars t ++ pvars u) Q)
    (apart : ∀ x ∈ pvars t ++ pvars u, x ∉ storePVars before.equations)
    (base : patternAction.Consistent before.equations) :
    (commSelection first second made₁ made₂).Valid patternAction label (commRule t u channel P Q) before ∧
      ReflectionClosure.Step GroundPrincipal SC (par (pFor t channel P) (pFor u channel Q))
        (par (applyDot bs P) (applyDot bs Q)) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((commSelection first second made₁ made₂).result label (commRule t u channel P Q) before).equations →
        psubst σ (label made₁) = applyDot bs P ∧ psubst σ (label made₂) = applyDot bs Q := by
  classical
  refine ⟨?_, ReflectionClosure.Step.comm t u channel P Q bs gp, ?_⟩
  · refine (comm_valid_iff label t u channel P Q before first second made₁ made₂).mpr
      ⟨distinct, madeDistinct, present₁, present₂, fresh₁, fresh₂, out₁, out₂, ?_⟩
    obtain ⟨σ₀, solved₀⟩ := base
    let glued : PSubst := fun x => if x ∈ pvars t ++ pvars u then bs.lookup x else σ₀ x
    have onPatterns : ∀ term : Pattern, (∀ x ∈ pvars term, x ∈ pvars t ++ pvars u) →
        psubst glued term = psubst bs.lookup term := by
      intro term inside
      apply psubst_congr
      intro x member
      show (if x ∈ pvars t ++ pvars u then bs.lookup x else σ₀ x) = bs.lookup x
      rw [if_pos (inside x member)]
    refine ⟨glued, ?_⟩
    intro e member
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with old | rfl | rfl | rfl
    · have equation := solved₀ e old
      change psubst σ₀ e.1 = psubst σ₀ e.2 at equation
      change psubst glued e.1 = psubst glued e.2
      have outside : ∀ term, (∀ x ∈ pvars term, x ∈ storePVars before.equations) →
          psubst glued term = psubst σ₀ term := by
        intro term inside
        apply psubst_congr
        intro x member
        have notPattern : x ∉ pvars t ++ pvars u := fun inPattern => apart x inPattern (inside x member)
        show (if x ∈ pvars t ++ pvars u then bs.lookup x else σ₀ x) = σ₀ x
        rw [if_neg notPattern]
      rw [outside e.1 (fun x member => by simp only [storePVars, List.mem_flatMap, List.mem_append]; exact ⟨e, old, .inl member⟩),
        outside e.2 (fun x member => by simp only [storePVars, List.mem_flatMap, List.mem_append]; exact ⟨e, old, .inr member⟩)]
      exact equation
    · change psubst glued (pFor t channel P) = psubst glued (label first)
      rw [labelFirst]
    · change psubst glued (pFor u channel Q) = psubst glued (label second)
      rw [labelSecond]
    · change psubst glued t = psubst glued u
      rw [onPatterns t (fun x member => List.mem_append_left _ member),
        onPatterns u (fun x member => List.mem_append_right _ member)]
      exact gp.solves
  · intro σ solved
    have equation := solved (t, u) (by simp [Selection.result, comm_problem])
    change psubst σ t = psubst σ u at equation
    rw [out₁, out₂]
    exact ⟨dotted_resolves gp equation P foP closedP, dotted_resolves gp equation Q foQ closedQ⟩

/-! ## REFL as one firing per derivation shape -/

/-- One REFL step whose premise is a root COMM between the two components. -/
def reflRule (x t u channel P Q : Pattern) : RuleInstance Pattern :=
  ⟨[pReflect x (par (pFor t channel P) (pFor u channel Q))], [], [(t, u)], [],
    [pFor (tProc (par (dotted (pvars t ++ pvars u) P) (dotted (pvars t ++ pvars u) Q))) x pZero]⟩

def oneTake {O : Type*} (taken made : O) : Selection O := ⟨[taken], [], [made]⟩

omit [DecidableEq O] in
theorem refl_problem (label : O → Pattern) (x t u channel P Q : Pattern)
    (before : Configuration Pattern O) (taken made : O) :
    (oneTake taken made).problem label (reflRule x t u channel P Q) before =
      before.equations ++ [(pReflect x (par (pFor t channel P) (pFor u channel Q)), label taken), (t, u)] := by
  simp [Selection.problem, Selection.equations, oneTake, reflRule]

/-- **REFL adequacy for a root COMM premise.** The firing is valid, the
manuscript's REFL rule relates source and target, and every solution of the
result store reads the produced listener as that target. -/
theorem reflect_adequacy (label : O → Pattern) (x t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : firstOrder P = true) (foQ : firstOrder Q = true)
    (closedP : ∀ v ∈ pvars P, v ∈ pvars t ++ pvars u)
    (closedQ : ∀ v ∈ pvars Q, v ∈ pvars t ++ pvars u) (closedX : pvars x = [])
    (before : Configuration Pattern O) (empty : before.equations = []) (taken made : O)
    (labelTaken : label taken = pReflect x (par (pFor t channel P) (pFor u channel Q)))
    (present : taken ∈ before.present) (fresh : made ∉ before.present)
    (out : label made =
      pFor (tProc (par (dotted (pvars t ++ pvars u) P) (dotted (pvars t ++ pvars u) Q))) x pZero) :
    (oneTake taken made).Valid patternAction label (reflRule x t u channel P Q) before ∧
      ReflectionClosure.Step GroundPrincipal SC (pReflect x (par (pFor t channel P) (pFor u channel Q)))
        (pFor (tProc (par (applyDot bs P) (applyDot bs Q))) x pZero) ∧
      ∀ σ : PSubst, patternAction.Models σ
          ((oneTake taken made).result label (reflRule x t u channel P Q) before).equations →
        psubst σ (label made) = pFor (tProc (par (applyDot bs P) (applyDot bs Q))) x pZero := by
  refine ⟨?_, .reflect x (.comm t u channel P Q bs gp), ?_⟩
  · refine ⟨by simp [oneTake], by simp [oneTake], rfl, rfl, by simp [oneTake, reflRule, out], ?_, ?_, ?_⟩
    · refine ⟨by simp [Selection.commit, oneTake, present], by simp [Selection.commit, oneTake],
        by simp [Selection.commit, oneTake], by simp [Selection.commit, oneTake, fresh], ?_⟩
      intro query member
      simp [Selection.commit] at member
    · rw [refl_problem, empty]
      refine ⟨bs.lookup, ?_⟩
      intro e member
      simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change psubst _ _ = psubst _ (label taken)
        rw [labelTaken]
      · exact gp.solves
    · intro check member
      simp [reflRule] at member
  · intro σ solved
    have equation := solved (t, u) (by simp [Selection.result, refl_problem])
    change psubst σ t = psubst σ u at equation
    rw [out, psubst_pFor, psubst_tProc, psubst_par, dotted_resolves gp equation P foP closedP,
      dotted_resolves gp equation Q foQ closedQ, psubst_of_pvars_nil σ x closedX, psubst_pZero]

/-- The depth-zero REFL rule instance never takes a nested reflection: the
two take patterns have different constructors under every substitution. -/
theorem nested_reflection_needs_its_own_shape (x t u channel P Q y R : Pattern) (σ : PSubst) :
    psubst σ (pReflect x (par (pFor t channel P) (pFor u channel Q))) ≠
      psubst σ (pReflect x (pReflect y R)) := by
  simp [pReflect, par, pPar, psubst, psubst.psubstList]

/-- The nested REFL step is itself one firing of the same kind, with the
nested shape in its take pattern. -/
def nestedReflRule (x₁ x₂ t u channel P Q : Pattern) : RuleInstance Pattern :=
  ⟨[pReflect x₁ (pReflect x₂ (par (pFor t channel P) (pFor u channel Q)))], [], [(t, u)], [],
    [pFor (tProc (pFor (tProc (par (dotted (pvars t ++ pvars u) P) (dotted (pvars t ++ pvars u) Q)))
      x₂ pZero)) x₁ pZero]⟩

theorem nested_reflect_firing (x₁ x₂ t u channel P Q : Pattern) (bs : Bindings)
    (gp : GroundPrincipal t u bs) (foP : firstOrder P = true) (foQ : firstOrder Q = true)
    (closedP : ∀ v ∈ pvars P, v ∈ pvars t ++ pvars u)
    (closedQ : ∀ v ∈ pvars Q, v ∈ pvars t ++ pvars u)
    (closed₁ : pvars x₁ = []) (closed₂ : pvars x₂ = []) {σ : PSubst}
    (solved : psubst σ t = psubst σ u) :
    ReflectionClosure.Step GroundPrincipal SC
        (pReflect x₁ (pReflect x₂ (par (pFor t channel P) (pFor u channel Q))))
        (pFor (tProc (pFor (tProc (par (applyDot bs P) (applyDot bs Q))) x₂ pZero)) x₁ pZero) ∧
      (nestedReflRule x₁ x₂ t u channel P Q).produce =
        [pFor (tProc (pFor (tProc (par (dotted (pvars t ++ pvars u) P) (dotted (pvars t ++ pvars u) Q)))
          x₂ pZero)) x₁ pZero] ∧
      psubst σ (pFor (tProc (pFor (tProc (par (dotted (pvars t ++ pvars u) P)
          (dotted (pvars t ++ pvars u) Q))) x₂ pZero)) x₁ pZero) =
        pFor (tProc (pFor (tProc (par (applyDot bs P) (applyDot bs Q))) x₂ pZero)) x₁ pZero := by
  refine ⟨ReflectionClosure.nested_reflection x₁ x₂ (.comm t u channel P Q bs gp), rfl, ?_⟩
  rw [psubst_pFor, psubst_tProc, psubst_pFor, psubst_tProc, psubst_par,
    dotted_resolves gp solved P foP closedP, dotted_resolves gp solved Q foQ closedQ,
    psubst_of_pvars_nil σ x₁ closed₁, psubst_of_pvars_nil σ x₂ closed₂, psubst_pZero]

/-! ## Separations from the executable step -/

namespace Executable

def f₂ (first second : Pattern) : Pattern := .apply "f" [first, second]
def a : Pattern := .apply "a" []
def X : Pattern := .fvar "X"
def Y : Pattern := .fvar "Y"

/-- `for(f(X,Y) <- @0) X | for(f(Y,a) <- @0) 0`. -/
def triangular : Proc := par (pFor (f₂ X Y) demoChan X) (pFor (f₂ Y a) demoChan pZero)

theorem executable_unifier_is_triangular :
    unifyPattern? (f₂ X Y) (f₂ Y a) = some [("Y", a), ("X", Y)] := by
  decide +kernel

/-- One executable reduct keeps `Y`, which the principal unifier binds to `a`. -/
theorem executable_triangular_reduct : par (nQuote Y) pZero ∈ step triangular := by
  decide +kernel

/-- The principal unifier. -/
def mgu : Bindings := [("X", a), ("Y", a)]

theorem mgu_ground_principal : GroundPrincipal (f₂ X Y) (f₂ Y a) mgu where
  keys := by decide +kernel
  covers := by
    intro v member
    simp only [f₂, X, Y, a, pvars, pvars.pvarsList, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact ⟨a, by decide +kernel, rfl⟩
  solves := by decide +kernel
  principal := by
    intro σ equation v member value found
    simp only [f₂, X, Y, a, psubst, psubst.psubstList, Pattern.apply.injEq, List.cons.injEq,
      true_and, and_true] at equation
    simp only [f₂, X, Y, a, pvars, pvars.pvarsList, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · have same : value = a := by
        simpa [mgu, Bindings.lookup, a] using found.symm
      subst same
      exact equation.1.trans equation.2
    · have same : value = a := by
        simpa [mgu, Bindings.lookup, a] using found.symm
      subst same
      exact equation.2
    · have same : value = a := by
        simpa [mgu, Bindings.lookup, a] using found.symm
      subst same
      exact equation.2

theorem paper_bodies : applyDot mgu X = nQuote a ∧ applyDot mgu pZero = pZero := by
  constructor <;> decide +kernel

/-- **Separation.** The executable reduct is not the manuscript's reduct in
either bag order; every solution of the firing reads `@a` and `0`. -/
theorem triangular_separates :
    par (nQuote Y) pZero ∈ step triangular ∧
      par (nQuote Y) pZero ≠ par (applyDot mgu X) (applyDot mgu pZero) ∧
      par (nQuote Y) pZero ≠ par (applyDot mgu pZero) (applyDot mgu X) := by
  refine ⟨executable_triangular_reduct, ?_, ?_⟩ <;> rw [paper_bodies.1, paper_bodies.2] <;> decide +kernel

/-- The capture canary: the second process's free `a` is read as the first
process's bound `a`. -/
theorem executable_capture : demoCommCapture ∈ step demoCommSource := by
  decide +kernel

/-- The same source with the first bound variable renamed. The manuscript's
alpha rule relates the two sources, since `a1` is not free in the body. -/
def renamed : Proc := par (pFor (.fvar "a1") demoChan (.fvar "a1")) (pFor pZero demoChan (.fvar "a"))

theorem executable_renamed : par (nQuote pZero) (.fvar "a") ∈ step renamed := by
  decide +kernel

theorem executable_not_alpha_invariant :
    demoCommCapture ∈ step demoCommSource ∧ par (nQuote pZero) (.fvar "a") ∈ step renamed ∧
      par (nQuote pZero) (.fvar "a") ∉ step demoCommSource ∧ demoCommCapture ∉ step renamed := by
  refine ⟨executable_capture, executable_renamed, ?_, ?_⟩ <;> decide +kernel

/-- With each input opened apart, the principal solution keeps the second
process's free name: `@0 | a`. -/
theorem opened_canary_reads_free_name :
    GroundPrincipal (.fvar "a1") pZero [("a1", pZero)] ∧
      psubst (Bindings.lookup [("a1", pZero)]) (dotted (pvars (.fvar "a1") ++ pvars pZero) (.fvar "a1")) =
        nQuote pZero ∧
      psubst (Bindings.lookup [("a1", pZero)]) (dotted (pvars (.fvar "a1") ++ pvars pZero) (.fvar "a")) =
        .fvar "a" := by
  refine ⟨⟨by decide +kernel, ?_, by decide +kernel, ?_⟩, by decide +kernel, by decide +kernel⟩
  · intro v member
    simp [pvars, pvars.pvarsList, pZero] at member
    subst member
    exact ⟨pZero, by decide +kernel, rfl⟩
  · intro σ equation v member value found
    simp [pvars, pvars.pvarsList, pZero] at member
    subst member
    have same : value = pZero := by simpa [Bindings.lookup] using found.symm
    subst same
    simpa [psubst, pZero, psubst.psubstList] using equation

/-- `for(X <- @0)X | for(f(X) <- @0)0` with one shared name. -/
def shared : Proc := par (pFor X demoChan X) (pFor (.apply "f" [X]) demoChan pZero)

theorem executable_refuses_unrenamed : step shared = [] := by
  decide +kernel

/-- The same two inputs, opened apart, as occurrences `0` and `1`. -/
def openedLabel (n : Nat) : Pattern :=
  if n = 0 then pFor (.fvar "X1") demoChan (.fvar "X1")
  else if n = 1 then pFor (.apply "f" [.fvar "X2"]) demoChan pZero
  else if n = 2 then dotted ["X1", "X2"] (.fvar "X1")
  else dotted ["X1", "X2"] pZero

def openedSolution : PSubst := fun v => if v = "X1" then some (.apply "f" [.fvar "X2"]) else none

theorem opened_solves :
    psubst openedSolution (.fvar "X1") = psubst openedSolution (.apply "f" [.fvar "X2"]) := by
  decide +kernel

theorem opened_inputs_fire :
    (commSelection 0 1 2 3).Valid patternAction openedLabel
      (commRule (.fvar "X1") (.apply "f" [.fvar "X2"]) demoChan (.fvar "X1") pZero) ⟨[], {0, 1}⟩ := by
  refine (comm_valid_iff openedLabel _ _ _ _ _ _ 0 1 2 3).mpr
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl, ?_⟩
  refine ⟨openedSolution, ?_⟩
  intro e member
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · rfl
  · rfl
  · exact opened_solves

/-- A REFL step with a capture-free premise: the executable target is the
listener that the REFL firing produces. -/
def reflSource : Proc := pReflect demoChan (par (pFor (.fvar "a") demoChan (.fvar "a")) (pFor pZero demoChan pZero))

theorem executable_reflect_agrees :
    pFor (tProc (par (applyDot [("a", pZero)] (.fvar "a")) (applyDot [("a", pZero)] pZero))) demoChan pZero ∈
      step reflSource := by
  decide +kernel

end Executable

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
