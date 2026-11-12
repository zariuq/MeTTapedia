import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Families
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowContext

/-!
# Meet narrowing in the tree's fibre: a declaration lowered to the universe it is seen at

An equation `X ≐ t` at a universe, with `X : U_u` and an unknown `Y : U_w` of `t` at a type position reached through
domains of Π types, first components of Σ types and types of identity types (`HoldsVar`), sees the value of `Y`
twice: at its own declaration `U_w`, and, through `X`, inside a type of `U_u`. Every solution sends `Y` to a type
equal to a type of `U_u` (`HoldsVar.small`). So where `u` lies below `w`, the declaration of `Y` is lowered to the
**meet** `U_u` of the two views, at whatever position `Y` is declared.

* `lowerAt`, `lowerAt_narrows`, `lowerAt_formed`: the telescope with one universe declaration lowered, a narrowing
  of the telescope in the tree's sense (`CtxNarrows`), formed.
* `forced_meet`: every solution of the store is, as a typed substitution, equal to one into the lowered telescope.
  This is the hypothesis `forced` of the tree's `narrowingUpdate`, here **proved from the shape of the equation**.
* **The rule** (`meetUpdate`, `meetRule`): the tree's `narrowingUpdate` at the lowered telescope. It is exact
  (`meet_exact`, through `exact_iff_update`), and every update the rule returns is exact (`meetRule_exact`).
* **The reading** (`readMeet`, `readMeet_view`): read from the codes of the first equation, with no budget: the
  annotation is a universe, the left side is an unknown declared at a universe, and an unknown of the right side at
  a domain position is declared at a universe strictly above. It finds the update on an arbitrary store, and finds
  nothing where the equation has another shape.

The rule compares two universe heads by `S.R.cumulative` only. In the tower that is the order of level expressions
under every valuation, so a comparison that holds at some valuations and fails at others selects no narrowing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentUniverseInjective ContextualDependentCumulative ContextualDependentEtaDepth

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Lowering one declaration -/

section Lowering

/-- The telescope with the declaration at `j` replaced by the universe `u`. -/
def lowerAt : {n : Nat} → Ctx Head n → Fin n → Head → Ctx Head n
  | _, .nil, j, _ => j.elim0
  | _, .snoc Γ A, j, u => Fin.cases (.snoc Γ (.head u)) (fun j' => .snoc (lowerAt Γ j' u) A) j

theorem lookup_lowerAt_self : ∀ {n : Nat} (Γ : Ctx Head n) (j : Fin n) (u : Head),
    Ctx.lookup (lowerAt Γ j u) j = .head u := by
  intro n Γ
  induction Γ with
  | nil => intro j; exact j.elim0
  | snoc Γ A ih =>
      intro j u
      cases j using Fin.cases with
      | zero =>
          simp only [lowerAt, Fin.cases_zero, Ctx.lookup_snoc_zero]
          rfl
      | succ j =>
          simp only [lowerAt, Fin.cases_succ, Ctx.lookup_snoc_succ, ih]
          rfl

theorem lookup_lowerAt_ne : ∀ {n : Nat} (Γ : Ctx Head n) (j i : Fin n) (u : Head), i ≠ j →
    Ctx.lookup (lowerAt Γ j u) i = Ctx.lookup Γ i := by
  intro n Γ
  induction Γ with
  | nil => intro j; exact j.elim0
  | snoc Γ A ih =>
      intro j i u ne
      cases j using Fin.cases with
      | zero =>
          cases i using Fin.cases with
          | zero => exact absurd rfl ne
          | succ i => simp only [lowerAt, Fin.cases_zero, Ctx.lookup_snoc_succ]
      | succ j =>
          cases i using Fin.cases with
          | zero => simp only [lowerAt, Fin.cases_succ, Ctx.lookup_snoc_zero]
          | succ i =>
              have ne' : i ≠ j := fun same => ne (by rw [same])
              simp only [lowerAt, Fin.cases_succ, Ctx.lookup_snoc_succ, ih j i u ne']

variable {R : Rules Head}

theorem lowerAt_narrows : ∀ {n : Nat} (Γ : Ctx Head n) (j : Fin n) {u w : Head},
    Ctx.lookup Γ j = .head w → R.cumulative u w → CtxNarrows R Γ (lowerAt Γ j u) := by
  intro n Γ
  induction Γ with
  | nil => intro j; exact j.elim0
  | snoc Γ A ih =>
      intro j u w declared below
      cases j using Fin.cases with
      | zero =>
          rw [Ctx.lookup_snoc_zero] at declared
          have same : A = .head w := rename_wk_inj (declared.trans rfl)
          subst same
          simp only [lowerAt, Fin.cases_zero]
          exact .lower (CtxNarrows.refl Γ) below
      | succ j =>
          rw [Ctx.lookup_snoc_succ] at declared
          have inner : Ctx.lookup Γ j = .head w := rename_wk_inj (declared.trans rfl)
          simp only [lowerAt, Fin.cases_succ]
          exact .same A (ih j inner below)

end Lowering

section Formed

variable {S : Setting Head L}

theorem lowerAt_formed : ∀ {n : Nat} (Γ : Ctx Head n) (j : Fin n) {u w : Head}, CtxFormed S.R Γ →
    Ctx.lookup Γ j = .head w → S.R.cumulative u w → S.R.isUniverse u → CtxFormed S.R (lowerAt Γ j u) := by
  intro n Γ
  induction Γ with
  | nil => intro j; exact j.elim0
  | snoc Γ A ih =>
      intro j u w formed declared below hu
      cases formed with
      | snoc formedΓ typeA =>
          cases j using Fin.cases with
          | zero =>
              simp only [lowerAt, Fin.cases_zero]
              exact formedΓ.snoc (IsType.head_of_universe hu)
          | succ j =>
              rw [Ctx.lookup_snoc_succ] at declared
              have inner : Ctx.lookup Γ j = .head w := rename_wk_inj (declared.trans rfl)
              simp only [lowerAt, Fin.cases_succ]
              exact (ih j formedΓ inner below hu).snoc (isType_narrow (lowerAt_narrows Γ j inner below) typeA)

/-- **The lowering of one declaration**, as a narrowing of the telescope in the tree's sense. -/
def lowering (Θ : Context S.R) (Y : Fin Θ.arity) {u w : Head} (declared : Ctx.lookup Θ.raw Y = .head w)
    (below : S.R.cumulative u w) (hu : S.R.isUniverse u) : Narrowing Θ where
  raw := lowerAt Θ.raw Y u
  formed := lowerAt_formed Θ.raw Y Θ.formed declared below hu
  narrows := lowerAt_narrows Θ.raw Y declared below

end Formed

/-! ## The shape and its forcing -/

section Forcing

variable {S : Setting Head L}

/-- **An equation that sees an unknown below its declaration**: `X ≐ t` at a universe `U_v`, with `X : U_u`, and an
unknown `Y : U_w` of `t` at a domain position, where `u` lies below `w`. -/
structure SeesBelow {Θ : Context S.R} (e : Equation (TotalTerm Θ)) where
  v : Head
  X : Fin Θ.arity
  Y : Fin Θ.arity
  u : Head
  w : Head
  annotation : e.1.1.code = .head v
  universe_v : S.R.isUniverse v
  side_left : e.1.2.code = .var X
  declared_X : Ctx.lookup Θ.raw X = .head u
  holds : HoldsVar Y e.2.2.code
  declared_Y : Ctx.lookup Θ.raw Y = .head w
  universe_u : S.R.isUniverse u
  universe_w : S.R.isUniverse w
  below : S.R.cumulative u w

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **What the equation forces**: every solution sends `Y` to a type equal to a type of `U_u`. -/
theorem forced_small {Θ Δ : Context S.R} {e : Equation (TotalTerm Θ)} (view : SeesBelow e) (σ : Δ ⟶ Θ)
    (solved : (frames S.levels).Solves σ e) :
    ∃ small, Typed S.R Δ.raw small (.head view.u) ∧ TypeEq S.R Δ.raw small (σ.substitution view.Y) := by
  have equal := ((equivalent_iff S.levels _ _).mp solved).2
  change Equal S.R Δ.raw (Presentation.subst σ.substitution e.1.2.code)
    (Presentation.subst σ.substitution e.2.2.code) (Presentation.subst σ.substitution e.1.1.code) at equal
  rw [view.side_left, view.annotation] at equal
  have tX : Typed S.R Δ.raw (σ.substitution view.X) (.head view.u) := by
    have typed := σ.typed view.X
    rw [view.declared_X] at typed
    exact typed
  exact HoldsVar.small facts roots heads algebra rigid complete view.holds Δ.formed view.universe_u σ.substitution
    tX ⟨view.v, view.universe_v, equal⟩

/-- The substitution that sends `Y` to `small`, and every other unknown where `σ` does. -/
def replaceAt {n m : Nat} (σ : Sub Head n m) (Y : Fin n) (small : Tm Head m) : Sub Head n m :=
  fun i => if i = Y then small else σ i

theorem replaceAt_self {n m : Nat} (σ : Sub Head n m) (Y : Fin n) (small : Tm Head m) :
    replaceAt σ Y small Y = small := by
  simp [replaceAt]

theorem replaceAt_ne {n m : Nat} (σ : Sub Head n m) {Y i : Fin n} (small : Tm Head m) (ne : i ≠ Y) :
    replaceAt σ Y small i = σ i := by
  simp [replaceAt, ne]

include facts roots heads algebra rigid complete in
/-- **Every solution factors through the lowered telescope**: the hypothesis `forced` of `narrowingUpdate`, proved
from the shape of the first equation. -/
theorem forced_meet {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (view : SeesBelow e)
    (rest : EquationStore (TotalTerm Θ)) :
    ∀ (Δ : Context S.R) (σ : Δ ⟶ Θ), (frames S.levels).Models σ (e :: rest) →
      ∃ τ : Δ ⟶ (lowering Θ view.Y view.declared_Y view.below view.universe_u).context,
        homTypedEquality S.R σ (τ ≫ (lowering Θ view.Y view.declared_Y view.below view.universe_u).hom) := by
  intro Δ σ solved
  obtain ⟨small, tSmall, eSmall⟩ :=
    forced_small facts roots heads algebra rigid complete view σ (solved e List.mem_cons_self)
  have tY : Typed S.R Δ.raw (σ.substitution view.Y) (.head view.w) := by
    have typed := σ.typed view.Y
    rw [view.declared_Y] at typed
    exact typed
  obtain ⟨x, hx, eX⟩ := eSmall
  have atW : Equal S.R Δ.raw small (σ.substitution view.Y) (.head view.w) :=
    universe_injective facts roots heads algebra rigid complete Δ.formed view.universe_w hx
      (Derivable.cumul tSmall view.below) tY eX
  have same : SubstEq S.R Θ.raw Δ.raw σ.substitution (replaceAt σ.substitution view.Y small) := by
    refine ⟨σ.typed, fun i => ?_⟩
    by_cases h : i = view.Y
    · rw [h, replaceAt_self, view.declared_Y]
      exact .symm atW
    · rw [replaceAt_ne _ _ h]
      exact .refl (σ.typed i)
  have typed : SubstMor S.R (lowerAt Θ.raw view.Y view.u) Δ.raw (replaceAt σ.substitution view.Y small) := by
    intro i
    by_cases h : i = view.Y
    · rw [h, lookup_lowerAt_self, replaceAt_self]
      exact tSmall
    · rw [lookup_lowerAt_ne Θ.raw view.Y i view.u h, replaceAt_ne _ _ h]
      obtain ⟨level, hlevel, tA⟩ := Θ.formed.lookup i
      have types : TypeEq S.R Δ.raw (Presentation.subst σ.substitution (Ctx.lookup Θ.raw i))
          (Presentation.subst (replaceAt σ.substitution view.Y small) (Ctx.lookup Θ.raw i)) :=
        ⟨level, hlevel, Typed.functional tA same⟩
      exact Typed.convType (σ.typed i) types
  exact ⟨⟨replaceAt σ.substitution view.Y small, typed⟩, same⟩

/-! ## The rule -/

/-- **Meet narrowing**: the declaration of `Y` lowered to `U_u`; the store is read over the lowered telescope. -/
def meetUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (view : SeesBelow e)
    (rest : EquationStore (TotalTerm Θ)) : Update S.levels (e :: rest) :=
  narrowingUpdate (lowering Θ view.Y view.declared_Y view.below view.universe_u) (e :: rest)
    (forced_meet facts roots heads algebra rigid complete view rest)

include facts roots heads algebra rigid complete in
/-- **Meet narrowing is exact.** -/
theorem meet_exact {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (view : SeesBelow e)
    (rest : EquationStore (TotalTerm Θ)) :
    Exact (frames S.levels) (e :: rest) (lowering Θ view.Y view.declared_Y view.below view.universe_u).hom
      ((frames S.levels).applyStore (lowering Θ view.Y view.declared_Y view.below view.universe_u).hom (e :: rest)) :=
  (DependentFibre.exact_iff_update (levels := S.levels) _ _).mpr
    ⟨meetUpdate facts roots heads algebra rigid complete view rest, rfl, rfl, rfl⟩

end Forcing

/-! ## The reading -/

section Reading

/-- The unknowns of a code at domain positions. -/
def domainVars : {n : Nat} → Tm Head n → List (Fin n)
  | _, .var i => [i]
  | _, .pi A _ => domainVars A
  | _, .sigma A _ => domainVars A
  | _, .id A _ _ => domainVars A
  | _, _ => []

theorem holdsVar_of_mem : ∀ {n : Nat} {t : Tm Head n} {Y : Fin n}, Y ∈ domainVars t → HoldsVar Y t := by
  intro n t
  induction t with
  | var i => intro Y member; rw [List.mem_singleton.mp member]; exact .here
  | pi A B ihA _ => intro Y member; exact .piDomain (ihA member)
  | sigma A B ihA _ => intro Y member; exact .sigmaFirst (ihA member)
  | id A a b ihA _ _ => intro Y member; exact .id (ihA member)
  | const => intro Y member; cases member
  | head => intro Y member; cases member
  | lam => intro Y member; cases member
  | app => intro Y member; cases member
  | pair => intro Y member; cases member
  | fst => intro Y member; cases member
  | snd => intro Y member; cases member
  | refl => intro Y member; cases member

/-- The head of a code, if it is one. -/
def headOf {n : Nat} : Tm Head n → Option Head
  | .head v => some v
  | _ => none

theorem headOf_sound {n : Nat} {t : Tm Head n} {v : Head} (h : headOf t = some v) : t = .head v := by
  cases t
  case head v' => cases h; rfl
  all_goals cases h

/-- The unknown a code is, if it is one. -/
def varOf {n : Nat} : Tm Head n → Option (Fin n)
  | .var i => some i
  | _ => none

theorem varOf_sound {n : Nat} {t : Tm Head n} {i : Fin n} (h : varOf t = some i) : t = .var i := by
  cases t
  case var i' => cases h; rfl
  all_goals cases h

/-- The universe an unknown is declared at, if it is one. -/
def declaredUniverse {n : Nat} (Γ : Ctx Head n) (i : Fin n) : Option Head := headOf (Ctx.lookup Γ i)

variable {S : Setting Head L} [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **Read the meet narrowing off the first equation**: annotation, left unknown, its universe, and an unknown at
a domain position of the right side declared strictly above it. -/
def readMeetData {Θ : Context S.R} (e : Equation (TotalTerm Θ)) :
    Option (Head × Fin Θ.arity × Head × Fin Θ.arity × Head) :=
  (headOf e.1.1.code).bind fun v =>
  (varOf e.1.2.code).bind fun X =>
  (declaredUniverse Θ.raw X).bind fun u =>
  (((domainVars e.2.2.code).filterMap fun Y => (declaredUniverse Θ.raw Y).bind fun w =>
      if S.R.isUniverse v ∧ S.R.isUniverse u ∧ S.R.isUniverse w ∧ S.R.cumulative u w ∧ ¬ S.R.cumulative w u then
        some (Y, w)
      else none).head?).map fun yw => (v, X, u, yw.1, yw.2)

/-- What a successful reading says. -/
theorem readMeetData_sound {Θ : Context S.R} {e : Equation (TotalTerm Θ)}
    {d : Head × Fin Θ.arity × Head × Fin Θ.arity × Head} (h : readMeetData e = some d) :
    e.1.1.code = .head d.1 ∧ e.1.2.code = .var d.2.1 ∧ Ctx.lookup Θ.raw d.2.1 = .head d.2.2.1 ∧
      d.2.2.2.1 ∈ domainVars e.2.2.code ∧ Ctx.lookup Θ.raw d.2.2.2.1 = .head d.2.2.2.2 ∧
      S.R.isUniverse d.1 ∧ S.R.isUniverse d.2.2.1 ∧ S.R.isUniverse d.2.2.2.2 ∧
      S.R.cumulative d.2.2.1 d.2.2.2.2 ∧ ¬ S.R.cumulative d.2.2.2.2 d.2.2.1 := by
  unfold readMeetData at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, X, hX, u, hu, ⟨Y, w⟩, found, rfl⟩ := h
  have inList := List.mem_of_mem_head? found
  obtain ⟨Y', member, hY'⟩ := List.mem_filterMap.mp inList
  simp only [Option.bind_eq_some_iff] at hY'
  obtain ⟨w', hw', hcond⟩ := hY'
  split_ifs at hcond with hc
  cases hcond
  exact ⟨headOf_sound hv, varOf_sound hX, headOf_sound hu, member, headOf_sound hw', hc⟩

/-- The view of a successful reading. -/
def viewMeet {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {d : Head × Fin Θ.arity × Head × Fin Θ.arity × Head}
    (h : readMeetData e = some d) : SeesBelow e where
  v := d.1
  X := d.2.1
  Y := d.2.2.2.1
  u := d.2.2.1
  w := d.2.2.2.2
  annotation := (readMeetData_sound h).1
  universe_v := (readMeetData_sound h).2.2.2.2.2.1
  side_left := (readMeetData_sound h).2.1
  declared_X := (readMeetData_sound h).2.2.1
  holds := holdsVar_of_mem (readMeetData_sound h).2.2.2.1
  declared_Y := (readMeetData_sound h).2.2.2.2.1
  universe_u := (readMeetData_sound h).2.2.2.2.2.2.1
  universe_w := (readMeetData_sound h).2.2.2.2.2.2.2.1
  below := (readMeetData_sound h).2.2.2.2.2.2.2.2.1

/-- **The reading of the meet narrowing.** -/
def readMeet {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (SeesBelow e) :=
  match h : readMeetData e with
  | some _ => some (viewMeet h)
  | none => none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **The meet narrowing rule** on a store: read the first equation, and lower the declaration it sees below. -/
def meetRule {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Update S.levels problem)
  | [] => none
  | e :: rest => (readMeet e).map fun view => meetUpdate facts roots heads algebra rigid complete view rest

/-- **Every update the rule returns is exact.** -/
theorem meetRule_exact {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {update : Update S.levels problem}
    (_ : meetRule facts roots heads algebra rigid complete problem = some update) :
    Exact (frames S.levels) problem update.answer update.remaining :=
  (DependentFibre.exact_iff_update (levels := S.levels) update.answer update.remaining).mpr
    ⟨update, rfl, rfl, rfl⟩

end Reading

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
