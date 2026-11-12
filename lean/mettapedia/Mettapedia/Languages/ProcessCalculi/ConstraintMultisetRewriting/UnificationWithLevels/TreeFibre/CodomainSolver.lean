import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CodomainReading

/-!
# Flex–rigid stores with unknowns at codomain positions, decided

**The fragment** (`InFlexCod`): every equation `X ≐ t` at a universe, `t` an arrow code with codomains; the unknowns
met declared at universes (`AtUniverses`) and no declaration mentioning them (`SidesApart`), the rest of the telescope
arbitrary; the heads of the codes typed by the computed head typings; distinct left unknowns. It contains the fragment
of flex–rigid stores without the chain (`inFlexCod_of_flexRigidGlb`), whose codes have heads at their codomains.

**The round** reads the first equation and deletes `X ≐ X`, refutes by the full occurs check or by a misfit head, or
narrows the misfit unknowns to greatest lower bounds and solves (`codNarrowSolveUpdate`).

**Kept by the rounds** (`flexCodRound_stable`): instantiation keeps the codes (`arrowCod_subst_solve`) and brings only
heads of the solved code. **Never stuck** on a nonempty store of the fragment, for a total greatest lower bound.
**Decided** (`flexCod_decided`): from some budget on, a principal answer or a certified refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Unknowns of arrow codes with codomains -/

section Support

/-- The unknowns of a Π code with codomains: those of the domain and those of the codomain. -/
theorem mem_support_pi_wk {n : Nat} {A B : Tm Head n} {i : Fin n} :
    i ∈ (Tm.pi A (Presentation.rename wk B)).support ↔ i ∈ A.support ∨ i ∈ B.support := by
  simp only [Tm.support, ContextualDependentSupport.support_rename, Finset.mem_union, mem_outerSupport,
    Finset.mem_image]
  constructor
  · rintro (h | ⟨j, hj, same⟩)
    · exact .inl h
    · have back : j = i := Fin.succ_injective _ same
      exact .inr (back ▸ hj)
  · rintro (h | h)
    · exact .inl h
    · exact .inr ⟨i, h, rfl⟩

/-- **After `X := t`, the unknowns of an arrow code with codomains are its own without `X`, and those of `t`.** -/
theorem support_subst_solve {n : Nat} {X : Fin n} {t : Tm Head n} :
    ∀ {s : Tm Head n}, ArrowCod s → ∀ i, i ∈ (Presentation.subst (solveSub X t) s).support →
      (i ∈ s.support ∧ i ≠ X) ∨ i ∈ t.support := by
  intro s code
  induction code with
  | var Y =>
      intro i member
      by_cases hY : Y = X
      · subst hY
        have same : Presentation.subst (solveSub Y t) (.var Y) = t := solveSub_self Y t
        rw [same] at member
        exact .inr member
      · have same : Presentation.subst (solveSub X t) (.var Y) = .var Y := solveSub_ne t hY
        rw [same] at member
        have back : i = Y := Finset.mem_singleton.mp member
        subst back
        exact .inl ⟨Finset.mem_singleton_self _, hY⟩
  | head h =>
      intro i member
      simp [Presentation.subst, Tm.support] at member
  | @pi A B _ _ ihA ihB =>
      intro i member
      change i ∈ (Tm.pi (Presentation.subst (solveSub X t) A)
        (Presentation.subst (liftSub (solveSub X t)) (Presentation.rename wk B))).support at member
      rw [subst_liftSub_wk, mem_support_pi_wk] at member
      rcases member with inA | inB
      · rcases ihA i inA with ⟨h, ne⟩ | h
        · exact .inl ⟨mem_support_pi_wk.mpr (.inl h), ne⟩
        · exact .inr h
      · rcases ihB i inB with ⟨h, ne⟩ | h
        · exact .inl ⟨mem_support_pi_wk.mpr (.inr h), ne⟩
        · exact .inr h

/-- **No declaration mentions an unknown of the two sides.** -/
def SidesApart {n : Nat} (Γ : Ctx Head n) (l r : Tm Head n) : Prop :=
  ∀ i, ∀ j ∈ (Ctx.lookup Γ i).support, j ∉ l.support ∧ j ∉ r.support

theorem SidesApart.swap {n : Nat} {Γ : Ctx Head n} {l r : Tm Head n} (apart : SidesApart Γ l r) :
    SidesApart Γ r l :=
  fun i j member => ⟨(apart i j member).2, (apart i j member).1⟩

/-- Whether no declaration mentions an unknown of the two sides, decided. -/
def sidesApartB {n : Nat} (Γ : Ctx Head n) (l r : Tm Head n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    !decide (j ∈ (Ctx.lookup Γ i).support) || (!decide (j ∈ l.support) && !decide (j ∈ r.support))

theorem sidesApart_of_B {n : Nat} {Γ : Ctx Head n} {l r : Tm Head n} (h : sidesApartB Γ l r = true) :
    SidesApart Γ l r := by
  intro i j member
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  have hj := List.all_eq_true.mp hi j (List.mem_finRange j)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Bool.and_eq_true]
    at hj
  rcases hj with absent | ⟨hl, hr⟩
  · exact absurd member absent
  · exact ⟨hl, hr⟩

theorem sidesApartB_of {n : Nat} {Γ : Ctx Head n} {l r : Tm Head n} (h : SidesApart Γ l r) :
    sidesApartB Γ l r = true := by
  apply List.all_eq_true.mpr
  intro i _
  apply List.all_eq_true.mpr
  intro j _
  by_cases member : j ∈ (Ctx.lookup Γ i).support
  · obtain ⟨hl, hr⟩ := h i j member
    simp [hl, hr]
  · simp [member]

/-- Declarations at universes mention no unknown of any sides. -/
theorem sidesApart_of_universes {S : Setting Head L} {Θ : Context S.R} (universes : AllUniverseDecls Θ)
    (l r : Tm Head Θ.arity) : SidesApart Θ.raw l r :=
  apart_of_universes universes

end Support

/-! ## The fragment -/

section Fragment

variable {S : Setting Head L}

/-- **The unknowns of a code are declared at universes.** -/
def AtUniverses {n : Nat} (Γ : Ctx Head n) (t : Tm Head n) : Prop :=
  ∀ Y ∈ t.support, ∃ w, Ctx.lookup Γ Y = .head w ∧ S.R.isUniverse w

/-- Whether the unknowns of a code are declared at universes, decided. -/
def atUniversesB [∀ head, Decidable (S.R.isUniverse head)] {n : Nat} (Γ : Ctx Head n) (t : Tm Head n) : Bool :=
  (List.finRange n).all fun Y => !decide (Y ∈ t.support) ||
    match headOf (Ctx.lookup Γ Y) with
    | some w => decide (S.R.isUniverse w)
    | none => false

theorem atUniverses_of_B [∀ head, Decidable (S.R.isUniverse head)] {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}
    (h : atUniversesB (S := S) Γ t = true) : AtUniverses (S := S) Γ t := by
  intro Y member
  have hY := List.all_eq_true.mp h Y (List.mem_finRange Y)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hY
  rcases hY with absent | found
  · exact absurd member absent
  · cases hw : headOf (Ctx.lookup Γ Y) with
    | none => rw [hw] at found; cases found
    | some w =>
        rw [hw] at found
        exact ⟨w, headOf_sound hw, of_decide_eq_true found⟩

theorem atUniversesB_of [∀ head, Decidable (S.R.isUniverse head)] {n : Nat} {Γ : Ctx Head n} {t : Tm Head n}
    (h : AtUniverses (S := S) Γ t) : atUniversesB (S := S) Γ t = true := by
  apply List.all_eq_true.mpr
  intro Y _
  by_cases member : Y ∈ t.support
  · obtain ⟨w, hw, uw⟩ := h Y member
    simp only [hw, headOf, uw, decide_true, Bool.or_true]
  · simp [member]

/-- An unknown at a universe, read through the declaration. -/
theorem universe_of_atUniverses {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} (occurring : AtUniverses (S := S) Γ t)
    {X : Fin n} (member : X ∈ t.support) {u : Head} (hu : declaredUniverse Γ X = some u) : S.R.isUniverse u := by
  obtain ⟨w, hw, uw⟩ := occurring X member
  unfold declaredUniverse at hu
  rw [hw] at hu
  cases hu
  exact uw

/-- **The fragment of flex–rigid stores with codomains**: the unknowns of the codes declared at universes, no
declaration mentioning an unknown of the store. -/
structure InFlexCod (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Prop where
  occurring : ∀ e ∈ problem, AtUniverses (S := S) Θ.raw e.2.2.code
  apart : ∀ e ∈ problem, SidesApart Θ.raw e.1.2.code e.2.2.code
  shapes : ∀ e ∈ problem, Nonempty (FlexCod e)
  typedHeads : ∀ e ∈ problem, ∀ h ∈ codHeads e.2.2.code, (choices.typing h).isSome = true
  distinct : problem.Pairwise (fun e₁ e₂ => ∀ (v₁ : FlexCod e₁) (v₂ : FlexCod e₂), v₁.X ≠ v₂.X)

theorem inFlexCod_delete {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InFlexCod choices (e :: rest)) :
    InFlexCod choices rest :=
  ⟨fun e' member => inside.occurring e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.apart e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.shapes e' (List.mem_cons_of_mem _ member),
    fun e' member => inside.typedHeads e' (List.mem_cons_of_mem _ member), (List.pairwise_cons.mp inside.distinct).2⟩

/-- The rule's condition on declarations, read from the sides. -/
theorem codApart_of_sides {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e)
    (apart : SidesApart Θ.raw e.1.2.code e.2.2.code) :
    ∀ i, ∀ j ∈ (Ctx.lookup Θ.raw i).support, j ≠ v.X ∧ j ∉ e.2.2.code.support := by
  intro i j member
  refine ⟨fun same => (apart i j member).1 ?_, (apart i j member).2⟩
  rw [v.side_left, same]
  exact Finset.mem_singleton_self _

/-- A first-order arrow code's heads are its heads as a code with codomains. -/
theorem mem_codHeads_of_arrow {n : Nat} {t : Tm Head n} (arrow : Arrow t) :
    ∀ h, h ∈ codHeads t → h ∈ arrowHeads t := by
  induction arrow with
  | var Y => intro h member; cases member
  | head h => intro h' member; exact member
  | @pi A h _ ih =>
      intro h' member
      change h' ∈ codHeads A ++ codHeads (.head h) at member
      rcases List.mem_append.mp member with inA | inH
      · exact List.mem_cons_of_mem _ (ih h' inA)
      · have same : h' = h := List.mem_singleton.mp inH
        rw [same]
        exact List.mem_cons_self

/-- A flex–rigid view is a view with codomains. -/
def FlexArrow.toCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexArrow e) : FlexCod e where
  v := v.v
  X := v.X
  u := v.u
  annotation_left := v.annotation_left
  annotation_right := v.annotation_right
  side_left := v.side_left
  declared := v.declared
  universe_u := v.universe_u
  universe_v := v.universe_v
  code := arrowCod_of_arrow v.arrow

/-- **The fragment of flex–rigid stores without the chain lies inside.** -/
theorem inFlexCod_of_flexRigidGlb {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} (inside : InFlexRigidGlb choices problem) : InFlexCod choices problem := by
  refine ⟨fun _ _ Y _ => inside.universes Y, fun _ _ => sidesApart_of_universes inside.universes _ _,
    fun e member => ?_, fun e member h hh => ?_, ?_⟩
  · obtain ⟨v⟩ := inside.shapes e member
    exact ⟨v.toCod⟩
  · obtain ⟨v⟩ := inside.shapes e member
    exact inside.typedHeads e member h (mem_codHeads_of_arrow v.arrow h hh)
  · refine inside.distinct.imp_of_mem ?_
    intro e₁ e₂ m₁ m₂ apart v₁ v₂
    obtain ⟨w₁⟩ := inside.shapes e₁ m₁
    obtain ⟨w₂⟩ := inside.shapes e₂ m₂
    rw [FlexCod.unique v₁ w₁.toCod, FlexCod.unique v₂ w₂.toCod]
    exact apart w₁ w₂

variable [DecidableRel S.R.cumulative] (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b) (algebra : CumulativeAlgebra S.R)

/-- The declaration of an unknown after narrowing: a greatest lower bound where it was a misfit, unchanged
otherwise. -/
theorem codNarrowed_lookup {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) (i : Fin Θ.arity) :
    (∃ g, Ctx.lookup (codNarrowed glb spec v).raw i = .head g ∧ S.R.isUniverse g) ∨
      Ctx.lookup (codNarrowed glb spec v).raw i = Ctx.lookup Θ.raw i := by
  cases found : codTarget (S := S) glb Θ.raw v.u e.2.2.code i with
  | some g => exact Or.inl ⟨g, lookup_lowerTo_some Θ.raw _ i found, codTarget_universe glb spec i g found⟩
  | none => exact Or.inr (lookup_lowerTo_none Θ.raw _ i found)

/-- **The view of an equation after narrowing and solving.** -/
theorem codNarrowSolve_view {Θ : Context S.R} {e e' : Equation (TotalTerm Θ)} (v : FlexCod e)
    (ok : CodSolvable glb v) (w : FlexCod e') (ne : w.X ≠ v.X) :
    ∃ t : FlexCod (((frames S.levels).act (codNarrowSolve glb spec algebra v ok) e'.1,
        (frames S.levels).act (codNarrowSolve glb spec algebra v ok) e'.2) :
          Equation (TotalTerm (codNarrowed glb spec v))), t.X = w.X := by
  have declared : ∃ u', Ctx.lookup (codNarrowed glb spec v).raw w.X = .head u' ∧ S.R.isUniverse u' := by
    rcases codNarrowed_lookup glb spec v w.X with low | same
    · exact low
    · exact ⟨w.u, same.trans w.declared, w.universe_u⟩
  obtain ⟨u', hu', uu'⟩ := declared
  exact ⟨{
    v := w.v
    X := w.X
    u := u'
    annotation_left := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.1.1.code = .head w.v
      rw [w.annotation_left]
      rfl
    annotation_right := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.2.1.code = .head w.v
      rw [w.annotation_right]
      rfl
    side_left := by
      change Presentation.subst (solveSub v.X e.2.2.code) e'.1.2.code = .var w.X
      rw [w.side_left]
      exact solveSub_ne _ ne
    declared := hu'
    universe_u := uu'
    universe_v := w.universe_v
    code := arrowCod_subst_solve v.code w.code }, rfl⟩

/-- **After narrowing and solving, an unknown declared at a universe stays declared at one.** -/
theorem codNarrowed_atUniverse {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) {i : Fin Θ.arity}
    (before : ∃ w, Ctx.lookup Θ.raw i = .head w ∧ S.R.isUniverse w) :
    ∃ w, Ctx.lookup (codNarrowed glb spec v).raw i = .head w ∧ S.R.isUniverse w := by
  rcases codNarrowed_lookup glb spec v i with low | same
  · exact low
  · obtain ⟨w, hw, uw⟩ := before
    exact ⟨w, same.trans hw, uw⟩

/-- **After narrowing and solving, an instantiated arrow code keeps its unknowns at universes.** -/
theorem atUniverses_solved {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) {s : Tm Head Θ.arity}
    (code : ArrowCod s) (occS : AtUniverses (S := S) Θ.raw s) (occT : AtUniverses (S := S) Θ.raw e.2.2.code) :
    AtUniverses (S := S) (codNarrowed glb spec v).raw (Presentation.subst (solveSub v.X e.2.2.code) s) := by
  intro Y member
  rcases support_subst_solve code Y member with ⟨inS, _⟩ | inT
  · exact codNarrowed_atUniverse glb spec v (occS Y inS)
  · exact codNarrowed_atUniverse glb spec v (occT Y inT)

/-- **After narrowing and solving, no declaration mentions an unknown of the instantiated sides.** -/
theorem sidesApart_solved {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) {l r : Tm Head Θ.arity}
    (codeL : ArrowCod l) (codeR : ArrowCod r) (apart : SidesApart Θ.raw l r)
    (apartE : SidesApart Θ.raw e.1.2.code e.2.2.code) :
    SidesApart (codNarrowed glb spec v).raw (Presentation.subst (solveSub v.X e.2.2.code) l)
      (Presentation.subst (solveSub v.X e.2.2.code) r) := by
  intro i j member
  have old : j ∈ (Ctx.lookup Θ.raw i).support := by
    rcases codNarrowed_lookup glb spec v i with ⟨g, hg, _⟩ | same
    · rw [hg] at member
      simp [Tm.support] at member
    · rwa [same] at member
  obtain ⟨notL, notR⟩ := apart i j old
  have notT := (apartE i j old).2
  refine ⟨fun inside => ?_, fun inside => ?_⟩
  · rcases support_subst_solve codeL j inside with ⟨h, _⟩ | h
    · exact notL h
    · exact notT h
  · rcases support_subst_solve codeR j inside with ⟨h, _⟩ | h
    · exact notR h
    · exact notT h

/-- **Narrowing to greatest lower bounds and solving keeps the fragment.** -/
theorem inFlexCod_narrowSolve {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)} (inside : InFlexCod choices (e :: rest))
    (v : FlexCod e) (ok : CodSolvable glb v) :
    InFlexCod choices ((frames S.levels).applyStore (codNarrowSolve glb spec algebra v ok) rest) := by
  have tail := List.pairwise_cons.mp inside.distinct
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    exact atUniverses_solved glb spec v w.code (inside.occurring e' (List.mem_cons_of_mem _ inRest))
      (inside.occurring e List.mem_cons_self)
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    have codeL : ArrowCod e'.1.2.code := by rw [w.side_left]; exact .var w.X
    exact sidesApart_solved glb spec v codeL w.code (inside.apart e' (List.mem_cons_of_mem _ inRest))
      (inside.apart e List.mem_cons_self)
  · intro e'' member
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    obtain ⟨t, _⟩ := codNarrowSolve_view glb spec algebra v ok w (fun same => tail.1 e' inRest v w same.symm)
    exact ⟨t⟩
  · intro e'' member h hh
    obtain ⟨e', inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨w⟩ := inside.shapes e' (List.mem_cons_of_mem _ inRest)
    rcases codHeads_subst_solve w.code h hh with fromE' | fromE
    · exact inside.typedHeads e' (List.mem_cons_of_mem _ inRest) h fromE'
    · exact inside.typedHeads e List.mem_cons_self h fromE
  · refine List.pairwise_map.mpr (tail.2.imp_of_mem ?_)
    intro e₁ e₂ m₁ m₂ apart t₁ t₂
    obtain ⟨w₁⟩ := inside.shapes e₁ (List.mem_cons_of_mem _ m₁)
    obtain ⟨w₂⟩ := inside.shapes e₂ (List.mem_cons_of_mem _ m₂)
    obtain ⟨s₁, h₁⟩ := codNarrowSolve_view glb spec algebra v ok w₁ (fun same => tail.1 e₁ m₁ v w₁ same.symm)
    obtain ⟨s₂, h₂⟩ := codNarrowSolve_view glb spec algebra v ok w₂ (fun same => tail.1 e₂ m₂ v w₂ same.symm)
    rw [FlexCod.unique t₁ s₁, FlexCod.unique t₂ s₂, h₁, h₂]
    exact apart w₁ w₂

end Fragment

/-! ## The solver -/

section Solver

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R) (glb : Head → Head → Option Head)
  (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- A fitting unknown, or a misfit unknown with a greatest lower bound with `u`. -/
def codMeetsPred {n : Nat} (Γ : Ctx Head n) (u : Head) (t : Tm Head n) (i : Fin n) : Bool :=
  !(codMisfit (S := S) Γ u t i) || (codTarget (S := S) glb Γ u t i).isSome

/-- **The conditions of the rule, decided.** -/
def codSolvableB {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e) : Bool :=
  (codHeads e.2.2.code).all (fitPred choices v.u) &&
    (List.finRange Θ.arity).all (codMeetsPred (S := S) glb Θ.raw v.u e.2.2.code) &&
    atUniversesB (S := S) Θ.raw e.2.2.code && sidesApartB Θ.raw e.1.2.code e.2.2.code

omit [DecidableEq Head] in
theorem codSolvable_of_B {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e)
    (h : codSolvableB choices glb v = true) (absent : v.X ∉ e.2.2.code.support) : CodSolvable glb v := by
  simp only [codSolvableB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hHeads, hMeets⟩, hOcc⟩, hApart⟩ := h
  refine ⟨absent, ?_, atUniverses_of_B hOcc, codApart_of_sides v (sidesApart_of_B hApart), ?_⟩
  · intro h member
    have fit := List.all_eq_true.mp hHeads h member
    unfold fitPred at fit
    cases hk : choices.typing h with
    | none => rw [hk] at fit; cases fit
    | some k =>
        rw [hk] at fit
        exact ⟨k.1, k.2, of_decide_eq_true fit⟩
  · intro i misfit w hw
    have m := List.all_eq_true.mp hMeets i (List.mem_finRange i)
    unfold codMeetsPred at m
    rw [misfit] at m
    simp only [Bool.not_true, Bool.false_or] at m
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp m
    obtain ⟨_, w', hw', found⟩ := codTarget_some glb hg
    have same : w' = w := Tm.head.inj (hw'.symm.trans hw)
    rw [same] at found
    exact ⟨g, found⟩

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (declared : DeclaredTypesFormed S.R)

/-- **One step on a read equation**: delete, refute by the occurs check or a misfit head, narrow to greatest lower
bounds and solve, or stuck. -/
def stepFlexCod {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : FlexCod e)
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels storeRank (e :: rest) :=
  if hdel : e.2.2.code = .var v.X then
    .progress (deleteCodes e (v.annotation_left.trans v.annotation_right.symm) (v.side_left.trans hdel.symm) rest)
      (below_of_length (by
        show rest.length < (e :: rest).length
        simp))
  else if hocc : v.X ∈ e.2.2.code.support then
    .refuted (cod_occurs_refutes facts roots heads algebra rigid complete v hocc hdel rest)
  else match hmis : (codHeads e.2.2.code).find? (misfitPred choices v.u) with
    | some _ =>
        .refuted (cod_misfitHead_refutes facts roots heads algebra rigid complete v (List.mem_of_find?_eq_some hmis)
          (misfit_apart choices headTypingUnique (List.find?_some hmis)) rest)
    | none =>
        if hok : codSolvableB choices glb v = true then
          .progress (codNarrowSolveUpdate glb spec facts roots heads algebra rigid complete headTypingUnique declared v
              (codSolvable_of_B choices glb v hok hocc) rest)
            (below_of_length (by
              show ((frames S.levels).applyStore _ rest).length < (e :: rest).length
              simp [Frames.applyStore]))
        else .stuck

/-- **The round of the solver**: read the first equation, then step. -/
def flexCodRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels storeRank problem
  | _, [] => .stuck
  | _, e :: rest =>
      match hd : readFlexCod e with
      | some _ => stepFlexCod choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
          (viewOfCod hd) rest
      | none => .stuck

/-- **The tree's driver on flex–rigid stores with codomains.** -/
def flexCodSolver : ContextualDependentWorklist.Solver S.levels where
  rank := storeRank
  round := flexCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared

variable (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)

include total in
/-- **Progress by shape**: on a nonempty store of the fragment, the round is not stuck. -/
theorem flexCodRound_ne_stuck {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    (inside : InFlexCod choices problem) (nonempty : problem ≠ []) :
    flexCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared problem ≠
      .stuck := by
  cases problem with
  | nil => exact absurd rfl nonempty
  | cons e rest =>
      obtain ⟨v⟩ := inside.shapes e List.mem_cons_self
      have hd := readFlexCod_complete v
      simp only [flexCodRound]
      split
      · rename_i d hd'
        unfold stepFlexCod
        by_cases hdel : e.2.2.code = .var (viewOfCod hd').X
        · rw [dif_pos hdel]
          intro h; cases h
        · rw [dif_neg hdel]
          by_cases hocc : (viewOfCod hd').X ∈ e.2.2.code.support
          · rw [dif_pos hocc]
            intro h; cases h
          · rw [dif_neg hocc]
            split
            · intro h; cases h
            · rename_i hmis
              have ok : codSolvableB choices glb (viewOfCod hd') = true := by
                simp only [codSolvableB, Bool.and_eq_true]
                refine ⟨⟨⟨?_, ?_⟩, atUniversesB_of (inside.occurring e List.mem_cons_self)⟩,
                  sidesApartB_of (inside.apart e List.mem_cons_self)⟩
                · apply List.all_eq_true.mpr
                  intro h member
                  have typed := inside.typedHeads e List.mem_cons_self h member
                  have notMisfit := List.find?_eq_none.mp hmis h member
                  unfold fitPred
                  unfold misfitPred at notMisfit
                  cases hk : choices.typing h with
                  | none => rw [hk] at typed; cases typed
                  | some k =>
                      rw [hk] at notMisfit
                      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_not] at notMisfit
                      exact decide_eq_true notMisfit
                · apply List.all_eq_true.mpr
                  intro i _
                  unfold codMeetsPred
                  cases misfit : codMisfit (S := S) Γ.raw (viewOfCod hd').u e.2.2.code i with
                  | false => rfl
                  | true =>
                      obtain ⟨w, hw, uw⟩ := inside.occurring e List.mem_cons_self i (codMisfit_mem misfit)
                      obtain ⟨g, hg⟩ := total (viewOfCod hd').universe_u uw
                      rw [codTarget_of_misfit glb misfit hw hg]
                      rfl
              rw [dif_pos ok]
              intro h; cases h
      · rename_i hd'
        rw [hd] at hd'
        cases hd'

/-- **The rules keep the fragment.** -/
theorem flexCodRound_stable {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem}
    {smaller : ContextualDependentWorklist.Below (storeRank update.remaining) (storeRank problem)}
    (inside : InFlexCod choices problem)
    (progressed : flexCodRound choices glb spec facts roots heads algebra rigid complete headTypingUnique declared
      problem = .progress update smaller) :
    InFlexCod choices update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [flexCodRound] at progressed
      split at progressed
      · rename_i d hd
        unfold stepFlexCod at progressed
        by_cases hdel : e.2.2.code = .var (viewOfCod hd).X
        · rw [dif_pos hdel] at progressed
          cases progressed
          exact inFlexCod_delete inside
        · rw [dif_neg hdel] at progressed
          by_cases hocc : (viewOfCod hd).X ∈ e.2.2.code.support
          · rw [dif_pos hocc] at progressed
            cases progressed
          · rw [dif_neg hocc] at progressed
            split at progressed
            · cases progressed
            · by_cases hok : codSolvableB choices glb (viewOfCod hd) = true
              · rw [dif_pos hok] at progressed
                cases progressed
                exact inFlexCod_narrowSolve glb spec algebra inside (viewOfCod hd) _
              · rw [dif_neg hok] at progressed
                cases progressed
      · cases progressed

/-- **The fragment of the solver.** -/
def flexCodFragment :
    ContextualDependentWorklist.Fragment
      (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared) where
  holds := InFlexCod choices
  stable := fun inside progressed =>
    flexCodRound_stable choices glb spec facts roots heads algebra rigid complete headTypingUnique declared inside
      progressed
  decisive := fun inside nonempty =>
    flexCodRound_ne_stuck choices glb spec facts roots heads algebra rigid complete headTypingUnique declared total
      inside nonempty

include total in
/-- **Decided by shape, unknowns at codomains included**: on the fragment, the tree's driver with narrowing to greatest
lower bounds, solving and the two refutations reaches, at some budget and at every larger one, a principal answer or
a certified refutation. -/
theorem flexCod_decided {Θ : Context S.R} {original : EquationStore (TotalTerm Θ)}
    (inside : InFlexCod choices original) :
    ∃ fuel, ∀ larger, fuel ≤ larger →
      run (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared) original
          larger =
        run (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared)
          original fuel ∧
        ((∃ state finished,
              run (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared)
                  original larger = .solved state finished ∧
                (frames S.levels).Principal original state.answer) ∨
          (∃ absent,
            run (flexCodSolver choices glb spec facts roots heads algebra rigid complete headTypingUnique declared)
              original larger = .refuted absent)) :=
  (flexCodFragment choices glb spec facts roots heads algebra rigid complete headTypingUnique declared total).decided
    inside

end Solver

/-! ## Membership, decided -/

section Membership

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
variable (choices : ExecutableChecking.HeadChoices S.R)

/-- The left unknown of an equation, read off its left side. -/
def codLeftOf {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (Fin Θ.arity) := varOf e.1.2.code

/-- **Membership in the fragment with codomains, decided.** -/
def inFlexCodB {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) : Bool :=
  problem.all (fun e => atUniversesB (S := S) Θ.raw e.2.2.code && sidesApartB Θ.raw e.1.2.code e.2.2.code) &&
    problem.all (fun e => (readFlexCod e).isSome) &&
    problem.all (fun e => (codHeads e.2.2.code).all fun h => (choices.typing h).isSome) &&
    (problem.map codLeftOf).Nodup

theorem inFlexCod_of_B {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (h : inFlexCodB choices problem = true) : InFlexCod choices problem := by
  simp only [inFlexCodB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hLocal, hShapes⟩, hHeads⟩, hNodup⟩ := h
  refine ⟨fun e member => ?_, fun e member => ?_, fun e member => ?_, fun e member h hh => ?_, ?_⟩
  · have he := List.all_eq_true.mp hLocal e member
    simp only [Bool.and_eq_true] at he
    exact atUniverses_of_B he.1
  · have he := List.all_eq_true.mp hLocal e member
    simp only [Bool.and_eq_true] at he
    exact sidesApart_of_B he.2
  · have he := List.all_eq_true.mp hShapes e member
    cases hd : readFlexCod e with
    | none => rw [hd] at he; cases he
    | some d => exact ⟨viewOfCod hd⟩
  · exact List.all_eq_true.mp (List.all_eq_true.mp hHeads e member) h hh
  · have pairwise := List.pairwise_map.mp (List.nodup_iff_pairwise_ne.mp hNodup)
    refine pairwise.imp ?_
    intro e₁ e₂ different v₁ v₂ same
    apply different
    unfold codLeftOf
    rw [v₁.side_left, v₂.side_left, same]

end Membership

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
