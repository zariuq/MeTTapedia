import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRank

/-!
# Miller sides with wider domains, and the direction of a permutation chosen by domain order

A **wide Miller side** `λ ȳ. G y_b` applies an unknown `G : Π (z̄ : U_{p̄}). U_c` to distinct binders whose universes lie
**below** its domains, `U_{q_{b j}} ≤ U_{p_j}`, where a Miller side asks them to be equal. A glb join produces such sides:
it declares an unknown again at least upper bounds of two domains, and the other equations then apply it to binders of
the smaller ones.

* **Typing** (`spineRen_substMorW`, `sideRen_typedW`, `flexBody_value_typedW`): reading the binders of `p̄` as the locals
  `b` is not a typed renaming any more, but it is a typed substitution, each local being typed at the wider domain by
  cumulativity.
* **Reading** (`FlexDataW`, `readFlexW`, `WideView`, `readWide`): an equation whose left side is a Miller side of `X`
  (exact domains) and whose right side is a wide side of `Y`; every Miller side is wide (`FlexDataW.ofExact`).
* **The direction by domain order** (`wideSolveRound`): when every local of the wide side is among `X`'s and `Y`'s
  codomain lies below `X`'s, `X := λ x̄. Y x_σ`. It is exact: every solution's value of `X` is forced by the equation
  (the tree's `flexFlex_forced` asks only that the solved side have exact domains), and the answer is typed by the wide
  typing. It lowers the common rank: `X` no longer occurs, and its value mentions only `Y` (`weight_value_lt`).
* **A solver of the driver** with the common rank (`wideRound`, `wideSolver`): the direction by domain order on the
  first equation, when it is read so.

The equation `λ x y. F x y ≐ λ x y. Z y x` with `F : U0 → U1 → U0` and `Z : U1 → U1 → U0` is what a glb join leaves of
a Miller permutation; it is read by neither the Miller reader nor the family reader, and this round solves it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace Miller

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-! ## Typing with wider domains -/

section Typing

variable {S : Setting Head L}

/-- **The renaming of a spine is a typed substitution** when the variables it reaches are typed at the binders'
universes, by cumulativity if need be. -/
theorem spineRen_substMorW : ∀ {n m : Nat} {Γ : Ctx Head n} {Γ' : Ctx Head m} (ps : List Head) (ρ : Ren n m)
    (img : Fin ps.length → Fin m), SubstMor S.R Γ Γ' (renSub ρ) →
      (∀ j, Typed S.R Γ' (.var (img j)) (.head (ps.get j))) → SubstMor S.R (ctx Γ ps) Γ' (renSub (spineRen ps ρ img))
  | _, _, _, _, [], _, _, typed, _ => typed
  | _, m, Γ, Γ', p :: ps, ρ, img, typed, imgs => by
      refine spineRen_substMorW (Γ := .snoc Γ (.head p)) ps (Fin.cases (motive := fun _ => Fin m) (img 0) ρ)
        (fun j => img j.succ) ?_ (fun j => imgs j.succ)
      intro index
      cases index using Fin.cases with
      | zero =>
          show Typed S.R Γ' (.var (img 0)) (Presentation.subst (renSub _) (Presentation.rename wk (.head p)))
          exact imgs 0
      | succ prior =>
          show Typed S.R Γ' (.var (ρ prior))
            (Presentation.subst (renSub _) (Presentation.rename wk (Ctx.lookup Γ prior)))
          rw [subst_renSub, rename_comp]
          have inner := typed prior
          rw [subst_renSub] at inner
          exact inner

/-- **A body read at locals of smaller universes is typed**: the locals are typed at the wider domains. -/
theorem sideRen_typedW {n : Nat} {Γ : Ctx Head n} (qs ps : List Head) (img : Fin ps.length → Fin qs.length)
    (wide : ∀ j, S.R.cumulative (qs.get (img j)) (ps.get j)) {t : Tm Head (arity n ps)} {c : Head}
    (typed : Typed S.R (ctx Γ ps) t (.head c)) :
    Typed S.R (ctx Γ qs) (Presentation.rename (sideRen qs ps img) t) (.head c) := by
  have mor : SubstMor S.R (ctx Γ ps) (ctx Γ qs) (renSub (sideRen qs ps img)) :=
    spineRen_substMorW ps (shift qs) (fun j => loc qs (img j))
      (fun index => by
        show Typed S.R (ctx Γ qs) (.var (shift qs index))
          (Presentation.subst (renSub (shift qs)) (Ctx.lookup Γ index))
        rw [subst_renSub, ← shift_ctxRen Γ qs index]
        exact Derivable.var _)
      (fun j => local_typed Γ qs (img j) (wide j))
  have moved := typed.substitute mor
  rw [subst_renSub] at moved
  exact moved

/-- The instantiated body of a wide side, at the annotation's codomain. -/
theorem flexBody_value_typedW {Θ Δ : Context S.R} (f : Δ ⟶ Θ) (qs : List Head) {F : Fin Θ.arity} {ps : List Head}
    {c d : Head} (img : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Θ.raw F = famCode ps c)
    (wide : ∀ j, S.R.cumulative (qs.get (img j)) (ps.get j)) (below : S.R.cumulative c d) :
    Typed S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution F))) (.head d) :=
  Derivable.cumul (sideRen_typedW qs ps img wide (value_opened_typed f declared)) below

end Typing

/-! ## Reading wide sides -/

section Reading

variable [DecidableEq Head]

/-- **A wide Miller side read from a code**: an unknown applied to distinct binders whose universes lie below its
domains. -/
structure FlexDataW (R : Rules Head) {N : Nat} (Γ : Ctx Head N) (qs : List Head) (code : Tm Head N) where
  unknown : Fin N
  ps : List Head
  c : Head
  img : Fin ps.length → Fin qs.length
  side : code = flexSide qs ps unknown img
  declared : Ctx.lookup Γ unknown = famCode ps c
  injective : Function.Injective img
  wide : ∀ j, R.cumulative (qs.get (img j)) (ps.get j)

variable {S : Setting Head L}

/-- **Every Miller side is wide**: equal universes lie below each other. -/
def FlexDataW.ofExact {N : Nat} {Γ : Ctx Head N} {qs : List Head} {code : Tm Head N} (data : FlexData Γ qs code)
    (universes : AllUniverses S.R qs) : FlexDataW S.R Γ qs code where
  unknown := data.unknown
  ps := data.ps
  c := data.c
  img := data.img
  side := data.side
  declared := data.declared
  injective := data.injective
  wide := fun j => by
    rw [data.domains j]
    exact S.levels.cumulative_refl (universes _ (List.get_mem qs (data.img j)))

variable [DecidableRel S.R.cumulative]

/-- The final check of a wide side, once its unknown, family and arguments are read. -/
def checkFlexW {N : Nat} (Γ : Ctx Head N) (qs : List Head) (code : Tm Head N) (F : Fin N) (ps : List Head)
    (c : Head) (ls : List (Fin qs.length)) : Option (FlexDataW S.R Γ qs code) :=
  if hlen : ls.length = ps.length then
    if h : code = flexSide qs ps F (fun j => ls.get (Fin.cast hlen.symm j)) ∧ Ctx.lookup Γ F = famCode ps c ∧
        ls.Nodup ∧ (∀ j : Fin ps.length, S.R.cumulative (qs.get (ls.get (Fin.cast hlen.symm j))) (ps.get j)) then
      some ⟨F, ps, c, fun j => ls.get (Fin.cast hlen.symm j), h.1, h.2.1, injective_of_nodup hlen h.2.2.1, h.2.2.2⟩
    else none
  else none

/-- **Read a wide side.** -/
def readFlexW {N : Nat} (Γ : Ctx Head N) (qs : List Head) (code : Tm Head N) : Option (FlexDataW S.R Γ qs code) :=
  match unlams qs code with
  | none => none
  | some body =>
      match readUnknown qs (unapps body).1 with
      | none => none
      | some F =>
          match readFam (Ctx.lookup Γ F) with
          | none => none
          | some r =>
              match (unapps body).2.mapM (readLoc qs) with
              | none => none
              | some ls => checkFlexW (S := S) Γ qs code F r.1 r.2 ls

end Reading

/-! ## Equations between a Miller side and a wide side -/

section Views

variable [DecidableEq Head] {S : Setting Head L}

/-- **An equation between a Miller side and a wide side**, at `Π ȳ : U_{qs}. U_d`: the left side's unknown has exactly
the binders' domains, the right side's unknown wider ones. -/
structure WideView {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Type where
  qs : List Head
  d : Head
  annotation_left : e.1.1.code = famCode qs d
  annotation_right : e.2.1.code = famCode qs d
  universes : AllUniverses S.R qs
  universe_d : S.R.isUniverse d
  exact : FlexData Θ.raw qs e.1.2.code
  below : S.R.cumulative exact.c d
  wide : FlexDataW S.R Θ.raw qs e.2.2.code
  wideBelow : S.R.cumulative wide.c d

variable [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **Read an equation between a Miller side and a wide side.** -/
def readWide {Θ : Context S.R} (e : Equation (TotalTerm Θ)) : Option (WideView (S := S) e) :=
  match readFam e.1.1.code with
  | none => none
  | some r =>
      if h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2 then
        match readFlex Θ.raw r.1 e.1.2.code, readFlexW (S := S) Θ.raw r.1 e.2.2.code with
        | some exact, some wide =>
            if hb : S.R.cumulative exact.c r.2 ∧ S.R.cumulative wide.c r.2 then
              some ⟨r.1, r.2, h.1, h.2.1, h.2.2.1, h.2.2.2, exact, hb.1, wide, hb.2⟩
            else none
        | _, _ => none
      else none

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- **The opened equation** at a solution: the wide side's instance equals the Miller side's. -/
theorem opensW {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (v : WideView (S := S) e) :
    ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs)
        (Presentation.rename (sideRen v.qs v.wide.ps v.wide.img) (opened v.wide.ps (f.substitution v.wide.unknown)))
        (Presentation.rename (sideRen v.qs v.exact.ps v.exact.img) (opened v.exact.ps (f.substitution v.exact.unknown)))
        (.head v.d) := by
  intro Δ f solved
  have tl : Typed S.R (ctx Δ.raw v.qs)
      (Presentation.subst (liftSubs v.qs f.substitution) (flexBody v.qs v.exact.ps v.exact.unknown v.exact.img))
      (.head v.d) := by
    rw [subst_flexBody_opened]
    exact flexBody_value_typed f v.qs v.exact.img v.exact.declared v.exact.domains v.below
  have tr : Typed S.R (ctx Δ.raw v.qs)
      (Presentation.subst (liftSubs v.qs f.substitution) (flexBody v.qs v.wide.ps v.wide.unknown v.wide.img))
      (.head v.d) := by
    rw [subst_flexBody_opened]
    exact flexBody_value_typedW f v.qs v.wide.img v.wide.declared v.wide.wide v.wideBelow
  have equal := solves_opened v.annotation_left v.exact.side v.wide.side v.universes v.universe_d f tl tr
    (solved e List.mem_cons_self)
  rw [subst_flexBody_opened, subst_flexBody_opened] at equal
  exact equal.symm

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
/-- The wide side's unknown occurs in the store. -/
theorem occurs_wide {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {qs : List Head} (data : FlexDataW S.R Θ.raw qs e.2.2.code) : data.unknown ∈ occ (e :: rest) := by
  have h := congrArg Tm.support data.side
  rw [support_flexSide] at h
  apply mem_occ.mpr
  refine ⟨e, List.mem_cons_self, Or.inr ?_⟩
  rw [h]
  exact Finset.mem_singleton_self _

end Views

/-! ## Re-reading side by side -/

section RereadW

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

/-- **Re-read one side on its own**: a Miller side of the answer's unknown is replaced by its β-contracted instance,
whatever the other side of its equation; every other side is instantiated. -/
def rereadSideW {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head} {d : Head}
    (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) : TotalTerm Θ' :=
  match readSide (S := S) Θ.raw qs d Y.2.code with
  | some view => rereadSide A Y annotation universes hd view
  | none => (frames S.levels).act σ Y

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem rereadSideW_E {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head}
    {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) :
    (frames S.levels).E ((frames S.levels).act σ Y) (rereadSideW A Y annotation universes hd) := by
  unfold rereadSideW
  split
  · exact rereadSide_E A Y annotation universes hd _
  · exact ((frames S.levels).equivalence Θ').refl _

/-- **Re-read one equation side by side.** -/
def rereadEqW {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    Equation (TotalTerm Θ') :=
  match readFam e.1.1.code with
  | none => ((frames S.levels).act σ e.1, (frames S.levels).act σ e.2)
  | some r =>
      if h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2 then
        (rereadSideW A e.1 h.1 h.2.2.1 h.2.2.2, rereadSideW A e.2 h.2.1 h.2.2.1 h.2.2.2)
      else ((frames S.levels).act σ e.1, (frames S.levels).act σ e.2)

theorem rereadEqW_E {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    (frames S.levels).E ((frames S.levels).act σ e.1) (rereadEqW A e).1 ∧
      (frames S.levels).E ((frames S.levels).act σ e.2) (rereadEqW A e).2 := by
  unfold rereadEqW
  split
  · exact ⟨((frames S.levels).equivalence Θ').refl _, ((frames S.levels).equivalence Θ').refl _⟩
  · split
    · exact ⟨rereadSideW_E A e.1 _ _ _, rereadSideW_E A e.2 _ _ _⟩
    · exact ⟨((frames S.levels).equivalence Θ').refl _, ((frames S.levels).equivalence Θ').refl _⟩

/-- **The store re-read side by side.** -/
def rereadStoreW {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (problem : EquationStore (TotalTerm Θ)) :
    EquationStore (TotalTerm Θ') :=
  problem.map (rereadEqW A)

/-- **The store re-read side by side has the solutions of the instantiated store.** -/
theorem rereadStoreW_models {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ)
    (problem : EquationStore (TotalTerm Θ)) {Δ : Context S.R} (g : Δ ⟶ Θ') :
    (frames S.levels).Models g (rereadStoreW A problem) ↔
      (frames S.levels).Models g ((frames S.levels).applyStore σ problem) := by
  have equivalence := (frames S.levels).equivalence Δ
  constructor
  · intro solved e member
    obtain ⟨e₀, member₀, rfl⟩ := List.mem_map.mp member
    have sides := rereadEqW_E A e₀
    have read := solved (rereadEqW A e₀) (List.mem_map.mpr ⟨e₀, member₀, rfl⟩)
    have one := (frames S.levels).preserves g sides.1
    have two := (frames S.levels).preserves g sides.2
    exact equivalence.trans one (equivalence.trans read (equivalence.symm two))
  · intro solved e member
    obtain ⟨e₀, member₀, rfl⟩ := List.mem_map.mp member
    have sides := rereadEqW_E A e₀
    have read := solved ((frames S.levels).act σ e₀.1, (frames S.levels).act σ e₀.2)
      (List.mem_map.mpr ⟨e₀, member₀, rfl⟩)
    have one := (frames S.levels).preserves g sides.1
    have two := (frames S.levels).preserves g sides.2
    exact equivalence.trans (equivalence.symm one) (equivalence.trans read two)

/-- **Re-reading side by side keeps only the answer's own unknowns in `X`'s place.** -/
theorem occ_rereadW {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {ps' : List Head} {c' : Head}
    {universes' : AllUniverses S.R ps'} {hc' : S.R.isUniverse c'}
    (σ : redecl Θ families X ps' c' universes' hc' ⟶ Θ) (A : AnswerData σ)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (store : EquationStore (TotalTerm Θ)) :
    occ (rereadStoreW A store) ⊆ (occ (Θ := Θ) store).erase X ∪ (lams A.psX A.val).support := by
  intro v h
  obtain ⟨e', member, hv⟩ := mem_occ.mp h
  obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp member
  have side : ∀ (code : Tm Head Θ.arity), code.support ⊆ (occ store) →
      (Presentation.subst σ.substitution code).support ⊆ (occ store).erase X ∪ (lams A.psX A.val).support := by
    intro code within w hw
    rw [hsub] at hw
    have := support_answer X A.psX A.val code hw
    rcases Finset.mem_union.mp this with h₁ | h₂
    · obtain ⟨ne, hw'⟩ := Finset.mem_erase.mp h₁
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne, within hw'⟩)
    · exact Finset.mem_union_right _ h₂
  have left : e.1.2.code.support ⊆ occ store := fun w hw => mem_occ.mpr ⟨e, eMember, .inl hw⟩
  have right : e.2.2.code.support ⊆ occ store := fun w hw => mem_occ.mpr ⟨e, eMember, .inr hw⟩
  have generic : ∀ (Y : TotalTerm Θ) {qs : List Head} {d : Head} (annotation : Y.1.code = famCode qs d)
      (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d),
      Y.2.code.support ⊆ occ store →
        (rereadSideW A Y annotation universes hd).2.code.support ⊆
          (occ store).erase X ∪ (lams A.psX A.val).support := by
    intro Y qs d annotation universes hd within
    unfold rereadSideW
    split
    · rename_i view _
      rcases rereadSide_code A Y annotation universes hd view with same | ⟨img, same⟩
      · rw [same]
        exact side _ within
      · rw [same]
        exact (support_reread qs A.psX img A.val).trans Finset.subset_union_right
    · exact side _ within
  unfold rereadEqW at hv
  cases hr : readFam e.1.1.code with
  | none =>
      rw [hr] at hv
      rcases hv with hv | hv
      · exact side _ left hv
      · exact side _ right hv
  | some r =>
      rw [hr] at hv
      dsimp only at hv
      by_cases h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2
      · rw [dif_pos h] at hv
        rcases hv with hv | hv
        · exact generic e.1 _ _ _ left hv
        · exact generic e.2 _ _ _ right hv
      · rw [dif_neg h] at hv
        rcases hv with hv | hv
        · exact side _ left hv
        · exact side _ right hv

/-- **A value rule re-read side by side lowers the weight**: `X` occurs, and the answer's value mentions only other
occurring unknowns. -/
theorem weight_value_ltW {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {psX : List Head} {cX : Head}
    {universesX : AllUniverses S.R psX} {hcX : S.R.isUniverse cX}
    (σ : redecl Θ families X psX cX universesX hcX ⟶ Θ) (A : AnswerData σ)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (store : EquationStore (TotalTerm Θ)) (occurs : X ∈ occ store)
    (valOcc : (lams A.psX A.val).support ⊆ (occ (Θ := Θ) store).erase X) :
    weight (rereadStoreW A store) < weight store := by
  have sub : occ (rereadStoreW A store) ⊆ (occ (Θ := Θ) store).erase X := by
    intro v h
    rcases Finset.mem_union.mp (occ_rereadW σ A hsub store h) with h | h
    · exact h
    · exact valOcc h
  have arities : ∀ i ∈ (occ (Θ := Θ) store).erase X,
      famArity (Ctx.lookup (setFamAt Θ.raw X psX cX) i) = famArity (Ctx.lookup Θ.raw i) := by
    intro i member
    rw [lookup_setFamAt_ne Θ.raw X i psX cX (Finset.mem_erase.mp member).1]
  unfold weight
  calc ∑ i ∈ occ (rereadStoreW A store), (famArity (Ctx.lookup (setFamAt Θ.raw X psX cX) i) + 1)
      ≤ ∑ i ∈ (occ (Θ := Θ) store).erase X, (famArity (Ctx.lookup (setFamAt Θ.raw X psX cX) i) + 1) :=
        Finset.sum_le_sum_of_subset sub
    _ = ∑ i ∈ (occ (Θ := Θ) store).erase X, (famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.sum_congr rfl fun i member => by rw [arities i member]
    _ < (famArity (Ctx.lookup Θ.raw X) + 1) +
          ∑ i ∈ (occ (Θ := Θ) store).erase X, (famArity (Ctx.lookup Θ.raw i) + 1) := by
        omega
    _ = ∑ i ∈ occ (Θ := Θ) store, (famArity (Ctx.lookup Θ.raw i) + 1) :=
        Finset.add_sum_erase (occ (Θ := Θ) store) (fun i => famArity (Ctx.lookup Θ.raw i) + 1) occurs

end RereadW

/-! ## The direction by domain order -/

section Round

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (inh : Inhabitants S.R)

include facts roots heads algebra rigid complete in
/-- **The value rule re-read side by side**: `X := λ x̄. val`, for a store whose every solution's value of `X` opens to
`val`; every Miller side of `X` is β-contracted, whatever the other side of its equation. -/
def valueUpdateW {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX d : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (hd : S.R.isUniverse d) (below : S.R.cumulative cX d) (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) val (.head cX))
    (forced : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw psX) (opened psX (f.substitution X))
        (Presentation.subst (liftSubs psX f.substitution) val) (.head d)) : Update S.levels (e :: rest) :=
  replaceUpdate (valueHom families X declared universesX hcX val typed)
    (rereadStoreW (valueData families X declared universesX hcX val typed) (e :: rest))
    (fun g => rereadStoreW_models _ (e :: rest) g)
    (fun f solved => ⟨sameHom Θ families X declared universesX hcX f,
      factor_of_opened facts roots heads algebra rigid complete X declared universesX hcX hd below
        (valueHom families X declared universesX hcX val typed) val
        (answerSub_self X psX val) typed f (sameHom Θ families X declared universesX hcX f)
        (fun i ne => by
          show Presentation.subst f.substitution (answerSub X psX val i) = f.substitution i
          rw [answerSub_ne X psX val ne]
          rfl)
        (forced f solved)⟩)

include facts roots heads algebra rigid complete inh in
/-- **The direction by domain order**: `X := λ x̄. Y x_σ`, for `λ ȳ. Y y_b ≐ λ ȳ. X y_a` with `X`'s domains exactly
the binders' and `Y`'s wider, once every local of `b` is among `a` and `Y`'s codomain lies below `X`'s. Exact, and it
lowers the common rank. -/
def wideSolveRound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) {qs : List Head} {d : Head} (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    {X Y : Fin Θ.arity} {psX psY : List Head} {cX cY : Head} (imgX : Fin psX.length → Fin qs.length)
    (imgY : Fin psY.length → Fin qs.length) (declX : Ctx.lookup Θ.raw X = famCode psX cX)
    (declY : Ctx.lookup Θ.raw Y = famCode psY cY) (injX : Function.Injective imgX)
    (domX : ∀ j, psX.get j = qs.get (imgX j)) (wideY : ∀ j, S.R.cumulative (qs.get (imgY j)) (psY.get j))
    (belowX : S.R.cumulative cX d) (ne : Y ≠ X) (cover : ∀ i, ∃ j, imgX j = imgY i)
    (codomains : S.R.cumulative cY cX) (occX : X ∈ occ (e :: rest)) (occY : Y ∈ occ (e :: rest))
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psY imgY) (opened psY (f.substitution Y)))
        (Presentation.rename (sideRen qs psX imgX) (opened psX (f.substitution X))) (.head d)) :
    Round S.levels commonRank (e :: rest) :=
  have wideσ : ∀ i, S.R.cumulative (psX.get (solveMap imgX imgY cover i)) (psY.get i) := fun i => by
    rw [domX (solveMap imgX imgY cover i), solveMap_spec imgX imgY cover i]
    exact wideY i
  have typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) (flexBody psX psY Y (solveMap imgX imgY cover))
      (.head cX) := by
    have tY : Typed S.R (setFamAt Θ.raw X psX cX) (.var Y) (famCode psY cY) := by
      have v := Derivable.var (R := S.R) (Γ := setFamAt Θ.raw X psX cX) Y
      rw [lookup_setFamAt_ne Θ.raw X Y psX cX ne, declY] at v
      exact v
    rw [flexBody_eq]
    exact Derivable.cumul (sideRen_typedW psX psY _ wideσ (opened_typed psY tY)) codomains
  .progress
    (valueUpdateW facts roots heads algebra rigid complete rest families X declX
      (famFacts families declX).1 (famFacts families declX).2 hd belowX
      (flexBody psX psY Y (solveMap imgX imgY cover)) typed
      (fun {Δ} f solved => by
        have forced := flexFlex_forced inh f qs imgY imgX universes domX injX (opens f solved)
        rw [subst_flexBody_opened, rename_opened]
        have args : ((List.finRange psY.length).map fun i => pullImg (n := Δ.arity) inh qs psX imgX (imgY i)) =
            spineArgs psY fun i => loc psX (solveMap imgX imgY cover i) := by
          unfold spineArgs
          congr 1
          funext i
          rw [← solveMap_spec imgX imgY cover i, pullImg_img inh injX]
        rw [args] at forced
        exact forced.symm))
    (Prod.Lex.left _ _ (weight_value_ltW _ (valueData families X declX _ _ _ typed) (fun _ => rfl) (e :: rest) occX
      (by
        show (flexSide psX psY Y (solveMap imgX imgY cover)).support ⊆ _
        rw [support_flexSide]
        intro v hv
        rw [Finset.mem_singleton.mp hv]
        exact Finset.mem_erase.mpr ⟨ne, occY⟩)))

include facts roots heads algebra rigid complete inh in
/-- **The round of the wide solver**: an equation whose two sides are the same code is deleted; on a telescope of
families, the direction by domain order on the first equation when it is read as a Miller side against a wide side
and its conditions hold; otherwise stuck. -/
def wideRound : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels commonRank problem
  | _, [] => .stuck
  | Γ, e :: rest =>
      if same : e.1.1.code = e.2.1.code ∧ e.1.2.code = e.2.2.code then
        .progress (deleteSame same.1 same.2 rest) (commonRank_drop e rest)
      else if hf : Families Γ then
        match readWide (S := S) e with
        | some v =>
            if ne : v.wide.unknown ≠ v.exact.unknown then
              if cover : ∀ i, ∃ j, v.exact.img j = v.wide.img i then
                if codomains : S.R.cumulative v.wide.c v.exact.c then
                  wideSolveRound facts roots heads algebra rigid complete inh rest hf v.universes v.universe_d
                    v.exact.img v.wide.img v.exact.declared v.wide.declared v.exact.injective v.exact.domains
                    v.wide.wide v.below ne cover codomains (occurs_side v.exact (.inl rfl)) (occurs_wide v.wide)
                    (opensW v)
                else .stuck
              else .stuck
            else .stuck
        | none => .stuck
      else .stuck

/-- **The wide solver**: one rank, the common rank. -/
def wideSolver : ContextualDependentWorklist.Solver S.levels where
  rank := commonRank
  round := wideRound facts roots heads algebra rigid complete inh

end Round

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
