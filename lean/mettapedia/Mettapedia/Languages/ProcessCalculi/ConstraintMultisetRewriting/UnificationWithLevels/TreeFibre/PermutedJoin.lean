import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.WideMix

/-!
# The glb join under a permutation

Two unknowns with wider domains each, related by a permutation, `λ x̄. F x̄ ≐ λ x̄. G x_b`, are joined after `G` is
**declared again with its arguments permuted** (`G := λ z̄. G' z_K`, `K` the inverse of `b`): pruning with every
position kept is exact for every value (`pruned_all`), and the equation then reads as a family equation.

* **β along a spine of variables typed by cumulativity** (`apps_congrW`, `beta_appsW`): the arguments lie in smaller
  universes than the domains.
* **Re-reading wide sides** (`reread_equalW`, `rereadSideP`, `rereadEqP`, `rereadStoreP`): a side `λ ȳ. X y_a` of the
  answer's unknown, its domains equal to or above the binders', is replaced by its β-contracted instance.
* **The permutation** (`permuteUpdate`): exact, and it does not raise the weight (`weight_permute_le`).
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

/-! ## β along a spine of variables typed by cumulativity -/

section WideBeta

variable {S : Setting Head L}

/-- Applications along a spine of variables typed at the domains, by cumulativity if need be, respect equality. -/
theorem apps_congrW : ∀ {m : Nat} {Γ' : Ctx Head m} (ps : List Head) {d : Head} {f f' : Tm Head m}
    (img : Fin ps.length → Fin m), (∀ j, Typed S.R Γ' (.var (img j)) (.head (ps.get j))) →
      Equal S.R Γ' f f' (famCode ps d) → Equal S.R Γ' (apps f (spineArgs ps img)) (apps f' (spineArgs ps img)) (.head d)
  | _, _, [], _, _, _, _, _, equal => equal
  | _, Γ', p :: ps, d, f, f', img, typed, equal => by
      rw [spineArgs_cons]
      apply apps_congrW ps (fun j => img j.succ) (fun j => typed j.succ)
      have step := Derivable.appCong (equal : Equal S.R Γ' f f' (.pi (.head p) (famCode ps d)))
        (Derivable.refl (typed 0))
      simpa only [inst0, famCode_subst] using step

/-- A renaming that is a typed substitution types the renamed term. -/
theorem typed_rename_of_substMor {n m : Nat} {Γ : Ctx Head n} {Γ' : Ctx Head m} {ρ : Ren n m}
    (mor : SubstMor S.R Γ Γ' (renSub ρ)) {t A : Tm Head n} (typed : Typed S.R Γ t A) :
    Typed S.R Γ' (Presentation.rename ρ t) (Presentation.rename ρ A) := by
  have moved := typed.substitute mor
  rw [subst_renSub, subst_renSub] at moved
  exact moved

/-- **β along a spine of variables typed by cumulativity.** -/
theorem beta_appsW : ∀ {n m : Nat} {Γ : Ctx Head n} {Γ' : Ctx Head m} (ps : List Head) {d : Head}
    {B : Tm Head (arity n ps)} (ρ : Ren n m) (img : Fin ps.length → Fin m),
    CtxFormed S.R Γ → CtxFormed S.R Γ' → AllUniverses S.R ps → S.R.isUniverse d → SubstMor S.R Γ Γ' (renSub ρ) →
      (∀ j, Typed S.R Γ' (.var (img j)) (.head (ps.get j))) → Typed S.R (ctx Γ ps) B (.head d) →
      Equal S.R Γ' (apps (Presentation.rename ρ (lams ps B)) (spineArgs ps img))
        (Presentation.rename (spineRen ps ρ img) B) (.head d)
  | _, _, Γ, _, [], d, B, _, _, _, _, _, _, compatible, _, typed => by
      have typed' : Typed S.R Γ B (.head d) := typed
      exact .refl (typed_rename_of_substMor compatible typed')
  | _, m, Γ, Γ', p :: ps, d, B, ρ, img, formed, formed', universes, hd, compatible, imgs, typed => by
      have formedP : CtxFormed S.R (.snoc Γ (.head p)) := formed.snoc (IsType.head_of_universe universes.head)
      have compatible' : SubstMor S.R (.snoc Γ (.head p)) Γ'
          (renSub (Fin.cases (motive := fun _ => Fin m) (img 0) ρ)) := by
        intro index
        cases index using Fin.cases with
        | zero =>
            show Typed S.R Γ' (.var (img 0)) (Presentation.subst (renSub _) (Presentation.rename wk (.head p)))
            exact imgs 0
        | succ prior =>
            show Typed S.R Γ' (.var (ρ prior))
              (Presentation.subst (renSub _) (Presentation.rename wk (Ctx.lookup Γ prior)))
            rw [subst_renSub, rename_comp]
            have inner := compatible prior
            rw [subst_renSub] at inner
            exact inner
      have ih := beta_appsW ps (Fin.cases (motive := fun _ => Fin m) (img 0) ρ) (fun j => img j.succ) formedP formed'
        universes.tail hd compatible' (fun j => imgs j.succ) typed
      have tBody := lams_typed ps formedP universes.tail hd typed
      have tLifted : Typed S.R (.snoc Γ' (.head p)) (Presentation.rename (liftRen ρ) (lams ps B)) (famCode ps d) := by
        have moved := tBody.substitute (compatible.lift (.head p))
        simp only [liftSub_renSub, subst_renSub, famCode_subst] at moved
        exact moved
      obtain ⟨u, hu, tPi⟩ := famCode_isType (p :: ps) universes hd formed'
      have tPi' : Typed S.R Γ' (.pi (.head p) (famCode ps d)) (.head u) := tPi
      have beta := Derivable.betaPi tPi' hu tLifted (imgs 0)
      rw [inst0_rename_liftRen] at beta
      have beta' : Equal S.R Γ' (.app (.lam (Presentation.rename (liftRen ρ) (lams ps B))) (.var (img 0)))
          (Presentation.rename (Fin.cases (motive := fun _ => Fin m) (img 0) ρ) (lams ps B)) (famCode ps d) := by
        simpa only [inst0, famCode_subst] using beta
      have spine := apps_congrW ps (fun j => img j.succ) (fun j => imgs j.succ) beta'
      rw [spineArgs_cons]
      exact spine.trans ih

/-- The weakening past the binders, as a typed substitution. -/
theorem shift_substMor {n : Nat} (Γ : Ctx Head n) (qs : List Head) : SubstMor S.R Γ (ctx Γ qs) (renSub (shift qs)) :=
  fun index => by
    show Typed S.R (ctx Γ qs) (.var (shift qs index)) (Presentation.subst (renSub (shift qs)) (Ctx.lookup Γ index))
    rw [subst_renSub, ← shift_ctxRen Γ qs index]
    exact Derivable.var _

/-- **β re-reading of a wide side of `X`**: the instantiated side `λ ȳ. (λ x̄. val) y_a`, the binders `y_a` in
universes below `X`'s domains, equals `λ ȳ. val[x̄ := y_a]`. -/
theorem reread_equalW {Θ Θ' : Context S.R} (σ : Θ' ⟶ Θ) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (val : Tm Head (arity Θ'.arity psX)) (hσ : σ.substitution X = lams psX val)
    (typed : Typed S.R (ctx Θ'.raw psX) val (.head cX)) (universesX : AllUniverses S.R psX)
    (qs : List Head) {d : Head} (img : Fin psX.length → Fin qs.length) (universes : AllUniverses S.R qs)
    (hd : S.R.isUniverse d) (wide : ∀ j, S.R.cumulative (qs.get (img j)) (psX.get j)) (below : S.R.cumulative cX d)
    (hcX : S.R.isUniverse cX) :
    Equal S.R Θ'.raw (Presentation.subst σ.substitution (flexSide qs psX X img))
      (lams qs (Presentation.rename (sideRen qs psX img) val)) (famCode qs d) := by
  rw [subst_flexSide, hσ]
  have beta := beta_appsW (S := S) (Γ := Θ'.raw) (Γ' := ctx Θ'.raw qs) psX (shift qs) (fun j => loc qs (img j))
    Θ'.formed (ctx_formed qs Θ'.formed universes) universesX hcX (shift_substMor Θ'.raw qs)
    (fun j => local_typed Θ'.raw qs (img j) (wide j)) typed
  have beta' := Derivable.cumulEq beta below
  obtain ⟨tl, tr⟩ := Equal.typed beta' (ctx_formed qs Θ'.formed universes)
  exact (lams_equal_iff qs Θ'.formed universes hd tl tr).mpr beta'

theorem wide_cast {qs ps psX : List Head} {img : Fin ps.length → Fin qs.length} (same : ps = psX)
    (wide : ∀ j, S.R.cumulative (qs.get (img j)) (ps.get j)) :
    ∀ j, S.R.cumulative (qs.get (castImg img same j)) (psX.get j) := by
  subst same
  exact wide

end WideBeta

/-! ## Re-reading wide sides -/

section RereadP

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

/-- **Re-read one side, exact or wide**: a side of the answer's unknown whose domains equal or lie above the binders'
is replaced by its β-contracted instance; every other side is instantiated. -/
def rereadSideP {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head} {d : Head}
    (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) : TotalTerm Θ' :=
  match readFlexW (S := S) Θ.raw qs Y.2.code with
  | some data =>
      if h : data.unknown = A.X ∧ data.ps = A.psX ∧ S.R.cumulative data.c d then
        replaceCode ((frames S.levels).act σ Y)
          (lams qs (Presentation.rename (sideRen qs A.psX (castImg data.img h.2.1)) A.val)) (by
            have hc : data.c = A.cX := by
              have decl := data.declared
              rw [h.1, A.declared] at decl
              exact (famCode_inj decl).2.symm
            have equal := reread_equalW σ A.X A.val A.answer_self A.typed A.universesX qs (castImg data.img h.2.1)
              universes hd (wide_cast h.2.1 data.wide) (hc ▸ h.2.2) A.universe_cX
            have hside : Y.2.code = flexSide qs A.psX A.X (castImg data.img h.2.1) :=
              data.side.trans ((flexSide_cast data.unknown data.img h.2.1).trans
                (congrArg (fun F => flexSide qs A.psX F (castImg data.img h.2.1)) h.1))
            have e1 : Presentation.subst σ.substitution Y.2.code =
                Presentation.subst σ.substitution (flexSide qs A.psX A.X (castImg data.img h.2.1)) :=
              congrArg _ hside
            have e2 : Presentation.subst σ.substitution Y.1.code = famCode qs d := by
              rw [annotation, famCode_subst]
            change Equal S.R Θ'.raw (Presentation.subst σ.substitution Y.2.code) _
              (Presentation.subst σ.substitution Y.1.code)
            rw [e1, e2]
            exact equal)
      else (frames S.levels).act σ Y
  | none => (frames S.levels).act σ Y

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem rereadSideP_E {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head}
    {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) :
    (frames S.levels).E ((frames S.levels).act σ Y) (rereadSideP A Y annotation universes hd) := by
  unfold rereadSideP
  split
  · split
    · exact replaceCode_E _ _ _
    · exact ((frames S.levels).equivalence Θ').refl _
  · exact ((frames S.levels).equivalence Θ').refl _

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem rereadSideP_code {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ) {qs : List Head}
    {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) :
    (rereadSideP A Y annotation universes hd).2.code = Presentation.subst σ.substitution Y.2.code ∨
      ∃ img : Fin A.psX.length → Fin qs.length,
        (rereadSideP A Y annotation universes hd).2.code = lams qs (Presentation.rename (sideRen qs A.psX img) A.val) := by
  unfold rereadSideP
  cases hr : readFlexW (S := S) Θ.raw qs Y.2.code with
  | none => exact .inl rfl
  | some data =>
      dsimp only
      by_cases h : data.unknown = A.X ∧ data.ps = A.psX ∧ S.R.cumulative data.c d
      · rw [dif_pos h]
        exact .inr ⟨_, rfl⟩
      · rw [dif_neg h]
        exact .inl rfl

/-- **Re-read one equation, exact and wide sides.** -/
def rereadEqP {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    Equation (TotalTerm Θ') :=
  match readFam e.1.1.code with
  | none => ((frames S.levels).act σ e.1, (frames S.levels).act σ e.2)
  | some r =>
      if h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2 then
        (rereadSideP A e.1 h.1 h.2.2.1 h.2.2.2, rereadSideP A e.2 h.2.1 h.2.2.1 h.2.2.2)
      else ((frames S.levels).act σ e.1, (frames S.levels).act σ e.2)

theorem rereadEqP_E {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    (frames S.levels).E ((frames S.levels).act σ e.1) (rereadEqP A e).1 ∧
      (frames S.levels).E ((frames S.levels).act σ e.2) (rereadEqP A e).2 := by
  unfold rereadEqP
  cases hr : readFam e.1.1.code with
  | none => exact ⟨((frames S.levels).equivalence Θ').refl _, ((frames S.levels).equivalence Θ').refl _⟩
  | some r =>
      dsimp only
      by_cases h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2
      · rw [dif_pos h]
        exact ⟨rereadSideP_E A e.1 h.1 h.2.2.1 h.2.2.2, rereadSideP_E A e.2 h.2.1 h.2.2.1 h.2.2.2⟩
      · rw [dif_neg h]
        exact ⟨((frames S.levels).equivalence Θ').refl _, ((frames S.levels).equivalence Θ').refl _⟩

theorem rereadEqP_codes {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (e : Equation (TotalTerm Θ)) :
    ((rereadEqP A e).1.2.code = Presentation.subst σ.substitution e.1.2.code ∨
        ∃ (qs : List Head) (img : Fin A.psX.length → Fin qs.length),
          (rereadEqP A e).1.2.code = lams qs (Presentation.rename (sideRen qs A.psX img) A.val)) ∧
      ((rereadEqP A e).2.2.code = Presentation.subst σ.substitution e.2.2.code ∨
        ∃ (qs : List Head) (img : Fin A.psX.length → Fin qs.length),
          (rereadEqP A e).2.2.code = lams qs (Presentation.rename (sideRen qs A.psX img) A.val)) := by
  unfold rereadEqP
  cases hr : readFam e.1.1.code with
  | none => exact ⟨.inl rfl, .inl rfl⟩
  | some r =>
      dsimp only
      by_cases h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2
      · rw [dif_pos h]
        refine ⟨?_, ?_⟩
        · rcases rereadSideP_code A e.1 h.1 h.2.2.1 h.2.2.2 with same | ⟨img, same⟩
          · exact .inl same
          · exact .inr ⟨_, img, same⟩
        · rcases rereadSideP_code A e.2 h.2.1 h.2.2.1 h.2.2.2 with same | ⟨img, same⟩
          · exact .inl same
          · exact .inr ⟨_, img, same⟩
      · rw [dif_neg h]
        exact ⟨.inl rfl, .inl rfl⟩

/-- **The store re-read, exact and wide sides.** -/
def rereadStoreP {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (problem : EquationStore (TotalTerm Θ)) :
    EquationStore (TotalTerm Θ') :=
  problem.map (rereadEqP A)

theorem rereadStoreP_models {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ)
    (problem : EquationStore (TotalTerm Θ)) {Δ : Context S.R} (g : Δ ⟶ Θ') :
    (frames S.levels).Models g (rereadStoreP A problem) ↔
      (frames S.levels).Models g ((frames S.levels).applyStore σ problem) := by
  have equivalence := (frames S.levels).equivalence Δ
  constructor
  · intro solved e member
    obtain ⟨e₀, member₀, rfl⟩ := List.mem_map.mp member
    have sides := rereadEqP_E A e₀
    have read := solved (rereadEqP A e₀) (List.mem_map.mpr ⟨e₀, member₀, rfl⟩)
    have one := (frames S.levels).preserves g sides.1
    have two := (frames S.levels).preserves g sides.2
    exact equivalence.trans one (equivalence.trans read (equivalence.symm two))
  · intro solved e member
    obtain ⟨e₀, member₀, rfl⟩ := List.mem_map.mp member
    have sides := rereadEqP_E A e₀
    have read := solved ((frames S.levels).act σ e₀.1, (frames S.levels).act σ e₀.2)
      (List.mem_map.mpr ⟨e₀, member₀, rfl⟩)
    have one := (frames S.levels).preserves g sides.1
    have two := (frames S.levels).preserves g sides.2
    exact equivalence.trans (equivalence.symm one) (equivalence.trans read two)

/-- **Re-reading keeps only the answer's own unknowns in `X`'s place.** -/
theorem occ_rereadP {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {ps' : List Head} {c' : Head}
    {universes' : AllUniverses S.R ps'} {hc' : S.R.isUniverse c'}
    (σ : redecl Θ families X ps' c' universes' hc' ⟶ Θ) (A : AnswerData σ)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (store : EquationStore (TotalTerm Θ)) :
    occ (rereadStoreP A store) ⊆ (occ (Θ := Θ) store).erase X ∪ (lams A.psX A.val).support := by
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
  obtain ⟨c1, c2⟩ := rereadEqP_codes A e
  rcases hv with hv | hv
  · rcases c1 with same | ⟨qs, img, same⟩
    · rw [same] at hv
      exact side _ left hv
    · rw [same] at hv
      exact Finset.mem_union_right _ (support_reread qs A.psX img A.val hv)
  · rcases c2 with same | ⟨qs, img, same⟩
    · rw [same] at hv
      exact side _ right hv
    · rw [same] at hv
      exact Finset.mem_union_right _ (support_reread qs A.psX img A.val hv)

end RereadP

/-! ## The permutation -/

section Permute

variable {S : Setting Head L} (inh : Inhabitants S.R)

/-- **Every value is pruned to a permutation of all its binders**: reading it at the kept binders and renaming back
fixes every variable. -/
theorem pruned_all {n : Nat} {Γ : Ctx Head n} {ps : List Head} {c d : Head} {t : Tm Head n}
    (typed : Typed S.R Γ t (famCode ps c)) (below : S.R.cumulative c d) (K : List (Fin ps.length))
    (nodup : K.Nodup) (all : ∀ i, i ∈ K) : Pruned inh Γ ps K d t := by
  have tOpen := opened_typed ps typed
  have fixed : Presentation.rename (sideRen ps (keptDomains ps K) (keptPos ps K))
      (Presentation.subst (pullSub inh ps (keptDomains ps K) (keptPos ps K)) (opened ps t)) = opened ps t := by
    rw [rename_subst]
    conv_rhs => rw [← subst_ids (opened ps t)]
    apply ContextualDependentGeneralPattern.subst_eq_of_support
    intro v _
    apply kept_fixed inh ps K nodup v
    rcases index_cases ps v with ⟨w, rfl⟩ | ⟨j, rfl⟩
    · exact .inl ⟨w, rfl⟩
    · exact .inr ⟨j, all j, rfl⟩
  unfold Pruned
  rw [fixed]
  exact .refl (Derivable.cumul tOpen below)

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **Declaring an unknown again with its arguments permuted does not raise the weight**: it still occurs once, at the
same arity. -/
theorem weight_permute_le {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {psX : List Head} {cX : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (K : List (Fin psX.length)) (hlen : K.length = psX.length) (store : EquationStore (TotalTerm Θ))
    (occurs : X ∈ occ store) :
    weight (rereadStoreP (pruneData families X declared universesX hcX K) store) ≤ weight store := by
  have sub : occ (rereadStoreP (pruneData families X declared universesX hcX K) store) ⊆ occ (Θ := Θ) store := by
    intro v h
    rcases Finset.mem_union.mp (occ_rereadP (pruneHom families X declared universesX hcX K)
      (pruneData families X declared universesX hcX K) (fun _ => rfl) store h) with h | h
    · exact (Finset.mem_erase.mp h).2
    · have h' : v ∈ (flexSide psX (keptDomains psX K) X (keptPos psX K) : Tm Head Θ.arity).support := h
      rw [support_flexSide] at h'
      rw [Finset.mem_singleton.mp h']
      exact occurs
  unfold weight
  calc ∑ i ∈ occ (rereadStoreP (pruneData families X declared universesX hcX K) store),
        (famArity (Ctx.lookup (setFamAt Θ.raw X (keptDomains psX K) cX) i) + 1)
      ≤ ∑ i ∈ occ (Θ := Θ) store, (famArity (Ctx.lookup (setFamAt Θ.raw X (keptDomains psX K) cX) i) + 1) :=
        Finset.sum_le_sum_of_subset sub
    _ = ∑ i ∈ occ (Θ := Θ) store, (famArity (Ctx.lookup Θ.raw i) + 1) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h : i = X
        · rw [h, lookup_setFamAt_self, declared, famArity_famCode, famArity_famCode]
          simp [keptDomains, hlen]
        · rw [lookup_setFamAt_ne Θ.raw X i _ cX h]

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **Declare an unknown again with its arguments permuted**, `X := λ x̄. X' x_K` for a permutation `K` of all its
binders; exact, every value being pruned to `K`; the store re-read for exact and wide sides of `X`. -/
def permuteUpdate {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX d : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (hd : S.R.isUniverse d) (below : S.R.cumulative cX d) (K : List (Fin psX.length)) (nodup : K.Nodup)
    (all : ∀ i, i ∈ K) : Update S.levels (e :: rest) :=
  replaceUpdate (pruneHom families X declared universesX hcX K)
    (rereadStoreP (pruneData families X declared universesX hcX K) (e :: rest))
    (fun g => rereadStoreP_models _ (e :: rest) g)
    (fun {Δ} f _ => ⟨prunedHom inh Θ families X declared universesX hcX K f,
      factor_of_opened facts roots heads algebra rigid complete X declared universesX hcX hd below
        (pruneHom families X declared universesX hcX K)
        (flexBody psX (keptDomains psX K) X (keptPos psX K)) (answerSub_self X psX _)
        (pruneData families X declared universesX hcX K).typed f
        (prunedHom inh Θ families X declared universesX hcX K f)
        (fun i ne => by
          show Presentation.subst (prunedHom inh Θ families X declared universesX hcX K f).substitution
            (answerSub X psX _ i) = f.substitution i
          rw [answerSub_ne X psX _ ne]
          show (if i = X then _ else f.substitution i) = f.substitution i
          rw [if_neg ne])
        (by
          have tF : Typed S.R Δ.raw (f.substitution X) (famCode psX cX) := by
            have t := f.typed X
            rw [declared, famCode_subst] at t
            exact t
          have held := pruned_all inh tF below K nodup all
          rw [subst_flexBody_opened]
          have hX : (prunedHom inh Θ families X declared universesX hcX K f).substitution X =
              lams (keptDomains psX K) (Presentation.subst (pullSub inh psX (keptDomains psX K) (keptPos psX K))
                (opened psX (f.substitution X))) := by
            show (if X = X then _ else _) = _
            rw [if_pos rfl]
          rw [hX]
          have tOpen := value_opened_typed f declared
          have tM := tOpen.substitute (pullSub_substMor inh Δ.raw psX (keptDomains psX K) (keptPos psX K)
            universesX (keptPos_domains psX K))
          have beta := opened_lams (keptDomains psX K) Δ.formed (keptDomains_universes K universesX) hcX tM
          have renamed := beta.rename (sideRen_ctxRen Δ.raw psX (keptDomains psX K) (keptPos psX K)
            (keptPos_domains psX K))
          exact held.trans (Derivable.cumulEq renamed below).symm)⟩)

theorem permuteUpdate_remaining {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) (X : Fin Θ.arity) {psX : List Head} {cX d : Head}
    (declared : Ctx.lookup Θ.raw X = famCode psX cX) (universesX : AllUniverses S.R psX) (hcX : S.R.isUniverse cX)
    (hd : S.R.isUniverse d) (below : S.R.cumulative cX d) (K : List (Fin psX.length)) (nodup : K.Nodup)
    (all : ∀ i, i ∈ K) :
    (permuteUpdate inh facts roots heads algebra rigid complete (e := e) rest families X declared universesX hcX hd
      below K nodup all).remaining = rereadStoreP (pruneData families X declared universesX hcX K) (e :: rest) := rfl

end Permute

/-! ## The glb join under a permutation, one round -/

section Round

variable {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (join : Head → Head → Option Head)
  (joinSound : ∀ {u v w : Head}, join u v = some w → S.R.isUniverse w ∧ IsLub S.R w u v)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

/-- The inverse of the arguments of a wide side, as a list of the unknown's binders. -/
def inverseArgs {qs ps : List Head} (img : Fin ps.length → Fin qs.length) : List (Fin ps.length) :=
  (List.finRange qs.length).filterMap (posOf img)

/-- **The glb join under a permutation, as one round**: the right side `λ ȳ. G y_b`, a wide side of `G`, is turned into
`λ ȳ. G' ȳ` by declaring `G` again with its arguments permuted; the equation then read as a family equation is joined.
It lowers the common rank: the permutation keeps the weight, the join lowers it. -/
def permutedJoinStep {Θ : Context S.R} (families : Families Θ) {e : Equation (TotalTerm Θ)}
    (rest : EquationStore (TotalTerm Θ)) : Round S.levels commonRank (e :: rest) :=
  match readFam e.1.1.code with
  | none => .stuck
  | some r =>
      if h : e.1.1.code = famCode r.1 r.2 ∧ e.2.1.code = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧
          S.R.isUniverse r.2 then
        match readFlexW (S := S) Θ.raw r.1 e.2.2.code with
        | none => .stuck
        | some dataG =>
            if hK : (inverseArgs dataG.img).Nodup ∧ (∀ i, i ∈ inverseArgs dataG.img) ∧
                (inverseArgs dataG.img).length = dataG.ps.length ∧ S.R.cumulative dataG.c r.2 then
              match hd : readFlexK (S := S)
                  (rereadEqP (pruneData families dataG.unknown dataG.declared (famFacts families dataG.declared).1
                    (famFacts families dataG.declared).2 (inverseArgs dataG.img)) e) with
              | none => .stuck
              | some _ =>
                  if hsame : (viewOfK hd).left = (viewOfK hd).right then .stuck
                  else if hx : List.Forall₂ (CrossAt S.R (viewOfK hd).cl (viewOfK hd).cr) (viewOfK hd).psl
                      (viewOfK hd).psr then
                    match hg : glb (viewOfK hd).cl (viewOfK hd).cr with
                    | some _ =>
                        match hj : joinsOf join (viewOfK hd).psl (viewOfK hd).psr with
                        | some _ =>
                            .progress
                              ((permuteUpdate inh facts roots heads algebra rigid complete rest families dataG.unknown
                                  dataG.declared (famFacts families dataG.declared).1
                                  (famFacts families dataG.declared).2 h.2.2.2 hK.2.2.2 (inverseArgs dataG.img) hK.1
                                  hK.2.1).then
                                (joinMillerUpdate (redecl_families Θ families dataG.unknown _ _ _ _) (viewOfK hd)
                                  (joinsOf_sound join joinSound hj) (spec hg).1 (spec hg).2.1 (spec hg).2.2.1
                                  (glbJoinK_forces facts roots heads algebra rigid complete headTypingUnique
                                    (viewOfK hd) (spec hg) (joinsOf_sound join joinSound hj) hx)
                                  (rest.map (rereadEqP (pruneData families dataG.unknown dataG.declared
                                    (famFacts families dataG.declared).1 (famFacts families dataG.declared).2
                                    (inverseArgs dataG.img))))))
                              (Prod.Lex.left _ _ (lt_of_lt_of_le
                                (weight_joinMiller_lt (redecl_families Θ families dataG.unknown _ _ _ _) (viewOfK hd)
                                  (joinsOf_sound join joinSound hj) (spec hg).1 (spec hg).2.1 (spec hg).2.2.1 _ hsame)
                                (weight_permute_le dataG.declared (famFacts families dataG.declared).1
                                  (famFacts families dataG.declared).2 (inverseArgs dataG.img) hK.2.2.1 (e :: rest)
                                  (occurs_wide dataG))))
                        | none => .stuck
                    | none => .stuck
                  else .stuck
            else .stuck
      else .stuck

/-- **The round of the solver with the permuted join**: the round of the mixed wide solver, and where that is stuck on
the first equation, the glb join under a permutation. -/
def mixPermRound0 : {Γ : Context S.R} → (problem : EquationStore (TotalTerm Γ)) → Round S.levels commonRank problem
  | _, [] => .stuck
  | Γ, e :: rest =>
      match mixWideRound0 facts roots heads algebra rigid complete normalizes inh headTypingUnique join joinSound glb
          spec (e :: rest) with
      | .stuck =>
          if hfam : Families Γ then
            permutedJoinStep facts roots heads algebra rigid complete inh headTypingUnique join joinSound glb spec hfam
              rest
          else .stuck
      | other => other

/-- **The round**, the equations of families with parameters first. -/
def mixPermRound {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Round S.levels commonRank problem :=
  transport (equivalent_perm (joinFirst_perm problem).symm) (commonRank_perm (joinFirst_perm problem))
    (mixPermRound0 facts roots heads algebra rigid complete normalizes inh headTypingUnique join joinSound glb spec
      (joinFirst problem))

/-- **One solver for Miller patterns mixed with glb-join families, permutations included**, one rank: the common
rank. -/
def mixPermSolver : ContextualDependentWorklist.Solver S.levels where
  rank := commonRank
  round := mixPermRound facts roots heads algebra rigid complete normalizes inh headTypingUnique join joinSound glb spec

end Round

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
