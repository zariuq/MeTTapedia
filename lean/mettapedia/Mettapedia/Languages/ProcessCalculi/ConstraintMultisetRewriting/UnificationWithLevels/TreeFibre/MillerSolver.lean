import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.MillerRank

/-!
# The Miller solver: the tree's driver decides Miller patterns with arbitrary distinct locals

**The fragment** (`InMiller`): a telescope of universe families whose codomains form a chain; every equation, at
`Π ȳ : U_{qs}. U_d`, is between Miller sides `λ ȳ. F y_{a₁} … y_{a_k}` (distinct locals, each of exactly the
universe of `F`'s domain) and rigid locals `λ ȳ. y_l`.

**One round** reads the first equation and:
* deletes it when its two sides are the same code;
* refutes two different rigid locals, a rigid local outside a flex side's arguments (it escapes the unknown's
  scope), and a rigid local whose universe does not lie below the unknown's codomain (`misfit_unsolvable`);
* projects `F := λ x̄. x_j` against a rigid local among its arguments;
* intersects `F y_a ≐ F y_b`: `F` declared again at the positions where `a` and `b` agree;
* prunes `F y_a ≐ G y_b` (`F ≠ G`) to the positions of `F` whose local is among `b` (or `G`'s, symmetrically);
* solves `F y_a ≐ G y_b` once both use the same locals: `G := λ z̄. F z_{b⁻¹a}` when `F`'s codomain lies below
  `G`'s, or the converse.

Every step is exact (`Miller.valueUpdate`, `Miller.pruneUpdate`, `Miller.deleteSame`) and lowers the rank; on the
fragment a nonempty store is never stuck (`millerRound_ne_stuck`) and the rules keep the fragment
(`millerRound_stable`). So **the tree's driver decides the fragment** (`miller_decided`): from some budget on, the
run is fixed and ends with a principal answer or a certified refutation.
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

/-! ## Reading, complete -/

section Complete

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]

omit [∀ head, Decidable (S.R.isUniverse head)] in
theorem readSide_isSome_of_view {N : Nat} {Γ : Ctx Head N} {qs : List Head} {d : Head} {code : Tm Head N}
    (view : SideView (S := S) Γ qs d code) : (readSide (S := S) Γ qs d code).isSome = true := by
  cases view with
  | flex data below =>
      rw [data.side]
      exact readSide_flex Γ qs data.ps d data.unknown data.c data.img data.declared data.injective data.domains below
  | rigid l side below =>
      rw [side]
      exact readSide_rigid Γ qs d l below

/-- **Every Miller equation is read.** -/
theorem readEq_isSome_of_view {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (v : EqView (S := S) e) :
    (readEq (S := S) e).isSome = true := by
  have hl := readSide_isSome_of_view v.left
  have hr := readSide_isSome_of_view v.right
  have hf : readFam e.1.1.code = some (v.qs, v.d) := by rw [v.annotation_left, readFam_famCode]
  unfold readEq
  rw [hf]
  dsimp only
  rw [dif_pos ⟨v.annotation_left, v.annotation_right, v.universes, v.universe_d⟩]
  cases h1 : readSide (S := S) Θ.raw v.qs v.d e.1.2.code with
  | none => rw [h1] at hl; cases hl
  | some left =>
      cases h2 : readSide (S := S) Θ.raw v.qs v.d e.2.2.code with
      | none => rw [h2] at hr; cases hr
      | some right => rfl

/-- Families are decided. -/
def familyB {n : Nat} (t : Tm Head n) : Bool :=
  match readFam t with
  | some r => decide (t = famCode r.1 r.2 ∧ AllUniverses S.R r.1 ∧ S.R.isUniverse r.2)
  | none => false

omit [DecidableRel S.R.cumulative] in
theorem familyB_iff {n : Nat} (t : Tm Head n) : familyB (S := S) t = true ↔
    ∃ (ps : List Head) (c : Head), t = famCode ps c ∧ AllUniverses S.R ps ∧ S.R.isUniverse c := by
  constructor
  · intro h
    unfold familyB at h
    split at h
    · rename_i r _
      exact ⟨r.1, r.2, of_decide_eq_true h⟩
    · cases h
  · rintro ⟨ps, c, rfl, u, hc⟩
    unfold familyB
    rw [readFam_famCode]
    exact decide_eq_true ⟨rfl, u, hc⟩

instance decidableFamilies (Θ : Context S.R) : Decidable (Families Θ) :=
  decidable_of_iff (∀ i : Fin Θ.arity, familyB (S := S) (Ctx.lookup Θ.raw i) = true) (by
    unfold Families
    exact forall_congr' fun i => familyB_iff _)

end Complete

/-! ## What re-reading keeps -/

section Shapes

variable {S : Setting Head L}

theorem famFacts {Θ : Context S.R} (families : Families Θ) {X : Fin Θ.arity} {ps : List Head} {c : Head}
    (declared : Ctx.lookup Θ.raw X = famCode ps c) : AllUniverses S.R ps ∧ S.R.isUniverse c := by
  obtain ⟨ps', c', h, u, hc⟩ := families X
  obtain ⟨rfl, rfl⟩ := famCode_inj (h.symm.trans declared)
  exact ⟨u, hc⟩

/-- Re-reading a Miller side of one unknown at the body of a Miller side of another. -/
theorem rename_flexBody {N : Nat} (qs psX psY : List Head) (Y : Fin N) (κ : Fin psY.length → Fin psX.length)
    (img : Fin psX.length → Fin qs.length) :
    Presentation.rename (sideRen qs psX img) (flexBody psX psY Y κ) = flexBody qs psY Y (fun i => img (κ i)) := by
  rw [flexBody_eq, flexBody_eq, rename_comp]
  apply rename_ext
  intro u
  rcases index_cases psY u with ⟨w, rfl⟩ | ⟨i, rfl⟩
  · show spineRen psX (shift qs) _ (spineRen psY (shift psX) _ (shift psY w)) =
      spineRen psY (shift qs) _ (shift psY w)
    rw [spineRen_shift, spineRen_shift, spineRen_shift]
  · show spineRen psX (shift qs) _ (spineRen psY (shift psX) _ (loc psY i)) =
      spineRen psY (shift qs) _ (loc psY i)
    rw [spineRen_loc, spineRen_loc, spineRen_loc]

/-- **The answer's re-reading of a side of `X` is a side again.** -/
def ValueShape (Θ' : Context S.R) (psX : List Head) (cX : Head) (val : Tm Head (arity Θ'.arity psX)) : Prop :=
  ∀ (qs : List Head) (d : Head) (img : Fin psX.length → Fin qs.length), Function.Injective img →
    (∀ j, psX.get j = qs.get (img j)) → S.R.cumulative cX d →
      Nonempty (SideView (S := S) Θ'.raw qs d (lams qs (Presentation.rename (sideRen qs psX img) val)))

/-- A projection re-reads to a rigid local. -/
theorem project_shape (algebra : CumulativeAlgebra S.R) (Θ' : Context S.R) (psX : List Head) (cX : Head)
    (j : Fin psX.length) (fit : S.R.cumulative (psX.get j) cX) : ValueShape Θ' psX cX (.var (loc psX j)) := by
  intro qs d img _ domains below
  have code : (lams qs (Presentation.rename (sideRen qs psX img) (.var (loc psX j))) : Tm Head Θ'.arity) =
      localSide qs (img j) := by
    show lams qs (Tm.var (spineRen psX (shift qs) _ (loc psX j))) = _
    rw [spineRen_loc]
    rfl
  rw [code]
  exact ⟨.rigid (img j) rfl (by rw [← domains j]; exact algebra.trans fit below)⟩

/-- `Y x_κ` re-reads to a Miller side of `Y`. -/
theorem flex_shape (algebra : CumulativeAlgebra S.R) (Θ' : Context S.R) (psX : List Head) (cX : Head)
    {psY : List Head} {cY : Head} (Y : Fin Θ'.arity) (κ : Fin psY.length → Fin psX.length)
    (declared : Ctx.lookup Θ'.raw Y = famCode psY cY) (injective : Function.Injective κ)
    (domains : ∀ i, psY.get i = psX.get (κ i)) (below : S.R.cumulative cY cX) :
    ValueShape Θ' psX cX (flexBody psX psY Y κ) := by
  intro qs d img injImg domImg belowD
  rw [rename_flexBody]
  exact ⟨.flex ⟨Y, psY, cY, fun i => img (κ i), rfl, declared, injImg.comp injective,
    fun i => (domains i).trans (domImg (κ i))⟩ (algebra.trans below belowD)⟩

variable [DecidableEq Head]

/-- **Every side, re-read after an answer of the right shape, is a side again.** -/
theorem rereadSide_view {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {ps' : List Head} {c' : Head}
    {universes' : AllUniverses S.R ps'} {hc' : S.R.isUniverse c'}
    (σ : redecl Θ families X ps' c' universes' hc' ⟶ Θ) (A : AnswerData σ) (hX : A.X = X)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (shape : ValueShape (redecl Θ families X ps' c' universes' hc') A.psX A.cX A.val)
    (Y : TotalTerm Θ) {qs : List Head} {d : Head} (annotation : Y.1.code = famCode qs d)
    (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) (view : SideView (S := S) Θ.raw qs d Y.2.code) :
    Nonempty (SideView (S := S) (redecl Θ families X ps' c' universes' hc').raw qs d
      (rereadSide A Y annotation universes hd view).2.code) := by
  cases view with
  | rigid l side below =>
      refine ⟨.rigid l ?_ below⟩
      show Presentation.subst σ.substitution Y.2.code = localSide qs l
      exact (congrArg (Presentation.subst σ.substitution) side).trans (by rw [hsub, subst_localSide])
  | flex data below =>
      unfold rereadSide
      dsimp only
      by_cases h : data.unknown = A.X ∧ data.ps = A.psX
      · rw [dif_pos h]
        have hc : data.c = A.cX := by
          have decl := data.declared
          rw [h.1, A.declared] at decl
          exact (famCode_inj decl).2.symm
        exact shape qs d (castImg data.img h.2) (injective_cast h.2 data.injective) (domains_cast h.2 data.domains)
          (hc ▸ below)
      · rw [dif_neg h]
        have hne : data.unknown ≠ X := by
          intro same
          apply h
          refine ⟨same.trans hX.symm, ?_⟩
          have decl := data.declared
          rw [same, ← hX, A.declared] at decl
          exact (famCode_inj decl).1.symm
        refine ⟨.flex ⟨data.unknown, data.ps, data.c, data.img, ?_, ?_, data.injective, data.domains⟩ below⟩
        · show Presentation.subst σ.substitution Y.2.code = flexSide qs data.ps data.unknown data.img
          refine (congrArg (Presentation.subst σ.substitution) data.side).trans ?_
          rw [hsub, subst_flexSide, answerSub_ne X A.psX A.val hne]
          rfl
        · show Ctx.lookup (setFamAt Θ.raw X ps' c') data.unknown = famCode data.ps data.c
          rw [lookup_setFamAt_ne Θ.raw X data.unknown ps' c' hne]
          exact data.declared

variable [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **Re-reading keeps every equation a Miller equation.** -/
theorem views_reread {Θ : Context S.R} {families : Families Θ} {X : Fin Θ.arity} {ps' : List Head} {c' : Head}
    {universes' : AllUniverses S.R ps'} {hc' : S.R.isUniverse c'}
    (σ : redecl Θ families X ps' c' universes' hc' ⟶ Θ) (A : AnswerData σ) (hX : A.X = X)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (shape : ValueShape (redecl Θ families X ps' c' universes' hc') A.psX A.cX A.val)
    (store : EquationStore (TotalTerm Θ)) (views : ∀ e ∈ store, Nonempty (EqView (S := S) e)) :
    ∀ e' ∈ rereadStore A store, Nonempty (EqView (S := S) e') := by
  intro e' member
  obtain ⟨e, eMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨w⟩ := views e eMember
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (readEq_isSome_of_view w)
  unfold rereadEq
  rw [hv]
  dsimp only
  obtain ⟨left⟩ := rereadSide_view σ A hX hsub shape e.1 v.annotation_left v.universes v.universe_d v.left
  obtain ⟨right⟩ := rereadSide_view σ A hX hsub shape e.2 v.annotation_right v.universes v.universe_d v.right
  refine ⟨⟨v.qs, v.d, ?_, ?_, v.universes, v.universe_d, left, right⟩⟩
  · rw [rereadSide_type]
    show Presentation.subst σ.substitution e.1.1.code = famCode v.qs v.d
    rw [v.annotation_left, famCode_subst]
  · rw [rereadSide_type]
    show Presentation.subst σ.substitution e.2.1.code = famCode v.qs v.d
    rw [v.annotation_right, famCode_subst]

end Shapes

/-! ## The fragment -/

section Fragment

variable {S : Setting Head L}

/-- **The fragment of Miller stores.** -/
structure InMiller {Γ : Context S.R} (problem : EquationStore (TotalTerm Γ)) : Prop where
  families : Families Γ
  chain : Chain Γ
  views : ∀ e ∈ problem, Nonempty (EqView (S := S) e)

end Fragment

/-! ## Helpers -/

section Helpers

variable {S : Setting Head L}

theorem posOf_isSome {qs ps : List Head} {img : Fin ps.length → Fin qs.length} {l : Fin qs.length}
    (hit : ∃ j, img j = l) : (posOf img l).isSome = true := by
  cases found : posOf img l with
  | none =>
      obtain ⟨j, hj⟩ := hit
      exact absurd hj (posOf_none found j)
  | some _ => rfl

theorem posOf_get {qs ps : List Head} {img : Fin ps.length → Fin qs.length} {l : Fin qs.length}
    (h : (posOf img l).isSome = true) : img ((posOf img l).get h) = l :=
  posOf_some (Option.some_get h).symm

theorem length_filter_lt {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α), x ∈ l → p x = false →
    (l.filter p).length < l.length
  | [], _, member, _ => absurd member List.not_mem_nil
  | a :: l, x, member, hp => by
      have le := List.length_filter_le p l
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.filter_cons, hp, Bool.false_eq_true, if_false, List.length_cons]
        omega
      · have ih := length_filter_lt p l x member hp
        by_cases hpa : p a = true
        · simp only [List.filter_cons, hpa, if_true, List.length_cons]
          omega
        · simp only [List.filter_cons, hpa, Bool.false_eq_true, if_false, List.length_cons]
          omega

theorem kept_shorter {ps : List Head} (p : Fin ps.length → Bool) (i : Fin ps.length) (hp : p i = false) :
    (keptDomains ps ((List.finRange ps.length).filter p)).length < ps.length := by
  unfold keptDomains
  rw [List.length_map]
  have := length_filter_lt p (List.finRange ps.length) i (List.mem_finRange i) hp
  rwa [List.length_finRange] at this

theorem occurs_side {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {qs : List Head} {code : Tm Head Θ.arity} (data : FlexData Θ.raw qs code)
    (which : code = e.1.2.code ∨ code = e.2.2.code) : data.unknown ∈ occ (e :: rest) := by
  have h := congrArg Tm.support data.side
  rw [support_flexSide] at h
  apply mem_occ.mpr
  refine ⟨e, List.mem_cons_self, ?_⟩
  rcases which with same | same
  · left
    rw [← same, h]
    exact Finset.mem_singleton_self _
  · right
    rw [← same, h]
    exact Finset.mem_singleton_self _

/-- The projection is typed. -/
theorem proj_typed {Θ : Context S.R} (X : Fin Θ.arity) {ps : List Head} {c : Head} (j : Fin ps.length)
    (fit : S.R.cumulative (ps.get j) c) :
    Typed S.R (ctx (setFamAt Θ.raw X ps c) ps) (.var (loc ps j)) (.head c) := by
  have v := Derivable.var (R := S.R) (Γ := ctx (setFamAt Θ.raw X ps c) ps) (loc ps j)
  rw [lookup_loc] at v
  exact Derivable.cumul v fit

/-- The map of a solve. -/
def solveMap {qs psX psY : List Head} (imgX : Fin psX.length → Fin qs.length) (imgY : Fin psY.length → Fin qs.length)
    (cover : ∀ i, ∃ j, imgX j = imgY i) : Fin psY.length → Fin psX.length :=
  fun i => (posOf imgX (imgY i)).get (posOf_isSome (cover i))

theorem solveMap_spec {qs psX psY : List Head} (imgX : Fin psX.length → Fin qs.length)
    (imgY : Fin psY.length → Fin qs.length) (cover : ∀ i, ∃ j, imgX j = imgY i) (i : Fin psY.length) :
    imgX (solveMap imgX imgY cover i) = imgY i :=
  posOf_get _

end Helpers

/-! ## The steps -/

section Steps

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Inhabitants S.R)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
include facts roots heads algebra rigid complete inh in
/-- **A misfit local refutes.** From `λ ȳ. F y_a ≐ λ ȳ. y_l` with `l` the `j`-th argument, when the universe of
`F`'s `j`-th domain does not lie below `F`'s codomain, there is no solution: `F`'s value would equal the variable
`x_j`, and no type of the codomain is equal to a variable of a universe not below it (the tree's `var_not_small`). -/
theorem misfit_unsolvable {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} {qs : List Head} {d : Head}
    (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d) {X : Fin Θ.arity} {ps : List Head} {c : Head}
    (img : Fin ps.length → Fin qs.length) (declared : Ctx.lookup Θ.raw X = famCode ps c)
    (universesP : AllUniverses S.R ps) (hc : S.R.isUniverse c) (injective : Function.Injective img)
    (domains : ∀ j, ps.get j = qs.get (img j)) (l : Fin qs.length) (j : Fin ps.length) (hp : posOf img l = some j)
    (misfit : ¬ S.R.cumulative (ps.get j) c)
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f problem →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)) :
    ¬ (frames S.levels).Solvable problem := by
  rintro ⟨Δ, f, solved⟩
  have forced := flexLocal_forced inh f qs img universes domains injective l (opens f solved)
  have hj : pullImg (n := Δ.arity) inh qs ps img l = .var (loc ps j) := by
    unfold pullImg
    rw [hp]
  rw [hj] at forced
  exact ContextualDependentUniverseInjective.var_not_small facts roots heads algebra rigid complete
    (ctx_formed ps Δ.formed universesP) (lookup_loc Δ.raw ps j) (universesP _ (List.get_mem ps j)) hc misfit
    (value_opened_typed f declared) ⟨d, hd, forced⟩

include facts roots heads algebra rigid complete inh in
/-- **Flex against a rigid local**: project; or refute, when the local escapes the unknown's scope, or when its
universe does not lie below the unknown's codomain. -/
def stepFlexLocal {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) {qs : List Head} {d : Head} (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    {X : Fin Θ.arity} {ps : List Head} {c : Head} (img : Fin ps.length → Fin qs.length)
    (declared : Ctx.lookup Θ.raw X = famCode ps c) (injective : Function.Injective img)
    (domains : ∀ j, ps.get j = qs.get (img j)) (below : S.R.cumulative c d) (l : Fin qs.length)
    (occurs : X ∈ occ (e :: rest))
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)) :
    Round S.levels millerRank (e :: rest) :=
  match hp : posOf img l with
  | some j =>
      if hfit : S.R.cumulative (ps.get j) c then
        .progress
          (valueUpdate facts roots heads algebra rigid complete rest families X declared
            (famFacts families declared).1 (famFacts families declared).2 hd below (.var (loc ps j))
            (proj_typed X j hfit)
            (fun {Δ} f solved => by
              have forced := flexLocal_forced inh f qs img universes domains injective l (opens f solved)
              have hj : pullImg (n := Δ.arity) inh qs ps img l = .var (loc ps j) := by
                unfold pullImg
                rw [hp]
              rw [hj] at forced
              show Equal S.R _ _ (liftSubs ps f.substitution (loc ps j)) _
              rw [liftSubs_loc]
              exact forced))
          (Prod.Lex.left _ _ (weight_value_lt _ (valueData families X declared _ _ _ _) (fun _ => rfl)
            (e :: rest) occurs (by
              show (localSide ps j : Tm Head Θ.arity).support ⊆ _
              rw [support_localSide]
              exact Finset.empty_subset _)))
      else
        .refuted (misfit_unsolvable facts roots heads algebra rigid complete inh universes hd img declared
          (famFacts families declared).1 (famFacts families declared).2 injective domains l j hp hfit opens)
  | none =>
      .refuted (scope_unsolvable rigid complete inh universes img domains injective l (posOf_none hp) opens)

include facts roots heads algebra rigid complete inh in
/-- **Solve** `X := λ x̄. Y x_σ`, for `λ ȳ. Y y_b ≐ λ ȳ. X y_a` once every local of `b` is among `a`. -/
def solveRound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) {qs : List Head} {d : Head} (universes : AllUniverses S.R qs) (hd : S.R.isUniverse d)
    {X Y : Fin Θ.arity} {psX psY : List Head} {cX cY : Head} (imgX : Fin psX.length → Fin qs.length)
    (imgY : Fin psY.length → Fin qs.length) (declX : Ctx.lookup Θ.raw X = famCode psX cX)
    (declY : Ctx.lookup Θ.raw Y = famCode psY cY) (injX : Function.Injective imgX)
    (_injY : Function.Injective imgY)
    (domX : ∀ j, psX.get j = qs.get (imgX j)) (domY : ∀ j, psY.get j = qs.get (imgY j))
    (belowX : S.R.cumulative cX d) (ne : Y ≠ X) (cover : ∀ i, ∃ j, imgX j = imgY i)
    (codomains : S.R.cumulative cY cX) (occX : X ∈ occ (e :: rest)) (occY : Y ∈ occ (e :: rest))
    (opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psY imgY) (opened psY (f.substitution Y)))
        (Presentation.rename (sideRen qs psX imgX) (opened psX (f.substitution X))) (.head d)) :
    Round S.levels millerRank (e :: rest) :=
  have domσ : ∀ i, psY.get i = psX.get (solveMap imgX imgY cover i) := fun i => by
    rw [domX (solveMap imgX imgY cover i), solveMap_spec imgX imgY cover i, domY i]
  have typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) (flexBody psX psY Y (solveMap imgX imgY cover))
      (.head cX) := by
    have tY : Typed S.R (setFamAt Θ.raw X psX cX) (.var Y) (famCode psY cY) := by
      have v := Derivable.var (R := S.R) (Γ := setFamAt Θ.raw X psX cX) Y
      rw [lookup_setFamAt_ne Θ.raw X Y psX cX ne, declY] at v
      exact v
    rw [flexBody_eq]
    exact Derivable.cumul ((opened_typed psY tY).rename (sideRen_ctxRen _ psX psY _ domσ)) codomains
  .progress
    (valueUpdate facts roots heads algebra rigid complete rest families X declX
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
    (Prod.Lex.left _ _ (weight_value_lt _ (valueData families X declX _ _ _ typed) (fun _ => rfl) (e :: rest) occX
      (by
        show (flexSide psX psY Y (solveMap imgX imgY cover)).support ⊆ _
        rw [support_flexSide]
        intro v hv
        rw [Finset.mem_singleton.mp hv]
        exact Finset.mem_erase.mpr ⟨ne, occY⟩)))

include facts roots heads algebra rigid complete inh in
/-- **Prune** `X := λ x̄. X' x_K` to a list `K` of its binders to which every solution's value is pruned. -/
def pruneRound {Θ : Context S.R} {e : Equation (TotalTerm Θ)} (rest : EquationStore (TotalTerm Θ))
    (families : Families Θ) {d : Head} (hd : S.R.isUniverse d) {X : Fin Θ.arity} {psX : List Head} {cX : Head}
    (declX : Ctx.lookup Θ.raw X = famCode psX cX) (belowX : S.R.cumulative cX d) (p : Fin psX.length → Bool)
    (dropped : ∃ i, p i = false) (occX : X ∈ occ (e :: rest))
    (pruned : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Pruned inh Δ.raw psX ((List.finRange psX.length).filter p) d (f.substitution X)) :
    Round S.levels millerRank (e :: rest) :=
  .progress
    (pruneUpdate facts roots heads algebra rigid complete inh rest families X declX (famFacts families declX).1
      (famFacts families declX).2 hd belowX ((List.finRange psX.length).filter p) pruned)
    (by
      obtain ⟨i, hi⟩ := dropped
      exact Prod.Lex.left _ _ (weight_prune_lt declX (kept_shorter p i hi) _
        (pruneData families X declX _ _ _) (fun _ => rfl) (e :: rest) occX (by
          show (flexSide psX _ X _).support ⊆ _
          rw [support_flexSide])))

end Steps

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
