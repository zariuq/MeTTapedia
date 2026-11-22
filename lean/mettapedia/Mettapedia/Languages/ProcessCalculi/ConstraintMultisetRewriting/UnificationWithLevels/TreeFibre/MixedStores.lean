import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.CommonRank

/-!
# Stores mixing Miller equations and equations between arrow codes: the Miller rounds keep both

A **mixed store** (`MixedStore`) lies over a telescope of universe families, and each of its equations is a Miller
equation or an equation between arrow codes with unknowns at universes (the arrow piece's condition, read on the one
equation: `InArrowsCod choices [e]`).

* **The Miller rounds keep the arrow equations** (`arrowEq_reread`, `arrowEq_lowered`). An unknown met by an equation
  between arrow codes is declared at a universe, a family of no parameters. A Miller answer for such an unknown is
  another unknown declared at a universe (solving `X := λ. Y` with both of no parameters); a projection and a pruning
  need parameters; a lowering to a greatest lower bound keeps a universe a universe. So an equation between arrow codes
  is re-read as one: its codes are instantiated by a renaming of unknowns at universes, its heads are kept, and no
  declaration of the telescope of families mentions an unknown.
* **They keep the Miller equations**: the Miller solver's own re-reading (`views_reread`, `lowerView`), read one
  equation at a time.
* **Every progress of the Miller round keeps a mixed store mixed** (`millerGlbRound_mixed`).

The other direction does not hold, and that is why a solver mixes the two pieces in one order: solving `X := t` with
`t` rigid turns a Miller side `λ ȳ. X` into `λ ȳ. t`, which is neither a Miller side nor an equation at a universe.
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

namespace Miller

/-! ## Codes of families, and the answer's value at no parameters -/

section Codes

/-- A universe family mentions no unknown. -/
theorem not_mem_support_famCode {n : Nat} : ∀ (ps : List Head) (c : Head) (v : Fin n),
    v ∉ (famCode ps c : Tm Head n).support
  | [], c, v => by simp only [famCode_nil, Tm.support, Finset.notMem_empty, not_false_eq_true]
  | p :: ps, c, v => by
      simp only [famCode_cons, Tm.support, Finset.mem_union, mem_outerSupport, Finset.notMem_empty, false_or]
      exact not_mem_support_famCode ps c v.succ

/-- A universe family equal to a universe has no parameters. -/
theorem famCode_eq_head {n : Nat} {ps : List Head} {c v : Head} (h : (famCode ps c : Tm Head n) = .head v) :
    ps = [] := by
  cases ps with
  | nil => rfl
  | cons p ps => cases h

/-- Re-reading a side of no binders through a value of no parameters gives the value itself. -/
theorem reread_nil {N : Nat} : ∀ (psX : List Head) (img : Fin psX.length → Fin ([] : List Head).length)
    (val : Tm Head (arity N psX)), lams [] (Presentation.rename (sideRen [] psX img) val) = lams psX val
  | [], _, val => Presentation.rename_id val
  | _ :: _, img, _ => (img ⟨0, Nat.succ_pos _⟩).elim0

end Codes

/-! ## Equations between arrow codes, one at a time -/

section Arrows

variable {S : Setting Head L}

/-- Over a telescope of universe families, no declaration mentions an unknown. -/
theorem sidesApart_of_families {Θ : Context S.R} (families : Families Θ) (l r : Tm Head Θ.arity) :
    SidesApart Θ.raw l r := by
  intro i j member
  obtain ⟨ps, c, hi, _, _⟩ := families i
  rw [hi] at member
  exact absurd member (not_mem_support_famCode ps c j)

/-- **A store is in the fragment of arrow codes exactly when each of its equations is.** -/
theorem inArrowsCod_iff {choices : ExecutableChecking.HeadChoices S.R} {Θ : Context S.R}
    {problem : EquationStore (TotalTerm Θ)} :
    InArrowsCod choices problem ↔ ∀ e ∈ problem, InArrowsCod choices [e] := by
  constructor
  · intro inside e member
    refine ⟨fun e' m => ?_, fun e' m => ?_, fun e' m => ?_, fun e' m => ?_⟩
    · obtain rfl := List.mem_singleton.mp m
      exact inside.occurring _ member
    · obtain rfl := List.mem_singleton.mp m
      exact inside.apart _ member
    · obtain rfl := List.mem_singleton.mp m
      exact inside.shapes _ member
    · obtain rfl := List.mem_singleton.mp m
      exact inside.typedHeads _ member
  · intro each
    exact ⟨fun e m => (each e m).occurring e (List.mem_singleton_self _),
      fun e m => (each e m).apart e (List.mem_singleton_self _),
      fun e m => (each e m).shapes e (List.mem_singleton_self _),
      fun e m => (each e m).typedHeads e (List.mem_singleton_self _)⟩

/-- **The decider of the fragment of arrow codes is complete.** -/
theorem inArrowsCodB_of [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
    (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    (inside : InArrowsCod choices problem) : inArrowsCodB choices problem = true := by
  simp only [inArrowsCodB, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun e member => ?_, fun e member => ?_⟩, fun e member => ?_⟩
  · exact ⟨⟨atUniversesB_of (inside.occurring e member).1, atUniversesB_of (inside.occurring e member).2⟩,
      sidesApartB_of (inside.apart e member)⟩
  · obtain ⟨w⟩ := inside.shapes e member
    rw [readArrowCodEq_complete w]
    rfl
  · exact ⟨fun h hh => (inside.typedHeads e member).1 h hh, fun h hh => (inside.typedHeads e member).2 h hh⟩

/-- **A lowering keeps an equation between arrow codes one.** -/
theorem arrowEq_lowered (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R} (ℓ : CodomainLowering Θ)
    (families' : Families ℓ.target) {e : Equation (TotalTerm Θ)} (inside : InArrowsCod choices [e]) :
    InArrowsCod choices
      [(((frames S.levels).act ℓ.hom e.1, (frames S.levels).act ℓ.hom e.2) : Equation (TotalTerm ℓ.target))] := by
  have self := List.mem_singleton_self e
  obtain ⟨w⟩ := inside.shapes e self
  obtain ⟨occL, occR⟩ := inside.occurring e self
  obtain ⟨headsL, headsR⟩ := inside.typedHeads e self
  have lowerOcc : ∀ t : Tm Head Θ.arity, AtUniverses (S := S) Θ.raw t → AtUniverses (S := S) ℓ.target.raw t := by
    intro t occ i member
    obtain ⟨u, hu, uu⟩ := occ i member
    by_cases h : i = ℓ.index
    · subst h
      have nil : ℓ.ps = [] := famCode_eq_head (ℓ.declared.symm.trans hu)
      refine ⟨ℓ.lower, ?_, ℓ.universe_lower⟩
      rw [ℓ.lookup_self, nil]
      rfl
    · rw [ℓ.lookup_ne h]
      exact ⟨u, hu, uu⟩
  refine ⟨fun e' m => ?_, fun e' m => ?_, fun e' m => ?_, fun e' m => ?_⟩
  · obtain rfl := List.mem_singleton.mp m
    rw [lowered_code, lowered_code]
    exact ⟨lowerOcc _ occL, lowerOcc _ occR⟩
  · obtain rfl := List.mem_singleton.mp m
    exact sidesApart_of_families families' _ _
  · obtain rfl := List.mem_singleton.mp m
    refine ⟨⟨w.v, ?_, ?_, w.universe_v, ?_, ?_⟩⟩
    · rw [lowered_typeCode]
      exact w.annotation_left
    · rw [lowered_typeCode]
      exact w.annotation_right
    · rw [lowered_code]
      exact w.code_left
    · rw [lowered_code]
      exact w.code_right
  · obtain rfl := List.mem_singleton.mp m
    rw [lowered_code, lowered_code]
    exact ⟨headsL, headsR⟩

end Arrows

/-! ## A Miller answer keeps an equation between arrow codes one -/

section Reread

variable {S : Setting Head L} [DecidableEq Head]

/-- **A side at a universe, re-read**: its instance, or the answer's value at no parameters. -/
theorem rereadSide_code_universe {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) (Y : TotalTerm Θ)
    {qs : List Head} {d : Head} (annotation : Y.1.code = famCode qs d) (universes : AllUniverses S.R qs)
    (hd : S.R.isUniverse d) (view : SideView (S := S) Θ.raw qs d Y.2.code) (hq : qs = []) :
    (rereadSide A Y annotation universes hd view).2.code = Presentation.subst σ.substitution Y.2.code ∨
      (A.psX = [] ∧ (rereadSide A Y annotation universes hd view).2.code = lams A.psX A.val) := by
  subst hq
  rcases rereadSide_code A Y annotation universes hd view with same | ⟨img, same⟩
  · exact .inl same
  · have nil : A.psX = [] := List.eq_nil_of_length_eq_zero (by
      by_contra pos
      exact (img ⟨0, Nat.pos_of_ne_zero pos⟩).elim0)
    exact .inr ⟨nil, same.trans (reread_nil A.psX img A.val)⟩

variable [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

/-- **An equation at a universe, re-read**: its annotations instantiated; each side its instance, or the answer's
value at no parameters. -/
theorem rereadEq_universe {Θ Θ' : Context S.R} {σ : Θ' ⟶ Θ} (A : AnswerData σ) {e : Equation (TotalTerm Θ)}
    {v : Head} (left : e.1.1.code = .head v) :
    ((rereadEq A e).1.1.code = Presentation.subst σ.substitution e.1.1.code ∧
      (rereadEq A e).2.1.code = Presentation.subst σ.substitution e.2.1.code) ∧
    ((rereadEq A e).1.2.code = Presentation.subst σ.substitution e.1.2.code ∨
      (A.psX = [] ∧ (rereadEq A e).1.2.code = lams A.psX A.val)) ∧
    ((rereadEq A e).2.2.code = Presentation.subst σ.substitution e.2.2.code ∨
      (A.psX = [] ∧ (rereadEq A e).2.2.code = lams A.psX A.val)) := by
  unfold rereadEq
  cases h : readEq (S := S) e with
  | none => exact ⟨⟨rfl, rfl⟩, .inl rfl, .inl rfl⟩
  | some w =>
      have hq : w.qs = [] := famCode_eq_head (w.annotation_left.symm.trans left)
      refine ⟨⟨?_, ?_⟩,
        rereadSide_code_universe A e.1 w.annotation_left w.universes w.universe_d w.left hq,
        rereadSide_code_universe A e.2 w.annotation_right w.universes w.universe_d w.right hq⟩
      · rw [rereadSide_type]
        rfl
      · rw [rereadSide_type]
        rfl

/-- **A Miller answer keeps an equation between arrow codes one**, when, at no parameters, its value is an unknown
declared at a universe. -/
theorem arrowEq_reread (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R} {families : Families Θ}
    {X : Fin Θ.arity} {ps' : List Head} {c' : Head} {universes' : AllUniverses S.R ps'} {hc' : S.R.isUniverse c'}
    (σ : redecl Θ families X ps' c' universes' hc' ⟶ Θ) (A : AnswerData σ) (hX : A.X = X)
    (hsub : ∀ t : Tm Head Θ.arity, Presentation.subst σ.substitution t =
      Presentation.subst (answerSub X A.psX A.val) t)
    (fitsNil : A.psX = [] → ∃ j w, lams A.psX A.val = .var j ∧
      Ctx.lookup (redecl Θ families X ps' c' universes' hc').raw j = .head w ∧ S.R.isUniverse w)
    {e : Equation (TotalTerm Θ)} (inside : InArrowsCod choices [e]) :
    InArrowsCod choices [rereadEq A e] := by
  have self := List.mem_singleton_self e
  obtain ⟨w⟩ := inside.shapes e self
  obtain ⟨occL, occR⟩ := inside.occurring e self
  obtain ⟨headsL, headsR⟩ := inside.typedHeads e self
  obtain ⟨⟨typeL, typeR⟩, codeL, codeR⟩ := rereadEq_universe A w.annotation_left
  have side : ∀ (t t' : Tm Head Θ.arity), ArrowCod t → AtUniverses (S := S) Θ.raw t →
      (∀ h ∈ codHeads t, (choices.typing h).isSome = true) →
      (t' = Presentation.subst σ.substitution t ∨ (A.psX = [] ∧ t' = lams A.psX A.val)) →
      ArrowCod t' ∧ AtUniverses (S := S) (redecl Θ families X ps' c' universes' hc').raw t' ∧
        ∀ h ∈ codHeads t', (choices.typing h).isSome = true := by
    intro t t' code occ heads which
    rcases which with same | ⟨nil, same⟩
    · rw [hsub] at same
      have hs : answerSub X A.psX A.val = solveSub X (lams A.psX A.val) := rfl
      rw [hs] at same
      by_cases inT : X ∈ t.support
      · obtain ⟨u, hu, _⟩ := occ X inT
        have nil : A.psX = [] := by
          have decl := A.declared
          rw [hX, hu] at decl
          exact famCode_eq_head decl.symm
        obtain ⟨j, wj, hj, lj, uj⟩ := fitsNil nil
        rw [hj] at same
        subst same
        refine ⟨arrowCod_subst_solve (.var j) code, fun i member => ?_, fun h member => ?_⟩
        · rcases support_subst_solve code i member with ⟨inner, ne⟩ | inj
          · rw [redecl_ne Θ families X ps' c' universes' hc' ne]
            exact occ i inner
          · have same : i = j := Finset.mem_singleton.mp inj
            subst same
            exact ⟨wj, lj, uj⟩
        · rcases codHeads_subst_solve code h member with inner | fromVar
          · exact heads h inner
          · cases fromVar
      · rw [subst_solveSub_absent _ code inT] at same
        subst same
        refine ⟨code, fun i member => ?_, heads⟩
        have ne : i ≠ X := fun same => inT (same ▸ member)
        rw [redecl_ne Θ families X ps' c' universes' hc' ne]
        exact occ i member
    · obtain ⟨j, wj, hj, lj, uj⟩ := fitsNil nil
      rw [hj] at same
      subst same
      refine ⟨.var j, fun i member => ?_, fun h member => by cases member⟩
      have same : i = j := Finset.mem_singleton.mp member
      subst same
      exact ⟨wj, lj, uj⟩
  obtain ⟨cL, aL, hL⟩ := side _ _ w.code_left occL headsL codeL
  obtain ⟨cR, aR, hR⟩ := side _ _ w.code_right occR headsR codeR
  have families' := redecl_families Θ families X ps' c' universes' hc'
  refine ⟨fun e' m => ?_, fun e' m => ?_, fun e' m => ?_, fun e' m => ?_⟩
  · obtain rfl := List.mem_singleton.mp m
    exact ⟨aL, aR⟩
  · obtain rfl := List.mem_singleton.mp m
    exact sidesApart_of_families families' _ _
  · obtain rfl := List.mem_singleton.mp m
    refine ⟨⟨w.v, ?_, ?_, w.universe_v, cL, cR⟩⟩
    · rw [typeL, w.annotation_left]
      rfl
    · rw [typeR, w.annotation_right]
      rfl
  · obtain rfl := List.mem_singleton.mp m
    exact ⟨hL, hR⟩

end Reread

/-! ## Mixed stores -/

section Mixed

variable {S : Setting Head L}

/-- **A store mixing Miller equations and equations between arrow codes**, over a telescope of universe families. -/
structure MixedStore (choices : ExecutableChecking.HeadChoices S.R) {Θ : Context S.R}
    (problem : EquationStore (TotalTerm Θ)) : Prop where
  families : Families Θ
  each : ∀ e ∈ problem, Nonempty (EqView (S := S) e) ∨ InArrowsCod choices [e]

variable {choices : ExecutableChecking.HeadChoices S.R}

theorem MixedStore.tail {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : MixedStore choices (e :: rest)) : MixedStore choices rest :=
  ⟨inside.families, fun e' m => inside.each e' (List.mem_cons_of_mem _ m)⟩

theorem MixedStore.perm {Θ : Context S.R} {P Q : EquationStore (TotalTerm Θ)} (inside : MixedStore choices P)
    (perm : P.Perm Q) : MixedStore choices Q :=
  ⟨inside.families, fun e m => inside.each e (perm.mem_iff.mpr m)⟩

/-- A Miller store is mixed. -/
theorem MixedStore.of_miller {Θ : Context S.R} {P : EquationStore (TotalTerm Θ)} (inside : InMillerGlb (S := S) P) :
    MixedStore choices P :=
  ⟨inside.families, fun e m => .inl (inside.views e m)⟩

/-- A store of equations between arrow codes over a telescope of families is mixed. -/
theorem MixedStore.of_arrows {Θ : Context S.R} {P : EquationStore (TotalTerm Θ)} (families : Families Θ)
    (inside : InArrowsCod choices P) : MixedStore choices P :=
  ⟨families, fun e m => .inr (inArrowsCod_iff.mp inside e m)⟩

variable (choices) (algebra : CumulativeAlgebra S.R)

include algebra in
/-- **A lowering keeps a store mixed.** -/
theorem mixed_lowered {Θ : Context S.R} (ℓ : CodomainLowering Θ) {P : EquationStore (TotalTerm Θ)}
    (inside : MixedStore choices P) : MixedStore choices ((frames S.levels).applyStore ℓ.hom P) := by
  have families' := lowering_families ℓ inside.families
  refine ⟨families', fun e' member => ?_⟩
  obtain ⟨e₀, m₀, rfl⟩ := List.mem_map.mp member
  rcases inside.each e₀ m₀ with view | arrow
  · obtain ⟨v⟩ := view
    exact .inl ⟨lowerView algebra ℓ v⟩
  · exact .inr (arrowEq_lowered choices ℓ families' arrow)

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]

omit algebra in
/-- **A value rule keeps a store mixed**, when, at no parameters, its value is an unknown declared at a universe. -/
theorem mixed_value {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : MixedStore choices (e :: rest)) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declX : Ctx.lookup Θ.raw X = famCode psX cX) (val : Tm Head (arity Θ.arity psX))
    (typed : Typed S.R (ctx (setFamAt Θ.raw X psX cX) psX) val (.head cX))
    (shape : ValueShape (redecl Θ inside.families X psX cX (famFacts inside.families declX).1
      (famFacts inside.families declX).2) psX cX val)
    (fitsNil : psX = [] → ∃ j w, lams psX val = .var j ∧
      Ctx.lookup (setFamAt Θ.raw X psX cX) j = .head w ∧ S.R.isUniverse w) :
    MixedStore choices (rereadStore (valueData inside.families X declX (famFacts inside.families declX).1
      (famFacts inside.families declX).2 val typed) (e :: rest)) := by
  refine ⟨redecl_families Θ inside.families X psX cX _ _, fun e' member => ?_⟩
  obtain ⟨e₀, m₀, rfl⟩ := List.mem_map.mp member
  rcases inside.each e₀ m₀ with view | arrow
  · left
    exact views_reread (valueHom inside.families X declX (famFacts inside.families declX).1
        (famFacts inside.families declX).2 val typed)
      (valueData inside.families X declX (famFacts inside.families declX).1 (famFacts inside.families declX).2
        val typed)
      rfl (fun _ => rfl) shape [e₀] (fun x hx => by obtain rfl := List.mem_singleton.mp hx; exact view) _
      (List.mem_map.mpr ⟨e₀, List.mem_singleton_self _, rfl⟩)
  · right
    exact arrowEq_reread choices (valueHom inside.families X declX (famFacts inside.families declX).1
        (famFacts inside.families declX).2 val typed)
      (valueData inside.families X declX (famFacts inside.families declX).1 (famFacts inside.families declX).2
        val typed)
      rfl (fun _ => rfl) fitsNil arrow

include algebra in
/-- **A pruning keeps a store mixed.** -/
theorem mixed_prune {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    (inside : MixedStore choices (e :: rest)) (X : Fin Θ.arity) {psX : List Head} {cX : Head}
    (declX : Ctx.lookup Θ.raw X = famCode psX cX) (K : List (Fin psX.length)) (nodup : K.Nodup) :
    MixedStore choices (rereadStore (pruneData inside.families X declX (famFacts inside.families declX).1
      (famFacts inside.families declX).2 K) (e :: rest)) := by
  have uK := keptDomains_universes K (famFacts inside.families declX).1
  have hcX := (famFacts inside.families declX).2
  have declX' : Ctx.lookup (setFamAt Θ.raw X (keptDomains psX K) cX) X = famCode (keptDomains psX K) cX :=
    lookup_setFamAt_self Θ.raw X _ cX
  refine ⟨redecl_families Θ inside.families X (keptDomains psX K) cX uK hcX, fun e' member => ?_⟩
  obtain ⟨e₀, m₀, rfl⟩ := List.mem_map.mp member
  rcases inside.each e₀ m₀ with view | arrow
  · left
    exact views_reread (pruneHom inside.families X declX (famFacts inside.families declX).1 hcX K)
      (pruneData inside.families X declX (famFacts inside.families declX).1 hcX K) rfl (fun _ => rfl)
      (flex_shape algebra (redecl Θ inside.families X (keptDomains psX K) cX uK hcX) psX cX X (keptPos psX K)
        declX' (keptPos_injective nodup) (keptPos_domains psX K) (S.levels.cumulative_refl hcX))
      [e₀] (fun x hx => by obtain rfl := List.mem_singleton.mp hx; exact view) _
      (List.mem_map.mpr ⟨e₀, List.mem_singleton_self _, rfl⟩)
  · right
    refine arrowEq_reread choices (pruneHom inside.families X declX (famFacts inside.families declX).1 hcX K)
      (pruneData inside.families X declX (famFacts inside.families declX).1 hcX K) rfl (fun _ => rfl)
      (fun nil => ?_) arrow
    change psX = [] at nil
    subst nil
    have empty : K = [] := by
      cases K with
      | nil => rfl
      | cons k _ => exact k.elim0
    subst empty
    exact ⟨X, cX, rfl, declX', hcX⟩

end Mixed

/-! ## Every Miller round keeps a mixed store mixed -/

section Rounds

variable {S : Setting Head L} [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
  [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (inh : Inhabitants S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (glb : Head → Head → Option Head) (spec : ∀ {a b g : Head}, glb a b = some g → IsGlb S.R g a b)

include algebra in
theorem solveRound_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {qs : List Head} {d : Head} {universes : AllUniverses S.R qs} {hd : S.R.isUniverse d}
    {X Y : Fin Θ.arity} {psX psY : List Head} {cX cY : Head} {imgX : Fin psX.length → Fin qs.length}
    {imgY : Fin psY.length → Fin qs.length} {declX : Ctx.lookup Θ.raw X = famCode psX cX}
    {declY : Ctx.lookup Θ.raw Y = famCode psY cY} {injX : Function.Injective imgX}
    {injY : Function.Injective imgY}
    {domX : ∀ j, psX.get j = qs.get (imgX j)} {domY : ∀ j, psY.get j = qs.get (imgY j)}
    {belowX : S.R.cumulative cX d} {ne : Y ≠ X} {cover : ∀ i, ∃ j, imgX j = imgY i}
    {codomains : S.R.cumulative cY cX} {occX : X ∈ occ (e :: rest)} {occY : Y ∈ occ (e :: rest)}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs psY imgY) (opened psY (f.substitution Y)))
        (Presentation.rename (sideRen qs psX imgX) (opened psX (f.substitution X))) (.head d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : MixedStore choices (e :: rest))
    (progressed : solveRound facts roots heads algebra rigid complete inh rest families universes hd imgX imgY declX
      declY injX injY domX domY belowX ne cover codomains occX occY opens = .progress update smaller) :
    MixedStore choices update.remaining := by
  unfold solveRound at progressed
  cases progressed
  have domσ : ∀ i, psY.get i = psX.get (solveMap imgX imgY cover i) := fun i => by
    rw [domX (solveMap imgX imgY cover i), solveMap_spec imgX imgY cover i, domY i]
  have injσ : Function.Injective (solveMap imgX imgY cover) := by
    intro a b same
    apply injY
    rw [← solveMap_spec imgX imgY cover a, ← solveMap_spec imgX imgY cover b, same]
  have declY' : Ctx.lookup (setFamAt Θ.raw X psX cX) Y = famCode psY cY := by
    rw [lookup_setFamAt_ne Θ.raw X Y psX cX ne, declY]
  refine mixed_value choices inside X declX _ _
    (flex_shape algebra (redecl Θ inside.families X psX cX (famFacts inside.families declX).1
      (famFacts inside.families declX).2) psX cX Y (solveMap imgX imgY cover) declY' injσ domσ codomains) ?_
  intro nil
  subst nil
  have emptyY : psY = [] := List.eq_nil_of_length_eq_zero (by
    by_contra pos
    obtain ⟨j, _⟩ := cover ⟨0, Nat.pos_of_ne_zero pos⟩
    exact j.elim0)
  subst emptyY
  exact ⟨Y, cY, rfl, declY', (famFacts inside.families declY).2⟩

include algebra in
theorem stepFlexLocal_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {qs : List Head} {d : Head} {universes : AllUniverses S.R qs} {hd : S.R.isUniverse d}
    {X : Fin Θ.arity} {ps : List Head} {c : Head} {img : Fin ps.length → Fin qs.length}
    {declared : Ctx.lookup Θ.raw X = famCode ps c} {injective : Function.Injective img}
    {domains : ∀ j, ps.get j = qs.get (img j)} {below : S.R.cumulative c d} {l : Fin qs.length}
    {occurs : X ∈ occ (e :: rest)}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw qs) (Presentation.rename (sideRen qs ps img) (opened ps (f.substitution X)))
        (.var (loc qs l)) (.head d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : MixedStore choices (e :: rest))
    (progressed : stepFlexLocal facts roots heads algebra rigid complete inh rest families universes hd img declared
      injective domains below l occurs opens = .progress update smaller) :
    MixedStore choices update.remaining := by
  unfold stepFlexLocal at progressed
  split at progressed
  · rename_i j _
    split at progressed
    · rename_i hfit
      cases progressed
      refine mixed_value choices inside X declared _ _
        (project_shape algebra (redecl Θ inside.families X ps c (famFacts inside.families declared).1
          (famFacts inside.families declared).2) ps c j hfit) ?_
      intro nil
      subst nil
      exact j.elim0
    · cases progressed
  · cases progressed

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative] in
theorem stepLocals_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {v : EqView (S := S) e} {l m : Fin v.qs.length} {sl : e.1.2.code = localSide v.qs l}
    {bl : S.R.cumulative (v.qs.get l) v.d} {sm : e.2.2.code = localSide v.qs m}
    {bm : S.R.cumulative (v.qs.get m) v.d}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : MixedStore choices (e :: rest))
    (progressed : stepLocals rigid complete rest v l m sl bl sm bm = .progress update smaller) :
    MixedStore choices update.remaining := by
  unfold stepLocals at progressed
  split at progressed
  · cases progressed
    exact inside.tail
  · cases progressed

include algebra in
theorem stepFlexFlex_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {opens : ∀ {Δ : Context S.R} (f : Δ ⟶ Θ), (frames S.levels).Models f (e :: rest) →
      Equal S.R (ctx Δ.raw v.qs) (Presentation.rename (sideRen v.qs D₁.ps D₁.img) (opened D₁.ps (f.substitution D₁.unknown)))
        (Presentation.rename (sideRen v.qs D₂.ps D₂.img) (opened D₂.ps (f.substitution D₂.unknown))) (.head v.d)}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : MixedStore choices (e :: rest))
    (progressed : stepFlexFlex facts roots heads algebra rigid complete normalizes inh rest families v D₁ b₁ D₂ b₂
      opens = .progress update smaller) :
    MixedStore choices update.remaining := by
  unfold stepFlexFlex at progressed
  split_ifs at progressed with hcode hF hcov₁ hcov₂ hc hc'
  · cases progressed
    exact inside.tail
  · unfold pruneRound at progressed
    cases progressed
    exact mixed_prune choices algebra inside _ _ _ ((List.nodup_finRange _).filter _)
  · exact solveRound_mixed choices facts roots heads algebra rigid complete inh inside progressed
  · exact solveRound_mixed choices facts roots heads algebra rigid complete inh
      (opens := fun f solved => (opens f solved).symm) inside progressed
  · unfold pruneRound at progressed
    cases progressed
    exact mixed_prune choices algebra inside _ _ _ ((List.nodup_finRange _).filter _)
  · unfold pruneRound at progressed
    cases progressed
    exact mixed_prune choices algebra inside _ _ _ ((List.nodup_finRange _).filter _)

include algebra in
theorem stepView_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : MixedStore choices (e :: rest))
    (progressed : stepView facts roots heads algebra rigid complete normalizes inh rest families v =
      .progress update smaller) :
    MixedStore choices update.remaining := by
  unfold stepView at progressed
  split at progressed
  · exact stepLocals_mixed choices rigid complete inside progressed
  · exact stepFlexLocal_mixed choices facts roots heads algebra rigid complete inh inside progressed
  · exact stepFlexLocal_mixed choices facts roots heads algebra rigid complete inh inside progressed
  · exact stepFlexFlex_mixed choices facts roots heads algebra rigid complete normalizes inh inside progressed

include algebra in
theorem glbSolveRound_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e} {D₁ : FlexData Θ.raw v.qs e.1.2.code}
    {b₁ : S.R.cumulative D₁.c v.d} {D₂ : FlexData Θ.raw v.qs e.2.2.code} {b₂ : S.R.cumulative D₂.c v.d}
    {hl : v.left = .flex D₁ b₁} {hr : v.right = .flex D₂ b₂} {g : Head} {isGlb : IsGlb S.R g D₁.c D₂.c}
    {ne : D₁.unknown ≠ D₂.unknown} {cover : ∀ i, ∃ j, D₂.img j = D₁.img i}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : MixedStore choices (e :: rest))
    (progressed : glbSolveRound facts roots heads algebra rigid complete inh headTypingUnique rest families v D₁ b₁
      D₂ b₂ hl hr isGlb ne cover = .progress update smaller) :
    MixedStore choices update.remaining := by
  unfold glbSolveRound at progressed
  obtain ⟨u, s, solved, rfl⟩ := roundAfter_progress _ _ progressed
  have lowered : MixedStore choices
      ((frames S.levels).applyStore (millerLowerG families v D₁ D₂ isGlb (fun h => ne h.symm)).hom
        ((frames S.levels).applyStore (millerLowerF families v D₁ D₂.c isGlb).hom (e :: rest))) :=
    mixed_lowered choices algebra _ (mixed_lowered choices algebra _ inside)
  exact solveRound_mixed choices facts roots heads algebra rigid complete inh
    (opens := lowered_opens rest families v D₁ b₁ D₂ b₂ hl hr isGlb ne) lowered solved

include algebra in
theorem stepViewGlb_mixed {Θ : Context S.R} {e : Equation (TotalTerm Θ)} {rest : EquationStore (TotalTerm Θ)}
    {families : Families Θ} {v : EqView (S := S) e}
    {update : Update S.levels (e :: rest)} {smaller : Below (millerRank update.remaining) (millerRank (e :: rest))}
    (inside : MixedStore choices (e :: rest))
    (progressed : stepViewGlb facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec rest
      families v = .progress update smaller) :
    MixedStore choices update.remaining := by
  unfold stepViewGlb at progressed
  split at progressed
  · split at progressed
    · split at progressed
      · exact glbSolveRound_mixed choices facts roots heads algebra rigid complete inh headTypingUnique inside
          progressed
      · cases progressed
    · exact stepView_mixed choices facts roots heads algebra rigid complete normalizes inh inside progressed
  · exact stepView_mixed choices facts roots heads algebra rigid complete normalizes inh inside progressed

/-- **Every progress of the Miller round keeps a mixed store mixed**: the Miller equations stay Miller equations and
the equations between arrow codes stay equations between arrow codes. -/
theorem millerGlbRound_mixed {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}
    {update : Update S.levels problem} {smaller : Below (millerRank update.remaining) (millerRank problem)}
    (inside : MixedStore choices problem)
    (progressed : millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
      problem = .progress update smaller) :
    MixedStore choices update.remaining := by
  cases problem with
  | nil => cases progressed
  | cons e rest =>
      simp only [millerGlbRound] at progressed
      rw [dif_pos inside.families] at progressed
      split at progressed
      · exact stepViewGlb_mixed choices facts roots heads algebra rigid complete normalizes inh headTypingUnique glb
          spec inside progressed
      · cases progressed

/-- **On a mixed store whose first equation is a Miller equation, the Miller round is not stuck**, for a total greatest
lower bound. -/
theorem millerGlbRound_ne_stuck_head
    (total : ∀ {a b : Head}, S.R.isUniverse a → S.R.isUniverse b → ∃ g, glb a b = some g)
    {Γ : Context S.R} {e : Equation (TotalTerm Γ)} {rest : EquationStore (TotalTerm Γ)} (families : Families Γ)
    (view : Nonempty (EqView (S := S) e)) :
    millerGlbRound facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec (e :: rest) ≠
      .stuck := by
  obtain ⟨w⟩ := view
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (readEq_isSome_of_view w)
  simp only [millerGlbRound]
  rw [dif_pos families]
  split
  · exact stepViewGlb_ne_stuck facts roots heads algebra rigid complete normalizes inh headTypingUnique glb spec
      total families _
  · rename_i hnone
    rw [hv] at hnone
    cases hnone

end Rounds

end Miller

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
