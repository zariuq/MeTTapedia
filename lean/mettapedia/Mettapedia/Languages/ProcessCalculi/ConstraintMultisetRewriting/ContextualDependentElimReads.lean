import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimShape
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimSigma
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsSigma

/-!
# The row of elimination spines is read, and a conditional decision from the rows outside it

**The executable reading is complete on the tower** (`tower_elimPartsN_reads`, `tower_elimsUnderN_reads`). Two typed
elimination spines of one bound local of the same shape are read from some budget on: the reducer eventually returns
the normal form of every type read, and a normal type below a Π type is a Π type (`tower_normal_pi_of_le`), below a
Σ type a Σ type (`tower_normal_sigma_of_le`). Unlike the reading of application spines, no normality of the
annotation or of the locals' types is assumed: the reading normalizes the head's type itself.

**The census row** (`tower_mixedReads_of_elimShape`). A census head whose η-long sides are elimination spines of one
bound local of the same shape, at an annotation whose type under its Π binders is a base type as it stands, is read by
the mixed family from some budget on.

**A conditional decision** (`tower_mixed_decided_of_uncovered`, `tower_elimSigma_decided_of_uncovered`). The mixed
family, and the family above it, decide every store of the dynamic pattern fragment provided every census head of a
constant preparation outside the rows read (`MixedCoveredHead`: the earlier rows, and the row of elimination spines by
shape) is read from some budget on. The hypothesis still holds every pattern row, the rows at a Σ base stated on the
expanded store, and any row not yet named. At the tower it fails: the conclusion would decide `crossStore`, solvable
and without principal answer (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every
store, runs are exact; on `crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentRank ContextualDependentSpinesMany ContextualDependentCoverageReadersHalf
open ContextualDependentConstantHeads ContextualDependentMillerClosure
open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4
open ContextualDependentExecutableJoin (Star Normal)
open ContextualDependentEliminations (Read appStep fstStep sndStep)

/-! ## Normal types below a Π or a Σ type -/

/-- **A normal type below a function type is a function type.** -/
theorem tower_normal_pi_of_le {n : Nat} {Γ : Ctx (LevelTower.Head Nat) n} (formed : CtxFormed setting.R Γ)
    {type domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)} (normal : Normal setting.R type)
    (isType : IsType setting.R Γ type) (isPi : IsType setting.R Γ (.pi domain codomain))
    (le : TypeLe setting.R Γ type (.pi domain codomain)) : ∃ DL EL, type = .pi DL EL := by
  have facts : FormFacts setting.R setting.roles := TowerModel.facts
  obtain ⟨form, red, isForm⟩ := facts.typeForm isType formed
  have same := normal.star_eq (ContextualDependentExecutableConversion.whRed_star (L := Nat) red.red)
  subst same
  obtain ⟨A₀, B₀, equal, _, _⟩ := Below.pi_inv facts (TypeLe.toBelow le isPi) formed (IsType.refl isPi)
  obtain ⟨DL, EL, shape, _, _⟩ := (facts.forms equal.symm formed (.inr (.inl ⟨_, _, rfl⟩)) isForm).pi_left
  exact ⟨DL, EL, shape⟩

/-- **A normal type below a pair type is a pair type.** -/
theorem tower_normal_sigma_of_le {n : Nat} {Γ : Ctx (LevelTower.Head Nat) n} (formed : CtxFormed setting.R Γ)
    {type first : Tower.Tm n} {second : Tower.Tm (n + 1)} (normal : Normal setting.R type)
    (isType : IsType setting.R Γ type) (isSigma : IsType setting.R Γ (.sigma first second))
    (le : TypeLe setting.R Γ type (.sigma first second)) : ∃ AL BL, type = .sigma AL BL := by
  have facts : FormFacts setting.R setting.roles := TowerModel.facts
  obtain ⟨form, red, isForm⟩ := facts.typeForm isType formed
  have same := normal.star_eq (ContextualDependentExecutableConversion.whRed_star (L := Nat) red.red)
  subst same
  obtain ⟨A₀, B₀, equal, _, _⟩ := Below.sigma_inv facts (TypeLe.toBelow le isSigma) formed (IsType.refl isSigma)
  obtain ⟨AL, BL, shape, _, _⟩ :=
    (facts.forms equal.symm formed (.inr (.inr (.inl ⟨_, _, rfl⟩))) isForm).sigma_left
  exact ⟨AL, BL, shape⟩

/-! ## Completeness of the executable reading -/

/-- **The executable reading reads two typed elimination spines of one bound local of the same shape**, from some
budget on, and the types it returns are normal. -/
theorem tower_elimPartsN_reads {n : Nat} {Γ : Ctx (LevelTower.Head Nat) n} (formed : CtxFormed setting.R Γ)
    {locals : List (Tower.Tm n)} (types : LocalTypes Γ locals) {h : Fin n} (small : h.val < locals.length) :
    ∀ (left right : Tower.Tm n) {C C' : Tower.Tm n}, SameSpines h left right →
      TypedEquality.Typed setting.R Γ left C → TypedEquality.Typed setting.R Γ right C' →
      ∃ (bound : Nat) (read : Read (LevelTower.Head Nat) n),
        (∀ larger, bound ≤ larger → elimPartsN (S := setting) ContextualDependentInversion.Controls.reducer larger
          locals left right = some read) ∧ Normal setting.R read.2.1 ∧ Normal setting.R read.2.2
  | .var i, .var j, _, _, ⟨sameLeft, sameRight⟩, _, _ => by
      have looked : locals[h.val]? = some locals[h.val] := List.getElem?_eq_getElem small
      have headType := types.head looked
      have isT : IsType setting.R Γ locals[h.val] := by
        rw [← headType]
        exact Typed.isType (.var h) formed
      obtain ⟨bound, N, normalN, _, _, const⟩ := tower_normalCode_eventually formed isT
      refine ⟨bound, ([], N, N), fun larger enough => ?_, normalN, normalN⟩
      rw [sameLeft, sameRight]
      simp [elimPartsN, looked, const larger enough]
  | .app f a, .app g b, _, _, shape, tl, tr => by
      have facts : FormFacts setting.R setting.roles := TowerModel.facts
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation tl
      obtain ⟨A', B', tg, _, _⟩ := Typed.generation tr
      obtain ⟨bound₁, read₁, const₁, normalL, normalR⟩ := tower_elimPartsN_reads formed types small f g shape tf tg
      obtain ⟨pieces, NL, NR⟩ := read₁
      obtain ⟨h', T, TL, TR, _, looked', rel, redL, redR⟩ :=
        elimPartsN_rel ContextualDependentInversion.Controls.reducer bound₁ locals f g (const₁ bound₁ le_rfl)
      have headType := types.head looked'
      subst headType
      have th : TypedEquality.Typed setting.R Γ (.var h') (Ctx.lookup Γ h') := .var h'
      have principal : ∀ U, TypedEquality.Typed setting.R Γ (.var h') U → TypeLe setting.R Γ (Ctx.lookup Γ h') U :=
        fun U typed => Typed.generation typed
      obtain ⟨tfL, principalF, _⟩ := rel.typed_left facts TowerModel.roots TowerModel.heads formed th principal tf
      obtain ⟨tgR, principalG, _⟩ :=
        rel.swap.typed_left facts TowerModel.roots TowerModel.heads formed th principal tg
      have toNL : TypeEq setting.R Γ TL NL :=
        Reduces.typeEq (S := setting) facts TowerModel.roots TowerModel.heads formed redL (Typed.isType tfL formed)
      have toNR : TypeEq setting.R Γ TR NR :=
        Reduces.typeEq (S := setting) facts TowerModel.roots TowerModel.heads formed redR (Typed.isType tgR formed)
      have leL : TypeLe setting.R Γ NL (.pi A B) := by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toNL
        exact .conv e hu (principalF _ tf)
      have leR : TypeLe setting.R Γ NR (.pi A' B') := by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toNR
        exact .conv e hu (principalG _ tg)
      obtain ⟨DL, EL, rfl⟩ := tower_normal_pi_of_le formed normalL (isType_of_typeEq formed toNL)
        (Typed.isType tf formed) leL
      obtain ⟨DR, ER, rfl⟩ := tower_normal_pi_of_le formed normalR (isType_of_typeEq formed toNR)
        (Typed.isType tg formed) leR
      have extended := ElimRel.app (a := a) (b := b) rel redL redR
      obtain ⟨typedL, _, _⟩ :=
        extended.typed_left facts TowerModel.roots TowerModel.heads formed th principal tl
      obtain ⟨typedR, _, _⟩ :=
        extended.swap.typed_left facts TowerModel.roots TowerModel.heads formed th principal tr
      obtain ⟨bL, ML, normalML, _, _, constL⟩ := tower_normalCode_eventually formed (Typed.isType typedL formed)
      obtain ⟨bR, MR, normalMR, _, _, constR⟩ := tower_normalCode_eventually formed (Typed.isType typedR formed)
      refine ⟨max bound₁ (max bL bR), (pieces ++ [⟨DL, a, DR, b⟩], ML, MR), fun larger enough => ?_, normalML,
        normalMR⟩
      simp only [elimPartsN]
      rw [const₁ larger ((le_max_left _ _).trans enough)]
      simp [appStep, normalRead, constL larger (((le_max_left _ _).trans (le_max_right _ _)).trans enough),
        constR larger (((le_max_right _ _).trans (le_max_right _ _)).trans enough)]
  | .fst p, .fst q, _, _, shape, tl, tr => by
      have facts : FormFacts setting.R setting.roles := TowerModel.facts
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨A', B', tq, _⟩ := Typed.generation tr
      obtain ⟨bound₁, read₁, const₁, normalL, normalR⟩ := tower_elimPartsN_reads formed types small p q shape tp tq
      obtain ⟨pieces, NL, NR⟩ := read₁
      obtain ⟨h', T, TL, TR, _, looked', rel, redL, redR⟩ :=
        elimPartsN_rel ContextualDependentInversion.Controls.reducer bound₁ locals p q (const₁ bound₁ le_rfl)
      have headType := types.head looked'
      subst headType
      have th : TypedEquality.Typed setting.R Γ (.var h') (Ctx.lookup Γ h') := .var h'
      have principal : ∀ U, TypedEquality.Typed setting.R Γ (.var h') U → TypeLe setting.R Γ (Ctx.lookup Γ h') U :=
        fun U typed => Typed.generation typed
      obtain ⟨tpL, principalP, _⟩ := rel.typed_left facts TowerModel.roots TowerModel.heads formed th principal tp
      obtain ⟨tqR, principalQ, _⟩ :=
        rel.swap.typed_left facts TowerModel.roots TowerModel.heads formed th principal tq
      have toNL : TypeEq setting.R Γ TL NL :=
        Reduces.typeEq (S := setting) facts TowerModel.roots TowerModel.heads formed redL (Typed.isType tpL formed)
      have toNR : TypeEq setting.R Γ TR NR :=
        Reduces.typeEq (S := setting) facts TowerModel.roots TowerModel.heads formed redR (Typed.isType tqR formed)
      have leL : TypeLe setting.R Γ NL (.sigma A B) := by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toNL
        exact .conv e hu (principalP _ tp)
      have leR : TypeLe setting.R Γ NR (.sigma A' B') := by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toNR
        exact .conv e hu (principalQ _ tq)
      obtain ⟨AL, BL, rfl⟩ := tower_normal_sigma_of_le formed normalL (isType_of_typeEq formed toNL)
        (Typed.isType tp formed) leL
      obtain ⟨AR, BR, rfl⟩ := tower_normal_sigma_of_le formed normalR (isType_of_typeEq formed toNR)
        (Typed.isType tq formed) leR
      have extended := ElimRel.fst rel redL redR
      obtain ⟨typedL, _, _⟩ :=
        extended.typed_left facts TowerModel.roots TowerModel.heads formed th principal tl
      obtain ⟨typedR, _, _⟩ :=
        extended.swap.typed_left facts TowerModel.roots TowerModel.heads formed th principal tr
      obtain ⟨bL, ML, normalML, _, _, constL⟩ := tower_normalCode_eventually formed (Typed.isType typedL formed)
      obtain ⟨bR, MR, normalMR, _, _, constR⟩ := tower_normalCode_eventually formed (Typed.isType typedR formed)
      refine ⟨max bound₁ (max bL bR), (pieces, ML, MR), fun larger enough => ?_, normalML, normalMR⟩
      simp only [elimPartsN]
      rw [const₁ larger ((le_max_left _ _).trans enough)]
      simp [fstStep, normalRead, constL larger (((le_max_left _ _).trans (le_max_right _ _)).trans enough),
        constR larger (((le_max_right _ _).trans (le_max_right _ _)).trans enough)]
  | .snd p, .snd q, _, _, shape, tl, tr => by
      have facts : FormFacts setting.R setting.roles := TowerModel.facts
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨A', B', tq, _⟩ := Typed.generation tr
      obtain ⟨bound₁, read₁, const₁, normalL, normalR⟩ := tower_elimPartsN_reads formed types small p q shape tp tq
      obtain ⟨pieces, NL, NR⟩ := read₁
      obtain ⟨h', T, TL, TR, _, looked', rel, redL, redR⟩ :=
        elimPartsN_rel ContextualDependentInversion.Controls.reducer bound₁ locals p q (const₁ bound₁ le_rfl)
      have headType := types.head looked'
      subst headType
      have th : TypedEquality.Typed setting.R Γ (.var h') (Ctx.lookup Γ h') := .var h'
      have principal : ∀ U, TypedEquality.Typed setting.R Γ (.var h') U → TypeLe setting.R Γ (Ctx.lookup Γ h') U :=
        fun U typed => Typed.generation typed
      obtain ⟨tpL, principalP, _⟩ := rel.typed_left facts TowerModel.roots TowerModel.heads formed th principal tp
      obtain ⟨tqR, principalQ, _⟩ :=
        rel.swap.typed_left facts TowerModel.roots TowerModel.heads formed th principal tq
      have toNL : TypeEq setting.R Γ TL NL :=
        Reduces.typeEq (S := setting) facts TowerModel.roots TowerModel.heads formed redL (Typed.isType tpL formed)
      have toNR : TypeEq setting.R Γ TR NR :=
        Reduces.typeEq (S := setting) facts TowerModel.roots TowerModel.heads formed redR (Typed.isType tqR formed)
      have leL : TypeLe setting.R Γ NL (.sigma A B) := by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toNL
        exact .conv e hu (principalP _ tp)
      have leR : TypeLe setting.R Γ NR (.sigma A' B') := by
        obtain ⟨u, hu, e⟩ := TypeEq.symm toNR
        exact .conv e hu (principalQ _ tq)
      obtain ⟨AL, BL, rfl⟩ := tower_normal_sigma_of_le formed normalL (isType_of_typeEq formed toNL)
        (Typed.isType tp formed) leL
      obtain ⟨AR, BR, rfl⟩ := tower_normal_sigma_of_le formed normalR (isType_of_typeEq formed toNR)
        (Typed.isType tq formed) leR
      have extended := ElimRel.snd rel redL redR
      obtain ⟨typedL, _, _⟩ :=
        extended.typed_left facts TowerModel.roots TowerModel.heads formed th principal tl
      obtain ⟨typedR, _, _⟩ :=
        extended.swap.typed_left facts TowerModel.roots TowerModel.heads formed th principal tr
      obtain ⟨bL, ML, normalML, _, _, constL⟩ := tower_normalCode_eventually formed (Typed.isType typedL formed)
      obtain ⟨bR, MR, normalMR, _, _, constR⟩ := tower_normalCode_eventually formed (Typed.isType typedR formed)
      refine ⟨max bound₁ (max bL bR), (pieces, ML, MR), fun larger enough => ?_, normalML, normalMR⟩
      simp only [elimPartsN]
      rw [const₁ larger ((le_max_left _ _).trans enough)]
      simp [sndStep, normalRead, constL larger (((le_max_left _ _).trans (le_max_right _ _)).trans enough),
        constR larger (((le_max_right _ _).trans (le_max_right _ _)).trans enough)]
  | .var _, .const _, _, _, shape, _, _ | .var _, .head _, _, _, shape, _, _ | .var _, .pi _ _, _, _, shape, _, _
  | .var _, .sigma _ _, _, _, shape, _, _ | .var _, .id _ _ _, _, _, shape, _, _ | .var _, .lam _, _, _, shape, _, _
  | .var _, .app _ _, _, _, shape, _, _ | .var _, .pair _ _, _, _, shape, _, _ | .var _, .fst _, _, _, shape, _, _
  | .var _, .snd _, _, _, shape, _, _ | .var _, .refl _, _, _, shape, _, _
  | .app _ _, .var _, _, _, shape, _, _ | .app _ _, .const _, _, _, shape, _, _ | .app _ _, .head _, _, _, shape, _, _
  | .app _ _, .pi _ _, _, _, shape, _, _ | .app _ _, .sigma _ _, _, _, shape, _, _
  | .app _ _, .id _ _ _, _, _, shape, _, _ | .app _ _, .lam _, _, _, shape, _, _
  | .app _ _, .pair _ _, _, _, shape, _, _ | .app _ _, .fst _, _, _, shape, _, _
  | .app _ _, .snd _, _, _, shape, _, _ | .app _ _, .refl _, _, _, shape, _, _
  | .fst _, .var _, _, _, shape, _, _ | .fst _, .const _, _, _, shape, _, _ | .fst _, .head _, _, _, shape, _, _
  | .fst _, .pi _ _, _, _, shape, _, _ | .fst _, .sigma _ _, _, _, shape, _, _
  | .fst _, .id _ _ _, _, _, shape, _, _ | .fst _, .lam _, _, _, shape, _, _ | .fst _, .app _ _, _, _, shape, _, _
  | .fst _, .pair _ _, _, _, shape, _, _ | .fst _, .snd _, _, _, shape, _, _ | .fst _, .refl _, _, _, shape, _, _
  | .snd _, .var _, _, _, shape, _, _ | .snd _, .const _, _, _, shape, _, _ | .snd _, .head _, _, _, shape, _, _
  | .snd _, .pi _ _, _, _, shape, _, _ | .snd _, .sigma _ _, _, _, shape, _, _
  | .snd _, .id _ _ _, _, _, shape, _, _ | .snd _, .lam _, _, _, shape, _, _ | .snd _, .app _ _, _, _, shape, _, _
  | .snd _, .pair _ _, _, _, shape, _, _ | .snd _, .fst _, _, _, shape, _, _ | .snd _, .refl _, _, _, shape, _, _
  | .const _, _, _, _, shape, _, _ | .head _, _, _, _, shape, _, _ | .pi _ _, _, _, _, shape, _, _
  | .sigma _ _, _, _, _, shape, _, _ | .id _ _ _, _, _, _, shape, _, _ | .lam _, _, _, _, shape, _, _
  | .pair _ _, _, _, _, shape, _, _ | .refl _, _, _, _, shape, _, _ => by
      simp [SameSpines] at shape

/-- **The row of elimination spines is read**: typed sides that are elimination spines of one bound local of the same
shape, at a base type as it stands, are read along the reducts of the types read from some budget on. -/
theorem tower_elimsUnderN_reads {depth n : Nat} {annotation left right : Tower.Tm n}
    (shape : ElimShape depth annotation left right) :
    ∀ {Γ : Ctx (LevelTower.Head Nat) n} {locals : List (Tower.Tm n)}, CtxFormed setting.R Γ →
      LocalTypes Γ locals → locals.length = depth → TypedEquality.Typed setting.R Γ left annotation →
      TypedEquality.Typed setting.R Γ right annotation →
      ∃ bound, ∀ larger, bound ≤ larger →
        (elimsUnderN (S := setting) ContextualDependentInversion.Controls.reducer larger locals annotation left
          right).isSome := by
  induction shape with
  | @under depth n D T l r _ ih =>
      intro Γ locals formed types length tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      obtain ⟨bound, reads⟩ := ih (formed.snoc ⟨u, hu, tD⟩) (types.under D)
        (by simp only [List.length_cons, List.length_map, length])
        (Typed.lam_inv TowerModel.facts tl formed) (Typed.lam_inv TowerModel.facts tr formed)
      refine ⟨bound, fun larger enough => ?_⟩
      simp only [elimsUnderN, Option.isSome_map]
      exact reads larger enough
  | @base depth n C left right h based small spines =>
      intro Γ locals formed types length tl tr
      have inside : h.val < locals.length := by omega
      obtain ⟨bound, read, const, _, _⟩ := tower_elimPartsN_reads formed types inside left right spines tl tr
      have notUnder : ¬ ∃ D T l r, C = .pi D T ∧ left = .lam l ∧ right = .lam r := by
        rintro ⟨D, T, l, r, rfl, rfl, rfl⟩
        simp [SameSpines] at spines
      refine ⟨bound, fun larger enough => ?_⟩
      rw [elimsUnderN_base _ larger notUnder]
      simp [elimBaseN, based, const larger enough]

/-! ## The census row -/

/-- **A store is read by the mixed family** from some budget on, when an equation of its η-long prepared store with
homogeneous twins, at one budget past the twins' constancy, is eventually read by the decomposition between
elimination spines. -/
theorem tower_mixedReads_of_fixed {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPreparedTwins larger problem = towerPreparedTwins threshold problem)
    {equation : Equation (TotalTerm (towerPreparedTwins threshold problem).target)}
    (member : equation ∈ expandStore TowerModel.facts (towerPreparedTwins threshold problem).remaining)
    {bound : Nat}
    (read : ∀ larger, bound ≤ larger → (mixedNormal (S := setting) TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices larger equation).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerMixedReads larger problem := by
  refine ⟨max threshold bound, fun larger enough => Or.inr ?_⟩
  change (decomposeMixed (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices larger
    (expandStore TowerModel.facts (towerPreparedTwins larger problem).remaining)).isSome
  rw [constant larger ((le_max_left _ _).trans enough)]
  exact decomposeMixed_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete ContextualDependentInversion.Controls.reducer
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices larger member
    (read larger ((le_max_right _ _).trans enough))

/-- **A census head whose η-long sides are eventually read as elimination spines of one local at a base type is
read** by the mixed family from some budget on. -/
theorem tower_mixedReads_of_elims {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (split : ∃ bound, ∀ larger, bound ≤ larger → (elimsUnderN (S := setting)
      ContextualDependentInversion.Controls.reducer larger [] equation.1.1.code
      (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)).isSome) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerMixedReads larger problem := by
  obtain ⟨bound, twins⟩ := tower_twins_keep constant member types
    (fun A l r => ∃ bound, ∀ larger, bound ≤ larger → (elimsUnderN (S := setting)
      ContextualDependentInversion.Controls.reducer larger [] A (expandTo (piCount A) l)
      (expandTo (piCount A) r)).isSome) split
  obtain ⟨settled, twinsConst⟩ := tower_preparedTwins_const problem
  have fixed := twinsConst (max bound settled) (le_max_right _ _)
  have kept : ∀ larger, max bound settled ≤ larger →
      towerPreparedTwins larger problem = towerPreparedTwins (max bound settled) problem := fun larger enough =>
    (twinsConst larger ((le_max_right _ _).trans enough)).trans fixed.symm
  obtain ⟨twin, twinMember, same, readBound, twinRead⟩ := twins (max bound settled) (le_max_left _ _)
  have expandedMember := longUpdate_mem (S := setting) TowerModel.facts twinMember
  have sameExpanded : (expandSide TowerModel.facts twin.2).1.code = (expandSide TowerModel.facts twin.1).1.code := same
  have rightCode : (expandSide TowerModel.facts twin.2).2.code = expandTo (piCount twin.1.1.code) twin.2.2.code := by
    change expandTo (piCount twin.2.1.code) twin.2.2.code = _
    rw [same]
  obtain ⟨settledRead, readConst⟩ := (readElims_const (S := setting) ContextualDependentInversion.Controls.reducer
    ContextualDependentDecisiveFragment.Controls.stable (expandSide TowerModel.facts twin.1).1.code
    (expandSide TowerModel.facts twin.1).2.code (expandSide TowerModel.facts twin.2).2.code).spec
  have readAt : (readElims (S := setting) ContextualDependentInversion.Controls.reducer (max settledRead readBound)
      (expandSide TowerModel.facts twin.1).1.code (expandSide TowerModel.facts twin.1).2.code
      (expandSide TowerModel.facts twin.2).2.code).isSome := by
    rw [← Option.isSome_map (f := Subtype.val), readElims_val, rightCode]
    exact twinRead _ (le_max_right _ _)
  obtain ⟨read, readComputed⟩ := Option.isSome_iff_exists.mp readAt
  have readKept : ∀ larger, max settledRead readBound ≤ larger →
      readElims (S := setting) ContextualDependentInversion.Controls.reducer larger
        (expandSide TowerModel.facts twin.1).1.code (expandSide TowerModel.facts twin.1).2.code
        (expandSide TowerModel.facts twin.2).2.code = some read := fun larger enough =>
    ((readConst larger ((le_max_left _ _).trans enough)).trans
      (readConst _ (le_max_left _ _)).symm).trans readComputed
  have typed := read.property.typed TowerModel.facts TowerModel.roots TowerModel.heads
    (towerPreparedTwins (max bound settled) problem).target.formed (LocalTypes.nil _)
    (expandSide TowerModel.facts twin.1).2.typed
    (by have tr := (expandSide TowerModel.facts twin.2).2.typed; rw [sameExpanded] at tr; exact tr)
  obtain ⟨formedBound, formed⟩ := tower_formNormal_eventually read.val typed
  exact tower_mixedReads_of_fixed kept expandedMember (bound := max (max settledRead readBound) formedBound)
    fun larger enough =>
    mixedNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra ContextualDependentPiSpine.Controls.rigid TowerModel.complete
      ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
      ExecutableTowerChoices.choices larger sameExpanded (readKept larger ((le_max_left _ _).trans enough))
      fun typed' =>
        formNormal_isSome (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
          ContextualDependentPiSpine.Controls.rigid TowerModel.complete
          ContextualDependentInversion.Controls.reducer ContextualDependentInversion.Controls.declarations_formed
          ExecutableTowerChoices.choices larger read.val typed'
          (formed larger ((le_max_right _ _).trans enough))

/-- **The row of elimination spines at every base type is read**: a census head whose η-long sides are elimination
spines of one bound local of the same shape, at an annotation whose type under its Π binders is a base type as it
stands, is read by the mixed family from some budget on. -/
theorem tower_mixedReads_of_elimShape {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (shape : ElimShape 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerMixedReads larger problem :=
  tower_mixedReads_of_elims constant member types
    (tower_elimsUnderN_reads shape (towerPrepare threshold problem).target.formed (LocalTypes.nil _) rfl
      (expanded_typed equation types).1 (expanded_typed equation types).2)

/-! ## A conditional decision, from the census rows outside the rows read -/

/-- **The census rows read by the mixed family**: the rows read by the base family, and elimination spines of one
bound local of the same shape at every base type. -/
def MixedCoveredHead {Γ : Context setting.R} (equation : Equation (TotalTerm Γ)) : Prop :=
  CensusCoveredHead equation ∨
    ElimShape 0 equation.1.1.code (expandTo (piCount equation.1.1.code) equation.1.2.code)
      (expandTo (piCount equation.1.1.code) equation.2.2.code)

/-- **A census head in a row read is read** by the mixed family from some budget on. -/
theorem tower_mixedReads_of_covered {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)}
    {threshold : Nat}
    (constant : ∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem)
    {equation : Equation (TotalTerm (towerPrepare threshold problem).target)}
    (member : equation ∈ (towerPrepare threshold problem).remaining)
    (normal : ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation)
    (types : TypeEq setting.R (towerPrepare threshold problem).target.raw equation.1.1.code equation.2.1.code)
    (covered : MixedCoveredHead equation) :
    ∃ bound, ∀ larger, bound ≤ larger → TowerMixedReads larger problem := by
  rcases covered with census | shape
  · obtain ⟨bound, reads⟩ := tower_baseReads_of_censusCovered constant member normal types census
    exact ⟨bound, fun larger enough => .inl (reads larger enough)⟩
  · exact tower_mixedReads_of_elimShape constant member types shape

/-- **Conditional decision for the tower's mixed family, from the census rows outside the rows read**: if every census
head of a constant preparation whose η-long opened sides are of a census kind and outside the rows read is read from
some budget on, the family decides every store of the dynamic pattern fragment, with a principal answer or a
certified refutation, constant at every larger budget. At the tower the hypothesis fails: the conclusion would decide
`crossStore` (`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`,
`ContextualDependentSweep.Witnesses.acceptance_conclusion_false`). For every store, runs are exact; on `crossStore`
they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_mixed_decided_of_uncovered
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ContextualDependentShortClosure.FragmentSidesMiller equation →
          Kind (openedFlexible (piCount equation.1.1.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.1.2.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.2.2.code)) →
          ¬ MixedCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerMixedReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (mixedTower.solver larger) problem larger = run (mixedTower.solver budget) problem budget ∧
      ((∃ state finished, run (mixedTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (mixedTower.solver larger) problem larger = .refuted absent)) :=
  tower_mixed_decided_of_mixedReads (fun {_} {problem} permuted nonempty => by
      obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
      by_cases covered : MixedCoveredHead equation
      · exact tower_mixedReads_of_covered constant member normal head.1 covered
      · have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
          (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
          TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing threshold problem
          permuted
        have sides := PermutedMiller.sides_of_mem prepared member
        exact uncovered permuted nonempty threshold constant equation member normal head sides
          (eta_kind sides normal.2.1 normal.2.2.2) covered)
    inside

/-- Readers of the tower's family above the mixed family at one budget. -/
abbrev TowerElimSigmaReads (fuel : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Prop :=
  ElimSigmaReads (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer (fun _ => none)
    ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
    ContextualDependentGeneralPattern.DispatchControls.certifyNormal
    ContextualDependentNormalCheckingTower.head_typing_unique
    (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening fuel problem

/-- **Conditional decision for the tower's family above the mixed family, from the census rows outside the rows
read**: if every census head of a constant preparation whose η-long opened sides are of a census kind and outside the
rows read is read by a reader of the family above the mixed family from some budget on, the family decides every store
of the dynamic pattern fragment, with a principal answer or a certified refutation, constant at every larger budget. At
the tower the hypothesis fails: the conclusion would decide `crossStore`
(`ContextualDependentSweep.Witnesses.fragment_without_principal_answer`). For every store, runs are exact; on
`crossStore` they stop postponed (`UnificationWithLevels.DependentFibre.cross_postponed`). -/
theorem tower_elimSigma_decided_of_uncovered
    (uncovered : ∀ {Γ : Context setting.R} {problem : EquationStore (TotalTerm Γ)},
      PermutedMiller setting.levels problem → problem ≠ [] → ∀ threshold,
        (∀ larger, threshold ≤ larger → towerPrepare larger problem = towerPrepare threshold problem) →
        ∀ equation ∈ (towerPrepare threshold problem).remaining,
          ContextualDependentNormalizing.NormalEquation (fun _ => (0 : Nat)) equation → CensusHead equation →
          ContextualDependentShortClosure.FragmentSidesMiller equation →
          Kind (openedFlexible (piCount equation.1.1.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.1.2.code))
            (ContextualDependentCensus.openNormal (piCount equation.1.1.code)
              (expandTo (piCount equation.1.1.code) equation.2.2.code)) →
          ¬ MixedCoveredHead equation → ∃ bound, ∀ larger, bound ≤ larger → TowerElimSigmaReads larger problem)
    {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} (inside : InFragmentStore problem) :
    ∃ budget, ∀ larger, budget ≤ larger →
      run (elimSigmaTower.solver larger) problem larger = run (elimSigmaTower.solver budget) problem budget ∧
      ((∃ state finished, run (elimSigmaTower.solver larger) problem larger = .solved state finished ∧
          (frames setting.levels).Principal problem state.answer) ∨
        (∃ absent, run (elimSigmaTower.solver larger) problem larger = .refuted absent)) :=
  tower_elimSigma_decided_of_firing (fun {_} {problem} permuted nonempty => by
      have reads : ∃ bound, ∀ larger, bound ≤ larger → TowerElimSigmaReads larger problem := by
        obtain ⟨threshold, constant, equation, member, normal, head⟩ := tower_stable_census_head permuted nonempty
        by_cases covered : MixedCoveredHead equation
        · obtain ⟨bound, mixed⟩ := tower_mixedReads_of_covered constant member normal head.1 covered
          exact ⟨bound, fun larger enough => .inl (mixed larger enough)⟩
        · have prepared := ContextualDependentCumulativeClosure.prepare_keeps (S := setting) (fun _ => none)
            (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) TowerModel.facts TowerModel.roots
            TowerModel.heads ContextualDependentPiSpine.Controls.rigid tower_stronglyNormalizing threshold problem
            permuted
          have sides := PermutedMiller.sides_of_mem prepared member
          exact uncovered permuted nonempty threshold constant equation member normal head sides
            (eta_kind sides normal.2.1 normal.2.2.2) covered
      obtain ⟨bound, eventually⟩ := reads
      exact ⟨bound, fun larger enough => elimSigmaRound_not_stuck_of_reads (S := setting) TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra ContextualDependentPiSpine.Controls.rigid
        TowerModel.complete ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
        ContextualDependentInversion.Controls.reducer (fun _ => none)
        ContextualDependentGeneralPattern.DispatchControls.tower_normalizes
        ContextualDependentGeneralPattern.DispatchControls.certifyNormal
        ContextualDependentNormalCheckingTower.head_typing_unique
        (ContextualDependentNormalizing.tower_rootComplete (fun _ => (0 : Nat))) tower_strengthening larger
        (eventually larger enough)⟩)
    inside

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
