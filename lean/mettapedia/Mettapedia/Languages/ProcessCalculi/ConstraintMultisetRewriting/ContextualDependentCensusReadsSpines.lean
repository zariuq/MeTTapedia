import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsPieces

/-!
# Spines of one local are always read along the reducts of the instantiated types

The piece family reads two spines of one bound local through the executable reading `dependentUnderN`, which takes the
reducer's reduct of every instantiated type. R121 covered that census row only where the executable reading succeeds.
Here the row is stated by shape alone and the executable reading is proved complete on it.

* **The shape** (`LocalSpines`): under the same abstractions, two spines of one bound local with equally many
  arguments, at least one, or equal projections of two such spines, at a rigid base type. It has no budget and no
  typing in it.
* **Typing inversion.** A typed spine of a variable at a base type is compared with itself by the algorithmic
  equality, argument by argument; each comparison weak-head reduces the type reached so far to a Π type
  (`SpineArgs`). So every type along a typed spine reduces to a Π type.
* **Completeness of the executable reading** (`tower_argPartsN_reads`). The reading starts from the local's type and
  continues with the normalizer's reduct of each instantiated codomain. A normal type that is joinable with a Π type
  is a Π type (`Join.pi_normal`), its codomain is equal to the one the typing derivation reaches, and the normalizer
  eventually returns the normal reduct of every type; so from some budget on the reading reads every argument, when
  the local's type is normal.
* **The row** (`tower_dependentUnderN_reads`): at a normal annotation, with normal types of the locals read so far,
  typed sides of the shape are read by `dependentUnderN` from some budget on. Hence they have a relational reading
  (`tower_localSpines_rel`), and conversely every relational reading has the shape (`DepRel.localSpines`).

The normality hypothesis is needed: the executable reading takes the local's type literally, so a local whose type
is a redex is not read at any budget, although it has a relational reading
(`ContextualDependentEtaDepth.SpineControls`).
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
open ContextualDependentConstantHeads ContextualDependentMillerClosure ContextualDependentRigidDecomposition
open ContextualDependentConstantHeadsProjections (project readProjection readProjection_project project_generation
  project_neutral spines_project_inv)

/-! ## The shape -/

section Shape

variable {Head : Type}

/-- **Two spines of one bound local under the same abstractions**, with equally many arguments and at least one, or
equal projections of two such spines, at a rigid base type. -/
inductive LocalSpines : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | under {depth n : Nat} {D : Tm Head n} {T l r : Tm Head (n + 1)} :
      LocalSpines (depth + 1) T l r → LocalSpines depth (.pi D T) (.lam l) (.lam r)
  | base {depth n : Nat} {C : Tm Head n} {h : Fin n} {as bs : List (Tm Head n)} :
      rigidBase depth C = true → h.val < depth → as ≠ [] → as.length = bs.length →
      LocalSpines depth C (appSpine (.var h) as) (appSpine (.var h) bs)
  | proj {depth n : Nat} {C : Tm Head n} {h : Fin n} {first : Bool} {as bs : List (Tm Head n)} :
      rigidBase depth C = true → h.val < depth → as ≠ [] → as.length = bs.length →
      LocalSpines depth C (project first (appSpine (.var h) as)) (project first (appSpine (.var h) bs))

/-- The shape at a Π annotation over two abstractions is the shape under the binder. -/
theorem LocalSpines.lam_inv {depth n : Nat} {D : Tm Head n} {T l r : Tm Head (n + 1)}
    (shape : LocalSpines depth (.pi D T) (.lam l) (.lam r)) : LocalSpines (depth + 1) T l r := by
  generalize sameA : Tm.pi D T = annotation at shape
  generalize sameL : Tm.lam l = left at shape
  generalize sameR : Tm.lam r = right at shape
  cases shape with
  | under inner =>
      cases sameA
      cases sameL
      cases sameR
      exact inner
  | base rigidB _ _ _ => exact absurd sameA.symm (rigidBase_not_pi rigidB D T)
  | proj rigidB _ _ _ => exact absurd sameA.symm (rigidBase_not_pi rigidB D T)

/-- **The shape ends at a rigid base type**: an annotation that is not a Π type is a rigid base. -/
theorem LocalSpines.base_rigid {depth n : Nat} {C l r : Tm Head n} (shape : LocalSpines depth C l r)
    (notPi : ∀ D T, C ≠ .pi D T) : rigidBase depth C = true := by
  cases shape with
  | under _ => exact absurd rfl (notPi _ _)
  | base rigidB _ _ _ => exact rigidB
  | proj rigidB _ _ _ => exact rigidB

/-- Two spines of one local bound among the `depth` newest variables, with equally many arguments and at least
one. -/
def sameSpines (depth : Nat) {n : Nat} (l r : Tm Head n) : Bool :=
  match spineOf l, spineOf r with
  | some (h, as), some (h', bs) => decide (h = h' ∧ h.val < depth ∧ 0 < as.length ∧ as.length = bs.length)
  | _, _ => false

/-- Equal projections of two such spines. -/
def sameProjections (depth : Nat) {n : Nat} (l r : Tm Head n) : Bool :=
  match readProjection l, readProjection r with
  | some (first, p), some (first', q) => decide (first = first') && sameSpines depth p q
  | _, _ => false

/-- **The decision of the shape**: it reads the annotation's binders and the two sides, and takes no budget. -/
def localSpinesAt : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Bool
  | depth, _, .pi _ T, .lam l, .lam r => localSpinesAt (depth + 1) T l r
  | depth, _, C, l, r => rigidBase depth C && (sameSpines depth l r || sameProjections depth l r)

theorem localSpinesAt_base (depth : Nat) {n : Nat} {annotation left right : Tm Head n}
    (notUnder : ¬ ∃ D T l r, annotation = .pi D T ∧ left = .lam l ∧ right = .lam r) :
    localSpinesAt depth annotation left right =
      (rigidBase depth annotation && (sameSpines depth left right || sameProjections depth left right)) := by
  cases annotation with
  | pi D T =>
      cases left with
      | lam l =>
          cases right with
          | lam r => exact absurd ⟨D, T, l, r, rfl, rfl, rfl⟩ notUnder
          | _ => rfl
      | _ => rfl
  | _ => rfl

theorem sameSpines_appSpine {depth n : Nat} {h : Fin n} {as bs : List (Tm Head n)} (small : h.val < depth)
    (nonempty : as ≠ []) (same : as.length = bs.length) :
    sameSpines depth (appSpine (.var h) as) (appSpine (.var h) bs) = true := by
  unfold sameSpines
  rw [spineOf_appSpine, spineOf_appSpine]
  exact decide_eq_true ⟨rfl, small, List.length_pos_iff.mpr nonempty, same⟩

/-- **The decision accepts the shape.** -/
theorem LocalSpines.decided {depth n : Nat} {annotation left right : Tm Head n}
    (shape : LocalSpines depth annotation left right) : localSpinesAt depth annotation left right = true := by
  induction shape with
  | under _ ih =>
      simp only [localSpinesAt]
      exact ih
  | base rigidB small nonempty same =>
      rw [localSpinesAt_base _ (fun ⟨D, T, _, _, isPi, _, _⟩ => rigidBase_not_pi rigidB D T isPi), rigidB,
        sameSpines_appSpine small nonempty same]
      rfl
  | @proj depth n C h first as bs rigidB small nonempty same =>
      have projections : sameProjections depth (project first (appSpine (.var h) as))
          (project first (appSpine (.var h) bs)) = true := by
        unfold sameProjections
        rw [readProjection_project, readProjection_project]
        dsimp only
        rw [sameSpines_appSpine small nonempty same, Bool.and_true]
        exact decide_eq_true rfl
      rw [localSpinesAt_base _ (fun ⟨D, T, _, _, isPi, _, _⟩ => rigidBase_not_pi rigidB D T isPi), rigidB,
        projections, Bool.or_true]
      rfl

/-- **Every relational reading has the shape.** -/
theorem DepRel.localSpines {R : Rules Head} {n : Nat} {locals : List (Tm Head n)} {annotation left right : Tm Head n}
    {pieces : List (Piece Head n)} (read : DepRel R locals annotation left right pieces) :
    LocalSpines locals.length annotation left right := by
  induction read with
  | under _ ih =>
      simp only [List.length_cons, List.length_map] at ih
      exact .under ih
  | base rigidB small nonempty _ args =>
      obtain ⟨sameL, sameR⟩ := args.sides
      exact .base rigidB small nonempty (by rw [← sameL, ← sameR, List.length_map, List.length_map])
  | proj rigidB small nonempty _ args =>
      obtain ⟨sameL, sameR⟩ := args.sides
      exact .proj rigidB small nonempty (by rw [← sameL, ← sameR, List.length_map, List.length_map])

end Shape

/-! ## Typing inversion along a spine -/

section Inversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem SpineArgs.cons_inv {n : Nat} {Γ : Ctx Head n} {T a b U : Tm Head n} {as bs : List (Tm Head n)}
    (args : SpineArgs S Γ T (a :: as) (b :: bs) U) :
    ∃ (A : Tm Head n) (B : Tm Head (n + 1)), RedTy S.R S.roles Γ T (.pi A B) ∧
      Algorithmic S.R S.roles (.terms Γ a b A) ∧ SpineArgs S Γ (inst0 a B) as bs U := by
  cases args with
  | cons red terms others => exact ⟨_, _, red, terms, others⟩

variable (complete : AlgorithmicComplete S.R S.roles)

include complete in
/-- **A typed spine of a variable at a base type is read argument by argument**, each type along it weak-head reducing
to a Π type. -/
theorem spineArgs_of_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n)
    {as : List (Tm Head n)} {C : Tm Head n} (base : BaseType S C) (nonempty : as ≠ [])
    (typed : TypedEquality.Typed S.R Γ (appSpine (.var h) as) C) :
    ∃ U, SpineArgs S Γ (Ctx.lookup Γ h) as as U := by
  obtain ⟨U, spines⟩ := terms_spine_inv h base nonempty rfl (complete formed (.refl typed))
  exact ⟨U, spines_inv (S := S) h as as rfl spines⟩

include complete in
/-- **A typed projection of a spine of a variable at a base type** reads its spine the same way. -/
theorem spineArgs_of_projection {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) (h : Fin n) (first : Bool)
    {as : List (Tm Head n)} {C : Tm Head n} (base : BaseType S C)
    (typed : TypedEquality.Typed S.R Γ (project first (appSpine (.var h) as)) C) :
    ∃ U, SpineArgs S Γ (Ctx.lookup Γ h) as as U := by
  obtain ⟨U, spines⟩ := ContextualDependentFragmentDecisive.terms_neutral_spines base
    (project_neutral first (neutral_appSpine h as)) (project_neutral first (neutral_appSpine h as))
    (complete formed (.refl typed))
  obtain ⟨U', prefixSpines⟩ := spines_project_inv first spines
  exact ⟨U', spines_inv (S := S) h as as rfl prefixSpines⟩

end Inversion

/-! ## The tower: completeness of the executable reading -/

section Tower

open ContextualDependentIntersectionGeneral.DeadControls ContextualDependentPatternFiring.Controls
open ContextualDependentAcceptance4
open ContextualDependentExecutableJoin (Star Normal Join confluent star_inst0)

/-- **The tower's reducer eventually returns one normal reduct of every type**, equal to it. -/
theorem tower_normalCode_eventually {n : Nat} {Γ : Ctx (LevelTower.Head Nat) n} (formed : CtxFormed setting.R Γ)
    {code : Tower.Tm n} (isType : IsType setting.R Γ code) :
    ∃ (bound : Nat) (N : Tower.Tm n), Normal setting.R N ∧ Star (R := setting.R) code N ∧
      TypeEq setting.R Γ code N ∧
      ∀ larger, bound ≤ larger → normalCode ContextualDependentInversion.Controls.reducer larger code = N := by
  obtain ⟨f₁, result, normal, steps, stable₁⟩ :=
    ContextualDependentExecutableConversion.red_eventually_type (L := Nat) formed isType
  have reduced : ∀ larger, f₁ ≤ larger →
      normalCode ContextualDependentInversion.Controls.reducer larger code = result.val := by
    intro larger enough
    unfold normalCode
    rw [show ContextualDependentInversion.Controls.reducer larger code = some result from stable₁ larger enough]
    rfl
  have equal := normalCode_typeEq (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
    ContextualDependentInversion.Controls.reducer f₁ formed isType
  rw [reduced f₁ le_rfl] at equal
  exact ⟨f₁, result.val, normal, steps, equal, reduced⟩

/-- **The executable reading along reducts reads every argument of two typed spines**, from some budget on, when it
starts from normal reducts of the two head types. -/
theorem tower_argPartsN_reads {n : Nat} {Γ : Ctx (LevelTower.Head Nat) n} (formed : CtxFormed setting.R Γ) :
    ∀ (as bs : List (Tower.Tm n)) {TL TR NL NR UL UR : Tower.Tm n},
      SpineArgs setting Γ TL as as UL → SpineArgs setting Γ TR bs bs UR → as.length = bs.length →
      Star (R := setting.R) TL NL → Normal setting.R NL → TypeEq setting.R Γ TL NL →
      Star (R := setting.R) TR NR → Normal setting.R NR → TypeEq setting.R Γ TR NR →
      ∃ bound, ∀ larger, bound ≤ larger →
        (argPartsN ContextualDependentInversion.Controls.reducer larger NL NR as bs).isSome
  | [], [], _, _, NL, NR, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨0, fun larger _ => by rw [argPartsN_nil]; rfl⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, length, _, _, _, _, _, _ => by simp at length
  | _ :: _, [], _, _, _, _, _, _, _, _, length, _, _, _, _, _, _ => by simp at length
  | a :: as, b :: bs, TL, TR, NL, NR, UL, UR, left, right, length, toNL, normalL, eqL, toNR, normalR, eqR => by
      have empty : setting.R.computation = RootComputation.empty := rfl
      obtain ⟨A, B, redL, termsL, restL⟩ := SpineArgs.cons_inv left
      obtain ⟨A', B', redR, termsR, restR⟩ := SpineArgs.cons_inv right
      obtain ⟨dL, fromPiL, fromNL⟩ := confluent empty
        (ContextualDependentExecutableConversion.whRed_star (L := Nat) redL.red) toNL
      obtain ⟨A₁, B₁, rfl, _, toB₁⟩ := Join.pi_normal empty ⟨dL, fromPiL, fromNL⟩ normalL
      obtain ⟨dR, fromPiR, fromNR⟩ := confluent empty
        (ContextualDependentExecutableConversion.whRed_star (L := Nat) redR.red) toNR
      obtain ⟨A₂, B₂, rfl, _, toB₂⟩ := Join.pi_normal empty ⟨dR, fromPiR, fromNR⟩ normalR
      -- the left codomain
      obtain ⟨_, codL⟩ := (ContextualDependentRigid.typeEq_pi_iff TowerModel.facts formed).mp
        (TypeEq.trans setting.levels (TypeEq.symm (RedTy.typeEq redL)) eqL)
      have ta : TypedEquality.Typed setting.R Γ a A := (Equal.typed (Algorithmic.sound_terms TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra formed termsL) formed).1
      have nextL : TypeEq setting.R Γ (inst0 a B) (inst0 a B₁) := TypeEq.instantiate codL ta
      obtain ⟨fL, ML, normalML, toML, eqML, constL⟩ :=
        tower_normalCode_eventually formed (isType_of_typeEq formed nextL)
      -- the right codomain
      obtain ⟨_, codR⟩ := (ContextualDependentRigid.typeEq_pi_iff TowerModel.facts formed).mp
        (TypeEq.trans setting.levels (TypeEq.symm (RedTy.typeEq redR)) eqR)
      have tb : TypedEquality.Typed setting.R Γ b A' := (Equal.typed (Algorithmic.sound_terms TowerModel.facts
        TowerModel.roots TowerModel.heads TowerModel.algebra formed termsR) formed).1
      have nextR : TypeEq setting.R Γ (inst0 b B') (inst0 b B₂) := TypeEq.instantiate codR tb
      obtain ⟨fR, MR, normalMR, toMR, eqMR, constR⟩ :=
        tower_normalCode_eventually formed (isType_of_typeEq formed nextR)
      obtain ⟨bound, reads⟩ := tower_argPartsN_reads formed as bs restL restR (by simpa using length)
        ((star_inst0 .refl toB₁).trans toML) normalML (TypeEq.trans setting.levels nextL eqML)
        ((star_inst0 .refl toB₂).trans toMR) normalMR (TypeEq.trans setting.levels nextR eqMR)
      refine ⟨max bound (max fL fR), fun larger enough => ?_⟩
      simp only [argPartsN]
      rw [constL larger (((le_max_left _ _).trans (le_max_right _ _)).trans enough),
        constR larger (((le_max_right _ _).trans (le_max_right _ _)).trans enough), Option.isSome_map]
      exact reads larger ((le_max_left _ _).trans enough)

/-- **The row**: at a normal annotation, with normal types of the locals read so far, typed sides that are spines of
one bound local, or equal projections of them, are read along the reducts of the instantiated types from some budget
on. -/
theorem tower_dependentUnderN_reads {depth n : Nat} {annotation left right : Tower.Tm n}
    (shape : LocalSpines depth annotation left right) :
    ∀ {Γ : Ctx (LevelTower.Head Nat) n} {locals : List (Tower.Tm n)}, CtxFormed setting.R Γ →
      LocalTypes Γ locals → locals.length = depth → (∀ T ∈ locals, Normal setting.R T) →
      Normal setting.R annotation → TypedEquality.Typed setting.R Γ left annotation →
      TypedEquality.Typed setting.R Γ right annotation →
      ∃ bound, ∀ larger, bound ≤ larger →
        (dependentUnderN (S := setting) ContextualDependentInversion.Controls.reducer larger locals annotation left
          right).isSome := by
  have empty : setting.R.computation = RootComputation.empty := rfl
  induction shape with
  | @under depth n D T l r _ ih =>
      intro Γ locals formed types length normalLocals normalA tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      obtain ⟨normalD, normalT⟩ := (normal_pi_iff empty).mp normalA
      obtain ⟨bound, reads⟩ := ih (formed.snoc ⟨u, hu, tD⟩) (types.under D)
        (by simp only [List.length_cons, List.length_map, length])
        (fun T' member => by
          rcases List.mem_cons.mp member with rfl | later
          · exact (ContextualDependentNormalizing.normal_rename_iff empty wk D).mpr normalD
          · obtain ⟨T₀, inside, rfl⟩ := List.mem_map.mp later
            exact (ContextualDependentNormalizing.normal_rename_iff empty wk T₀).mpr (normalLocals T₀ inside))
        normalT (Typed.lam_inv TowerModel.facts tl formed) (Typed.lam_inv TowerModel.facts tr formed)
      refine ⟨bound, fun larger enough => ?_⟩
      simp only [dependentUnderN, Option.isSome_map]
      exact reads larger enough
  | @base depth n C h as bs rigidB small nonempty same =>
      intro Γ locals formed types length normalLocals _ tl tr
      subst length
      have looked : locals[h.val]? = some locals[h.val] := List.getElem?_eq_getElem small
      have headType := types.head looked
      have nonemptyR : bs ≠ [] := fun nil => nonempty (List.eq_nil_of_length_eq_zero (by rw [same, nil]; rfl))
      have baseC : BaseType setting C := rigidBase_spec rigidB
      obtain ⟨UL, argsL⟩ := spineArgs_of_typed TowerModel.complete formed h baseC nonempty tl
      obtain ⟨UR, argsR⟩ := spineArgs_of_typed TowerModel.complete formed h baseC nonemptyR tr
      rw [headType] at argsL argsR
      have th : TypedEquality.Typed setting.R Γ (.var h) locals[h.val] := by
        have typedVar : TypedEquality.Typed setting.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have isT := Typed.isType th formed
      have normalT := normalLocals _ (List.getElem_mem small)
      obtain ⟨bound, reads⟩ := tower_argPartsN_reads formed as bs argsL argsR same .refl normalT isT.refl .refl
        normalT isT.refl
      refine ⟨bound, fun larger enough => ?_⟩
      rw [dependentUnderN_base _ _ (fun ⟨D, T, l, r, isPi, _, _⟩ => rigidBase_not_pi rigidB D T isPi)]
      have shaped : baseShape locals C (appSpine (.var h) as) (appSpine (.var h) bs) =
          some (locals[h.val], as, bs) := by
        unfold baseShape
        rw [if_pos rigidB, spineOf_appSpine, spineOf_appSpine]
        dsimp only
        rw [if_pos ⟨rfl, small, List.length_pos_iff.mpr nonempty⟩, looked]
        rfl
      unfold dependentBaseN
      rw [shaped]
      simp only [Option.bind_some, Option.isSome_or, reads larger enough, Bool.true_or]
  | @proj depth n C h first as bs rigidB small nonempty same =>
      intro Γ locals formed types length normalLocals _ tl tr
      subst length
      have looked : locals[h.val]? = some locals[h.val] := List.getElem?_eq_getElem small
      have headType := types.head looked
      have baseC : BaseType setting C := rigidBase_spec rigidB
      obtain ⟨UL, argsL⟩ := spineArgs_of_projection TowerModel.complete formed h first baseC tl
      obtain ⟨UR, argsR⟩ := spineArgs_of_projection TowerModel.complete formed h first baseC tr
      rw [headType] at argsL argsR
      have th : TypedEquality.Typed setting.R Γ (.var h) locals[h.val] := by
        have typedVar : TypedEquality.Typed setting.R Γ (.var h) (Ctx.lookup Γ h) := .var h
        rwa [headType] at typedVar
      have isT := Typed.isType th formed
      have normalT := normalLocals _ (List.getElem_mem small)
      obtain ⟨bound, reads⟩ := tower_argPartsN_reads formed as bs argsL argsR same .refl normalT isT.refl .refl
        normalT isT.refl
      refine ⟨bound, fun larger enough => ?_⟩
      rw [dependentUnderN_base _ _ (fun ⟨D, T, l, r, isPi, _, _⟩ => rigidBase_not_pi rigidB D T isPi)]
      have shaped : projShape locals C (project first (appSpine (.var h) as))
          (project first (appSpine (.var h) bs)) = some (locals[h.val], as, bs) := by
        unfold projShape
        rw [readProjection_project, readProjection_project]
        dsimp only
        rw [if_pos rfl]
        unfold baseShape
        rw [if_pos rigidB, spineOf_appSpine, spineOf_appSpine]
        dsimp only
        rw [if_pos ⟨rfl, small, List.length_pos_iff.mpr nonempty⟩, looked]
        rfl
      unfold dependentBaseN
      rw [shaped]
      simp only [Option.bind_some, Option.isSome_or, reads larger enough, Bool.or_true]

/-- **Typed sides of the shape have a relational reading**, at a normal annotation with normal types of the locals
read so far. -/
theorem tower_localSpines_rel {depth n : Nat} {annotation left right : Tower.Tm n}
    (shape : LocalSpines depth annotation left right) {Γ : Ctx (LevelTower.Head Nat) n}
    {locals : List (Tower.Tm n)} (formed : CtxFormed setting.R Γ) (types : LocalTypes Γ locals)
    (length : locals.length = depth) (normalLocals : ∀ T ∈ locals, Normal setting.R T)
    (normalA : Normal setting.R annotation) (tl : TypedEquality.Typed setting.R Γ left annotation)
    (tr : TypedEquality.Typed setting.R Γ right annotation) :
    ∃ pieces, DepRel setting.R locals annotation left right pieces := by
  obtain ⟨bound, reads⟩ := tower_dependentUnderN_reads shape formed types length normalLocals normalA tl tr
  obtain ⟨pieces, found⟩ := Option.isSome_iff_exists.mp (reads bound le_rfl)
  exact ⟨pieces, dependentUnderN_rel _ bound locals annotation left right found⟩

end Tower

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
