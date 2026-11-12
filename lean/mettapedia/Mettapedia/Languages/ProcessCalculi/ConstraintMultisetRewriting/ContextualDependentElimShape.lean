import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentElimRelUnder

/-!
# Typed elimination spines of one shape always have a reading

**The shape** (`SameSpines`, `ElimShape`). Two codes are elimination spines of one variable of the same shape when
they are that variable under the same applications and projections, in the same order; under the same abstractions,
at an annotation whose type under them is a base type as it stands, this is the shape `ElimShape`.

**Typing alone gives the reading** (`ElimRel.of_typed`, `elimSpines_of_shape`). Two typed codes of the shape have a
reading along reducts: at an application the principal type of the prefix is below a Π type, so it reduces to one
(`reduces_pi_of_le`); at a projection it reduces to a Σ type. No budget, no executable and no normality hypothesis is
involved; the reading exists for every typed pair of the shape. Conversely every checked reading has the shape
(`ElimSpines.elimShape`). So the row of elimination spines of one local is a row by shape.

**Controls.** Two different locals do not have the shape, and neither do spines of one local with eliminations of
different shapes (`SameSpines` is `False` there by definition; `sameSpines_shapes`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRank ContextualDependentOccursFull ContextualDependentRigidDecomposition
open ContextualDependentSpinesMany ContextualDependentDecisiveFragment

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## The shape -/

/-- **Two elimination spines of the variable `h` of the same shape.** -/
def SameSpines {n : Nat} (h : Fin n) : Tm Head n → Tm Head n → Prop
  | .var i, .var j => i = h ∧ j = h
  | .app f _, .app g _ => SameSpines h f g
  | .fst p, .fst q => SameSpines h p q
  | .snd p, .snd q => SameSpines h p q
  | _, _ => False

/-- **Two elimination spines of one bound local of the same shape under the same abstractions**, at an annotation
whose type under the abstractions is a base type as it stands. -/
inductive ElimShape {Head : Type} : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | under {depth n : Nat} {D : Tm Head n} {T l r : Tm Head (n + 1)} :
      ElimShape (depth + 1) T l r → ElimShape depth (.pi D T) (.lam l) (.lam r)
  | base {depth n : Nat} {C left right : Tm Head n} {h : Fin n} :
      anyBase C = true → h.val < depth → SameSpines h left right → ElimShape depth C left right

omit [UniverseLevel.LevelOrder L] in
/-- Every reading of two spines of a variable has the shape. -/
theorem ElimRel.sameSpines {R : Rules Head} {n : Nat} {h : Fin n} {type left right TL TR : Tm Head n}
    {pieces : List (Piece Head n)} (read : ElimRel R (.var h) type left right pieces TL TR) :
    SameSpines h left right := by
  induction read with
  | nil => exact ⟨rfl, rfl⟩
  | app _ _ _ ih => exact ih
  | fst _ _ _ ih => exact ih
  | snd _ _ _ ih => exact ih

omit [UniverseLevel.LevelOrder L] in
/-- **Every checked reading has the shape.** -/
theorem ElimSpines.elimShape {R : Rules Head} {n : Nat} {locals : List (Tm Head n)}
    {annotation left right : Tm Head n} {pieces : List (Piece Head n)}
    (read : ElimSpines R true locals annotation left right pieces) :
    ElimShape locals.length annotation left right := by
  induction read with
  | under _ ih =>
      simp only [List.length_cons, List.length_map] at ih
      exact .under ih
  | base based small _ spines => exact .base (based rfl) small spines.sameSpines

/-! ## Typing gives the reading -/

section Theory

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)

include facts in
/-- A type below a function type reduces to a function type. -/
theorem reduces_pi_of_le {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {type domain : Tm Head n} {codomain : Tm Head (n + 1)} (isType : IsType S.R Γ type)
    (isPi : IsType S.R Γ (.pi domain codomain)) (le : TypeLe S.R Γ type (.pi domain codomain)) :
    ∃ DL EL, Reduces S.R type (.pi DL EL) := by
  obtain ⟨form, red, isForm⟩ := facts.typeForm isType formed
  obtain ⟨A₀, B₀, same, _, _⟩ := Below.pi_inv facts (TypeLe.toBelow le isPi) formed (IsType.refl isPi)
  obtain ⟨DL, EL, shape, _, _⟩ := (facts.forms
    (TypeEq.trans S.levels (TypeEq.symm red.typeEq) same).symm formed (.inr (.inl ⟨_, _, rfl⟩)) isForm).pi_left
  subst shape
  exact ⟨DL, EL, red.red.reduces⟩

include facts roots heads in
/-- **Two typed elimination spines of one variable of the same shape have a reading along reducts.** -/
theorem ElimRel.of_typed {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {h : Fin n} :
    ∀ (left right : Tm Head n) {C C' : Tm Head n}, SameSpines h left right →
      TypedEquality.Typed S.R Γ left C → TypedEquality.Typed S.R Γ right C' →
      ∃ pieces TL TR, ElimRel S.R (.var h) (Ctx.lookup Γ h) left right pieces TL TR
  | .var i, .var j, _, _, ⟨sameLeft, sameRight⟩, _, _ => by
      subst sameLeft
      subst sameRight
      exact ⟨[], _, _, .nil⟩
  | .app f a, .app g b, _, _, shape, tl, tr => by
      have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
        fun U typed => Typed.generation typed
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation tl
      obtain ⟨A', B', tg, _, _⟩ := Typed.generation tr
      obtain ⟨pieces, TL, TR, read⟩ := ElimRel.of_typed formed f g shape tf tg
      obtain ⟨tfL, principalF, _⟩ := read.typed_left facts roots heads formed th principal tf
      obtain ⟨tgR, principalG, _⟩ := read.swap.typed_left facts roots heads formed th principal tg
      obtain ⟨DL, EL, redL⟩ := reduces_pi_of_le facts formed (Typed.isType tfL formed) (Typed.isType tf formed)
        (principalF _ tf)
      obtain ⟨DR, ER, redR⟩ := reduces_pi_of_le facts formed (Typed.isType tgR formed) (Typed.isType tg formed)
        (principalG _ tg)
      exact ⟨_, _, _, .app read redL redR⟩
  | .fst p, .fst q, _, _, shape, tl, tr => by
      have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
        fun U typed => Typed.generation typed
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨A', B', tq, _⟩ := Typed.generation tr
      obtain ⟨pieces, TL, TR, read⟩ := ElimRel.of_typed formed p q shape tp tq
      obtain ⟨tpL, principalP, _⟩ := read.typed_left facts roots heads formed th principal tp
      obtain ⟨tqR, principalQ, _⟩ := read.swap.typed_left facts roots heads formed th principal tq
      obtain ⟨AL, BL, redL⟩ := reduces_sigma_of_le facts formed (Typed.isType tpL formed) (Typed.isType tp formed)
        (principalP _ tp)
      obtain ⟨AR, BR, redR⟩ := reduces_sigma_of_le facts formed (Typed.isType tqR formed) (Typed.isType tq formed)
        (principalQ _ tq)
      exact ⟨_, _, _, .fst read redL redR⟩
  | .snd p, .snd q, _, _, shape, tl, tr => by
      have th : TypedEquality.Typed S.R Γ (.var h) (Ctx.lookup Γ h) := .var h
      have principal : ∀ U, TypedEquality.Typed S.R Γ (.var h) U → TypeLe S.R Γ (Ctx.lookup Γ h) U :=
        fun U typed => Typed.generation typed
      obtain ⟨A, B, tp, _⟩ := Typed.generation tl
      obtain ⟨A', B', tq, _⟩ := Typed.generation tr
      obtain ⟨pieces, TL, TR, read⟩ := ElimRel.of_typed formed p q shape tp tq
      obtain ⟨tpL, principalP, _⟩ := read.typed_left facts roots heads formed th principal tp
      obtain ⟨tqR, principalQ, _⟩ := read.swap.typed_left facts roots heads formed th principal tq
      obtain ⟨AL, BL, redL⟩ := reduces_sigma_of_le facts formed (Typed.isType tpL formed) (Typed.isType tp formed)
        (principalP _ tp)
      obtain ⟨AR, BR, redR⟩ := reduces_sigma_of_le facts formed (Typed.isType tqR formed) (Typed.isType tq formed)
        (principalQ _ tq)
      exact ⟨_, _, _, .snd read redL redR⟩
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

include facts roots heads in
/-- **Typed sides of the shape have a checked reading**: the row of elimination spines of one local is a row by
shape. -/
theorem elimSpines_of_shape {depth n : Nat} {annotation left right : Tm Head n}
    (shape : ElimShape depth annotation left right) :
    ∀ {Γ : Ctx Head n} {locals : List (Tm Head n)}, locals.length = depth → CtxFormed S.R Γ → LocalTypes Γ locals →
      TypedEquality.Typed S.R Γ left annotation → TypedEquality.Typed S.R Γ right annotation →
      ∃ pieces, ElimSpines S.R true locals annotation left right pieces := by
  induction shape with
  | @under depth n D T l r _ ih =>
      intro Γ locals length formed types tl tr
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      obtain ⟨pieces, inner⟩ := ih (locals := Presentation.rename wk D :: locals.map (Presentation.rename wk))
        (by simp [length]) (formed.snoc ⟨u, hu, tD⟩) (types.under D) (Typed.lam_inv facts tl formed)
        (Typed.lam_inv facts tr formed)
      exact ⟨_, .under inner⟩
  | @base depth n C left right h based small spines =>
      intro Γ locals length formed types tl tr
      have inside : h.val < locals.length := by omega
      have looked : locals[h.val]? = some locals[h.val] := List.getElem?_eq_getElem inside
      have headType := types.head looked
      obtain ⟨pieces, TL, TR, read⟩ := ElimRel.of_typed facts roots heads formed left right spines tl tr
      rw [headType] at read
      exact ⟨pieces, .base (fun _ => based) inside looked read⟩

end Theory

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
