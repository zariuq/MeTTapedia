import Mettapedia.GSLT.Core.ContextualLadderBaseCategory

/-!
# Terminal contexts for the contextual ladder

The standard definitions of a ucwf, scwf, and cwf include a chosen terminal
context.  `ContextualLadder` deliberately isolated the reusable
substitution/comprehension core; this module supplies the missing standard
component without changing that existing interface.

The terminal structure is preserved on the nose by the unityped-to-simple
and simple-to-dependent ladder maps.  The set-family models provide concrete
instances with `PUnit` as the empty context.  `PEmpty` is a negative canary:
it cannot even receive a substitution from every context, so terminality is
not being obtained vacuously.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

/-! ## Standard terminal-context extensions -/

/-- A full cwf at the structural level used here: the existing dependent
substitution/comprehension core plus a chosen terminal context. -/
structure CwfWithTerminal : Type (max (u + 1) (v + 1) (w + 1) (w' + 1)) where
  toCwf : Cwf.{u, v, w, w'}
  empty : toCwf.Ctx
  toEmpty : (Γ : toCwf.Ctx) → toCwf.Sub Γ empty
  toEmpty_unique : ∀ (Γ : toCwf.Ctx) (substitution : toCwf.Sub Γ empty),
    substitution = toEmpty Γ

/-- A full simply typed cwf: the simple substitution/comprehension core plus
a chosen terminal context. -/
structure ScwfWithTerminal : Type (max (u + 1) (v + 1) (w + 1) (w' + 1)) where
  toScwf : Scwf.{u, v, w, w'}
  empty : toScwf.Ctx
  toEmpty : (Γ : toScwf.Ctx) → toScwf.Sub Γ empty
  toEmpty_unique : ∀ (Γ : toScwf.Ctx) (substitution : toScwf.Sub Γ empty),
    substitution = toEmpty Γ

/-- A full unityped cwf: the unityped substitution/comprehension core plus a
chosen terminal context. -/
structure UcwfWithTerminal : Type (max (u + 1) (v + 1) (w' + 1)) where
  toUcwf : Ucwf.{u, v, w'}
  empty : toUcwf.Ctx
  toEmpty : (Γ : toUcwf.Ctx) → toUcwf.Sub Γ empty
  toEmpty_unique : ∀ (Γ : toUcwf.Ctx) (substitution : toUcwf.Sub Γ empty),
    substitution = toEmpty Γ

/-! ## Constructive terminal universal properties -/

/-- The chosen empty context of a full cwf has its terminal universal
property constructively. -/
@[reducible] def CwfWithTerminal.emptyUniversal
    (C : CwfWithTerminal.{u, v, w, w'}) :
    ∀ Γ : C.toCwf.Ctx, Unique (C.toCwf.Sub Γ C.empty) :=
  fun Γ =>
    { default := C.toEmpty Γ
      uniq := C.toEmpty_unique Γ }

/-- The chosen empty context of a full scwf has its terminal universal
property constructively. -/
@[reducible] def ScwfWithTerminal.emptyUniversal
    (S : ScwfWithTerminal.{u, v, w, w'}) :
    ∀ Γ : S.toScwf.Ctx, Unique (S.toScwf.Sub Γ S.empty) :=
  fun Γ =>
    { default := S.toEmpty Γ
      uniq := S.toEmpty_unique Γ }

/-- The chosen empty context of a full ucwf has its terminal universal
property constructively. -/
@[reducible] def UcwfWithTerminal.emptyUniversal
    (U : UcwfWithTerminal.{u, v, w'}) :
    ∀ Γ : U.toUcwf.Ctx, Unique (U.toUcwf.Sub Γ U.empty) :=
  fun Γ =>
    { default := U.toEmpty Γ
      uniq := U.toEmpty_unique Γ }

/-! ## The full contextual ladder -/

/-- Adding the unique simple type preserves the chosen terminal context on
the nose. -/
def UcwfWithTerminal.toScwfWithTerminal
    (U : UcwfWithTerminal.{u, v, w'}) :
    ScwfWithTerminal.{u, v, w, w'} where
  toScwf := U.toUcwf.toScwf
  empty := U.empty
  toEmpty := U.toEmpty
  toEmpty_unique := U.toEmpty_unique

/-- Passing to constant dependent families preserves the chosen terminal
context on the nose. -/
def ScwfWithTerminal.toCwfWithTerminal
    (S : ScwfWithTerminal.{u, v, w, w'}) :
    CwfWithTerminal.{u, v, w, w'} where
  toCwf := S.toScwf.toCwf
  empty := S.empty
  toEmpty := S.toEmpty
  toEmpty_unique := S.toEmpty_unique

/-- The two full ladder maps preserve the empty context definitionally. -/
@[simp] theorem UcwfWithTerminal.ladder_empty
    (U : UcwfWithTerminal.{u, v, w'}) :
    U.toScwfWithTerminal.toCwfWithTerminal.empty = U.empty := rfl

/-- The two full ladder maps preserve terminal substitutions definitionally. -/
@[simp] theorem UcwfWithTerminal.ladder_toEmpty
    (U : UcwfWithTerminal.{u, v, w'}) (Γ : U.toUcwf.Ctx) :
    U.toScwfWithTerminal.toCwfWithTerminal.toEmpty Γ = U.toEmpty Γ := rfl

/-! ## Set-family instances -/

/-- The dependent set-family cwf with `PUnit` as its empty context. -/
def familiesCwfWithTerminal : CwfWithTerminal.{w + 1, w, w + 1, w} where
  toCwf := familiesCwf
  empty := PUnit
  toEmpty _ := fun _ => PUnit.unit
  toEmpty_unique := by
    intro Γ substitution
    funext γ
    cases substitution γ
    rfl

/-- The simply typed set-family cwf with `PUnit` as its empty context. -/
def simpleFamiliesWithTerminal :
    ScwfWithTerminal.{w + 1, w, w + 1, w} where
  toScwf := simpleFamilies
  empty := PUnit
  toEmpty _ := fun _ => PUnit.unit
  toEmpty_unique := by
    intro Γ substitution
    funext γ
    cases substitution γ
    rfl

/-- The unityped set-family cwf with `PUnit` as its empty context. -/
def unitypedFamiliesWithTerminal (V : Type w) :
    UcwfWithTerminal.{w + 1, w, w} where
  toUcwf := unitypedFamilies V
  empty := PUnit
  toEmpty _ := fun _ => PUnit.unit
  toEmpty_unique := by
    intro Γ substitution
    funext γ
    cases substitution γ
    rfl

/-! ## Positive and negative terminal witnesses -/

/-- The selected empty context of the families model has a unique map from
every context. -/
@[reducible] def families_empty_unique (Γ : Type w) :
    Unique (familiesCwfWithTerminal.toCwf.Sub Γ
      familiesCwfWithTerminal.empty) :=
  familiesCwfWithTerminal.emptyUniversal Γ

/-- Positive: any two maps into the selected empty context are equal. -/
theorem families_empty_maps_equal (Γ : Type w)
    (left right : familiesCwfWithTerminal.toCwf.Sub Γ
      familiesCwfWithTerminal.empty) :
    left = right :=
  (families_empty_unique Γ).uniq left |>.trans
    ((families_empty_unique Γ).uniq right).symm

/-- Negative: `PEmpty` cannot be selected as the terminal context in the
category of types and functions, because even `PUnit` has no map to it. -/
theorem pempty_cannot_receive_all_context_maps :
    ¬ ((Γ : Type w) → Γ → PEmpty) := by
  intro maps
  exact nomatch maps PUnit PUnit.unit

#print axioms CwfWithTerminal.emptyUniversal
#print axioms UcwfWithTerminal.toScwfWithTerminal
#print axioms ScwfWithTerminal.toCwfWithTerminal
#print axioms familiesCwfWithTerminal
#print axioms families_empty_unique
#print axioms families_empty_maps_equal
#print axioms pempty_cannot_receive_all_context_maps

end Mettapedia.GSLT.Core.ContextualLadder
