import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mettapedia.Logic.HOL.Syntax.Subst

/-!
# The live HOL syntax as a simply typed category with families

This module packages the existing intrinsically typed HOL terms and their
simultaneous substitutions as the simply typed rung of the contextual
ladder.  It does not introduce a parallel HOL syntax.

A contextual arrow `Γ ⟶ Δ` assigns a term in `Γ` to every variable of
`Δ`, so it is represented by the existing `Subst Const Δ Γ`.  Context
extension is list cons, the newest variable is `Var.vz`, and pairing extends
a simultaneous substitution by one typed term.

The resulting dependent interface is only the constant-family image
`holScwf.toCwf`: its types cannot vary with the context.  Interpreting HOL in
a genuinely dependent presentation therefore additionally requires an
authored interpretation of base types and constants; the contextual ladder
alone does not manufacture one.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ContextualStructure

open Mettapedia.GSLT.Core.ContextualLadder
open CategoryTheory

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Simultaneous-substitution comprehension -/

/-- Extend a simultaneous substitution with the image of the newest
variable. -/
def extendSubst {Γ Δ : Ctx Base} {A : Ty Base}
    (substitution : Subst Const Δ Γ) (term : Term Const Γ A) :
    Subst Const (A :: Δ) Γ
  | _, .vz => term
  | _, .vs boundVar => substitution boundVar

/-- Equality of simultaneous substitutions is pointwise equality on typed
variables. -/
theorem substitution_ext {Γ Δ : Ctx Base}
    {left right : Subst Const Γ Δ}
    (equal : ∀ {A : Ty Base} (boundVar : Var Γ A),
      left boundVar = right boundVar) :
    (fun {A : Ty Base} (boundVar : Var Γ A) => left boundVar) =
      (fun {A : Ty Base} (boundVar : Var Γ A) => right boundVar) := by
  funext A boundVar
  exact equal boundVar

/-! ## The actual HOL `Scwf` -/

/-- The existing HOL syntax and substitution calculus, packaged as a
simply typed category with families. -/
def holScwf (Base : Type u) (Const : Ty Base → Type v) :
    Scwf.{u, max u v, u, max u v} where
  Ctx := Ctx Base
  Sub Γ Δ := Subst Const Δ Γ
  idS Γ := Subst.id (Base := Base) (Const := Const) (Γ := Γ)
  compS later earlier := Subst.comp earlier later
  id_comp := by
    intro Γ Δ substitution
    apply substitution_ext
    intro A boundVar
    rfl
  comp_id := by
    intro Γ Δ substitution
    apply substitution_ext
    intro A boundVar
    exact subst_id (Base := Base) (Const := Const) (substitution boundVar)
  comp_assoc := by
    intro Γ Δ Θ Ξ latest middle earliest
    apply substitution_ext
    intro A boundVar
    exact subst_comp (Base := Base) (Const := Const)
      earliest middle (latest boundVar)
  Ty := Ty Base
  Tm Γ A := Term Const Γ A
  tmSub term substitution := subst substitution term
  tmSub_id term := subst_id (Base := Base) (Const := Const) term
  tmSub_comp := by
    intro Γ Δ Θ A term later earlier
    exact (subst_comp (Base := Base) (Const := Const) earlier later term).symm
  ext Γ A := A :: Γ
  wk A := Subst.ofRename
    (Rename.weaken (Base := Base) (Γ := _) (σ := A))
  vz _ := .var .vz
  pair substitution _ term := extendSubst substitution term
  wk_pair := by
    intro Γ Δ substitution A term
    apply substitution_ext
    intro B boundVar
    rfl
  vz_pair := by
    intro Γ Δ substitution A term
    rfl
  pair_eta := by
    intro Γ Δ A substitution
    apply substitution_ext
    intro B boundVar
    cases boundVar <;> rfl

/-! ## The standard terminal context omitted by the bare ladder interface -/

/-- The empty HOL context. -/
def emptyContext (Base : Type u) : Ctx Base := []

/-- The unique substitution from any HOL context into the empty context. -/
def toEmpty (context : Ctx Base) : Subst Const (emptyContext Base) context :=
  fun {_A} boundVar => nomatch boundVar

/-- The empty HOL context is terminal in the context/substitution category. -/
theorem toEmpty_unique (context : Ctx Base)
    (substitution : Subst Const (emptyContext Base) context) :
    (fun {A : Ty Base} (boundVar : Var (emptyContext Base) A) =>
      substitution boundVar) =
    (fun {A : Ty Base} (boundVar : Var (emptyContext Base) A) =>
      toEmpty context boundVar) := by
  apply substitution_ext
  intro A boundVar
  exact nomatch boundVar

/-- The empty list, regarded as an object of the HOL context category. -/
def emptyContextObject : (holScwf Base Const).base.Context :=
  ⟨emptyContext Base⟩

/-- Every context has a unique contextual arrow to the empty context. -/
instance uniqueToEmptyContext
    (context : (holScwf Base Const).base.Context) :
    Unique (context ⟶ emptyContextObject) where
  default := toEmpty context.val
  uniq substitution := toEmpty_unique context.val substitution

/-- Constructive terminality of the empty HOL context: every hom-set into it
has exactly one inhabitant. -/
@[reducible] def emptyTerminalUniversal :
    ∀ context : (holScwf Base Const).base.Context,
      Unique (context ⟶ emptyContextObject) :=
  fun context => uniqueToEmptyContext context

/-- The live HOL syntax with its chosen empty context, packaged as a full
standard simply typed cwf. -/
def holScwfWithTerminal (Base : Type u) (Const : Ty Base → Type v) :
    ScwfWithTerminal.{u, max u v, u, max u v} where
  toScwf := holScwf Base Const
  empty := emptyContext Base
  toEmpty := toEmpty
  toEmpty_unique := by
    intro context substitution
    exact toEmpty_unique context substitution

/-! ## Positive and negative boundary witnesses -/

/-- Positive: substituting an extended environment into the newest variable
returns exactly the newly supplied term. -/
theorem newestVariable_after_pair {Γ Δ : Ctx Base} {A : Ty Base}
    (substitution : (holScwf Base Const).Sub Γ Δ)
    (term : (holScwf Base Const).Tm Γ A) :
    (holScwf Base Const).tmSub
        ((holScwf Base Const).vz A)
        ((holScwf Base Const).pair substitution A term) = term := rfl

/-- Negative: the dependent presentation obtained from HOL by the contextual
ladder has no nontrivial type reindexing.  This is the exact limitation of
the simple fragment, not an assertion that dependent families collapse. -/
theorem no_nontrivial_type_reindexing :
    ¬ ∃ (Γ Δ : (holScwf Base Const).toCwf.Ctx)
        (A : (holScwf Base Const).toCwf.Ty Δ)
        (substitution : (holScwf Base Const).toCwf.Sub Γ Δ),
      (holScwf Base Const).toCwf.tySub A substitution ≠ A := by
  rintro ⟨Γ, Δ, A, substitution, different⟩
  exact different rfl

#print axioms holScwf
#print axioms toEmpty_unique
#print axioms emptyTerminalUniversal
#print axioms holScwfWithTerminal
#print axioms newestVariable_after_pair
#print axioms no_nontrivial_type_reindexing

end Mettapedia.Logic.HOL.ContextualStructure
