import Mettapedia.Logic.HOL.ImpredicativeConnectives
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLInterface

/-!
# Total HOL term representation through derived logical connectives

The existing declared logical interface is total after the generic HOL
impredicative expansion. No new native constant, reduction or typing rule is
introduced. Every source term, including formulas containing conjunction and
existence, has a computed representation with formation-sensitive typing.
The exact output commutes with simultaneous substitution.

This module establishes term representation. The companion
`HOLImpredicativeProofCompilation` extends the retained-proof compiler through
the same expansion. Neither construction turns a declared source axiom into
a theorem of the dependent core.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLImpredicativeRepresentation

open Presentation Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic
open HOL.ImpredicativeConnectives

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

theorem represent_core (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ)
    (core : IsCore t) : ∃ out, represent signature t = some out := by
  induction t with
  | var i => exact ⟨_, rfl⟩
  | const c => exact ⟨_, rfl⟩
  | app f a ihf iha =>
      obtain ⟨f', hf⟩ := ihf core.1
      obtain ⟨a', ha⟩ := iha core.2
      exact ⟨_, represent_app signature f a hf ha⟩
  | lam b ih =>
      obtain ⟨b', hb⟩ := ih core
      exact ⟨_, represent_lam signature b hb⟩
  | imp p q ihp ihq =>
      obtain ⟨p', hp⟩ := ihp core.1
      obtain ⟨q', hq⟩ := ihq core.2
      rw [represent_imp, hp, hq]
      exact ⟨_, rfl⟩
  | eq p q ihp ihq =>
      obtain ⟨p', hp⟩ := ihp core.1
      obtain ⟨q', hq⟩ := ihq core.2
      exact ⟨_, represent_eq signature p q hp hq⟩
  | all b ih =>
      obtain ⟨b', hb⟩ := ih core
      rw [represent_all, hb]
      exact ⟨_, rfl⟩
  | top | bot | and | or | not | ex => exact core.elim

theorem represent_expand_isSome (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) :
    (represent signature (expand t)).isSome := by
  obtain ⟨out, success⟩ := represent_core signature _ (expand_isCore t)
  simp [success]

/-- Computed output of the existing representation, with impossibility of
failure proved for the expanded grammar. This is not a choice of a witness. -/
def translate (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) : Tower.Tm Γ.length :=
  (represent signature (expand t)).get (represent_expand_isSome signature t)

theorem translate_eq (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) :
    represent signature (expand t) = some (translate signature t) :=
  (Option.some_get (represent_expand_isSome signature t)).symm

@[simp] theorem translate_var (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (i : HOL.Var Γ τ) :
    translate signature (.var i) = .var (variableIndex i) := by
  apply Option.some.inj
  rw [← translate_eq]
  rfl

@[simp] theorem translate_app (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {a b : HOL.Ty Base}
    (function : HOL.Term Const Γ (.arr a b)) (argument : HOL.Term Const Γ a) :
    translate signature (.app function argument) =
      .app (translate signature function) (translate signature argument) := by
  apply Option.some.inj
  rw [← translate_eq]
  exact represent_app signature _ _ (translate_eq signature function) (translate_eq signature argument)

@[simp] theorem translate_lam (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {a b : HOL.Ty Base} (body : HOL.Term Const (a :: Γ) b) :
    translate signature (.lam body) = .lam (translate signature body) := by
  apply Option.some.inj
  rw [← translate_eq]
  exact represent_lam signature _ (translate_eq signature body)

theorem translate_typed (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) :
    Typing signature.rules (context signature.types Γ) (translate signature t)
      (typeAt signature.types Γ.length τ) :=
  represent_typed signature _ (translate_eq signature t)

theorem translate_rename (signature : LogicalSignature Base Const)
    {Γ Δ : HOL.Ctx Base} {τ : HOL.Ty Base}
    (ρ : HOL.Rename Base Γ Δ) (raw : Ren Γ.length Δ.length)
    (compatible : ∀ {a} (i : HOL.Var Γ a),
      variableIndex (ρ i) = raw (variableIndex i))
    (t : HOL.Term Const Γ τ) :
    translate signature (HOL.rename ρ t) = Presentation.rename raw (translate signature t) := by
  apply Option.some.inj
  rw [← translate_eq, expand_rename,
    represent_rename signature ρ raw compatible, translate_eq]
  rfl

/-- Binding compatibility concerns the computed outputs, not merely existence
of some equally typed representation. -/
theorem translate_subst (signature : LogicalSignature Base Const)
    {Γ Δ : HOL.Ctx Base} {τ : HOL.Ty Base}
    (σs : HOL.Subst Const Γ Δ) (raw : Sub Tower.Head Γ.length Δ.length)
    (compatible : ∀ {a} (i : HOL.Var Γ a),
      translate signature (σs i) = raw (variableIndex i))
    (t : HOL.Term Const Γ τ) :
    translate signature (HOL.subst σs t) = Presentation.subst raw (translate signature t) := by
  apply Option.some.inj
  rw [← translate_eq, expand_subst]
  have images : ∀ {a} (i : HOL.Var Γ a),
      represent signature (expand (σs i)) = some (raw (variableIndex i)) := by
    intro a i
    rw [translate_eq, compatible]
  rw [represent_subst signature (fun i => expand (σs i)) raw images,
    translate_eq]
  rfl

/-- Source beta instantiation computes the same result as native opening,
including source binders and derived logical connectives. -/
theorem translate_instantiate (signature : LogicalSignature Base Const)
    {Γ : HOL.Ctx Base} {a b : HOL.Ty Base}
    (argument : HOL.Term Const Γ a) (body : HOL.Term Const (a :: Γ) b) :
    translate signature (HOL.instantiate argument body) =
      inst0 (translate signature argument) (translate signature body) := by
  apply translate_subst signature (HOL.Subst.single argument)
    (subst0 (translate signature argument))
  intro type index
  cases index with
  | vz => rfl
  | vs index => simp [HOL.Subst.single, variableIndex, subst0]

#print axioms translate_typed
#print axioms translate_subst
#print axioms translate_instantiate

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLImpredicativeRepresentation
