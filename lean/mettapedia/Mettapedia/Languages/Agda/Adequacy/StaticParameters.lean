import Mettapedia.Languages.Agda.Adequacy.StaticContext
import Mettapedia.Languages.Agda.Structural.StaticSyntax

/-!
# Correspondence of raw static rule parameters

Source annotated types and both abstraction forms supply the structural rule
parameters. Their code, opening, and instantiation operations agree exactly.
No rule derivations or typing judgments are imported from the reference here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy

open Mettapedia.OSLF.Binding
open Structural (sig scope)

def embedTypeParameter {n : Nat} : StaticSpecification.Ty n → Structural.Statics.TypeParameter n
  | .el level term => ⟨level, embedTerm term⟩

def embedTermBody {n : Nat} : StaticSpecification.Abs n → Structural.Statics.TermBody n
  | .bind body => .bind (embedTerm body)
  | .noBind body => .noBind (embedTerm body)

def embedTypeBody {n : Nat} : StaticSpecification.TyAbs n → Structural.Statics.TypeBody n
  | .bind body => .bind (embedTypeParameter body)
  | .noBind body => .noBind (embedTypeParameter body)

@[simp] theorem embedTypeParameter_code {n : Nat} (type : StaticSpecification.Ty n) :
    (embedTypeParameter type).code = embedTy type := by cases type; rfl

@[simp] theorem embedTypeParameter_level {n : Nat} (type : StaticSpecification.Ty n) :
    (embedTypeParameter type).level = type.level := by cases type; rfl

@[simp] theorem embedTypeParameter_term {n : Nat} (type : StaticSpecification.Ty n) :
    (embedTypeParameter type).term = embedTerm type.term := by cases type; rfl

@[simp] theorem embedTypeBody_level {n : Nat} (body : StaticSpecification.TyAbs n) :
    (embedTypeBody body).level = body.level := by
  cases body with
  | bind body => exact embedTypeParameter_level body
  | noBind body => exact embedTypeParameter_level body

@[simp] theorem embedTermBody_lambda {n : Nat} (body : StaticSpecification.Abs n) :
    (embedTermBody body).lambda = embedTerm (.lam body) := by cases body <;> rfl

@[simp] theorem embedTypeBody_pi {n : Nat} (type : StaticSpecification.Ty n)
    (body : StaticSpecification.TyAbs n) :
    (embedTypeBody body).pi (embedTypeParameter type) = embedTerm (.pi type body) := by
  cases type
  cases body with
  | bind body => cases body; rfl
  | noBind body => cases body; rfl

theorem embedTypeParameter_subst {n m : Nat} (type : StaticSpecification.Ty n)
    (σ : StaticSpecification.Substitution n m) :
    embedTypeParameter (type.subst σ) = (embedTypeParameter type).substitute (embedSub σ) := by
  cases type with
  | el level term => exact congrArg (Structural.Statics.TypeParameter.mk level) (embedTerm_subst σ term)

theorem embedTypeParameter_rename {n m : Nat} (type : StaticSpecification.Ty n)
    (ρ : StaticSpecification.Renaming n m) :
    embedTypeParameter (type.rename ρ) =
      ⟨type.level, rename (embedRen ρ) (embedTerm type.term)⟩ := by
  cases type with
  | el level term => exact congrArg (Structural.Statics.TypeParameter.mk level) (embedTerm_rename ρ term)

/-- Native weakening agrees with source weakening before any typing is imposed. -/
theorem bind_projection_embedTerm {n : Nat} (term : StaticSpecification.Term n) :
    bind (Telescope.projection (S := sig) Structural.Srt.term n) (embedTerm term) =
      embedTerm term.weaken :=
  (Telescope.bind_projection (S := sig) (b := Structural.Srt.term) (embedTerm term)).trans
    (embedTerm_weaken term).symm

theorem bind_projection_embedTy {n : Nat} (type : StaticSpecification.Ty n) :
    bind (Telescope.projection (S := sig) Structural.Srt.term n) (embedTy type) =
      embedTy type.weaken :=
  (Telescope.bind_projection (S := sig) (b := Structural.Srt.term) (embedTy type)).trans
    (embedTy_weaken type).symm

theorem embedTypeParameter_weaken {n : Nat} (type : StaticSpecification.Ty n) :
    embedTypeParameter type.weaken = (embedTypeParameter type).weaken := by
  cases type with
  | el level term =>
      exact congrArg (Structural.Statics.TypeParameter.mk level) (bind_projection_embedTerm term).symm

@[simp] theorem embedTermBody_open {n : Nat} (body : StaticSpecification.Abs n) :
    (embedTermBody body).open = embedTerm body.open := by
  cases body with
  | bind body => rfl
  | noBind body => exact bind_projection_embedTerm body

@[simp] theorem embedTypeBody_open {n : Nat} (body : StaticSpecification.TyAbs n) :
    (embedTypeBody body).open = embedTypeParameter body.open := by
  cases body with
  | bind body => rfl
  | noBind body => exact (embedTypeParameter_weaken body).symm

theorem embedTermBody_open_subst {n m : Nat} (body : StaticSpecification.Abs n)
    (σ : StaticSpecification.Substitution n m) :
    (embedTermBody (body.subst σ)).open =
      bind (liftSub (embedSub σ) [.term]) (embedTermBody body).open := by
  rw [embedTermBody_open, embedTermBody_open, StaticSpecification.Abs.open_subst,
    embedTerm_subst, embedSub_lift]
  rfl

theorem embedTypeBody_open_subst {n m : Nat} (body : StaticSpecification.TyAbs n)
    (σ : StaticSpecification.Substitution n m) :
    (embedTypeBody (body.subst σ)).open =
      (embedTypeBody body).open.substitute (m := m + 1) (liftSub (embedSub σ) [.term]) := by
  rw [embedTypeBody_open, embedTypeBody_open, StaticSpecification.TyAbs.open_subst,
    embedTypeParameter_subst, embedSub_lift]

theorem embedSub_single_native {n : Nat} (argument : StaticSpecification.Term n) :
    embedSub (StaticSpecification.Substitution.single argument) =
      Structural.Statics.single (embedTerm argument) := by
  rw [embedSub_single]
  funext s v
  cases v <;> rfl

@[simp] theorem embedTermBody_instantiate {n : Nat} (body : StaticSpecification.Abs n)
    (argument : StaticSpecification.Term n) :
    (embedTermBody body).instantiate (embedTerm argument) = embedTerm (body.instantiate argument) := by
  change bind (Structural.Statics.single (embedTerm argument)) (embedTermBody body).open =
    embedTerm (body.open.subst (StaticSpecification.Substitution.single argument))
  rw [embedTermBody_open, embedTerm_subst, embedSub_single_native]
  rfl

@[simp] theorem embedTypeBody_instantiate {n : Nat} (body : StaticSpecification.TyAbs n)
    (argument : StaticSpecification.Term n) :
    (embedTypeBody body).instantiate (embedTerm argument) =
      embedTypeParameter (body.instantiate argument) := by
  change (embedTypeBody body).open.substitute (Structural.Statics.single (embedTerm argument)) =
    embedTypeParameter (body.open.subst (StaticSpecification.Substitution.single argument))
  rw [embedTypeBody_open, embedTypeParameter_subst, embedSub_single_native]

@[simp] theorem embedTypeParameter_universe (n level : Nat) :
    embedTypeParameter (StaticSpecification.Ty.universe (n := n) level) =
      Structural.Statics.universeType n level := rfl

@[simp] theorem embedTerm_sort {n : Nat} (level : Nat) :
    embedTerm (StaticSpecification.Term.sort (n := n) level) =
      Structural.Statics.universeTerm level := rfl

@[simp] theorem embedTypeParameter_pi {n : Nat} (type : StaticSpecification.Ty n)
    (body : StaticSpecification.TyAbs n) :
    embedTypeParameter (StaticSpecification.Ty.pi type body) =
      Structural.Statics.piType (embedTypeParameter type) (embedTypeBody body) := by
  cases type
  cases body with
  | bind body => cases body; rfl
  | noBind body => cases body; rfl

@[simp] theorem embedTerm_app {n : Nat} (function argument : StaticSpecification.Term n) :
    embedTerm (function.app argument) = Structural.Statics.app (embedTerm function) (embedTerm argument) := rfl

/-- Source lists act by successive singleton nodes; no spine flattening is performed. -/
theorem embedTerm_applySpine {n : Nat} (function : StaticSpecification.Term n)
    (spine : StaticSpecification.Spine n) :
    embedTerm (function.applySpine spine) =
      spine.foldl (fun head e => Structural.eliminate head
        (Structural.cons (embedElim e) Structural.nil)) (embedTerm function) := by
  induction spine generalizing function with
  | nil => rfl
  | cons e es ih => exact ih (.elim function e)

theorem embedTypeParameter_injective {n : Nat} : Function.Injective (embedTypeParameter (n := n)) := by
  intro first second same
  apply embedTy_injective
  rw [← embedTypeParameter_code, ← embedTypeParameter_code, same]

theorem embedTermBody_injective {n : Nat} : Function.Injective (embedTermBody (n := n)) := by
  intro first second same
  apply StaticSpecification.Term.lam.inj
  apply embedTerm_injective
  rw [← embedTermBody_lambda, ← embedTermBody_lambda, same]

theorem embedTypeBody_injective {n : Nat} : Function.Injective (embedTypeBody (n := n)) := by
  intro first second same
  have terms : embedTerm (.pi (StaticSpecification.Ty.universe 0) first) =
      embedTerm (.pi (StaticSpecification.Ty.universe 0) second) := by
    rw [← embedTypeBody_pi, ← embedTypeBody_pi, same]
  exact (StaticSpecification.Term.pi.inj (embedTerm_injective terms)).2

end Mettapedia.Languages.Agda.StaticAdequacy
