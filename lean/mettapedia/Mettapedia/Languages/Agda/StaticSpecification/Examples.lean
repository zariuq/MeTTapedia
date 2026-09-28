import Mettapedia.Languages.Agda.StaticSpecification.Eta

/-! Positive and negative controls for scope, formation, beta, eta, and evidence. -/

namespace Mettapedia.Languages.Agda.StaticSpecification.Examples

def typeContext : RawContext 1 := .snoc .nil (Ty.universe 0)
def typeContextFormed : FormCtx typeContext := .snoc .nil (.universe .nil 0)
def typeVariable : Ty 1 := .el 0 (.var 0)
def typeVariableFormed : FormTy typeContext typeVariable :=
  .ofTyping (.var 0 typeContextFormed)

/-- The familiar `A : Set` context admits the polymorphic identity's body. -/
def identityAtTypeVariable :
    Typing typeContext (.lam (.bind (.var 0))) (Ty.pi typeVariable (.noBind typeVariable)) :=
  .lam typeVariableFormed (typeVariableFormed.weaken typeVariableFormed)
    (.var 0 (.snoc typeContextFormed typeVariableFormed))

def twoTypes : RawContext 2 := .snoc typeContext (Ty.universe 0)
def twoTypesFormed : FormCtx twoTypes :=
  .snoc typeContextFormed (.universe typeContextFormed 0)

def olderTypeImage : Substitution 1 2 := fun _ => .var 1
def newestTypeImage : Substitution 1 2 := fun _ => .var 0

def olderTypeSubstitution : SubDeriv typeContext twoTypes olderTypeImage where
  source := typeContextFormed
  target := twoTypesFormed
  lookup := fun i => by
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact Typing.var 1 twoTypesFormed

def newestTypeSubstitution : SubDeriv typeContext twoTypes newestTypeImage where
  source := typeContextFormed
  target := twoTypesFormed
  lookup := fun i => by
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact Typing.var 0 twoTypesFormed

/-- A genuinely dependent type changes when its type-variable image changes. -/
def substitutedOlderType : FormTy twoTypes (.el 0 (.var 1)) :=
  typeVariableFormed.substitute olderTypeSubstitution

def substitutedNewestType : FormTy twoTypes (.el 0 (.var 0)) :=
  typeVariableFormed.substitute newestTypeSubstitution

theorem distinct_type_images :
    typeVariable.subst olderTypeImage ≠ typeVariable.subst newestTypeImage := by
  intro h
  have e : (1 : Fin 2) = 0 := Term.var.inj (Ty.el.inj h).2
  exact (by decide : (1 : Fin 2) ≠ 0) e

/-- Substitution also returns the complete typing tree of the dependent identity. -/
def substitutedIdentity := identityAtTypeVariable.substitute olderTypeSubstitution

def closedIdentity : Term 0 := .lam (.bind (.var 0))
def closedIdentityType : Ty 0 := Ty.pi (Ty.universe 1) (.noBind (Ty.universe 1))
def oneUniverseContext : RawContext 1 := .snoc .nil (Ty.universe 1)
def oneUniverseFormed : FormCtx oneUniverseContext := .snoc .nil (.universe .nil 1)

def closedIdentityTyping : Typing .nil closedIdentity closedIdentityType :=
  .lam (.universe .nil 1) (.universe oneUniverseFormed 1) (.var 0 oneUniverseFormed)

/-- A closed beta redex and its reduct both receive actual typing evidence. -/
def closedBeta :
    TermEq .nil (closedIdentity.app (.sort 0)) (.sort 0) (Ty.universe 1) :=
  .beta (b := .noBind (Ty.universe 1)) (body := .bind (.var 0))
    (.universe .nil 1) (.universe oneUniverseFormed 1)
    (.var 0 oneUniverseFormed) (.sort 0 .nil)

def closedBetaReduct : Typing .nil (.sort 0) (Ty.universe 1) :=
  Typing.instantiate (a := Ty.universe 1) (b := .noBind (Ty.universe 1))
    (body := .bind (.var 0)) (.var 0 oneUniverseFormed)
    (.universe .nil 1) (.sort 0 .nil)

theorem beta_is_not_raw_equality : closedIdentity.app (.sort 0) ≠ .sort 0 := by
  intro h
  cases h

/-- Typed eta compares the function with a syntactically different expansion. -/
def closedEta : TermEq .nil closedIdentity
    (.lam (.bind (closedIdentity.weaken.app (.var 0)))) closedIdentityType :=
  TermEq.etaExpand closedIdentityTyping (.universe .nil 1) (.universe oneUniverseFormed 1)

theorem eta_is_not_raw_equality :
    closedIdentity ≠ .lam (.bind (closedIdentity.weaken.app (.var 0))) := by
  intro h
  cases h

def constantFunction : Term 0 := .lam (.bind (.lam (.bind (.var 1))))
def constantFunctionType : Ty 0 :=
  Ty.pi (Ty.universe 1) (.noBind (Ty.pi (Ty.universe 1) (.noBind (Ty.universe 1))))
def twoUniversesFormed : FormCtx (oneUniverseContext.snoc (Ty.universe 1)) :=
  .snoc oneUniverseFormed (.universe oneUniverseFormed 1)

def constantFunctionTyping : Typing .nil constantFunction constantFunctionType :=
  .lam (b := .noBind (Ty.pi (Ty.universe 1) (.noBind (Ty.universe 1))))
    (.universe .nil 1)
    (.pi (b := .noBind (Ty.universe 1)) (.universe oneUniverseFormed 1)
      (.universe twoUniversesFormed 1))
    (.lam (b := .noBind (Ty.universe 1)) (.universe oneUniverseFormed 1) (.universe twoUniversesFormed 1)
      (.var 1 twoUniversesFormed))

def smallFunctionType : Term 0 := .pi (Ty.universe 0) (.noBind (Ty.universe 0))
def smallFunctionTypeTyping : Typing .nil smallFunctionType (Ty.universe 1) :=
  .pi (.universe .nil 0) (.universe typeContextFormed 0)

def orderedSpine : Spine 0 := [.apply (.sort 0), .apply smallFunctionType]

/-- Two eliminations retain their order and their intermediate dependent type. -/
def orderedSpineTyping :
    SpineTyping .nil constantFunction constantFunctionType orderedSpine (Ty.universe 1) :=
  .cons constantFunctionTyping (.sort 0 .nil)
    (.cons (.app constantFunctionTyping (.sort 0 .nil)) smallFunctionTypeTyping
      (.nil (.app (.app constantFunctionTyping (.sort 0 .nil)) smallFunctionTypeTyping)))

def orderedSpineResult := orderedSpineTyping.typing

theorem swapping_spine_changes_raw_term :
    constantFunction.applySpine orderedSpine ≠
      constantFunction.applySpine [.apply smallFunctionType, .apply (.sort 0)] := by
  intro h
  have e := (Term.elim.inj h).2
  cases e

/-- A free variable substituted below a binder stays free. -/
theorem avoids_capture :
    (Term.lam (.bind (.var (1 : Fin 3)))).subst (Substitution.single (.var (0 : Fin 1))) =
      .lam (.bind (.var (1 : Fin 2))) := rfl

theorem rejects_captured_result :
    (Term.lam (.bind (.var (1 : Fin 3)))).subst (Substitution.single (.var (0 : Fin 1))) ≠
      .lam (.bind (.var (0 : Fin 2))) := by
  intro h
  have e : (1 : Fin 2) = 0 := Term.var.inj (Abs.bind.inj (Term.lam.inj h))
  exact (by decide : (1 : Fin 2) ≠ 0) e

/-- `NoAbs` has no hidden binder to capture or discard the supplied variable. -/
theorem nonbinding_instantiation :
    (Abs.noBind (.var (0 : Fin 1))).instantiate (.sort 0) = .var 0 :=
  Abs.instantiate_noBind _ _

theorem wrong_universe_rejected {Γ : RawContext n} :
    ¬ Nonempty (Typing Γ (.sort 0) (Ty.universe 0)) := by
  rintro ⟨d⟩
  have e : 1 = 2 := d.sort_level
  contradiction

theorem wrong_annotation_rejected {Γ : RawContext n} :
    ¬ Nonempty (FormTy Γ (.el 0 (.sort 0))) := by
  rintro ⟨d⟩
  have e : 0 = 1 := d.sort_annotation
  contradiction

def malformedTelescope : RawContext 1 := .snoc .nil (.el 0 (.sort 0))

theorem malformed_telescope_rejected : ¬ Nonempty (FormCtx malformedTelescope) := by
  rintro ⟨d⟩
  cases d with
  | snoc _ h => exact wrong_annotation_rejected ⟨h⟩

/-- Raw scoping of a variable does not make an ill-formed telescope admissible. -/
theorem malformed_telescope_has_no_typing (t : Term 1) (a : Ty 1) :
    ¬ Nonempty (Typing malformedTelescope t a) := by
  rintro ⟨d⟩
  exact malformed_telescope_rejected ⟨d.context⟩

theorem distinct_universes_not_convertible {Γ : RawContext n} :
    ¬ Nonempty (TypeEq Γ (Ty.universe 0) (Ty.universe 1)) := by
  rintro ⟨d⟩
  have e : 1 = 2 := d.level_eq
  contradiction

def directSortTyping : Typing .nil (.sort 0) (Ty.universe 1) := .sort 0 .nil
def detouredSortTyping : Typing .nil (.sort 0) (Ty.universe 1) :=
  .conv directSortTyping (TypeEq.refl (.universe .nil 1))

/-- Identical endpoints do not identify a direct derivation with a conversion detour. -/
theorem retained_derivations_distinct : directSortTyping ≠ detouredSortTyping := by
  intro h
  cases h

end Mettapedia.Languages.Agda.StaticSpecification.Examples
