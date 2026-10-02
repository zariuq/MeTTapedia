import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.RootPreservation

/-!
# Annotated templates for the decoding of proposition codes

The decoding templates of implication, of every quantifier instance and of every
equation instance satisfy `TemplateTyped` (`imp_templateTyped`,
`all_templateTyped`, `eq_templateTyped`). Their elaborated right sides are typed
in the contexts and at the types recovered from their left sides. Simple types
over `prop`, the numbers and the sets are formed in the universe of proofs
(`typeAt_formed`), and their annotations are closed (`subst_liftTm_typeAt`).

These are inputs to the generic schema-preservation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open AlgebraicSchema (SchemaFamily)
open FormationSensitiveHOLInterface (typeAt typeAt_rename)
open Mettapedia.Logic

namespace CodeModel

/-! ## Universes and declared constants -/

section Constants

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The universe at a level, annotated. -/
abbrev CU {n : Nat} (l : LevelExpr Nat) : CTm Tower.Head n := .head (.sort l)

theorem CU_typed (l : LevelExpr Nat) : CTyped objectChurch Γ (CU l) (CU (.succ l)) :=
  .headType (.sort l)

/-- `max 0 0` is below `0`. -/
theorem cumulative_max_zero :
    objectRules.cumulative (.sort (.max Tower.zero Tower.zero)) (.sort Tower.zero) := fun _ => by
  simp [LevelExpr.eval, LevelTower.zero]

/-- A declared type without abstractions is the annotated declared type. -/
theorem objectChurch_declared {c : DeclName} {T : Tower.Tm 0}
    (h : objectRules.constantType c = some T) (lf : lamFree T = true) :
    objectChurch.constantType c = some (liftTm T) := by
  rw [objectChurch_constantType]
  exact elabDeclarations_lamFree (c := c) (T := T) objectRules.constantType h lf

/-- A constant declared at a universe `U₀`-typed type, in every context. -/
theorem const_typed {c : DeclName} {T : Tower.Tm 0} (h : objectRules.constantType c = some T)
    (lf : lamFree T = true) {u : Tower.Head} (formed : CTyped objectChurch .nil (liftTm T) (.head u))
    (hu : objectRules.isUniverse u) :
    CTyped objectChurch Γ (.const c) (liftTm T).liftClosed :=
  .const (objectChurch_declared h lf) formed hu

/-- A constant declared at `U₀`. -/
theorem const_U0_typed {c : DeclName}
    (h : objectRules.constantType c = some (.head (.sort Tower.zero))) :
    CTyped objectChurch Γ (.const c) (CU Tower.zero) :=
  const_typed h rfl (CU_typed Tower.zero) (.sort _)

end Constants

/-! ## Simple types -/

/-- A simple type has no abstraction. -/
theorem lamFree_typeAt : ∀ (type : HOL.Ty SetProfile.SetBase) (n : Nat),
    lamFree (typeAt SetProfile.types n type) = true
  | .prop, _ => rfl
  | .base _, _ => rfl
  | .arr a b, n => by
      simp only [typeAt, lamFree, lamFree_typeAt a n, lamFree_typeAt b (n + 1), Bool.and_self]

theorem liftClosed_liftTm {n : Nat} (t : Tower.Tm 0) :
    (liftTm t).liftClosed = (liftTm (Presentation.liftClosed t) : CTm Tower.Head n) := by
  unfold CTm.liftClosed Presentation.liftClosed
  rw [liftTm_rename]

/-- **The simple types are formed in the universe of proofs.** -/
theorem typeAt_formed : ∀ (type : HOL.Ty SetProfile.SetBase) {n : Nat} (Γ : CCtx Tower.Head n),
    CTyped objectChurch Γ (liftTm (typeAt SetProfile.types n type)) (CU Tower.zero)
  | .prop, _, _ => const_U0_typed (c := SetProfile.propName) (by decide)
  | .base .num, _, _ => const_U0_typed (c := SetProfile.baseName .num) (by decide)
  | .base .set, _, _ => const_U0_typed (c := SetProfile.baseName .set) (by decide)
  | .arr a b, _, Γ =>
      .sub (.piForm (typeAt_formed a Γ) (.sort _)
        (typeAt_formed b (.snoc Γ (liftTm (typeAt SetProfile.types _ a)))) (.sort _) (.sorts _ _))
        (.subUniv cumulative_max_zero)

/-! ## Decoding -/

section Decoding

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The decoder, declared at `prop → U₀`. -/
theorem holds_typed :
    CTyped objectChurch Γ (.const holdsN) (.pi (.const propN) (CU Tower.zero)) :=
  const_typed (T := programCodes.holdsType) (by decide) rfl
    (.piForm (const_U0_typed (c := propN) (by decide)) (.sort _) (CU_typed _) (.sort _)
      (.sorts _ _)) (.sort _)

/-- A decoded code is a type of the universe of proofs. -/
theorem holds_app_typed {c : CTm Tower.Head n} (tc : CTyped objectChurch Γ c (.const propN)) :
    CTyped objectChurch Γ (.app (.const holdsN) c) (CU Tower.zero) :=
  .appElim holds_typed tc

/-- The right side of the decoding of an implication is typed. -/
theorem imp_templateTyped : TemplateTyped (k := 2) objectChurch objectDecls
    (.app (.const holdsN) (.app (.app (.const impN) (.var 1)) (.var 0)))
    (.pi (.app (.const holdsN) (.var 1)) (.app (.const holdsN) (Presentation.rename wk (.var 0)))) := by
  refine ⟨liftCtx (.snoc (.snoc .nil programCodes.propT) programCodes.propT), CU Tower.zero, ?_, ?_, ?_⟩
  · intro i
    revert i
    decide
  · decide
  · rw [elabRight, elab_lamFree _ rfl]
    exact .sub (.piForm (holds_app_typed (.var 1)) (.sort _) (holds_app_typed (.var 1)) (.sort _)
      (.sorts _ _)) (.subUniv cumulative_max_zero)

theorem objectDecls_allName (type : HOL.Ty SetProfile.SetBase) :
    objectDecls (SetProfile.allName type) = some (liftTm (SetProfile.allType type)) :=
  elabDeclarations_lamFree objectRules.constantType (declared_allName type)
    (lamFree_typeAt (.arr (.arr type .prop) .prop) 0)

theorem objectDecls_eqName (type : HOL.Ty SetProfile.SetBase) :
    objectDecls (SetProfile.eqName type) = some (liftTm (SetProfile.eqType type)) :=
  elabDeclarations_lamFree objectRules.constantType (declared_eqName type)
    (lamFree_typeAt (.arr type (.arr type .prop)) 0)

theorem objectDecls_holds : objectDecls holdsN = some (liftTm programCodes.holdsType) :=
  elabDeclarations_lamFree objectRules.constantType (by decide) rfl

theorem liftClosed_liftTm_typeAt {m : Nat} (type : HOL.Ty SetProfile.SetBase) :
    (liftTm (typeAt SetProfile.types 0 type)).liftClosed =
      (liftTm (typeAt SetProfile.types m type) : CTm Tower.Head m) := by
  rw [liftClosed_liftTm]
  unfold Presentation.liftClosed
  rw [typeAt_rename]

/-- The right side of the decoding of a quantifier instance is typed. -/
theorem all_templateTyped (type : HOL.Ty SetProfile.SetBase) :
    TemplateTyped (k := 1) objectChurch objectDecls
      (.app (.const holdsN) (.app (.const (SetProfile.allName type)) (.var 0)))
      (.pi (liftClosed (typeAt SetProfile.types 0 type))
        (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))) := by
  refine ⟨liftCtx (.snoc .nil (typeAt SetProfile.types 0 (.arr type .prop))), CU Tower.zero,
    ?_, ?_, ?_⟩
  · intro i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [patternKnowledge, elaborate, objectDecls_allName,
      Option.map_some, Knowledge.merge, Knowledge.empty, if_true]
    rw [show SetProfile.allType type = typeAt SetProfile.types 0 (.arr (.arr type .prop) .prop)
      from rfl, liftClosed_liftTm_typeAt]
    simp only [liftCtx_lookup, Ctx.lookup_snoc_zero, typeAt_rename]
    rfl
  · simp only [leftType, elaborate, objectDecls_holds, objectDecls_allName, Option.map_some]
    rfl
  · have lf : lamFree ((Tm.pi (liftClosed (typeAt SetProfile.types 0 type))
        (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))) : Tower.Tm 1) =
        true := by
      simp only [lamFree, Presentation.liftClosed, typeAt_rename, lamFree_typeAt,
        Presentation.rename, Bool.and_self]
    rw [elabRight, elab_lamFree _ lf]
    have hdom : (liftTm (liftClosed (typeAt SetProfile.types 0 type)) : CTm Tower.Head 1) =
        liftTm (typeAt SetProfile.types 1 type) := by
      unfold Presentation.liftClosed
      rw [typeAt_rename]
    have hf : (liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 (.arr type .prop)))
        (liftClosed (typeAt SetProfile.types 0 type)))).lookup 1 =
        .pi (liftTm (typeAt SetProfile.types 2 type)) (.const propN) := by
      rw [liftCtx_lookup]
      change liftTm (Presentation.rename wk (Presentation.rename wk
        (typeAt SetProfile.types 0 (.arr type .prop)))) = _
      simp only [typeAt_rename]
      rfl
    have hx : (liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 (.arr type .prop)))
        (liftClosed (typeAt SetProfile.types 0 type)))).lookup 0 =
        liftTm (typeAt SetProfile.types 2 type) := by
      simp only [liftCtx_lookup, Ctx.lookup_snoc_zero, Presentation.liftClosed, typeAt_rename]
    have tf := CDerivable.var (P := objectChurch)
      (Γ := liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 (.arr type .prop)))
        (liftClosed (typeAt SetProfile.types 0 type)))) 1
    have tx := CDerivable.var (P := objectChurch)
      (Γ := liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 (.arr type .prop)))
        (liftClosed (typeAt SetProfile.types 0 type)))) 0
    rw [hf] at tf
    rw [hx] at tx
    have body := holds_app_typed (CDerivable.appElim tf tx)
    have tdom := typeAt_formed type (liftCtx (.snoc .nil (typeAt SetProfile.types 0 (.arr type .prop))))
    show CTyped objectChurch _ (.pi (liftTm (liftClosed (typeAt SetProfile.types 0 type)))
      (.app (.const holdsN) (.app (.var 1) (.var 0)))) _
    rw [← hdom] at tdom
    exact .sub (.piForm tdom (.sort _) body (.sort _) (.sorts _ _)) (.subUniv cumulative_max_zero)

/-- A simple type, annotated, is closed: substitution leaves it in place. -/
theorem subst_liftTm_typeAt {n m : Nat} (σ : CSub Tower.Head n m)
    (type : HOL.Ty SetProfile.SetBase) :
    (liftTm (typeAt SetProfile.types n type)).subst σ = liftTm (typeAt SetProfile.types m type) := by
  rw [← liftClosed_liftTm_typeAt (m := n), CTm.subst_liftClosed, liftClosed_liftTm_typeAt]

/-- The annotated type of `eq@A`, in any context. -/
theorem liftClosed_liftTm_eqType {m : Nat} (type : HOL.Ty SetProfile.SetBase) :
    (liftTm (SetProfile.eqType type)).liftClosed =
      (.pi (liftTm (typeAt SetProfile.types m type))
        (.pi (liftTm (typeAt SetProfile.types (m + 1) type)) (.const propN)) : CTm Tower.Head m) := by
  rw [show SetProfile.eqType type = typeAt SetProfile.types 0 (.arr type (.arr type .prop)) from rfl,
    liftClosed_liftTm_typeAt]
  rfl

/-- The right side of the decoding of an equation instance is typed. -/
theorem eq_templateTyped (type : HOL.Ty SetProfile.SetBase) :
    TemplateTyped (k := 2) objectChurch objectDecls
      (.app (.const holdsN) (.app (.app (.const (SetProfile.eqName type)) (.var 1)) (.var 0)))
      (.id (liftClosed (typeAt SetProfile.types 0 type)) (.var 1) (.var 0)) := by
  refine ⟨liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 type))
    (typeAt SetProfile.types 1 type)), CU Tower.zero, ?_, ?_, ?_⟩
  · intro i
    simp only [patternKnowledge, elaborate, objectDecls_eqName, Option.map_some,
      Knowledge.merge, Knowledge.empty, liftClosed_liftTm_eqType, CTm.inst0, CTm.subst,
      subst_liftTm_typeAt, liftCtx_lookup]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.isValue, zero_ne_one, if_false, if_true]
      rw [Ctx.lookup_snoc_zero, typeAt_rename]
    · obtain rfl : j = 0 := Subsingleton.elim j 0
      simp only [Fin.succ_zero_eq_one, Fin.isValue, if_true]
      change some _ = some (liftTm (Presentation.rename wk (Presentation.rename wk
        (typeAt SetProfile.types 0 type))))
      rw [typeAt_rename, typeAt_rename]
  · simp only [leftType, elaborate, objectDecls_holds, objectDecls_eqName, Option.map_some]
    rfl
  · have lf : lamFree ((Tm.id (liftClosed (typeAt SetProfile.types 0 type)) (.var 1) (.var 0)) :
        Tower.Tm 2) = true := by
      simp only [lamFree, Presentation.liftClosed, typeAt_rename, lamFree_typeAt, Bool.and_self]
    rw [elabRight, elab_lamFree _ lf]
    have hA : (liftTm (liftClosed (typeAt SetProfile.types 0 type)) : CTm Tower.Head 2) =
        liftTm (typeAt SetProfile.types 2 type) := by
      unfold Presentation.liftClosed
      rw [typeAt_rename]
    have hx : ∀ i : Fin 2, (liftCtx (.snoc (.snoc .nil (typeAt SetProfile.types 0 type))
        (typeAt SetProfile.types 1 type))).lookup i = liftTm (typeAt SetProfile.types 2 type) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [liftCtx_lookup, Ctx.lookup_snoc_zero, typeAt_rename]
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        rw [liftCtx_lookup]
        change liftTm (Presentation.rename wk (Presentation.rename wk
          (typeAt SetProfile.types 0 type))) = _
        rw [typeAt_rename, typeAt_rename]
    have t1 := CDerivable.var (P := objectChurch) (Γ := liftCtx (.snoc (.snoc .nil
      (typeAt SetProfile.types 0 type)) (typeAt SetProfile.types 1 type))) 1
    have t0 := CDerivable.var (P := objectChurch) (Γ := liftCtx (.snoc (.snoc .nil
      (typeAt SetProfile.types 0 type)) (typeAt SetProfile.types 1 type))) 0
    rw [hx] at t1 t0
    show CTyped objectChurch _ (.id (liftTm (liftClosed (typeAt SetProfile.types 0 type)))
      (.var 1) (.var 0)) _
    rw [hA]
    exact .idForm (typeAt_formed type _) (.sort _) t1 t0

end Decoding

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
