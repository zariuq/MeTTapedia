import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeIdentityPaths
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeIdentityExtension
import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeHedberg

/-!
# A native two-constructor Boolean datatype for identity-region evidence

The signature has a Boolean type, two constructors and a dependent eliminator
with its two iota rules. Its declaration formation and used eliminator instances
are checked in the formation-sensitive native calculus. This is a genuine
computational signature extension; its roots are not discarded as opacity.

The module does not claim normalization of the extended calculus.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRegion

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic
open SharedJudgmentIdentityRegions (arrow)

variable {n m : Nat}

def zero : LevelExpr := Tower.zero
def one : LevelExpr := .succ zero
def two : LevelExpr := .succ one

def boolName : DeclName := `BooleanRegion.Bool
def falseName : DeclName := `BooleanRegion.false
def trueName : DeclName := `BooleanRegion.true
def eliminateName : DeclName := `BooleanRegion.eliminate

def boolTm : Tower.Tm n := .const boolName
def falseTm : Tower.Tm n := .const falseName
def trueTm : Tower.Tm n := .const trueName

def eliminate (motive onFalse onTrue value : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const eliminateName) motive) onFalse) onTrue) value

def motiveType : Tower.Tm n := .pi boolTm (sortTm two)

def eliminateType : Tower.Tm 0 :=
  .pi motiveType (.pi (.app (.var 0) falseTm)
    (.pi (.app (.var 1) trueTm) (.pi boolTm (.app (.var 3) (.var 0)))))

inductive IotaEvidence (n : Nat) : Tower.Tm n → Tower.Tm n → Type where
  | onFalse (motive onFalse onTrue : Tower.Tm n) :
      IotaEvidence n (eliminate motive onFalse onTrue falseTm) onFalse
  | onTrue (motive onFalse onTrue : Tower.Tm n) :
      IotaEvidence n (eliminate motive onFalse onTrue trueTm) onTrue

def iota : RootComputation Tower.Head where
  step {n} left right := Nonempty (IotaEvidence n left right)
  rename := by
    intro n m rho left right evidence
    rcases evidence with ⟨evidence⟩
    cases evidence with
    | onFalse => exact ⟨.onFalse _ _ _⟩
    | onTrue => exact ⟨.onTrue _ _ _⟩
  substitute := by
    intro n m sigma left right evidence
    rcases evidence with ⟨evidence⟩
    cases evidence with
    | onFalse => exact ⟨.onFalse _ _ _⟩
    | onTrue => exact ⟨.onTrue _ _ _⟩

def declarations : List (DeclName × Entry Tower.Head) :=
  [(boolName, { type := sortTm zero }), (falseName, { type := boolTm }),
   (trueName, { type := boolTm }), (eliminateName, { type := eliminateType })]

def signature : Signature Tower.Head where
  entries := (Signature.ofList declarations).entries
  computation := iota

def baseRules : Rules Tower.Head := SharedJudgmentNativeIdentityPaths.rules one Signature.empty
def rules : Rules Tower.Head := extendRules baseRules signature

theorem bool_lookup : rules.constantType boolName = some (sortTm zero) := by decide
theorem false_lookup : rules.constantType falseName = some boolTm := by decide
theorem true_lookup : rules.constantType trueName = some boolTm := by decide
theorem eliminate_lookup : rules.constantType eliminateName = some eliminateType := by decide

theorem bool_typed (context : Tower.Ctx n) : Typing rules context boolTm (sortTm zero) :=
  .const bool_lookup (.headType (.sort zero)) (.sort one)

theorem false_typed (context : Tower.Ctx n) : Typing rules context falseTm boolTm :=
  .const false_lookup (bool_typed .nil) (.sort zero)

theorem true_typed (context : Tower.Ctx n) : Typing rules context trueTm boolTm :=
  .const true_lookup (bool_typed .nil) (.sort zero)

theorem bool_typed_one (context : Tower.Ctx n) : Typing rules context boolTm (sortTm one) :=
  .cumul (bool_typed context) (fun _ => Nat.le_succ _)

theorem bool_typed_two (context : Tower.Ctx n) : Typing rules context boolTm (sortTm two) :=
  .cumul (bool_typed context) (fun _ => Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))

def motiveLevel : LevelExpr := .max zero (.succ two)
def eliminateLevel : LevelExpr := .max motiveLevel (.max two (.max two (.max zero two)))

theorem motiveType_formed (context : Tower.Ctx n) :
    Typing rules context motiveType (sortTm motiveLevel) :=
  .piForm (bool_typed context) (.sort zero) (.headType (.sort two)) (.sort (.succ two))
    (.sorts zero (.succ two))

theorem motive_apply_typed {context : Tower.Ctx n} {motive value : Tower.Tm n}
    (motiveTyped : Typing rules context motive motiveType)
    (valueTyped : Typing rules context value boolTm) :
    Typing rules context (.app motive value) (sortTm two) := by
  exact Typing.appElim motiveTyped valueTyped

theorem eliminateType_formed : Typing rules .nil eliminateType (sortTm eliminateLevel) := by
  apply Typing.piForm (motiveType_formed .nil) (.sort motiveLevel) _ (.sort (.max two (.max two (.max zero two))))
    (.sorts motiveLevel (.max two (.max two (.max zero two))))
  apply Typing.piForm (motive_apply_typed (.var 0) (false_typed _)) (.sort two) _
    (.sort (.max two (.max zero two))) (.sorts two (.max two (.max zero two)))
  apply Typing.piForm (motive_apply_typed (.var 1) (true_typed _)) (.sort two) _
    (.sort (.max zero two)) (.sorts two (.max zero two))
  exact Typing.piForm (bool_typed _) (.sort zero)
    (motive_apply_typed (.var 3) (.var 0)) (.sort two) (.sorts zero two)

theorem eliminate_constant_typed (context : Tower.Ctx n) :
    Typing rules context (.const eliminateName) (liftClosed eliminateType) :=
  .const eliminate_lookup eliminateType_formed (.sort eliminateLevel)

@[simp] theorem substitute_weaken (argument term : Tower.Tm n) :
    subst (subst0 argument) (rename wk term) = term := inst0_rename_wk argument term

theorem eliminate_typed {context : Tower.Ctx n} {motive onFalse onTrue value : Tower.Tm n}
    (motiveTyped : Typing rules context motive motiveType)
    (falseTyped : Typing rules context onFalse (.app motive falseTm))
    (trueTyped : Typing rules context onTrue (.app motive trueTm))
    (valueTyped : Typing rules context value boolTm) :
    Typing rules context (eliminate motive onFalse onTrue value) (.app motive value) := by
  have first := Typing.appElim (eliminate_constant_typed context) motiveTyped
  have firstExact : Typing rules context (.app (.const eliminateName) motive)
      (.pi (.app motive falseTm)
        (.pi (.app (rename wk motive) trueTm)
          (.pi boolTm (.app (rename wk (rename wk (rename wk motive))) (.var 0))))) := by
    convert first using 1
    rfl
  have second := Typing.appElim firstExact falseTyped
  have secondExact : Typing rules context (.app (.app (.const eliminateName) motive) onFalse)
      (.pi (.app motive trueTm) (.pi boolTm (.app (rename wk (rename wk motive)) (.var 0)))) := by
    simpa only [inst0, subst, subst_liftSub_wk, substitute_weaken, liftSub,
      boolTm, trueTm, Fin.cases_zero] using second
  have third := Typing.appElim secondExact trueTyped
  have thirdExact : Typing rules context (.app (.app (.app (.const eliminateName) motive) onFalse) onTrue)
      (.pi boolTm (.app (rename wk motive) (.var 0))) := by
    simpa only [inst0, subst, subst_liftSub_wk, substitute_weaken, liftSub,
      boolTm, Fin.cases_zero] using third
  simpa only [eliminate, inst0, subst, substitute_weaken, subst0, Fin.cases_zero]
    using Typing.appElim thirdExact valueTyped

theorem iota_false (motive onFalse onTrue : Tower.Tm n) :
    rules.computation.step (eliminate motive onFalse onTrue falseTm) onFalse :=
  .declared ⟨.onFalse _ _ _⟩

theorem iota_true (motive onFalse onTrue : Tower.Tm n) :
    rules.computation.step (eliminate motive onFalse onTrue trueTm) onTrue :=
  .declared ⟨.onTrue _ _ _⟩

theorem false_branch_preserves {context : Tower.Ctx n} {motive onFalse onTrue : Tower.Tm n}
    (motiveTyped : Typing rules context motive motiveType)
    (falseTyped : Typing rules context onFalse (.app motive falseTm))
    (trueTyped : Typing rules context onTrue (.app motive trueTm)) :
    Typing rules context (eliminate motive onFalse onTrue falseTm) (.app motive falseTm) ∧
      Typing rules context onFalse (.app motive falseTm) :=
  ⟨eliminate_typed motiveTyped falseTyped trueTyped (false_typed _), falseTyped⟩

theorem true_branch_preserves {context : Tower.Ctx n} {motive onFalse onTrue : Tower.Tm n}
    (motiveTyped : Typing rules context motive motiveType)
    (falseTyped : Typing rules context onFalse (.app motive falseTm))
    (trueTyped : Typing rules context onTrue (.app motive trueTm)) :
    Typing rules context (eliminate motive onFalse onTrue trueTm) (.app motive trueTm) ∧
      Typing rules context onTrue (.app motive trueTm) :=
  ⟨eliminate_typed motiveTyped falseTyped trueTyped (true_typed _), trueTyped⟩

/-! ## Native discrimination rows and transport into them -/

def emptyTm : Tower.Tm n := .pi (sortTm zero) (.var 0)

theorem empty_formed (context : Tower.Ctx n) : Typing rules context emptyTm (sortTm one) := by
  have raw : Typing rules context emptyTm (sortTm (.max one zero)) :=
    .piForm (.headType (.sort zero)) (.sort one) (.var 0) (.sort zero) (.sorts one zero)
  exact .cumul raw (by intro valuation; simp [LevelExpr.eval, one, zero, Tower.zero])

def emptyEliminate (impossible target : Tower.Tm n) : Tower.Tm n := .app impossible target

theorem empty_eliminate_typed {context : Tower.Ctx n} {impossible target : Tower.Tm n}
    (emptyTyped : Typing rules context impossible emptyTm)
    (targetFormed : Typing rules context target (sortTm zero)) :
    Typing rules context (emptyEliminate impossible target) target :=
  .appElim emptyTyped targetFormed

def point (side : Bool) : Tower.Tm n := if side then trueTm else falseTm

theorem point_typed (side : Bool) (context : Tower.Ctx n) : Typing rules context (point side) boolTm := by
  cases side
  · exact false_typed context
  · exact true_typed context

def typeMotive : Tower.Tm n := .lam (sortTm one)

theorem typeMotive_typed (context : Tower.Ctx n) : Typing rules context typeMotive motiveType :=
  .lamIntro (motiveType_formed context) (.sort motiveLevel) (.headType (.sort one))

theorem typeMotive_beta (value : Tower.Tm n) :
    Conv rules.headEq (.app typeMotive value) (sortTm one) rules.computation :=
  .rel _ _ (.betaPi _ _)

def codeRow (side : Bool) (value : Tower.Tm n) : Tower.Tm n :=
  eliminate typeMotive (if side then emptyTm else boolTm) (if side then boolTm else emptyTm) value

@[simp] theorem codeRow_subst (sigma : Sub Tower.Head n m) (side : Bool) (value : Tower.Tm n) :
    subst sigma (codeRow side value) = codeRow side (subst sigma value) := by
  cases side <;> rfl

@[simp] theorem codeRow_rename (rho : Ren n m) (side : Bool) (value : Tower.Tm n) :
    rename rho (codeRow side value) = codeRow side (rename rho value) := by
  cases side <;> rfl

@[simp] theorem point_subst (sigma : Sub Tower.Head n m) (side : Bool) :
    subst sigma (point side) = point side := by cases side <;> rfl

@[simp] theorem point_rename (rho : Ren n m) (side : Bool) :
    rename rho (point side) = point side := by cases side <;> rfl

theorem codeRow_typed {context : Tower.Ctx n} (side : Bool) {value : Tower.Tm n}
    (valueTyped : Typing rules context value boolTm) :
    Typing rules context (codeRow side value) (sortTm one) := by
  have branches (entry : Tower.Tm n) (typed : Typing rules context entry (sortTm one)) (target : Tower.Tm n)
      (targetTyped : Typing rules context target boolTm) :
      Typing rules context entry (.app typeMotive target) :=
    .conv typed (motive_apply_typed (typeMotive_typed context) targetTyped) (.sort two)
      (typeMotive_beta target).symm
  refine Typing.conv (R := rules) ?_ (.headType (.sort one)) (.sort two) (typeMotive_beta value)
  unfold codeRow
  apply eliminate_typed (typeMotive_typed context) _ _ valueTyped
  · cases side
    · exact branches boolTm (bool_typed_one context) falseTm (false_typed context)
    · exact branches emptyTm (empty_formed context) falseTm (false_typed context)
  · cases side
    · exact branches emptyTm (empty_formed context) trueTm (true_typed context)
    · exact branches boolTm (bool_typed_one context) trueTm (true_typed context)

theorem codeRow_same (side : Bool) :
    Conv rules.headEq (codeRow side (point side) : Tower.Tm n) boolTm rules.computation := by
  cases side
  · exact .rel _ _ (.root (iota_false ..))
  · exact .rel _ _ (.root (iota_true ..))

theorem codeRow_opposite (side : Bool) :
    Conv rules.headEq (codeRow side (point (!side)) : Tower.Tm n) emptyTm rules.computation := by
  cases side
  · exact .rel _ _ (.root (iota_true ..))
  · exact .rel _ _ (.root (iota_false ..))

def encode (side : Bool) (right path : Tower.Tm n) : Tower.Tm n :=
  identityEliminateApp boolTm (point side) (.lam (.lam (codeRow side (.var 1)))) trueTm right path

theorem encode_typed {context : Tower.Ctx n} (side : Bool)
    (formed : ContextFormation rules context) {right path : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm)
    (pathTyped : Typing rules context path (.id boolTm (point side) right)) :
    Typing rules context (encode side right path) (codeRow side right) := by
  have body := codeRow_typed side (context := FormationSensitiveBasedIdentity.basedContext context boolTm (point side))
    (value := .var 1) (.var 1)
  have method : Typing rules context trueTm
      (subst (FormationSensitiveBasedIdentity.reflexivitySub (point side)) (codeRow side (.var 1))) := by
    rw [codeRow_subst]
    exact .conv (true_typed context) (codeRow_typed side (point_typed side context)) (.sort one)
      (codeRow_same side).symm
  have result := SharedJudgmentNativeIdentityExtension.ofBody_point (theta := fun _ => one)
    (signature := signature) formed (bool_typed_one context) (point_typed side context)
    (codeRow side (.var 1)) body method rightTyped pathTyped
  have reduce : subst (FormationSensitiveBasedIdentity.pointSub right path) (codeRow side (.var 1)) =
      codeRow side right := by
    rw [codeRow_subst]
    rfl
  simpa only [reduce, encode, rules, baseRules, SharedJudgmentNativeIdentityExtension.rules,
    SharedJudgmentNativeIdentityExtension.base] using result.typing

def discriminate (side : Bool) (path : Tower.Tm n) : Tower.Tm n := encode side (point (!side)) path

theorem discriminate_typed {context : Tower.Ctx n} (side : Bool)
    (formed : ContextFormation rules context) {path : Tower.Tm n}
    (pathTyped : Typing rules context path (.id boolTm (point side) (point (!side)))) :
    Typing rules context (discriminate side path) emptyTm :=
  .conv (encode_typed side formed (point_typed (!side) context) pathTyped)
    (empty_formed context) (.sort one) (codeRow_opposite side)

/-! ## Dependent Boolean cases and the based selector -/

theorem pi_formed {context : Tower.Ctx n} {domain : Tower.Tm n} {family : Tower.Tm (n + 1)}
    {level : LevelExpr} (domainFormed : Typing rules context domain (sortTm level))
    (familyFormed : Typing rules (.snoc context domain) family (sortTm level)) :
    Typing rules context (.pi domain family) (sortTm level) :=
  .cumul (.piForm domainFormed (.sort level) familyFormed (.sort level) (.sorts level level))
    (fun _ => by simp [LevelExpr.eval])

theorem lambda_typed {context : Tower.Ctx n} {domain : Tower.Tm n}
    {family body : Tower.Tm (n + 1)} {level : LevelExpr}
    (domainFormed : Typing rules context domain (sortTm level))
    (familyFormed : Typing rules (.snoc context domain) family (sortTm level))
    (bodyTyped : Typing rules (.snoc context domain) body family) :
    Typing rules context (.lam body) (.pi domain family) :=
  .lamIntro (pi_formed domainFormed familyFormed) (.sort level) bodyTyped

theorem arrow_formed {context : Tower.Ctx n} {domain codomain : Tower.Tm n} {level : LevelExpr}
    (domainFormed : Typing rules context domain (sortTm level))
    (codomainFormed : Typing rules context codomain (sortTm level)) :
    Typing rules context (arrow domain codomain) (sortTm level) :=
  pi_formed domainFormed codomainFormed.weaken

theorem inst_typed {context : Tower.Ctx n} {body : Tower.Tm (n + 1)} {value : Tower.Tm n}
    {level : LevelExpr} (bodyFormed : Typing rules (.snoc context boolTm) body (sortTm level))
    (valueTyped : Typing rules context value boolTm) :
    Typing rules context (inst0 value body) (sortTm level) := by
  have base := FormationSensitiveContextual.identityTyped (rules := rules) context
  have sub := base.extend (type := boolTm) (term := value) valueTyped
  exact bodyFormed.substitute sub

def casesTerm (body : Tower.Tm (n + 1)) (onFalse onTrue value : Tower.Tm n) : Tower.Tm n :=
  eliminate (.lam body) onFalse onTrue value

theorem cases_typed {context : Tower.Ctx n} {body : Tower.Tm (n + 1)}
    {onFalse onTrue value : Tower.Tm n} {level : LevelExpr}
    (levelBound : ∀ valuation, LevelExpr.eval valuation level ≤ LevelExpr.eval valuation two)
    (bodyFormed : Typing rules (.snoc context boolTm) body (sortTm level))
    (falseTyped : Typing rules context onFalse (inst0 falseTm body))
    (trueTyped : Typing rules context onTrue (inst0 trueTm body))
    (valueTyped : Typing rules context value boolTm) :
    Typing rules context (casesTerm body onFalse onTrue value) (inst0 value body) := by
  have motive : Typing rules context (.lam body) motiveType :=
    .lamIntro (motiveType_formed context) (.sort motiveLevel) (.cumul bodyFormed levelBound)
  have beta (term : Tower.Tm n) : Conv rules.headEq (.app (.lam body) term) (inst0 term body) rules.computation :=
    .rel _ _ (.betaPi _ _)
  have cases := eliminate_typed motive
    (.conv falseTyped (motive_apply_typed motive (false_typed context)) (.sort two) (beta falseTm).symm)
    (.conv trueTyped (motive_apply_typed motive (true_typed context)) (.sort two) (beta trueTm).symm)
    valueTyped
  exact .conv cases (inst_typed bodyFormed valueTyped) (.sort level) (beta value)

def pathType (side : Bool) (right : Tower.Tm n) : Tower.Tm n := .id boolTm (point side) right

@[simp] theorem pathType_rename (rho : Ren n m) (side : Bool) (right : Tower.Tm n) :
    rename rho (pathType side right) = pathType side (rename rho right) := by
  simp only [pathType, rename, point_rename, boolTm]

@[simp] theorem pathType_subst (sigma : Sub Tower.Head n m) (side : Bool) (right : Tower.Tm n) :
    subst sigma (pathType side right) = pathType side (subst sigma right) := by
  simp only [pathType, subst, point_subst, boolTm]

theorem pathType_formed {context : Tower.Ctx n} (side : Bool) {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) :
    Typing rules context (pathType side right) (sortTm zero) :=
  .idForm (bool_typed context) (.sort zero) (point_typed side context) rightTyped

def selectorBody (side : Bool) : Tower.Tm (n + 1) :=
  arrow (pathType side (.var 0)) (pathType side (.var 0))

theorem selectorBody_formed (side : Bool) (context : Tower.Ctx n) :
    Typing rules (.snoc context boolTm) (selectorBody side) (sortTm zero) :=
  arrow_formed (pathType_formed side (.var 0)) (pathType_formed side (.var 0))

def sameBranch (side : Bool) : Tower.Tm n := .lam (.refl (point side))
def oppositeBranch (side : Bool) : Tower.Tm n :=
  .lam (emptyEliminate (discriminate side (.var 0)) (pathType side (point (!side))))

theorem sameBranch_typed (side : Bool) (context : Tower.Ctx n) :
    Typing rules context (sameBranch side)
      (arrow (pathType side (point side)) (pathType side (point side))) := by
  have domain := pathType_formed side (point_typed side context)
  apply lambda_typed domain domain.weaken
  rw [pathType_rename, point_rename]
  exact .reflIntro (point_typed side _)

theorem oppositeBranch_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) :
    Typing rules context (oppositeBranch side)
      (arrow (pathType side (point (!side))) (pathType side (point (!side)))) := by
  have domain := pathType_formed side (point_typed (!side) context)
  apply lambda_typed domain domain.weaken
  have pathVariable : Typing rules (.snoc context (pathType side (point (!side)))) (.var 0)
      (pathType side (point (!side))) := by
    simpa only [Ctx.lookup_snoc_zero, pathType_rename, point_rename] using
      (Typing.var (R := rules) (Γ := .snoc context (pathType side (point (!side)))) 0)
  simpa only [pathType_rename, point_rename] using empty_eliminate_typed
    (discriminate_typed side (.snoc formed domain (.sort zero)) pathVariable)
    (pathType_formed side (point_typed (!side) _))

def selectorAt (side : Bool) (right : Tower.Tm n) : Tower.Tm n :=
  casesTerm (selectorBody side) (if side then oppositeBranch side else sameBranch side)
    (if side then sameBranch side else oppositeBranch side) right

@[simp] theorem selectorBody_inst (side : Bool) (right : Tower.Tm n) :
    inst0 right (selectorBody side) = arrow (pathType side right) (pathType side right) := by
  cases side <;> simp only [selectorBody, arrow, pathType, point, Bool.false_eq_true, ↓reduceIte,
    trueTm, falseTm, boolTm, inst0, subst, subst_liftSub_wk, subst0, Fin.cases_zero]

theorem selectorAt_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) :
    Typing rules context (selectorAt side right) (arrow (pathType side right) (pathType side right)) := by
  have cases : Typing rules context (selectorAt side right) (inst0 right (selectorBody side)) := by
    apply cases_typed (level := zero) (by intro valuation; simp [zero, two, one, Tower.zero, LevelExpr.eval])
      (selectorBody_formed side context) _ _ rightTyped
    · cases side
      · exact sameBranch_typed false context
      · exact oppositeBranch_typed true formed
    · cases side
      · exact oppositeBranch_typed false formed
      · exact sameBranch_typed true context
  simpa only [selectorBody_inst] using cases

def selector (side : Bool) : Tower.Tm n := .lam (selectorAt side (.var 0))

theorem selector_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) :
    Typing rules context (selector side) (SharedJudgmentNativeHedberg.selectorType boolTm (point side)) := by
  have body := selectorAt_typed side (.snoc formed (bool_typed context) (.sort zero)) (.var 0)
  have result := lambda_typed (bool_typed context) (selectorBody_formed side context) body
  simpa only [selector, SharedJudgmentNativeHedberg.selectorType, selectorBody, pathType,
    point_rename, boolTm, rename] using result

@[simp] theorem selector_rename (rho : Ren n m) (side : Bool) :
    rename rho (selector side) = selector side := by cases side <;> rfl

@[simp] theorem selector_subst (sigma : Sub Tower.Head n m) (side : Bool) :
    subst sigma (selector side) = selector side := by cases side <;> rfl

@[simp] theorem selectorAt_subst (sigma : Sub Tower.Head n m) (side : Bool) (right : Tower.Tm n) :
    subst sigma (selectorAt side right) = selectorAt side (subst sigma right) := by cases side <;> rfl

def selected (side : Bool) (right path : Tower.Tm n) : Tower.Tm n :=
  SharedJudgmentNativeHedberg.select (selector side) right path

@[simp] theorem selected_subst (sigma : Sub Tower.Head n m) (side : Bool) (right path : Tower.Tm n) :
    subst sigma (selected side right path) = selected side (subst sigma right) (subst sigma path) := by
  simp only [selected, SharedJudgmentNativeHedberg.select_substitute, selector_subst]

@[simp] theorem selected_rename (rho : Ren n m) (side : Bool) (right path : Tower.Tm n) :
    rename rho (selected side right path) = selected side (rename rho right) (rename rho path) := by
  simp only [selected, SharedJudgmentNativeHedberg.select, rename, selector_rename]

theorem selected_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right path : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm)
    (pathTyped : Typing rules context path (pathType side right)) :
    Typing rules context (selected side right path) (pathType side right) := by
  have first := Typing.appElim (selector_typed side formed) rightTyped
  have firstExact : Typing rules context (.app (selector side) right)
      (arrow (pathType side right) (pathType side right)) := by
    convert first using 1
    cases side <;> rfl
  simpa only [arrow, inst0_rename_wk, selected, SharedJudgmentNativeHedberg.select]
    using Typing.appElim firstExact pathTyped

theorem selector_beta (side : Bool) (right : Tower.Tm n) :
    Conv rules.headEq (.app (selector side) right) (selectorAt side right) rules.computation := by
  have beta : Conv rules.headEq (.app (selector side) right)
      (inst0 right (selectorAt side (.var 0))) rules.computation := .rel _ _ (.betaPi _ _)
  simpa only [inst0, selectorAt_subst, subst, subst0, Fin.cases_zero] using beta

theorem selected_same_conversion (side : Bool) (path : Tower.Tm n) :
    Conv rules.headEq (selected side (point side) path) (.refl (point side)) rules.computation := by
  have first : Conv rules.headEq (selected side (point side) path)
      (.app (selectorAt side (point side)) path) rules.computation :=
    .congApp (selector_beta side (point side)) (.refl path)
  have branch : Conv rules.headEq (selectorAt side (point side) : Tower.Tm n) (sameBranch side) rules.computation := by
    cases side
    · exact .rel _ _ (.root (iota_false ..))
    · exact .rel _ _ (.root (iota_true ..))
  have last : Conv rules.headEq (.app (sameBranch side) path) (.refl (point side)) rules.computation := by
    cases side <;> exact .rel _ _ (.betaPi _ _)
  exact .trans _ _ _ first (.trans _ _ _ (Conv.congApp branch (.refl _)) last)

/-! ## Signature qualification and exact declared-root boundaries

Formation and freshness of the declarations are separate from a global
preservation theorem. The branch-preservation theorems above qualify the
formation-sensitive instances used here; the exact-root controls below do not
assert normalization or preservation for arbitrary raw typed source terms.
-/

theorem signature_entry_name {name : DeclName} {entry : Entry Tower.Head}
    (lookup : signature.entries name = some entry) :
    name = boolName ∨ name = falseName ∨ name = trueName ∨ name = eliminateName := by
  by_cases isBool : name = boolName
  · exact Or.inl isBool
  by_cases isFalse : name = falseName
  · exact Or.inr (Or.inl isFalse)
  by_cases isTrue : name = trueName
  · exact Or.inr (Or.inr (Or.inl isTrue))
  by_cases isEliminate : name = eliminateName
  · exact Or.inr (Or.inr (Or.inr isEliminate))
  · simp [signature, declarations, Signature.ofList, Signature.insert,
      Signature.empty, isBool, isFalse, isTrue, isEliminate] at lookup

theorem signature_fresh {name : DeclName} {entry : Entry Tower.Head}
    (lookup : signature.entries name = some entry) :
    baseRules.constantType name = none := by
  rcases signature_entry_name lookup with same | same | same | same <;>
    subst name <;> decide

@[simp] theorem signature_valueOf_none (name : DeclName) :
    signature.valueOf? name = none := by
  by_cases isBool : name = boolName
  · subst name; decide
  by_cases isFalse : name = falseName
  · subst name; decide
  by_cases isTrue : name = trueName
  · subst name; decide
  by_cases isEliminate : name = eliminateName
  · subst name; decide
  · simp [signature, declarations, Signature.valueOf?, Signature.ofList,
      Signature.insert, Signature.empty, isBool, isFalse, isTrue, isEliminate]

theorem signature_types_formed {name : DeclName} {type : Tower.Tm 0}
    (lookup : signature.typeOf? name = some type) :
    ∃ level : LevelExpr, Typing rules .nil type (sortTm level) := by
  by_cases isBool : name = boolName
  · subst name
    have typeEquality : type = sortTm zero := by
      change some (sortTm zero) = some type at lookup
      exact (Option.some.inj lookup).symm
    subst type
    exact ⟨one, .headType (.sort zero)⟩
  by_cases isFalse : name = falseName
  · subst name
    have typeEquality : type = boolTm := by
      change some boolTm = some type at lookup
      exact (Option.some.inj lookup).symm
    subst type
    exact ⟨zero, bool_typed .nil⟩
  by_cases isTrue : name = trueName
  · subst name
    have typeEquality : type = boolTm := by
      change some boolTm = some type at lookup
      exact (Option.some.inj lookup).symm
    subst type
    exact ⟨zero, bool_typed .nil⟩
  by_cases isEliminate : name = eliminateName
  · subst name
    have typeEquality : type = eliminateType := by
      change some eliminateType = some type at lookup
      exact (Option.some.inj lookup).symm
    subst type
    exact ⟨eliminateLevel, eliminateType_formed⟩
  · simp [signature, declarations, Signature.typeOf?, Signature.ofList,
      Signature.insert, Signature.empty, isBool, isFalse, isTrue, isEliminate] at lookup

/-- The native J declarations and the Boolean declaration names are disjoint;
all four added declaration types are formed, and none conceals a delta body. -/
theorem signature_formed : signature.Formed baseRules := {
  fresh := signature_fresh
  types := by
    intro name type lookup
    obtain ⟨level, formed⟩ := signature_types_formed lookup
    exact ⟨.sort level, .sort level, formed.toRaw⟩
  values := by
    intro name type value _ valueLookup
    rw [signature_valueOf_none] at valueLookup
    cases valueLookup
  noSelfDelta := by
    intro name value valueLookup
    rw [signature_valueOf_none] at valueLookup
    cases valueLookup
}

theorem false_true_distinct : (falseTm : Tower.Tm n) ≠ trueTm := by
  intro equality
  have names : falseName = trueName := Tm.const.inj equality
  exact (by decide : falseName ≠ trueName) names

theorem iota_false_exact (motive onFalse onTrue result : Tower.Tm n) :
    iota.step (eliminate motive onFalse onTrue falseTm) result ↔ result = onFalse := by
  constructor
  · rintro ⟨step⟩
    generalize sourceEq : eliminate motive onFalse onTrue falseTm = source at step
    cases step with
    | onFalse =>
      exact ((Tm.app.inj (Tm.app.inj (Tm.app.inj sourceEq).1).1).2).symm
    | onTrue =>
      exact False.elim (false_true_distinct (Tm.app.inj sourceEq).2)
  · rintro rfl
    exact ⟨.onFalse _ _ _⟩

theorem iota_true_exact (motive onFalse onTrue result : Tower.Tm n) :
    iota.step (eliminate motive onFalse onTrue trueTm) result ↔ result = onTrue := by
  constructor
  · rintro ⟨step⟩
    generalize sourceEq : eliminate motive onFalse onTrue trueTm = source at step
    cases step with
    | onFalse =>
      exact False.elim (false_true_distinct (Tm.app.inj sourceEq).2.symm)
    | onTrue =>
      exact ((Tm.app.inj (Tm.app.inj sourceEq).1).2).symm
  · rintro rfl
    exact ⟨.onTrue _ _ _⟩

/-- Declared Boolean elimination does not rewrite a neutral argument. This is
about this signature's roots, not all conversions of the ambient calculus. -/
theorem iota_neutral_absent (motive onFalse onTrue result : Tower.Tm (n + 1)) :
    ¬ iota.step (eliminate motive onFalse onTrue (.var 0)) result := by
  rintro ⟨step⟩
  cases step

/-- Inspectable Boolean values are not identified by a declared iota rule. -/
theorem iota_does_not_identify_constructors :
    ¬ iota.step (falseTm : Tower.Tm n) trueTm := by
  rintro ⟨step⟩
  cases step

theorem false_elimination_cannot_choose_true (motive : Tower.Tm n) :
    ¬ iota.step (eliminate motive falseTm trueTm falseTm) trueTm := by
  intro step
  exact false_true_distinct ((iota_false_exact ..).mp step).symm

theorem true_elimination_cannot_choose_false (motive : Tower.Tm n) :
    ¬ iota.step (eliminate motive falseTm trueTm trueTm) falseTm := by
  intro step
  exact false_true_distinct ((iota_true_exact ..).mp step)

#print axioms eliminateType_formed
#print axioms eliminate_typed
#print axioms false_branch_preserves
#print axioms true_branch_preserves
#print axioms codeRow_typed
#print axioms encode_typed
#print axioms discriminate_typed
#print axioms cases_typed
#print axioms oppositeBranch_typed
#print axioms selector_typed
#print axioms signature_formed
#print axioms iota_false_exact
#print axioms iota_true_exact
#print axioms iota_neutral_absent
#print axioms false_elimination_cannot_choose_true

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRegion
