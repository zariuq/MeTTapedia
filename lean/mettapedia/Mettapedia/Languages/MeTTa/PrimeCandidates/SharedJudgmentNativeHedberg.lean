import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeIdentityPaths

/-!
# Internal Hedberg construction over native identity terms

A weakly constant endomap on each based identity type supplies an actual
native UIP proof. Selectors and their weak-constancy evidence are object
terms with independently checked types. The construction uses the native J
declaration, its ordinary computation, and derived path operations. It does
not invoke the external route-family Hedberg theorem or declare UIP.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeHedberg

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open NativeIndexedFamilies NativeIndexedFamilies.Intrinsic
open FormationSensitiveBasedIdentity (doubleWeaken basedContext pointSub reflexivitySub)
open SharedJudgmentIdentityRegions (arrow apply_typed ofBody_point)
open SharedJudgmentNativeIdentityPaths

variable {n m : Nat} {level : LevelExpr Nat} {signature : Signature Tower.Head}
variable {context : Tower.Ctx n}

def selectorType (carrier left : Tower.Tm n) : Tower.Tm n :=
  .pi carrier (arrow (.id (rename wk carrier) (rename wk left) (.var 0))
    (.id (rename wk carrier) (rename wk left) (.var 0)))

def select (selector right path : Tower.Tm n) : Tower.Tm n :=
  .app (.app selector right) path

@[simp] theorem selectorType_substitute (substitution : Sub Tower.Head n m)
    (carrier left : Tower.Tm n) :
    subst substitution (selectorType carrier left) =
      selectorType (subst substitution carrier) (subst substitution left) := by
  simp only [selectorType, arrow, subst, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem selectorType_rename (rho : Ren n m) (carrier left : Tower.Tm n) :
    rename rho (selectorType carrier left) =
      selectorType (rename rho carrier) (rename rho left) := by
  simp only [selectorType, arrow, rename, rename_comp, liftRen, wk, Fin.cases_succ, Fin.cases_zero]

@[simp] theorem select_substitute (substitution : Sub Tower.Head n m)
    (selector right path : Tower.Tm n) :
    subst substitution (select selector right path) =
      select (subst substitution selector) (subst substitution right) (subst substitution path) := rfl

@[simp] theorem arrow_substitute (substitution : Sub Tower.Head n m) (domain codomain : Tower.Tm n) :
    subst substitution (arrow domain codomain) = arrow (subst substitution domain) (subst substitution codomain) := by
  simp only [arrow, subst, subst_liftSub_wk]

@[simp] theorem subst0_weaken (argument term : Tower.Tm n) :
    subst (subst0 argument) (rename wk term) = term := inst0_rename_wk argument term

theorem select_typed {carrier left selector right path : Tower.Tm n}
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left))
    (rightTyped : Typing (rules level signature) context right carrier)
    (pathTyped : Typing (rules level signature) context path (.id carrier left right)) :
    Typing (rules level signature) context (select selector right path) (.id carrier left right) := by
  have first := Typing.appElim selectorTyped rightTyped
  have functionTyped : Typing (rules level signature) context (.app selector right)
      (arrow (.id carrier left right) (.id carrier left right)) := by
    change Typing _ _ _ (subst (subst0 right)
      (arrow (.id (rename wk carrier) (rename wk left) (.var 0))
        (.id (rename wk carrier) (rename wk left) (.var 0)))) at first
    simpa only [arrow_substitute, subst, subst0_weaken, subst0, Fin.cases_zero] using first
  exact apply_typed functionTyped pathTyped

def normalized (carrier left selector right path : Tower.Tm n) : Tower.Tm n :=
  compose carrier left left (inverse carrier left left (select selector left (.refl left)))
    right (select selector right path)

@[simp] theorem normalized_substitute (substitution : Sub Tower.Head n m)
    (carrier left selector right path : Tower.Tm n) :
    subst substitution (normalized carrier left selector right path) =
      normalized (subst substitution carrier) (subst substitution left)
        (subst substitution selector) (subst substitution right) (subst substitution path) := by
  simp only [normalized, compose_substitute, inverse_substitute, select_substitute, subst]

theorem normalized_typed {carrier left selector right path : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left))
    (rightTyped : Typing (rules level signature) context right carrier)
    (pathTyped : Typing (rules level signature) context path (.id carrier left right)) :
    Typing (rules level signature) context (normalized carrier left selector right path)
      (.id carrier left right) :=
  compose_typed formed carrierTyped leftTyped leftTyped rightTyped
    (inverse_typed formed carrierTyped leftTyped leftTyped
      (select_typed selectorTyped leftTyped (.reflIntro leftTyped)))
    (select_typed selectorTyped rightTyped pathTyped)

def fixedMotive (carrier left selector : Tower.Tm n) : Tower.Tm (n + 2) :=
  .id (.id (doubleWeaken carrier) (doubleWeaken left) (.var 1))
    (normalized (doubleWeaken carrier) (doubleWeaken left) (doubleWeaken selector) (.var 1) (.var 0))
    (.var 0)

def fixed (carrier left selector right path : Tower.Tm n) : Tower.Tm n :=
  identityEliminateApp carrier left (.lam (.lam (fixedMotive carrier left selector)))
    (cancellation carrier left left (select selector left (.refl left))) right path

@[simp] theorem fixedMotive_point (carrier left selector right path : Tower.Tm n) :
    subst (pointSub right path) (fixedMotive carrier left selector) =
      .id (.id carrier left right) (normalized carrier left selector right path) path := by
  simp only [fixedMotive, subst, normalized_substitute,
    FormationSensitiveBasedIdentity.pointSub_doubleWeaken]
  rfl

theorem fixedMotive_typed {carrier left selector : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left)) :
    Typing (rules level signature) (basedContext context carrier left)
      (fixedMotive carrier left selector) (sortTm level) := by
  have basedFormed := based_formed formed carrierTyped leftTyped
  have selectorTwice : Typing (rules level signature) (basedContext context carrier left)
      (doubleWeaken selector) (selectorType (doubleWeaken carrier) (doubleWeaken left)) := by
    simpa only [doubleWeaken, selectorType_rename] using
      (twice_typed (carrier := carrier) (left := left) selectorTyped)
  exact .idForm (.idForm (twice_typed carrierTyped) (.sort level) (twice_typed leftTyped) (.var 1))
    (.sort level)
    (normalized_typed basedFormed (twice_typed carrierTyped) (twice_typed leftTyped)
      selectorTwice (.var 1) (.var 0)) (.var 0)

/-- Native path induction proves that cancellation-normalized selection fixes
every path. Weak constancy is not needed for this half of Hedberg. -/
theorem fixed_typed {carrier left selector right path : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left))
    (rightTyped : Typing (rules level signature) context right carrier)
    (pathTyped : Typing (rules level signature) context path (.id carrier left right)) :
    Typing (rules level signature) context (fixed carrier left selector right path)
      (.id (.id carrier left right) (normalized carrier left selector right path) path) := by
  have methodTyped : Typing (rules level signature) context
      (cancellation carrier left left (select selector left (.refl left)))
      (subst (reflexivitySub left) (fixedMotive carrier left selector)) := by
    change Typing _ _ _ (subst (pointSub left (.refl left)) _)
    rw [fixedMotive_point]
    exact cancellation_typed formed carrierTyped leftTyped leftTyped
      (select_typed selectorTyped leftTyped (.reflIntro leftTyped))
  have result := ofBody_point formed carrierTyped leftTyped (fixedMotive carrier left selector)
    (fixedMotive_typed formed carrierTyped leftTyped selectorTyped)
    methodTyped rightTyped pathTyped
  simpa only [fixed, fixedMotive_point] using result.typing

@[simp] theorem fixed_substitute (substitution : Sub Tower.Head n m)
    (carrier left selector right path : Tower.Tm n) :
    subst substitution (fixed carrier left selector right path) =
      fixed (subst substitution carrier) (subst substitution left)
        (subst substitution selector) (subst substitution right) (subst substitution path) := by
  simp only [fixed, identityEliminateApp, subst, fixedMotive, normalized_substitute,
    cancellation_substitute, select_substitute, doubleWeaken, subst_liftSub_wk, liftSub]
  rfl

def prepend (carrier left selector right path : Tower.Tm n) : Tower.Tm n :=
  compose carrier left left (inverse carrier left left (select selector left (.refl left))) right path

@[simp] theorem prepend_substitute (substitution : Sub Tower.Head n m)
    (carrier left selector right path : Tower.Tm n) :
    subst substitution (prepend carrier left selector right path) =
      prepend (subst substitution carrier) (subst substitution left)
        (subst substitution selector) (subst substitution right) (subst substitution path) := by
  simp only [prepend, compose_substitute, inverse_substitute, select_substitute, subst]

theorem prepend_typed {carrier left selector right path : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left))
    (rightTyped : Typing (rules level signature) context right carrier)
    (pathTyped : Typing (rules level signature) context path (.id carrier left right)) :
    Typing (rules level signature) context (prepend carrier left selector right path)
      (.id carrier left right) :=
  compose_typed formed carrierTyped leftTyped leftTyped rightTyped
    (inverse_typed formed carrierTyped leftTyped leftTyped
      (select_typed selectorTyped leftTyped (.reflIntro leftTyped))) pathTyped

def prefixFunction (carrier left selector right : Tower.Tm n) : Tower.Tm n :=
  .lam (prepend (rename wk carrier) (rename wk left) (rename wk selector) (rename wk right) (.var 0))

theorem prefixFunction_typed {carrier left selector right : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left))
    (rightTyped : Typing (rules level signature) context right carrier) :
    Typing (rules level signature) context (prefixFunction carrier left selector right)
      (arrow (.id carrier left right) (.id carrier left right)) := by
  have pathFormed := Typing.idForm carrierTyped (.sort level) leftTyped rightTyped
  have selectorWeakened : Typing (rules level signature) (.snoc context (.id carrier left right))
      (rename wk selector) (selectorType (rename wk carrier) (rename wk left)) := by
    simpa only [selectorType_rename] using selectorTyped.weaken (extension := .id carrier left right)
  exact .lamIntro
    (.piForm pathFormed (.sort level) pathFormed.weaken (.sort level) (.sorts level level))
    (.sort (.max level level))
    (prepend_typed (.snoc formed pathFormed (.sort level)) carrierTyped.weaken leftTyped.weaken
      selectorWeakened rightTyped.weaken (.var 0))

theorem prefixFunction_beta (carrier left selector right path : Tower.Tm n) :
    Conv (rules level signature).headEq (.app (prefixFunction carrier left selector right) path)
      (prepend carrier left selector right path) (rules level signature).computation := by
  have reduction : Conv (rules level signature).headEq
      (.app (prefixFunction carrier left selector right) path)
      (inst0 path (prepend (rename wk carrier) (rename wk left) (rename wk selector)
        (rename wk right) (.var 0))) (rules level signature).computation := .rel _ _ (.betaPi _ _)
  simpa only [inst0, prepend_substitute, subst0_weaken, subst, subst0, Fin.cases_zero] using reduction

def normalizedComparison (carrier left selector right first second constant : Tower.Tm n) : Tower.Tm n :=
  SharedJudgmentIdentityRegions.congruenceTerm (.id carrier left right) (select selector right first)
    (.id carrier left right) (prefixFunction carrier left selector right) (select selector right second) constant

/-- Weak constancy is supplied as typed native identity evidence at the
selected pair, not as an external equality of syntax or a UIP premise. -/
theorem normalizedComparison_typed
    {carrier left selector right first second constant : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left))
    (rightTyped : Typing (rules level signature) context right carrier)
    (firstTyped : Typing (rules level signature) context first (.id carrier left right))
    (secondTyped : Typing (rules level signature) context second (.id carrier left right))
    (constantTyped : Typing (rules level signature) context constant
      (.id (.id carrier left right) (select selector right first) (select selector right second))) :
    Typing (rules level signature) context (normalizedComparison carrier left selector right first second constant)
      (.id (.id carrier left right) (normalized carrier left selector right first)
        (normalized carrier left selector right second)) := by
  have pathFormed := Typing.idForm carrierTyped (.sort level) leftTyped rightTyped
  have firstSelected := select_typed selectorTyped rightTyped firstTyped
  have secondSelected := select_typed selectorTyped rightTyped secondTyped
  have compared := SharedJudgmentIdentityRegions.congruence_typed formed pathFormed pathFormed
    firstSelected secondSelected (prefixFunction_typed formed carrierTyped leftTyped selectorTyped rightTyped)
    constantTyped
  exact .conv compared.typing
    (.idForm pathFormed (.sort level)
      (normalized_typed formed carrierTyped leftTyped selectorTyped rightTyped firstTyped)
      (normalized_typed formed carrierTyped leftTyped selectorTyped rightTyped secondTyped))
    (.sort level) (Conv.congId (.refl _) (prefixFunction_beta ..) (prefixFunction_beta ..))

def hedberg (carrier left selector right first second constant : Tower.Tm n) : Tower.Tm n :=
  compose (.id carrier left right) first (normalized carrier left selector right second)
    (compose (.id carrier left right) first (normalized carrier left selector right first)
      (inverse (.id carrier left right) (normalized carrier left selector right first) first
        (fixed carrier left selector right first))
      (normalized carrier left selector right second)
      (normalizedComparison carrier left selector right first second constant))
    second (fixed carrier left selector right second)

/-- The internal Hedberg core constructs an actual native equality proof
between arbitrary input paths from their selector's weak constancy. -/
theorem hedberg_typed {carrier left selector right first second constant : Tower.Tm n}
    (formed : ContextFormation (rules level signature) context)
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier)
    (selectorTyped : Typing (rules level signature) context selector (selectorType carrier left))
    (rightTyped : Typing (rules level signature) context right carrier)
    (firstTyped : Typing (rules level signature) context first (.id carrier left right))
    (secondTyped : Typing (rules level signature) context second (.id carrier left right))
    (constantTyped : Typing (rules level signature) context constant
      (.id (.id carrier left right) (select selector right first) (select selector right second))) :
    Typing (rules level signature) context (hedberg carrier left selector right first second constant)
      (.id (.id carrier left right) first second) := by
  have pathFormed := Typing.idForm carrierTyped (.sort level) leftTyped rightTyped
  have firstNormalized := normalized_typed formed carrierTyped leftTyped selectorTyped rightTyped firstTyped
  have secondNormalized := normalized_typed formed carrierTyped leftTyped selectorTyped rightTyped secondTyped
  have firstFixed := fixed_typed formed carrierTyped leftTyped selectorTyped rightTyped firstTyped
  have secondFixed := fixed_typed formed carrierTyped leftTyped selectorTyped rightTyped secondTyped
  exact compose_typed formed pathFormed firstTyped secondNormalized secondTyped
    (compose_typed formed pathFormed firstTyped firstNormalized secondNormalized
      (inverse_typed formed pathFormed firstNormalized firstTyped firstFixed)
      (normalizedComparison_typed formed carrierTyped leftTyped selectorTyped rightTyped firstTyped secondTyped constantTyped))
    secondFixed

@[simp] theorem prefixFunction_substitute (substitution : Sub Tower.Head n m)
    (carrier left selector right : Tower.Tm n) :
    subst substitution (prefixFunction carrier left selector right) =
      prefixFunction (subst substitution carrier) (subst substitution left)
        (subst substitution selector) (subst substitution right) := by
  simp only [prefixFunction, subst, prepend_substitute, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem normalizedComparison_substitute (substitution : Sub Tower.Head n m)
    (carrier left selector right first second constant : Tower.Tm n) :
    subst substitution (normalizedComparison carrier left selector right first second constant) =
      normalizedComparison (subst substitution carrier) (subst substitution left)
        (subst substitution selector) (subst substitution right) (subst substitution first)
        (subst substitution second) (subst substitution constant) := by
  simp only [normalizedComparison, SharedJudgmentIdentityRegions.congruenceTerm_substitute,
    prefixFunction_substitute, select_substitute, subst]

@[simp] theorem hedberg_substitute (substitution : Sub Tower.Head n m)
    (carrier left selector right first second constant : Tower.Tm n) :
    subst substitution (hedberg carrier left selector right first second constant) =
      hedberg (subst substitution carrier) (subst substitution left)
        (subst substitution selector) (subst substitution right) (subst substitution first)
        (subst substitution second) (subst substitution constant) := by
  simp only [hedberg, compose_substitute, inverse_substitute, fixed_substitute,
    normalizedComparison_substitute, normalized_substitute, subst]

def selectorLevel (level : LevelExpr Nat) : LevelExpr Nat := .max level (.max level level)

theorem selectorType_formed {carrier left : Tower.Tm n}
    (carrierTyped : Typing (rules level signature) context carrier (sortTm level))
    (leftTyped : Typing (rules level signature) context left carrier) :
    Typing (rules level signature) context (selectorType carrier left) (sortTm (selectorLevel level)) := by
  have pathFormed : Typing (rules level signature) (.snoc context carrier)
      (.id (rename wk carrier) (rename wk left) (.var 0)) (sortTm level) :=
    .idForm carrierTyped.weaken (.sort level) leftTyped.weaken (.var 0)
  exact .piForm carrierTyped (.sort level)
    (.piForm pathFormed (.sort level) pathFormed.weaken (.sort level) (.sorts level level))
    (.sort (.max level level)) (.sorts level (.max level level))

/-- Abstract a genuine local hypothesis. Universe formation is recovered
from the existing regularity theorem, not posited as a new rule. -/
theorem abstract_judgment {domain : Tower.Tm n} {body result : Tower.Tm (n + 1)}
    (judgment : Judgment (rules level signature) (.snoc context domain) body result) :
    Judgment (rules level signature) context (.lam body) (.pi domain result) := by
  obtain ⟨v, resultUniverse, resultFormed⟩ := judgment.regularity
    (NativeIdentityLevelInstantiation.universes (fun _ => level) signature)
  cases judgment.context with
  | snoc previous domainFormed domainUniverse =>
      cases domainUniverse with
      | sort u =>
        cases resultUniverse with
        | sort v =>
          exact ⟨previous, .lamIntro
            (.piForm domainFormed (.sort u) resultFormed.typing (.sort v) (.sorts u v))
            (.sort (.max u v)) judgment.typing⟩

def contextA (level : LevelExpr Nat) : Tower.Ctx 1 := .snoc .nil (sortTm level)
def contextAX (level : LevelExpr Nat) : Tower.Ctx 2 := .snoc (contextA level) (.var 0)
def contextAXC (level : LevelExpr Nat) : Tower.Ctx 3 :=
  .snoc (contextAX level) (selectorType (.var 1) (.var 0))
def contextAXCY (level : LevelExpr Nat) : Tower.Ctx 4 := .snoc (contextAXC level) (.var 2)
def contextAXCYP (level : LevelExpr Nat) : Tower.Ctx 5 :=
  .snoc (contextAXCY level) (.id (.var 3) (.var 2) (.var 0))
def contextAXCYPQ (level : LevelExpr Nat) : Tower.Ctx 6 :=
  .snoc (contextAXCYP level) (.id (.var 4) (.var 3) (.var 1))
def constancyInstanceType : Tower.Tm 6 :=
  .id (.id (.var 5) (.var 4) (.var 2))
    (select (.var 3) (.var 2) (.var 1)) (select (.var 3) (.var 2) (.var 0))
def schemaContext (level : LevelExpr Nat) : Tower.Ctx 7 :=
  .snoc (contextAXCYPQ level) constancyInstanceType

theorem contextAXCYPQ_formed (level : LevelExpr Nat) (signature : Signature Tower.Head) :
    ContextFormation (rules level signature) (contextAXCYPQ level) := by
  exact .snoc (.snoc (.snoc (.snoc
    (.snoc (.snoc .nil (.headType (.sort level)) (.sort (.succ level))) (.var 0) (.sort level))
    (selectorType_formed (.var 1) (.var 0)) (.sort (selectorLevel level)))
    (.var 2) (.sort level))
    (.idForm (.var 3) (.sort level) (.var 2) (.var 0)) (.sort level))
    (.idForm (.var 4) (.sort level) (.var 3) (.var 1)) (.sort level)

theorem schemaContext_formed (level : LevelExpr Nat) (signature : Signature Tower.Head) :
    ContextFormation (rules level signature) (schemaContext level) := by
  have selectorTyped : Typing (rules level signature) (contextAXCYPQ level) (.var 3)
      (selectorType (.var 5) (.var 4)) := by
    exact .var 3
  exact .snoc (contextAXCYPQ_formed level signature)
    (.idForm (.idForm (.var 5) (.sort level) (.var 4) (.var 2)) (.sort level)
      (select_typed selectorTyped (.var 2) (.var 1))
      (select_typed selectorTyped (.var 2) (.var 0))) (.sort level)

def schemaTerm : Tower.Tm 7 := hedberg (.var 6) (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)
def schemaType : Tower.Tm 7 := .id (.id (.var 6) (.var 5) (.var 3)) (.var 2) (.var 1)

theorem schema_judgment (level : LevelExpr Nat) (signature : Signature Tower.Head) :
    Judgment (rules level signature) (schemaContext level) schemaTerm schemaType := by
  have selectorTyped : Typing (rules level signature) (schemaContext level) (.var 4)
      (selectorType (.var 6) (.var 5)) := by
    exact .var 4
  exact ⟨schemaContext_formed level signature,
    hedberg_typed (schemaContext_formed level signature) (.var 6) (.var 5) selectorTyped
      (.var 3) (.var 2) (.var 1) (.var 0)⟩

/-- A closed universal theorem, so genuine datatype signatures with new
computation roots can import it before supplying their native selectors. -/
def hedbergClosed : Tower.Tm 0 := .lam (.lam (.lam (.lam (.lam (.lam (.lam schemaTerm))))))

def hedbergClosedType (level : LevelExpr Nat) : Tower.Tm 0 :=
  .pi (sortTm level) (.pi (.var 0) (.pi (selectorType (.var 1) (.var 0))
    (.pi (.var 2) (.pi (.id (.var 3) (.var 2) (.var 0))
      (.pi (.id (.var 4) (.var 3) (.var 1)) (.pi constancyInstanceType schemaType))))))

theorem hedbergClosed_judgment (level : LevelExpr Nat) (signature : Signature Tower.Head) :
    Judgment (rules level signature) (.nil : Tower.Ctx 0) hedbergClosed (hedbergClosedType level) :=
  abstract_judgment (abstract_judgment (abstract_judgment (abstract_judgment
    (abstract_judgment (abstract_judgment (abstract_judgment (schema_judgment level signature)))))))

/-- The checked closed proof is usable in a real computation extension.
No opacity condition deletes the extension's datatype iota rules. -/
theorem hedbergClosed_includeSignature (level : LevelExpr Nat) (signature extension : Signature Tower.Head) :
    Typing (extendRules (rules level signature) extension) (.nil : Tower.Ctx 0)
      hedbergClosed (hedbergClosedType level) :=
  (hedbergClosed_judgment level signature).typing.includeSignature extension

/-- The actual seven arguments of the native theorem. The final argument
is evidence about the selector, not an assumed equality of the original paths. -/
def arguments (carrier left selector right first second comparison : Tower.Tm n) : Sub Tower.Head 7 n :=
  consSub comparison (consSub second (consSub first (consSub right (consSub selector
    (consSub left (consSub carrier (fun index => Fin.elim0 index)))))))

theorem arguments_term (carrier left selector right first second comparison : Tower.Tm n) :
    subst (arguments carrier left selector right first second comparison) schemaTerm =
      hedberg carrier left selector right first second comparison := by
  simp only [schemaTerm, hedberg_substitute, subst, arguments, consSub]
  rfl

theorem arguments_type (carrier left selector right first second comparison : Tower.Tm n) :
    subst (arguments carrier left selector right first second comparison) schemaType =
      .id (.id carrier left right) first second := rfl

/-- Application in an extension uses the already checked universal proof.
The target can have genuine datatype computation: no opaque-signature
condition is needed, and no new rules are introduced here. -/
theorem hedberg_in_extension (extension : Signature Tower.Head)
    {carrier left selector right first second comparison : Tower.Tm n}
    (formed : ContextFormation (extendRules (rules level signature) extension) context)
    (carrierTyped : Typing (extendRules (rules level signature) extension) context carrier (sortTm level))
    (leftTyped : Typing (extendRules (rules level signature) extension) context left carrier)
    (selectorTyped : Typing (extendRules (rules level signature) extension) context selector (selectorType carrier left))
    (rightTyped : Typing (extendRules (rules level signature) extension) context right carrier)
    (firstTyped : Typing (extendRules (rules level signature) extension) context first (.id carrier left right))
    (secondTyped : Typing (extendRules (rules level signature) extension) context second (.id carrier left right))
    (comparisonTyped : Typing (extendRules (rules level signature) extension) context comparison
      (.id (.id carrier left right) (select selector right first) (select selector right second))) :
    Judgment (extendRules (rules level signature) extension) context
      (hedberg carrier left selector right first second comparison) (.id (.id carrier left right) first second) := by
  have parameters : FormationSensitive.CtxMor (extendRules (rules level signature) extension)
      (schemaContext level) context (arguments carrier left selector right first second comparison) := by
    exact Fin.cases comparisonTyped (Fin.cases secondTyped (Fin.cases firstTyped
      (Fin.cases rightTyped (Fin.cases selectorTyped (Fin.cases leftTyped
        (Fin.cases carrierTyped (fun index => Fin.elim0 index)))))))
  have application := ((schema_judgment level signature).typing.includeSignature extension).substitute parameters
  exact ⟨formed, by simpa only [arguments_term, arguments_type] using application⟩

/-- A datatype branch may establish weak constancy by reducing both selected
values to one common value. The resulting evidence is native reflexivity,
checked at its formed target type, in the actual target rules. -/
theorem comparison_from_common_conversion {targetRules : Rules Tower.Head}
    {carrier first second common : Tower.Tm n}
    (universeWitness : targetRules.isUniverse (.sort level))
    (carrierTyped : Typing targetRules context carrier (sortTm level))
    (firstTyped : Typing targetRules context first carrier)
    (secondTyped : Typing targetRules context second carrier)
    (commonTyped : Typing targetRules context common carrier)
    (firstConversion : Conv targetRules.headEq first common targetRules.computation)
    (secondConversion : Conv targetRules.headEq second common targetRules.computation) :
    Typing targetRules context (.refl common) (.id carrier first second) :=
  .conv (.reflIntro commonTyped)
    (.idForm carrierTyped universeWitness firstTyped secondTyped) universeWitness
    (.congId (.refl _) (.symm _ _ firstConversion) (.symm _ _ secondConversion))

/-- A neutral path is not silently treated as reflexivity while proving
selector normalization. This concerns the native iota root, not global
non-derivability or the normalization of an arbitrary extension. -/
theorem fixed_variable_no_iota (opacity : OpaqueRelatorExtension.Opacity signature)
    (carrier left selector right output : Tower.Tm (n + 1)) :
    ¬ (rules level signature).computation.step
      (fixed carrier left selector right (.var 0)) output := by
  intro root
  obtain ⟨_, impossible, _⟩ := FormationSensitiveNativeIdentity.identity_root_iff.mp
    ((NativeIdentityLevelInstantiation.root_iff (fun _ => level) opacity).mp root)
  cases impossible

/-- At reflexivity the same actual term does use the native computation
rule, returning the previously constructed cancellation proof. -/
theorem fixed_reflexivity_iota (carrier left selector : Tower.Tm n) :
    (rules level signature).computation.step
      (fixed carrier left selector left (.refl left))
      (cancellation carrier left left (select selector left (.refl left))) :=
  NativeIdentityLevelInstantiation.beta (fun _ => level) signature carrier left
    (.lam (.lam (fixedMotive carrier left selector)))
    (cancellation carrier left left (select selector left (.refl left)))

namespace Controls

/-- The generic proof is exercised in a genuinely formed native telescope
whose two paths are distinct variables. Constancy is retained as a typed
selector equation rather than inserted into conversion. -/
theorem native_nonreflexive_schema (level : LevelExpr Nat) (signature : Signature Tower.Head) :
    ContextFormation (rules level signature) (schemaContext level) ∧
      Typing (rules level signature) (schemaContext level) schemaTerm schemaType ∧
      (.var 2 : Tower.Tm 7) ≠ .var 1 :=
  ⟨schemaContext_formed level signature, (schema_judgment level signature).typing, by decide⟩

def syntaxChecks : List Bool :=
  [decide ((.var 2 : Tower.Tm 7) ≠ .var 1),
   decide (schemaTerm ≠ (.refl (.var 2) : Tower.Tm 7)),
   decide (constancyInstanceType ≠ (.id (.id (.var 5) (.var 4) (.var 2)) (.var 1) (.var 0) : Tower.Tm 6)),
   decide (hedbergClosed ≠ (.lam (.var 0) : Tower.Tm 0))]

theorem syntaxChecks_all : syntaxChecks = [true, true, true, true] := by decide

end Controls

#print axioms select_typed
#print axioms normalized_typed
#print axioms fixed_typed
#print axioms fixed_substitute
#print axioms prefixFunction_typed
#print axioms normalizedComparison_typed
#print axioms hedberg_typed
#print axioms hedberg_substitute
#print axioms schema_judgment
#print axioms hedbergClosed_judgment
#print axioms hedbergClosed_includeSignature
#print axioms hedberg_in_extension
#print axioms comparison_from_common_conversion
#print axioms fixed_variable_no_iota
#print axioms fixed_reflexivity_iota
#print axioms Controls.native_nonreflexive_schema
#print axioms Controls.syntaxChecks_all

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeHedberg
