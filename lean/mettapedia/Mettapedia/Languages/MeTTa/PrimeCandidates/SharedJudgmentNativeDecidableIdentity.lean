import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRegion

/-!
# Native decidable identity and weakly constant selectors

Decisions are object terms: a Boolean paired with either a witness or a
function from witnesses to the small-type empty encoding. Boolean elimination
constructs a selector and a proof that its outputs are equal. Nothing in this
construction inspects a host-language decision procedure or adds UIP as an axiom.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeDecidableIdentity

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open SharedJudgmentIdentityRegions (arrow)
open SharedJudgmentNativeBooleanRegion

variable {n m : Nat} {context : Tower.Ctx n}

theorem apply_typed {domain codomain function argument : Tower.Tm n}
    (functionTyped : Typing rules context function (arrow domain codomain))
    (argumentTyped : Typing rules context argument domain) :
    Typing rules context (.app function argument) codomain := by
  simpa only [arrow, inst0, substitute_weaken] using Typing.appElim functionTyped argumentTyped

theorem small_lift {type : Tower.Tm n}
    (typed : Typing rules context type (sortTm zero)) :
    Typing rules context type (sortTm one) :=
  .cumul typed (fun _ => Nat.le_succ _)

theorem arrow_subst (sigma : Sub Tower.Head n m) (domain codomain : Tower.Tm n) :
    subst sigma (arrow domain codomain) = arrow (subst sigma domain) (subst sigma codomain) := by
  simp only [arrow, subst, subst_liftSub_wk]

theorem arrow_rename (rho : Ren n m) (domain codomain : Tower.Tm n) :
    rename rho (arrow domain codomain) = arrow (rename rho domain) (rename rho codomain) := by
  simp only [arrow, rename, rename_comp, liftRen, wk, Fin.cases_succ]

def constancyType (type function : Tower.Tm n) : Tower.Tm n :=
  .pi type (.pi (rename wk type)
    (.id (rename wk (rename wk type))
      (.app (rename wk (rename wk function)) (.var 1))
      (.app (rename wk (rename wk function)) (.var 0))))

@[simp] theorem constancyType_subst (sigma : Sub Tower.Head n m) (type function : Tower.Tm n) :
    subst sigma (constancyType type function) =
      constancyType (subst sigma type) (subst sigma function) := by
  simp only [constancyType, subst, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem constancyType_rename (rho : Ren n m) (type function : Tower.Tm n) :
    rename rho (constancyType type function) =
      constancyType (rename rho type) (rename rho function) := by
  simp only [constancyType, rename, rename_comp, liftRen, wk, Fin.cases_succ, Fin.cases_zero]
  rfl

theorem constancyType_formed {type function : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (functionTyped : Typing rules context function (arrow type type)) :
    Typing rules context (constancyType type function) (sortTm zero) := by
  have twice : Typing rules (.snoc (.snoc context type) (rename wk type))
      (rename wk (rename wk function))
      (arrow (rename wk (rename wk type)) (rename wk (rename wk type))) := by
    simpa only [arrow_rename] using functionTyped.weaken.weaken
  exact pi_formed typeFormed (pi_formed typeFormed.weaken
    (.idForm typeFormed.weaken.weaken (.sort zero)
      (apply_typed twice (.var 1)) (apply_typed twice (.var 0))))

def selectorPackageType (type : Tower.Tm n) : Tower.Tm n :=
  .sigma (arrow type type) (constancyType (rename wk type) (.var 0))

@[simp] theorem selectorPackageType_subst (sigma : Sub Tower.Head n m) (type : Tower.Tm n) :
    subst sigma (selectorPackageType type) = selectorPackageType (subst sigma type) := by
  simp only [selectorPackageType, subst, arrow_subst, constancyType_subst, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem selectorPackageType_rename (rho : Ren n m) (type : Tower.Tm n) :
    rename rho (selectorPackageType type) = selectorPackageType (rename rho type) := by
  simp only [selectorPackageType, rename, arrow_rename, constancyType_rename,
    rename_comp, liftRen, wk, Fin.cases_succ, Fin.cases_zero]

theorem selectorPackageType_formed {type : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero)) :
    Typing rules context (selectorPackageType type) (sortTm zero) := by
  have variableTyped : Typing rules (.snoc context (arrow type type)) (.var 0)
      (arrow (rename wk type) (rename wk type)) := by
    simpa only [Ctx.lookup, arrow_rename, Fin.cases_zero] using (Typing.var (R := rules)
      (Γ := .snoc context (arrow type type)) 0)
  exact .cumul (.sigmaForm (arrow_formed typeFormed typeFormed) (.sort zero)
    (constancyType_formed typeFormed.weaken variableTyped) (.sort zero) (.sorts zero zero))
    (fun _ => by simp [LevelExpr.eval])

theorem selector_package_typed {type function constant : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (functionTyped : Typing rules context function (arrow type type))
    (constantTyped : Typing rules context constant (constancyType type function)) :
    Typing rules context (.pair function constant) (selectorPackageType type) := by
  apply Typing.pairIntro (selectorPackageType_formed typeFormed) (.sort zero) functionTyped
  simpa only [inst0, constancyType_subst, substitute_weaken, subst, subst0, Fin.cases_zero]
    using constantTyped

def positiveFunction (witness : Tower.Tm n) : Tower.Tm n := .lam (rename wk witness)
def positiveConstant (witness : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.refl (rename wk (rename wk witness))))

theorem positiveFunction_typed {type witness : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (witnessTyped : Typing rules context witness type) :
    Typing rules context (positiveFunction witness) (arrow type type) :=
  lambda_typed typeFormed typeFormed.weaken witnessTyped.weaken

theorem positiveFunction_beta (witness input : Tower.Tm n) :
    Conv rules.headEq (.app (positiveFunction witness) input) witness rules.computation := by
  have beta : Conv rules.headEq (.app (positiveFunction witness) input)
      (inst0 input (rename wk witness)) rules.computation := .rel _ _ (.betaPi _ _)
  simpa only [inst0, substitute_weaken] using beta

theorem positiveConstant_typed {type witness : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (witnessTyped : Typing rules context witness type) :
    Typing rules context (positiveConstant witness) (constancyType type (positiveFunction witness)) := by
  have function := positiveFunction_typed typeFormed witnessTyped
  have twice : Typing rules (.snoc (.snoc context type) (rename wk type))
      (rename wk (rename wk (positiveFunction witness)))
      (arrow (rename wk (rename wk type)) (rename wk (rename wk type))) := by
    simpa only [arrow_rename] using function.weaken.weaken
  have result := Typing.idForm typeFormed.weaken.weaken (.sort zero)
    (apply_typed twice (.var 1)) (apply_typed twice (.var 0))
  apply lambda_typed typeFormed (pi_formed typeFormed.weaken result)
  apply lambda_typed typeFormed.weaken result
  apply Typing.conv (.reflIntro witnessTyped.weaken.weaken) result (.sort zero)
  apply Conv.congId (.refl _)
  · simpa only [positiveFunction, rename, rename_comp, liftRen, wk, Fin.cases_succ] using
      (positiveFunction_beta (rename wk (rename wk witness)) (.var 1)).symm
  · simpa only [positiveFunction, rename, rename_comp, liftRen, wk, Fin.cases_succ] using
      (positiveFunction_beta (rename wk (rename wk witness)) (.var 0)).symm

def negativeFunction (type refutation : Tower.Tm n) : Tower.Tm n :=
  .lam (emptyEliminate (.app (rename wk refutation) (.var 0)) (rename wk type))

theorem negativeFunction_typed {type refutation : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (refutationTyped : Typing rules context refutation (arrow type emptyTm)) :
    Typing rules context (negativeFunction type refutation) (arrow type type) := by
  apply lambda_typed typeFormed typeFormed.weaken
  have weakened : Typing rules (.snoc context type) (rename wk refutation)
      (arrow (rename wk type) emptyTm) := by
    simpa only [arrow_rename, emptyTm, rename, sortTm, liftRen, Fin.cases_zero] using refutationTyped.weaken
  exact empty_eliminate_typed (apply_typed weakened (.var 0)) typeFormed.weaken

def negativeConstant (type refutation : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (emptyEliminate (.app (rename wk (rename wk refutation)) (.var 1))
    (.id (rename wk (rename wk type))
      (.app (rename wk (rename wk (negativeFunction type refutation))) (.var 1))
      (.app (rename wk (rename wk (negativeFunction type refutation))) (.var 0)))))

theorem negativeConstant_typed {type refutation : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (refutationTyped : Typing rules context refutation (arrow type emptyTm)) :
    Typing rules context (negativeConstant type refutation)
      (constancyType type (negativeFunction type refutation)) := by
  have function := negativeFunction_typed typeFormed refutationTyped
  have twice : Typing rules (.snoc (.snoc context type) (rename wk type))
      (rename wk (rename wk (negativeFunction type refutation)))
      (arrow (rename wk (rename wk type)) (rename wk (rename wk type))) := by
    simpa only [arrow_rename] using function.weaken.weaken
  have result := Typing.idForm typeFormed.weaken.weaken (.sort zero)
    (apply_typed twice (.var 1)) (apply_typed twice (.var 0))
  apply lambda_typed typeFormed (pi_formed typeFormed.weaken result)
  apply lambda_typed typeFormed.weaken result
  have weakened : Typing rules (.snoc (.snoc context type) (rename wk type))
      (rename wk (rename wk refutation)) (arrow (rename wk (rename wk type)) emptyTm) := by
    simpa only [arrow_rename, emptyTm, rename, sortTm, liftRen, Fin.cases_zero] using refutationTyped.weaken.weaken
  exact empty_eliminate_typed (apply_typed weakened (.var 1)) result

def payload (type bit : Tower.Tm n) : Tower.Tm n :=
  eliminate typeMotive (arrow type emptyTm) type bit

@[simp] theorem payload_subst (sigma : Sub Tower.Head n m) (type bit : Tower.Tm n) :
    subst sigma (payload type bit) = payload (subst sigma type) (subst sigma bit) := by
  simp only [payload, eliminate, subst, arrow_subst, typeMotive, emptyTm]
  rfl

@[simp] theorem payload_rename (rho : Ren n m) (type bit : Tower.Tm n) :
    rename rho (payload type bit) = payload (rename rho type) (rename rho bit) := by
  simp only [payload, eliminate, rename, arrow_rename, typeMotive, emptyTm]
  rfl

theorem payload_formed {type bit : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (bitTyped : Typing rules context bit boolTm) :
    Typing rules context (payload type bit) (sortTm one) := by
  have branch {term : Tower.Tm n} (typed : Typing rules context term (sortTm one))
      (value : Tower.Tm n) (valueTyped : Typing rules context value boolTm) :
      Typing rules context term (.app typeMotive value) :=
    .conv typed (motive_apply_typed (typeMotive_typed context) valueTyped) (.sort two)
      (typeMotive_beta value).symm
  exact .conv
    (eliminate_typed (typeMotive_typed context)
      (branch (arrow_formed (small_lift typeFormed) (empty_formed context)) falseTm (false_typed context))
      (branch (small_lift typeFormed) trueTm (true_typed context)) bitTyped)
    (.headType (.sort one)) (.sort two) (typeMotive_beta bit)

theorem payload_false (type : Tower.Tm n) :
    Conv rules.headEq (payload type falseTm) (arrow type emptyTm) rules.computation :=
  .rel _ _ (.root (iota_false ..))

theorem payload_true (type : Tower.Tm n) :
    Conv rules.headEq (payload type trueTm) type rules.computation :=
  .rel _ _ (.root (iota_true ..))

/-- The decision carries both the native Boolean tag and its dependent evidence. -/
def decidableType (type : Tower.Tm n) : Tower.Tm n :=
  .sigma boolTm (payload (rename wk type) (.var 0))

@[simp] theorem decidableType_subst (sigma : Sub Tower.Head n m) (type : Tower.Tm n) :
    subst sigma (decidableType type) = decidableType (subst sigma type) := by
  simp only [decidableType, subst, boolTm, payload_subst, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem decidableType_rename (rho : Ren n m) (type : Tower.Tm n) :
    rename rho (decidableType type) = decidableType (rename rho type) := by
  simp only [decidableType, rename, boolTm, payload_rename,
    rename_comp, liftRen, wk, Fin.cases_succ, Fin.cases_zero]

theorem decidableType_formed {type : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero)) :
    Typing rules context (decidableType type) (sortTm one) :=
  .cumul (.sigmaForm (bool_typed context) (.sort zero)
    (payload_formed typeFormed.weaken (.var 0)) (.sort one) (.sorts zero one))
    (by intro valuation; simp [LevelExpr.eval, zero, one, LevelTower.zero])

def choiceBody (type : Tower.Tm n) : Tower.Tm (n + 1) :=
  arrow (payload (rename wk type) (.var 0)) (selectorPackageType (rename wk type))

theorem choiceBody_inst (type bit : Tower.Tm n) :
    inst0 bit (choiceBody type) = arrow (payload type bit) (selectorPackageType type) := by
  simp only [choiceBody, inst0, arrow_subst, payload_subst, selectorPackageType_subst,
    substitute_weaken, subst, subst0, Fin.cases_zero]

theorem choiceBody_formed {type : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero)) :
    Typing rules (.snoc context boolTm) (choiceBody type) (sortTm one) :=
  arrow_formed (payload_formed typeFormed.weaken (.var 0))
    (small_lift (selectorPackageType_formed typeFormed.weaken))

def positivePackage : Tower.Tm n :=
  .lam (.pair (positiveFunction (.var 0)) (positiveConstant (.var 0)))

theorem positivePackage_typed {type : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero)) :
    Typing rules context positivePackage (arrow type (selectorPackageType type)) := by
  apply lambda_typed typeFormed
    (by simpa only [selectorPackageType_rename, sortTm, rename] using (selectorPackageType_formed typeFormed).weaken)
  have witnessTyped : Typing rules (.snoc context type) (.var 0) (rename wk type) := .var 0
  simpa only [selectorPackageType_rename] using selector_package_typed typeFormed.weaken
    (positiveFunction_typed typeFormed.weaken witnessTyped)
    (positiveConstant_typed typeFormed.weaken witnessTyped)

def negativePackage (type : Tower.Tm n) : Tower.Tm n :=
  .lam (.pair (negativeFunction (rename wk type) (.var 0))
    (negativeConstant (rename wk type) (.var 0)))

theorem negativePackage_typed {type : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero)) :
    Typing rules context (negativePackage type)
      (arrow (arrow type emptyTm) (selectorPackageType type)) := by
  apply lambda_typed (arrow_formed (small_lift typeFormed) (empty_formed context))
    (small_lift (by simpa only [selectorPackageType_rename, sortTm, rename] using (selectorPackageType_formed typeFormed).weaken))
  have refutationTyped : Typing rules (.snoc context (arrow type emptyTm)) (.var 0)
      (arrow (rename wk type) emptyTm) := by
    simpa only [Ctx.lookup, arrow_rename, emptyTm, sortTm, rename, liftRen, Fin.cases_zero]
      using (Typing.var (R := rules) (Γ := .snoc context (arrow type emptyTm)) 0)
  simpa only [selectorPackageType_rename] using selector_package_typed typeFormed.weaken
    (negativeFunction_typed typeFormed.weaken refutationTyped)
    (negativeConstant_typed typeFormed.weaken refutationTyped)

def chooseAt (type bit : Tower.Tm n) : Tower.Tm n :=
  casesTerm (choiceBody type) (negativePackage type) positivePackage bit

theorem chooseAt_typed {type bit : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (bitTyped : Typing rules context bit boolTm) :
    Typing rules context (chooseAt type bit)
      (arrow (payload type bit) (selectorPackageType type)) := by
  have branchFormed (value : Tower.Tm n) (valueTyped : Typing rules context value boolTm) :
      Typing rules context (arrow (payload type value) (selectorPackageType type)) (sortTm one) :=
    arrow_formed (payload_formed typeFormed valueTyped) (small_lift (selectorPackageType_formed typeFormed))
  have onFalse : Typing rules context (negativePackage type) (inst0 falseTm (choiceBody type)) := by
    rw [choiceBody_inst]
    exact .conv (negativePackage_typed typeFormed) (branchFormed falseTm (false_typed context))
      (.sort one) (Conv.congPi (payload_false type).symm (.refl _))
  have onTrue : Typing rules context positivePackage (inst0 trueTm (choiceBody type)) := by
    rw [choiceBody_inst]
    exact .conv (positivePackage_typed typeFormed) (branchFormed trueTm (true_typed context))
      (.sort one) (Conv.congPi (payload_true type).symm (.refl _))
  have result := cases_typed (level := one)
    (by intro valuation; simp [one, two, LevelExpr.eval])
    (choiceBody_formed typeFormed) onFalse onTrue bitTyped
  simpa only [choiceBody_inst, chooseAt] using result

def decisionSelection (type decision : Tower.Tm n) : Tower.Tm n :=
  .app (chooseAt type (.fst decision)) (.snd decision)

theorem decisionSelection_typed {type decision : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (decisionTyped : Typing rules context decision (decidableType type)) :
    Typing rules context (decisionSelection type decision) (selectorPackageType type) := by
  have tag : Typing rules context (.fst decision) boolTm := .fstElim decisionTyped
  have evidence : Typing rules context (.snd decision) (payload type (.fst decision)) := by
    simpa only [decidableType, inst0, payload_subst, substitute_weaken, subst, subst0,
      Fin.cases_zero] using Typing.sndElim decisionTyped
  exact apply_typed (chooseAt_typed typeFormed tag) evidence

@[simp] theorem positiveFunction_subst (sigma : Sub Tower.Head n m) (witness : Tower.Tm n) :
    subst sigma (positiveFunction witness) = positiveFunction (subst sigma witness) := by
  simp only [positiveFunction, subst, subst_liftSub_wk]

@[simp] theorem positiveConstant_subst (sigma : Sub Tower.Head n m) (witness : Tower.Tm n) :
    subst sigma (positiveConstant witness) = positiveConstant (subst sigma witness) := by
  simp only [positiveConstant, subst, subst_liftSub_wk]

@[simp] theorem negativeFunction_subst (sigma : Sub Tower.Head n m) (type refutation : Tower.Tm n) :
    subst sigma (negativeFunction type refutation) =
      negativeFunction (subst sigma type) (subst sigma refutation) := by
  simp only [negativeFunction, emptyEliminate, subst, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem negativeConstant_subst (sigma : Sub Tower.Head n m) (type refutation : Tower.Tm n) :
    subst sigma (negativeConstant type refutation) =
      negativeConstant (subst sigma type) (subst sigma refutation) := by
  simp only [negativeConstant, emptyEliminate, subst, subst_liftSub_wk, negativeFunction_subst, liftSub]
  rfl

@[simp] theorem decisionSelection_subst (sigma : Sub Tower.Head n m) (type decision : Tower.Tm n) :
    subst sigma (decisionSelection type decision) =
      decisionSelection (subst sigma type) (subst sigma decision) := by
  simp only [decisionSelection, chooseAt, casesTerm, choiceBody, eliminate, positivePackage,
    negativePackage, subst, arrow_subst, payload_subst, selectorPackageType_subst,
    positiveFunction_subst, positiveConstant_subst, negativeFunction_subst, negativeConstant_subst,
    subst_liftSub_wk, liftSub]
  rfl

def chosenFunction (type decision : Tower.Tm n) : Tower.Tm n :=
  .fst (decisionSelection type decision)

def chosenConstant (type decision : Tower.Tm n) : Tower.Tm n :=
  .snd (decisionSelection type decision)

@[simp] theorem chosenFunction_subst (sigma : Sub Tower.Head n m) (type decision : Tower.Tm n) :
    subst sigma (chosenFunction type decision) =
      chosenFunction (subst sigma type) (subst sigma decision) := by
  simp only [chosenFunction, subst, decisionSelection_subst]

theorem chosenFunction_typed {type decision : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (decisionTyped : Typing rules context decision (decidableType type)) :
    Typing rules context (chosenFunction type decision) (arrow type type) :=
  .fstElim (decisionSelection_typed typeFormed decisionTyped)

theorem chosenConstant_typed {type decision : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (decisionTyped : Typing rules context decision (decidableType type)) :
    Typing rules context (chosenConstant type decision)
      (constancyType type (chosenFunction type decision)) := by
  simpa only [selectorPackageType, inst0, constancyType_subst, substitute_weaken, subst,
    subst0, Fin.cases_zero, chosenConstant, chosenFunction]
    using Typing.sndElim (decisionSelection_typed typeFormed decisionTyped)

def compareChosen (type decision first second : Tower.Tm n) : Tower.Tm n :=
  .app (.app (chosenConstant type decision) first) second

theorem compareChosen_typed {type decision first second : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (decisionTyped : Typing rules context decision (decidableType type))
    (firstTyped : Typing rules context first type)
    (secondTyped : Typing rules context second type) :
    Typing rules context (compareChosen type decision first second)
      (.id type (.app (chosenFunction type decision) first)
        (.app (chosenFunction type decision) second)) := by
  have firstApplication := Typing.appElim (chosenConstant_typed typeFormed decisionTyped) firstTyped
  have firstExact : Typing rules context (.app (chosenConstant type decision) first)
      (.pi type (.id (rename wk type)
        (.app (rename wk (chosenFunction type decision)) (rename wk first))
        (.app (rename wk (chosenFunction type decision)) (.var 0)))) := by
    convert firstApplication using 1
    simp only [inst0, subst, subst_liftSub_wk, substitute_weaken,
      liftSub, subst0, Fin.cases_zero]
    rfl
  simpa only [inst0, subst, substitute_weaken, subst0, Fin.cases_zero, compareChosen]
    using Typing.appElim firstExact secondTyped

/-- A native based decision function. Full decidable equality supplies one
such function at every chosen left endpoint. -/
def basedDecisionType (carrier left : Tower.Tm n) : Tower.Tm n :=
  .pi carrier (decidableType (.id (rename wk carrier) (rename wk left) (.var 0)))

@[simp] theorem basedDecisionType_rename (rho : Ren n m) (carrier left : Tower.Tm n) :
    rename rho (basedDecisionType carrier left) =
      basedDecisionType (rename rho carrier) (rename rho left) := by
  simp only [basedDecisionType, rename, decidableType_rename,
    rename_comp, liftRen, wk, Fin.cases_succ, Fin.cases_zero]

theorem basedDecisionType_formed {carrier left : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (leftTyped : Typing rules context left carrier) :
    Typing rules context (basedDecisionType carrier left) (sortTm one) :=
  pi_formed (small_lift carrierFormed)
    (decidableType_formed (.idForm carrierFormed.weaken (.sort zero) leftTyped.weaken (.var 0)))

theorem decide_at_typed {carrier left decision right : Tower.Tm n}
    (decisionTyped : Typing rules context decision (basedDecisionType carrier left))
    (rightTyped : Typing rules context right carrier) :
    Typing rules context (.app decision right) (decidableType (.id carrier left right)) := by
  simpa only [basedDecisionType, inst0, decidableType_subst, subst, substitute_weaken,
    subst0, Fin.cases_zero] using Typing.appElim decisionTyped rightTyped

def basedSelector (carrier left decision : Tower.Tm n) : Tower.Tm n :=
  .lam (chosenFunction (.id (rename wk carrier) (rename wk left) (.var 0))
    (.app (rename wk decision) (.var 0)))

theorem basedSelector_typed {carrier left decision : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (leftTyped : Typing rules context left carrier)
    (decisionTyped : Typing rules context decision (basedDecisionType carrier left)) :
    Typing rules context (basedSelector carrier left decision)
      (SharedJudgmentNativeHedberg.selectorType carrier left) := by
  have pathFormed := Typing.idForm carrierFormed.weaken (.sort zero) leftTyped.weaken
    (Typing.var (R := rules) (Γ := .snoc context carrier) 0)
  have decisionWeakened : Typing rules (.snoc context carrier) (rename wk decision)
      (basedDecisionType (rename wk carrier) (rename wk left)) := by
    simpa only [basedDecisionType_rename] using decisionTyped.weaken
  apply lambda_typed carrierFormed (arrow_formed pathFormed pathFormed)
  exact chosenFunction_typed pathFormed (decide_at_typed decisionWeakened (.var 0))

theorem basedSelector_beta (carrier left decision right : Tower.Tm n) :
    Conv rules.headEq (.app (basedSelector carrier left decision) right)
      (chosenFunction (.id carrier left right) (.app decision right)) rules.computation := by
  have result : Conv rules.headEq (.app (basedSelector carrier left decision) right)
      (inst0 right (chosenFunction (.id (rename wk carrier) (rename wk left) (.var 0))
        (.app (rename wk decision) (.var 0)))) rules.computation :=
    .rel _ _ (.betaPi _ _)
  simpa only [inst0, chosenFunction_subst, subst, substitute_weaken, subst0, Fin.cases_zero] using result

theorem selected_typed {carrier left decision right path : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (leftTyped : Typing rules context left carrier)
    (decisionTyped : Typing rules context decision (basedDecisionType carrier left))
    (rightTyped : Typing rules context right carrier)
    (pathTyped : Typing rules context path (.id carrier left right)) :
    Typing rules context
      (SharedJudgmentNativeHedberg.select (basedSelector carrier left decision) right path)
      (.id carrier left right) := by
  have first := Typing.appElim (basedSelector_typed carrierFormed leftTyped decisionTyped) rightTyped
  have exactFirst : Typing rules context (.app (basedSelector carrier left decision) right)
      (arrow (.id carrier left right) (.id carrier left right)) := by
    simpa only [SharedJudgmentNativeHedberg.selectorType, inst0, arrow_subst, subst,
      substitute_weaken, subst0, Fin.cases_zero] using first
  exact apply_typed exactFirst pathTyped

def nativeComparison (carrier left decision right first second : Tower.Tm n) : Tower.Tm n :=
  compareChosen (.id carrier left right) (.app decision right) first second

theorem nativeComparison_typed {carrier left decision right first second : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (leftTyped : Typing rules context left carrier)
    (decisionTyped : Typing rules context decision (basedDecisionType carrier left))
    (rightTyped : Typing rules context right carrier)
    (firstTyped : Typing rules context first (.id carrier left right))
    (secondTyped : Typing rules context second (.id carrier left right)) :
    Typing rules context (nativeComparison carrier left decision right first second)
      (.id (.id carrier left right)
        (SharedJudgmentNativeHedberg.select (basedSelector carrier left decision) right first)
        (SharedJudgmentNativeHedberg.select (basedSelector carrier left decision) right second)) := by
  have pathFormed := Typing.idForm carrierFormed (.sort zero) leftTyped rightTyped
  have resultFormed := Typing.idForm pathFormed (.sort zero)
    (selected_typed carrierFormed leftTyped decisionTyped rightTyped firstTyped)
    (selected_typed carrierFormed leftTyped decisionTyped rightTyped secondTyped)
  apply Typing.conv
    (compareChosen_typed pathFormed (decide_at_typed decisionTyped rightTyped) firstTyped secondTyped)
    resultFormed (.sort zero)
  exact Conv.congId (.refl _)
    (Conv.congApp (basedSelector_beta carrier left decision right).symm (.refl _))
    (Conv.congApp (basedSelector_beta carrier left decision right).symm (.refl _))

def uniqueness (carrier left decision right first second : Tower.Tm n) : Tower.Tm n :=
  SharedJudgmentNativeHedberg.hedberg carrier left (basedSelector carrier left decision)
    right first second (nativeComparison carrier left decision right first second)

/-- Decidable native identity supplies a genuine proof that any two paths
with those endpoints agree. The decision input is typed object-language data. -/
theorem uniqueness_judgment {carrier left decision right first second : Tower.Tm n}
    (formed : ContextFormation rules context)
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (leftTyped : Typing rules context left carrier)
    (decisionTyped : Typing rules context decision (basedDecisionType carrier left))
    (rightTyped : Typing rules context right carrier)
    (firstTyped : Typing rules context first (.id carrier left right))
    (secondTyped : Typing rules context second (.id carrier left right)) :
    Judgment rules context (uniqueness carrier left decision right first second)
      (.id (.id carrier left right) first second) :=
  SharedJudgmentNativeHedberg.hedberg_in_extension signature formed (small_lift carrierFormed)
    leftTyped (basedSelector_typed carrierFormed leftTyped decisionTyped) rightTyped firstTyped secondTyped
    (nativeComparison_typed carrierFormed leftTyped decisionTyped rightTyped firstTyped secondTyped)

@[simp] theorem basedDecisionType_subst (sigma : Sub Tower.Head n m) (carrier left : Tower.Tm n) :
    subst sigma (basedDecisionType carrier left) =
      basedDecisionType (subst sigma carrier) (subst sigma left) := by
  simp only [basedDecisionType, subst, decidableType_subst, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem basedSelector_subst (sigma : Sub Tower.Head n m) (carrier left decision : Tower.Tm n) :
    subst sigma (basedSelector carrier left decision) =
      basedSelector (subst sigma carrier) (subst sigma left) (subst sigma decision) := by
  simp only [basedSelector, subst, chosenFunction_subst, subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem compareChosen_subst (sigma : Sub Tower.Head n m)
    (type decision first second : Tower.Tm n) :
    subst sigma (compareChosen type decision first second) =
      compareChosen (subst sigma type) (subst sigma decision) (subst sigma first) (subst sigma second) := by
  simp only [compareChosen, chosenConstant, subst, decisionSelection_subst]

@[simp] theorem uniqueness_subst (sigma : Sub Tower.Head n m)
    (carrier left decision right first second : Tower.Tm n) :
    subst sigma (uniqueness carrier left decision right first second) =
      uniqueness (subst sigma carrier) (subst sigma left) (subst sigma decision)
        (subst sigma right) (subst sigma first) (subst sigma second) := by
  simp only [uniqueness, SharedJudgmentNativeHedberg.hedberg_substitute, basedSelector_subst,
    nativeComparison, compareChosen_subst, subst]

def decidableEqualityType (carrier : Tower.Tm n) : Tower.Tm n :=
  .pi carrier (basedDecisionType (rename wk carrier) (.var 0))

@[simp] theorem decidableEqualityType_rename (rho : Ren n m) (carrier : Tower.Tm n) :
    rename rho (decidableEqualityType carrier) = decidableEqualityType (rename rho carrier) := by
  simp only [decidableEqualityType, rename, basedDecisionType_rename, rename_comp,
    liftRen, wk, Fin.cases_succ, Fin.cases_zero]

theorem decidableEqualityType_formed {carrier : Tower.Tm n}
    (carrierFormed : Typing rules context carrier (sortTm zero)) :
    Typing rules context (decidableEqualityType carrier) (sortTm one) :=
  pi_formed (small_lift carrierFormed) (basedDecisionType_formed carrierFormed.weaken (.var 0))

def decidableEqualityUIP (carrier decision left right first second : Tower.Tm n) : Tower.Tm n :=
  uniqueness carrier left (.app decision left) right first second

/-- Internal Hedberg for arbitrary small carriers. This assumes a native
decision term of the declared Boolean/Sigma type, not host decidable equality. -/
theorem decidableEqualityUIP_judgment {carrier decision left right first second : Tower.Tm n}
    (formed : ContextFormation rules context)
    (carrierFormed : Typing rules context carrier (sortTm zero))
    (decisionTyped : Typing rules context decision (decidableEqualityType carrier))
    (leftTyped : Typing rules context left carrier)
    (rightTyped : Typing rules context right carrier)
    (firstTyped : Typing rules context first (.id carrier left right))
    (secondTyped : Typing rules context second (.id carrier left right)) :
    Judgment rules context (decidableEqualityUIP carrier decision left right first second)
      (.id (.id carrier left right) first second) := by
  have based : Typing rules context (.app decision left) (basedDecisionType carrier left) := by
    simpa only [decidableEqualityType, inst0, basedDecisionType_subst, substitute_weaken,
      subst, subst0, Fin.cases_zero] using Typing.appElim decisionTyped leftTyped
  exact uniqueness_judgment formed carrierFormed leftTyped based rightTyped firstTyped secondTyped

@[simp] theorem decidableEqualityUIP_subst (sigma : Sub Tower.Head n m)
    (carrier decision left right first second : Tower.Tm n) :
    subst sigma (decidableEqualityUIP carrier decision left right first second) =
      decidableEqualityUIP (subst sigma carrier) (subst sigma decision) (subst sigma left)
        (subst sigma right) (subst sigma first) (subst sigma second) := by
  simp only [decidableEqualityUIP, uniqueness_subst, subst]

/-! ## A closed object-language theorem -/

def contextA : Tower.Ctx 1 := .snoc .nil (sortTm zero)
def contextAD : Tower.Ctx 2 := .snoc contextA (decidableEqualityType (.var 0))
def contextADX : Tower.Ctx 3 := .snoc contextAD (.var 1)
def contextADXY : Tower.Ctx 4 := .snoc contextADX (.var 2)
def contextADXYP : Tower.Ctx 5 := .snoc contextADXY (.id (.var 3) (.var 1) (.var 0))
def schemaContext : Tower.Ctx 6 := .snoc contextADXYP (.id (.var 4) (.var 2) (.var 1))

theorem schemaContext_formed : ContextFormation rules schemaContext :=
  .snoc (.snoc (.snoc (.snoc
    (.snoc (.snoc .nil (.headType (.sort zero)) (.sort one))
      (decidableEqualityType_formed (.var 0)) (.sort one))
    (.var 1) (.sort zero)) (.var 2) (.sort zero))
    (.idForm (.var 3) (.sort zero) (.var 1) (.var 0)) (.sort zero))
    (.idForm (.var 4) (.sort zero) (.var 2) (.var 1)) (.sort zero)

def schemaTerm : Tower.Tm 6 :=
  decidableEqualityUIP (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def schemaType : Tower.Tm 6 := .id (.id (.var 5) (.var 3) (.var 2)) (.var 1) (.var 0)

theorem schema_judgment : Judgment rules schemaContext schemaTerm schemaType := by
  have decisionTyped : Typing rules schemaContext (.var 4) (decidableEqualityType (.var 5)) := by
    exact .var 4
  exact decidableEqualityUIP_judgment schemaContext_formed (.var 5) decisionTyped
    (.var 3) (.var 2) (.var 1) (.var 0)

/-- A reusable theorem value with all six parameters abstracted in native
lambda/Pi syntax. Its decision is still an explicit object-language argument. -/
def hedbergClosed : Tower.Tm 0 := .lam (.lam (.lam (.lam (.lam (.lam schemaTerm)))))

def hedbergClosedType : Tower.Tm 0 :=
  .pi (sortTm zero) (.pi (decidableEqualityType (.var 0))
    (.pi (.var 1) (.pi (.var 2) (.pi (.id (.var 3) (.var 1) (.var 0))
      (.pi (.id (.var 4) (.var 2) (.var 1)) schemaType)))))

theorem hedbergClosed_judgment : Judgment rules (.nil : Tower.Ctx 0) hedbergClosed hedbergClosedType :=
  SharedJudgmentNativeIdentityExtension.abstract_judgment
    (SharedJudgmentNativeIdentityExtension.abstract_judgment
      (SharedJudgmentNativeIdentityExtension.abstract_judgment
        (SharedJudgmentNativeIdentityExtension.abstract_judgment
          (SharedJudgmentNativeIdentityExtension.abstract_judgment
            (SharedJudgmentNativeIdentityExtension.abstract_judgment schema_judgment)))))

/-! ## Positive and negative decisions compute through their actual constructors -/

def positiveDecision (witness : Tower.Tm n) : Tower.Tm n := .pair trueTm witness
def negativeDecision (refutation : Tower.Tm n) : Tower.Tm n := .pair falseTm refutation

theorem positiveDecision_typed {type witness : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (witnessTyped : Typing rules context witness type) :
    Typing rules context (positiveDecision witness) (decidableType type) := by
  apply Typing.pairIntro (decidableType_formed typeFormed) (.sort one) (true_typed context)
  have typed := Typing.conv witnessTyped (payload_formed typeFormed (true_typed context))
    (.sort one) (payload_true type).symm
  simpa only [inst0, payload_subst, substitute_weaken, subst, subst0, Fin.cases_zero] using typed

theorem negativeDecision_typed {type refutation : Tower.Tm n}
    (typeFormed : Typing rules context type (sortTm zero))
    (refutationTyped : Typing rules context refutation (arrow type emptyTm)) :
    Typing rules context (negativeDecision refutation) (decidableType type) := by
  apply Typing.pairIntro (decidableType_formed typeFormed) (.sort one) (false_typed context)
  have typed := Typing.conv refutationTyped (payload_formed typeFormed (false_typed context))
    (.sort one) (payload_false type).symm
  simpa only [inst0, payload_subst, substitute_weaken, subst, subst0, Fin.cases_zero] using typed

theorem chooseAt_positive (type : Tower.Tm n) :
    Conv rules.headEq (chooseAt type trueTm) positivePackage rules.computation :=
  .rel _ _ (.root (iota_true ..))

theorem chooseAt_negative (type : Tower.Tm n) :
    Conv rules.headEq (chooseAt type falseTm) (negativePackage type) rules.computation :=
  .rel _ _ (.root (iota_false ..))

theorem positiveDecision_computes (type witness : Tower.Tm n) :
    Conv rules.headEq (decisionSelection type (positiveDecision witness))
      (.pair (positiveFunction witness) (positiveConstant witness)) rules.computation := by
  have tag : Conv rules.headEq (.fst (positiveDecision witness)) trueTm rules.computation :=
    .rel _ _ (.betaSigmaFst _ _)
  have evidence : Conv rules.headEq (.snd (positiveDecision witness)) witness rules.computation :=
    .rel _ _ (.betaSigmaSnd _ _)
  have head := Conv.congApp
    (Conv.congApp (function := .app (.app (.app (.const eliminateName) (.lam (choiceBody type)))
      (negativePackage type)) positivePackage) (.refl _) tag) evidence
  have beta : Conv rules.headEq (.app (positivePackage : Tower.Tm n) witness)
      (inst0 witness (.pair (positiveFunction (.var 0)) (positiveConstant (.var 0)))) rules.computation :=
    .rel _ _ (.betaPi _ _)
  exact .trans _ _ _ head (.trans _ _ _ (Conv.congApp (chooseAt_positive type) (.refl _))
    (by simpa only [inst0, subst, positiveFunction_subst, positiveConstant_subst,
      subst0, Fin.cases_zero] using beta))

theorem negativeDecision_computes (type refutation : Tower.Tm n) :
    Conv rules.headEq (decisionSelection type (negativeDecision refutation))
      (.pair (negativeFunction type refutation) (negativeConstant type refutation)) rules.computation := by
  have tag : Conv rules.headEq (.fst (negativeDecision refutation)) falseTm rules.computation :=
    .rel _ _ (.betaSigmaFst _ _)
  have evidence : Conv rules.headEq (.snd (negativeDecision refutation)) refutation rules.computation :=
    .rel _ _ (.betaSigmaSnd _ _)
  have head := Conv.congApp
    (Conv.congApp (function := .app (.app (.app (.const eliminateName) (.lam (choiceBody type)))
      (negativePackage type)) positivePackage) (.refl _) tag) evidence
  have beta : Conv rules.headEq (.app (negativePackage type) refutation)
      (inst0 refutation (.pair (negativeFunction (rename wk type) (.var 0))
        (negativeConstant (rename wk type) (.var 0)))) rules.computation :=
    .rel _ _ (.betaPi _ _)
  exact .trans _ _ _ head (.trans _ _ _ (Conv.congApp (chooseAt_negative type) (.refl _))
    (by simpa only [inst0, subst, negativeFunction_subst, negativeConstant_subst,
      substitute_weaken, subst0, Fin.cases_zero] using beta))

namespace Controls

/-- The two constructors carry distinct tags. The negative branch is a
refutation-bearing decision, not a fabricated positive witness. -/
theorem decision_tags_distinct (witness refutation : Tower.Tm n) :
    positiveDecision witness ≠ negativeDecision refutation := by
  intro same
  have tags : (trueTm : Tower.Tm n) = falseTm := Tm.pair.inj same |>.1
  have distinct : trueName ≠ falseName := by decide
  exact distinct (Tm.const.inj tags)

def syntaxChecks : List Bool :=
  [decide ((positiveDecision (.var 0) : Tower.Tm 1) ≠ negativeDecision (.var 0)),
   decide ((decidableType (.var 0) : Tower.Tm 1) ≠ .var 0),
   decide ((selectorPackageType (.var 0) : Tower.Tm 1) ≠ arrow (.var 0) (.var 0)),
   decide ((decidableEqualityUIP (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) : Tower.Tm 6)
     ≠ .refl (.var 1))]

theorem syntaxChecks_all : syntaxChecks = [true, true, true, true] := by decide

end Controls

#print axioms decisionSelection_typed
#print axioms compareChosen_typed
#print axioms uniqueness_judgment
#print axioms decidableEqualityUIP_judgment
#print axioms decidableEqualityUIP_subst
#print axioms schema_judgment
#print axioms hedbergClosed_judgment
#print axioms positiveDecision_typed
#print axioms negativeDecision_typed
#print axioms positiveDecision_computes
#print axioms negativeDecision_computes
#print axioms Controls.decision_tags_distinct
#print axioms Controls.syntaxChecks_all

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeDecidableIdentity
