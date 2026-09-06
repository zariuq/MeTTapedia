import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.StructuralLaws

/-!
# Typed substitution and context comprehension

This module lifts the shared raw renaming/substitution algebra to the generic
declarative typing judgment.  The result is presentation-independent: both
the sealed Legacy rules and the cumulative Tower rules inherit weakening,
typed simultaneous substitution, typed context-morphism composition, and the
context-extension beta/eta laws.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

/-! ## Additional raw substitution laws -/

@[simp] theorem Ctx.lookup_snoc_zero (Gamma : Ctx Head n) (type : Tm Head n) :
    Ctx.lookup (.snoc Gamma type) 0 = rename wk type :=
  rfl

@[simp] theorem Ctx.lookup_snoc_succ (Gamma : Ctx Head n) (type : Tm Head n)
    (index : Fin n) :
    Ctx.lookup (.snoc Gamma type) index.succ =
      rename wk (Ctx.lookup Gamma index) :=
  rfl

/-- A renaming regarded as a variable-only substitution. -/
def renSub (rho : Ren n m) : Sub Head n m :=
  fun index => .var (rho index)

@[simp] theorem liftSub_renSub (rho : Ren n m) :
    liftSub (renSub (Head := Head) rho) = renSub (liftRen rho) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

@[simp] theorem subst_renSub (rho : Ren n m) :
    ∀ term : Tm Head n, subst (renSub rho) term = rename rho term := by
  intro term
  induction term generalizing m with
  | var index => rfl
  | const name => rfl
  | head value => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp [subst, rename, ihDomain, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp [subst, rename, ihDomain, ihCodomain]
  | id type left right ihType ihLeft ihRight =>
      simp [subst, rename, ihType, ihLeft, ihRight]
  | lam body ihBody => simp [subst, rename, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [subst, rename, ihFunction, ihArgument]
  | pair first second ihFirst ihSecond =>
      simp [subst, rename, ihFirst, ihSecond]
  | fst pair ihPair => simp [subst, rename, ihPair]
  | snd pair ihPair => simp [subst, rename, ihPair]
  | refl term ihTerm => simp [subst, rename, ihTerm]

/-- A closed declaration type is unaffected by renaming the ambient local
telescope. -/
@[simp] theorem rename_liftClosed (rho : Ren n m) (term : Tm Head 0) :
    rename rho (liftClosed term : Tm Head n) = liftClosed term := by
  calc
    rename rho (liftClosed term : Tm Head n) =
        rename (fun index => rho (Fin.elim0 index)) term := by
          simpa only [liftClosed] using
            (rename_comp rho Fin.elim0 term)
    _ = rename Fin.elim0 term := by
          apply rename_ext
          intro index
          exact Fin.elim0 index
    _ = liftClosed term := rfl

/-- A closed declaration type is unaffected by simultaneous substitution in
the ambient local telescope. -/
@[simp] theorem subst_liftClosed (sigma : Sub Head n m) (term : Tm Head 0) :
    subst sigma (liftClosed term : Tm Head n) = liftClosed term := by
  calc
    subst sigma (liftClosed term : Tm Head n) =
        subst (fun index => sigma (Fin.elim0 index)) term := by
          simpa only [liftClosed] using
            (subst_rename (sigma := sigma) (rho := Fin.elim0) (term := term))
    _ = subst (renSub (Head := Head) Fin.elim0) term := by
          apply subst_ext
          intro index
          exact Fin.elim0 index
    _ = rename Fin.elim0 term := subst_renSub Fin.elim0 term
    _ = liftClosed term := rfl

/-- Renaming commutes with opening the newest binder. -/
@[simp] theorem rename_inst0 (rho : Ren n m) (argument : Tm Head n)
    (body : Tm Head (n + 1)) :
    rename rho (inst0 argument body) =
      inst0 (rename rho argument) (rename (liftRen rho) body) := by
  calc
    rename rho (inst0 argument body) =
        subst (fun index => rename rho (subst0 argument index)) body := by
          simpa [inst0] using
            (rename_subst (rho := rho) (sigma := subst0 argument)
              (term := body))
    _ = subst
        (fun index => subst0 (rename rho argument) (liftRen rho index))
        body := by
          apply subst_ext
          intro index
          refine Fin.cases ?_ ?_ index
          · rfl
          · intro prior
            rfl
    _ = subst (subst0 (rename rho argument))
        (rename (liftRen rho) body) := by
          symm
          simpa using
            (subst_rename (sigma := subst0 (rename rho argument))
              (rho := liftRen rho) (term := body))
    _ = inst0 (rename rho argument) (rename (liftRen rho) body) := by
          rfl

/-- Simultaneous substitution commutes with opening the newest binder. -/
@[simp] theorem subst_inst0 (sigma : Sub Head n m) (argument : Tm Head n)
    (body : Tm Head (n + 1)) :
    subst sigma (inst0 argument body) =
      inst0 (subst sigma argument) (subst (liftSub sigma) body) := by
  calc
    subst sigma (inst0 argument body) =
        subst (fun index => subst sigma (subst0 argument index)) body := by
          simp [inst0, subst_comp]
    _ = subst
        (fun index =>
          subst (subst0 (subst sigma argument)) (liftSub sigma index))
        body := by
          apply subst_ext
          intro index
          refine Fin.cases ?_ ?_ index
          · rfl
          · intro prior
            calc
              subst sigma (subst0 argument prior.succ) = sigma prior := by rfl
              _ = subst (subst0 (subst sigma argument))
                  (rename wk (sigma prior)) := by
                    symm
                    exact inst0_rename_wk (subst sigma argument) (sigma prior)
    _ = inst0 (subst sigma argument) (subst (liftSub sigma) body) := by
          simp [inst0, subst_comp]

/-! ## Conversion is stable under renaming and substitution -/

theorem StepCore.renameTerms {rootRules : RootComputation Head}
    {left right : Tm Head n}
    (step : Step headEq left right rootRules) :
    ∀ {m : Nat} (rho : Ren n m),
      Step headEq (rename rho left) (rename rho right) rootRules := by
  induction step with
  | betaPi body argument =>
      intro m rho
      simpa only [rename, rename_inst0] using
        (Step.betaPi (headEq := headEq)
          (rename (liftRen rho) body) (rename rho argument))
  | betaSigmaFst first second =>
      intro m rho
      exact .betaSigmaFst _ _
  | betaSigmaSnd first second =>
      intro m rho
      exact .betaSigmaSnd _ _
  | head equality =>
      intro m rho
      exact .head equality
  | root computation =>
      intro m rho
      exact .root (rootRules.rename rho computation)
  | congPiDom step ih =>
      intro m rho
      exact .congPiDom (ih rho)
  | congPiCod step ih =>
      intro m rho
      exact .congPiCod (ih (liftRen rho))
  | congSigmaDom step ih =>
      intro m rho
      exact .congSigmaDom (ih rho)
  | congSigmaCod step ih =>
      intro m rho
      exact .congSigmaCod (ih (liftRen rho))
  | congIdTy step ih =>
      intro m rho
      exact .congIdTy (ih rho)
  | congIdLeft step ih =>
      intro m rho
      exact .congIdLeft (ih rho)
  | congIdRight step ih =>
      intro m rho
      exact .congIdRight (ih rho)
  | congLam step ih =>
      intro m rho
      exact .congLam (ih (liftRen rho))
  | congAppFun step ih =>
      intro m rho
      exact .congAppFun (ih rho)
  | congAppArg step ih =>
      intro m rho
      exact .congAppArg (ih rho)
  | congPairFst step ih =>
      intro m rho
      exact .congPairFst (ih rho)
  | congPairSnd step ih =>
      intro m rho
      exact .congPairSnd (ih rho)
  | congFst step ih =>
      intro m rho
      exact .congFst (ih rho)
  | congSnd step ih =>
      intro m rho
      exact .congSnd (ih rho)
  | congRefl step ih =>
      intro m rho
      exact .congRefl (ih rho)

theorem Conv.renameTerms {rootRules : RootComputation Head}
    (rho : Ren n m) {left right : Tm Head n}
    (conversion : Conv headEq left right rootRules) :
    Conv headEq (rename rho left) (rename rho right) rootRules := by
  induction conversion with
  | rel left right step => exact .rel _ _ (step.renameTerms rho)
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact .trans _ _ _ ihFirst ihSecond

theorem StepCore.substitute {rootRules : RootComputation Head}
    {left right : Tm Head n}
    (step : Step headEq left right rootRules) :
    ∀ {m : Nat} (sigma : Sub Head n m),
      Step headEq (subst sigma left) (subst sigma right) rootRules := by
  induction step with
  | betaPi body argument =>
      intro m sigma
      simpa only [subst, subst_inst0] using
        (Step.betaPi (headEq := headEq)
          (subst (liftSub sigma) body) (subst sigma argument))
  | betaSigmaFst first second =>
      intro m sigma
      exact .betaSigmaFst _ _
  | betaSigmaSnd first second =>
      intro m sigma
      exact .betaSigmaSnd _ _
  | head equality =>
      intro m sigma
      exact .head equality
  | root computation =>
      intro m sigma
      exact .root (rootRules.substitute sigma computation)
  | congPiDom step ih =>
      intro m sigma
      exact .congPiDom (ih sigma)
  | congPiCod step ih =>
      intro m sigma
      exact .congPiCod (ih (liftSub sigma))
  | congSigmaDom step ih =>
      intro m sigma
      exact .congSigmaDom (ih sigma)
  | congSigmaCod step ih =>
      intro m sigma
      exact .congSigmaCod (ih (liftSub sigma))
  | congIdTy step ih =>
      intro m sigma
      exact .congIdTy (ih sigma)
  | congIdLeft step ih =>
      intro m sigma
      exact .congIdLeft (ih sigma)
  | congIdRight step ih =>
      intro m sigma
      exact .congIdRight (ih sigma)
  | congLam step ih =>
      intro m sigma
      exact .congLam (ih (liftSub sigma))
  | congAppFun step ih =>
      intro m sigma
      exact .congAppFun (ih sigma)
  | congAppArg step ih =>
      intro m sigma
      exact .congAppArg (ih sigma)
  | congPairFst step ih =>
      intro m sigma
      exact .congPairFst (ih sigma)
  | congPairSnd step ih =>
      intro m sigma
      exact .congPairSnd (ih sigma)
  | congFst step ih =>
      intro m sigma
      exact .congFst (ih sigma)
  | congSnd step ih =>
      intro m sigma
      exact .congSnd (ih sigma)
  | congRefl step ih =>
      intro m sigma
      exact .congRefl (ih sigma)

theorem Conv.substitute {rootRules : RootComputation Head}
    (sigma : Sub Head n m) {left right : Tm Head n}
    (conversion : Conv headEq left right rootRules) :
    Conv headEq (subst sigma left) (subst sigma right) rootRules := by
  induction conversion with
  | rel left right step => exact .rel _ _ (step.substitute sigma)
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact .trans _ _ _ ihFirst ihSecond

namespace Conv

/-- Conversion lifts through any one-hole term constructor whose underlying
one-step relation is closed under that constructor. -/
theorem mapCompatible
    {rootRules : RootComputation Head}
    (wrap : Tm Head n → Tm Head m)
    (compatible : ∀ {left right : Tm Head n},
      Step headEq left right rootRules →
        Step headEq (wrap left) (wrap right) rootRules)
    {left right : Tm Head n}
    (conversion : Conv headEq left right rootRules) :
    Conv headEq (wrap left) (wrap right) rootRules := by
  induction conversion with
  | rel left right step => exact .rel _ _ (compatible step)
  | refl term => exact .refl _
  | symm left right conversion ih => exact .symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact .trans _ _ _ ihFirst ihSecond

theorem congPi
    {rootRules : RootComputation Head}
    {domain domain' : Tm Head n}
    {codomain codomain' : Tm Head (n + 1)}
    (domainConversion : Conv headEq domain domain' rootRules)
    (codomainConversion : Conv headEq codomain codomain' rootRules) :
    Conv headEq (.pi domain codomain) (.pi domain' codomain') rootRules :=
  .trans _ _ _
    (mapCompatible (fun next => .pi next codomain)
      (fun step => .congPiDom step) domainConversion)
    (mapCompatible (fun next => .pi domain' next)
      (fun step => .congPiCod step) codomainConversion)

theorem congSigma
    {rootRules : RootComputation Head}
    {domain domain' : Tm Head n}
    {codomain codomain' : Tm Head (n + 1)}
    (domainConversion : Conv headEq domain domain' rootRules)
    (codomainConversion : Conv headEq codomain codomain' rootRules) :
    Conv headEq (.sigma domain codomain) (.sigma domain' codomain') rootRules :=
  .trans _ _ _
    (mapCompatible (fun next => .sigma next codomain)
      (fun step => .congSigmaDom step) domainConversion)
    (mapCompatible (fun next => .sigma domain' next)
      (fun step => .congSigmaCod step) codomainConversion)

theorem congId
    {rootRules : RootComputation Head}
    {type type' left left' right right' : Tm Head n}
    (typeConversion : Conv headEq type type' rootRules)
    (leftConversion : Conv headEq left left' rootRules)
    (rightConversion : Conv headEq right right' rootRules) :
    Conv headEq (.id type left right) (.id type' left' right') rootRules :=
  .trans _ _ _
    (mapCompatible (fun next => .id next left right)
      (fun step => .congIdTy step) typeConversion)
    (.trans _ _ _
      (mapCompatible (fun next => .id type' next right)
        (fun step => .congIdLeft step) leftConversion)
      (mapCompatible (fun next => .id type' left' next)
        (fun step => .congIdRight step) rightConversion))

theorem congLam
    {rootRules : RootComputation Head}
    {body body' : Tm Head (n + 1)}
    (conversion : Conv headEq body body' rootRules) :
    Conv headEq (.lam body) (.lam body') rootRules :=
  mapCompatible Tm.lam (fun step => .congLam step) conversion

theorem congApp
    {rootRules : RootComputation Head}
    {function function' argument argument' : Tm Head n}
    (functionConversion : Conv headEq function function' rootRules)
    (argumentConversion : Conv headEq argument argument' rootRules) :
    Conv headEq (.app function argument) (.app function' argument') rootRules :=
  .trans _ _ _
    (mapCompatible (fun next => .app next argument)
      (fun step => .congAppFun step) functionConversion)
    (mapCompatible (fun next => .app function' next)
      (fun step => .congAppArg step) argumentConversion)

theorem congPair
    {rootRules : RootComputation Head}
    {first first' second second' : Tm Head n}
    (firstConversion : Conv headEq first first' rootRules)
    (secondConversion : Conv headEq second second' rootRules) :
    Conv headEq (.pair first second) (.pair first' second') rootRules :=
  .trans _ _ _
    (mapCompatible (fun next => .pair next second)
      (fun step => .congPairFst step) firstConversion)
    (mapCompatible (fun next => .pair first' next)
      (fun step => .congPairSnd step) secondConversion)

private theorem liftSub_pointwise
    {rootRules : RootComputation Head}
    {source target : Sub Head n m}
    (pointwise : ∀ index,
      Conv headEq (source index) (target index) rootRules) :
    ∀ index,
      Conv headEq (liftSub source index) (liftSub target index) rootRules := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact .refl _
  · intro prior
    exact (pointwise prior).renameTerms wk

/-- Pointwise conversion of substitutions lifts through every open term.
Unlike `Conv.substitute`, which applies one substitution to an existing
conversion, this theorem varies the substituted terms themselves. -/
theorem substitutePointwise
    {rootRules : RootComputation Head}
    {source target : Sub Head n m}
    (pointwise : ∀ index,
      Conv headEq (source index) (target index) rootRules) :
    ∀ term : Tm Head n,
      Conv headEq (subst source term) (subst target term) rootRules := by
  intro term
  induction term generalizing m with
  | var index => exact pointwise index
  | const name => exact .refl _
  | head value => exact .refl _
  | pi domain codomain domainIH codomainIH =>
      exact congPi (domainIH pointwise)
        (codomainIH (liftSub_pointwise pointwise))
  | sigma domain codomain domainIH codomainIH =>
      exact congSigma (domainIH pointwise)
        (codomainIH (liftSub_pointwise pointwise))
  | id type left right typeIH leftIH rightIH =>
      exact congId (typeIH pointwise) (leftIH pointwise)
        (rightIH pointwise)
  | lam body bodyIH =>
      exact congLam (bodyIH (liftSub_pointwise pointwise))
  | app function argument functionIH argumentIH =>
      exact congApp (functionIH pointwise) (argumentIH pointwise)
  | pair first second firstIH secondIH =>
      exact congPair (firstIH pointwise) (secondIH pointwise)
  | fst pair pairIH =>
      exact mapCompatible Tm.fst (fun step => .congFst step)
        (pairIH pointwise)
  | snd pair pairIH =>
      exact mapCompatible Tm.snd (fun step => .congSnd step)
        (pairIH pointwise)
  | refl term termIH =>
      exact mapCompatible Tm.refl (fun step => .congRefl step)
        (termIH pointwise)

end Conv

/-! ## Typing under context renaming -/

/-- Lookup compatibility for a context renaming. -/
def CtxRen (Gamma : Ctx Head n) (Delta : Ctx Head m) (rho : Ren n m) : Prop :=
  ∀ index : Fin n,
    Ctx.lookup Delta (rho index) = rename rho (Ctx.lookup Gamma index)

theorem CtxRen.snoc {Gamma : Ctx Head n} {Delta : Ctx Head m}
    {rho : Ren n m} (compatible : CtxRen Gamma Delta rho)
    (type : Tm Head n) :
    CtxRen (.snoc Gamma type) (.snoc Delta (rename rho type))
      (liftRen rho) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · calc
      Ctx.lookup (.snoc Delta (rename rho type)) (liftRen rho 0) =
          rename wk (rename rho type) := by rfl
      _ = rename (fun prior => wk (rho prior)) type := by
            simp [rename_comp]
      _ = rename (fun prior => liftRen rho (wk prior)) type := by
            apply rename_ext
            intro prior
            rfl
      _ = rename (liftRen rho) (rename wk type) := by
            simp [rename_comp]
      _ = rename (liftRen rho)
          (Ctx.lookup (.snoc Gamma type) 0) := by rfl
  · intro prior
    calc
      Ctx.lookup (.snoc Delta (rename rho type))
          (liftRen rho prior.succ) =
          rename wk (Ctx.lookup Delta (rho prior)) := by rfl
      _ = rename wk (rename rho (Ctx.lookup Gamma prior)) := by
            rw [compatible prior]
      _ = rename (fun index => wk (rho index))
          (Ctx.lookup Gamma prior) := by
            simp [rename_comp]
      _ = rename (fun index => liftRen rho (wk index))
          (Ctx.lookup Gamma prior) := by
            apply rename_ext
            intro index
            rfl
      _ = rename (liftRen rho)
          (rename wk (Ctx.lookup Gamma prior)) := by
            simp [rename_comp]
      _ = rename (liftRen rho)
          (Ctx.lookup (.snoc Gamma type) prior.succ) := by rfl

theorem HasType.renameTyping {R : Rules Head} {Gamma : Ctx Head n}
    {term type : Tm Head n} (typing : HasType R Gamma term type) :
    ∀ {m : Nat} {Delta : Ctx Head m} {rho : Ren n m},
      CtxRen Gamma Delta rho →
        HasType R Delta (rename rho term) (rename rho type) := by
  induction typing with
  | headType headTyping =>
      intro m Delta rho compatible
      exact .headType headTyping
  | var index =>
      intro m Delta rho compatible
      simpa only [Presentation.rename, compatible index] using
        (HasType.var (R := R) (Γ := Delta) (rho index))
  | const constantTyping =>
      intro m Delta rho compatible
      simpa only [Presentation.rename, rename_liftClosed] using
        (HasType.const (R := R) (Γ := Delta) constantTyping)
  | piForm typeTyping typeUniverse bodyTyping bodyUniverse join
      ihType ihBody =>
      intro m Delta rho compatible
      exact .piForm (ihType compatible) typeUniverse
        (ihBody (CtxRen.snoc compatible _)) bodyUniverse join
  | sigmaForm typeTyping typeUniverse bodyTyping bodyUniverse join
      ihType ihBody =>
      intro m Delta rho compatible
      exact .sigmaForm (ihType compatible) typeUniverse
        (ihBody (CtxRen.snoc compatible _)) bodyUniverse join
  | lamIntro bodyTyping ihBody =>
      intro m Delta rho compatible
      exact .lamIntro (ihBody (CtxRen.snoc compatible _))
  | appElim functionTyping argumentTyping ihFunction ihArgument =>
      intro m Delta rho compatible
      simpa only [Presentation.rename, rename_inst0] using
        (HasType.appElim (ihFunction compatible) (ihArgument compatible))
  | pairIntro firstTyping secondTyping ihFirst ihSecond =>
      intro m Delta rho compatible
      have second := ihSecond compatible
      rw [rename_inst0] at second
      exact .pairIntro (ihFirst compatible) second
  | fstElim pairTyping ihPair =>
      intro m Delta rho compatible
      exact .fstElim (ihPair compatible)
  | sndElim pairTyping ihPair =>
      intro m Delta rho compatible
      simpa only [Presentation.rename, rename_inst0] using
        (HasType.sndElim (ihPair compatible))
  | idForm typeTyping universeWitness leftTyping rightTyping
      ihType ihLeft ihRight =>
      intro m Delta rho compatible
      exact .idForm (ihType compatible) universeWitness
        (ihLeft compatible) (ihRight compatible)
  | reflIntro termTyping ihTerm =>
      intro m Delta rho compatible
      exact .reflIntro (ihTerm compatible)
  | cumul prior order ihPrior =>
      intro m Delta rho compatible
      exact .cumul (ihPrior compatible) order
  | conv prior conversion ihPrior =>
      intro m Delta rho compatible
      exact .conv (ihPrior compatible) (conversion.renameTerms rho)

/-- Weakening by one telescope entry. -/
theorem HasType.weaken {R : Rules Head} {Gamma : Ctx Head n}
    {term type extension : Tm Head n}
    (typing : HasType R Gamma term type) :
    HasType R (.snoc Gamma extension) (rename wk term) (rename wk type) := by
  have compatible : CtxRen Gamma (.snoc Gamma extension) wk := by
    intro index
    rfl
  exact typing.renameTyping compatible

/-! ## Typed simultaneous substitutions -/

/-- A well-typed simultaneous substitution from `Delta` into `Gamma`. -/
def CtxMor (R : Rules Head) (Gamma : Ctx Head n) (Delta : Ctx Head m)
    (sigma : Sub Head n m) : Prop :=
  ∀ index : Fin n,
    HasType R Delta (sigma index)
      (subst sigma (Ctx.lookup Gamma index))

/-- Every context-compatible renaming is a typed variable-only
substitution. -/
theorem CtxRen.toCtxMor {R : Rules Head} {Gamma : Ctx Head n}
    {Delta : Ctx Head m} {rho : Ren n m}
    (compatible : CtxRen Gamma Delta rho) :
    CtxMor R Gamma Delta (renSub rho) := by
  intro index
  change HasType R Delta (.var (rho index))
    (subst (renSub rho) (Ctx.lookup Gamma index))
  rw [subst_renSub, ← compatible index]
  exact HasType.var (rho index)

theorem CtxMor.lift {R : Rules Head} {Gamma : Ctx Head n}
    {Delta : Ctx Head m} {sigma : Sub Head n m}
    (typed : CtxMor R Gamma Delta sigma) (type : Tm Head n) :
    CtxMor R (.snoc Gamma type) (.snoc Delta (subst sigma type))
      (liftSub sigma) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [liftSub_zero, Ctx.lookup_snoc_zero,
      subst_liftSub_wk] using
      (HasType.var (R := R)
        (Γ := .snoc Delta (subst sigma type)) (0 : Fin (m + 1)))
  · intro prior
    have weakened : HasType R (.snoc Delta (subst sigma type))
        (rename wk (sigma prior))
        (rename wk (subst sigma (Ctx.lookup Gamma prior))) :=
      (typed prior).weaken
    simpa only [liftSub_succ, Ctx.lookup_snoc_succ,
      subst_liftSub_wk] using weakened

theorem HasType.substitute {R : Rules Head} {Gamma : Ctx Head n}
    {term type : Tm Head n} (typing : HasType R Gamma term type) :
    ∀ {m : Nat} {Delta : Ctx Head m} {sigma : Sub Head n m},
      CtxMor R Gamma Delta sigma →
        HasType R Delta (subst sigma term) (subst sigma type) := by
  induction typing with
  | headType headTyping =>
      intro m Delta sigma typed
      exact .headType headTyping
  | var index =>
      intro m Delta sigma typed
      exact typed index
  | const constantTyping =>
      intro m Delta sigma typed
      simpa only [Presentation.subst, subst_liftClosed] using
        (HasType.const (R := R) (Γ := Delta) constantTyping)
  | piForm typeTyping typeUniverse bodyTyping bodyUniverse join
      ihType ihBody =>
      intro m Delta sigma typed
      exact .piForm (ihType typed) typeUniverse
        (ihBody (CtxMor.lift typed _)) bodyUniverse join
  | sigmaForm typeTyping typeUniverse bodyTyping bodyUniverse join
      ihType ihBody =>
      intro m Delta sigma typed
      exact .sigmaForm (ihType typed) typeUniverse
        (ihBody (CtxMor.lift typed _)) bodyUniverse join
  | lamIntro bodyTyping ihBody =>
      intro m Delta sigma typed
      exact .lamIntro (ihBody (CtxMor.lift typed _))
  | appElim functionTyping argumentTyping ihFunction ihArgument =>
      intro m Delta sigma typed
      simpa only [Presentation.subst, subst_inst0] using
        (HasType.appElim (ihFunction typed) (ihArgument typed))
  | pairIntro firstTyping secondTyping ihFirst ihSecond =>
      intro m Delta sigma typed
      have second := ihSecond typed
      rw [subst_inst0] at second
      exact .pairIntro (ihFirst typed) second
  | fstElim pairTyping ihPair =>
      intro m Delta sigma typed
      exact .fstElim (ihPair typed)
  | sndElim pairTyping ihPair =>
      intro m Delta sigma typed
      simpa only [Presentation.subst, subst_inst0] using
        (HasType.sndElim (ihPair typed))
  | idForm typeTyping universeWitness leftTyping rightTyping
      ihType ihLeft ihRight =>
      intro m Delta sigma typed
      exact .idForm (ihType typed) universeWitness
        (ihLeft typed) (ihRight typed)
  | reflIntro termTyping ihTerm =>
      intro m Delta sigma typed
      exact .reflIntro (ihTerm typed)
  | cumul prior order ihPrior =>
      intro m Delta sigma typed
      exact .cumul (ihPrior typed) order
  | conv prior conversion ihPrior =>
      intro m Delta sigma typed
      exact .conv (ihPrior typed) (conversion.substitute sigma)

/-! ## Category and context-comprehension laws -/

/-- Composition of simultaneous substitutions. -/
def subComp (tau : Sub Head m k) (sigma : Sub Head n m) : Sub Head n k :=
  fun index => subst tau (sigma index)

@[simp] theorem subst_subComp (tau : Sub Head m k) (sigma : Sub Head n m)
    (term : Tm Head n) :
    subst tau (subst sigma term) = subst (subComp tau sigma) term :=
  subst_comp tau sigma term

theorem subComp_assoc (upsilon : Sub Head k l) (tau : Sub Head m k)
    (sigma : Sub Head n m) :
    subComp upsilon (subComp tau sigma) =
      subComp (subComp upsilon tau) sigma := by
  funext index
  exact subst_comp upsilon tau (sigma index)

@[simp] theorem subComp_ids_left (sigma : Sub Head n m) :
    subComp ids sigma = sigma := by
  funext index
  exact subst_ids (sigma index)

@[simp] theorem subComp_ids_right (sigma : Sub Head n m) :
    subComp sigma ids = sigma := by
  rfl

theorem CtxMor.identity (R : Rules Head) (Gamma : Ctx Head n) :
    CtxMor R Gamma Gamma ids := by
  intro index
  change HasType R Gamma (.var index)
    (subst ids (Ctx.lookup Gamma index))
  simpa only [subst_ids] using
    (HasType.var (R := R) (Γ := Gamma) index)

theorem CtxMor.comp {R : Rules Head}
    {Gamma : Ctx Head n} {Delta : Ctx Head m} {Theta : Ctx Head k}
    {sigma : Sub Head n m} {tau : Sub Head m k}
    (sigmaTyped : CtxMor R Gamma Delta sigma)
    (tauTyped : CtxMor R Delta Theta tau) :
    CtxMor R Gamma Theta (subComp tau sigma) := by
  intro index
  have transported := (sigmaTyped index).substitute tauTyped
  change HasType R Theta (subst tau (sigma index))
    (subst (fun prior => subst tau (sigma prior))
      (Ctx.lookup Gamma index))
  rw [subst_comp] at transported
  exact transported

/-- Pair a newest term with an existing simultaneous substitution. -/
def consSub (term : Tm Head m) (sigma : Sub Head n m) :
    Sub Head (n + 1) m :=
  Fin.cases term sigma

@[simp] theorem consSub_zero (term : Tm Head m) (sigma : Sub Head n m) :
    consSub term sigma 0 = term :=
  rfl

@[simp] theorem consSub_succ (term : Tm Head m) (sigma : Sub Head n m)
    (index : Fin n) :
    consSub term sigma index.succ = sigma index :=
  rfl

/-- Simultaneous substitution into an extended telescope is exactly opening
the newest binder after substituting the weakened older telescope.  This is
the context-comprehension form of repeated dependent application. -/
theorem subst_consSub (term : Tm Head m) (sigma : Sub Head n m)
    (body : Tm Head (n + 1)) :
    subst (consSub term sigma) body =
      inst0 term (subst (liftSub sigma) body) := by
  rw [inst0, subst_comp]
  apply subst_ext
  intro index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    exact (inst0_rename_wk term (sigma prior)).symm

@[simp] theorem subst_consSub_rename_wk (term : Tm Head m)
    (sigma : Sub Head n m) (body : Tm Head n) :
    subst (consSub term sigma) (rename wk body) = subst sigma body := by
  calc
    subst (consSub term sigma) (rename wk body) =
        subst (fun index => consSub term sigma (wk index)) body := by
          simpa using
            (subst_rename (sigma := consSub term sigma) (rho := wk)
              (term := body))
    _ = subst sigma body := by
          apply subst_ext
          intro index
          rfl

theorem CtxMor.extend {R : Rules Head}
    {Gamma : Ctx Head n} {Delta : Ctx Head m}
    {sigma : Sub Head n m} {type : Tm Head n} {term : Tm Head m}
    (sigmaTyped : CtxMor R Gamma Delta sigma)
    (termTyped : HasType R Delta term (subst sigma type)) :
    CtxMor R (.snoc Gamma type) Delta (consSub term sigma) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · simpa only [consSub_zero, Ctx.lookup_snoc_zero,
      subst_consSub_rename_wk] using termTyped
  · intro prior
    simpa only [consSub_succ, Ctx.lookup_snoc_succ,
      subst_consSub_rename_wk] using sigmaTyped prior

/-- Context-extension projection. -/
def projection : Sub Head n (n + 1) := renSub wk

@[simp] theorem subst_projection (term : Tm Head n) :
    subst (projection (Head := Head)) term = rename wk term :=
  subst_renSub wk term

theorem CtxMor.projectionTyped (R : Rules Head) (Gamma : Ctx Head n)
    (type : Tm Head n) :
    CtxMor R Gamma (.snoc Gamma type) projection := by
  intro index
  change HasType R (.snoc Gamma type) (.var index.succ)
    (subst projection (Ctx.lookup Gamma index))
  simpa only [subst_projection, Ctx.lookup_snoc_succ] using
    (HasType.var (R := R) (Γ := .snoc Gamma type) index.succ)

/-- First context-comprehension beta law. -/
@[simp] theorem subComp_consSub_projection (term : Tm Head m)
    (sigma : Sub Head n m) :
    subComp (consSub term sigma) projection = sigma := by
  funext index
  rfl

/-- Second context-comprehension beta law. -/
@[simp] theorem subst_consSub_var_zero (term : Tm Head m)
    (sigma : Sub Head n m) :
    subst (consSub term sigma) (.var 0) = term :=
  rfl

/-- Context-comprehension eta law. -/
theorem consSub_eta (sigma : Sub Head (n + 1) m) :
    consSub (sigma 0) (fun index => sigma index.succ) = sigma := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

/-- Composition distributes through context pairing. -/
theorem subComp_consSub (tau : Sub Head m k) (term : Tm Head m)
    (sigma : Sub Head n m) :
    subComp tau (consSub term sigma) =
      consSub (subst tau term) (subComp tau sigma) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

/-! ## Executable boundary examples -/

/-- Positive: identity substitution is typed for every presentation. -/
example (R : Rules Head) (Gamma : Ctx Head n) :
    CtxMor R Gamma Gamma ids :=
  CtxMor.identity R Gamma

/-- Negative: the newest variable and every weakened older variable remain
distinct, so projection cannot masquerade as the comprehension term. -/
example (index : Fin n) :
    (.var 0 : Tm Head (n + 1)) ≠ .var (wk index) := by
  intro equality
  have indexEquality : (0 : Fin (n + 1)) = wk index :=
    Tm.var.inj equality
  exact (Fin.succ_ne_zero index) indexEquality.symm

/-! ## Axiom audit -/

#print axioms Conv.substitutePointwise
#print axioms subst_consSub
#print axioms CtxMor.extend
#print axioms consSub_eta

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
