import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalModel

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Semantic versions of selected p. 85 "quoted results" from Henkin (1950)
whose paper statements are already clear, but whose exact proof-theoretic
bridge to the current trusted HOL core is still being refined.

These are kept separate from `DerivedResults.lean`, which records the fragment
already available as actual derivations in the extensional overlay.
-/

/-- Universal closure of a predicate term. -/
def allOf {Γ : Ctx Atom} {α : HTy} (p : Term Γ (Pred α)) : Formula Γ :=
  .all (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz))

/-- Predicate complement as a term. -/
def complementPred {Γ : Ctx Atom} {α : HTy} (p : Term Γ (Pred α)) : Term Γ (Pred α) :=
  .lam (.not (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)))

/-- Pointwise equality predicate between two function terms. -/
def pointwiseEqPred {Γ : Ctx Atom} {α β : HTy}
    (f g : Term Γ (β ⇒ α)) : Term Γ (Pred β) :=
  .lam
    (.eq
      (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
      (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz)))

/-- Pointwise disequality predicate between two function terms. -/
def pointwiseNePred {Γ : Ctx Atom} {α β : HTy}
    (f g : Term Γ (β ⇒ α)) : Term Γ (Pred β) :=
  complementPred (pointwiseEqPred f g)

/-- The sole predicate variable in context `[Pred α]`. -/
def topPred {α : HTy} : Term [Pred α] (Pred α) := .var .vz

/-- The older function variable in context `[β ⇒ α, β ⇒ α]`. -/
def firstFun {α β : HTy} : Term [β ⇒ α, β ⇒ α] (β ⇒ α) := .var (.vs .vz)

/-- The newer function variable in context `[β ⇒ α, β ⇒ α]`. -/
def secondFun {α β : HTy} : Term [β ⇒ α, β ⇒ α] (β ⇒ α) := .var .vz

/-- Existential pointwise-disequality for two function terms. -/
def exPointwiseNe {Γ : Ctx Atom} {α β : HTy}
    (f g : Term Γ (β ⇒ α)) : Formula Γ :=
  let q := pointwiseNePred f g
  .ex (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) q) (.var .vz))

/-- Equality at the `ι`-chosen point of the pointwise-disequality predicate
for two function terms. -/
def eqAtIotaPointwiseNe {Γ : Ctx Atom} {α β : HTy}
    (f g : Term Γ (β ⇒ α)) : Formula Γ :=
  let q := pointwiseNePred f g
  .eq
    (.app f (iotaTerm q))
    (.app g (iotaTerm q))

/-- Henkin's quoted result 22 as an open formula. -/
def derived22 {α β : HTy} : Formula [β ⇒ α, β ⇒ α] :=
  imp
    (eqAtIotaPointwiseNe
      (firstFun (α := α) (β := β))
      (secondFun (α := α) (β := β)))
    (eq (firstFun (α := α) (β := β)) (secondFun (α := α) (β := β)))

/-- Henkin's quoted result 28 as an open formula. -/
def derived28 {α : HTy} : Formula [Pred α] :=
  let q := complementPred (topPred (α := α))
  imp
    (.app (topPred (α := α)) (iotaTerm q))
    (allOf (topPred (α := α)))

@[simp] theorem weaken_complementPred
    {Γ : Ctx Atom} {α σ : HTy} (p : Term Γ (Pred α)) :
    weaken (Base := Atom) (Const := Primitive) (σ := σ) (complementPred p) =
      complementPred (weaken (Base := Atom) (Const := Primitive) (σ := σ) p) := by
  unfold complementPred weaken
  apply congrArg Term.lam
  apply congrArg Term.not
  apply congrArg (fun q => Term.app q (.var .vz))
  simpa [weaken] using
    (rename_lift_weaken
      (Base := Atom)
      (Const := Primitive)
      (σ := α)
      (ρ := Rename.weaken (Base := Atom) (Γ := Γ) (σ := σ))
      (t := p))

@[simp] theorem weaken_pointwiseEqPred
    {Γ : Ctx Atom} {α β σ : HTy} (f g : Term Γ (β ⇒ α)) :
    weaken (Base := Atom) (Const := Primitive) (σ := σ) (pointwiseEqPred f g) =
      pointwiseEqPred
        (weaken (Base := Atom) (Const := Primitive) (σ := σ) f)
        (weaken (Base := Atom) (Const := Primitive) (σ := σ) g) := by
  unfold pointwiseEqPred weaken
  apply congrArg Term.lam
  apply congrArg₂ (fun a b => Term.eq a b)
  · apply congrArg (fun q => Term.app q (.var .vz))
    simpa [weaken] using
      (rename_lift_weaken
        (Base := Atom)
        (Const := Primitive)
        (σ := β)
        (ρ := Rename.weaken (Base := Atom) (Γ := Γ) (σ := σ))
        (t := f))
  · apply congrArg (fun q => Term.app q (.var .vz))
    simpa [weaken] using
      (rename_lift_weaken
        (Base := Atom)
        (Const := Primitive)
        (σ := β)
        (ρ := Rename.weaken (Base := Atom) (Γ := Γ) (σ := σ))
        (t := g))

@[simp] theorem weaken_pointwiseNePred
    {Γ : Ctx Atom} {α β σ : HTy} (f g : Term Γ (β ⇒ α)) :
    weaken (Base := Atom) (Const := Primitive) (σ := σ) (pointwiseNePred f g) =
      pointwiseNePred
        (weaken (Base := Atom) (Const := Primitive) (σ := σ) f)
        (weaken (Base := Atom) (Const := Primitive) (σ := σ) g) := by
  simp [pointwiseNePred]

/-- Closing an application of `pointwiseEqPred` is exactly closing the
corresponding equality-at-a-point formula. -/
theorem closeFormula_pointwiseEqPred_mem_iff_eq_mem
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ρ : RepresentativeAssignment Γ)
    {α β : HTy}
    (f g : Term Γ (β ⇒ α)) (t : Term Γ β) :
    closeFormula ρ (.app (pointwiseEqPred f g) t) ∈ T ↔
      closeFormula ρ (.eq (.app f t) (.app g t)) ∈ T := by
  let body : Formula (β :: Γ) :=
    .eq
      (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
      (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
  let t' : ClosedTerm β := closeTerm ρ t
  have hAppClose
      (h : Term Γ (β ⇒ α)) :
      subst
          (RepresentativeAssignment.extend ρ t')
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) h) (.var .vz)
            : Term (β :: Γ) α) =
        subst ρ (.app h t : Term Γ α) := by
    have hWeaken :
        subst
            (RepresentativeAssignment.extend ρ t')
            (weaken (Base := Atom) (Const := Primitive) (σ := β) h) =
          subst ρ h := by
      rw [weaken, subst_rename]
      apply subst_ext
      intro τ v
      simp [Rename.weaken, RepresentativeAssignment.extend]
    calc
      subst
          (RepresentativeAssignment.extend ρ t')
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) h) (.var .vz)
            : Term (β :: Γ) α) =
        .app
          (subst
            (RepresentativeAssignment.extend ρ t')
            (weaken (Base := Atom) (Const := Primitive) (σ := β) h))
          (RepresentativeAssignment.extend ρ t' .vz) := by
            rfl
      _ = .app (subst ρ h) t' := by
            simp [hWeaken, RepresentativeAssignment.extend]
      _ = subst ρ (.app h t : Term Γ α) := by
            rfl
  have hBody :
      closeTerm (RepresentativeAssignment.extend ρ t') body =
        closeFormula ρ (.eq (.app f t) (.app g t)) := by
    unfold body
    change
      Term.eq
        (subst
          (RepresentativeAssignment.extend ρ t')
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz)))
        (subst
          (RepresentativeAssignment.extend ρ t')
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))) =
      Term.eq
        (subst ρ (.app f t))
        (subst ρ (.app g t))
    exact congrArg₂ (fun a b => Term.eq a b) (hAppClose f) (hAppClose g)
  have hInst :
      instantiate (Base := Atom) t'
        (subst
          (Subst.lift (Base := Atom) (Const := Primitive) ρ)
          body) =
        closeFormula ρ (.eq (.app f t) (.app g t)) := by
    calc
      instantiate (Base := Atom) t'
          (subst
            (Subst.lift (Base := Atom) (Const := Primitive) ρ)
            body) =
        closeTerm (RepresentativeAssignment.extend ρ t') body := by
          exact
            instantiate_subst_lift
              (ρ := ρ)
              (t := t')
              (u := body)
      _ = closeFormula ρ (.eq (.app f t) (.app g t)) := hBody
  have hEq :
      TermEquivalent T
        (closeFormula ρ (.app (pointwiseEqPred f g) t))
        (closeFormula ρ (.eq (.app f t) (.app g t))) := by
    exact
      extSetProvable_of_theorem (T := T) <|
        by
          have hbeta :=
            ExtDerivation.beta (Const := Primitive)
              (Δ := ([] : List (ClosedFormula Primitive))) t'
              (subst (Subst.lift (Base := Atom) (Const := Primitive) ρ) body)
          rw [hInst] at hbeta
          simpa [t', body, pointwiseEqPred, closeFormula, closeTerm, subst, eq, Subst.lift] using hbeta
  exact
    mem_iff_of_provablyEquivalent_prop hT
      (provablyEquivalent_of_termEquivalent_prop hEq)

/-- Closing an application of the complement predicate amounts to closing the
negation of the original application. -/
theorem closeFormula_complementPred_mem_iff_not_mem
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ρ : RepresentativeAssignment Γ)
    {α : HTy}
    (p : Term Γ (Pred α)) (t : Term Γ α) :
    closeFormula ρ (.app (complementPred p) t) ∈ T ↔
      closeFormula ρ (.app p t) ∉ T := by
  let body : Formula (α :: Γ) :=
    .not (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz))
  let t' : ClosedTerm α := closeTerm ρ t
  have hInst :
      instantiate (Base := Atom) t'
        (subst
          (Subst.lift (Base := Atom) (Const := Primitive) ρ)
          body) =
        (.not (closeFormula ρ (.app p t)) : Sentence) := by
    calc
      instantiate (Base := Atom) t'
          (subst
            (Subst.lift (Base := Atom) (Const := Primitive) ρ)
            body) =
        closeTerm (RepresentativeAssignment.extend ρ t') body := by
          exact
            instantiate_subst_lift
              (ρ := ρ)
              (t := t')
              (u := body)
      _ = (.not (closeFormula ρ (.app p t)) : Sentence) := by
          have hWeaken :
              subst
                  (RepresentativeAssignment.extend ρ t')
                  (weaken (Base := Atom) (Const := Primitive) (σ := α) p) =
                subst ρ p := by
            rw [weaken, subst_rename]
            apply subst_ext
            intro τ v
            simp [Rename.weaken, RepresentativeAssignment.extend]
          have hApp :
              subst
                (RepresentativeAssignment.extend ρ t')
                (.app
                  (weaken (Base := Atom) (Const := Primitive) (σ := α) p)
                  (.var .vz) : Formula (α :: Γ)) =
              subst ρ (.app p t : Formula Γ) := by
            calc
              subst
                  (RepresentativeAssignment.extend ρ t')
                  (.app
                    (weaken (Base := Atom) (Const := Primitive) (σ := α) p)
                    (.var .vz) : Formula (α :: Γ)) =
                .app
                  (subst
                    (RepresentativeAssignment.extend ρ t')
                    (weaken (Base := Atom) (Const := Primitive) (σ := α) p))
                  (RepresentativeAssignment.extend ρ t' .vz) := by
                    rfl
              _ = .app (subst ρ p) t' := by
                    simp [hWeaken, RepresentativeAssignment.extend]
              _ = subst ρ (.app p t : Formula Γ) := by
                    change Term.app (subst ρ p) (subst ρ t) =
                      subst ρ (.app p t : Formula Γ)
                    rfl
          unfold body
          exact congrArg Term.not hApp
  have hBetaTheorem :
      ExtDerivation.Theorem Primitive
        (eq
          (closeFormula ρ (.app (complementPred p) t))
          (.not (closeFormula ρ (.app p t)))) := by
    have hbeta :=
      ExtDerivation.beta (Const := Primitive)
        (Δ := ([] : List (ClosedFormula Primitive))) t'
        (subst (Subst.lift (Base := Atom) (Const := Primitive) ρ) body)
    rw [hInst] at hbeta
    simpa [t', body, complementPred, closeFormula, closeTerm, subst, eq, not, Subst.lift] using hbeta
  have hBeta :
      TermEquivalent T
        (closeFormula ρ (.app (complementPred p) t))
        (.not (closeFormula ρ (.app p t))) :=
    extSetProvable_of_theorem (T := T) hBetaTheorem
  have hEqv :
      Mettapedia.Logic.HOL.ClosedTheorySet.ProvablyEquivalent
        (Const := Primitive) T
        (closeFormula ρ (.app (complementPred p) t))
        (.not (closeFormula ρ (.app p t))) :=
    provablyEquivalent_of_termEquivalent_prop hBeta
  constructor
  · intro hMem
    have hNegMem :
        (.not (closeFormula ρ (.app p t)) : Sentence) ∈ T :=
      (mem_iff_of_provablyEquivalent_prop (T := T) hT hEqv).mp hMem
    exact (CompleteConsistentTheory.neg_mem_iff_not_mem hT).mp hNegMem
  · intro hNotMem
    have hNegMem :
        (.not (closeFormula ρ (.app p t)) : Sentence) ∈ T :=
      (CompleteConsistentTheory.neg_mem_iff_not_mem hT).mpr hNotMem
    exact (mem_iff_of_provablyEquivalent_prop (T := T) hT hEqv).mpr hNegMem

/-- In the packaged canonical class model, the complement predicate behaves as
logical negation under any realizing representative substitution. -/
theorem denoteFormula_app_complementPred_iff_not
    (M : CanonicalClassModel)
    {ν : M.Assignment Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    {α : HTy}
    (p : Term Γ (Pred α)) (t : Term Γ α) :
    M.denoteFormula ν (.app (complementPred p) t) ↔
      ¬ M.denoteFormula ν (.app p t) := by
  constructor
  · intro hComp hApp
    have hCompMem :
        closeFormula ρ (.app (complementPred p) t) ∈ M.T :=
      (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
        (.app (complementPred p) t)).mp hComp
    have hAppMem :
        closeFormula ρ (.app p t) ∈ M.T :=
      (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
        (.app p t)).mp hApp
    exact
      (closeFormula_complementPred_mem_iff_not_mem
        (T := M.T)
        M.completeConsistent
        ρ
        p
        t).mp hCompMem hAppMem
  · intro hNotComp
    have hCompMem :
        closeFormula ρ (.app (complementPred p) t) ∈ M.T :=
      (closeFormula_complementPred_mem_iff_not_mem
        (T := M.T)
        M.completeConsistent
        ρ
        p
        t).mpr
        (fun hAppMem =>
          hNotComp <|
            (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
              (.app p t)).mpr hAppMem)
    exact
      (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
        (.app (complementPred p) t)).mpr hCompMem

/-- Applying `pointwiseEqPred` in the canonical class model is exactly
equality-at-a-point. -/
theorem denoteFormula_app_pointwiseEqPred_iff_eq
    (M : CanonicalClassModel)
    {ν : M.Assignment Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    {α β : HTy}
    (f g : Term Γ (β ⇒ α)) (t : Term Γ β) :
    M.denoteFormula ν (.app (pointwiseEqPred f g) t) ↔
      M.denoteFormula ν (.eq (.app f t) (.app g t)) := by
  constructor
  · intro hEqPred
    have hMem :
        closeFormula ρ (.app (pointwiseEqPred f g) t) ∈ M.T :=
      (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
        (.app (pointwiseEqPred f g) t)).mp hEqPred
    exact
      (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
        (.eq (.app f t) (.app g t))).mpr <|
        (closeFormula_pointwiseEqPred_mem_iff_eq_mem
          (T := M.T)
          M.completeConsistent
          ρ
          f
          g
          t).mp hMem
  · intro hEq
    have hMem :
        closeFormula ρ (.eq (.app f t) (.app g t)) ∈ M.T :=
      (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
        (.eq (.app f t) (.app g t))).mp hEq
    exact
      (M.denoteFormula_iff_closeFormula_mem_of_realizes hρ
        (.app (pointwiseEqPred f g) t)).mpr <|
        (closeFormula_pointwiseEqPred_mem_iff_eq_mem
          (T := M.T)
          M.completeConsistent
          ρ
          f
          g
          t).mpr hMem

/-- Applying `pointwiseNePred` in the canonical class model is exactly
disequality-at-a-point. -/
theorem denoteFormula_app_pointwiseNePred_iff_not_eq
    (M : CanonicalClassModel)
    {ν : M.Assignment Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    {α β : HTy}
    (f g : Term Γ (β ⇒ α)) (t : Term Γ β) :
    M.denoteFormula ν (.app (pointwiseNePred f g) t) ↔
      ¬ M.denoteFormula ν (.eq (.app f t) (.app g t)) := by
  constructor
  · intro hNe hEq
    exact
      (denoteFormula_app_complementPred_iff_not
        M
        (hρ := hρ)
        (p := pointwiseEqPred f g)
        (t := t)).mp hNe <|
        (denoteFormula_app_pointwiseEqPred_iff_eq
          M
          (hρ := hρ)
          f
          g
          t).2 hEq
  · intro hNotEq
    exact
      (denoteFormula_app_complementPred_iff_not
        M
        (hρ := hρ)
        (p := pointwiseEqPred f g)
        (t := t)).2 <|
        fun hEqPred =>
          hNotEq <|
            (denoteFormula_app_pointwiseEqPred_iff_eq
              M
              (hρ := hρ)
              f
              g
              t).1 hEqPred

/-- Quoted result 28 already holds in the packaged canonical description model,
for any predicate term in any context. -/
theorem denoteFormula_derived28_general
    {Γ : Ctx Atom} {α : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (p : Term Γ (Pred α)) :
    M.toCanonicalClassModel.denoteFormula ν
      (imp
        (.app p (iotaTerm (complementPred p)))
        (allOf p) : Formula Γ) := by
  rw [M.toCanonicalClassModel.denoteFormula_imp_iff]
  intro hpChoice
  change M.toCanonicalClassModel.denoteFormula ν
      (.all (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := α) p)
        (.var .vz)))
  rw [M.toCanonicalClassModel.denoteFormula_all_iff]
  intro x
  by_cases hpx :
      M.toCanonicalClassModel.denoteFormula
        (ClassAssignment.extend ν x)
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz))
  · exact hpx
  · have hComplementWitness :
        M.toCanonicalClassModel.denoteFormula
          (ClassAssignment.extend ν x)
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := α) (complementPred p))
            (.var .vz)) := by
      simpa using
        (denoteFormula_app_complementPred_iff_not
          M.toCanonicalClassModel
          (hρ := ClassAssignment.chooseRepresentatives_realizes
            (ClassAssignment.extend ν x))
          (p := weaken (Base := Atom) (Const := Primitive) (σ := α) p)
          (t := (.var .vz : Term (α :: Γ) α))).2 hpx
    have hEx :
        M.toCanonicalClassModel.denoteFormula ν
          (.ex (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := α) (complementPred p))
            (.var .vz)) : Formula Γ) := by
      exact
        (M.toCanonicalClassModel.denoteFormula_ex_iff
          (ν := ν)
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := α) (complementPred p))
            (.var .vz))).2 ⟨x, hComplementWitness⟩
    have hComplementChoice :
        M.toCanonicalClassModel.denoteFormula ν
          (.app (complementPred p) (iotaTerm (complementPred p)) : Formula Γ) :=
      (M.toCanonicalClassModel.denoteFormula_imp_iff
        ν
        (.ex (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := α) (complementPred p))
          (.var .vz)))
        (.app (complementPred p) (iotaTerm (complementPred p)))).mp
          (M.denoteFormula_description_instance ν (complementPred p))
          hEx
    have hNotChoice :
        ¬ M.toCanonicalClassModel.denoteFormula ν
            (.app p (iotaTerm (complementPred p)) : Formula Γ) :=
      (denoteFormula_app_complementPred_iff_not
        M.toCanonicalClassModel
        (hρ := ClassAssignment.chooseRepresentatives_realizes ν)
        (p := p)
        (t := iotaTerm (complementPred p))).mp hComplementChoice
    exact False.elim (hNotChoice hpChoice)

/-- Canonical-description-model instance of quoted result 28. -/
theorem derived28_denoteFormula_inCanonicalDescriptionModel
    {α : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [Pred α]) :
    M.toCanonicalClassModel.denoteFormula ν (derived28 (α := α)) := by
  simpa [derived28] using
    denoteFormula_derived28_general
      (M := M)
      (ν := ν)
      (p := topPred (α := α))

/-- Quoted result 28 now also has a representative-free canonical membership
form in the packaged canonical description model. -/
theorem derived28_closeFormula_mem_inCanonicalDescriptionModel
    {α : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [Pred α]) :
    ClassAssignment.closeFormula ν (derived28 (α := α)) ∈ M.T := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula, Holds] using
    derived28_denoteFormula_inCanonicalDescriptionModel (M := M) ν

/-- Representative-independent closed-theory form of quoted result 28 in the
packaged canonical description model. -/
theorem derived28_closeFormula_mem_of_realizes_inCanonicalDescriptionModel
    {α : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {ν : M.toCanonicalClassModel.Assignment [Pred α]}
    {ρ : RepresentativeAssignment [Pred α]}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν) :
    closeFormula ρ (derived28 (α := α)) ∈ M.T := by
  exact
    (M.toCanonicalClassModel.denoteFormula_iff_closeFormula_mem_of_realizes
      hρ
      (derived28 (α := α))).mp <|
      derived28_denoteFormula_inCanonicalDescriptionModel (M := M) ν

/-- Canonical-description-model instance of quoted result 22. -/
theorem derived22_denoteFormula_inCanonicalDescriptionModel
    {α β : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [β ⇒ α, β ⇒ α]) :
    M.toCanonicalClassModel.denoteFormula ν (derived22 (α := α) (β := β)) := by
  let q : Term [β ⇒ α, β ⇒ α] (Pred β) :=
    pointwiseNePred
      (firstFun (α := α) (β := β))
      (secondFun (α := α) (β := β))
  let axiom10Ante : Formula [β ⇒ α, β ⇒ α] :=
    .all
      (.eq
        (.app (.var (.vs .vz)) (.var .vz))
        (.app (.var (.vs (.vs .vz))) (.var .vz)))
  let axiom10Cons : Formula [β ⇒ α, β ⇒ α] :=
    .eq
      (secondFun (α := α) (β := β))
      (firstFun (α := α) (β := β))
  rw [derived22, M.toCanonicalClassModel.denoteFormula_imp_iff]
  intro hChosenEq
  have hAxiom10Imp :
      M.toCanonicalClassModel.denoteFormula ν
        (imp axiom10Ante axiom10Cons) := by
    simpa only [axiom10Ante, axiom10Cons, axiom10, firstFun, secondFun, imp] using
      (M.toCanonicalClassModel.axiom10_holds (σ := β) (τ := α) ν)
  have hAxiom10 :
      M.toCanonicalClassModel.denoteFormula ν axiom10Ante →
        M.toCanonicalClassModel.denoteFormula ν
          axiom10Cons :=
    (M.toCanonicalClassModel.denoteFormula_imp_iff
      (ν := ν)
      axiom10Ante
      axiom10Cons).1 hAxiom10Imp
  have hAllEqReverse :
      M.toCanonicalClassModel.denoteFormula ν
        axiom10Ante := by
    rw [M.toCanonicalClassModel.denoteFormula_all_iff]
    intro x
    by_cases hEqAtX :
        M.toCanonicalClassModel.denoteFormula
          (ClassAssignment.extend ν x)
          (.eq
            (.app
              (weaken (Base := Atom) (Const := Primitive) (σ := β)
                (firstFun (α := α) (β := β)))
              (.var .vz))
            (.app
              (weaken (Base := Atom) (Const := Primitive) (σ := β)
                (secondFun (α := α) (β := β)))
              (.var .vz)) : Formula (β :: [β ⇒ α, β ⇒ α])) 
    · have hEqAtXReverse :
          M.toCanonicalClassModel.denoteFormula
            (ClassAssignment.extend ν x)
            (.eq
              (.app (.var (.vs .vz)) (.var .vz))
              (.app (.var (.vs (.vs .vz))) (.var .vz)) :
                Formula (β :: [β ⇒ α, β ⇒ α])) := by
        have hEqAtXTerms :
            M.toCanonicalClassModel.denoteTerm
              (ClassAssignment.extend ν x)
              (.app
                (weaken (Base := Atom) (Const := Primitive) (σ := β)
                  (firstFun (α := α) (β := β)))
                (.var .vz)) =
            M.toCanonicalClassModel.denoteTerm
              (ClassAssignment.extend ν x)
              (.app
                (weaken (Base := Atom) (Const := Primitive) (σ := β)
                  (secondFun (α := α) (β := β)))
                (.var .vz)) :=
          (M.toCanonicalClassModel.denoteFormula_eq_iff
            (ν := ClassAssignment.extend ν x)
            (t := .app
              (weaken (Base := Atom) (Const := Primitive) (σ := β)
                (firstFun (α := α) (β := β)))
              (.var .vz))
            (u := .app
              (weaken (Base := Atom) (Const := Primitive) (σ := β)
                (secondFun (α := α) (β := β)))
              (.var .vz))).1 hEqAtX
        exact
          (M.toCanonicalClassModel.denoteFormula_eq_iff
            (ν := ClassAssignment.extend ν x)
            (t := .app (.var (.vs .vz)) (.var .vz))
            (u := .app (.var (.vs (.vs .vz))) (.var .vz))).2 <|
            by
              simpa [firstFun, secondFun, ClassAssignment.extend] using hEqAtXTerms.symm
      exact hEqAtXReverse
    · have hWitness :
          M.toCanonicalClassModel.denoteFormula
            (ClassAssignment.extend ν x)
            (.app
              (weaken (Base := Atom) (Const := Primitive) (σ := β) q)
              (.var .vz) : Formula (β :: [β ⇒ α, β ⇒ α])) := by
        have hNotEqAtX :
            ¬ M.toCanonicalClassModel.denoteFormula
                (ClassAssignment.extend ν x)
                (.eq
                  (.app
                    (weaken (Base := Atom) (Const := Primitive) (σ := β)
                      (firstFun (α := α) (β := β)))
                    (.var .vz))
                  (.app
                    (weaken (Base := Atom) (Const := Primitive) (σ := β)
                      (secondFun (α := α) (β := β)))
                    (.var .vz)) : Formula (β :: [β ⇒ α, β ⇒ α])) :=
          hEqAtX
        simpa [q] using
          (denoteFormula_app_pointwiseNePred_iff_not_eq
            M.toCanonicalClassModel
            (hρ := ClassAssignment.chooseRepresentatives_realizes
              (ClassAssignment.extend ν x))
            (f := weaken (Base := Atom) (Const := Primitive) (σ := β)
              (firstFun (α := α) (β := β)))
            (g := weaken (Base := Atom) (Const := Primitive) (σ := β)
              (secondFun (α := α) (β := β)))
            (t := (.var .vz : Term (β :: [β ⇒ α, β ⇒ α]) β))).2 hNotEqAtX
      have hEx :
          M.toCanonicalClassModel.denoteFormula ν
            (.ex
              (.app
                (weaken (Base := Atom) (Const := Primitive) (σ := β) q)
                (.var .vz)) : Formula [β ⇒ α, β ⇒ α]) := by
        exact
          (M.toCanonicalClassModel.denoteFormula_ex_iff
            (ν := ν)
            (.app
              (weaken (Base := Atom) (Const := Primitive) (σ := β) q)
              (.var .vz))).2 ⟨x, hWitness⟩
      have hChosenNe :
          M.toCanonicalClassModel.denoteFormula ν
            (.app q (iotaTerm q) : Formula [β ⇒ α, β ⇒ α]) :=
        ((M.toCanonicalClassModel.denoteFormula_imp_iff
          (ν := ν)
          (.ex
            (.app
              (weaken (Base := Atom) (Const := Primitive) (σ := β) q)
              (.var .vz)))
          (.app q (iotaTerm q))).1
          (M.denoteFormula_description_instance ν q))
          hEx
      have hNotChosenEq :
          ¬ M.toCanonicalClassModel.denoteFormula ν
              (.eq
                (.app
                  (firstFun (α := α) (β := β))
                  (iotaTerm q))
                (.app
                  (secondFun (α := α) (β := β))
                  (iotaTerm q)) : Formula [β ⇒ α, β ⇒ α]) := by
        exact
          (denoteFormula_app_pointwiseNePred_iff_not_eq
            M.toCanonicalClassModel
            (hρ := ClassAssignment.chooseRepresentatives_realizes ν)
            (f := firstFun (α := α) (β := β))
            (g := secondFun (α := α) (β := β))
            (t := iotaTerm q)).1 hChosenNe
      exact False.elim (hNotChosenEq hChosenEq)
  have hEqReverse :
      M.toCanonicalClassModel.denoteFormula ν
        axiom10Cons :=
    hAxiom10 hAllEqReverse
  have hEqForward :
      M.toCanonicalClassModel.denoteFormula ν
        (.eq
          (firstFun (α := α) (β := β))
          (secondFun (α := α) (β := β)) : Formula [β ⇒ α, β ⇒ α]) := by
    have hEqReverseTerms :
        M.toCanonicalClassModel.denoteTerm ν
          (secondFun (α := α) (β := β)) =
        M.toCanonicalClassModel.denoteTerm ν
          (firstFun (α := α) (β := β)) :=
      (M.toCanonicalClassModel.denoteFormula_eq_iff
        (ν := ν)
        (t := secondFun (α := α) (β := β))
        (u := firstFun (α := α) (β := β))).1 hEqReverse
    exact
      (M.toCanonicalClassModel.denoteFormula_eq_iff
        (ν := ν)
        (t := firstFun (α := α) (β := β))
        (u := secondFun (α := α) (β := β))).2 hEqReverseTerms.symm
  exact hEqForward

/-- Quoted result 22 now has a representative-free canonical membership form in
the packaged canonical description model. -/
theorem derived22_closeFormula_mem_inCanonicalDescriptionModel
    {α β : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [β ⇒ α, β ⇒ α]) :
    ClassAssignment.closeFormula ν (derived22 (α := α) (β := β)) ∈ M.T := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula, Holds] using
    derived22_denoteFormula_inCanonicalDescriptionModel (M := M) ν

/-- Representative-independent closed-theory form of quoted result 22 in the
packaged canonical description model. -/
theorem derived22_closeFormula_mem_of_realizes_inCanonicalDescriptionModel
    {α β : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {ν : M.toCanonicalClassModel.Assignment [β ⇒ α, β ⇒ α]}
    {ρ : RepresentativeAssignment [β ⇒ α, β ⇒ α]}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν) :
    closeFormula ρ (derived22 (α := α) (β := β)) ∈ M.T := by
  exact
    (M.toCanonicalClassModel.denoteFormula_iff_closeFormula_mem_of_realizes
      hρ
      (derived22 (α := α) (β := β))).mp <|
      derived22_denoteFormula_inCanonicalDescriptionModel (M := M) ν

/-- Mixed description-aware truth canary: if two function terms differ at some
argument, then they are not extensionally equal in the packaged canonical
description model. -/
theorem denoteFormula_exists_pointwiseNe_imp_not_eq
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    M.toCanonicalClassModel.denoteFormula ν
      (imp
        (.ex
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseNePred f g))
            (.var .vz)))
        (not (.eq f g)) : Formula Γ) := by
  let q : Term Γ (Pred β) := pointwiseNePred f g
  rw [M.toCanonicalClassModel.denoteFormula_imp_iff]
  intro hEx
  rw [M.toCanonicalClassModel.denoteFormula_not_iff]
  intro hEq
  have hChoiceNe :
      M.toCanonicalClassModel.denoteFormula ν
        (.app q (iotaTerm q) : Formula Γ) :=
    ((M.toCanonicalClassModel.denoteFormula_imp_iff
      (ν := ν)
      (.ex
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β) q)
          (.var .vz)))
      (.app q (iotaTerm q))).1
      (M.denoteFormula_description_instance ν q))
      hEx
  have hNotEqAtChoice :
      ¬ M.toCanonicalClassModel.denoteFormula ν
          (.eq
            (.app f (iotaTerm q))
            (.app g (iotaTerm q)) : Formula Γ) :=
    (denoteFormula_app_pointwiseNePred_iff_not_eq
      M.toCanonicalClassModel
      (hρ := ClassAssignment.chooseRepresentatives_realizes ν)
      (f := f)
      (g := g)
      (t := iotaTerm q)).1 hChoiceNe
  have hEqTerms :
      M.toCanonicalClassModel.denoteTerm ν f =
        M.toCanonicalClassModel.denoteTerm ν g :=
    (M.toCanonicalClassModel.denoteFormula_eq_iff
      (ν := ν)
      (t := f)
      (u := g)).1 hEq
  have hEqAtChoice :
      M.toCanonicalClassModel.denoteFormula ν
        (.eq
          (.app f (iotaTerm q))
          (.app g (iotaTerm q)) : Formula Γ) := by
    apply
      (M.toCanonicalClassModel.denoteFormula_eq_iff
        (ν := ν)
        (t := .app f (iotaTerm q))
        (u := .app g (iotaTerm q))).2
    rw [M.toCanonicalClassModel.denoteTerm_app, M.toCanonicalClassModel.denoteTerm_app, hEqTerms]
  exact hNotEqAtChoice hEqAtChoice

/-- Representative-free canonical membership form of the mixed pointwise
disequality canary. -/
theorem classAssignment_closeFormula_exists_pointwiseNe_imp_not_eq_mem
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    ClassAssignment.closeFormula ν
      (imp
        (.ex
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseNePred f g))
            (.var .vz)))
        (not (.eq f g)) : Formula Γ) ∈ M.T := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula, Holds] using
    denoteFormula_exists_pointwiseNe_imp_not_eq (M := M) ν f g

/-- Realizing-representative closed-theory form of the mixed pointwise
disequality canary. -/
theorem closeFormula_exists_pointwiseNe_imp_not_eq_mem_of_realizes
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    {ν : M.toCanonicalClassModel.Assignment Γ}
    {ρ : RepresentativeAssignment Γ}
    (hρ : RepresentativeAssignment.Realizes M.T ρ ν)
    (f g : Term Γ (β ⇒ α)) :
    closeFormula ρ
      (imp
        (.ex
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseNePred f g))
            (.var .vz)))
        (not (.eq f g)) : Formula Γ) ∈ M.T := by
  exact
    (M.toCanonicalClassModel.denoteFormula_iff_closeFormula_mem_of_realizes
      hρ
      (imp
        (.ex
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseNePred f g))
            (.var .vz)))
        (not (.eq f g)) : Formula Γ)).mp <|
      denoteFormula_exists_pointwiseNe_imp_not_eq (M := M) ν f g

/-- Canonical-truth form of pointwise equality at a chosen argument. -/
theorem holds_app_pointwiseEqPred_iff_holds_eq
    (M : CanonicalClassModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) (t : Term Γ β) :
    Holds M.T ν (.app (pointwiseEqPred f g) t) ↔
      Holds M.T ν (.eq (.app f t) (.app g t) : Formula Γ) := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula] using
    (denoteFormula_app_pointwiseEqPred_iff_eq
      M
      (ν := ν)
      (hρ := ClassAssignment.chooseRepresentatives_realizes ν)
      f
      g
      t)

/-- Canonical-truth form of pointwise disequality at a chosen argument. -/
theorem holds_app_pointwiseNePred_iff_not_holds_eq
    (M : CanonicalClassModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) (t : Term Γ β) :
    Holds M.T ν (.app (pointwiseNePred f g) t) ↔
      ¬ Holds M.T ν (.eq (.app f t) (.app g t) : Formula Γ) := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula] using
    (denoteFormula_app_pointwiseNePred_iff_not_eq
      M
      (ν := ν)
      (hρ := ClassAssignment.chooseRepresentatives_realizes ν)
      f
      g
      t)

/-- Canonical-truth form of the arbitrary-context description instance. -/
theorem holds_description_instance
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (p : Term Γ (Pred α)) :
    Holds M.T ν
      (imp
        (.ex (.app (weaken (Base := Atom) (Const := Primitive) (σ := α) p) (.var .vz)))
        (.app p (iotaTerm p)) : Formula Γ) := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula] using
    M.denoteFormula_description_instance ν p

/-- Quotient-class truth form of the mixed pointwise disequality canary. -/
theorem holds_exists_pointwiseNe_imp_not_eq
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (.ex
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseNePred f g))
            (.var .vz)))
        (not (.eq f g)) : Formula Γ) := by
  simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula] using
    denoteFormula_exists_pointwiseNe_imp_not_eq (M := M) ν f g

/-- Direct canonical-truth version of the description witness contradiction:
if there exists a pointwise disequality witness, then the chosen `ι` point
cannot be a point of equality. -/
theorem holds_exists_pointwiseNe_imp_not_eqAtIota
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (.ex
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseNePred f g))
            (.var .vz)))
        (not
          (.eq
            (.app f (iotaTerm (pointwiseNePred f g)))
            (.app g (iotaTerm (pointwiseNePred f g)))) : Formula Γ)) := by
  let q : Term Γ (Pred β) := pointwiseNePred f g
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := .ex
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β) q)
          (.var .vz)))
      (ψ := not
        (.eq
          (.app f (iotaTerm q))
          (.app g (iotaTerm q))))).2
  intro hEx
  have hChoiceNe : Holds M.T ν (.app q (iotaTerm q) : Formula Γ) :=
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := .ex
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β) q)
          (.var .vz)))
      (ψ := .app q (iotaTerm q))
      (holds_description_instance M ν q)
      hEx
  have hNotEqAtChoice :
      ¬ Holds M.T ν
          (.eq
            (.app f (iotaTerm q))
            (.app g (iotaTerm q)) : Formula Γ) :=
    (holds_app_pointwiseNePred_iff_not_holds_eq
      M.toCanonicalClassModel
      ν
      f
      g
      (iotaTerm q)).1 hChoiceNe
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (.eq
        (.app f (iotaTerm q))
        (.app g (iotaTerm q)) : Formula Γ)).2 hNotEqAtChoice

/-- Direct non-holding form of the existential pointwise-disequality canary:
an existential witness already rules out extensional equality. -/
theorem not_holds_eq_of_exPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEx : Holds M.T ν (exPointwiseNe f g)) :
    ¬ Holds M.T ν (.eq f g : Formula Γ) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (.eq f g : Formula Γ)).1
      (holds_imp_mp
        (T := M.T)
        M.toCanonicalClassModel.completeConsistent
        (ν := ν)
        (φ := exPointwiseNe f g)
        (ψ := not (.eq f g))
        (by
          simpa [exPointwiseNe] using
            (holds_exists_pointwiseNe_imp_not_eq
          (M := M)
          (ν := ν)
          (f := f)
          (g := g)))
        hEx)

/-- Direct holding form of the existential pointwise-disequality canary:
an existential witness already forces extensional inequality. -/
theorem holds_not_eq_of_exPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEx : Holds M.T ν (exPointwiseNe f g)) :
    Holds M.T ν (not (.eq f g) : Formula Γ) := by
  exact
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := exPointwiseNe f g)
      (ψ := not (.eq f g))
      (by
        simpa [exPointwiseNe] using
          (holds_exists_pointwiseNe_imp_not_eq
            (M := M)
            (ν := ν)
            (f := f)
            (g := g)))
      hEx

/-- Direct contradiction form of the existential extensional-disequality canary:
an existential pointwise-disequality witness together with extensional equality
yields canonical falsehood. -/
theorem holds_bot_of_exPointwiseNe_and_eq
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEx : Holds M.T ν (exPointwiseNe f g))
    (hEq : Holds M.T ν (.eq f g : Formula Γ)) :
    Holds M.T ν (.bot : Formula Γ) := by
  exact False.elim
    ((not_holds_eq_of_exPointwiseNe
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      hEx) hEq)

/-- Implication-form contradiction canary: an existential pointwise-disequality
witness together with extensional equality yields canonical falsehood. -/
theorem holds_exists_pointwiseNe_imp_bot_of_eq
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (exPointwiseNe f g)
        (imp (.eq f g) .bot) : Formula Γ) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := exPointwiseNe f g)
      (ψ := imp (.eq f g) .bot)).2
  intro hEx
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := .eq f g)
      (ψ := .bot)).2
  intro hEq
  exact
    holds_bot_of_exPointwiseNe_and_eq
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      hEx
      hEq

/-- Direct non-holding form of the existential description-witness contradiction:
an existential pointwise-disequality witness already rules out equality at the
chosen `ι` point. -/
theorem not_holds_eqAtIotaPointwiseNe_of_exPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEx : Holds M.T ν (exPointwiseNe f g)) :
    ¬ Holds M.T ν (eqAtIotaPointwiseNe f g) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (eqAtIotaPointwiseNe f g)).1
      (holds_imp_mp
        (T := M.T)
        M.toCanonicalClassModel.completeConsistent
        (ν := ν)
        (φ := exPointwiseNe f g)
        (ψ := not (eqAtIotaPointwiseNe f g))
        (by
          simpa [exPointwiseNe, eqAtIotaPointwiseNe] using
            (holds_exists_pointwiseNe_imp_not_eqAtIota
          (M := M)
          (ν := ν)
          (f := f)
          (g := g)))
        hEx)

/-- Direct holding form of the existential description-witness contradiction:
an existential pointwise-disequality witness already forces non-equality at the
chosen `ι` point. -/
theorem holds_not_eqAtIotaPointwiseNe_of_exPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEx : Holds M.T ν (exPointwiseNe f g)) :
    Holds M.T ν (not (eqAtIotaPointwiseNe f g) : Formula Γ) := by
  exact
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := exPointwiseNe f g)
      (ψ := not (eqAtIotaPointwiseNe f g))
      (by
        simpa [exPointwiseNe, eqAtIotaPointwiseNe] using
          (holds_exists_pointwiseNe_imp_not_eqAtIota
            (M := M)
            (ν := ν)
            (f := f)
            (g := g)))
      hEx

/-- Direct contradiction form of the existential description-witness canary:
an existential pointwise-disequality witness together with equality at the
chosen `ι` point yields canonical falsehood. -/
theorem holds_bot_of_exPointwiseNe_and_eqAtIotaPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEx : Holds M.T ν (exPointwiseNe f g))
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T ν (.bot : Formula Γ) := by
  exact False.elim
    ((not_holds_eqAtIotaPointwiseNe_of_exPointwiseNe
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      hEx) hEqAtIota)

/-- Direct canonical-truth specialization of quoted result 28 to the pointwise
equality predicate. -/
theorem holds_eqAtIotaPointwiseNe_imp_all_pointwiseEq
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (.eq
          (.app f (iotaTerm (pointwiseNePred f g)))
          (.app g (iotaTerm (pointwiseNePred f g))))
        (allOf (pointwiseEqPred f g)) : Formula Γ) := by
  let q : Term Γ (Pred β) := pointwiseNePred f g
  have hDerived28 :
      Holds M.T ν
        (imp
          (.app (pointwiseEqPred f g) (iotaTerm q))
          (allOf (pointwiseEqPred f g)) : Formula Γ) := by
    simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula, pointwiseNePred, q] using
      denoteFormula_derived28_general
        (M := M)
        (ν := ν)
        (p := pointwiseEqPred f g)
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := .eq
        (.app f (iotaTerm q))
        (.app g (iotaTerm q)))
      (ψ := allOf (pointwiseEqPred f g))).2
  intro hEqAtChoice
  have hEqPredAtChoice :
      Holds M.T ν (.app (pointwiseEqPred f g) (iotaTerm q) : Formula Γ) :=
    (holds_app_pointwiseEqPred_iff_holds_eq
      M.toCanonicalClassModel
      ν
      f
      g
      (iotaTerm q)).2 hEqAtChoice
  exact
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := .app (pointwiseEqPred f g) (iotaTerm q))
      (ψ := allOf (pointwiseEqPred f g))
      hDerived28
      hEqPredAtChoice

/-- Direct holding form of the quoted-result-28 specialization: equality at the
chosen `ι` point forces universal pointwise equality. -/
theorem holds_allPointwiseEq_of_eqAtIotaPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T ν (allOf (pointwiseEqPred f g)) := by
  exact
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := eqAtIotaPointwiseNe f g)
      (ψ := allOf (pointwiseEqPred f g))
      (holds_eqAtIotaPointwiseNe_imp_all_pointwiseEq
        (M := M)
        (ν := ν)
        (f := f)
        (g := g))
      hEqAtIota

/-- Direct canonical-truth transport of Henkin's axiom 10 to arbitrary open
function terms. -/
theorem holds_extensionality_instance
    (M : CanonicalClassModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (.all
          (.eq
            (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
            (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))))
        (.eq f g) : Formula Γ) := by
  let σfg : Subst Primitive [β ⇒ α, β ⇒ α] Γ :=
    fun {_τ} v =>
      match v with
      | .vz => f
      | .vs .vz => g
  have hSubst :
      TheoremInContext
        (subst σfg (axiom10 (σ := β) (τ := α))) :=
    derivation_subst
      (Γ := [β ⇒ α, β ⇒ α])
      (Δ := Γ)
      (Θ := [])
      (φ := axiom10 (σ := β) (τ := α))
      σfg
      axiom10_theorem
  have hInst :
      TheoremInContext
        (imp
          (.all
            (.eq
              (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
              (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))))
          (.eq f g) : Formula Γ) := by
    simpa [σfg, axiom10, weaken, subst, eq, imp, Subst.lift] using hSubst
  exact
    holds_of_theoremInContext
      (T := M.T)
      M.completeConsistent
      ν
      hInst

/-- Pointwise equality over all arguments implies extensional equality for
arbitrary open function terms, entirely inside canonical truth. -/
theorem holds_allPointwiseEq_imp_eq
    (M : CanonicalClassModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (allOf (pointwiseEqPred f g))
        (.eq f g) : Formula Γ) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.completeConsistent
      (ν := ν)
      (φ := allOf (pointwiseEqPred f g))
      (ψ := .eq f g)).2
  intro hAllPointwise
  have hAllEq :
      Holds M.T ν
        (.all
          (.eq
            (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
            (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz)))
          : Formula Γ) := by
    apply
      (holds_all_iff_forall_class_extensions
        (T := M.T)
        M.completeConsistent
        M.existsWitness
        M.allCounterexample
        ν
        (.eq
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz)))).2
    intro c
    have hAtC :
        Holds M.T
          (ClassAssignment.extend ν c)
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseEqPred f g))
            (.var .vz) : Formula (β :: Γ)) :=
      (holds_all_iff_forall_class_extensions
        (T := M.T)
        M.completeConsistent
        M.existsWitness
        M.allCounterexample
        ν
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseEqPred f g))
          (.var .vz))).1 hAllPointwise c
    have hAtC' :
        Holds M.T
          (ClassAssignment.extend ν c)
          (.app
            (pointwiseEqPred
              (weaken (Base := Atom) (Const := Primitive) (σ := β) f)
              (weaken (Base := Atom) (Const := Primitive) (σ := β) g))
            (.var .vz) : Formula (β :: Γ)) := by
      simpa [weaken_pointwiseEqPred] using hAtC
    exact
      (holds_app_pointwiseEqPred_iff_holds_eq
        M
        (ν := ClassAssignment.extend ν c)
        (f := weaken (Base := Atom) (Const := Primitive) (σ := β) f)
        (g := weaken (Base := Atom) (Const := Primitive) (σ := β) g)
        (t := (.var .vz : Term (β :: Γ) β))).1 hAtC'
  exact
    holds_imp_mp
      (T := M.T)
      M.completeConsistent
      (ν := ν)
      (φ := .all
        (.eq
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))))
      (ψ := .eq f g)
      (holds_extensionality_instance M ν f g)
      hAllEq

/-- Arbitrary-context direct canonical-truth form of quoted result 22: equality
at the `ι`-chosen point of the pointwise-disequality predicate forces
extensional equality. -/
theorem holds_eqAtIotaPointwiseNe_imp_eq
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (eqAtIotaPointwiseNe f g)
        (.eq f g) : Formula Γ) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := eqAtIotaPointwiseNe f g)
      (ψ := .eq f g)).2
  intro hEqAtIota
  have hAllPointwise :
      Holds M.T ν (allOf (pointwiseEqPred f g)) :=
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := eqAtIotaPointwiseNe f g)
      (ψ := allOf (pointwiseEqPred f g))
      (holds_eqAtIotaPointwiseNe_imp_all_pointwiseEq
        (M := M)
        (ν := ν)
        (f := f)
        (g := g))
      hEqAtIota
  exact
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := allOf (pointwiseEqPred f g))
      (ψ := .eq f g)
      (holds_allPointwiseEq_imp_eq
        (M := M.toCanonicalClassModel)
        (ν := ν)
        (f := f)
        (g := g))
      hAllPointwise

/-- Direct holding form of quoted result 22: equality at the chosen `ι` point
forces extensional equality. -/
theorem holds_eq_of_eqAtIotaPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T ν (.eq f g : Formula Γ) := by
  exact
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := eqAtIotaPointwiseNe f g)
      (ψ := .eq f g)
      (holds_eqAtIotaPointwiseNe_imp_eq
        (M := M)
        (ν := ν)
        (f := f)
        (g := g))
      hEqAtIota

/-- Class-wise positive consequence of equality at the chosen `ι` point:
every quotient-class argument becomes a point of pointwise equality. -/
theorem holds_pointwiseEq_of_eqAtIotaPointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseEqPred f g))
        (.var .vz) : Formula (β :: Γ)) := by
  have hAllPointwise :
      Holds M.T ν (allOf (pointwiseEqPred f g)) :=
    holds_allPointwiseEq_of_eqAtIotaPointwiseNe
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      hEqAtIota
  simpa [allOf] using
    (holds_all_iff_forall_class_extensions
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      M.toCanonicalClassModel.existsWitness
      M.toCanonicalClassModel.allCounterexample
      ν
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseEqPred f g))
        (.var .vz))).1 hAllPointwise c

/-- At a fixed quotient-class argument, equality at the chosen `ι` point forces
equality of the two weakened applications at that argument. -/
theorem holds_eqAtClass_of_eqAtIotaPointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ)) := by
  have hEqAtC :
      Holds M.T
        (ClassAssignment.extend ν c)
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseEqPred f g))
          (.var .vz) : Formula (β :: Γ)) :=
    holds_pointwiseEq_of_eqAtIotaPointwiseNe_class
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hEqAtIota
  have hEqAtC' :
      Holds M.T
        (ClassAssignment.extend ν c)
        (.app
          (pointwiseEqPred
            (weaken (Base := Atom) (Const := Primitive) (σ := β) f)
            (weaken (Base := Atom) (Const := Primitive) (σ := β) g))
          (.var .vz) : Formula (β :: Γ)) := by
    simpa [weaken_pointwiseEqPred] using hEqAtC
  exact
    (holds_app_pointwiseEqPred_iff_holds_eq
      M.toCanonicalClassModel
      (ν := ClassAssignment.extend ν c)
      (f := weaken (Base := Atom) (Const := Primitive) (σ := β) f)
      (g := weaken (Base := Atom) (Const := Primitive) (σ := β) g)
      (t := (.var .vz : Term (β :: Γ) β))).1 hEqAtC'

/-- Direct predicate-level consequence of equality at a fixed quotient-class
argument: equality of the weakened applications yields pointwise equality at
that same class point. -/
theorem holds_pointwiseEq_of_eqAtClass
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtC : Holds M.T
      (ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ))) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseEqPred f g))
        (.var .vz) : Formula (β :: Γ)) := by
  have hEqAtC' :
      Holds M.T
        (ClassAssignment.extend ν c)
        (.app
          (pointwiseEqPred
            (weaken (Base := Atom) (Const := Primitive) (σ := β) f)
            (weaken (Base := Atom) (Const := Primitive) (σ := β) g))
          (.var .vz) : Formula (β :: Γ)) :=
    (holds_app_pointwiseEqPred_iff_holds_eq
      M.toCanonicalClassModel
      (ν := ClassAssignment.extend ν c)
      (f := weaken (Base := Atom) (Const := Primitive) (σ := β) f)
      (g := weaken (Base := Atom) (Const := Primitive) (σ := β) g)
      (t := (.var .vz : Term (β :: Γ) β))).2 hEqAtC
  simpa [weaken_pointwiseEqPred] using hEqAtC'

/-- A concrete pointwise-disequality witness directly yields negated equality of
the weakened applications at that same class point. -/
theorem holds_not_eqAtClass_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (not
        (.eq
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
          : Formula (β :: Γ)) : Formula (β :: Γ)) := by
  apply
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ))).2
  have hNeAtC' :
      Holds M.T
        (ClassAssignment.extend ν c)
        (.app
          (pointwiseNePred
            (weaken (Base := Atom) (Const := Primitive) (σ := β) f)
            (weaken (Base := Atom) (Const := Primitive) (σ := β) g))
          (.var .vz) : Formula (β :: Γ)) := by
    simpa [weaken_pointwiseNePred] using hc
  exact
    (holds_app_pointwiseNePred_iff_not_holds_eq
      M.toCanonicalClassModel
      (ν := ClassAssignment.extend ν c)
      (f := weaken (Base := Atom) (Const := Primitive) (σ := β) f)
      (g := weaken (Base := Atom) (Const := Primitive) (σ := β) g)
      (t := (.var .vz : Term (β :: Γ) β))).1 hNeAtC'

/-- Direct non-holding form of class-wise extensional disequality: a concrete
pointwise-disequality witness already rules out equality of the weakened
applications at that same class point. -/
theorem not_holds_eqAtClass_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    ¬ Holds M.T
        (ClassAssignment.extend ν c)
        (.eq
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
          : Formula (β :: Γ)) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ))).1
      (holds_not_eqAtClass_of_pointwiseNe_class
        (M := M)
        (ν := ν)
        (f := f)
        (g := g)
        (c := c)
        hc)

/-- Direct contradiction form at a fixed quotient-class argument: a concrete
pointwise-disequality witness together with equality of the weakened
applications at that class point yields canonical falsehood in the extended
context. -/
theorem holds_bot_of_pointwiseNe_class_and_eqAtClass
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ)))
    (hEqAtC : Holds M.T
      (ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ))) :
    Holds M.T (ClassAssignment.extend ν c) (.bot : Formula (β :: Γ)) := by
  exact False.elim
    ((not_holds_eqAtClass_of_pointwiseNe_class
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hc) hEqAtC)

/-- Fixed-class implication form of the local contradiction rule: equality of
the weakened applications forces any pointwise-disequality claim at that class
point to collapse to canonical falsehood. -/
theorem holds_pointwiseNe_imp_bot_of_eqAtClass
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtC : Holds M.T
      (ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ))) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (imp
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseNePred f g))
          (.var .vz))
        .bot : Formula (β :: Γ)) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (φ := .app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz))
      (ψ := .bot)).2
  intro hNeAtC
  exact
    holds_bot_of_pointwiseNe_class_and_eqAtClass
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hNeAtC
      hEqAtC

/-- Fixed-class implication form of extensional disequality: a concrete
pointwise-disequality witness already turns equality of the weakened
applications at that class point into canonical falsehood. -/
theorem holds_eqAtClass_imp_bot_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (imp
        (.eq
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz)))
        .bot : Formula (β :: Γ)) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (φ := .eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz)))
      (ψ := .bot)).2
  intro hEqAtC
  exact
    holds_bot_of_pointwiseNe_class_and_eqAtClass
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hc
      hEqAtC

/-- Predicate-level direct holding form of class-wise extensional disequality:
a concrete pointwise-disequality witness already forces the negation of
pointwise equality at that same class point. -/
theorem holds_not_pointwiseEq_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (not
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseEqPred f g))
          (.var .vz) : Formula (β :: Γ)) : Formula (β :: Γ)) := by
  apply
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseEqPred f g))
        (.var .vz) : Formula (β :: Γ))).2
  intro hPointwiseEqAtC
  have hEqAtC :
      Holds M.T
        (ClassAssignment.extend ν c)
        (.eq
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
          (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
          : Formula (β :: Γ)) := by
    have hPointwiseEqAtC' :
        Holds M.T
          (ClassAssignment.extend ν c)
          (.app
            (pointwiseEqPred
              (weaken (Base := Atom) (Const := Primitive) (σ := β) f)
              (weaken (Base := Atom) (Const := Primitive) (σ := β) g))
            (.var .vz) : Formula (β :: Γ)) := by
      simpa using
        hPointwiseEqAtC
    simpa [CanonicalClassModel.denoteFormula, CanonicalFrame.denoteFormula] using
      (denoteFormula_app_pointwiseEqPred_iff_eq
        (M := M.toCanonicalClassModel)
        (ν := ClassAssignment.extend ν c)
        (hρ := ClassAssignment.chooseRepresentatives_realizes
          (ClassAssignment.extend ν c))
        (f := weaken (Base := Atom) (Const := Primitive) (σ := β) f)
        (g := weaken (Base := Atom) (Const := Primitive) (σ := β) g)
        (t := (.var .vz : Term (β :: Γ) β))).1
        hPointwiseEqAtC'
  have hBot :
      Holds M.T (ClassAssignment.extend ν c) (.bot : Formula (β :: Γ)) :=
    holds_bot_of_pointwiseNe_class_and_eqAtClass
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hc
      hEqAtC
  exact
    (not_holds_bot
      (T := M.T)
      (ν := ClassAssignment.extend ν c)
      M.toCanonicalClassModel.completeConsistent) hBot

/-- Predicate-level direct non-holding form of class-wise extensional
disequality: a concrete pointwise-disequality witness already rules out
pointwise equality at that same class point. -/
theorem not_holds_pointwiseEq_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    ¬ Holds M.T
        (ClassAssignment.extend ν c)
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseEqPred f g))
          (.var .vz) : Formula (β :: Γ)) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseEqPred f g))
        (.var .vz) : Formula (β :: Γ))).1
      (holds_not_pointwiseEq_of_pointwiseNe_class
        (M := M)
        (ν := ν)
        (f := f)
        (g := g)
      (c := c)
      hc)

/-- Predicate-level implication form of class-wise extensional disequality: a
concrete pointwise-disequality witness turns any pointwise-equality claim at
that same class point into canonical falsehood. -/
theorem holds_pointwiseEq_imp_bot_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (imp
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseEqPred f g))
          (.var .vz))
        .bot : Formula (β :: Γ)) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (φ := .app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseEqPred f g))
        (.var .vz))
      (ψ := .bot)).2
  intro hEqAtC
  exact False.elim
    ((not_holds_pointwiseEq_of_pointwiseNe_class
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hc) hEqAtC)

/-- Direct holding form at a fixed quotient-class argument: equality of the
weakened applications rules out pointwise disequality at that same class
point. -/
theorem holds_not_pointwiseNe_of_eqAtClass
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtC : Holds M.T
      (ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ))) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (not
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseNePred f g))
          (.var .vz) : Formula (β :: Γ)) : Formula (β :: Γ)) := by
  apply
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))).2
  intro hNeAtC
  have hBot :
      Holds M.T (ClassAssignment.extend ν c) (.bot : Formula (β :: Γ)) :=
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (φ := .app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz))
      (ψ := .bot)
      (holds_pointwiseNe_imp_bot_of_eqAtClass
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hEqAtC)
      hNeAtC
  exact
    (not_holds_bot
      (T := M.T)
      (ν := ClassAssignment.extend ν c)
      M.toCanonicalClassModel.completeConsistent) hBot

/-- Fixed-class implication form transported from the chosen-`ι` equality rule:
equality at the `ι`-chosen point forces any pointwise-disequality claim at a
concrete class point to collapse to canonical falsehood. -/
theorem holds_pointwiseNe_imp_bot_of_eqAtIotaPointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (imp
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseNePred f g))
          (.var .vz))
        .bot : Formula (β :: Γ)) := by
  exact
    holds_pointwiseNe_imp_bot_of_eqAtClass
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      (holds_eqAtClass_of_eqAtIotaPointwiseNe_class
        (M := M)
        (ν := ν)
        (f := f)
        (g := g)
        (c := c)
        hEqAtIota)

/-- Direct non-holding form at a fixed quotient-class argument: equality of the
weakened applications rules out pointwise disequality at that same class
point. -/
theorem not_holds_pointwiseNe_of_eqAtClass
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtC : Holds M.T
      (ClassAssignment.extend ν c)
      (.eq
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) f) (.var .vz))
        (.app (weaken (Base := Atom) (Const := Primitive) (σ := β) g) (.var .vz))
        : Formula (β :: Γ))) :
    ¬ Holds M.T
        (ClassAssignment.extend ν c)
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseNePred f g))
          (.var .vz) : Formula (β :: Γ)) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))).1
      (holds_not_pointwiseNe_of_eqAtClass
        (M := M)
        (ν := ν)
        (f := f)
        (g := g)
        (c := c)
        hEqAtC)

/-- At a fixed quotient-class argument, equality at the chosen `ι` point rules
out pointwise disequality at that same argument. -/
theorem holds_not_pointwiseNe_of_eqAtIotaPointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T
      (ClassAssignment.extend ν c)
      (not
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseNePred f g))
          (.var .vz) : Formula (β :: Γ)) : Formula (β :: Γ)) := by
  apply
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))).2
  intro hNeAtC
  have hBot :
      Holds M.T (ClassAssignment.extend ν c) (.bot : Formula (β :: Γ)) :=
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (φ := .app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz))
      (ψ := .bot)
      (holds_pointwiseNe_imp_bot_of_eqAtIotaPointwiseNe_class
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hEqAtIota)
      hNeAtC
  exact
    (not_holds_bot
      (T := M.T)
      (ν := ClassAssignment.extend ν c)
      M.toCanonicalClassModel.completeConsistent) hBot

/-- Class-wise negative consequence of equality at the chosen `ι` point:
no quotient-class argument can remain a point of pointwise disequality. -/
theorem not_holds_pointwiseNe_of_eqAtIotaPointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    ¬ Holds M.T
        (ClassAssignment.extend ν c)
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseNePred f g))
          (.var .vz) : Formula (β :: Γ)) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))).1
      (holds_not_pointwiseNe_of_eqAtIotaPointwiseNe_class
        (M := M)
        (ν := ν)
        (f := f)
        (g := g)
        (c := c)
        hEqAtIota)

/-- Arbitrary-context mixed contradiction canary: existential pointwise
disequality together with equality at the `ι`-chosen point yields canonical
falsehood. -/
theorem holds_exists_pointwiseNe_imp_bot_of_eqAtIota
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (exPointwiseNe f g)
        (imp (eqAtIotaPointwiseNe f g) .bot) : Formula Γ) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := exPointwiseNe f g)
      (ψ := imp (eqAtIotaPointwiseNe f g) .bot)).2
  intro hEx
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := eqAtIotaPointwiseNe f g)
      (ψ := .bot)).2
  intro hEqAtIota
  exact
    holds_bot_of_exPointwiseNe_and_eqAtIotaPointwiseNe
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      hEx
      hEqAtIota

/-- Arbitrary-context canonical-truth consequence: equality at the `ι`-chosen
point rules out the existence of a pointwise disequality witness. -/
theorem holds_eqAtIotaPointwiseNe_imp_not_exPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α)) :
    Holds M.T ν
      (imp
        (eqAtIotaPointwiseNe f g)
        (not (exPointwiseNe f g)) : Formula Γ) := by
  apply
    (holds_imp_iff
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := eqAtIotaPointwiseNe f g)
      (ψ := not (exPointwiseNe f g))).2
  intro hEqAtIota
  apply
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (exPointwiseNe f g)).2
  intro hEx
  rcases
      (holds_ex_iff_exists_class_witness
        (T := M.T)
        M.toCanonicalClassModel.completeConsistent
        M.toCanonicalClassModel.existsWitness
        M.toCanonicalClassModel.allCounterexample
        ν
        (.app
          (weaken (Base := Atom) (Const := Primitive) (σ := β)
            (pointwiseNePred f g))
          (.var .vz))).1
        (by simpa [exPointwiseNe] using hEx) with ⟨c, hc⟩
  exact
    not_holds_pointwiseNe_of_eqAtIotaPointwiseNe_class
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hEqAtIota
      hc

/-- Direct holding form of the witness-elimination rule: equality at the chosen
`ι` point rules out existential pointwise disequality. -/
theorem holds_not_exPointwiseNe_of_eqAtIotaPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T ν (not (exPointwiseNe f g) : Formula Γ) := by
  exact
    holds_imp_mp
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (φ := eqAtIotaPointwiseNe f g)
      (ψ := not (exPointwiseNe f g))
      (holds_eqAtIotaPointwiseNe_imp_not_exPointwiseNe
        (M := M)
        (ν := ν)
        (f := f)
        (g := g))
      hEqAtIota

/-- Direct non-holding form of the arbitrary-context witness-elimination rule:
equality at the `ι`-chosen point rules out existential pointwise disequality. -/
theorem not_holds_exPointwiseNe_of_eqAtIotaPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    ¬ Holds M.T ν (exPointwiseNe f g) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (exPointwiseNe f g)).1
      (holds_imp_mp
        (T := M.T)
        M.toCanonicalClassModel.completeConsistent
        (ν := ν)
        (φ := eqAtIotaPointwiseNe f g)
        (ψ := not (exPointwiseNe f g))
        (holds_eqAtIotaPointwiseNe_imp_not_exPointwiseNe
          (M := M)
          (ν := ν)
          (f := f)
          (g := g))
        hEqAtIota)

/-- Arbitrary-context quotient-class witness rule: a class witness of
pointwise disequality rules out equality at the `ι`-chosen point. -/
theorem holds_not_eqAtIota_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    Holds M.T ν (not (eqAtIotaPointwiseNe f g) : Formula Γ) := by
  have hEx :
      Holds M.T ν (exPointwiseNe f g) :=
    holds_ex_of_class_witness
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      ν
      c
      hc
  exact
    holds_not_eqAtIotaPointwiseNe_of_exPointwiseNe
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      hEx

/-- Direct non-holding form of the quotient-class witness rule ruling out
equality at the chosen `ι` point. -/
theorem not_holds_eqAtIotaPointwiseNe_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    ¬ Holds M.T ν (eqAtIotaPointwiseNe f g) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (eqAtIotaPointwiseNe f g)).1
      (holds_not_eqAtIota_of_pointwiseNe_class
        (M := M)
        (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hc)

/-- Direct contradiction form of the class-witness description canary: a single
class witness of pointwise disequality together with equality at the chosen
`ι` point yields canonical falsehood. -/
theorem holds_bot_of_pointwiseNe_class_and_eqAtIotaPointwiseNe
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ)))
    (hEqAtIota : Holds M.T ν (eqAtIotaPointwiseNe f g)) :
    Holds M.T ν (.bot : Formula Γ) := by
  exact False.elim
    ((not_holds_eqAtIotaPointwiseNe_of_pointwiseNe_class
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hc) hEqAtIota)

/-- Direct canonical-truth derivation of quoted result 22 from the rebased
quoted result 28 plus axiom 10. This keeps the whole argument at Henkin's
quotient-class truth layer. -/
theorem holds_derived22_via_derived28
    {α β : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [β ⇒ α, β ⇒ α]) :
    Holds M.T ν (derived22 (α := α) (β := β)) := by
  simpa [derived22, eqAtIotaPointwiseNe, eq] using
    (holds_eqAtIotaPointwiseNe_imp_eq
      (M := M)
      (ν := ν)
      (f := firstFun (α := α) (β := β))
      (g := secondFun (α := α) (β := β)))

/-- Mixed direct canonical-truth contradiction canary: combining the rebased
quoted-result-22 path with the existential pointwise-disequality path yields a
direct inconsistency from an existential disequality witness together with
equality at the `ι`-chosen point. -/
theorem holds_exists_pointwiseNe_imp_bot_of_eqAtIota_via_derived22
    {α β : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [β ⇒ α, β ⇒ α]) :
    Holds M.T ν
      (imp
        (exPointwiseNe
          (firstFun (α := α) (β := β))
          (secondFun (α := α) (β := β)))
        (imp
          (eqAtIotaPointwiseNe
            (firstFun (α := α) (β := β))
            (secondFun (α := α) (β := β)))
          .bot)) := by
  simpa using
    (holds_exists_pointwiseNe_imp_bot_of_eqAtIota
      (M := M)
      (ν := ν)
      (f := firstFun (α := α) (β := β))
      (g := secondFun (α := α) (β := β)))

/-- Direct quotient-class witness form of the mixed pointwise disequality
canary. A single quotient-class witness of pointwise disequality already forces
`¬(f = g)` in canonical truth. -/
theorem holds_not_eq_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    Holds M.T ν (not (.eq f g) : Formula Γ) := by
  have hEx :
      Holds M.T ν
        (.ex
          (.app
            (weaken (Base := Atom) (Const := Primitive) (σ := β)
              (pointwiseNePred f g))
            (.var .vz)) : Formula Γ) :=
    holds_ex_of_class_witness
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      ν
      c
      hc
  exact
    holds_not_eq_of_exPointwiseNe
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (by simpa [exPointwiseNe] using hEx)

/-- Direct contradiction form of the class-witness extensional-disequality
canary: a single class witness of pointwise disequality together with
extensional equality yields canonical falsehood. -/
theorem holds_bot_of_pointwiseNe_class_and_eq
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ)))
    (hEq : Holds M.T ν (.eq f g : Formula Γ)) :
    Holds M.T ν (.bot : Formula Γ) := by
  have hNotEq :
      Holds M.T ν (not (.eq f g) : Formula Γ) :=
    holds_not_eq_of_pointwiseNe_class
      (M := M)
      (ν := ν)
      (f := f)
      (g := g)
      (c := c)
      hc
  have hEqFalse :
      ¬ Holds M.T ν (.eq f g : Formula Γ) :=
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (.eq f g : Formula Γ)).1 hNotEq
  exact False.elim (hEqFalse hEq)

/-- Direct non-holding form of the quotient-class witness rule forcing
extensional inequality. -/
theorem not_holds_eq_of_pointwiseNe_class
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    {Γ : Ctx Atom} {α β : HTy}
    (ν : M.toCanonicalClassModel.Assignment Γ)
    (f g : Term Γ (β ⇒ α))
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred f g))
        (.var .vz) : Formula (β :: Γ))) :
    ¬ Holds M.T ν (.eq f g : Formula Γ) := by
  exact
    (holds_not_iff_not_holds
      (T := M.T)
      M.toCanonicalClassModel.completeConsistent
      (ν := ν)
      (.eq f g : Formula Γ)).1
      (holds_not_eq_of_pointwiseNe_class
        (M := M)
        (ν := ν)
        (f := f)
        (g := g)
        (c := c)
        hc)

/-- Quotient-class witness form of the mixed contradiction canary: a concrete
class witness of pointwise disequality rules out equality at the `ι`-chosen
point through the result-22 path. -/
theorem holds_not_eqAtIota_of_pointwiseNe_class_via_derived22
    {α β : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [β ⇒ α, β ⇒ α])
    (c : M.toCanonicalClassModel.Carrier β)
    (hc : Holds M.T
      (ClassAssignment.extend ν c)
      (.app
        (weaken (Base := Atom) (Const := Primitive) (σ := β)
          (pointwiseNePred
            (firstFun (α := α) (β := β))
            (secondFun (α := α) (β := β))))
        (.var .vz) : Formula (β :: [β ⇒ α, β ⇒ α]))) :
    Holds M.T ν
      (not (eqAtIotaPointwiseNe
        (firstFun (α := α) (β := β))
        (secondFun (α := α) (β := β)))) := by
  simpa using
    (holds_not_eqAtIota_of_pointwiseNe_class
      (M := M)
      (ν := ν)
      (f := firstFun (α := α) (β := β))
      (g := secondFun (α := α) (β := β))
      (c := c)
      hc)

/-- Quoted result 13 is valid in all paper-general models:
`(A ⊃ B) ⊃ ((¬A ⊃ B) ⊃ B)`. -/
theorem derived13_validInGeneral (A B : Sentence) :
    ValidInGeneral (imp (imp A B) (imp (imp (not A) B) B)) := by
  intro M
  classical
  change M.toHenkinModel.models (.imp (.imp A B) (.imp (.imp (.not A) B) B))
  rw [HenkinModel.models_imp]
  intro hAB
  rw [HenkinModel.models_imp]
  intro hNotAB
  by_cases hA : HenkinModel.models M.toHenkinModel A
  · exact hAB hA
  · exact hNotAB (by simpa [not, HenkinModel.models, PreModel.models] using hA)

/-- Quoted result 14 is valid in all paper-general models: `A = A`. -/
theorem derived14_validInGeneral {α : HTy} (t : ClosedTerm α) :
    ValidInGeneral (eq t t) := by
  intro M
  change HenkinModel.Eqv M.toHenkinModel α
    (HenkinModel.denote M.toHenkinModel t emptyValuation)
    (HenkinModel.denote M.toHenkinModel t emptyValuation)
  exact
    HenkinModel.eqv_refl M.toHenkinModel
      (HenkinModel.denote_admissible M.toHenkinModel
        (by
          intro τ v
          nomatch v)
        t)

/-- Quoted result 15 is valid in all paper-general models:
`A = B ⊃ B = A`. -/
theorem derived15_validInGeneral {α : HTy} (t u : ClosedTerm α) :
    ValidInGeneral (imp (eq t u) (eq u t)) := by
  intro M
  change M.toHenkinModel.models (.imp (.eq t u) (.eq u t))
  rw [HenkinModel.models_imp]
  intro hEq
  exact HenkinModel.eqv_symm M.toHenkinModel hEq

/-- Quoted result 16 is valid in all paper-general models:
`A = B ⊃ (B = C ⊃ A = C)`. -/
theorem derived16_validInGeneral {α : HTy} (t u v : ClosedTerm α) :
    ValidInGeneral (imp (eq t u) (imp (eq u v) (eq t v))) := by
  intro M
  change M.toHenkinModel.models (.imp (.eq t u) (.imp (.eq u v) (.eq t v)))
  rw [HenkinModel.models_imp]
  intro htu
  rw [HenkinModel.models_imp]
  intro huv
  exact HenkinModel.eqv_trans M.toHenkinModel htu huv

/-- Quoted result 17 is valid in all paper-general models:
`A ⊃ ((A = B) ⊃ B)`. -/
theorem derived17_validInGeneral (A B : Sentence) :
    ValidInGeneral (imp A (imp (eq A B) B)) := by
  intro M
  change M.toHenkinModel.models (.imp A (.imp (.eq A B) B))
  rw [HenkinModel.models_imp]
  intro hA
  rw [HenkinModel.models_imp]
  intro hEq
  have hAB : M.toHenkinModel.models A ↔ M.toHenkinModel.models B := hEq
  exact hAB.mp hA

/-- Quoted result 18 is valid in all paper-general models:
`¬A ⊃ ((A = B) ⊃ ¬B)`. -/
theorem derived18_validInGeneral (A B : Sentence) :
    ValidInGeneral (imp (not A) (imp (eq A B) (not B))) := by
  intro M
  change M.toHenkinModel.models (.imp (.not A) (.imp (.eq A B) (.not B)))
  rw [HenkinModel.models_imp]
  intro hNotA
  rw [HenkinModel.models_imp]
  intro hEq
  have hAB : M.toHenkinModel.models A ↔ M.toHenkinModel.models B := hEq
  have hNotA' : ¬ M.toHenkinModel.models A := by
    simpa [not] using hNotA
  simpa [not] using fun hB => hNotA' (hAB.mpr hB)

/-- Quoted result 19 is valid in all paper-general models:
`A ⊃ (B ⊃ A = B)`. -/
theorem derived19_validInGeneral (A B : Sentence) :
    ValidInGeneral (imp A (imp B (eq A B))) := by
  intro M
  change M.toHenkinModel.models (.imp A (.imp B (.eq A B)))
  rw [HenkinModel.models_imp]
  intro hA
  rw [HenkinModel.models_imp]
  intro hB
  change M.toHenkinModel.models A ↔ M.toHenkinModel.models B
  exact ⟨fun _ => hB, fun _ => hA⟩

/-- Quoted result 20 is valid in all paper-general models:
`¬A ⊃ (¬B ⊃ A = B)`. -/
theorem derived20_validInGeneral (A B : Sentence) :
    ValidInGeneral (imp (not A) (imp (not B) (eq A B))) := by
  intro M
  change M.toHenkinModel.models (.imp (.not A) (.imp (.not B) (.eq A B)))
  rw [HenkinModel.models_imp]
  intro hNotA
  rw [HenkinModel.models_imp]
  intro hNotB
  have hNotA' : ¬ M.toHenkinModel.models A := by
    simpa [not] using hNotA
  have hNotB' : ¬ M.toHenkinModel.models B := by
    simpa [not] using hNotB
  change M.toHenkinModel.models A ↔ M.toHenkinModel.models B
  exact ⟨fun hA => False.elim (hNotA' hA), fun hB => False.elim (hNotB' hB)⟩

/-- Quoted result 21 holds in a single paper-general model once the model class is
strengthened by the explicit higher-order argument-congruence principle
`EqAppArgSound`. -/
theorem derived21_models_of_eqAppArgSound
    {α β : HTy}
    (M : GeneralModel)
    (f g : ClosedTerm (α ⇒ β)) (t u : ClosedTerm α)
    (hSound : EqAppArgSound M) :
    HenkinModel.models M.toHenkinModel
      (imp (eq f g) (imp (eq t u) (eq (.app f t) (.app g u)))) := by
  let HM := M.toHenkinModel
  let fv : Ty.denote HM.Carrier (α ⇒ β) := HenkinModel.denote HM f emptyValuation
  let gv : Ty.denote HM.Carrier (α ⇒ β) := HenkinModel.denote HM g emptyValuation
  let tv : Ty.denote HM.Carrier α := HenkinModel.denote HM t emptyValuation
  let uv : Ty.denote HM.Carrier α := HenkinModel.denote HM u emptyValuation
  have hf : HM.adm (α ⇒ β) fv := by
    dsimp [fv]
    exact HenkinModel.denote_admissible HM (by intro τ v; nomatch v) f
  have hg : HM.adm (α ⇒ β) gv := by
    dsimp [gv]
    exact HenkinModel.denote_admissible HM (by intro τ v; nomatch v) g
  have ht : HM.adm α tv := by
    dsimp [tv]
    exact HenkinModel.denote_admissible HM (by intro τ v; nomatch v) t
  have hu : HM.adm α uv := by
    dsimp [uv]
    exact HenkinModel.denote_admissible HM (by intro τ v; nomatch v) u
  change HM.models (.imp (.eq f g) (.imp (.eq t u) (.eq (.app f t) (.app g u))))
  rw [HenkinModel.models_imp]
  intro hfg
  rw [HenkinModel.models_imp]
  intro htu
  have hft_gt : HenkinModel.Eqv HM β (fv tv) (gv tv) :=
    HenkinModel.eqv_arr_apply HM (by exact hfg) ht
  have hgt_gu : HenkinModel.Eqv HM β (gv tv) (gv uv) :=
    hSound gv hg ht hu (by exact htu)
  exact HenkinModel.eqv_trans HM hft_gt hgt_gu

/-- Quoted result 21 becomes paper-general valid once the model class is
strengthened by the explicit higher-order argument-congruence principle
`EqAppArgSound`. This isolates the exact semantic seam still blocking an
unconditional extensional soundness theorem for the current `GeneralModel`
interface. -/
theorem derived21_validInGeneral_of_eqAppArgSound
    {α β : HTy}
    (f g : ClosedTerm (α ⇒ β)) (t u : ClosedTerm α)
    (hSound : ∀ M : GeneralModel, EqAppArgSound M) :
    ValidInGeneral (imp (eq f g) (imp (eq t u) (eq (.app f t) (.app g u)))) := by
  intro M
  exact derived21_models_of_eqAppArgSound M f g t u (hSound M)

/-- Quoted result 21 is unconditionally valid in all paper-standard models,
because standard models satisfy `EqAppArgSound`. -/
theorem derived21_validInStandard
    {α β : HTy}
    (f g : ClosedTerm (α ⇒ β)) (t u : ClosedTerm α) :
    ValidInStandard (imp (eq f g) (imp (eq t u) (eq (.app f t) (.app g u)))) := by
  intro M
  exact
    derived21_models_of_eqAppArgSound
      (StandardModel.toGeneralModel M) f g t u
      (eqAppArgSound_of_standardModel M)

/-- Quoted result 22 is valid in all paper-general models. -/
theorem derived22_validInGeneral {α β : HTy} :
    ValidInGeneralCtx (derived22 (α := α) (β := β)) := by
  intro M ρ hρ
  classical
  let HM := M.toHenkinModel
  let f : Ty.denote HM.Carrier (β ⇒ α) := ρ (.vs .vz)
  let g : Ty.denote HM.Carrier (β ⇒ α) := ρ .vz
  let q : Ty.denote HM.Carrier (Pred β) :=
    HenkinModel.denote HM
      (pointwiseNePred
        (firstFun (α := α) (β := β))
        (secondFun (α := α) (β := β)))
      ρ
  have hq : HM.adm (Pred β) q := by
    dsimp [q]
    exact HenkinModel.denote_admissible HM hρ
      (pointwiseNePred
        (firstFun (α := α) (β := β))
        (secondFun (α := α) (β := β)))
  change
    (HenkinModel.Eqv HM α (f (HM.constDen (.iota β) q)) (g (HM.constDen (.iota β) q)) →
      HenkinModel.Eqv HM (β ⇒ α) f g)
  intro hChosen x hx
  by_cases hfgx : HenkinModel.Eqv HM α (f x) (g x)
  · exact hfgx
  · have hqWitness : ∃ y : Ty.denote HM.Carrier β, HM.adm β y ∧ (q y).down := by
      refine ⟨x, hx, ?_⟩
      dsimp [q, f, g]
      simpa [pointwiseNePred, pointwiseEqPred, complementPred, firstFun, secondFun,
          HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend,
          q, f, g]
        using hfgx
    have hqChoice : (q (HM.constDen (.iota β) q)).down :=
      M.iota_sound β q hq hqWitness
    have hChosenFalse :
        ¬ HenkinModel.Eqv HM α (f (HM.constDen (.iota β) q)) (g (HM.constDen (.iota β) q)) := by
      dsimp [q, f, g] at hqChoice
      simpa [pointwiseNePred, pointwiseEqPred, complementPred, firstFun, secondFun,
          HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend,
          q, f, g]
        using hqChoice
    exact False.elim (hChosenFalse hChosen)

/-- Quoted result 28 is valid in all paper-general models. -/
theorem derived28_validInGeneral {α : HTy} :
    ValidInGeneralCtx (derived28 (α := α)) := by
  intro M ρ hρ
  classical
  let HM := M.toHenkinModel
  let p : Ty.denote HM.Carrier (Pred α) := ρ .vz
  let q : Ty.denote HM.Carrier (Pred α) :=
    HenkinModel.denote HM (complementPred (topPred (α := α))) ρ
  have hq : HM.adm (Pred α) q := by
    dsimp [q]
    exact HenkinModel.denote_admissible HM hρ
      (complementPred (topPred (α := α)))
  change
    ((p (HM.constDen (.iota α) q)).down →
      ∀ x : Ty.denote HM.Carrier α, HM.adm α x → (p x).down)
  intro hpChoice x hx
  by_cases hpx : (p x).down
  · exact hpx
  · have hqWitness : ∃ y : Ty.denote HM.Carrier α, HM.adm α y ∧ (q y).down := by
      refine ⟨x, hx, ?_⟩
      dsimp [q, p]
      exact hpx
    have hqChoice : (q (HM.constDen (.iota α) q)).down :=
      M.iota_sound α q hq hqWitness
    have hpChoiceFalse : ¬ (p (HM.constDen (.iota α) q)).down := by
      dsimp [q, p] at hqChoice
      exact hqChoice
    exact False.elim (hpChoiceFalse hpChoice)

/-- Quoted result 29 is Henkin's description axiom, already available semantically. -/
theorem derived29_validInGeneral {α : HTy} :
    ValidInGeneralCtx (axiom11 (α := α)) :=
  axiom11_validInGeneral

/-- Partial rebase of quoted result 29 onto the packaged canonical description
model layer: its representative-closed canonical instance belongs to the
theory. -/
theorem derived29_closeFormula_mem_inCanonicalDescriptionModel
    {α : HTy}
    (M : CanonicalClassModel.CanonicalDescriptionModel)
    (ν : M.toCanonicalClassModel.Assignment [α, Pred α]) :
    ClassAssignment.closeFormula ν (axiom11 (α := α)) ∈ M.T :=
  M.classAssignment_closeFormula_axiom11_mem ν

/-- Quoted result 30 is valid in all paper-general models:
`(¬B ⊃ B) ⊃ B`. -/
theorem derived30_validInGeneral (B : Sentence) :
    ValidInGeneral (imp (imp (not B) B) B) := by
  intro M
  classical
  change M.toHenkinModel.models (.imp (.imp (.not B) B) B)
  rw [HenkinModel.models_imp]
  intro h
  by_cases hB : HenkinModel.models M.toHenkinModel B
  · exact hB
  · exact False.elim (hB (h (by simpa [not, HenkinModel.models, PreModel.models] using hB)))

end Mettapedia.AutoBooks.Codex.Henkin1950
