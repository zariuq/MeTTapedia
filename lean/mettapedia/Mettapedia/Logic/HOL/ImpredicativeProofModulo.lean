import Mettapedia.Logic.HOL.ImpredicativeProofTranslation

/-!
# The derived connectives, by definition, in proofs modulo conversion

The checker's calculus `ProofSyntaxModulo` has hypotheses, implication and
universal quantification, and retyping along the source's conversion. Its
formulas may contain the connectives `⊤ ⊥ ∧ ∨ ¬ ∃` of the source syntax, but it
has no rules for them, and its readers decline them.

This module elaborates them by their impredicative definitions, written out in
place (`expandInline`):

* `⊤ := ∀r. r → r` and `⊥ := ∀r. r`;
* `p ∧ q := ∀r. (p → q → r) → r` and `p ∨ q := ∀r. (p → r) → (q → r) → r`;
* `¬p := p → ⊥` and `∃x. φ := ∀r. (∀x. φ → r) → r`.

The expansion is total, leaves constants, application, abstraction and
equality alone, lands in the core grammar (`isCore_expandInline`), commutes
with renaming and substitution (`expandInline_rename`, `expandInline_subst`),
and preserves the Henkin meaning of every term (`denote_expandInline`). It
differs from `expand`, which writes the connectives as applications of
operator constants, by the β-steps that unfold those applications: here no
conversion is needed to use a connective.

`expandProofModulo?` maps a retained proof of the extensional calculus to a
proof modulo conversion of the expanded sequent. The rules of the connectives
become proofs of the checker's calculus: each introduction and elimination is
a closed proof of the corresponding implication, applied by modus ponens, and
its compilation is the standard combinator of the encoding (pairing,
projection, injection, case analysis, witness packing and unpacking). The map
is defined exactly on the hypothesis, connective and quantifier rules
(`expandProofModulo?_isSome`): the equality rules, including propositional and
functional extensionality and η, are not elaborated, because the calculus
modulo conversion has no counterpart of them.

The image is small (`Elaborated`, `expandProofModulo?_elaborated`): every
introduced premise and instantiated term is core (`expandProofModulo?_isCore`),
and every retyping step is between syntactically equal formulas, so the
elaboration uses no definitional conversion at all. Every retained proof of
the fragment therefore gives a proof modulo any list of equations
(`expandProofModulo?_derivable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ImpredicativeConnectives

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## The expansion -/

section Expansion

variable {Γ Δ : Ctx Base}

/-- `∃x. φ` as `∀r. (∀x. φ → r) → r`, with `φ` read below the binder of `r`. -/
def existentialInline {σ : Ty Base} (φ : Formula Const (σ :: Γ)) : Formula Const Γ :=
  .all (.imp (.all (.imp (rename (Rename.lift Rename.weaken) φ) (.var (.vs .vz)))) (.var .vz))

/-- The derived connectives replaced by their impredicative definitions. -/
def expandInline : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ
  | _, _, .var i => .var i
  | _, _, .const c => .const c
  | _, _, .app f a => .app (expandInline f) (expandInline a)
  | _, _, .lam b => .lam (expandInline b)
  | _, _, .top => truth
  | _, _, .bot => falsity
  | _, _, .and p q => conjunctionFormula (expandInline p) (expandInline q)
  | _, _, .or p q => disjunctionFormula (expandInline p) (expandInline q)
  | _, _, .imp p q => .imp (expandInline p) (expandInline q)
  | _, _, .not p => .imp (expandInline p) falsity
  | _, _, .eq l r => .eq (expandInline l) (expandInline r)
  | _, _, .all b => .all (expandInline b)
  | _, _, .ex b => existentialInline (expandInline b)

/-- The boolean core predicate of the checker is the core grammar. -/
theorem isCore_eq_true_iff {τ : Ty Base} (t : Term Const Γ τ) :
    t.isCore = true ↔ IsCore t := by
  induction t with
  | var => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | const => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | app f a ihf iha | imp f a ihf iha | eq f a ihf iha =>
      simp only [Term.isCore, IsCore, Bool.and_eq_true, ihf, iha]
  | lam b ih | all b ih => simpa only [Term.isCore, IsCore] using ih
  | top | bot | and | or | not | ex =>
      exact ⟨fun h => (nomatch h), fun h => h.elim⟩

theorem isCore_subst {τ : Ty Base} (t : Term Const Γ τ) :
    ∀ {Δ : Ctx Base} {s : Subst Const Γ Δ},
      (∀ {τ : Ty Base} (i : Var Γ τ), IsCore (s i)) →
      IsCore t → IsCore (subst s t) := by
  induction t with
  | var i => exact fun hs _ => hs i
  | const => exact fun _ _ => trivial
  | app _ _ ihf iha | imp _ _ ihf iha | eq _ _ ihf iha =>
      exact fun hs h => ⟨ihf hs h.1, iha hs h.2⟩
  | lam _ ih | all _ ih =>
      intro Δ s hs h
      refine ih (s := Subst.lift s) (fun i => ?_) h
      cases i with
      | vz => trivial
      | vs i => exact (isCore_rename _ _).mpr (hs i)
  | top | bot | and | or | not | ex => exact fun _ h => h.elim

theorem isCore_instantiate {σ τ : Ty Base} {t : Term Const Γ σ} {b : Term Const (σ :: Γ) τ}
    (ht : IsCore t) (hb : IsCore b) : IsCore (instantiate t b) :=
  isCore_subst b (fun i => by cases i with
    | vz => exact ht
    | vs _ => trivial) hb

theorem isCore_expandInline {τ : Ty Base} (t : Term Const Γ τ) : IsCore (expandInline t) := by
  induction t with
  | var | const | top | bot => trivial
  | app _ _ ihf iha | imp _ _ ihf iha | eq _ _ ihf iha => exact ⟨ihf, iha⟩
  | lam _ ih | all _ ih => exact ih
  | and _ _ ihp ihq =>
      exact ⟨⟨(isCore_rename _ _).mpr ihp, (isCore_rename _ _).mpr ihq, trivial⟩, trivial⟩
  | or _ _ ihp ihq =>
      exact ⟨⟨(isCore_rename _ _).mpr ihp, trivial⟩,
        ⟨(isCore_rename _ _).mpr ihq, trivial⟩, trivial⟩
  | not _ ih => exact ⟨ih, trivial⟩
  | ex _ ih => exact ⟨⟨(isCore_rename _ _).mpr ih, trivial⟩, trivial⟩

theorem expandInline_isCore {τ : Ty Base} (t : Term Const Γ τ) :
    (expandInline t).isCore = true :=
  (isCore_eq_true_iff _).mpr (isCore_expandInline t)

theorem expandInline_of_isCore {τ : Ty Base} (t : Term Const Γ τ) (h : IsCore t) :
    expandInline t = t := by
  induction t with
  | var | const => rfl
  | app _ _ ihf iha | imp _ _ ihf iha | eq _ _ ihf iha =>
      simp only [expandInline, ihf h.1, iha h.2]
  | lam _ ih | all _ ih => simp only [expandInline, ih h]
  | top | bot | and | or | not | ex => exact h.elim

theorem expandInline_idempotent {τ : Ty Base} (t : Term Const Γ τ) :
    expandInline (expandInline t) = expandInline t :=
  expandInline_of_isCore _ (isCore_expandInline t)

/-! ### Renaming and substitution -/

theorem rename_conjunctionFormula (ρ : Rename Base Γ Δ) (p q : Formula Const Γ) :
    rename ρ (conjunctionFormula p q) = conjunctionFormula (rename ρ p) (rename ρ q) := by
  simp only [conjunctionFormula, rename, weaken, rename_lift_weaken, Rename.lift]

theorem rename_disjunctionFormula (ρ : Rename Base Γ Δ) (p q : Formula Const Γ) :
    rename ρ (disjunctionFormula p q) = disjunctionFormula (rename ρ p) (rename ρ q) := by
  simp only [disjunctionFormula, rename, weaken, rename_lift_weaken, Rename.lift]

theorem rename_existentialInline {σ : Ty Base} (ρ : Rename Base Γ Δ)
    (φ : Formula Const (σ :: Γ)) :
    rename ρ (existentialInline φ) = existentialInline (rename (Rename.lift ρ) φ) := by
  have inner : rename (Rename.lift (Rename.lift ρ)) (rename (Rename.lift Rename.weaken) φ) =
      rename (Rename.lift (σ := σ) (Rename.weaken (σ := .prop)))
        (rename (Rename.lift ρ) φ) := by
    rw [rename_comp, rename_comp]
    apply rename_ext
    intro τ i
    cases i <;> rfl
  change Term.all (.imp (.all (.imp (rename (Rename.lift (Rename.lift ρ))
    (rename (Rename.lift Rename.weaken) φ)) (.var (.vs .vz)))) (.var .vz)) = _
  rw [inner]
  rfl

theorem subst_conjunctionFormula (s : Subst Const Γ Δ) (p q : Formula Const Γ) :
    subst s (conjunctionFormula p q) = conjunctionFormula (subst s p) (subst s q) := by
  simp only [conjunctionFormula, subst, subst_weaken, Subst.lift]

theorem subst_disjunctionFormula (s : Subst Const Γ Δ) (p q : Formula Const Γ) :
    subst s (disjunctionFormula p q) = disjunctionFormula (subst s p) (subst s q) := by
  simp only [disjunctionFormula, subst, subst_weaken, Subst.lift]

theorem subst_existentialInline {σ : Ty Base} (s : Subst Const Γ Δ)
    (φ : Formula Const (σ :: Γ)) :
    subst s (existentialInline φ) = existentialInline (subst (Subst.lift s) φ) := by
  have inner : subst (Subst.lift (Subst.lift s)) (rename (Rename.lift Rename.weaken) φ) =
      rename (Rename.lift (σ := σ) (Rename.weaken (σ := .prop))) (subst (Subst.lift s) φ) := by
    rw [subst_rename, rename_subst]
    apply subst_ext
    intro τ i
    cases i with
    | vz => rfl
    | vs i => exact (rename_lift_weaken _ _).symm
  change Term.all (.imp (.all (.imp (subst (Subst.lift (Subst.lift s))
    (rename (Rename.lift Rename.weaken) φ)) (.var (.vs .vz)))) (.var .vz)) = _
  rw [inner]
  rfl

theorem expandInline_rename {τ : Ty Base} (ρ : Rename Base Γ Δ) (t : Term Const Γ τ) :
    expandInline (rename ρ t) = rename ρ (expandInline t) := by
  induction t generalizing Δ with
  | var | const | top | bot => rfl
  | app _ _ ihf iha | imp _ _ ihf iha | eq _ _ ihf iha =>
      simp only [rename, expandInline, ihf, iha]
  | lam _ ih | all _ ih => simp only [rename, expandInline, ih]
  | and _ _ ihp ihq => simp only [rename, expandInline, ihp, ihq, rename_conjunctionFormula]
  | or _ _ ihp ihq => simp only [rename, expandInline, ihp, ihq, rename_disjunctionFormula]
  | not _ ih => simp only [rename, expandInline, ih]; rfl
  | ex _ ih => simp only [rename, expandInline, ih, rename_existentialInline]

theorem expandInline_weaken {σ τ : Ty Base} (t : Term Const Γ τ) :
    expandInline (weaken (σ := σ) t) = weaken (expandInline t) :=
  expandInline_rename _ t

private theorem expandInline_lift {σ : Ty Base} (s : Subst Const Γ Δ) :
    (fun {τ} (i : Var (σ :: Γ) τ) => expandInline (Subst.lift s i)) =
      (Subst.lift (fun i => expandInline (s i)) : Subst Const (σ :: Γ) (σ :: Δ)) := by
  funext τ i
  cases i with
  | vz => rfl
  | vs i => exact expandInline_rename _ _

theorem expandInline_subst {τ : Ty Base} (s : Subst Const Γ Δ) (t : Term Const Γ τ) :
    expandInline (subst s t) = subst (fun i => expandInline (s i)) (expandInline t) := by
  induction t generalizing Δ with
  | var | const | top | bot => rfl
  | app _ _ ihf iha | imp _ _ ihf iha | eq _ _ ihf iha =>
      simp only [subst, expandInline, ihf, iha]
  | lam _ ih | all _ ih => simp only [subst, expandInline, ih, expandInline_lift]
  | and _ _ ihp ihq => simp only [subst, expandInline, ihp, ihq, subst_conjunctionFormula]
  | or _ _ ihp ihq => simp only [subst, expandInline, ihp, ihq, subst_disjunctionFormula]
  | not _ ih => simp only [subst, expandInline, ih]; rfl
  | ex _ ih => simp only [subst, expandInline, ih, expandInline_lift, subst_existentialInline]

theorem expandInline_instantiate {σ τ : Ty Base} (t : Term Const Γ σ)
    (b : Term Const (σ :: Γ) τ) :
    expandInline (instantiate t b) = instantiate (expandInline t) (expandInline b) := by
  unfold instantiate
  rw [expandInline_subst]
  apply subst_ext
  intro _ i
  cases i <;> rfl

/-- Expansion commutes with weakening an assumption list. -/
theorem map_expandInline_weakenHyps {σ : Ty Base} :
    ∀ hyps : List (Formula Const Γ),
      (weakenHyps (σ := σ) hyps).map expandInline = weakenHyps (hyps.map expandInline)
  | [] => rfl
  | δ :: hyps => by
      change expandInline (weaken δ) :: (weakenHyps hyps).map expandInline =
        weaken (expandInline δ) :: weakenHyps (hyps.map expandInline)
      rw [expandInline_weaken, map_expandInline_weakenHyps hyps]

/-- The expanded hypothesis at an occurrence. -/
theorem get_map_expandInline :
    ∀ (hyps : List (Formula Const Γ)) (i : Fin hyps.length),
      (hyps.map expandInline).get (i.cast (List.length_map expandInline).symm) =
        expandInline (hyps.get i)
  | [], i => i.elim0
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: hyps, ⟨k + 1, h⟩ => get_map_expandInline hyps ⟨k, Nat.lt_of_succ_lt_succ h⟩

end Expansion

/-! ## Meaning -/

section Meaning

variable {Γ : Ctx Base}

private theorem denote_rename_lift_weaken (M : HenkinModel.{u, v, w} Base Const)
    {σ τ : Ty Base} (b : Term Const (σ :: Γ) τ) (ρ : HenkinModel.Valuation M Γ)
    (r : Ty.denote M.Carrier .prop) (x : Ty.denote M.Carrier σ) :
    HenkinModel.denote M (rename (Rename.lift (Rename.weaken (σ := .prop))) b)
        (HenkinModel.extend M (HenkinModel.extend M ρ r) x) =
      HenkinModel.denote M b (HenkinModel.extend M ρ x) := by
  rw [Soundness.denote_rename]
  congr 1
  funext τ i
  cases i <;> rfl

/-- **The expansion keeps the meaning** of every term in every Henkin model,
at every valuation. -/
theorem denote_expandInline (M : HenkinModel.{u, v, w} Base Const) {τ : Ty Base}
    (t : Term Const Γ τ) (ρ : HenkinModel.Valuation M Γ) :
    HenkinModel.denote M (expandInline t) ρ = HenkinModel.denote M t ρ := by
  induction t with
  | var | const => rfl
  | app _ _ ihf iha => simp only [expandInline, PreModel.denote, ihf, iha]
  | lam _ ih => funext x; exact ih _
  | imp _ _ ihp ihq | eq _ _ ihp ihq => simp only [expandInline, PreModel.denote, ihp, ihq]; rfl
  | all _ ih => simp only [expandInline, PreModel.denote, ih]; rfl
  | top =>
      apply ULift.ext
      apply propext
      exact ⟨fun _ => trivial, fun _ _ _ h => h⟩
  | bot =>
      apply ULift.ext
      apply propext
      exact ⟨fun h => h (.up False) (M.prop_mem _), False.elim⟩
  | and p q ihp ihq =>
      apply ULift.ext
      apply propext
      change (∀ r, M.adm .prop r → ((HenkinModel.denote M (weaken (expandInline p))
          (HenkinModel.extend M ρ r)).down → (HenkinModel.denote M (weaken (expandInline q))
          (HenkinModel.extend M ρ r)).down → r.down) → r.down) ↔
        (HenkinModel.denote M p ρ).down ∧ (HenkinModel.denote M q ρ).down
      simp only [Soundness.denote_weaken, ihp, ihq]
      exact ⟨fun h => h (.up _) (M.prop_mem _) And.intro, fun ⟨hp, hq⟩ _ _ k => k hp hq⟩
  | or p q ihp ihq =>
      apply ULift.ext
      apply propext
      change (∀ r, M.adm .prop r → ((HenkinModel.denote M (weaken (expandInline p))
          (HenkinModel.extend M ρ r)).down → r.down) → ((HenkinModel.denote M
          (weaken (expandInline q)) (HenkinModel.extend M ρ r)).down → r.down) → r.down) ↔
        (HenkinModel.denote M p ρ).down ∨ (HenkinModel.denote M q ρ).down
      simp only [Soundness.denote_weaken, ihp, ihq]
      exact ⟨fun h => h (.up _) (M.prop_mem _) Or.inl Or.inr,
        fun h _ _ l k => h.elim l k⟩
  | not p ih =>
      apply ULift.ext
      apply propext
      change ((HenkinModel.denote M (expandInline p) ρ).down →
          ∀ r, M.adm .prop r → r.down) ↔ ¬ (HenkinModel.denote M p ρ).down
      rw [ih]
      exact ⟨fun h hp => h hp (.up False) (M.prop_mem _), fun h hp => (h hp).elim⟩
  | @ex σ Γ b ih =>
      apply ULift.ext
      apply propext
      change (∀ r, M.adm .prop r → (∀ x, M.adm σ x →
          (HenkinModel.denote M (rename (Rename.lift Rename.weaken) (expandInline b))
            (HenkinModel.extend M (HenkinModel.extend M ρ r) x)).down → r.down) → r.down) ↔
        ∃ x, M.adm σ x ∧ (HenkinModel.denote M b (HenkinModel.extend M ρ x)).down
      simp only [denote_rename_lift_weaken, ih]
      exact ⟨fun h => h (.up _) (M.prop_mem _) fun x hx hb => ⟨x, hx, hb⟩,
        fun ⟨x, hx, hb⟩ _ _ k => k x hx hb⟩

theorem models_expandInline (M : HenkinModel.{u, v, w} Base Const) (φ : ClosedFormula Const) :
    M.models (expandInline φ) ↔ M.models φ :=
  Iff.of_eq (congrArg ULift.down (denote_expandInline M φ (fun i => nomatch i)))

/-- The two expansions mean the same: the operator form of `expand` and the
inlined definitions. -/
theorem denote_expand_eq_expandInline (M : HenkinModel.{u, v, w} Base Const) {τ : Ty Base}
    (t : Term Const Γ τ) (ρ : HenkinModel.Valuation M Γ) :
    HenkinModel.denote M (expand t) ρ = HenkinModel.denote M (expandInline t) ρ :=
  (denote_expand M t ρ).trans (denote_expandInline M t ρ).symm

end Meaning

/-! ## The connective rules in the calculus modulo conversion -/

namespace Modulo

variable {eqs : List (DefiningEquation Const)} {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

/-- Retyping along an equality of formulas: a conversion article by
reflexivity. -/
def cast {φ ψ : Formula Const Γ} (h : φ = ψ) (d : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs Δ ψ :=
  .convert (h ▸ Relation.EqvGen.refl φ) d

/-- Transport along an equality of assumption lists. -/
def castHyps {Δ' : List (Formula Const Γ)} {φ : Formula Const Γ} (h : Δ = Δ')
    (d : ProofSyntaxModulo eqs Δ φ) : ProofSyntaxModulo eqs Δ' φ :=
  h ▸ d

/-- `⊤`: `λr. λx. x`. -/
def truthIntro : ProofSyntaxModulo eqs Δ truth := .allI (.impI (.hyp 0))

/-- `p → q → p ∧ q`: pairing, `λa. λb. λr. λk. k a b`. -/
def conjunctionIntroLemma (p q : Formula Const Γ) :
    ProofSyntaxModulo eqs Δ (.imp p (.imp q (conjunctionFormula p q))) :=
  .impI (.impI (.allI (.impI (.impE (.impE (.hyp 0) (.hyp 2)) (.hyp 1)))))

def conjunctionIntro {p q : Formula Const Γ} (left : ProofSyntaxModulo eqs Δ p)
    (right : ProofSyntaxModulo eqs Δ q) : ProofSyntaxModulo eqs Δ (conjunctionFormula p q) :=
  .impE (.impE (conjunctionIntroLemma p q) left) right

theorem instantiate_conjunctionBody (r p q : Formula Const Γ) :
    instantiate r (.imp (.imp (weaken p) (.imp (weaken q) (.var .vz))) (.var .vz)) =
      .imp (.imp p (.imp q r)) r := by
  change Term.imp (.imp (instantiate r (weaken p)) (.imp (instantiate r (weaken q)) r)) r = _
  rw [instantiate_weaken, instantiate_weaken]

/-- A conjunction at the proposition `r`. -/
def conjunctionElim {p q : Formula Const Γ} (r : Formula Const Γ)
    (proof : ProofSyntaxModulo eqs Δ (conjunctionFormula p q)) :
    ProofSyntaxModulo eqs Δ (.imp (.imp p (.imp q r)) r) :=
  cast (instantiate_conjunctionBody r p q) (.allE r proof)

/-- The first projection, `z p (λa. λb. a)`. -/
def conjunctionLeft {p q : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ (conjunctionFormula p q)) : ProofSyntaxModulo eqs Δ p :=
  .impE (conjunctionElim p proof) (.impI (.impI (.hyp 1)))

/-- The second projection, `z q (λa. λb. b)`. -/
def conjunctionRight {p q : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ (conjunctionFormula p q)) : ProofSyntaxModulo eqs Δ q :=
  .impE (conjunctionElim q proof) (.impI (.impI (.hyp 0)))

/-- `p → p ∨ q`: the left injection, `λa. λr. λl. λk. l a`. -/
def disjunctionLeftLemma (p q : Formula Const Γ) :
    ProofSyntaxModulo eqs Δ (.imp p (disjunctionFormula p q)) :=
  .impI (.allI (.impI (.impI (.impE (.hyp 1) (.hyp 2)))))

/-- `q → p ∨ q`: the right injection, `λb. λr. λl. λk. k b`. -/
def disjunctionRightLemma (p q : Formula Const Γ) :
    ProofSyntaxModulo eqs Δ (.imp q (disjunctionFormula p q)) :=
  .impI (.allI (.impI (.impI (.impE (.hyp 0) (.hyp 2)))))

def disjunctionLeft {p q : Formula Const Γ} (proof : ProofSyntaxModulo eqs Δ p) :
    ProofSyntaxModulo eqs Δ (disjunctionFormula p q) :=
  .impE (disjunctionLeftLemma p q) proof

def disjunctionRight {p q : Formula Const Γ} (proof : ProofSyntaxModulo eqs Δ q) :
    ProofSyntaxModulo eqs Δ (disjunctionFormula p q) :=
  .impE (disjunctionRightLemma p q) proof

theorem instantiate_disjunctionBody (r p q : Formula Const Γ) :
    instantiate r (.imp (.imp (weaken p) (.var .vz))
        (.imp (.imp (weaken q) (.var .vz)) (.var .vz))) =
      .imp (.imp p r) (.imp (.imp q r) r) := by
  change Term.imp (.imp (instantiate r (weaken p)) r) (.imp (.imp (instantiate r (weaken q)) r) r) =
    _
  rw [instantiate_weaken, instantiate_weaken]

/-- Case analysis, `z r (λa. left) (λb. right)`. -/
def disjunctionElim {p q r : Formula Const Γ}
    (cases : ProofSyntaxModulo eqs Δ (disjunctionFormula p q))
    (left : ProofSyntaxModulo eqs (p :: Δ) r) (right : ProofSyntaxModulo eqs (q :: Δ) r) :
    ProofSyntaxModulo eqs Δ r :=
  .impE (.impE (cast (instantiate_disjunctionBody r p q) (.allE r cases)) (.impI left))
    (.impI right)

theorem subst_lift_single_rename_lift_weaken {σ τ : Ty Base} (r : Formula Const Γ)
    (φ : Term Const (σ :: Γ) τ) :
    subst (Subst.lift (Subst.single r))
      (rename (Rename.lift (Rename.weaken (σ := .prop))) φ) = φ := by
  rw [subst_rename]
  calc subst (fun {_} i => Subst.lift (Subst.single r) (Rename.lift Rename.weaken i)) φ
      = subst Subst.id φ := by
        apply subst_ext
        intro _ i
        cases i <;> rfl
    _ = φ := subst_id φ

theorem instantiate_existentialBody {σ : Ty Base} (r : Formula Const Γ)
    (φ : Formula Const (σ :: Γ)) :
    instantiate r (.imp (.all (.imp (rename (Rename.lift Rename.weaken) φ) (.var (.vs .vz))))
        (.var .vz)) =
      .imp (.all (.imp φ (weaken r))) r := by
  change Term.imp (.all (.imp (subst (Subst.lift (Subst.single r))
    (rename (Rename.lift Rename.weaken) φ)) (weaken r))) r = _
  rw [subst_lift_single_rename_lift_weaken]

theorem instantiate_existentialInstance {σ : Ty Base} (t : Term Const Γ σ)
    (φ : Formula Const (σ :: Γ)) :
    instantiate (weaken (σ := .prop) t)
        (.imp (rename (Rename.lift Rename.weaken) φ) (.var (.vs .vz))) =
      .imp (weaken (instantiate t φ)) (.var .vz) := by
  change Term.imp (instantiate (weaken t) (rename (Rename.lift Rename.weaken) φ)) (.var .vz) = _
  congr 1
  unfold instantiate weaken
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro _ i
  cases i <;> rfl

/-- `φ[t] → ∃x. φ`: packing the witness, `λa. λr. λk. k t a`. -/
def existentialIntroLemma {σ : Ty Base} (t : Term Const Γ σ) (φ : Formula Const (σ :: Γ)) :
    ProofSyntaxModulo eqs Δ (.imp (instantiate t φ) (existentialInline φ)) :=
  .impI (.allI (.impI (.impE (cast (instantiate_existentialInstance t φ)
    (.allE (weaken t) (.hyp 0))) (.hyp 1))))

def existentialIntro {σ : Ty Base} (t : Term Const Γ σ) {φ : Formula Const (σ :: Γ)}
    (proof : ProofSyntaxModulo eqs Δ (instantiate t φ)) :
    ProofSyntaxModulo eqs Δ (existentialInline φ) :=
  .impE (existentialIntroLemma t φ) proof

/-- Unpacking the witness, `z r (λx. λa. body)`. -/
def existentialElim {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {r : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ (existentialInline φ))
    (body : ProofSyntaxModulo eqs (φ :: weakenHyps Δ) (weaken r)) : ProofSyntaxModulo eqs Δ r :=
  .impE (cast (instantiate_existentialBody r φ) (.allE r proof)) (.allI (.impI body))

end Modulo

/-! ## The elaboration of retained proofs -/

section Elaboration

variable {eqs : List (DefiningEquation Const)}

/-- The rules the elaboration covers: hypotheses, the connectives and the
quantifiers. The equality rules are outside it. -/
def connectiveFragment : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
    {φ : Formula Const Γ} → ProofSyntax Const Δ φ → Bool
  | _, _, _, .hyp _ => true
  | _, _, _, .topI => true
  | _, _, _, .botE proof => connectiveFragment proof
  | _, _, _, .andI left right => connectiveFragment left && connectiveFragment right
  | _, _, _, .andEL proof => connectiveFragment proof
  | _, _, _, .andER proof => connectiveFragment proof
  | _, _, _, .orIL proof => connectiveFragment proof
  | _, _, _, .orIR proof => connectiveFragment proof
  | _, _, _, .orE cases left right =>
      connectiveFragment cases && connectiveFragment left && connectiveFragment right
  | _, _, _, .impI body => connectiveFragment body
  | _, _, _, .impE function argument => connectiveFragment function && connectiveFragment argument
  | _, _, _, .notI body => connectiveFragment body
  | _, _, _, .notE negative positive =>
      connectiveFragment negative && connectiveFragment positive
  | _, _, _, .allI body => connectiveFragment body
  | _, _, _, .allE _ proof => connectiveFragment proof
  | _, _, _, .exI _ proof => connectiveFragment proof
  | _, _, _, .exE witness body => connectiveFragment witness && connectiveFragment body
  | _, _, _, .eqRefl _ | _, _, _, .eqSymm _ | _, _, _, .eqTrans _ _ | _, _, _, .eqPropI _ _
  | _, _, _, .eqPropEL _ | _, _, _, .eqPropER _ | _, _, _, .eqApp _ _ | _, _, _, .eqAppArg _ _
  | _, _, _, .eqLam _ | _, _, _, .funExt _ | _, _, _, .beta _ _ | _, _, _, .eta _ => false

/-- **The elaboration.** A retained proof of the connective fragment becomes a
proof modulo conversion of the expanded sequent. -/
def expandProofModulo? : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} →
    {φ : Formula Const Γ} → ProofSyntax Const Δ φ →
      Option (ProofSyntaxModulo eqs (Δ.map expandInline) (expandInline φ))
  | _, Δ, _, .hyp occurrence =>
      some (Modulo.cast (get_map_expandInline Δ occurrence)
        (.hyp (occurrence.cast (List.length_map expandInline).symm)))
  | _, _, _, .topI => some Modulo.truthIntro
  | _, _, _, @ProofSyntax.botE _ _ _ _ φ proof =>
      (expandProofModulo? proof).map fun z => .allE (expandInline φ) z
  | _, _, _, .andI left right => do
      let a ← expandProofModulo? left
      let b ← expandProofModulo? right
      pure (Modulo.conjunctionIntro a b)
  | _, _, _, .andEL proof => (expandProofModulo? proof).map Modulo.conjunctionLeft
  | _, _, _, .andER proof => (expandProofModulo? proof).map Modulo.conjunctionRight
  | _, _, _, .orIL proof => (expandProofModulo? proof).map Modulo.disjunctionLeft
  | _, _, _, .orIR proof => (expandProofModulo? proof).map Modulo.disjunctionRight
  | _, _, _, .orE cases left right => do
      let c ← expandProofModulo? cases
      let l ← expandProofModulo? left
      let r ← expandProofModulo? right
      pure (Modulo.disjunctionElim c l r)
  | _, _, _, .impI body => (expandProofModulo? body).map .impI
  | _, _, _, .impE function argument => do
      let f ← expandProofModulo? function
      let a ← expandProofModulo? argument
      pure (.impE f a)
  | _, _, _, .notI body => (expandProofModulo? body).map .impI
  | _, _, _, .notE negative positive => do
      let n ← expandProofModulo? negative
      let p ← expandProofModulo? positive
      pure (.impE n p)
  | _, Δ, _, .allI body =>
      (expandProofModulo? body).map fun b =>
        .allI (Modulo.castHyps (map_expandInline_weakenHyps Δ) b)
  | _, _, _, @ProofSyntax.allE _ _ _ _ _ φ term proof =>
      (expandProofModulo? proof).map fun f =>
        Modulo.cast (expandInline_instantiate term φ).symm (.allE (expandInline term) f)
  | _, _, _, @ProofSyntax.exI _ _ _ _ _ φ term proof =>
      (expandProofModulo? proof).map fun p =>
        Modulo.existentialIntro (expandInline term)
          (Modulo.cast (expandInline_instantiate term φ) p)
  | _, Δ, _, @ProofSyntax.exE _ _ _ _ _ φ ψ witness body => do
      let e ← expandProofModulo? witness
      let b ← expandProofModulo? body
      pure (Modulo.existentialElim e (Modulo.castHyps (congrArg (expandInline φ :: ·)
        (map_expandInline_weakenHyps Δ)) (Modulo.cast (expandInline_weaken ψ) b)))
  | _, _, _, .eqRefl _ | _, _, _, .eqSymm _ | _, _, _, .eqTrans _ _ | _, _, _, .eqPropI _ _
  | _, _, _, .eqPropEL _ | _, _, _, .eqPropER _ | _, _, _, .eqApp _ _ | _, _, _, .eqAppArg _ _
  | _, _, _, .eqLam _ | _, _, _, .funExt _ | _, _, _, .beta _ _ | _, _, _, .eta _ => none

private theorem isSome_bind_some₂ {α β γ : Type*} (x : Option α) (y : Option β)
    (f : α → β → γ) :
    (x.bind fun a => y.bind fun b => some (f a b)).isSome = (x.isSome && y.isSome) := by
  cases x <;> cases y <;> rfl

private theorem isSome_bind_some₃ {α β γ δ : Type*} (x : Option α) (y : Option β)
    (z : Option γ)
    (f : α → β → γ → δ) :
    (x.bind fun a => y.bind fun b => z.bind fun c => some (f a b c)).isSome =
      (x.isSome && y.isSome && z.isSome) := by
  cases x <;> cases y <;> cases z <;> rfl

private theorem eq_some_of_bind_some₂ {α β γ : Type*} {x : Option α} {y : Option β}
    {f : α → β → γ} {c : γ} (h : (x.bind fun a => y.bind fun b => some (f a b)) = some c) :
    ∃ a b, x = some a ∧ y = some b ∧ f a b = c := by
  cases x <;> cases y <;> cases h
  exact ⟨_, _, rfl, rfl, rfl⟩

private theorem eq_some_of_bind_some₃ {α β γ δ : Type*} {x : Option α} {y : Option β}
    {z : Option γ} {f : α → β → γ → δ} {d : δ}
    (h : (x.bind fun a => y.bind fun b => z.bind fun c => some (f a b c)) = some d) :
    ∃ a b c, x = some a ∧ y = some b ∧ z = some c ∧ f a b c = d := by
  cases x <;> cases y <;> cases z <;> cases h
  exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- **Exact domain.** The elaboration succeeds exactly on the connective
fragment. -/
theorem expandProofModulo?_isSome {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    (expandProofModulo? (eqs := eqs) proof).isSome = connectiveFragment proof := by
  induction proof with
  | hyp | topI => rfl
  | botE _ ih | andEL _ ih | andER _ ih | orIL _ ih | orIR _ ih | impI _ ih | notI _ ih
  | allI _ ih | allE _ _ ih | exI _ _ ih =>
      rw [connectiveFragment, ← ih]
      exact Option.isSome_map
  | andI left right ihl ihr | impE left right ihl ihr | notE left right ihl ihr
  | exE left right ihl ihr =>
      rw [connectiveFragment, ← ihl, ← ihr]
      exact isSome_bind_some₂ _ _ _
  | orE cases left right ihc ihl ihr =>
      rw [connectiveFragment, ← ihc, ← ihl, ← ihr]
      exact isSome_bind_some₃ _ _ _ _
  | eqRefl | eqSymm | eqTrans | eqPropI | eqPropEL | eqPropER | eqApp | eqAppArg | eqLam
  | funExt | beta | eta => rfl

end Elaboration

/-! ## The shape of the image -/

section Image

variable {eqs : List (DefiningEquation Const)}

/-- The shape of an elaborated proof: every introduced premise and every
instantiated term is core, and every retyping step is between syntactically
equal formulas. -/
inductive Elaborated :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    ProofSyntaxModulo eqs Δ φ → Prop
  | hyp {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (i : Fin Δ.length) :
      Elaborated (.hyp (equations := eqs) (Δ := Δ) i)
  | impI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
      {body : ProofSyntaxModulo eqs (φ :: Δ) ψ} :
      IsCore φ → Elaborated body → Elaborated (.impI body)
  | impE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
      {function : ProofSyntaxModulo eqs Δ (.imp φ ψ)} {argument : ProofSyntaxModulo eqs Δ φ} :
      Elaborated function → Elaborated argument → Elaborated (.impE function argument)
  | allI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
      {φ : Formula Const (σ :: Γ)} {body : ProofSyntaxModulo eqs (weakenHyps (σ := σ) Δ) φ} :
      Elaborated body → Elaborated (.allI body)
  | allE {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {σ : Ty Base}
      {φ : Formula Const (σ :: Γ)} {t : Term Const Γ σ}
      {function : ProofSyntaxModulo eqs Δ (.all φ)} :
      IsCore t → Elaborated function → Elaborated (.allE t function)
  | convert {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ ψ : Formula Const Γ}
      {article : CoreConversion eqs φ ψ} {inner : ProofSyntaxModulo eqs Δ φ} :
      φ = ψ → Elaborated inner → Elaborated (.convert article inner)

namespace Elaborated

variable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

theorem isCoreProofModulo {φ : Formula Const Γ} {d : ProofSyntaxModulo eqs Δ φ}
    (h : Elaborated d) : IsCoreProofModulo d := by
  induction h with
  | hyp => trivial
  | impI premise _ ih => exact ⟨premise, ih⟩
  | impE _ _ ihf iha => exact ⟨ihf, iha⟩
  | allI _ ih => exact ih
  | allE core _ ih => exact ⟨core, ih⟩
  | convert _ _ ih => exact ih

theorem cast {φ ψ : Formula Const Γ} (h : φ = ψ) {d : ProofSyntaxModulo eqs Δ φ}
    (e : Elaborated d) : Elaborated (Modulo.cast h d) :=
  .convert h e

theorem castHyps {Δ' : List (Formula Const Γ)} {φ : Formula Const Γ} (h : Δ = Δ')
    {d : ProofSyntaxModulo eqs Δ φ} (e : Elaborated d) : Elaborated (Modulo.castHyps h d) := by
  subst h
  exact e

theorem truthIntro : Elaborated (Modulo.truthIntro : ProofSyntaxModulo eqs Δ truth) :=
  .allI (.impI trivial (.hyp _))

theorem conjunctionIntro {p q : Formula Const Γ} (hp : IsCore p) (hq : IsCore q)
    {a : ProofSyntaxModulo eqs Δ p} {b : ProofSyntaxModulo eqs Δ q} (ea : Elaborated a)
    (eb : Elaborated b) : Elaborated (Modulo.conjunctionIntro a b) :=
  .impE (.impE (.impI hp (.impI hq (.allI (.impI
    ⟨(isCore_rename _ _).mpr hp, (isCore_rename _ _).mpr hq, trivial⟩
    (.impE (.impE (.hyp _) (.hyp _)) (.hyp _)))))) ea) eb

theorem conjunctionLeft {p q : Formula Const Γ} (hp : IsCore p) (hq : IsCore q)
    {z : ProofSyntaxModulo eqs Δ (conjunctionFormula p q)} (ez : Elaborated z) :
    Elaborated (Modulo.conjunctionLeft z) :=
  .impE (.convert (Modulo.instantiate_conjunctionBody p p q) (.allE hp ez))
    (.impI hp (.impI hq (.hyp _)))

theorem conjunctionRight {p q : Formula Const Γ} (hp : IsCore p) (hq : IsCore q)
    {z : ProofSyntaxModulo eqs Δ (conjunctionFormula p q)} (ez : Elaborated z) :
    Elaborated (Modulo.conjunctionRight z) :=
  .impE (.convert (Modulo.instantiate_conjunctionBody q p q) (.allE hq ez))
    (.impI hp (.impI hq (.hyp _)))

theorem disjunctionLeft {p q : Formula Const Γ} (hp : IsCore p) (hq : IsCore q)
    {a : ProofSyntaxModulo eqs Δ p} (ea : Elaborated a) :
    Elaborated (Modulo.disjunctionLeft (q := q) a) :=
  .impE (.impI hp (.allI (.impI ⟨(isCore_rename _ _).mpr hp, trivial⟩
    (.impI ⟨(isCore_rename _ _).mpr hq, trivial⟩ (.impE (.hyp _) (.hyp _)))))) ea

theorem disjunctionRight {p q : Formula Const Γ} (hp : IsCore p) (hq : IsCore q)
    {b : ProofSyntaxModulo eqs Δ q} (eb : Elaborated b) :
    Elaborated (Modulo.disjunctionRight (p := p) b) :=
  .impE (.impI hq (.allI (.impI ⟨(isCore_rename _ _).mpr hp, trivial⟩
    (.impI ⟨(isCore_rename _ _).mpr hq, trivial⟩ (.impE (.hyp _) (.hyp _)))))) eb

theorem disjunctionElim {p q r : Formula Const Γ} (hp : IsCore p) (hq : IsCore q)
    (hr : IsCore r) {z : ProofSyntaxModulo eqs Δ (disjunctionFormula p q)}
    {left : ProofSyntaxModulo eqs (p :: Δ) r} {right : ProofSyntaxModulo eqs (q :: Δ) r}
    (ez : Elaborated z) (el : Elaborated left) (er : Elaborated right) :
    Elaborated (Modulo.disjunctionElim z left right) :=
  .impE (.impE (.convert (Modulo.instantiate_disjunctionBody r p q) (.allE hr ez)) (.impI hp el))
    (.impI hq er)

theorem existentialIntro {σ : Ty Base} {t : Term Const Γ σ} {φ : Formula Const (σ :: Γ)}
    (ht : IsCore t) (hφ : IsCore φ) {d : ProofSyntaxModulo eqs Δ (instantiate t φ)}
    (ed : Elaborated d) : Elaborated (Modulo.existentialIntro t d) :=
  .impE (.impI (isCore_instantiate ht hφ) (.allI (.impI ⟨(isCore_rename _ _).mpr hφ, trivial⟩
    (.impE (.convert (Modulo.instantiate_existentialInstance t φ)
      (.allE ((isCore_rename _ _).mpr ht) (.hyp _))) (.hyp _))))) ed

theorem existentialElim {σ : Ty Base} {φ : Formula Const (σ :: Γ)} {r : Formula Const Γ}
    (hφ : IsCore φ) (hr : IsCore r) {z : ProofSyntaxModulo eqs Δ (existentialInline φ)}
    {body : ProofSyntaxModulo eqs (φ :: weakenHyps Δ) (weaken r)} (ez : Elaborated z)
    (eb : Elaborated body) : Elaborated (Modulo.existentialElim z body) :=
  .impE (.convert (Modulo.instantiate_existentialBody r φ) (.allE hr ez)) (.allI (.impI hφ eb))

end Elaborated

/-- **The image of the elaboration.** Every elaborated proof has core premises
and instantiated terms, and retypes only along syntactic equality. -/
theorem expandProofModulo?_elaborated {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    ∀ {d : ProofSyntaxModulo eqs (Δ.map expandInline) (expandInline φ)},
      expandProofModulo? proof = some d → Elaborated d := by
  induction proof with
  | hyp occurrence =>
      intro d h
      cases h
      exact .cast _ (.hyp _)
  | topI =>
      intro d h
      cases h
      exact .truthIntro
  | botE _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .allE (isCore_expandInline _) (ih hz)
  | andI left right ihl ihr =>
      intro d h
      obtain ⟨a, b, ha, hb, rfl⟩ := eq_some_of_bind_some₂ h
      exact .conjunctionIntro (isCore_expandInline _) (isCore_expandInline _) (ihl ha) (ihr hb)
  | andEL _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .conjunctionLeft (isCore_expandInline _) (isCore_expandInline _) (ih hz)
  | andER _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .conjunctionRight (isCore_expandInline _) (isCore_expandInline _) (ih hz)
  | orIL _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .disjunctionLeft (isCore_expandInline _) (isCore_expandInline _) (ih hz)
  | orIR _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .disjunctionRight (isCore_expandInline _) (isCore_expandInline _) (ih hz)
  | orE cases left right ihc ihl ihr =>
      intro d h
      obtain ⟨c, l, r, hc, hl, hr, rfl⟩ := eq_some_of_bind_some₃ h
      exact .disjunctionElim (isCore_expandInline _) (isCore_expandInline _)
        (isCore_expandInline _) (ihc hc) (ihl hl) (ihr hr)
  | impI _ ih | notI _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .impI (isCore_expandInline _) (ih hz)
  | impE function argument ihf iha | notE function argument ihf iha =>
      intro d h
      obtain ⟨f, a, hf, ha, rfl⟩ := eq_some_of_bind_some₂ h
      exact .impE (ihf hf) (iha ha)
  | allI _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .allI (.castHyps _ (ih hz))
  | allE t _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .cast _ (.allE (isCore_expandInline t) (ih hz))
  | exI t _ ih =>
      intro d h
      obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
      exact .existentialIntro (isCore_expandInline t) (isCore_expandInline _) (.cast _ (ih hz))
  | exE witness body ihw ihb =>
      intro d h
      obtain ⟨e, b, he, hb, rfl⟩ := eq_some_of_bind_some₂ h
      exact .existentialElim (isCore_expandInline _) (isCore_expandInline _) (ihw he)
        (.castHyps _ (.cast _ (ihb hb)))
  | eqRefl | eqSymm | eqTrans | eqPropI | eqPropEL | eqPropER | eqApp | eqAppArg | eqLam
  | funExt | beta | eta => intro d h; cases h

/-- The elaborated proofs are core proofs modulo conversion. -/
theorem expandProofModulo?_isCore {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} {proof : ProofSyntax Const Δ φ}
    {d : ProofSyntaxModulo eqs (Δ.map expandInline) (expandInline φ)}
    (h : expandProofModulo? proof = some d) : IsCoreProofModulo d :=
  (expandProofModulo?_elaborated proof h).isCoreProofModulo

/-- **Soundness of the elaboration**: every retained proof of the connective
fragment gives a proof modulo conversion of the expanded sequent, for every
list of defining equations. -/
theorem expandProofModulo?_derivable {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ)
    (fragment : connectiveFragment proof = true) :
    Nonempty (ProofSyntaxModulo eqs (Δ.map expandInline) (expandInline φ)) := by
  have some := (expandProofModulo?_isSome (eqs := eqs) proof).trans fragment
  obtain ⟨d, _⟩ := Option.isSome_iff_exists.mp some
  exact ⟨d⟩

end Image

end Mettapedia.Logic.HOL.ImpredicativeConnectives
