import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationPrincipal

/-!
# Translated terms observe metavariables only through applications

A translated term mentions a metavariable only applied to all of its parameters. So two
substitutions that agree on the object positions and agree **applicatively** on every metavariable
(applied to convertible arguments, after any renaming, they convert) act convertibly on every
translated term (`encode_conv_of_appAgree`). In particular a variable and its eta expansion are
indistinguishable on translated terms, although they are distinct judged terms of the telescope.

**The pattern equation, on the image** (`pattern_factorsOnImage`). The translation of the
second-order principal answer `m, n ↦ g(x)` factors every dependent solution of `m(x) ≐ n(x)` on
translated terms. Hence asks of translated equation guards are preserved and reflected at this
store (`pattern_entails_iff`), although no principal answer exists on all judged terms
(`pattern_no_principal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace Translation

open CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual

variable {Head : Type}

section Agreement

variable {headEq : Head → Head → Prop} {root : RootComputation Head}

/-- Two heads agree applicatively on `p` arguments: after any renaming, applied to convertible
arguments, they convert. -/
def AppAgree {n : Nat} (f f' : Tm Head n) (p : Nat) : Prop :=
  ∀ {k : Nat} (ρ : Ren n k) (w w' : Sub Head p k), (∀ j, Conv headEq (w j) (w' j) root) →
    Conv headEq (spine (rename ρ f) w) (spine (rename ρ f') w') root

theorem AppAgree.renamed {n m : Nat} {f f' : Tm Head n} {p : Nat}
    (agree : AppAgree (headEq := headEq) (root := root) f f' p) (ρ : Ren n m) :
    AppAgree (headEq := headEq) (root := root) (rename ρ f) (rename ρ f') p := by
  intro k ρ' w w' arguments
  rw [rename_comp, rename_comp]
  exact agree (fun i => ρ' (ρ i)) w w' arguments

variable {S : Binding.Signature} (names : BindingSignatureEmbedding.Names S)
  (M : List (Binding.MetaArity S))

/-- Two scope substitutions agree on object positions up to conversion and applicatively on every
metavariable. -/
def ImageAgree {Γ : Binding.Ctx S} {n : Nat} (σ σ' : Sub Head (M.length + Γ.length) n) : Prop :=
  (∀ j : Fin Γ.length, Conv headEq (σ (inner j)) (σ' (inner j)) root) ∧
    ∀ i : Fin M.length,
      AppAgree (headEq := headEq) (root := root) (σ (outer i)) (σ' (outer i)) (M.get i).1.length

theorem imageAgree_lift {Γ : Binding.Ctx S} {k : Nat} {Ξ : Binding.Ctx S}
    {σ σ' : Sub Head (M.length + Γ.length) (k + Ξ.length)}
    (agree : ImageAgree (headEq := headEq) (root := root) M σ σ') :
    ∀ bound : List S.Srt,
      ImageAgree (headEq := headEq) (root := root) M (liftSubB σ bound) (liftSubB σ' bound)
  | [] => agree
  | _ :: bound => by
      have ih := imageAgree_lift agree bound
      refine ⟨fun j => ?_, fun i => ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · exact .refl _
        · exact Conv.renameTerms wk (ih.1 j)
      · exact AppAgree.renamed (ih.2 i) wk

mutual

/-- **Applicatively agreeing substitutions act convertibly on translated terms.** -/
theorem encode_conv_of_appAgree : ∀ {Γ : Binding.Ctx S} {s : S.Srt} {k : Nat} {Ξ : Binding.Ctx S}
    (t : Binding.Term (Sig S M) Γ s) (σ σ' : Sub Head (M.length + Γ.length) (k + Ξ.length)),
    ImageAgree (headEq := headEq) (root := root) M σ σ' →
      Conv headEq (subst σ (encode names M t)) (subst σ' (encode names M t)) root
  | _, _, _, _, .var v, _, _, agree => agree.1 (vIdx v)
  | _, _, _, _, .op (.inl o) args, σ, σ', agree => by
      show Conv headEq (subst σ (applyVec (.const (names.operator o)) (encodeArgs names M args)))
        (subst σ' (applyVec (.const (names.operator o)) (encodeArgs names M args))) root
      rw [subst_applyVec, subst_applyVec]
      exact conv_applyVec (.refl _) (fun j => encodeArgs_conv_of_appAgree args σ σ' agree j)
  | _, _, _, _, .op (.inr (.mk i)) args, σ, σ', agree => by
      have castLength : (M.get i).1.length =
          ((M.get i).1.map (fun sort => (([] : List S.Srt), sort))).length := by simp
      show Conv headEq
        (subst σ (spine (.var (outer i)) (fun j => encodeArgs names M args (Fin.cast castLength j))))
        (subst σ' (spine (.var (outer i)) (fun j => encodeArgs names M args (Fin.cast castLength j))))
        root
      rw [subst_spine, subst_spine]
      have heads := agree.2 i idRen _ _
        (fun j => encodeArgs_conv_of_appAgree args σ σ' agree (Fin.cast castLength j))
      rw [rename_id, rename_id] at heads
      exact heads

theorem encodeArgs_conv_of_appAgree : ∀ {as : List (List S.Srt × S.Srt)} {Γ : Binding.Ctx S}
    {k : Nat} {Ξ : Binding.Ctx S} (args : Binding.Args (Sig S M) as Γ)
    (σ σ' : Sub Head (M.length + Γ.length) (k + Ξ.length)),
    ImageAgree (headEq := headEq) (root := root) M σ σ' →
      ∀ j, Conv headEq (subst σ (encodeArgs names M args j)) (subst σ' (encodeArgs names M args j)) root
  | _, _, _, _, .nil, _, _, _, j => j.elim0
  | _, _, _, _, .cons (bs := bound) body rest, σ, σ', agree, j => by
      refine Fin.cases ?_ (fun j => ?_) j
      · show Conv headEq (subst σ (abstractB bound (encode names M body)))
          (subst σ' (abstractB bound (encode names M body))) root
        rw [subst_abstractB, subst_abstractB]
        exact conv_abstractB bound
          (encode_conv_of_appAgree body _ _ (imageAgree_lift M agree bound))
      · exact encodeArgs_conv_of_appAgree rest σ σ' agree j

end

end Agreement

/-! ## Eta expansions agree applicatively -/

section Eta

variable {rules : Rules Head}

theorem rename_etaOf {n m : Nat} (ρ : Ren n m) (u : Tm Head n) :
    rename ρ (etaOf u) = etaOf (rename ρ u) := by
  show Tm.lam (Tm.app (rename (liftRen ρ) (rename wk u)) (.var (liftRen ρ 0))) =
    Tm.lam (Tm.app (rename wk (rename ρ u)) (.var 0))
  rw [rename_comp, rename_comp]
  rfl

/-- Applying an eta expansion beta-reduces to applying the term. -/
theorem app_etaOf {n : Nat} (u a : Tm Head n) :
    Conv rules.headEq (.app (etaOf u) a) (.app u a) rules.computation := by
  have reduce := StepCore.betaPi (root := rules.computation) (headEq := rules.headEq)
    (.app (rename wk u) (.var 0)) a
  have target : inst0 a (Tm.app (rename wk u) (.var 0)) = .app u a := by
    show Tm.app (inst0 a (rename wk u)) a = .app u a
    rw [inst0_rename_wk]
  rw [target] at reduce
  exact .rel _ _ reduce

/-- A unary head agrees applicatively with its eta expansion. -/
theorem appAgree_eta {n : Nat} (u : Tm Head n) :
    AppAgree (headEq := rules.headEq) (root := rules.computation) u (etaOf u) 1 := by
  intro k ρ w w' arguments
  show Conv rules.headEq (.app (rename ρ u) (w 0)) (.app (rename ρ (etaOf u)) (w' 0)) rules.computation
  rw [rename_etaOf]
  exact .trans _ _ _ (Conv.congApp (.refl _) (arguments 0)) (.symm _ _ (app_etaOf _ _))

/-- If `λx. u x` and `λx. v x` convert, `v` agrees applicatively with the eta expansion of `u`. -/
theorem appAgree_of_eta_conv (cr : ConversionCoherence.ChurchRosser rules)
    (noRoot : ∀ {n : Nat} (a b : Tm Head n), ¬ rules.computation.step a b) {n : Nat}
    {u v : Tm Head n} (same : Conv rules.headEq (etaOf u) (etaOf v) rules.computation) :
    AppAgree (headEq := rules.headEq) (root := rules.computation) v (etaOf u) 1 := by
  intro k ρ w w' arguments
  have bodies := conv_lam_inj cr noRoot same
  have moved := Conv.substitute (consSub (w 0) (renSub ρ)) bodies
  have unfold : ∀ t : Tm Head n,
      subst (consSub (w 0) (renSub ρ)) (Tm.app (rename wk t) (.var 0)) = .app (rename ρ t) (w 0) := by
    intro t
    show Tm.app (subst (consSub (w 0) (renSub ρ)) (rename wk t)) (w 0) = _
    rw [subst_consSub_rename_wk, subst_renSub]
  rw [unfold, unfold] at moved
  show Conv rules.headEq (.app (rename ρ v) (w 0)) (.app (rename ρ (etaOf u)) (w' 0))
    rules.computation
  exact .trans _ _ _ (.symm _ _ moved) (appAgree_eta u ρ w w' arguments)

end Eta

/-! ## The pattern equation on the image -/

section Pattern

variable {S : Binding.Signature} (names : BindingSignatureEmbedding.Names S)
  {rules : Rules Head} (realization : BindingSignatureEmbedding.Realization names rules)
  (s : S.Srt)

/-- A solution of the unary telescope by one term of type `Π s. s`. -/
def oneHom {Δ : Context rules} (u : Tm Head Δ.arity)
    (typed : FormationSensitive.Typing rules Δ.raw u (liftClosed (unaryType names s))) :
    Δ ⟶ ctxOf names realization (unaryFrame s) where
  substitution := consSub u (fun k => k.elim0)
  typed := by
    intro (i : Fin (unaryFrame s).length)
    show FormationSensitive.Typing rules Δ.raw _
      (subst _ (Ctx.lookup (metaCtx names (unaryFrame s)) i))
    rw [metaCtx_lookup, subst_liftClosed]
    refine Fin.cases ?_ (fun k => k.elim0) i
    exact typed

theorem liftN_outer_rename {k n : Nat} (σ : Sub Head k n) {p : Nat} (i : Fin k) :
    liftN σ p (outer i) = rename (fun i' => outer i') (σ i) :=
  (liftN_outer σ i).trans (subst_renSub _ _)

/-- A component of a solution into a translated telescope has the closed type of its
metavariable. -/
theorem hom_typed_closed {Δ : Context rules} {M : List (Binding.MetaArity S)}
    (τ : Δ ⟶ ctxOf names realization M) (i : Fin M.length) :
    FormationSensitive.Typing rules Δ.raw (τ.substitution i)
      (liftClosed (BindingSignatureEmbedding.bindingType names (M.get i).1 (M.get i).2)) := by
  have typed := τ.typed i
  change FormationSensitive.Typing rules Δ.raw (τ.substitution i)
    (subst τ.substitution (Ctx.lookup (metaCtx names M) i)) at typed
  rw [metaCtx_lookup, subst_liftClosed] at typed
  exact typed

theorem pattern_factors_core (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) {b : Context rules}
    (τ : b ⟶ ctxOf names realization (pairFrame s))
    (sound : Conv rules.headEq (etaOf (τ.substitution (mIdx s))) (etaOf (τ.substitution (nIdx s)))
      rules.computation) :
    ∃ residual : b ⟶ ctxOf names realization (unaryFrame s),
      ∀ o : Binding.ContextualFamily.Observation S (pairFrame s).get,
        Dependent.Entry.Convertible ((entry names realization o).reindex τ)
          ((entry names realization o).reindex (residual ≫ homOf names realization (collapse s))) := by
  have cr : ConversionCoherence.ChurchRosser rules :=
    EmptyRootConversion.churchRosser rules empty symmetric
  have noRoot : ∀ {n : Nat} (a c : Tm Head n), ¬ rules.computation.step a c := by
    intro n a c step
    rw [empty] at step
    exact step
  refine ⟨oneHom names realization s (τ.substitution (mIdx s))
    (hom_typed_closed names realization τ (mIdx s)), fun o => ?_⟩
  obtain ⟨Γ, sort, t⟩ := o
  refine ⟨?_, ?_⟩
  · show Conv rules.headEq
      (subst τ.substitution (liftClosed (BindingSignatureEmbedding.bindingType names Γ sort)))
      (subst _ (liftClosed (BindingSignatureEmbedding.bindingType names Γ sort))) rules.computation
    rw [subst_liftClosed, subst_liftClosed]
    exact .refl _
  · show Conv rules.headEq (subst τ.substitution (abstractN Γ.length (encode names (pairFrame s) t)))
      (subst (subComp (oneHom names realization s (τ.substitution (mIdx s))
          (hom_typed_closed names realization τ (mIdx s))).substitution
          (homCode names (pairFrame s) (unaryFrame s) (collapse s)))
        (abstractN Γ.length (encode names (pairFrame s) t))) rules.computation
    rw [subst_abstractN, subst_abstractN]
    refine conv_abstractN Γ.length
      (encode_conv_of_appAgree names (pairFrame s) t _ _ ⟨fun j => ?_, fun i => ?_⟩)
    · rw [liftN_inner, liftN_inner]
      exact .refl _
    · rw [liftN_outer_rename, liftN_outer_rename]
      apply AppAgree.renamed
      rcases i with ⟨_ | _ | k, bound⟩
      · exact appAgree_eta (τ.substitution (mIdx s))
      · exact appAgree_of_eta_conv cr noRoot sound
      · exact absurd bound (by simp)

/-- **On translated terms, the translated principal answer factors every solution** of the pattern
equation `m(x) ≐ n(x)`, through `g ↦ τ(m)`. -/
theorem pattern_factorsOnImage (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) :
    (translation names realization).FactorsOnImage (patternStore s)
      ((translation names realization).hom (collapse s)) :=
  fun _ τ solved => pattern_factors_core names realization s empty symmetric τ
    ((pattern_models_iff names realization s τ).mp solved)

/-- **At the pattern equation, asks of translated equation guards are preserved and reflected.** -/
theorem pattern_entails_iff (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq) (sortInjective : Function.Injective names.sort)
    (operatorInjective : ∀ {s : S.Srt}, Function.Injective (names.operator (sort := s)))
    (G : EquationStore (Binding.ContextualFamily.Observation S (pairFrame s).get)) :
    (Dependent.frames rules).Entails ((translation names realization).store (patternStore s))
        (fun _ g => (Dependent.frames rules).Models g ((translation names realization).store G)) ↔
      (listFrames S).Entails (a := pairFrame s) (patternStore s)
        (fun _ f => (listFrames S).Models f G) :=
  (translation names realization).entails_iff_of_factorsOnImage
    (translation_reflects names realization empty symmetric sortInjective @operatorInjective)
    (pattern_principal s) (pattern_factorsOnImage names realization s empty symmetric)

end Pattern

end Translation

#print axioms Translation.encode_conv_of_appAgree
#print axioms Translation.appAgree_eta
#print axioms Translation.appAgree_of_eta_conv
#print axioms Translation.pattern_factorsOnImage
#print axioms Translation.pattern_entails_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
