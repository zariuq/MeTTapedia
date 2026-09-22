import Mettapedia.Languages.OpenTheory.EtaCompleteness

/-!
# Heyting-valued completeness over the OpenTheory target signature

`EtaCompleteness.lean` states Heyting-valued completeness over the target
signature extended by parameters.  This module removes the parameters from
the statement: for a closed theory whose variable symbols have names from a
finite list, derivability is consequence over all Heyting-valued
substitutional models of the target signature `Symbol` itself.  The finite
hypothesis sets of OpenTheory sequents qualify
(`variableNamesBounded_translatedHypotheses`), so

* `kernelProvable_etaAxiomPolicy_iff_heytingConsequence`: for a
  sequent with Boolean hypotheses, kernel provability under `etaAxiomPolicy`
  is consequence of the translated hypotheses over all Heyting-valued models
  of `Symbol`, the semantics of the soundness theorem
  `derives_heytingConsequence`.

## Construction

The Lindenbaum model of the embedded theory over `WithParams Symbol` is
restricted to `Symbol`: the values are the same, and a formula is valued by
its embedding (`symbolLindenbaumModel`).  Every valuation law transfers along
the embedding except the three laws that quantify over closed terms (`∀`,
`∃`, and equality of abstractions), which now range over `Symbol`-terms only.
They hold because `Symbol` has infinitely many variable symbols at every type:
an instance at a variable symbol named by no symbol of the theory, the
hypothesis or the body generalizes (`provable_all_of_symbolInstances`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic
open ReverseTranslation

namespace EtaCompleteness

/-! ## Constant occurrence under constant maps -/

section ConstMap

universe u v w

variable {Base : Type u} {Const : HOL.Ty Base → Type v} {Const' : HOL.Ty Base → Type w}

/-- A constant map reflects absence: if the image of `c` does not occur in the
image of `t`, then `c` does not occur in `t`. -/
theorem noConstOccurrence_of_mapConst (f : ∀ {τ : HOL.Ty Base}, Const τ → Const' τ)
    {σ : HOL.Ty Base} {c : Const σ} :
    ∀ {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (t : HOL.Term Const Γ τ),
      HOL.NoConstOccurrence (f c) (HOL.mapConst f t) → HOL.NoConstOccurrence c t
  | _, _, .var _, _ => .var
  | _, ρ, .const d, h => by
      by_cases hty : σ = ρ
      · subst hty
        refine .const_same_ne d fun hd => ?_
        subst hd
        cases h with
        | const_diff_type hne => exact hne rfl
        | const_same_ne _ hne => exact hne rfl
      · exact .const_diff_type hty d
  | _, _, .app g t, h => by
      cases h with
      | app hg ht =>
          exact .app (noConstOccurrence_of_mapConst f g hg) (noConstOccurrence_of_mapConst f t ht)
  | _, _, .lam t, h => by
      cases h with
      | lam ht => exact .lam (noConstOccurrence_of_mapConst f t ht)
  | _, _, .top, _ => .top
  | _, _, .bot, _ => .bot
  | _, _, .and p q, h => by
      cases h with
      | and hp hq =>
          exact .and (noConstOccurrence_of_mapConst f p hp) (noConstOccurrence_of_mapConst f q hq)
  | _, _, .or p q, h => by
      cases h with
      | or hp hq =>
          exact .or (noConstOccurrence_of_mapConst f p hp) (noConstOccurrence_of_mapConst f q hq)
  | _, _, .imp p q, h => by
      cases h with
      | imp hp hq =>
          exact .imp (noConstOccurrence_of_mapConst f p hp) (noConstOccurrence_of_mapConst f q hq)
  | _, _, .not p, h => by
      cases h with
      | not hp => exact .not (noConstOccurrence_of_mapConst f p hp)
  | _, _, .eq t u, h => by
      cases h with
      | eq ht hu =>
          exact .eq (noConstOccurrence_of_mapConst f t ht) (noConstOccurrence_of_mapConst f u hu)
  | _, _, .all p, h => by
      cases h with
      | all hp => exact .all (noConstOccurrence_of_mapConst f p hp)
  | _, _, .ex p, h => by
      cases h with
      | ex hp => exact .ex (noConstOccurrence_of_mapConst f p hp)

theorem embedParams_instantiate {Γ : HOL.Ctx Base} {σ τ : HOL.Ty Base}
    (t : HOL.Term Const Γ σ) (u : HOL.Term Const (σ :: Γ) τ) :
    embedParams (HOL.instantiate t u) = HOL.instantiate (embedParams t) (embedParams u) :=
  HOL.mapConst_instantiate _ t u

theorem embedParams_weaken {Γ : HOL.Ctx Base} {σ τ : HOL.Ty Base} (t : HOL.Term Const Γ τ) :
    embedParams (HOL.weaken (σ := σ) t) = HOL.weaken (embedParams t) :=
  HOL.mapConst_weaken _ t

end ConstMap

/-! ## Variable symbols of translations and theories -/

/-- The translation of a term mentions the variable symbol of a source
variable only if the variable is free in the term. -/
theorem noConstOccurrence_ofVar_of_translates {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {τ : HOL.Ty AtomicTy} {target : HOL.Term Symbol Γ τ}
    (translation : Translates Γ term τ target) (sourceVar : SourceVar)
    (absent : ¬ DBTerm.FreeOccurrence sourceVar term) :
    HOL.NoConstOccurrence (Symbol.ofVar sourceVar) target := by
  induction translation with
  | equality => exact .lam (.lam (.eq .var .var))
  | constant _ typed =>
      exact Symbol.noConstOccurrence_const _ _ (Symbol.sigma_constant_ne_ofVar _ _ typed _)
  | @free _ other _ typed =>
      have different : other ≠ sourceVar := by
        rintro rfl
        exact absent .here
      exact Symbol.noConstOccurrence_const _ _ (Symbol.sigma_variable_ne_ofVar typed different)
  | bound => exact .var
  | equalityApp _ _ _ _ leftIH rightIH =>
      exact .eq (leftIH fun found => absent (.appFunction (.appArgument found)))
        (rightIH fun found => absent (.appArgument found))
  | app _ _ _ functionIH argumentIH =>
      exact .app (functionIH fun found => absent (.appFunction found))
        (argumentIH fun found => absent (.appArgument found))
  | abs _ _ bodyIH =>
      exact .lam (bodyIH fun found => absent (.absBody found))

/-- Every variable symbol of the theory has its name in a finite list. -/
def VariableNamesBounded (T : HOL.ClosedTheorySet Symbol) : Prop :=
  ∃ bound : List Name, ∀ ψ ∈ T, ∀ name ∉ bound, ∀ ty : Ty,
    HOL.NoConstOccurrence (Symbol.ofVar ⟨name, ty⟩) ψ

/-- The translated hypotheses of a finite hypothesis set mention only the
names of its free variables. -/
theorem variableNamesBounded_translatedHypotheses (hyp : Finset CanonicalTerm) :
    VariableNamesBounded (translatedHypotheses hyp) :=
  ⟨(hypothesesFreeNames hyp).toList, fun _ ⟨term, member, translation⟩ _ fresh _ =>
    noConstOccurrence_ofVar_of_translates translation _ fun found =>
      fresh (Finset.mem_toList.mpr
        (Finset.mem_biUnion.mpr ⟨term, member, DBTerm.name_mem_freeNames found⟩))⟩

/-! ## Generalization at variable symbols -/

/-- **Generalization from the `Symbol`-instances.**  Over the embedding of a
theory with boundedly many variable-symbol names, if every instance of a body
at a closed `Symbol`-term is provable from `ω`, so is its universal closure:
the instance at a variable symbol named by nothing in sight generalizes. -/
theorem provable_all_of_symbolInstances {T : HOL.ClosedTheorySet Symbol}
    (bounded : VariableNamesBounded T) {σ : HOL.Ty AtomicTy}
    {body : HOL.Formula (HOL.WithParams Symbol) [σ]}
    {ω : HOL.ClosedFormula (HOL.WithParams Symbol)}
    (instances : ∀ t : HOL.ClosedTerm Symbol σ,
      HOL.ClosedTheorySet.Provable (insert ω (embedParams '' T))
        (HOL.instantiate (embedParams t) body)) :
    HOL.ClosedTheorySet.Provable (insert ω (embedParams '' T)) (.all body) := by
  obtain ⟨bound, hbound⟩ := bounded
  obtain ⟨ty, rfl⟩ := Ty.toHOL_surjective σ
  let avoid := bound ++ variableSymbolNames (HOL.mapConst (eraseParams paramSymbol) ω) ++
    variableSymbolNames (HOL.mapConst (eraseParams paramSymbol) body)
  have fresh := freshName_not_mem avoid
  simp only [avoid, List.mem_append, not_or] at fresh
  let variable' : Symbol ty.toHOL := Symbol.ofVar ⟨freshName avoid, ty⟩
  have absent : ∀ {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy}
      (t : HOL.Term (HOL.WithParams Symbol) Γ τ),
      freshName avoid ∉ variableSymbolNames (HOL.mapConst (eraseParams paramSymbol) t) →
        HOL.NoConstOccurrence (HOL.WithParams.inj variable') t := fun t hname =>
    noConstOccurrence_of_mapConst (eraseParams paramSymbol) t
      (noConstOccurrence_of_not_mem_variableSymbolNames ty _ hname)
  refine HOL.ClosedTheorySet.provable_all_intro_fresh (HOL.WithParams.inj variable') ?_
    (absent body fresh.2) (instances (.const variable'))
  intro ψ member
  rcases Set.mem_insert_iff.mp member with rfl | ⟨ψ₀, hψ₀, rfl⟩
  · exact absent ψ fresh.1.2
  · refine noConstOccurrence_of_mapConst (eraseParams paramSymbol) (embedParams ψ₀) ?_
    rw [mapConst_eraseParams_embedParams]
    exact hbound ψ₀ hψ₀ _ fresh.1.1 ty

/-- The existential law of the restricted model: if every instance at a
closed `Symbol`-term proves `ω`, so does the existential. -/
theorem provable_insert_ex_of_symbolInstances {T : HOL.ClosedTheorySet Symbol}
    (bounded : VariableNamesBounded T) {σ : HOL.Ty AtomicTy} (φ : HOL.Formula Symbol [σ])
    (ω : HOL.ClosedFormula (HOL.WithParams Symbol))
    (instances : ∀ t : HOL.ClosedTerm Symbol σ, HOL.ClosedTheorySet.Provable
      (insert (embedParams (HOL.instantiate t φ)) (embedParams '' T)) ω) :
    HOL.ClosedTheorySet.Provable (insert (.ex (embedParams φ)) (embedParams '' T)) ω := by
  refine HOL.provable_of_ex_and_all_imp
    (HOL.ClosedTheorySet.provable_of_mem (Set.mem_insert _ _)) ?_
  refine provable_all_of_symbolInstances bounded fun t => ?_
  have hinst : HOL.instantiate (embedParams t) (.imp (embedParams φ) (HOL.weaken ω)) =
      .imp (embedParams (HOL.instantiate t φ)) ω := by
    rw [embedParams_instantiate]
    show HOL.Term.imp _ (HOL.instantiate (embedParams t) (HOL.weaken ω)) = _
    rw [HOL.instantiate_weaken]
    rfl
  rw [hinst]
  refine HOL.provable_imp_of_insert ?_
  exact HOL.HeytingSem.Lindenbaum.provable_mono
    (Set.insert_subset_insert (Set.subset_insert _ _)) (instances t)

/-- The law for equality of abstractions in the restricted model: if every
instance at a closed `Symbol`-term of the bodies' equation follows from `ω`,
so does the equation of the abstractions. -/
theorem provable_eq_lam_of_symbolInstances {T : HOL.ClosedTheorySet Symbol}
    (bounded : VariableNamesBounded T) {σ τ : HOL.Ty AtomicTy}
    (t u : HOL.Term Symbol [σ] τ) (ω : HOL.ClosedFormula (HOL.WithParams Symbol))
    (instances : ∀ w : HOL.ClosedTerm Symbol σ, HOL.ClosedTheorySet.Provable
      (insert ω (embedParams '' T))
      (embedParams (.eq (HOL.instantiate w t) (HOL.instantiate w u)))) :
    HOL.ClosedTheorySet.Provable (insert ω (embedParams '' T))
      (.eq (.lam (embedParams t)) (.lam (embedParams u))) := by
  refine HOL.HeytingSem.Lindenbaum.provable_funExt ?_
  refine provable_all_of_symbolInstances bounded fun w => ?_
  have hshape : HOL.instantiate (embedParams w)
      (.eq (.app (HOL.weaken (σ := σ) (.lam (embedParams t))) (.var .vz))
        (.app (HOL.weaken (σ := σ) (.lam (embedParams u))) (.var .vz)) :
        HOL.Formula (HOL.WithParams Symbol) [σ]) =
      .eq (.app (.lam (embedParams t)) (embedParams w))
        (.app (.lam (embedParams u)) (embedParams w)) := by
    show HOL.Term.eq
        (.app (HOL.instantiate (embedParams w) (HOL.weaken (σ := σ) (.lam (embedParams t))))
          (HOL.instantiate (embedParams w) (.var .vz)))
        (.app (HOL.instantiate (embedParams w) (HOL.weaken (σ := σ) (.lam (embedParams u))))
          (HOL.instantiate (embedParams w) (.var .vz))) = _
    simp only [HOL.instantiate_weaken, HOL.instantiate_var_vz]
  rw [hshape]
  obtain ⟨premises, hpremises, derivation⟩ := instances w
  refine ⟨premises, hpremises, ?_⟩
  have heq : embedParams (HOL.Term.eq (HOL.instantiate w t) (HOL.instantiate w u)) =
      .eq (HOL.instantiate (embedParams w) (embedParams t))
        (HOL.instantiate (embedParams w) (embedParams u)) := by
    show HOL.Term.eq (embedParams (HOL.instantiate w t)) (embedParams (HOL.instantiate w u)) = _
    rw [embedParams_instantiate, embedParams_instantiate]
  rw [heq] at derivation
  exact .eqTrans (.beta _ _) (.eqTrans derivation (.eqSymm (.beta _ _)))

/-! ## The restricted Lindenbaum model -/

theorem embedParams_image_paramFree (T : HOL.ClosedTheorySet Symbol) :
    ∀ ψ ∈ embedParams '' T, ∀ (σ : HOL.Ty AtomicTy) (index : Nat),
      HOL.NoConstOccurrence (HOL.WithParams.param σ index : HOL.WithParams Symbol σ) ψ := by
  rintro ψ ⟨ψ₀, -, rfl⟩ σ index
  exact HOL.WithParams.noConstOccurrence_param_of_inj index ψ₀

/-- The Lindenbaum model of the embedded theory, restricted to the target
signature: a formula is valued by its embedding. -/
noncomputable def symbolLindenbaumModel (T : HOL.ClosedTheorySet Symbol)
    (bounded : VariableNamesBounded T) : HOL.HeytingSem.HeytingGeneralModel AtomicTy Symbol :=
  let L := HOL.HeytingSem.Lindenbaum.lindenbaumModel (embedParams '' T)
    (embedParams_image_paramFree T)
  { L with
    val := fun ψ => embedParams ψ
    val_top := rfl
    val_bot := rfl
    val_and := fun _ _ => rfl
    val_or := fun _ _ => rfl
    val_imp := fun _ _ => rfl
    val_not_le := fun φ => L.val_not_le (embedParams φ)
    le_val_not := fun φ => L.le_val_not (embedParams φ)
    val_all_le := fun φ t => by
      show L.le (embedParams (.all φ)) (embedParams (HOL.instantiate t φ))
      rw [embedParams_instantiate]
      exact L.val_all_le (embedParams φ) (embedParams t)
    le_val_all := fun φ ω h => provable_all_of_symbolInstances bounded fun t => by
      have ht : L.le ω (embedParams (HOL.instantiate t φ)) := h t
      rw [embedParams_instantiate] at ht
      exact ht
    val_ex_le := fun φ ω h => provable_insert_ex_of_symbolInstances bounded φ ω h
    le_val_ex := fun φ t => by
      show L.le (embedParams (HOL.instantiate t φ)) (embedParams (.ex φ))
      rw [embedParams_instantiate]
      exact L.le_val_ex (embedParams φ) (embedParams t)
    val_eq_refl := fun t => L.val_eq_refl (embedParams t)
    val_eq_symm := fun t u => L.val_eq_symm (embedParams t) (embedParams u)
    val_eq_trans := fun t u v => L.val_eq_trans (embedParams t) (embedParams u) (embedParams v)
    val_eq_app := fun f g t => L.val_eq_app (embedParams f) (embedParams g) (embedParams t)
    val_eq_appArg := fun f t u => L.val_eq_appArg (embedParams f) (embedParams t) (embedParams u)
    val_eq_propI := fun p q => L.val_eq_propI (embedParams p) (embedParams q)
    val_eq_propEL := fun p q => L.val_eq_propEL (embedParams p) (embedParams q)
    val_eq_propER := fun p q => L.val_eq_propER (embedParams p) (embedParams q)
    val_eq_lam := fun t u ω h => provable_eq_lam_of_symbolInstances bounded t u ω h
    val_funExt := fun {σ _} f g => by
      show L.le
        (.all (.eq (.app (embedParams (HOL.weaken (σ := σ) f)) (.var .vz))
          (.app (embedParams (HOL.weaken (σ := σ) g)) (.var .vz))))
        (.eq (embedParams f) (embedParams g))
      rw [embedParams_weaken, embedParams_weaken]
      exact L.val_funExt (embedParams f) (embedParams g)
    val_beta := fun t u => by
      show L.le L.top (.eq (.app (.lam (embedParams u)) (embedParams t))
        (embedParams (HOL.instantiate t u)))
      rw [embedParams_instantiate]
      exact L.val_beta (embedParams t) (embedParams u)
    val_eta := fun {σ _} f => by
      show L.le L.top (.eq (.lam (.app (embedParams (HOL.weaken (σ := σ) f)) (.var .vz)))
        (embedParams f))
      rw [embedParams_weaken]
      exact L.val_eta (embedParams f) }

/-! ## Completeness -/

/-- **Heyting-valued completeness over the target signature.**  For a closed
theory with boundedly many variable-symbol names, a consequence over all
Heyting-valued substitutional models of `Symbol` is derivable. -/
theorem provable_of_heytingConsequence {T : HOL.ClosedTheorySet Symbol}
    (bounded : VariableNamesBounded T) {φ : HOL.ClosedFormula Symbol}
    (consequence : HOL.HeytingSem.HeytingConsequence (Base := AtomicTy) T φ) :
    HOL.ClosedTheorySet.Provable T φ := by
  have holds := consequence (symbolLindenbaumModel T bounded) fun ψ member =>
    HOL.ClosedTheorySet.provable_of_mem (Set.mem_insert_of_mem _ ⟨ψ, member, rfl⟩)
  exact (provable_iff_provable_withParams paramSymbol).mpr
    (HOL.HeytingSem.Lindenbaum.provable_cut holds (HOL.ClosedTheorySet.provable_top _))

theorem provable_iff_heytingConsequence {T : HOL.ClosedTheorySet Symbol}
    (bounded : VariableNamesBounded T) {φ : HOL.ClosedFormula Symbol} :
    HOL.ClosedTheorySet.Provable T φ ↔ HOL.HeytingSem.HeytingConsequence (Base := AtomicTy) T φ :=
  ⟨HOL.HeytingSem.heytingConsequence_of_provable, provable_of_heytingConsequence bounded⟩

/-- **Heyting-valued soundness and completeness of the OpenTheory kernel with
eta.**  For a sequent with Boolean hypotheses and the translation `φ` of its
conclusion, kernel provability under `etaAxiomPolicy` is consequence of the
translated hypotheses over all Heyting-valued substitutional models of the
target signature. -/
theorem kernelProvable_etaAxiomPolicy_iff_heytingConsequence {sequent : Sequent}
    (hypBool : ∀ term ∈ sequent.hyp, term.IsBool) {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] sequent.concl.term .prop φ) :
    KernelProvable etaAxiomPolicy sequent.hyp sequent.concl.term ↔
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (translatedHypotheses sequent.hyp) φ := by
  rw [kernelProvable_etaAxiomPolicy_iff_translatedProvable hypBool,
    ← provable_iff_heytingConsequence (variableNamesBounded_translatedHypotheses sequent.hyp)]
  constructor
  · intro provable
    have hprovable := provable.provable translation
    rwa [Set.empty_union] at hprovable
  · intro provable
    exact ⟨φ, translation, by rwa [Set.empty_union]⟩

end EtaCompleteness

/-! ## Controls -/

namespace EtaCompletenessHeytingExamples

open EtaCompleteness ExcludedMiddle

/-- **Negative control.**  Excluded middle `⊢ ∀ p. p ∨ ¬ p` is not
kernel-provable even with the eta axiom. -/
theorem excludedMiddle_not_kernelProvable_etaAxiomPolicy :
    ¬ KernelProvable etaAxiomPolicy ∅ excludedMiddleDB := by
  intro h
  obtain ⟨φ, hφ, premises, hpremises, derivation⟩ :=
    translatedProvable_of_kernelProvable (sequent := ⟨∅, excludedMiddleTerm⟩)
      etaAxiomPolicy_translatedProvable h
  obtain rfl : φ = excludedMiddleDefinition := hφ.unique_eq (excludedMiddleDB_translates [])
  refine not_extDerivation_excludedMiddleDefinition
    (HOL.ExtDerivation.mono (fun {χ} hχ => ?_) derivation)
  rcases hpremises χ hχ with hempty | ⟨term, hterm, _⟩
  · exact absurd hempty (Set.notMem_empty _)
  · exact absurd hterm (Finset.notMem_empty _)

/-- Hence some Heyting-valued model of the target signature refutes the
translation of excluded middle. -/
theorem not_heytingConsequence_excludedMiddleDefinition :
    ¬ HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
      (∅ : HOL.ClosedTheorySet Symbol) excludedMiddleDefinition := by
  intro consequence
  refine excludedMiddle_not_kernelProvable_etaAxiomPolicy
    ((kernelProvable_etaAxiomPolicy_iff_heytingConsequence
      (sequent := ⟨∅, excludedMiddleTerm⟩)
      (fun _ member => absurd member (Finset.notMem_empty _))
      (excludedMiddleDB_translates [])).mpr ?_)
  simpa [translatedHypotheses] using consequence

end EtaCompletenessHeytingExamples

end Mettapedia.Languages.OpenTheory
