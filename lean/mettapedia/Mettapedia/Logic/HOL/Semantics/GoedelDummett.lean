import Mettapedia.Logic.HOL.Semantics.HeytingGeneral

/-!
# Gödel–Dummett HOL: the prelinearity extension and its Lindenbaum route

`ProvableLC` extends EM-free derivability by the prelinearity schema — both
closed instances `(φ → ψ) ∨ (ψ → φ)` and their single-binder universal
closures (the closures are what make fresh-parameter quantifier introduction
survive the schema's parameter-fullness).  The completeness argument mirrors
the intuitionistic Lindenbaum route; the one new ingredient is
*deduction compression*: a derivation from `T ∪ schema` is squeezed into an
implication from finitely many schema members over `T` alone, generalized
there by a fresh parameter, and recombined through derivable quantifier
distribution facts.
-/

namespace Mettapedia.Logic.HOL
namespace HeytingSem
namespace GoedelDummett

open Mettapedia.Logic.HOL.WithParams
open ClosedTheorySet

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Prelinearity shapes: prelinearity instances under arbitrary universal
closures, in any context.  Closure under abstraction (below) is why the depth
is unbounded. -/
inductive PrelinShape : {Γ : Ctx Base} → Formula (WithParams Const) Γ → Prop
  | base {Γ : Ctx Base} (A B : Formula (WithParams Const) Γ) :
      PrelinShape (.or (.imp A B) (.imp B A))
  | all {Γ : Ctx Base} {σ : Ty Base} {body : Formula (WithParams Const) (σ :: Γ)} :
      PrelinShape body → PrelinShape (.all body)

/-- The prelinearity schema: closed prelinearity shapes. -/
def lcSchema (Const : Ty Base → Type v) : ClosedTheorySet (WithParams Const) :=
  { χ | PrelinShape (Base := Base) χ }

/-- Abstraction preserves prelinearity shapes (index-cast induction). -/
theorem PrelinShape.abstract_aux {ρ : Ty Base} (c : WithParams Const ρ)
    {Γall : Ctx Base} {φ : Formula (WithParams Const) Γall}
    (h : PrelinShape (Base := Base) φ) :
    ∀ {Γ Ξ : Ctx Base} (hctx : Γall = Ξ ++ Γ),
      PrelinShape (Base := Base)
        (abstractConstAt (Base := Base) c Ξ (hctx ▸ φ)) := by
  induction h with
  | base A B =>
      intro Γ Ξ hctx
      subst hctx
      simp only [abstractConstAt]
      exact PrelinShape.base _ _
  | all h ih =>
      intro Γ Ξ hctx
      subst hctx
      simp only [abstractConstAt]
      exact PrelinShape.all (ih (Ξ := _ :: Ξ) rfl)

/-- Abstraction preserves prelinearity shapes. -/
theorem PrelinShape.abstract {Γ : Ctx Base} {ρ : Ty Base}
    (c : WithParams Const ρ) (Ξ : Ctx Base)
    {φ : Formula (WithParams Const) (Ξ ++ Γ)}
    (h : PrelinShape (Base := Base) φ) :
    PrelinShape (Base := Base) (abstractConstAt (Base := Base) c Ξ φ) :=
  PrelinShape.abstract_aux c h rfl

/-- Gödel–Dummett provability: derivability from the theory extended by the
prelinearity schema. -/
def ProvableLC (T : ClosedTheorySet (WithParams Const))
    (θ : ClosedFormula (WithParams Const)) : Prop :=
  ClosedTheorySet.Provable (Const := WithParams Const)
    (T ∪ lcSchema (Base := Base) Const) θ

/-- Iterated conjunction of a list of closed formulas. -/
def andList : List (ClosedFormula (WithParams Const)) →
    ClosedFormula (WithParams Const)
  | [] => .top
  | φ :: L => .and φ (andList L)

/-- **Deduction compression**: a derivation from `T ∪ S` factors as an
implication from a finite conjunction of `S`-members, derived over `T`
alone. -/
theorem provable_imp_andList_of_union
    {T S : ClosedTheorySet (WithParams Const)}
    {χ : ClosedFormula (WithParams Const)}
    (h : ClosedTheorySet.Provable (Const := WithParams Const) (T ∪ S) χ) :
    ∃ L : List (ClosedFormula (WithParams Const)),
      (∀ s ∈ L, s ∈ S) ∧
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.imp (andList (Base := Base) L) χ) := by
  classical
  obtain ⟨Γ, hΓ, d⟩ := h
  induction Γ generalizing χ with
  | nil =>
      refine ⟨[], by simp, ?_⟩
      exact ⟨[], by simp, ExtDerivation.impI
        (ExtDerivation.mono (by intro ξ hξ; cases hξ) d)⟩
  | cons ψ Γ' ih =>
      have hd' : ExtDerivation (WithParams Const) Γ' (.imp ψ χ) :=
        ExtDerivation.impI (ExtDerivation.mono
          (by
            intro ξ hξ
            rcases List.mem_cons.mp hξ with rfl | hξ
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ hξ) d)
      obtain ⟨L, hL, hImp⟩ := ih (fun ξ hξ => hΓ ξ (List.mem_cons_of_mem _ hξ)) hd'
      rcases hΓ ψ List.mem_cons_self with hT | hS
      · -- absorb the theory member
        refine ⟨L, hL, ?_⟩
        -- from T ⊢ andList L → (ψ → χ) and ψ ∈ T conclude T ⊢ andList L → χ
        rcases hImp with ⟨Γ₀, hΓ₀, d₀⟩
        refine ⟨ψ :: Γ₀, ?_, ?_⟩
        · intro ξ hξ
          rcases List.mem_cons.mp hξ with rfl | hξ
          · exact hT
          · exact hΓ₀ ξ hξ
        · refine ExtDerivation.impI ?_
          refine ExtDerivation.impE (φ := ψ) ?_ ?_
          · refine ExtDerivation.impE
              (φ := andList (Base := Base) L) ?_ (ExtDerivation.hyp List.mem_cons_self)
            exact ExtDerivation.mono
              (by intro ξ hξ; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hξ)) d₀
          · exact ExtDerivation.hyp
              (List.mem_cons_of_mem _ List.mem_cons_self)
      · -- push the schema member into the conjunction
        refine ⟨ψ :: L, ?_, ?_⟩
        · intro ξ hξ
          rcases List.mem_cons.mp hξ with rfl | hξ
          · exact hS
          · exact hL ξ hξ
        · rcases hImp with ⟨Γ₀, hΓ₀, d₀⟩
          refine ⟨Γ₀, hΓ₀, ?_⟩
          refine ExtDerivation.impI ?_
          have hand : ExtDerivation (WithParams Const)
              ((.and ψ (andList (Base := Base) L)) :: Γ₀)
              (.and ψ (andList (Base := Base) L)) :=
            ExtDerivation.hyp List.mem_cons_self
          refine ExtDerivation.impE (φ := ψ) ?_ (ExtDerivation.andEL hand)
          refine ExtDerivation.impE (φ := andList (Base := Base) L) ?_
            (ExtDerivation.andER hand)
          exact ExtDerivation.mono
            (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) d₀

/-- Hypotheses cut: replace every hypothesis of a derivation by a derivation
from another context. -/
theorem ExtDerivation.cut_hyps {Γ : Ctx Base}
    {Δ₁ Δ₂ : List (Formula (WithParams Const) Γ)}
    {χ : Formula (WithParams Const) Γ}
    (d : ExtDerivation (WithParams Const) Δ₁ χ)
    (e : ∀ ψ ∈ Δ₁, ExtDerivation (WithParams Const) Δ₂ ψ) :
    ExtDerivation (WithParams Const) Δ₂ χ := by
  induction Δ₁ generalizing χ with
  | nil => exact ExtDerivation.mono (by intro ξ hξ; cases hξ) d
  | cons ψ Δ₁' ih =>
      have dimp : ExtDerivation (WithParams Const) Δ₁' (.imp ψ χ) :=
        ExtDerivation.impI (ExtDerivation.mono
          (by
            intro ξ hξ
            rcases List.mem_cons.mp hξ with rfl | hξ
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ hξ) d)
      exact ExtDerivation.impE
        (ih dimp (fun ξ hξ => e ξ (List.mem_cons_of_mem _ hξ)))
        (e ψ List.mem_cons_self)

/-- Instantiating a weakened one-variable formula at the bound variable is the
identity. -/
theorem instantiate_var_vz_rename_lift_weaken {σ' : Ty Base}
    (A : Formula (WithParams Const) [σ']) :
    instantiate (Base := Base) (.var .vz)
        (rename (Rename.lift (Rename.weaken (Base := Base) (Γ := ([] : Ctx Base)) (σ := σ'))) A)
      = A := by
  unfold instantiate
  rw [subst_rename (Base := Base) (Const := WithParams Const)]
  exact ((subst_ext (fun v => by cases v with
    | vz => rfl
    | vs v => cases v) A).trans (subst_id (Base := Base) A))

/-- **The crux**: fresh-parameter universal introduction over a parameter-free
theory extended by the prelinearity schema.  The witnessing derivation is
abstracted wholesale; parameter-free hypotheses become weakenings, and schema
hypotheses — which may mention the fresh parameter — abstract to open
prelinearity shapes that are recovered from their universal closures (schema
members again) by instantiation at the bound variable. -/
theorem lc_all_intro_of_instances
    {T : ClosedTheorySet (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    {σ' : Ty Base} {φb : Formula (WithParams Const) [σ']}
    {ω : ClosedFormula (WithParams Const)}
    (h : ∀ t : ClosedTerm (WithParams Const) σ',
      ClosedTheorySet.Provable (Const := WithParams Const)
        (insert ω (T ∪ lcSchema (Base := Base) Const))
        (instantiate (Base := Base) t φb)) :
    ClosedTheorySet.Provable (Const := WithParams Const)
      (insert ω (T ∪ lcSchema (Base := Base) Const)) (.all φb) := by
  classical
  set k := max (maxParam ω) (maxParam φb) with hk
  set c₀ : WithParams Const σ' := param σ' k with hc₀
  have hωfresh : NoConstOccurrence c₀ ω :=
    noConstOccurrence_param_of_ge k ω (le_max_left _ _)
  have hφfresh : NoConstOccurrence c₀ φb :=
    noConstOccurrence_param_of_ge k φb (le_max_right _ _)
  obtain ⟨Γ, hΓ, d⟩ := h (.const c₀)
  have key := ExtDerivation.abstractConstAt_deriv (Γ := ([] : Ctx Base)) (Ξ := []) c₀ d
  have key' := (abstractConstAt_nil_instantiate_const c₀ φb hφfresh) ▸ key
  -- final closed hypothesis list: schema members are replaced by the
  -- universal closures of their abstractions
  refine ⟨Γ.map (fun ψ =>
    if PrelinShape (Base := Base) ψ
    then .all (abstractConstAt (Base := Base) c₀ [] ψ) else ψ), ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_map.mp hξ with ⟨ψ, hψ, rfl⟩
    by_cases hs : PrelinShape (Base := Base) ψ
    · simp only [hs, if_true]
      exact Set.mem_insert_of_mem _ (Set.mem_union_right _
        (PrelinShape.all (PrelinShape.abstract c₀ [] hs)))
    · simp only [hs, if_false]
      exact hΓ ψ hψ
  · refine ExtDerivation.allI ?_
    refine ExtDerivation.cut_hyps (Δ₁ := Γ.map (abstractConstAt (Base := Base) c₀ [])) key' ?_
    intro ξ hξ
    rcases List.mem_map.mp hξ with ⟨ψ, hψ, rfl⟩
    by_cases hs : PrelinShape (Base := Base) ψ
    · -- schema hypothesis: recover the open shape from its universal closure
      have hmem : (weaken (Base := Base) (σ := σ')
            (.all (abstractConstAt (Base := Base) c₀ [] ψ))
          : Formula (WithParams Const) [σ']) ∈
          weakenHyps (Base := Base) (σ := σ') (Γ.map (fun ψ =>
            if PrelinShape (Base := Base) ψ
            then .all (abstractConstAt (Base := Base) c₀ [] ψ) else ψ)) := by
        unfold weakenHyps
        refine List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨ψ, hψ, ?_⟩, rfl⟩
        simp only [hs, if_true]
      have hall := ExtDerivation.allE (Const := WithParams Const)
        (φ := rename (Rename.lift (Rename.weaken (Base := Base)
            (Γ := ([] : Ctx Base)) (σ := σ')))
          (abstractConstAt (Base := Base) c₀ [] ψ))
        (.var .vz) (ExtDerivation.hyp hmem)
      rwa [instantiate_var_vz_rename_lift_weaken] at hall
    · -- parameter-free hypothesis: its abstraction is its weakening
      have hfresh : NoConstOccurrence c₀ ψ := by
        rcases Set.mem_insert_iff.mp (hΓ ψ hψ) with rfl | hTS
        · exact hωfresh
        · rcases hTS with hT | hS
          · exact hT0 ψ hT σ' k
          · exact absurd hS hs
      have habs : abstractConstAt (Base := Base) c₀ [] ψ
          = weaken (Base := Base) (σ := σ') ψ :=
        abstractConstAt_noOccurrence (c := c₀) [] ψ hfresh
      rw [habs]
      refine ExtDerivation.hyp ?_
      unfold weakenHyps
      refine List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨ψ, hψ, ?_⟩, rfl⟩
      simp only [hs, if_false]

/-- Substitution preserves prelinearity shapes. -/
theorem PrelinShape.subst_preserve {Γall : Ctx Base}
    {φ : Formula (WithParams Const) Γall}
    (h : PrelinShape (Base := Base) φ) :
    ∀ {Δ : Ctx Base} (σs : Subst (WithParams Const) Γall Δ),
      PrelinShape (Base := Base) (subst σs φ) := by
  induction h with
  | base A B =>
      intro Δ σs
      simp only [subst]
      exact PrelinShape.base _ _
  | all h ih =>
      intro Δ σs
      simp only [subst]
      exact PrelinShape.all (ih _)

/-- Every closed prelinearity shape is top-valued in every prelinear
Heyting-valued model. -/
theorem prelinShape_valid (M : HeytingGeneralModel Base (WithParams Const))
    (hpre : ∀ a b : M.Ω, M.le M.top (M.sup (M.himp a b) (M.himp b a))) :
    ∀ {Γall : Ctx Base} {φ : Formula (WithParams Const) Γall},
      PrelinShape (Base := Base) φ →
      ∀ (σs : Subst (WithParams Const) Γall []),
        M.le M.top (M.val (subst σs φ)) := by
  intro Γall φ h
  induction h with
  | base A B =>
      intro σs
      show M.le M.top (M.val (.or (.imp (subst σs A) (subst σs B))
        (.imp (subst σs B) (subst σs A))))
      rw [M.val_or, M.val_imp, M.val_imp]
      exact hpre _ _
  | all h ih =>
      intro σs
      show M.le M.top (M.val (.all (subst (Subst.lift σs) _)))
      refine M.le_val_all _ _ (fun t => ?_)
      rw [KripkeHenkin.ClosedEnv.instantiate_subst_lift_extend
        (Base := Base) (Const := WithParams Const) (ρ := σs) (t := t)]
      exact ih _

/-- The Lindenbaum model of the schema-extended theory: values are closed
formulas, order is derivability over `T ∪ lcSchema`, and quantifier exactness
is carried by the schema-aware fresh-parameter introduction. -/
noncomputable def lindenbaumLCModel (T : ClosedTheorySet (WithParams Const))
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    HeytingGeneralModel Base (WithParams Const) :=
  Lindenbaum.lindenbaumModelOfAllIntro (Base := Base)
    (T ∪ lcSchema (Base := Base) Const)
    (fun {σ' φb ω} h => lc_all_intro_of_instances (Base := Base) hT0 h)

/-- The Lindenbaum-LC model is prelinear: prelinearity instances are schema
members. -/
theorem lindenbaumLCModel_prelinear (T : ClosedTheorySet (WithParams Const))
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (a b : (lindenbaumLCModel (Base := Base) T hT0).Ω) :
    (lindenbaumLCModel (Base := Base) T hT0).le
      (lindenbaumLCModel (Base := Base) T hT0).top
      ((lindenbaumLCModel (Base := Base) T hT0).sup
        ((lindenbaumLCModel (Base := Base) T hT0).himp a b)
        ((lindenbaumLCModel (Base := Base) T hT0).himp b a)) :=
  ClosedTheorySet.provable_of_mem (Const := WithParams Const)
    (Set.mem_insert_of_mem _ (Set.mem_union_right _ (PrelinShape.base a b)))

/-- Semantic consequence over all prelinear Heyting-valued models. -/
def PrelinearHeytingConsequence (T : ClosedTheorySet (WithParams Const))
    (θ : ClosedFormula (WithParams Const)) : Prop :=
  ∀ M : HeytingGeneralModel.{u, v, max u v} Base (WithParams Const),
    (∀ a b : M.Ω, M.le M.top (M.sup (M.himp a b) (M.himp b a))) →
    (∀ ψ ∈ T, M.le M.top (M.val ψ)) → M.le M.top (M.val θ)

/-- Soundness: LC-provability implies prelinear semantic consequence. -/
theorem prelinearHeytingConsequence_of_provableLC
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (h : ProvableLC (Base := Base) T θ) :
    PrelinearHeytingConsequence (Base := Base) T θ := by
  intro M hpre hT
  refine heytingConsequence_of_provable (Base := Base) h M ?_
  intro ψ hψ
  rcases hψ with hTm | hS
  · exact hT ψ hTm
  · have := prelinShape_valid (Base := Base) M hpre hS
      (emptySubst (Base := Base) (Const := WithParams Const))
    rwa [KripkeHenkin.ClosedEnv.subst_empty (Base := Base)
      (Const := WithParams Const) _ ψ] at this

/-- Completeness: prelinear semantic consequence over a parameter-free theory
is LC-provable, via the prelinear Lindenbaum-LC countermodel. -/
theorem provableLC_of_prelinearHeytingConsequence
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ)
    (hSem : PrelinearHeytingConsequence (Base := Base) T θ) :
    ProvableLC (Base := Base) T θ := by
  classical
  have hLin := hSem (lindenbaumLCModel (Base := Base) T hT0)
    (lindenbaumLCModel_prelinear (Base := Base) T hT0)
    (fun ψ hψ => Lindenbaum.provable_mono (Set.subset_insert _ _)
      (ClosedTheorySet.provable_of_mem (Const := WithParams Const)
        (Set.mem_union_left _ hψ)))
  exact Lindenbaum.provable_cut hLin
    (ClosedTheorySet.provable_top (Const := WithParams Const) _)

/-- **Gödel–Dummett HOL completeness**: for parameter-free theories,
LC-provability coincides with semantic consequence over all prelinear
Heyting-valued models. -/
theorem provableLC_iff_prelinearHeytingConsequence_param_free
    {T : ClosedTheorySet (WithParams Const)}
    {θ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ k : WithParams Const σ) ψ) :
    ProvableLC (Base := Base) T θ ↔
      PrelinearHeytingConsequence (Base := Base) T θ :=
  ⟨prelinearHeytingConsequence_of_provableLC (Base := Base),
    provableLC_of_prelinearHeytingConsequence (Base := Base) hT0⟩

/-- Positive example: prelinearity itself is LC-provable (a schema member),
for any pair of closed formulas. -/
theorem provableLC_prelinearity (T : ClosedTheorySet (WithParams Const))
    (φ ψ : ClosedFormula (WithParams Const)) :
    ProvableLC (Base := Base) T (.or (.imp φ ψ) (.imp ψ φ)) :=
  ClosedTheorySet.provable_of_mem (Const := WithParams Const)
    (Set.mem_union_right _ (PrelinShape.base φ ψ))

end GoedelDummett
end HeytingSem
end Mettapedia.Logic.HOL
