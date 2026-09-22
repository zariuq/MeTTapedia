import Mettapedia.Languages.OpenTheory.DerivedRulesEta
import Mettapedia.Languages.OpenTheory.ReverseTranslation

/-!
# The rules of extensional higher-order logic in the OpenTheory kernel

Every rule of the extensional calculus `HOL.ExtDerivation` is admissible in the
OpenTheory primitive kernel under any axiom policy that admits the eta sequent
`EtaAxiom.sequent`, through the reverse translation of `ReverseTranslation.lean`:

* `kernelProvable_reverse_of_extDerivation`: if `Δ ⊢ φ` is derivable in
  context `Γ`, then for every naming of `Γ` the reversed sequent
  `reverseHypotheses names Δ ⊢ reverseTerm names φ` is kernel-provable.

The naming need not be injective: a naming that identifies two context
variables reverses a derivation to an instance of it, and every rule is
uniform in its terms.

Rule by rule:

* connectives: the derived natural-deduction rules of
  `DerivedRulesConnectives.lean`, whose connective applications are exactly
  the images of the reverse translation;
* `allI`, `exE`, `eqLam`: GEN, CHOOSE and ABS at a variable whose name is
  avoided by the naming and by every variable symbol involved
  (`exists_fresh_name`);
* `allE`, `exI`, `beta`: SPEC, EXISTS and BETA_CONV, with target instantiation
  reversed to kernel instantiation (`reverseTerm_instantiate`);
* `funExt`, `eta`: EXT and ETA of `DerivedRulesEta.lean`, the only uses of the
  eta axiom;
* hypothesis lists become finite sets; discharged and duplicated hypotheses
  are handled by `Finset` union, insertion and erasure, and weakening.

The symbol `equalitySymbol a`, primitive equality as an uninterpreted target
constant, reverses to primitive equality; no rule inspects constants, so
formulas mentioning it need no special treatment here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic
open CanonicalTerm (equalityDB)
open DerivedRules
open ReverseTranslation
open ExcludedMiddle (andDB orDB notDB impAppDB forallDB falsityDefinitionDB)

namespace EtaCompleteness

/-! ## The reverse translation on connectives -/

section Unfolding

variable {Γ : HOL.Ctx AtomicTy} (names : Naming Γ)

theorem reverseTerm_and_eq_andAppDB (p q : HOL.Formula Symbol Γ) :
    reverseTerm names (.and p q) = andAppDB (reverseTerm names p) (reverseTerm names q) := rfl

theorem reverseTerm_or_eq_orAppDB (p q : HOL.Formula Symbol Γ) :
    reverseTerm names (.or p q) = orAppDB (reverseTerm names p) (reverseTerm names q) := rfl

theorem reverseTerm_imp_eq_impAppDB (p q : HOL.Formula Symbol Γ) :
    reverseTerm names (.imp p q) = impAppDB (reverseTerm names p) (reverseTerm names q) := rfl

theorem reverseTerm_not_eq_notAppDB (p : HOL.Formula Symbol Γ) :
    reverseTerm names (.not p) = notAppDB (reverseTerm names p) := rfl

theorem reverseTerm_eq_eq_equalityDB {ρ : HOL.Ty AtomicTy} (left right : HOL.Term Symbol Γ ρ) :
    reverseTerm names (.eq left right) =
      equalityDB (reverseTy ρ) (reverseTerm names left) (reverseTerm names right) := rfl

theorem reverseTerm_all_eq_forallAppDB {σ : HOL.Ty AtomicTy} (body : HOL.Formula Symbol (σ :: Γ)) :
    reverseTerm names (.all body) =
      forallAppDB (reverseTy σ)
        (.abs (reverseTy σ) (reverseTermWith (VarEnv.lift (Naming.env names)) body)) := rfl

theorem reverseTerm_ex_eq_existsAppDB {σ : HOL.Ty AtomicTy} (body : HOL.Formula Symbol (σ :: Γ)) :
    reverseTerm names (.ex body) =
      existsAppDB (reverseTy σ)
        (.abs (reverseTy σ) (reverseTermWith (VarEnv.lift (Naming.env names)) body)) := rfl

/-- Under a binder, a weakened term reverses to the reverse of the term: the
reverse is closed, so the shift past the binder changes nothing. -/
theorem reverseTermWith_lift_env_weaken {σ τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol Γ τ) :
    reverseTermWith (VarEnv.lift (σ := σ) (Naming.env names)) (HOL.weaken term) =
      reverseTerm names term := by
  rw [reverseTermWith_weaken]
  exact shiftLoose_of_closed (term := reverseTermWith (Naming.env names) term)
    (looseBelow_zero_reverseTerm names term) 0

/-- Naming the innermost variable is instantiating the outermost binder of the
body by that name. -/
theorem reverseTerm_cons_eq_instantiateAt {σ τ : HOL.Ty AtomicTy} (name : Name)
    (body : HOL.Term Symbol (σ :: Γ) τ) :
    reverseTerm (Naming.cons name names) body =
      DBTerm.instantiateAt (.free ⟨name, reverseTy σ⟩) 0
        (reverseTermWith (VarEnv.lift (Naming.env names)) body) := by
  rw [instantiateAt_reverseTermWith (replacement := .free ⟨name, reverseTy σ⟩) trivial]
  refine reverseTermWith_congr (fun x => ?_) body
  cases x with
  | vz => simp [VarEnv.lift, Naming.env, Naming.sourceVar, Naming.cons]
  | vs x => simp [VarEnv.lift, Naming.env, Naming.sourceVar, Naming.cons, shiftLoose,
      DBTerm.instantiateAt]

end Unfolding

/-! ## Freshness -/

section Freshness

variable {Γ : HOL.Ctx AtomicTy} {names : Naming Γ} {sourceVar : SourceVar}

/-- A free variable avoided by the naming and named by no symbol of a term is
not free in its reverse. -/
theorem not_freeOccurrence_reverseTerm (fresh : Naming.Avoids names sourceVar)
    {τ : HOL.Ty AtomicTy} {term : HOL.Term Symbol Γ τ}
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar sourceVar) term) :
    ¬ DBTerm.FreeOccurrence sourceVar (reverseTerm names term) :=
  not_freeOccurrence_reverseTermWith (fun x found => by
    cases found
    exact fresh x rfl) symbolAbsent

/-- The same under one binder. -/
theorem not_freeOccurrence_reverseTermWith_lift (fresh : Naming.Avoids names sourceVar)
    {σ τ : HOL.Ty AtomicTy} {body : HOL.Term Symbol (σ :: Γ) τ}
    (symbolAbsent : HOL.NoConstOccurrence (Symbol.ofVar sourceVar) body) :
    ¬ DBTerm.FreeOccurrence sourceVar (reverseTermWith (VarEnv.lift (Naming.env names)) body) :=
  not_freeOccurrence_reverseTermWith (fun x found => by
    cases x with
    | vz => cases found
    | vs x =>
        rw [Naming.lift_env_vs] at found
        cases found
        exact fresh x rfl) symbolAbsent

end Freshness

/-! ## Admissibility -/

variable {policy : AxiomPolicy}

/-- Weakening into the reversal of a hypothesis list. -/
theorem weaken_reverseHypotheses {Γ : HOL.Ctx AtomicTy} {names : Naming Γ}
    {Δ : List (HOL.Formula Symbol Γ)} {hyp : Finset CanonicalTerm} {concl : DBTerm}
    (h : KernelProvable policy hyp concl) (subset : hyp ⊆ reverseHypotheses names Δ) :
    KernelProvable policy (reverseHypotheses names Δ) concl :=
  KernelProvable.weaken h subset fun _ member => isBool_of_mem_reverseHypotheses member

/-- **Admissibility of the extensional rules.**  Under every axiom policy
admitting the eta sequent, a derivation `Δ ⊢ φ` of `HOL.ExtDerivation`
reverses, under every naming of its context, to a kernel-provable sequent. -/
theorem kernelProvable_reverse_of_extDerivation (admitted : policy EtaAxiom.sequent)
    {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {φ : HOL.Formula Symbol Γ}
    (derivation : HOL.ExtDerivation Symbol Δ φ) :
    ∀ names : Naming Γ,
      KernelProvable policy (reverseHypotheses names Δ) (reverseTerm names φ) := by
  induction derivation with
  | @hyp Γ Δ φ member =>
      intro names
      exact weaken_reverseHypotheses
        (KernelProvable.assume (reverseCanonical names φ) (reverseCanonical_isBool names φ))
        (Finset.singleton_subset_iff.mpr (reverseCanonical_mem_reverseHypotheses names member))
  | topI =>
      intro names
      exact weaken_reverseHypotheses KernelProvable.truth (Finset.empty_subset _)
  | @botE Γ Δ φ _ ih =>
      intro names
      exact KernelProvable.contr (ih names) (inferType_reverseTerm names [] φ)
  | @andI Γ Δ φ ψ _ _ ihφ ihψ =>
      intro names
      rw [reverseTerm_and_eq_andAppDB]
      exact (KernelProvable.conj (ihφ names) (ihψ names)).congr_hyp (Finset.union_self _)
  | @andEL Γ Δ φ ψ _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_and_eq_andAppDB] at h
      exact KernelProvable.conjunct1 h
  | @andER Γ Δ φ ψ _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_and_eq_andAppDB] at h
      exact KernelProvable.conjunct2 h
  | @orIL Γ Δ φ ψ _ ih =>
      intro names
      rw [reverseTerm_or_eq_orAppDB]
      exact KernelProvable.disj1 (ih names) (inferType_reverseTerm names [] ψ)
  | @orIR Γ Δ φ ψ _ ih =>
      intro names
      rw [reverseTerm_or_eq_orAppDB]
      exact KernelProvable.disj2 (inferType_reverseTerm names [] φ) (ih names)
  | @orE Γ Δ φ ψ χ _ _ _ ihOr ihLeft ihRight =>
      intro names
      have hOr := ihOr names
      rw [reverseTerm_or_eq_orAppDB] at hOr
      have hLeft := ihLeft names
      have hRight := ihRight names
      rw [reverseHypotheses_cons] at hLeft hRight
      exact weaken_reverseHypotheses
        (KernelProvable.disjCases (reverseCanonical names φ) (reverseCanonical names ψ)
          hOr hLeft hRight)
        (Finset.union_subset (Finset.union_subset subset_rfl (Finset.erase_insert_subset _ _))
          (Finset.erase_insert_subset _ _))
  | @impI Γ Δ φ ψ _ ih =>
      intro names
      have h := ih names
      rw [reverseHypotheses_cons] at h
      rw [reverseTerm_imp_eq_impAppDB]
      exact weaken_reverseHypotheses
        (KernelProvable.disch (reverseCanonical names φ) (reverseCanonical_isBool names φ) h)
        (Finset.erase_insert_subset _ _)
  | @impE Γ Δ φ ψ _ _ ihImp ihφ =>
      intro names
      have hImp := ihImp names
      rw [reverseTerm_imp_eq_impAppDB] at hImp
      exact (KernelProvable.mp hImp (ihφ names)).congr_hyp (Finset.union_self _)
  | @notI Γ Δ φ _ ih =>
      intro names
      have h := ih names
      rw [reverseHypotheses_cons] at h
      rw [reverseTerm_not_eq_notAppDB]
      exact weaken_reverseHypotheses
        (KernelProvable.notIntro
          (KernelProvable.disch (reverseCanonical names φ) (reverseCanonical_isBool names φ) h))
        (Finset.erase_insert_subset _ _)
  | @notE Γ Δ φ _ _ ihNot ihφ =>
      intro names
      have hNot := ihNot names
      rw [reverseTerm_not_eq_notAppDB] at hNot
      exact (KernelProvable.mp (KernelProvable.notElim hNot) (ihφ names)).congr_hyp
        (Finset.union_self _)
  | @allI Γ Δ σ φ _ ih =>
      intro names
      obtain ⟨name, avoids, bodyAbsent, hypsAbsent⟩ := exists_fresh_name names σ φ Δ
      have h := ih (Naming.cons name names)
      rw [reverseHypotheses_weakenHyps] at h
      have hgen := KernelProvable.gen ⟨name, reverseTy σ⟩ h
        (not_freeInHypotheses_reverseHypotheses avoids hypsAbsent)
      rw [closeFreeAt_reverseTerm_cons names name φ avoids bodyAbsent] at hgen
      rw [reverseTerm_all_eq_forallAppDB]
      exact hgen
  | @allE Γ Δ σ φ t _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_all_eq_forallAppDB] at h
      have hspec := KernelProvable.spec h (inferType_reverseTerm names [] t)
      rw [← reverseTerm_instantiate] at hspec
      exact hspec
  | @exI Γ Δ σ φ t _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_instantiate] at h
      rw [reverseTerm_ex_eq_existsAppDB]
      exact KernelProvable.existsIntro h (inferType_reverseTerm names [] t)
  | @exE Γ Δ σ φ ψ _ _ ihEx ihBody =>
      intro names
      obtain ⟨name, avoids, bodyAbsent, hypsAbsent⟩ := exists_fresh_name names σ φ (ψ :: Δ)
      have hEx := ihEx names
      rw [reverseTerm_ex_eq_existsAppDB] at hEx
      have hBody := ihBody (Naming.cons name names)
      rw [reverseHypotheses_cons, reverseHypotheses_weakenHyps, reverseTerm_weaken] at hBody
      have hypsFresh : ¬ FreeInHypotheses ⟨name, reverseTy σ⟩ (reverseHypotheses names Δ) :=
        not_freeInHypotheses_reverseHypotheses avoids
          fun ψ' member => hypsAbsent ψ' (List.mem_cons_of_mem _ member)
      exact weaken_reverseHypotheses
        (KernelProvable.choose ⟨name, reverseTy σ⟩ (reverseCanonical (Naming.cons name names) φ)
          (reverseTerm_cons_eq_instantiateAt names name φ) hEx hBody
          (fun found => by
            cases found with
            | absBody found =>
                exact not_freeOccurrence_reverseTermWith_lift avoids bodyAbsent found)
          (not_freeOccurrence_reverseTerm avoids (hypsAbsent ψ List.mem_cons_self))
          (fun occurs => hypsFresh (freeInHypotheses_mono (Finset.erase_insert_subset _ _)
            occurs)))
        (Finset.union_subset subset_rfl (Finset.erase_insert_subset _ _))
  | @eqRefl Γ Δ τ t =>
      intro names
      rw [reverseTerm_eq_eq_equalityDB]
      exact weaken_reverseHypotheses (KernelProvable.refl (inferType_reverseTerm names [] t))
        (Finset.empty_subset _)
  | @eqSymm Γ Δ τ t u _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_eq_eq_equalityDB] at h
      rw [reverseTerm_eq_eq_equalityDB]
      exact KernelProvable.sym h
  | @eqTrans Γ Δ τ t u v _ _ ihFirst ihLast =>
      intro names
      have hFirst := ihFirst names
      have hLast := ihLast names
      rw [reverseTerm_eq_eq_equalityDB] at hFirst hLast
      rw [reverseTerm_eq_eq_equalityDB]
      exact (KernelProvable.trans hFirst hLast).congr_hyp (Finset.union_self _)
  | @eqPropI Γ Δ p q _ _ ihForward ihBackward =>
      intro names
      have hForward := ihForward names
      have hBackward := ihBackward names
      rw [reverseTerm_imp_eq_impAppDB] at hForward hBackward
      rw [reverseTerm_eq_eq_equalityDB]
      exact (KernelProvable.impAntisym (reverseCanonical names p) (reverseCanonical names q)
        hForward hBackward).congr_hyp (Finset.union_self _)
  | @eqPropEL Γ Δ p q _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_eq_eq_equalityDB] at h
      rw [reverseTerm_imp_eq_impAppDB]
      exact KernelProvable.eqImpRuleLeft (reverseCanonical names p) h
  | @eqPropER Γ Δ p q _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_eq_eq_equalityDB] at h
      rw [reverseTerm_imp_eq_impAppDB]
      exact KernelProvable.eqImpRuleRight (reverseCanonical names q) h
  | @eqApp Γ Δ σ τ f g t _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_eq_eq_equalityDB] at h
      rw [reverseTerm_eq_eq_equalityDB]
      exact KernelProvable.apThm h (inferType_reverseTerm names [] t)
  | @eqAppArg Γ Δ σ τ f t u _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_eq_eq_equalityDB] at h
      rw [reverseTerm_eq_eq_equalityDB]
      exact KernelProvable.apTerm (inferType_reverseTerm names [] f) h
  | @eqLam Γ Δ σ τ t u _ ih =>
      intro names
      obtain ⟨name, avoids, absent, hypsAbsent⟩ := exists_fresh_name names σ (.eq t u) Δ
      have h := ih (Naming.cons name names)
      rw [reverseHypotheses_weakenHyps, reverseTerm_eq_eq_equalityDB] at h
      have habs := KernelProvable.abs ⟨name, reverseTy σ⟩ h
        (not_freeInHypotheses_reverseHypotheses avoids hypsAbsent)
      rw [closeFreeAt_reverseTerm_cons names name t avoids (noConstOccurrence_eq_inv absent).1,
        closeFreeAt_reverseTerm_cons names name u avoids (noConstOccurrence_eq_inv absent).2]
        at habs
      rw [reverseTerm_eq_eq_equalityDB]
      exact habs
  | @funExt Γ Δ σ τ f g _ ih =>
      intro names
      have h := ih names
      rw [reverseTerm_all_eq_forallAppDB] at h
      have hbody : reverseTermWith (VarEnv.lift (Naming.env names))
          (HOL.Term.eq (.app (HOL.weaken f) (.var .vz)) (.app (HOL.weaken g) (.var .vz)) :
            HOL.Formula Symbol (σ :: Γ)) =
          equalityDB (reverseTy τ) (.app (reverseTerm names f) (.bound 0))
            (.app (reverseTerm names g) (.bound 0)) := by
        show equalityDB (reverseTy τ)
            (.app (reverseTermWith (VarEnv.lift (Naming.env names)) (HOL.weaken f)) (.bound 0))
            (.app (reverseTermWith (VarEnv.lift (Naming.env names)) (HOL.weaken g)) (.bound 0)) = _
        rw [reverseTermWith_lift_env_weaken, reverseTermWith_lift_env_weaken]
      rw [hbody] at h
      rw [reverseTerm_eq_eq_equalityDB]
      exact KernelProvable.ext admitted (looseBelow_zero_reverseTerm names f)
        (looseBelow_zero_reverseTerm names g) h
  | @beta Γ Δ σ τ t u =>
      intro names
      have htyped : (DBTerm.app
          (.abs (reverseTy σ) (reverseTermWith (VarEnv.lift (Naming.env names)) u))
          (reverseTerm names t)).inferType [] = some (reverseTy τ) :=
        inferType_reverseTerm names [] (.app (.lam u) t)
      have hred := KernelProvable.betaConv (policy := policy) htyped
      rw [← reverseTerm_instantiate] at hred
      exact weaken_reverseHypotheses hred (Finset.empty_subset _)
  | @eta Γ Δ σ τ f =>
      intro names
      have hgoal : reverseTerm names
          (HOL.Term.eq (.lam (.app (HOL.weaken f) (.var .vz))) f : HOL.Formula Symbol Γ) =
          equalityDB (.function (reverseTy σ) (reverseTy τ))
            (.abs (reverseTy σ) (.app (reverseTerm names f) (.bound 0))) (reverseTerm names f) := by
        show equalityDB (.function (reverseTy σ) (reverseTy τ))
            (.abs (reverseTy σ)
              (.app (reverseTermWith (VarEnv.lift (Naming.env names)) (HOL.weaken f)) (.bound 0)))
            (reverseTerm names f) = _
        rw [reverseTermWith_lift_env_weaken]
      rw [hgoal]
      exact weaken_reverseHypotheses
        (KernelProvable.eta admitted (inferType_reverseTerm names [] f)) (Finset.empty_subset _)

end EtaCompleteness

end Mettapedia.Languages.OpenTheory
