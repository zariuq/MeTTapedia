import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.Formation

/-!
# Dependent pairs in the consistency model

A dependent pair type denotes, at a world, the pairs of terms whose first
projections are related at its domain and whose second projections are related
at its codomain instantiated at the first projection. A projection of a pair
weak-head reduces to the component, and the model's relations are closed under
weak-head expansion, so pairs are related as soon as their components are. At
related first components the codomain has one denotation.

From these: validity of pairing and of the projections, their congruences, β
for both projections and η. The β-rules hold by weak-head expansion alone, so
each needs only the validity of the component it returns.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Consistency

open Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {M : Model Head L}

/-! ## Pairs in a world -/

/-- Related pairs have first projections related at the domain. -/
theorem Den.sigma_fst (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {R : Rel Head n} (den : Den M ξ (.sigma A B) R) {p q : Tm Head n}
    (h : R p q) {RA : Rel Head n} (denA : Den M ξ A RA) : RA (.fst p) (.fst q) := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, -, -⟩ := InterpAt.sigma_inv laws interp
  obtain ⟨_, hfst, _⟩ := h
  have domI := domInterp (Morph.id ξ)
  rw [rename_id] at domI
  rw [Den.deterministic laws denA ⟨l, domI⟩]
  exact hfst

/-- Related pairs have second projections related at the codomain
instantiated at the first projection. -/
theorem Den.sigma_snd (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {R : Rel Head n} (den : Den M ξ (.sigma A B) R) {p q : Tm Head n}
    (h : R p q) {RB : Rel Head n} (denB : Den M ξ (Presentation.inst0 (.fst p) B) RB) :
    RB (.snd p) (.snd q) := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, -, codInterp, -⟩ := InterpAt.sigma_inv laws interp
  obtain ⟨hp, -, hsnd⟩ := h
  have codI := codInterp (Morph.id ξ) hp
  rw [liftRen_id, rename_id] at codI
  rw [Den.deterministic laws denB ⟨l, codI⟩]
  exact hsnd

/-- At related arguments, the codomain of a dependent pair type has one
denotation. -/
theorem Den.sigma_cod (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {R : Rel Head n} (den : Den M ξ (.sigma A B) R) {a b : Tm Head n}
    (hab : ∀ {RA : Rel Head n}, Den M ξ A RA → RA a b) {RB : Rel Head n}
    (denB : Den M ξ (Presentation.inst0 a B) RB) : Den M ξ (Presentation.inst0 b B) RB := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, -, domInterp, codInterp, codRespect⟩ := InterpAt.sigma_inv laws interp
  have domI := domInterp (Morph.id ξ)
  rw [rename_id] at domI
  have hab' : P.dom (Morph.id ξ) a b := hab ⟨l, domI⟩
  have ha := Den.refl_left laws ⟨l, domI⟩ hab'
  have hb := Den.refl_right laws ⟨l, domI⟩ hab'
  have codA := codInterp (Morph.id ξ) ha
  have codB := codInterp (Morph.id ξ) hb
  rw [liftRen_id, rename_id] at codA codB
  rw [Den.deterministic laws denB ⟨l, codA⟩, codRespect (Morph.id ξ) ha hb hab']
  exact ⟨l, codB⟩

/-- Pairs are related at a dependent pair type when their first components are
related at the domain and their second components at the codomain
instantiated at the first component. -/
theorem Den.sigma_pair (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {B : Tm Head (n + 1)} {R : Rel Head n} (den : Den M ξ (.sigma A B) R)
    {a a' b b' : Tm Head n} (ha : ∀ {RA : Rel Head n}, Den M ξ A RA → RA a a')
    (hb : ∀ {RB : Rel Head n}, Den M ξ (Presentation.inst0 a B) RB → RB b b') :
    R (.pair a b) (.pair a' b') := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, codRespect⟩ := InterpAt.sigma_inv laws interp
  have domI := domInterp (Morph.id ξ)
  rw [rename_id] at domI
  have haa' : P.dom (Morph.id ξ) a a' := ha ⟨l, domI⟩
  have haa := Den.refl_left laws ⟨l, domI⟩ haa'
  have codI := codInterp (Morph.id ξ) haa
  rw [liftRen_id, rename_id] at codI
  have hpa : P.dom (Morph.id ξ) (.fst (.pair a b)) a :=
    domI.expandLeft (Relation.ReflTransGen.single (WhStep.fstPair a b)) haa
  have hp : P.dom (Morph.id ξ) (.fst (.pair a b)) (.fst (.pair a b)) :=
    domI.expandRight (Relation.ReflTransGen.single (WhStep.fstPair a b)) hpa
  refine ⟨hp, domI.expandLeft (Relation.ReflTransGen.single (WhStep.fstPair a b))
    (domI.expandRight (Relation.ReflTransGen.single (WhStep.fstPair a' b')) haa'), ?_⟩
  rw [codRespect (Morph.id ξ) hp haa hpa]
  exact codI.expandLeft (Relation.ReflTransGen.single (WhStep.sndPair a b))
    (codI.expandRight (Relation.ReflTransGen.single (WhStep.sndPair a' b')) (hb ⟨l, codI⟩))

/-! ## Pairing and projections -/

/-- Pairing. -/
theorem ValidTm.pair (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n}
    {B : Tm Head (n + 1)} (validSigma : ValidTy M Γ (.sigma A B)) (validA : ValidTm M Γ a A)
    (validB : ValidTm M Γ b (Presentation.inst0 a B)) :
    ValidTm M Γ (.pair a b) (.sigma A B) := by
  obtain ⟨_, relA⟩ := validA
  obtain ⟨_, relB⟩ := validB
  refine ⟨validSigma, fun {_ ξ σ σ'} e {R} den => ?_⟩
  refine Den.sigma_pair laws den (relA e) (fun {RB} denB => ?_)
  rw [← subst_inst0] at denB
  exact relB e denB

/-- First projection. -/
theorem ValidTm.fst (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n}
    {B : Tm Head (n + 1)} (valid : ValidTm M Γ p (.sigma A B)) (validA : ValidTy M Γ A) :
    ValidTm M Γ (.fst p) A := by
  obtain ⟨validSigma, rel⟩ := valid
  refine ⟨validA, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨_, denS, _⟩ := validSigma e
  exact Den.sigma_fst laws denS (rel e denS) den

/-- Second projection. -/
theorem ValidTm.snd (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n}
    {B : Tm Head (n + 1)} (valid : ValidTm M Γ p (.sigma A B)) (validA : ValidTy M Γ A)
    (validB : ValidTy M (.snoc Γ A) B) :
    ValidTm M Γ (.snd p) (Presentation.inst0 (.fst p) B) := by
  have validInst : ValidTy M Γ (Presentation.inst0 (.fst p) B) :=
    ValidTy.inst0 validB (ValidTm.fst laws valid validA)
  obtain ⟨validSigma, rel⟩ := valid
  refine ⟨validInst, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨_, denS, _⟩ := validSigma e
  rw [subst_inst0] at den
  exact Den.sigma_snd laws denS (rel e denS) den

/-! ## Congruences -/

/-- Congruence of pairing. -/
theorem ValidEq.pair (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {A a a' b b' : Tm Head n}
    {B : Tm Head (n + 1)} (validSigma : ValidTy M Γ (.sigma A B))
    (validB : ValidTy M (.snoc Γ A) B) (eqA : ValidEq M Γ a a' A)
    (eqB : ValidEq M Γ b b' (Presentation.inst0 a B)) :
    ValidEq M Γ (.pair a b) (.pair a' b') (.sigma A B) := by
  obtain ⟨validLeft, ⟨validTyA, relA'⟩, relAA'⟩ := eqA
  obtain ⟨validB₁, ⟨_, relB₂⟩, relBB'⟩ := eqB
  have validB₂ : ValidTm M Γ b' (Presentation.inst0 a' B) := by
    refine ⟨ValidTy.inst0 validB ⟨validTyA, relA'⟩, fun {_ ξ σ σ'} e {R} den => ?_⟩
    obtain ⟨_, denS, _⟩ := validSigma e
    apply relB₂ e
    rw [subst_inst0] at den ⊢
    exact Den.sigma_cod laws denS
      (fun {_} denA => Den.trans laws denA (relA' e denA) (Den.symm laws denA (relAA' e denA)))
      den
  refine ⟨ValidTm.pair laws validSigma validLeft validB₁,
    ValidTm.pair laws validSigma ⟨validTyA, relA'⟩ validB₂,
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  refine Den.sigma_pair laws den (relAA' e) (fun {RB} denB => ?_)
  rw [← subst_inst0] at denB
  exact relBB' e denB

/-- Congruence of the first projection. -/
theorem ValidEq.fst (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n}
    {B : Tm Head (n + 1)} (eq : ValidEq M Γ p q (.sigma A B)) (validA : ValidTy M Γ A) :
    ValidEq M Γ (.fst p) (.fst q) A := by
  obtain ⟨validP, validQ, rel⟩ := eq
  have fstP := ValidTm.fst laws validP validA
  have fstQ := ValidTm.fst laws validQ validA
  obtain ⟨validSigma, _⟩ := validP
  refine ⟨fstP, fstQ, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨_, denS, _⟩ := validSigma e
  exact Den.sigma_fst laws denS (rel e denS) den

/-- Congruence of the second projection. -/
theorem ValidEq.snd (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n}
    {B : Tm Head (n + 1)} (eq : ValidEq M Γ p q (.sigma A B)) (validA : ValidTy M Γ A)
    (validB : ValidTy M (.snoc Γ A) B) :
    ValidEq M Γ (.snd p) (.snd q) (Presentation.inst0 (.fst p) B) := by
  obtain ⟨validP, validQ, rel⟩ := eq
  obtain ⟨validInst, relSndP⟩ := ValidTm.snd laws validP validA validB
  obtain ⟨_, relSndQ⟩ := ValidTm.snd laws validQ validA validB
  obtain ⟨validSigma, _⟩ := validP
  obtain ⟨_, relQ⟩ := validQ
  refine ⟨⟨validInst, relSndP⟩, ⟨validInst, fun {_ ξ σ σ'} e {R} den => ?_⟩,
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  · obtain ⟨_, denS, _⟩ := validSigma e
    apply relSndQ e
    rw [subst_inst0] at den ⊢
    exact Den.sigma_cod laws denS
      (fun {_} denA => Den.trans laws denA (Den.sigma_fst laws denS (rel e denS) denA)
        (Den.symm laws denA (Den.sigma_fst laws denS (relQ e denS) denA)))
      den
  · obtain ⟨_, denS, _⟩ := validSigma e
    rw [subst_inst0] at den
    exact Den.sigma_snd laws denS (rel e denS) den

/-! ## β and η -/

/-- β for the first projection: the first projection of a pair weak-head
reduces to its first component. -/
theorem ValidEq.betaFst {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
    (validA : ValidTm M Γ a A) : ValidEq M Γ (.fst (.pair a b)) a A := by
  obtain ⟨validTyA, rel⟩ := validA
  refine ⟨⟨validTyA, fun {_ ξ σ σ'} e {R} den => ?_⟩, ⟨validTyA, rel⟩,
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  · exact Den.expandLeft den (Relation.ReflTransGen.single (WhStep.fstPair _ _))
      (Den.expandRight den (Relation.ReflTransGen.single (WhStep.fstPair _ _)) (rel e den))
  · exact Den.expandLeft den (Relation.ReflTransGen.single (WhStep.fstPair _ _)) (rel e den)

/-- β for the second projection: the second projection of a pair weak-head
reduces to its second component. -/
theorem ValidEq.betaSnd {n : Nat} {Γ : Ctx Head n} {a b : Tm Head n}
    {B : Tm Head (n + 1)} (validB : ValidTm M Γ b (Presentation.inst0 a B)) :
    ValidEq M Γ (.snd (.pair a b)) b (Presentation.inst0 a B) := by
  obtain ⟨validTyB, rel⟩ := validB
  refine ⟨⟨validTyB, fun {_ ξ σ σ'} e {R} den => ?_⟩, ⟨validTyB, rel⟩,
    fun {_ ξ σ σ'} e {R} den => ?_⟩
  · exact Den.expandLeft den (Relation.ReflTransGen.single (WhStep.sndPair _ _))
      (Den.expandRight den (Relation.ReflTransGen.single (WhStep.sndPair _ _)) (rel e den))
  · exact Den.expandLeft den (Relation.ReflTransGen.single (WhStep.sndPair _ _)) (rel e den)

/-- η for pairs: pairs are equal when their projections are. -/
theorem ValidEq.etaSigma (laws : M.Laws) {n : Nat} {Γ : Ctx Head n} {p q A : Tm Head n}
    {B : Tm Head (n + 1)} (validP : ValidTm M Γ p (.sigma A B))
    (validQ : ValidTm M Γ q (.sigma A B)) (eqFst : ValidEq M Γ (.fst p) (.fst q) A)
    (eqSnd : ValidEq M Γ (.snd p) (.snd q) (Presentation.inst0 (.fst p) B)) :
    ValidEq M Γ p q (.sigma A B) := by
  obtain ⟨_, _, relFst⟩ := eqFst
  obtain ⟨_, _, relSnd⟩ := eqSnd
  refine ⟨validP, validQ, fun {_ ξ σ σ'} e {R} den => ?_⟩
  obtain ⟨l, interp⟩ := den
  obtain ⟨P, rfl, domInterp, codInterp, -⟩ := InterpAt.sigma_inv laws interp
  have domI := domInterp (Morph.id ξ)
  rw [rename_id] at domI
  have hfst : P.dom (Morph.id ξ) (.fst (Presentation.subst σ p))
      (.fst (Presentation.subst σ' q)) := relFst e ⟨l, domI⟩
  have hp := Den.refl_left laws ⟨l, domI⟩ hfst
  have codI := codInterp (Morph.id ξ) hp
  rw [liftRen_id, rename_id] at codI
  have denB : Den M ξ (Presentation.subst σ (Presentation.inst0 (.fst p) B))
      (P.cod (Morph.id ξ) hp) := by
    rw [subst_inst0]
    exact ⟨l, codI⟩
  exact ⟨hp, hfst, relSnd e denB⟩

end Consistency
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
