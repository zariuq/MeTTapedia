import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceBackward

/-!
# The REFL correspondence at the name frame: the commit at a child is a source COMM

`child_commit_sound`: EVERY admitted located COMM at a child location `l`, on two rows that read as the represented
inputs `predot (for(t <- x)A) @ l` and `predot (for(u <- x')B) @ l` and the token `Pending(l, m)`, is the source's
COMM on the bag of parallel parts (`FiniteProgram.BagComm`): the channels are one name, a ground principal unifier
`bs` exists, and every solution of the result reads the made rows as the represented dotted continuations at `l`
and the made token as `Done(l, m, 0)`.

Its hypotheses are the source's on the pair (`GroundUnifiable` for these two inputs, the variable convention,
first-order continuations) and step 1′'s named hypothesis at the name frame (ground, canonical bags in the patterns;
ground channels written canonically). The name frame's unification is turned into a syntactic one by
`ReflQuotient.canonSubst_unifies`.

With `refl_close_reads`, the hosted REFL quotes the bag that this COMM made at the child, whatever the cooling
order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero applyDot)
open MeTTaOperationsComm (psubst PSubst pvars psubst_of_pvars_nil psubst_pFor dotted GroundPrincipal firstOrder)
open MeTTaCalculus.Corrected (Apart)
open FiniteProgram (predot predot_pFor predot_ground firstPattern secondPattern channelUnknown firstBody secondBody)
open OneFrame (embed)
open ReflQuotient (bagCanon groundBags canonSubst_unifies)
open ReflNames (NameLaws nameAction QN QNE nameLaws_pFor_iff bagLaws_of_nameLaws nameCanon)
open ReflLocated (atLoc pendingTok doneTok locL located locatedFrame_name psubst_atLoc_any)
open ReflLocatedStep (take_reads res commChildAt)

variable {O : Type*}

/-- **The commit at a child is a source COMM.** -/
theorem child_commit_sound [DecidableEq O] (label : O → Pattern) (C : Configuration Pattern O)
    (t u ch ch' A B l m : Pattern) (first second token made₁ made₂ madeTok : O) (ρ : PSubst)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (predot (pFor t ch A)) l)))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (predot (pFor u ch' B)) l)))
    (readsToken : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label token)) (psubst σ (pendingTok l m)))
    (groundCh : pvars ch = []) (groundCh' : pvars ch' = []) (canonicalCh : nameCanon ch = ch)
    (canonicalCh' : nameCanon ch' = ch')
    (unifiable : (∃ σ : PSubst, psubst σ t = psubst σ u) →
      ∃ bs : Bindings, GroundPrincipal t u bs ∧ ∀ y v, bs.lookup y = some v → firstOrder v = true)
    (convention : Apart t A u B) (foA : firstOrder A = true) (foB : firstOrder B = true)
    (groundT : groundBags t = true) (groundU : groundBags u = true)
    (canonicalT : bagCanon t = t) (canonicalU : bagCanon u = u)
    (admitted : (RuleSyntax.step QN O QNE located).Admits (s := embed label C)
      (commChildAt ρ first second token made₁ made₂ madeTok))
    (rest : Multiset Pattern) :
    ch = ch' ∧ ∃ bs : Bindings,
      FiniteProgram.BagComm (pFor t ch A ::ₘ pFor u ch B ::ₘ rest)
        ((FiniteProgram.parts (applyDot bs A) : Multiset Pattern) +
          (FiniteProgram.parts (applyDot bs B) : Multiset Pattern) + rest) ∧
      ∀ σ : PSubst,
        nameAction.Models σ (res label C (commChildAt ρ first second token made₁ made₂ madeTok)).knowledge →
        nameAction.Models σ C.equations ∧
        NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₁))
          (psubst σ (atLoc (predot (applyDot bs A)) l)) ∧
        NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label made₂))
          (psubst σ (atLoc (predot (applyDot bs B)) l)) ∧
        NameLaws (psubst σ ((res label C (commChildAt ρ first second token made₁ made₂ madeTok)).label madeTok))
          (psubst σ (doneTok l m pZero)) := by
  obtain ⟨fresh, shapes, enabled, ⟨_, w, solved⟩, _, _⟩ := (RuleSyntax.admits_iff _).mp admitted
  have distinct : [first, second, token].Nodup := shapes.1
  have madeDistinct : [made₁, made₂, madeTok].Nodup := shapes.2.1
  have ne₁₂ : made₁ ≠ made₂ := fun same => (List.nodup_cons.mp madeDistinct).1 (List.mem_cons.mpr (.inl same))
  have rowFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (atLoc (pFor t (predot ch) (dotted (pvars t) (predot A))) l)) :=
    fun σ known => by
      have read := readsFirst σ known
      rw [predot_pFor] at read
      exact read
  have rowSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (atLoc (pFor u (predot ch') (dotted (pvars u) (predot B))) l)) :=
    fun σ known => by
      have read := readsSecond σ known
      rw [predot_pFor] at read
      exact read
  obtain ⟨knownW, unifyW, -, -⟩ := child_comm_reads label C t u (predot ch) (predot ch') (dotted (pvars t) (predot A))
    (dotted (pvars u) (predot B)) l first second token made₁ made₂ madeTok rowFirst rowSecond ne₁₂ ρ solved
  obtain ⟨bs, gp, values⟩ :=
    unifiable ⟨_, canonSubst_unifies groundT groundU canonicalT canonicalU (bagLaws_of_nameLaws unifyW)⟩
  have zipped₁ : (atLoc (pFor firstPattern channelUnknown firstBody) locL, first) ∈
      (commChildAt ρ first second token made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρ first second token made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, ReflLocated.commChild]
  have zipped₂ : (atLoc (pFor secondPattern channelUnknown secondBody) locL, second) ∈
      (commChildAt ρ first second token made₁ made₂ madeTok).rule.body.take.zip
        (commChildAt ρ first second token made₁ made₂ madeTok).selection.taken := by
    simp [commChildAt, ReflLocated.commChild]
  have solvedInfo : nameAction.Models w
      ((commChildAt ρ first second token made₁ made₂ madeTok).information QN (embed label C)) := solved
  have read₁ := (take_reads _ solvedInfo zipped₁).trans (rowFirst w knownW)
  have read₂ := (take_reads _ solvedInfo zipped₂).trans (rowSecond w knownW)
  simp only [psubst_atLoc_any, psubst_pFor] at read₁ read₂
  obtain ⟨inputs₁, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp read₁
  obtain ⟨inputs₂, -⟩ := (locatedFrame_name.atLoc_iff _ _ _ _).mp read₂
  obtain ⟨-, chan₁, -⟩ := nameLaws_pFor_iff.mp inputs₁
  obtain ⟨-, chan₂, -⟩ := nameLaws_pFor_iff.mp inputs₂
  have channels : NameLaws ch ch' := by
    have both := chan₁.symm.trans chan₂
    rw [predot_ground ch groundCh, predot_ground ch' groundCh', psubst_of_pvars_nil w ch groundCh,
      psubst_of_pvars_nil w ch' groundCh'] at both
    exact both
  have sameCh : ch = ch' := by
    have canon := (ReflNames.nameLaws_iff ch ch').mp channels
    rw [canonicalCh, canonicalCh'] at canon
    exact canon
  have present : first ∈ C.present ∧ second ∈ C.present ∧ token ∈ C.present :=
    ⟨enabled.taken_subset (by simp [commChildAt, Selection.commit]),
      enabled.taken_subset (by simp [commChildAt, Selection.commit]),
      enabled.taken_subset (by simp [commChildAt, Selection.commit])⟩
  have freshMade : made₁ ∉ C.present ∧ made₂ ∉ C.present ∧ madeTok ∉ C.present :=
    ⟨fun inside => Finset.disjoint_left.mp enabled.fresh (by simp [commChildAt, Selection.commit]) inside,
      fun inside => Finset.disjoint_left.mp enabled.fresh (by simp [commChildAt, Selection.commit]) inside,
      fun inside => Finset.disjoint_left.mp enabled.fresh (by simp [commChildAt, Selection.commit]) inside⟩
  obtain ⟨-, reads⟩ := child_commit label C t u ch A B l m bs gp convention foA foB groundT groundU canonicalT
    canonicalU first second token made₁ made₂ madeTok readsFirst (by rw [sameCh]; exact readsSecond) readsToken
    distinct madeDistinct present freshMade knownW unifyW fresh
  exact ⟨sameCh, bs, FiniteProgram.BagComm.comm t u ch A B bs rest gp convention values, reads⟩

#print axioms child_commit_sound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
