import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchAdequacy

/-!
# Adequacy of the numeral recursor, and of every constant of the object package

Every statement about adequacy here is about a package containing the object package
(`ObjectExtension`), the object package itself among them; the last section is the object
package's own.

**Numerals in the type of numbers.** A token typed at the numbers is zero, the successor
tag or a predecessor token of such a token (`tyTok_nat_cases`). The predecessor of a
number is a number (`projT_natI_predI`). A number without the zero tag lies below the
successor of its predecessor (`le_succI_predI`); a number whose typed tokens are the zero
tag or observe nothing lies below zero (`le_zeroI`).

**The recursor at a number** (`rec_claim`). The recursor's spine at terms related as far
as a number observes is related to itself at the motive there, as far as every typed token
of the `k`-th approximant of its numeral recursion observes. A token that observes
something names the tag of the number through the approximant's generators, so no case
split on the number's tags is needed. At zero,
the spine reduces to the zero case, whose relation at `P zero` converts to `P n` along
the motive's adequacy; at a successor it reduces to the step at the predecessor and the
recursive value, adequate over the context extended by them, whose relation at
`P (suc m)` converts to `P n` the same way. The recursive value is related by the claim at
the predecessor. With the relation of the motive's argument, `num-rec` is adequate
through its spine (`constAdequateAt_numRec`).

**Every constant of the object package is adequate in every extension**
(`ObjectExtension.objectConsts_adequate`), and every constant of the object package itself
(`objectChurch_constAdequate`). So every derivable statement
of the object package is valid (`objectChurch_fundamental`), and with no hypothesis: the
facts about the weak-head forms of its annotated types (`objectFormFacts`), the injectivity
and no-confusion of its type formers (`objectFormerFacts`), the coherence of annotations
(`objectCoherence`) and the preservation of types by root steps (`objectRootPreserving`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Impredicative.Domain
open Presentation.TypedEquality.Impredicative.Domain.Ideal
  (projT TypedAt principal natI zeroI succI predI natRecApprox natRec nrStep)
open Package (numRecName transportName composeName returnIterName sucStepName)
open Mettapedia.Logic

namespace CodeModel

variable (X : ObjectExtension)

/-! ## Numerals in the type of numbers -/

/-- **The tokens typed at the numbers**: zero, the successor tag, and predecessor tokens of
typed tokens. -/
theorem tyTok_nat_cases {g : Tok} (h : TyTok Elem.nat g) :
    g = .tag .zero ∨ g = .tag .succ ∨ ∃ s, g = .arg .succ 0 [] s ∧ TyTok Elem.nat s := by
  have nmem : ∀ {k : Kind}, k ≠ .nat → Tok.tag k ∉ Elem.nat := fun hk h' =>
    hk (Tok.tag.inj (List.mem_singleton.1 h'))
  have nuniv : ¬ IsUniv Elem.nat := fun h' => h'.elim (nmem (by decide)) (nmem (by decide))
  cases g with
  | tag k =>
      rcases tag_cases k with hk | rfl | rfl | rfl | rfl | rfl | hk
      · exact absurd ((tyTok_tag_former hk).1 h) nuniv
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact absurd (tyTok_tag_refl.1 h) (nmem (by decide))
      · exact absurd h tyTok_tag_lam
      · exact absurd h tyTok_tag_pair
      · obtain ⟨d, c, fs, rfl⟩ := hk
        exact absurd (tyTok_tag_ctor.1 h) (nmem (k := .data _) nofun)
  | arg k i C s =>
      rcases Decidable.em ((k, i) ∈ argSlots) with hs | hother
      swap
      · rcases decl_cases k with ⟨d, rfl⟩ | ⟨d, c, fs, rfl⟩ | hk
        · exact absurd (tyTok_param.1 h).1 nuniv
        · exact absurd (tyTok_field.1 h).1 (nmem (k := .data _) nofun)
        · exact absurd h (tyTok_arg_other hother hk)
      simp only [argSlots, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd ((tyTok_dom (.inl rfl)).1 h).1 nuniv
      · exact absurd ((tyTok_dom (.inr (.inl rfl))).1 h).1 nuniv
      · exact absurd ((tyTok_dom (.inr (.inr rfl))).1 h).1 nuniv
      · exact absurd ((tyTok_endpoint (.inl rfl)).1 h).1 nuniv
      · exact absurd ((tyTok_endpoint (.inr rfl)).1 h).1 nuniv
      · obtain ⟨-, rfl, hs⟩ := tyTok_pred.1 h
        exact .inr (.inr ⟨s, rfl, hs⟩)
      · exact absurd (tyTok_reflPoint.1 h).1 (nmem (by decide))
      · exact absurd (tyTok_fst.1 h).1 (nmem (by decide))
      · exact absurd (tyTok_snd.1 h).1 (nmem (by decide))
  | fn k C X Y =>
      rcases fn_cases k with hk | rfl | hother
      · exact absurd ((tyTok_family hk).1 h).1 nuniv
      · exact absurd (tyTok_lam.1 h).1 (nmem (by decide))
      · exact absurd h (tyTok_fn_other hother)

/-- **The predecessor of a number is a number**: a component of a successor token of a
number is entailed by components of its typed predecessor tokens, which are typed. -/
theorem projT_natI_predI {ν : Ideal} (hν : projT natI ν = ν) : projT natI (predI ν) = predI ν := by
  unfold Ideal.predI
  refine Ideal.projT_closure_eq fun g ⟨C, hg⟩ => ?_
  rw [← hν] at hg
  obtain ⟨u, hu, huT, e⟩ := Ideal.projT_eq_iSup.1 hg
  rw [ent_arg, Bool.and_eq_true] at e
  refine ⟨args .succ 0 u, fun s hs => ?_, e.2⟩
  rcases mem_args_iff.1 hs with ⟨C', hC'⟩ | ⟨-, t, ht, -, hd⟩
  · obtain ⟨-, rfl, hsT⟩ := tyTok_pred.1 (Ideal.tyTok_nat_of_typedAt (huT _ hC'))
    exact ⟨Ideal.subset_closure ⟨[], hu _ hC'⟩, Elem.nat, Ideal.below_nat, Ideal.nat_type, hsT⟩
  · rcases tyTok_nat_cases (Ideal.tyTok_nat_of_typedAt (huT t ht)) with rfl | rfl | ⟨r, rfl, -⟩
    · cases hd
    · cases hd
    · cases hd

/-- **A number without the zero tag lies below the successor of its predecessor.** -/
theorem le_succI_predI {ν : Ideal} (hν : projT natI ν = ν) (hz : ¬ ν.Mem (.tag .zero)) :
    ν ≤ succI (predI ν) := by
  intro t ht
  rw [← hν] at ht
  obtain ⟨u, hu, huT, e⟩ := Ideal.projT_eq_iSup.1 ht
  refine (succI (predI ν)).closed (v := u) (fun g hg => ?_) e
  rcases tyTok_nat_cases (Ideal.tyTok_nat_of_typedAt (huT g hg)) with rfl | rfl | ⟨s, rfl, -⟩
  · exact absurd (hu _ hg) hz
  · exact Ideal.succI_mem_succ _
  · exact Ideal.subset_closure (.inr ⟨s, rfl, Ideal.subset_closure ⟨[], hu _ hg⟩⟩)

/-- **A number whose typed tokens are the zero tag or observe nothing lies below zero.** -/
theorem le_zeroI {ν : Ideal} (hν : projT natI ν = ν)
    (hg : ∀ g, ν.Mem g → TypedAt natI g → g = .tag .zero ∨ ent [] g = true) : ν ≤ zeroI := by
  intro t ht
  rw [← hν] at ht
  obtain ⟨u, hu, huT, e⟩ := Ideal.projT_eq_iSup.1 ht
  refine zeroI.closed (v := u) (fun g hgu => ?_) e
  rcases hg g (hu g hgu) (huT g hgu) with rfl | hv
  · exact Ideal.zeroI_mem_zero
  · exact Ideal.mem_principal.2 (ent_mono (fun _ h => absurd h List.not_mem_nil) hv)

/-! ## The recursor's spine -/

section Spine

variable {n : Nat}

/-- `num-rec P z s q`, annotated. -/
abbrev cRecApp (P z s q : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.app (.app (.const numRecName) P) z) s) q

/-- The context of the recursor's spine: the motive, the zero case, the step and the
numeral. -/
abbrev cRecSpineTele : CCtx Tower.Head 4 := .snoc cRecTele cnum

/-- The recursor's spine at the variables of its context. -/
abbrev cRecSpine : CTm Tower.Head 4 := cRecApp (.var 3) (.var 2) (.var 1) (.var 0)

/-- The motive at the numeral, `P t`. -/
abbrev cMotiveAt : CTm Tower.Head 4 := .app (.var 3) (.var 0)

/-- The context of the step's application: the recursor's parameters, a predecessor and
the recursive value at it. -/
abbrev cRecStepTele : CCtx Tower.Head 5 := .snoc cRecSpineTele cMotiveAt

/-- The step at the predecessor and the recursive value, `s v r`. -/
abbrev cRecStepBody : CTm Tower.Head 5 := .app (.app (.var 2) (.var 1)) (.var 0)

/-- The motive at the successor of the predecessor, `P (suc v)`. -/
abbrev cRecStepType : CTm Tower.Head 5 := .app (.var 4) (csuc (.var 1))

/-- The zero rule of `num-rec`, as an annotated root step: `num-rec P z s 0 ⟶ z`. -/
theorem cnumRecZero_step (P z s : CTm Tower.Head n) :
    objectChurch.computation.step (cRecApp P z s czero) z := by
  have step := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 0) (by decide))
    (L := iotaLeft numRecName zeroN 2 0) (R := iotaRight numRecName 2 0 ([] : List CtorField))
    (show iotaSchema numRecName ctors _ _ from ⟨0, zeroN, [], rfl, rfl⟩)
    (CTm.consSub s (CTm.consSub z (CTm.consSub P Fin.elim0)))
  rw [numRecZero_elabLeft, numRecZero_elabRight] at step
  exact step

/-- **The zero rule of `num-rec` is admitted** along a typed substitution of the recursor's
parameters: a motive, its zero case and its step. -/
theorem cnumRecZero_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {Γ : CCtx Tower.Head n}
    {τ : CSub Tower.Head 3 n} (mor : CSubstMor Q cRecTele Γ τ)
    (within : StepsWithin objectChurch Q := by exact objectChurch_within rfl) :
    Q.Admits Γ (cRecApp (τ 2) (τ 1) (τ 0) czero) (τ 1) := by
  have a := objectChurch_admits_of_mor within
    (List.getElem_mem (l := computationSpecs) (n := 0) (by decide))
    (L := iotaLeft numRecName zeroN 2 0) (R := iotaRight numRecName 2 0 ([] : List CtorField))
    (show iotaSchema numRecName ctors _ _ from ⟨0, zeroN, [], rfl, rfl⟩) τ numRecZero_knowledge
    numRecZero_equations mor
  rw [numRecZero_elabLeft, numRecZero_elabRight] at a
  exact a

/-- The successor rule of `num-rec`, as an annotated root step:
`num-rec P z s (suc a) ⟶ s a (num-rec P z s a)`. -/
theorem cnumRecSuc_step (P z s a : CTm Tower.Head n) :
    objectChurch.computation.step (cRecApp P z s (csuc a))
      (.app (.app s a) (cRecApp P z s a)) := by
  have step := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 0) (by decide))
    (L := iotaLeft numRecName sucN 2 1) (R := iotaRight numRecName 2 1 [(.recursive : CtorField)])
    (show iotaSchema numRecName ctors _ _ from ⟨1, sucN, [.recursive], rfl, rfl⟩)
    (CTm.consSub a (CTm.consSub s (CTm.consSub z (CTm.consSub P Fin.elim0))))
  rw [numRecSuc_elabLeft, numRecSuc_elabRight] at step
  exact step

/-- **The successor rule of `num-rec` is admitted** along a typed substitution of the
recursor's parameters and a number. -/
theorem cnumRecSuc_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {Γ : CCtx Tower.Head n}
    {τ : CSub Tower.Head 3 n} {q : CTm Tower.Head n}
    (mor : CSubstMor Q (.snoc cRecTele cnum) Γ (CTm.consSub q τ))
    (within : StepsWithin objectChurch Q := by exact objectChurch_within rfl) :
    Q.Admits Γ (cRecApp (τ 2) (τ 1) (τ 0) (csuc q))
      (.app (.app (τ 0) q) (cRecApp (τ 2) (τ 1) (τ 0) q)) := by
  have a := objectChurch_admits_of_mor within
    (List.getElem_mem (l := computationSpecs) (n := 0) (by decide))
    (L := iotaLeft numRecName sucN 2 1) (R := iotaRight numRecName 2 1 [(.recursive : CtorField)])
    (show iotaSchema numRecName ctors _ _ from ⟨1, sucN, [.recursive], rfl, rfl⟩)
    (CTm.consSub q τ) numRecSuc_knowledge (by decide) mor
  rw [numRecSuc_elabLeft, numRecSuc_elabRight] at a
  exact a

/-- The recursor's parameters are formed. -/
theorem cRecTele_formed : CCtxFormed objectChurch cRecTele :=
  .snoc (.snoc (.snoc .nil ⟨_, .sort _, cpiT (craise cnum_typed) cU0_typed⟩)
    ⟨_, .sort _, .appElim (B := cU0) (.var 0) czero_typed⟩)
    ⟨_, .sort _, cpiT cnum_typed (cpiT (.appElim (B := cU0) (.var 2) (.var 0))
      (.appElim (B := cU0) (.var 3) (csuc_typed (.var 1))))⟩

/-- The motive at the numeral is a type of `U₀`, derived with no constant. -/
theorem cmotiveAt_typed_within {A : DeclName → Bool} :
    CTyped (objectChurch.restrict A) cRecSpineTele cMotiveAt cU0 :=
  .appElim (B := cU0) (.var 3) (.var 0)

theorem cmotiveAt_typed : CTyped objectChurch cRecSpineTele cMotiveAt cU0 :=
  .appElim (B := cU0) (.var 3) (.var 0)

theorem cRecSpineTele_formed : CCtxFormed objectChurch cRecSpineTele :=
  .snoc cRecTele_formed ⟨_, .sort _, cnum_typed⟩

theorem cRecStepTele_formed : CCtxFormed objectChurch cRecStepTele :=
  .snoc cRecSpineTele_formed ⟨_, .sort _, cmotiveAt_typed⟩

/-- The recursor's spine at the variables of its context is typed at the motive at the
numeral. -/
theorem cRecSpine_typed : CTyped objectChurch cRecSpineTele cRecSpine cMotiveAt := by
  have r1 := CDerivable.appElim (cnumRec_typed (Γ := cRecSpineTele)) (.var 3)
  have r2 := CDerivable.appElim r1 (.var 2)
  have r3 := CDerivable.appElim r2 (.var 1)
  exact CDerivable.appElim r3 (.var 0)

/-- The step at the predecessor and the recursive value is typed at the motive at the
successor, derived with no constant. -/
theorem cRecStepBody_typed_within {A : DeclName → Bool} :
    CTyped (objectChurch.restrict A) cRecStepTele cRecStepBody cRecStepType :=
  CDerivable.appElim (A := .app (.var 4) (.var 1)) (B := .app (.var 5) (csuc (.var 2)))
    (CDerivable.appElim (A := cnum) (B := .pi (.app (.var 5) (.var 0)) (.app (.var 6) (csuc (.var 1))))
      (.var 2) (.var 1)) (.var 0)

theorem cRecStepBody_typed : CTyped objectChurch cRecStepTele cRecStepBody cRecStepType :=
  CDerivable.appElim (A := .app (.var 4) (.var 1)) (B := .app (.var 5) (csuc (.var 2)))
    (CDerivable.appElim (A := cnum) (B := .pi (.app (.var 5) (.var 0)) (.app (.var 6) (csuc (.var 1))))
      (.var 2) (.var 1)) (.var 0)

/-- The motive at the numeral is an adequate type. -/
theorem adequateType_motiveAt : AdequateType X.reading X.head cRecSpineTele cMotiveAt :=
  (X.valid_within (allowed := fun _ => false) (fun h => absurd h Bool.false_ne_true)
    cmotiveAt_typed_within (X.liftFormed cRecSpineTele_formed)).1.adequateType X.levels
      X.soundnessFacts (X.sort _)

/-- The step at the predecessor and the recursive value is adequate at the motive at the
successor. -/
theorem adequate_recStepBody :
    Adequate X.reading X.head cRecStepTele cRecStepBody cRecStepType :=
  (X.valid_within (allowed := fun _ => false) (fun h => absurd h Bool.false_ne_true)
    cRecStepBody_typed_within (X.liftFormed cRecStepTele_formed)).1

end Spine

/-! ## Head expansion along the two rules -/

section Expansion

variable {m : Nat} {Δ : CCtx Tower.Head m}

/-- A substitution of the recursor's parameters extended by a number is a substitution of
the spine's context. -/
theorem CSubstMor.recCons {τ : CSub Tower.Head 3 m} (mor : CSubstMor X.church cRecTele Δ τ)
    {N : CTm Tower.Head m} (tN : CTyped X.church Δ N cnum) :
    CSubstMor X.church cRecSpineTele Δ (CTm.consSub N τ) :=
  (CSubstEq.cons ⟨mor, fun i => .refl (mor i)⟩ tN (.refl tN)).1

/-- The reduction of the recursor's spine along the reduction of its numeral. -/
theorem recSpine_red {τ : CSub Tower.Head 3 m} {N N' : CTm Tower.Head m}
    (red : Relation.ReflTransGen X.head.step N N') :
    Relation.ReflTransGen X.head.step (cRecSpine.subst (CTm.consSub N τ))
      (cRecSpine.subst (CTm.consSub N' τ)) := by
  have h := Relation.ReflTransGen.lift
    (fun q : CTm Tower.Head m => (CTm.app (CTm.appSpine (.const numRecName) [τ 2, τ 1, τ 0]) q :
      CTm Tower.Head m))
    (fun _ _ h => X.head_numRec h) _ _ red
  exact h

/-- **The recursor's spine at a numeral that reduces to zero reduces to its zero case**, at
the motive at the numeral. -/
theorem CRedTm.recZero (formed : CCtxFormed X.church Δ) {τ : CSub Tower.Head 3 m}
    {N : CTm Tower.Head m} (mor : CSubstMor X.church cRecTele Δ τ)
    (hN : CRedTm X.head Δ N czero cnum) :
    CRedTm X.head Δ (cRecSpine.subst (CTm.consSub N τ)) (τ 1)
      (cMotiveAt.subst (CTm.consSub N τ)) := by
  obtain ⟨tN, -⟩ := CEqual.typed X.levels hN.2 formed
  have eNZ : CSubstEq X.church cRecSpineTele Δ (CTm.consSub N τ) (CTm.consSub czero τ) :=
    CSubstEq.cons ⟨mor, fun i => .refl (mor i)⟩ tN hN.2
  refine ⟨(recSpine_red X hN.1).tail (X.head.root (X.within.step (cnumRecZero_step (τ 2) (τ 1) (τ 0)))),
    ?_⟩
  have e₁ := CDerivable.functional (X.lift cRecSpine_typed) eNZ
  have e₂ : CEqual X.church Δ (cRecSpine.subst (CTm.consSub czero τ)) (τ 1)
      (cMotiveAt.subst (CTm.consSub czero τ)) :=
    .rootAdmitted (X.within.step (cnumRecZero_step (τ 2) (τ 1) (τ 0))) (cnumRecZero_admits mor X.within)
      (CTyped.substitute (X.lift cRecSpine_typed) (CSubstMor.recCons X mor (X.lift czero_typed))) (mor 1)
  have eT : CEqual X.church Δ (cMotiveAt.subst (CTm.consSub czero τ))
      (cMotiveAt.subst (CTm.consSub N τ)) cU0 :=
    .symm (CDerivable.functional (X.lift cmotiveAt_typed) eNZ)
  exact .trans e₁ (.convEq e₂ eT (X.sort _))

/-- **The recursor's spine at a numeral that reduces to a successor reduces to the step at
the predecessor and the recursive value there**, at the motive at the numeral. -/
theorem CRedTm.recSuc (formed : CCtxFormed X.church Δ) {τ : CSub Tower.Head 3 m}
    {N q : CTm Tower.Head m} (mor : CSubstMor X.church cRecTele Δ τ)
    (tq : CTyped X.church Δ q cnum) (hN : CRedTm X.head Δ N (csuc q) cnum) :
    CRedTm X.head Δ (cRecSpine.subst (CTm.consSub N τ))
      (.app (.app (τ 0) q) (cRecSpine.subst (CTm.consSub q τ)))
      (cMotiveAt.subst (CTm.consSub N τ)) := by
  obtain ⟨tN, -⟩ := CEqual.typed X.levels hN.2 formed
  have eNS : CSubstEq X.church cRecSpineTele Δ (CTm.consSub N τ) (CTm.consSub (csuc q) τ) :=
    CSubstEq.cons ⟨mor, fun i => .refl (mor i)⟩ tN hN.2
  refine ⟨(recSpine_red X hN.1).tail
    (X.head.root (X.within.step (cnumRecSuc_step (τ 2) (τ 1) (τ 0) q))), ?_⟩
  have e₁ := CDerivable.functional (X.lift cRecSpine_typed) eNS
  have mor₂ : CSubstMor X.church cRecStepTele Δ
      (CTm.consSub (cRecSpine.subst (CTm.consSub q τ)) (CTm.consSub q τ)) :=
    (CSubstEq.cons ⟨CSubstMor.recCons X mor tq, fun i => .refl (CSubstMor.recCons X mor tq i)⟩
      (CTyped.substitute (X.lift cRecSpine_typed) (CSubstMor.recCons X mor tq))
      (.refl (CTyped.substitute (X.lift cRecSpine_typed) (CSubstMor.recCons X mor tq)))).1
  have e₂ : CEqual X.church Δ (cRecSpine.subst (CTm.consSub (csuc q) τ))
      (.app (.app (τ 0) q) (cRecSpine.subst (CTm.consSub q τ)))
      (cMotiveAt.subst (CTm.consSub (csuc q) τ)) :=
    .rootAdmitted (X.within.step (cnumRecSuc_step (τ 2) (τ 1) (τ 0) q))
      (cnumRecSuc_admits (CSubstMor.recCons X mor tq) X.within)
      (CTyped.substitute (X.lift cRecSpine_typed) (CSubstMor.recCons X mor (X.csuc_typed tq)))
      (CTyped.substitute (X.lift cRecStepBody_typed) mor₂)
  have eT : CEqual X.church Δ (cMotiveAt.subst (CTm.consSub (csuc q) τ))
      (cMotiveAt.subst (CTm.consSub N τ)) cU0 :=
    .symm (CDerivable.functional (X.lift cmotiveAt_typed) eNS)
  exact .trans e₁ (.convEq e₂ eT (X.sort _))

end Expansion

/-! ## The recursor at the approximants of its numeral recursion -/

section Claim

variable {m : Nat} {Δ : CCtx Tower.Head m}

/-- The numbers are related to themselves as far as a token of the numbers observes. -/
theorem RT.cnum_self {r : Tok} (hr : natI.Mem r) :
    RT X.head Δ false r cnum cnum cnum := by
  refine RT.closed' hr fun q hq => ?_
  rw [List.mem_singleton.1 hq]
  have red : CRedTy X.head Δ (cnum : CTm Tower.Head m) cnum :=
    CRedTy.refl ⟨_, X.sort _, X.lift cnum_typed⟩
  exact RT.ty_nat_iff.2 ⟨red, red⟩

/-- **Related substitutions of the recursor's parameters, extended by numbers** related as
far as a value observes. -/
theorem SubstRel.recCons (formed : CCtxFormed X.church Δ) {ρ : Env 3}
    {τ τ' : CSub Tower.Head 3 m}
    (hτ : SubstRel X.reading X.head cRecTele ρ Δ τ τ') {ν : Ideal}
    {N N' : CTm Tower.Head m} (hNN : CEqual X.church Δ N N' cnum)
    (hν : ∀ x, ν.Mem x → RT X.head Δ true x cnum N N') :
    SubstRel X.reading X.head cRecSpineTele (Env.cons ν ρ) Δ
      (CTm.consSub N τ) (CTm.consSub N' τ') :=
  SubstRel.cons X.levels formed hτ hNN ⟨_, X.sort _, .refl (X.lift cnum_typed)⟩
    (fun r hr _ => RT.cnum_self X (by rwa [X.cinterp_cnum] at hr)) (fun s hs _ => hν s hs)

/-- An environment of the recursor's parameters, extended by a number, fits the spine's
context. -/
theorem fits_recCons {ρ : Env 3} (fits : Fits X.reading cRecTele ρ) {ν : Ideal}
    (hν : projT natI ν = ν) : Fits X.reading cRecSpineTele (Env.cons ν ρ) :=
  ⟨fits, by rw [X.cinterp_cnum]; exact Ideal.typeGenerated_natI,
    by rw [X.cinterp_cnum]; exact hν⟩

/-- **The recursor at the approximants of its numeral recursion.** Let the substitutions of
the recursor's parameters be related over an environment fitting them. For numbers related
as far as a number observes, the recursor's spines at them are related at the motive at the
left number, as far as every token of the `k`-th approximant of the numeral recursion at
that number, typed at the motive there, observes.

At zero, the spines reduce to the zero cases, related at `P zero`; the motive's adequacy at
the numbers `zero` and `n`, related as far as zero observes, converts the relation to
`P n`. At a successor they reduce to the step at the predecessor and the recursive value,
adequate over the context extended by them, the recursive values related by the claim at
the predecessor; the motive's adequacy converts the relation from `P (suc m)` to `P n`. -/
theorem rec_claim (formed : CCtxFormed X.church Δ) {ρ : Env 3}
    (fits : Fits X.reading cRecTele ρ) {τ τ' : CSub Tower.Head 3 m}
    (hτ : SubstRel X.reading X.head cRecTele ρ Δ τ τ') :
    ∀ (k : Nat) (ν : Ideal) (N N' : CTm Tower.Head m), projT natI ν = ν →
      CEqual X.church Δ N N' cnum → (∀ x, ν.Mem x → RT X.head Δ true x cnum N N') →
      ∀ y, (natRecApprox (ρ 1) (nrStep (ρ 2) (ρ 0)) k ν).Mem y → TypedAt (Ideal.app (ρ 2) ν) y →
        RT X.head Δ true y (cMotiveAt.subst (CTm.consSub N τ))
          (cRecSpine.subst (CTm.consSub N τ)) (cRecSpine.subst (CTm.consSub N' τ'))
  | 0, _, _, _, _, _, _, _, hy, _ => RT.of_vacuous hy
  | k + 1, ν, N, N', hνT, hNN, hν, y, hy, hyT => by
      have mor : CSubstMor X.church cRecTele Δ τ := hτ.1.1
      have mor' : CSubstMor X.church cRecTele Δ τ' :=
        (hτ.symm X.levels formed).1.1
      obtain ⟨tN, -⟩ := CEqual.typed X.levels hNN formed
      have eMotive : CTypeEq X.church Δ (cMotiveAt.subst (CTm.consSub N' τ'))
          (cMotiveAt.subst (CTm.consSub N τ)) :=
        ⟨_, X.sort _, .symm (CDerivable.functional (X.lift cmotiveAt_typed) (CSubstEq.cons hτ.1 tN hNN))⟩
      -- a number does not reduce both to zero and to a successor
      have both : ν.Mem (.tag .zero) → ν.Mem (.tag .succ) → False := fun hz hs => by
        obtain ⟨-, h0, -⟩ := RT.tm_zero_iff.1 (hν _ hz)
        obtain ⟨m₀, m₀', -, hs0, -, -⟩ := RT.tm_succTag_iff.1 (hν _ hs)
        have e := CRedTm.nf_unique h0 hs0 X.head.normal_zero
          (X.head.normal_suc _)
        cases e
      rw [natRecApprox] at hy
      cases hvac : ent [] y with
      | true => exact RT.of_vacuous hvac
      | false =>
      -- a generator that observes something names a tag of the number
      have tag : ν.Mem (.tag .zero) ∨ ν.Mem (.tag .succ) := by
        obtain ⟨v, hv, e⟩ := hy
        obtain ⟨g, hg, -, hgn⟩ := source_of_ent e hvac
        rcases hv g hg with ⟨w, hw, ew⟩ | ⟨w, hw, ew⟩
        · cases w with
          | nil => rw [ew] at hgn; cases hgn
          | cons r _ => exact .inl (hw r List.mem_cons_self).1
        · cases w with
          | nil => rw [ew] at hgn; cases hgn
          | cons r _ => exact .inr (hw r List.mem_cons_self).1
      rcases tag with hz | hs
      · -- zero
        have hs : ¬ ν.Mem (.tag .succ) := both hz
        rw [Ideal.whenTag_of_mem hz, Ideal.whenTag_of_not_mem hs, Ideal.join_bot] at hy
        obtain ⟨-, hN0, hN'0⟩ := RT.tm_zero_iff.1 (hν _ hz)
        -- the number lies below zero
        have hν0 : ν ≤ zeroI := le_zeroI hνT fun g hg hgT => by
          rcases tyTok_nat_cases (Ideal.tyTok_nat_of_typedAt hgT) with rfl | rfl | ⟨s, rfl, -⟩
          · exact .inl rfl
          · exact absurd hg hs
          · rcases RT.tm_argSucc_iff.1 (hν _ hg) with hvac | ⟨m₁, m₁', hsucc, -, -⟩
            · exact .inr hvac
            · exfalso
              have e := CRedTm.nf_unique hN0 hsucc.2.1 X.head.normal_zero
                (X.head.normal_suc _)
              cases e
        have hyT0 : TypedAt (Ideal.app (ρ 2) zeroI) y :=
          Ideal.TypedAt.mono (Ideal.app_mono (Ideal.le_refl _) hν0) hyT
        -- the zero cases, related at `P zero`
        have hzRel : RT X.head Δ true y (cMotiveAt.subst (CTm.consSub czero τ))
            (τ 1) (τ' 1) :=
          (hτ.2 1).2.2 y hy (by
            show TypedAt (Ideal.app (ρ 2) (X.reading.const zeroN)) y
            rw [X.reading_zero]
            exact hyT0)
        -- the motive at `zero` and at `n`
        have hsub : SubstRel X.reading X.head cRecSpineTele
            (Env.cons zeroI ρ) Δ (CTm.consSub czero τ) (CTm.consSub N τ) :=
          SubstRel.recCons X formed hτ.left (.symm hN0.2) fun x hx => by
            refine RT.closed' hx fun q hq => ?_
            rw [List.mem_singleton.1 hq]
            exact RT.tm_zero_iff.2 ⟨CRedTy.refl ⟨_, X.sort _, X.lift cnum_typed⟩,
              CRedTm.refl (X.lift czero_typed), hN0⟩
        obtain ⟨a, ha, hau, hta⟩ := hyT0
        have hN := (RT.conv_iff X.levels formed hau hta
          (fun r hr => adequateType_motiveAt X _ (fits_recCons X fits Ideal.projT_natI_zeroI) formed
            hsub r (ha r hr) (hau r hr))
          ⟨_, X.sort _, CDerivable.functional (X.lift cmotiveAt_typed) hsub.1⟩).1 hzRel
        exact RT.expand X.levels formed (CRedTm.recZero X formed mor hN0)
          ((CRedTm.recZero X formed mor' hN'0).convType eMotive) hN
      · -- successor
        have hz : ¬ ν.Mem (.tag .zero) := fun hz => both hz hs
        rw [Ideal.whenTag_of_not_mem hz, Ideal.whenTag_of_mem hs, Ideal.bot_join] at hy
        obtain ⟨m₀, m₀', hT, hNs, hN's, hm⟩ := RT.tm_succTag_iff.1 (hν _ hs)
        obtain ⟨tm₀, tm₀'⟩ := CEqual.typed X.levels hm formed
        have hpν := projT_natI_predI hνT
        -- the predecessors, related as far as the predecessor observes
        have hpred : ∀ x, (predI ν).Mem x → RT X.head Δ true x cnum m₀ m₀' := by
          intro x hx
          obtain ⟨v, hv, e⟩ := hx
          refine RT.closed' e fun s hs' => ?_
          obtain ⟨C, hC⟩ := hv s hs'
          rcases RT.tm_argSucc_iff.1 (hν _ hC) with hvac | ⟨m₁, m₁', hsucc, -, hrel⟩
          · exact RT.of_vacuous (vacuous_arg hvac)
          obtain ⟨rfl, rfl⟩ := SuccRed.align ⟨hT, hNs, hN's, hm⟩ hsucc
          exact hrel rfl
        have ih := rec_claim formed fits hτ k (predI ν) m₀ m₀' hpν hm hpred
        -- the substitutions of the step's context, related
        have hσv := SubstRel.recCons X formed hτ hm hpred
        have hσ₂ : SubstRel X.reading X.head cRecStepTele
            (Env.cons (projT (Ideal.app (ρ 2) (predI ν))
              (natRecApprox (ρ 1) (nrStep (ρ 2) (ρ 0)) k (predI ν))) (Env.cons (predI ν) ρ)) Δ
            (CTm.consSub (cRecSpine.subst (CTm.consSub m₀ τ)) (CTm.consSub m₀ τ))
            (CTm.consSub (cRecSpine.subst (CTm.consSub m₀' τ')) (CTm.consSub m₀' τ')) :=
          SubstRel.cons X.levels formed hσv
            (CDerivable.functional (X.lift cRecSpine_typed) hσv.1)
            ⟨_, X.sort _, CDerivable.functional (X.lift cmotiveAt_typed) hσv.1⟩
            (fun r hr hrU => adequateType_motiveAt X _ (fits_recCons X fits hpν) formed hσv r hr hrU)
            (fun s hs' _ => by
              obtain ⟨v, hv, hvT, e⟩ := Ideal.projT_eq_iSup.1 hs'
              exact RT.closed' e fun g hg => ih g (hv g hg) (hvT g hg))
        have fits₂ : Fits X.reading cRecStepTele
            (Env.cons (projT (Ideal.app (ρ 2) (predI ν))
              (natRecApprox (ρ 1) (nrStep (ρ 2) (ρ 0)) k (predI ν))) (Env.cons (predI ν) ρ)) :=
          ⟨fits_recCons X fits hpν, X.soundnessFacts.typeGenerated_of_head (X.sort _)
            (X.lift cmotiveAt_typed) (fits_recCons X fits hpν), Ideal.projT_projT _ _⟩
        -- the typing at the successor of the predecessor
        have hyTs : TypedAt (Ideal.app (ρ 2) (succI (predI ν))) y :=
          Ideal.TypedAt.mono (Ideal.app_mono (Ideal.le_refl _) (le_succI_predI hνT hz)) hyT
        have hyT₂ : TypedAt (cinterp X.reading cRecStepType
            (Env.cons (projT (Ideal.app (ρ 2) (predI ν))
              (natRecApprox (ρ 1) (nrStep (ρ 2) (ρ 0)) k (predI ν))) (Env.cons (predI ν) ρ))) y := by
          show TypedAt (Ideal.app (ρ 2) (Ideal.app (X.reading.const sucN) (predI ν))) y
          rw [X.reading_const (by decide), objectChurchReading_suc, app_sucConst objectChurchReading
            numNames objectChurchReading_num, hpν]
          exact hyTs
        have hstep := adequate_recStepBody X _ fits₂ formed hσ₂ y hy hyT₂
        -- the motive at `suc m` and at `n`
        have hSR : SuccRed X.head Δ cnum (csuc m₀) N m₀ m₀ :=
          ⟨hT, CRedTm.refl (X.csuc_typed tm₀), hNs, .refl tm₀⟩
        have hsub : SubstRel X.reading X.head cRecSpineTele
            (Env.cons (succI (predI ν)) ρ) Δ (CTm.consSub (csuc m₀) τ) (CTm.consSub N τ) :=
          SubstRel.recCons X formed hτ.left (.symm hNs.2) fun x hx => by
            obtain ⟨v, hv, e⟩ := hx
            refine RT.closed' e fun g hg => ?_
            rcases hv g hg with rfl | ⟨s', rfl, hs'⟩
            · exact RT.tm_succTag_iff.2 ⟨m₀, m₀, hSR⟩
            · exact RT.tm_argSucc_iff.2 (.inr ⟨m₀, m₀, hSR, fun c hc => absurd hc List.not_mem_nil,
                fun _ => RT.left (hpred s' hs')⟩)
        obtain ⟨a, ha, hau, hta⟩ := hyTs
        have hN := (RT.conv_iff X.levels formed hau hta
          (fun r hr => adequateType_motiveAt X _ (fits_recCons X fits (Ideal.projT_natI_succI hpν))
            formed hsub r (ha r hr) (hau r hr))
          ⟨_, X.sort _, CDerivable.functional (X.lift cmotiveAt_typed) hsub.1⟩).1 hstep
        exact RT.expand X.levels formed (CRedTm.recSuc X formed mor tm₀ hNs)
          ((CRedTm.recSuc X formed mor' tm₀' hN's).convType eMotive) hN

/-- `num-rec` is read in every extension as in the object package. -/
theorem ObjectExtension.reading_numRec :
    X.reading.const numRecName = nrConst X.reading numNames := by
  rw [X.reading_const (by decide), objectChurchReading_numRec]
  unfold nrConst nrTypeI
  rw [X.cinterp_eq _ (by decide)]

/-- **The recursor's spine is adequate** at the motive at the numeral: its denotation is
numeral recursion at the numeral, projected onto the motive there, and each token of the
recursion lies in an approximant (`rec_claim`). -/
theorem adequate_recSpine : Adequate X.reading X.head cRecSpineTele cRecSpine cMotiveAt := by
  intro ρ' fits' m Δ σ σ' formed hσ s hs hsT
  obtain ⟨x, ρ, rfl⟩ : ∃ x ρ, ρ' = Env.cons x ρ := ⟨_, _, env_eq_cons_tail ρ'⟩
  obtain ⟨N, τ, rfl⟩ : ∃ N τ, σ = CTm.consSub N τ := ⟨_, _, CTm.eq_consSub_tail σ⟩
  obtain ⟨N', τ', rfl⟩ : ∃ N' τ', σ' = CTm.consSub N' τ' := ⟨_, _, CTm.eq_consSub_tail σ'⟩
  obtain ⟨hτ, hNN, hNx⟩ := SubstRel.of_cons hσ
  have fits : Fits X.reading cRecTele ρ := fits'.1
  have hx : projT natI x = x := by
    have h := fits'.2.2
    rwa [X.cinterp_cnum] at h
  -- the denotation of the spine
  have spine : Ideal.SpineTyped (nrTypeI X.reading numNames) [ρ 2, ρ 1, ρ 0] :=
    (spineTyped_cinterp_pi _ _ _ _ _ _).2 ⟨fits.1.1.2.2, (spineTyped_cinterp_pi _ _ _ _ _ _).2
      ⟨fits.1.2.2, (spineTyped_cinterp_pi _ _ _ _ _ _).2 ⟨fits.2.2, trivial⟩⟩⟩
  have den : cinterp X.reading cRecSpine (Env.cons x ρ) =
      projT (Ideal.app (ρ 2) x) (natRec (ρ 1) (nrStep (ρ 2) (ρ 0)) x) := by
    change Ideal.appSpine (X.reading.const numRecName) [ρ 2, ρ 1, ρ 0, x] = _
    rw [X.reading_numRec, appSpine_nrConst spine X.reading_num, hx]
  rw [den] at hs
  change TypedAt (Ideal.app (ρ 2) x) s at hsT
  obtain ⟨v, hvI, hvT, e⟩ := Ideal.projT_eq_iSup.1 hs
  refine RT.closed' e fun g hg => ?_
  obtain ⟨k, hk⟩ := (Ideal.mem_natRec (Ideal.cont₂_nrStep _ _)).1 (hvI g hg)
  have hν : ∀ y, x.Mem y → RT X.head Δ true y cnum N N' := by
    intro y hy
    rw [← hx] at hy
    obtain ⟨w, hw, hwT, ew⟩ := Ideal.projT_eq_iSup.1 hy
    refine RT.closed' ew fun t ht => ?_
    exact hNx t (hw t ht) (by rw [X.cinterp_cnum]; exact hwT t ht)
  exact rec_claim X formed fits hτ k x N N' hx hNN hν g hk (hvT g hg)

end Claim

/-- **`num-rec` is adequate**, through its spine at the variables of its telescope. -/
theorem constAdequateAt_numRec : ConstAdequateAt X.reading X.head numRecName :=
  ConstAdequateAt.of_spine (Θ := cRecSpineTele) (T := cMotiveAt) X.levels X.soundnessFacts
    (X.sub.constantType
      (objectChurch_declared (c := numRecName) (T := Package.numRecType) (by decide) rfl))
    (X.lift cRecSpine_typed) (adequate_recSpine X)

/-! ## Every constant of the object package is adequate -/

/-- **Every constant of the object package is adequate in every extension.** -/
theorem ObjectExtension.objectConsts_adequate :
    ∀ {c : DeclName} {D : CTm Tower.Head 0}, objectChurch.constantType c = some D →
      ConstAdequateAt X.reading X.head c :=
  X.objectConsts_adequate_of (constAdequateAt_power X) (constAdequateAt_pow X)
    (constAdequateAt_numRec X) (constAdequateAt_transport X) (constAdequateAt_compose X)
    (constAdequateAt_returnIter X) (constAdequateAt_sucStep X) (constAdequateAt_holds X)
    (constAdequateAt_imp X) (constAdequateAt_eq X)

/-- **Every constant of the object package is adequate.** -/
theorem objectChurch_constAdequate : ConstAdequate objectChurchReading objectHeadReduction :=
  fun declared => objectExtension.objectConsts_adequate declared declared

/-- **The fundamental lemma at the object package**, with no hypothesis: every derivable
statement is valid over a formed context. -/
theorem objectChurch_fundamental {J : CStatement Tower.Head} (derivation : CDerivable objectChurch J)
    (formed : J.CtxFormed objectChurch) : J.Valid objectChurchReading objectHeadReduction :=
  CDerivable.valid_of_constAdequate ConvRules.objectLevels objectChurchReading_valid
    objectExtension.groundHeads objectRules_groundHeadEq objectExtension.decoderStuck
    objectChurch_constAdequate derivation formed

/-- **The facts about the weak-head forms of the object package's annotated types**, with
no hypothesis. -/
theorem objectFormFacts : CFormFacts objectChurch objectRoles :=
  ObjectExtension.formFacts (X := objectExtension) objectChurch_constAdequate

/-- **The injectivity and no-confusion of the object package's annotated type formers.** -/
theorem objectFormerFacts : CFormerFacts objectChurch :=
  ObjectExtension.formerFacts (X := objectExtension) objectChurch_constAdequate

/-- **Coherence of annotations for the object package**: two annotated terms with one
erasure, typed at one type, are equal at it. -/
theorem objectCoherence {n : Nat} {Γ : CCtx Tower.Head n} (formed : CCtxFormed objectChurch Γ)
    {t t' A : CTm Tower.Head n} (typing : CTyped objectChurch Γ t A)
    (typing' : CTyped objectChurch Γ t' A) (same : t.erase = t'.erase) :
    CEqual objectChurch Γ t t' A :=
  objectChurch_coherence_of_constAdequate objectChurch_constAdequate formed typing typing' same

/-- **The object package's root steps preserve types.** -/
theorem objectRootPreserving : CRootPreserving objectChurch :=
  objectChurch_rootPreserving_of_constAdequate objectChurch_constAdequate

/-- **The typing of a redex of the object package gives the premises of its root step**: the
typings of the instances of the schema's metavariables and the equations of its reflexivity
positions, by pattern inversion. -/
theorem objectRootPremised : CRootPremised objectChurch :=
  fun formed step typing => objectChurch_premisedIn (ChurchRulesSub.refl _)
    (objectChurch_within rfl) objectFormerFacts ConvRules.objectLevels formed step typing

/-- **The object package's root steps of typed terms are equalities.** -/
theorem objectRootAdmitted : CRootAdmitted objectChurch :=
  objectRootPreserving.admitted objectRootPremised

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
