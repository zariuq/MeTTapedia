import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectHeadReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationConstants

/-!
# Adequacy of object constants: the successor move, `keepCert`, the iterator, the quantifiers

**The package conditions.** The heads typed by a head are universes or the legacy ground
head, read as the ground type and one of the rigid ground types
(`objectRigid_groundHeads`); head equality is trivial on the heads that are not
universes (`objectRules_groundHeadEq`). The decoder applied to a head is a weak-head
normal form (`holds_head_whnf`), so it is stuck at universes
(`objectHeadReduction_decoderStuck`), and heads equal by head equality are valid as equal
at every type at which both are valid (`CStatement.Valid.objectHeadEq`).

**The successor move** (`constAdequateAt_sucMove`): `sucMove` is adequate, given the
validity of the typing of its right side at its codomain `eqAt (suc n)`
(`csucMoveRhs_typed`). Its applications reduce to its right side by one root step
(`sucMove_teleReduces`).

**`keepCert`** (`constAdequateAt_keep`) is adequate: its right side, the pair of the value
and its evidence, is adequate at `Σ (y : A). P y` (`adequate_keepRhs`), and its
applications reduce to it by one root step (`keep_teleReduces`).

**The iterator** (`constAdequateAt_iter`) is adequate. Its applications reduce along its
parameters (`iter_teleReduces`) by its zero and successor equations (`iterZero_step`,
`iterSuc_step`); its zero case and its successor step are adequate
(`adequate_iterZeroBody`, `adequate_iterStepBody`). By recursion on the approximants of
the numeral recursion at a compact numeral, the iterator at numbers related as far as the
numeral observes is related to itself at its type at a count (`iter_claim`).

**The quantifiers** (`constAdequateAt_all`): the quantifier at every simple type is
adequate, in particular at `num → num` (`constAdequateAt_allNumNum`). Every simple type is
an adequate type over every context (`adequateType_typeAt`), and decoding a quantified code
is a root step (`objectChurch_decodeAll`).
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
open Presentation.TypedEquality.Impredicative.Domain.Ideal (projT TypedAt principal natRecApprox natRec natI)
open TelescopeAbstraction (applyClosed)
open FormationSensitiveHOLInterface (typeAt)
open Package (jName eqAtName sucMoveName keepName iterName eqAtTelescope)
open Mettapedia.Logic

namespace CodeModel

/-! ## The package conditions -/

/-- **The heads typed by a head are universes or rigid ground types** at the object
package: the legacy ground head is read as the ground type and is a rigid ground type. -/
theorem objectRigid_groundHeads : objectRigid.GroundHeads objectChurchReading := by
  intro h u typing
  cases typing with
  | legacyGround => exact .inr ⟨rfl, fun {_} => .inr rfl⟩
  | sort l => exact .inl (.sort l)

/-- **Head equality is trivial on the heads that are not universes** at the object
package: the legacy ground head is equal only to itself. -/
theorem objectRules_groundHeadEq : GroundHeadEq objectRules := by
  intro h h' same
  cases h <;> cases h'
  · exact .inr rfl
  · exact same.elim
  · exact same.elim
  · exact .inl (.sort _)

/-- The decoder applied to a head is a weak-head normal form of the object package: no
schema's left side is an instance of it (the declared computations are apart from the
decoder's redexes, and the decoder's own left sides decode applications), its function
is a spine below the decoder's arity, and a head takes no step. -/
theorem holds_head_whnf {n : Nat} (h : Tower.Head) :
    Whnf objectRules objectRoles (.app (.const holdsN) (.head h) : Tower.Tm n) := by
  intro u step
  generalize ht : (Tm.app (.const holdsN) (.head h) : Tower.Tm n) = t at step
  cases step with
  | beta => cases ht
  | fstPair => cases ht
  | sndPair => cases ht
  | fst => cases ht
  | snd => cases ht
  | appFun s =>
      injection ht with _ hf _
      subst hf
      exact partialSpine_whnf objectShape objectRoles_holds (args := []) Nat.zero_lt_one _ s
  | root s =>
      subst ht
      have ss := objectRules_presents.1 s
      generalize hl : (Tm.app (.const holdsN) (.head h) : Tower.Tm n) = l at ss
      cases ss with
      | instantiate rule τ =>
          rcases rule with rule | rule
          · obtain ⟨p, mem, rule⟩ := DeclaredComputation.mem_of_schemaUnionAll rule
            have hA := List.all_eq_true.1 specLeftSides_apart_holds _ (mem_specLeftSides mem rule)
            exact Apart.subst_ne _ _ hA τ (fun _ => .head h) hl.symm
          · rcases rule with rule | ⟨a, A, _, rule⟩ | ⟨e, A, _, rule⟩ <;> cases rule <;>
              (injection hl with _ _ h₂; simp [Presentation.subst] at h₂)
  | scrutinee role length focus inner =>
      have e : Normalization.appSpine (.const _) _ = Normalization.appSpine (.const holdsN)
          [(.head h : Tower.Tm n)] := ht.symm
      obtain ⟨rfl, rfl⟩ := Normalization.appSpine_const_injective e
      rw [objectRoles_holds] at role
      injection role with harity hinspect
      subst harity hinspect
      obtain ⟨before, after, hb, hv, -, -⟩ := InspectTree.Focus.single focus
      rw [List.length_eq_zero_iff] at hb
      subst hb
      injection hv with ha _
      subst ha
      exact head_whnf objectShape h _ inner

/-- **The decoder is stuck at universes** in the object package's weak-head reduction. -/
theorem objectHeadReduction_decoderStuck : objectHeadReduction.DecoderStuckAtUniverses := by
  intro n h _ u step
  exact holds_head_whnf h _ (CWhStepR.erase step)

/-- **Validity of head equality** at the object package: heads equal by head equality are
related at every type at which both are valid. -/
theorem CStatement.Valid.objectHeadEq {n : Nat} {Γ : CCtx Tower.Head n} {h h' : Tower.Head}
    {A : CTm Tower.Head n} (same : objectRules.headEq h h')
    (hh : (CStatement.typing Γ (.head h) A).Valid objectChurchReading objectHeadReduction)
    (hh' : (CStatement.typing Γ (.head h') A).Valid objectChurchReading objectHeadReduction) :
    (CStatement.equality Γ (.head h) (.head h') A).Valid objectChurchReading
      objectHeadReduction :=
  Annotated.CStatement.Valid.headEq ConvRules.objectLevels objectChurch_soundnessFacts
    objectRules_groundHeadEq objectHeadReduction_decoderStuck same hh hh'

/-! ## The successor move -/

/-- The right side of `sucMove`, as the object package elaborates it:
`J num (add zero n) (λ y p. Id num (suc (add zero n)) (suc y)) (refl (suc (add zero n))) n e`. -/
abbrev cSucMoveRhs : CTm Tower.Head 2 :=
  .app (.app (.app (.app (.app (.app (.const jName) cnum) (cadd czero (.var 1))) cSucMotive)
    (.refl (csuc (cadd czero (.var 1))))) (.var 1)) (.var 0)

/-- The codomain of `sucMove`: `eqAt (suc n)`. -/
abbrev cSucMoveCod : CTm Tower.Head 2 := ceqAt (csuc (.var 1))

/-- `sucMove` is declared at `Π (n : num). eqAt n → eqAt (suc n)`. -/
theorem sucMove_declared :
    objectChurch.constantType sucMoveName = some (pisCtx cEqAtTele cSucMoveCod) :=
  objectChurch_declared (T := Package.sucMoveType) (by decide) (by decide)

/-- `sucMove` denotes the abstraction of its right side, projected onto its declared
type. -/
theorem objectChurchReading_sucMove :
    objectChurchReading.const sucMoveName =
      defConst objectChurchReading cEqAtTele cSucMoveCod cSucMoveRhs := by
  have h := objectChurchReading_def (f := sucMoveName) (tag := .sucMove) (by decide)
    (Θ := eqAtTelescope) (rhs := sucMoveRhs) (T := cSucMoveCod) (by decide) rfl
  have e : defRhs sucMoveName eqAtTelescope sucMoveRhs = cSucMoveRhs := by
    decide
  rw [h, e]
  rfl

/-- **The right side of `sucMove` is typed at its codomain** in its telescope: the typing
of the definition's template, whose conversions are β, the equation of `eqAt` and the
successor equation of addition. -/
theorem csucMoveRhs_typed : CTyped objectChurch cEqAtTele cSucMoveRhs cSucMoveCod := by
  obtain ⟨Θ, T, know, left, typed⟩ := sucMove_template
  have kn : ∀ i, patternKnowledge objectDecls none
      (applyClosed eqAtTelescope Presentation.ids (.const sucMoveName)) i =
        some (cEqAtTele.lookup i) := by
    decide
  have hΘ : ∀ i, Θ.lookup i = cEqAtTele.lookup i := fun i =>
    Option.some.inj ((know i).symm.trans (kn i))
  have hT : T = cSucMoveCod := Option.some.inj (left.symm.trans (by decide))
  have he : elabRight objectDecls (applyClosed eqAtTelescope Presentation.ids (.const sucMoveName))
      sucMoveRhs = cSucMoveRhs := by
    decide
  have h := CTyped.substitute (Δ := cEqAtTele) (σ := CTm.ids) typed fun i => by
    rw [hΘ i, CTm.subst_ids]
    exact .var i
  rw [CTm.subst_ids, CTm.subst_ids, he, hT] at h
  exact h

/-- **The applications of `sucMove` reduce to its right side**, by its root step, at its
codomain. -/
theorem sucMove_teleReduces {K : RigidTypes objectChurch} (H : HeadReduction objectChurch K)
    {m : Nat} {Δ : CCtx Tower.Head m} :
    TeleReduces H Δ (CCtx.toTele cEqAtTele) cSucMoveCod cSucMoveRhs (.const sucMoveName)
      fun i => .var (Fin.elim0 i) := by
  intro N tN e te
  have mor : CSubstMor objectChurch cEqAtTele Δ
      (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i))) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact te
    · obtain rfl : j = 0 := Subsingleton.elim j 0
      exact tN
  have eL : elabLeft objectDecls
      (applyClosed eqAtTelescope Presentation.ids (.const sucMoveName)) =
      (CTm.appSpine (.const sucMoveName) [.var 1, .var 0] : CTm Tower.Head 2) := by
    decide
  have eR : elabRight objectDecls
      (applyClosed eqAtTelescope Presentation.ids (.const sucMoveName))
      sucMoveRhs = cSucMoveRhs := by
    decide
  have step : objectChurch.computation.step (.app (.app (.const sucMoveName) N) e)
      (cSucMoveRhs.subst (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i)))) := by
    have s := objectChurch_step_of_spec
      (List.getElem_mem (l := computationSpecs) (n := 5) (by decide))
      (L := applyClosed eqAtTelescope Presentation.ids (.const sucMoveName))
      (R := sucMoveRhs) rfl
      (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i)))
    rw [eL, eR] at s
    exact s
  have admits : objectChurch.Admits Δ (.app (.app (.const sucMoveName) N) e)
      (cSucMoveRhs.subst (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i)))) := by
    have a := objectChurch_admits_of_mor rfl
      (List.getElem_mem (l := computationSpecs) (n := 5) (by decide))
      (L := applyClosed eqAtTelescope Presentation.ids (.const sucMoveName))
      (R := sucMoveRhs) rfl
      (CTm.consSub e (CTm.consSub N fun i => .var (Fin.elim0 i))) (by decide) (by decide) mor
    rw [eL, eR] at a
    exact a
  have t₁ := CDerivable.appElim (A := cnum) (B := .pi (ceqAt (.var 0)) (ceqAt (csuc (.var 1))))
    (csucMove_typed (Γ := Δ)) tN
  have t₂ := CDerivable.appElim t₁ te
  have eTy : CTm.inst0 e (ceqAt (csuc (N.rename wk))) = ceqAt (csuc N) := by
    change CTm.app _ (CTm.app _ (CTm.inst0 e (N.rename wk))) = _
    rw [CTm.inst0_rename_wk]
    rfl
  have tl : CTyped objectChurch Δ (.app (.app (.const sucMoveName) N) e) (ceqAt (csuc N)) := by
    rw [← eTy]
    exact t₂
  exact ⟨.single (H.root step), .rootAdmitted step admits tl (csucMoveRhs_typed.substitute mor)⟩

/-- **The successor move is adequate**, given the validity of the typing of its right side
at its codomain `eqAt (suc n)` in its telescope `n : num, e : eqAt n`: head expansion
along its root step, and the relation of its right side. -/
theorem constAdequateAt_sucMove {K : RigidTypes objectChurch} {H : HeadReduction objectChurch K}
    (rhs : (CStatement.typing cEqAtTele cSucMoveRhs cSucMoveCod).Valid objectChurchReading H) :
    ConstAdequateAt objectChurchReading H sucMoveName :=
  ConstAdequateAt.ofDefinition ConvRules.objectLevels objectChurch_soundnessFacts sucMove_declared
    objectChurchReading_sucMove rhs.1 fun _ => sucMove_teleReduces H

/-! ## The iterator: typings -/

/-- The iterator's parameters after its count, as a telescope over `n` variables: the
carrier, the family, the step, the value and its evidence. -/
def iterParams (n : Nat) : CTele Tower.Head n (n + 5) :=
  .cons cU0 (.cons (.pi (.var 0) cU0) (.cons cStep (.cons (.var 2)
    (.cons (.app (.var 2) (.var 0)) .nil))))

/-- The iterator's codomain after its parameters, `Σ (y : A). P y`. -/
abbrev iterCodAt {n : Nat} : CTm Tower.Head (n + 5) := .sigma (.var 4) (.app (.var 4) (.var 0))

/-- The substitution of the iterator's schema variables: the count, the carrier, the
family, the step, the value and its evidence. -/
abbrev iterSub {m : Nat} (q A P st x e : CTm Tower.Head m) : CSub Tower.Head 6 m :=
  CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P (CTm.consSub A
    (CTm.consSub q fun i => .var (Fin.elim0 i))))))

/-- The type of the iterator at a count is a type of `U₁`. -/
theorem citerTail_formed : CTyped objectChurch .nil iterTail cU1 :=
  cpiT cU0_typed (cpiT (cpiT (craise (.var 0)) cU0_typed)
    (cpiT (craise cstepFamily_formed)
      (cpiT (craise (.var 2))
        (cpiT (craise (.appElim (B := cU0) (.var 2) (.var 0)))
          (craise (csigmaT (.var 4) (.appElim (B := cU0) (.var 4) (.var 0))))))))

/-- The declared type of the iterator is the dependent function type over the numbers of
its type at a count. -/
theorem liftTm_iterType : (liftTm Package.iterType : CTm Tower.Head 0) = .pi cnum (iterTail.rename wk) := by
  decide

theorem liftClosed_iterType {n : Nat} :
    ((liftTm Package.iterType).liftClosed : CTm Tower.Head n) = .pi cnum iterTail.liftClosed := by
  rw [liftTm_iterType]
  show CTm.pi cnum ((iterTail.rename wk).rename (liftRen Fin.elim0)) = _
  rw [CTm.rename_comp, CTm.rename_closed]

/-- The iterator at its type over the numbers, the type at a count lifted. -/
theorem citer_typed' {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectChurch Γ (.const iterName) (.pi cnum iterTail.liftClosed) := by
  rw [← liftClosed_iterType]
  exact citer_typed

/-- **The iterator's spine at its schema variables is typed** at `Σ (y : A). P y`, in the
context of the iterator's successor equation. -/
theorem citerSpine_typed :
    CTyped objectChurch cIterSucTele
      (CTm.appSpine (.const iterName) [.var 5, .var 4, .var 3, .var 2, .var 1, .var 0])
      (.sigma (.var 4) (.app (.var 4) (.var 0))) := by
  have t₁ := CDerivable.appElim (citer_typed (Γ := cIterSucTele)) (CDerivable.var 5)
  have t₂ := CDerivable.appElim t₁ (CDerivable.var 4)
  have t₃ := CDerivable.appElim t₂ (CDerivable.var 3)
  have t₄ := CDerivable.appElim t₃ (CDerivable.var 2)
  have t₅ := CDerivable.appElim t₄ (CDerivable.var 1)
  exact CDerivable.appElim t₅ (CDerivable.var 0)

/-! ## The iterator: reduction along its parameters -/

/-- **The iterator reduces along its parameters**: applied to a count that reduces to `q`
and to typed parameters, the iterator reduces, by the scrutinee congruence and then a
root step at `q` admitted at those parameters, to a typed contractum. -/
theorem iter_teleReduces {n m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed objectChurch Δ)
    {σ : CSub Tower.Head n m} {E : CTm Tower.Head (n + 5)} {M q : CTm Tower.Head m}
    (hM : CRedTm objectHeadReduction Δ M q cnum)
    (root : ∀ A P st x e : CTm Tower.Head m, objectChurch.computation.step
      (CTm.appSpine (.const iterName) [q, A, P, st, x, e])
      (E.subst (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P (CTm.consSub A σ)))))))
    (admits : ∀ A P st x e : CTm Tower.Head m,
      (∀ {r : CTm Tower.Head m}, CTyped objectChurch Δ r cnum →
        CSubstMor objectChurch cIterSucTele Δ (iterSub r A P st x e)) →
      objectChurch.Admits Δ (CTm.appSpine (.const iterName) [q, A, P, st, x, e])
        (E.subst (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P (CTm.consSub A σ)))))))
    (typedE : ∀ A P st x e : CTm Tower.Head m,
      (∀ {r : CTm Tower.Head m}, CTyped objectChurch Δ r cnum →
        CSubstMor objectChurch cIterSucTele Δ (iterSub r A P st x e)) →
      CTyped objectChurch Δ
        (E.subst (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P (CTm.consSub A σ))))))
        ((iterCodAt : CTm Tower.Head (n + 5)).subst
          (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P (CTm.consSub A σ))))))) :
    TeleReduces objectHeadReduction Δ (iterParams n) iterCodAt E (.app (.const iterName) M) σ := by
  intro A tA P tP st tst x tx e te
  obtain ⟨tM, tq⟩ := CEqual.typed ConvRules.objectLevels hM.2 formed
  have morOf : ∀ {r : CTm Tower.Head m}, CTyped objectChurch Δ r cnum →
      CSubstMor objectChurch cIterSucTele Δ (iterSub r A P st x e) := by
    intro r tr i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact te
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tx
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tst
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tP
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tA
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tr
    exact i.elim0
  have eqSpine : CEqual objectChurch Δ (CTm.appSpine (.const iterName) [M, A, P, st, x, e])
      (CTm.appSpine (.const iterName) [q, A, P, st, x, e])
      ((.sigma (.var 4) (.app (.var 4) (.var 0)) : CTm Tower.Head 6).subst (iterSub M A P st x e)) := by
    have hEq : CSubstEq objectChurch cIterSucTele Δ (iterSub M A P st x e)
        (iterSub q A P st x e) := by
      refine ⟨morOf tM, fun i => ?_⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .refl te
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .refl tx
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .refl tst
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .refl tP
      refine Fin.cases ?_ (fun i => ?_) i
      · exact .refl tA
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hM.2
      exact i.elim0
    exact CDerivable.functional citerSpine_typed hEq
  have tSpine := citerSpine_typed.substitute (morOf tq)
  have red : Relation.ReflTransGen objectHeadReduction.step
      (CTm.appSpine (.const iterName) [M, A, P, st, x, e])
      (CTm.appSpine (.const iterName) [q, A, P, st, x, e]) :=
    Relation.ReflTransGen.lift (fun t => CTm.appSpine (.const iterName) [t, A, P, st, x, e])
      (fun _ _ h => objectHeadReduction_iter h) _ _ hM.1
  exact ⟨red.tail (objectHeadReduction.root (root A P st x e)),
    .trans eqSpine (.rootAdmitted (root A P st x e) (admits A P st x e morOf) tSpine
      (typedE A P st x e morOf))⟩

/-! ## The iterator: its two root steps -/

/-- The iterator's root step at zero: `iterCert 0 A P step x e ⟶ (x, e)`. -/
theorem iterZero_step {m : Nat} (A P st x e : CTm Tower.Head m) :
    objectChurch.computation.step (CTm.appSpine (.const iterName) [czero, A, P, st, x, e])
      (.pair x e) := by
  have s := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 9) (by decide))
    (L := applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
    (R := Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN []))
    (show recursionSchema iterName ctors iterEntries 0 5 iterBody _ _ from
      ⟨zeroN, [], List.mem_cons_self .., rfl⟩)
    (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P (CTm.consSub A
      fun i => .var (Fin.elim0 i))))))
  rw [iterZero_elabLeft, iterZero_elabRight] at s
  exact s

/-- **The iterator's root step at zero is admitted** along a typed substitution of the
context of its equation. -/
theorem iterZero_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {m : Nat}
    {Γ : CCtx Tower.Head m} {A P st x e : CTm Tower.Head m}
    (mor : CSubstMor Q cIterTele Γ (CTm.consSub e (CTm.consSub x (CTm.consSub st
      (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))))
    (same : Q.computation = objectChurch.computation := by rfl) :
    Q.Admits Γ (CTm.appSpine (.const iterName) [czero, A, P, st, x, e]) (.pair x e) := by
  have a := objectChurch_admits_of_mor same
    (List.getElem_mem (l := computationSpecs) (n := 9) (by decide))
    (L := applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
    (R := Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN []))
    (show recursionSchema iterName ctors iterEntries 0 5 iterBody _ _ from
      ⟨zeroN, [], List.mem_cons_self .., rfl⟩)
    (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P (CTm.consSub A
      fun i => .var (Fin.elim0 i)))))) iterZero_knowledge (by decide) mor
  rw [iterZero_elabLeft, iterZero_elabRight] at a
  exact a

/-- The iterator's contractum at a successor, as elaborated. -/
abbrev cIterSucRhs : CTm Tower.Head 6 :=
  .app (.lam (.sigma (.var 4) (.app (.var 4) (.var 0)))
      (.app (.app (.app (.app (.app (.app (.const iterName) (.var 6)) (.var 5)) (.var 4))
        (.var 3)) (.fst (.var 0))) (.snd (.var 0))))
    (.app (.app (.var 2) (.var 1)) (.var 0))

/-- The substitution writing the recursive value of the step body as the iterator at the
count. -/
abbrev iterRecSub : CSub Tower.Head 6 6 :=
  CTm.consSub (.var 0) (CTm.consSub (.var 1) (CTm.consSub (.var 2) (CTm.consSub (.var 3)
    (CTm.consSub (.var 4) (CTm.consSub (.app (.const iterName) (.var 5)) Fin.elim0)))))

/-- The contractum is the step body at the iterator of the count. -/
theorem cIterSucRhs_eq : cIterSucRhs = iterStepBody.subst iterRecSub := by
  decide

theorem iterRecSub_comp {m : Nat} (q A P st x e : CTm Tower.Head m) :
    (fun i => (iterRecSub i).subst (iterSub q A P st x e)) =
      CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P
        (CTm.consSub A (CTm.consSub (.app (.const iterName) q) fun i => .var (Fin.elim0 i)))))) := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  refine Fin.cases rfl (fun i => ?_) i
  exact i.elim0

/-- The iterator's codomain is unchanged by the recursive-value substitution. -/
theorem iterCodAt_eq : (.sigma (.var 4) (.app (.var 4) (.var 0)) : CTm Tower.Head 6) =
    (iterCodAt : CTm Tower.Head 6).subst iterRecSub := by
  decide

/-- The iterator's codomain at an instance, at the recursive value `iterCert q`. -/
theorem iterCodAt_subst {m : Nat} (q A P st x e : CTm Tower.Head m) :
    (.sigma (.var 4) (.app (.var 4) (.var 0)) : CTm Tower.Head 6).subst (iterSub q A P st x e) =
      (iterCodAt : CTm Tower.Head 6).subst (CTm.consSub e (CTm.consSub x (CTm.consSub st
        (CTm.consSub P (CTm.consSub A (CTm.consSub (.app (.const iterName) q)
          fun i => .var (Fin.elim0 i))))))) := by
  rw [iterCodAt_eq, CTm.subst_comp, iterRecSub_comp]

/-- The contractum at an instance is the step body at the recursive value `iterCert q`. -/
theorem cIterSucRhs_subst {m : Nat} (q A P st x e : CTm Tower.Head m) :
    cIterSucRhs.subst (iterSub q A P st x e) =
      iterStepBody.subst (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P
        (CTm.consSub A (CTm.consSub (.app (.const iterName) q) fun i => .var (Fin.elim0 i))))))) := by
  rw [cIterSucRhs_eq, CTm.subst_comp, iterRecSub_comp]

/-- The iterator's root step at a successor: `iterCert (suc q) A P step x e` computes to
the step body at the recursive value `iterCert q`. -/
theorem iterSuc_step {m : Nat} (q A P st x e : CTm Tower.Head m) :
    objectChurch.computation.step (CTm.appSpine (.const iterName) [csuc q, A, P, st, x, e])
      (iterStepBody.subst (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P
        (CTm.consSub A (CTm.consSub (.app (.const iterName) q) fun i => .var (Fin.elim0 i)))))))) := by
  have s := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 9) (by decide))
    (L := applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
    (R := Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
      (iterBody sucN [.recursive]))
    (show recursionSchema iterName ctors iterEntries 0 5 iterBody _ _ from
      ⟨sucN, [.recursive], List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩)
    (iterSub q A P st x e)
  have eR : elabRight objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) = cIterSucRhs :=
    iterSuc_elabRight
  rw [iterSuc_elabLeft, eR, cIterSucRhs_subst] at s
  exact s

/-- **The iterator's root step at a successor is admitted** along a typed substitution of the
context of its equation. -/
theorem iterSuc_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {m : Nat}
    {Γ : CCtx Tower.Head m} {q A P st x e : CTm Tower.Head m}
    (mor : CSubstMor Q cIterSucTele Γ (iterSub q A P st x e))
    (same : Q.computation = objectChurch.computation := by rfl) :
    Q.Admits Γ (CTm.appSpine (.const iterName) [csuc q, A, P, st, x, e])
      (iterStepBody.subst (CTm.consSub e (CTm.consSub x (CTm.consSub st (CTm.consSub P
        (CTm.consSub A (CTm.consSub (.app (.const iterName) q) fun i => .var (Fin.elim0 i)))))))) := by
  have a := objectChurch_admits_of_mor same
    (List.getElem_mem (l := computationSpecs) (n := 9) (by decide))
    (L := applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
    (R := Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
      (iterBody sucN [.recursive]))
    (show recursionSchema iterName ctors iterEntries 0 5 iterBody _ _ from
      ⟨sucN, [.recursive], List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩)
    (iterSub q A P st x e) iterSuc_knowledge (by decide) mor
  have eR : elabRight objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) = cIterSucRhs :=
    iterSuc_elabRight
  rw [iterSuc_elabLeft, eR, cIterSucRhs_subst] at a
  exact a

/-- **The iterator's contractum at a successor is typed** at `Σ (y : A). P y` in the
context of its equation: the typing of its template. -/
theorem citerSucRhs_typed :
    CTyped objectChurch cIterSucTele cIterSucRhs (.sigma (.var 4) (.app (.var 4) (.var 0))) := by
  obtain ⟨Θ, T, know, left, typed⟩ := iterSuc_template
  have kn : ∀ i, patternKnowledge objectDecls none
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName)) i =
        some (cIterSucTele.lookup i) := by
    decide
  have hΘ : ∀ i, Θ.lookup i = cIterSucTele.lookup i := fun i =>
    Option.some.inj ((know i).symm.trans (kn i))
  have hT : T = .sigma (.var 4) (.app (.var 4) (.var 0)) :=
    Option.some.inj (left.symm.trans (by decide))
  have he : elabRight objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) = cIterSucRhs := by
    decide
  have h := CTyped.substitute (Δ := cIterSucTele) (σ := CTm.ids) typed fun i => by
    rw [hΘ i, CTm.subst_ids]
    exact .var i
  rw [CTm.subst_ids, CTm.subst_ids, he, hT] at h
  exact h

/-! ## The iterator: its zero case and its successor step are adequate -/

section IterBodies

variable {K : RigidTypes objectChurch} {H : HeadReduction objectChurch K}

/-- **`Σ (y : A). P y` is valid** over a carrier `A : U₀` and a family `P : A → U₀` of the
context: the formation of dependent pair types, of the variable carrier and of the
family's value at the bound variable. -/
theorem valid_sigmaFam {n : Nat} {Γ : CCtx Tower.Head n} (a p : Fin n) (hA : Γ.lookup a = cU0)
    (hP : Γ.lookup p = .pi (.var a) cU0) :
    (CStatement.typing Γ (.sigma (.var a) (.app (.var p.succ) (.var 0)))
      (.head (.sort (.max Tower.zero Tower.zero)))).Valid objectChurchReading H ∧
    CTyped objectChurch Γ (.sigma (.var a) (.app (.var p.succ) (.var 0)))
      (.head (.sort (.max Tower.zero Tower.zero))) := by
  have vA : (CStatement.typing Γ (.var a) cU0).Valid objectChurchReading H := by
    rw [← hA]
    exact CStatement.Valid.var a
  have tA : CTyped objectChurch Γ (.var a) cU0 := by
    rw [← hA]
    exact .var a
  have hP' : (CCtx.snoc Γ (.var a)).lookup p.succ = .pi (.var a.succ) cU0 := by
    rw [CCtx.lookup_snoc_succ, hP]
    rfl
  have hy : (CCtx.snoc Γ (.var a)).lookup 0 = .var a.succ := by
    rw [CCtx.lookup_snoc_zero]
    rfl
  have vP : (CStatement.typing (.snoc Γ (.var a)) (.var p.succ) (.pi (.var a.succ) cU0)).Valid
      objectChurchReading H := by
    rw [← hP']
    exact CStatement.Valid.var p.succ
  have tP : CTyped objectChurch (.snoc Γ (.var a)) (.var p.succ) (.pi (.var a.succ) cU0) := by
    rw [← hP']
    exact .var p.succ
  have vy : (CStatement.typing (.snoc Γ (.var a)) (.var 0) (.var a.succ)).Valid
      objectChurchReading H := by
    rw [← hy]
    exact CStatement.Valid.var 0
  have ty : CTyped objectChurch (.snoc Γ (.var a)) (.var 0) (.var a.succ) := by
    rw [← hy]
    exact .var 0
  have vPy := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts vP vy tP ty
  have tPy := CDerivable.appElim tP ty
  exact ⟨CStatement.Valid.sigmaForm ConvRules.objectLevels objectChurch_soundnessFacts vA (.sort _)
    vPy (.sort _) (.sorts _ _) tA tPy, .sigmaForm tA (.sort _) tPy (.sort _) (.sorts _ _)⟩

/-- **The iterator's zero case is adequate**: the pair `(x, e)` at `Σ (y : A). P y`, by the
compatibility of pairs with the relation. -/
theorem adequate_iterZeroBody :
    Adequate objectChurchReading H iterTele (.pair (.var 1) (.var 0)) iterCodAt := by
  obtain ⟨vS, tS⟩ := valid_sigmaFam (H := H) (Γ := iterTele) 4 3 rfl rfl
  have vx : (CStatement.typing iterTele (.var 1) (.var 4)).Valid objectChurchReading H :=
    CStatement.Valid.var 1
  have ve : (CStatement.typing iterTele (.var 0) (.app (.var 3) (.var 1))).Valid
      objectChurchReading H :=
    CStatement.Valid.var 0
  exact Adequate.pair ConvRules.objectLevels objectChurch_soundnessFacts (.sort _) vS.1 vx.1 ve.1 tS
    (.var 1) (.var 0)

/-- The context of the step body extended by the pack. -/
abbrev iterPackTele : CCtx Tower.Head 7 :=
  .snoc iterStepTele (.sigma (.var 4) (.app (.var 4) (.var 0)))

/-- **The iterator's successor step is adequate**: the step at the value and its evidence,
and the recursive value at the carrier, the family, the step and the components of the
pack; assembled from the compatibility of variables, applications, abstractions, the
projections and the formation of dependent pair and function types. -/
theorem adequate_iterStepBody :
    Adequate objectChurchReading H iterStepTele iterStepBody iterCodAt := by
  -- the step at the value and its evidence
  have vSt : (CStatement.typing iterStepTele (.var 2) (.pi (.var 4) (.pi (.app (.var 4) (.var 0))
      (.sigma (.var 6) (.app (.var 6) (.var 0)))))).Valid objectChurchReading H :=
    CStatement.Valid.var 2
  have tSt : CTyped objectChurch iterStepTele (.var 2) (.pi (.var 4) (.pi (.app (.var 4) (.var 0))
      (.sigma (.var 6) (.app (.var 6) (.var 0))))) := .var 2
  have vx : (CStatement.typing iterStepTele (.var 1) (.var 4)).Valid objectChurchReading H :=
    CStatement.Valid.var 1
  have ve : (CStatement.typing iterStepTele (.var 0) (.app (.var 3) (.var 1))).Valid
      objectChurchReading H :=
    CStatement.Valid.var 0
  have vStx := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts vSt vx
    tSt (.var 1)
  have tStx := CDerivable.appElim tSt (.var 1)
  have vStxe := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts vStx ve
    tStx (.var 0)
  have tStxe := CDerivable.appElim tStx (.var 0)
  -- the pack type and the dependent function type out of it
  obtain ⟨vS, tS⟩ := valid_sigmaFam (H := H) (Γ := iterStepTele) 4 3 rfl rfl
  obtain ⟨vS', tS'⟩ := valid_sigmaFam (H := H) (Γ := iterPackTele) 5 4 rfl rfl
  have vPi := CStatement.Valid.piForm ConvRules.objectLevels objectChurch_soundnessFacts vS (.sort _)
    vS' (.sort _) (.sorts _ _) tS tS'
  have tPi := CDerivable.piForm tS (.sort _) tS' (.sort _) (.sorts _ _)
  -- the recursive value at the carrier, the family, the step and the pack's components
  have vpk : (CStatement.typing iterPackTele (.var 0) (.sigma (.var 5) (.app (.var 5) (.var 0)))).Valid
      objectChurchReading H :=
    CStatement.Valid.var 0
  have tpk : CTyped objectChurch iterPackTele (.var 0) (.sigma (.var 5) (.app (.var 5) (.var 0))) :=
    .var 0
  have vA7 : (CStatement.typing iterPackTele (.var 5) cU0).Valid objectChurchReading H :=
    CStatement.Valid.var 5
  have vfst : (CStatement.typing iterPackTele (.fst (.var 0)) (.var 5)).Valid objectChurchReading H :=
    ⟨Adequate.fst ConvRules.objectLevels vpk.1 tpk,
      vA7.1.adequateType ConvRules.objectLevels objectChurch_soundnessFacts (.sort _)⟩
  have tfst : CTyped objectChurch iterPackTele (.fst (.var 0)) (.var 5) := .fstElim tpk
  have vP7 : (CStatement.typing iterPackTele (.var 4) (.pi (.var 5) cU0)).Valid
      objectChurchReading H :=
    CStatement.Valid.var 4
  have tP7 : CTyped objectChurch iterPackTele (.var 4) (.pi (.var 5) cU0) := .var 4
  have vPfst := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts vP7 vfst
    tP7 tfst
  have vsnd : (CStatement.typing iterPackTele (.snd (.var 0))
      (CTm.inst0 (.fst (.var 0)) (.app (.var 5) (.var 0)))).Valid objectChurchReading H :=
    ⟨Adequate.snd ConvRules.objectLevels objectChurch_soundnessFacts vpk.1 tpk,
      vPfst.1.adequateType ConvRules.objectLevels objectChurch_soundnessFacts (.sort _)⟩
  have tsnd : CTyped objectChurch iterPackTele (.snd (.var 0))
      (CTm.inst0 (.fst (.var 0)) (.app (.var 5) (.var 0))) := .sndElim tpk
  have vRec := CStatement.Valid.var (Rd := objectChurchReading) (H := H) (Γ := iterPackTele) 6
  have tRec : CTyped objectChurch iterPackTele (.var 6) (iterPackTele.lookup 6) := .var 6
  have v₁ := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts vRec vA7
    tRec (.var 5)
  have t₁ := CDerivable.appElim tRec (.var 5)
  have v₂ := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts v₁ vP7 t₁ tP7
  have t₂ := CDerivable.appElim t₁ tP7
  have vSt7 := CStatement.Valid.var (Rd := objectChurchReading) (H := H) (Γ := iterPackTele) 3
  have tSt7 : CTyped objectChurch iterPackTele (.var 3) (iterPackTele.lookup 3) := .var 3
  have v₃ := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts v₂ vSt7 t₂ tSt7
  have t₃ := CDerivable.appElim t₂ tSt7
  have v₄ := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts v₃ vfst t₃ tfst
  have t₄ := CDerivable.appElim t₃ tfst
  have v₅ := CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts v₄ vsnd t₄ tsnd
  have t₅ := CDerivable.appElim t₄ tsnd
  -- the abstraction over the pack, applied to the step's value
  have vLam := CStatement.Valid.lamIntro ConvRules.objectLevels objectChurch_soundnessFacts vS (.sort _)
    vPi (.sort _) v₅ tS tPi t₅
  have tLam := CDerivable.lamIntro tS (.sort _) tPi (.sort _) t₅
  exact (CStatement.Valid.appElim ConvRules.objectLevels objectChurch_soundnessFacts vLam vStxe tLam
    tStxe).1

end IterBodies

/-! ## A definition with no hypothesis: `keepCert` -/

/-- The telescope of `keepCert`, annotated: a carrier, a family, a value and its evidence. -/
abbrev cKeepTele : CCtx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0)) (.var 1)) (.app (.var 1) (.var 0))

/-- The codomain of `keepCert`: `Σ (y : A). P y`. -/
abbrev cKeepCod : CTm Tower.Head 4 := .sigma (.var 3) (.app (.var 3) (.var 0))

theorem keep_declared :
    objectChurch.constantType keepName = some (pisCtx cKeepTele cKeepCod) :=
  objectChurch_declared (T := Package.keepType) (by decide) (by decide)

theorem objectChurchReading_keep :
    objectChurchReading.const keepName =
      defConst objectChurchReading cKeepTele cKeepCod (.pair (.var 1) (.var 0)) := by
  have h := objectChurchReading_def (f := keepName) (tag := .keep) (by decide)
    (Θ := keepTele) (rhs := keepRhs) (T := cKeepCod) (by decide) rfl
  have e : defRhs keepName keepTele keepRhs = (.pair (.var 1) (.var 0) : CTm Tower.Head 4) := by
    decide
  rw [h, e]
  rfl

/-- **The right side of `keepCert` is adequate** at its codomain: the pair of the value and
its evidence. -/
theorem adequate_keepRhs {K : RigidTypes objectChurch} {H : HeadReduction objectChurch K} :
    Adequate objectChurchReading H cKeepTele (.pair (.var 1) (.var 0)) cKeepCod := by
  obtain ⟨vS, tS⟩ := valid_sigmaFam (H := H) (Γ := cKeepTele) 3 2 rfl rfl
  have vx : (CStatement.typing cKeepTele (.var 1) (.var 3)).Valid objectChurchReading H :=
    CStatement.Valid.var 1
  have ve : (CStatement.typing cKeepTele (.var 0) (.app (.var 2) (.var 1))).Valid
      objectChurchReading H :=
    CStatement.Valid.var 0
  exact Adequate.pair ConvRules.objectLevels objectChurch_soundnessFacts (.sort _) vS.1 vx.1 ve.1 tS
    (.var 1) (.var 0)

/-- The spine of `keepCert` at its variables is typed at its codomain. -/
theorem ckeepSpine_typed :
    CTyped objectChurch cKeepTele (CTm.appSpine (.const keepName) [.var 3, .var 2, .var 1, .var 0])
      cKeepCod := by
  have t₀ : CTyped objectChurch cKeepTele (.const keepName) (liftTm Package.keepType).liftClosed :=
    const_typed (T := Package.keepType) (by decide) (by decide)
      (cpiT cU0_typed (cpiT (cpiT (craise (.var 0)) cU0_typed) (cpiT (craise (.var 1))
        (cpiT (craise (.appElim (B := cU0) (.var 1) (.var 0)))
          (craise (csigmaT (.var 3) (.appElim (B := cU0) (.var 3) (.var 0)))))))) (.sort _)
  have t₁ := CDerivable.appElim t₀ (CDerivable.var 3)
  have t₂ := CDerivable.appElim t₁ (CDerivable.var 2)
  have t₃ := CDerivable.appElim t₂ (CDerivable.var 1)
  exact CDerivable.appElim t₃ (CDerivable.var 0)

/-- The applications of `keepCert` reduce to its right side, by its root step. -/
theorem keep_teleReduces {K : RigidTypes objectChurch} (H : HeadReduction objectChurch K)
    {m : Nat} {Δ : CCtx Tower.Head m} :
    TeleReduces H Δ (CCtx.toTele cKeepTele) cKeepCod (.pair (.var 1) (.var 0)) (.const keepName)
      fun i => .var (Fin.elim0 i) := by
  intro A tA P tP x tx e te
  have mor : CSubstMor objectChurch cKeepTele Δ (CTm.consSub e (CTm.consSub x (CTm.consSub P
      (CTm.consSub A fun i => .var (Fin.elim0 i))))) := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact te
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tx
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tP
    refine Fin.cases ?_ (fun i => ?_) i
    · exact tA
    exact i.elim0
  have eL : elabLeft objectDecls (applyClosed keepTele Presentation.ids (.const keepName)) =
      (CTm.appSpine (.const keepName) [.var 3, .var 2, .var 1, .var 0] : CTm Tower.Head 4) := by
    decide
  have eR : elabRight objectDecls (applyClosed keepTele Presentation.ids (.const keepName))
      keepRhs = (.pair (.var 1) (.var 0) : CTm Tower.Head 4) := by
    decide
  have step : objectChurch.computation.step
      ((CTm.appSpine (.const keepName) [.var 3, .var 2, .var 1, .var 0] : CTm Tower.Head 4).subst
        (CTm.consSub e (CTm.consSub x (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i))))))
      ((.pair (.var 1) (.var 0) : CTm Tower.Head 4).subst
        (CTm.consSub e (CTm.consSub x (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))) := by
    have s := objectChurch_step_of_spec
      (List.getElem_mem (l := computationSpecs) (n := 6) (by decide))
      (L := applyClosed keepTele Presentation.ids (.const keepName)) (R := keepRhs) rfl
      (CTm.consSub e (CTm.consSub x (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))
    rw [eL, eR] at s
    exact s
  have admits : objectChurch.Admits Δ
      ((CTm.appSpine (.const keepName) [.var 3, .var 2, .var 1, .var 0] : CTm Tower.Head 4).subst
        (CTm.consSub e (CTm.consSub x (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i))))))
      ((.pair (.var 1) (.var 0) : CTm Tower.Head 4).subst
        (CTm.consSub e (CTm.consSub x (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i)))))) := by
    have a := objectChurch_admits_of_mor rfl
      (List.getElem_mem (l := computationSpecs) (n := 6) (by decide))
      (L := applyClosed keepTele Presentation.ids (.const keepName)) (R := keepRhs) rfl
      (CTm.consSub e (CTm.consSub x (CTm.consSub P (CTm.consSub A fun i => .var (Fin.elim0 i))))) (by decide) (by decide) mor
    rw [eL, eR] at a
    exact a
  have tRhs : CTyped objectChurch cKeepTele (.pair (.var 1) (.var 0)) cKeepCod :=
    .pairIntro (csigmaT (.var 3) (.appElim (B := cU0) (.var 3) (.var 0))) (.sort _) (.var 1) (.var 0)
  exact ⟨.single (H.root step), .rootAdmitted step admits (ckeepSpine_typed.substitute mor)
    (CTyped.substitute tRhs mor)⟩

/-- **`keepCert` is adequate**, with no hypothesis: its right side's adequacy is assembled
from the compatibility lemmas, and its applications reduce to its right side. -/
theorem constAdequateAt_keep {K : RigidTypes objectChurch} {H : HeadReduction objectChurch K} :
    ConstAdequateAt objectChurchReading H keepName :=
  ConstAdequateAt.ofDefinition ConvRules.objectLevels objectChurch_soundnessFacts keep_declared
    objectChurchReading_keep adequate_keepRhs fun _ => keep_teleReduces H


/-! ## The iterator is adequate -/

section Iterator

/-- **The numeral zero is adequate** at the numbers. -/
theorem adequate_czero : Adequate objectChurchReading objectHeadReduction .nil czero cnum := by
  intro ρ _ m Δ σ σ' _ _ s hs _
  have hs' : ent Elem.zero s = true := by
    have h : (objectChurchReading.const zeroN).Mem s := hs
    rwa [objectChurchReading_zero] at h
  refine RT.closed' hs' fun q hq => ?_
  rw [List.mem_singleton.1 hq]
  exact RT.tm_zero_iff.2 ⟨CRedTy.refl ⟨_, .sort _, cnum_typed⟩, CRedTm.refl czero_typed,
    CRedTm.refl czero_typed⟩

/-- The type of the iterator at a count, opened at any argument, is itself. -/
theorem inst0_iterTail {m : Nat} (N : CTm Tower.Head m) :
    CTm.inst0 N (iterTail.liftClosed : CTm Tower.Head (m + 1)) = iterTail.liftClosed :=
  CTm.subst_liftClosed _ _

/-- The dependent function type of the iterator's parameters over the recursive value is the
iterator's type at a count, weakened. -/
theorem pis_iterParams_one :
    (iterParams 1).pis (iterCodAt : CTm Tower.Head 6) = iterTail.rename wk := by
  decide

/-- The predecessor of a compact numeral is its predecessor components. -/
theorem predI_principal (X : List Tok) : Ideal.predI (principal X) = principal (args .succ 0 X) := by
  apply Ideal.le_antisymm
  · refine Ideal.closure_le fun s ⟨C, hs⟩ => ?_
    have h : ent X (.arg .succ 0 C s) = true := hs
    rw [ent_arg, Bool.and_eq_true] at h
    exact h.2
  · intro s hs
    refine Ideal.subset_closure ⟨[], ?_⟩
    show ent X (.arg .succ 0 [] s) = true
    rw [ent_arg]
    simpa using hs

/-- **The iterator at a count, by numeral recursion on the count.** For numbers related as
far as a numeral observes, the iterator at them is related to itself at its type at a
count, as far as every typed token of the `k`-th approximant of its numeral recursion
there observes. At zero, the head expansion along the zero equation and the adequacy of
the pair; at a successor, the head expansion along the successor equation and the adequacy
of the step body, whose recursive value is the iterator at the predecessor, related by the
recursion at `k`. -/
theorem iter_claim {m : Nat} {Δ : CCtx Tower.Head m} (formed : CCtxFormed objectChurch Δ)
    (hTail : AdequateType objectChurchReading objectHeadReduction .nil iterTail) :
    ∀ (k : Nat) (X : List Tok) (M M' : CTm Tower.Head m), CEqual objectChurch Δ M M' cnum →
      (∀ x, (principal X).Mem x → RT objectHeadReduction Δ true x cnum M M') →
      ∀ y, (natRecApprox (iterZero objectChurchReading)
          (fun _ r => Ideal.app (iterSucc objectChurchReading) r) k (principal X)).Mem y →
        TypedAt (cinterp objectChurchReading iterTail Env.nil) y →
        RT objectHeadReduction Δ true y iterTail.liftClosed (.app (.const iterName) M)
          (.app (.const iterName) M')
  | 0, _, _, _, _, _, _, hy, _ => RT.of_vacuous hy
  | k + 1, X, M, M', hMM, hν, y, hy, hyT => by
      have tTail : CIsType objectChurch .nil iterTail := ⟨_, .sort _, citerTail_formed⟩
      rw [natRecApprox, predI_principal] at hy
      by_cases hz : ent X (.tag .zero) = true <;> by_cases hs : ent X (.tag .succ) = true
      · -- a numeral does not reduce both to zero and to a successor
        exfalso
        obtain ⟨-, h0, -⟩ := RT.tm_zero_iff.1 (hν _ hz)
        obtain ⟨m₀, m₀', -, hs0, -, -⟩ := RT.tm_succTag_iff.1 (hν _ hs)
        have e := CRedTm.nf_unique h0 hs0 objectHeadReduction.normal_zero
          (objectHeadReduction.normal_suc _)
        cases e
      · -- zero
        rw [Ideal.whenTag_of_not_mem (ν := principal X) (k := .succ) hs, Ideal.join_bot, Ideal.whenTag_of_mem (ν := principal X) (k := .zero) hz] at hy
        obtain ⟨-, hM0, hM'0⟩ := RT.tm_zero_iff.1 (hν _ hz)
        have typedZero : ∀ {M₀ : CTm Tower.Head m}, CRedTm objectHeadReduction Δ M₀ czero cnum →
            TeleReduces objectHeadReduction Δ (iterParams 0) iterCodAt (.pair (.var 1) (.var 0))
              (.app (.const iterName) M₀) fun i => .var (Fin.elim0 i) := by
          intro M₀ hM₀
          refine iter_teleReduces formed hM₀ (fun A P st x e => iterZero_step A P st x e)
            (fun A P st x e mor => iterZero_admits fun i => by
              have mor₀ := mor czero_typed
              refine Fin.cases ?_ (fun i => ?_) i
              · exact mor₀ 0
              refine Fin.cases ?_ (fun i => ?_) i
              · exact mor₀ 1
              refine Fin.cases ?_ (fun i => ?_) i
              · exact mor₀ 2
              refine Fin.cases ?_ (fun i => ?_) i
              · exact mor₀ 3
              refine Fin.cases ?_ (fun i => ?_) i
              · exact mor₀ 4
              exact i.elim0) ?_
          intro A P st x e mor
          have mor₀ := mor czero_typed
          have e' : CTm.inst0 x (.app (P.rename wk) (.var 0)) = .app P x := by
            change CTm.app (CTm.inst0 x (P.rename wk)) x = _
            rw [CTm.inst0_rename_wk]
          have te : CTyped objectChurch Δ e (CTm.inst0 x (.app (P.rename wk) (.var 0))) := by
            rw [e']
            exact mor₀ 0
          exact .pairIntro (csigmaT (mor₀ 4) (.appElim (CTyped.weaken (mor₀ 3)) (.var 0)))
            (.sort _) (mor₀ 1) te
        have tele := RT.telescope ConvRules.objectLevels objectChurch_soundnessFacts (iterParams 0)
          (Γ := .nil) (T := iterCodAt) (E := .pair (.var 1) (.var 0)) tTail hTail
          adequate_iterZeroBody Env.nil trivial formed SubstRel.nil (typedZero hM0) (typedZero hM'0)
          y hy hyT
        rwa [show (iterParams 0).pis (iterCodAt : CTm Tower.Head 5) = iterTail from rfl,
          CTm.subst_closed] at tele
      · -- successor
        rw [Ideal.whenTag_of_mem (ν := principal X) (k := .succ) hs, Ideal.whenTag_of_not_mem (ν := principal X) (k := .zero) hz, Ideal.bot_join] at hy
        obtain ⟨m₀, m₀', hT, hMs, hM's, hm⟩ := RT.tm_succTag_iff.1 (hν _ hs)
        -- the predecessors, related as far as the predecessor observes
        have hpred : ∀ x, (principal (args .succ 0 X)).Mem x →
            RT objectHeadReduction Δ true x cnum m₀ m₀' := by
          intro x hx
          rw [← predI_principal] at hx
          obtain ⟨v, hv, e⟩ := hx
          refine RT.closed' e fun s hs' => ?_
          obtain ⟨C, hC⟩ := hv s hs'
          rcases RT.tm_argSucc_iff.1 (hν _ hC) with hvac | ⟨m₁, m₁', hsucc, -, hrel⟩
          · exact RT.of_vacuous (vacuous_arg hvac)
          obtain ⟨rfl, rfl⟩ := SuccRed.align ⟨hT, hMs, hM's, hm⟩ hsucc
          exact hrel rfl
        have ih := iter_claim formed hTail k (args .succ 0 X) m₀ m₀' hm hpred
        -- the value of the successor step at the recursive value
        have hy' : (cinterp objectChurchReading ((iterParams 1).lams iterStepBody)
            (Env.cons (projT (cinterp objectChurchReading iterTail Env.nil)
              (natRecApprox (iterZero objectChurchReading)
                (fun _ r => Ideal.app (iterSucc objectChurchReading) r) k (principal (args .succ 0 X))))
              Env.nil)).Mem y := by
          have e : iterSucc objectChurchReading = Ideal.clam
              (cinterp objectChurchReading iterTail Env.nil) fun z =>
                cinterp objectChurchReading ((iterParams 1).lams iterStepBody) (Env.cons z Env.nil) :=
            rfl
          have hy₀ : (Ideal.app (iterSucc objectChurchReading)
              (natRecApprox (iterZero objectChurchReading)
                (fun _ r => Ideal.app (iterSucc objectChurchReading) r) k (principal (args .succ 0 X)))).Mem y :=
            hy
          rw [e, Ideal.app_clam (cinterp_cont_cons _ _ _)] at hy₀
          exact hy₀
        -- the recursive values, related over the recursive value's type
        have tRec : ∀ {q : CTm Tower.Head m}, CTyped objectChurch Δ q cnum →
            CTyped objectChurch Δ (.app (.const iterName) q) (iterTail.subst fun i => .var (Fin.elim0 i)) := by
          intro q tq
          have h := CDerivable.appElim (citer_typed' (Γ := Δ)) tq
          rwa [inst0_iterTail, ← CTm.subst_closed iterTail (fun i => .var (Fin.elim0 i))] at h
        obtain ⟨tm₀, tm₀'⟩ := CEqual.typed ConvRules.objectLevels hm formed
        have eRec : CEqual objectChurch Δ (.app (.const iterName) m₀) (.app (.const iterName) m₀')
            (iterTail.subst fun i => .var (Fin.elim0 i)) := by
          have h := CDerivable.appCong (.refl (citer_typed' (Γ := Δ))) hm
          rwa [inst0_iterTail, ← CTm.subst_closed iterTail (fun i => .var (Fin.elim0 i))] at h
        have hsub : SubstRel objectChurchReading objectHeadReduction (.snoc .nil iterTail)
            (Env.cons (projT (cinterp objectChurchReading iterTail Env.nil)
              (natRecApprox (iterZero objectChurchReading)
                (fun _ r => Ideal.app (iterSucc objectChurchReading) r) k (principal (args .succ 0 X))))
              Env.nil) Δ
            (CTm.consSub (.app (.const iterName) m₀) fun i => .var (Fin.elim0 i))
            (CTm.consSub (.app (.const iterName) m₀') fun i => .var (Fin.elim0 i)) := by
          refine SubstRel.cons ConvRules.objectLevels formed SubstRel.nil eRec
            ⟨_, .sort _, .refl (citerTail_formed.substitute fun i => i.elim0)⟩
            (fun r hr hrU => hTail Env.nil trivial formed SubstRel.nil r hr hrU) ?_
          intro s hs _
          obtain ⟨v, hv, e⟩ := hs
          refine RT.closed' e fun s' hs' => ?_
          rw [CTm.subst_closed]
          exact ih s' (hv s' hs').1 (hv s' hs').2
        have fits : Fits objectChurchReading (.snoc .nil iterTail)
            (Env.cons (projT (cinterp objectChurchReading iterTail Env.nil)
              (natRecApprox (iterZero objectChurchReading)
                (fun _ r => Ideal.app (iterSucc objectChurchReading) r) k (principal (args .succ 0 X))))
              Env.nil) :=
          ⟨trivial, objectChurch_soundnessFacts.typeGenerated_of_head (.sort _) citerTail_formed
            trivial, Ideal.projT_projT _ _⟩
        have typedSuc : ∀ {M₀ q : CTm Tower.Head m}, CTyped objectChurch Δ q cnum →
            CRedTm objectHeadReduction Δ M₀ (csuc q) cnum →
            TeleReduces objectHeadReduction Δ (iterParams 1) iterCodAt iterStepBody
              (.app (.const iterName) M₀)
              (CTm.consSub (.app (.const iterName) q) fun i => .var (Fin.elim0 i)) := by
          intro M₀ q tq hM₀
          refine iter_teleReduces formed hM₀ (fun A P st x e => iterSuc_step q A P st x e)
            (fun A P st x e mor => iterSuc_admits (mor tq)) ?_
          intro A P st x e mor
          have h := citerSucRhs_typed.substitute (mor tq)
          rw [cIterSucRhs_subst, iterCodAt_subst] at h
          exact h
        have hU : AdequateType objectChurchReading objectHeadReduction (.snoc .nil iterTail)
            ((iterParams 1).pis iterCodAt) := by
          rw [pis_iterParams_one]
          exact AdequateType.weaken hTail
        have tU : CIsType objectChurch (.snoc .nil iterTail) ((iterParams 1).pis iterCodAt) := by
          rw [pis_iterParams_one]
          exact ⟨_, .sort _, citerTail_formed.weaken⟩
        have hyT' : TypedAt (cinterp objectChurchReading ((iterParams 1).pis iterCodAt)
            (Env.cons (projT (cinterp objectChurchReading iterTail Env.nil)
              (natRecApprox (iterZero objectChurchReading)
                (fun _ r => Ideal.app (iterSucc objectChurchReading) r) k (principal (args .succ 0 X))))
              Env.nil)) y := by
          rw [pis_iterParams_one, cinterp_rename_wk]
          exact hyT
        have tele := RT.telescope ConvRules.objectLevels objectChurch_soundnessFacts (iterParams 1)
          (Γ := .snoc .nil iterTail) (T := iterCodAt) (E := iterStepBody) tU hU
          adequate_iterStepBody _ fits formed hsub (typedSuc tm₀ hMs) (typedSuc tm₀' hM's) y hy' hyT'
        rwa [pis_iterParams_one, CTm.subst_consSub_wk, CTm.subst_closed] at tele
      · -- no tag: the least element observes nothing
        rw [Ideal.whenTag_of_not_mem (ν := principal X) (k := .succ) hs, Ideal.whenTag_of_not_mem (ν := principal X) (k := .zero) hz, Ideal.join_bot] at hy
        exact RT.of_vacuous hy

/-- **The iterator is adequate**: its constant is related to itself at its declared type,
as far as every typed token of its denotation observes. A token is a function entry of the
numeral recursion; for numbers related as far as its input observes, each output lies in an
approximant of the recursion at the input, where the iterator at them is related to itself
(`iter_claim`). The type at a count is adequate: the declared type's family at zero. -/
theorem constAdequateAt_iter : ConstAdequateAt objectChurchReading objectHeadReduction iterName := by
  intro D u declared _ _ hD m Δ formed s hs _
  have hDecl : objectChurch.constantType iterName = some (liftTm Package.iterType) :=
    objectChurch_declared (by decide) (by decide)
  obtain rfl : liftTm Package.iterType = D := Option.some.inj (hDecl.symm.trans declared)
  -- the type at a count is adequate
  rw [liftTm_iterType] at hD
  have hTail := AdequateType.inst ConvRules.objectLevels objectChurch_soundnessFacts hD adequate_czero
    czero_typed
  rw [CTm.inst0_rename_wk] at hTail
  -- the generators of the constant's tokens
  rw [objectChurchReading_iter] at hs
  obtain ⟨v, hvI, hvT, e⟩ := Ideal.projT_eq_iSup.1 hs
  rw [liftClosed_iterType]
  refine RT.closed' e fun t ht => ?_
  obtain ⟨b, hb, hbu, hbt⟩ := hvT t ht
  rw [liftTm_iterType] at hb
  have hbF : Ideal.Below b (Ideal.former .pi (cinterp objectChurchReading cnum Env.nil) fun X =>
      cinterp objectChurchReading (iterTail.rename wk)
        (Env.cons (projT (cinterp objectChurchReading cnum Env.nil) (principal X)) Env.nil)) := hb
  obtain ⟨X, Y, rfl, -, hYt⟩ := Ideal.tyTok_below_pi hbF hbt
  have hmono : Ideal.Monotone fun N => natRec (iterZero objectChurchReading)
      (fun _ r => Ideal.app (iterSucc objectChurchReading) r) (principal N) := fun h =>
    (Ideal.cont_natRec (cont₂_constStep _)).mono (principal_mono h)
  have hY := (Ideal.mem_lam_fn hmono).1 (hvI _ ht)
  have hbelow : Ideal.Below (fnApp .pi b X) (cinterp objectChurchReading iterTail Env.nil) := by
    have h := Ideal.below_fam_fnApp (k := .pi) (y := principal X) hb fun x hx => ent_of_mem hx
    rwa [fam_cinterp_pi, cinterp_rename_wk] at h
  have hyT : ∀ y ∈ Y, TypedAt (cinterp objectChurchReading iterTail Env.nil) y := fun y hy =>
    ⟨fnApp .pi b X, hbelow, Ideal.ty_fnApp (.inl rfl) hbu X, hYt y hy⟩
  have claim : ∀ {N N' : CTm Tower.Head m}, CEqual objectChurch Δ N N' cnum →
      (∀ x ∈ X, RT objectHeadReduction Δ true x cnum N N') → ∀ y ∈ Y,
        RT objectHeadReduction Δ true y iterTail.liftClosed (.app (.const iterName) N)
          (.app (.const iterName) N') := by
    intro N N' hNN hNX y hy
    obtain ⟨k, hk⟩ := (Ideal.mem_natRec (cont₂_constStep _)).1 (hY y hy)
    exact iter_claim formed hTail k X N N' hNN (fun x hx => RT.closed' hx hNX) y hk (hyT y hy)
  refine RT.tm_lam_iff.2 (.inr fun D' E' hred => ?_)
  have e' := objectHeadReduction.red_normal (objectHeadReduction.normal_pi _ _) hred.1
  injection e' with _ eD eE
  subst eD eE
  refine ⟨fun N N' hNN hNX y hy => ?_, fun N tN hNX y hy => ?_⟩
  · rw [inst0_iterTail]
    exact ⟨claim hNN hNX y hy, claim hNN hNX y hy⟩
  · rw [inst0_iterTail]
    exact claim (.refl tN) hNX y hy

end Iterator

/-! ## The quantifier at every simple type -/

section Quantifiers

variable {H : HeadReduction objectChurch objectRigid}

/-- **Every simple type is an adequate type**, over every context: the codes, the numbers
and the sets are related to themselves at their tags, and a function type of adequate
components is adequate. -/
theorem adequateType_typeAt : ∀ (type : HOL.Ty SetProfile.SetBase) {n : Nat} (Γ : CCtx Tower.Head n),
    AdequateType objectChurchReading H Γ (liftTm (typeAt SetProfile.types n type))
  | .prop, _, _ => by
      intro ρ _ m Δ σ σ' _ _ r hr _
      have hr' : Ideal.codesIdeal.Mem r := by
        have h : (objectChurchReading.const propN).Mem r := hr
        rwa [objectChurchReading_prop] at h
      exact RT.prop_self (P := objectChurch) (K := objectRigid) (.sort Tower.zero)
        (const_U0_typed (by decide)) hr'
  | .base .num, _, _ => by
      intro ρ _ m Δ σ σ' _ _ r hr _
      have hr' : ent Elem.nat r = true := by
        have h : (objectChurchReading.const numN).Mem r := hr
        rwa [objectChurchReading_num] at h
      refine RT.closed' hr' fun q hq => ?_
      rw [List.mem_singleton.1 hq]
      have red : CRedTy H Δ (cnum : CTm Tower.Head m) cnum := CRedTy.refl ⟨_, .sort _, cnum_typed⟩
      exact RT.ty_nat_iff.2 ⟨red, red⟩
  | .base .set, _, _ => by
      intro ρ _ m Δ σ σ' _ _ r hr _
      have hr' : ent Elem.ground r = true := by
        have h : (objectChurchReading.const setN).Mem r := hr
        rwa [objectChurchReading_set] at h
      refine RT.closed' hr' fun q hq => ?_
      rw [List.mem_singleton.1 hq]
      have red : CRedTy H Δ (cset : CTm Tower.Head m) cset := CRedTy.refl ⟨_, .sort _, cset_typed⟩
      exact RT.ty_ground_iff.2 ⟨cset, .inl rfl, red, red⟩
  | .arr a b, n, Γ =>
      AdequateType.pi ConvRules.objectLevels objectChurch_soundnessFacts
        ⟨_, .sort _, typeAt_formed (.arr a b) Γ⟩ (adequateType_typeAt a Γ)
        (adequateType_typeAt b (.snoc Γ (liftTm (typeAt SetProfile.types n a))))

/-- **Decoding a quantified code is an annotated root step** at every simple type:
`holds (all@A f) ⟶ Π (x : A). holds (f x)`. -/
theorem objectChurch_decodeAll (type : HOL.Ty SetProfile.SetBase) {n : Nat}
    (f : CTm Tower.Head n) :
    objectChurch.computation.step (.app (.const holdsN) (.app (.const (SetProfile.allName type)) f))
      (.pi (liftTm (typeAt SetProfile.types n type))
        (.app (.const holdsN) (.app (f.rename wk) (.var 0)))) := by
  have carrier : programCodes.decoders.allCarrier (SetProfile.allName type) = some (typeTerm type) := by
    change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = _
    rw [SetProfile.allInstance?_allName]
    rfl
  have s := objectChurch_step_of_decoder
    (Or.inr (Or.inl ⟨SetProfile.allName type, typeTerm type, carrier, rfl⟩)) (fun _ => f)
  have lf : lamFree ((Tm.pi (Presentation.liftClosed (typeTerm type))
      (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))) : Tower.Tm 1) =
      true := by
    simp only [lamFree, Presentation.liftClosed, typeTerm,
      FormationSensitiveHOLInterface.typeAt_rename, lamFree_typeAt, Presentation.rename,
      Bool.and_self]
  have eh : programCodes.decoders.holds = holdsN := rfl
  rw [eh, elabLeft_firstOrder objectDecls (rfl : firstOrder
      (.app (.const holdsN) (.app (.const (SetProfile.allName type)) (.var 0)) : Tower.Tm 1) =
        true), elabRight, elab_lamFree _ lf] at s
  have hA : (liftTm (Presentation.liftClosed (typeTerm type)) : CTm Tower.Head 1) =
      liftTm (typeAt SetProfile.types 1 type) := by
    unfold Presentation.liftClosed typeTerm
    rw [FormationSensitiveHOLInterface.typeAt_rename]
  have e : (liftTm (Tm.pi (Presentation.liftClosed (typeTerm type))
      (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0))) : Tower.Tm 1)).subst
        (fun _ => f) =
      .pi (liftTm (typeAt SetProfile.types n type))
        (.app (.const holdsN) (.app (f.rename wk) (.var 0))) := by
    show CTm.pi ((liftTm (Presentation.liftClosed (typeTerm type))).subst fun _ => f) _ = _
    rw [hA, subst_liftTm_typeAt]
    rfl
  rw [e] at s
  exact s

/-- **Decoding a quantified code is admitted where the family is typed** at `A → prop`. -/
theorem objectChurch_decodeAll_admits (type : HOL.Ty SetProfile.SetBase)
    {R' : Rules Tower.Head} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx Tower.Head n}
    {f : CTm Tower.Head n}
    (typed : CTyped Q Γ f (liftTm (typeAt SetProfile.types n (.arr type .prop))))
    (same : Q.computation = objectChurch.computation := by rfl) :
    Q.Admits Γ (.app (.const holdsN) (.app (.const (SetProfile.allName type)) f))
      (.pi (liftTm (typeAt SetProfile.types n type))
        (.app (.const holdsN) (.app (f.rename wk) (.var 0)))) := by
  have carrier : programCodes.decoders.allCarrier (SetProfile.allName type) = some (typeTerm type) := by
    change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = _
    rw [SetProfile.allInstance?_allName]
    rfl
  have a := objectChurch_admits_of_decoder same
    (Or.inr (Or.inl ⟨SetProfile.allName type, typeTerm type, carrier, rfl⟩)) (Γ := Γ)
    (fun _ => f)
    (CSubstMor.patternTypings (all_knowledge type) (fun i => by
      obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
      rw [liftCtx_lookup, Ctx.lookup_snoc_zero, FormationSensitiveHOLInterface.typeAt_rename,
        subst_liftTm_typeAt]
      exact typed))
    (fun e member => by
      have noEquations : patternEquations objectDecls none (allLeft type) = [] := rfl
      change e ∈ patternEquations objectDecls none (allLeft type) at member
      rw [noEquations] at member
      cases member)
  have lf : lamFree ((Tm.pi (Presentation.liftClosed (typeTerm type))
      (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0)))) : Tower.Tm 1) =
      true := by
    simp only [lamFree, Presentation.liftClosed, typeTerm,
      FormationSensitiveHOLInterface.typeAt_rename, lamFree_typeAt, Presentation.rename,
      Bool.and_self]
  have eh : programCodes.decoders.holds = holdsN := rfl
  rw [eh, elabLeft_firstOrder objectDecls (rfl : firstOrder
      (.app (.const holdsN) (.app (.const (SetProfile.allName type)) (.var 0)) : Tower.Tm 1) =
        true), elabRight, elab_lamFree _ lf] at a
  have hA : (liftTm (Presentation.liftClosed (typeTerm type)) : CTm Tower.Head 1) =
      liftTm (typeAt SetProfile.types 1 type) := by
    unfold Presentation.liftClosed typeTerm
    rw [FormationSensitiveHOLInterface.typeAt_rename]
  have e : (liftTm (Tm.pi (Presentation.liftClosed (typeTerm type))
      (.app (.const holdsN) (.app (Presentation.rename wk (.var 0)) (.var 0))) : Tower.Tm 1)).subst
        (fun _ => f) =
      .pi (liftTm (typeAt SetProfile.types n type))
        (.app (.const holdsN) (.app (f.rename wk) (.var 0))) := by
    show CTm.pi ((liftTm (Presentation.liftClosed (typeTerm type))).subst fun _ => f) _ = _
    rw [hA, subst_liftTm_typeAt]
    rfl
  rw [e] at a
  exact a

/-- **The quantifier at a simple type is adequate**: at every token of its constant typed
at `(A → prop) → prop`, `all@A` is related to itself there. The carrier `A` is an adequate
type, so its type tokens relate it to itself, and the decoding of a quantified code is the
dependent function type over `A` of the family's decodings. -/
theorem constAdequateAt_all (type : HOL.Ty SetProfile.SetBase) :
    ConstAdequateAt objectChurchReading H (SetProfile.allName type) := by
  intro D u declared _ _ _ m Δ formed s hs hsT
  have hDecl : objectChurch.constantType (SetProfile.allName type) =
      some (liftTm (SetProfile.allType type)) := by
    rw [objectChurch_constantType]
    exact objectDecls_allName type
  obtain rfl : liftTm (SetProfile.allType type) = D := Option.some.inj (hDecl.symm.trans declared)
  have hD : (liftTm (SetProfile.allType type) : CTm Tower.Head 0) =
      liftTm (typeAt SetProfile.types 0 (.arr (.arr type .prop) .prop)) := rfl
  rw [hD, liftClosed_liftTm_typeAt]
  rw [hD, cinterp_objectTypeAt] at hsT
  rw [objectChurchReading_all] at hs
  have tAll : CTyped objectChurch Δ (.const (SetProfile.allName type))
      (liftTm (typeAt SetProfile.types m (.arr (.arr type .prop) .prop))) := by
    rw [← liftClosed_liftTm_typeAt]
    exact .const (objectDecls_allName type) (typeAt_formed (.arr (.arr type .prop) .prop) .nil)
      (.sort _)
  have hC : ∀ d, (simpleI type).Mem d → TyTok Elem.univ d →
      RT H Δ false d (liftTm (typeAt SetProfile.types m type))
        (liftTm (typeAt SetProfile.types m type)) (liftTm (typeAt SetProfile.types m type)) := by
    intro d hd hdU
    have h := adequateType_typeAt (H := H) type .nil Env.nil trivial formed SubstRel.nil d
      (by rw [cinterp_objectTypeAt]; exact hd) hdU
    rwa [subst_liftTm_typeAt] at h
  exact RT.allCodeAt ConvRules.objectLevels formed (SetProfile.allName type) hC (.sort Tower.zero)
    (.sort Tower.zero) (const_U0_typed (by decide)) (typeAt_formed type Δ) tAll
    (objectChurch_decodeAll type) (fun typed => objectChurch_decodeAll_admits type typed)
    s hs hsT

/-- **The quantifier over the functions on the numbers**, `all@(num → num)`, is adequate. -/
theorem constAdequateAt_allNumNum :
    ConstAdequateAt objectChurchReading H (SetProfile.allName (.arr SetProfile.numTy SetProfile.numTy)) :=
  constAdequateAt_all _

end Quantifiers

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
