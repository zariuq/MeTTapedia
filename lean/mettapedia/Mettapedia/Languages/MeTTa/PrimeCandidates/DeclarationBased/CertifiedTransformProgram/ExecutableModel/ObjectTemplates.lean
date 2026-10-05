import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectFormation

/-!
# The elaborated right-hand sides of the object package are typed

Each root computation of the executable package is presented by rewrite
schemas, and the annotation of the object package (`objectChurch`) elaborates
each schema's right-hand side against the type its left side synthesizes. This
module proves every such elaborated right-hand side typed in the annotated
calculus (`TemplateTyped`), in a context whose variables have the types the left
side's positions require:

* the definitions by one equation: `eqAt`, `sucMove`, `keepCert`,
  `transportCert`, `composeCert`, `returnIter`, `sucStep`;
* the equations of addition, of the iterated power set and of the iterator, one
  per constructor of the numbers;
* the computation rules of `num-rec`, one per constructor.

The right-hand sides with abstractions are typed at the annotations the
elaboration chose: the motive of `sucMove`, checked against the eliminator's
motive type, has the domains `num` and `Id num (add zero n) y`; the shared use
of a step in `composeCert` and in the iterator's successor equation is annotated
with the step's result type `Σ y : A. P y`; the five abstractions of
`returnIter` carry the domains of its declared type. The typing of `sucMove`'s
right-hand side converts by β, by the equation of `eqAt` and by the successor
equation of addition, each an annotated root step of the object package.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open TelescopeAbstraction (applyClosed)
open Package (jName numRecName eqAtName sucMoveName keepName transportName composeName
  iterName returnIterName sucStepName U0 numT eqAtApp eqAtTelescope transportTelescope
  composeTelescope iterTelescope iterSucTelescope returnIterResult)
open SetProfile (sucNative)

namespace CodeModel

/-! ## Annotated root steps used in conversions -/

section Steps

variable {n : Nat}

/-- The left side of the equation of `eqAt`, elaborated. -/
theorem eqAt_elabLeft : elabLeft objectDecls (applyClosed eqAtTele ids (.const eqAtName)) =
    (ceqAt (.var 0) : CTm Tower.Head 1) := by
  decide

/-- The right side of the equation of `eqAt`, elaborated. -/
theorem eqAt_elabRight :
    elabRight objectDecls (applyClosed eqAtTele ids (.const eqAtName)) eqAtRhs =
      (.id cnum (cadd czero (.var 0)) (.var 0) : CTm Tower.Head 1) := by
  decide

/-- The equation of `eqAt`, as an annotated root step. -/
theorem ceqAt_step (t : CTm Tower.Head n) :
    objectChurch.computation.step (ceqAt t) (.id cnum (cadd czero t) t) := by
  have s := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 4) (by decide))
    (L := applyClosed eqAtTele ids (.const eqAtName)) (R := eqAtRhs) rfl (fun _ => t)
  rw [eqAt_elabLeft, eqAt_elabRight] at s
  exact s

/-- **The equation of `eqAt` is admitted where its argument is a number**, by every package
with the object package's root computation. -/
theorem ceqAt_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {Γ : CCtx Tower.Head n}
    {t : CTm Tower.Head n} (typed : CTyped Q Γ t cnum)
    (within : StepsWithin objectChurch Q := by exact objectChurch_within rfl) :
    Q.Admits Γ (ceqAt t) (.id cnum (cadd czero t) t) := by
  have a := objectChurch_admits_of_mor within
    (List.getElem_mem (l := computationSpecs) (n := 4) (by decide))
    (L := applyClosed eqAtTele ids (.const eqAtName)) (R := eqAtRhs) rfl (Γ := Γ)
    (fun _ => t) (Θ := .snoc .nil cnum) (by decide) (by decide) (fun i => by
      obtain rfl : i = 0 := Subsingleton.elim i 0
      exact typed)
  rw [eqAt_elabLeft, eqAt_elabRight] at a
  exact a

/-! The shapes of the two equations of addition. -/

theorem addZero_knowledge : ∀ i, patternKnowledge objectDecls none
    (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN)) i =
      some ((CCtx.snoc .nil cnum : CCtx Tower.Head 1).lookup i) := by
  decide

theorem addZero_elabLeft : elabLeft objectDecls
    (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN)) =
      (cadd (.var 0) czero : CTm Tower.Head 1) := by
  decide

theorem addZero_elabRight : elabRight objectDecls
    (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
    (Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN [])) =
      (.var 0 : CTm Tower.Head 1) := by
  decide

theorem addSuc_knowledge : ∀ i, patternKnowledge objectDecls none
    (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN)) i =
      some ((CCtx.snoc (.snoc .nil cnum) cnum : CCtx Tower.Head 2).lookup i) := by
  decide

theorem addSuc_elabLeft : elabLeft objectDecls
    (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN)) =
      (cadd (.var 1) (csuc (.var 0)) : CTm Tower.Head 2) := by
  decide

theorem addSuc_elabRight : elabRight objectDecls
    (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
    (Presentation.subst (hypSub addN addEntries 1 0 [.recursive]) (addBody sucN [.recursive])) =
      (csuc (cadd (.var 1) (.var 0)) : CTm Tower.Head 2) := by
  decide

/-- The zero equation of addition, as an annotated root step. -/
theorem caddZero_step (t : CTm Tower.Head n) :
    objectChurch.computation.step (cadd t czero) t := by
  have s := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 1) (by decide))
    (L := applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
    (R := Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN []))
    (show recursionSchema addN ctors addEntries 1 0 addBody _ _ from
      ⟨zeroN, [], List.mem_cons_self .., rfl⟩) ![t]
  rw [addZero_elabLeft, addZero_elabRight] at s
  exact s

/-- **The zero equation of addition is admitted where its first summand is a number.** -/
theorem caddZero_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {Γ : CCtx Tower.Head n}
    {t : CTm Tower.Head n} (typed : CTyped Q Γ t cnum)
    (within : StepsWithin objectChurch Q := by exact objectChurch_within rfl) :
    Q.Admits Γ (cadd t czero) t := by
  have a := objectChurch_admits_of_mor within
    (List.getElem_mem (l := computationSpecs) (n := 1) (by decide))
    (L := applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
    (R := Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN []))
    (show recursionSchema addN ctors addEntries 1 0 addBody _ _ from
      ⟨zeroN, [], List.mem_cons_self .., rfl⟩) (Γ := Γ) ![t] addZero_knowledge (by decide)
    (fun i => by
      obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) i 0
      exact typed)
  rw [addZero_elabLeft, addZero_elabRight] at a
  exact a

/-- The successor equation of addition, as an annotated root step. -/
theorem caddSuc_step (a b : CTm Tower.Head n) :
    objectChurch.computation.step (cadd a (csuc b)) (csuc (cadd a b)) := by
  have s := objectChurch_step_of_spec
    (List.getElem_mem (l := computationSpecs) (n := 1) (by decide))
    (L := applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
    (R := Presentation.subst (hypSub addN addEntries 1 0 [.recursive]) (addBody sucN [.recursive]))
    (show recursionSchema addN ctors addEntries 1 0 addBody _ _ from
      ⟨sucN, [.recursive], List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩) ![b, a]
  rw [addSuc_elabLeft, addSuc_elabRight] at s
  exact s

/-- **The successor equation of addition is admitted where its summands are numbers.** -/
theorem caddSuc_admits {R' : Rules Tower.Head} {Q : ChurchRules R'} {Γ : CCtx Tower.Head n}
    {a b : CTm Tower.Head n} (ta : CTyped Q Γ a cnum) (tb : CTyped Q Γ b cnum)
    (within : StepsWithin objectChurch Q := by exact objectChurch_within rfl) :
    Q.Admits Γ (cadd a (csuc b)) (csuc (cadd a b)) := by
  have s := objectChurch_admits_of_mor within
    (List.getElem_mem (l := computationSpecs) (n := 1) (by decide))
    (L := applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
    (R := Presentation.subst (hypSub addN addEntries 1 0 [.recursive]) (addBody sucN [.recursive]))
    (show recursionSchema addN ctors addEntries 1 0 addBody _ _ from
      ⟨sucN, [.recursive], List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩) (Γ := Γ)
    ![b, a] addSuc_knowledge (by decide) (fun i => by
      refine Fin.cases ?_ (fun j => ?_) i
      · exact tb
      · obtain rfl : j = 0 := Subsingleton.elim j 0
        exact ta)
  rw [addSuc_elabLeft, addSuc_elabRight] at s
  exact s

end Steps

/-! ## Two β-steps of a type family -/

/-- Two β-steps of an annotated family of types. -/
theorem cbetaTwo {n : Nat} {Γ : CCtx Tower.Head n} {A : CTm Tower.Head n}
    {B : CTm Tower.Head (n + 1)} {M : CTm Tower.Head (n + 2)} {a b : CTm Tower.Head n}
    {l : LevelExpr Nat}
    (formed : CTyped objectChurch Γ (.pi A (.pi B cU0)) (CU l))
    (formed₂ : CTyped objectChurch (.snoc Γ A) (.pi B cU0) (CU l))
    (formedB : CTyped objectChurch (.snoc Γ A) B (CU l))
    (body : CTyped objectChurch (.snoc (.snoc Γ A) B) M cU0)
    (ta : CTyped objectChurch Γ a A) (tb : CTyped objectChurch Γ b (CTm.inst0 a B)) :
    CEqual objectChurch Γ (.app (.app (.lam A (.lam B M)) a) b)
      (CTm.inst0 b (M.subst (CTm.liftSub (CTm.subst0 a)))) cU0 := by
  have lamM : CTyped objectChurch (.snoc Γ A) (.lam B M) (.pi B cU0) :=
    .lamIntro formedB (.sort l) formed₂ (.sort l) body
  have e₁ := CDerivable.betaPi formed (.sort l) lamM ta
  have e₂ : CEqual objectChurch Γ (.app (.app (.lam A (.lam B M)) a) b)
      (.app (CTm.inst0 a (.lam B M)) b) (CTm.inst0 b cU0) :=
    CDerivable.appCong (A := CTm.inst0 a B) (B := cU0) e₁ (.refl tb)
  have formedInst : CTyped objectChurch Γ (.pi (CTm.inst0 a B) cU0) (CU l) :=
    CTyped.instantiate formed₂ ta
  have bodyInst : CTyped objectChurch (.snoc Γ (CTm.inst0 a B))
      (M.subst (CTm.liftSub (CTm.subst0 a))) cU0 :=
    CTyped.substitute body (CSubstMor.lift (CSubstMor.single ta) B)
  have e₃ := CDerivable.betaPi formedInst (.sort l) bodyInst tb
  exact .trans e₂ e₃

/-! ## Definitions by one equation -/

theorem eqAt_template :
    TemplateTyped objectChurch objectDecls (applyClosed eqAtTele ids (.const eqAtName))
      eqAtRhs := by
  refine ⟨liftCtx eqAtTele, liftTm U0, by decide, by decide, ?_⟩
  have e : elabRight objectDecls (applyClosed eqAtTele ids (.const eqAtName)) eqAtRhs =
      (.id cnum (cadd czero (.var 0)) (.var 0) : CTm Tower.Head 1) := by decide
  rw [e]
  show CTyped objectChurch (.snoc .nil cnum) (.id cnum (cadd czero (.var 0)) (.var 0)) cU0
  exact cidT cnum_typed (cadd_typed czero_typed (.var 0)) (.var 0)

theorem keep_template :
    TemplateTyped objectChurch objectDecls (applyClosed keepTele ids (.const keepName))
      keepRhs := by
  refine ⟨liftCtx keepTele, liftTm (.sigma (.var 3) (.app (.var 3) (.var 0))), by decide,
    by decide, ?_⟩
  have e : elabRight objectDecls (applyClosed keepTele ids (.const keepName)) keepRhs =
      (.pair (.var 1) (.var 0) : CTm Tower.Head 4) := by decide
  rw [e]
  show CTyped objectChurch
    (.snoc (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0)) (.var 1)) (.app (.var 1) (.var 0)))
    (.pair (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0)))
  exact .pairIntro (csigmaT (.var 3) (.appElim (B := cU0) (.var 3) (.var 0))) (.sort Tower.zero)
    (.var 1) (.var 0)

/-- The telescope of `transportCert`, annotated. -/
abbrev cTransportTele : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0)) (.pi (.var 1) (.var 2)))
    (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 2) (.var 1))))))
    (.var 3)) (.app (.var 3) (.var 0))

theorem transport_template :
    TemplateTyped objectChurch objectDecls
      (applyClosed transportTelescope ids (.const transportName)) transportRhs := by
  refine ⟨liftCtx transportTelescope, liftTm (.sigma (.var 5) (.app (.var 5) (.var 0))),
    by decide, by decide, ?_⟩
  have e : elabRight objectDecls (applyClosed transportTelescope ids (.const transportName))
      transportRhs =
      (.pair (.app (.var 3) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)) :
        CTm Tower.Head 6) := by decide
  rw [e]
  show CTyped objectChurch cTransportTele
    (.pair (.app (.var 3) (.var 1)) (.app (.app (.var 2) (.var 1)) (.var 0)))
    (.sigma (.var 5) (.app (.var 5) (.var 0)))
  have value := CDerivable.appElim (B := .var 6)
    (CDerivable.var (P := objectChurch) (Γ := cTransportTele) 3) (.var 1)
  have moved := CDerivable.appElim
    (CDerivable.appElim (CDerivable.var (P := objectChurch) (Γ := cTransportTele) 2) (.var 1))
    (.var 0)
  exact .pairIntro (csigmaT (.var 5) (.appElim (B := cU0) (.var 5) (.var 0))) (.sort Tower.zero)
    value moved

/-- The telescope `n : num, e : eqAt n`, annotated. -/
abbrev cEqAtTele : CCtx Tower.Head 2 := .snoc (.snoc .nil cnum) (ceqAt (.var 0))

theorem sucStep_template :
    TemplateTyped objectChurch objectDecls (applyClosed eqAtTelescope ids (.const sucStepName))
      sucStepRhs := by
  refine ⟨liftCtx eqAtTelescope, liftTm (.sigma numT (eqAtApp (.var 0))), by decide, by decide,
    ?_⟩
  have e : elabRight objectDecls (applyClosed eqAtTelescope ids (.const sucStepName)) sucStepRhs =
      (.app (.app (.app (.app (.app (.app (.const transportName) cnum) (.const eqAtName))
        (.const sucN)) (.const sucMoveName)) (.var 1)) (.var 0) : CTm Tower.Head 2) := by decide
  rw [e]
  show CTyped objectChurch cEqAtTele
    (.app (.app (.app (.app (.app (.app (.const transportName) cnum) (.const eqAtName))
      (.const sucN)) (.const sucMoveName)) (.var 1)) (.var 0))
    (.sigma cnum (ceqAt (.var 0)))
  have t1 := CDerivable.appElim (ctransport_typed (Γ := cEqAtTele)) cnum_typed
  have t2 := CDerivable.appElim t1 ceqAtConst_typed
  have t3 := CDerivable.appElim t2 csucConst_typed
  have t4 := CDerivable.appElim t3 csucMove_typed
  have t5 := CDerivable.appElim t4 (CDerivable.var 1)
  exact CDerivable.appElim t5 (CDerivable.var 0)

/-- The motive of the successor move, annotated as elaborated:
`λ (y : num). λ (p : Id num (add zero n) y). Id num (suc (add zero n)) (suc y)`. -/
abbrev cSucMotive : CTm Tower.Head 2 :=
  .lam cnum (.lam (.id cnum (cadd czero (.var 2)) (.var 0))
    (.id cnum (csuc (cadd czero (.var 3))) (csuc (.var 1))))

/-- The declared type of the identity eliminator, annotated. -/
abbrev cJType {n : Nat} : CTm Tower.Head n :=
  .pi cU0 (.pi (.var 0)
    (.pi (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
      (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
        (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
          (.app (.app (.var 3) (.var 1)) (.var 0)))))))

/-- The family of the motive's second argument, `Id num (add 0 n) y`, is a type. -/
theorem cSucMotive_family : CTyped objectChurch (.snoc cEqAtTele cnum)
    (.id cnum (cadd czero (.var 2)) (.var 0)) cU0 :=
  cidT cnum_typed (cadd_typed czero_typed (.var 2)) (.var 0)

/-- The type of the motive at a number is a type. -/
theorem cSucMotive_familyType : CTyped objectChurch (.snoc cEqAtTele cnum)
    (.pi (.id cnum (cadd czero (.var 2)) (.var 0)) cU0) cU1 :=
  cpiT (craise cSucMotive_family) cU0_typed

/-- The eliminator's motive type at `num` and `add 0 n` is a type. -/
theorem cSucMotive_type : CTyped objectChurch cEqAtTele
    (.pi cnum (.pi (.id cnum (cadd czero (.var 2)) (.var 0)) cU0)) cU1 :=
  cpiT (craise cnum_typed) cSucMotive_familyType

/-- The body of the motive, `Id num (suc (add 0 n)) (suc y)`, is a type. -/
theorem cSucMotive_body : CTyped objectChurch
    (.snoc (.snoc cEqAtTele cnum) (.id cnum (cadd czero (.var 2)) (.var 0)))
    (.id cnum (csuc (cadd czero (.var 3))) (csuc (.var 1))) cU0 :=
  cidT cnum_typed (csuc_typed (cadd_typed czero_typed (.var 3))) (csuc_typed (.var 1))

/-- **The motive of the successor move is typed** at the eliminator's motive type, over
`n : num, e : eqAt n`. -/
theorem cSucMotive_typed : CTyped objectChurch cEqAtTele cSucMotive
    (.pi cnum (.pi (.id cnum (cadd czero (.var 2)) (.var 0)) cU0)) :=
  .lamIntro cnum_typed (.sort _) cSucMotive_type (.sort _)
    (.lamIntro cSucMotive_family (.sort _) cSucMotive_familyType (.sort _) cSucMotive_body)

/-- **The reflexivity case of the successor move is typed** at the motive at the base point
`add 0 n` and its reflexivity, by two β-steps of the motive. -/
theorem cSucReflCase_typed : CTyped objectChurch cEqAtTele (.refl (csuc (cadd czero (.var 1))))
    (.app (.app cSucMotive (cadd czero (.var 1))) (.refl (cadd czero (.var 1)))) :=
  .conv (.reflIntro (csuc_typed (cadd_typed czero_typed (.var 1))))
    (.symm (cbetaTwo cSucMotive_type cSucMotive_familyType (craise cSucMotive_family)
      cSucMotive_body (cadd_typed czero_typed (.var 1))
      (.reflIntro (cadd_typed czero_typed (.var 1)))))
    (.sort Tower.zero)

theorem sucMove_template :
    TemplateTyped objectChurch objectDecls (applyClosed eqAtTelescope ids (.const sucMoveName))
      sucMoveRhs := by
  refine ⟨liftCtx eqAtTelescope, liftTm (eqAtApp (sucNative (.var 1))), by decide, by decide, ?_⟩
  have e : elabRight objectDecls (applyClosed eqAtTelescope ids (.const sucMoveName)) sucMoveRhs =
      (.app (.app (.app (.app (.app (.app (.const jName) cnum) (cadd czero (.var 1))) cSucMotive)
        (.refl (csuc (cadd czero (.var 1))))) (.var 1)) (.var 0) : CTm Tower.Head 2) := by
    decide
  rw [e]
  show CTyped objectChurch cEqAtTele
    (.app (.app (.app (.app (.app (.app (.const jName) cnum) (cadd czero (.var 1))) cSucMotive)
      (.refl (csuc (cadd czero (.var 1))))) (.var 1)) (.var 0))
    (ceqAt (csuc (.var 1)))
  have point : CTyped objectChurch cEqAtTele (cadd czero (.var 1)) cnum :=
    cadd_typed czero_typed (.var 1)
  -- the motive, typed at the eliminator's motive type, and the reflexivity case
  have formedB := cSucMotive_family
  have formed₂ := cSucMotive_familyType
  have formed := cSucMotive_type
  have bodyM := cSucMotive_body
  have motiveTyped := cSucMotive_typed
  have reflCase := cSucReflCase_typed
  -- the evidence, retyped by the equation of `eqAt`
  have eAt : CEqual objectChurch cEqAtTele (ceqAt (.var 1))
      (.id cnum (cadd czero (.var 1)) (.var 1)) cU0 :=
    .rootAdmitted (ceqAt_step _) (ceqAt_admits (.var 1)) (ceqAt_typed (.var 1))
      (cidT cnum_typed point (.var 1))
  have path : CTyped objectChurch cEqAtTele (.var 0) (.id cnum (cadd czero (.var 1)) (.var 1)) :=
    .conv (.var 0) eAt (.sort Tower.zero)
  -- the eliminator
  have j0 : CTyped objectChurch cEqAtTele (.const jName) cJType := cj_typed
  have j1 := CDerivable.appElim j0 cnum_typed
  have j2 := CDerivable.appElim j1 point
  have j3 := CDerivable.appElim j2 motiveTyped
  have j4 := CDerivable.appElim j3 reflCase
  have j5 := CDerivable.appElim j4 (CDerivable.var 1)
  have j6 := CDerivable.appElim j5 path
  -- the motive at the endpoint is `eqAt (suc n)`: β, `eqAt`, `add`
  have βend := cbetaTwo formed formed₂ (craise formedB) bodyM (CDerivable.var 1) path
  have eqAtSuc : CEqual objectChurch cEqAtTele (ceqAt (csuc (.var 1)))
      (.id cnum (cadd czero (csuc (.var 1))) (csuc (.var 1))) cU0 :=
    .rootAdmitted (ceqAt_step _) (ceqAt_admits (csuc_typed (.var 1)))
      (ceqAt_typed (csuc_typed (.var 1)))
      (cidT cnum_typed (cadd_typed czero_typed (csuc_typed (.var 1))) (csuc_typed (.var 1)))
  have addSuc : CEqual objectChurch cEqAtTele (cadd czero (csuc (.var 1)))
      (csuc (cadd czero (.var 1))) cnum :=
    .rootAdmitted (caddSuc_step _ _) (caddSuc_admits czero_typed (.var 1))
      (cadd_typed czero_typed (csuc_typed (.var 1))) (csuc_typed point)
  have idEq : CEqual objectChurch cEqAtTele
      (.id cnum (cadd czero (csuc (.var 1))) (csuc (.var 1)))
      (.id cnum (csuc (cadd czero (.var 1))) (csuc (.var 1))) cU0 :=
    .idCong (.refl cnum_typed) (.sort _) addSuc (.refl (csuc_typed (.var 1)))
  exact .conv j6 (.trans βend (.symm (.trans eqAtSuc idEq))) (.sort Tower.zero)

/-- The telescope of `composeCert`, annotated. -/
abbrev cComposeTele : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0))
    (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0))))))
    (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))))
    (.var 3)) (.app (.var 3) (.var 0))

theorem compose_template :
    TemplateTyped objectChurch objectDecls (applyClosed composeTelescope ids (.const composeName))
      composeRhs := by
  refine ⟨liftCtx composeTelescope, liftTm (.sigma (.var 5) (.app (.var 5) (.var 0))),
    by decide, by decide, ?_⟩
  have e : elabRight objectDecls (applyClosed composeTelescope ids (.const composeName))
      composeRhs =
      (.app (.lam (.sigma (.var 5) (.app (.var 5) (.var 0)))
          (.app (.app (.var 3) (.fst (.var 0))) (.snd (.var 0))))
        (.app (.app (.var 3) (.var 1)) (.var 0)) : CTm Tower.Head 6) := by decide
  rw [e]
  show CTyped objectChurch cComposeTele
    (.app (.lam (.sigma (.var 5) (.app (.var 5) (.var 0)))
        (.app (.app (.var 3) (.fst (.var 0))) (.snd (.var 0))))
      (.app (.app (.var 3) (.var 1)) (.var 0)))
    (.sigma (.var 5) (.app (.var 5) (.var 0)))
  have sigmaTyped : CTyped objectChurch cComposeTele (.sigma (.var 5) (.app (.var 5) (.var 0)))
      cU0 :=
    csigmaT (.var 5) (.appElim (B := cU0) (.var 5) (.var 0))
  have package := CDerivable.appElim
    (CDerivable.appElim (CDerivable.var (P := objectChurch) (Γ := cComposeTele) 3) (.var 1))
    (.var 0)
  have pkg : CTyped objectChurch
      (.snoc cComposeTele (.sigma (.var 5) (.app (.var 5) (.var 0))))
      (.var 0) (.sigma (.var 6) (.app (.var 6) (.var 0))) := .var 0
  have b1 := CDerivable.appElim
    (CDerivable.var (P := objectChurch)
      (Γ := .snoc cComposeTele (.sigma (.var 5) (.app (.var 5) (.var 0)))) 3)
    (CDerivable.fstElim pkg)
  have b2 := CDerivable.appElim b1 (CDerivable.sndElim pkg)
  have arrow : CTyped objectChurch cComposeTele
      (.pi (.sigma (.var 5) (.app (.var 5) (.var 0))) (.sigma (.var 6) (.app (.var 6) (.var 0))))
      cU0 :=
    cpiT sigmaTyped (CTyped.weaken sigmaTyped)
  have closure := CDerivable.lamIntro sigmaTyped (.sort _) arrow (.sort _) b2
  exact CDerivable.appElim closure package

theorem returnIter_template :
    TemplateTyped objectChurch objectDecls (applyClosed returnIterTele ids (.const returnIterName))
      returnIterRhs := by
  refine ⟨liftCtx returnIterTele, liftTm returnIterResult, by decide, by decide, ?_⟩
  have e : elabRight objectDecls (applyClosed returnIterTele ids (.const returnIterName))
      returnIterRhs =
      (.lam (.pi (.var 0) cU0) (.lam cnum
        (.lam (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0)))))
          (.lam (.var 3) (.lam (.app (.var 3) (.var 0))
            (.app (.app (.app (.app (.app (.app (.const iterName) (.var 3)) (.var 5)) (.var 4))
              (.var 2)) (.var 1)) (.var 0)))))) : CTm Tower.Head 1) := by decide
  rw [e]
  let c1 : CCtx Tower.Head 1 := .snoc .nil cU0
  let c2 : CCtx Tower.Head 2 := .snoc c1 (.pi (.var 0) cU0)
  let c3 : CCtx Tower.Head 3 := .snoc c2 cnum
  let c4 : CCtx Tower.Head 4 :=
    .snoc c3 (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0)))))
  let c5 : CCtx Tower.Head 5 := .snoc c4 (.var 3)
  let c6 : CCtx Tower.Head 6 := .snoc c5 (.app (.var 3) (.var 0))
  show CTyped objectChurch c1 _ _
  -- the innermost body
  have i1 := CDerivable.appElim (citer_typed (Γ := c6)) (CDerivable.var 3)
  have i2 := CDerivable.appElim i1 (CDerivable.var 5)
  have i3 := CDerivable.appElim i2 (CDerivable.var 4)
  have i4 := CDerivable.appElim i3 (CDerivable.var 2)
  have i5 := CDerivable.appElim i4 (CDerivable.var 1)
  have body := CDerivable.appElim i5 (CDerivable.var 0)
  -- the domains and the function types
  have tStep : CTyped objectChurch c3
      (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0))))) cU0 :=
    CTyped.weaken (cstepFamily_formed (Δ := .nil))
  have fe : CTyped objectChurch c5
      (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))) cU0 :=
    cpiT (.appElim (B := cU0) (.var 3) (.var 0))
      (csigmaT (.var 5) (.appElim (B := cU0) (.var 5) (.var 0)))
  have fx : CTyped objectChurch c4
      (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0))))) cU0 :=
    cpiT (.var 3) fe
  have fs : CTyped objectChurch c3
      (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.sigma (.var 4) (.app (.var 4) (.var 0)))))
        (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0))))))
      cU0 :=
    cpiT tStep fx
  have fn : CTyped objectChurch c2
      (.pi cnum (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0))
          (.sigma (.var 4) (.app (.var 4) (.var 0)))))
        (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.sigma (.var 5) (.app (.var 5) (.var 0)))))))
      cU0 :=
    cpiT cnum_typed fs
  have tMotive : CTyped objectChurch c1 (.pi (.var 0) cU0) cU1 :=
    cpiT (craise (.var 0)) cU0_typed
  have fp := cpiT tMotive (craise fn)
  exact .lamIntro tMotive (.sort _) fp (.sort _)
    (.lamIntro cnum_typed (.sort _) fn (.sort _)
      (.lamIntro tStep (.sort _) fs (.sort _)
        (.lamIntro (.var 3) (.sort _) fx (.sort _)
          (.lamIntro (.appElim (B := cU0) (.var 3) (.var 0)) (.sort _) fe (.sort _) body))))

/-! ## Definitions by structural recursion -/

theorem addZero_template :
    TemplateTyped objectChurch objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN [])) := by
  refine ⟨.snoc .nil cnum, cnum, by decide, by decide, ?_⟩
  have e : elabRight objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 0 0 zeroN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 []) (addBody zeroN [])) =
      (.var 0 : CTm Tower.Head 1) := by decide
  rw [e]
  exact .var 0

theorem addSuc_template :
    TemplateTyped objectChurch objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 [.recursive])
        (addBody sucN [.recursive])) := by
  refine ⟨.snoc (.snoc .nil cnum) cnum, cnum, by decide, by decide, ?_⟩
  have e : elabRight objectDecls
      (applyClosed (ofEntries addEntries 2) (patternSub 1 1 0 sucN) (.const addN))
      (Presentation.subst (hypSub addN addEntries 1 0 [.recursive]) (addBody sucN [.recursive])) =
      (csuc (cadd (.var 1) (.var 0)) : CTm Tower.Head 2) := by decide
  rw [e]
  exact csuc_typed (cadd_typed (.var 1) (.var 0))

theorem powZero_template :
    TemplateTyped objectChurch objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 []) (powBody zeroN [])) := by
  refine ⟨.snoc .nil cset, cset, by decide, by decide, ?_⟩
  have e : elabRight objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 0 1 zeroN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 []) (powBody zeroN [])) =
      (.var 0 : CTm Tower.Head 1) := by decide
  rw [e]
  exact .var 0

theorem powSuc_template :
    TemplateTyped objectChurch objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 [.recursive])
        (powBody sucN [.recursive])) := by
  refine ⟨.snoc (.snoc .nil cnum) cset, cset, by decide, by decide, ?_⟩
  have e : elabRight objectDecls
      (applyClosed (ofEntries powEntries 2) (patternSub 0 1 1 sucN) (.const powN))
      (Presentation.subst (hypSub powN powEntries 0 1 [.recursive]) (powBody sucN [.recursive])) =
      (.app (.const powerN) (.app (.app (.const powN) (.var 1)) (.var 0)) :
        CTm Tower.Head 2) := by decide
  rw [e]
  have tPow := CDerivable.appElim
    (CDerivable.appElim (cpowConst_typed (Γ := .snoc (.snoc .nil cnum) cset)) (.var 1)) (.var 0)
  exact CDerivable.appElim cpowerConst_typed tPow

/-- The context of the equation of the iterator at zero, annotated. -/
abbrev cIterTele : CCtx Tower.Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil cU0) (.pi (.var 0) cU0))
    (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0))))))
    (.var 2)) (.app (.var 2) (.var 0))

theorem iterZero_template :
    TemplateTyped objectChurch objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN [])) := by
  refine ⟨cIterTele, .sigma (.var 4) (.app (.var 4) (.var 0)), by decide, by decide, ?_⟩
  have e : elabRight objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 0 5 zeroN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 []) (iterBody zeroN [])) =
      (.pair (.var 1) (.var 0) : CTm Tower.Head 5) := by decide
  rw [e]
  exact .pairIntro (csigmaT (.var 4) (.appElim (B := cU0) (.var 4) (.var 0))) (.sort Tower.zero)
    (.var 1) (.var 0)

/-- The context of the equation of the iterator at a successor, annotated. -/
abbrev cIterSucTele : CCtx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil cnum) cU0) (.pi (.var 0) cU0))
    (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0))))))
    (.var 2)) (.app (.var 2) (.var 0))

theorem iterSuc_template :
    TemplateTyped objectChurch objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) := by
  refine ⟨cIterSucTele, .sigma (.var 4) (.app (.var 4) (.var 0)), by decide, by decide, ?_⟩
  have e : elabRight objectDecls
      (applyClosed (ofEntries iterEntries 6) (patternSub 0 1 5 sucN) (.const iterName))
      (Presentation.subst (hypSub iterName iterEntries 0 5 [.recursive])
        (iterBody sucN [.recursive])) =
      (.app (.lam (.sigma (.var 4) (.app (.var 4) (.var 0)))
          (.app (.app (.app (.app (.app (.app (.const iterName) (.var 6)) (.var 5)) (.var 4))
            (.var 3)) (.fst (.var 0))) (.snd (.var 0))))
        (.app (.app (.var 2) (.var 1)) (.var 0)) : CTm Tower.Head 6) := by decide
  rw [e]
  have sigmaTyped : CTyped objectChurch cIterSucTele (.sigma (.var 4) (.app (.var 4) (.var 0)))
      cU0 :=
    csigmaT (.var 4) (.appElim (B := cU0) (.var 4) (.var 0))
  have package := CDerivable.appElim
    (CDerivable.appElim (CDerivable.var (P := objectChurch) (Γ := cIterSucTele) 2) (.var 1))
    (.var 0)
  have pkg : CTyped objectChurch
      (.snoc cIterSucTele (.sigma (.var 4) (.app (.var 4) (.var 0))))
      (.var 0) (.sigma (.var 5) (.app (.var 5) (.var 0))) := .var 0
  have c1 := CDerivable.appElim
    (citer_typed (Γ := .snoc cIterSucTele (.sigma (.var 4) (.app (.var 4) (.var 0)))))
    (CDerivable.var 6)
  have c2 := CDerivable.appElim c1 (CDerivable.var 5)
  have c3 := CDerivable.appElim c2 (CDerivable.var 4)
  have c4 := CDerivable.appElim c3 (CDerivable.var 3)
  have c5 := CDerivable.appElim c4 (CDerivable.fstElim pkg)
  have c6 := CDerivable.appElim c5 (CDerivable.sndElim pkg)
  have arrow : CTyped objectChurch cIterSucTele
      (.pi (.sigma (.var 4) (.app (.var 4) (.var 0))) (.sigma (.var 5) (.app (.var 5) (.var 0))))
      cU0 :=
    cpiT sigmaTyped (CTyped.weaken sigmaTyped)
  have closure := CDerivable.lamIntro sigmaTyped (.sort _) arrow (.sort _) c6
  exact CDerivable.appElim closure package

/-! ## The recursor -/

/-- The motive and the two methods of `num-rec`, annotated. -/
abbrev cRecTele : CCtx Tower.Head 3 :=
  .snoc (.snoc (.snoc .nil (.pi cnum cU0)) (.app (.var 0) czero))
    (.pi cnum (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (csuc (.var 1)))))

theorem numRecZero_template :
    TemplateTyped objectChurch objectDecls (iotaLeft numRecName zeroN 2 0)
      (iotaRight numRecName 2 0 ([] : List CtorField)) := by
  refine ⟨cRecTele, .app (.var 2) czero, by decide, by decide, ?_⟩
  have e : elabRight objectDecls (iotaLeft numRecName zeroN 2 0)
      (iotaRight numRecName 2 0 ([] : List CtorField)) = (.var 1 : CTm Tower.Head 3) := by decide
  rw [e]
  exact .var 1

theorem numRecSuc_template :
    TemplateTyped objectChurch objectDecls (iotaLeft numRecName sucN 2 1)
      (iotaRight numRecName 2 1 [(.recursive : CtorField)]) := by
  refine ⟨.snoc cRecTele cnum, .app (.var 3) (csuc (.var 0)), by decide, by decide, ?_⟩
  have e : elabRight objectDecls (iotaLeft numRecName sucN 2 1)
      (iotaRight numRecName 2 1 [(.recursive : CtorField)]) =
      (.app (.app (.var 1) (.var 0))
        (.app (.app (.app (.app (.const numRecName) (.var 3)) (.var 2)) (.var 1)) (.var 0)) :
        CTm Tower.Head 4) := by decide
  rw [e]
  have r1 := CDerivable.appElim (cnumRec_typed (Γ := .snoc cRecTele cnum)) (.var 3)
  have r2 := CDerivable.appElim r1 (.var 2)
  have r3 := CDerivable.appElim r2 (.var 1)
  have r4 := CDerivable.appElim r3 (.var 0)
  have m1 := CDerivable.appElim (CDerivable.var (P := objectChurch) (Γ := .snoc cRecTele cnum) 1)
    (.var 0)
  exact CDerivable.appElim m1 r4

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
