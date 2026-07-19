import Mettapedia.Languages.OpenTheory.CoreTerm

/-!
# The first six nonbinding OpenTheory kernel rules

This module gives both an executable checker and an independent,
proof-relevant semantics for `axiom`, `assume`, `refl`, `app`,
`deductAntisym`, and `eqMp` at OpenTheory revision
`f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`.

The raw checker deliberately follows source partiality.  In particular, it
does not impose a global Boolean-sequent gate on rules whose source
implementations do not have one.  A verified wrapper is a separate profile.
-/

namespace Mettapedia.Languages.OpenTheory

namespace Theorem

/-- The theorem produced by the primitive `axiom` rule. -/
def axiomResult (sequent : Sequent) (hbool : sequent.IsBool) : Theorem :=
  { axioms := {sequent}
    axiomsBoolean := by
      intro tagged htagged
      have htaggedEq : tagged = sequent := by
        simpa using htagged
      subst tagged
      exact hbool
    sequent := sequent }

/-- A theorem result with no axiom provenance. -/
def emptyResult (hyp : Finset CanonicalTerm) (concl : CanonicalTerm) : Theorem :=
  { axioms := ∅
    axiomsBoolean := by simp
    sequent := ⟨hyp, concl⟩ }

/-- A binary-rule result with the exact union of both axiom-provenance sets. -/
def unionResult (left right : Theorem)
    (hyp : Finset CanonicalTerm) (concl : CanonicalTerm) : Theorem :=
  { axioms := left.axioms ∪ right.axioms
    axiomsBoolean := left.axiomsBoolean_union right
    sequent := ⟨hyp, concl⟩ }

end Theorem

/-! ## Independent declarative semantics -/

/-- Exact structural theorem output, including axiom provenance. -/
def HasParts (out : Theorem) (axioms : Finset Sequent)
    (hyp : Finset CanonicalTerm) (concl : CanonicalTerm) : Prop :=
  out.axioms = axioms ∧
    out.sequent.hyp = hyp ∧
    out.sequent.concl = concl

namespace HasParts

/-- Exact parts determine a theorem structurally, not merely under source
theorem comparison (which intentionally ignores axiom provenance). -/
theorem eq {out candidate : Theorem}
    (hparts : HasParts out candidate.axioms candidate.sequent.hyp
      candidate.sequent.concl) :
    out = candidate := by
  apply Theorem.ext hparts.1
  apply Sequent.ext
  · exact hparts.2.1
  · exact hparts.2.2

/-- The theorem's current sequent is exactly the displayed conclusion and
hypothesis set. -/
theorem sequent_eq {out : Theorem} {axioms : Finset Sequent}
    {hyp : Finset CanonicalTerm} {concl : CanonicalTerm}
    (hparts : HasParts out axioms hyp concl) :
    out.sequent = ⟨hyp, concl⟩ := by
  apply Sequent.ext
  · exact hparts.2.1
  · exact hparts.2.2

end HasParts

@[simp] theorem theorem_axiomResult_eq_iff_hasParts
    (sequent : Sequent) (hbool : sequent.IsBool) (out : Theorem) :
    Theorem.axiomResult sequent hbool = out ↔
      HasParts out {sequent} sequent.hyp sequent.concl := by
  constructor
  · intro heq
    subst out
    exact ⟨rfl, rfl, rfl⟩
  · intro hparts
    exact hparts.eq.symm

@[simp] theorem theorem_emptyResult_eq_iff_hasParts
    (hyp : Finset CanonicalTerm) (concl : CanonicalTerm) (out : Theorem) :
    Theorem.emptyResult hyp concl = out ↔
      HasParts out ∅ hyp concl := by
  constructor
  · intro heq
    subst out
    exact ⟨rfl, rfl, rfl⟩
  · intro hparts
    exact hparts.eq.symm

@[simp] theorem theorem_unionResult_eq_iff_hasParts
    (left right : Theorem) (hyp : Finset CanonicalTerm)
    (concl : CanonicalTerm) (out : Theorem) :
    Theorem.unionResult left right hyp concl = out ↔
      HasParts out (left.axioms ∪ right.axioms) hyp concl := by
  constructor
  · intro heq
    subst out
    exact ⟨rfl, rfl, rfl⟩
  · intro hparts
    exact hparts.eq.symm

/-- Declarative semantics of primitive `axiom`. -/
def AxiomSemantics (sequent : Sequent) (out : Theorem) : Prop :=
  sequent.IsBool ∧
    HasParts out {sequent} sequent.hyp sequent.concl

/-- Declarative semantics of primitive `assume`. -/
def AssumeSemantics (term : CanonicalTerm) (out : Theorem) : Prop :=
  term.IsBool ∧
    HasParts out ∅ {term} term

/-- Declarative semantics of primitive `refl`. -/
def ReflSemantics (term : CanonicalTerm) (out : Theorem) : Prop :=
  ∃ equality,
    CanonicalTerm.EqualityConstructionSemantics term term equality ∧
      HasParts out ∅ ∅ equality

/-- Declarative semantics of primitive theorem application. -/
def AppSemantics (functionEquality argumentEquality out : Theorem) : Prop :=
  ∃ functionLeft functionRight argumentLeft argumentRight
      applicationLeft applicationRight equality,
    CanonicalTerm.EqualityViewSemantics
        functionEquality.sequent.concl functionLeft functionRight ∧
      CanonicalTerm.EqualityViewSemantics
        argumentEquality.sequent.concl argumentLeft argumentRight ∧
      CanonicalTerm.ApplicationSemantics
        functionLeft argumentLeft applicationLeft ∧
      CanonicalTerm.ApplicationSemantics
        functionRight argumentRight applicationRight ∧
      CanonicalTerm.EqualityConstructionSemantics
        applicationLeft applicationRight equality ∧
      HasParts out
        (functionEquality.axioms ∪ argumentEquality.axioms)
        (functionEquality.sequent.hyp ∪ argumentEquality.sequent.hyp)
        equality

/-- Declarative semantics of primitive deduction antisymmetry. -/
def DeductAntisymSemantics (left right out : Theorem) : Prop :=
  ∃ equality,
    CanonicalTerm.EqualityConstructionSemantics
        left.sequent.concl right.sequent.concl equality ∧
      HasParts out (left.axioms ∪ right.axioms)
        ((left.sequent.hyp.erase right.sequent.concl) ∪
          (right.sequent.hyp.erase left.sequent.concl))
        equality

/-- Declarative semantics of primitive equality modus ponens. -/
def EqMpSemantics (equality premise out : Theorem) : Prop :=
  ∃ left right,
    CanonicalTerm.EqualityViewSemantics equality.sequent.concl left right ∧
      left = premise.sequent.concl ∧
      HasParts out (equality.axioms ∪ premise.axioms)
        (equality.sequent.hyp ∪ premise.sequent.hyp) right

/-- Requests for the first nonbinding primitive-rule tranche. -/
inductive CoreRequest where
  | axiom (sequent : Sequent)
  | assume (term : CanonicalTerm)
  | refl (term : CanonicalTerm)
  | app (functionEquality argumentEquality : Theorem)
  | deductAntisym (left right : Theorem)
  | eqMp (equality premise : Theorem)

/-- A Type-valued certificate for one primitive inference.  Intermediate terms
are retained as data rather than hidden inside propositional existentials. -/
inductive CoreEvidence : CoreRequest → Theorem → Type where
  | axiom (hbool : sequent.IsBool)
      (parts : HasParts out {sequent} sequent.hyp sequent.concl) :
      CoreEvidence (.axiom sequent) out
  | assume (hbool : term.IsBool)
      (parts : HasParts out ∅ {term} term) :
      CoreEvidence (.assume term) out
  | refl (equality : CanonicalTerm)
      (construction : CanonicalTerm.EqualityConstructionSemantics
        term term equality)
      (parts : HasParts out ∅ ∅ equality) :
      CoreEvidence (.refl term) out
  | app (functionLeft functionRight argumentLeft argumentRight
      applicationLeft applicationRight equality : CanonicalTerm)
      (functionView : CanonicalTerm.EqualityViewSemantics
        functionEquality.sequent.concl functionLeft functionRight)
      (argumentView : CanonicalTerm.EqualityViewSemantics
        argumentEquality.sequent.concl argumentLeft argumentRight)
      (leftApplication : CanonicalTerm.ApplicationSemantics
        functionLeft argumentLeft applicationLeft)
      (rightApplication : CanonicalTerm.ApplicationSemantics
        functionRight argumentRight applicationRight)
      (construction : CanonicalTerm.EqualityConstructionSemantics
        applicationLeft applicationRight equality)
      (parts : HasParts out
        (functionEquality.axioms ∪ argumentEquality.axioms)
        (functionEquality.sequent.hyp ∪ argumentEquality.sequent.hyp)
        equality) :
      CoreEvidence (.app functionEquality argumentEquality) out
  | deductAntisym (equality : CanonicalTerm)
      (construction : CanonicalTerm.EqualityConstructionSemantics
        left.sequent.concl right.sequent.concl equality)
      (parts : HasParts out (left.axioms ∪ right.axioms)
        ((left.sequent.hyp.erase right.sequent.concl) ∪
          (right.sequent.hyp.erase left.sequent.concl))
        equality) :
      CoreEvidence (.deductAntisym left right) out
  | eqMp (left right : CanonicalTerm)
      (view : CanonicalTerm.EqualityViewSemantics
        equality.sequent.concl left right)
      (hmatch : left = premise.sequent.concl)
      (parts : HasParts out (equality.axioms ∪ premise.axioms)
        (equality.sequent.hyp ∪ premise.sequent.hyp) right) :
      CoreEvidence (.eqMp equality premise) out

/-- Declarative derivability is inhabited Type-valued inference evidence. -/
def CoreStep (request : CoreRequest) (out : Theorem) : Prop :=
  Nonempty (CoreEvidence request out)

theorem axiomSemantics_iff_coreStep (sequent : Sequent) (out : Theorem) :
    AxiomSemantics sequent out ↔ CoreStep (.axiom sequent) out := by
  constructor
  · rintro ⟨hbool, parts⟩
    exact ⟨CoreEvidence.axiom hbool parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | «axiom» hbool parts => exact ⟨hbool, parts⟩

theorem assumeSemantics_iff_coreStep (term : CanonicalTerm) (out : Theorem) :
    AssumeSemantics term out ↔ CoreStep (.assume term) out := by
  constructor
  · rintro ⟨hbool, parts⟩
    exact ⟨CoreEvidence.assume hbool parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | «assume» hbool parts => exact ⟨hbool, parts⟩

theorem reflSemantics_iff_coreStep (term : CanonicalTerm) (out : Theorem) :
    ReflSemantics term out ↔ CoreStep (.refl term) out := by
  constructor
  · rintro ⟨equality, construction, parts⟩
    exact ⟨CoreEvidence.refl equality construction parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | refl equality construction parts =>
        exact ⟨equality, construction, parts⟩

theorem appSemantics_iff_coreStep
    (functionEquality argumentEquality out : Theorem) :
    AppSemantics functionEquality argumentEquality out ↔
      CoreStep (.app functionEquality argumentEquality) out := by
  constructor
  · rintro ⟨functionLeft, functionRight, argumentLeft, argumentRight,
      applicationLeft, applicationRight, equality, functionView, argumentView,
      leftApplication, rightApplication, construction, parts⟩
    exact ⟨CoreEvidence.app functionLeft functionRight argumentLeft argumentRight
      applicationLeft applicationRight equality functionView argumentView
      leftApplication rightApplication construction parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | app functionLeft functionRight argumentLeft argumentRight
        applicationLeft applicationRight equality functionView argumentView
        leftApplication rightApplication construction parts =>
        exact ⟨functionLeft, functionRight, argumentLeft, argumentRight,
          applicationLeft, applicationRight, equality, functionView,
          argumentView, leftApplication, rightApplication, construction, parts⟩

theorem deductAntisymSemantics_iff_coreStep
    (left right out : Theorem) :
    DeductAntisymSemantics left right out ↔
      CoreStep (.deductAntisym left right) out := by
  constructor
  · rintro ⟨equality, construction, parts⟩
    exact ⟨CoreEvidence.deductAntisym equality construction parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | deductAntisym equality construction parts =>
        exact ⟨equality, construction, parts⟩

theorem eqMpSemantics_iff_coreStep (equality premise out : Theorem) :
    EqMpSemantics equality premise out ↔
      CoreStep (.eqMp equality premise) out := by
  constructor
  · rintro ⟨left, right, view, hmatch, parts⟩
    exact ⟨CoreEvidence.eqMp left right view hmatch parts⟩
  · rintro ⟨evidence⟩
    cases evidence with
    | eqMp left right view hmatch parts =>
        exact ⟨left, right, view, hmatch, parts⟩

/-! ## Executable raw checker -/

/-- Execute primitive `axiom`, including its Boolean-sequent gate. -/
def checkAxiom (sequent : Sequent) : Option Theorem :=
  if hbool : sequent.isBoolB then
    some (Theorem.axiomResult sequent
      ((Sequent.isBoolB_eq_true_iff sequent).mp hbool))
  else
    none

/-- Execute primitive `assume`, including its Boolean-term gate. -/
def checkAssume (term : CanonicalTerm) : Option Theorem :=
  if _ : term.isBoolB then
    some (Theorem.emptyResult {term} term)
  else
    none

/-- Execute primitive reflexivity at any checked term type. -/
def checkRefl (term : CanonicalTerm) : Option Theorem := do
  let equality ← term.mkEquality? term
  pure (Theorem.emptyResult ∅ equality)

/-- Execute primitive theorem application. -/
def checkApp (functionEquality argumentEquality : Theorem) : Option Theorem := do
  let (functionLeft, functionRight) ←
    functionEquality.sequent.concl.destEquality?
  let (argumentLeft, argumentRight) ←
    argumentEquality.sequent.concl.destEquality?
  let applicationLeft ← functionLeft.apply? argumentLeft
  let applicationRight ← functionRight.apply? argumentRight
  let equality ← applicationLeft.mkEquality? applicationRight
  pure (Theorem.unionResult functionEquality argumentEquality
    (functionEquality.sequent.hyp ∪ argumentEquality.sequent.hyp) equality)

/-- Execute primitive deduction antisymmetry. -/
def checkDeductAntisym (left right : Theorem) : Option Theorem := do
  let equality ← left.sequent.concl.mkEquality? right.sequent.concl
  pure (Theorem.unionResult left right
    ((left.sequent.hyp.erase right.sequent.concl) ∪
      (right.sequent.hyp.erase left.sequent.concl))
    equality)

/-- Execute primitive equality modus ponens. -/
def checkEqMp (equality premise : Theorem) : Option Theorem := do
  let (left, right) ← equality.sequent.concl.destEquality?
  if left.same premise.sequent.concl then
    pure (Theorem.unionResult equality premise
      (equality.sequent.hyp ∪ premise.sequent.hyp) right)
  else
    none

/-- Dispatch the executable first-six-rule checker. -/
def checkCore : CoreRequest → Option Theorem
  | .axiom sequent => checkAxiom sequent
  | .assume term => checkAssume term
  | .refl term => checkRefl term
  | .app functionEquality argumentEquality =>
      checkApp functionEquality argumentEquality
  | .deductAntisym left right => checkDeductAntisym left right
  | .eqMp equality premise => checkEqMp equality premise

/-! ## Type-valued one-step certificates -/

/-- A checked theorem paired with inspectable evidence for the requested rule. -/
abbrev CertifiedCoreResult (request : CoreRequest) :=
  Σ out, CoreEvidence request out

/-- Execute a request while retaining its intermediate-term certificate.  This
is one inference step; recursive article trails are a later layer. -/
def checkCoreEvidence (request : CoreRequest) :
    Option (CertifiedCoreResult request) :=
  match request with
  | .axiom sequent =>
      if hbool : sequent.isBoolB then
        let hsem := (Sequent.isBoolB_eq_true_iff sequent).mp hbool
        let out := Theorem.axiomResult sequent hsem
        some ⟨out, CoreEvidence.axiom hsem ⟨rfl, rfl, rfl⟩⟩
      else
        none
  | .assume term =>
      if hbool : term.isBoolB then
        let hsem := (CanonicalTerm.isBoolB_eq_true_iff term).mp hbool
        let out := Theorem.emptyResult {term} term
        some ⟨out, CoreEvidence.assume hsem ⟨rfl, rfl, rfl⟩⟩
      else
        none
  | .refl term =>
      match hequality : term.mkEquality? term with
      | none => none
      | some equality =>
          let out := Theorem.emptyResult ∅ equality
          some ⟨out, CoreEvidence.refl equality
            ((CanonicalTerm.mkEquality?_eq_some_iff term term equality).mp
              hequality)
            ⟨rfl, rfl, rfl⟩⟩
  | .app functionEquality argumentEquality =>
      match hfunctionView :
          functionEquality.sequent.concl.destEquality? with
      | none => none
      | some (functionLeft, functionRight) =>
          match hargumentView :
              argumentEquality.sequent.concl.destEquality? with
          | none => none
          | some (argumentLeft, argumentRight) =>
              match hleftApplication : functionLeft.apply? argumentLeft with
              | none => none
              | some applicationLeft =>
                  match hrightApplication :
                      functionRight.apply? argumentRight with
                  | none => none
                  | some applicationRight =>
                      match hconstruction :
                          applicationLeft.mkEquality? applicationRight with
                      | none => none
                      | some equality =>
                          let out := Theorem.unionResult
                            functionEquality argumentEquality
                            (functionEquality.sequent.hyp ∪
                              argumentEquality.sequent.hyp)
                            equality
                          some ⟨out, CoreEvidence.app
                            functionLeft functionRight argumentLeft argumentRight
                            applicationLeft applicationRight equality
                            ((CanonicalTerm.destEquality?_eq_some_iff _ _ _).mp
                              hfunctionView)
                            ((CanonicalTerm.destEquality?_eq_some_iff _ _ _).mp
                              hargumentView)
                            ((CanonicalTerm.apply?_eq_some_iff _ _ _).mp
                              hleftApplication)
                            ((CanonicalTerm.apply?_eq_some_iff _ _ _).mp
                              hrightApplication)
                            ((CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp
                              hconstruction)
                            ⟨rfl, rfl, rfl⟩⟩
  | .deductAntisym left right =>
      match hconstruction :
          left.sequent.concl.mkEquality? right.sequent.concl with
      | none => none
      | some equality =>
          let hyp :=
            (left.sequent.hyp.erase right.sequent.concl) ∪
              (right.sequent.hyp.erase left.sequent.concl)
          let out := Theorem.unionResult left right hyp equality
          some ⟨out, CoreEvidence.deductAntisym equality
            ((CanonicalTerm.mkEquality?_eq_some_iff _ _ _).mp hconstruction)
            ⟨rfl, rfl, rfl⟩⟩
  | .eqMp equality premise =>
      match hview : equality.sequent.concl.destEquality? with
      | none => none
      | some (left, right) =>
          if hmatch : left.same premise.sequent.concl then
            let out := Theorem.unionResult equality premise
              (equality.sequent.hyp ∪ premise.sequent.hyp) right
            some ⟨out, CoreEvidence.eqMp left right
              ((CanonicalTerm.destEquality?_eq_some_iff _ _ _).mp hview)
              ((CanonicalTerm.same_eq_true_iff _ _).mp hmatch)
              ⟨rfl, rfl, rfl⟩⟩
          else
            none

/-- Forgetting certificate data recovers the independently defined raw
checker exactly. -/
theorem checkCoreEvidence_map_out (request : CoreRequest) :
    (checkCoreEvidence request).map Sigma.fst = checkCore request := by
  cases request with
  | «axiom» sequent =>
      simp [checkCoreEvidence, checkCore, checkAxiom]
  | «assume» term =>
      simp [checkCoreEvidence, checkCore, checkAssume]
  | refl term =>
      simp only [checkCoreEvidence, checkCore, checkRefl]
      split <;> simp_all
  | app functionEquality argumentEquality =>
      simp only [checkCoreEvidence, checkCore, checkApp]
      repeat' (split <;> simp_all)
  | deductAntisym left right =>
      simp only [checkCoreEvidence, checkCore, checkDeductAntisym]
      split <;> simp_all
  | eqMp equality premise =>
      simp only [checkCoreEvidence, checkCore, checkEqMp]
      repeat' (split <;> simp_all)

/-! ## Success and failure correspondence -/

theorem checkAxiom_eq_some_iff (sequent : Sequent) (out : Theorem) :
    checkAxiom sequent = some out ↔ AxiomSemantics sequent out := by
  by_cases hbool : sequent.isBoolB = true
  · have hsem : sequent.IsBool :=
      (Sequent.isBoolB_eq_true_iff sequent).mp hbool
    simp [checkAxiom, hbool, AxiomSemantics, hsem]
  · have hsem : ¬ sequent.IsBool := by
      intro hsem
      exact hbool ((Sequent.isBoolB_eq_true_iff sequent).mpr hsem)
    simp [checkAxiom, hbool, AxiomSemantics, hsem]

theorem checkAssume_eq_some_iff (term : CanonicalTerm) (out : Theorem) :
    checkAssume term = some out ↔ AssumeSemantics term out := by
  by_cases hbool : term.isBoolB = true
  · have hsem : term.IsBool :=
      (CanonicalTerm.isBoolB_eq_true_iff term).mp hbool
    simp [checkAssume, hbool, AssumeSemantics, hsem]
  · have hsem : ¬ term.IsBool := by
      intro hsem
      exact hbool ((CanonicalTerm.isBoolB_eq_true_iff term).mpr hsem)
    simp [checkAssume, hbool, AssumeSemantics, hsem]

theorem checkRefl_eq_some_iff (term : CanonicalTerm) (out : Theorem) :
    checkRefl term = some out ↔ ReflSemantics term out := by
  simp [checkRefl, ReflSemantics, Option.bind_eq_some_iff,
    CanonicalTerm.mkEquality?_eq_some_iff]

theorem checkApp_eq_some_iff
    (functionEquality argumentEquality out : Theorem) :
    checkApp functionEquality argumentEquality = some out ↔
      AppSemantics functionEquality argumentEquality out := by
  simp [checkApp, AppSemantics, Option.bind_eq_some_iff,
    CanonicalTerm.destEquality?_eq_some_iff,
    CanonicalTerm.apply?_eq_some_iff,
    CanonicalTerm.mkEquality?_eq_some_iff]

theorem checkDeductAntisym_eq_some_iff (left right out : Theorem) :
    checkDeductAntisym left right = some out ↔
      DeductAntisymSemantics left right out := by
  simp [checkDeductAntisym, DeductAntisymSemantics,
    Option.bind_eq_some_iff, CanonicalTerm.mkEquality?_eq_some_iff]

theorem checkEqMp_eq_some_iff (equality premise out : Theorem) :
    checkEqMp equality premise = some out ↔
      EqMpSemantics equality premise out := by
  simp [checkEqMp, EqMpSemantics, Option.bind_eq_some_iff,
    CanonicalTerm.destEquality?_eq_some_iff,
    CanonicalTerm.same_eq_true_iff]

private theorem option_eq_none_iff_no_semantics {α : Type}
    (result : Option α) (Semantics : α → Prop)
    (adequate : ∀ out, result = some out ↔ Semantics out) :
    result = none ↔ ¬ ∃ out, Semantics out := by
  constructor
  · intro hnone ⟨out, evidence⟩
    have hsome := (adequate out).mpr evidence
    rw [hnone] at hsome
    contradiction
  · intro hmissing
    cases hresult : result with
    | none => rfl
    | some out =>
        exfalso
        exact hmissing ⟨out, (adequate out).mp hresult⟩

theorem checkAxiom_eq_none_iff (sequent : Sequent) :
    checkAxiom sequent = none ↔
      ¬ ∃ out, AxiomSemantics sequent out := by
  apply option_eq_none_iff_no_semantics
  exact checkAxiom_eq_some_iff sequent

theorem checkAssume_eq_none_iff (term : CanonicalTerm) :
    checkAssume term = none ↔
      ¬ ∃ out, AssumeSemantics term out := by
  apply option_eq_none_iff_no_semantics
  exact checkAssume_eq_some_iff term

theorem checkRefl_eq_none_iff (term : CanonicalTerm) :
    checkRefl term = none ↔
      ¬ ∃ out, ReflSemantics term out := by
  apply option_eq_none_iff_no_semantics
  exact checkRefl_eq_some_iff term

theorem checkApp_eq_none_iff (functionEquality argumentEquality : Theorem) :
    checkApp functionEquality argumentEquality = none ↔
      ¬ ∃ out, AppSemantics functionEquality argumentEquality out := by
  apply option_eq_none_iff_no_semantics
  exact checkApp_eq_some_iff functionEquality argumentEquality

theorem checkDeductAntisym_eq_none_iff (left right : Theorem) :
    checkDeductAntisym left right = none ↔
      ¬ ∃ out, DeductAntisymSemantics left right out := by
  apply option_eq_none_iff_no_semantics
  exact checkDeductAntisym_eq_some_iff left right

theorem checkEqMp_eq_none_iff (equality premise : Theorem) :
    checkEqMp equality premise = none ↔
      ¬ ∃ out, EqMpSemantics equality premise out := by
  apply option_eq_none_iff_no_semantics
  exact checkEqMp_eq_some_iff equality premise

/-- Executable acceptance is exactly independent proof-relevant derivability. -/
theorem checkCore_eq_some_iff (request : CoreRequest) (out : Theorem) :
    checkCore request = some out ↔ CoreStep request out := by
  cases request with
  | «axiom» sequent =>
      rw [checkCore, checkAxiom_eq_some_iff,
        axiomSemantics_iff_coreStep]
  | «assume» term =>
      rw [checkCore, checkAssume_eq_some_iff,
        assumeSemantics_iff_coreStep]
  | refl term =>
      rw [checkCore, checkRefl_eq_some_iff,
        reflSemantics_iff_coreStep]
  | app functionEquality argumentEquality =>
      rw [checkCore, checkApp_eq_some_iff,
        appSemantics_iff_coreStep]
  | deductAntisym left right =>
      rw [checkCore, checkDeductAntisym_eq_some_iff,
        deductAntisymSemantics_iff_coreStep]
  | eqMp equality premise =>
      rw [checkCore, checkEqMp_eq_some_iff,
        eqMpSemantics_iff_coreStep]

/-- The certificate-producing checker succeeds at exactly the independently
specified derivable output. -/
theorem checkCoreEvidence_map_eq_some_iff
    (request : CoreRequest) (out : Theorem) :
    (checkCoreEvidence request).map Sigma.fst = some out ↔
      CoreStep request out := by
  rw [checkCoreEvidence_map_out, checkCore_eq_some_iff]

/-- Every declarative step is returned with an inspectable certificate whose
first projection is the exact theorem output. -/
theorem checkCoreEvidence_exists_of_step
    {request : CoreRequest} {out : Theorem} (step : CoreStep request out) :
    ∃ certificate : CertifiedCoreResult request,
      checkCoreEvidence request = some certificate ∧ certificate.1 = out := by
  have mapped :=
    (checkCoreEvidence_map_eq_some_iff request out).mpr step
  cases hcertificate : checkCoreEvidence request with
  | none =>
      rw [hcertificate] at mapped
      contradiction
  | some certificate =>
      refine ⟨certificate, rfl, ?_⟩
      simpa [hcertificate] using mapped

/-- Rejection is exactly the absence of a declarative output witness. -/
theorem checkCore_eq_none_iff (request : CoreRequest) :
    checkCore request = none ↔ ¬ ∃ out, CoreStep request out := by
  constructor
  · intro hnone ⟨out, hstep⟩
    have hsome := (checkCore_eq_some_iff request out).mpr hstep
    rw [hnone] at hsome
    contradiction
  · intro hmissing
    cases hcheck : checkCore request with
    | none => rfl
    | some out =>
        exfalso
        exact hmissing ⟨out, (checkCore_eq_some_iff request out).mp hcheck⟩

/-- The first-six declarative kernel is deterministic because the executable
checker has at most one result. -/
theorem CoreStep.deterministic {request : CoreRequest} {left right : Theorem}
    (hleft : CoreStep request left) (hright : CoreStep request right) :
    left = right := by
  have leftAccepted := (checkCore_eq_some_iff request left).mpr hleft
  have rightAccepted := (checkCore_eq_some_iff request right).mpr hright
  exact Option.some.inj (leftAccepted.symm.trans rightAccepted)

/-! ## Verified profile -/

/-- Evidence for the additional premises required by the verified profile.
Nullary rules need no Boolean premise; each binary constructor carries
Booleanity of both input theorem sequents. -/
inductive VerifiedInputs : CoreRequest → Prop where
  | axiom : VerifiedInputs (.axiom sequent)
  | assume : VerifiedInputs (.assume term)
  | refl : VerifiedInputs (.refl term)
  | app : left.sequent.IsBool → right.sequent.IsBool →
      VerifiedInputs (.app left right)
  | deductAntisym : left.sequent.IsBool → right.sequent.IsBool →
      VerifiedInputs (.deductAntisym left right)
  | eqMp : equality.sequent.IsBool → premise.sequent.IsBool →
      VerifiedInputs (.eqMp equality premise)

/-- A primitive request together with the verified-profile input invariant. -/
structure VerifiedRequest where
  raw : CoreRequest
  inputs : VerifiedInputs raw

/-- The verified profile is closed under every first-six declarative step. -/
theorem CoreStep.outputIsBool {request : CoreRequest} {out : Theorem}
    (step : CoreStep request out) (inputs : VerifiedInputs request) :
    out.sequent.IsBool := by
  rcases step with ⟨evidence⟩
  cases evidence with
  | «axiom» hbool hparts =>
      cases inputs
      rw [hparts.sequent_eq]
      exact hbool
  | «assume» hbool hparts =>
      cases inputs
      rw [hparts.sequent_eq]
      constructor
      · exact hbool
      · intro hypothesis hmember
        simp only [Finset.mem_singleton] at hmember
        subst hypothesis
        exact hbool
  | refl equality construction hparts =>
      cases inputs
      rw [hparts.sequent_eq]
      constructor
      · exact construction.resultIsBool
      · simp
  | app functionLeft functionRight argumentLeft argumentRight
      applicationLeft applicationRight equality functionView argumentView
      leftApplication rightApplication construction hparts =>
      cases inputs with
      | app leftBool rightBool =>
          rw [hparts.sequent_eq]
          constructor
          · exact construction.resultIsBool
          · intro hypothesis hmember
            rw [Finset.mem_union] at hmember
            rcases hmember with hleft | hright
            · exact leftBool.2 hypothesis hleft
            · exact rightBool.2 hypothesis hright
  | deductAntisym equality construction hparts =>
      cases inputs with
      | deductAntisym leftBool rightBool =>
          rw [hparts.sequent_eq]
          constructor
          · exact construction.resultIsBool
          · intro hypothesis hmember
            rw [Finset.mem_union] at hmember
            rcases hmember with hleft | hright
            · exact leftBool.2 hypothesis (Finset.mem_of_mem_erase hleft)
            · exact rightBool.2 hypothesis (Finset.mem_of_mem_erase hright)
  | eqMp left right view hmatch hparts =>
      cases inputs with
      | eqMp equalityBool premiseBool =>
          have hleftBool : left.IsBool := by
            rw [hmatch]
            exact premiseBool.1
          have hrightBool : right.IsBool := by
            unfold CanonicalTerm.IsBool
            calc
              right.ty = left.ty := view.1.symm
              _ = Ty.bool := hleftBool
          rw [hparts.sequent_eq]
          constructor
          · exact hrightBool
          · intro hypothesis hmember
            rw [Finset.mem_union] at hmember
            rcases hmember with hleft | hright
            · exact equalityBool.2 hypothesis hleft
            · exact premiseBool.2 hypothesis hright

/-- Run the raw checker and package its output with the verified invariant. -/
def checkVerified (request : VerifiedRequest) : Option VerifiedTheorem :=
  match haccepted : checkCore request.raw with
  | none => none
  | some out =>
      some
        { raw := out
          currentBool :=
            CoreStep.outputIsBool
              ((checkCore_eq_some_iff request.raw out).mp haccepted)
              request.inputs }

/-- Erasing verified evidence recovers the exact raw checker result. -/
theorem checkVerified_map_raw (request : VerifiedRequest) :
    (checkVerified request).map VerifiedTheorem.raw = checkCore request.raw := by
  unfold checkVerified
  split <;> simp_all

/-- Verified checking accepts exactly the same declarative step whenever the
verified input invariant is supplied. -/
theorem checkVerified_raw_eq_some_iff
    (request : VerifiedRequest) (out : Theorem) :
    (checkVerified request).map VerifiedTheorem.raw = some out ↔
      CoreStep request.raw out := by
  rw [checkVerified_map_raw, checkCore_eq_some_iff]

end Mettapedia.Languages.OpenTheory
