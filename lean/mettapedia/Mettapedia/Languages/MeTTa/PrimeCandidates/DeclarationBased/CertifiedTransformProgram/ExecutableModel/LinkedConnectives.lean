import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedProofs
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.IntuitionisticImport
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.PublishedTheorems
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Models
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.FalsumConservativity
import Mettapedia.Logic.HOL.ProofSyntaxModuloKripke
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.HOLReadingConnectives

/-!
# Linked proofs with the derived connectives

The object package reads the connectives `⊤ ⊥ ∧ ∨ ¬ ∃` of the set profile
through their impredicative definitions. The codes are the ones of the
propositional import and of the consistency theorem: `⊥` is `botCode`, and
`∧`, `∨` are `andCode`, `orCode` (`setReading_botCode`, `setReading_andCode`,
`setReading_orCode`).

**A linked theorem with an existential and a conjunction.** The retained proof
of `∀n. ∃m. add zero n = m ∧ m = n` from `zero-add` and reflexivity
(`witnessProof`) is elaborated and compiled against the linked `zero-add` proof
and the realization of reflexivity. The result is a closed term of the object
package at the decoding of the code of the elaborated statement
(`witnessTerm_typedO`); it is strongly normalizing (`witnessTerm_sn`), and the
package does not refute the statement (`witness_not_refuted`).

**The declared signature.** The constants the object package declares form a
signature (`ObjectConst`) that it reads in full (`objectReading_total`), as the
set reading reads them (`setReading_term_mapConst`). Every retained proof of
the connective fragment over it compiles once elaborated, to a term of the
object package at the decoding of the code of its expanded conclusion
(`object_compiles_typed`); closed theorems give closed, strongly normalizing
terms (`object_closed_compiles_sn`). The other constants of the set profile
are not declared by the package and stay unread.

**Eliminations.** The retained proof of
`∀P Q. (∃x. P x ∧ Q x) → (∃x. P x) ∧ (∃x. Q x)` (`splitProof`) uses the
elimination rules of `∃` and `∧`; its elaboration compiles to a closed,
strongly normalizing term of the object package (`split_compiles_typed`).

**Controls.**

* The reader still declines the connectives themselves, and the retained
  proof is not a proof of the checker's calculus (`witnessStatement_not_read`,
  `witnessProof_not_checker`): the connectives are accepted only through the
  elaboration.
* The elaboration does not produce extensionality: η and propositional
  extensionality are outside its domain (`etaProof_not_elaborated`,
  `propextProof_not_elaborated`).
* A wrong witness statement has no proof modulo the equations from the
  elaborated facts (`wrongWitness_not_derivable`), hence no retained proof in
  the connective fragment (`wrongWitness_not_retained`): the elaboration keeps
  meaning, and the statement fails in the numbers. With `Falsum` defined it has
  no proof either (`wrongWitness_not_derivable_defined`), by the conservativity
  of the definition.
* The encodings stay intuitionistic. The elaborated excluded middle
  `∀p. p ∨ ¬p` has no proof modulo the equations from the published facts,
  induction included (`em_not_derivable`, in a two-world Kripke model of the
  profile), hence no retained proof in the connective fragment
  (`em_not_retained`); with `Falsum` defined, none either
  (`em_not_derivable_defined`). Its double negation has one, and it compiles to a
  closed, strongly normalizing term of the object package
  (`dnem_compiles_typed`).

## `⊥` and the defined `Falsum`

The elaborated `⊥` is `∀p. p`, read as `botCode`, the code for which the
package is proved consistent (`consistent_bot`). Its elimination rule is
application to a code (`botElimO`): it reaches every decoded code, and through
the identity reading the identity types at carriers (`botElim_id`). Nothing
here eliminates it into other types.

The signature's constant `Falsum` is not the connective `⊥`: the elaboration
leaves it alone (`expandInline_falsum`). The signature defines
`Falsum := ∀p. p` (`SetProfile.falsumEquation`), and the checker keeps `Falsum`
a named constant whose definition is a computation rule:

* the object package declares no constant for `Falsum`, so the set reading
  does not read it (`falsum_not_read`) and does not realize its definition
  (`falsumEquation_not_realized`). Without the definition, `Falsum → ⊥` has no
  proof modulo the equations of `add` and `pow` (`falsum_not_bot`, in the
  numbers with `Falsum` read as true);
* the package with the definition publishes `Falsum` by name
  (`definedRules`), and the reading with the definition reads `Falsum` as that
  constant (`falsum_read`). The definition is realized by its δ-step
  (`falsumEquation_realized`), one definitional step identifies `Falsum` with
  the elaborated `⊥` (`falsum_converts`), and `Falsum → ∀p. p` has a proof
  (`falsumElim`);
* **ex falso, linked.** For every formula `φ` the reading with the definition
  reads, the proof of `Falsum → φ` through the definition compiles to a closed,
  strongly normalizing term of the package with the definition, at the
  decoding of `Falsum ⇒ φ` (`exFalso_compiles_typed`). The elaboration of
  `Falsum → ψ` is `Falsum → ψ'`, with `ψ'` the elaboration of `ψ`
  (`expandInline_falsumImp`);
* **consistency.** No closed term of the package with the definition proves
  `Falsum` (`falsum_unprovable`), so no proof of `Falsum` from published facts
  links (`falsum_not_linked`);
* adopting the definition is not conservative over the equations of `add` and
  `pow`: a formula that mentions `Falsum` gains a proof
  (`old_formula_gains_a_proof`, `falsum_revision_not_conservative`). The
  definition revises the meaning of an existing constant; it is not a fresh
  definitional extension. For formulas that do not mention `Falsum` it is
  conservative (`SetProfile.falsum_definition_conservative`), and a core formula
  has a proof with the definition exactly when its unfolding has one without it
  (`SetProfile.falsum_definition_unfolds`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open Mettapedia.Logic.HOL.ImpredicativeConnectives
open SetProfile (SetBase SetConst numTy zeroT sucT addT)
open SetProfile.Models (naturals naturals_lawful emptyValuation emptyValuation_admissible)
open IdentityEquality.Translation (linkedZeroAdd)
open IdentityEquality.Realizations (reflRealization)

namespace CodeModel

/-! ## The codes of the connectives -/

theorem setReading_botCode {n : Nat} : (setReading.botCode : Tower.Tm n) = botCode := rfl

theorem setReading_andCode {n : Nat} (p q : Tower.Tm n) : setReading.andCode p q = andCode p q :=
  rfl

theorem setReading_orCode {n : Nat} (p q : Tower.Tm n) : setReading.orCode p q = orCode p q :=
  rfl

/-- The elaborated `⊥` is the bottom code of the consistency theorem. -/
theorem setReading_term_bot {Γ : HOL.Ctx SetBase} :
    setReading.term (expandInline (.bot : HOL.Formula SetConst Γ)) = some botCode :=
  rfl

/-! ## A theorem with an existential and a conjunction -/

/-- `∀n. ∃m. add zero n = m ∧ m = n`. -/
def witnessStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.ex (σ := numTy)
    (.and (.eq (addT zeroT (.var (.vs .vz))) (.var .vz)) (.eq (.var .vz) (.var (.vs .vz)))))

/-- The facts it uses: `zero-add` and reflexivity at the numbers. -/
def witnessAssumptions : List (HOL.Formula SetConst []) :=
  [SetProfile.zeroAddStatement, SetProfile.reflAxiom]

/-- The retained proof: for `n`, the witness `n`, with `add zero n = n` by
`zero-add` and `n = n` by reflexivity. -/
def witnessProof : HOL.ProofSyntax SetConst witnessAssumptions witnessStatement :=
  .allI (.exI (.var .vz) (.andI
    (.allE (φ := .eq (addT zeroT (.var .vz)) (.var .vz)) (.var .vz) (.hyp ⟨0, by decide⟩))
    (.allE (φ := .eq (.var .vz) (.var .vz)) (.var .vz) (.hyp ⟨1, by decide⟩))))

/-- Its elaboration. -/
def witnessExpanded : HOL.ProofSyntaxModulo SetProfile.sourceEquations
    (witnessAssumptions.map expandInline) (expandInline witnessStatement) :=
  (expandProofModulo? witnessProof).get rfl

theorem witnessProof_expands :
    expandProofModulo? (eqs := SetProfile.sourceEquations) witnessProof = some witnessExpanded :=
  rfl

/-- The code of the elaborated statement:
`∀n. ∃m. eq (add zero n) m ∧ eq m n` with the codes of `∃` and `∧`. -/
def witnessCode : Tower.Tm 0 :=
  setReading.allOf numTy (.lam (setReading.exCode numTy
    (andCode (setReading.eqOf numTy (SetProfile.addNative SetProfile.zeroNative (.var 1)) (.var 0))
      (setReading.eqOf numTy (.var 0) (.var 1)))))

theorem witnessStatement_read :
    setReading.term (expandInline witnessStatement) = some witnessCode :=
  rfl

/-- The realizations of the facts: the linked `zero-add` proof and `λx. refl x`. -/
def witnessRealizations : Fin (witnessAssumptions.map expandInline).length → Tower.Tm 0 :=
  ![linkedZeroAdd, reflRealization]

/-- The linked term: for `n`, the witness `n` packed with the pair of
`zero-add n` and `refl n`. -/
def witnessTerm : Tower.Tm 0 :=
  .lam (.app (.lam (.lam (.lam (.app (.app (.var 0) (.var 3)) (.var 2)))))
    (.app (.app pairProof (.app (Presentation.rename wk linkedZeroAdd) (.var 0)))
      (.app (Presentation.rename wk reflRealization) (.var 0))))

/-- The reading compiles the elaborated proof, against the realizations, to the
linked term. -/
theorem witness_compiled :
    setReading.compile witnessExpanded Fin.elim0 witnessRealizations = some witnessTerm :=
  rfl

theorem witnessRealizations_typed (i : Fin (witnessAssumptions.map expandInline).length) :
    ∃ c, setReading.term ((witnessAssumptions.map expandInline).get i) = some c ∧
      Typed setReading.rules .nil (witnessRealizations i)
        (setReading.holdsOf (Presentation.subst (Fin.elim0 : Sub Tower.Head 0 0) c)) := by
  match i with
  | ⟨0, _⟩ =>
      exact ⟨SetProfile.zeroAddCode, rfl, by
        rw [SetProfile.subst_elim0]
        exact linkedZeroAdd_typedO⟩
  | ⟨1, _⟩ =>
      exact ⟨_, rfl, by
        rw [SetProfile.subst_elim0]
        exact reflRealization_typedO numTy⟩
  | ⟨k + 2, h⟩ => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 2 k))

/-- **The linked theorem is a term of the object package** at the decoding of
the code of `∀n. ∃m. add zero n = m ∧ m = n`. -/
theorem witnessTerm_typedO :
    Typed objectRules .nil witnessTerm (programCodes.holdsOf witnessCode) := by
  obtain ⟨code, read, typed⟩ := setReading_laws.expandProofModulo?_typed witnessProof_expands
    (fun i => Fin.elim0 i) witnessRealizations_typed witness_compiled
  rw [witnessStatement_read] at read
  cases read
  rw [SetProfile.subst_elim0] at typed
  exact typed

/-- The linked theorem is strongly normalizing under the package's reduction. -/
theorem witnessTerm_sn : StrongNormalization.SN objectRules witnessTerm :=
  (objectRules_sn .nil witnessTerm_typedO).1

/-- **Consistency coverage.** No closed term of the object package proves
`(∀n. ∃m. add zero n = m ∧ m = n) ⇒ ⊥`. -/
theorem witness_not_refuted (f : Tower.Tm 0) :
    ¬ Typed objectRules .nil f (programCodes.holdsOf (programCodes.impOf witnessCode botCode)) :=
  fun refutation => consistent_bot (.app f witnessTerm) (setReading_laws.impElim
    (setReading_laws.term_typed witnessStatement_read) botCode_typed refutation witnessTerm_typedO)

/-! ## Eliminations: splitting an existential conjunction -/

/-- `P x` for the predicate variable `P : num → prop` and the numeral variable `x`. -/
abbrev splitLeft : HOL.Formula SetConst [numTy, .arr numTy .prop, .arr numTy .prop] :=
  .app (.var (.vs (.vs .vz))) (.var .vz)

/-- `Q x` for the predicate variable `Q : num → prop`. -/
abbrev splitRight : HOL.Formula SetConst [numTy, .arr numTy .prop, .arr numTy .prop] :=
  .app (.var (.vs .vz)) (.var .vz)

/-- `∀P Q. (∃x. P x ∧ Q x) → (∃x. P x) ∧ (∃x. Q x)`. -/
def splitStatement : HOL.Formula SetConst [] :=
  .all (σ := .arr numTy .prop) (.all (σ := .arr numTy .prop)
    (.imp (.ex (.and splitLeft splitRight)) (.and (.ex splitLeft) (.ex splitRight))))

/-- The retained proof: unpack the witness, project both halves, pack twice. -/
def splitProof : HOL.ProofSyntax SetConst [] splitStatement :=
  .allI (.allI (ProofControls.splitExistential splitLeft splitRight))

def splitExpanded : HOL.ProofSyntaxModulo SetProfile.sourceEquations []
    (expandInline splitStatement) :=
  (expandProofModulo? splitProof).get rfl

theorem splitProof_expands :
    expandProofModulo? (eqs := SetProfile.sourceEquations) splitProof = some splitExpanded :=
  rfl

/-- **The eliminations compile.** The elaborated proof compiles to a closed
term of the object package at the decoding of the code of the elaborated
statement, and that term is strongly normalizing. -/
theorem split_compiles_typed :
    ∃ t code, setReading.compile splitExpanded Fin.elim0 Fin.elim0 = some t ∧
      setReading.term (expandInline splitStatement) = some code ∧
      Typed objectRules .nil t (programCodes.holdsOf code) ∧
      StrongNormalization.SN objectRules t := by
  obtain ⟨t, compiled⟩ : ∃ t, setReading.compile splitExpanded Fin.elim0 Fin.elim0 = some t :=
    ⟨_, rfl⟩
  obtain ⟨code, read, typed⟩ := setReading_laws.expandProofModulo?_typed splitProof_expands
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) compiled
  rw [SetProfile.subst_elim0] at typed
  exact ⟨t, code, compiled, read, typed, (objectRules_sn .nil typed).1⟩

/-! ## The declared signature, read in full -/

/-- The constants of the set profile that the object package declares. -/
inductive ObjectConst : HOL.Ty SetBase → Type
  | zero : ObjectConst numTy
  | suc : ObjectConst (.arr numTy numTy)
  | add : ObjectConst (.arr numTy (.arr numTy numTy))
  | power : ObjectConst (.arr SetProfile.setTy SetProfile.setTy)
  | pow : ObjectConst (.arr numTy (.arr SetProfile.setTy SetProfile.setTy))

/-- Each declared constant is a constant of the set profile. -/
def ObjectConst.toSet : {τ : HOL.Ty SetBase} → ObjectConst τ → SetConst τ
  | _, .zero => .zero
  | _, .suc => .suc
  | _, .add => .add
  | _, .power => .power
  | _, .pow => .pow

/-- The declared signature read in the object package, each constant as the
set reading reads it. -/
def objectReading : HOLReading Tower.Head SetBase ObjectConst where
  codes := programCodes
  base := rules
  sort := fun b => .const (SetProfile.baseName b)
  constant := fun c => setConstant c.toSet
  allName := SetProfile.allName
  eqName := SetProfile.eqName

theorem objectReading_rules : objectReading.rules = objectRules := rfl

/-- The object reading interprets every constant of its signature. -/
theorem objectReading_total : objectReading.Total := by
  intro τ c
  cases c <;> rfl

theorem objectReading_carrierAt {n : Nat} (τ : HOL.Ty SetBase) :
    objectReading.carrierAt n τ = setReading.carrierAt n τ := by
  induction τ generalizing n with
  | prop | base => rfl
  | arr a b ia ib => simp only [HOLReading.carrierAt, ia, ib]

theorem objectReading_laws : objectReading.Laws where
  quantifier τ := by
    rw [HOLReading.carrier, objectReading_carrierAt]
    exact setReading_laws.quantifier τ
  equation τ := by
    rw [HOLReading.carrier, objectReading_carrierAt]
    exact setReading_laws.equation τ
  allName_apart := setReading_laws.allName_apart
  eqName_apart := setReading_laws.eqName_apart
  imp_apart := setReading_laws.imp_apart
  holds_apart := setReading_laws.holds_apart
  proofs_universe := setReading_laws.proofs_universe
  proofs_typed := setReading_laws.proofs_typed
  proofs_pi := setReading_laws.proofs_pi
  holds_formed := setReading_laws.holds_formed
  sort_typed := setReading_laws.sort_typed
  const_typed c t found := by
    rw [HOLReading.carrier, objectReading_carrierAt]
    exact setReading_laws.const_typed c.toSet found

/-- The object reading is the set reading on the declared constants. -/
theorem setReading_term_mapConst {Γ : HOL.Ctx SetBase} {τ : HOL.Ty SetBase}
    (t : HOL.Term ObjectConst Γ τ) :
    setReading.term (HOL.mapConst ObjectConst.toSet t) = objectReading.term t := by
  induction t with
  | var | const | top | bot | and | or | not | ex => rfl
  | app _ _ ihf iha => simp only [HOL.mapConst, HOLReading.term, ihf, iha]
  | imp _ _ ihf iha | eq _ _ ihf iha =>
      simp only [HOL.mapConst, HOLReading.term, ihf, iha]
      rfl
  | lam _ ih => simp only [HOL.mapConst, HOLReading.term, ih]
  | all _ ih =>
      simp only [HOL.mapConst, HOLReading.term, ih]
      rfl

/-- **Compile totality in the object package.** Every retained proof of the
connective fragment over the declared constants compiles once elaborated, and
its compilation is a term of the object package at the decoding of the code of
the expanded conclusion. -/
theorem object_compiles_typed {eqs : List (HOL.DefiningEquation ObjectConst)}
    {Γ : HOL.Ctx SetBase} {Δ : List (HOL.Formula ObjectConst Γ)}
    {φ : HOL.Formula ObjectConst Γ}
    {proof : HOL.ProofSyntax ObjectConst Δ φ}
    {d : HOL.ProofSyntaxModulo eqs (Δ.map expandInline) (expandInline φ)}
    (expanded : expandProofModulo? proof = some d) {n : Nat} {target : Tower.Ctx n}
    {objects : Sub Tower.Head Γ.length n} {hyps : Fin (Δ.map expandInline).length → Tower.Tm n}
    (objectsTyped : SubstMor objectRules (objectReading.objCtx Γ) target objects)
    (hypsTyped : ∀ i, ∃ c, objectReading.term ((Δ.map expandInline).get i) = some c ∧
      Typed objectRules target (hyps i) (programCodes.holdsOf (Presentation.subst objects c))) :
    ∃ out, objectReading.compile d objects hyps = some out ∧
      ∃ code, objectReading.term (expandInline φ) = some code ∧
        Typed objectRules target out (programCodes.holdsOf (Presentation.subst objects code)) :=
  objectReading_laws.expandProofModulo?_compiles_typed objectReading_total expanded objectsTyped
    hypsTyped

/-- **Closed theorems** over the declared constants compile to closed, strongly
normalizing terms of the object package. -/
theorem object_closed_compiles_sn {eqs : List (HOL.DefiningEquation ObjectConst)}
    {φ : HOL.Formula ObjectConst []} {proof : HOL.ProofSyntax ObjectConst [] φ}
    {d : HOL.ProofSyntaxModulo eqs [] (expandInline φ)}
    (expanded : expandProofModulo? proof = some d) :
    ∃ out code, objectReading.compile d Fin.elim0 Fin.elim0 = some out ∧
      objectReading.term (expandInline φ) = some code ∧
      Typed objectRules .nil out (programCodes.holdsOf code) ∧
      StrongNormalization.SN objectRules out := by
  obtain ⟨out, compiled, code, read, typed⟩ :=
    object_compiles_typed expanded (target := .nil) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rw [SetProfile.subst_elim0] at typed
  exact ⟨out, code, compiled, read, typed, (objectRules_sn .nil typed).1⟩

/-! ## Controls -/

/-- The reader declines the connectives themselves. -/
theorem witnessStatement_not_read : setReading.term witnessStatement = none := rfl

/-- The retained proof is not a proof of the checker's calculus: its
connective rules have no counterpart there. -/
theorem witnessProof_not_checker :
    HOL.ProofSyntaxModulo.ofProofSyntax? (equations := SetProfile.sourceEquations) witnessProof =
      none :=
  rfl

/-- η at `num → num`: `∀f. (λx. f x) = f`. -/
def etaStatement : HOL.Formula SetConst [] :=
  .all (σ := .arr numTy numTy) (.eq (.lam (.app (HOL.weaken (.var .vz)) (.var .vz))) (.var .vz))

def etaProof : HOL.ProofSyntax SetConst [] etaStatement := .allI (.eta (.var .vz))

/-- The elaboration does not produce η. -/
theorem etaProof_not_elaborated :
    expandProofModulo? (eqs := SetProfile.sourceEquations) etaProof = none :=
  rfl

/-- Propositional extensionality: `∀p q. (p → q) → (q → p) → p = q`. -/
def propextStatement : HOL.Formula SetConst [] :=
  .all (σ := .prop) (.all (σ := .prop) (.imp (.imp (.var (.vs .vz)) (.var .vz))
    (.imp (.imp (.var .vz) (.var (.vs .vz))) (.eq (.var (.vs .vz)) (.var .vz)))))

def propextProof : HOL.ProofSyntax SetConst [] propextStatement :=
  .allI (.allI (.impI (.impI (.eqPropI (.hyp ⟨1, by decide⟩) (.hyp ⟨0, by decide⟩)))))

/-- The elaboration does not produce propositional extensionality. -/
theorem propextProof_not_elaborated :
    expandProofModulo? (eqs := SetProfile.sourceEquations) propextProof = none :=
  rfl

/-- `∀n. ∃m. add zero n = m ∧ m = suc n`, a wrong witness statement. -/
def wrongWitnessStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.ex (σ := numTy)
    (.and (.eq (addT zeroT (.var (.vs .vz))) (.var .vz)) (.eq (.var .vz) (sucT (.var (.vs .vz))))))

/-- **Wrong witness.** No proof modulo the equations, from the elaborated
facts, proves the elaborated wrong statement. -/
theorem wrongWitness_not_derivable :
    ¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations
      (witnessAssumptions.map expandInline) (expandInline wrongWitnessStatement)) := by
  rintro ⟨proof⟩
  have facts : ∀ fact ∈ witnessAssumptions.map expandInline,
      (HOL.HenkinModel.denote naturals.model fact (emptyValuation naturals.model)).down := by
    intro fact listed
    obtain ⟨δ, mem, rfl⟩ := List.mem_map.mp listed
    rw [denote_expandInline]
    simp only [witnessAssumptions, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact SetProfile.Models.zeroAdd_holds
    · exact SetProfile.Models.refl_holds naturals
  have holds := SetProfile.Models.proof_sound naturals proof
    (SetProfile.Models.equationsHold naturals_lawful) facts
  rw [denote_expandInline] at holds
  obtain ⟨m, _, first, second⟩ := holds ⟨0⟩ trivial
  have atZero : (⟨0 + 0⟩ : ULift.{1} ℕ) = ⟨0 + 1⟩ := Eq.trans first second
  exact absurd (congrArg ULift.down atZero) (by decide)

/-- **Wrong witness, with `Falsum` defined.** Neither the facts nor the statement
mention `Falsum`, so the definition adds no proof of it
(`SetProfile.falsum_definition_conservative`). -/
theorem wrongWitness_not_derivable_defined :
    ¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations
      (witnessAssumptions.map expandInline) (expandInline wrongWitnessStatement)) :=
  fun proof => wrongWitness_not_derivable ((SetProfile.falsum_definition_conservative
    (SetProfile.noFalsumHyps (by decide)) (SetProfile.noFalsum (by decide))).mp proof)

/-- Hence no retained proof of the connective fragment proves it either. -/
theorem wrongWitness_not_retained (proof : HOL.ProofSyntax SetConst witnessAssumptions
    wrongWitnessStatement) : connectiveFragment proof = false := by
  cases fragment : connectiveFragment proof
  · rfl
  · exact absurd (expandProofModulo?_derivable (eqs := SetProfile.sourceEquations) proof fragment)
      wrongWitness_not_derivable

/-! ## Excluded middle -/

/-- `∀p. p ∨ ¬p`. -/
def emStatement : HOL.Formula SetConst [] :=
  .all (σ := .prop) (.or (.var .vz) (.not (.var .vz)))

/-- `∀p. ¬¬(p ∨ ¬p)`. -/
def dnemStatement : HOL.Formula SetConst [] :=
  .all (σ := .prop) (.not (.not (.or (.var .vz) (.not (.var .vz)))))

/-- The intuitionistic proof of `¬¬(p ∨ ¬p)`. -/
def dnemProof : HOL.ProofSyntax SetConst [] dnemStatement :=
  .allI (.notI (.notE (.hyp ⟨0, by decide⟩)
    (.orIR (.notI (.notE (.hyp ⟨1, by decide⟩) (.orIL (.hyp ⟨0, by decide⟩)))))))

def dnemExpanded : HOL.ProofSyntaxModulo SetProfile.sourceEquations []
    (expandInline dnemStatement) :=
  (expandProofModulo? dnemProof).get rfl

theorem dnemProof_expands :
    expandProofModulo? (eqs := SetProfile.sourceEquations) dnemProof = some dnemExpanded :=
  rfl

/-- **Positive twin.** The double negation of excluded middle compiles to a
closed, strongly normalizing term of the object package. -/
theorem dnem_compiles_typed :
    ∃ t code, setReading.compile dnemExpanded Fin.elim0 Fin.elim0 = some t ∧
      setReading.term (expandInline dnemStatement) = some code ∧
      Typed objectRules .nil t (programCodes.holdsOf code) ∧
      StrongNormalization.SN objectRules t := by
  obtain ⟨t, compiled⟩ : ∃ t, setReading.compile dnemExpanded Fin.elim0 Fin.elim0 = some t :=
    ⟨_, rfl⟩
  obtain ⟨code, read, typed⟩ := setReading_laws.expandProofModulo?_typed dnemProof_expands
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) compiled
  rw [SetProfile.subst_elim0] at typed
  exact ⟨t, code, compiled, read, typed, (objectRules_sn .nil typed).1⟩

section Countermodel

open HOL.KripkeModulo

/-- Two worlds: the root (`false`) sees the leaf (`true`). -/
def emFrame : Frame where
  World := Bool
  le w v := w = false ∨ v = true
  le_refl w := match w with
    | false => .inl rfl
    | true => .inr rfl
  le_trans {u v w} huv hvw := by
    rcases huv with hu | hv
    · exact .inl hu
    · rcases hvw with hv' | hw
      · exact nomatch hv.symm.trans hv'
      · exact .inr hw

/-- The proposition true at the leaf only. -/
def leafUp : emFrame.Up :=
  ⟨fun w => w = true, fun {w v} hwv hw => by
    rcases hwv with hw' | hv
    · exact nomatch hw.symm.trans hw'
    · exact hv⟩

/-- Numbers for `num`, a point for `set`. -/
def emCarrier : SetBase → Type
  | .set => PUnit
  | .num => ℕ

/-- The constants of the set profile: the numbers with their addition, sets
by a point. -/
def emConstants : {τ : HOL.Ty SetBase} → SetConst τ → Den emFrame emCarrier τ
  | _, .falsum => emFrame.constUp False
  | _, .member => fun _ _ => emFrame.constUp True
  | _, .empty => PUnit.unit
  | _, .union => id
  | _, .power => id
  | _, .separation => fun set _ => set
  | _, .replacement => fun set _ => set
  | _, .epsilon => fun _ => PUnit.unit
  | _, .universeOf => id
  | _, .zero => (0 : ℕ)
  | _, .suc => Nat.succ
  | _, .add => Nat.add
  | _, .pow => fun _ set => set

/-- A two-world Kripke model of the set profile. -/
def emModel : Model SetBase SetConst where
  frame := emFrame
  Carrier := emCarrier
  constDen := emConstants

def emValuation : emModel.Valuation [] := fun i => nomatch i

theorem emModel_equationsHold : emModel.EquationsHold SetProfile.sourceEquations := by
  intro equation listed ρ
  simp only [SetProfile.sourceEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl <;> rfl

/-- The published facts, induction included, hold at every world. -/
theorem emModel_facts (w : Bool) :
    ∀ fact ∈ SetProfile.zeroAddAssumptions.map expandInline,
      (emModel.denote fact emValuation).holds w := by
  intro fact listed
  obtain ⟨δ, mem, rfl⟩ := List.mem_map.mp listed
  simp only [SetProfile.zeroAddAssumptions, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · intro P v _ base u hvu step x
    induction x with
    | zero => exact (P _).mono hvu base
    | succ n ih => exact step n u (emFrame.le_refl u) ih
  · intro a
    rfl
  · intro P a b v _ same u _ holds
    cases same
    exact holds

/-- **Excluded middle is not produced.** No proof modulo the equations, from
the published facts, proves the elaborated `∀p. p ∨ ¬p`. -/
theorem em_not_derivable :
    ¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations
      (SetProfile.zeroAddAssumptions.map expandInline) (expandInline emStatement)) := by
  rintro ⟨proof⟩
  have holds := emModel.proofSyntaxModulo_sound emModel_equationsHold proof emValuation false
    (emModel_facts false)
  have atRoot : leafUp.holds false :=
    holds leafUp leafUp false (.inl rfl) (fun _ _ h => h) false (.inl rfl)
      (fun _ _ negated => (negated true (.inr rfl) rfl (emFrame.constUp False)).elim)
  exact Bool.false_ne_true atRoot

end Countermodel

/-- **Excluded middle is not produced, with `Falsum` defined.** Neither the
published facts nor `∀p. p ∨ ¬p` mention `Falsum`
(`SetProfile.falsum_definition_conservative`). -/
theorem em_not_derivable_defined :
    ¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations
      (SetProfile.zeroAddAssumptions.map expandInline) (expandInline emStatement)) :=
  fun proof => em_not_derivable ((SetProfile.falsum_definition_conservative
    (SetProfile.noFalsumHyps (by decide)) (SetProfile.noFalsum (by decide))).mp proof)

/-- Hence no retained proof of the connective fragment proves excluded middle
from the published facts. -/
theorem em_not_retained (proof : HOL.ProofSyntax SetConst SetProfile.zeroAddAssumptions
    emStatement) : connectiveFragment proof = false := by
  cases fragment : connectiveFragment proof
  · rfl
  · exact absurd (expandProofModulo?_derivable (eqs := SetProfile.sourceEquations) proof fragment)
      em_not_derivable

/-! ## `⊥` and the signature's `Falsum` -/

/-- Elimination of `⊥` at an equation code: under the identity reading it
reaches the identity type at a carrier. -/
theorem botElim_id {n : Nat} {Γ : Tower.Ctx n} {τ : HOL.Ty SetBase} {z x y : Tower.Tm n}
    (hz : Typed objectRules Γ z (programCodes.holdsOf botCode))
    (hx : Typed objectRules Γ x (setReading.carrierAt n τ))
    (hy : Typed objectRules Γ y (setReading.carrierAt n τ)) :
    Typed objectRules Γ (.app z (setReading.eqOf τ x y)) (.id (setReading.carrierAt n τ) x y) :=
  .conv (botElimO hz (setReading_laws.eqOf_typed hx hy)) (setReading_laws.equal_holds_eq hx hy)
    setReading_laws.proofs_universe

/-- The elaboration leaves the signature's `Falsum` alone. -/
theorem expandInline_falsum {Γ : HOL.Ctx SetBase} :
    expandInline (.const .falsum : HOL.Formula SetConst Γ) = .const .falsum :=
  rfl

/-- The object package does not read `Falsum`. -/
theorem falsum_not_read {Γ : HOL.Ctx SetBase} :
    setReading.term (.const .falsum : HOL.Formula SetConst Γ) = none :=
  rfl

/-- The reading with the definition reads `Falsum` by its name. -/
theorem falsum_read {Γ : HOL.Ctx SetBase} :
    definedReading.term (.const .falsum : HOL.Formula SetConst Γ) = some (.const falsumN) :=
  rfl

/-- The constants of the numbers, with `Falsum` read as true. -/
def trueFalsumConstants : {τ : HOL.Ty SetBase} → SetConst τ →
    HOL.Ty.denote.{0, 0} naturals.carrier τ
  | _, .falsum => ULift.up True
  | _, .member => naturals.constDen .member
  | _, .empty => naturals.constDen .empty
  | _, .union => naturals.constDen .union
  | _, .power => naturals.constDen .power
  | _, .separation => naturals.constDen .separation
  | _, .replacement => naturals.constDen .replacement
  | _, .epsilon => naturals.constDen .epsilon
  | _, .universeOf => naturals.constDen .universeOf
  | _, .zero => naturals.constDen .zero
  | _, .suc => naturals.constDen .suc
  | _, .add => naturals.constDen .add
  | _, .pow => naturals.constDen .pow

/-- The numbers with `Falsum` read as true. -/
abbrev trueFalsumModel : HOL.HenkinModel.{0, 0, 0} SetBase SetConst :=
  HOL.HenkinModel.standard.{0, 0, 0} naturals.carrier trueFalsumConstants

theorem trueFalsum_equationsHold :
    HOL.Soundness.EquationsHold trueFalsumModel SetProfile.sourceEquations := by
  intro equation listed ρ
  simp only [SetProfile.sourceEquations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · exact naturals_lawful.add_zero (ρ .vz)
  · exact naturals_lawful.add_suc (ρ (.vs .vz)) (ρ .vz)
  · exact naturals_lawful.pow_zero (ρ .vz)
  · exact naturals_lawful.pow_suc (ρ (.vs .vz)) (ρ .vz)

/-- `Falsum → ⊥`, with `⊥` elaborated. -/
def falsumImpBot : HOL.Formula SetConst [] := .imp (.const .falsum) (expandInline .bot)

/-- **Without the definition, `Falsum` and `⊥` are apart**: `Falsum → ∀p. p` has
no proof modulo the equations of `add` and `pow`. -/
theorem falsum_not_bot :
    ¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations [] falsumImpBot) := by
  rintro ⟨proof⟩
  have holds := HOL.Soundness.proofSyntaxModulo_sound proof trueFalsum_equationsHold
    (emptyValuation_admissible trueFalsumModel) (fun _ listed => absurd listed List.not_mem_nil)
  exact holds trivial (.up False) trivial

/-- **With the definition, one step identifies them.** -/
theorem falsum_converts :
    HOL.CoreConversion SetProfile.definedEquations
      (.const .falsum : HOL.Formula SetConst []) (expandInline .bot) :=
  .rel _ _ ⟨rfl, rfl, HOL.SourceStep.delta (Γ := []) SetProfile.falsumEquation
    SetProfile.falsumEquation_mem (fun i => nomatch i) (fun i => nomatch i)⟩

/-- `Falsum → ∀p. p`, through the definition. -/
def falsumElim : HOL.ProofSyntaxModulo SetProfile.definedEquations [] falsumImpBot :=
  .impI (.convert falsum_converts (.hyp ⟨0, by decide⟩))

/-- **The definition is realized by its δ-step** in the package with the
definition. -/
theorem falsumEquation_realized : definedReading.Realizes [SetProfile.falsumEquation] := by
  intro equation listed
  rw [List.mem_singleton] at listed
  subst listed
  exact definedReading_realizes _ SetProfile.falsumEquation_mem

/-- The set reading does not realize the definition: it does not read
`Falsum`. -/
theorem falsumEquation_not_realized : ¬ setReading.Realizes [SetProfile.falsumEquation] := by
  intro realized
  obtain ⟨l, r, read, _, _⟩ := realized SetProfile.falsumEquation (List.Mem.head _)
  cases read

/-! ### Ex falso, linked -/

/-- The elaboration of `Falsum → ψ` is `Falsum → ψ'`, with `ψ'` the elaboration
of `ψ`. -/
theorem expandInline_falsumImp (ψ : HOL.Formula SetConst []) :
    expandInline (.imp (.const .falsum) ψ) = .imp (.const .falsum) (expandInline ψ) :=
  rfl

/-- Ex falso through the definition: from `Falsum`, the definition gives
`∀p. p`, instantiated at `φ`. -/
def exFalsoProof (φ : HOL.Formula SetConst []) :
    HOL.ProofSyntaxModulo SetProfile.definedEquations [] (.imp (.const .falsum) φ) :=
  .impI (.allE φ (.convert falsum_converts (.hyp ⟨0, by decide⟩)))

/-- Its only conversion article, the definition of `Falsum`, is between read
terms. -/
theorem exFalso_articles (φ : HOL.Formula SetConst []) :
    definedReading.ArticlesRead SetProfile.definedEquations (exFalsoProof φ) :=
  .impI (.allE _ (.convert (.rel _ _ ⟨rfl, rfl, .delta (Γ := []) SetProfile.falsumEquation
    SetProfile.falsumEquation_mem (fun i => nomatch i) (fun i => nomatch i)⟩) (.hyp _)))

/-- The linked term of ex falso at a formula read as `c`: `λh. h c`. -/
theorem exFalso_compiled (φ : HOL.Formula SetConst []) {c : Tower.Tm 0}
    (read : definedReading.term φ = some c) :
    definedReading.compile (exFalsoProof φ) Fin.elim0 Fin.elim0 =
      some (.lam (.app (.var 0)
        (Presentation.subst (fun i => Presentation.rename wk (Fin.elim0 i : Tower.Tm 0)) c))) := by
  simp only [exFalsoProof, HOLReading.compile, read]
  rfl

/-- **Ex falso, linked.** For every formula `φ` the reading with the definition
reads, the proof of `Falsum → φ` through the definition compiles to a closed
term of the package with the definition, at the decoding of `Falsum ⇒ φ`, and
that term is strongly normalizing. -/
theorem exFalso_compiles_typed (φ : HOL.Formula SetConst []) {c : Tower.Tm 0}
    (read : definedReading.term φ = some c) :
    ∃ t, definedReading.compile (exFalsoProof φ) Fin.elim0 Fin.elim0 = some t ∧
      Typed definedRules .nil t (programCodes.holdsOf (programCodes.impOf (.const falsumN) c)) ∧
      StrongNormalization.SN definedRules t := by
  obtain ⟨code, statementRead, typed⟩ := definedReading_laws.compile_typed
    definedReading_realizes (exFalso_articles φ) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (exFalso_compiled φ read)
  have code_eq : code = programCodes.impOf (.const falsumN) c := by
    have direct : definedReading.term (.imp (.const .falsum) φ : HOL.Formula SetConst []) =
        some (programCodes.impOf (.const falsumN) c) := by
      simp only [HOLReading.term, read]
      rfl
    rw [direct] at statementRead
    exact (Option.some.inj statementRead).symm
  subst code_eq
  rw [SetProfile.subst_elim0, definedReading_rules] at typed
  exact ⟨_, exFalso_compiled φ read, typed,
    (objectRules_withTheorem_sn falsumN_fresh prop_isType botCode_typed .nil typed).1⟩

/-- **No closed term proves `Falsum`** in the package with the definition:
applied to the false code after the δ-step, it would prove
`∀n : num, zero = suc n` there. -/
theorem falsum_unprovable (t : Tower.Tm 0) :
    ¬ Typed definedRules .nil t (programCodes.holdsOf (.const falsumN)) := by
  intro proof
  rw [← definedReading_rules] at proof
  have atBot : Typed definedReading.rules .nil t (definedReading.holdsOf botCode) :=
    .conv proof (definedReading_laws.equal_holdsOf (definedReading_rules ▸ falsum_equal_bot))
      definedReading_laws.proofs_universe
  have atFalse := definedReading_laws.allElim (τ := .prop) (B := .var 0)
    (definedReading.var_carrier .prop) atBot (typed_defined falseCode_typed)
  rw [definedReading_rules] at atFalse
  exact objectRules_withTheorem_consistent falsumN_fresh prop_isType botCode_typed _ atFalse

/-- **No proof of `Falsum` links.** A proof of `Falsum` from published facts,
whose conversion articles stay inside the read terms, compiled against the
realizations, would be a closed term of the package with the definition at the
decoding of `Falsum`. -/
theorem falsum_not_linked {assumptions : List (HOL.Formula SetConst [])}
    {proof : HOL.ProofSyntaxModulo SetProfile.definedEquations assumptions (.const .falsum)}
    (articles : definedReading.ArticlesRead SetProfile.definedEquations proof)
    (published : ∀ i : Fin assumptions.length,
      IdentityEquality.Linking.Published (assumptions.get i)) {term : Tower.Tm 0}
    (compiled : definedReading.compile proof Fin.elim0 (fun i => (published i).realization) =
      some term) : False := by
  obtain ⟨code, read, typed⟩ := definedReading_laws.compile_typed definedReading_realizes
    articles (fun i => Fin.elim0 i)
    (fun i => by
      obtain ⟨c, hc, t⟩ := published_typedO (published i)
      exact ⟨c, definedReading_term_of_setReading hc,
        by rw [SetProfile.subst_elim0]; exact typed_defined t⟩)
    compiled
  rw [falsum_read] at read
  cases read
  rw [SetProfile.subst_elim0, definedReading_rules] at typed
  exact falsum_unprovable term typed

/-! ### The definition is not conservative -/

/-- A formula that mentions `Falsum` gains a proof: `Falsum → ∀p. p` has none
modulo the equations of `add` and `pow`, and one with the definition. -/
theorem old_formula_gains_a_proof :
    ¬ Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations [] falsumImpBot) ∧
      Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations [] falsumImpBot) :=
  ⟨falsum_not_bot, ⟨falsumElim⟩⟩

/-- **Adopting the definition is not conservative** over the equations of `add`
and `pow`: provability with the definition does not reflect to provability
without it. This says nothing against the consistency of the definition
(`falsum_unprovable`). -/
theorem falsum_revision_not_conservative :
    ¬ (∀ P : HOL.Formula SetConst [],
      Nonempty (HOL.ProofSyntaxModulo SetProfile.definedEquations [] P) →
      Nonempty (HOL.ProofSyntaxModulo SetProfile.sourceEquations [] P)) :=
  fun reflects => falsum_not_bot (reflects falsumImpBot ⟨falsumElim⟩)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
