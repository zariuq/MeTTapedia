import Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision

/-!
# Quantifier elimination for atomless Boolean algebras

The first-order decision procedure can be reified as an ordinary
quantifier-free Boolean-algebra formula.  For a formula with `n` free
variables, finite profile evaluation determines exactly which `n`-variable
Venn profiles satisfy it.  This module builds a disjunction of exact-profile
formulas for those accepted profiles.

The result is theory-relative in the necessary sense: equivalence holds in
every nontrivial atomless Boolean algebra.  A negative canary proves that the
same eliminated formula need not remain equivalent in the two-element
algebra, where the atomless extension property fails.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanQuantifierElimination

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanTermProfileBridge
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision

universe u v w

/-! ## Reifying cells as ordinary Boolean terms -/

/-- Rename every variable in a Boolean term. -/
def renameTerm {Var : Type v} {Var' : Type w} (rename : Var -> Var') :
    Term Var -> Term Var'
  | .atom name => .atom (rename name)
  | .bottom => .bottom
  | .top => .top
  | .meet left right => .meet (renameTerm rename left) (renameTerm rename right)
  | .join left right => .join (renameTerm rename left) (renameTerm rename right)
  | .complement body => .complement (renameTerm rename body)

theorem eval_renameTerm
    {Var : Type v} {Var' : Type w} {B : Type u} [BooleanAlgebra B]
    (rename : Var -> Var') (valuation : Var' -> B) (term : Term Var) :
    (renameTerm rename term).eval valuation =
      term.eval (fun name => valuation (rename name)) := by
  induction term with
  | atom name => rfl
  | bottom => rfl
  | top => rfl
  | meet left right leftIH rightIH =>
      simp only [renameTerm, Term.eval, leftIH, rightIH]
  | join left right leftIH rightIH =>
      simp only [renameTerm, Term.eval, leftIH, rightIH]
  | complement body bodyIH =>
      simp only [renameTerm, Term.eval, bodyIH]

/-- The ordinary Boolean term denoting one Venn cell. -/
def cellTerm : {arity : Nat} -> Cell arity -> Term (Fin arity)
  | 0, _cell => .top
  | _arity + 1, cell =>
      .meet
        (if cell 0 then .atom 0 else .complement (.atom 0))
        (renameTerm Fin.succ (cellTerm
          (Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.tailCell
            cell)))

/-- Reified cell terms have exactly the previously defined cell semantics. -/
theorem eval_cellTerm
    {B : Type u} [BooleanAlgebra B] :
    {arity : Nat} -> (cell : Cell arity) ->
      (valuation : Fin arity -> B) ->
      (cellTerm cell).eval valuation = cellValue valuation cell := by
  intro arity
  induction arity with
  | zero =>
      intro cell valuation
      rfl
  | succ arity inductionHypothesis =>
      intro cell valuation
      cases headValue : cell 0 <;>
        simp only [cellTerm, headValue, Bool.false_eq_true, reduceIte,
          Term.eval, eval_renameTerm, cellValue]
      · rw [inductionHypothesis
          (Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.tailCell
            cell)
          (fun index => valuation index.succ)]
        rfl
      · rw [inductionHypothesis
          (Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.tailCell
            cell)
          (fun index => valuation index.succ)]
        rfl

/-! ## Quantifier-free exact-profile formulas -/

/-- Syntactic quantifier-freeness for the ordinary source language. -/
def QuantifierFree : {arity : Nat} -> Formula arity -> Prop
  | _, .equation _claim => True
  | _, .falsum => True
  | _, .conjunction left right => QuantifierFree left /\ QuantifierFree right
  | _, .negation body => QuantifierFree body
  | _, .existsF _body => False

def truthFormula {arity : Nat} : Formula arity := .negation .falsum

def formulaConjoin {arity : Nat} : List (Formula arity) -> Formula arity
  | [] => truthFormula
  | formula :: formulas => .conjunction formula (formulaConjoin formulas)

theorem satisfies_formulaConjoin_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (formulas : List (Formula arity)) (valuation : Fin arity -> B) :
    Satisfies (formulaConjoin formulas) valuation <->
      forall formula, formula ∈ formulas -> Satisfies formula valuation := by
  induction formulas with
  | nil => simp [formulaConjoin, truthFormula, Satisfies]
  | cons formula formulas inductionHypothesis =>
      simp only [formulaConjoin, Satisfies, List.mem_cons]
      rw [inductionHypothesis]
      constructor
      · rintro ⟨headSatisfied, tailSatisfied⟩ candidate
        rintro (rfl | member)
        · exact headSatisfied
        · exact tailSatisfied candidate member
      · intro allSatisfied
        exact ⟨allSatisfied formula (Or.inl rfl),
          fun candidate member => allSatisfied candidate (Or.inr member)⟩

/-- Ordinary first-order formula saying that one cell is nonzero. -/
def cellNonzeroFormula {arity : Nat} (cell : Cell arity) : Formula arity :=
  .negation (.equation { left := cellTerm cell, right := .bottom })

theorem satisfies_cellNonzeroFormula_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (cell : Cell arity) (valuation : Fin arity -> B) :
    Satisfies (cellNonzeroFormula cell) valuation <->
      cellValue valuation cell ≠ ⊥ := by
  simp [cellNonzeroFormula, Satisfies, eval_cellTerm, Term.eval]

/-- One literal fixes one bit of a proposed profile. -/
def profileBitFormula {arity : Nat} (profile : Profile arity)
    (cell : Cell arity) : Formula arity :=
  if profile cell then cellNonzeroFormula cell
  else .negation (cellNonzeroFormula cell)

theorem satisfies_profileBitFormula_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (profile : Profile arity) (cell : Cell arity)
    (valuation : Fin arity -> B) :
    Satisfies (profileBitFormula profile cell) valuation <->
      profileOf valuation cell = profile cell := by
  cases profileValue : profile cell
  · simp only [profileBitFormula, profileValue, Bool.false_eq_true,
      reduceIte, Satisfies]
    rw [satisfies_cellNonzeroFormula_iff, profileOf_eq_false_iff]
    exact not_ne_iff
  · simp only [profileBitFormula, profileValue, reduceIte]
    exact (satisfies_cellNonzeroFormula_iff cell valuation).trans
      (profileOf_eq_true_iff valuation cell).symm

/-- A quantifier-free formula specifying every cell-status bit. -/
def exactProfileFormula {arity : Nat} (profile : Profile arity) :
    Formula arity :=
  formulaConjoin ((allCells arity).map (profileBitFormula profile))

theorem satisfies_exactProfileFormula_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (profile : Profile arity) (valuation : Fin arity -> B) :
    Satisfies (exactProfileFormula profile) valuation <->
      profileOf valuation = profile := by
  simp only [exactProfileFormula, satisfies_formulaConjoin_iff, List.mem_map]
  constructor
  · intro allBits
    funext cell
    apply (satisfies_profileBitFormula_iff profile cell valuation).mp
    exact allBits (profileBitFormula profile cell)
      ⟨cell, mem_allCells cell, rfl⟩
  · intro profileEqual formula formulaMember
    obtain ⟨cell, _cellMember, rfl⟩ := formulaMember
    apply (satisfies_profileBitFormula_iff profile cell valuation).mpr
    exact congrFun profileEqual cell

/-- Disjunction expressed through the source language's functionally complete
negation/conjunction basis. -/
def formulaDisjunction {arity : Nat}
    (left right : Formula arity) : Formula arity :=
  .negation (.conjunction (.negation left) (.negation right))

theorem satisfies_formulaDisjunction_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (left right : Formula arity) (valuation : Fin arity -> B) :
    Satisfies (formulaDisjunction left right) valuation <->
      Satisfies left valuation ∨ Satisfies right valuation := by
  simp only [formulaDisjunction, Satisfies]
  constructor
  · intro notBothFalse
    by_cases leftSatisfied : Satisfies left valuation
    · exact Or.inl leftSatisfied
    · apply Or.inr
      by_contra rightSatisfied
      exact notBothFalse ⟨leftSatisfied, rightSatisfied⟩
  · rintro (leftSatisfied | rightSatisfied) bothFalse
    · exact bothFalse.1 leftSatisfied
    · exact bothFalse.2 rightSatisfied

def formulaDisjoin {arity : Nat} : List (Formula arity) -> Formula arity
  | [] => .falsum
  | formula :: formulas => formulaDisjunction formula (formulaDisjoin formulas)

theorem satisfies_formulaDisjoin_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (formulas : List (Formula arity)) (valuation : Fin arity -> B) :
    Satisfies (formulaDisjoin formulas) valuation <->
      exists formula, formula ∈ formulas ∧ Satisfies formula valuation := by
  induction formulas with
  | nil => simp [formulaDisjoin, Satisfies]
  | cons formula formulas inductionHypothesis =>
      rw [formulaDisjoin, satisfies_formulaDisjunction_iff,
        inductionHypothesis]
      constructor
      · rintro (headSatisfied | ⟨candidate, member, satisfied⟩)
        · exact ⟨formula, List.mem_cons_self, headSatisfied⟩
        · exact ⟨candidate, List.mem_cons_of_mem _ member, satisfied⟩
      · rintro ⟨candidate, member, satisfied⟩
        rcases List.mem_cons.mp member with rfl | tailMember
        · exact Or.inl satisfied
        · exact Or.inr ⟨candidate, tailMember, satisfied⟩

/-! ## Reified quantifier elimination -/

/-- The finite profiles accepted by a source formula. -/
def acceptedProfiles {arity : Nat} (formula : Formula arity) :
    List (Profile arity) :=
  (Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.allProfiles
    arity).filter fun profile => decideAt formula profile = true

/-- Reify the finite semantic classifier as an ordinary quantifier-free
formula. -/
def eliminateQuantifiers {arity : Nat} (formula : Formula arity) :
    Formula arity :=
  formulaDisjoin ((acceptedProfiles formula).map exactProfileFormula)

theorem profileBitFormula_quantifierFree {arity : Nat}
    (profile : Profile arity) (cell : Cell arity) :
    QuantifierFree (profileBitFormula profile cell) := by
  cases profileValue : profile cell <;>
    simp [profileBitFormula, profileValue, cellNonzeroFormula, QuantifierFree]

theorem formulaConjoin_quantifierFree {arity : Nat}
    (formulas : List (Formula arity))
    (allQuantifierFree : forall formula, formula ∈ formulas ->
      QuantifierFree formula) :
    QuantifierFree (formulaConjoin formulas) := by
  induction formulas with
  | nil => simp [formulaConjoin, truthFormula, QuantifierFree]
  | cons formula formulas inductionHypothesis =>
      simp only [formulaConjoin, QuantifierFree]
      exact ⟨allQuantifierFree formula List.mem_cons_self,
        inductionHypothesis (fun candidate member =>
          allQuantifierFree candidate (List.mem_cons_of_mem _ member))⟩

theorem exactProfileFormula_quantifierFree {arity : Nat}
    (profile : Profile arity) :
    QuantifierFree (exactProfileFormula profile) := by
  apply formulaConjoin_quantifierFree
  intro formula member
  obtain ⟨cell, _cellMember, rfl⟩ := List.mem_map.mp member
  exact profileBitFormula_quantifierFree profile cell

theorem formulaDisjoin_quantifierFree {arity : Nat}
    (formulas : List (Formula arity))
    (allQuantifierFree : forall formula, formula ∈ formulas ->
      QuantifierFree formula) :
    QuantifierFree (formulaDisjoin formulas) := by
  induction formulas with
  | nil => simp [formulaDisjoin, QuantifierFree]
  | cons formula formulas inductionHypothesis =>
      simp only [formulaDisjoin, formulaDisjunction, QuantifierFree]
      exact ⟨allQuantifierFree formula List.mem_cons_self,
        inductionHypothesis (fun candidate member =>
          allQuantifierFree candidate (List.mem_cons_of_mem _ member))⟩

/-- The eliminator has a syntactically quantifier-free output. -/
theorem eliminateQuantifiers_quantifierFree {arity : Nat}
    (formula : Formula arity) :
    QuantifierFree (eliminateQuantifiers formula) := by
  apply formulaDisjoin_quantifierFree
  intro exactFormula member
  obtain ⟨profile, _profileMember, rfl⟩ := List.mem_map.mp member
  exact exactProfileFormula_quantifierFree profile

/-- If finite profile evaluation accepts the actual profile of a valuation,
the reified quantifier-free formula holds there.  This direction is purely
representational and does not require atomlessness. -/
theorem satisfies_eliminateQuantifiers_of_decideAt_true
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (formula : Formula arity) (valuation : Fin arity -> B)
    (accepted : decideAt formula (profileOf valuation) = true) :
    Satisfies (eliminateQuantifiers formula) valuation := by
  rw [eliminateQuantifiers, satisfies_formulaDisjoin_iff]
  refine ⟨exactProfileFormula (profileOf valuation), ?_, ?_⟩
  · apply List.mem_map.mpr
    refine ⟨profileOf valuation, ?_, rfl⟩
    simp [acceptedProfiles,
      Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.mem_allProfiles,
      accepted]
  · exact (satisfies_exactProfileFormula_iff
      (profileOf valuation) valuation).mpr rfl

/-- Full quantifier elimination: source formula and reified quantifier-free
formula agree at every valuation in every atomless Boolean algebra. -/
theorem satisfies_eliminateQuantifiers_iff
    {B : Type u} [BooleanAlgebra B] (gunky : IsGunky B)
    {arity : Nat} (formula : Formula arity)
    (valuation : Fin arity -> B) :
    Satisfies (eliminateQuantifiers formula) valuation <->
      Satisfies formula valuation := by
  constructor
  · intro eliminatedSatisfied
    rw [eliminateQuantifiers, satisfies_formulaDisjoin_iff] at eliminatedSatisfied
    obtain ⟨exactFormula, exactMember, exactSatisfied⟩ := eliminatedSatisfied
    obtain ⟨profile, profileMember, rfl⟩ := List.mem_map.mp exactMember
    have profileEqual : profileOf valuation = profile :=
      (satisfies_exactProfileFormula_iff profile valuation).mp exactSatisfied
    have accepted : decideAt formula profile = true := by
      simpa [acceptedProfiles] using (List.mem_filter.mp profileMember).2
    apply (decideAt_eq_true_iff_satisfies gunky formula valuation).mp
    rw [profileEqual]
    exact accepted
  · intro sourceSatisfied
    apply satisfies_eliminateQuantifiers_of_decideAt_true formula valuation
    exact (decideAt_eq_true_iff_satisfies gunky formula valuation).mpr
      sourceSatisfied

/-! ## Theory-relative positive and negative canaries -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.AtomlessBooleanFirstOrderDecision.Canary

theorem properPart_eliminates_quantifiers :
    QuantifierFree (eliminateQuantifiers properPartSentence) :=
  eliminateQuantifiers_quantifierFree properPartSentence

theorem properPart_elimination_holds_in_atomless
    {B : Type u} [BooleanAlgebra B] [Nontrivial B]
    (gunky : IsGunky B) :
    Satisfies (eliminateQuantifiers properPartSentence)
      (emptyValuation (B := B)) :=
  (satisfies_eliminateQuantifiers_iff gunky properPartSentence
    emptyValuation).mpr (properPartSentence_holds_in_atomless gunky)

/-- The eliminated sentence is true even in `Bool`, because it reifies the
atomless theory's finite classifier rather than preserving arbitrary-model
semantics. -/
theorem eliminated_properPart_holds_in_bool :
    Satisfies (eliminateQuantifiers properPartSentence)
      (emptyValuation (B := Bool)) := by
  apply satisfies_eliminateQuantifiers_of_decideAt_true
  have emptyProfile :
      profileOf (emptyValuation (B := Bool)) = fun _cell => true := by
    simpa [emptyValuation,
      Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.emptyValuation]
      using
        (Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision.empty_profile_eq_true
          (B := Bool))
  rw [emptyProfile]
  exact properPartSentence_decides_true

/-- Negative canary: atomlessness cannot be removed from the equivalence
theorem. -/
theorem atomlessness_is_necessary :
    Satisfies (eliminateQuantifiers properPartSentence)
        (emptyValuation (B := Bool)) /\
      ¬ Satisfies properPartSentence (emptyValuation (B := Bool)) :=
  ⟨eliminated_properPart_holds_in_bool, properPartSentence_fails_in_bool⟩

end Canary

#print axioms eval_renameTerm
#print axioms eval_cellTerm
#print axioms satisfies_exactProfileFormula_iff
#print axioms eliminateQuantifiers_quantifierFree
#print axioms satisfies_eliminateQuantifiers_of_decideAt_true
#print axioms satisfies_eliminateQuantifiers_iff
#print axioms Canary.properPart_elimination_holds_in_atomless
#print axioms Canary.atomlessness_is_necessary

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanQuantifierElimination
